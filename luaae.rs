use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::iter::Peekable;
use std::rc::Rc;
use std::str::Chars;
use std::io;
use std::env;

const QNAN: u64 = 0x7FFC000000000000;
const SIGN_BIT: u64 = 0x8000000000000000;
const TAG_NIL: u64 = QNAN | 1;
const TAG_FALSE: u64 = QNAN | 2;
const TAG_TRUE: u64 = QNAN | 3;
const TAG_OBJ: u64 = QNAN | SIGN_BIT;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Value(u64);

impl Value {
    #[inline(always)]
    pub fn nil() -> Self {
        Value(TAG_NIL)
    }
    #[inline(always)]
    pub fn bool(b: bool) -> Self {
        Value(if b { TAG_TRUE } else { TAG_FALSE })
    }
    #[inline(always)]
    pub fn num(n: f64) -> Self {
        Value(n.to_bits())
    }
    #[inline(always)]
    pub fn obj(id: u32) -> Self {
        Value(TAG_OBJ | (id as u64))
    }

    #[inline(always)]
    pub fn is_obj(self) -> bool {
        (self.0 & TAG_OBJ) == TAG_OBJ
    }
    #[inline(always)]
    pub fn as_obj(self) -> u32 {
        (self.0 & !TAG_OBJ) as u32
    }
    #[inline(always)]
    pub fn as_num(self) -> f64 {
        f64::from_bits(self.0)
    }
    pub fn is_truthy(self) -> bool {
        self.0 != TAG_NIL && self.0 != TAG_FALSE
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum ThreadStatus {
    Suspended,
    Running,
    Dead,
}

#[derive(Clone)]
pub struct ThreadState {
    pub call_stack: Vec<CallFrame>,
    pub data_stack: Vec<Value>,
    pub handler_stack: Vec<HandlerFrame>,
    pub status: ThreadStatus,
}

#[derive(Clone)]
pub enum GcObject {
    Str(String),
    Table(HashMap<Value, Value>, Option<u32>),
    Upval(Value),
    Closure {
        chunk_idx: usize,
        upvalues: Vec<u32>,
    },
    Continuation {
        calls: Vec<CallFrame>,
        data: Vec<Value>,
        handlers: Vec<HandlerFrame>,
        orig_call_depth: usize,
        orig_data_depth: usize,
        orig_handler_depth: usize,
    },
    NativeFn(fn(&mut VM, Vec<Value>) -> usize),
    Thread(Option<Box<ThreadState>>),
    NativeClosure(fn(&mut VM, Vec<Value>, Value) -> usize, Value),
    File(Rc<RefCell<Option<File>>>, Option<u32>),
}

#[derive(Clone, Copy, Debug)]
pub enum OpCode {
    LoadConst(u32),
    LoadLocal(u32),
    StoreLocal(u32),
    GetTabUp(u32, u32),
    SetTabUp(u32, u32),
    SetTabLocal(u32, u32),
    LoadUpval(u32),
    StoreUpval(u32),
    Pop,
    PushNil,
    PushTrue,
    PushFalse,
    Dup,
    Swap,
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Mod,
    Pow,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Neq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    Concat,
    Len,
    Not,
    Neg,
    ForceNum,
    AppendMulti,
    JumpIfFalse(usize),
    Jump(usize),
    JumpIfFalseKeep(usize),
    JumpIfTrueKeep(usize),
    MakeClosure(u32),
    Call(u32, bool),
    Return(u32, bool),
    AdjustStack(u32),
    PushHandler(u32),
    PopHandler,
    Perform(u32, u32),
    MakeTable,
    GetTable,
    SetTable,
    LoadVararg,
    TailCall(u32, bool),
    PushStash,
    PopStash,
    ReverseStash(u32),
    ForCond,
    CloseLocals(u32),
    DetachUpvals(u32, u32),
}

#[derive(Clone)]
pub struct Chunk {
    pub instructions: Vec<OpCode>,
    pub lines: Vec<usize>,
    pub constants: Vec<Value>,
    pub local_count: usize,
    pub param_count: usize,
    pub is_vararg: bool,
    pub upvals: Vec<(bool, usize, String)>, // (is_local, index_in_parent, name)
    pub source_id: usize,
    pub linedefined: usize,
}

macro_rules! bin_op {
    ($vm:ident, $op:tt, $event:expr) => {{
        let b_val = $vm.data_stack.pop().unwrap();
        let a_val = $vm.data_stack.pop().unwrap();

        if let (Some(a), Some(b)) = ($vm.to_num(a_val), $vm.to_num(b_val)) {
            $vm.data_stack.push(Value::num(a $op b));
        } else {
            let mut mm = $vm.get_metamethod(a_val, $event);
            if mm.is_none() { mm = $vm.get_metamethod(b_val, $event); }

            if let Some(func) = mm {
                if !$vm.trigger_metamethod(func, vec![a_val, b_val]) {
                    $vm.runtime_error("attempt to perform arithmetic on an uncallable metamethod");
                }
            } else {
                $vm.runtime_error("attempt to perform arithmetic on a non-number");
            }
        }
    }};
}
macro_rules! cmp_op {

    ($vm:ident, $op:tt, $event:expr, $swap:expr) => {{
        let b_val = $vm.data_stack.pop().unwrap();
        let a_val = $vm.data_stack.pop().unwrap();

        if a_val.is_obj() && b_val.is_obj() && matches!(&$vm.objects[a_val.as_obj() as usize], Some(GcObject::Str(_))) && matches!(&$vm.objects[b_val.as_obj() as usize], Some(GcObject::Str(_))) {
            let a_str = $vm.val_to_str(a_val);
            let b_str = $vm.val_to_str(b_val);
            $vm.data_stack.push(Value::bool(a_str $op b_str));
        } else if let (Some(a), Some(b)) = ($vm.to_num(a_val), $vm.to_num(b_val)) {
            $vm.data_stack.push(Value::bool(a $op b));
        } else {
            let mm_a = $vm.get_metamethod(a_val, $event);
            let mm_b = $vm.get_metamethod(b_val, $event);

            if let (Some(func_a), Some(func_b)) = (mm_a, mm_b) {
                if func_a == func_b {
                    let (target_a, target_b) = if $swap { (b_val, a_val) } else { (a_val, b_val) };
                    if !$vm.trigger_metamethod(func_a, vec![target_a, target_b]) {
                        $vm.runtime_error("attempt to compare with an uncallable metamethod");
                    }
                } else {
                    $vm.runtime_error("attempt to compare uncomparable types");
                }
            } else {
                $vm.runtime_error("attempt to compare uncomparable types");
            }
        }
    }};

    ($vm:ident, $op:tt, $event:expr, $swap:expr, $fb_event:expr, $fb_swap:expr) => {{
        let b_val = $vm.data_stack.pop().unwrap();
        let a_val = $vm.data_stack.pop().unwrap();

        if a_val.is_obj() && b_val.is_obj() && matches!(&$vm.objects[a_val.as_obj() as usize], Some(GcObject::Str(_))) && matches!(&$vm.objects[b_val.as_obj() as usize], Some(GcObject::Str(_))) {
            let a_str = $vm.val_to_str(a_val);
            let b_str = $vm.val_to_str(b_val);
            $vm.data_stack.push(Value::bool(a_str $op b_str));
        } else if let (Some(a), Some(b)) = ($vm.to_num(a_val), $vm.to_num(b_val)) {
            $vm.data_stack.push(Value::bool(a $op b));
        } else {
            let mm_a = $vm.get_metamethod(a_val, $event);
            let mm_b = $vm.get_metamethod(b_val, $event);

            let mut handled = false;

            if let (Some(func_a), Some(func_b)) = (mm_a, mm_b) {
                if func_a == func_b {
                    let (target_a, target_b) = if $swap { (b_val, a_val) } else { (a_val, b_val) };
                    if !$vm.trigger_metamethod(func_a, vec![target_a, target_b]) {
                        $vm.runtime_error("attempt to compare with an uncallable metamethod");
                    }
                    handled = true;
                }
            }

            if !handled {
                let mm_fb_a = $vm.get_metamethod(a_val, $fb_event);
                let mm_fb_b = $vm.get_metamethod(b_val, $fb_event);

                if let (Some(func_fb_a), Some(func_fb_b)) = (mm_fb_a, mm_fb_b) {
                    if func_fb_a == func_fb_b {
                        let (fb_a, fb_b) = if $fb_swap { (b_val, a_val) } else { (a_val, b_val) };
                        if !$vm.trigger_metamethod(func_fb_a, vec![fb_a, fb_b]) {
                            $vm.runtime_error("attempt to compare with an uncallable metamethod");
                        }
                        let res = $vm.data_stack.pop().unwrap();
                        $vm.data_stack.push(Value::bool(!res.is_truthy()));
                    } else {
                        $vm.runtime_error("attempt to compare uncomparable types");
                    }
                } else {
                    $vm.runtime_error("attempt to compare uncomparable types");
                }
            }
        }
    }};
}

macro_rules! bit_op {
    ($vm:ident, $op:tt, $event:expr) => {{
        let b_val = $vm.data_stack.pop().unwrap();
        let a_val = $vm.data_stack.pop().unwrap();

        if let (Some(a), Some(b)) = ($vm.to_num(a_val), $vm.to_num(b_val)) {
            $vm.data_stack.push(Value::num(((a as i64) $op (b as i64)) as f64));
        } else {
            let mut mm = $vm.get_metamethod(a_val, $event);
            if mm.is_none() { mm = $vm.get_metamethod(b_val, $event); }

            if let Some(func) = mm {
                if !$vm.trigger_metamethod(func, vec![a_val, b_val]) {
                    $vm.runtime_error("attempt to perform bitwise operation on an uncallable metamethod");
                }
            } else {
                $vm.runtime_error("attempt to perform bitwise operation on a non-number");
            }
        }
    }};
}
macro_rules! get_table_core {
    ($vm:ident, $current:expr, $key:expr, $frame_idx:expr, $chunk_idx:expr) => {{
        let mut current = $current;
        let key = $key;

        // Fast non-allocating string lookup for "__index"
        let mut index_key = Value::nil();
        for (idx, obj) in $vm.objects.iter().enumerate() {
            if let Some(GcObject::Str(s)) = obj {
                if s == "__index" {
                    index_key = Value::obj(idx as u32);
                    break;
                }
            }
        }

        let mut handled = false;
        for _ in 0..20 {
            // 1. Direct Table Lookup (Only if it's actually an object)
            let mut found_val = None;
            if current.is_obj() {
                if let Some(GcObject::Table(map, _)) = &$vm.objects[current.as_obj() as usize] {
                    found_val = map.get(&key).copied();
                } else if let Some(GcObject::Str(_)) = &$vm.objects[current.as_obj() as usize] {
                    let string_table = $vm.get_global("string");
                    if string_table.is_obj() {
                        if let Some(GcObject::Table(map, _)) =
                            &$vm.objects[string_table.as_obj() as usize]
                        {
                            found_val = map.get(&key).copied();
                        }
                    }
                }
            }

            if let Some(v) = found_val {
                $vm.data_stack.push(v);
                handled = true;
                break;
            }

            // 2. Metatable __index Lookup (Using our universal helper)
            let mt_id = $vm.get_type_metatable(current);

            if let Some(id) = mt_id {
                if let Some(GcObject::Table(mt_map, _)) = &$vm.objects[id as usize] {
                    let mut index_val = mt_map.get(&index_key).copied().unwrap_or(Value::nil());

                    // String comparison fallback (if __index wasn't interned properly)
                    if index_val.0 == TAG_NIL {
                        for (&k, &v) in mt_map.iter() {
                            if k.is_obj() && $vm.val_to_str(k) == "__index" {
                                index_val = v;
                                break;
                            }
                        }
                    }

                    if index_val.is_obj() {
                        match $vm.objects[index_val.as_obj() as usize].clone().unwrap() {
                            GcObject::Table(..) => {
                                current = index_val;
                                continue;
                            }
                            GcObject::NativeFn(_)
                            | GcObject::Closure { .. }
                            | GcObject::NativeClosure(..)
                            | GcObject::Continuation { .. } => {
                                $vm.internal_call(index_val, vec![current, key]);

                                if $vm.multiret_count > 0 {
                                    let first_ret =
                                        $vm.data_stack[$vm.data_stack.len() - $vm.multiret_count];
                                    for _ in 0..$vm.multiret_count {
                                        $vm.data_stack.pop();
                                    }
                                    $vm.data_stack.push(first_ret);
                                } else {
                                    $vm.data_stack.push(Value::nil());
                                }

                                handled = true;
                                break;
                            }
                            _ => {}
                        }
                    }
                }
            }

            // 3. Not found & No metatable -> Return nil if table, else Error
            if current.is_obj()
                && matches!(
                    $vm.objects[current.as_obj() as usize],
                    Some(GcObject::Table(..))
                )
            {
                $vm.data_stack.push(Value::nil());
                handled = true;
                break;
            } else {
                $vm.runtime_error(&format!(
                    "attempt to index a {} value",
                    $vm.val_to_str(current)
                ));
            }
        }
        if !handled {
            $vm.data_stack.push(Value::nil());
        }
    }};
}

macro_rules! set_table_core {
    ($vm:ident, $current:expr, $key:expr, $val:expr, $frame_idx:expr) => {{
        let mut current = $current;
        let key = $key;
        let val = $val;
        if key.0 == TAG_NIL {
            $vm.runtime_error("table index is nil");
        }
        if !key.is_obj() && key.0 != TAG_FALSE && key.0 != TAG_TRUE {
            if key.as_num().is_nan() {
                $vm.runtime_error("table index is NaN");
            }
        }

        let mut newindex_key = Value::nil();
        for (idx, obj) in $vm.objects.iter().enumerate() {
            if let Some(GcObject::Str(s)) = obj {
                if s == "__newindex" {
                    newindex_key = Value::obj(idx as u32);
                    break;
                }
            }
        }

        let mut handled = false;
        for _ in 0..20 {
            // 1. Direct Table Lookup
            let mut has_key = false;
            if current.is_obj() {
                if let Some(GcObject::Table(map, _)) = &$vm.objects[current.as_obj() as usize] {
                    has_key = map.contains_key(&key);
                }
            }

            if has_key {
                if let Some(GcObject::Table(map, _)) = &mut $vm.objects[current.as_obj() as usize] {
                    if val.0 == TAG_NIL {
                        map.remove(&key);
                    } else {
                        map.insert(key, val);
                    }
                }
                handled = true;
                break;
            }

            // 2. Metatable __newindex Lookup
            let mt_id = $vm.get_type_metatable(current);

            if let Some(id) = mt_id {
                if let Some(GcObject::Table(mt_map, _)) = &$vm.objects[id as usize] {
                    let mut newindex_val =
                        mt_map.get(&newindex_key).copied().unwrap_or(Value::nil());

                    if newindex_val.0 == TAG_NIL {
                        for (&k, &v) in mt_map.iter() {
                            if k.is_obj() && $vm.val_to_str(k) == "__newindex" {
                                newindex_val = v;
                                break;
                            }
                        }
                    }

                    if newindex_val.is_obj() {
                        match $vm.objects[newindex_val.as_obj() as usize].clone().unwrap() {
                            GcObject::Table(..) => {
                                current = newindex_val;
                                continue;
                            }
                            GcObject::NativeFn(_)
                            | GcObject::Closure { .. }
                            | GcObject::NativeClosure(..)
                            | GcObject::Continuation { .. } => {
                                $vm.internal_call(newindex_val, vec![current, key, val]);
                                for _ in 0..$vm.multiret_count {
                                    $vm.data_stack.pop();
                                }
                                handled = true;
                                break;
                            }
                            _ => {}
                        }
                    }
                }
            }

            // 3. Not found & no metatable -> mutate if table, else Error
            if current.is_obj()
                && matches!(
                    $vm.objects[current.as_obj() as usize],
                    Some(GcObject::Table(..))
                )
            {
                if let Some(GcObject::Table(map, _)) = &mut $vm.objects[current.as_obj() as usize] {
                    if val.0 == TAG_NIL {
                        map.remove(&key);
                    } else {
                        map.insert(key, val);
                    }
                }
                handled = true;
                break;
            } else {
                $vm.runtime_error(&format!(
                    "attempt to index a {} value",
                    $vm.val_to_str(current)
                ));
            }
        }
        if !handled {
            $vm.runtime_error("__newindex chain too deep");
        }
        $vm.data_stack.push(val);
    }};
}

#[derive(Clone, Debug)]
pub struct CallFrame {
    pub closure_id: u32,
    pub chunk_idx: usize,
    pub ip: usize,
    pub stack_base: usize,
    pub handler_base: usize,
    pub varargs: Vec<Value>,
}

#[derive(Clone, Debug)]
pub struct HandlerFrame {
    pub effect_id: u32,
    pub closure_id: u32,
    pub call_depth: usize,
    pub data_depth: usize,
    pub is_active: bool,
}

pub struct VM {
    pub objects: Vec<Option<GcObject>>,
    pub chunks: Vec<Chunk>,
    pub global_env: u32,
    pub strings: Vec<String>,
    pub marked: Vec<bool>,
    pub free_list: Vec<usize>,
    pub gray_stack: Vec<u32>,
    pub bytes_allocated: usize,
    pub temp_roots: Vec<Value>,
    pub next_gc_threshold: usize,
    pub call_stack: Vec<CallFrame>,
    pub data_stack: Vec<Value>,
    pub handler_stack: Vec<HandlerFrame>,
    pub multiret_count: usize,
    pub sources: Vec<Vec<String>>,
    pub source_names: Vec<String>,
    pub last_traceback: String,
    pub yielded: bool,
    pub c_call_depth: usize,
    pub current_thread: Option<u32>,
    pub rng_state: u64,
}

impl VM {
    pub fn new() -> Self {
        let mut vm = Self {
            objects: Vec::new(),
            chunks: Vec::new(),
            global_env: 0,
            strings: Vec::new(),
            call_stack: Vec::new(),
            data_stack: Vec::new(),
            handler_stack: Vec::new(),
            multiret_count: 0,
            sources: Vec::new(),
            source_names: Vec::new(),
            last_traceback: String::new(),
            marked: Vec::new(),
            temp_roots: Vec::new(),
            free_list: Vec::new(),
            gray_stack: Vec::new(),
            bytes_allocated: 0,
            next_gc_threshold: 1024 * 1024,
            yielded: false,
            c_call_depth: 0,
            current_thread: None,
            rng_state: 853049102483120,
        };
        let global_map = HashMap::new();
        let env_id = vm.alloc(GcObject::Table(global_map, None));
        vm.global_env = env_id;

        let g_str = vm.alloc_str("_G");
        if let Some(GcObject::Table(map, _)) = &mut vm.objects[env_id as usize] {
            map.insert(g_str, Value::obj(env_id));
        }
        vm
    }

    pub fn generate_traceback(&self, skip: usize) -> String {
        let mut msg = String::from("stack traceback:");
        let stack_len = self.call_stack.len();
        if skip >= stack_len {
            return msg;
        }

        let start_idx = stack_len - skip;
        let frames: Vec<_> = self.call_stack.iter().take(start_idx).collect();
        let total_frames = frames.len();

        for (i, frame) in frames.into_iter().rev().enumerate() {
            let chunk = &self.chunks[frame.chunk_idx];
            let ip = frame.ip.saturating_sub(1);
            let line = *chunk.lines.get(ip).unwrap_or(&0);
            let source_name = self
                .source_names
                .get(chunk.source_id)
                .map(|s| s.as_str())
                .unwrap_or("?");

            msg.push_str(&format!("\n\t{}:{} in ", source_name, line));
            if i == total_frames - 1 {
                msg.push_str("main chunk");
            } else {
                msg.push_str("function");
            }
        }
        msg
    }

    pub fn runtime_error(&mut self, msg: &str) -> ! {
        let mut err_msg = format!("{}", msg);
        let tb = self.generate_traceback(0);
        self.last_traceback = tb.clone();
        err_msg.push_str("\n");
        err_msg.push_str(&tb);
        panic!("{}", err_msg);
    }

    pub fn get_global(&mut self, name: &str) -> Value {
        let key = self.alloc_str(name);
        if let Some(GcObject::Table(map, _)) = &self.objects[self.global_env as usize] {
            map.get(&key).copied().unwrap_or(Value::nil())
        } else {
            Value::nil()
        }
    }

    pub fn set_global(&mut self, name: &str, val: Value) {
        let key = self.alloc_str(name);
        if let Some(GcObject::Table(map, _)) = &mut self.objects[self.global_env as usize] {
            map.insert(key, val);
        }
    }

    pub fn alloc(&mut self, obj: GcObject) -> u32 {
        if self.bytes_allocated > self.next_gc_threshold {
            self.collect_garbage();
        }

        self.bytes_allocated += 1;

        if let Some(idx) = self.free_list.pop() {
            self.objects[idx] = Some(obj);
            self.marked[idx] = false;
            idx as u32
        } else {
            self.objects.push(Some(obj));
            self.marked.push(false);
            (self.objects.len() - 1) as u32
        }
    }
    pub fn collect_garbage(&mut self) {
        self.mark_roots();
        self.trace_references();
        self.sweep();
        self.next_gc_threshold = self.bytes_allocated * 2;
    }

    fn mark_value(&mut self, val: Value) {
        if val.is_obj() {
            self.mark_object(val.as_obj());
        }
    }

    fn mark_object(&mut self, id: u32) {
        let idx = id as usize;
        if !self.marked[idx] {
            self.marked[idx] = true;
            self.gray_stack.push(id);
        }
    }

    fn mark_roots(&mut self) {

        for i in 0..self.data_stack.len() {
            let val = self.data_stack[i];
            self.mark_value(val);
        }

        self.mark_object(self.global_env);

        for i in 0..self.call_stack.len() {
            let closure_id = self.call_stack[i].closure_id;
            self.mark_object(closure_id);

            for j in 0..self.call_stack[i].varargs.len() {
                let val = self.call_stack[i].varargs[j];
                self.mark_value(val);
            }
        }

        for i in 0..self.handler_stack.len() {
            let closure_id = self.handler_stack[i].closure_id;
            self.mark_object(closure_id);
        }

        for i in 0..self.chunks.len() {
            for j in 0..self.chunks[i].constants.len() {
                let val = self.chunks[i].constants[j];
                self.mark_value(val);
            }
        }

        for i in 0..self.temp_roots.len() {
            let val = self.temp_roots[i];
            self.mark_value(val);
        }
    }

    fn trace_references(&mut self) {
        while let Some(id) = self.gray_stack.pop() {
            let obj = self.objects[id as usize].clone();

            if let Some(gc_obj) = obj {
                match gc_obj {
                    GcObject::Table(map, meta_opt) => {
                        for (k, v) in map {
                            self.mark_value(k);
                            self.mark_value(v);
                        }
                        if let Some(meta) = meta_opt {
                            self.mark_object(meta);
                        }
                    }
                    GcObject::Closure { upvalues, .. } => {
                        for upval_id in upvalues {
                            self.mark_object(upval_id);
                        }
                    }
                    GcObject::Upval(val) => {
                        self.mark_value(val);
                    }
                    GcObject::Continuation {
                        calls,
                        data,
                        handlers,
                        ..
                    } => {

                        for frame in calls {
                            self.mark_object(frame.closure_id);
                            for &val in &frame.varargs {
                                self.mark_value(val);
                            }
                        }
                        for val in data {
                            self.mark_value(val);
                        }
                        for h in handlers {
                            self.mark_object(h.closure_id);
                        }
                    }
                    GcObject::Thread(Some(ts)) => {

                        for val in &ts.data_stack {
                            self.mark_value(*val);
                        }
                        for frame in &ts.call_stack {
                            self.mark_object(frame.closure_id);
                            for &val in &frame.varargs {
                                self.mark_value(val);
                            }
                        }
                        for frame in &ts.handler_stack {
                            self.mark_object(frame.closure_id);
                        }
                    }
                    GcObject::Thread(None) => {}
                    GcObject::NativeClosure(_, state_val) => {
                        self.mark_value(state_val);
                    }
                    GcObject::Str(_) | GcObject::NativeFn(_) => {}
                    GcObject::File(_, mt) => {
                        if let Some(meta) = mt {
                            self.mark_object(meta);
                        }
                    }
                }
            }
        }
    }
    fn sweep(&mut self) {
        for i in 0..self.objects.len() {
            if self.objects[i].is_some() {
                if self.marked[i] {
                    self.marked[i] = false;
                } else {
                    self.objects[i] = None;
                    self.free_list.push(i);
                }
            }
        }
    }
    pub fn intern_str(&mut self, s: &str) -> u32 {
        if let Some(idx) = self.strings.iter().position(|x| x == s) {
            return idx as u32;
        }
        self.strings.push(s.to_string());
        (self.strings.len() - 1) as u32
    }
    pub fn alloc_str(&mut self, s: &str) -> Value {
        for (idx, obj) in self.objects.iter().enumerate() {
            if let Some(GcObject::Str(existing)) = obj {
                if existing == s {
                    return Value::obj(idx as u32);
                }
            }
        }
        let id = self.alloc(GcObject::Str(s.to_string()));
        Value::obj(id)
    }
    pub fn val_to_str(&self, val: Value) -> String {
        if val.0 == TAG_NIL {
            "nil".to_string()
        } else if val.0 == TAG_FALSE {
            "false".to_string()
        } else if val.0 == TAG_TRUE {
            "true".to_string()
        } else if val.is_obj() {
            match &self.objects[val.as_obj() as usize].as_ref().unwrap() {
                GcObject::Str(s) => s.clone(),
                GcObject::Table(..) => format!("table: 0x{:x}", val.as_obj()),
                GcObject::Closure {
                    chunk_idx: _,
                    upvalues: _,
                }
                | GcObject::NativeFn(_)
                | GcObject::NativeClosure(..) => format!("function: 0x{:x}", val.as_obj()),
                GcObject::File(..) => format!("file: 0x{:x}", val.as_obj()),
                GcObject::Thread(..) => format!("thread: 0x{:x}", val.as_obj()),
                _ => "object".to_string(),
            }
        } else {
            val.as_num().to_string()
        }
    }
    pub fn to_num(&self, val: Value) -> Option<f64> {
        if !val.is_obj() && val.0 != TAG_NIL && val.0 != TAG_FALSE && val.0 != TAG_TRUE {
            Some(val.as_num())
        } else if val.is_obj() {
            if let Some(Some(GcObject::Str(s))) = self.objects.get(val.as_obj() as usize) {
                s.trim().parse::<f64>().ok()
            } else {
                None
            }
        } else {
            None
        }
    }
    pub fn get_metamethod(&mut self, val: Value, event: &str) -> Option<Value> {
        let mt_id = self.get_type_metatable(val);

        if let Some(mt_id) = mt_id {
            let mut ev_key_opt = None;
            for (idx, obj) in self.objects.iter().enumerate() {
                if let Some(GcObject::Str(existing)) = obj {
                    if existing == event {
                        ev_key_opt = Some(Value::obj(idx as u32));
                        break;
                    }
                }
            }

            if let Some(ev_key) = ev_key_opt {
                if let Some(GcObject::Table(mt_map, _)) = &self.objects[mt_id as usize] {
                    if let Some(&mm) = mt_map.get(&ev_key) {
                        if mm.is_truthy() {
                            return Some(mm);
                        }
                    }
                }
            }
        }
        None
    }
    // Put this inside `impl VM`
    pub fn get_type_metatable(&mut self, val: Value) -> Option<u32> {
        if val.is_obj() {
            match &self.objects[val.as_obj() as usize] {
                Some(GcObject::Table(_, mt)) | Some(GcObject::File(_, mt)) => {
                    return *mt;
                }
                Some(GcObject::Str(_)) => {
                    // Try __mt_string first (allows debug.setmetatable("", mt))
                    let k = self.alloc_str("__mt_string");
                    if let Some(GcObject::Table(genv, _)) = &self.objects[self.global_env as usize]
                    {
                        if let Some(mt_val) = genv.get(&k) {
                            if mt_val.is_obj() {
                                return Some(mt_val.as_obj());
                            }
                        }
                    }
                    // Fallback to standard string library metatable
                    let st_key = self.alloc_str("string");
                    if let Some(GcObject::Table(genv, _)) = &self.objects[self.global_env as usize]
                    {
                        if let Some(st) = genv.get(&st_key) {
                            if st.is_obj() {
                                if let Some(GcObject::Table(_, mt)) =
                                    &self.objects[st.as_obj() as usize]
                                {
                                    return *mt;
                                }
                            }
                        }
                    }
                    return None;
                }
                Some(GcObject::Closure { .. })
                | Some(GcObject::NativeFn(_))
                | Some(GcObject::NativeClosure(..)) => {
                    let k = self.alloc_str("__mt_function");
                    if let Some(GcObject::Table(genv, _)) = &self.objects[self.global_env as usize]
                    {
                        if let Some(mt_val) = genv.get(&k) {
                            if mt_val.is_obj() {
                                return Some(mt_val.as_obj());
                            }
                        }
                    }
                    return None;
                }
                Some(GcObject::Thread(_)) => {
                    let k = self.alloc_str("__mt_thread");
                    if let Some(GcObject::Table(genv, _)) = &self.objects[self.global_env as usize]
                    {
                        if let Some(mt_val) = genv.get(&k) {
                            if mt_val.is_obj() {
                                return Some(mt_val.as_obj());
                            }
                        }
                    }
                    return None;
                }
                _ => return None,
            }
        } else {
            // Primitive types: fetch from global_env using hidden keys
            let type_name = match val.0 {
                TAG_NIL => "__mt_nil",
                TAG_FALSE | TAG_TRUE => "__mt_boolean",
                _ => "__mt_number",
            };
            let k = self.alloc_str(type_name);
            if let Some(GcObject::Table(genv, _)) = &self.objects[self.global_env as usize] {
                if let Some(mt_val) = genv.get(&k) {
                    if mt_val.is_obj() {
                        return Some(mt_val.as_obj());
                    }
                }
            }
            return None;
        }
    }

    pub fn trigger_metamethod(&mut self, func: Value, args: Vec<Value>) -> bool {
        if !func.is_obj() {
            return false;
        }

        match self.objects[func.as_obj() as usize].clone().unwrap() {

            GcObject::Closure { .. }
            | GcObject::NativeFn(_)
            | GcObject::NativeClosure(..)
            | GcObject::Continuation { .. } => {

                self.internal_call(func, args);

                if self.multiret_count > 0 {

                    let first_ret = self.data_stack[self.data_stack.len() - self.multiret_count];

                    for _ in 0..self.multiret_count {
                        self.data_stack.pop();
                    }

                    self.data_stack.push(first_ret);
                } else {

                    self.data_stack.push(Value::nil());
                }

                true
            }
            _ => false,
        }
    }

    fn register_method(
        &mut self,
        map: &mut HashMap<Value, Value>,
        name: &str,
        func: fn(&mut VM, Vec<Value>) -> usize,
    ) {
        let key = self.alloc_str(name);
        let val = self.alloc(GcObject::NativeFn(func));
        map.insert(key, Value::obj(val));
    }

    pub fn open_standard_libs(&mut self) {
        self.open_base_lib();
        self.open_math_lib();
        self.open_table_lib();
        self.open_string_lib();
        self.open_os_lib();
        self.open_coroutine_lib();
        self.open_package_lib();
        self.open_io_lib();
        self.open_debug_lib();

        let pkg_val = self.get_global("package");
        if pkg_val.is_obj() {
            let loaded_key = self.alloc_str("loaded");
            let loaded_tab_val =
                if let Some(GcObject::Table(map, _)) = &self.objects[pkg_val.as_obj() as usize] {
                    map.get(&loaded_key).copied().unwrap_or(Value::nil())
                } else {
                    Value::nil()
                };

            if loaded_tab_val.is_obj() {

                let std_libs = [
                    "_G",
                    "coroutine",
                    "package",
                    "string",
                    "table",
                    "math",
                    "io",
                    "os",
                    "debug",
                ];
                for lib_name in std_libs {

                    let lib_val = if lib_name == "_G" {
                        Value::obj(self.global_env)
                    } else {
                        self.get_global(lib_name)
                    };

                    if lib_val.is_truthy() {
                        let name_key = self.alloc_str(lib_name);

                        if let Some(GcObject::Table(map, _)) =
                            &mut self.objects[loaded_tab_val.as_obj() as usize]
                        {
                            map.insert(name_key, lib_val);
                        }
                    }
                }
            }
        }
    }

    fn open_base_lib(&mut self) {
        // 1. type(v)
        let type_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'type' (value expected)");
            }
            let t_name = match args[0].0 {
                TAG_NIL => "nil",
                TAG_FALSE | TAG_TRUE => "boolean",
                _ if !args[0].is_obj() => "number",
                _ => match &vm.objects[args[0].as_obj() as usize].as_ref().unwrap() {
                    GcObject::Str(_) => "string",
                    GcObject::Table(..) => "table",
                    GcObject::Closure { .. } | GcObject::NativeFn(_) | GcObject::NativeClosure(..) => "function",
                    GcObject::Continuation { .. } | GcObject::Thread(_) => "thread",
                    GcObject::Upval(_) => "upvalue",
                    GcObject::File(..) => "userdata",
                    _ => "unknown",
                },
            };
            let str_val = vm.alloc_str(t_name);
            vm.data_stack.push(str_val);
            1
        }));

        // 2. error(msg)
        let error_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let msg_val = args.get(0).copied().unwrap_or(Value::nil());
            let level = args.get(1).and_then(|v| vm.to_num(*v)).unwrap_or(1.0) as usize;

            let mut prefix = String::new();
            if level > 0 {
                let skip = level.saturating_sub(1);
                let stack_len = vm.call_stack.len();
                if skip < stack_len {
                    let frame = &vm.call_stack[stack_len - 1 - skip];
                    let chunk = &vm.chunks[frame.chunk_idx];
                    let ip = frame.ip.saturating_sub(1);
                    let line = *chunk.lines.get(ip).unwrap_or(&0);
                    let source_name = vm
                        .source_names
                        .get(chunk.source_id)
                        .map(|s| s.as_str())
                        .unwrap_or("?");
                    prefix = format!("{}:{}: ", source_name, line);
                }
            }

            vm.last_traceback = vm.generate_traceback(0);

            let msg_str = if msg_val.is_obj()
                && matches!(
                    vm.objects[msg_val.as_obj() as usize],
                    Some(GcObject::Str(_))
                ) {
                format!("{}{}", prefix, vm.val_to_str(msg_val))
            } else if msg_val.0 == TAG_NIL {
                format!("{}nil", prefix)
            } else {
                format!("{}{}", prefix, vm.val_to_str(msg_val))
            };

            if msg_val.is_obj()
                && matches!(
                    vm.objects[msg_val.as_obj() as usize],
                    Some(GcObject::Str(_))
                )
            {
                std::panic::panic_any(vm.alloc_str(&msg_str));
            } else if msg_val.0 == TAG_NIL {
                std::panic::panic_any(vm.alloc_str(&msg_str));
            } else {
                std::panic::panic_any(msg_val);
            }
        }));

        // 3. print(...)
        let print_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    print!("\t");
                }
                print!("{}", vm.val_to_str(*a));
            }
            println!();
            0
        }));

        // 4. assert(v, [message])
        let assert_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() || !args[0].is_truthy() {
                let msg = if args.len() > 1 {
                    vm.val_to_str(args[1])
                } else {
                    "Assertion failed!".to_string()
                };
                vm.runtime_error(&msg);
            }
            for a in &args {
                vm.data_stack.push(*a);
            }
            args.len()
        }));

        // 5. tonumber(e)
        let tonumber_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'tonumber' (value expected)");
            }
            let val = args[0];
            let base_val = args.get(1).copied().unwrap_or(Value::nil());

            let base = if base_val.0 != TAG_NIL {
                if let Some(n) = vm.to_num(base_val) {
                    let b = n as u32;
                    if b != 10 && (b < 2 || b > 36) {
                        vm.runtime_error("bad argument #2 to 'tonumber' (base out of range)");
                    }
                    Some(b)
                } else {
                    vm.runtime_error("bad argument #2 to 'tonumber' (number expected)");
                    None
                }
            } else {
                None
            };

            let s = if val.is_obj() {
                if let Some(GcObject::Str(s)) = &vm.objects[val.as_obj() as usize] {
                    Some(s.trim().to_string())
                } else {
                    None
                }
            } else if val.0 != TAG_NIL && val.0 != TAG_FALSE && val.0 != TAG_TRUE {
                Some(val.as_num().to_string())
            } else {
                None
            };

            if let Some(mut str_val) = s {
                let mut sign = 1.0;
                if str_val.starts_with('-') {
                    sign = -1.0;
                    str_val.remove(0);
                } else if str_val.starts_with('+') {
                    str_val.remove(0);
                }
                str_val = str_val.trim().to_string();

                if let Some(b) = base {
                    if let Ok(n) = u64::from_str_radix(&str_val, b) {
                        vm.data_stack.push(Value::num((n as f64) * sign));
                        return 1;
                    }
                } else {
                    if let Ok(n) = str_val.parse::<f64>() {
                        vm.data_stack.push(Value::num(n * sign));
                        return 1;
                    } else if str_val.to_lowercase().starts_with("0x") {
                        let n = parse_hex_float(&str_val);
                        if !n.is_nan() {
                            vm.data_stack.push(Value::num(n * sign));
                            return 1;
                        }
                    }
                }
            }
            vm.data_stack.push(Value::nil());
            1
        }));

        // 6. tostring(e)
        let tostring_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 1 {
                vm.runtime_error("bad argument #1 to 'tostring' (value expected)");
            }
            let val = args.get(0).copied().unwrap_or(Value::nil());

            if let Some(mm) = vm.get_metamethod(val, "__tostring") {
                if vm.trigger_metamethod(mm, vec![val]) {
                    return 1;
                }
            }

            let s = vm.val_to_str(val);
            let s_val = vm.alloc_str(&s);
            vm.data_stack.push(s_val);
            1
        }));

        // 7. setmetatable(table, metatable)
        let setmetatable_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 2 || !args[0].is_obj() {
                vm.runtime_error("bad argument to 'setmetatable' (table expected)");
            }
            let (t, mt) = (args[0], args[1]);
            let t_idx = t.as_obj() as usize;

            if let Some(GcObject::Table(_, Some(old_mt_id))) = vm.objects[t_idx].clone() {

                let meta_key = vm.alloc_str("__metatable");

                if let Some(GcObject::Table(mt_map, _)) = &vm.objects[old_mt_id as usize] {
                    let mut is_protected = mt_map.contains_key(&meta_key);

                    if !is_protected {
                        for (&k, _) in mt_map.iter() {
                            if k.is_obj() && vm.val_to_str(k) == "__metatable" {
                                is_protected = true;
                                break;
                            }
                        }
                    }

                    if is_protected {
                        vm.runtime_error("cannot change a protected metatable");
                    }
                }
            }

            let new_mt = if mt.0 == TAG_NIL {
                None
            } else if mt.is_obj()
                && matches!(
                    vm.objects[mt.as_obj() as usize],
                    Some(GcObject::Table(_, _))
                )
            {
                Some(mt.as_obj())
            } else {
                vm.runtime_error("bad argument #2 to 'setmetatable' (nil or table expected)");
                return 0;
            };

            if let Some(GcObject::Table(_, ref mut meta)) = &mut vm.objects[t_idx] {
                *meta = new_mt;
            }

            vm.data_stack.push(t);
            1
        }));

        // 8. getmetatable(table)
        let getmetatable_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument to 'getmetatable' (value expected)");
            }

            let mt_id = vm.get_type_metatable(args[0]);

            if let Some(id) = mt_id {
                let meta_key = vm.alloc_str("__metatable");
                if let Some(GcObject::Table(mt_map, _)) = &vm.objects[id as usize] {
                    let mut protected_val = mt_map.get(&meta_key).copied().unwrap_or(Value::nil());

                    if protected_val.0 == TAG_NIL {
                        for (&k, &v) in mt_map.iter() {
                            if k.is_obj() && vm.val_to_str(k) == "__metatable" {
                                protected_val = v;
                                break;
                            }
                        }
                    }

                    if protected_val.0 != TAG_NIL {
                        vm.data_stack.push(protected_val);
                        return 1;
                    }
                }
                vm.data_stack.push(Value::obj(id));
                return 1;
            }

            vm.data_stack.push(Value::nil());
            1
        }));

        // 9. next(table, [index])
        let next_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'next' (table expected)");
            }
            let (table, key) = (args[0], args.get(1).copied().unwrap_or(Value::nil()));
            if let Some(GcObject::Table(map, _)) = &vm.objects[table.as_obj() as usize] {
                let mut keys: Vec<Value> = map.keys().copied().collect();
                keys.sort_by(|a, b| a.0.cmp(&b.0));

                if key.0 == TAG_NIL {
                    if keys.is_empty() {
                        vm.data_stack.push(Value::nil());
                        return 1;
                    }
                    vm.data_stack.push(keys[0]);
                    vm.data_stack.push(map[&keys[0]]);
                    return 2;
                } else {
                    if let Some(&next_k) = keys.iter().find(|&&k| k.0 > key.0) {
                        vm.data_stack.push(next_k);
                        vm.data_stack.push(map[&next_k]);
                        return 2;
                    }
                }
                vm.data_stack.push(Value::nil());
                return 1;
            }
            vm.runtime_error("bad argument to 'next'");
        }));

        // 10. pairs & ipairs
        let pairs_fn = self.alloc(GcObject::NativeClosure(
            |vm, args, state| {
                vm.data_stack.push(state);
                vm.data_stack
                    .push(args.get(0).copied().unwrap_or(Value::nil()));
                vm.data_stack.push(Value::nil());
                3
            },
            Value::obj(next_fn),
        ));

        let ipairs_iter_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let (table, index) = (args[0], args[1].as_num() as usize + 1);
            if let Some(GcObject::Table(map, _)) = &vm.objects[table.as_obj() as usize] {
                let key = Value::num(index as f64);
                if let Some(&val) = map.get(&key) {
                    vm.data_stack.push(key);
                    vm.data_stack.push(val);
                    return 2;
                }
            }
            vm.data_stack.push(Value::nil());
            1
        }));

        self.set_global("ipairs_iter", Value::obj(ipairs_iter_fn));

        let ipairs_fn = self.alloc(GcObject::NativeClosure(
            |vm, args, state| {
                vm.data_stack.push(state);
                vm.data_stack
                    .push(args.get(0).copied().unwrap_or(Value::nil()));
                vm.data_stack.push(Value::num(0.0));
                3
            },
            Value::obj(ipairs_iter_fn),
        ));

        let pcall_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.data_stack.push(Value::bool(false));
                let err_str = vm.alloc_str("bad argument to 'pcall' (function expected)");
                vm.data_stack.push(err_str);
                return 2;
            }

            let func = args[0];
            let call_args = args[1..].to_vec();

            let call_depth = vm.call_stack.len();
            let data_depth = vm.data_stack.len();
            let handler_depth = vm.handler_stack.len();
            let roots_depth = vm.temp_roots.len();

            let prev_hook = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));

            vm.c_call_depth += 1;
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {

                vm.internal_call(func, call_args);

                let ret_count = vm.multiret_count;
                let mut rets = Vec::new();
                for _ in 0..ret_count {
                    rets.push(vm.data_stack.pop().unwrap());
                }
                rets.reverse();
                rets
            }));
            vm.c_call_depth -= 1;

            std::panic::set_hook(prev_hook);

            match result {
                Ok(rets) => {

                    vm.data_stack.push(Value::bool(true));
                    for r in rets {
                        vm.data_stack.push(r);
                    }
                    1 + vm.multiret_count
                }
                Err(payload) => {

                    vm.call_stack.truncate(call_depth);
                    vm.data_stack.truncate(data_depth);
                    vm.handler_stack.truncate(handler_depth);
                    vm.temp_roots.truncate(roots_depth);

                    let err_val = if let Some(&v) = payload.downcast_ref::<Value>() {
                        v
                    } else {

                        let err_msg = if let Some(s) = payload.downcast_ref::<String>() {
                            s.clone()
                        } else if let Some(s) = payload.downcast_ref::<&str>() {
                            s.to_string()
                        } else {
                            "unknown runtime error".to_string()
                        };
                        vm.alloc_str(&err_msg)
                    };

                    vm.data_stack.push(Value::bool(false));
                    vm.data_stack.push(err_val);
                    2
                }
            }
        }));

        let getfenv_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let mut f_arg = args.get(0).copied().unwrap_or(Value::num(1.0));
            if f_arg.0 == TAG_NIL {
                f_arg = Value::num(1.0);
            }
            let mut target_closure = None;

            if let Some(n) = vm.to_num(f_arg) {
                let level = n as usize;
                if level == 0 {
                    vm.data_stack.push(Value::obj(vm.global_env));
                    return 1;
                }
                if level <= vm.call_stack.len() {
                    target_closure = Some(vm.call_stack[vm.call_stack.len() - level].closure_id);
                } else {
                    vm.runtime_error("invalid level");
                }
            } else if f_arg.is_obj()
                && matches!(
                    vm.objects[f_arg.as_obj() as usize],
                    Some(GcObject::Closure { .. })
                )
            {
                target_closure = Some(f_arg.as_obj());
            } else {
                vm.runtime_error("bad argument #1 to 'getfenv'");
            }

            if let Some(closure_id) = target_closure {
                if let Some(GcObject::Closure {
                    chunk_idx,
                    upvalues,
                }) = &vm.objects[closure_id as usize]
                {
                    let chunk = &vm.chunks[*chunk_idx];
                    for (i, upv) in chunk.upvals.iter().enumerate() {
                        if upv.2 == "_ENV" {

                            if let Some(GcObject::Upval(inner)) = &vm.objects[upvalues[i] as usize]
                            {
                                vm.data_stack.push(*inner);
                                return 1;
                            }
                        }
                    }
                }
            }
            vm.data_stack.push(Value::obj(vm.global_env));
            1
        }));

        let setfenv_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let f_arg = args.get(0).copied().unwrap_or(Value::nil());
            let t_arg = args.get(1).copied().unwrap_or(Value::nil());

            if !t_arg.is_obj()
                || !matches!(
                    vm.objects[t_arg.as_obj() as usize],
                    Some(GcObject::Table(_, _))
                )
            {
                vm.runtime_error("bad argument #2 to 'setfenv' (table expected)");
            }

            let mut target_closure = None;

            if let Some(n) = vm.to_num(f_arg) {
                let level = n as usize;
                if level == 0 {

                    vm.global_env = t_arg.as_obj();
                    return 0;
                }
                if level <= vm.call_stack.len() {
                    target_closure = Some(vm.call_stack[vm.call_stack.len() - level].closure_id);
                } else {
                    vm.runtime_error("invalid level");
                }
            } else if f_arg.is_obj()
                && matches!(
                    vm.objects[f_arg.as_obj() as usize],
                    Some(GcObject::Closure { .. })
                )
            {
                target_closure = Some(f_arg.as_obj());
            } else {
                vm.runtime_error("bad argument #1 to 'setfenv' (number or function expected)");
            }

            if let Some(closure_id) = target_closure {

                let mut env_upval_idx = None;
                if let Some(GcObject::Closure {
                    chunk_idx,
                    upvalues,
                }) = &vm.objects[closure_id as usize]
                {
                    let chunk = &vm.chunks[*chunk_idx];
                    for (i, upv) in chunk.upvals.iter().enumerate() {
                        if upv.2 == "_ENV" {
                            env_upval_idx = Some(i);
                            break;
                        }
                    }
                }

                if let Some(idx) = env_upval_idx {

                    let new_upval_id = vm.alloc(GcObject::Upval(t_arg));
                    if let Some(GcObject::Closure { upvalues, .. }) =
                        &mut vm.objects[closure_id as usize]
                    {
                        upvalues[idx] = new_upval_id;
                    }
                }

                vm.data_stack.push(Value::obj(closure_id));
                return 1;
            }

            0
        }));

        // collectgarbage(opt, [arg])
        let collectgarbage_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let opt = args
                .get(0)
                .map(|v| vm.val_to_str(*v))
                .unwrap_or_else(|| "collect".to_string());

            match opt.as_str() {
                "collect" => {
                    vm.collect_garbage();
                    vm.data_stack.push(Value::num(0.0));
                    1
                }
                "count" => {

                    let kb = vm.bytes_allocated as f64 / 1024.0;
                    vm.data_stack.push(Value::num(kb));
                    1
                }
                "step" => {

                    vm.collect_garbage();
                    vm.data_stack.push(Value::bool(true));
                    1
                }
                _ => {

                    vm.data_stack.push(Value::num(0.0));
                    1
                }
            }
        }));

        // xpcall(f, msgh, [args...])
        let xpcall_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 2 || !args[0].is_obj() || !args[1].is_obj() {
                vm.data_stack.push(Value::bool(false));
                let err_str = vm.alloc_str("bad argument to 'xpcall'");
                vm.data_stack.push(err_str);
                return 2;
            }

            let func = args[0];
            let msgh = args[1];

            let call_args = if args.len() > 2 {
                args[2..].to_vec()
            } else {
                Vec::new()
            };

            let call_depth = vm.call_stack.len();
            let data_depth = vm.data_stack.len();
            let handler_depth = vm.handler_stack.len();
            let roots_depth = vm.temp_roots.len();

            let prev_hook = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));

            vm.c_call_depth += 1;

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                vm.internal_call(func, call_args);
                let ret_count = vm.multiret_count;
                let mut rets = Vec::with_capacity(ret_count);
                for _ in 0..ret_count {
                    rets.push(vm.data_stack.pop().unwrap());
                }
                rets.reverse();
                rets
            }));

            vm.c_call_depth -= 1;
            std::panic::set_hook(prev_hook);

            match result {
                Ok(rets) => {

                    vm.data_stack.push(Value::bool(true));
                    for r in rets {
                        vm.data_stack.push(r);
                    }
                    1 + vm.multiret_count
                }
                Err(payload) => {

                    vm.call_stack.truncate(call_depth);
                    vm.data_stack.truncate(data_depth);
                    vm.handler_stack.truncate(handler_depth);
                    vm.temp_roots.truncate(roots_depth);

                    let err_msg = if let Some(s) = payload.downcast_ref::<String>() {
                        s.clone()
                    } else if let Some(s) = payload.downcast_ref::<&str>() {
                        s.to_string()
                    } else {
                        "unknown runtime error".to_string()
                    };

                    let err_val = if let Some(&v) = payload.downcast_ref::<Value>() {
                        v
                    } else {
                        let err_msg = if let Some(s) = payload.downcast_ref::<String>() {
                            s.clone()
                        } else if let Some(s) = payload.downcast_ref::<&str>() {
                            s.to_string()
                        } else {
                            "unknown runtime error".to_string()
                        };
                        vm.alloc_str(&err_msg)
                    };

                    vm.c_call_depth += 1;
                    let prev_hook = std::panic::take_hook();
                    std::panic::set_hook(Box::new(|_| {}));

                    let msgh_result =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            vm.internal_call(msgh, vec![err_val]);
                            if vm.multiret_count > 0 {
                                let ret = vm.data_stack.pop().unwrap();
                                for _ in 1..vm.multiret_count {
                                    vm.data_stack.pop();
                                }
                                ret
                            } else {
                                Value::nil()
                            }
                        }));

                    std::panic::set_hook(prev_hook);
                    vm.c_call_depth -= 1;

                    vm.data_stack.push(Value::bool(false));
                    match msgh_result {
                        Ok(handler_ret) => {
                            vm.data_stack.push(handler_ret);
                        }
                        Err(_) => {
                            let double_err = vm.alloc_str("error in error handling");
                            vm.data_stack.push(double_err);
                        }
                    }
                    2
                }
            }
        }));

        let rawget_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'rawget' (2 expected)");
            }
            let (t, k) = (args[0], args[1]);

            if t.is_obj() {
                if let Some(GcObject::Table(map, _)) = &vm.objects[t.as_obj() as usize] {
                    let val = map.get(&k).copied().unwrap_or(Value::nil());
                    vm.data_stack.push(val);
                    return 1;
                }
            }
            vm.runtime_error("bad argument #1 to 'rawget' (table expected)");
            0
        }));

        let rawset_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 3 {
                vm.runtime_error("bad argument to 'rawset' (3 expected)");
            }
            let (t, k, v) = (args[0], args[1], args[2]);

            if k.0 == TAG_NIL {
                vm.runtime_error("table index is nil");
            }

            if t.is_obj() {
                if let Some(GcObject::Table(map, _)) = &mut vm.objects[t.as_obj() as usize] {
                    if v.0 == TAG_NIL {
                        map.remove(&k);
                    } else {
                        map.insert(k, v);
                    }
                    vm.data_stack.push(t);
                    return 1;
                }
            }
            vm.runtime_error("bad argument #1 to 'rawset' (table expected)");
            0
        }));

        let rawequal_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'rawequal' (2 expected)");
            }
            let (v1, v2) = (args[0], args[1]);

            let mut is_eq = v1 == v2;

            if !is_eq && v1.is_obj() && v2.is_obj() {
                if let (Some(GcObject::Str(s1)), Some(GcObject::Str(s2))) = (
                    &vm.objects[v1.as_obj() as usize],
                    &vm.objects[v2.as_obj() as usize],
                ) {
                    is_eq = s1 == s2;
                }
            }

            if is_eq && !v1.is_obj() && v1.0 != TAG_NIL && v1.0 != TAG_FALSE && v1.0 != TAG_TRUE {
                if v1.as_num().is_nan() {
                    is_eq = false;
                }
            }

            vm.data_stack.push(Value::bool(is_eq));
            1
        }));

        let gcinfo_fn = self.alloc(GcObject::NativeFn(|vm, _| {
            let kb = vm.bytes_allocated as f64 / 1024.0;
            vm.data_stack.push(Value::num(kb));
            1
        }));

        let newproxy_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let mut mt_id = None;
            if !args.is_empty() {
                let arg = args[0];
                if arg.is_truthy() && arg.0 == TAG_TRUE {

                    let new_mt = vm.alloc(GcObject::Table(HashMap::new(), None));
                    mt_id = Some(new_mt);
                } else if arg.is_obj() {

                    if let Some(GcObject::File(_, mt)) = &vm.objects[arg.as_obj() as usize] {
                        mt_id = *mt;
                    }
                }
            }

            let ud = vm.alloc(GcObject::File(
                std::rc::Rc::new(std::cell::RefCell::new(None)),
                mt_id,
            ));
            vm.data_stack.push(Value::obj(ud));
            1
        }));

        // loadstring(string [, chunkname])
        let loadstring_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'loadstring' (string expected)");
            }
            let source = vm.val_to_str(args[0]);

            if source.starts_with("\x1bLUA_AE_DUMP:") {
                let id_str = &source["\x1bLUA_AE_DUMP:".len()..];
                if let Ok(id) = id_str.parse::<u32>() {

                    vm.data_stack.push(Value::obj(id));
                    return 1;
                }
            }

            match Compiler::compile(vm, &source, "=(load)") {
                Ok(chunk_idx) => {
                    let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                    let closure = vm.alloc(GcObject::Closure {
                        chunk_idx,
                        upvalues: vec![env_upval],
                    });
                    vm.data_stack.push(Value::obj(closure));
                    1
                }
                Err(err) => {
                    vm.data_stack.push(Value::nil());
                    let err_str = vm.alloc_str(&err);
                    vm.data_stack.push(err_str);
                    2
                }
            }
        }));
        // 13. load(func_or_string [, chunkname])
        let load_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'load' (function expected)");
            }
            let chunk_arg = args[0];

            let mut source = String::new();

            if chunk_arg.is_obj()
                && matches!(
                    vm.objects[chunk_arg.as_obj() as usize],
                    Some(GcObject::Str(_))
                )
            {

                source = vm.val_to_str(chunk_arg);
            } else if chunk_arg.is_obj()
                && matches!(
                    vm.objects[chunk_arg.as_obj() as usize],
                    Some(GcObject::Closure { .. })
                        | Some(GcObject::NativeFn(_))
                        | Some(GcObject::NativeClosure(.., _))
                )
            {

                loop {

                    let call_depth = vm.call_stack.len();

                    vm.internal_call(chunk_arg, vec![]);

                    if vm.multiret_count > 0 {
                        let ret = vm.data_stack.pop().unwrap();
                        for _ in 1..vm.multiret_count {
                            vm.data_stack.pop();
                        }

                        if ret.0 == TAG_NIL {
                            break;
                        }
                        let piece = vm.val_to_str(ret);
                        if piece.is_empty() {
                            break;
                        }

                        source.push_str(&piece);
                    } else {
                        break;
                    }
                }
            } else {
                vm.runtime_error("bad argument #1 to 'load' (function or string expected)");
            }

            if source.starts_with("\x1bLUA_AE_DUMP:") {
                let id_str = &source["\x1bLUA_AE_DUMP:".len()..];
                if let Ok(id) = id_str.parse::<u32>() {
                    vm.data_stack.push(Value::obj(id));
                    return 1;
                }
            }

            match Compiler::compile(vm, &source, "=(load)") {
                Ok(chunk_idx) => {
                    let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                    let closure = vm.alloc(GcObject::Closure {
                        chunk_idx,
                        upvalues: vec![env_upval],
                    });
                    vm.data_stack.push(Value::obj(closure));
                    1
                }
                Err(err) => {
                    vm.data_stack.push(Value::nil());
                    let err_str = vm.alloc_str(&err);
                    vm.data_stack.push(err_str);
                    2
                }
            }
        }));

        // loadfile([filename])
        let loadfile_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let mut source = String::new();
            let mut filename = String::from("stdin");

            if args.is_empty() || args[0].0 == TAG_NIL {
                if std::io::Read::read_to_string(&mut std::io::stdin(), &mut source).is_err() {
                    vm.data_stack.push(Value::nil());
                    let err = vm.alloc_str("cannot read from stdin");
                    vm.data_stack.push(err);
                    return 2;
                }
            } else {
                filename = vm.val_to_str(args[0]);
                match std::fs::read_to_string(&filename) {
                    Ok(c) => source = c,
                    Err(_) => {

                        vm.data_stack.push(Value::nil());
                        let err_str = vm.alloc_str(&format!(
                            "cannot open {}: No such file or directory",
                            filename
                        ));
                        vm.data_stack.push(err_str);
                        return 2;
                    }
                }
            }

            match Compiler::compile(vm, &source, &filename) {
                Ok(chunk_idx) => {
                    let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                    let closure = vm.alloc(GcObject::Closure {
                        chunk_idx,
                        upvalues: vec![env_upval],
                    });
                    vm.data_stack.push(Value::obj(closure));
                    1
                }
                Err(err) => {
                    vm.data_stack.push(Value::nil());
                    let err_msg = format!("syntax error in {}: {}", filename, err);
                    let err_str = vm.alloc_str(&err_msg);
                    vm.data_stack.push(err_str);
                    2
                }
            }
        }));

        // dofile([filename])
        let dofile_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let mut source = String::new();
            let mut filename = String::from("=(stdin)");
            if args.is_empty() || args[0].0 == TAG_NIL {
                std::io::Read::read_to_string(&mut std::io::stdin(), &mut source)
                    .unwrap_or_default();
            } else {
                filename = vm.val_to_str(args[0]);
                source = std::fs::read_to_string(&filename)
                    .unwrap_or_else(|_| vm.runtime_error(&format!("cannot open {}", filename)));
            }

            match Compiler::compile(vm, &source, &filename) {

                Ok(chunk_idx) => {
                    let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                    let closure = vm.alloc(GcObject::Closure {
                        chunk_idx,
                        upvalues: vec![env_upval],
                    });
                    let closure_val = Value::obj(closure);
                    vm.internal_call(closure_val, vec![]);
                    vm.multiret_count
                }
                Err(err) => {
                    vm.runtime_error(&err);
                    0
                }
            }
        }));

        // 11. unpack(list [, i [, j]])
        let unpack_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'unpack' (table expected)");
            }
            let t_idx = args[0].as_obj() as usize;

            let i = args.get(1).and_then(|v| vm.to_num(*v)).unwrap_or(1.0) as i64;
            let j = args.get(2).and_then(|v| vm.to_num(*v)).unwrap_or_else(|| {
                // Find max integer key (same logic as your table.maxn)
                let mut max_key = 0;
                if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                    for k in map.keys() {
                        if !k.is_obj() && k.0 != TAG_NIL && k.0 != TAG_FALSE && k.0 != TAG_TRUE {
                            let num = k.as_num();
                            if num.fract() == 0.0 && num > 0.0 {
                                let int_k = num as i64;
                                if int_k > max_key {
                                    max_key = int_k;
                                }
                            }
                        }
                    }
                }
                max_key as f64
            }) as i64;

            if i > j {
                return 0;
            }

            let mut rets = 0;
            if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                for idx in i..=j {
                    let val = map
                        .get(&Value::num(idx as f64))
                        .copied()
                        .unwrap_or(Value::nil());
                    vm.data_stack.push(val);
                    rets += 1;
                }
            }
            rets
        }));

        // 12. select(index, ...)
        let select_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'select' (number expected, got no value)");
            }

            // Check if arg[0] is the "#" string
            if args[0].is_obj() {
                if let Some(GcObject::Str(s)) = &vm.objects[args[0].as_obj() as usize] {
                    if s == "#" {
                        vm.data_stack
                            .push(Value::num((args.len().saturating_sub(1)) as f64));
                        return 1;
                    }
                }
            }

            // Otherwise, it must be a number index
            let mut n = vm.to_num(args[0]).unwrap_or_else(|| {
                vm.runtime_error("bad argument #1 to 'select' (number expected)")
            }) as i64;
            let total_args = (args.len().saturating_sub(1)) as i64;

            if n < 0 {
                n = total_args + n + 1;
            }
            if n < 1 {
                n = 1;
            } // Lua 5.1 truncates values < 1 down to index 1

            let start_idx = n as usize;
            if start_idx > args.len() - 1 {
                return 0;
            }

            let mut rets = 0;
            for idx in start_idx..args.len() {
                vm.data_stack.push(args[idx]);
                rets += 1;
            }
            rets
        }));

        let module_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'module' (string expected)");
            }
            let modname_val = args[0];
            let modname = vm.val_to_str(modname_val);

            let mut current_table = Value::obj(vm.global_env);
            let parts: Vec<&str> = modname.split('.').collect();

            let mut package_name = String::new();
            for (i, part) in parts.iter().enumerate() {
                if i < parts.len() - 1 {
                    package_name.push_str(part);
                    package_name.push('.');
                }

                let part_key = vm.alloc_str(part);
                let mut next_table = Value::nil();

                if let Some(GcObject::Table(map, _)) = &vm.objects[current_table.as_obj() as usize]
                {
                    next_table = map.get(&part_key).copied().unwrap_or(Value::nil());
                }

                if !next_table.is_truthy() {
                    let new_id = vm.alloc(GcObject::Table(HashMap::new(), None));
                    next_table = Value::obj(new_id);
                    if let Some(GcObject::Table(map, _)) =
                        &mut vm.objects[current_table.as_obj() as usize]
                    {
                        map.insert(part_key, next_table);
                    }
                } else if !next_table.is_obj()
                    || !matches!(
                        vm.objects[next_table.as_obj() as usize],
                        Some(GcObject::Table(..))
                    )
                {
                    vm.runtime_error(&format!("name conflict for module '{}'", modname));
                }

                current_table = next_table;
            }

            let module_table = current_table;

            let name_key = vm.alloc_str("_NAME");
            let m_key = vm.alloc_str("_M");
            let package_key = vm.alloc_str("_PACKAGE");

            let package_val = vm.alloc_str(&package_name);

            if let Some(GcObject::Table(map, _)) = &mut vm.objects[module_table.as_obj() as usize] {
                map.insert(name_key, modname_val);
                map.insert(m_key, module_table);
                map.insert(package_key, package_val);
            }

            let pkg_val = vm.get_global("package");
            if pkg_val.is_obj() {
                let loaded_key = vm.alloc_str("loaded");
                let loaded_tab_val =
                    if let Some(GcObject::Table(map, _)) = &vm.objects[pkg_val.as_obj() as usize] {
                        map.get(&loaded_key).copied().unwrap_or(Value::nil())
                    } else {
                        Value::nil()
                    };

                if loaded_tab_val.is_obj() {
                    if let Some(GcObject::Table(map, _)) =
                        &mut vm.objects[loaded_tab_val.as_obj() as usize]
                    {
                        map.insert(modname_val, module_table);
                    }
                }
            }

            if let Some(frame) = vm.call_stack.last() {
                let closure_id = frame.closure_id;
                let mut env_upval_idx = None;
                if let Some(GcObject::Closure { chunk_idx, .. }) = &vm.objects[closure_id as usize]
                {
                    let chunk = &vm.chunks[*chunk_idx];
                    for (i, upv) in chunk.upvals.iter().enumerate() {
                        if upv.2 == "_ENV" {
                            env_upval_idx = Some(i);
                            break;
                        }
                    }
                }

                if let Some(idx) = env_upval_idx {
                    let new_upval_id = vm.alloc(GcObject::Upval(module_table));
                    if let Some(GcObject::Closure { upvalues, .. }) =
                        &mut vm.objects[closure_id as usize]
                    {
                        upvalues[idx] = new_upval_id;
                    }
                }
            }

            let call_args = args[1..].to_vec();
            for arg in call_args {
                vm.internal_call(arg, vec![module_table]);
                for _ in 0..vm.multiret_count {
                    vm.data_stack.pop();
                }
            }

            0
        }));

        let globals = vec![
            ("type", type_fn),
            ("error", error_fn),
            ("__print", print_fn),
            ("assert", assert_fn),
            ("tonumber", tonumber_fn),
            ("tostring", tostring_fn),
            ("setmetatable", setmetatable_fn),
            ("getmetatable", getmetatable_fn),
            ("next", next_fn),
            ("pairs", pairs_fn),
            ("ipairs", ipairs_fn),
            ("loadstring", loadstring_fn),
            ("pcall", pcall_fn),
            ("getfenv", getfenv_fn),
            ("setfenv", setfenv_fn),
            ("collectgarbage", collectgarbage_fn),
            ("xpcall", xpcall_fn),
            ("rawget", rawget_fn),
            ("rawset", rawset_fn),
            ("rawequal", rawequal_fn),
            ("gcinfo", gcinfo_fn),
            ("newproxy", newproxy_fn),
            ("loadstring", loadstring_fn),
            ("loadfile", loadfile_fn),
            ("dofile", dofile_fn),
            ("unpack", unpack_fn),
            ("select", select_fn),
            ("load", load_fn),
            ("module", module_fn),
        ];
        for (name, id) in globals {
            self.set_global(name, Value::obj(id));
        }
        let raw_print_fn = Value::obj(self.alloc(GcObject::NativeFn(|vm, args| {
            let s = args.get(0).map(|v| vm.val_to_str(*v)).unwrap_or_default();
            println!("{}", s);
            0
        })));
        self.set_global("__raw_print", raw_print_fn);
    }
    fn open_math_lib(&mut self) {
        let mut math_map = HashMap::new();

        fn get_num(vm: &mut VM, args: &[Value], idx: usize, func_name: &str) -> f64 {
            let val = args.get(idx).copied().unwrap_or(Value::nil());
            if let Some(n) = vm.to_num(val) {
                return n;
            }
            vm.runtime_error(&format!(
                "bad argument #{} to '{}' (number expected)",
                idx + 1,
                func_name
            ));
        }

        self.register_method(&mut math_map, "abs", |vm, args| {
            let n = get_num(vm, &args, 0, "abs").abs();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "floor", |vm, args| {
            let n = get_num(vm, &args, 0, "floor").floor();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "ceil", |vm, args| {
            let n = get_num(vm, &args, 0, "ceil").ceil();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "sqrt", |vm, args| {
            let n = get_num(vm, &args, 0, "sqrt").sqrt();
            vm.data_stack.push(Value::num(n));
            1
        });

        self.register_method(&mut math_map, "sin", |vm, args| {
            let n = get_num(vm, &args, 0, "sin").sin();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "cos", |vm, args| {
            let n = get_num(vm, &args, 0, "cos").cos();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "tan", |vm, args| {
            let n = get_num(vm, &args, 0, "tan").tan();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "asin", |vm, args| {
            let n = get_num(vm, &args, 0, "asin").asin();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "acos", |vm, args| {
            let n = get_num(vm, &args, 0, "acos").acos();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "atan", |vm, args| {
            let n = get_num(vm, &args, 0, "atan").atan();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "atan2", |vm, args| {
            let y = get_num(vm, &args, 0, "atan2");
            let x = get_num(vm, &args, 1, "atan2");
            vm.data_stack.push(Value::num(y.atan2(x)));
            1
        });
        self.register_method(&mut math_map, "sinh", |vm, args| {
            let n = get_num(vm, &args, 0, "sinh").sinh();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "cosh", |vm, args| {
            let n = get_num(vm, &args, 0, "cosh").cosh();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "tanh", |vm, args| {
            let n = get_num(vm, &args, 0, "tanh").tanh();
            vm.data_stack.push(Value::num(n));
            1
        });

        self.register_method(&mut math_map, "exp", |vm, args| {
            let n = get_num(vm, &args, 0, "exp").exp();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "log", |vm, args| {
            let n = get_num(vm, &args, 0, "log").ln();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "log10", |vm, args| {
            let n = get_num(vm, &args, 0, "log10").log10();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "pow", |vm, args| {
            let x = get_num(vm, &args, 0, "pow");
            let y = get_num(vm, &args, 1, "pow");
            vm.data_stack.push(Value::num(x.powf(y)));
            1
        });

        self.register_method(&mut math_map, "deg", |vm, args| {
            let n = get_num(vm, &args, 0, "deg").to_degrees();
            vm.data_stack.push(Value::num(n));
            1
        });
        self.register_method(&mut math_map, "rad", |vm, args| {
            let n = get_num(vm, &args, 0, "rad").to_radians();
            vm.data_stack.push(Value::num(n));
            1
        });

        self.register_method(&mut math_map, "fmod", |vm, args| {
            let x = get_num(vm, &args, 0, "fmod");
            let y = get_num(vm, &args, 1, "fmod");
            vm.data_stack.push(Value::num(x % y));
            1
        });
        self.register_method(&mut math_map, "mod", |vm, args| {
            let x = get_num(vm, &args, 0, "mod");
            let y = get_num(vm, &args, 1, "mod");
            vm.data_stack.push(Value::num(x % y));
            1
        });
        self.register_method(&mut math_map, "modf", |vm, args| {
            let x = get_num(vm, &args, 0, "modf");
            vm.data_stack.push(Value::num(x.trunc()));
            vm.data_stack.push(Value::num(x.fract()));
            2
        });

        // Min / Max
        self.register_method(&mut math_map, "max", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument to 'max'");
            }
            let mut max_v = get_num(vm, &args, 0, "max");
            for i in 1..args.len() {
                let v = get_num(vm, &args, i, "max");
                if v > max_v {
                    max_v = v;
                }
            }
            vm.data_stack.push(Value::num(max_v));
            1
        });
        self.register_method(&mut math_map, "min", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument to 'min'");
            }
            let mut min_v = get_num(vm, &args, 0, "min");
            for i in 1..args.len() {
                let v = get_num(vm, &args, i, "min");
                if v < min_v {
                    min_v = v;
                }
            }
            vm.data_stack.push(Value::num(min_v));
            1
        });

        self.register_method(&mut math_map, "random", |vm, args| {

            vm.rng_state = vm
                .rng_state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1);
            let r = (vm.rng_state >> 32) as u32;
            let float_rand = (r as f64) / (u32::MAX as f64 + 1.0);

            if args.is_empty() {
                vm.data_stack.push(Value::num(float_rand));
            } else if args.len() == 1 {
                let m = get_num(vm, &args, 0, "random").floor();
                if m < 1.0 {
                    vm.runtime_error("bad argument #1 to 'random' (interval is empty)");
                }
                vm.data_stack
                    .push(Value::num((float_rand * m).floor() + 1.0));
            } else {
                let m = get_num(vm, &args, 0, "random").floor();
                let n = get_num(vm, &args, 1, "random").floor();
                if m > n {
                    vm.runtime_error("bad argument #2 to 'random' (interval is empty)");
                }
                vm.data_stack
                    .push(Value::num((float_rand * (n - m + 1.0)).floor() + m));
            }
            1
        });

        self.register_method(&mut math_map, "randomseed", |vm, args| {
            let seed = get_num(vm, &args, 0, "randomseed");
            vm.rng_state = seed.to_bits();
            0
        });

        self.register_method(&mut math_map, "frexp", |vm, args| {
            let x = get_num(vm, &args, 0, "frexp");
            if x == 0.0 || x.is_nan() || x.is_infinite() {

                vm.data_stack.push(Value::num(x));
                vm.data_stack.push(Value::num(0.0));
            } else {

                let mut e = (x.abs().log2().floor() + 1.0) as i32;
                let mut m = x * 2.0f64.powi(-e);

                if m.abs() >= 1.0 {
                    m *= 0.5;
                    e += 1;
                } else if m.abs() < 0.5 {
                    m *= 2.0;
                    e -= 1;
                }

                vm.data_stack.push(Value::num(m));
                vm.data_stack.push(Value::num(e as f64));
            }

            2
        });

        self.register_method(&mut math_map, "ldexp", |vm, args| {
            let m = get_num(vm, &args, 0, "ldexp");
            let e = get_num(vm, &args, 1, "ldexp");
            vm.data_stack.push(Value::num(m * 2.0f64.powf(e)));
            1
        });

        let pi_key = self.alloc_str("pi");
        let huge_key = self.alloc_str("huge");
        math_map.insert(pi_key, Value::num(std::f64::consts::PI));
        math_map.insert(huge_key, Value::num(std::f64::INFINITY));

        let math_table = self.alloc(GcObject::Table(math_map, None));
        self.set_global("math", Value::obj(math_table));
    }
    fn open_table_lib(&mut self) {
        let mut table_map = HashMap::new();

        fn get_max_key(vm: &VM, t_idx: usize) -> i64 {
            let mut max_key = 0;
            if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                for k in map.keys() {
                    if !k.is_obj() && k.0 != TAG_NIL && k.0 != TAG_FALSE && k.0 != TAG_TRUE {
                        let num = k.as_num();
                        if num.fract() == 0.0 && num > 0.0 {
                            let int_k = num as i64;
                            if int_k > max_key {
                                max_key = int_k;
                            }
                        }
                    }
                }
            }
            max_key
        }

        // table.insert(t, [pos,] value)
        self.register_method(&mut table_map, "insert", |vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'table.insert'");
            }
            let t_val = args[0];
            if !t_val.is_obj() {
                vm.runtime_error("bad argument #1 to 'table.insert' (table expected)");
            }

            let t_idx = t_val.as_obj() as usize;
            let len = get_max_key(vm, t_idx);

            let (pos, val) = if args.len() == 2 {
                (len + 1, args[1])
            } else {
                (args[1].as_num() as i64, args[2])
            };

            if let Some(GcObject::Table(map, _)) = &mut vm.objects[t_idx] {

                for i in (pos..=len).rev() {
                    if let Some(v) = map.remove(&Value::num(i as f64)) {
                        map.insert(Value::num((i + 1) as f64), v);
                    }
                }
                map.insert(Value::num(pos as f64), val);
            }
            0
        });

        // table.remove(t, [pos])
        self.register_method(&mut table_map, "remove", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'table.remove'");
            }
            let t_idx = args[0].as_obj() as usize;
            let len = get_max_key(vm, t_idx);
            let pos = if args.len() > 1 {
                args[1].as_num() as i64
            } else {
                len
            };

            let mut removed_val = Value::nil();
            if let Some(GcObject::Table(map, _)) = &mut vm.objects[t_idx] {
                if let Some(v) = map.remove(&Value::num(pos as f64)) {
                    removed_val = v;
                }

                for i in (pos + 1)..=len {
                    if let Some(v) = map.remove(&Value::num(i as f64)) {
                        map.insert(Value::num((i - 1) as f64), v);
                    }
                }
            }
            vm.data_stack.push(removed_val);
            1
        });

        // table.concat(t, [sep, i, j])
        self.register_method(&mut table_map, "concat", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'table.concat'");
            }
            let t_idx = args[0].as_obj() as usize;
            let len = get_max_key(vm, t_idx);

            // use `vm.to_num` safely to fall back or extract indices securely
            let sep = if args.len() > 1 && args[1].0 != TAG_NIL {
                vm.val_to_str(args[1])
            } else {
                "".to_string()
            };
            let start = if args.len() > 2 && args[2].0 != TAG_NIL {
                vm.to_num(args[2]).unwrap_or(1.0) as i64
            } else {
                1
            };
            let end = if args.len() > 3 && args[3].0 != TAG_NIL {
                vm.to_num(args[3]).unwrap_or(len as f64) as i64
            } else {
                len
            };

            let mut result = String::new();
            if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                for i in start..=end {
                    if i > start {
                        result.push_str(&sep);
                    }

                    let val = map
                        .get(&Value::num(i as f64))
                        .copied()
                        .unwrap_or(Value::nil());

                    if val.0 == TAG_NIL {
                        vm.runtime_error(&format!(
                            "invalid value (nil) at index {} in table for 'concat'",
                            i
                        ));
                    } else if !val.is_obj() && val.0 != TAG_FALSE && val.0 != TAG_TRUE {
                        result.push_str(&val.as_num().to_string());
                    } else if val.is_obj() {
                        match &vm.objects[val.as_obj() as usize].as_ref().unwrap() {
                            GcObject::Str(s) => result.push_str(s),
                            GcObject::Table(..) => vm.runtime_error(&format!(
                                "invalid value (table) at index {} in table for 'concat'",
                                i
                            )),
                            GcObject::Closure { .. } | GcObject::NativeFn(_) => {
                                vm.runtime_error(&format!(
                                    "invalid value (function) at index {} in table for 'concat'",
                                    i
                                ))
                            }
                            GcObject::Continuation { .. } | GcObject::Thread(_) => vm
                                .runtime_error(&format!(
                                    "invalid value (thread) at index {} in table for 'concat'",
                                    i
                                )),
                            _ => vm.runtime_error(&format!(
                                "invalid value (userdata) at index {} in table for 'concat'",
                                i
                            )),
                        }
                    } else {
                        vm.runtime_error(&format!(
                            "invalid value (boolean) at index {} in table for 'concat'",
                            i
                        ));
                    }
                }
            }
            let str_val = vm.alloc_str(&result);
            vm.data_stack.push(str_val);
            1
        });

        // table.sort(t, [comp])

        self.register_method(&mut table_map, "sort", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'table.sort'");
            }
            let t_idx = args[0].as_obj() as usize;
            let len = get_max_key(vm, t_idx);

            let mut array_vals = Vec::with_capacity(len as usize);
            if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                for i in 1..=len {
                    array_vals.push(
                        map.get(&Value::num(i as f64))
                            .copied()
                            .unwrap_or(Value::nil()),
                    );
                }
            }

            let has_comp = args.len() > 1 && args[1].is_truthy();
            let comp_fn = if has_comp { args[1] } else { Value::nil() };

            array_vals.sort_by(|a, b| {
                if has_comp {

                    vm.internal_call(comp_fn, vec![*a, *b]);

                    let mut res = Value::bool(false);
                    if vm.multiret_count > 0 {
                        res = vm.data_stack.pop().unwrap();
                        for _ in 1..vm.multiret_count {
                            vm.data_stack.pop();
                        }
                    }

                    if res.is_truthy() {
                        std::cmp::Ordering::Less
                    } else {
                        std::cmp::Ordering::Greater
                    }
                } else {

                    let a_is_str = a.is_obj()
                        && matches!(&vm.objects[a.as_obj() as usize], Some(GcObject::Str(_)));
                    let b_is_str = b.is_obj()
                        && matches!(&vm.objects[b.as_obj() as usize], Some(GcObject::Str(_)));

                    if a_is_str && b_is_str {

                        let str_a = vm.val_to_str(*a);
                        let str_b = vm.val_to_str(*b);
                        str_a.cmp(&str_b)
                    }

                    else if let (Some(num_a), Some(num_b)) = (vm.to_num(*a), vm.to_num(*b)) {
                        num_a
                            .partial_cmp(&num_b)
                            .unwrap_or(std::cmp::Ordering::Equal)
                    }

                    else {
                        let mm_a = vm.get_metamethod(*a, "__lt");
                        let mm_b = vm.get_metamethod(*b, "__lt");

                        if let (Some(func_a), Some(func_b)) = (mm_a, mm_b) {

                            if func_a == func_b {
                                vm.internal_call(func_a, vec![*a, *b]);

                                let mut res = Value::bool(false);
                                if vm.multiret_count > 0 {
                                    res = vm.data_stack.pop().unwrap();
                                    for _ in 1..vm.multiret_count {
                                        vm.data_stack.pop();
                                    }
                                }

                                if res.is_truthy() {
                                    std::cmp::Ordering::Less
                                } else {
                                    std::cmp::Ordering::Greater
                                }
                            } else {
                                vm.runtime_error(
                                    "attempt to compare uncomparable types in table.sort",
                                );
                                std::cmp::Ordering::Equal
                            }
                        } else {
                            vm.runtime_error("attempt to compare uncomparable types in table.sort");
                            std::cmp::Ordering::Equal
                        }
                    }
                }
            });

            if let Some(GcObject::Table(map, _)) = &mut vm.objects[t_idx] {
                for (i, val) in array_vals.into_iter().enumerate() {
                    map.insert(Value::num((i + 1) as f64), val);
                }
            }
            0
        });

        self.register_method(&mut table_map, "maxn", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'table.maxn' (table expected)");
            }

            let mut max_k = 0.0f64;
            if let Some(GcObject::Table(map, _)) = &vm.objects[args[0].as_obj() as usize] {
                for k in map.keys() {

                    if !k.is_obj() && k.0 != TAG_NIL && k.0 != TAG_FALSE && k.0 != TAG_TRUE {
                        let num = k.as_num();

                        if num > max_k {
                            max_k = num;
                        }
                    }
                }
            }

            vm.data_stack.push(Value::num(max_k));
            1
        });

        self.register_method(&mut table_map, "getn", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'table.getn'");
            }

            let max_k = get_max_key(vm, args[0].as_obj() as usize);
            vm.data_stack.push(Value::num(max_k as f64));
            1
        });

        // table.foreach(t, f)
        self.register_method(&mut table_map, "foreach", |vm, args| {
            if args.len() < 2 || !args[0].is_obj() || !args[1].is_obj() {
                vm.runtime_error("bad argument to 'foreach' (table and function expected)");
            }
            let (t, f) = (args[0], args[1]);

            let mut kv_pairs = Vec::new();
            if let Some(GcObject::Table(map, _)) = &vm.objects[t.as_obj() as usize] {
                for (&k, &v) in map.iter() {
                    kv_pairs.push((k, v));
                }
            }

            kv_pairs.sort_by(|(k1, _), (k2, _)| k1.0.cmp(&k2.0));

            for (k, v) in kv_pairs {
                vm.internal_call(f, vec![k, v]);

                if vm.multiret_count > 0 {
                    let ret = vm.data_stack.pop().unwrap();
                    for _ in 1..vm.multiret_count {
                        vm.data_stack.pop();
                    }

                    if ret.0 != TAG_NIL {
                        vm.data_stack.push(ret);
                        return 1;
                    }
                }
            }

            vm.data_stack.push(Value::nil());
            1
        });

        // table.foreachi(t, f)
        self.register_method(&mut table_map, "foreachi", |vm, args| {
            if args.len() < 2 || !args[0].is_obj() || !args[1].is_obj() {
                vm.runtime_error("bad argument to 'foreachi' (table and function expected)");
            }
            let (t, f) = (args[0], args[1]);
            let t_idx = t.as_obj() as usize;

            let max_k = get_max_key(vm, t_idx);

            for i in 1..=max_k {
                let k = Value::num(i as f64);
                let v = if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                    map.get(&k).copied().unwrap_or(Value::nil())
                } else {
                    Value::nil()
                };

                vm.internal_call(f, vec![k, v]);

                if vm.multiret_count > 0 {
                    let ret = vm.data_stack.pop().unwrap();
                    for _ in 1..vm.multiret_count {
                        vm.data_stack.pop();
                    }

                    if ret.0 != TAG_NIL {
                        vm.data_stack.push(ret);
                        return 1;
                    }
                }
            }

            vm.data_stack.push(Value::nil());
            1
        });

        let table_table = self.alloc(GcObject::Table(table_map, None));
        self.set_global("table", Value::obj(table_table));
    }
    fn open_string_lib(&mut self) {
        let mut string_map = HashMap::new();

        fn get_str_arg(vm: &mut VM, args: &[Value], idx: usize, func_name: &str) -> String {
            if let Some(&val) = args.get(idx) {
                if val.is_obj() {
                    if let Some(GcObject::Str(s)) = &vm.objects[val.as_obj() as usize] {
                        return s.clone();
                    }
                } else if val.0 != TAG_NIL && val.0 != TAG_TRUE && val.0 != TAG_FALSE {
                    if let Some(n) = vm.to_num(val) {
                        return n.to_string();
                    }
                }
            }
            let type_name = if let Some(&v) = args.get(idx) {
                if v.0 == TAG_NIL {
                    "nil"
                } else if v.0 == TAG_TRUE || v.0 == TAG_FALSE {
                    "boolean"
                } else {
                    "value"
                }
            } else {
                "no value"
            };
            vm.runtime_error(&format!(
                "bad argument #{} to '{}' (string expected, got {})",
                idx + 1,
                func_name,
                type_name
            ));
            String::new()
        }

        fn get_num_arg(
            vm: &mut VM,
            args: &[Value],
            idx: usize,
            default: Option<f64>,
            func_name: &str,
        ) -> f64 {
            if let Some(&val) = args.get(idx) {
                if val.0 == TAG_NIL {
                    if let Some(def) = default {
                        return def;
                    }
                } else {
                    if let Some(n) = vm.to_num(val) {
                        return n;
                    } else if val.is_obj() {
                        if let Some(GcObject::Str(s)) = &vm.objects[val.as_obj() as usize] {
                            if let Ok(n) = s.parse::<f64>() {
                                return n;
                            }
                        }
                    }
                }
                vm.runtime_error(&format!(
                    "bad argument #{} to '{}' (number expected)",
                    idx + 1,
                    func_name
                ));
            }
            if let Some(def) = default {
                return def;
            }
            vm.runtime_error(&format!(
                "bad argument #{} to '{}' (number expected)",
                idx + 1,
                func_name
            ));
            0.0
        }

        const L_ESC: char = '%';

        struct MatchState<'a> {
            src: &'a [char],
            p: &'a [char],
            captures: Vec<(usize, isize)>, // (start, len). len < 0 means unfinished
        }

        impl<'a> MatchState<'a> {
            fn new(src: &'a [char], p: &'a [char]) -> Self {
                Self {
                    src,
                    p,
                    captures: Vec::new(),
                }
            }

            fn check_capture(&self, l: char) -> Result<usize, String> {
                let idx = (l as u32 - '1' as u32) as usize;
                if idx >= self.captures.len() || self.captures[idx].1 < 0 {
                    return Err(format!("invalid capture index %{}", l));
                }
                Ok(idx)
            }

            fn match_class(c: char, cl: char) -> bool {
                let res = match cl.to_ascii_lowercase() {
                    'a' => c.is_ascii_alphabetic(),
                    'c' => c.is_ascii_control(),
                    'd' => c.is_ascii_digit(),
                    'l' => c.is_ascii_lowercase(),
                    'p' => c.is_ascii_punctuation(),
                    's' => c.is_ascii_whitespace(),
                    'u' => c.is_ascii_uppercase(),
                    'w' => c.is_ascii_alphanumeric(),
                    'x' => c.is_ascii_hexdigit(),
                    'z' => c == '\0',
                    _ => return c == cl,
                };
                if cl.is_ascii_uppercase() {
                    !res
                } else {
                    res
                }
            }

            fn match_bracketclass(&self, c: char, p_idx: usize, ep_idx: usize) -> bool {
                let mut sig = true;
                let mut p = p_idx + 1;
                if self.p[p] == '^' {
                    sig = false;
                    p += 1;
                }
                while p < ep_idx {
                    if self.p[p] == L_ESC {
                        p += 1;
                        if Self::match_class(c, self.p[p]) {
                            return sig;
                        }
                    } else if self.p.get(p + 1) == Some(&'-') && p + 2 < ep_idx {
                        p += 2;
                        if self.p[p - 2] <= c && c <= self.p[p] {
                            return sig;
                        }
                    } else if self.p[p] == c {
                        return sig;
                    }
                    p += 1;
                }
                !sig
            }

            fn single_match(&self, c: char, p_idx: usize, ep_idx: usize) -> bool {
                match self.p[p_idx] {
                    '.' => true,
                    L_ESC => Self::match_class(c, self.p[p_idx + 1]),
                    '[' => self.match_bracketclass(c, p_idx, ep_idx - 1),
                    _ => self.p[p_idx] == c,
                }
            }

            fn class_end(&self, mut p: usize) -> Result<usize, String> {
                match self.p[p] {
                    L_ESC => {
                        if p + 1 == self.p.len() {
                            return Err("malformed pattern (ends with '%')".to_string());
                        }
                        Ok(p + 2)
                    }
                    '[' => {
                        p += 1;
                        if p < self.p.len() && self.p[p] == '^' {
                            p += 1;
                        }
                        if p < self.p.len() && self.p[p] == ']' {
                            p += 1;
                        } // Skip first ']'
                        while p < self.p.len() && self.p[p] != ']' {
                            if self.p[p] == L_ESC && p + 1 < self.p.len() {
                                p += 1;
                            }
                            p += 1;
                        }
                        if p == self.p.len() {
                            return Err("malformed pattern (missing ']')".to_string());
                        }
                        Ok(p + 1)
                    }
                    _ => Ok(p + 1),
                }
            }

            fn match_balance(&self, mut s: usize, p: usize) -> Result<Option<usize>, String> {

                if p + 3 >= self.p.len() {
                    return Err("malformed pattern (missing arguments to '%b')".to_string());
                }

                let b = self.p[p + 2];
                let e = self.p[p + 3];

                if s >= self.src.len() || self.src[s] != b {
                    return Ok(None);
                }

                let mut cont = 1;
                s += 1;
                while s < self.src.len() {
                    if self.src[s] == e {
                        cont -= 1;
                        if cont == 0 {
                            return Ok(Some(s + 1));
                        }
                    } else if self.src[s] == b {
                        cont += 1;
                    }
                    s += 1;
                }
                Ok(None)
            }

            fn max_expand(
                &mut self,
                s: usize,
                p: usize,
                ep: usize,
            ) -> Result<Option<usize>, String> {
                let mut i = 0;
                while s + i < self.src.len() && self.single_match(self.src[s + i], p, ep) {
                    i += 1;
                }
                while i > 0 {
                    if let Some(res) = self.match_impl(s + i, ep + 1)? {
                        return Ok(Some(res));
                    }
                    i -= 1;
                }
                self.match_impl(s, ep + 1)
            }

            fn min_expand(
                &mut self,
                mut s: usize,
                p: usize,
                ep: usize,
            ) -> Result<Option<usize>, String> {
                loop {
                    if let Some(res) = self.match_impl(s, ep + 1)? {
                        return Ok(Some(res));
                    }
                    if s < self.src.len() && self.single_match(self.src[s], p, ep) {
                        s += 1;
                    } else {
                        break;
                    }
                }
                Ok(None)
            }

            fn start_capture(
                &mut self,
                s: usize,
                p: usize,
                what: isize,
            ) -> Result<Option<usize>, String> {
                let level = self.captures.len();
                self.captures.push((s, what));
                let res = self.match_impl(s, p);
                if let Ok(None) = res {
                    self.captures.pop();
                }
                res
            }

            fn end_capture(&mut self, s: usize, p: usize) -> Result<Option<usize>, String> {
                let l = self
                    .captures
                    .iter()
                    .rposition(|c| c.1 == -1)
                    .ok_or("invalid pattern capture")?;
                self.captures[l].1 = (s - self.captures[l].0) as isize;
                let res = self.match_impl(s, p);
                if let Ok(None) = res {
                    self.captures[l].1 = -1;
                }
                res
            }

            fn match_impl(&mut self, mut s: usize, mut p: usize) -> Result<Option<usize>, String> {
                loop {
                    if p >= self.p.len() {
                        return Ok(Some(s));
                    }
                    match self.p[p] {
                        '(' => {
                            if p + 1 < self.p.len() && self.p[p + 1] == ')' {
                                return self.start_capture(s, p + 2, -2); // Position capture
                            } else {
                                return self.start_capture(s, p + 1, -1);
                            }
                        }
                        ')' => {
                            return self.end_capture(s, p + 1);
                        }
                        '$' if p + 1 == self.p.len() => {
                            return if s == self.src.len() {
                                Ok(Some(s))
                            } else {
                                Ok(None)
                            };
                        }
                        L_ESC => match self.p.get(p + 1) {
                            Some('b') => {
                                if let Some(next_s) = self.match_balance(s, p)? {
                                    s = next_s;
                                    p += 4;
                                    continue;
                                } else {
                                    return Ok(None);
                                }
                            }
                            Some('f') => {
                                p += 2;
                                if self.p.get(p) != Some(&'[') {
                                    return Err("missing '[' after '%f' in pattern".to_string());
                                }
                                let ep = self.class_end(p)?;
                                let previous = if s == 0 { '\0' } else { self.src[s - 1] };
                                let current = if s == self.src.len() {
                                    '\0'
                                } else {
                                    self.src[s]
                                };
                                if self.match_bracketclass(previous, p, ep - 1)
                                    || !self.match_bracketclass(current, p, ep - 1)
                                {
                                    return Ok(None);
                                }
                                p = ep;
                                continue;
                            }
                            Some(c) if c.is_ascii_digit() => {
                                let l = self.check_capture(*c)?;
                                let cap_s = self.captures[l].0;
                                let cap_l = self.captures[l].1 as usize;
                                if s + cap_l > self.src.len()
                                    || &self.src[s..s + cap_l] != &self.src[cap_s..cap_s + cap_l]
                                {
                                    return Ok(None);
                                }
                                s += cap_l;
                                p += 2;
                                continue;
                            }
                            _ => {}
                        },
                        _ => {}
                    }

                    let ep = self.class_end(p)?;
                    let m = s < self.src.len() && self.single_match(self.src[s], p, ep);
                    match self.p.get(ep) {
                        Some('?') => {
                            if m {
                                if let Some(res) = self.match_impl(s + 1, ep + 1)? {
                                    return Ok(Some(res));
                                }
                            }
                            s = s;
                            p = ep + 1;
                            continue;
                        }
                        Some('*') => {
                            return self.max_expand(s, p, ep);
                        }
                        Some('+') => {
                            return if m {
                                self.max_expand(s + 1, p, ep)
                            } else {
                                Ok(None)
                            };
                        }
                        Some('-') => {
                            return self.min_expand(s, p, ep);
                        }
                        _ => {
                            if m {
                                s += 1;
                                p = ep;
                                continue;
                            } else {
                                return Ok(None);
                            }
                        }
                    }
                }
            }
        }

        self.register_method(&mut string_map, "find", |vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'find'");
            }
            let s = get_str_arg(vm, &args, 0, "find");
            let pattern = get_str_arg(vm, &args, 1, "find");
            let mut init = get_num_arg(vm, &args, 2, Some(1.0), "find") as i64;
            let plain = if args.len() > 3 {
                args[3].is_truthy()
            } else {
                false
            };

            let s_chars: Vec<char> = s.chars().collect();
            let p_chars: Vec<char> = pattern.chars().collect();
            let len = s_chars.len() as i64;

            if init < 0 {
                init = len + init + 1;
            }
            if init < 1 {
                init = 1;
            }
            let start_idx = (init - 1).min(len) as usize;
            let has_magic = p_chars.iter().any(|&c| "^$()%.[]*+-?".contains(c));

            if plain || !has_magic {
                if p_chars.is_empty() {
                    if init > len + 1 {
                        vm.data_stack.push(Value::nil());
                        return 1;
                    }
                    vm.data_stack.push(Value::num((start_idx + 1) as f64));
                    vm.data_stack.push(Value::num(start_idx as f64));
                    return 2;
                }
                if let Some(pos) = s_chars[start_idx..]
                    .windows(p_chars.len())
                    .position(|w| w == p_chars)
                {
                    let actual_pos = start_idx + pos;
                    vm.data_stack.push(Value::num((actual_pos + 1) as f64));
                    vm.data_stack
                        .push(Value::num((actual_pos + p_chars.len()) as f64));
                    return 2;
                }
            } else {
                let anchor = p_chars.first() == Some(&'^');
                let p_slice = if anchor { &p_chars[1..] } else { &p_chars[..] };

                let mut i = start_idx;
                while i <= s_chars.len() {
                    let mut ms = MatchState::new(&s_chars, p_slice);
                    match ms.match_impl(i, 0) {
                        Ok(Some(end)) => {
                            vm.data_stack.push(Value::num((i + 1) as f64));
                            vm.data_stack.push(Value::num(end as f64));
                            let cap_count = ms.captures.len();
                            for cap in ms.captures {
                                if cap.1 == -2 {
                                    vm.data_stack.push(Value::num((cap.0 + 1) as f64));
                                } else {
                                    let cap_str: String =
                                        s_chars[cap.0..cap.0 + cap.1 as usize].iter().collect();
                                    let cv = vm.alloc_str(&cap_str);
                                    vm.data_stack.push(cv);
                                }
                            }
                            return 2 + cap_count;
                        }
                        Err(e) => vm.runtime_error(&e),
                        _ => {}
                    }
                    if anchor {
                        break;
                    }
                    i += 1;
                }
            }
            vm.data_stack.push(Value::nil());
            1
        });

        self.register_method(&mut string_map, "match", |vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'match'");
            }
            let s = get_str_arg(vm, &args, 0, "match");
            let pattern = get_str_arg(vm, &args, 1, "match");
            let init = get_num_arg(vm, &args, 2, Some(1.0), "match") as i64;

            let s_chars: Vec<char> = s.chars().collect();
            let p_chars: Vec<char> = pattern.chars().collect();
            let len = s_chars.len() as i64;
            let start_idx = (if init < 0 {
                (len + init + 1).max(1)
            } else {
                init.max(1)
            } - 1)
                .min(len) as usize;

            let anchor = p_chars.first() == Some(&'^');
            let p_slice = if anchor { &p_chars[1..] } else { &p_chars[..] };

            let mut i = start_idx;
            while i <= s_chars.len() {
                let mut ms = MatchState::new(&s_chars, p_slice);
                match ms.match_impl(i, 0) {
                    Ok(Some(end)) => {
                        if ms.captures.is_empty() {
                            let whole_match: String = s_chars[i..end].iter().collect();
                            let sv = vm.alloc_str(&whole_match);
                            vm.data_stack.push(sv);
                            return 1;
                        } else {
                            let cap_count = ms.captures.len();
                            for cap in ms.captures {
                                if cap.1 == -2 {
                                    vm.data_stack.push(Value::num((cap.0 + 1) as f64));
                                } else {
                                    let cap_str: String =
                                        s_chars[cap.0..cap.0 + cap.1 as usize].iter().collect();
                                    let cv = vm.alloc_str(&cap_str);
                                    vm.data_stack.push(cv);
                                }
                            }
                            return cap_count;
                        }
                    }
                    Err(e) => vm.runtime_error(&e),
                    _ => {}
                }
                if anchor {
                    break;
                }
                i += 1;
            }
            vm.data_stack.push(Value::nil());
            1
        });

        self.register_method(&mut string_map, "gmatch", |vm, args| {
            let s = get_str_arg(vm, &args, 0, "gmatch");
            let pattern = get_str_arg(vm, &args, 1, "gmatch");

            let mut state_map = HashMap::new();
            state_map.insert(vm.alloc_str("s"), vm.alloc_str(&s));
            state_map.insert(vm.alloc_str("p"), vm.alloc_str(&pattern));
            state_map.insert(vm.alloc_str("i"), Value::num(0.0)); // 0-based
            let state_table = vm.alloc(GcObject::Table(state_map, None));

            let iter_func = |vm: &mut VM, _args: Vec<Value>, state: Value| -> usize {
                let s_key = vm.alloc_str("s");
                let p_key = vm.alloc_str("p");
                let i_key = vm.alloc_str("i");

                if let Some(GcObject::Table(map, _)) = &vm.objects[state.as_obj() as usize] {
                    let s_str = vm.val_to_str(map[&s_key]);
                    let p_str = vm.val_to_str(map[&p_key]);
                    let mut i = map[&i_key].as_num() as usize;

                    let s_chars: Vec<char> = s_str.chars().collect();
                    let p_chars: Vec<char> = p_str.chars().collect();

                    while i <= s_chars.len() {
                        let mut ms = MatchState::new(&s_chars, &p_chars);
                        if let Ok(Some(end)) = ms.match_impl(i, 0) {
                            let next_i = if i == end { end + 1 } else { end };
                            if let Some(GcObject::Table(m, _)) =
                                &mut vm.objects[state.as_obj() as usize]
                            {
                                m.insert(i_key, Value::num(next_i as f64));
                            }

                            if ms.captures.is_empty() {
                                let whole: String = s_chars[i..end].iter().collect();
                                let sv = vm.alloc_str(&whole);
                                vm.data_stack.push(sv);
                                return 1;
                            } else {
                                let count = ms.captures.len();
                                for cap in ms.captures {
                                    if cap.1 == -2 {
                                        vm.data_stack.push(Value::num((cap.0 + 1) as f64));
                                    } else {
                                        let cstr: String =
                                            s_chars[cap.0..cap.0 + cap.1 as usize].iter().collect();
                                        let cv = vm.alloc_str(&cstr);
                                        vm.data_stack.push(cv);
                                    }
                                }
                                return count;
                            }
                        }
                        i += 1;
                    }
                }
                vm.data_stack.push(Value::nil());
                1
            };

            let closure_id = vm.alloc(GcObject::NativeClosure(iter_func, Value::obj(state_table)));
            vm.data_stack.push(Value::obj(closure_id));
            1
        });

        self.register_method(&mut string_map, "gsub", |vm, args| {
            if args.len() < 3 { vm.runtime_error("bad argument to 'gsub'"); }
            let s_str = get_str_arg(vm, &args, 0, "gsub");
            let p_str = get_str_arg(vm, &args, 1, "gsub");
            let repl = args[2];
            let limit = get_num_arg(vm, &args, 3, Some(-1.0), "gsub") as i64;

            let s_chars: Vec<char> = s_str.chars().collect();
            let p_chars: Vec<char> = p_str.chars().collect();
            let anchor = p_chars.first() == Some(&'^');
            let p_slice = if anchor { &p_chars[1..] } else { &p_chars[..] };

            let mut result_string = String::new();
            let mut i = 0;
            let mut match_count = 0;

            while i <= s_chars.len() && (limit < 0 || match_count < limit) {
                let mut ms = MatchState::new(&s_chars, p_slice);
                match ms.match_impl(i, 0) {
                    Ok(Some(end)) => {
                        let match_str: String = s_chars[i..end].iter().collect();

                        let cap_str = if ms.captures.is_empty() { match_str.clone() }
                                      else if ms.captures[0].1 == -2 { (ms.captures[0].0 + 1).to_string() }
                                      else { s_chars[ms.captures[0].0..ms.captures[0].0 + ms.captures[0].1 as usize].iter().collect() };

                        let mut repl_str = String::new();
                        let mut use_original = false;

                        match vm.objects[repl.as_obj() as usize].clone() {
                            Some(GcObject::Str(rep_s)) => {
                                let mut r_chars = rep_s.chars().peekable();
                                while let Some(c) = r_chars.next() {
                                    if c == '%' {
                                        if let Some(&nc) = r_chars.peek() {
                                            if nc.is_ascii_digit() {
                                                r_chars.next();
                                                let d = nc as u8 - b'0';
                                                if d == 0 {
                                                    repl_str.push_str(&match_str);
                                                } else {
                                                    let idx = d as usize - 1;
                                                    if idx < ms.captures.len() {
                                                        let cap = ms.captures[idx];
                                                        if cap.1 == -2 { repl_str.push_str(&(cap.0 + 1).to_string()); }
                                                        else { repl_str.push_str(&s_chars[cap.0..cap.0 + cap.1 as usize].iter().collect::<String>()); }
                                                    } else if idx == 0 && ms.captures.is_empty() {

                                                        repl_str.push_str(&match_str);
                                                    } else {
                                                        vm.runtime_error(&format!("invalid capture index %{}", d));
                                                    }
                                                }
                                                continue;
                                            }else if nc == '%' { r_chars.next(); repl_str.push('%'); continue; }
                                        }
                                    }
                                    repl_str.push(c);
                                }
                            }
                            Some(GcObject::Table(map, _)) => {
                                let key_val = if ms.captures.is_empty() {
                                    vm.alloc_str(&match_str)
                                } else if ms.captures[0].1 == -2 {
                                    Value::num((ms.captures[0].0 + 1) as f64)
                                } else {
                                    let s: String = s_chars[ms.captures[0].0..ms.captures[0].0 + ms.captures[0].1 as usize].iter().collect();
                                    vm.alloc_str(&s)
                                };

                                let mut found = map.get(&key_val).copied().unwrap_or(Value::nil());

                                if found.0 == TAG_NIL && key_val.is_obj() {
                                    let search_string = vm.val_to_str(key_val);
                                    for (&k, &v) in map.iter() {
                                        if k.is_obj() && vm.val_to_str(k) == search_string {
                                            found = v;
                                            break;
                                        }
                                    }
                                }

                                if found.0 == TAG_NIL {

                                    if let Some(GcObject::Table(_, Some(mt_id))) = vm.objects[repl.as_obj() as usize].clone() {

                                        let mt_idx = mt_id as usize;

                                        if let Some(GcObject::Table(mt_map, _)) = vm.objects[mt_idx].clone() {
                                            let index_key = vm.alloc_str("__index");
                                            let mut index_handler = mt_map.get(&index_key).copied().unwrap_or(Value::nil());

                                            if index_handler.0 == TAG_NIL {
                                                for (&k, &v) in mt_map.iter() {
                                                    if k.is_obj() && vm.val_to_str(k) == "__index" {
                                                        index_handler = v; break;
                                                    }
                                                }
                                            }

                                            if index_handler.is_obj() {
                                                match vm.objects[index_handler.as_obj() as usize].clone() {
                                                    Some(GcObject::Closure { .. }) | Some(GcObject::NativeFn(_)) | Some(GcObject::NativeClosure(..)) => {

                                                        vm.internal_call(index_handler, vec![repl, key_val]);
                                                        if vm.multiret_count > 0 {
                                                            let mut ret = Value::nil();
                                                            for idx in 0..vm.multiret_count {
                                                                let v = vm.data_stack.pop().unwrap();
                                                                if idx == vm.multiret_count - 1 { ret = v; }
                                                            }
                                                            found = ret;
                                                        }
                                                    }
                                                    Some(GcObject::Table(idx_map, _)) => {

                                                        found = idx_map.get(&key_val).copied().unwrap_or(Value::nil());
                                                        if found.0 == TAG_NIL && key_val.is_obj() {
                                                            let search_string = vm.val_to_str(key_val);
                                                            for (&k, &v) in idx_map.iter() {
                                                                if k.is_obj() && vm.val_to_str(k) == search_string {
                                                                    found = v; break;
                                                                }
                                                            }
                                                        }
                                                    }
                                                    _ => {}
                                                }
                                            }
                                        }
                                    }
                                }

                                if found.is_truthy() {
                                    if !found.is_obj() && found.0 != TAG_FALSE && found.0 != TAG_TRUE ||
                                       (found.is_obj() && matches!(vm.objects[found.as_obj() as usize], Some(GcObject::Str(_)))) {
                                        repl_str = vm.val_to_str(found);
                                    } else {
                                        vm.runtime_error("invalid replacement value (a table must return a string or number)");
                                    }
                                } else {
                                    use_original = true;
                                }
                            }
                            Some(GcObject::Closure { .. }) | Some(GcObject::NativeFn(_)) => {
                                let mut call_args = Vec::new();
                                if ms.captures.is_empty() {
                                    call_args.push(vm.alloc_str(&match_str));
                                } else {
                                    for cap in &ms.captures {
                                        if cap.1 == -2 { call_args.push(Value::num((cap.0 + 1) as f64)); }
                                        else {
                                            let cs: String = s_chars[cap.0..cap.0 + cap.1 as usize].iter().collect();
                                            call_args.push(vm.alloc_str(&cs));
                                        }
                                    }
                                }
                                vm.internal_call(repl, call_args);
                                if vm.multiret_count > 0 {
                                    let mut ret = Value::nil();
                                    for idx in 0..vm.multiret_count { let v = vm.data_stack.pop().unwrap(); if idx == vm.multiret_count - 1 { ret = v; } }
                                    if ret.is_truthy() {
                                        if !ret.is_obj() && ret.0 != TAG_FALSE && ret.0 != TAG_TRUE ||
                                           (ret.is_obj() && matches!(vm.objects[ret.as_obj() as usize], Some(GcObject::Str(_)))) {
                                            repl_str = vm.val_to_str(ret);
                                        } else { vm.runtime_error("invalid replacement value (a function must return a string or number)"); }
                                    } else { use_original = true; }
                                } else { use_original = true; }
                            }
                            _ => vm.runtime_error("bad argument #3 to 'gsub' (string/function/table expected)"),
                        }

                        if use_original { result_string.push_str(&match_str); }
                        else { result_string.push_str(&repl_str); }

                        match_count += 1;
                        if i == end {
                            if i < s_chars.len() { result_string.push(s_chars[i]); }
                            i += 1;
                        }
                        else { i = end; }
                    }
                    Err(e) => vm.runtime_error(&e),
                    Ok(None) => {
                        if i < s_chars.len() { result_string.push(s_chars[i]); }
                        if anchor {
                            let rest: String = s_chars[i..].iter().collect();
                            result_string.push_str(&rest);
                            break;
                        }
                        i += 1;
                    }
                }
            }

            if i < s_chars.len() {
                let rest: String = s_chars[i..].iter().collect();
                result_string.push_str(&rest);
            }

            let final_val = vm.alloc_str(&result_string);
            vm.data_stack.push(final_val);
            vm.data_stack.push(Value::num(match_count as f64));
            2
        });

        self.register_method(&mut string_map, "len", |vm, args| {
            let s = get_str_arg(vm, &args, 0, "len");
            vm.data_stack.push(Value::num(s.chars().count() as f64));
            1
        });
        self.register_method(&mut string_map, "lower", |vm, args| {
            let res = get_str_arg(vm, &args, 0, "lower").to_lowercase();
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });
        self.register_method(&mut string_map, "upper", |vm, args| {
            let res = get_str_arg(vm, &args, 0, "upper").to_uppercase();
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });
        self.register_method(&mut string_map, "reverse", |vm, args| {
            let res = get_str_arg(vm, &args, 0, "reverse")
                .chars()
                .rev()
                .collect::<String>();
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });

        self.register_method(&mut string_map, "sub", |vm, args| {
            let s = get_str_arg(vm, &args, 0, "sub");
            let len = s.chars().count() as i64;
            let mut start = get_num_arg(vm, &args, 1, None, "sub") as i64;
            let mut end = get_num_arg(vm, &args, 2, Some(-1.0), "sub") as i64;
            if start < 0 {
                start = len + start + 1;
            }
            if end < 0 {
                end = len + end + 1;
            }
            start = start.max(1);
            end = end.min(len);
            let res = if start <= end {
                s.chars()
                    .skip((start - 1) as usize)
                    .take((end - start + 1) as usize)
                    .collect::<String>()
            } else {
                "".to_string()
            };
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });

        self.register_method(&mut string_map, "rep", |vm, args| {
            let s = get_str_arg(vm, &args, 0, "rep");
            let n = get_num_arg(vm, &args, 1, None, "rep") as isize;
            let res = if n > 0 {
                s.repeat(n as usize)
            } else {
                "".to_string()
            };
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });

        self.register_method(&mut string_map, "char", |vm, args| {
            let mut res = String::new();
            for (i, arg) in args.iter().enumerate() {
                let n = vm.to_num(*arg).unwrap_or_else(|| {
                    vm.runtime_error(&format!("bad argument #{} to 'char'", i + 1))
                }) as u32;
                if let Some(c) = std::char::from_u32(n) {
                    res.push(c);
                } else {
                    vm.runtime_error(&format!("bad argument #{} to 'char'", i + 1));
                }
            }
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });

        self.register_method(&mut string_map, "byte", |vm, args| {
            let s = get_str_arg(vm, &args, 0, "byte");
            let chars: Vec<char> = s.chars().collect();
            let len = chars.len() as i64;
            let mut start = get_num_arg(vm, &args, 1, Some(1.0), "byte") as i64;
            let mut end = get_num_arg(vm, &args, 2, Some(start as f64), "byte") as i64;
            if start < 0 {
                start = len + start + 1;
            }
            if end < 0 {
                end = len + end + 1;
            }
            start = start.max(1);
            end = end.min(len);
            if start > end {
                return 0;
            }
            for i in start..=end {
                vm.data_stack
                    .push(Value::num(chars[(i - 1) as usize] as u32 as f64));
            }
            (end - start + 1) as usize
        });

        // 4. format
        // 4. format
        self.register_method(&mut string_map, "format", |vm, args| {
            let fmt = get_str_arg(vm, &args, 0, "format");
            let mut res = String::new();
            let mut chars = fmt.chars().peekable();
            let mut arg_idx = 1;

            while let Some(c) = chars.next() {
                if c != '%' {
                    res.push(c);
                    continue;
                }

                let mut flags = String::new();
                while let Some(&nc) = chars.peek() {
                    if nc == '-' || nc == '+' || nc == ' ' || nc == '#' || nc == '0' {
                        flags.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                let mut width = String::new();
                while let Some(&nc) = chars.peek() {
                    if nc.is_ascii_digit() {
                        width.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                let mut precision = String::new();
                let mut has_precision = false;
                if chars.peek() == Some(&'.') {
                    has_precision = true;
                    chars.next(); // consume '.'
                    while let Some(&nc) = chars.peek() {
                        if nc.is_ascii_digit() {
                            precision.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                }

                if let Some(spec) = chars.next() {
                    if spec == '%' {
                        res.push('%');
                        continue;
                    }

                    if arg_idx >= args.len() {
                        vm.runtime_error("bad argument to 'format' (no value)");
                    }
                    let val = args[arg_idx];
                    arg_idx += 1;

                    let w = width.parse::<usize>().unwrap_or(0);
                    let left_align = flags.contains('-');
                    let zero_pad = flags.contains('0') && !left_align;

                    match spec {
                        's' => {
                            let mut s = vm.val_to_str(val);
                            if has_precision {
                                let p = precision.parse::<usize>().unwrap_or(0);
                                if s.chars().count() > p {
                                    s = s.chars().take(p).collect();
                                }
                            }
                            let char_len = s.chars().count();
                            if w > char_len {
                                let pad = " ".repeat(w - char_len);
                                if left_align {
                                    res.push_str(&s);
                                    res.push_str(&pad);
                                } else {
                                    res.push_str(&pad);
                                    res.push_str(&s);
                                }
                            } else {
                                res.push_str(&s);
                            }
                        }
                        'c' => {
                            let n = vm.to_num(val).unwrap_or(0.0) as u32;
                            let c_str = if let Some(ch) = std::char::from_u32(n) {
                                ch.to_string()
                            } else {
                                "".to_string()
                            };
                            if w > 1 {
                                let pad = " ".repeat(w - 1);
                                if left_align {
                                    res.push_str(&c_str);
                                    res.push_str(&pad);
                                } else {
                                    res.push_str(&pad);
                                    res.push_str(&c_str);
                                }
                            } else {
                                res.push_str(&c_str);
                            }
                        }
                        'd' | 'i' | 'u' => {
                            let n = vm.to_num(val).unwrap_or(0.0) as i64;
                            let mut num_str = n.abs().to_string();
                            if has_precision {
                                let p = precision.parse::<usize>().unwrap_or(1);
                                if p > num_str.len() {
                                    num_str = "0".repeat(p - num_str.len()) + &num_str;
                                } else if p == 0 && n == 0 {
                                    num_str = "".to_string();
                                }
                            }

                            let sign = if n < 0 {
                                "-"
                            } else if flags.contains('+') {
                                "+"
                            } else if flags.contains(' ') {
                                " "
                            } else {
                                ""
                            };

                            let total_len = num_str.len() + sign.len();
                            if w > total_len {
                                let pad_char = if zero_pad && !has_precision { "0" } else { " " };
                                let pad = pad_char.repeat(w - total_len);
                                if left_align {
                                    res.push_str(sign);
                                    res.push_str(&num_str);
                                    res.push_str(&pad);
                                } else if zero_pad && !has_precision {
                                    res.push_str(sign);
                                    res.push_str(&pad);
                                    res.push_str(&num_str);
                                } else {
                                    res.push_str(&pad);
                                    res.push_str(sign);
                                    res.push_str(&num_str);
                                }
                            } else {
                                res.push_str(sign);
                                res.push_str(&num_str);
                            }
                        }
                        'f' => {
                            let n = vm.to_num(val).unwrap_or(0.0);
                            let p = if has_precision {
                                precision.parse::<usize>().unwrap_or(0)
                            } else {
                                6
                            };
                            let num_str = format!("{:.*}", p, n.abs());
                            let sign = if n < 0.0 || n.is_sign_negative() {
                                "-"
                            } else if flags.contains('+') {
                                "+"
                            } else if flags.contains(' ') {
                                " "
                            } else {
                                ""
                            };
                            let total_len = num_str.len() + sign.len();

                            if w > total_len {
                                let pad_char = if zero_pad { "0" } else { " " };
                                let pad = pad_char.repeat(w - total_len);
                                if left_align {
                                    res.push_str(sign);
                                    res.push_str(&num_str);
                                    res.push_str(&pad);
                                } else if zero_pad {
                                    res.push_str(sign);
                                    res.push_str(&pad);
                                    res.push_str(&num_str);
                                } else {
                                    res.push_str(&pad);
                                    res.push_str(sign);
                                    res.push_str(&num_str);
                                }
                            } else {
                                res.push_str(sign);
                                res.push_str(&num_str);
                            }
                        }
                        'x' | 'X' => {
                            let n = vm.to_num(val).unwrap_or(0.0) as i64;
                            let mut num_str = if spec == 'x' {
                                format!("{:x}", n)
                            } else {
                                format!("{:X}", n)
                            };
                            if has_precision {
                                let p = precision.parse::<usize>().unwrap_or(1);
                                if p > num_str.len() {
                                    num_str = "0".repeat(p - num_str.len()) + &num_str;
                                } else if p == 0 && n == 0 {
                                    num_str = "".to_string();
                                }
                            }

                            if w > num_str.len() {
                                let pad_char = if zero_pad && !has_precision { "0" } else { " " };
                                let pad = pad_char.repeat(w - num_str.len());
                                if left_align {
                                    res.push_str(&num_str);
                                    res.push_str(&pad);
                                } else {
                                    res.push_str(&pad);
                                    res.push_str(&num_str);
                                }
                            } else {
                                res.push_str(&num_str);
                            }
                        }
                        'q' => {
                            let s = vm.val_to_str(val);
                            res.push('"');
                            for b in s.bytes() {
                                match b {
                                    b'"' | b'\\' | b'\n' => {
                                        res.push('\\');
                                        if b == b'\n' {
                                            res.push('\n');
                                        } else {
                                            res.push(b as char);
                                        }
                                    }
                                    b'\r' => res.push_str("\\r"),
                                    0 => res.push_str("\\000"),
                                    _ => res.push(b as char),
                                }
                            }
                            res.push('"');
                        }
                        _ => {
                            res.push('%');
                            res.push_str(&flags);
                            res.push_str(&width);
                            if has_precision {
                                res.push('.');
                                res.push_str(&precision);
                            }
                            res.push(spec);
                        }
                    }
                } else {
                    res.push('%');
                }
            }
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });

        self.register_method(&mut string_map, "dump", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'dump' (function expected)");
            }

            let func_val = args[0];
            let func_id = func_val.as_obj();

            let reg_name = "__DUMPED_FUNCS_REGISTRY";
            let mut reg_table_val = vm.get_global(reg_name);

            if !reg_table_val.is_obj() {
                let id = vm.alloc(GcObject::Table(HashMap::new(), None));
                reg_table_val = Value::obj(id);
                vm.set_global(reg_name, reg_table_val);
            }

            if let Some(GcObject::Table(map, _)) = &mut vm.objects[reg_table_val.as_obj() as usize]
            {
                map.insert(Value::num(func_id as f64), func_val);
            }

            let magic_str = format!("\x1bLUA_AE_DUMP:{}", func_id);
            let str_val = vm.alloc_str(&magic_str);

            vm.data_stack.push(str_val);
            1
        });

        let string_table = self.alloc(GcObject::Table(string_map, None));
        self.set_global("string", Value::obj(string_table));
    }
    fn open_os_lib(&mut self) {
        let mut os_map = HashMap::new();

        // 1. os.time([table])
        self.register_method(&mut os_map, "time", |vm, args| {
            let arg = args.get(0).copied().unwrap_or(Value::nil());
            if arg.0 == TAG_NIL {
                let secs = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs() as f64;
                vm.data_stack.push(Value::num(secs));
            } else if arg.is_obj()
                && matches!(vm.objects[arg.as_obj() as usize], Some(GcObject::Table(..)))
            {

                let mut get_field = |key: &str, default: f64| -> f64 {
                    let k = vm.alloc_str(key);
                    if let Some(GcObject::Table(map, _)) = &vm.objects[arg.as_obj() as usize] {
                        map.get(&k).and_then(|v| vm.to_num(*v)).unwrap_or(default)
                    } else {
                        default
                    }
                };

                let year = get_field("year", 1970.0) as i64;
                let month = get_field("month", 1.0) as i64;
                let day = get_field("day", 1.0) as i64;
                let hour = get_field("hour", 12.0) as i64;
                let min = get_field("min", 0.0) as i64;
                let sec = get_field("sec", 0.0) as i64;

                let a = (14 - month) / 12;
                let y = year + 4800 - a;
                let m = month + 12 * a - 3;
                let jdn = day + (153 * m + 2) / 5 + 365 * y + y / 4 - y / 100 + y / 400 - 32045;
                let unix_days = jdn - 2440588;
                let timestamp = unix_days * 86400 + hour * 3600 + min * 60 + sec;

                vm.data_stack.push(Value::num(timestamp as f64));
            } else {
                vm.runtime_error("bad argument #1 to 'time' (table or nil expected)");
            }
            1
        });

        // 2. os.difftime(t2, t1)
        self.register_method(&mut os_map, "difftime", |vm, args| {
            let t2 = vm
                .to_num(args.get(0).copied().unwrap_or(Value::nil()))
                .unwrap_or(0.0);
            let t1 = vm
                .to_num(args.get(1).copied().unwrap_or(Value::nil()))
                .unwrap_or(0.0);
            vm.data_stack.push(Value::num(t2 - t1));
            1
        });

        // 3. os.clock()
        self.register_method(&mut os_map, "clock", |vm, _| {
            let process_time = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs_f64();
            vm.data_stack.push(Value::num(process_time));
            1
        });

        // 4. os.getenv(varname)
        self.register_method(&mut os_map, "getenv", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'getenv'");
            }
            let varname = vm.val_to_str(args[0]);
            if let Ok(val) = std::env::var(varname) {
                let str_val = vm.alloc_str(&val);
                vm.data_stack.push(str_val);
            } else {
                vm.data_stack.push(Value::nil());
            }
            1
        });

        // 5. os.execute([command])
        self.register_method(&mut os_map, "execute", |vm, args| {
            if args.is_empty() || args[0].0 == TAG_NIL {

                vm.data_stack.push(Value::bool(true));
                return 1;
            }
            let cmd = vm.val_to_str(args[0]);
            let status = if cfg!(target_os = "windows") {
                std::process::Command::new("cmd")
                    .args(["/C", &cmd])
                    .status()
            } else {
                std::process::Command::new("sh").args(["-c", &cmd]).status()
            };

            match status {
                Ok(exit_status) => {
                    let code = exit_status.code().unwrap_or(0) as f64;
                    vm.data_stack.push(Value::num(code));
                }
                Err(_) => vm.data_stack.push(Value::num(-1.0)),
            }
            1
        });

        // 6. os.exit([code])
        self.register_method(&mut os_map, "exit", |vm, args| {
            let code = if args.is_empty() {
                0
            } else {
                vm.to_num(args[0]).unwrap_or(0.0) as i32
            };
            std::process::exit(code);
        });

        // 7. os.remove(filename)
        self.register_method(&mut os_map, "remove", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'remove'");
            }
            let filename = vm.val_to_str(args[0]);
            match std::fs::remove_file(&filename).or_else(|_| std::fs::remove_dir(&filename)) {
                Ok(_) => {
                    vm.data_stack.push(Value::bool(true));
                    1
                }
                Err(e) => {
                    vm.data_stack.push(Value::nil());
                    let err_str = vm.alloc_str(&e.to_string());
                    vm.data_stack.push(err_str);
                    2
                }
            }
        });

        // 8. os.rename(oldname, newname)
        self.register_method(&mut os_map, "rename", |vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'rename'");
            }
            let oldname = vm.val_to_str(args[0]);
            let newname = vm.val_to_str(args[1]);
            match std::fs::rename(oldname, newname) {
                Ok(_) => {
                    vm.data_stack.push(Value::bool(true));
                    1
                }
                Err(e) => {
                    vm.data_stack.push(Value::nil());
                    let err_str = vm.alloc_str(&e.to_string());
                    vm.data_stack.push(err_str);
                    2
                }
            }
        });

        // 9. os.tmpname()
        // 9. os.tmpname()
        self.register_method(&mut os_map, "tmpname", |vm, _| {
            let t = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let mut path = std::env::temp_dir();
            path.push(format!("lua_{:x}", t));
            let path_str = path.to_str().unwrap_or("temp_lua_file").to_string();
            let s_val = vm.alloc_str(&path_str);
            vm.data_stack.push(s_val);
            1
        });

        // 10. os.date([format [, time]])
        self.register_method(&mut os_map, "date", |vm, args| {
            let fmt = args
                .get(0)
                .map(|v| vm.val_to_str(*v))
                .unwrap_or_else(|| "%c".to_string());
            let t = args.get(1).and_then(|v| vm.to_num(*v)).unwrap_or_else(|| {
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs() as f64
            }) as i64;

            let z = t / 86400 + 719468;
            let era = (if z >= 0 { z } else { z - 146096 }) / 146097;
            let doe = (z - era * 146097) as u32;
            let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
            let y = (yoe as i64) + era * 400;
            let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
            let mp = (5 * doy + 2) / 153;
            let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
            let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
            let year = y + (if m <= 2 { 1 } else { 0 });

            let mut rem = t % 86400;
            if rem < 0 {
                rem += 86400;
            }
            let hour = (rem / 3600) as u32;
            let min = ((rem / 60) % 60) as u32;
            let sec = (rem % 60) as u32;

            if fmt == "*t" || fmt == "!*t" {
                let mut map = HashMap::new();
                map.insert(vm.alloc_str("year"), Value::num(year as f64));
                map.insert(vm.alloc_str("month"), Value::num(m as f64));
                map.insert(vm.alloc_str("day"), Value::num(d as f64));
                map.insert(vm.alloc_str("hour"), Value::num(hour as f64));
                map.insert(vm.alloc_str("min"), Value::num(min as f64));
                map.insert(vm.alloc_str("sec"), Value::num(sec as f64));
                let table_id = vm.alloc(GcObject::Table(map, None));
                vm.data_stack.push(Value::obj(table_id));
            } else {
                let mut res = fmt.clone();
                res = res.replace("%Y", &format!("{:04}", year));
                res = res.replace("%m", &format!("{:02}", m));
                res = res.replace("%d", &format!("{:02}", d));
                res = res.replace("%H", &format!("{:02}", hour));
                res = res.replace("%M", &format!("{:02}", min));
                res = res.replace("%S", &format!("{:02}", sec));
                res = res.replace(
                    "%c",
                    &format!(
                        "{:04}-{:02}-{:02} {:02}:{:02}:{:02}",
                        year, m, d, hour, min, sec
                    ),
                );
                let str_val = vm.alloc_str(&res);
                vm.data_stack.push(str_val);
            }
            1
        });

        self.register_method(&mut os_map, "setlocale", |vm, _| {
            let s = vm.alloc_str("C");
            vm.data_stack.push(s);
            1
        });

        let os_table = self.alloc(GcObject::Table(os_map, None));
        self.set_global("os", Value::obj(os_table));
    }
    fn open_coroutine_lib(&mut self) {
        let mut coro_map = HashMap::new();

        // coroutine.create(f)
        self.register_method(&mut coro_map, "create", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'create' (function expected)");
            }
            let ts = ThreadState {
                call_stack: Vec::new(),
                data_stack: vec![args[0]],
                handler_stack: Vec::new(),
                status: ThreadStatus::Suspended,
            };
            let id = vm.alloc(GcObject::Thread(Some(Box::new(ts))));
            vm.data_stack.push(Value::obj(id));
            1
        });

        // coroutine.resume(co, ...)
        self.register_method(&mut coro_map, "resume", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.data_stack.push(Value::bool(false));
                let msg = vm.alloc_str("bad argument to 'resume'");
                vm.data_stack.push(msg);
                return 2;
            }

            let co_idx = args[0].as_obj() as usize;

            let mut thread_state = match &mut vm.objects[co_idx] {
                Some(GcObject::Thread(ts_opt)) => {
                    if let Some(ts) = ts_opt.take() {
                        *ts
                    } else {
                        vm.data_stack.push(Value::bool(false));
                        let msg = vm.alloc_str("cannot resume running coroutine");
                        vm.data_stack.push(msg);
                        return 2;
                    }
                }
                _ => {
                    vm.data_stack.push(Value::bool(false));
                    let msg = vm.alloc_str("bad argument #1 to 'resume'");
                    vm.data_stack.push(msg);
                    return 2;
                }
            };

            if thread_state.status == ThreadStatus::Dead {
                if let Some(GcObject::Thread(ts_opt)) = &mut vm.objects[co_idx] {
                    *ts_opt = Some(Box::new(thread_state));
                }
                vm.data_stack.push(Value::bool(false));
                let msg = vm.alloc_str("cannot resume dead coroutine");
                vm.data_stack.push(msg);
                return 2;
            }

            let resume_args = args[1..].to_vec();

            std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
            std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
            std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);

            vm.yielded = false;
            let prev_thread = vm.current_thread;
            vm.current_thread = Some(co_idx as u32);

            let prev_hook = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                if thread_state.status == ThreadStatus::Suspended && vm.call_stack.is_empty() {

                    let func = vm.data_stack.pop().unwrap();
                    vm.internal_call(func, resume_args);
                } else {

                    for arg in &resume_args {
                        vm.data_stack.push(*arg);
                    }
                    vm.multiret_count = resume_args.len();
                    vm.run_until(0);
                }

                let ret_count = vm.multiret_count;
                let mut rets = Vec::new();
                for _ in 0..ret_count {
                    rets.push(vm.data_stack.pop().unwrap());
                }
                rets.reverse();
                (vm.yielded, rets)
            }));

            std::panic::set_hook(prev_hook);

            std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
            std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
            std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);

            vm.yielded = false;
            vm.current_thread = prev_thread;

            match result {
                Ok((did_yield, rets)) => {
                    thread_state.status = if did_yield {
                        ThreadStatus::Suspended
                    } else {
                        ThreadStatus::Dead
                    };
                    if let Some(GcObject::Thread(ts_opt)) = &mut vm.objects[co_idx] {
                        *ts_opt = Some(Box::new(thread_state));
                    }

                    vm.data_stack.push(Value::bool(true));
                    for r in &rets {
                        vm.data_stack.push(*r);
                    }
                    1 + rets.len() // 1 (true) + args
                }
                Err(payload) => {
                    thread_state.status = ThreadStatus::Dead;
                    if let Some(GcObject::Thread(ts_opt)) = &mut vm.objects[co_idx] {
                        *ts_opt = Some(Box::new(thread_state));
                    }

                    let err_val = if let Some(&v) = payload.downcast_ref::<Value>() {
                        v
                    } else {
                        let err_msg = if let Some(s) = payload.downcast_ref::<String>() {
                            s.clone()
                        } else if let Some(s) = payload.downcast_ref::<&str>() {
                            s.to_string()
                        } else {
                            "unknown runtime error".to_string()
                        };
                        vm.alloc_str(&err_msg)
                    };

                    vm.data_stack.push(Value::bool(false));
                    vm.data_stack.push(err_val);
                    2
                }
            }
        });

        // coroutine.wrap(f)
        self.register_method(&mut coro_map, "wrap", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'wrap' (function expected)");
            }

            let ts = ThreadState {
                call_stack: Vec::new(),
                data_stack: vec![args[0]],
                handler_stack: Vec::new(),
                status: ThreadStatus::Suspended,
            };
            let co_id = vm.alloc(GcObject::Thread(Some(Box::new(ts))));

            let wrapper_func = |vm: &mut VM, resume_args: Vec<Value>, state: Value| -> usize {
                let co_idx = state.as_obj() as usize;

                let mut thread_state = match &mut vm.objects[co_idx] {
                    Some(GcObject::Thread(ts_opt)) => {
                        if let Some(ts) = ts_opt.take() {
                            *ts
                        } else {
                            vm.runtime_error("cannot resume running coroutine");
                        }
                    }
                    _ => vm.runtime_error("invalid coroutine state"),
                };

                if thread_state.status == ThreadStatus::Dead {
                    if let Some(GcObject::Thread(ts_opt)) = &mut vm.objects[co_idx] {
                        *ts_opt = Some(Box::new(thread_state));
                    }
                    vm.runtime_error("cannot resume dead coroutine");
                }

                std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
                std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
                std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);

                vm.yielded = false;
                let prev_thread = vm.current_thread;
                vm.current_thread = Some(co_idx as u32);

                let prev_hook = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));

                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    if thread_state.status == ThreadStatus::Suspended && vm.call_stack.is_empty() {
                        let func = vm.data_stack.pop().unwrap();
                        vm.internal_call(func, resume_args);
                    } else {
                        for arg in &resume_args {
                            vm.data_stack.push(*arg);
                        }
                        vm.multiret_count = resume_args.len();
                        vm.run_until(0);
                    }

                    let ret_count = vm.multiret_count;
                    let mut rets = Vec::new();
                    for _ in 0..ret_count {
                        rets.push(vm.data_stack.pop().unwrap());
                    }
                    rets.reverse();
                    (vm.yielded, rets)
                }));

                std::panic::set_hook(prev_hook);

                std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
                std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
                std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);

                vm.yielded = false;
                vm.current_thread = prev_thread;

                match result {
                    Ok((did_yield, rets)) => {
                        thread_state.status = if did_yield {
                            ThreadStatus::Suspended
                        } else {
                            ThreadStatus::Dead
                        };
                        if let Some(GcObject::Thread(ts_opt)) = &mut vm.objects[co_idx] {
                            *ts_opt = Some(Box::new(thread_state));
                        }

                        for r in &rets {
                            vm.data_stack.push(*r);
                        }
                        rets.len()
                    }
                    Err(payload) => {
                        thread_state.status = ThreadStatus::Dead;
                        if let Some(GcObject::Thread(ts_opt)) = &mut vm.objects[co_idx] {
                            *ts_opt = Some(Box::new(thread_state));
                        }

                        std::panic::resume_unwind(payload);
                    }
                }
            };

            let wrapper_id = vm.alloc(GcObject::NativeClosure(wrapper_func, Value::obj(co_id)));
            vm.data_stack.push(Value::obj(wrapper_id));
            1
        });

        // coroutine.yield(...)
        self.register_method(&mut coro_map, "yield", |vm, args| {
            if vm.c_call_depth > 0 {
                vm.runtime_error("attempt to yield across a C-call boundary (e.g. inside pcall)");
            }
            if vm.current_thread.is_none() {
                vm.runtime_error("attempt to yield from outside a coroutine");
            }

            vm.yielded = true;
            for arg in &args {
                vm.data_stack.push(*arg);
            }
            args.len()
        });

        // coroutine.status(co)
        self.register_method(&mut coro_map, "status", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'status' (thread expected)");
            }
            let co_idx = args[0].as_obj() as usize;
            let status_str = match &vm.objects[co_idx] {
                Some(GcObject::Thread(Some(ts))) => match ts.status {
                    ThreadStatus::Suspended => "suspended",
                    ThreadStatus::Running => "running",
                    ThreadStatus::Dead => "dead",
                },
                Some(GcObject::Thread(None)) => "running",
                _ => vm.runtime_error("bad argument #1 to 'status' (thread expected)"),
            };
            let s_val = vm.alloc_str(status_str);
            vm.data_stack.push(s_val);
            1
        });

        // coroutine.running()
        self.register_method(&mut coro_map, "running", |vm, _| {
            if let Some(id) = vm.current_thread {
                vm.data_stack.push(Value::obj(id));
            } else {
                vm.data_stack.push(Value::nil());
            }
            1
        });

        let coro_table = self.alloc(GcObject::Table(coro_map, None));
        self.set_global("coroutine", Value::obj(coro_table));
    }

    fn open_package_lib(&mut self) {
        let mut package_map = HashMap::new();

        let loaded_map = HashMap::new();
        let loaded_table = self.alloc(GcObject::Table(loaded_map, None));
        let loaded_key = self.alloc_str("loaded");
        package_map.insert(loaded_key, Value::obj(loaded_table));

        let mut preload_map = HashMap::new();

        let table_new_loader = self.alloc(GcObject::NativeFn(|vm, _| {
            let actual_fn = vm.alloc(GcObject::NativeFn(|vm, args| {
                let narray = args.get(0).and_then(|v| vm.to_num(*v)).unwrap_or(0.0) as usize;
                let nhash = args.get(1).and_then(|v| vm.to_num(*v)).unwrap_or(0.0) as usize;
                let map = HashMap::with_capacity(narray + nhash);
                let id = vm.alloc(GcObject::Table(map, None));
                vm.data_stack.push(Value::obj(id));
                1
            }));
            vm.data_stack.push(Value::obj(actual_fn));
            1
        }));
        let table_new_key = self.alloc_str("table.new");
        preload_map.insert(table_new_key, Value::obj(table_new_loader));

        let table_clear_loader = self.alloc(GcObject::NativeFn(|vm, _| {
            let actual_fn = vm.alloc(GcObject::NativeFn(|vm, args| {
                if args.is_empty() || !args[0].is_obj() {
                    vm.runtime_error("bad argument #1 to 'clear' (table expected)");
                }
                let t_idx = args[0].as_obj() as usize;
                if let Some(GcObject::Table(map, _)) = &mut vm.objects[t_idx] {

                    map.clear();
                }
                0
            }));
            vm.data_stack.push(Value::obj(actual_fn));
            1
        }));
        let table_clear_key = self.alloc_str("table.clear");
        preload_map.insert(table_clear_key, Value::obj(table_clear_loader));

        let bit_loader = self.alloc(GcObject::NativeFn(|vm, _| {
            let actual_fn = vm.alloc(GcObject::NativeFn(|vm, _| {
                let mut bit_map = HashMap::new();

                fn to_i32(vm: &VM, val: Value) -> i32 {
                    if let Some(n) = vm.to_num(val) {
                        n as i32
                    } else {
                        0
                    }
                }

                macro_rules! reg_bit {
                    ($m:ident, $name:expr, $func:expr) => {
                        let k = vm.alloc_str($name);
                        let f = vm.alloc(GcObject::NativeFn($func));
                        $m.insert(k, Value::obj(f));
                    };
                }

                reg_bit!(bit_map, "tobit", |vm, args| {
                    let v = to_i32(vm, args.get(0).copied().unwrap_or(Value::nil()));
                    vm.data_stack.push(Value::num(v as f64));
                    1
                });
                reg_bit!(bit_map, "bnot", |vm, args| {
                    let v = to_i32(vm, args.get(0).copied().unwrap_or(Value::nil()));
                    vm.data_stack.push(Value::num((!v) as f64));
                    1
                });

                reg_bit!(bit_map, "band", |vm, args| {
                    let mut r = if args.is_empty() {
                        -1
                    } else {
                        to_i32(vm, args[0])
                    };
                    for a in args.iter().skip(1) {
                        r &= to_i32(vm, *a);
                    }
                    vm.data_stack.push(Value::num(r as f64));
                    1
                });
                reg_bit!(bit_map, "bor", |vm, args| {
                    let mut r = if args.is_empty() {
                        0
                    } else {
                        to_i32(vm, args[0])
                    };
                    for a in args.iter().skip(1) {
                        r |= to_i32(vm, *a);
                    }
                    vm.data_stack.push(Value::num(r as f64));
                    1
                });
                reg_bit!(bit_map, "bxor", |vm, args| {
                    let mut r = if args.is_empty() {
                        0
                    } else {
                        to_i32(vm, args[0])
                    };
                    for a in args.iter().skip(1) {
                        r ^= to_i32(vm, *a);
                    }
                    vm.data_stack.push(Value::num(r as f64));
                    1
                });

                reg_bit!(bit_map, "lshift", |vm, args| {
                    let v = to_i32(vm, args.get(0).copied().unwrap_or(Value::nil()));
                    let s = to_i32(vm, args.get(1).copied().unwrap_or(Value::nil())) & 31;
                    vm.data_stack.push(Value::num((v << s) as f64));
                    1
                });
                reg_bit!(bit_map, "rshift", |vm, args| {
                    let v = to_i32(vm, args.get(0).copied().unwrap_or(Value::nil())) as u32;
                    let s = to_i32(vm, args.get(1).copied().unwrap_or(Value::nil())) & 31;
                    vm.data_stack.push(Value::num((v >> s) as f64));
                    1
                });
                reg_bit!(bit_map, "arshift", |vm, args| {
                    let v = to_i32(vm, args.get(0).copied().unwrap_or(Value::nil()));
                    let s = to_i32(vm, args.get(1).copied().unwrap_or(Value::nil())) & 31;
                    vm.data_stack.push(Value::num((v >> s) as f64));
                    1
                });

                reg_bit!(bit_map, "tohex", |vm, args| {
                    let v = to_i32(vm, args.get(0).copied().unwrap_or(Value::nil())) as u32;
                    let n = args.get(1).and_then(|x| vm.to_num(*x)).unwrap_or(8.0) as i32;
                    let abs_n = n.abs() as usize;
                    let hex_str = if n < 0 {
                        format!("{:0>width$X}", v, width = abs_n)
                    } else {
                        format!("{:0>width$x}", v, width = abs_n)
                    };
                    let s_val = vm.alloc_str(&hex_str);
                    vm.data_stack.push(s_val);
                    1
                });

                let bit_table = vm.alloc(GcObject::Table(bit_map, None));
                vm.data_stack.push(Value::obj(bit_table));
                1
            }));
            vm.data_stack.push(Value::obj(actual_fn));
            1
        }));
        let bit_key = self.alloc_str("bit");
        preload_map.insert(bit_key, Value::obj(bit_loader));

        let ffi_loader = self.alloc(GcObject::NativeFn(|vm, _| {
            let actual_fn = vm.alloc(GcObject::NativeFn(|vm, _| {
                let mut ffi_map = HashMap::new();

                let dummy_fn = vm.alloc(GcObject::NativeFn(|vm, _| {
                    vm.data_stack.push(Value::nil());
                    1
                }));
                ffi_map.insert(vm.alloc_str("cdef"), Value::obj(dummy_fn));
                ffi_map.insert(vm.alloc_str("new"), Value::obj(dummy_fn));
                ffi_map.insert(vm.alloc_str("typeof"), Value::obj(dummy_fn));
                ffi_map.insert(vm.alloc_str("load"), Value::obj(dummy_fn));

                let ffi_table = vm.alloc(GcObject::Table(ffi_map, None));
                vm.data_stack.push(Value::obj(ffi_table));
                1
            }));
            vm.data_stack.push(Value::obj(actual_fn));
            1
        }));
        let ffi_key = self.alloc_str("ffi");
        preload_map.insert(ffi_key, Value::obj(ffi_loader));

        let preload_table = self.alloc(GcObject::Table(preload_map, None));
        let preload_key = self.alloc_str("preload");
        package_map.insert(preload_key, Value::obj(preload_table));

        let path_str = self.alloc_str("?.lua;?/init.lua");
        let path_key = self.alloc_str("path");
        package_map.insert(path_key, path_str);

        let cpath_str = self.alloc_str("?.so;?.dll");
        let cpath_key = self.alloc_str("cpath");
        package_map.insert(cpath_key, cpath_str);

        let seeall_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'seeall' (table expected)");
            }
            let module_val = args[0];
            let mut mt_map = HashMap::new();
            let index_key = vm.alloc_str("__index");
            mt_map.insert(index_key, Value::obj(vm.global_env));
            let mt_id = vm.alloc(GcObject::Table(mt_map, None));
            if let Some(GcObject::Table(_, ref mut meta)) =
                &mut vm.objects[module_val.as_obj() as usize]
            {
                *meta = Some(mt_id);
            }
            0
        }));
        let seeall_key = self.alloc_str("seeall");
        package_map.insert(seeall_key, Value::obj(seeall_fn));

        let loadlib_fn = self.alloc(GcObject::NativeFn(|vm, _| {

            vm.data_stack.push(Value::nil());
            let err = vm.alloc_str("dynamic libraries not enabled");
            vm.data_stack.push(err);
            let absent = vm.alloc_str("absent");
            vm.data_stack.push(absent);
            3
        }));
        let loadlib_key = self.alloc_str("loadlib");
        package_map.insert(loadlib_key, Value::obj(loadlib_fn));
        let package_table = self.alloc(GcObject::Table(package_map, None));
        self.set_global("package", Value::obj(package_table));

        let require_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'require' (string expected)");
            }
            let modname_val = args[0];
            let modname = vm.val_to_str(modname_val);

            let pkg_val = vm.get_global("package");
            if !pkg_val.is_obj() {
                vm.runtime_error("'package' table missing");
            }

            let loaded_key = vm.alloc_str("loaded");
            let loaded_tab_val =
                if let Some(GcObject::Table(map, _)) = &vm.objects[pkg_val.as_obj() as usize] {
                    map.get(&loaded_key).copied().unwrap_or(Value::nil())
                } else {
                    Value::nil()
                };

            if loaded_tab_val.is_obj() {
                if let Some(GcObject::Table(map, _)) = &vm.objects[loaded_tab_val.as_obj() as usize]
                {
                    if let Some(&cached) = map.get(&modname_val) {
                        if cached.is_truthy() {

                            vm.data_stack.push(cached);
                            return 1;
                        }
                    }
                }
            }

            let preload_key = vm.alloc_str("preload");
            let preload_tab_val =
                if let Some(GcObject::Table(map, _)) = &vm.objects[pkg_val.as_obj() as usize] {
                    map.get(&preload_key).copied().unwrap_or(Value::nil())
                } else {
                    Value::nil()
                };

            let mut loader = Value::nil();

            if preload_tab_val.is_obj() {
                if let Some(GcObject::Table(map, _)) =
                    &vm.objects[preload_tab_val.as_obj() as usize]
                {
                    loader = map.get(&modname_val).copied().unwrap_or(Value::nil());
                }
            }

            if !loader.is_truthy() {
                let path_key = vm.alloc_str("path");
                let path_val =
                    if let Some(GcObject::Table(map, _)) = &vm.objects[pkg_val.as_obj() as usize] {
                        map.get(&path_key).copied().unwrap_or(Value::nil())
                    } else {
                        Value::nil()
                    };

                let path_str = vm.val_to_str(path_val);
                let mod_path = modname.replace('.', "/");

                let mut found_source = String::new();
                let mut found_filename = String::new();

                for template in path_str.split(';') {
                    let filename = template.replace('?', &mod_path);
                    if let Ok(content) = std::fs::read_to_string(&filename) {
                        found_source = content;
                        found_filename = filename;
                        break;
                    }
                }

                if found_source.is_empty() {
                    vm.runtime_error(&format!(
                        "module '{}' not found:\n\tno file in package.path",
                        modname
                    ));
                }

                match Compiler::compile(vm, &found_source, &found_filename) {
                    Ok(chunk_idx) => {
                        let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                        let closure_id = vm.alloc(GcObject::Closure {
                            chunk_idx,
                            upvalues: vec![env_upval],
                        });
                        loader = Value::obj(closure_id);
                    }
                    Err(err) => {
                        vm.runtime_error(&format!(
                            "error loading module '{}' from file '{}':\n\t{}",
                            modname, found_filename, err
                        ));
                    }
                }
            }

            if loaded_tab_val.is_obj() {
                if let Some(GcObject::Table(map, _)) =
                    &mut vm.objects[loaded_tab_val.as_obj() as usize]
                {
                    map.insert(modname_val, Value::bool(true));
                }
            }

            vm.internal_call(loader, vec![modname_val]);

            let mut has_ret = false;
            let mut ret_val = Value::nil();
            if vm.multiret_count > 0 {
                has_ret = true;
                ret_val = vm.data_stack.pop().unwrap();
                for _ in 1..vm.multiret_count {
                    vm.data_stack.pop();
                }
            }

            let mut final_result = ret_val;

            if loaded_tab_val.is_obj() {
                if has_ret && ret_val.0 != TAG_NIL {

                    if let Some(GcObject::Table(map, _)) =
                        &mut vm.objects[loaded_tab_val.as_obj() as usize]
                    {
                        map.insert(modname_val, ret_val);
                    }
                } else {

                    let current_loaded = if let Some(GcObject::Table(map, _)) =
                        &vm.objects[loaded_tab_val.as_obj() as usize]
                    {
                        map.get(&modname_val).copied().unwrap_or(Value::nil())
                    } else {
                        Value::nil()
                    };

                    if current_loaded.is_truthy() && current_loaded != Value::bool(true) {
                        final_result = current_loaded;
                    } else {

                        final_result = Value::bool(true);
                        if let Some(GcObject::Table(map, _)) =
                            &mut vm.objects[loaded_tab_val.as_obj() as usize]
                        {
                            map.insert(modname_val, final_result);
                        }
                    }
                }
            }

            vm.data_stack.push(final_result);
            1
        }));

        self.set_global("require", Value::obj(require_fn));
    }

    fn open_io_lib(&mut self) {
        let mut io_map = HashMap::new();
        let mut file_mt_map = HashMap::new();

        use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};

        // file:write(...)
        self.register_method(&mut file_mt_map, "write", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'write'");
            }
            let rc_file =
                if let Some(GcObject::File(rc, _)) = &vm.objects[args[0].as_obj() as usize] {
                    Some(rc.clone())
                } else {
                    None
                };

            let mut success = true;
            if let Some(rc) = rc_file {
                if let Some(file) = &mut *rc.borrow_mut() {
                    for arg in args.iter().skip(1) {
                        let text = vm.val_to_str(*arg);
                        if file.write_all(text.as_bytes()).is_err() {
                            success = false;
                            break;
                        }
                    }
                } else {
                    vm.runtime_error("attempt to use a closed file");
                }
            } else {
                vm.runtime_error("bad argument #1 to 'write' (FILE expected)");
            }

            if success {
                vm.data_stack.push(args[0]);
                1
            } else {
                vm.data_stack.push(Value::nil());
                1
            }
        });

        // file:read(...)
        self.register_method(&mut file_mt_map, "read", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'read'");
            }
            let mode = args
                .get(1)
                .map(|v| vm.val_to_str(*v))
                .unwrap_or_else(|| "*l".to_string());

            let rc_file =
                if let Some(GcObject::File(rc, _)) = &vm.objects[args[0].as_obj() as usize] {
                    Some(rc.clone())
                } else {
                    None
                };

            let mut result_str = String::new();
            let mut eof = false;

            if let Some(rc) = rc_file {
                if let Some(file) = &mut *rc.borrow_mut() {
                    if mode == "*a" {
                        if file.read_to_string(&mut result_str).is_err() {
                            eof = true;
                        }
                    } else if mode.starts_with("*n") {
                        let mut temp = String::new();
                        let mut reader = BufReader::new(file);
                        let mut in_number = false;
                        let mut buf = [0u8; 1];
                        while let Ok(1) = reader.read(&mut buf) {
                            let c = buf[0] as char;
                            if c.is_whitespace() {
                                if in_number {
                                    break;
                                }
                            } else {
                                in_number = true;
                                temp.push(c);
                            }
                        }
                        if temp.is_empty() {
                            eof = true;
                        } else {
                            result_str = temp;
                        }
                    } else {
                        if let Ok(bytes_to_read) = mode.parse::<usize>() {
                            let mut buf = vec![0u8; bytes_to_read];
                            if let Ok(read_len) = file.read(&mut buf) {
                                if read_len == 0 {
                                    eof = true;
                                } else {
                                    result_str =
                                        String::from_utf8_lossy(&buf[..read_len]).to_string();
                                }
                            }
                        } else {
                            let mut reader = BufReader::new(file);
                            if reader.read_line(&mut result_str).unwrap_or(0) == 0 {
                                eof = true;
                            }
                            result_str = result_str.trim_end_matches(&['\r', '\n'][..]).to_string();
                        }
                    }
                } else {
                    vm.runtime_error("attempt to use a closed file");
                }
            } else {
                vm.runtime_error("bad argument #1 to 'read' (FILE expected)");
            }

            if eof && result_str.is_empty() {
                vm.data_stack.push(Value::nil());
            } else if mode.starts_with("*n") {
                let parsed = if result_str.to_lowercase().starts_with("0x") {
                    Some(parse_hex_float(&result_str))
                } else {
                    result_str.parse::<f64>().ok()
                };
                if let Some(n) = parsed {
                    vm.data_stack.push(Value::num(n));
                } else {
                    vm.data_stack.push(Value::nil());
                }
            } else {
                let sv = vm.alloc_str(&result_str);
                vm.data_stack.push(sv);
            }
            1
        });

        // file:seek([whence [, offset]])
        self.register_method(&mut file_mt_map, "seek", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'seek'");
            }
            let whence_str = args
                .get(1)
                .map(|v| vm.val_to_str(*v))
                .unwrap_or_else(|| "cur".to_string());
            let offset = args.get(2).and_then(|v| vm.to_num(*v)).unwrap_or(0.0) as i64;
            let whence = match whence_str.as_str() {
                "set" => SeekFrom::Start(offset as u64),
                "end" => SeekFrom::End(offset),
                _ => SeekFrom::Current(offset),
            };

            let rc_file =
                if let Some(GcObject::File(rc, _)) = &vm.objects[args[0].as_obj() as usize] {
                    Some(rc.clone())
                } else {
                    None
                };
            if let Some(rc) = rc_file {
                if let Some(file) = &mut *rc.borrow_mut() {
                    match file.seek(whence) {
                        Ok(pos) => {
                            vm.data_stack.push(Value::num(pos as f64));
                            1
                        }
                        Err(_) => {
                            vm.data_stack.push(Value::nil());
                            1
                        }
                    }
                } else {
                    vm.runtime_error("attempt to use a closed file");
                }
            } else {
                vm.runtime_error("bad argument #1 to 'seek' (FILE expected)");
            }
        });

        // file:flush()
        self.register_method(&mut file_mt_map, "flush", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'flush'");
            }
            let rc_file =
                if let Some(GcObject::File(rc, _)) = &vm.objects[args[0].as_obj() as usize] {
                    Some(rc.clone())
                } else {
                    None
                };
            if let Some(rc) = rc_file {
                if let Some(file) = &mut *rc.borrow_mut() {
                    file.flush().unwrap_or(());
                    vm.data_stack.push(Value::bool(true));
                } else {
                    vm.runtime_error("attempt to use a closed file");
                }
            } else {
                vm.runtime_error("bad argument #1 to 'flush' (FILE expected)");
            }
            1
        });

        // file:close()
        self.register_method(&mut file_mt_map, "close", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'close'");
            }
            let rc_file =
                if let Some(GcObject::File(rc, _)) = &vm.objects[args[0].as_obj() as usize] {
                    Some(rc.clone())
                } else {
                    None
                };
            if let Some(rc) = rc_file {
                *rc.borrow_mut() = None;
                vm.data_stack.push(Value::bool(true));
            } else {
                vm.runtime_error("bad argument #1 to 'close' (FILE expected)");
            }
            1
        });

        self.register_method(&mut file_mt_map, "setvbuf", |vm, args| {
            vm.data_stack.push(Value::bool(true));
            1
        });

        let index_key = self.alloc_str("__index");
        let file_mt_id = self.alloc(GcObject::Table(file_mt_map, None));
        if let Some(GcObject::Table(m, _)) = &mut self.objects[file_mt_id as usize] {
            m.insert(index_key, Value::obj(file_mt_id));
        }

        // io.open(filename, mode)
        let open_fn = self.alloc(GcObject::NativeClosure(
            |vm, args, mt_val| {
                if args.is_empty() {
                    vm.runtime_error("bad argument #1 to 'open' (string expected)");
                }
                let filename = vm.val_to_str(args[0]);
                let mode = args
                    .get(1)
                    .map(|v| vm.val_to_str(*v))
                    .unwrap_or_else(|| "r".to_string());

                let mut opts = std::fs::OpenOptions::new();
                if mode.contains('w') {
                    opts.write(true).create(true).truncate(true);
                } else if mode.contains('a') {
                    opts.write(true).create(true).append(true);
                } else if mode.contains('r') && mode.contains('+') {
                    opts.read(true).write(true);
                } else {
                    opts.read(true);
                } // default 'r'

                match opts.open(&filename) {
                    Ok(file) => {
                        let file_id = vm.alloc(GcObject::File(
                            std::rc::Rc::new(std::cell::RefCell::new(Some(file))),
                            Some(mt_val.as_obj()),
                        ));
                        vm.data_stack.push(Value::obj(file_id));
                        1
                    }
                    Err(e) => {
                        vm.data_stack.push(Value::nil());
                        let err_msg = vm.alloc_str(&e.to_string());
                        vm.data_stack.push(err_msg);
                        2
                    }
                }
            },
            Value::obj(file_mt_id),
        ));

        io_map.insert(self.alloc_str("open"), Value::obj(open_fn));

        // io.type(obj)
        self.register_method(&mut io_map, "type", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'type'");
            }
            if args[0].is_obj() {
                if let Some(GcObject::File(rc_file, _)) = &vm.objects[args[0].as_obj() as usize] {
                    if rc_file.borrow().is_some() {
                        let v = vm.alloc_str("file");
                        vm.data_stack.push(v);
                        return 1;
                    } else {
                        let v = vm.alloc_str("closed file");
                        vm.data_stack.push(v);
                        return 1;
                    }
                }
            }
            vm.data_stack.push(Value::nil());
            1
        });

        self.register_method(&mut io_map, "input", |vm, args| {
            if args.is_empty() {
                let v = vm.get_global("_IO_input");
                vm.data_stack.push(v);
                return 1;
            }
            let target = args[0];
            if target.is_obj()
                && matches!(
                    vm.objects[target.as_obj() as usize],
                    Some(GcObject::File(..))
                )
            {
                vm.set_global("_IO_input", target);
            } else {
                let open = vm.get_global("io");
                let open_key = vm.alloc_str("open");
                let mode_key = vm.alloc_str("r");

                let mut open_fn_val = Value::nil();
                if let Some(GcObject::Table(m, _)) = &vm.objects[open.as_obj() as usize] {
                    if let Some(&f) = m.get(&open_key) {
                        open_fn_val = f;
                    }
                }

                if open_fn_val.is_truthy() {
                    vm.internal_call(open_fn_val, vec![target, mode_key]);

                    let count = vm.multiret_count;
                    let mut rets = Vec::new();
                    for _ in 0..count {
                        rets.push(vm.data_stack.pop().unwrap());
                    }
                    rets.reverse();

                    if count > 0 && rets[0].is_truthy() {
                        vm.set_global("_IO_input", rets[0]);
                    } else {

                        let err_msg = if count > 1 {
                            vm.val_to_str(rets[1])
                        } else {
                            "cannot open file".to_string()
                        };
                        vm.runtime_error(&err_msg);
                    }
                }
            }
            let v = vm.get_global("_IO_input");
            vm.data_stack.push(v);
            1
        });

        self.register_method(&mut io_map, "output", |vm, args| {
            if args.is_empty() {
                let v = vm.get_global("_IO_output");
                vm.data_stack.push(v);
                return 1;
            }
            let target = args[0];
            if target.is_obj()
                && matches!(
                    vm.objects[target.as_obj() as usize],
                    Some(GcObject::File(..))
                )
            {
                vm.set_global("_IO_output", target);
            } else {
                let open = vm.get_global("io");
                let open_key = vm.alloc_str("open");
                let mode_key = vm.alloc_str("w");

                let mut open_fn_val = Value::nil();
                if let Some(GcObject::Table(m, _)) = &vm.objects[open.as_obj() as usize] {
                    if let Some(&f) = m.get(&open_key) {
                        open_fn_val = f;
                    }
                }

                if open_fn_val.is_truthy() {
                    vm.internal_call(open_fn_val, vec![target, mode_key]);

                    let count = vm.multiret_count;
                    let mut rets = Vec::new();
                    for _ in 0..count {
                        rets.push(vm.data_stack.pop().unwrap());
                    }
                    rets.reverse();

                    if count > 0 && rets[0].is_truthy() {
                        vm.set_global("_IO_output", rets[0]);
                    } else {
                        let err_msg = if count > 1 {
                            vm.val_to_str(rets[1])
                        } else {
                            "cannot open file".to_string()
                        };
                        vm.runtime_error(&err_msg);
                    }
                }
            }
            let v = vm.get_global("_IO_output");
            vm.data_stack.push(v);
            1
        });

        // io.read(...)

        self.register_method(&mut io_map, "read", |vm, args| {
            let input = vm.get_global("_IO_input");
            if !input.is_truthy() {
                vm.runtime_error("default input file is not set");
            }
            let mut read_args = vec![input];
            read_args.extend_from_slice(&args);

            let mt_id = if let Some(GcObject::File(_, mt)) = &vm.objects[input.as_obj() as usize] {
                *mt
            } else {
                None
            };

            if let Some(id) = mt_id {
                let read_key = vm.alloc_str("read");
                let mut read_fn = Value::nil();
                if let Some(GcObject::Table(m, _)) = &vm.objects[id as usize] {
                    if let Some(&f) = m.get(&read_key) {
                        read_fn = f;
                    }
                }
                if read_fn.is_truthy() {
                    vm.internal_call(read_fn, read_args);
                    return vm.multiret_count;
                }
            }
            0
        });

        // io.write(...)

        self.register_method(&mut io_map, "write", |vm, args| {
            let output = vm.get_global("_IO_output");
            if !output.is_truthy() {
                vm.runtime_error("default output file is not set");
            }
            let mut write_args = vec![output];
            write_args.extend_from_slice(&args);

            let mt_id = if let Some(GcObject::File(_, mt)) = &vm.objects[output.as_obj() as usize] {
                *mt
            } else {
                None
            };

            if let Some(id) = mt_id {
                let write_key = vm.alloc_str("write");
                let mut write_fn = Value::nil();
                if let Some(GcObject::Table(m, _)) = &vm.objects[id as usize] {
                    if let Some(&f) = m.get(&write_key) {
                        write_fn = f;
                    }
                }
                if write_fn.is_truthy() {
                    vm.internal_call(write_fn, write_args);
                    return vm.multiret_count;
                }
            }
            0
        });

        // io.flush()

        self.register_method(&mut io_map, "flush", |vm, _| {
            let output = vm.get_global("_IO_output");
            if !output.is_truthy() {
                return 0;
            }

            let mt_id = if let Some(GcObject::File(_, mt)) = &vm.objects[output.as_obj() as usize] {
                *mt
            } else {
                None
            };

            if let Some(id) = mt_id {
                let flush_key = vm.alloc_str("flush");
                let mut flush_fn = Value::nil();
                if let Some(GcObject::Table(m, _)) = &vm.objects[id as usize] {
                    if let Some(&f) = m.get(&flush_key) {
                        flush_fn = f;
                    }
                }
                if flush_fn.is_truthy() {
                    vm.internal_call(flush_fn, vec![output]);
                    return vm.multiret_count;
                }
            }
            0
        });
        // io.close([file])
        self.register_method(&mut io_map, "close", |vm, args| {

            let target = if args.is_empty() || args[0].0 == TAG_NIL {
                vm.get_global("_IO_output")
            } else {
                args[0]
            };

            if !target.is_truthy() {
                vm.runtime_error("default output file is not set");
            }

            let mt_id = if let Some(GcObject::File(_, mt)) = &vm.objects[target.as_obj() as usize] {
                *mt
            } else {
                None
            };

            if let Some(id) = mt_id {
                let close_key = vm.alloc_str("close");
                let mut close_fn = Value::nil();

                if let Some(GcObject::Table(m, _)) = &vm.objects[id as usize] {
                    if let Some(&f) = m.get(&close_key) {
                        close_fn = f;
                    }
                }

                if close_fn.is_truthy() {
                    vm.internal_call(close_fn, vec![target]);
                    return vm.multiret_count;
                }
            }

            vm.runtime_error("bad argument to 'close' (FILE expected)");
            0
        });

        // io.lines([filename])
        let lines_fn = self.alloc(GcObject::NativeClosure(
            |vm, args, mt_val| {
                let file_val = if args.is_empty() {
                    vm.get_global("_IO_input")
                } else {
                    let filename = vm.val_to_str(args[0]);
                    let mut opts = std::fs::OpenOptions::new();
                    match opts.read(true).open(&filename) {
                        Ok(file) => {
                            let file_id = vm.alloc(GcObject::File(
                                std::rc::Rc::new(std::cell::RefCell::new(Some(file))),
                                Some(mt_val.as_obj()),
                            ));
                            Value::obj(file_id)
                        }
                        Err(e) => {
                            vm.runtime_error(&format!("cannot open file '{}': {}", filename, e))
                        }
                    }
                };

                let iter = vm.alloc(GcObject::NativeClosure(
                    |vm, _, state_val| {

                        if let Some(GcObject::File(rc_file, _)) =
                            &vm.objects[state_val.as_obj() as usize]
                        {
                            let mut eof = false;
                            let mut result_str = String::new();
                            if let Some(file) = &mut *rc_file.borrow_mut() {
                                use std::io::{BufRead, BufReader};
                                let mut reader = BufReader::new(file);
                                if reader.read_line(&mut result_str).unwrap_or(0) == 0 {
                                    eof = true;
                                }
                                result_str =
                                    result_str.trim_end_matches(&['\r', '\n'][..]).to_string();
                            }

                            if eof {
                                vm.data_stack.push(Value::nil());
                            } else {
                                let sv = vm.alloc_str(&result_str);
                                vm.data_stack.push(sv);
                            }
                            return 1;
                        }
                        0
                    },
                    file_val,
                ));

                vm.data_stack.push(Value::obj(iter));
                1
            },
            Value::obj(file_mt_id),
        ));

        io_map.insert(self.alloc_str("lines"), Value::obj(lines_fn));

        // io.tmpfile()
        let tmpfile_fn = self.alloc(GcObject::NativeClosure(
            |vm, _args, mt_val| {
                // 1. Generate a unique temporary file path using system time
                let t = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos();
                let mut path = std::env::temp_dir();
                path.push(format!("luaae_tmp_{:x}", t));

                let mut opts = std::fs::OpenOptions::new();
                // 2. Open in "w+" mode (read, write, create, truncate)
                match opts
                    .read(true)
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .open(&path)
                {
                    Ok(file) => {
                        // 3. Attempt to unlink (delete) the file immediately.
                        // On Unix-like systems, the file remains usable until closed, then vanishes.
                        // On Windows, this may fail if the file is held open, so we safely ignore errors.
                        let _ = std::fs::remove_file(&path);

                        // 4. Wrap the std::fs::File in your GcObject::File, attaching the file metatable
                        let file_id = vm.alloc(GcObject::File(
                            std::rc::Rc::new(std::cell::RefCell::new(Some(file))),
                            Some(mt_val.as_obj()),
                        ));

                        vm.data_stack.push(Value::obj(file_id));
                        1
                    }
                    Err(e) => {
                        // 5. If it fails, return nil + error message (Lua standard)
                        vm.data_stack.push(Value::nil());
                        let err_msg = vm.alloc_str(&e.to_string());
                        vm.data_stack.push(err_msg);
                        2
                    }
                }
            },
            Value::obj(file_mt_id),
        )); // Pass the file metatable ID as the closure state

        io_map.insert(self.alloc_str("tmpfile"), Value::obj(tmpfile_fn));

        let io_table = self.alloc(GcObject::Table(io_map, None));
        self.set_global("io", Value::obj(io_table));
    }

    fn open_debug_lib(&mut self) {
        let mut debug_map = HashMap::new();

        self.register_method(&mut debug_map, "getinfo", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'getinfo'");
            }
            let mut target_closure = None;
            let mut current_ip = 0;
            let mut is_active = false;

            if let Some(level) = vm.to_num(args[0]) {
                let lvl = level as usize;
                if lvl > vm.call_stack.len() || lvl == 0 {
                    vm.data_stack.push(Value::nil());
                    return 1;
                }
                let frame = &vm.call_stack[vm.call_stack.len() - lvl];
                target_closure = Some(frame.closure_id);
                current_ip = frame.ip.saturating_sub(1);
                is_active = true;
            }

            else if args[0].is_obj() {
                target_closure = Some(args[0].as_obj());
            }

            if let Some(cid) = target_closure {
                let mut info_map = HashMap::new();
                info_map.insert(vm.alloc_str("func"), Value::obj(cid));

                match vm.objects[cid as usize].clone() {
                    Some(GcObject::Closure { chunk_idx, .. }) => {

                        let (currentline, linedefined) = {
                            let chunk = &vm.chunks[chunk_idx];
                            let cl = if is_active {
                                chunk.lines.get(current_ip).copied().unwrap_or(0) as f64
                            } else {
                                -1.0
                            };
                            (cl, chunk.linedefined as f64)
                        };

                        let cl_key = vm.alloc_str("currentline");
                        info_map.insert(cl_key, Value::num(currentline));

                        let ld_key = vm.alloc_str("linedefined");
                        info_map.insert(ld_key, Value::num(linedefined));
                    }

                    Some(GcObject::NativeFn(_))
                    | Some(GcObject::NativeClosure(..))
                    | Some(GcObject::Continuation { .. }) => {
                        let cl_key = vm.alloc_str("currentline");
                        info_map.insert(cl_key, Value::num(-1.0));
                        let ld_key = vm.alloc_str("linedefined");
                        info_map.insert(ld_key, Value::num(-1.0));
                    }
                    _ => {}
                }

                let id = vm.alloc(GcObject::Table(info_map, None));
                vm.data_stack.push(Value::obj(id));
                return 1;
            }

            vm.data_stack.push(Value::nil());
            1
        });

        // debug.traceback([message], [level])
        self.register_method(&mut debug_map, "traceback", |vm, args| {
            let mut msg = args.get(0).map(|v| vm.val_to_str(*v)).unwrap_or_default();
            let level = args.get(1).and_then(|v| vm.to_num(*v)).unwrap_or(1.0) as usize;

            if !msg.is_empty() {
                msg.push_str("\n");
            }
            let skip = level.saturating_sub(1);
            msg.push_str(&vm.generate_traceback(skip));

            let str_val = vm.alloc_str(&msg);
            vm.data_stack.push(str_val);
            1
        });

        self.register_method(&mut debug_map, "getmetatable", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'getmetatable'");
            }
            if let Some(id) = vm.get_type_metatable(args[0]) {
                vm.data_stack.push(Value::obj(id));
            } else {
                vm.data_stack.push(Value::nil());
            }
            1
        });

        self.register_method(&mut debug_map, "setmetatable", |vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'setmetatable' (2 expected)");
            }
            let (target, mt) = (args[0], args[1]);
            let mt_id = if mt.0 == TAG_NIL {
                None
            } else {
                Some(mt.as_obj())
            };

            if target.is_obj() {
                match &mut vm.objects[target.as_obj() as usize] {
                    Some(GcObject::Table(_, meta)) | Some(GcObject::File(_, meta)) => {
                        *meta = mt_id;
                    }
                    Some(GcObject::Str(_)) => {
                        let k = vm.alloc_str("__mt_string");
                        if let Some(GcObject::Table(map, _)) =
                            &mut vm.objects[vm.global_env as usize]
                        {
                            map.insert(k, mt);
                        }
                    }
                    Some(GcObject::Closure { .. })
                    | Some(GcObject::NativeFn(_))
                    | Some(GcObject::NativeClosure(..)) => {
                        let k = vm.alloc_str("__mt_function");
                        if let Some(GcObject::Table(map, _)) =
                            &mut vm.objects[vm.global_env as usize]
                        {
                            map.insert(k, mt);
                        }
                    }
                    Some(GcObject::Thread(_)) => {
                        let k = vm.alloc_str("__mt_thread");
                        if let Some(GcObject::Table(map, _)) =
                            &mut vm.objects[vm.global_env as usize]
                        {
                            map.insert(k, mt);
                        }
                    }
                    _ => {}
                }
            } else {
                // Handling Primitive types
                let type_name = match target.0 {
                    TAG_NIL => "__mt_nil",
                    TAG_FALSE | TAG_TRUE => "__mt_boolean",
                    _ => "__mt_number",
                };

                let k = vm.alloc_str(type_name);

                if let Some(GcObject::Table(map, _)) = &mut vm.objects[vm.global_env as usize] {
                    if mt.0 == TAG_NIL {
                        // Delete the entry entirely if they pass nil!
                        map.remove(&k);
                    } else {
                        map.insert(k, mt);
                    }
                }
            }
            vm.data_stack.push(target);
            1
        });

        let debug_table = self.alloc(GcObject::Table(debug_map, None));
        self.set_global("debug", Value::obj(debug_table));
    }

    pub fn internal_call(&mut self, callable: Value, args: Vec<Value>) {
        if !callable.is_obj() {
            self.runtime_error("Attempt to call a non-function value in metamethod");
        }
        match self.objects[callable.as_obj() as usize].clone().unwrap() {
            GcObject::Closure { chunk_idx, .. } => {
                let param_count = self.chunks[chunk_idx].param_count;
                let local_count = self.chunks[chunk_idx].local_count;

                let mut fixed_params = args.clone();
                let varargs = if fixed_params.len() > param_count {
                    fixed_params.split_off(param_count)
                } else {
                    Vec::new()
                };

                let sb = self.data_stack.len();
                self.data_stack.extend(fixed_params);

                for _ in self.data_stack.len() - sb..local_count {
                    self.data_stack.push(Value::nil());
                }

                self.call_stack.push(CallFrame {
                    closure_id: callable.as_obj(),
                    chunk_idx,
                    ip: 0,
                    stack_base: sb,
                    handler_base: self.handler_stack.len(),
                    varargs,
                });

                let target_depth = self.call_stack.len() - 1;
                self.run_until(target_depth);
            }
            GcObject::NativeFn(func) => {
                let roots_start = self.temp_roots.len();
                self.temp_roots.extend(args.clone());
                self.temp_roots.push(callable);

                self.multiret_count = func(self, args);

                self.temp_roots.truncate(roots_start);
            }
            GcObject::NativeClosure(func, state) => {
                let roots_start = self.temp_roots.len();
                self.temp_roots.extend(args.clone());
                self.temp_roots.push(callable);

                self.multiret_count = func(self, args, state);

                self.temp_roots.truncate(roots_start);
            }
            _ => self.runtime_error("Uncallable object in metamethod"),
        }
    }

    pub fn run(&mut self) {
        self.run_until(0);
    }

    pub fn run_until(&mut self, target_depth: usize) {
        loop {
            if self.yielded {
                break;
            }
            if self.call_stack.len() <= target_depth {
                return;
            }

            let frame_idx = self.call_stack.len() - 1;
            let chunk_idx = self.call_stack[frame_idx].chunk_idx;
            let ip = self.call_stack[frame_idx].ip;

            if ip >= self.chunks[chunk_idx].instructions.len() {
                self.call_stack.pop();
                continue;
            }
            let inst = self.chunks[chunk_idx].instructions[ip];
            self.call_stack[frame_idx].ip += 1;

            match inst {
                OpCode::LoadConst(idx) => self
                    .data_stack
                    .push(self.chunks[chunk_idx].constants[idx as usize]),
                OpCode::LoadLocal(idx) => {
                    let base = self.call_stack[frame_idx].stack_base;
                    let mut val = self.data_stack[base + idx as usize];
                    if val.is_obj() {
                        if let Some(GcObject::Upval(inner)) = &self.objects[val.as_obj() as usize] {
                            val = *inner;
                        }
                    }
                    self.data_stack.push(val);
                }
                OpCode::StoreLocal(idx) => {
                    let base = self.call_stack[frame_idx].stack_base;
                    let val = *self.data_stack.last().unwrap();
                    let slot = self.data_stack[base + idx as usize];
                    let mut is_upval = false;
                    if slot.is_obj() {
                        if let Some(GcObject::Upval(inner)) =
                            &mut self.objects[slot.as_obj() as usize]
                        {
                            *inner = val;
                            is_upval = true;
                        }
                    }
                    if !is_upval {
                        self.data_stack[base + idx as usize] = val;
                    }
                }
                OpCode::LoadUpval(idx) => {
                    let curr_closure_id = self.call_stack[frame_idx].closure_id;
                    let upval_id = if let Some(GcObject::Closure { upvalues, .. }) =
                        &self.objects[curr_closure_id as usize]
                    {
                        upvalues[idx as usize]
                    } else {
                        unreachable!()
                    };
                    if let Some(GcObject::Upval(v)) = &self.objects[upval_id as usize] {
                        self.data_stack.push(*v);
                    } else {
                        unreachable!()
                    }
                }
                OpCode::StoreUpval(idx) => {
                    let val = *self.data_stack.last().unwrap();
                    let curr_closure_id = self.call_stack[frame_idx].closure_id;
                    let upval_id = if let Some(GcObject::Closure { upvalues, .. }) =
                        &self.objects[curr_closure_id as usize]
                    {
                        upvalues[idx as usize]
                    } else {
                        unreachable!()
                    };
                    if let Some(GcObject::Upval(inner)) = &mut self.objects[upval_id as usize] {
                        *inner = val;
                    } else {
                        unreachable!()
                    }
                }
                // OpCode::LoadGlobal(name_id) => { let name = &self.strings[name_id as usize]; let val = self.get_global(name).copied().unwrap_or(Value::nil()); self.data_stack.push(val); }
                // OpCode::StoreGlobal(name_id) => { let name = self.strings[name_id as usize].clone(); let val = *self.data_stack.last().unwrap(); self.set_global(name, val); }
                OpCode::Pop => {
                    self.data_stack.pop();
                }
                OpCode::PushNil => {
                    self.data_stack.push(Value::nil());
                }
                OpCode::Dup => {
                    let val = *self.data_stack.last().unwrap();
                    self.data_stack.push(val);
                }
                OpCode::PushNil => {
                    self.data_stack.push(Value::nil());
                }
                OpCode::PushTrue => {
                    self.data_stack.push(Value::bool(true));
                }
                OpCode::PushFalse => {
                    self.data_stack.push(Value::bool(false));
                }
                OpCode::Swap => {
                    let len = self.data_stack.len();
                    self.data_stack.swap(len - 1, len - 2);
                }
                OpCode::ForceNum => {
                    let val = self.data_stack.pop().unwrap();
                    if let Some(n) = self.to_num(val) {
                        self.data_stack.push(Value::num(n));
                    } else {
                        self.runtime_error(&format!(
                            "'for' loop initial/limit/step must be a number, got {}",
                            self.val_to_str(val)
                        ));
                    }
                }
                OpCode::Not => {
                    let a = self.data_stack.pop().unwrap();
                    self.data_stack.push(Value::bool(!a.is_truthy()));
                }

                OpCode::Add => bin_op!(self, +, "__add"),
                OpCode::Sub => bin_op!(self, -, "__sub"),
                OpCode::Mul => bin_op!(self, *, "__mul"),
                OpCode::Div => bin_op!(self, /, "__div"),
                OpCode::Mod => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    if let (Some(a), Some(b)) = (self.to_num(a_val), self.to_num(b_val)) {
                        let res = a - (a / b).floor() * b;
                        self.data_stack.push(Value::num(res));
                    } else {
                        let mut mm = self.get_metamethod(a_val, "__mod");
                        if mm.is_none() {
                            mm = self.get_metamethod(b_val, "__mod");
                        }

                        if let Some(func) = mm {
                            if !self.trigger_metamethod(func, vec![a_val, b_val]) {
                                self.runtime_error(
                                    "attempt to perform arithmetic on an uncallable metamethod",
                                );
                            }
                        } else {
                            self.runtime_error("attempt to perform arithmetic on a non-number");
                        }
                    }
                }
                OpCode::BitAnd => bit_op!(self, &, "__band"),
                OpCode::BitOr => bit_op!(self, |, "__bor"),
                OpCode::BitXor => bit_op!(self, ^, "__bxor"),
                OpCode::Shl => bit_op!(self, <<, "__shl"),
                OpCode::Shr => bit_op!(self, >>, "__shr"),
                OpCode::Pow => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    if let (Some(a), Some(b)) = (self.to_num(a_val), self.to_num(b_val)) {

                        self.data_stack.push(Value::num(a.powf(b)));
                    } else {

                        let mut mm = self.get_metamethod(a_val, "__pow");
                        if mm.is_none() {
                            mm = self.get_metamethod(b_val, "__pow");
                        }

                        if let Some(func) = mm {
                            if !self.trigger_metamethod(func, vec![a_val, b_val]) {
                                self.runtime_error(
                                    "attempt to perform exponentiation on an uncallable metamethod",
                                );
                            }
                        } else {
                            self.runtime_error("attempt to perform arithmetic on a non-number");
                        }
                    }
                }
                OpCode::FloorDiv => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    if let (Some(a), Some(b)) = (self.to_num(a_val), self.to_num(b_val)) {
                        self.data_stack.push(Value::num((a / b).floor()));
                    } else {
                        let mut mm = self.get_metamethod(a_val, "__idiv");
                        if mm.is_none() {
                            mm = self.get_metamethod(b_val, "__idiv");
                        }

                        if let Some(func) = mm {
                            if !self.trigger_metamethod(func, vec![a_val, b_val]) {
                                self.runtime_error(
                                    "attempt to perform floor division on an uncallable metamethod",
                                );
                            }
                        } else {
                            self.runtime_error("attempt to perform arithmetic on a non-number");
                        }
                    }
                }

                OpCode::Lt => cmp_op!(self, <, "__lt", false),
                OpCode::Gt => cmp_op!(self, >, "__lt", true),
                OpCode::LtEq => cmp_op!(self, <=, "__le", false, "__lt", true),
                OpCode::GtEq => cmp_op!(self, >=, "__le", true, "__lt", false),
                OpCode::Neq => {
                    let b = self.data_stack.pop().unwrap();
                    let a = self.data_stack.pop().unwrap();
                    self.data_stack.push(Value::bool(a.0 != b.0));
                }

                OpCode::Neg => {
                    let val = self.data_stack.pop().unwrap();
                    if let Some(n) = self.to_num(val) {
                        self.data_stack.push(Value::num(-n));
                    } else if let Some(mm) = self.get_metamethod(val, "__unm") {
                        if !self.trigger_metamethod(mm, vec![val]) {
                            self.runtime_error(
                                "attempt to perform arithmetic on an uncallable __unm metamethod",
                            );
                        }
                    } else {
                        self.runtime_error("attempt to perform arithmetic on a non-number");
                    }
                }

                OpCode::Concat => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    let a_is_str = a_val.is_obj()
                        && matches!(
                            &self.objects[a_val.as_obj() as usize],
                            Some(GcObject::Str(_))
                        );
                    let b_is_str = b_val.is_obj()
                        && matches!(
                            &self.objects[b_val.as_obj() as usize],
                            Some(GcObject::Str(_))
                        );

                    let a_is_valid = a_is_str || self.to_num(a_val).is_some();
                    let b_is_valid = b_is_str || self.to_num(b_val).is_some();

                    if a_is_valid && b_is_valid {

                        let a_str = self.val_to_str(a_val);
                        let b_str = self.val_to_str(b_val);
                        let new_str = self.alloc_str(&(a_str + &b_str));
                        self.data_stack.push(new_str);
                    } else {

                        let mut mm = self.get_metamethod(a_val, "__concat");
                        if mm.is_none() {
                            mm = self.get_metamethod(b_val, "__concat");
                        }

                        if let Some(func) = mm {
                            if !self.trigger_metamethod(func, vec![a_val, b_val]) {
                                self.runtime_error(
                                    "attempt to concatenate with an uncallable __concat metamethod",
                                );
                            }
                        } else {
                            self.runtime_error("attempt to concatenate unconcatable types");
                        }
                    }
                }
                OpCode::Eq => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    let mut is_eq = a_val == b_val;

                    if is_eq
                        && !a_val.is_obj()
                        && a_val.0 != TAG_NIL
                        && a_val.0 != TAG_FALSE
                        && a_val.0 != TAG_TRUE
                    {
                        if a_val.as_num().is_nan() {
                            is_eq = false;
                        }
                    }

                    if is_eq {
                        self.data_stack.push(Value::bool(true));
                    } else {

                        let mm_a = self.get_metamethod(a_val, "__eq");
                        let mm_a = self.get_metamethod(a_val, "__eq");
                        let mm_b = self.get_metamethod(b_val, "__eq");

                        let mut handled = false;
                        if let (Some(func_a), Some(func_b)) = (mm_a, mm_b) {
                            if func_a == func_b {
                                if self.trigger_metamethod(func_a, vec![a_val, b_val]) {
                                    handled = true;
                                }
                            }
                        }

                        if !handled {
                            self.data_stack.push(Value::bool(false));
                        }
                    }
                }

                OpCode::Len => {
                    let val = self.data_stack.pop().unwrap();
                    if let Some(mm) = self.get_metamethod(val, "__len") {
                        if !self.trigger_metamethod(mm, vec![val]) {
                            self.runtime_error(
                                "attempt to get length of object with uncallable __len",
                            );
                        }
                    } else if val.is_obj() {
                        match &self.objects[val.as_obj() as usize].as_ref().unwrap() {
                            GcObject::Str(s) => self.data_stack.push(Value::num(s.len() as f64)),
                            GcObject::Table(m, _) => {
                                let mut len = 0;
                                loop {
                                    if let Some(v) = m.get(&Value::num((len + 1) as f64)) {
                                        if v.0 != TAG_NIL {
                                            len += 1;
                                            continue;
                                        }
                                    }
                                    break;
                                }
                                self.data_stack.push(Value::num(len as f64));
                            }
                            _ => self.runtime_error("Len operator applied to invalid object type"),
                        }
                    } else {
                        self.runtime_error("Len operator applied to non-object");
                    }
                }

                OpCode::MakeTable => {
                    let id = self.alloc(GcObject::Table(HashMap::new(), None));
                    self.data_stack.push(Value::obj(id));
                }
                OpCode::GetTable => {
                    let key = self.data_stack.pop().unwrap();
                    let current = self.data_stack.pop().unwrap();
                    get_table_core!(self, current, key, frame_idx, chunk_idx);
                }
                OpCode::GetTabUp(upv_idx, const_idx) => {
                    let curr_closure_id = self.call_stack[frame_idx].closure_id;
                    let upval_id = if let Some(GcObject::Closure { upvalues, .. }) =
                        &self.objects[curr_closure_id as usize]
                    {
                        upvalues[upv_idx as usize]
                    } else {
                        unreachable!()
                    };
                    let current = if let Some(GcObject::Upval(v)) = &self.objects[upval_id as usize]
                    {
                        *v
                    } else {
                        unreachable!()
                    };
                    let key = self.chunks[chunk_idx].constants[const_idx as usize];
                    get_table_core!(self, current, key, frame_idx, chunk_idx);
                }
                OpCode::SetTable => {
                    let val = self.data_stack.pop().unwrap();
                    let key = self.data_stack.pop().unwrap();
                    let current = self.data_stack.pop().unwrap();
                    set_table_core!(self, current, key, val, frame_idx);
                }
                OpCode::SetTabUp(upv_idx, const_idx) => {
                    let val = self.data_stack.pop().unwrap();
                    let curr_closure_id = self.call_stack[frame_idx].closure_id;
                    let upval_id = if let Some(GcObject::Closure { upvalues, .. }) =
                        &self.objects[curr_closure_id as usize]
                    {
                        upvalues[upv_idx as usize]
                    } else {
                        unreachable!()
                    };
                    let current = if let Some(GcObject::Upval(v)) = &self.objects[upval_id as usize]
                    {
                        *v
                    } else {
                        unreachable!()
                    };
                    let key = self.chunks[chunk_idx].constants[const_idx as usize];
                    set_table_core!(self, current, key, val, frame_idx);
                }
                OpCode::SetTabLocal(local_idx, const_idx) => {
                    let val = self.data_stack.pop().unwrap();
                    let base = self.call_stack[frame_idx].stack_base;
                    let current = self.data_stack[base + local_idx as usize];
                    let key = self.chunks[chunk_idx].constants[const_idx as usize];
                    set_table_core!(self, current, key, val, frame_idx);
                }
                OpCode::AppendMulti => {
                    let count = self.multiret_count;
                    let mut vals = Vec::new();

                    for _ in 0..count {
                        vals.push(self.data_stack.pop().unwrap());
                    }
                    vals.reverse();

                    let start_key = self.data_stack.pop().unwrap().as_num() as i64;
                    let table_val = self.data_stack.pop().unwrap();

                    if let Some(GcObject::Table(map, _)) =
                        &mut self.objects[table_val.as_obj() as usize]
                    {
                        for (i, val) in vals.into_iter().enumerate() {
                            map.insert(Value::num((start_key + i as i64) as f64), val);
                        }
                    }
                }

                OpCode::JumpIfFalse(target_ip) => {
                    let cond = self.data_stack.pop().unwrap();
                    if !cond.is_truthy() {
                        self.call_stack[frame_idx].ip = target_ip;
                    }
                }
                OpCode::Jump(target_ip) => {
                    self.call_stack[frame_idx].ip = target_ip;
                }
                OpCode::JumpIfFalseKeep(target_ip) => {
                    let cond = self.data_stack.last().unwrap();
                    if !cond.is_truthy() {
                        self.call_stack[frame_idx].ip = target_ip;
                    }
                }
                OpCode::JumpIfTrueKeep(target_ip) => {
                    let cond = self.data_stack.last().unwrap();
                    if cond.is_truthy() {
                        self.call_stack[frame_idx].ip = target_ip;
                    }
                }

                OpCode::MakeClosure(c_idx) => {
                    let mut captured = Vec::new();
                    for idx in 0..self.chunks[c_idx as usize].upvals.len() {
                        let (is_local, parent_idx, _) = self.chunks[c_idx as usize].upvals[idx];
                        if is_local {
                            let base = self.call_stack[frame_idx].stack_base;
                            let slot_val = self.data_stack[base + parent_idx];
                            let upval_id = if slot_val.is_obj()
                                && matches!(
                                    self.objects[slot_val.as_obj() as usize],
                                    Some(GcObject::Upval(_))
                                ) {
                                slot_val.as_obj()
                            } else {
                                let id = self.alloc(GcObject::Upval(slot_val));
                                self.data_stack[base + parent_idx] = Value::obj(id); // Box local safely
                                id
                            };
                            captured.push(upval_id);
                        } else {
                            let curr_closure_id = self.call_stack[frame_idx].closure_id;
                            if let Some(GcObject::Closure { upvalues, .. }) =
                                &self.objects[curr_closure_id as usize]
                            {
                                captured.push(upvalues[parent_idx]);
                            } else {
                                unreachable!()
                            }
                        }
                    }
                    let id = self.alloc(GcObject::Closure {
                        chunk_idx: c_idx as usize,
                        upvalues: captured,
                    });
                    self.data_stack.push(Value::obj(id));
                }
                OpCode::CloseLocals(start_idx) => {
                    let base = self.call_stack[frame_idx].stack_base;
                    let start = base + start_idx as usize;
                    let end = base + self.chunks[chunk_idx].local_count;
                    for i in start..end {
                        self.data_stack[i] = Value::nil();
                    }
                }
                OpCode::DetachUpvals(start_idx, count) => {
                    let base = self.call_stack[frame_idx].stack_base;
                    let start = base + start_idx as usize;
                    let end = start + count as usize;

                    for i in start..end {
                        let val = self.data_stack[i];
                        if val.is_obj() {
                            if let Some(GcObject::Upval(inner)) =
                                self.objects[val.as_obj() as usize]
                            {
                                // Pull the inner value out of the heap box
                                // and put it flat on the stack. The old closure keeps the box
                                self.data_stack[i] = inner;
                            }
                        }
                    }
                }
                OpCode::Call(fixed_args, has_multi) => {
                    let dyn_count = if has_multi { self.multiret_count } else { 1 };
                    let total_args = if has_multi {
                        fixed_args as usize - 1 + dyn_count
                    } else {
                        fixed_args as usize
                    };
                    let callee_idx = self.data_stack.len() - 1 - total_args;
                    let callable = self.data_stack[callee_idx];

                    let mut resolved_callable = callable;
                    let mut is_metamethod = false;

                    if !callable.is_obj()
                        || matches!(
                            &self.objects[callable.as_obj() as usize],
                            Some(GcObject::Table(..)) | Some(GcObject::Str(_))
                        )
                    {
                        if let Some(mm) = self.get_metamethod(callable, "__call") {
                            resolved_callable = mm;
                            is_metamethod = true;
                        } else {
                            self.runtime_error(&format!(
                                "Attempt to call a non-function value: {}",
                                self.val_to_str(callable)
                            ));
                        }
                    }

                    match self.objects[resolved_callable.as_obj() as usize]
                        .clone()
                        .unwrap()
                    {
                        GcObject::Closure { chunk_idx, .. } => {
                            let mut args = Vec::new();
                            for _ in 0..total_args {
                                args.push(self.data_stack.pop().unwrap());
                            }
                            args.reverse();
                            self.data_stack.pop();

                            if is_metamethod {
                                args.insert(0, callable);
                            }

                            let param_count = self.chunks[chunk_idx].param_count;
                            let local_count = self.chunks[chunk_idx].local_count;

                            let mut fixed_params = args.clone();
                            let varargs = if fixed_params.len() > param_count {
                                fixed_params.split_off(param_count)
                            } else {
                                Vec::new()
                            };

                            let sb = self.data_stack.len();

                            self.data_stack.extend(fixed_params);

                            for _ in self.data_stack.len() - sb..local_count {
                                self.data_stack.push(Value::nil());
                            }

                            self.call_stack.push(CallFrame {
                                closure_id: resolved_callable.as_obj(),
                                chunk_idx,
                                ip: 0,
                                stack_base: sb,
                                handler_base: self.handler_stack.len(),
                                varargs,
                            });
                        }

                        GcObject::Continuation {
                            calls,
                            data,
                            handlers,
                            orig_call_depth,
                            orig_data_depth,
                            orig_handler_depth,
                        } => {
                            let mut args = Vec::new();
                            for _ in 0..total_args {
                                args.push(self.data_stack.pop().unwrap());
                            }
                            args.reverse();

                            self.data_stack.pop();

                            if is_metamethod {
                                args.insert(0, callable);
                            }

                            let mut cloned_calls = calls.clone();
                            let mut cloned_data = data.clone();
                            let mut cloned_handlers = handlers.clone();

                            let call_offset = self.call_stack.len() - orig_call_depth;
                            let data_offset = self.data_stack.len() - orig_data_depth;
                            let handler_offset = self.handler_stack.len() - orig_handler_depth;

                            for frame in &mut cloned_calls {
                                frame.stack_base += data_offset;
                                frame.handler_base += handler_offset;
                            }
                            for h in &mut cloned_handlers {
                                h.call_depth += call_offset;
                                h.data_depth += data_offset;
                            }

                            self.call_stack.extend(cloned_calls);
                            self.data_stack.extend(cloned_data);
                            self.handler_stack.extend(cloned_handlers);

                            self.data_stack.extend(&args);
                            self.multiret_count = args.len();
                        }
                        GcObject::NativeFn(func) => {
                            let mut args = Vec::new();
                            for _ in 0..total_args {
                                args.push(self.data_stack.pop().unwrap());
                            }
                            args.reverse();
                            let callable_val = self.data_stack.pop().unwrap();

                            if is_metamethod {
                                args.insert(0, callable_val);
                            }

                            let roots_start = self.temp_roots.len();
                            self.temp_roots.extend(args.clone());
                            self.temp_roots.push(callable_val);

                            self.multiret_count = func(self, args);

                            self.temp_roots.truncate(roots_start);
                        }
                        GcObject::NativeClosure(func, state) => {
                            let mut args = Vec::new();
                            for _ in 0..total_args {
                                args.push(self.data_stack.pop().unwrap());
                            }
                            args.reverse();
                            let callable_val = self.data_stack.pop().unwrap();

                            if is_metamethod {
                                args.insert(0, callable_val);
                            }

                            let roots_start = self.temp_roots.len();
                            self.temp_roots.extend(args.clone());
                            self.temp_roots.push(callable_val);

                            self.multiret_count = func(self, args, state);

                            self.temp_roots.truncate(roots_start);
                        }
                        _ => self.runtime_error("Uncallable object"),
                    }
                }
                OpCode::Return(fixed, has_multi) => {
                    let frame = self.call_stack.pop().unwrap();
                    let dyn_count = if has_multi { self.multiret_count } else { 1 };
                    let total = if has_multi {
                        fixed as usize - 1 + dyn_count
                    } else {
                        fixed as usize
                    };
                    let mut rets = Vec::new();
                    for _ in 0..total {
                        rets.push(self.data_stack.pop().unwrap());
                    }
                    rets.reverse();
                    self.handler_stack.truncate(frame.handler_base);
                    self.data_stack.truncate(frame.stack_base);
                    self.data_stack.extend(rets);
                    self.multiret_count = total;
                }
                OpCode::TailCall(fixed_args, has_multi) => {
                    let dyn_count = if has_multi { self.multiret_count } else { 1 };
                    let total_args = if has_multi {
                        fixed_args as usize - 1 + dyn_count
                    } else {
                        fixed_args as usize
                    };
                    let callee_idx = self.data_stack.len() - 1 - total_args;
                    let callable = self.data_stack[callee_idx];

                    let mut resolved_callable = callable;
                    let mut is_metamethod = false;

                    if !callable.is_obj()
                        || matches!(
                            &self.objects[callable.as_obj() as usize],
                            Some(GcObject::Table(..)) | Some(GcObject::Str(_))
                        )
                    {
                        if let Some(mm) = self.get_metamethod(callable, "__call") {
                            resolved_callable = mm;
                            is_metamethod = true;
                        } else {
                            self.runtime_error(&format!(
                                "Attempt to tail call a non-function value: {}",
                                self.val_to_str(callable)
                            ));
                        }
                    }

                    match self.objects[resolved_callable.as_obj() as usize]
                        .clone()
                        .unwrap()
                    {
                        GcObject::Closure { chunk_idx, .. } => {
                            let mut args = Vec::new();
                            for _ in 0..total_args {
                                args.push(self.data_stack.pop().unwrap());
                            }
                            args.reverse();
                            self.data_stack.pop();

                            if is_metamethod {
                                args.insert(0, callable);
                            }

                            let param_count = self.chunks[chunk_idx].param_count;
                            let local_count = self.chunks[chunk_idx].local_count;

                            let mut fixed_params = args.clone();
                            let varargs = if fixed_params.len() > param_count {
                                fixed_params.split_off(param_count)
                            } else {
                                Vec::new()
                            };

                            let current_frame = self.call_stack.last_mut().unwrap();

                            self.data_stack.truncate(current_frame.stack_base);

                            self.data_stack.extend(fixed_params);
                            for _ in self.data_stack.len() - current_frame.stack_base..local_count {
                                self.data_stack.push(Value::nil());
                            }

                            current_frame.closure_id = resolved_callable.as_obj();
                            current_frame.chunk_idx = chunk_idx;
                            current_frame.ip = 0;
                            current_frame.varargs = varargs;
                        }
                        GcObject::Continuation {
                            calls,
                            data,
                            handlers,
                            orig_call_depth,
                            orig_data_depth,
                            orig_handler_depth,
                        } => {
                            let mut args = Vec::new();
                            for _ in 0..total_args {
                                args.push(self.data_stack.pop().unwrap());
                            }
                            args.reverse();
                            self.data_stack.pop();

                            if is_metamethod {
                                args.insert(0, callable);
                            }

                            let current_frame = self.call_stack.pop().unwrap();
                            self.handler_stack.truncate(current_frame.handler_base);
                            self.data_stack.truncate(current_frame.stack_base);

                            let mut cloned_calls = calls.clone();
                            let mut cloned_data = data.clone();
                            let mut cloned_handlers = handlers.clone();

                            let call_offset = self.call_stack.len() - orig_call_depth;
                            let data_offset = self.data_stack.len() - orig_data_depth;
                            let handler_offset = self.handler_stack.len() - orig_handler_depth;

                            for frame in &mut cloned_calls {
                                frame.stack_base += data_offset;
                                frame.handler_base += handler_offset;
                            }
                            for h in &mut cloned_handlers {
                                h.call_depth += call_offset;
                                h.data_depth += data_offset;
                            }

                            self.call_stack.extend(cloned_calls);
                            self.data_stack.extend(cloned_data);
                            self.handler_stack.extend(cloned_handlers);

                            self.data_stack.extend(&args);
                            self.multiret_count = args.len();
                        }
                        GcObject::NativeFn(func) => {
                            let mut args = Vec::new();
                            let start_idx = self.data_stack.len() - total_args;
                            for i in 0..total_args {
                                args.push(self.data_stack[start_idx + i]);
                            }

                            if is_metamethod {
                                args.insert(0, callable);
                            }
                            self.multiret_count = func(self, args);

                            let mut rets = Vec::new();
                            for _ in 0..self.multiret_count {
                                rets.push(self.data_stack.pop().unwrap());
                            }
                            rets.reverse();

                            let frame = self.call_stack.pop().unwrap();
                            self.handler_stack.truncate(frame.handler_base);
                            self.data_stack.truncate(frame.stack_base); // <--- Truncate implicitly unroots the args
                            self.data_stack.extend(rets);
                        }
                        GcObject::NativeClosure(func, state) => {
                            let mut args = Vec::new();
                            let start_idx = self.data_stack.len() - total_args;
                            for i in 0..total_args {
                                args.push(self.data_stack[start_idx + i]);
                            }

                            if is_metamethod {
                                args.insert(0, callable);
                            }
                            self.multiret_count = func(self, args, state);

                            let mut rets = Vec::new();
                            for _ in 0..self.multiret_count {
                                rets.push(self.data_stack.pop().unwrap());
                            }
                            rets.reverse();

                            let frame = self.call_stack.pop().unwrap();
                            self.handler_stack.truncate(frame.handler_base);
                            self.data_stack.truncate(frame.stack_base);
                            self.data_stack.extend(rets);
                        }
                        _ => self.runtime_error("Uncallable object in tail call"),
                    }
                }

                OpCode::LoadVararg => {
                    let frame = self.call_stack.last().unwrap();
                    let count = frame.varargs.len();
                    for val in &frame.varargs {
                        self.data_stack.push(*val);
                    }
                    self.multiret_count = count;
                }
                OpCode::AdjustStack(expected) => {
                    let expected = expected as usize;
                    let current = self.multiret_count;
                    if current > expected {
                        for _ in 0..(current - expected) {
                            self.data_stack.pop();
                        }
                    } else if current < expected {
                        for _ in 0..(expected - current) {
                            self.data_stack.push(Value::nil());
                        }
                    }
                    self.multiret_count = expected;
                }
                OpCode::PushStash => {
                    let val = self.data_stack.pop().unwrap();
                    self.temp_roots.push(val);
                }
                OpCode::PopStash => {
                    let val = self.temp_roots.pop().unwrap();
                    self.data_stack.push(val);
                }
                OpCode::ReverseStash(n) => {
                    let len = self.temp_roots.len();
                    self.temp_roots[len - n as usize..].reverse();
                }
                OpCode::ForCond => {
                    // 1. First, pop the values (mutable borrow of self.data_stack)
                    let step_val = self.data_stack.pop().unwrap();
                    let limit_val = self.data_stack.pop().unwrap();
                    let curr_val = self.data_stack.pop().unwrap();

                    // 2. Then, convert them to numbers (immutable borrow of self)
                    let step = self.to_num(step_val).unwrap_or(0.0);
                    let limit = self.to_num(limit_val).unwrap_or(0.0);
                    let curr = self.to_num(curr_val).unwrap_or(0.0);

                    // 3. Evaluate the condition based on the step's direction
                    let cond = if step >= 0.0 {
                        curr <= limit
                    } else {
                        curr >= limit
                    };
                    self.data_stack.push(Value::bool(cond));
                }

                // Effect OpCodes
                OpCode::PushHandler(eff_id) => {
                    let closure_val = self.data_stack.pop().unwrap();
                    self.handler_stack.push(HandlerFrame {
                        effect_id: eff_id,
                        closure_id: closure_val.as_obj(),
                        call_depth: self.call_stack.len(),
                        data_depth: self.data_stack.len(),
                        is_active: true,
                    });
                }
                OpCode::PopHandler => {
                    self.handler_stack.pop();
                }
                OpCode::Perform(eff_id, arg_count) => {
                    let handler_idx_opt = self
                        .handler_stack
                        .iter()
                        .rposition(|h| h.effect_id == eff_id && h.is_active);
                
                    let handler_idx = match handler_idx_opt {
                        Some(idx) => idx,
                        None => {
                            let eff_name = self.strings.get(eff_id as usize)
                                .map(|s| s.as_str())
                                .unwrap_or("<unknown>");
                            self.runtime_error(&format!("unhandled effect '{}'", eff_name));
                        }
                    };
                
                    self.handler_stack[handler_idx].is_active = false;
                    let handler = self.handler_stack[handler_idx].clone();
                    let mut args = Vec::new();
                    for _ in 0..arg_count {
                        args.push(self.data_stack.pop().unwrap());
                    }
                    args.reverse();
                    let mut cap_calls = self.call_stack.split_off(handler.call_depth);
                    let cap_data = self.data_stack.split_off(handler.data_depth);
                    let mut cap_handlers = self.handler_stack.split_off(handler_idx + 1);
                    for f in &mut cap_calls {
                        f.handler_base += 1;
                    }
                    let mut reinjected = handler.clone();
                    reinjected.is_active = true;
                    cap_handlers.insert(0, reinjected);
                    let cont_id = self.alloc(GcObject::Continuation {
                        calls: cap_calls,
                        data: cap_data,
                        handlers: cap_handlers,
                        orig_call_depth: handler.call_depth,
                        orig_data_depth: handler.data_depth,
                        orig_handler_depth: handler_idx + 1,
                    });
                    let c_idx = if let Some(GcObject::Closure { chunk_idx, .. }) =
                        &self.objects[handler.closure_id as usize]
                    {
                        *chunk_idx
                    } else {
                        unreachable!()
                    };
                    self.data_stack.extend(args);
                    self.data_stack.push(Value::obj(cont_id));
                    let passed = arg_count as usize + 1;
                    let sb = self.data_stack.len() - passed;
                    for _ in 0..self.chunks[c_idx].local_count.saturating_sub(passed) {
                        self.data_stack.push(Value::nil());
                    }
                    self.call_stack.push(CallFrame {
                        closure_id: handler.closure_id,
                        chunk_idx: c_idx,
                        ip: 0,
                        stack_base: sb,
                        handler_base: self.handler_stack.len(),
                        varargs: Vec::new(),
                    });
                }
                _ => {}
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Ident(String),
    Num(f64),
    StringLiteral(String),
    Local,
    Function,
    End,
    Do,
    Then,
    If,
    Elseif,
    Else,
    While,
    Repeat,
    Until,
    For,
    In,
    Return,
    Break,
    Nil,
    True,
    False,
    And,
    Or,
    Not,
    Perform,
    Handle,
    With,
    Continue,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    FloorDiv,
    Caret,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    EqEq,
    Neq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    DotDot,
    Hash,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Dot,
    Comma,
    Semi,
    Colon,
    DotDotDot,
    EOF,
}

pub struct Scanner<'a> {
    chars: Peekable<Chars<'a>>,
    pub line: usize,
    pub col: usize,
    pub token_start_line: usize,
    pub token_start_col: usize,
}

fn parse_hex_float(s: &str) -> f64 {
    let s = if s.to_lowercase().starts_with("0x") {
        &s[2..]
    } else {
        s
    };
    let mut parts = s.splitn(2, |c| c == 'p' || c == 'P');
    let hex_part = parts.next().unwrap_or("");
    let exp_part = parts.next().unwrap_or("0");

    let mut int_val = 0.0;
    let mut fract_val = 0.0;
    let mut fract_div = 1.0;
    let mut in_fract = false;

    for c in hex_part.chars() {
        if c == '.' {
            in_fract = true;
        } else if let Some(digit) = c.to_digit(16) {
            if in_fract {
                fract_div *= 16.0;
                fract_val += digit as f64 / fract_div;
            } else {
                int_val = int_val * 16.0 + digit as f64;
            }
        }
    }

    let base = int_val + fract_val;
    let exp = exp_part.parse::<f64>().unwrap_or(0.0);
    base * 2.0_f64.powf(exp)
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut s = Self {
            chars: source.chars().peekable(),
            line: 1,
            col: 1,
            token_start_line: 1,
            token_start_col: 1,
        };
        if source.starts_with('#') {
            while let Some(c) = s.advance() {
                if c == '\n' {
                    break;
                }
            }
        }
        s
    }
    fn advance(&mut self) -> Option<char> {
        let c = self.chars.next();
        if c == Some('\n') {
            self.line += 1;
            self.col = 1;
        } else if c.is_some() {
            self.col += 1;
        }
        c
    }
    fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }
    fn match_char(&mut self, expected: char) -> bool {
        if let Some(&c) = self.peek() {
            if c == expected {
                self.advance();
                return true;
            }
        }
        false
    }
    pub fn peek_token(&self) -> Token {
        let mut clone = Scanner {
            chars: self.chars.clone(),
            token_start_line: self.line,
            token_start_col: self.col,
            line: self.line,
            col: self.col,
        };
        clone.next_token()
    }

    pub fn next_token(&mut self) -> Token {
        while let Some(&c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
                continue;
            }
            self.token_start_line = self.line;
            self.token_start_col = self.col;
            match c {
                '/' => {
                    self.advance();
                    if self.match_char('/') {
                        return Token::FloorDiv;
                    }
                    return Token::Slash;
                }
                '"' | '\'' => {
                    let quote = c;
                    self.advance();
                    let mut s = String::new();

                    while let Some(&nc) = self.peek() {
                        if nc == quote {
                            self.advance();
                            break;
                        }

                        if nc == '\\' {
                            self.advance();
                            if let Some(&esc) = self.peek() {
                                match esc {
                                    'a' => {
                                        s.push('\x07');
                                        self.advance();
                                    }
                                    'b' => {
                                        s.push('\x08');
                                        self.advance();
                                    }
                                    'f' => {
                                        s.push('\x0C');
                                        self.advance();
                                    }
                                    'n' => {
                                        s.push('\n');
                                        self.advance();
                                    }
                                    'r' => {
                                        s.push('\r');
                                        self.advance();
                                    }
                                    't' => {
                                        s.push('\t');
                                        self.advance();
                                    }
                                    'v' => {
                                        s.push('\x0B');
                                        self.advance();
                                    }
                                    '\\' => {
                                        s.push('\\');
                                        self.advance();
                                    }
                                    '"' => {
                                        s.push('"');
                                        self.advance();
                                    }
                                    '\'' => {
                                        s.push('\'');
                                        self.advance();
                                    }
                                    '0'..='9' => {
                                        let mut num_str = String::new();
                                        num_str.push(esc);
                                        self.advance();
                                        for _ in 0..2 {
                                            if let Some(&dc) = self.peek() {
                                                if dc.is_ascii_digit() {
                                                    num_str.push(dc);
                                                    self.advance();
                                                } else {
                                                    break;
                                                }
                                            } else {
                                                break;
                                            }
                                        }
                                        if let Ok(n) = num_str.parse::<u8>() {
                                            s.push(n as char);
                                        } else {
                                            panic!("Invalid decimal escape sequence");
                                        }
                                    }
                                    'x' => {
                                        self.advance();
                                        let mut hex_str = String::new();
                                        for _ in 0..2 {
                                            if let Some(&hc) = self.peek() {
                                                if hc.is_ascii_hexdigit() {
                                                    hex_str.push(hc);
                                                    self.advance();
                                                } else {
                                                    break;
                                                }
                                            } else {
                                                break;
                                            }
                                        }
                                        if hex_str.len() == 2 {
                                            if let Ok(n) = u8::from_str_radix(&hex_str, 16) {
                                                s.push(n as char);
                                            }
                                        } else {
                                            panic!("Invalid hex escape sequence");
                                        }
                                    }
                                    'z' => {
                                        self.advance();
                                        while let Some(&wc) = self.peek() {
                                            if wc.is_whitespace() {
                                                self.advance();
                                            } else {
                                                break;
                                            }
                                        }
                                    }
                                    '\n' | '\r' => {
                                        s.push('\n');
                                        self.advance();
                                        if let Some(&nc2) = self.peek() {

                                            if (esc == '\n' && nc2 == '\r')
                                                || (esc == '\r' && nc2 == '\n')
                                            {
                                                self.advance();
                                            }
                                        }
                                    }
                                    _ => {
                                        s.push(esc);
                                        self.advance();
                                    }
                                }
                            }
                        } else {
                            s.push(nc);
                            self.advance();
                        }
                    }
                    return Token::StringLiteral(s);
                }
                ':' => {
                    self.advance();
                    return Token::Colon;
                }
                '#' => {
                    self.advance();
                    return Token::Hash;
                }
                '^' => {
                    self.advance();
                    return Token::Caret;
                }
                '%' => {
                    self.advance();
                    return Token::Percent;
                }
                '+' => {
                    self.advance();
                    return Token::Plus;
                }
                '*' => {
                    self.advance();
                    return Token::Star;
                }
                '=' => {
                    self.advance();
                    return if self.match_char('=') {
                        Token::EqEq
                    } else {
                        Token::Eq
                    };
                }
                '<' => {
                    self.advance();
                    return if self.match_char('=') {
                        Token::LtEq
                    } else {
                        Token::Lt
                    };
                }
                '>' => {
                    self.advance();
                    return if self.match_char('=') {
                        Token::GtEq
                    } else {
                        Token::Gt
                    };
                }
                '(' => {
                    self.advance();
                    return Token::LParen;
                }
                ')' => {
                    self.advance();
                    return Token::RParen;
                }
                '{' => {
                    self.advance();
                    return Token::LBrace;
                }
                '}' => {
                    self.advance();
                    return Token::RBrace;
                }
                '-' => {
                    self.advance();
                    if self.match_char('-') {
                        if self.match_char('[') {
                            let mut sep_count = 0;
                            while self.match_char('=') {
                                sep_count += 1;
                            }
                            if self.match_char('[') {

                                loop {
                                    if let Some(&nc) = self.peek() {
                                        if nc == ']' {
                                            self.advance();
                                            let mut close_count = 0;
                                            while self.match_char('=') {
                                                close_count += 1;
                                            }

                                            if let Some(&nc2) = self.peek() {
                                                if nc2 == ']' && close_count == sep_count {
                                                    self.advance();
                                                    break;
                                                }
                                            }

                                        } else {
                                            self.advance();
                                        }
                                    } else {
                                        break;
                                    }
                                }
                                continue;
                            }
                        }

                        while let Some(&nc) = self.peek() {
                            if nc == '\n' {
                                break;
                            }
                            self.advance();
                        }
                        continue;
                    }
                    return Token::Minus;
                }
                '&' => {
                    self.advance();
                    return Token::BitAnd;
                }
                '|' => {
                    self.advance();
                    return Token::BitOr;
                }
                '~' => {
                    self.advance();
                    if self.match_char('=') {
                        return Token::Neq;
                    }
                    return Token::BitXor;
                }
                '[' => {
                    self.advance();
                    let mut sep_count = 0;
                    while self.match_char('=') {
                        sep_count += 1;
                    }

                    if self.match_char('[') {
                        let mut s = String::new();
                        loop {
                            if let Some(&nc) = self.peek() {
                                if nc == ']' {
                                    self.advance();
                                    let mut close_count = 0;
                                    while self.match_char('=') {
                                        close_count += 1;
                                    }

                                    if let Some(&nc2) = self.peek() {
                                        if nc2 == ']' && close_count == sep_count {
                                            self.advance();
                                            break;
                                        }
                                    }

                                    s.push(']');
                                    for _ in 0..close_count {
                                        s.push('=');
                                    }
                                }

                                else if nc == '\n' || nc == '\r' {
                                    let c1 = self.advance().unwrap();
                                    s.push('\n');
                                    if let Some(&c2) = self.peek() {
                                        if (c1 == '\n' && c2 == '\r') || (c1 == '\r' && c2 == '\n')
                                        {
                                            self.advance();
                                        }
                                    }
                                } else {
                                    s.push(self.advance().unwrap());
                                }
                            } else {
                                panic!("unfinished long string");
                            }
                        }

                        if s.starts_with('\n') {
                            s.remove(0);
                        }

                        return Token::StringLiteral(s);
                    }

                    if sep_count == 0 {
                        return Token::LBracket;
                    } else {
                        panic!("invalid long string delimiter");
                    }
                }
                '!' => {
                    self.advance();
                    if self.match_char('=') {
                        return Token::Neq;
                    }
                    return Token::Not;
                }
                ']' => {
                    self.advance();
                    return Token::RBracket;
                }
                ',' => {
                    self.advance();
                    return Token::Comma;
                }
                ';' => {
                    self.advance();
                    return Token::Semi;
                }
                '.' => {
                    self.advance();
                    if self.match_char('.') {
                        if self.match_char('.') {
                            return Token::DotDotDot;
                        }
                        return Token::DotDot;
                    }

                    if let Some(&nc) = self.peek() {
                        if nc.is_ascii_digit() {
                            let mut num_str = String::from(".");
                            while let Some(&nc2) = self.peek() {
                                if nc2.is_ascii_digit() || nc2 == 'e' || nc2 == 'E' {
                                    num_str.push(self.advance().unwrap());
                                } else if nc2 == '.' {
                                    let mut lookahead = self.chars.clone();
                                    lookahead.next();
                                    if let Some(&nnc) = lookahead.peek() {
                                        if nnc == '.' {
                                            break;
                                        }
                                    }
                                    num_str.push(self.advance().unwrap());
                                } else if (nc2 == '+' || nc2 == '-')
                                    && num_str.to_lowercase().ends_with('e')
                                {
                                    num_str.push(self.advance().unwrap());
                                } else {
                                    break;
                                }
                            }
                            let val = num_str
                                .parse()
                                .unwrap_or_else(|_| panic!("malformed number near '{}'", num_str));
                            return Token::Num(val);
                        }
                    }
                    return Token::Dot;
                }

                _ if c.is_ascii_digit() => {
                    let mut num_str = String::new();
                    num_str.push(self.advance().unwrap());

                    let mut is_hex = false;
                    if num_str == "0" {
                        if let Some(&nc) = self.peek() {
                            if nc == 'x' || nc == 'X' {
                                is_hex = true;
                                num_str.push(self.advance().unwrap());
                            }
                        }
                    }

                    while let Some(&nc) = self.peek() {
                        if is_hex {
                            if nc.is_ascii_hexdigit() || nc == 'p' || nc == 'P' {
                                num_str.push(self.advance().unwrap());
                            } else if nc == '.' {

                                let mut lookahead = self.chars.clone();
                                lookahead.next();
                                if let Some(&nnc) = lookahead.peek() {
                                    if nnc == '.' {
                                        break;
                                    }
                                }
                                num_str.push(self.advance().unwrap());
                            } else if (nc == '+' || nc == '-')
                                && num_str.to_lowercase().ends_with('p')
                            {
                                num_str.push(self.advance().unwrap());
                            } else {
                                break;
                            }
                        } else {
                            if nc.is_ascii_digit() || nc == 'e' || nc == 'E' {
                                num_str.push(self.advance().unwrap());
                            } else if nc == '.' {
                                let mut lookahead = self.chars.clone();
                                lookahead.next();
                                if let Some(&nnc) = lookahead.peek() {
                                    if nnc == '.' {
                                        break;
                                    }
                                }
                                num_str.push(self.advance().unwrap());
                            } else if (nc == '+' || nc == '-')
                                && num_str.to_lowercase().ends_with('e')
                            {
                                num_str.push(self.advance().unwrap());
                            } else {
                                break;
                            }
                        }
                    }

                    let val = if is_hex {
                        parse_hex_float(&num_str)
                    } else {

                        num_str
                            .parse()
                            .unwrap_or_else(|_| panic!("malformed number near '{}'", num_str))
                    };
                    return Token::Num(val);
                }
                _ if c.is_alphabetic() || c == '_' => {
                    let mut id = String::new();
                    while let Some(&nc) = self.peek() {
                        if nc.is_alphanumeric() || nc == '_' {
                            id.push(self.advance().unwrap());
                        } else {
                            break;
                        }
                    }
                    return match id.as_str() {
                        "and" => Token::And,
                        "or" => Token::Or,
                        "not" => Token::Not,
                        "local" => Token::Local,
                        "function" => Token::Function,
                        "end" => Token::End,
                        "do" => Token::Do,
                        "then" => Token::Then,
                        "if" => Token::If,
                        "elseif" => Token::Elseif,
                        "else" => Token::Else,
                        "while" => Token::While,
                        "repeat" => Token::Repeat,
                        "until" => Token::Until,
                        "for" => Token::For,
                        "in" => Token::In,
                        "return" => Token::Return,
                        "break" => Token::Break,
                        "perform" => Token::Perform,
                        "handle" => Token::Handle,
                        "continue" => Token::Continue,
                        "with" => Token::With,
                        "nil" => Token::Nil,
                        "true" => Token::True,
                        "false" => Token::False,
                        _ => Token::Ident(id),
                    };
                }
                _ => panic!("Unexpected character: {}", c),
            }
        }
        Token::EOF
    }
}

#[derive(PartialEq, PartialOrd, Clone, Copy)]
enum Precedence {
    None,
    Assignment,
    Or,
    And,
    Comparison,
    BitOr,
    BitXor,
    BitAnd,
    BitShift,
    Concat,
    Term,
    Factor,
    Unary,
    Power,
    Call,
    Primary,
}
enum Lhs {
    Local(u32),
    Upval(u32),
    TabLocal(u32, u32),
    TabUp(u32, u32),
    Table,
    Call(bool),
}

pub struct CompilerState {
    pub locals: Vec<String>,
    pub max_locals: usize,
    pub chunk_idx: usize,
    pub loop_exits: Vec<Vec<usize>>,
    pub loop_continues: Vec<Vec<usize>>,
    pub upvals: Vec<(bool, usize, String)>,
    pub is_vararg: bool,
}
pub struct Compiler<'a, 'b> {
    vm: &'a mut VM,
    scanner: &'b mut Scanner<'b>,
    current: Token,
    previous: Token,
    states: Vec<CompilerState>,
    current_line: usize,
    current_col: usize,
    previous_line: usize,
    previous_col: usize,
    source_id: usize,
}

impl<'a, 'b> Compiler<'a, 'b> {
    fn leave_scope(&mut self, local_start: usize) {
        let state = self.states.last_mut().unwrap();
        let current_len = state.locals.len();
        if current_len > local_start {
            let chunk_idx = state.chunk_idx;
            self.vm.chunks[chunk_idx]
                .instructions
                .push(OpCode::CloseLocals(local_start as u32));
            self.vm.chunks[chunk_idx].lines.push(self.previous_line);
            state.locals.truncate(local_start);
        }
    }
    pub fn compile(vm: &mut VM, source: &str, source_name: &str) -> Result<usize, String> {
        let lines: Vec<String> = source.lines().map(|s| s.to_string()).collect();
        vm.sources.push(lines);
        vm.source_names.push(source_name.to_string());
        let source_id = vm.sources.len() - 1;

        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut scanner = Scanner::new(source);
            let mut compiler = Compiler {
                vm,
                scanner: &mut scanner,
                current: Token::EOF,
                previous: Token::EOF,
                current_line: 1,
                current_col: 1,
                previous_line: 1,
                previous_col: 1,
                states: Vec::new(),
                source_id,
            };
            compiler.advance();
            let chunk_idx = compiler.create_chunk();
            compiler.states.push(CompilerState {
                locals: Vec::new(),
                max_locals: 0,
                chunk_idx,
                loop_exits: Vec::new(),
                loop_continues: Vec::new(),
                upvals: vec![(false, 0, "_ENV".to_string())],
                is_vararg: true,
            });
            compiler.statement_list();
            compiler.emit(OpCode::Return(0, false));
            let final_state = compiler.states.pop().unwrap();
            compiler.vm.chunks[final_state.chunk_idx].local_count = final_state.max_locals;
            compiler.vm.chunks[final_state.chunk_idx].upvals = final_state.upvals;
            final_state.chunk_idx
        }));

        std::panic::set_hook(prev_hook);

        match result {
            Ok(chunk_idx) => Ok(chunk_idx),
            Err(payload) => {
                let msg = if let Some(s) = payload.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = payload.downcast_ref::<&str>() {
                    s.to_string()
                } else {
                    "Unknown syntax error".to_string()
                };
                Err(msg)
            }
        }
    }

    fn error(&self, msg: &str) -> ! {
        let line = self.current_line;
        let col = self.current_col;
        let line_text = self.vm.sources[self.source_id]
            .get(line.saturating_sub(1))
            .map(|s| s.as_str())
            .unwrap_or("");

        let err_msg = format!(
            "\n[Compile Error] {}\n  --> line {}:{}\n   |\n{:>3}| {}\n   | {:>width$}^",
            msg,
            line,
            col,
            line,
            line_text,
            "",
            width = col.saturating_sub(1)
        );
        panic!("{}", err_msg);
    }

    fn advance(&mut self) {
        self.previous = self.current.clone();
        self.previous_line = self.current_line;
        self.previous_col = self.current_col;

        self.current = self.scanner.next_token();
        self.current_line = self.scanner.token_start_line;
        self.current_col = self.scanner.token_start_col;
    }
    fn check(&self, token: Token) -> bool {
        self.current == token
    }
    fn match_token(&mut self, token: Token) -> bool {
        if self.check(token) {
            self.advance();
            true
        } else {
            false
        }
    }
    fn consume(&mut self, token: Token, err: &str) {
        if self.check(token) {
            self.advance();
        } else {
            self.error(err);
        }
    }
    fn emit(&mut self, op: OpCode) {
        let idx = self.states.last().unwrap().chunk_idx;
        self.vm.chunks[idx].instructions.push(op);
        self.vm.chunks[idx].lines.push(self.previous_line);
    }
    fn emit_jump(&mut self, op: OpCode) -> usize {
        self.emit(op);
        let idx = self.states.last().unwrap().chunk_idx;
        self.vm.chunks[idx].instructions.len() - 1
    }
    fn patch_jump(&mut self, offset: usize) {
        let idx = self.states.last().unwrap().chunk_idx;
        let target = self.vm.chunks[idx].instructions.len();
        match &mut self.vm.chunks[idx].instructions[offset] {
            OpCode::JumpIfFalse(ref mut ip)
            | OpCode::Jump(ref mut ip)
            | OpCode::JumpIfFalseKeep(ref mut ip)
            | OpCode::JumpIfTrueKeep(ref mut ip) => *ip = target,
            _ => unreachable!(),
        }
    }

    fn create_chunk(&mut self) -> usize {
        let idx = self.vm.chunks.len();
        self.vm.chunks.push(Chunk {
            instructions: vec![],
            lines: vec![],
            constants: vec![],
            local_count: 0,
            param_count: 0,
            is_vararg: false,
            upvals: vec![],
            source_id: self.source_id,
            linedefined: self.previous_line,
        });
        idx
    }
    fn add_constant(&mut self, val: Value) -> u32 {
        let idx = self.states.last().unwrap().chunk_idx;
        self.vm.chunks[idx].constants.push(val);
        (self.vm.chunks[idx].constants.len() - 1) as u32
    }

    fn resolve_local_in(&self, state_idx: usize, name: &str) -> Option<usize> {
        self.states[state_idx]
            .locals
            .iter()
            .rposition(|l| l == name)
    }
    fn add_upvalue(&mut self, state_idx: usize, is_local: bool, index: usize, name: &str) -> usize {
        for (i, upv) in self.states[state_idx].upvals.iter().enumerate() {
            if upv.0 == is_local && upv.1 == index && upv.2 == name {
                return i;
            }
        }
        self.states[state_idx]
            .upvals
            .push((is_local, index, name.to_string()));
        self.states[state_idx].upvals.len() - 1
    }

    fn resolve_upvalue(&mut self, state_idx: usize, name: &str) -> Option<usize> {
        if let Some((i, _)) = self.states[state_idx]
            .upvals
            .iter()
            .enumerate()
            .find(|(_, u)| u.2 == name)
        {
            return Some(i);
        }
        if state_idx == 0 {
            return None;
        }
        let parent_idx = state_idx - 1;
        if let Some(loc_idx) = self.resolve_local_in(parent_idx, name) {
            return Some(self.add_upvalue(state_idx, true, loc_idx, name));
        }
        if let Some(upv_idx) = self.resolve_upvalue(parent_idx, name) {
            return Some(self.add_upvalue(state_idx, false, upv_idx, name));
        }
        None
    }

    fn parse_rhs_and_adjust(&mut self, lhs_count: usize) {
        let mut rhs_count = 0;
        let mut last_is_multiret = false;
        loop {
            last_is_multiret = self.expression();
            rhs_count += 1;
            if self.match_token(Token::Comma) {
                if last_is_multiret {
                    self.emit(OpCode::AdjustStack(1));
                }
            } else {
                break;
            }
        }
        if rhs_count < lhs_count {
            let needed = lhs_count - rhs_count + 1;
            if last_is_multiret {
                self.emit(OpCode::AdjustStack(needed as u32));
            } else {
                for _ in 0..(needed - 1) {
                    self.emit(OpCode::PushNil);
                }
            }
        } else if rhs_count == lhs_count {
            if last_is_multiret {
                self.emit(OpCode::AdjustStack(1));
            }
        } else {
            let over = rhs_count - lhs_count;
            if last_is_multiret {
                self.emit(OpCode::AdjustStack(0));
                for _ in 0..(over - 1) {
                    self.emit(OpCode::Pop);
                }
            } else {
                for _ in 0..over {
                    self.emit(OpCode::Pop);
                }
            }
        }
    }

    fn statement_list(&mut self) {
        while !self.check(Token::End)
            && !self.check(Token::With)
            && !self.check(Token::Else)
            && !self.check(Token::Elseif)
            && !self.check(Token::Until)
            && !self.check(Token::EOF)
        {
            self.declaration();
        }
    }

    fn declaration(&mut self) {
        if self.match_token(Token::Function) {
            self.fun_declaration();
        } else if self.match_token(Token::Local) {
            if self.match_token(Token::Function) {
                self.local_fun_declaration();
            } else {
                let mut names = Vec::new();
                loop {
                    self.advance();
                    let name = if let Token::Ident(n) = &self.previous {
                        n.clone()
                    } else {
                        self.error("Expected name");
                    };
                    names.push(name);
                    if self.match_token(Token::Comma) {
                        continue;
                    } else {
                        break;
                    }
                }

                // 1. Evaluate RHS first before registering locals
                if self.match_token(Token::Eq) {
                    self.parse_rhs_and_adjust(names.len());
                } else {
                    for _ in 0..names.len() {
                        self.emit(OpCode::PushNil);
                    }
                }

                // 2. Register them strictly in sequential order
                for name in &names {
                    let state = self.states.last_mut().unwrap();
                    state.locals.push(name.clone());
                    if state.locals.len() > state.max_locals {
                        state.max_locals = state.locals.len();
                    }
                }

                // 3. Store results reading down from the top of the stack
                for (i, _) in names.iter().enumerate().rev() {
                    let state = self.states.last().unwrap();
                    let idx = state.locals.len() - names.len() + i;
                    self.emit(OpCode::StoreLocal(idx as u32));
                    self.emit(OpCode::Pop);
                }
            }
        } else {
            self.statement();
        }
        if self.match_token(Token::Semi) {}
    }

    fn emit_lhs_get(&mut self, lhs: &Lhs) {
        match lhs {
            Lhs::Local(idx) => self.emit(OpCode::LoadLocal(*idx)),
            Lhs::Upval(idx) => self.emit(OpCode::LoadUpval(*idx)),
            Lhs::TabLocal(loc_idx, c_idx) => {
                self.emit(OpCode::LoadLocal(*loc_idx));
                self.emit(OpCode::LoadConst(*c_idx));
                self.emit(OpCode::GetTable);
            }
            Lhs::TabUp(up_idx, c_idx) => {
                self.emit(OpCode::GetTabUp(*up_idx, *c_idx));
            }
            Lhs::Table => self.emit(OpCode::GetTable),
            Lhs::Call(is_multi) => {
                if *is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
            }
        }
    }

    fn parse_prefix_expr(&mut self) -> Lhs {
        let mut lhs;
        if self.match_token(Token::LParen) {
            let is_multi = self.expression();
            self.consume(Token::RParen, "Expected ')'");
            if is_multi {
                self.emit(OpCode::AdjustStack(1));
            }
            lhs = Lhs::Call(false);
        } else if let Token::Ident(name) = self.current.clone() {
            self.advance();
            let curr = self.states.len() - 1;
            if let Some(idx) = self.resolve_local_in(curr, &name) {
                lhs = Lhs::Local(idx as u32);
            } else if let Some(idx) = self.resolve_upvalue(curr, &name) {
                lhs = Lhs::Upval(idx as u32);
            } else {
                let str_val = self.vm.alloc_str(&name);
                let const_id = self.add_constant(str_val);
                if let Some(env_local_idx) = self.resolve_local_in(curr, "_ENV") {
                    lhs = Lhs::TabLocal(env_local_idx as u32, const_id);
                } else {
                    let env_idx = self
                        .resolve_upvalue(curr, "_ENV")
                        .unwrap_or_else(|| self.error("Missing _ENV upvalue"));
                    lhs = Lhs::TabUp(env_idx as u32, const_id);
                }
            }
        } else {
            self.error("Expected variable or '('");
            unreachable!()
        }

        loop {
            if self.match_token(Token::LBracket) {
                self.emit_lhs_get(&lhs);
                let is_multi = self.expression();
                if is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.consume(Token::RBracket, "Expected ']'");
                lhs = Lhs::Table;
            } else if self.match_token(Token::Dot) {
                self.emit_lhs_get(&lhs);
                let name = if let Token::Ident(n) = self.current.clone() {
                    n
                } else {
                    self.error("Expected field name");
                    unreachable!()
                };
                self.advance();
                let str_val = self.vm.alloc_str(&name);
                let const_id = self.add_constant(str_val);
                self.emit(OpCode::LoadConst(const_id));
                lhs = Lhs::Table;
            } else if self.match_token(Token::Colon) {
                self.emit_lhs_get(&lhs);
                let name = if let Token::Ident(n) = self.current.clone() {
                    n
                } else {
                    self.error("Expected method name");
                    unreachable!()
                };
                self.advance();

                self.emit(OpCode::Dup);
                let str_val = self.vm.alloc_str(&name);
                let const_id = self.add_constant(str_val);
                self.emit(OpCode::LoadConst(const_id));
                self.emit(OpCode::GetTable);
                self.emit(OpCode::Swap);

                let mut arg_count = 1;
                let mut last_multi = false;
                if self.match_token(Token::LParen) {
                    if !self.check(Token::RParen) {
                        loop {
                            last_multi = self.expression();
                            arg_count += 1;
                            if !self.match_token(Token::Comma) {
                                break;
                            }
                        }
                    }
                    self.consume(Token::RParen, "Expected ')' for method call");
                } else if let Token::StringLiteral(s) = self.current.clone() {
                    self.advance();
                    let str_val = self.vm.alloc_str(&s);
                    let const_id = self.add_constant(str_val);
                    self.emit(OpCode::LoadConst(const_id));
                    arg_count += 1;
                } else if self.check(Token::LBrace) {
                    self.expression();
                    arg_count += 1;
                } else {
                    self.error("Expected '(', '{', or string literal for method call");
                }
                self.emit(OpCode::Call(arg_count as u32, last_multi));
                lhs = Lhs::Call(true);
            } else if self.check(Token::LParen)
                || self.check(Token::LBrace)
                || matches!(self.current, Token::StringLiteral(_))
            {
                self.emit_lhs_get(&lhs);
                let mut arg_count = 0;
                let mut last_multi = false;
                if self.match_token(Token::LParen) {
                    if !self.check(Token::RParen) {
                        loop {
                            last_multi = self.expression();
                            arg_count += 1;
                            if !self.match_token(Token::Comma) {
                                break;
                            }
                        }
                    }
                    self.consume(Token::RParen, "Expected ')' for call");
                } else if self.check(Token::LBrace) {
                    self.expression();
                    arg_count = 1;
                } else if let Token::StringLiteral(s) = self.current.clone() {
                    self.advance();
                    let str_val = self.vm.alloc_str(&s);
                    let const_id = self.add_constant(str_val);
                    self.emit(OpCode::LoadConst(const_id));
                    arg_count = 1;
                }
                self.emit(OpCode::Call(arg_count as u32, last_multi));
                lhs = Lhs::Call(true);
            } else {
                break;
            }
        }
        lhs
    }

    fn statement(&mut self) {
        if self.match_token(Token::Handle) {
            self.handle_statement();
        } else if self.match_token(Token::If) {
            self.if_statement();
        } else if self.match_token(Token::While) {
            self.while_statement();
        } else if self.match_token(Token::Repeat) {
            self.repeat_statement();
        } else if self.match_token(Token::For) {
            self.for_statement();
        } else if self.match_token(Token::Do) {
            self.do_statement();
        } else if self.match_token(Token::Return) {
            if self.check(Token::End)
                || self.check(Token::Else)
                || self.check(Token::Elseif)
                || self.check(Token::Until)
                || self.check(Token::Semi)
            {
                self.emit(OpCode::Return(0, false));
            } else {
                let mut rhs_count = 0;
                let mut last_multiret = false;
                loop {
                    last_multiret = self.expression();
                    rhs_count += 1;
                    if self.match_token(Token::Comma) {
                        if last_multiret {
                            self.emit(OpCode::AdjustStack(1));
                        }
                    } else {
                        break;
                    }
                }

                let idx = self.states.last().unwrap().chunk_idx;
                let insts = &mut self.vm.chunks[idx].instructions;

                if rhs_count == 1 && last_multiret {
                    if let Some(OpCode::Call(args, multi)) = insts.last().copied() {
                        insts.pop();
                        self.emit(OpCode::TailCall(args, multi));
                        return;
                    }
                }

                self.emit(OpCode::Return(rhs_count as u32, last_multiret));
            }
        } else if self.match_token(Token::Break) {
            self.break_statement();
        } else if self.match_token(Token::Continue) {
            let is_empty = self
                .states
                .last()
                .map_or(true, |s| s.loop_continues.is_empty());
            if is_empty {
                self.error("No loop to continue");
            }

            let jump = self.emit_jump(OpCode::Jump(0));
            self.states
                .last_mut()
                .unwrap()
                .loop_continues
                .last_mut()
                .unwrap()
                .push(jump);
        } else if self.check(Token::Perform) {
            let is_multi = self.expression();
            if is_multi {
                self.emit(OpCode::AdjustStack(0));
            } else {
                self.emit(OpCode::Pop);
            }
        } else {
            let mut targets = Vec::new();
            loop {
                targets.push(self.parse_prefix_expr());
                if self.match_token(Token::Comma) {
                    continue;
                } else {
                    break;
                }
            }

            if self.match_token(Token::Eq) {
                self.parse_rhs_and_adjust(targets.len());

                for _ in 0..targets.len() {
                    self.emit(OpCode::PushStash);
                }

                self.emit(OpCode::ReverseStash(targets.len() as u32));

                for target in targets.into_iter().rev() {
                    match target {
                        Lhs::Local(idx) => {
                            self.emit(OpCode::PopStash);
                            self.emit(OpCode::StoreLocal(idx));
                            self.emit(OpCode::Pop);
                        }
                        Lhs::Upval(idx) => {
                            self.emit(OpCode::PopStash);
                            self.emit(OpCode::StoreUpval(idx));
                            self.emit(OpCode::Pop);
                        }
                        Lhs::TabUp(up_idx, c_idx) => {
                            self.emit(OpCode::PopStash);
                            self.emit(OpCode::SetTabUp(up_idx, c_idx));
                            self.emit(OpCode::Pop);
                        }
                        Lhs::TabLocal(loc_idx, c_idx) => {
                            self.emit(OpCode::PopStash);
                            self.emit(OpCode::SetTabLocal(loc_idx, c_idx));
                            self.emit(OpCode::Pop);
                        }
                        Lhs::Table => {

                            self.emit(OpCode::PopStash);
                            self.emit(OpCode::SetTable);
                            self.emit(OpCode::Pop);
                        }
                        Lhs::Call(_) => {
                            self.error("Syntax error: cannot assign to a function call")
                        }
                    }
                }
            } else {
                if targets.len() > 1 {
                    self.error("Syntax error: unexpected ','");
                }
                match targets[0] {
                    Lhs::Call(is_multi) => {
                        if is_multi {
                            self.emit(OpCode::AdjustStack(0));
                        } else {
                            self.emit(OpCode::Pop);
                        }
                    }
                    _ => self.error("Syntax error: expected assignment or function call"),
                }
            }
        }
    }

    fn fun_declaration(&mut self) {
        self.advance();
        let root_name = if let Token::Ident(name) = &self.previous {
            name.clone()
        } else {
            self.error("Expected function name");
            unreachable!()
        };

        let mut fields = Vec::new();
        let mut is_method = false;

        while self.match_token(Token::Dot) {
            self.advance();
            if let Token::Ident(field) = &self.previous {
                fields.push(field.clone());
            } else {
                self.error("Expected field name after '.'");
            }
        }

        if self.match_token(Token::Colon) {
            self.advance();
            if let Token::Ident(field) = &self.previous {
                fields.push(field.clone());
            } else {
                self.error("Expected method name after ':'");
            }
            is_method = true;
        }

        self.consume(Token::LParen, "Expected '(' for function declaration");
        let mut params = Vec::new();
        let mut is_vararg = false;

        if is_method {
            params.push("self".to_string());
        }

        if !self.check(Token::RParen) {
            loop {
                if self.match_token(Token::DotDotDot) {
                    is_vararg = true;
                    break;
                }
                self.advance();
                if let Token::Ident(param) = &self.previous {
                    params.push(param.clone());
                }
                if !self.match_token(Token::Comma) {
                    break;
                }
            }
        }
        self.consume(Token::RParen, "Expected ')'");

        let chunk_idx = self.create_chunk();
        self.states.push(CompilerState {
            locals: params.clone(),
            max_locals: 0,
            chunk_idx,
            loop_exits: Vec::new(),
            upvals: Vec::new(),
            loop_continues: Vec::new(),
            is_vararg,
        });
        let curr = self.states.len() - 1;
        self.resolve_upvalue(curr, "_ENV");

        self.vm.chunks[chunk_idx].param_count = params.len();
        self.vm.chunks[chunk_idx].is_vararg = is_vararg;

        let mut state = self.states.last_mut().unwrap();
        state.max_locals = state.locals.len();
        self.statement_list();

        self.consume(Token::End, "Expected 'end' for function");
        self.emit(OpCode::Return(0, false));
        let finished_state = self.states.pop().unwrap();
        self.vm.chunks[finished_state.chunk_idx].local_count = finished_state.max_locals;
        self.vm.chunks[finished_state.chunk_idx].upvals = finished_state.upvals;

        if fields.is_empty() {
            let curr = self.states.len() - 1;
            self.emit(OpCode::MakeClosure(chunk_idx as u32));

            if let Some(idx) = self.resolve_local_in(curr, &root_name) {

                self.emit(OpCode::StoreLocal(idx as u32));
                self.emit(OpCode::Pop);
            } else if let Some(idx) = self.resolve_upvalue(curr, &root_name) {

                self.emit(OpCode::StoreUpval(idx as u32));
                self.emit(OpCode::Pop);
            } else {

                let str_val = self.vm.alloc_str(&root_name);
                let const_id = self.add_constant(str_val);

                if let Some(env_local_idx) = self.resolve_local_in(curr, "_ENV") {
                    self.emit(OpCode::SetTabLocal(env_local_idx as u32, const_id));
                } else {
                    let env_idx = self
                        .resolve_upvalue(curr, "_ENV")
                        .unwrap_or_else(|| self.error("Missing _ENV upvalue"));
                    self.emit(OpCode::SetTabUp(env_idx as u32, const_id));
                }
                self.emit(OpCode::Pop);
            }
        } else {

            let curr = self.states.len() - 1;
            if let Some(idx) = self.resolve_local_in(curr, &root_name) {
                self.emit(OpCode::LoadLocal(idx as u32));
            } else if let Some(idx) = self.resolve_upvalue(curr, &root_name) {
                self.emit(OpCode::LoadUpval(idx as u32));
            } else {
                let str_val = self.vm.alloc_str(&root_name);
                let const_id = self.add_constant(str_val);

                if let Some(env_local_idx) = self.resolve_local_in(curr, "_ENV") {
                    self.emit(OpCode::LoadLocal(env_local_idx as u32));
                    self.emit(OpCode::LoadConst(const_id));
                    self.emit(OpCode::GetTable);
                } else {
                    let env_idx = self
                        .resolve_upvalue(curr, "_ENV")
                        .unwrap_or_else(|| self.error("Missing _ENV upvalue"));
                    self.emit(OpCode::GetTabUp(env_idx as u32, const_id));
                }
            }

            for i in 0..fields.len() - 1 {
                let str_val = self.vm.alloc_str(&fields[i]);
                let const_id = self.add_constant(str_val);
                self.emit(OpCode::LoadConst(const_id));
                self.emit(OpCode::GetTable);
            }

            let last_field = fields.last().unwrap();
            let str_val = self.vm.alloc_str(last_field);
            let const_id = self.add_constant(str_val);
            self.emit(OpCode::LoadConst(const_id));

            self.emit(OpCode::MakeClosure(chunk_idx as u32));

            self.emit(OpCode::SetTable);
            self.emit(OpCode::Pop);
        }
    }

    fn local_fun_declaration(&mut self) {
        self.advance();
        let fn_name = if let Token::Ident(name) = &self.previous {
            name.clone()
        } else {
            self.error("Expected fn name");
            unreachable!()
        };

        let state = self.states.last_mut().unwrap();
        state.locals.push(fn_name.clone());
        if state.locals.len() > state.max_locals {
            state.max_locals = state.locals.len();
        }
        let store_idx = state.locals.len() - 1;

        self.consume(Token::LParen, "Expected '('");
        let mut params = Vec::new();
        let mut is_vararg = false;

        if !self.check(Token::RParen) {
            loop {
                if self.match_token(Token::DotDotDot) {

                    is_vararg = true;
                    break;
                }
                self.advance();
                if let Token::Ident(param) = &self.previous {
                    params.push(param.clone());
                }
                if !self.match_token(Token::Comma) {
                    break;
                }
            }
        }
        self.consume(Token::RParen, "Expected ')'");

        let chunk_idx = self.create_chunk();
        self.states.push(CompilerState {
            locals: params.clone(),
            max_locals: 0,
            chunk_idx,
            loop_exits: Vec::new(),
            upvals: Vec::new(),
            loop_continues: Vec::new(),
            is_vararg,
        });
        let curr = self.states.len() - 1;
        self.resolve_upvalue(curr, "_ENV");

        self.vm.chunks[chunk_idx].param_count = params.len();
        self.vm.chunks[chunk_idx].is_vararg = is_vararg;

        let mut inner_state = self.states.last_mut().unwrap();
        inner_state.max_locals = inner_state.locals.len();
        self.statement_list();
        self.consume(Token::End, "Expected 'end' for local function");
        self.emit(OpCode::Return(0, false));
        let finished_state = self.states.pop().unwrap();
        self.vm.chunks[finished_state.chunk_idx].local_count = finished_state.max_locals;
        self.vm.chunks[finished_state.chunk_idx].upvals = finished_state.upvals;
        self.emit(OpCode::MakeClosure(chunk_idx as u32));
        self.emit(OpCode::StoreLocal(store_idx as u32));
        self.emit(OpCode::Pop);
    }

    fn if_statement(&mut self) {
        let is_multi = self.expression();
        if is_multi {
            self.emit(OpCode::AdjustStack(1));
        }

        self.consume(Token::Then, "Expected 'then'");
        let mut jumps = Vec::new();
        let jump_if_false = self.emit_jump(OpCode::JumpIfFalse(0));

        let local_start = self.states.last().unwrap().locals.len();
        self.statement_list();
        self.leave_scope(local_start);

        jumps.push(self.emit_jump(OpCode::Jump(0)));
        self.patch_jump(jump_if_false);

        while self.match_token(Token::Elseif) {
            let is_multi = self.expression();
            if is_multi {
                self.emit(OpCode::AdjustStack(1));
            }

            self.consume(Token::Then, "Expected 'then'");
            let elseif_jump = self.emit_jump(OpCode::JumpIfFalse(0));

            let local_start = self.states.last().unwrap().locals.len();
            self.statement_list();
            self.leave_scope(local_start);

            jumps.push(self.emit_jump(OpCode::Jump(0)));
            self.patch_jump(elseif_jump);
        }

        if self.match_token(Token::Else) {

            let local_start = self.states.last().unwrap().locals.len();
            self.statement_list();
            self.leave_scope(local_start);
        }

        self.consume(Token::End, "Expected 'end' for if");
        for j in jumps {
            self.patch_jump(j);
        }
    }

    fn while_statement(&mut self) {
        let loop_start = self.vm.chunks[self.states.last().unwrap().chunk_idx]
            .instructions
            .len();
        let is_multi = self.expression();
        if is_multi {
            self.emit(OpCode::AdjustStack(1));
        }
        self.consume(Token::Do, "Expected 'do'");
        let exit_jump = self.emit_jump(OpCode::JumpIfFalse(0));
        self.states.last_mut().unwrap().loop_exits.push(Vec::new());
        self.states
            .last_mut()
            .unwrap()
            .loop_continues
            .push(Vec::new());
        let local_start = self.states.last().unwrap().locals.len();

        self.statement_list();
        self.consume(Token::End, "Expected 'end' for while");

        let mut state = self.states.last_mut().unwrap();
        let exits = state.loop_exits.pop().unwrap();
        let continues = state.loop_continues.pop().unwrap();

        for cont in continues {
            self.patch_jump(cont);
        }
        self.leave_scope(local_start);

        self.emit(OpCode::Jump(loop_start));
        self.patch_jump(exit_jump);
        for exit in exits {
            self.patch_jump(exit);
        }
    }

    fn repeat_statement(&mut self) {
        let loop_start = self.vm.chunks[self.states.last().unwrap().chunk_idx]
            .instructions
            .len();
        self.states.last_mut().unwrap().loop_exits.push(Vec::new());
        self.states
            .last_mut()
            .unwrap()
            .loop_continues
            .push(Vec::new());
        let local_start = self.states.last().unwrap().locals.len();

        self.statement_list();

        let mut state = self.states.last_mut().unwrap();
        let continues = state.loop_continues.pop().unwrap();
        for cont in continues {
            self.patch_jump(cont);
        }

        self.consume(Token::Until, "Expected 'until'");
        let is_multi = self.expression();
        if is_multi {
            self.emit(OpCode::AdjustStack(1));
        }

        let cond_false = self.emit_jump(OpCode::JumpIfFalse(0));
        let exit_jump = self.emit_jump(OpCode::Jump(0));

        self.patch_jump(cond_false);
        self.emit(OpCode::CloseLocals(local_start as u32));
        self.emit(OpCode::Jump(loop_start));

        self.patch_jump(exit_jump);
        let mut state = self.states.last_mut().unwrap();
        let exits = state.loop_exits.pop().unwrap();
        for exit in exits {
            self.patch_jump(exit);
        }

        self.leave_scope(local_start);
    }

    fn for_statement(&mut self) {
        let local_start = self.states.last().unwrap().locals.len();
        self.advance();

        let mut var_names = Vec::new();
        if let Token::Ident(name) = &self.previous {
            var_names.push(name.clone());
        } else {
            self.error("Expected loop var");
        }
        while self.match_token(Token::Comma) {
            self.advance();
            if let Token::Ident(name) = &self.previous {
                var_names.push(name.clone());
            } else {
                self.error("Expected loop var");
            }
        }

        if self.match_token(Token::Eq) {
            if var_names.len() > 1 {
                self.error("Numeric for only takes one variable");
            }
            let loop_var = var_names[0].clone();

            let is_multi_start = self.expression();
            if is_multi_start {
                self.emit(OpCode::AdjustStack(1));
            }
            self.emit(OpCode::ForceNum);
            let mut state = self.states.last_mut().unwrap();
            state.locals.push(loop_var.clone());
            if state.locals.len() > state.max_locals {
                state.max_locals = state.locals.len();
            }
            let loop_idx = state.locals.len() - 1;
            self.emit(OpCode::StoreLocal(loop_idx as u32));
            self.emit(OpCode::Pop);

            self.consume(Token::Comma, "Expected ','");

            let is_multi_end = self.expression();
            if is_multi_end {
                self.emit(OpCode::AdjustStack(1));
            }
            self.emit(OpCode::ForceNum);
            let mut state = self.states.last_mut().unwrap();
            state.locals.push(format!("$end_{}", loop_var));
            if state.locals.len() > state.max_locals {
                state.max_locals = state.locals.len();
            }
            let end_idx = state.locals.len() - 1;
            self.emit(OpCode::StoreLocal(end_idx as u32));
            self.emit(OpCode::Pop);

            let step_idx = self.states.last().unwrap().locals.len();
            if self.match_token(Token::Comma) {
                let is_multi_step = self.expression();
                if is_multi_step {
                    self.emit(OpCode::AdjustStack(1));
                }
            } else {
                let const_idx = self.add_constant(Value::num(1.0));
                self.emit(OpCode::LoadConst(const_idx));
            }
            self.emit(OpCode::ForceNum);
            let mut state = self.states.last_mut().unwrap();
            state.locals.push(format!("$step_{}", loop_var));
            if state.locals.len() > state.max_locals {
                state.max_locals = state.locals.len();
            }
            self.emit(OpCode::StoreLocal(step_idx as u32));
            self.emit(OpCode::Pop);

            self.consume(Token::Do, "Expected 'do'");
            let loop_start = self.vm.chunks[self.states.last().unwrap().chunk_idx]
                .instructions
                .len();

            self.emit(OpCode::LoadLocal(loop_idx as u32));
            self.emit(OpCode::LoadLocal(end_idx as u32));
            self.emit(OpCode::LoadLocal(step_idx as u32));

            self.emit(OpCode::ForCond);

            let exit_jump = self.emit_jump(OpCode::JumpIfFalse(0));
            self.states.last_mut().unwrap().loop_exits.push(Vec::new());
            self.states
                .last_mut()
                .unwrap()
                .loop_continues
                .push(Vec::new());

            let body_start = self.states.last().unwrap().locals.len();
            self.statement_list();
            self.consume(Token::End, "Expected 'end' for loop");

            let mut state = self.states.last_mut().unwrap();
            let exits = state.loop_exits.pop().unwrap();
            let continues = state.loop_continues.pop().unwrap();

            // 1. Patch continues first, so 'continue' jumps directly to the cleanup phase!
            for cont in continues {
                self.patch_jump(cont);
            }

            // 2. Clear inner body locals (fixes the 'local y' bug)
            self.leave_scope(body_start);

            // 3. FIX: Detach the loop variables (i) so the next iteration gets fresh upvals!
            let loop_vars_count = (body_start - local_start) as u32;
            self.emit(OpCode::DetachUpvals(local_start as u32, loop_vars_count));

            // 4. Loop update & jump
            self.emit(OpCode::LoadLocal(loop_idx as u32));
            self.emit(OpCode::LoadLocal(step_idx as u32));
            self.emit(OpCode::Add);
            self.emit(OpCode::StoreLocal(loop_idx as u32));
            self.emit(OpCode::Pop);
            self.emit(OpCode::Jump(loop_start));
            self.patch_jump(exit_jump);
            for exit in exits {
                self.patch_jump(exit);
            }
            self.leave_scope(local_start);
        } else if self.match_token(Token::In) {
            self.parse_rhs_and_adjust(3);

            let mut state = self.states.last_mut().unwrap();
            state.locals.push("$f".to_string());
            let f_idx = state.locals.len() - 1;
            state.locals.push("$s".to_string());
            let s_idx = state.locals.len() - 1;
            state.locals.push("$c".to_string());
            let c_idx = state.locals.len() - 1;
            if state.locals.len() > state.max_locals {
                state.max_locals = state.locals.len();
            }

            self.emit(OpCode::StoreLocal(c_idx as u32));
            self.emit(OpCode::Pop);
            self.emit(OpCode::StoreLocal(s_idx as u32));
            self.emit(OpCode::Pop);
            self.emit(OpCode::StoreLocal(f_idx as u32));
            self.emit(OpCode::Pop);

            let mut var_indices = Vec::new();
            for name in &var_names {
                let idx = {
                    let mut state = self.states.last_mut().unwrap();
                    state.locals.push(name.clone());
                    if state.locals.len() > state.max_locals {
                        state.max_locals = state.locals.len();
                    }
                    state.locals.len() - 1
                };

                var_indices.push(idx);

                self.emit(OpCode::PushNil);
                self.emit(OpCode::StoreLocal(idx as u32));
                self.emit(OpCode::Pop);
            }

            self.consume(Token::Do, "Expected 'do'");
            let loop_start = self.vm.chunks[self.states.last().unwrap().chunk_idx]
                .instructions
                .len();

            self.emit(OpCode::LoadLocal(f_idx as u32));
            self.emit(OpCode::LoadLocal(s_idx as u32));
            self.emit(OpCode::LoadLocal(c_idx as u32));
            self.emit(OpCode::Call(2, false));

            self.emit(OpCode::AdjustStack(var_names.len() as u32));

            for &idx in var_indices.iter().rev() {
                self.emit(OpCode::StoreLocal(idx as u32));
                self.emit(OpCode::Pop);
            }

            self.emit(OpCode::LoadLocal(var_indices[0] as u32));
            self.emit(OpCode::StoreLocal(c_idx as u32));
            self.emit(OpCode::Pop);

            self.emit(OpCode::LoadLocal(c_idx as u32));
            self.emit(OpCode::PushNil);
            self.emit(OpCode::Eq);

            let exit_jump = self.emit_jump(OpCode::JumpIfTrueKeep(0));
            self.emit(OpCode::Pop);

            self.states.last_mut().unwrap().loop_exits.push(Vec::new());
            self.states
                .last_mut()
                .unwrap()
                .loop_continues
                .push(Vec::new());

            let body_start = self.states.last().unwrap().locals.len();
            self.statement_list();
            self.consume(Token::End, "Expected 'end' for loop");

            let mut state = self.states.last_mut().unwrap();
            let exits = state.loop_exits.pop().unwrap();
            let continues = state.loop_continues.pop().unwrap();

            // 1. Patch continues
            for cont in continues {
                self.patch_jump(cont);
            }

            // 2. Clear inner body locals
            self.leave_scope(body_start);

            // 3. FIX: Detach iterator variables (k, v) for fresh upvals
            let loop_vars_count = (body_start - local_start) as u32;
            self.emit(OpCode::DetachUpvals(local_start as u32, loop_vars_count));

            // 4. Jump to loop condition
            self.emit(OpCode::Jump(loop_start));

            self.patch_jump(exit_jump);
            self.emit(OpCode::Pop);

            for exit in exits {
                self.patch_jump(exit);
            }
            self.leave_scope(local_start);
        } else {
            self.error("Expected '=' or 'in' for loop");
        }
    }
    fn do_statement(&mut self) {
        let local_start = self.states.last().unwrap().locals.len();
        self.statement_list();
        self.consume(Token::End, "Expected 'end' for do");
        self.leave_scope(local_start);
    }
    fn break_statement(&mut self) {
        let jump = self.emit_jump(OpCode::Jump(0));
        if let Some(exits) = self.states.last_mut().unwrap().loop_exits.last_mut() {
            exits.push(jump);
        } else {
            self.error("'break' outside loop");
        }
    }

    fn handle_statement(&mut self) {
        let chunk_idx = self.create_chunk();
        self.states.push(CompilerState {
            locals: Vec::new(),
            max_locals: 0,
            chunk_idx,
            loop_exits: Vec::new(),
            upvals: Vec::new(),
            loop_continues: Vec::new(),
            is_vararg: false,
        });
        let curr = self.states.len() - 1;
        self.resolve_upvalue(curr, "_ENV");
        self.statement_list();
        self.emit(OpCode::Return(0, false));
        let thunk_state = self.states.pop().unwrap();
        self.vm.chunks[thunk_state.chunk_idx].local_count = thunk_state.max_locals;
        self.vm.chunks[thunk_state.chunk_idx].upvals = thunk_state.upvals;
        if !self.check(Token::With) {
            self.error("Expected 'with' to handle effects");
        }

        let mut handlers = Vec::new();
        while self.match_token(Token::With) {
            self.advance();
            let eff_name = if let Token::Ident(name) = &self.previous {
                name.clone()
            } else {
                self.error("Expected effect name");
                unreachable!()
            };
            self.consume(Token::LParen, "Expected '('");
            let mut handler_params = Vec::new();
            if !self.check(Token::RParen) {
                loop {
                    self.advance();
                    if let Token::Ident(param) = &self.previous {
                        handler_params.push(param.clone());
                    }
                    if !self.match_token(Token::Comma) {
                        break;
                    }
                }
            }
            self.consume(Token::RParen, "Expected ')'");

            let h_chunk_idx = self.create_chunk();
            self.states.push(CompilerState {
                locals: handler_params,
                max_locals: 0,
                chunk_idx: h_chunk_idx,
                loop_exits: Vec::new(),
                upvals: Vec::new(),
                loop_continues: Vec::new(),
                is_vararg: false,
            });
            let mut state = self.states.last_mut().unwrap();
            state.max_locals = state.locals.len();
            let curr = self.states.len() - 1;
            self.resolve_upvalue(curr, "_ENV");
            self.statement_list();
            self.emit(OpCode::Return(0, false));
            let handler_state = self.states.pop().unwrap();
            self.vm.chunks[handler_state.chunk_idx].local_count = handler_state.max_locals;
            self.vm.chunks[handler_state.chunk_idx].upvals = handler_state.upvals;

            let eff_id = self.vm.intern_str(&eff_name);
            handlers.push((eff_id, h_chunk_idx));
        }

        self.consume(Token::End, "Expected 'end' for handle");

        for (eff_id, h_chunk_idx) in &handlers {
            self.emit(OpCode::MakeClosure(*h_chunk_idx as u32));
            self.emit(OpCode::PushHandler(*eff_id));
        }

        self.emit(OpCode::MakeClosure(thunk_state.chunk_idx as u32));
        self.emit(OpCode::Call(0, false));

        for _ in 0..handlers.len() {
            self.emit(OpCode::PopHandler);
        }
        self.emit(OpCode::AdjustStack(0));
    }

    fn expression(&mut self) -> bool {
        self.parse_precedence(Precedence::Assignment)
    }
    fn parse_precedence(&mut self, precedence: Precedence) -> bool {
        self.advance();
        let can_assign = precedence <= Precedence::Assignment;
        let mut is_multi = self.prefix_rule(can_assign);
        while precedence <= self.get_precedence(&self.current) {
            if is_multi {
                self.emit(OpCode::AdjustStack(1));
            }
            self.advance();
            is_multi = self.infix_rule(can_assign);
        }
        is_multi
    }
    fn get_precedence(&self, token: &Token) -> Precedence {
        match token {
            Token::Or => Precedence::Or,
            Token::And => Precedence::And,
            Token::BitOr => Precedence::BitOr,
            Token::BitXor => Precedence::BitXor,
            Token::BitAnd => Precedence::BitAnd,
            Token::EqEq | Token::Neq | Token::Lt | Token::Gt | Token::LtEq | Token::GtEq => {
                Precedence::Comparison
            }
            Token::Shl | Token::Shr => Precedence::BitShift,
            Token::DotDot => Precedence::Concat,
            Token::Plus | Token::Minus => Precedence::Term,
            Token::Star | Token::Slash | Token::Percent | Token::FloorDiv => Precedence::Factor,
            Token::Caret => Precedence::Power,
            Token::LParen
            | Token::Dot
            | Token::LBracket
            | Token::Colon
            | Token::StringLiteral(_)
            | Token::LBrace => Precedence::Call,
            _ => Precedence::None,
        }
    }

    fn prefix_rule(&mut self, can_assign: bool) -> bool {
        match self.previous.clone() {
            Token::DotDotDot => {
                if !self.states.last().unwrap().is_vararg {
                    self.error("Cannot use '...' outside a vararg function");
                }
                self.emit(OpCode::LoadVararg);
                true
            }
            Token::Num(n) => {
                let id = self.add_constant(Value::num(n));
                self.emit(OpCode::LoadConst(id));
                false
            }
            Token::Nil => {
                self.emit(OpCode::PushNil);
                false
            }
            Token::True => {
                self.emit(OpCode::PushTrue);
                false
            }
            Token::False => {
                self.emit(OpCode::PushFalse);
                false
            }
            Token::StringLiteral(s) => {
                let str_val = self.vm.alloc_str(&s);
                let id = self.add_constant(str_val);
                self.emit(OpCode::LoadConst(id));
                false
            }
            Token::Minus => {
                if self.parse_precedence(Precedence::Unary) {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.emit(OpCode::Neg);
                false
            }
            Token::Not => {
                if self.parse_precedence(Precedence::Unary) {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.emit(OpCode::Not);
                false
            }
            Token::Hash => {
                if self.parse_precedence(Precedence::Unary) {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.emit(OpCode::Len);
                false
            }
            Token::LBrace => {
                self.emit(OpCode::MakeTable);
                let mut array_idx = 1.0;

                while !self.check(Token::RBrace) && !self.check(Token::EOF) {
                    let mut is_array_entry = false;
                    self.emit(OpCode::Dup);

                    let mut is_multi = false;
                    if self.match_token(Token::LBracket) {
                        self.expression(); // Key
                        self.consume(Token::RBracket, "Expected ']'");
                        self.consume(Token::Eq, "Expected '='");
                        is_multi = self.expression(); // Value
                    } else if let Token::Ident(name) = self.current.clone() {
                        let next = self.scanner.peek_token();
                        if next == Token::Eq {
                            self.advance();
                            let str_val = self.vm.alloc_str(&name);
                            let id = self.add_constant(str_val);
                            self.emit(OpCode::LoadConst(id)); // Key
                            self.consume(Token::Eq, "Expected '='");
                            is_multi = self.expression(); // Value
                        } else {
                            let id = self.add_constant(Value::num(array_idx));
                            self.emit(OpCode::LoadConst(id)); // Key
                            is_multi = self.expression(); // Value
                            is_array_entry = true;
                        }
                    } else {
                        let id = self.add_constant(Value::num(array_idx));
                        self.emit(OpCode::LoadConst(id)); // Key
                        is_multi = self.expression(); // Value
                        is_array_entry = true;
                    }

                    let is_last = self.check(Token::RBrace)
                        || self.check(Token::EOF)
                        || ((self.check(Token::Comma) || self.check(Token::Semi)) && {
                            let t = self.scanner.peek_token();
                            t == Token::RBrace || t == Token::EOF
                        });

                    if is_multi && is_last && is_array_entry {

                        self.emit(OpCode::AppendMulti);
                        array_idx += 1.0;
                    } else {

                        if is_multi {
                            self.emit(OpCode::AdjustStack(1));
                        }
                        self.emit(OpCode::SetTable);
                        self.emit(OpCode::Pop);
                        if is_array_entry {
                            array_idx += 1.0;
                        }
                    }

                    if !self.match_token(Token::Comma) && !self.match_token(Token::Semi) {
                        break;
                    }
                }
                self.consume(Token::RBrace, "Expected '}' for table constructor");
                false
            }
            Token::Function => {
                self.consume(Token::LParen, "Expected '('");
                let mut params = Vec::new();
                let mut is_vararg = false;

                if !self.check(Token::RParen) {
                    loop {
                        if self.match_token(Token::DotDotDot) {

                            is_vararg = true;
                            break;
                        }
                        self.advance();
                        if let Token::Ident(param) = &self.previous {
                            params.push(param.clone());
                        }
                        if !self.match_token(Token::Comma) {
                            break;
                        }
                    }
                }
                self.consume(Token::RParen, "Expected ')'");

                let chunk_idx = self.create_chunk();
                self.states.push(CompilerState {
                    locals: params.clone(),
                    max_locals: 0,
                    chunk_idx,
                    loop_exits: Vec::new(),
                    upvals: Vec::new(),
                    loop_continues: Vec::new(),
                    is_vararg,
                });
                let curr = self.states.len() - 1;
                self.resolve_upvalue(curr, "_ENV");

                self.vm.chunks[chunk_idx].param_count = params.len();
                self.vm.chunks[chunk_idx].is_vararg = is_vararg;

                let mut state = self.states.last_mut().unwrap();
                state.max_locals = state.locals.len();
                self.statement_list();
                self.consume(Token::End, "Expected 'end' for function");
                self.emit(OpCode::Return(0, false));
                let finished_state = self.states.pop().unwrap();
                self.vm.chunks[finished_state.chunk_idx].local_count = finished_state.max_locals;
                self.vm.chunks[finished_state.chunk_idx].upvals = finished_state.upvals;
                self.emit(OpCode::MakeClosure(chunk_idx as u32));
                false
            }
            Token::Ident(name) => {
                let curr = self.states.len() - 1;
                if let Some(idx) = self.resolve_local_in(curr, &name) {
                    self.emit(OpCode::LoadLocal(idx as u32));
                } else if let Some(idx) = self.resolve_upvalue(curr, &name) {
                    self.emit(OpCode::LoadUpval(idx as u32));
                } else {
                    let str_val = self.vm.alloc_str(&name);
                    let const_id = self.add_constant(str_val);
                    if let Some(env_local_idx) = self.resolve_local_in(curr, "_ENV") {
                        self.emit(OpCode::LoadLocal(env_local_idx as u32));
                        self.emit(OpCode::LoadConst(const_id));
                        self.emit(OpCode::GetTable);
                    } else {
                        let env_idx = self
                            .resolve_upvalue(curr, "_ENV")
                            .unwrap_or_else(|| self.error("Missing _ENV upvalue"));
                        self.emit(OpCode::GetTabUp(env_idx as u32, const_id));
                    }
                }
                false
            }
            Token::Perform => {
                self.advance();
                let eff_name = if let Token::Ident(name) = &self.previous {
                    name.clone()
                } else {
                    self.error("Expected effect name");
                };
                self.consume(Token::LParen, "Expected '('");
                let mut arg_count = 0;
                if !self.check(Token::RParen) {
                    loop {
                        self.expression();
                        arg_count += 1;
                        if !self.match_token(Token::Comma) {
                            break;
                        }
                    }
                }
                self.consume(Token::RParen, "Expected ')'");
                let eff_id = self.vm.intern_str(&eff_name);
                self.emit(OpCode::Perform(eff_id, arg_count));
                true
            }
            Token::LParen => {
                let is_multi = self.expression();
                self.consume(Token::RParen, "Expected ')'");
                if is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                false
            }
            Token::Handle => {
                let chunk_idx = self.create_chunk();
                self.states.push(CompilerState {
                    locals: Vec::new(),
                    max_locals: 0,
                    chunk_idx,
                    loop_exits: Vec::new(),
                    upvals: Vec::new(),
                    loop_continues: Vec::new(),
                    is_vararg: false,
                });
                let curr = self.states.len() - 1;
                self.resolve_upvalue(curr, "_ENV");
                self.statement_list();
                self.emit(OpCode::Return(0, false));
                
                let thunk_state = self.states.pop().unwrap();
                self.vm.chunks[thunk_state.chunk_idx].local_count = thunk_state.max_locals;
                self.vm.chunks[thunk_state.chunk_idx].upvals = thunk_state.upvals;

                if !self.check(Token::With) {
                    self.error("Expected 'with' to handle effects");
                }

                let mut handlers = Vec::new();

                while self.match_token(Token::With) {
                    self.advance();
                    let eff_name = if let Token::Ident(name) = &self.previous {
                        name.clone()
                    } else {
                        self.error("Expected effect name");
                        unreachable!()
                    };
                    
                    self.consume(Token::LParen, "Expected '('");
                    let mut handler_params = Vec::new();
                    if !self.check(Token::RParen) {
                        loop {
                            self.advance();
                            if let Token::Ident(param) = &self.previous {
                                handler_params.push(param.clone());
                            }
                            if !self.match_token(Token::Comma) {
                                break;
                            }
                        }
                    }
                    self.consume(Token::RParen, "Expected ')'");

                    let h_chunk_idx = self.create_chunk();
                    self.states.push(CompilerState {
                        locals: handler_params,
                        max_locals: 0,
                        chunk_idx: h_chunk_idx,
                        loop_exits: Vec::new(),
                        upvals: Vec::new(),
                        loop_continues: Vec::new(),
                        is_vararg: false,
                    });
                    let mut state = self.states.last_mut().unwrap();
                    state.max_locals = state.locals.len();
                    let curr = self.states.len() - 1;
                    self.resolve_upvalue(curr, "_ENV");
                    self.statement_list();
                    self.emit(OpCode::Return(0, false));
                    
                    let handler_state = self.states.pop().unwrap();
                    self.vm.chunks[handler_state.chunk_idx].local_count = handler_state.max_locals;
                    self.vm.chunks[handler_state.chunk_idx].upvals = handler_state.upvals;

                    let eff_id = self.vm.intern_str(&eff_name);
                    handlers.push((eff_id, h_chunk_idx));
                }

                self.consume(Token::End, "Expected 'end' for handle");

                for (eff_id, h_chunk_idx) in &handlers {
                    self.emit(OpCode::MakeClosure(*h_chunk_idx as u32));
                    self.emit(OpCode::PushHandler(*eff_id));
                }

                self.emit(OpCode::MakeClosure(thunk_state.chunk_idx as u32));
                self.emit(OpCode::Call(0, true)); 
                
                for _ in 0..handlers.len() {
                    self.emit(OpCode::PopHandler);
                }
                true 
            }
            _ => self.error("Expected expression"),
        }
    }

    fn infix_rule(&mut self, can_assign: bool) -> bool {
        match self.previous.clone() {
            t @ (Token::Plus
            | Token::Minus
            | Token::Star
            | Token::Slash
            | Token::Percent
            | Token::FloorDiv
            | Token::EqEq
            | Token::Neq
            | Token::Lt
            | Token::Gt
            | Token::LtEq
            | Token::GtEq
            | Token::BitAnd
            | Token::BitOr
            | Token::BitXor
            | Token::Shl
            | Token::Shr
            | Token::Caret) => {
                let prec = self.get_precedence(&t);

                let next_prec = if t == Token::Caret {
                    prec
                } else {
                    unsafe { std::mem::transmute(prec as u8 + 1) }
                };

                let right_is_multi = self.parse_precedence(next_prec);
                if right_is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                match t {
                    Token::Plus => self.emit(OpCode::Add),
                    Token::Minus => self.emit(OpCode::Sub),
                    Token::Star => self.emit(OpCode::Mul),
                    Token::Slash => self.emit(OpCode::Div),
                    Token::Percent => self.emit(OpCode::Mod),
                    Token::FloorDiv => self.emit(OpCode::FloorDiv),
                    Token::Caret => self.emit(OpCode::Pow),
                    Token::EqEq => self.emit(OpCode::Eq),
                    Token::Neq => {
                        self.emit(OpCode::Eq);
                        self.emit(OpCode::Not)
                    }
                    Token::Lt => self.emit(OpCode::Lt),
                    Token::Gt => self.emit(OpCode::Gt),
                    Token::LtEq => self.emit(OpCode::LtEq),
                    Token::GtEq => self.emit(OpCode::GtEq),
                    Token::BitAnd => self.emit(OpCode::BitAnd),
                    Token::BitOr => self.emit(OpCode::BitOr),
                    Token::BitXor => self.emit(OpCode::BitXor),
                    Token::Shl => self.emit(OpCode::Shl),
                    Token::Shr => self.emit(OpCode::Shr),
                    _ => unreachable!(),
                }
                false
            }
            Token::And => {
                let jump = self.emit_jump(OpCode::JumpIfFalseKeep(0));
                self.emit(OpCode::Pop);
                let right_is_multi = self.parse_precedence(Precedence::And);
                if right_is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.patch_jump(jump);
                false
            }
            Token::Or => {
                let jump = self.emit_jump(OpCode::JumpIfTrueKeep(0));
                self.emit(OpCode::Pop);
                let right_is_multi = self.parse_precedence(Precedence::Or);
                if right_is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.patch_jump(jump);
                false
            }
            Token::DotDot => {
                let right_is_multi = self.parse_precedence(Precedence::Concat);
                if right_is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.emit(OpCode::Concat);
                false
            }
            Token::Dot => {
                self.advance();
                let field = if let Token::Ident(name) = &self.previous {
                    name.clone()
                } else {
                    self.error("Expected field name");
                    unreachable!()
                };
                let str_val = self.vm.alloc_str(&field);
                let const_id = self.add_constant(str_val);
                self.emit(OpCode::LoadConst(const_id));
                if can_assign && self.match_token(Token::Eq) {
                    let is_multi_val = self.expression();

                    if is_multi_val {
                        self.emit(OpCode::AdjustStack(1));
                    }

                    self.emit(OpCode::SetTable);
                } else {
                    self.emit(OpCode::GetTable);
                }
                false
            }
            Token::LBracket => {
                let is_multi = self.expression();

                if is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }

                self.consume(Token::RBracket, "Expected ']'");
                if can_assign && self.match_token(Token::Eq) {
                    let is_multi_val = self.expression();

                    if is_multi_val {
                        self.emit(OpCode::AdjustStack(1));
                    }

                    self.emit(OpCode::SetTable);
                } else {
                    self.emit(OpCode::GetTable);
                }
                false
            }
            Token::LParen => {
                let mut arg_count = 0;
                let mut last_multi = false;
                if !self.check(Token::RParen) {
                    loop {
                        last_multi = self.expression();
                        arg_count += 1;
                        if self.match_token(Token::Comma) {
                            if last_multi {
                                self.emit(OpCode::AdjustStack(1));
                            }
                        } else {
                            break;
                        }
                    }
                }
                self.consume(Token::RParen, "Expected ')' for function call");
                self.emit(OpCode::Call(arg_count as u32, last_multi));
                true
            }
            Token::Colon => {
                self.advance();
                let method_name = if let Token::Ident(name) = &self.previous {
                    name.clone()
                } else {
                    self.error("Expected method name");
                    unreachable!()
                };

                self.emit(OpCode::Dup);
                let str_val = self.vm.alloc_str(&method_name);
                let const_id = self.add_constant(str_val);
                self.emit(OpCode::LoadConst(const_id));

                self.emit(OpCode::GetTable);
                self.emit(OpCode::Swap);

                let mut arg_count = 1;
                let mut last_multi = false;

                if self.match_token(Token::LParen) {

                    if !self.check(Token::RParen) {
                        loop {
                            last_multi = self.expression();
                            arg_count += 1;
                            if self.match_token(Token::Comma) {
                                if last_multi {
                                    self.emit(OpCode::AdjustStack(1));
                                }
                            } else {
                                break;
                            }
                        }
                    }
                    self.consume(Token::RParen, "Expected ')' for method call");
                } else if let Token::StringLiteral(s) = self.current.clone() {

                    self.advance();
                    let str_val = self.vm.alloc_str(&s);
                    let const_id = self.add_constant(str_val);
                    self.emit(OpCode::LoadConst(const_id));
                    arg_count += 1;
                } else if self.check(Token::LBrace) {

                    self.expression();
                    arg_count += 1;
                } else {
                    self.error("Expected '(', '{', or string literal for method call");
                }

                self.emit(OpCode::Call(arg_count as u32, last_multi));
                true
            }
            Token::StringLiteral(s) => {
                let str_val = self.vm.alloc_str(&s);
                let const_id = self.add_constant(str_val);
                self.emit(OpCode::LoadConst(const_id));

                self.emit(OpCode::Call(1, false));
                true
            }
            Token::LBrace => {
                self.prefix_rule(false);
                self.emit(OpCode::Call(1, false));
                true
            }
            _ => unreachable!(),
        }
    }
}

fn execute_source(vm: &mut VM, source: &str, chunk_name: &str) -> Result<(), String> {
    let chunk_idx = Compiler::compile(vm, source, chunk_name)?;
    let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
    let closure = vm.alloc(GcObject::Closure {
        chunk_idx,
        upvalues: vec![env_upval],
    });

    vm.call_stack.push(CallFrame {
        closure_id: closure,
        chunk_idx,
        ip: 0,
        stack_base: vm.data_stack.len(),
        handler_base: vm.handler_stack.len(),
        varargs: Vec::new(),
    });

    for _ in 0..vm.chunks[chunk_idx].local_count {
        vm.data_stack.push(Value::nil());
    }

    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        vm.run();
    }));

    std::panic::set_hook(prev_hook);

    match result {
        Ok(_) => Ok(()),
        Err(payload) => {
            if let Some(err_msg) = payload.downcast_ref::<String>() {
                Err(format!("Uncaught Error: {}", err_msg))
            } else if let Some(val) = payload.downcast_ref::<Value>() {
                Err(format!("Uncaught Error: {}\n{}", vm.val_to_str(*val), vm.last_traceback))
            } else {
                Err(format!("Uncaught runtime error.\n{}", vm.last_traceback))
            }
        }
    }
}

fn run_repl(vm: &mut VM) {
    println!("Lua Algebraic Effects REPL");
    let mut input = String::new();

    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        input.clear();

        if io::stdin().read_line(&mut input).unwrap_or(0) == 0 {
            println!();
            break; // EOF
        }

        let line = input.trim();
        if line.is_empty() {
            continue;
        }

        // Trick: First try to compile it as an expression returning a value
        let expr_source = format!("return {}", line);
        let compile_res = Compiler::compile(vm, &expr_source, "=(stdin)");

        let chunk_idx = match compile_res {
            Ok(idx) => idx,
            Err(_) => {
                // If it fails, compile it as a standard statement
                match Compiler::compile(vm, line, "=(stdin)") {
                    Ok(idx) => idx,
                    Err(err) => {
                        eprintln!("{}", err);
                        continue;
                    }
                }
            }
        };

        let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
        let closure = vm.alloc(GcObject::Closure {
            chunk_idx,
            upvalues: vec![env_upval],
        });

        let stack_base = vm.data_stack.len();
        vm.call_stack.push(CallFrame {
            closure_id: closure,
            chunk_idx,
            ip: 0,
            stack_base,
            handler_base: vm.handler_stack.len(),
            varargs: Vec::new(),
        });

        for _ in 0..vm.chunks[chunk_idx].local_count {
            vm.data_stack.push(Value::nil());
        }

        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            vm.run();
        }));

        std::panic::set_hook(prev_hook);

        match result {
            Ok(_) => {
                let rets = vm.multiret_count;
                if rets > 0 {
                    let start = vm.data_stack.len().saturating_sub(rets);
                    for i in 0..rets {
                        let val = vm.data_stack[start + i];
                        print!("{}\t", vm.val_to_str(val));
                    }
                    println!();
                    vm.data_stack.truncate(start); // cleanup returns
                }
            }
            Err(payload) => {
                if let Some(err_msg) = payload.downcast_ref::<String>() {
                    eprintln!("Error: {}", err_msg);
                } else if let Some(val) = payload.downcast_ref::<Value>() {
                    eprintln!("Error: {}\n{}", vm.val_to_str(*val), vm.last_traceback);
                } else {
                    eprintln!("Runtime error.\n{}", vm.last_traceback);
                }
                vm.data_stack.truncate(stack_base);
                vm.call_stack.clear();
                vm.handler_stack.clear();
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut vm = VM::new();
    vm.open_standard_libs();

    let init_script = r##"
        function print(...)
            local args = {...}
            local out = {}
            for i = 1, select("#", ...) do
                table.insert(out, tostring(args[i]))
            end
            __raw_print(table.concat(out, "\t"))
        end
    "##;
    
    if let Err(e) = execute_source(&mut vm, init_script, "=(init)") {
        eprintln!("Init error: {}", e);
        return;
    }

    let mut i = 1;
    let mut script_file = None;
    let mut script_args = Vec::new();
    let mut enter_repl = false;
    let mut execute_stmts = Vec::new();
    let mut require_libs = Vec::new();

    if args.len() == 1 {
        enter_repl = true;
    }

    // Parse CLI arguments
    while i < args.len() {
        let arg = &args[i];
        if script_file.is_some() {
            script_args.push(arg.clone());
        } else if arg == "-i" {
            enter_repl = true;
        } else if arg == "-v" {
            println!("LuaAE 0.1.0");
        } else if arg == "-e" {
            i += 1;
            if i < args.len() {
                execute_stmts.push(args[i].clone());
            }
        } else if arg == "-l" {
            i += 1;
            if i < args.len() {
                require_libs.push(args[i].clone());
            }
        } else if arg == "--" {
            i += 1;
            if i < args.len() {
                script_file = Some(args[i].clone());
                i += 1;
                while i < args.len() {
                    script_args.push(args[i].clone());
                    i += 1;
                }
            }
            break;
        } else if arg == "-" {
            script_file = Some(arg.clone());
        } else if arg.starts_with('-') {
            eprintln!("usage: {} [options] [script [args]]", args[0]);
            eprintln!("Available options:");
            eprintln!("  -e stat  execute string 'stat'");
            eprintln!("  -i       enter interactive mode after executing 'script'");
            eprintln!("  -l name  require library 'name'");
            eprintln!("  -v       show version information");
            eprintln!("  --       stop handling options");
            eprintln!("  -        stop handling options and execute stdin");
            return;
        } else {
            script_file = Some(arg.clone());
        }
        i += 1;
    }

    // Build the global `arg` table
    let mut arg_map = std::collections::HashMap::new();
    arg_map.insert(Value::num(0.0), vm.alloc_str(script_file.as_deref().unwrap_or(&args[0])));
    
    for (idx, arg_str) in script_args.iter().enumerate() {
        let val = vm.alloc_str(arg_str);
        arg_map.insert(Value::num((idx + 1) as f64), val);
    }
    
    // Negative indices for arguments before the script
    let mut neg_idx = -1.0;
    for arg_str in args.iter().take(args.iter().position(|r| Some(r) == script_file.as_ref()).unwrap_or(args.len())).rev() {
        let val = vm.alloc_str(arg_str);
        arg_map.insert(Value::num(neg_idx), val);
        neg_idx -= 1.0;
    }

    let arg_table_id = vm.alloc(GcObject::Table(arg_map, None));
    vm.set_global("arg", Value::obj(arg_table_id));

    // Handle -l
    for lib in require_libs {
        let req_src = format!("require('{}')", lib);
        if let Err(e) = execute_source(&mut vm, &req_src, "=(command line)") {
            eprintln!("{}", e);
            return;
        }
    }

    // Handle -e
    for stmt in execute_stmts {
        if let Err(e) = execute_source(&mut vm, &stmt, "=(command line)") {
            eprintln!("{}", e);
            return;
        }
    }

    // Execute script
    if let Some(filename) = script_file {
        let source = if filename == "-" {
            let mut src = String::new();
            std::io::Read::read_to_string(&mut io::stdin(), &mut src).unwrap();
            src
        } else {
            match std::fs::read_to_string(&filename) {
                Ok(content) => content,
                Err(err) => {
                    eprintln!("Cannot open {}: {}", filename, err);
                    return;
                }
            }
        };

        if let Err(e) = execute_source(&mut vm, &source, &format!("@{}", filename)) {
            eprintln!("{}", e);
            if !enter_repl {
                std::process::exit(1);
            }
        }
    }

    // REPL if requested or no script provided
    if enter_repl {
        run_repl(&mut vm);
    }
}
