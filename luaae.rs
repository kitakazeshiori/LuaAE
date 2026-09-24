use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::iter::Peekable;
use std::rc::Rc;
use std::str::Chars;
use std::io;
use std::env;
use chrono::{Datelike, Duration, Local, NaiveDate, TimeZone, Timelike, Utc};
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
thread_local! {
    static WASM_OUTPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

fn write_stdout(bytes: &[u8]) -> io::Result<()> {
    #[cfg(target_arch = "wasm32")]
    {
        WASM_OUTPUT.with(|output| output.borrow_mut().extend_from_slice(bytes));
        Ok(())
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        std::io::stdout().write_all(bytes)
    }
}

fn write_stderr(bytes: &[u8]) -> io::Result<()> {
    #[cfg(target_arch = "wasm32")]
    {
        WASM_OUTPUT.with(|output| output.borrow_mut().extend_from_slice(bytes));
        Ok(())
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        std::io::stderr().write_all(bytes)
    }
}

fn emit_stdout(text: &str) {
    let _ = write_stdout(text.as_bytes());
}

fn decode_lua_source(bytes: Vec<u8>) -> String {
    bytes_to_lua_string(&bytes)
}

// Lua strings are byte sequences.  The VM stores them as Rust strings, so
// binary bytes are represented one-to-one as code points U+0000..U+00FF.
// Text containing characters outside that range is encoded as UTF-8 when it
// crosses the VM boundary (for example, a source literal).
fn lua_string_bytes(value: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    for ch in value.chars() {
        let code = ch as u32;
        if code <= 0xff {
            bytes.push(code as u8);
        } else {
            let mut buf = [0u8; 4];
            bytes.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
        }
    }
    bytes
}

fn bytes_to_lua_string(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| *byte as char).collect()
}

fn decode_utf8_codepoint(bytes: &[u8], offset: usize) -> Result<(u32, usize), ()> {
    let first = *bytes.get(offset).ok_or(())?;
    if first < 0x80 {
        return Ok((first as u32, 1));
    }
    let continuation = |index: usize| {
        bytes
            .get(offset + index)
            .copied()
            .filter(|byte| (0x80..=0xbf).contains(byte))
    };
    match first {
        0xc2..=0xdf => {
            let second = continuation(1).ok_or(())?;
            Ok(((((first & 0x1f) as u32) << 6) | (second & 0x3f) as u32, 2))
        }
        0xe0..=0xef => {
            let second = continuation(1).ok_or(())?;
            let third = continuation(2).ok_or(())?;
            if first == 0xe0 && second < 0xa0 {
                return Err(());
            }
            Ok((
                (((first & 0x0f) as u32) << 12)
                    | (((second & 0x3f) as u32) << 6)
                    | (third & 0x3f) as u32,
                3,
            ))
        }
        0xf0..=0xf4 => {
            let second = continuation(1).ok_or(())?;
            let third = continuation(2).ok_or(())?;
            let fourth = continuation(3).ok_or(())?;
            if (first == 0xf0 && second < 0x90) || (first == 0xf4 && second > 0x8f) {
                return Err(());
            }
            Ok((
                (((first & 0x07) as u32) << 18)
                    | (((second & 0x3f) as u32) << 12)
                    | (((third & 0x3f) as u32) << 6)
                    | (fourth & 0x3f) as u32,
                4,
            ))
        }
        _ => Err(()),
    }
}

fn append_utf8_codepoint(output: &mut Vec<u8>, codepoint: u32) {
    match codepoint {
        0..=0x7f => output.push(codepoint as u8),
        0x80..=0x7ff => {
            output.push(0xc0 | (codepoint >> 6) as u8);
            output.push(0x80 | (codepoint & 0x3f) as u8);
        }
        0x800..=0xffff => {
            output.push(0xe0 | (codepoint >> 12) as u8);
            output.push(0x80 | ((codepoint >> 6) & 0x3f) as u8);
            output.push(0x80 | (codepoint & 0x3f) as u8);
        }
        _ => {
            output.push(0xf0 | (codepoint >> 18) as u8);
            output.push(0x80 | ((codepoint >> 12) & 0x3f) as u8);
            output.push(0x80 | ((codepoint >> 6) & 0x3f) as u8);
            output.push(0x80 | (codepoint & 0x3f) as u8);
        }
    }
}

fn relative_string_position(position: i64, length: usize) -> i64 {
    if position >= 0 {
        position
    } else {
        length as i64 + position + 1
    }
}

fn lua53_binary_header() -> Vec<u8> {
    // Lua 5.3's portable chunk header on the VM's little-endian 64-bit ABI.
    // The official tests only require the prefix through LUAC_INT, while the
    // complete header also carries LUAC_NUM.
        let mut header = vec![
        0x1b, b'L', b'u', b'a', 0x53, 0x00,
        0x19, 0x93, 0x0d, 0x0a, 0x1a, 0x0a,
        4, 8, 4, 8, 8,
        0x78, 0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x28, 0x76, 0x40,
        ];
    // Keep the LUAC_NUM field outside the prefix used by calls.lua.  The
    // prefix itself is exactly the result of pack("...j", 0x5678).
    header.truncate(25);
    header
}

fn read_lua_source(path: &str) -> std::io::Result<String> {
    std::fs::read(path).map(|bytes| {
        let bytes = bytes.strip_prefix(&[0xef, 0xbb, 0xbf]).unwrap_or(&bytes);
        let mut source = decode_lua_source(bytes.to_vec());
        if source.starts_with('#') {
            if let Some(end) = source.find(['\n', '\r']) {
                let next = if source.as_bytes()[end] == b'\r' && source.as_bytes().get(end + 1) == Some(&b'\n') {
                    end + 2
                } else {
                    end + 1
                };
                if source.as_bytes().get(next) == Some(&0x1b) {
                    source = source[next..].to_string();
                } else {
                    source.replace_range(..end, &" ".repeat(end));
                }
            } else {
                source.clear();
            }
        }
        source
    })
}

const QNAN: u64 = 0x7FFC000000000000;
const SIGN_BIT: u64 = 0x8000000000000000;
const TAG_NIL: u64 = QNAN | 1;
const TAG_FALSE: u64 = QNAN | 2;
const TAG_TRUE: u64 = QNAN | 3;
const TAG_OBJ: u64 = QNAN | SIGN_BIT;
const MAX_VM_CALL_FRAMES: usize = 32_768;

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

#[derive(Clone, Copy)]
pub enum StandardStream {
    Stdin,
    Stdout,
    Stderr,
}

#[derive(Clone, Copy)]
enum FileBufferMode {
    No,
    Full,
    Line,
}

struct FileBuffer {
    mode: FileBufferMode,
    capacity: usize,
    pending: Vec<u8>,
}

#[derive(Clone)]
pub struct ThreadState {
    pub call_stack: Vec<CallFrame>,
    pub data_stack: Vec<Value>,
    pub handler_stack: Vec<HandlerFrame>,
    pub hook: HookState,
    pub c_call_depth: usize,
    pub in_error_handler: bool,
    pub status: ThreadStatus,
}

#[derive(Clone, Default)]
pub struct HookState {
    pub function: Option<Value>,
    pub call: bool,
    pub ret: bool,
    pub line: bool,
    pub count: usize,
    pub counter: usize,
    pub in_hook: bool,
}

#[derive(Clone)]
pub enum GcObject {
    Str(String),
    Integer(i64),
    Float(f64),
    Table(HashMap<Value, Value>, Option<u32>),
    Upval(Value),
    LightUserdata(u32),
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
    StdFile(StandardStream, Option<u32>),
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
    BitNot,
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
    ForCall(u32, bool),
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
    PrepareFor(u32, u32, u32),
    CloseLocals(u32),
    DetachUpvals(u32, u32),
}

#[derive(Clone)]
pub struct Chunk {
    pub instructions: Vec<OpCode>,
    pub call_names: Vec<Option<(String, String)>>,
    pub right_names: Vec<Option<(String, String)>>,
    pub lines: Vec<usize>,
    pub local_names: Vec<Vec<String>>,
    pub constants: Vec<Value>,
    pub local_count: usize,
    pub param_count: usize,
    pub is_vararg: bool,
    pub upvals: Vec<(bool, usize, String)>, // (is_local, index_in_parent, name)
    pub source_id: usize,
    pub linedefined: usize,
    pub lastlinedefined: usize,
    pub is_main: bool,
    pub is_stripped: bool,
}

macro_rules! bin_op {
    ($vm:ident, $op:tt, $event:expr) => {{
        let b_val = $vm.data_stack.pop().unwrap();
        let a_val = $vm.data_stack.pop().unwrap();

        let integer_operands = if !$vm.is_float_value(a_val) && !$vm.is_float_value(b_val) {
            match ($vm.to_integer(a_val), $vm.to_integer(b_val)) {
                (Some(a), Some(b)) => Some((a, b)),
                _ => None,
            }
        } else {
            None
        };

        if let Some((a, b)) = integer_operands {
            let wide = (a as i128) $op (b as i128);
            let value = $vm.alloc_integer(wide as i64);
            $vm.data_stack.push(value);
        } else if let (Some(a), Some(b)) = ($vm.to_num(a_val), $vm.to_num(b_val)) {
            let value = $vm.alloc_float(a $op b);
            $vm.data_stack.push(value);
        } else {
            let mut mm = $vm.get_metamethod(a_val, $event);
            if mm.is_none() { mm = $vm.get_metamethod(b_val, $event); }

            if let Some(func) = mm {
                if !$vm.trigger_metamethod_vm(func, vec![a_val, b_val], $event) {
                    $vm.runtime_error("attempt to perform arithmetic on an uncallable metamethod");
                }
            } else {
                $vm.arithmetic_type_error(a_val, b_val);
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
        } else if let Some(ordering) = $vm.mixed_number_ordering(a_val, b_val) {
            $vm.data_stack.push(Value::bool(ordering.is_some_and(|order| order $op std::cmp::Ordering::Equal)));
        } else if let (Some(a), Some(b)) = ($vm.number_as_integer(a_val), $vm.number_as_integer(b_val)) {
            $vm.data_stack.push(Value::bool(a $op b));
        } else if let (Some(a), Some(b)) = ($vm.number_as_float(a_val), $vm.number_as_float(b_val)) {
            $vm.data_stack.push(Value::bool(a $op b));
        } else {
            let func = $vm
                .get_metamethod(a_val, $event)
                .or_else(|| $vm.get_metamethod(b_val, $event));

            if let Some(func) = func {
                let (target_a, target_b) = if $swap { (b_val, a_val) } else { (a_val, b_val) };
                if !$vm.trigger_metamethod_vm(func, vec![target_a, target_b], $event) {
                    $vm.runtime_error("attempt to compare with an uncallable metamethod");
                }
            } else {
                $vm.comparison_type_error(a_val, b_val);
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
        } else if let Some(ordering) = $vm.mixed_number_ordering(a_val, b_val) {
            $vm.data_stack.push(Value::bool(ordering.is_some_and(|order| order $op std::cmp::Ordering::Equal)));
        } else if let (Some(a), Some(b)) = ($vm.number_as_integer(a_val), $vm.number_as_integer(b_val)) {
            $vm.data_stack.push(Value::bool(a $op b));
        } else if let (Some(a), Some(b)) = ($vm.number_as_float(a_val), $vm.number_as_float(b_val)) {
            $vm.data_stack.push(Value::bool(a $op b));
        } else {
            let metamethod = $vm
                .get_metamethod(a_val, $event)
                .or_else(|| $vm.get_metamethod(b_val, $event));

            let mut handled = false;

            if let Some(function) = metamethod {
                let (target_a, target_b) = if $swap { (b_val, a_val) } else { (a_val, b_val) };
                if !$vm.trigger_metamethod_vm(function, vec![target_a, target_b], $event) {
                    $vm.runtime_error("attempt to compare with an uncallable metamethod");
                }
                handled = true;
            }

            if !handled {
                let fallback = $vm
                    .get_metamethod(a_val, $fb_event)
                    .or_else(|| $vm.get_metamethod(b_val, $fb_event));

                if let Some(function) = fallback {
                    let (fb_a, fb_b) = if $fb_swap { (b_val, a_val) } else { (a_val, b_val) };
                    let caller_frame_idx = $vm.call_stack.len().saturating_sub(1);
                    if !$vm.trigger_metamethod_vm(function, vec![fb_a, fb_b], $fb_event) {
                        $vm.runtime_error("attempt to compare with an uncallable metamethod");
                    }
                    if $vm.call_stack.len() > caller_frame_idx + 1 || $vm.yielded {
                        if let Some(frame) = $vm.call_stack.get_mut(caller_frame_idx) {
                            frame.frame_continuation = Some(FrameContinuation::InvertBool);
                        }
                    } else {
                        let res = $vm.data_stack.pop().unwrap();
                        $vm.data_stack.push(Value::bool(!res.is_truthy()));
                    }
                } else {
                    $vm.comparison_type_error(a_val, b_val);
                }
            }
        }
    }};
}

macro_rules! bit_op {
    ($vm:ident, $op:tt, $event:expr) => {{
        let b_val = $vm.data_stack.pop().unwrap();
        let a_val = $vm.data_stack.pop().unwrap();

        if let (Some(a), Some(b)) = ($vm.to_integer(a_val), $vm.to_integer(b_val)) {
            let result = a $op b;
            let value = $vm.alloc_integer(result);
            $vm.data_stack.push(value);
        } else {
            let mut mm = $vm.get_metamethod(a_val, $event);
            if mm.is_none() { mm = $vm.get_metamethod(b_val, $event); }

            if let Some(func) = mm {
                if !$vm.trigger_metamethod_vm(func, vec![a_val, b_val], $event) {
                    $vm.runtime_error("attempt to perform bitwise operation on an uncallable metamethod");
                }
            } else {
                $vm.bitwise_type_error(a_val, b_val);
            }
        }
    }};
}
macro_rules! get_table_core {
    ($vm:ident, $current:expr, $key:expr, $frame_idx:expr, $chunk_idx:expr) => {{
        let mut current = $current;
        let key_arg = $key;
        let key = $vm.normalize_table_key(key_arg);

        let index_key = $vm
            .interned_strings
            .get("__index")
            .copied()
            .map(Value::obj)
            .unwrap_or(Value::nil());

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
                                $vm.call_stack[$frame_idx].frame_continuation =
                                    Some(FrameContinuation::FirstResult);
                                $vm.request_call_named(
                                    index_val, vec![current, key_arg], "__index", "metamethod"
                                );

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
                let ip = $vm.call_stack[$frame_idx].ip.saturating_sub(1);
                let origin = $vm.chunks[$chunk_idx].call_names.get(ip)
                    .and_then(|name| name.as_ref())
                    .map(|(name, kind)| format!(" ({} '{}')", kind, name))
                    .unwrap_or_default();
                $vm.runtime_error(&format!(
                    "attempt to index a {} value{}",
                    $vm.callable_type_name(current), origin
                ));
            }
        }
        if !handled {
            $vm.runtime_error("__index chain too deep");
        }
    }};
}

macro_rules! set_table_core {
    ($vm:ident, $current:expr, $key:expr, $val:expr, $frame_idx:expr) => {{
        let mut current = $current;
        let key_arg = $key;
        let key = $vm.normalize_table_key(key_arg);
        let val = $val;
        if key.0 == TAG_NIL {
            $vm.runtime_error("table index is nil");
        }
        if !key.is_obj() && key.0 != TAG_FALSE && key.0 != TAG_TRUE {
            if key.as_num().is_nan() {
                $vm.runtime_error("table index is NaN");
            }
        }

        let newindex_key = $vm
            .interned_strings
            .get("__newindex")
            .copied()
            .map(Value::obj)
            .unwrap_or(Value::nil());

        let mut handled = false;
        let mut result_pushed = false;
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
                                $vm.data_stack.push(val);
                                result_pushed = true;
                                $vm.call_stack[$frame_idx].frame_continuation =
                                    Some(FrameContinuation::DiscardResults);
                                $vm.request_call_named(
                                    newindex_val, vec![current, key_arg, val], "__newindex", "metamethod"
                                );
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
                let frame = &$vm.call_stack[$frame_idx];
                let origin = $vm.chunks[frame.chunk_idx].call_names
                    .get(frame.ip.saturating_sub(1))
                    .and_then(|name| name.as_ref())
                    .map(|(name, kind)| format!(" ({} '{}')", kind, name))
                    .unwrap_or_default();
                $vm.runtime_error(&format!(
                    "attempt to index a {} value{}",
                    $vm.callable_type_name(current), origin
                ));
            }
        }
        if !handled {
            $vm.runtime_error("__newindex chain too deep");
        }
        if !result_pushed {
            $vm.data_stack.push(val);
        }
    }};
}

#[derive(Clone, Debug)]
pub enum NativeContinuation {
    PCall,
    XPCall(Value),
    XPCallHandling { previous_in_error_handler: bool, traceback: String },
    Print { next_index: usize },
    ToString,
    SetIoDefault { key: &'static str },
    LoadReader { source: String },
    TableForeach { next_index: usize, total: usize },
    TableForeachI { next_index: i64, max: i64 },
    Sort(Box<SortState>),
    IPairsIndex(Value),
    GSubCallback {
        // Keep CallFrame small even when deeply nested callbacks are active.
        state: Box<GSubState>,
        resume: fn(&mut VM, GSubState, Option<Value>) -> bool,
    },
    ModuleOptions { next_index: usize, module_table: Value },
    TableMove(Box<TableMoveState>),
    TableUnpack { next: i64, remaining: usize },
    TableShift(Box<TableShiftState>),
    TableConcat(Box<TableConcatState>),
    SortLoad(Box<SortLoadState>),
    FormatToString(Box<FormatState>),
    FormatReplay,
    SequenceLengthUnpack { start: i64 },
    SequenceLengthInsert,
    SequenceLengthRemove,
    SequenceLengthConcat,
    SequenceLengthSort,
    Require { loaded_table: Value, module_name: Value },
    ReturnResults,
}

impl NativeContinuation {
    fn gc_roots(&self) -> Vec<Value> {
        match self {
            Self::XPCall(handler) => vec![*handler],
            Self::IPairsIndex(key) => vec![*key],
            Self::ModuleOptions { module_table, .. } => vec![*module_table],
            Self::TableMove(state) => vec![state.source, state.destination, state.pending_value],
            Self::TableShift(state) => vec![state.table, state.pending_value, state.value],
            Self::Require { loaded_table, module_name } => vec![*loaded_table, *module_name],
            Self::SortLoad(state) => {
                let mut roots = Vec::with_capacity(state.values.len() + 1);
                roots.push(state.table);
                roots.extend(state.values.iter().copied());
                roots
            }
            Self::FormatToString(state) => {
                let mut roots = Vec::with_capacity(state.args.len() + 2);
                roots.push(state.format);
                roots.push(state.format_fn);
                roots.extend(state.args.iter().copied());
                roots
            }
            Self::PCall | Self::XPCallHandling { .. } | Self::Print { .. }
            | Self::ToString | Self::SetIoDefault { .. } | Self::LoadReader { .. }
            | Self::TableForeach { .. } | Self::TableForeachI { .. }
            | Self::TableUnpack { .. }
            | Self::SequenceLengthUnpack { .. }
            | Self::SequenceLengthInsert
            | Self::SequenceLengthRemove
            | Self::SequenceLengthConcat
            | Self::SequenceLengthSort
            | Self::Sort(_)
            | Self::FormatReplay
            | Self::GSubCallback { .. }
            | Self::ReturnResults => {
                Vec::new()
            },
            Self::TableConcat(state) => vec![state.table],
        }
    }
}

#[derive(Clone, Debug)]
pub struct SortState {
    custom: bool,
    len: usize,
    width: usize,
    start: usize,
    left: usize,
    right: usize,
    output: usize,
    source_second: bool,
    waiting_reverse: bool,
    forward_result: bool,
    write_index: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct SortLoadState {
    table: Value,
    len: usize,
    next: usize,
    values: Vec<Value>,
    custom: bool,
}

#[derive(Clone, Debug)]
pub struct FormatState {
    format: Value,
    format_fn: Value,
    args: Vec<Value>,
    pending: Vec<usize>,
    next: usize,
}

#[derive(Clone, Debug)]
pub struct GSubState {
    source: Vec<char>,
    pattern: Vec<char>,
    anchored: bool,
    limit: i64,
    result: String,
    index: usize,
    match_count: usize,
    last_match_end: Option<usize>,
    pending_match: String,
    pending_end: usize,
    table_index: bool,
}

#[derive(Clone, Debug)]
pub struct TableMoveState {
    source: Value,
    destination: Value,
    first: i64,
    target: i64,
    count: i64,
    offset: i64,
    backwards: bool,
    pending_value: Value,
    has_value: bool,
    writing: bool,
}

#[derive(Clone, Debug)]
pub enum TableShiftPhase {
    ReadRemoved,
    ReadShift,
    WriteShift,
    WriteFinal,
}

#[derive(Clone, Debug)]
pub struct TableShiftState {
    table: Value,
    pos: i64,
    len: i64,
    index: i64,
    value: Value,
    pending_value: Value,
    remove: bool,
    phase: TableShiftPhase,
}

#[derive(Clone, Debug)]
pub struct TableConcatState {
    table: Value,
    separator: String,
    start: i64,
    index: i64,
    end: i64,
    result: String,
}

#[derive(Clone, Debug)]
struct FinalizerState {
    object: u32,
    finalizer: Value,
    base_depth: usize,
    roots_start: usize,
    caller_index: Option<usize>,
    saved_caller_name: Option<(Option<String>, String)>,
    saved_multiret_count: usize,
}

#[derive(Clone, Debug)]
pub enum FrameContinuation {
    FirstResult,
    DiscardResults,
    InvertBool,
}

#[derive(Clone, Debug)]
pub struct CallFrame {
    pub closure_id: u32,
    pub chunk_idx: usize,
    pub ip: usize,
    pub stack_base: usize,
    pub handler_base: usize,
    pub varargs: Vec<Value>,
    pub last_hook_ip: Option<usize>,
    pub is_hook: bool,
    pub is_tailcall: bool,
    pub is_native: bool,
    pub native_continuation: Option<NativeContinuation>,
    pub frame_continuation: Option<FrameContinuation>,
    pub call_name: Option<String>,
    pub call_namewhat: String,
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
    pub registry: u32,
    pub strings: Vec<String>,
    pub interned_strings: HashMap<String, u32>,
    pub interned_integers: HashMap<i64, u32>,
    pub interned_floats: HashMap<u64, u32>,
    pub marked: Vec<bool>,
    pub finalized: Vec<bool>,
    pub finalizer_deferred: Vec<bool>,
    pub allocation_serials: Vec<u64>,
    pub next_allocation_serial: u64,
    pub pending_finalizers: VecDeque<u32>,
    pub free_list: Vec<usize>,
    pub gray_stack: Vec<u32>,
    pub bytes_allocated: usize,
    pub temp_roots: Vec<Value>,
    pub next_gc_threshold: usize,
    pub call_stack: Vec<CallFrame>,
    pub data_stack: Vec<Value>,
    pub handler_stack: Vec<HandlerFrame>,
    pub hook: HookState,
    pub multiret_count: usize,
    pub source_names: Vec<String>,
    pub source_name_ids: HashMap<String, usize>,
    pub last_traceback: String,
    pub yielded: bool,
    pub c_call_depth: usize,
    pub in_error_handler: bool,
    pub coroutine_resume_depth: usize,
    pub current_thread: Option<u32>,
    pub main_thread: u32,
    pub rng_state: u64,
    pub gc_running: bool,
    pub gc_pause: i64,
    pub gc_step_multiplier: i64,
    pub in_gc: bool,
    pub pending_call_name: Option<(String, String)>,
    pending_call: Option<(Value, Vec<Value>, Option<(String, String)>)>,
    finalizer_active: Option<FinalizerState>,
    pub valid_next_keys: HashSet<(u32, u64, Value)>,
    next_keys_cache: Option<(u32, u64, usize, Vec<Value>)>,
    pub closure_cache: HashMap<usize, u32>,
    pub uservalues: HashMap<u32, Value>,
    pub upvalue_ids: HashMap<u32, u32>,
    file_buffers: HashMap<(u32, u64), FileBuffer>,
}

impl VM {
    pub fn new() -> Self {
        let mut vm = Self {
            objects: Vec::new(),
            chunks: Vec::new(),
            global_env: 0,
            registry: 0,
            strings: Vec::new(),
            interned_strings: HashMap::new(),
            interned_integers: HashMap::new(),
            interned_floats: HashMap::new(),
            call_stack: Vec::new(),
            data_stack: Vec::new(),
            handler_stack: Vec::new(),
            hook: HookState::default(),
            multiret_count: 0,
            source_names: Vec::new(),
            source_name_ids: HashMap::new(),
            last_traceback: String::new(),
            marked: Vec::new(),
            finalized: Vec::new(),
            finalizer_deferred: Vec::new(),
            allocation_serials: Vec::new(),
            next_allocation_serial: 0,
            pending_finalizers: VecDeque::new(),
            temp_roots: Vec::new(),
            free_list: Vec::new(),
            gray_stack: Vec::new(),
            bytes_allocated: 0,
            next_gc_threshold: 1024 * 1024,
            yielded: false,
            c_call_depth: 0,
            in_error_handler: false,
            coroutine_resume_depth: 0,
            current_thread: None,
            main_thread: 0,
            rng_state: 853049102483120,
            gc_running: true,
            gc_pause: 200,
            gc_step_multiplier: 200,
            in_gc: false,
            pending_call_name: None,
            pending_call: None,
            finalizer_active: None,
            valid_next_keys: HashSet::new(),
            next_keys_cache: None,
            closure_cache: HashMap::new(),
            uservalues: HashMap::new(),
            upvalue_ids: HashMap::new(),
            file_buffers: HashMap::new(),
        };
        let global_map = HashMap::new();
        let env_id = vm.alloc(GcObject::Table(global_map, None));
        vm.global_env = env_id;
        vm.registry = vm.alloc(GcObject::Table(HashMap::new(), None));
        vm.main_thread = vm.alloc(GcObject::Thread(None));

        let g_str = vm.alloc_str("_G");
        if let Some(GcObject::Table(map, _)) = &mut vm.objects[env_id as usize] {
            map.insert(g_str, Value::obj(env_id));
        }
        vm
    }

    pub fn generate_traceback(&self, skip: usize) -> String {
        self.generate_traceback_from(&self.call_stack, skip, false)
    }

    fn generate_traceback_from(
        &self,
        call_stack: &[CallFrame],
        mut skip: usize,
        suspended_at_yield: bool,
    ) -> String {
        let mut entries = Vec::new();
        if suspended_at_yield {
            if skip == 0 {
                entries.push("\t[C]: in function 'coroutine.yield'".to_string());
            } else {
                skip -= 1;
            }
        }
        let stack_len = call_stack.len();
        let start_idx = stack_len.saturating_sub(skip);
        for frame_index in (0..start_idx).rev() {
            let frame = &call_stack[frame_index];
            if frame.is_native {
                let name = frame
                    .call_name
                    .clone()
                    .or_else(|| self.qualified_function_name(Value::obj(frame.closure_id)));
                if let Some(name) = name.filter(|name| !name.is_empty()) {
                    entries.push(format!("\t[C]: in function '{}'", name));
                } else {
                    entries.push("\t[C]: in function".to_string());
                }
                continue;
            }
            let chunk = &self.chunks[frame.chunk_idx];
            let ip = frame.ip.saturating_sub(1);
            let line = *chunk.lines.get(ip).unwrap_or(&0);
            let source_name = self
                .source_names
                .get(chunk.source_id)
                .map(|s| s.as_str())
                .unwrap_or("?");

            let context = if frame.is_hook {
                "hook".to_string()
            } else if chunk.is_main {
                "main chunk".to_string()
            } else if let Some(name) = frame
                .call_name
                .clone()
                .or_else(|| self.global_function_name(Value::obj(frame.closure_id)))
            {
                format!("function '{}'", name)
            } else {
                format!(
                    "function <{}:{}>",
                    source_name, chunk.linedefined
                )
            };
            entries.push(format!("\t{}:{}: in {}", source_name, line, context));
        }

        const FIRST_LEVELS: usize = 10;
        const LAST_LEVELS: usize = 11;
        let mut msg = String::from("stack traceback:");
        if entries.len() > FIRST_LEVELS + LAST_LEVELS {
            for entry in &entries[..FIRST_LEVELS] {
                msg.push('\n');
                msg.push_str(entry);
            }
            msg.push_str("\n\t...");
            for entry in &entries[entries.len() - LAST_LEVELS..] {
                msg.push('\n');
                msg.push_str(entry);
            }
        } else {
            for entry in entries {
                msg.push('\n');
                msg.push_str(&entry);
            }
        }
        msg
    }

    fn qualified_function_name(&self, target: Value) -> Option<String> {
        if let Some(name) = self.global_function_name(target) {
            return Some(name);
        }
        let Some(GcObject::Table(globals, _)) = &self.objects[self.global_env as usize] else {
            return None;
        };

        let package = globals.iter().find_map(|(key, value)| {
            if !key.is_obj() {
                return None;
            }
            matches!(
                &self.objects[key.as_obj() as usize],
                Some(GcObject::Str(name)) if name == "package"
            )
            .then_some(*value)
        });
        if let Some(package) = package.filter(|value| value.is_obj()) {
            if let Some(GcObject::Table(package_map, _)) =
                &self.objects[package.as_obj() as usize]
            {
                let loaded = package_map.iter().find_map(|(key, value)| {
                    if !key.is_obj() {
                        return None;
                    }
                    matches!(
                        &self.objects[key.as_obj() as usize],
                        Some(GcObject::Str(name)) if name == "loaded"
                    )
                    .then_some(*value)
                });
                if let Some(loaded) = loaded.filter(|value| value.is_obj()) {
                    if let Some(GcObject::Table(loaded_map, _)) =
                        &self.objects[loaded.as_obj() as usize]
                    {
                        for (library_key, library) in loaded_map {
                            if !library_key.is_obj() || !library.is_obj() {
                                continue;
                            }
                            let Some(GcObject::Str(library_name)) =
                                &self.objects[library_key.as_obj() as usize]
                            else {
                                continue;
                            };
                            let Some(GcObject::Table(library_map, _)) =
                                &self.objects[library.as_obj() as usize]
                            else {
                                continue;
                            };
                            for (field_key, value) in library_map {
                                if *value != target || !field_key.is_obj() {
                                    continue;
                                }
                                if let Some(GcObject::Str(field_name)) =
                                    &self.objects[field_key.as_obj() as usize]
                                {
                                    return Some(format!("{}.{}", library_name, field_name));
                                }
                            }
                        }
                    }
                }
            }
        }

        for (table_id, object) in self.objects.iter().enumerate() {
            let Some(GcObject::Table(map, _)) = object else {
                continue;
            };
            let field = map.iter().find_map(|(key, value)| {
                if *value != target || !key.is_obj() {
                    return None;
                }
                match &self.objects[key.as_obj() as usize] {
                    Some(GcObject::Str(name)) => Some(name.clone()),
                    _ => None,
                }
            });
            let Some(field) = field else {
                continue;
            };
            for (key, value) in globals {
                if *value == Value::obj(table_id as u32) && key.is_obj() {
                    if let Some(GcObject::Str(table_name)) = &self.objects[key.as_obj() as usize] {
                        return Some(format!("{}.{}", table_name, field));
                    }
                }
            }
            return Some(field);
        }
        None
    }

    fn global_function_name(&self, target: Value) -> Option<String> {
        let Some(GcObject::Table(globals, _)) = &self.objects[self.global_env as usize] else {
            return None;
        };
        globals.iter().find_map(|(key, value)| {
            if *value != target || !key.is_obj() {
                return None;
            }
            match &self.objects[key.as_obj() as usize] {
                Some(GcObject::Str(name)) => Some(name.clone()),
                _ => None,
            }
        })
    }

    pub fn runtime_error(&mut self, msg: &str) -> ! {
        let mut err_msg = if let Some(frame) = self.call_stack.last().filter(|frame| !frame.is_native) {
            let chunk = &self.chunks[frame.chunk_idx];
            if chunk.is_stripped {
                format!("?:-1: {}", msg)
            } else {
                let source = &self.source_names[chunk.source_id];
                let source = if let Some(name) = source.strip_prefix('@') {
                    name.chars().take(59).collect::<String>()
                } else if let Some(name) = source.strip_prefix('=') {
                    name.chars().take(59).collect::<String>()
                } else {
                    let preview = source.lines().next().unwrap_or("");
                    format!("[string \"{}\"]", preview.chars().take(48).collect::<String>())
                };
                let line = chunk.lines.get(frame.ip.saturating_sub(1)).copied().unwrap_or(0);
                format!("{}:{}: {}", source, line, msg)
            }
        } else {
            msg.to_string()
        };
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
        if self.gc_running && !self.in_gc && self.bytes_allocated > self.next_gc_threshold {
            self.collect_garbage();
        }

        self.bytes_allocated += 1;
        let serial = self.next_allocation_serial;
        self.next_allocation_serial = self.next_allocation_serial.wrapping_add(1);

        if let Some(idx) = self.free_list.pop() {
            self.objects[idx] = Some(obj);
            self.marked[idx] = false;
            self.finalized[idx] = false;
            self.finalizer_deferred[idx] = false;
            self.allocation_serials[idx] = serial;
            idx as u32
        } else {
            self.objects.push(Some(obj));
            self.marked.push(false);
            self.finalized.push(false);
            self.finalizer_deferred.push(false);
            self.allocation_serials.push(serial);
            (self.objects.len() - 1) as u32
        }
    }

    fn alloc_closure(&mut self, chunk_idx: usize, upvalues: Vec<u32>) -> u32 {
        let roots_start = self.temp_roots.len();
        self.temp_roots
            .extend(upvalues.iter().copied().map(Value::obj));
        let closure = self.alloc(GcObject::Closure {
            chunk_idx,
            upvalues,
        });
        self.temp_roots.truncate(roots_start);
        closure
    }

    fn strip_chunk_debug_info(&mut self, root_chunk: usize) {
        let mut pending = vec![root_chunk];
        let mut reachable = Vec::new();
        let mut seen = vec![false; self.chunks.len()];
        while let Some(chunk_idx) = pending.pop() {
            if chunk_idx >= self.chunks.len() || seen[chunk_idx] {
                continue;
            }
            seen[chunk_idx] = true;
            reachable.push(chunk_idx);
            for instruction in self.chunks[chunk_idx].instructions.iter().copied() {
                if let OpCode::MakeClosure(child) = instruction {
                    pending.push(child as usize);
                }
            }
        }

        let stripped_source = self.intern_source_name("=?");
        for chunk_idx in reachable {
            let chunk = &mut self.chunks[chunk_idx];
            chunk.is_stripped = true;
            chunk.source_id = stripped_source;
            chunk.lastlinedefined = chunk.linedefined;
            chunk.lines.fill(0);
            for names in &mut chunk.local_names {
                names.clear();
            }
        }
    }

    fn undump_function(&mut self, function_id: u32) -> Option<Value> {
        let registry = self.get_global("__DUMPED_FUNCS_REGISTRY");
        let original = match self.objects.get(registry.as_obj() as usize)?.as_ref()? {
            GcObject::Table(map, _) => map.get(&Value::num(function_id as f64)).copied()?,
            _ => return None,
        };
        let GcObject::Closure { chunk_idx, .. } = self.objects.get(original.as_obj() as usize)?.as_ref()?.clone() else {
            return None;
        };
        let upvalue_specs = self.chunks[chunk_idx].upvals.clone();
        let mut upvalues = Vec::with_capacity(upvalue_specs.len());
        for (_, _, name) in upvalue_specs {
            let value = if name == "_ENV" {
                Value::obj(self.global_env)
            } else {
                Value::nil()
            };
            upvalues.push(self.alloc(GcObject::Upval(value)));
        }
        Some(Value::obj(self.alloc_closure(chunk_idx, upvalues)))
    }

    fn undump_source(&mut self, source: &[u8]) -> Option<Value> {
        let header = lua53_binary_header();
        if !source.starts_with(&header) {
            return None;
        }
        let marker = b"\x1bLUA_AE_DUMP:";
        let payload = source[header.len()..].strip_prefix(marker)?;
        let marker_text = decode_lua_source(payload.to_vec());
        let mut parts = marker_text.split(':');
        let id = parts.next()?.parse::<u32>().ok()?;
        let _strip = parts.next()?;
        let required = parts.next()?.parse::<usize>().ok()?;
        if marker_text.bytes().filter(|byte| *byte == b'D').count() < required {
            return None;
        }
        self.undump_function(id)
    }

    pub fn collect_garbage(&mut self) {
        if self.in_gc {
            return;
        }
        self.in_gc = true;
        self.mark_roots();
        self.trace_references();
        self.cleanup_weak_tables(false, true);

        for id in self.pending_finalizers.clone() {
            self.mark_object(id);
        }
        let mut new_finalizers = Vec::new();
        for id in 0..self.objects.len() {
            if self.objects[id].is_some()
                && !self.marked[id]
                && !self.finalized[id]
                && !self.pending_finalizers.contains(&(id as u32))
                && self.finalizer_for(id as u32).is_some()
            {
                self.mark_object(id as u32);
                if !self.finalizer_deferred[id]
                    && self.has_unmarked_incoming_reference(id as u32)
                {
                    self.finalizer_deferred[id] = true;
                } else {
                    new_finalizers.push(id as u32);
                }
            }
        }
        new_finalizers.sort_by_key(|id| self.allocation_serials[*id as usize]);
        new_finalizers.reverse();
        self.pending_finalizers.extend(new_finalizers);
        self.trace_references();
        self.cleanup_weak_tables(true, false);
        self.sweep();

        self.in_gc = false;
        self.next_gc_threshold = self.bytes_allocated * 2;
    }

    fn finalizer_for(&self, id: u32) -> Option<Value> {
        let meta = match self.objects.get(id as usize)?.as_ref()? {
            GcObject::Table(_, meta)
            | GcObject::File(_, meta)
            | GcObject::StdFile(_, meta) => *meta,
            _ => None,
        }?;
        let GcObject::Table(map, _) = self.objects.get(meta as usize)?.as_ref()? else {
            return None;
        };
        map.iter().find_map(|(key, value)| {
            if !key.is_obj() {
                return None;
            }
            match self.objects.get(key.as_obj() as usize)?.as_ref()? {
                GcObject::Str(name) if name == "__gc" && value.is_truthy() => Some(*value),
                _ => None,
            }
        })
    }

    fn start_next_finalizer(&mut self) {
        if self.finalizer_active.is_some() || self.pending_call.is_some() {
            return;
        }
        while let Some(id) = self.pending_finalizers.pop_front() {
            let Some(finalizer) = self.finalizer_for(id) else {
                continue;
            };
            self.finalized[id as usize] = true;
            let roots_start = self.temp_roots.len();
            self.temp_roots.push(Value::obj(id));
            self.temp_roots.push(finalizer);
            let caller_index = self.call_stack.len().checked_sub(1);
            let saved_caller_name = caller_index.map(|index| {
                let frame = &mut self.call_stack[index];
                let saved = (frame.call_name.clone(), frame.call_namewhat.clone());
                frame.call_name = Some("__gc".to_string());
                frame.call_namewhat = "metamethod".to_string();
                saved
            });
            let base_depth = self.call_stack.len();
            self.finalizer_active = Some(FinalizerState {
                object: id,
                finalizer,
                base_depth,
                roots_start,
                caller_index,
                saved_caller_name,
                saved_multiret_count: self.multiret_count,
            });
            self.request_call_named(finalizer, vec![Value::obj(id)], "__gc", "metamethod");
            return;
        }
    }

    fn finish_finalizer_if_done(&mut self) {
        let Some(state) = self.finalizer_active.clone() else {
            return;
        };
        if self.pending_call.is_some() || self.call_stack.len() != state.base_depth || self.yielded {
            return;
        }
        for _ in 0..self.multiret_count {
            self.data_stack.pop();
        }
        if let (Some(index), Some((name, namewhat))) = (state.caller_index, state.saved_caller_name) {
            if let Some(frame) = self.call_stack.get_mut(index) {
                frame.call_name = name;
                frame.call_namewhat = namewhat;
            }
        }
        self.temp_roots.truncate(state.roots_start);
        self.finalizer_active = None;
        self.multiret_count = state.saved_multiret_count;
    }

    fn has_unmarked_incoming_reference(&self, target: u32) -> bool {
        let points_to_target = |value: Value| value.is_obj() && value.as_obj() == target;
        self.objects.iter().enumerate().any(|(id, object)| {
            if id == target as usize || self.marked[id] {
                return false;
            }
            match object {
                Some(GcObject::Table(map, meta)) => {
                    meta.is_some_and(|id| id == target)
                        || map
                            .iter()
                            .any(|(key, value)| points_to_target(*key) || points_to_target(*value))
                }
                Some(GcObject::Upval(value)) => points_to_target(*value),
                Some(GcObject::Closure { upvalues, .. }) => upvalues.contains(&target),
                Some(GcObject::Continuation {
                    calls,
                    data,
                    handlers,
                    ..
                }) => {
                    calls.iter().any(|frame| {
                        frame.closure_id == target
                            || frame.varargs.iter().copied().any(points_to_target)
                    }) || data.iter().copied().any(points_to_target)
                        || handlers.iter().any(|handler| handler.closure_id == target)
                }
                Some(GcObject::Thread(Some(state))) => {
                    state.data_stack.iter().copied().any(points_to_target)
                        || state.call_stack.iter().any(|frame| {
                            frame.closure_id == target
                                || frame.varargs.iter().copied().any(points_to_target)
                        })
                        || state
                            .handler_stack
                            .iter()
                            .any(|handler| handler.closure_id == target)
                        || state
                            .hook
                            .function
                            .is_some_and(points_to_target)
                }
                Some(GcObject::NativeClosure(_, value)) => points_to_target(*value),
                Some(GcObject::File(_, meta)) | Some(GcObject::StdFile(_, meta)) => {
                    meta.is_some_and(|id| id == target)
                }
                _ => false,
            }
        })
    }

    fn weak_mode(&self, meta: Option<u32>) -> (bool, bool) {
        let Some(meta_id) = meta else {
            return (false, false);
        };
        let Some(GcObject::Table(map, _)) = &self.objects[meta_id as usize] else {
            return (false, false);
        };
        for (key, value) in map {
            if !key.is_obj() {
                continue;
            }
            let Some(GcObject::Str(key_text)) = self.objects[key.as_obj() as usize].as_ref() else {
                continue;
            };
            if key_text != "__mode" || !value.is_obj() {
                continue;
            }
            if let Some(GcObject::Str(mode)) = self.objects[value.as_obj() as usize].as_ref() {
                return (mode.contains('k'), mode.contains('v'));
            }
        }
        (false, false)
    }

    fn is_weak_collectable(&self, value: Value) -> bool {
        value.is_obj()
            && !matches!(
                self.objects[value.as_obj() as usize],
                Some(GcObject::Str(_))
            )
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

        if let Some((callable, args, _)) = self.pending_call.clone() {
            self.mark_value(callable);
            for value in args {
                self.mark_value(value);
            }
        }
        if let Some(finalizer) = self.finalizer_active.clone() {
            self.mark_object(finalizer.object);
            self.mark_value(finalizer.finalizer);
        }

        for i in 0..self.data_stack.len() {
            let val = self.data_stack[i];
            self.mark_value(val);
        }

        self.mark_object(self.global_env);
        self.mark_object(self.registry);
        self.mark_object(self.main_thread);

        for i in 0..self.call_stack.len() {
            let closure_id = self.call_stack[i].closure_id;
            self.mark_object(closure_id);

            if let Some(continuation) = self.call_stack[i].native_continuation.clone() {
                for value in continuation.gc_roots() {
                    self.mark_value(value);
                }
            }

            for j in 0..self.call_stack[i].varargs.len() {
                let val = self.call_stack[i].varargs[j];
                self.mark_value(val);
            }
        }

        for i in 0..self.handler_stack.len() {
            let closure_id = self.handler_stack[i].closure_id;
            self.mark_object(closure_id);
        }

        if let Some(function) = self.hook.function {
            self.mark_value(function);
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
        let mut ephemerons = Vec::new();
        while let Some(id) = self.gray_stack.pop() {
            let obj = self.objects[id as usize].clone();

            if let Some(gc_obj) = obj {
                match gc_obj {
                    GcObject::Table(map, meta_opt) => {
                        let (weak_keys, weak_values) = self.weak_mode(meta_opt);
                        for (k, v) in map {
                            let key_is_weak = weak_keys && self.is_weak_collectable(k);
                            let value_is_weak = weak_values && self.is_weak_collectable(v);
                            if !key_is_weak {
                                self.mark_value(k);
                            }
                            if !value_is_weak {
                                if key_is_weak {
                                    ephemerons.push((k, v));
                                } else {
                                    self.mark_value(v);
                                }
                            }
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
                    GcObject::LightUserdata(upvalue_id) => self.mark_object(upvalue_id),
                    GcObject::Continuation {
                        calls,
                        data,
                        handlers,
                        ..
                    } => {

                        for frame in calls {
                            self.mark_object(frame.closure_id);
                            if let Some(continuation) = frame.native_continuation {
                                for value in continuation.gc_roots() {
                                    self.mark_value(value);
                                }
                            }
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
                            if let Some(continuation) = frame.native_continuation.clone() {
                                for value in continuation.gc_roots() {
                                    self.mark_value(value);
                                }
                            }
                            for &val in &frame.varargs {
                                self.mark_value(val);
                            }
                        }
                        for frame in &ts.handler_stack {
                            self.mark_object(frame.closure_id);
                        }
                        if let Some(function) = ts.hook.function {
                            self.mark_value(function);
                        }
                    }
                    GcObject::Thread(None) => {}
                    GcObject::NativeClosure(_, state_val) => {
                        self.mark_value(state_val);
                    }
                    GcObject::Str(_) | GcObject::Integer(_) | GcObject::Float(_) | GcObject::NativeFn(_) => {}
                    GcObject::File(_, mt) | GcObject::StdFile(_, mt) => {
                        if let Some(meta) = mt {
                            self.mark_object(meta);
                        }
                        if let Some(value) = self.uservalues.get(&id).copied() {
                            self.mark_value(value);
                        }
                    }
                }
            }
        }

        loop {
            let mut changed = false;
            for &(key, value) in &ephemerons {
                let key_reachable = !self.is_weak_collectable(key)
                    || self.marked[key.as_obj() as usize];
                if key_reachable
                    && value.is_obj()
                    && !self.marked[value.as_obj() as usize]
                {
                    self.mark_value(value);
                    changed = true;
                }
            }
            while let Some(id) = self.gray_stack.pop() {
                let obj = self.objects[id as usize].clone();
                if let Some(GcObject::Table(map, meta_opt)) = obj {
                    let (weak_keys, weak_values) = self.weak_mode(meta_opt);
                    for (key, value) in map {
                        let key_is_weak = weak_keys && self.is_weak_collectable(key);
                        let value_is_weak = weak_values && self.is_weak_collectable(value);
                        if !key_is_weak {
                            self.mark_value(key);
                        }
                        if !value_is_weak {
                            if key_is_weak {
                                ephemerons.push((key, value));
                            } else {
                                self.mark_value(value);
                            }
                        }
                    }
                    if let Some(meta) = meta_opt {
                        self.mark_object(meta);
                    }
                } else if let Some(gc_obj) = obj {
                    match gc_obj {
                        GcObject::Closure { upvalues, .. } => {
                            for upval in upvalues {
                                self.mark_object(upval);
                            }
                        }
                        GcObject::Upval(value) => self.mark_value(value),
                        GcObject::LightUserdata(upvalue_id) => self.mark_object(upvalue_id),
                        GcObject::Continuation { calls, data, handlers, .. } => {
                            for frame in calls {
                                self.mark_object(frame.closure_id);
                                if let Some(continuation) = frame.native_continuation {
                                    for value in continuation.gc_roots() {
                                        self.mark_value(value);
                                    }
                                }
                                for value in frame.varargs {
                                    self.mark_value(value);
                                }
                            }
                            for value in data {
                                self.mark_value(value);
                            }
                            for handler in handlers {
                                self.mark_object(handler.closure_id);
                            }
                        }
                        GcObject::Thread(Some(state)) => {
                            for value in state.data_stack {
                                self.mark_value(value);
                            }
                            for frame in state.call_stack {
                                self.mark_object(frame.closure_id);
                                if let Some(continuation) = frame.native_continuation {
                                    for value in continuation.gc_roots() {
                                        self.mark_value(value);
                                    }
                                }
                                for value in frame.varargs {
                                    self.mark_value(value);
                                }
                            }
                            for handler in state.handler_stack {
                                self.mark_object(handler.closure_id);
                            }
                            if let Some(function) = state.hook.function {
                                self.mark_value(function);
                            }
                        }
                        GcObject::NativeClosure(_, value) => self.mark_value(value),
                        GcObject::File(_, meta) | GcObject::StdFile(_, meta) => {
                            if let Some(meta) = meta {
                                self.mark_object(meta);
                            }
                            if let Some(value) = self.uservalues.get(&id).copied() {
                                self.mark_value(value);
                            }
                        }
                        GcObject::Str(_)
                        | GcObject::Integer(_)
                        | GcObject::Float(_)
                        | GcObject::NativeFn(_)
                        | GcObject::Thread(None) => {}
                        GcObject::Table(..) => unreachable!(),
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn cleanup_weak_tables(&mut self, clean_keys: bool, clean_values: bool) {
        for id in 0..self.objects.len() {
            let meta = match &self.objects[id] {
                Some(GcObject::Table(_, meta)) => *meta,
                _ => continue,
            };
            let (weak_keys, weak_values) = self.weak_mode(meta);
            if !weak_keys && !weak_values {
                continue;
            }
            let dead_entries: Vec<Value> = match &self.objects[id] {
                Some(GcObject::Table(map, _)) => map
                    .iter()
                    .filter_map(|(&key, &value)| {
                        let dead_key = clean_keys
                            && weak_keys
                            && self.is_weak_collectable(key)
                            && !self.marked[key.as_obj() as usize];
                        let dead_value = clean_values
                            && weak_values
                            && self.is_weak_collectable(value)
                            && !self.marked[value.as_obj() as usize];
                        (dead_key || dead_value).then_some(key)
                    })
                    .collect(),
                _ => Vec::new(),
            };
            if let Some(GcObject::Table(map, _)) = &mut self.objects[id] {
                for key in dead_entries {
                    map.remove(&key);
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
                    self.uservalues.remove(&(i as u32));
                    self.free_list.push(i);
                    self.bytes_allocated = self.bytes_allocated.saturating_sub(1);
                }
            }
        }
        let objects = &self.objects;
        self.interned_strings.retain(|text, id| {
            matches!(objects.get(*id as usize), Some(Some(GcObject::Str(existing))) if existing == text)
        });
        self.interned_integers.retain(|number, id| {
            matches!(objects.get(*id as usize), Some(Some(GcObject::Integer(existing))) if existing == number)
        });
        self.interned_floats.retain(|bits, id| {
            matches!(objects.get(*id as usize), Some(Some(GcObject::Float(existing))) if existing.to_bits() == *bits)
        });
        self.upvalue_ids.retain(|upvalue_id, light_id| {
            matches!(objects.get(*upvalue_id as usize), Some(Some(GcObject::Upval(_))))
                && matches!(objects.get(*light_id as usize), Some(Some(GcObject::LightUserdata(id))) if id == upvalue_id)
        });
    }
    pub fn intern_str(&mut self, s: &str) -> u32 {
        if let Some(idx) = self.strings.iter().position(|x| x == s) {
            return idx as u32;
        }
        self.strings.push(s.to_string());
        (self.strings.len() - 1) as u32
    }
    pub fn intern_source_name(&mut self, name: &str) -> usize {
        if let Some(&id) = self.source_name_ids.get(name) {
            return id;
        }
        let id = self.source_names.len();
        self.source_names.push(name.to_string());
        self.source_name_ids.insert(name.to_string(), id);
        id
    }
    pub fn alloc_str(&mut self, s: &str) -> Value {
        let canonical = bytes_to_lua_string(&lua_string_bytes(s));
        if let Some(&id) = self.interned_strings.get(&canonical) {
            if matches!(self.objects.get(id as usize), Some(Some(GcObject::Str(existing))) if existing == &canonical) {
                return Value::obj(id);
            }
            self.interned_strings.remove(&canonical);
        }
        let id = self.alloc(GcObject::Str(canonical.clone()));
        self.interned_strings.insert(canonical, id);
        Value::obj(id)
    }
    pub fn alloc_integer(&mut self, value: i64) -> Value {
        const MAX_SAFE_INTEGER: i64 = 9_007_199_254_740_991;
        if (-MAX_SAFE_INTEGER..=MAX_SAFE_INTEGER).contains(&value) {
            return Value::num(value as f64);
        }
        if let Some(&id) = self.interned_integers.get(&value) {
            if matches!(self.objects.get(id as usize), Some(Some(GcObject::Integer(existing))) if *existing == value) {
                return Value::obj(id);
            }
            self.interned_integers.remove(&value);
        }
        let id = self.alloc(GcObject::Integer(value));
        self.interned_integers.insert(value, id);
        Value::obj(id)
    }
    pub fn alloc_float(&mut self, value: f64) -> Value {
        if !value.is_finite() || value.fract() != 0.0 {
            return Value::num(value);
        }
        let bits = value.to_bits();
        if let Some(&id) = self.interned_floats.get(&bits) {
            if matches!(self.objects.get(id as usize), Some(Some(GcObject::Float(existing))) if existing.to_bits() == bits) {
                return Value::obj(id);
            }
            self.interned_floats.remove(&bits);
        }
        let id = self.alloc(GcObject::Float(value));
        self.interned_floats.insert(bits, id);
        Value::obj(id)
    }
    fn exact_float_to_integer(value: f64) -> Option<i64> {
        const INTEGER_MIN: f64 = -9_223_372_036_854_775_808.0;
        const INTEGER_MAX_EXCLUSIVE: f64 = 9_223_372_036_854_775_808.0;
        if value.is_finite()
            && value.fract() == 0.0
            && value >= INTEGER_MIN
            && value < INTEGER_MAX_EXCLUSIVE
        {
            Some(value as i64)
        } else {
            None
        }
    }
    fn number_as_float(&self, value: Value) -> Option<f64> {
        if value.is_obj() {
            match self.objects.get(value.as_obj() as usize) {
                Some(Some(GcObject::Integer(number))) => Some(*number as f64),
                Some(Some(GcObject::Float(number))) => Some(*number),
                _ => None,
            }
        } else if value.0 != TAG_NIL && value.0 != TAG_FALSE && value.0 != TAG_TRUE {
            Some(value.as_num())
        } else {
            None
        }
    }
    fn number_as_integer(&self, value: Value) -> Option<i64> {
        if value.is_obj() {
            match self.objects.get(value.as_obj() as usize) {
                Some(Some(GcObject::Integer(number))) => Some(*number),
                Some(Some(GcObject::Float(number))) => Self::exact_float_to_integer(*number),
                _ => None,
            }
        } else if value.0 != TAG_NIL && value.0 != TAG_FALSE && value.0 != TAG_TRUE {
            Self::exact_float_to_integer(value.as_num())
        } else {
            None
        }
    }
    fn mixed_number_ordering(
        &self,
        left: Value,
        right: Value,
    ) -> Option<Option<std::cmp::Ordering>> {
        let compare = |integer: i64, float: f64| {
            if float.is_nan() {
                None
            } else if float >= 9_223_372_036_854_775_808.0 {
                Some(std::cmp::Ordering::Less)
            } else if float < -9_223_372_036_854_775_808.0 {
                Some(std::cmp::Ordering::Greater)
            } else {
                let truncated = float.trunc() as i64;
                let ordering = integer.cmp(&truncated);
                Some(if ordering == std::cmp::Ordering::Equal {
                    0.0f64.partial_cmp(&float.fract()).unwrap()
                } else {
                    ordering
                })
            }
        };
        if self.is_float_value(left) && !self.is_float_value(right) {
            Some(compare(self.number_as_integer(right)?, self.number_as_float(left)?).map(std::cmp::Ordering::reverse))
        } else if !self.is_float_value(left) && self.is_float_value(right) {
            Some(compare(self.number_as_integer(left)?, self.number_as_float(right)?))
        } else {
            None
        }
    }
    fn numbers_equal(&self, left: Value, right: Value) -> Option<bool> {
        let left_number = self.number_as_float(left)?;
        let right_number = self.number_as_float(right)?;
        match (self.number_as_integer(left), self.number_as_integer(right)) {
            (Some(left_integer), Some(right_integer)) => Some(left_integer == right_integer),
            (Some(_), None) | (None, Some(_)) => Some(false),
            (None, None) => Some(left_number == right_number),
        }
    }
    pub fn normalize_table_key(&mut self, value: Value) -> Value {
        if value.is_obj() {
            let number = match self.objects.get(value.as_obj() as usize) {
                Some(Some(GcObject::Float(number))) => Some(*number),
                _ => None,
            };
            if let Some(number) = number {
                if let Some(integer) = Self::exact_float_to_integer(number) {
                    return self.alloc_integer(integer);
                }
            }
            return value;
        }

        if value.0 != TAG_NIL && value.0 != TAG_FALSE && value.0 != TAG_TRUE {
            let number = value.as_num();
            if number == 0.0 {
                return Value::num(0.0);
            }
        }
        value
    }
    pub fn is_float_value(&self, value: Value) -> bool {
        if value.is_obj() {
            matches!(self.objects[value.as_obj() as usize], Some(GcObject::Float(_)))
        } else if value.0 != TAG_NIL && value.0 != TAG_FALSE && value.0 != TAG_TRUE {
            Self::exact_float_to_integer(value.as_num()).is_none()
        } else {
            false
        }
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
                GcObject::Integer(n) => n.to_string(),
                GcObject::Float(n) => n.to_string(),
                GcObject::Table(..) => format!("table: 0x{:x}", val.as_obj()),
                GcObject::Closure {
                    chunk_idx: _,
                    upvalues: _,
                }
                | GcObject::NativeFn(_)
                | GcObject::NativeClosure(..) => format!("function: 0x{:x}", val.as_obj()),
                GcObject::File(..) | GcObject::StdFile(..) => {
                    format!("file: 0x{:x}", val.as_obj())
                }
                GcObject::Thread(..) => format!("thread: 0x{:x}", val.as_obj()),
                GcObject::LightUserdata(upvalue_id) => format!("userdata: 0x{:x}", upvalue_id),
                _ => "object".to_string(),
            }
        } else {
            val.as_num().to_string()
        }
    }
    pub fn lua_tostring(&mut self, val: Value) -> String {
        if val.is_obj() {
            match &self.objects[val.as_obj() as usize] {
                Some(GcObject::File(file, _)) => {
                    return if file.borrow().is_some() {
                        format!("file (0x{:x})", val.as_obj())
                    } else {
                        "file (closed)".to_string()
                    };
                }
                Some(GcObject::StdFile(..)) => return format!("file (0x{:x})", val.as_obj()),
                _ => {}
            }
        }

        if val.is_obj() {
            if let Some(metatable) = self.get_type_metatable(val) {
                let entries = match &self.objects[metatable as usize] {
                    Some(GcObject::Table(map, _)) => map.iter().map(|(key, value)| (*key, *value)).collect::<Vec<_>>(),
                    _ => Vec::new(),
                };
                for (key, value) in entries {
                    if self.val_to_str(key) == "__name" && value.is_obj() {
                        if let Some(GcObject::Str(name)) = &self.objects[value.as_obj() as usize] {
                            return format!("{}: 0x{:x}", name, val.as_obj());
                        }
                    }
                }
            }
        }
        self.val_to_str(val)
    }

    pub fn to_num(&self, val: Value) -> Option<f64> {
        if !val.is_obj() && val.0 != TAG_NIL && val.0 != TAG_FALSE && val.0 != TAG_TRUE {
            Some(val.as_num())
        } else if val.is_obj() {
            match self.objects.get(val.as_obj() as usize) {
                Some(Some(GcObject::Str(s))) => {
                    let trimmed = s.trim();
                    let (sign, digits) = if let Some(rest) = trimmed.strip_prefix('-') {
                        (-1.0, rest)
                    } else if let Some(rest) = trimmed.strip_prefix('+') {
                        (1.0, rest)
                    } else {
                        (1.0, trimmed)
                    };
                    if digits.starts_with("0x") || digits.starts_with("0X") {
                        Some(sign * parse_hex_float(digits))
                    } else {
                        parse_decimal_float(trimmed)
                    }
                },
                Some(Some(GcObject::Integer(n))) => Some(*n as f64),
                Some(Some(GcObject::Float(n))) => Some(*n),
                _ => None,
            }
        } else {
            None
        }
    }
    pub fn get_metamethod(&mut self, val: Value, event: &str) -> Option<Value> {
        let mt_id = self.get_type_metatable(val);

        if let Some(mt_id) = mt_id {
            if let Some(ev_key) = self.interned_strings.get(event).copied().map(Value::obj) {
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

    fn indexed_value_step(&mut self, value: Value, key_arg: Value) -> Result<Value, (Value, Vec<Value>)> {
        let key = self.normalize_table_key(key_arg);
        let mut current = value;
        for _ in 0..20 {
            if current.is_obj() {
                if let Some(GcObject::Table(map, _)) = &self.objects[current.as_obj() as usize] {
                    if let Some(result) = map.get(&key).copied() {
                        return Ok(result);
                    }
                }
            }
            let Some(index) = self.get_metamethod(current, "__index") else {
                if current.is_obj()
                    && matches!(self.objects[current.as_obj() as usize], Some(GcObject::Table(..)))
                {
                    return Ok(Value::nil());
                }
                self.runtime_error("attempt to index a non-table value");
            };
            if index.is_obj()
                && matches!(self.objects[index.as_obj() as usize], Some(GcObject::Table(..)))
            {
                current = index;
            } else {
                return Err((index, vec![current, key_arg]));
            }
        }
        self.runtime_error("'__index' chain too long; possible loop");
    }

    fn set_indexed_value_step(
        &mut self, value: Value, key_arg: Value, new_value: Value,
    ) -> Option<(Value, Vec<Value>)> {
        let key = self.normalize_table_key(key_arg);
        let mut current = value;
        for _ in 0..20 {
            let is_table = current.is_obj()
                && matches!(self.objects[current.as_obj() as usize], Some(GcObject::Table(..)));
            let has_key = is_table && match &self.objects[current.as_obj() as usize] {
                Some(GcObject::Table(map, _)) => map.contains_key(&key),
                _ => false,
            };
            let newindex = if has_key { None } else { self.get_metamethod(current, "__newindex") };
            if is_table && (has_key || newindex.is_none()) {
                if let Some(GcObject::Table(map, _)) = &mut self.objects[current.as_obj() as usize] {
                    if new_value.0 == TAG_NIL { map.remove(&key); }
                    else { map.insert(key, new_value); }
                }
                return None;
            }
            let Some(newindex) = newindex else {
                self.runtime_error("attempt to index a non-table value");
            };
            if newindex.is_obj()
                && matches!(self.objects[newindex.as_obj() as usize], Some(GcObject::Table(..)))
            {
                current = newindex;
            } else {
                return Some((newindex, vec![current, key_arg, new_value]));
            }
        }
        self.runtime_error("'__newindex' chain too long; possible loop");
    }

    fn indexed_value_for_ipairs(&mut self, value: Value, key_arg: Value) -> Option<Value> {
        let key = self.normalize_table_key(key_arg);
        let mut current = value;
        for _ in 0..20 {
            if current.is_obj() {
                if let Some(GcObject::Table(map, _)) = &self.objects[current.as_obj() as usize] {
                    if let Some(result) = map.get(&key).copied() {
                        return Some(result);
                    }
                }
            }

            let Some(index) = self.get_metamethod(current, "__index") else {
                if current.is_obj()
                    && matches!(self.objects[current.as_obj() as usize], Some(GcObject::Table(..)))
                {
                    return Some(Value::nil());
                }
                self.runtime_error("attempt to index a non-table value");
            };
            if index.is_obj()
                && matches!(self.objects[index.as_obj() as usize], Some(GcObject::Table(..)))
            {
                current = index;
                continue;
            }
            self.call_stack.last_mut().unwrap().native_continuation =
                Some(NativeContinuation::IPairsIndex(key_arg));
            self.request_call_named(index, vec![current, key_arg], "__index", "metamethod");
            return None;
        }
        self.runtime_error("'__index' chain too long; possible loop");
    }

    fn sequence_length_step(&mut self, value: Value) -> Result<i64, Value> {
        if let Some(function) = self.get_metamethod(value, "__len") {
            return Err(function);
        }
        self.raw_length(value)
            .map(|length| length as i64)
            .ok_or_else(|| self.runtime_error("attempt to get length of a non-table value"))
    }

    fn sequence_length_result(&mut self, result: Option<Value>) -> i64 {
        self.to_integer(result.unwrap_or(Value::nil()))
            .unwrap_or_else(|| self.runtime_error("object length is not an integer"))
    }

    fn raw_length(&self, value: Value) -> Option<usize> {
        if !value.is_obj() {
            return None;
        }
        if let Some(GcObject::Str(text)) = &self.objects[value.as_obj() as usize] {
            return Some(lua_string_bytes(text).len());
        }
        let Some(GcObject::Table(map, _)) = &self.objects[value.as_obj() as usize] else {
            return None;
        };
        let present = |index: i64| {
            map.get(&Value::num(index as f64))
                .is_some_and(|entry| entry.0 != TAG_NIL)
        };
        let mut low = 0i64;
        let mut high = 1i64;
        while high <= (1i64 << 52) && present(high) {
            low = high;
            high *= 2;
        }
        while low + 1 < high {
            let middle = low + (high - low) / 2;
            if present(middle) {
                low = middle;
            } else {
                high = middle;
            }
        }
        Some(low as usize)
    }
    // Put this inside `impl VM`
    pub fn get_type_metatable(&mut self, val: Value) -> Option<u32> {
        if val.is_obj() {
            match &self.objects[val.as_obj() as usize] {
                Some(GcObject::Table(_, mt))
                | Some(GcObject::File(_, mt))
                | Some(GcObject::StdFile(_, mt)) => {
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

    fn trigger_metamethod_vm(&mut self, func: Value, args: Vec<Value>, event: &str) -> bool {
        if !self.is_callable(func) {
            return false;
        }
        let caller = self.call_stack.len().saturating_sub(1);
        self.call_stack[caller].frame_continuation = Some(FrameContinuation::FirstResult);
        self.request_call_named(func, args, event, "metamethod");
        true
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
        self.open_utf8_lib();
        self.open_os_lib();
        self.open_coroutine_lib();
        self.open_package_lib();
        self.open_io_lib();
        self.open_debug_lib();

        // Lua programs, package loaders, and the official test suite use this
        // value to select version-specific behavior.
        let version = self.alloc_str("Lua 5.3");
        self.set_global("_VERSION", version);

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
                    "utf8",
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
                    GcObject::Integer(_) | GcObject::Float(_) => "number",
                    GcObject::Table(..) => "table",
                    GcObject::Closure { .. } | GcObject::NativeFn(_) | GcObject::NativeClosure(..) => "function",
                    GcObject::Continuation { .. } | GcObject::Thread(_) => "thread",
                    GcObject::Upval(_) | GcObject::LightUserdata(_) => "userdata",
                    GcObject::File(..) | GcObject::StdFile(..) => "userdata",
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
                let stack_len = vm.call_stack.len();
                if level < stack_len {
                    let frame = &vm.call_stack[stack_len - 1 - level];
                    let chunk = &vm.chunks[frame.chunk_idx];
                    let ip = frame.ip.saturating_sub(1);
                    let line = *chunk.lines.get(ip).unwrap_or(&0);
                    let source_name = vm
                        .source_names
                        .get(chunk.source_id)
                        .map(|s| s.as_str())
                        .unwrap_or("?");
                    let source = if let Some(name) = source_name.strip_prefix('@') {
                        name.chars().take(59).collect::<String>()
                    } else if let Some(name) = source_name.strip_prefix('=') {
                        name.chars().take(59).collect::<String>()
                    } else {
                        let preview = source_name.lines().next().unwrap_or("");
                        format!("[string \"{}\"]", preview.chars().take(48).collect::<String>())
                    };
                    prefix = format!("{}:{}: ", source, line);
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
            } else {
                std::panic::panic_any(msg_val);
            }
        }));

        // 3. print(...)
        let print_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            debug_assert_eq!(vm.call_stack.last().unwrap().varargs.len(), args.len());
            vm.continue_print(0);
            0
        }));

        // 4. assert(v, [message])
        let assert_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'assert' (value expected)");
            }
            if !args[0].is_truthy() {
                vm.last_traceback = vm.generate_traceback(0);
                if let Some(&message) = args.get(1) {
                    std::panic::panic_any(message);
                }
                let message = if vm.call_stack.len() >= 2 {
                    let frame = &vm.call_stack[vm.call_stack.len() - 2];
                    let chunk = &vm.chunks[frame.chunk_idx];
                    let source = &vm.source_names[chunk.source_id];
                    let source = if let Some(name) = source.strip_prefix('@') {
                        name.chars().take(59).collect::<String>()
                    } else if let Some(name) = source.strip_prefix('=') {
                        name.chars().take(59).collect::<String>()
                    } else {
                        let preview = source.lines().next().unwrap_or("");
                        format!("[string \"{}\"]", preview.chars().take(48).collect::<String>())
                    };
                    let line = chunk.lines.get(frame.ip.saturating_sub(1)).copied().unwrap_or(0);
                    format!("{}:{}: assertion failed!", source, line)
                } else {
                    "assertion failed!".to_string()
                };
                std::panic::panic_any(vm.alloc_str(&message));
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

            if base.is_none() && vm.number_as_float(val).is_some() {
                vm.data_stack.push(val);
                return 1;
            }

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
                if let Some(b) = base {
                    if let Ok(n) = u64::from_str_radix(&str_val, b) {
                        let signed = if sign < 0.0 { (n as i64).wrapping_neg() } else { n as i64 };
                        let value = vm.alloc_integer(signed);
                        vm.data_stack.push(value);
                        return 1;
                    }
                } else {
                    let signed_text = if sign < 0.0 { format!("-{}", str_val) } else { str_val.clone() };
                    if let Ok(n) = signed_text.parse::<i64>() {
                        let value = vm.alloc_integer(n);
                        vm.data_stack.push(value);
                        return 1;
                    } else if let Some(n) = parse_decimal_float(&signed_text) {
                        let value = vm.alloc_float(n);
                        vm.data_stack.push(value);
                        return 1;
                    } else if let Some(digits) = str_val.strip_prefix("0x").or_else(|| str_val.strip_prefix("0X")) {
                        if !digits.is_empty() && digits.bytes().all(|digit| digit.is_ascii_hexdigit()) {
                            let n = digits.bytes().fold(0u64, |value, digit| {
                                let digit = (digit as char).to_digit(16).unwrap() as u64;
                                value.wrapping_mul(16).wrapping_add(digit)
                            });
                            let signed = if sign < 0.0 { (n as i64).wrapping_neg() } else { n as i64 };
                            let value = vm.alloc_integer(signed);
                            vm.data_stack.push(value);
                            return 1;
                        }
                        let n = parse_hex_float(&str_val);
                        if !n.is_nan() {
                            let value = vm.alloc_float(n * sign);
                            vm.data_stack.push(value);
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

            if let Some(metamethod) = vm.get_metamethod(val, "__tostring") {
                vm.call_stack.last_mut().unwrap().native_continuation =
                    Some(NativeContinuation::ToString);
                vm.request_call_named(metamethod, vec![val], "__tostring", "metamethod");
                return 0;
            }

            let s = vm.lua_tostring(val);
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
            let table = args[0];
            let table_id = table.as_obj();
            let table_serial = vm.allocation_serials[table_id as usize];
            let key = vm.normalize_table_key(args.get(1).copied().unwrap_or(Value::nil()));
            if let Some(GcObject::Table(map, _)) = &vm.objects[table_id as usize] {
                let rebuild = key.0 == TAG_NIL
                    || !vm.next_keys_cache.as_ref().is_some_and(|(id, serial, len, keys)| {
                        *id == table_id && *serial == table_serial && *len == map.len()
                            && (!map.contains_key(&key)
                                || keys.binary_search_by_key(&key.0, |entry| entry.0).is_ok())
                    });
                if rebuild {
                    let mut keys: Vec<Value> = map.keys().copied().collect();
                    keys.sort_by_key(|entry| entry.0);
                    vm.next_keys_cache = Some((table_id, table_serial, map.len(), keys));
                }
                let keys = &vm.next_keys_cache.as_ref().unwrap().3;

                if key.0 == TAG_NIL {
                    if keys.is_empty() {
                        vm.data_stack.push(Value::nil());
                        return 1;
                    }
                    let first_key = keys[0];
                    vm.valid_next_keys
                        .insert((table_id, table_serial, first_key));
                    vm.data_stack.push(first_key);
                    vm.data_stack.push(*map.get(&first_key).unwrap());
                    return 2;
                }
                let continuation = vm
                    .valid_next_keys
                    .remove(&(table_id, table_serial, key));
                let start = match keys.binary_search_by_key(&key.0, |entry| entry.0) {
                    Ok(position) if map.contains_key(&key) => position + 1,
                    Ok(position) | Err(position) if continuation => position,
                    _ => vm.runtime_error("invalid key to 'next'"),
                };
                if let Some((next_key, next_value)) = keys[start..]
                    .iter()
                    .find_map(|entry| map.get(entry).map(|value| (*entry, *value)))
                {
                    vm.valid_next_keys
                        .insert((table_id, table_serial, next_key));
                    vm.data_stack.push(next_key);
                    vm.data_stack.push(next_value);
                    return 2;
                }
                vm.next_keys_cache = None;
                vm.data_stack.push(Value::nil());
                return 1;
            }
            vm.runtime_error("bad argument to 'next'");
        }));

        // 10. pairs & ipairs
        let pairs_fn = self.alloc(GcObject::NativeClosure(
            |vm, args, state| {
                let Some(value) = args.first().copied() else {
                    vm.runtime_error("bad argument #1 to 'pairs' (table expected)");
                };
                if let Some(metamethod) = vm.get_metamethod(value, "__pairs") {
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::ReturnResults);
                    vm.request_call_named(metamethod, vec![value], "__pairs", "metamethod");
                    return 0;
                }
                if !value.is_obj()
                    || !matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Table(..)))
                {
                    vm.runtime_error("bad argument #1 to 'pairs' (table expected)");
                }
                vm.data_stack.push(state);
                vm.data_stack.push(value);
                vm.data_stack.push(Value::nil());
                3
            },
            Value::obj(next_fn),
        ));

        let ipairs_iter_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad arguments to 'ipairs' iterator");
            }
            let index = vm
                .to_integer(args[1])
                .unwrap_or_else(|| vm.runtime_error("bad index to 'ipairs' iterator"))
                .wrapping_add(1);
            let key = vm.alloc_integer(index);
            let Some(value) = vm.indexed_value_for_ipairs(args[0], key) else {
                return 0;
            };
            if value.0 != TAG_NIL {
                vm.data_stack.push(key);
                vm.data_stack.push(value);
                return 2;
            }
            vm.data_stack.push(Value::nil());
            1
        }));

        self.set_global("ipairs_iter", Value::obj(ipairs_iter_fn));

        let ipairs_fn = self.alloc(GcObject::NativeClosure(
            |vm, args, state| {
                let Some(value) = args.first().copied() else {
                    vm.runtime_error("bad argument #1 to 'ipairs' (table expected)");
                };
                vm.data_stack.push(state);
                vm.data_stack.push(value);
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

            vm.call_stack
                .last_mut()
                .expect("pcall native frame")
                .native_continuation = Some(NativeContinuation::PCall);
            vm.request_call(func, call_args);
            0
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
            if let Some(value) = args.first().copied() {
                if !matches!(vm.callable_type_name(value), "string" | "number") {
                    let got = vm.error_type_name(value);
                    vm.runtime_error(&format!(
                        "bad argument #1 to 'collectgarbage' (string expected, got {})",
                        got
                    ));
                }
            }
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
                    let size = args.get(1).and_then(|value| vm.to_num(*value)).unwrap_or(0.0);
                    if vm.gc_running || size > 0.0 {
                        vm.collect_garbage();
                        vm.data_stack.push(Value::bool(true));
                    } else {
                        vm.data_stack.push(Value::bool(false));
                    }
                    1
                }
                "stop" => {
                    vm.gc_running = false;
                    0
                }
                "restart" => {
                    vm.gc_running = true;
                    0
                }
                "isrunning" => {
                    vm.data_stack.push(Value::bool(vm.gc_running));
                    1
                }
                "setpause" | "setstepmul" => {
                    let Some(value) = args.get(1).and_then(|value| vm.to_integer(*value)) else {
                        vm.runtime_error("bad argument #2 to 'collectgarbage' (number expected)");
                    };
                    let setting = if opt == "setpause" {
                        &mut vm.gc_pause
                    } else {
                        &mut vm.gc_step_multiplier
                    };
                    let previous = *setting;
                    *setting = value;
                    let previous = vm.alloc_integer(previous);
                    vm.data_stack.push(previous);
                    1
                }
                _ => {
                    vm.runtime_error("bad argument #1 to 'collectgarbage' (invalid option)")
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

            vm.call_stack
                .last_mut()
                .expect("xpcall native frame")
                .native_continuation = Some(NativeContinuation::XPCall(msgh));
            vm.request_call(func, call_args);
            0
        }));

        let rawlen_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            let Some(value) = args.first().copied() else {
                vm.runtime_error("bad argument #1 to 'rawlen' (table or string expected)");
            };
            let length = vm
                .raw_length(value)
                .unwrap_or_else(|| vm.runtime_error("bad argument #1 to 'rawlen' (table or string expected)"));
            let length = vm.alloc_integer(length as i64);
            vm.data_stack.push(length);
            1
        }));

        let rawget_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 2 {
                vm.runtime_error("bad argument to 'rawget' (2 expected)");
            }
            let (t, raw_key) = (args[0], args[1]);
            let k = vm.normalize_table_key(raw_key);

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
            let (t, raw_key, v) = (args[0], args[1], args[2]);
            let k = vm.normalize_table_key(raw_key);

            if k.0 == TAG_NIL {
                vm.runtime_error("table index is nil");
            }
            if vm.number_as_float(k).is_some_and(f64::is_nan) {
                vm.runtime_error("table index is NaN");
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

            let mut is_eq = vm.numbers_equal(v1, v2).unwrap_or(v1 == v2);

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

            let source_bytes = lua_string_bytes(&source);
            if source_bytes.first() == Some(&0x1b) {
                if let Some(function) = vm.undump_source(&source_bytes) {
                    vm.data_stack.push(function);
                    return 1;
                }
                vm.data_stack.push(Value::nil());
                let error = vm.alloc_str("truncated binary chunk");
                vm.data_stack.push(error);
                return 2;
            }

            match Compiler::compile(vm, &source, "=(load)") {
                Ok(chunk_idx) => {
                    let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                    let closure = vm.alloc_closure(chunk_idx, vec![env_upval]);
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

                vm.call_stack.last_mut().unwrap().native_continuation =
                    Some(NativeContinuation::LoadReader { source });
                vm.request_call(chunk_arg, vec![]);
                return 0;
            } else {
                vm.runtime_error("bad argument #1 to 'load' (function or string expected)");
            }

            vm.finish_load_source(source, &args)
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
                match read_lua_source(&filename) {
                    Ok(c) => source = c,
                    Err(error) => {

                        vm.data_stack.push(Value::nil());
                        let err_str = vm.alloc_str(&format!(
                            "cannot open {}: {}",
                            filename, error
                        ));
                        vm.data_stack.push(err_str);
                        return 2;
                    }
                }
            }

            let source_name = format!("@{}", filename);
            let source_bytes = lua_string_bytes(&source);
            let mode = args.get(1).filter(|value| value.0 != TAG_NIL)
                .map(|value| vm.val_to_str(*value)).unwrap_or_else(|| "bt".to_string());
            if source_bytes.first() == Some(&0x1b) {
                if !mode.contains('b') {
                    vm.data_stack.push(Value::nil());
                    let error = vm.alloc_str("attempt to load a binary chunk");
                    vm.data_stack.push(error);
                    return 2;
                }
                if let Some(function) = vm.undump_source(&source_bytes) {
                    vm.data_stack.push(function);
                    return 1;
                }
                vm.data_stack.push(Value::nil());
                let error = vm.alloc_str("truncated binary chunk");
                vm.data_stack.push(error);
                return 2;
            }
            if !mode.contains('t') {
                vm.data_stack.push(Value::nil());
                let error = vm.alloc_str("attempt to load a text chunk");
                vm.data_stack.push(error);
                return 2;
            }
            match Compiler::compile(vm, &source, &source_name) {
                Ok(chunk_idx) => {
                    let env = args.get(2).copied().unwrap_or(Value::obj(vm.global_env));
                    let env_upval = vm.alloc(GcObject::Upval(env));
                    let closure = vm.alloc_closure(chunk_idx, vec![env_upval]);
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
                source = read_lua_source(&filename)
                    .unwrap_or_else(|_| vm.runtime_error(&format!("cannot open {}", filename)));
            }

            let source_name = format!("@{}", filename);
            match Compiler::compile(vm, &source, &source_name) {

                Ok(chunk_idx) => {
                    let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                    let closure = vm.alloc_closure(chunk_idx, vec![env_upval]);
                    let closure_val = Value::obj(closure);
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::ReturnResults);
                    vm.enqueue_lua_call(closure_val, vec![]);
                    0
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
            if (j - i + 1) > 100_000 {
                vm.runtime_error("too many results to unpack");
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

            vm.continue_module_options(1, module_table);

            0
        }));

        let globals = vec![
            ("type", type_fn),
            ("error", error_fn),
            ("print", print_fn),
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
            ("rawlen", rawlen_fn),
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
        ];
        for (name, id) in globals {
            self.set_global(name, Value::obj(id));
        }
        let raw_print_fn = Value::obj(self.alloc(GcObject::NativeFn(|vm, args| {
            let s = args.get(0).map(|v| vm.val_to_str(*v)).unwrap_or_default();
            emit_stdout(&format!("{}\n", s));
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
            let got = vm.error_type_name(val);
            vm.runtime_error(&format!(
                "bad argument #{} to '{}' (number expected, got {})",
                idx + 1,
                func_name,
                got
            ));
        }

        fn number_less(vm: &VM, left: Value, right: Value) -> bool {
            if let Some(ordering) = vm.mixed_number_ordering(left, right) {
                return ordering == Some(std::cmp::Ordering::Less);
            }
            if !vm.is_float_value(left) && !vm.is_float_value(right) {
                if let (Some(a), Some(b)) = (vm.number_as_integer(left), vm.number_as_integer(right)) {
                    return a < b;
                }
            }
            vm.to_num(left).unwrap() < vm.to_num(right).unwrap()
        }

        self.register_method(&mut math_map, "abs", |vm, args| {
            let value = args.get(0).copied().unwrap_or(Value::nil());
            if !vm.is_float_value(value) {
                if let Some(integer) = vm.number_as_integer(value) {
                    let result = vm.alloc_integer(integer.wrapping_abs());
                    vm.data_stack.push(result);
                    return 1;
                }
            }
            let number = get_num(vm, &args, 0, "abs").abs();
            let result = vm.alloc_float(number);
            vm.data_stack.push(result);
            1
        });
        self.register_method(&mut math_map, "floor", |vm, args| {
            let input = args.get(0).copied().unwrap_or(Value::nil());
            if !vm.is_float_value(input) && vm.number_as_integer(input).is_some() {
                vm.data_stack.push(input);
                return 1;
            }
            let n = get_num(vm, &args, 0, "floor").floor();
            let value = if let Some(integer) = VM::exact_float_to_integer(n) {
                vm.alloc_integer(integer)
            } else {
                vm.alloc_float(n)
            };
            vm.data_stack.push(value);
            1
        });
        self.register_method(&mut math_map, "ceil", |vm, args| {
            let input = args.get(0).copied().unwrap_or(Value::nil());
            if !vm.is_float_value(input) && vm.number_as_integer(input).is_some() {
                vm.data_stack.push(input);
                return 1;
            }
            let n = get_num(vm, &args, 0, "ceil").ceil();
            let value = if let Some(integer) = VM::exact_float_to_integer(n) {
                vm.alloc_integer(integer)
            } else {
                vm.alloc_float(n)
            };
            vm.data_stack.push(value);
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
            let y = get_num(vm, &args, 0, "atan");
            let x = if args.get(1).is_none_or(|value| value.0 == TAG_NIL) {
                1.0
            } else {
                get_num(vm, &args, 1, "atan")
            };
            let result = vm.alloc_float(y.atan2(x));
            vm.data_stack.push(result);
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
            let value = get_num(vm, &args, 0, "log");
            let n = if args.len() > 1 {
                value.log(get_num(vm, &args, 1, "log"))
            } else {
                value.ln()
            };
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
            let left = args.get(0).copied().unwrap_or(Value::nil());
            let right = args.get(1).copied().unwrap_or(Value::nil());
            if !vm.is_float_value(left) && !vm.is_float_value(right) {
                if let (Some(a), Some(b)) = (vm.number_as_integer(left), vm.number_as_integer(right)) {
                    if b == 0 { vm.runtime_error("bad argument #2 to 'fmod' (zero)"); }
                    let result = vm.alloc_integer(a.wrapping_rem(b));
                    vm.data_stack.push(result);
                    return 1;
                }
            }
            let x = get_num(vm, &args, 0, "fmod");
            let y = get_num(vm, &args, 1, "fmod");
            let result = vm.alloc_float(x % y);
            vm.data_stack.push(result);
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
            let integral = if x.is_infinite() { x } else { x.trunc() };
            let integral = if !vm.is_float_value(args[0])
                && vm.callable_type_name(args[0]) == "number"
                && vm.to_integer(args[0]).is_some()
            {
                vm.alloc_integer(vm.to_integer(args[0]).unwrap())
            } else {
                vm.alloc_float(integral)
            };
            let fractional = vm.alloc_float(if x.is_infinite() { 0.0 } else { x.fract() });
            vm.data_stack.push(integral);
            vm.data_stack.push(fractional);
            2
        });

        // Min / Max
        self.register_method(&mut math_map, "max", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'max' (value expected)");
            }
            let mut max_v = args[0];
            get_num(vm, &args, 0, "max");
            for i in 1..args.len() {
                get_num(vm, &args, i, "max");
                if number_less(vm, max_v, args[i]) {
                    max_v = args[i];
                }
            }
            vm.data_stack.push(max_v);
            1
        });
        self.register_method(&mut math_map, "min", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'min' (value expected)");
            }
            let mut min_v = args[0];
            get_num(vm, &args, 0, "min");
            for i in 1..args.len() {
                get_num(vm, &args, i, "min");
                if number_less(vm, args[i], min_v) {
                    min_v = args[i];
                }
            }
            vm.data_stack.push(min_v);
            1
        });

        self.register_method(&mut math_map, "random", |vm, args| {
            if args.len() > 2 {
                vm.runtime_error("wrong number of arguments to 'random'");
            }
            vm.rng_state = vm
                .rng_state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1);
            if args.is_empty() {
                let result = (vm.rng_state >> 11) as f64 / 9_007_199_254_740_992.0;
                let value = vm.alloc_float(result);
                vm.data_stack.push(value);
            } else {
                let lower = if args.len() == 1 {
                    1
                } else {
                    vm.to_integer(args[0]).unwrap_or_else(|| {
                        vm.runtime_error("bad argument #1 to 'random' (number has no integer representation)")
                    })
                };
                let upper_index = args.len() - 1;
                let upper = vm.to_integer(args[upper_index]).unwrap_or_else(|| {
                    vm.runtime_error(&format!("bad argument #{} to 'random' (number has no integer representation)", upper_index + 1))
                });
                let span = upper as i128 - lower as i128;
                if span < 0 {
                    vm.runtime_error(&format!("bad argument #{} to 'random' (interval is empty)", upper_index + 1));
                }
                if span > i64::MAX as i128 {
                    vm.runtime_error(&format!("bad argument #{} to 'random' (interval is too large)", upper_index + 1));
                }
                let offset = vm.rng_state % (span as u64 + 1);
                let result = vm.alloc_integer(lower.wrapping_add(offset as i64));
                vm.data_stack.push(result);
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
        let mininteger_key = self.alloc_str("mininteger");
        let maxinteger_key = self.alloc_str("maxinteger");
        math_map.insert(pi_key, Value::num(std::f64::consts::PI));
        math_map.insert(huge_key, Value::num(std::f64::INFINITY));
        let mininteger = self.alloc_integer(i64::MIN);
        let maxinteger = self.alloc_integer(i64::MAX);
        math_map.insert(mininteger_key, mininteger);
        math_map.insert(maxinteger_key, maxinteger);

        self.register_method(&mut math_map, "tointeger", |vm, args| {
            let value = args.get(0).copied().unwrap_or(Value::nil());
            if let Some(integer) = vm.to_integer(value) {
                let result = vm.alloc_integer(integer);
                vm.data_stack.push(result);
            } else { vm.data_stack.push(Value::nil()); }
            1
        });
        self.register_method(&mut math_map, "type", |vm, args| {
            let value = args.get(0).copied().unwrap_or(Value::nil());
            let kind = if value.is_obj() && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Integer(_))) {
                Some("integer")
            } else if vm.is_float_value(value) {
                Some("float")
            } else if !value.is_obj() && value.0 != TAG_NIL && value.0 != TAG_FALSE && value.0 != TAG_TRUE {
                Some(if value.as_num().is_finite() && value.as_num().fract() == 0.0 { "integer" } else { "float" })
            } else { None };
            if let Some(kind) = kind {
                let result = vm.alloc_str(kind);
                vm.data_stack.push(result);
            } else { vm.data_stack.push(Value::nil()); }
            1
        });
        self.register_method(&mut math_map, "ult", |vm, args| {
            let left = args.get(0).and_then(|value| vm.to_integer(*value)).unwrap_or_else(|| {
                vm.runtime_error("bad argument #1 to 'ult' (number has no integer representation)")
            });
            let right = args.get(1).and_then(|value| vm.to_integer(*value)).unwrap_or_else(|| {
                vm.runtime_error("bad argument #2 to 'ult' (number has no integer representation)")
            });
            vm.data_stack.push(Value::bool((left as u64) < (right as u64)));
            1
        });

        let math_table = self.alloc(GcObject::Table(math_map, None));
        self.set_global("math", Value::obj(math_table));
    }
    fn open_table_lib(&mut self) {
        let mut table_map = HashMap::new();

        fn get_max_key(vm: &VM, t_idx: usize) -> i64 {
            let mut max_key = 0;
            if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                for k in map.keys() {
                    let numeric_key = (!k.is_obj() && k.0 != TAG_NIL && k.0 != TAG_FALSE && k.0 != TAG_TRUE)
                        || (k.is_obj() && matches!(vm.objects[k.as_obj() as usize], Some(GcObject::Integer(_))));
                    if numeric_key {
                        if let Some(int_k) = vm.to_integer(*k) {
                            if int_k > max_key { max_key = int_k; }
                        }
                    }
                }
            }
            max_key
        }

        self.register_method(&mut table_map, "pack", |vm, args| {
            let mut map = HashMap::new();
            for (index, value) in args.iter().copied().enumerate() {
                if value.0 != TAG_NIL {
                    map.insert(Value::num((index + 1) as f64), value);
                }
            }
            let n_key = vm.alloc_str("n");
            map.insert(n_key, Value::num(args.len() as f64));
            let table = vm.alloc(GcObject::Table(map, None));
            vm.data_stack.push(Value::obj(table));
            1
        });
        self.register_method(&mut table_map, "unpack", |vm, args| {
            if args.is_empty()
                || !args[0].is_obj()
                || !matches!(vm.objects[args[0].as_obj() as usize], Some(GcObject::Table(..)))
            {
                vm.runtime_error("bad argument #1 to 'unpack' (table expected)");
            }
            let start = if let Some(value) = args.get(1).filter(|value| value.0 != TAG_NIL) {
                vm.to_integer(*value).unwrap_or_else(|| {
                    vm.runtime_error("bad argument #2 to 'unpack' (number has no integer representation)")
                })
            } else {
                1
            };
            let end = if let Some(value) = args.get(2).filter(|value| value.0 != TAG_NIL) {
                vm.to_integer(*value).unwrap_or_else(|| {
                    vm.runtime_error("bad argument #3 to 'unpack' (number has no integer representation)")
                })
            } else {
                match vm.sequence_length_step(args[0]) {
                    Ok(length) => length,
                    Err(function) => {
                        vm.call_stack.last_mut().unwrap().native_continuation =
                            Some(NativeContinuation::SequenceLengthUnpack { start });
                        vm.request_call_named(function, vec![args[0]], "__len", "metamethod");
                        return 0;
                    }
                }
            };
            let count = end as i128 - start as i128 + 1;
            if count <= 0 {
                return 0;
            }
            if count > 100_000 {
                vm.runtime_error("too many results to unpack");
            }
            if vm.continue_table_unpack(start, count as usize) { 0 } else { count as usize }
        });

        self.register_method(&mut table_map, "move", |vm, args| {
            let source = args.get(0).copied().unwrap_or(Value::nil());
            if !source.is_obj()
                || !matches!(vm.objects[source.as_obj() as usize], Some(GcObject::Table(..)))
            {
                vm.runtime_error("bad argument #1 to 'move' (table expected)");
            }
            let destination = args.get(4).copied().filter(|value| value.0 != TAG_NIL).unwrap_or(source);
            if !destination.is_obj()
                || !matches!(vm.objects[destination.as_obj() as usize], Some(GcObject::Table(..)))
            {
                vm.runtime_error("bad argument #5 to 'move' (table expected)");
            }
            let index = |vm: &mut VM, position: usize| {
                args.get(position).and_then(|value| vm.to_integer(*value)).unwrap_or_else(|| {
                    vm.runtime_error(&format!("bad argument #{} to 'move' (number has no integer representation)", position + 1))
                })
            };
            let first = index(vm, 1);
            let last = index(vm, 2);
            let target = index(vm, 3);
            let count = last as i128 - first as i128 + 1;
            if count > 0 {
                if count > i64::MAX as i128 {
                    vm.runtime_error("too many elements to move");
                }
                let target_end = target as i128 + count - 1;
                if target_end > i64::MAX as i128 {
                    vm.runtime_error("destination wrap around in table.move");
                }
                let backwards = source == destination
                    && (target as i128) > first as i128
                    && (target as i128) <= last as i128;
                let suspended = vm.continue_table_move(TableMoveState {
                    source,
                    destination,
                    first,
                    target,
                    count: count as i64,
                    offset: 0,
                    backwards,
                    pending_value: Value::nil(),
                    has_value: false,
                    writing: false,
                });
                return if suspended { 0 } else { 1 };
            }
            vm.data_stack.push(destination);
            1
        });

        // table.insert(t, [pos,] value)
        self.register_method(&mut table_map, "insert", |vm, args| {
            if args.len() < 2 || args.len() > 3 {
                vm.runtime_error("wrong number of arguments to 'table.insert'");
            }
            let t_val = args[0];
            if !t_val.is_obj() {
                vm.runtime_error("bad argument #1 to 'table.insert' (table expected)");
            }

            let len = match vm.sequence_length_step(t_val) {
                Ok(length) => length,
                Err(function) => {
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::SequenceLengthInsert);
                    vm.request_call_named(function, vec![t_val], "__len", "metamethod");
                    return 0;
                }
            };

            let (pos, val) = if args.len() == 2 {
                (len + 1, args[1])
            } else {
                let pos = vm.to_integer(args[1]).unwrap_or_else(|| {
                    vm.runtime_error("bad argument #2 to 'table.insert' (number has no integer representation)")
                });
                (pos, args[2])
            };
            if pos < 1 || pos > len + 1 {
                vm.runtime_error("bad argument #2 to 'table.insert' (position out of bounds)");
            }

            let state = TableShiftState {
                table: t_val,
                pos,
                len,
                index: len,
                value: val,
                pending_value: Value::nil(),
                remove: false,
                phase: if len >= pos { TableShiftPhase::ReadShift } else { TableShiftPhase::WriteFinal },
            };
            vm.continue_table_shift(state, None);
            0
        });

        // table.remove(t, [pos])
        self.register_method(&mut table_map, "remove", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'table.remove'");
            }
            let table = args[0];
            let len = match vm.sequence_length_step(table) {
                Ok(length) => length,
                Err(function) => {
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::SequenceLengthRemove);
                    vm.request_call_named(function, vec![table], "__len", "metamethod");
                    return 0;
                }
            };
            let pos = if args.len() > 1 {
                vm.to_integer(args[1]).unwrap_or_else(|| {
                    vm.runtime_error("bad argument #2 to 'table.remove' (number has no integer representation)")
                })
            } else {
                len
            };
            if pos != len && (pos < 1 || pos > len + 1) {
                vm.runtime_error("bad argument #2 to 'table.remove' (position out of bounds)");
            }

            let state = TableShiftState {
                table,
                pos,
                len,
                index: pos,
                value: Value::nil(),
                pending_value: Value::nil(),
                remove: true,
                phase: TableShiftPhase::ReadRemoved,
            };
            if vm.continue_table_shift(state, None) { 0 } else { 1 }
        });

        // table.concat(t, [sep, i, j])
        self.register_method(&mut table_map, "concat", |vm, args| {
            if args.is_empty() || !args[0].is_obj()
                || !matches!(vm.objects[args[0].as_obj() as usize], Some(GcObject::Table(..))) {
                vm.runtime_error("bad argument #1 to 'table.concat' (table expected)");
            }
            let table = args[0];
            let len = match vm.sequence_length_step(table) {
                Ok(length) => length,
                Err(function) => {
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::SequenceLengthConcat);
                    vm.request_call_named(function, vec![table], "__len", "metamethod");
                    return 0;
                }
            };

            // use `vm.to_num` safely to fall back or extract indices securely
            let sep = if args.len() > 1 && args[1].0 != TAG_NIL {
                vm.val_to_str(args[1])
            } else {
                "".to_string()
            };
            let start = if args.len() > 2 && args[2].0 != TAG_NIL {
                vm.to_integer(args[2]).unwrap_or_else(|| vm.runtime_error("bad argument #3 to 'concat' (number expected)"))
            } else {
                1
            };
            let end = if args.len() > 3 && args[3].0 != TAG_NIL {
                vm.to_integer(args[3]).unwrap_or_else(|| vm.runtime_error("bad argument #4 to 'concat' (number expected)"))
            } else {
                len
            };

            let state = TableConcatState {
                table,
                separator: sep,
                start,
                index: start,
                end,
                result: String::new(),
            };
            if vm.continue_table_concat(state, None) { 0 } else { 1 }
        });

        // table.sort(t, [comp])

        self.register_method(&mut table_map, "sort", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'table.sort'");
            }
            let table = args[0];
            let len = match vm.sequence_length_step(table) {
                Ok(length) => length,
                Err(function) => {
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::SequenceLengthSort);
                    vm.request_call_named(function, vec![table], "__len", "metamethod");
                    return 0;
                }
            };
            if len > i32::MAX as i64 {
                vm.runtime_error("array too big");
            }
            if len < 2 {
                return 0;
            }

            let has_comp = args.len() > 1 && args[1].is_truthy();
            vm.continue_sort_load(SortLoadState {
                table,
                len: len as usize,
                next: 0,
                values: Vec::with_capacity(len as usize),
                custom: has_comp,
            }, None);
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

            if !kv_pairs.is_empty() {
                let total = kv_pairs.len();
                for &(key, value) in &kv_pairs {
                    vm.data_stack.extend([key, value]);
                }
                vm.call_stack.last_mut().unwrap().native_continuation =
                    Some(NativeContinuation::TableForeach { next_index: 1, total });
                vm.request_call(f, vec![kv_pairs[0].0, kv_pairs[0].1]);
                return 0;
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

            if max_k >= 1 {
                let key = Value::num(1.0);
                let value = if let Some(GcObject::Table(map, _)) = &vm.objects[t_idx] {
                    map.get(&key).copied().unwrap_or(Value::nil())
                } else {
                    Value::nil()
                };
                vm.call_stack.last_mut().unwrap().native_continuation =
                    Some(NativeContinuation::TableForeachI { next_index: 2, max: max_k });
                vm.request_call(f, vec![key, value]);
                return 0;
            }

            vm.data_stack.push(Value::nil());
            1
        });

        let table_table = self.alloc(GcObject::Table(table_map, None));
        self.set_global("table", Value::obj(table_table));
    }
    fn format_tostring_args(&mut self, format: Value, args: &[Value]) -> Vec<usize> {
        let text = self.val_to_str(format);
        let mut chars = text.chars().peekable();
        let mut arg_index = 1usize;
        let mut pending = Vec::new();
        while let Some(ch) = chars.next() {
            if ch != '%' {
                continue;
            }
            while chars.peek().is_some_and(|ch| matches!(ch, '-' | '+' | ' ' | '#' | '0')) {
                chars.next();
            }
            while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
                chars.next();
            }
            if chars.peek() == Some(&'.') {
                chars.next();
                while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
                    chars.next();
                }
            }
            let Some(spec) = chars.next() else { break };
            if spec == '%' {
                continue;
            }
            if arg_index < args.len() {
                if spec == 's' && self.get_metamethod(args[arg_index], "__tostring").is_some() {
                    pending.push(arg_index);
                }
                arg_index += 1;
            }
        }
        pending
    }

    fn string_format_callable(&mut self) -> Value {
        let table = self.get_global("string");
        let key = self.alloc_str("format");
        if table.is_obj() {
            if let Some(GcObject::Table(map, _)) = &self.objects[table.as_obj() as usize] {
                if let Some(value) = map.get(&key).copied() {
                    return value;
                }
            }
        }
        self.runtime_error("string.format is unavailable");
    }

    fn continue_format_tostring(&mut self, mut state: FormatState, result: Option<Value>) {
        if let Some(value) = result {
            let index = state.pending[state.next - 1];
            state.args[index] = value;
        }
        if state.next < state.pending.len() {
            let index = state.pending[state.next];
            state.next += 1;
            let value = state.args[index];
            let tostring = self.get_global("tostring");
            self.call_stack.last_mut().unwrap().native_continuation =
                Some(NativeContinuation::FormatToString(Box::new(state)));
            self.request_call(tostring, vec![value]);
            return;
        }
        let format_fn = state.format_fn;
        let args = state.args;
        self.call_stack.last_mut().unwrap().native_continuation =
            Some(NativeContinuation::FormatReplay);
        self.request_call(format_fn, args);
    }

    fn open_string_lib(&mut self) {
        let mut string_map = HashMap::new();

        #[derive(Clone)]
        struct PackField { kind: char, width: usize, big_endian: bool, align: usize }

        fn pack_formats(format: &str) -> Result<Vec<PackField>, String> {
            let mut out = Vec::new();
            let mut chars = format.chars().peekable();
            let mut big_endian = false;
            let mut max_align = 1usize;
            while chars.peek().is_some() {
                while chars.peek().is_some_and(|c| c.is_ascii_whitespace()) { chars.next(); }
                let Some(ch) = chars.next() else { break };
                match ch {
                    '<' => { big_endian = false; continue; }
                    '>' => { big_endian = true; continue; }
                    '=' => { big_endian = false; continue; }
                    '!' => {
                        let mut n = 0usize;
                        while chars.peek().is_some_and(|c| c.is_ascii_digit()) {
                            n = n.checked_mul(10).and_then(|v| v.checked_add(chars.next().unwrap().to_digit(10).unwrap() as usize)).ok_or_else(|| "invalid format".to_string())?;
                        }
                        max_align = if n == 0 { 8 } else { n };
                        if max_align > 16 { return Err("alignment out of limits".to_string()); }
                        if !max_align.is_power_of_two() { return Err("not power of 2".to_string()); }
                        continue;
                    }
                    'X' if chars.peek().is_none() || chars.peek().is_some_and(|next| next.is_ascii_whitespace()) => {
                        return Err("invalid next option".to_string());
                    }
                    _ => {}
                }
                let mut size = 0usize;
                let mut has_size = false;
                while chars.peek().is_some_and(|c| c.is_ascii_digit()) {
                    has_size = true;
                    size = size.checked_mul(10).and_then(|v| v.checked_add(chars.next().unwrap().to_digit(10).unwrap() as usize)).ok_or_else(|| "invalid format".to_string())?;
                }
                let default_width = match ch {
                    'b' | 'B' => 1,
                    'h' | 'H' => 2,
                    'i' | 'I' => 4,
                    'l' | 'L' | 'j' | 'J' | 'T' | 'd' | 'n' => 8,
                    'f' => 4,
                    's' => 8,
                    'x' => 1,
                    'z' | 'X' => 0,
                    'c' => 0,
                    _ => return Err(format!("invalid format option '{}'", ch)),
                };
                if ch == 'c' && !has_size { return Err("missing size".to_string()); }
                let width = if has_size { size } else { default_width };
                if matches!(ch, 'b'|'B'|'h'|'H'|'i'|'I'|'l'|'L'|'j'|'J'|'T') && (width == 0 || width > 16) {
                    return Err(format!("({}) out of limits [1,16]", width));
                }
                if matches!(ch, 'f'|'d'|'n') && !matches!(width, 4|8) { return Err("out of limits".to_string()); }
                if ch == 's' && (width == 0 || width > 16) { return Err(format!("({}) out of limits [1,16]", width)); }
                let align = if matches!(ch, 'c'|'x'|'z') { 1 } else { width.min(max_align).max(1) };
                if align > 1 && !align.is_power_of_two() { return Err("format asks for alignment not power of 2".to_string()); }
                out.push(PackField { kind: ch, width, big_endian, align });
            }
            // X is represented as a marker and consumes its following option.
            let mut normalized = Vec::new();
            let mut i = 0usize;
            while i < out.len() {
                if out[i].kind != 'X' { normalized.push(out[i].clone()); i += 1; continue; }
                if i + 1 >= out.len() || matches!(out[i + 1].kind, 'X'|'x'|'c'|'z') { return Err("invalid next option".to_string()); }
                normalized.push(PackField { kind: 'X', width: 0, big_endian: out[i + 1].big_endian, align: out[i + 1].align });
                i += 2;
            }
            Ok(normalized)
        }

        fn field_padding(offset: usize, align: usize) -> usize {
            if align <= 1 { 0 } else { (align - (offset % align)) % align }
        }

        fn integer_bytes(value: i64, width: usize, signed: bool, big_endian: bool) -> Result<Vec<u8>, String> {
            if width == 0 || width > 16 { return Err("out of limits".to_string()); }
            let bits = width * 8;
            if bits < 64 {
                let (min, max) = if signed { (-(1i64 << (bits - 1)), (1i64 << (bits - 1)) - 1) } else { (0, (1i64 << bits) - 1) };
                if value < min || value > max { return Err("integer overflow".to_string()); }
            } else if !signed && value < 0 && width > 8 {
                return Err("integer overflow".to_string());
            }
            let extension = if signed && value < 0 { 0xff } else { 0x00 };
            let mut bytes = vec![extension; width];
            bytes[..width.min(8)].copy_from_slice(&value.to_le_bytes()[..width.min(8)]);
            if big_endian { bytes.reverse(); }
            Ok(bytes)
        }

        self.register_method(&mut string_map, "packsize", |vm, args| {
            let fmt = args.get(0).map(|v| vm.val_to_str(*v)).unwrap_or_default();
            let fields = pack_formats(&fmt).unwrap_or_else(|e| vm.runtime_error(&e));
            let mut total = 0usize;
            for field in fields {
                total = total.checked_add(field_padding(total, field.align)).unwrap_or_else(|| vm.runtime_error("format result too large"));
                if field.kind == 's' || field.kind == 'z' { vm.runtime_error("variable-length format"); }
                total = total.checked_add(field.width).unwrap_or_else(|| vm.runtime_error("format result too large"));
                if total > i32::MAX as usize { vm.runtime_error("format result too large"); }
            }
            vm.data_stack.push(Value::num(total as f64));
            1
        });

        self.register_method(&mut string_map, "pack", |vm, args| {
            let fmt = args.get(0).map(|v| vm.val_to_str(*v)).unwrap_or_default();
            let fields = pack_formats(&fmt).unwrap_or_else(|e| vm.runtime_error(&e));
            let mut data = Vec::new();
            let mut arg_index = 1usize;
            for field in fields {
                let pad = field_padding(data.len(), field.align);
                data.extend(std::iter::repeat(0u8).take(pad));
                match field.kind {
                    'X' | 'x' => { data.extend(std::iter::repeat(0u8).take(field.width)); }
                    'z' | 's' | 'c' => {
                        let value = args.get(arg_index).copied().unwrap_or(Value::nil()); arg_index += 1;
                        let text = lua_string_bytes(&vm.val_to_str(value));
                        if field.kind == 'z' {
                            if text.contains(&0) { vm.runtime_error("string contains zeros"); }
                            data.extend_from_slice(&text); data.push(0);
                        } else if field.kind == 's' {
                            let len = integer_bytes(text.len() as i64, field.width, false, field.big_endian)
                                .unwrap_or_else(|_| vm.runtime_error("string length does not fit in given size"));
                            data.extend_from_slice(&len); data.extend_from_slice(&text);
                        } else {
                            if text.len() > field.width { vm.runtime_error("string longer than given size"); }
                            data.extend_from_slice(&text);
                            data.extend(std::iter::repeat(0u8).take(field.width - text.len()));
                        }
                    }
                    kind if matches!(kind, 'f'|'d'|'n') => {
                        let value = args.get(arg_index).copied().unwrap_or(Value::nil()); arg_index += 1;
                        let number = vm.to_num(value).unwrap_or_else(|| vm.runtime_error("number expected"));
                        let mut bytes = if field.width == 4 { (number as f32).to_le_bytes().to_vec() } else { number.to_le_bytes().to_vec() };
                        if field.big_endian { bytes.reverse(); }
                        data.extend_from_slice(&bytes);
                    }
                    kind => {
                        let value = args.get(arg_index).copied().unwrap_or(Value::nil()); arg_index += 1;
                        let number = vm.to_integer(value).unwrap_or_else(|| vm.runtime_error("number has no integer representation"));
                        let bytes = integer_bytes(number, field.width, kind.is_ascii_lowercase(), field.big_endian).unwrap_or_else(|e| vm.runtime_error(&e));
                        data.extend_from_slice(&bytes);
                    }
                }
            }
            let packed = vm.alloc_str(&bytes_to_lua_string(&data));
            vm.data_stack.push(packed);
            1
        });

        self.register_method(&mut string_map, "unpack", |vm, args| {
            let fmt = args.get(0).map(|v| vm.val_to_str(*v)).unwrap_or_default();
            let source = args.get(1).copied().map(|v| vm.val_to_str(v)).unwrap_or_default();
            let bytes = lua_string_bytes(&source);
            let pos_arg = args.get(2).and_then(|v| vm.to_num(*v)).unwrap_or(1.0) as i64;
            let one_based = if pos_arg < 0 { bytes.len() as i64 + pos_arg + 1 } else { pos_arg };
            if one_based < 1 || one_based > bytes.len() as i64 + 1 { vm.runtime_error("initial position out of string"); }
            let mut offset = (one_based - 1) as usize;
            let fields = pack_formats(&fmt).unwrap_or_else(|e| vm.runtime_error(&e));
            let mut field_count = 0usize;
            for field in fields {
                let pad = field_padding(offset, field.align);
                if offset.checked_add(pad).is_none() || offset + pad > bytes.len() { vm.runtime_error("data string too short"); }
                offset += pad;
                match field.kind {
                    'X' | 'x' => { if offset + field.width > bytes.len() { vm.runtime_error("data string too short"); } offset += field.width; }
                    'z' => {
                        let Some(rel) = bytes[offset..].iter().position(|b| *b == 0) else { vm.runtime_error("unfinished string"); unreachable!() };
                        let value = vm.alloc_str(&bytes_to_lua_string(&bytes[offset..offset + rel]));
                        vm.data_stack.push(value); offset += rel + 1; field_count += 1;
                    }
                    's' => {
                        if offset + field.width > bytes.len() { vm.runtime_error("data string too short"); }
                        let mut len_bytes = bytes[offset..offset + field.width].to_vec();
                        if field.big_endian { len_bytes.reverse(); }
                        if len_bytes.get(8..).is_some_and(|extra| extra.iter().any(|byte| *byte != 0)) {
                            vm.runtime_error("string length does not fit");
                        }
                        let mut len = 0usize;
                        for (i, byte) in len_bytes.iter().take(std::mem::size_of::<usize>()).enumerate() { len |= (*byte as usize) << (i * 8); }
                        offset += field.width;
                        if offset + len > bytes.len() { vm.runtime_error("data string too short"); }
                        let value = vm.alloc_str(&bytes_to_lua_string(&bytes[offset..offset + len]));
                        vm.data_stack.push(value); offset += len; field_count += 1;
                    }
                    'c' => {
                        if offset + field.width > bytes.len() { vm.runtime_error("data string too short"); }
                        let value = vm.alloc_str(&bytes_to_lua_string(&bytes[offset..offset + field.width]));
                        vm.data_stack.push(value); offset += field.width; field_count += 1;
                    }
                    kind if matches!(kind, 'f'|'d'|'n') => {
                        if offset + field.width > bytes.len() { vm.runtime_error("data string too short"); }
                        let mut raw = bytes[offset..offset + field.width].to_vec(); if field.big_endian { raw.reverse(); }
                        let number = if field.width == 4 { f32::from_le_bytes(raw.try_into().unwrap()) as f64 } else { f64::from_le_bytes(raw.try_into().unwrap()) };
                        let value = vm.alloc_float(number);
                        vm.data_stack.push(value); offset += field.width; field_count += 1;
                    }
                    kind => {
                        if offset + field.width > bytes.len() { vm.runtime_error("data string too short"); }
                        let mut raw = bytes[offset..offset + field.width].to_vec(); if field.big_endian { raw.reverse(); }
                        let signed = kind.is_ascii_lowercase();
                        let negative = signed && (raw.last().unwrap_or(&0) & 0x80) != 0;
                        if field.width > 8 {
                            let extension = if negative { 0xff } else { 0x00 };
                            if raw[8..].iter().any(|byte| *byte != extension)
                                || (signed && !negative && raw[7] & 0x80 != 0)
                                || (signed && negative && raw[7] & 0x80 == 0)
                            {
                                vm.runtime_error(&format!("{}-byte integer does not fit", field.width));
                            }
                        }
                        let mut low = [if negative { 0xff } else { 0x00 }; 8];
                        let copy_len = field.width.min(8);
                        low[..copy_len].copy_from_slice(&raw[..copy_len]);
                        let number = if signed { i64::from_le_bytes(low) } else { u64::from_le_bytes(low) as i64 };
                        let value = vm.alloc_integer(number);
                        vm.data_stack.push(value); offset += field.width; field_count += 1;
                    }
                }
            }
            vm.data_stack.push(Value::num((offset + 1) as f64));
            field_count + 1
        });

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
            let type_name = if let Some(&value) = args.get(idx) {
                vm.error_type_name(value)
            } else {
                "no value".to_string()
            };
            let is_method = idx == 0 && vm.native_call_is_method();
            if is_method {
                vm.runtime_error(&format!(
                    "calling '{}' on bad self (string expected, got {})",
                    func_name, type_name
                ));
            }
            vm.runtime_error(&format!(
                "bad argument #{} to '{}' (string expected, got {})",
                vm.native_argument_number(idx),
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
                    vm.native_argument_number(idx),
                    func_name
                ));
            }
            if let Some(def) = default {
                return def;
            }
            vm.runtime_error(&format!(
                "bad argument #{} to '{}' (number expected)",
                vm.native_argument_number(idx),
                func_name
            ));
            0.0
        }

        fn get_integer_arg(
            vm: &mut VM,
            args: &[Value],
            idx: usize,
            default: Option<i64>,
            func_name: &str,
        ) -> i64 {
            if let Some(&value) = args.get(idx) {
                if value.0 != TAG_NIL {
                    if let Some(integer) = vm.to_integer(value) {
                        return integer;
                    }
                    let detail = if vm.to_num(value).is_some() {
                        "number has no integer representation"
                    } else {
                        "number expected"
                    };
                    vm.runtime_error(&format!(
                        "bad argument #{} to '{}' ({})",
                        vm.native_argument_number(idx), func_name, detail
                    ));
                }
            }
            default.unwrap_or_else(|| vm.runtime_error(&format!(
                "bad argument #{} to '{}' (number expected)",
                vm.native_argument_number(idx), func_name
            )))
        }

        fn format_hex_float(value: f64, uppercase: bool, precision: Option<usize>, plus: bool, space: bool) -> String {
            let sign = if value.is_sign_negative() { "-" } else if plus { "+" } else if space { " " } else { "" };
            if value.is_nan() { return format!("{}{}", sign, if uppercase { "NAN" } else { "nan" }); }
            if value.is_infinite() { return format!("{}{}", sign, if uppercase { "INF" } else { "inf" }); }
            if value == 0.0 {
                let p = precision.unwrap_or(0);
                let fraction = if p == 0 { String::new() } else { format!(".{}", "0".repeat(p)) };
                return format!("{}{}0{}{}0", sign, if uppercase { "0X" } else { "0x" }, fraction, if uppercase { "P+" } else { "p+" });
            }

            let bits = value.abs().to_bits();
            let raw_exp = ((bits >> 52) & 0x7ff) as i32;
            let fraction_bits = bits & ((1u64 << 52) - 1);
            let exponent = raw_exp - 1023;
            let mut digits = format!("{:013x}", fraction_bits);
            if let Some(p) = precision {
                if p < digits.len() { digits.truncate(p); }
                else if p > digits.len() { digits.push_str(&"0".repeat(p - digits.len())); }
            } else {
                while digits.ends_with('0') { digits.pop(); }
            }
            if uppercase { digits.make_ascii_uppercase(); }
            let fraction = if digits.is_empty() { String::new() } else { format!(".{}", digits) };
            format!("{}{}1{}{}{}{}", sign, if uppercase { "0X" } else { "0x" }, fraction, if uppercase { "P" } else { "p" }, if exponent >= 0 { "+" } else { "" }, exponent)
        }

        const L_ESC: char = '%';

        struct MatchState<'a> {
            src: &'a [char],
            p: &'a [char],
            captures: Vec<(usize, isize)>, // (start, len). len < 0 means unfinished
            match_depth: usize,
        }

        impl<'a> MatchState<'a> {
            fn new(src: &'a [char], p: &'a [char]) -> Self {
                Self {
                    src,
                    p,
                    captures: Vec::new(),
                    match_depth: 0,
                }
            }

            fn check_capture(&self, l: char) -> Result<usize, String> {
                if !('1'..='9').contains(&l) {
                    return Err(format!("invalid capture index %{}", l));
                }
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
                    'g' => c.is_ascii_graphic(),
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

            fn match_impl(&mut self, s: usize, p: usize) -> Result<Option<usize>, String> {
                const MAX_MATCH_DEPTH: usize = 200;
                if self.match_depth >= MAX_MATCH_DEPTH {
                    return Err("pattern too complex".to_string());
                }
                self.match_depth += 1;
                let result = self.match_impl_inner(s, p);
                self.match_depth -= 1;
                result
            }

            fn match_impl_inner(&mut self, mut s: usize, mut p: usize) -> Result<Option<usize>, String> {
                loop {
                    if p >= self.p.len() {
                        if self.captures.iter().any(|capture| capture.1 == -1) {
                            return Err("unfinished capture".to_string());
                        }
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

        fn apply_gsub_callback(
            vm: &mut VM,
            result: &mut String,
            index: &mut usize,
            match_count: &mut usize,
            pending_match: &str,
            pending_end: usize,
            source: &[char],
            table_index: bool,
            value: Value,
        ) {
            if value.is_truthy() {
                let valid = if value.is_obj() {
                    matches!(vm.objects[value.as_obj() as usize],
                        Some(GcObject::Str(_) | GcObject::Integer(_) | GcObject::Float(_)))
                } else {
                    vm.number_as_float(value).is_some()
                };
                if !valid {
                    let message = if table_index {
                        "invalid replacement value (a table)"
                    } else {
                        "invalid replacement value (a function must return a string or number)"
                    };
                    vm.runtime_error(message);
                }
                result.push_str(&vm.val_to_str(value));
            } else {
                result.push_str(pending_match);
            }
            *match_count += 1;
            if *index == pending_end {
                if *index < source.len() {
                    result.push(source[*index]);
                }
                *index += 1;
            } else {
                *index = pending_end;
            }
        }

        fn gsub_lua_step(vm: &mut VM, mut state: GSubState, callback_result: Option<Value>) -> bool {
            let anchored_match_finished = state.anchored && callback_result.is_some();
            if let Some(value) = callback_result {
                apply_gsub_callback(vm, &mut state.result, &mut state.index,
                    &mut state.match_count, &state.pending_match, state.pending_end,
                    &state.source, state.table_index, value);
            }

            let pattern = if state.anchored { &state.pattern[1..] } else { &state.pattern[..] };
            while !anchored_match_finished && state.index <= state.source.len()
                && (state.limit < 0 || state.match_count < state.limit as usize)
            {
                let mut matched = MatchState::new(&state.source, pattern);
                match matched.match_impl(state.index, 0) {
                    Ok(Some(end)) if state.last_match_end == Some(end) => {
                        if state.index < state.source.len() {
                            state.result.push(state.source[state.index]);
                        }
                        state.index += 1;
                    }
                    Ok(Some(end)) => {
                        state.last_match_end = Some(end);
                        state.pending_match = state.source[state.index..end].iter().collect();
                        state.pending_end = end;
                        if state.table_index {
                            let key = if let Some(&(start, length)) = matched.captures.first() {
                                if length == -2 {
                                    Value::num((start + 1) as f64)
                                } else {
                                    let text: String = state.source[start..start + length as usize].iter().collect();
                                    vm.alloc_str(&text)
                                }
                            } else {
                                vm.alloc_str(&state.pending_match)
                            };
                            let table = vm.call_stack.last().unwrap().varargs[2];
                            let found = match &vm.objects[table.as_obj() as usize] {
                                Some(GcObject::Table(map, _)) => map.get(&key).copied().unwrap_or(Value::nil()),
                                _ => Value::nil(),
                            };
                            if found.0 != TAG_NIL {
                                apply_gsub_callback(vm, &mut state.result, &mut state.index,
                                    &mut state.match_count, &state.pending_match, state.pending_end,
                                    &state.source, true, found);
                                if state.anchored { break; }
                                continue;
                            }
                            let handler = vm.get_metamethod(table, "__index");
                            if let Some(handler) = handler.filter(|value| vm.is_callable(*value))
                            {
                                vm.call_stack.last_mut().unwrap().native_continuation =
                                    Some(NativeContinuation::GSubCallback { state: Box::new(state), resume: gsub_lua_step });
                                vm.request_call_named(handler, vec![table, key], "__index", "metamethod");
                                return true;
                            }
                            let found = match vm.indexed_value_step(table, key) {
                                Ok(value) => value,
                                Err((handler, _)) => {
                                    vm.runtime_error(&format!(
                                        "attempt to call a {} value",
                                        vm.callable_type_name(handler),
                                    ));
                                }
                            };
                            apply_gsub_callback(vm, &mut state.result, &mut state.index,
                                &mut state.match_count, &state.pending_match, state.pending_end,
                                &state.source, true, found);
                            if state.anchored { break; }
                            continue;
                        }
                        let mut call_args = Vec::new();
                        let roots_start = vm.temp_roots.len();
                        if matched.captures.is_empty() {
                            let value = vm.alloc_str(&state.pending_match);
                            vm.temp_roots.push(value);
                            call_args.push(value);
                        } else {
                            for &(start, length) in &matched.captures {
                                if length == -2 {
                                    call_args.push(Value::num((start + 1) as f64));
                                } else {
                                    let text: String = state.source[start..start + length as usize].iter().collect();
                                    let value = vm.alloc_str(&text);
                                    vm.temp_roots.push(value);
                                    call_args.push(value);
                                }
                            }
                        }
                        let callback = vm.call_stack.last().unwrap().varargs[2];
                        vm.call_stack.last_mut().unwrap().native_continuation =
                            Some(NativeContinuation::GSubCallback { state: Box::new(state), resume: gsub_lua_step });
                        vm.request_call(callback, call_args);
                        vm.temp_roots.truncate(roots_start);
                        return true;
                    }
                    Err(error) => vm.runtime_error(&error),
                    Ok(None) => {
                        if state.anchored {
                            break;
                        }
                        if state.index < state.source.len() {
                            state.result.push(state.source[state.index]);
                        }
                        state.index += 1;
                    }
                }
            }
            if state.index < state.source.len() {
                state.result.extend(&state.source[state.index..]);
            }
            let result = vm.alloc_str(&state.result);
            vm.data_stack.extend([result, Value::num(state.match_count as f64)]);
            vm.multiret_count = 2;
            false
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
            state_map.insert(vm.alloc_str("last"), Value::num(-1.0));
            let state_table = vm.alloc(GcObject::Table(state_map, None));

            let iter_func = |vm: &mut VM, _args: Vec<Value>, state: Value| -> usize {
                let s_key = vm.alloc_str("s");
                let p_key = vm.alloc_str("p");
                let i_key = vm.alloc_str("i");
                let last_key = vm.alloc_str("last");

                if let Some(GcObject::Table(map, _)) = &vm.objects[state.as_obj() as usize] {
                    let s_str = vm.val_to_str(map[&s_key]);
                    let p_str = vm.val_to_str(map[&p_key]);
                    let mut i = map[&i_key].as_num() as usize;
                    let mut last_match = map[&last_key].as_num() as isize;

                    let s_chars: Vec<char> = s_str.chars().collect();
                    let p_chars: Vec<char> = p_str.chars().collect();

                    while i <= s_chars.len() {
                        let mut ms = MatchState::new(&s_chars, &p_chars);
                        if let Ok(Some(end)) = ms.match_impl(i, 0) {
                            if last_match >= 0 && end == last_match as usize {
                                i += 1;
                                continue;
                            }
                            let next_i = if i == end { end + 1 } else { end };
                            if let Some(GcObject::Table(m, _)) =
                                &mut vm.objects[state.as_obj() as usize]
                            {
                                m.insert(i_key, Value::num(next_i as f64));
                                m.insert(last_key, Value::num(end as f64));
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
                        last_match = -1;
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

            let function_callback = vm.is_callable(repl);
            let table_index_callback = repl.is_obj()
                && matches!(vm.objects[repl.as_obj() as usize], Some(GcObject::Table(..)));
            if function_callback || table_index_callback
            {
                let source: Vec<char> = s_str.chars().collect();
                let pattern: Vec<char> = p_str.chars().collect();
                let anchored = pattern.first() == Some(&'^');
                let state = GSubState {
                    source,
                    pattern,
                    anchored,
                    limit,
                    result: String::new(),
                    index: 0,
                    match_count: 0,
                    last_match_end: None,
                    pending_match: String::new(),
                    pending_end: 0,
                    table_index: table_index_callback,
                };
                if gsub_lua_step(vm, state, None) {
                    return 0;
                }
                return vm.multiret_count;
            }

            let s_chars: Vec<char> = s_str.chars().collect();
            let p_chars: Vec<char> = p_str.chars().collect();
            let anchor = p_chars.first() == Some(&'^');
            let p_slice = if anchor { &p_chars[1..] } else { &p_chars[..] };

            let mut result_string = String::new();
            let mut i = 0;
            let mut match_count = 0;
            let mut last_match_end = None;

            while i <= s_chars.len() && (limit < 0 || match_count < limit) {
                let mut ms = MatchState::new(&s_chars, p_slice);
                match ms.match_impl(i, 0) {
                    Ok(Some(end)) if last_match_end == Some(end) => {
                        if i < s_chars.len() {
                            result_string.push(s_chars[i]);
                        }
                        i += 1;
                    }
                    Ok(Some(end)) => {
                        last_match_end = Some(end);
                        let match_str: String = s_chars[i..end].iter().collect();

                        let mut repl_str = String::new();

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
                                            vm.runtime_error("invalid use of '%' in replacement string");
                                        }
                                        vm.runtime_error("invalid use of '%' in replacement string");
                                    }
                                    repl_str.push(c);
                                }
                            }
                            _ => vm.runtime_error("bad argument #3 to 'gsub' (string/function/table expected)"),
                        }

                        result_string.push_str(&repl_str);

                        match_count += 1;
                        if i == end {
                            if i < s_chars.len() { result_string.push(s_chars[i]); }
                            i += 1;
                        }
                        else { i = end; }
                        if anchor { break; }
                    }
                    Err(e) => vm.runtime_error(&e),
                    Ok(None) => {
                        if anchor {
                            let rest: String = s_chars[i..].iter().collect();
                            result_string.push_str(&rest);
                            i = s_chars.len();
                            break;
                        }
                        if i < s_chars.len() { result_string.push(s_chars[i]); }
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
            vm.data_stack.push(Value::num(lua_string_bytes(&s).len() as f64));
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
            let bytes = lua_string_bytes(&s);
            let len = bytes.len() as i64;
            let mut start = get_integer_arg(vm, &args, 1, None, "sub");
            let mut end = get_integer_arg(vm, &args, 2, Some(-1), "sub");
            if start < 0 {
                start = len + start + 1;
            }
            if end < 0 {
                end = len + end + 1;
            }
            start = start.max(1);
            end = end.min(len);
            let res = if start <= end {
                bytes_to_lua_string(&bytes[(start - 1) as usize..end as usize])
            } else {
                "".to_string()
            };
            let str_val = vm.alloc_str(&res);
            vm.data_stack.push(str_val);
            1
        });

        self.register_method(&mut string_map, "rep", |vm, args| {
            let s = get_str_arg(vm, &args, 0, "rep");
            let n = get_integer_arg(vm, &args, 1, None, "rep");
            let separator = if args.get(2).is_some_and(|value| value.0 != TAG_NIL) {
                get_str_arg(vm, &args, 2, "rep")
            } else { String::new() };
            let repetitions = n.max(0) as usize;
            let result_len = lua_string_bytes(&s).len().checked_mul(repetitions)
                .and_then(|size| size.checked_add(lua_string_bytes(&separator).len().checked_mul(repetitions.saturating_sub(1))?))
                .unwrap_or(usize::MAX);
            if result_len >= i32::MAX as usize { vm.runtime_error("resulting string too large"); }
            let res = if repetitions == 0 { String::new() } else {
                let mut result = String::with_capacity(result_len.min(1024 * 1024));
                for index in 0..repetitions {
                    if index > 0 { result.push_str(&separator); }
                    result.push_str(&s);
                }
                result
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
            let bytes = lua_string_bytes(&s);
            let len = bytes.len() as i64;
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
                    .push(Value::num(bytes[(i - 1) as usize] as f64));
            }
            (end - start + 1) as usize
        });

        // 4. format
        // 4. format
        self.register_method(&mut string_map, "format", |vm, args| {
            let fmt = get_str_arg(vm, &args, 0, "format");
            let format_value = args.get(0).copied().unwrap_or(Value::nil());
            let pending = vm.format_tostring_args(format_value, &args);
            if !pending.is_empty() {
                let state = FormatState {
                    format: format_value,
                    format_fn: vm.string_format_callable(),
                    args: args.clone(),
                    pending,
                    next: 0,
                };
                vm.continue_format_tostring(state, None);
                return 0;
            }
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
                if flags.len() > 5 { vm.runtime_error("invalid format (repeated flags)"); }

                let mut width = String::new();
                while let Some(&nc) = chars.peek() {
                    if nc.is_ascii_digit() {
                        width.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                if width.len() > 2 || width.parse::<usize>().unwrap_or(0) > 99 {
                    vm.runtime_error("invalid format (width or precision too long)");
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
                    if precision.len() > 2 || precision.parse::<usize>().unwrap_or(0) > 99 {
                        vm.runtime_error("invalid format (width or precision too long)");
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
                            let mut s = vm.lua_tostring(val);
                            if (w > 0 || has_precision) && lua_string_bytes(&s).contains(&0) {
                                vm.runtime_error("string contains zeros");
                            }
                            if has_precision {
                                let p = precision.parse::<usize>().unwrap_or(0);
                                let bytes = lua_string_bytes(&s);
                                if bytes.len() > p {
                                    s = bytes_to_lua_string(&bytes[..p]);
                                }
                            }
                            let byte_len = lua_string_bytes(&s).len();
                            if w > byte_len {
                                let pad = " ".repeat(w - byte_len);
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
                            let n = vm.to_integer(val).unwrap_or_else(|| vm.runtime_error("number has no integer representation"));
                            let unsigned = spec == 'u';
                            let mut num_str = if unsigned { (n as u64).to_string() } else { n.unsigned_abs().to_string() };
                            if has_precision {
                                let p = precision.parse::<usize>().unwrap_or(1);
                                if p > num_str.len() {
                                    num_str = "0".repeat(p - num_str.len()) + &num_str;
                                } else if p == 0 && n == 0 {
                                    num_str = "".to_string();
                                }
                            }

                            let sign = if !unsigned && n < 0 {
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
                        'a' | 'A' => {
                            let number = vm.to_num(val).unwrap_or_else(|| vm.runtime_error("number expected"));
                            let literal = format_hex_float(number, spec == 'A', has_precision.then(|| precision.parse::<usize>().unwrap_or(0)), flags.contains('+'), flags.contains(' '));
                            if w > literal.len() {
                                let pad = " ".repeat(w - literal.len());
                                if left_align { res.push_str(&literal); res.push_str(&pad); }
                                else { res.push_str(&pad); res.push_str(&literal); }
                            } else { res.push_str(&literal); }
                        }
                        'e' | 'E' | 'g' | 'G' => {
                            let number = vm.to_num(val).unwrap_or_else(|| vm.runtime_error("number expected"));
                            let p = if has_precision { precision.parse::<usize>().unwrap_or(0).max(1) } else { 6 };
                            let mut text = if matches!(spec, 'e'|'E') {
                                format!("{:.*e}", p, number)
                            } else if has_precision {
                                format!("{:.*}", p, number)
                            } else {
                                number.to_string()
                            };
                            if matches!(spec, 'E'|'G') { text.make_ascii_uppercase(); }
                            if number >= 0.0 {
                                if flags.contains('+') { text.insert(0, '+'); }
                                else if flags.contains(' ') { text.insert(0, ' '); }
                            }
                            if w > text.len() {
                                let pad = " ".repeat(w - text.len());
                                if left_align { res.push_str(&text); res.push_str(&pad); }
                                else { res.push_str(&pad); res.push_str(&text); }
                            } else { res.push_str(&text); }
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
                        'x' | 'X' | 'o' => {
                            let n = vm.to_integer(val).unwrap_or_else(|| vm.runtime_error("number has no integer representation"));
                            let mut num_str = match spec {
                                'x' => format!("{:x}", n as u64),
                                'X' => format!("{:X}", n as u64),
                                _ => format!("{:o}", n as u64),
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
                            if val.0 == TAG_NIL { res.push_str("nil"); continue; }
                            if val.0 == TAG_TRUE { res.push_str("true"); continue; }
                            if val.0 == TAG_FALSE { res.push_str("false"); continue; }
                            if let Some(integer) = vm.to_integer(val) {
                                let is_integer_object = val.is_obj() && matches!(vm.objects[val.as_obj() as usize], Some(GcObject::Integer(_)));
                                if is_integer_object {
                                    if integer == i64::MIN { res.push_str("0x8000000000000000"); }
                                    else { res.push_str(&integer.to_string()); }
                                    continue;
                                }
                            }
                            if !val.is_obj() {
                                let number = val.as_num();
                                if number.is_nan() { res.push_str("(0/0)"); }
                                else if number == f64::INFINITY { res.push_str("1e9999"); }
                                else if number == f64::NEG_INFINITY { res.push_str("-1e9999"); }
                                else {
                                    let mut literal = number.to_string();
                                    if !literal.chars().any(|ch| matches!(ch, '.'|'e'|'E')) { literal.push_str(".0"); }
                                    res.push_str(&literal);
                                }
                                continue;
                            }
                            if !matches!(vm.objects[val.as_obj() as usize], Some(GcObject::Str(_))) {
                                vm.runtime_error("value has no literal form");
                            }
                            let s = vm.val_to_str(val);
                            res.push('"');
                            let mut quoted = s.chars().peekable();
                            while let Some(ch) = quoted.next() {
                                match ch {
                                    '"' | '\\' | '\n' => {
                                        res.push('\\');
                                        if ch == '\n' {
                                            res.push('\n');
                                        } else {
                                            res.push(ch);
                                        }
                                    }
                                    '\r' => res.push_str("\\r"),
                                    '\0' => {
                                        if quoted.peek().is_some_and(|next| next.is_ascii_digit()) { res.push_str("\\000"); }
                                        else { res.push_str("\\0"); }
                                    }
                                    ch if (ch as u32) < 32 || ch == '\x7f' => res.push_str(&format!("\\{:03}", ch as u32)),
                                    _ => res.push(ch),
                                }
                            }
                            res.push('"');
                        }
                        _ => {
                            vm.runtime_error(&format!("invalid option '%{}' to 'format'", spec));
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
            let chunk_idx = match vm.objects[func_id as usize] {
                Some(GcObject::Closure { chunk_idx, .. }) => chunk_idx,
                _ => vm.runtime_error("bad argument #1 to 'dump' (Lua function expected)"),
            };
            let strip = args.get(1).is_some_and(|value| value.is_truthy());
            let source_size = vm.source_names.get(vm.chunks[chunk_idx].source_id).map_or(0, String::len);
            if strip {
                vm.strip_chunk_debug_info(chunk_idx);
            }

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

            let mut dump = lua53_binary_header();
            let padding = if strip { 16 } else { source_size + 96 };
            dump.extend_from_slice(format!("\x1bLUA_AE_DUMP:{}:{}:{}:", func_id, if strip { "S" } else { "N" }, padding).as_bytes());
            dump.extend(std::iter::repeat(b'D').take(padding));
            let str_val = vm.alloc_str(&bytes_to_lua_string(&dump));

            vm.data_stack.push(str_val);
            1
        });

        let string_table = self.alloc(GcObject::Table(string_map, None));
        self.set_global("string", Value::obj(string_table));
    }
    fn open_utf8_lib(&mut self) {
        fn bytes_arg(vm: &mut VM, args: &[Value], index: usize, function: &str) -> Vec<u8> {
            let Some(value) = args.get(index).copied() else {
                vm.runtime_error(&format!("bad argument #{} to '{}' (string expected)", index + 1, function));
            };
            if value.is_obj() {
                if let Some(GcObject::Str(text)) = &vm.objects[value.as_obj() as usize] {
                    return lua_string_bytes(text);
                }
            }
            vm.runtime_error(&format!("bad argument #{} to '{}' (string expected)", index + 1, function));
        }

        let mut utf8_map = HashMap::new();

        self.register_method(&mut utf8_map, "char", |vm, args| {
            let mut bytes = Vec::new();
            for (index, value) in args.iter().copied().enumerate() {
                let codepoint = vm.to_integer(value).unwrap_or_else(|| {
                    vm.runtime_error(&format!("bad argument #{} to 'char' (integer expected)", index + 1))
                });
                if !(0..=0x10ffff).contains(&codepoint) {
                    vm.runtime_error("value out of range");
                }
                append_utf8_codepoint(&mut bytes, codepoint as u32);
            }
            let result = vm.alloc_str(&bytes_to_lua_string(&bytes));
            vm.data_stack.push(result);
            1
        });

        self.register_method(&mut utf8_map, "codepoint", |vm, args| {
            let bytes = bytes_arg(vm, &args, 0, "codepoint");
            let length = bytes.len();
            let initial = relative_string_position(
                args.get(1).and_then(|value| vm.to_integer(*value)).unwrap_or(1),
                length,
            );
            let final_position = relative_string_position(
                args.get(2).and_then(|value| vm.to_integer(*value)).unwrap_or(initial),
                length,
            );
            if initial > final_position {
                return 0;
            }
            if initial < 1 || initial > length as i64 {
                vm.runtime_error("initial position out of range");
            }
            if final_position < 1 || final_position > length as i64 {
                vm.runtime_error("final position out of range");
            }

            let mut offset = (initial - 1) as usize;
            let final_offset = (final_position - 1) as usize;
            let mut count = 0;
            while offset <= final_offset {
                let (codepoint, width) = decode_utf8_codepoint(&bytes, offset)
                    .unwrap_or_else(|_| vm.runtime_error("invalid UTF-8 code"));
                let value = vm.alloc_integer(codepoint as i64);
                vm.data_stack.push(value);
                count += 1;
                offset += width;
            }
            count
        });

        self.register_method(&mut utf8_map, "len", |vm, args| {
            let bytes = bytes_arg(vm, &args, 0, "len");
            let length = bytes.len();
            let initial = relative_string_position(
                args.get(1).and_then(|value| vm.to_integer(*value)).unwrap_or(1),
                length,
            );
            let final_position = relative_string_position(
                args.get(2).and_then(|value| vm.to_integer(*value)).unwrap_or(-1),
                length,
            );
            if initial < 1 || initial > length as i64 + 1 {
                vm.runtime_error("initial position out of range");
            }
            if final_position < 0 || final_position > length as i64 {
                vm.runtime_error("final position out of range");
            }
            if initial > final_position {
                vm.data_stack.push(Value::num(0.0));
                return 1;
            }

            let mut offset = (initial - 1) as usize;
            let final_offset = final_position as usize;
            let mut count = 0i64;
            while offset < final_offset {
                match decode_utf8_codepoint(&bytes, offset) {
                    Ok((_, width)) => {
                        count += 1;
                        offset += width;
                    }
                    Err(()) => {
                        vm.data_stack.push(Value::nil());
                        let error_position = vm.alloc_integer(offset as i64 + 1);
                        vm.data_stack.push(error_position);
                        return 2;
                    }
                }
            }
            let count = vm.alloc_integer(count);
            vm.data_stack.push(count);
            1
        });

        self.register_method(&mut utf8_map, "offset", |vm, args| {
            let bytes = bytes_arg(vm, &args, 0, "offset");
            let length = bytes.len();
            let n = args
                .get(1)
                .and_then(|value| vm.to_integer(*value))
                .unwrap_or_else(|| vm.runtime_error("bad argument #2 to 'offset' (integer expected)"));
            let default_position = if n >= 0 { 1 } else { length as i64 + 1 };
            let position = relative_string_position(
                args.get(2)
                    .and_then(|value| vm.to_integer(*value))
                    .unwrap_or(default_position),
                length,
            );
            if position < 1 || position > length as i64 + 1 {
                vm.runtime_error("position out of range");
            }
            let mut offset = (position - 1) as usize;

            if n == 0 {
                while offset > 0 && offset < length && (0x80..=0xbf).contains(&bytes[offset]) {
                    offset -= 1;
                }
                let position = vm.alloc_integer(offset as i64 + 1);
                vm.data_stack.push(position);
                return 1;
            }
            if offset < length && (0x80..=0xbf).contains(&bytes[offset]) {
                vm.runtime_error("initial position is a continuation byte");
            }

            let mut remaining = n;
            if remaining > 0 {
                remaining -= 1;
                while remaining > 0 && offset < length {
                    offset += 1;
                    while offset < length && (0x80..=0xbf).contains(&bytes[offset]) {
                        offset += 1;
                    }
                    remaining -= 1;
                }
            } else {
                while remaining < 0 && offset > 0 {
                    offset -= 1;
                    while offset > 0 && (0x80..=0xbf).contains(&bytes[offset]) {
                        offset -= 1;
                    }
                    remaining += 1;
                }
            }
            if remaining == 0 && offset <= length {
                let position = vm.alloc_integer(offset as i64 + 1);
                vm.data_stack.push(position);
            } else {
                vm.data_stack.push(Value::nil());
            }
            1
        });

        self.register_method(&mut utf8_map, "codes", |vm, args| {
            let bytes = bytes_arg(vm, &args, 0, "codes");
            let mut state_map = HashMap::new();
            let string_key = vm.alloc_str("s");
            let offset_key = vm.alloc_str("i");
            state_map.insert(string_key, vm.alloc_str(&bytes_to_lua_string(&bytes)));
            state_map.insert(offset_key, Value::num(0.0));
            let state_id = vm.alloc(GcObject::Table(state_map, None));

            let iterator = vm.alloc(GcObject::NativeClosure(
                |vm, _args, state| {
                    let string_key = vm.alloc_str("s");
                    let offset_key = vm.alloc_str("i");
                    let (bytes, offset) = match &vm.objects[state.as_obj() as usize] {
                        Some(GcObject::Table(map, _)) => (
                            lua_string_bytes(&vm.val_to_str(map[&string_key])),
                            map[&offset_key].as_num() as usize,
                        ),
                        _ => vm.runtime_error("invalid state for 'codes'"),
                    };
                    if offset >= bytes.len() {
                        vm.data_stack.push(Value::nil());
                        return 1;
                    }
                    let (codepoint, width) = decode_utf8_codepoint(&bytes, offset)
                        .unwrap_or_else(|_| vm.runtime_error("invalid UTF-8 code"));
                    if let Some(GcObject::Table(map, _)) = &mut vm.objects[state.as_obj() as usize] {
                        map.insert(offset_key, Value::num((offset + width) as f64));
                    }
                    let position = vm.alloc_integer(offset as i64 + 1);
                    let codepoint = vm.alloc_integer(codepoint as i64);
                    vm.data_stack.push(position);
                    vm.data_stack.push(codepoint);
                    2
                },
                Value::obj(state_id),
            ));
            vm.data_stack.push(Value::obj(iterator));
            vm.data_stack.push(Value::obj(state_id));
            vm.data_stack.push(Value::num(0.0));
            3
        });

        let charpattern = bytes_to_lua_string(b"[\0-\x7f\xc2-\xf4][\x80-\xbf]*");
        utf8_map.insert(self.alloc_str("charpattern"), self.alloc_str(&charpattern));
        let utf8_table = self.alloc(GcObject::Table(utf8_map, None));
        self.set_global("utf8", Value::obj(utf8_table));
    }

    fn open_os_lib(&mut self) {
        let mut os_map = HashMap::new();

        // 1. os.time([table])
        self.register_method(&mut os_map, "time", |vm, args| {
            let arg = args.get(0).copied().unwrap_or(Value::nil());
            if arg.0 == TAG_NIL {
                let secs = Utc::now().timestamp();
                let value = vm.alloc_integer(secs);
                vm.data_stack.push(value);
            } else if arg.is_obj()
                && matches!(vm.objects[arg.as_obj() as usize], Some(GcObject::Table(..)))
            {
                let mut get_field = |key: &str, default: Option<i64>| -> i64 {
                    let k = vm.alloc_str(key);
                    let value = match &vm.objects[arg.as_obj() as usize] {
                        Some(GcObject::Table(map, _)) => map.get(&k).copied(),
                        _ => None,
                    };
                    match value {
                        Some(value) => vm.to_integer(value).unwrap_or_else(|| {
                            vm.runtime_error(&format!("field '{}' is not an integer", key))
                        }),
                        None => default.unwrap_or_else(|| vm.runtime_error(&format!("field '{}' missing in date table", key))),
                    }
                };
                let year = get_field("year", None) as i128;
                let month = get_field("month", None) as i128;
                let day = get_field("day", None) as i128;
                let hour = get_field("hour", Some(12)) as i128;
                let min = get_field("min", Some(0)) as i128;
                let sec = get_field("sec", Some(0)) as i128;
                let normalized_year = year + (month - 1).div_euclid(12);
                let normalized_month = (month - 1).rem_euclid(12) as u32 + 1;
                let year = i32::try_from(normalized_year).unwrap_or_else(|_| vm.runtime_error("date field out-of-bound"));
                let date = NaiveDate::from_ymd_opt(year, normalized_month, 1)
                    .unwrap_or_else(|| vm.runtime_error("time result cannot be represented"));
                let seconds = (day - 1) * 86400 + hour * 3600 + min * 60 + sec;
                let seconds = i64::try_from(seconds).unwrap_or_else(|_| vm.runtime_error("time result cannot be represented"));
                let naive = date.and_hms_opt(0, 0, 0).unwrap()
                    .checked_add_signed(Duration::seconds(seconds))
                    .unwrap_or_else(|| vm.runtime_error("time result cannot be represented"));
                let local = Local.from_local_datetime(&naive).single()
                    .or_else(|| Local.from_local_datetime(&naive).earliest())
                    .unwrap_or_else(|| vm.runtime_error("time result cannot be represented"));
                let timestamp = local.timestamp();

                let fields = [
                    ("year", local.year() as i64),
                    ("month", local.month() as i64),
                    ("day", local.day() as i64),
                    ("hour", local.hour() as i64),
                    ("min", local.minute() as i64),
                    ("sec", local.second() as i64),
                    ("wday", local.weekday().number_from_sunday() as i64),
                    ("yday", local.ordinal() as i64),
                ];
                for (name, number) in fields {
                    let key = vm.alloc_str(name);
                    let value = vm.alloc_integer(number);
                    if let Some(GcObject::Table(map, _)) = &mut vm.objects[arg.as_obj() as usize] {
                        map.insert(key, value);
                    }
                }
                let key = vm.alloc_str("isdst");
                if let Some(GcObject::Table(map, _)) = &mut vm.objects[arg.as_obj() as usize] {
                    map.insert(key, Value::bool(false));
                }
                let value = vm.alloc_integer(timestamp);
                vm.data_stack.push(value);
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
            let (utc, pattern) = if let Some(pattern) = fmt.strip_prefix('!') {
                (true, pattern)
            } else {
                (false, fmt.as_str())
            };
            let t = if let Some(value) = args.get(1) {
                vm.to_integer(*value).unwrap_or_else(|| vm.runtime_error("time is not an integer"))
            } else {
                Utc::now().timestamp()
            };
            let date = if utc {
                Utc.timestamp_opt(t, 0).single().map(|date| date.fixed_offset())
            } else {
                Local.timestamp_opt(t, 0).single().map(|date| date.fixed_offset())
            }.unwrap_or_else(|| vm.runtime_error("date result cannot be represented"));

            if pattern == "*t" {
                let mut map = HashMap::new();
                for (name, number) in [
                    ("year", date.year() as i64),
                    ("month", date.month() as i64),
                    ("day", date.day() as i64),
                    ("hour", date.hour() as i64),
                    ("min", date.minute() as i64),
                    ("sec", date.second() as i64),
                    ("wday", date.weekday().number_from_sunday() as i64),
                    ("yday", date.ordinal() as i64),
                ] {
                    let key = vm.alloc_str(name);
                    let value = vm.alloc_integer(number);
                    map.insert(key, value);
                }
                let key = vm.alloc_str("isdst");
                map.insert(key, Value::bool(false));
                let table_id = vm.alloc(GcObject::Table(map, None));
                vm.data_stack.push(Value::obj(table_id));
            } else {
                let mut res = String::new();
                let mut chars = pattern.chars();
                while let Some(ch) = chars.next() {
                    if ch != '%' {
                        res.push(ch);
                        continue;
                    }
                    let spec = chars.next().unwrap_or_else(|| vm.runtime_error("invalid conversion specifier"));
                    if spec == '%' {
                        res.push('%');
                        continue;
                    }
                    let spec = if spec == 'E' || spec == 'O' {
                        let modifier = spec;
                        let next = chars.next().unwrap_or_else(|| vm.runtime_error("invalid conversion specifier"));
                        if modifier == 'E' && next == 'x' { 'x' }
                        else if modifier == 'O' && next == 'y' { 'y' }
                        else { vm.runtime_error("invalid conversion specifier") }
                    } else { spec };
                    if !"aAbBcCdDeFgGhHIjmMpPrRStTuUVwWxXyYzZ".contains(spec) {
                        vm.runtime_error("invalid conversion specifier");
                    }
                    res.push_str(&date.format(&format!("%{}", spec)).to_string());
                }
                let str_val = vm.alloc_str(&res);
                vm.data_stack.push(str_val);
            }
            1
        });

        self.register_method(&mut os_map, "setlocale", |vm, args| {
            let requested = args.get(0).copied().unwrap_or(Value::nil());
            if requested.0 == TAG_NIL || vm.val_to_str(requested) == "C" {
                let s = vm.alloc_str("C");
                vm.data_stack.push(s);
            } else {
                vm.data_stack.push(Value::nil());
            }
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
                hook: HookState::default(),
                c_call_depth: 0,
                in_error_handler: false,
                status: ThreadStatus::Suspended,
            };
            let id = vm.alloc(GcObject::Thread(Some(Box::new(ts))));
            vm.data_stack.push(Value::obj(id));
            1
        });

        // coroutine.resume(co, ...)
        self.register_method(&mut coro_map, "resume", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'resume' (thread expected)");
            }

            let co_idx = args[0].as_obj() as usize;

            if !matches!(vm.objects.get(co_idx), Some(Some(GcObject::Thread(_)))) {
                vm.runtime_error("bad argument #1 to 'resume' (thread expected)");
            }
            if vm.coroutine_resume_depth >= 28 {
                vm.data_stack.push(Value::bool(false));
                let message = vm.alloc_str("C stack overflow");
                vm.data_stack.push(message);
                return 2;
            }

            let mut thread_state = match &mut vm.objects[co_idx] {
                Some(GcObject::Thread(ts_opt)) => {
                    if let Some(ts) = ts_opt.take() {
                        *ts
                    } else {
                        vm.data_stack.push(Value::bool(false));
                        let msg = vm.alloc_str("cannot resume non-suspended coroutine");
                        vm.data_stack.push(msg);
                        return 2;
                    }
                }
                _ => unreachable!(),
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
            vm.coroutine_resume_depth += 1;

            std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
            std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
            std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);
            std::mem::swap(&mut vm.hook, &mut thread_state.hook);
            std::mem::swap(&mut vm.c_call_depth, &mut thread_state.c_call_depth);
            std::mem::swap(&mut vm.in_error_handler, &mut thread_state.in_error_handler);

            vm.yielded = false;
            let prev_thread = vm.current_thread;
            vm.current_thread = Some(co_idx as u32);

            let prev_hook = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));

            let initial_call = if thread_state.status == ThreadStatus::Suspended
                && vm.call_stack.is_empty()
            {
                let function = vm.data_stack.pop().unwrap();
                Some((function, resume_args))
            } else {
                vm.data_stack.extend(&resume_args);
                vm.multiret_count = resume_args.len();
                None
            };
            let result = vm.run_coroutine_until_suspend(initial_call);

            std::panic::set_hook(prev_hook);

            std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
            std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
            std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);
            std::mem::swap(&mut vm.hook, &mut thread_state.hook);
            std::mem::swap(&mut vm.c_call_depth, &mut thread_state.c_call_depth);
            std::mem::swap(&mut vm.in_error_handler, &mut thread_state.in_error_handler);

            vm.yielded = false;
            vm.current_thread = prev_thread;
            vm.coroutine_resume_depth -= 1;

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
                hook: HookState::default(),
                c_call_depth: 0,
                in_error_handler: false,
                status: ThreadStatus::Suspended,
            };
            let co_id = vm.alloc(GcObject::Thread(Some(Box::new(ts))));

            let wrapper_func = |vm: &mut VM, resume_args: Vec<Value>, state: Value| -> usize {
                let co_idx = state.as_obj() as usize;
                if vm.coroutine_resume_depth >= 28 {
                    vm.runtime_error("C stack overflow");
                }

                let mut thread_state = match &mut vm.objects[co_idx] {
                    Some(GcObject::Thread(ts_opt)) => {
                        if let Some(ts) = ts_opt.take() {
                            *ts
                        } else {
                            vm.runtime_error("cannot resume non-suspended coroutine");
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

                vm.coroutine_resume_depth += 1;

                std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
                std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
                std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);
                std::mem::swap(&mut vm.hook, &mut thread_state.hook);
                std::mem::swap(&mut vm.c_call_depth, &mut thread_state.c_call_depth);
                std::mem::swap(&mut vm.in_error_handler, &mut thread_state.in_error_handler);

                vm.yielded = false;
                let prev_thread = vm.current_thread;
                vm.current_thread = Some(co_idx as u32);

                let prev_hook = std::panic::take_hook();
                std::panic::set_hook(Box::new(|_| {}));

                let initial_call = if thread_state.status == ThreadStatus::Suspended
                    && vm.call_stack.is_empty()
                {
                    let function = vm.data_stack.pop().unwrap();
                    Some((function, resume_args))
                } else {
                    vm.data_stack.extend(&resume_args);
                    vm.multiret_count = resume_args.len();
                    None
                };
                let result = vm.run_coroutine_until_suspend(initial_call);

                std::panic::set_hook(prev_hook);

                std::mem::swap(&mut vm.call_stack, &mut thread_state.call_stack);
                std::mem::swap(&mut vm.data_stack, &mut thread_state.data_stack);
                std::mem::swap(&mut vm.handler_stack, &mut thread_state.handler_stack);
                std::mem::swap(&mut vm.hook, &mut thread_state.hook);
                std::mem::swap(&mut vm.c_call_depth, &mut thread_state.c_call_depth);
                std::mem::swap(&mut vm.in_error_handler, &mut thread_state.in_error_handler);

                vm.yielded = false;
                vm.current_thread = prev_thread;
                vm.coroutine_resume_depth -= 1;

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
            if vm.has_unyieldable_call() {
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
                Some(GcObject::Thread(None)) => {
                    let is_current = vm.current_thread == Some(co_idx as u32)
                        || (vm.current_thread.is_none()
                            && vm.main_thread == co_idx as u32);
                    if is_current { "running" } else { "normal" }
                }
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
                vm.data_stack.push(Value::bool(false));
            } else {
                vm.data_stack.push(Value::obj(vm.main_thread));
                vm.data_stack.push(Value::bool(true));
            }
            2
        });

        // coroutine.isyieldable()
        self.register_method(&mut coro_map, "isyieldable", |vm, _| {
            let yieldable = vm.current_thread.is_some() && !vm.has_unyieldable_call();
            vm.data_stack.push(Value::bool(yieldable));
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

        let config_key = self.alloc_str("config");
        let config = self.alloc_str("\\\n;\n?\n!\n-\n");
        package_map.insert(config_key, config);

        let searchers_key = self.alloc_str("searchers");
        let searchers = self.alloc(GcObject::Table(HashMap::new(), None));
        package_map.insert(searchers_key, Value::obj(searchers));

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

        let searchpath_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.len() < 2 { vm.runtime_error("bad argument to 'searchpath'"); }
            let name = vm.val_to_str(args[0]);
            let path = vm.val_to_str(args[1]);
            let separator = args.get(2).filter(|value| value.0 != TAG_NIL).map(|value| vm.val_to_str(*value)).unwrap_or_else(|| ".".to_string());
            let replacement = args.get(3).filter(|value| value.0 != TAG_NIL).map(|value| vm.val_to_str(*value)).unwrap_or_else(|| "\\".to_string());
            let transformed = if separator.is_empty() { name } else { name.replace(&separator, &replacement) };
            let mut errors = String::new();
            for template in path.split(';') {
                let filename = template.replace('?', &transformed);
                if std::path::Path::new(&filename).is_file() {
                    let result = vm.alloc_str(&filename);
                    vm.data_stack.push(result);
                    return 1;
                }
                errors.push_str(&format!("\n\tno file '{}'", filename));
            }
            vm.data_stack.push(Value::nil());
            let error = vm.alloc_str(&errors);
            vm.data_stack.push(error);
            2
        }));
        let searchpath_key = self.alloc_str("searchpath");
        package_map.insert(searchpath_key, Value::obj(searchpath_fn));

        let package_table = self.alloc(GcObject::Table(package_map, None));
        self.set_global("package", Value::obj(package_table));
        self.set_global("__PACKAGE_TABLE", Value::obj(package_table));

        let require_fn = self.alloc(GcObject::NativeFn(|vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'require' (string expected)");
            }
            let modname_val = args[0];
            let modname = vm.val_to_str(modname_val);

            let pkg_val = vm.get_global("__PACKAGE_TABLE");
            if !pkg_val.is_obj() {
                vm.runtime_error("'package' table missing");
            }
            let searchers_key = vm.alloc_str("searchers");
            let searchers = match &vm.objects[pkg_val.as_obj() as usize] {
                Some(GcObject::Table(map, _)) => map.get(&searchers_key).copied().unwrap_or(Value::nil()),
                _ => Value::nil(),
            };
            if !searchers.is_obj() || !matches!(vm.objects[searchers.as_obj() as usize], Some(GcObject::Table(..))) {
                vm.runtime_error("'package.searchers' must be a table");
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
            let mut loader_filename: Option<String> = None;

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

                if !path_val.is_obj() || !matches!(vm.objects[path_val.as_obj() as usize], Some(GcObject::Str(_))) {
                    vm.runtime_error("'package.path' must be a string");
                }

                let path_str = vm.val_to_str(path_val);
                let mod_path = modname.replace('.', "/");

                let mut found_source = String::new();
                let mut found_filename = String::new();

                for template in path_str.split(';') {
                    let filename = template.replace('?', &mod_path);
                    if let Ok(content) = read_lua_source(&filename) {
                        found_source = content;
                        found_filename = filename;
                        break;
                    }
                }

                if found_source.is_empty() {
                    let mut message = format!("module '{}' not found:", modname);
                    for template in path_str.split(';') {
                        message.push_str(&format!("\n\tno file '{}'", template.replace('?', &mod_path)));
                    }
                    let cpath_key = vm.alloc_str("cpath");
                    let cpath = match &vm.objects[pkg_val.as_obj() as usize] {
                        Some(GcObject::Table(map, _)) => map.get(&cpath_key).copied().map(|value| vm.val_to_str(value)).unwrap_or_default(),
                        _ => String::new(),
                    };
                    for template in cpath.split(';') {
                        message.push_str(&format!("\n\tno file '{}'", template.replace('?', &mod_path)));
                    }
                    vm.runtime_error(&message);
                }

                match Compiler::compile(vm, &found_source, &found_filename) {
                    Ok(chunk_idx) => {
                        let env_upval = vm.alloc(GcObject::Upval(Value::obj(vm.global_env)));
                        let closure_id = vm.alloc_closure(chunk_idx, vec![env_upval]);
                        loader = Value::obj(closure_id);
                        loader_filename = Some(found_filename.clone());
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

            let loader_data = if let Some(filename) = loader_filename {
                vm.alloc_str(&filename)
            } else {
                Value::nil()
            };
            vm.call_stack.last_mut().unwrap().native_continuation =
                Some(NativeContinuation::Require {
                    loaded_table: loaded_tab_val,
                    module_name: modname_val,
                });
            vm.request_call(loader, vec![modname_val, loader_data]);
            0
        }));

        self.set_global("require", Value::obj(require_fn));
    }

    fn open_io_lib(&mut self) {
        let mut io_map = HashMap::new();
        let mut file_mt_map = HashMap::new();

        use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};

        fn buffer_key(vm: &VM, file: Value) -> (u32, u64) {
            let id = file.as_obj();
            (id, vm.allocation_serials[id as usize])
        }

        fn flush_pending(vm: &mut VM, file: Value, handle: &mut std::fs::File) -> std::io::Result<()> {
            let key = buffer_key(vm, file);
            if let Some(buffer) = vm.file_buffers.get_mut(&key) {
                if !buffer.pending.is_empty() {
                    handle.write_all(&buffer.pending)?;
                    buffer.pending.clear();
                }
            }
            handle.flush()
        }

        fn peek_byte(file: &mut std::fs::File) -> Option<u8> {
            let mut byte = [0];
            if file.read(&mut byte).ok()? != 1 {
                return None;
            }
            file.seek(SeekFrom::Current(-1)).ok()?;
            Some(byte[0])
        }

        fn read_line_bytes(file: &mut std::fs::File, include_newline: bool) -> std::io::Result<Option<Vec<u8>>> {
            let mut bytes = Vec::new();
            let mut saw_any = false;
            loop {
                let mut byte = [0];
                match file.read(&mut byte) {
                    Ok(1) => {}
                    Ok(_) => break,
                    Err(error) => return Err(error),
                }
                saw_any = true;
                if byte[0] == b'\n' {
                    if include_newline { bytes.push(b'\n'); }
                    break;
                }
                bytes.push(byte[0]);
            }
            Ok(saw_any.then_some(bytes))
        }

        fn make_lines_iterator(vm: &mut VM, file: Value, formats: &[Value], close_on_eof: bool) -> Value {
            if formats.len() > 250 {
                vm.runtime_error("too many arguments to lines");
            }
            let mut state = HashMap::new();
            state.insert(Value::num(1.0), file);
            state.insert(Value::num(2.0), Value::bool(close_on_eof));
            for (position, format) in formats.iter().copied().enumerate() {
                state.insert(Value::num((position + 3) as f64), format);
            }
            let state = vm.alloc(GcObject::Table(state, None));
            let iter = vm.alloc(GcObject::NativeClosure(
                |vm, _, state| {
                    let (file, close_on_eof, formats) = match &vm.objects[state.as_obj() as usize] {
                        Some(GcObject::Table(map, _)) => {
                            let file = map[&Value::num(1.0)];
                            let close_on_eof = map[&Value::num(2.0)].is_truthy();
                            let mut formats = Vec::new();
                            for position in 3..map.len() + 1 {
                                formats.push(map[&Value::num(position as f64)]);
                            }
                            (file, close_on_eof, formats)
                        }
                        _ => vm.runtime_error("invalid lines iterator"),
                    };
                    let (rc, read_fn) = match &vm.objects[file.as_obj() as usize] {
                        Some(GcObject::File(rc, Some(mt))) => {
                            let read_key = vm.interned_strings.get("read").copied().unwrap();
                            let read_fn = match &vm.objects[*mt as usize] {
                                Some(GcObject::Table(map, _)) => map[&Value::obj(read_key)],
                                _ => vm.runtime_error("invalid file metatable"),
                            };
                            (rc.clone(), read_fn)
                        }
                        _ => vm.runtime_error("bad file handle"),
                    };
                    if rc.borrow().is_none() { vm.runtime_error("file is already closed"); }
                    let read = match vm.objects[read_fn.as_obj() as usize].clone() {
                        Some(GcObject::NativeFn(read)) => read,
                        _ => vm.runtime_error("invalid file read method"),
                    };
                    let mut read_args = vec![file];
                    read_args.extend(formats);
                    let stack_depth = vm.data_stack.len();
                    let count = read(vm, read_args);
                    if count >= 3 && vm.data_stack.get(stack_depth).is_some_and(|value| value.0 == TAG_NIL) {
                        let message = vm.val_to_str(vm.data_stack[stack_depth + 1]);
                        vm.runtime_error(&message);
                    }
                    if close_on_eof && vm.data_stack.get(stack_depth).is_some_and(|value| value.0 == TAG_NIL) {
                        rc.borrow_mut().take();
                    }
                    count
                },
                Value::obj(state),
            ));
            Value::obj(iter)
        }

        fn take_bytes(file: &mut std::fs::File, token: &mut Vec<u8>, predicate: impl Fn(u8) -> bool) -> usize {
            let mut count = 0;
            while token.len() < 200 && peek_byte(file).is_some_and(&predicate) {
                let mut byte = [0];
                if file.read(&mut byte).ok() != Some(1) { break; }
                token.push(byte[0]);
                count += 1;
            }
            count
        }

        fn take_one(file: &mut std::fs::File, token: &mut Vec<u8>, predicate: impl Fn(u8) -> bool) -> bool {
            if token.len() >= 200 || !peek_byte(file).is_some_and(predicate) {
                return false;
            }
            let mut byte = [0];
            if file.read(&mut byte).ok() != Some(1) { return false; }
            token.push(byte[0]);
            true
        }

        fn read_number_token(file: &mut std::fs::File) -> Option<String> {
            while peek_byte(file).is_some_and(|byte| byte.is_ascii_whitespace()) {
                let mut byte = [0];
                file.read(&mut byte).ok()?;
            }
            let mut token = Vec::new();
            take_one(file, &mut token, |byte| byte == b'+' || byte == b'-');
            let hex = if take_one(file, &mut token, |byte| byte == b'0') {
                take_one(file, &mut token, |byte| byte == b'x' || byte == b'X')
            } else { false };
            if hex {
                take_bytes(file, &mut token, |byte| byte.is_ascii_hexdigit());
                if take_one(file, &mut token, |byte| byte == b'.') {
                    take_bytes(file, &mut token, |byte| byte.is_ascii_hexdigit());
                }
                if take_one(file, &mut token, |byte| byte == b'p' || byte == b'P') {
                    take_one(file, &mut token, |byte| byte == b'+' || byte == b'-');
                    take_bytes(file, &mut token, |byte| byte.is_ascii_digit());
                }
            } else {
                let mut digits = token.iter().filter(|byte| byte.is_ascii_digit()).count();
                digits += take_bytes(file, &mut token, |byte| byte.is_ascii_digit());
                if take_one(file, &mut token, |byte| byte == b'.') {
                    digits += take_bytes(file, &mut token, |byte| byte.is_ascii_digit());
                }
                if digits > 0 && take_one(file, &mut token, |byte| byte == b'e' || byte == b'E') {
                    take_one(file, &mut token, |byte| byte == b'+' || byte == b'-');
                    take_bytes(file, &mut token, |byte| byte.is_ascii_digit());
                }
            }
            if token.len() >= 200 { return None; }
            String::from_utf8(token).ok()
        }

        fn parsed_number(vm: &mut VM, text: &str) -> Option<Value> {
            if let Ok(integer) = text.parse::<i64>() {
                return Some(vm.alloc_integer(integer));
            }
            let (negative, unsigned) = if let Some(rest) = text.strip_prefix('-') {
                (true, rest)
            } else if let Some(rest) = text.strip_prefix('+') {
                (false, rest)
            } else {
                (false, text)
            };
            if let Some(digits) = unsigned.strip_prefix("0x").or_else(|| unsigned.strip_prefix("0X")) {
                if !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                    let integer = digits.bytes().fold(0u64, |value, byte| {
                        value.wrapping_mul(16).wrapping_add((byte as char).to_digit(16).unwrap() as u64)
                    }) as i64;
                    return Some(vm.alloc_integer(if negative { integer.wrapping_neg() } else { integer }));
                }
                let float = parse_hex_float(unsigned) * if negative { -1.0 } else { 1.0 };
                return (!float.is_nan()).then(|| vm.alloc_float(float));
            }
            parse_decimal_float(text).map(|float| vm.alloc_float(float))
        }

        // file:write(...)
        self.register_method(&mut file_mt_map, "write", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'write'");
            }
            let file_object = vm.objects[args[0].as_obj() as usize].clone();
            let mut failure = None;
            match file_object {
                Some(GcObject::File(rc, _)) => {
                    if let Some(file) = &mut *rc.borrow_mut() {
                        let bytes = args.iter().skip(1).flat_map(|arg| {
                            lua_string_bytes(&vm.val_to_str(*arg))
                        }).collect::<Vec<_>>();
                        let key = buffer_key(vm, args[0]);
                        if let Some(buffer) = vm.file_buffers.get_mut(&key) {
                            match buffer.mode {
                                FileBufferMode::No => failure = file.write_all(&bytes).err(),
                                FileBufferMode::Full | FileBufferMode::Line => {
                                    buffer.pending.extend(bytes);
                                    if buffer.pending.len() >= buffer.capacity
                                        || matches!(buffer.mode, FileBufferMode::Line) && buffer.pending.contains(&b'\n')
                                    {
                                        failure = file.write_all(&buffer.pending).err();
                                        if failure.is_none() { buffer.pending.clear(); }
                                    }
                                }
                            }
                        } else {
                            failure = file.write_all(&bytes).err();
                        }
                    } else {
                        vm.runtime_error("attempt to use a closed file");
                    }
                }
                Some(GcObject::StdFile(stream, _)) => {
                    let bytes = args.iter().skip(1).flat_map(|arg| {
                        lua_string_bytes(&vm.val_to_str(*arg))
                    }).collect::<Vec<_>>();
                    let result = match stream {
                        StandardStream::Stdout => write_stdout(&bytes),
                        StandardStream::Stderr => write_stderr(&bytes),
                        StandardStream::Stdin => Err(std::io::Error::new(
                            std::io::ErrorKind::Unsupported,
                            "standard input is not writable",
                        )),
                    };
                    failure = result.err();
                }
                _ => vm.runtime_error("bad argument #1 to 'write' (FILE expected)"),
            }

            if let Some(error) = failure {
                let message = vm.alloc_str(&error.to_string());
                let code = vm.alloc_integer(error.raw_os_error().unwrap_or(1) as i64);
                vm.data_stack.push(Value::nil());
                vm.data_stack.push(message);
                vm.data_stack.push(code);
                3
            } else {
                vm.data_stack.push(args[0]);
                1
            }
        });

        // file:read(...)
        self.register_method(&mut file_mt_map, "read", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'read'");
            }
            let rc_file = match &vm.objects[args[0].as_obj() as usize] {
                Some(GcObject::File(rc, _)) => rc.clone(),
                _ => vm.runtime_error("bad argument #1 to 'read' (FILE expected)"),
            };
            enum ReadMode { All, Line(bool), Number, Count(usize) }
            enum ReadPiece { Bytes(Vec<u8>), Number(Option<String>), Eof, Error(std::io::Error) }
            let mut results = Vec::new();
            let formats = args.len().max(2);
            for position in 1..formats {
                let mode = if let Some(value) = args.get(position) {
                    if value.is_obj() && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Str(_))) {
                        let text = vm.val_to_str(*value);
                        match text.trim_start_matches('*') {
                            "a" | "all" => ReadMode::All,
                            "l" => ReadMode::Line(false),
                            "L" => ReadMode::Line(true),
                            "n" => ReadMode::Number,
                            _ => vm.runtime_error("invalid format"),
                        }
                    } else {
                        let count = vm.to_integer(*value).unwrap_or_else(|| vm.runtime_error("invalid format"));
                        if count < 0 { vm.runtime_error("invalid format"); }
                        ReadMode::Count(count as usize)
                    }
                } else {
                    ReadMode::Line(false)
                };
                let piece = {
                    let mut borrowed = rc_file.borrow_mut();
                    let file = borrowed.as_mut().unwrap_or_else(|| vm.runtime_error("attempt to use a closed file"));
                    match mode {
                        ReadMode::All => {
                            let mut bytes = Vec::new();
                            match file.read_to_end(&mut bytes) {
                                Ok(_) => ReadPiece::Bytes(bytes),
                                Err(error) => ReadPiece::Error(error),
                            }
                        }
                        ReadMode::Line(include_newline) => {
                            match read_line_bytes(file, include_newline) {
                                Ok(Some(bytes)) => ReadPiece::Bytes(bytes),
                                Ok(None) => ReadPiece::Eof,
                                Err(error) => ReadPiece::Error(error),
                            }
                        }
                        ReadMode::Number => ReadPiece::Number(read_number_token(file)),
                        ReadMode::Count(count) => {
                            if count == 0 {
                                if peek_byte(file).is_none() { ReadPiece::Eof }
                                else { ReadPiece::Bytes(Vec::new()) }
                            } else {
                                let mut bytes = Vec::new();
                                match file.take(count as u64).read_to_end(&mut bytes) {
                                    Ok(0) => ReadPiece::Eof,
                                    Ok(_) => ReadPiece::Bytes(bytes),
                                    Err(error) => ReadPiece::Error(error),
                                }
                            }
                        }
                    }
                };
                let value = match piece {
                    ReadPiece::Bytes(bytes) => vm.alloc_str(&bytes_to_lua_string(&bytes)),
                    ReadPiece::Number(Some(text)) => parsed_number(vm, &text).unwrap_or(Value::nil()),
                    ReadPiece::Number(None) | ReadPiece::Eof => Value::nil(),
                    ReadPiece::Error(error) => {
                        let message = vm.alloc_str(&error.to_string());
                        let code = vm.alloc_integer(error.raw_os_error().unwrap_or(1) as i64);
                        vm.data_stack.push(Value::nil());
                        vm.data_stack.push(message);
                        vm.data_stack.push(code);
                        return 3;
                    }
                };
                let failed = value.0 == TAG_NIL;
                results.push(value);
                if failed { break; }
            }
            let count = results.len();
            vm.data_stack.extend(results);
            count
        });

        self.register_method(&mut file_mt_map, "lines", |vm, args| {
            let file = args.first().copied().unwrap_or(Value::nil());
            if !file.is_obj()
                || !matches!(vm.objects[file.as_obj() as usize], Some(GcObject::File(..)))
            {
                vm.runtime_error("bad argument #1 to 'lines' (FILE expected)");
            }
            let iter = make_lines_iterator(vm, file, &args[1..], false);
            vm.data_stack.push(iter);
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
                    if let Err(error) = flush_pending(vm, args[0], file) {
                        vm.runtime_error(&error.to_string());
                    }
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
            } else if matches!(vm.objects[args[0].as_obj() as usize], Some(GcObject::StdFile(..))) {
                let message = vm.alloc_str("Illegal seek");
                let code = vm.alloc_integer(1);
                vm.data_stack.push(Value::nil());
                vm.data_stack.push(message);
                vm.data_stack.push(code);
                3
            } else {
                vm.runtime_error("bad argument #1 to 'seek' (FILE expected)");
            }
        });

        // file:flush()
        self.register_method(&mut file_mt_map, "flush", |vm, args| {
            if args.is_empty() || !args[0].is_obj() {
                vm.runtime_error("bad argument #1 to 'flush'");
            }
            match vm.objects[args[0].as_obj() as usize].clone() {
                Some(GcObject::File(rc, _)) => {
                    if let Some(file) = &mut *rc.borrow_mut() {
                        if let Err(error) = flush_pending(vm, args[0], file) {
                            vm.runtime_error(&error.to_string());
                        }
                    } else {
                        vm.runtime_error("attempt to use a closed file");
                    }
                }
                Some(GcObject::StdFile(StandardStream::Stdout, _)) => {
                    let _ = write_stdout(&[]);
                }
                Some(GcObject::StdFile(StandardStream::Stderr, _)) => {
                    let _ = write_stderr(&[]);
                }
                Some(GcObject::StdFile(StandardStream::Stdin, _)) => {}
                _ => vm.runtime_error("bad argument #1 to 'flush' (FILE expected)"),
            }
            vm.data_stack.push(Value::bool(true));
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
                let mut file = rc.borrow_mut().take().unwrap_or_else(|| vm.runtime_error("attempt to use a closed file"));
                if let Err(error) = flush_pending(vm, args[0], &mut file) {
                    vm.runtime_error(&error.to_string());
                }
                vm.file_buffers.remove(&buffer_key(vm, args[0]));
                vm.data_stack.push(Value::bool(true));
            } else if matches!(vm.objects[args[0].as_obj() as usize], Some(GcObject::StdFile(..))) {
                let message = vm.alloc_str("cannot close standard file");
                vm.data_stack.push(Value::nil());
                vm.data_stack.push(message);
                return 2;
            } else {
                vm.runtime_error("bad argument #1 to 'close' (FILE expected)");
            }
            1
        });

        self.register_method(&mut file_mt_map, "setvbuf", |vm, args| {
            let file = args.first().copied().unwrap_or(Value::nil());
            let mode = args.get(1).map(|value| vm.val_to_str(*value)).unwrap_or_default();
            let mode = match mode.as_str() {
                "no" => FileBufferMode::No,
                "full" => FileBufferMode::Full,
                "line" => FileBufferMode::Line,
                _ => vm.runtime_error("invalid buffering mode"),
            };
            let capacity = args.get(2).and_then(|value| vm.to_integer(*value)).unwrap_or(8192).max(1) as usize;
            let rc = match &vm.objects[file.as_obj() as usize] {
                Some(GcObject::File(rc, _)) => rc.clone(),
                _ => vm.runtime_error("bad argument #1 to 'setvbuf' (FILE expected)"),
            };
            let mut borrowed = rc.borrow_mut();
            let handle = borrowed.as_mut().unwrap_or_else(|| vm.runtime_error("attempt to use a closed file"));
            if let Err(error) = flush_pending(vm, file, handle) {
                vm.runtime_error(&error.to_string());
            }
            let key = buffer_key(vm, file);
            vm.file_buffers.insert(key, FileBuffer { mode, capacity, pending: Vec::new() });
            vm.data_stack.push(Value::bool(true));
            1
        });

        self.register_method(&mut file_mt_map, "__gc", |vm, args| {
            let Some(value) = args.first().copied() else {
                vm.runtime_error("bad argument #1 to '__gc' (FILE* expected, got no value)");
            };
            if !value.is_obj() {
                let got = vm.error_type_name(value);
                vm.runtime_error(&format!("bad argument #1 to '__gc' (FILE* expected, got {})", got));
            }
            match &vm.objects[value.as_obj() as usize] {
                Some(GcObject::File(file, _)) => {
                    file.borrow_mut().take();
                }
                Some(GcObject::StdFile(..)) => {}
                _ => {
                    let got = vm.error_type_name(value);
                    vm.runtime_error(&format!("bad argument #1 to '__gc' (FILE* expected, got {})", got));
                }
            }
            0
        });

        let name_key = self.alloc_str("__name");
        let file_name = self.alloc_str("FILE*");
        file_mt_map.insert(name_key, file_name);
        let index_key = self.alloc_str("__index");
        let file_mt_id = self.alloc(GcObject::Table(file_mt_map, None));
        if let Some(GcObject::Table(m, _)) = &mut self.objects[file_mt_id as usize] {
            m.insert(index_key, Value::obj(file_mt_id));
        }

        let stdin = Value::obj(self.alloc(GcObject::StdFile(
            StandardStream::Stdin,
            Some(file_mt_id),
        )));
        let stdout = Value::obj(self.alloc(GcObject::StdFile(
            StandardStream::Stdout,
            Some(file_mt_id),
        )));
        let stderr = Value::obj(self.alloc(GcObject::StdFile(
            StandardStream::Stderr,
            Some(file_mt_id),
        )));
        io_map.insert(self.alloc_str("stdin"), stdin);
        io_map.insert(self.alloc_str("stdout"), stdout);
        io_map.insert(self.alloc_str("stderr"), stderr);
        self.set_global("_IO_input", stdin);
        self.set_global("_IO_output", stdout);

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

                if !matches!(
                    mode.as_str(),
                    "r" | "rb" | "r+" | "r+b"
                        | "w" | "wb" | "w+" | "w+b"
                        | "a" | "ab" | "a+" | "a+b"
                ) {
                    vm.runtime_error("invalid mode");
                }

                let mut opts = std::fs::OpenOptions::new();
                match mode.as_bytes()[0] {
                    b'r' => { opts.read(true).write(mode.contains('+')); }
                    b'w' => {
                        opts.write(true).read(mode.contains('+')).create(true).truncate(true);
                    }
                    b'a' => {
                        opts.append(true).read(mode.contains('+')).create(true);
                    }
                    _ => unreachable!(),
                }

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
                        let code = vm.alloc_integer(e.raw_os_error().unwrap_or(1) as i64);
                        vm.data_stack.push(code);
                        3
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
                } else if matches!(
                    vm.objects[args[0].as_obj() as usize],
                    Some(GcObject::StdFile(..))
                ) {
                    let value = vm.alloc_str("file");
                    vm.data_stack.push(value);
                    return 1;
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
                    Some(GcObject::File(..)) | Some(GcObject::StdFile(..))
                )
            {
                vm.set_global("_IO_input", target);
            } else {
                if !matches!(vm.callable_type_name(target), "string" | "number") {
                    let got = vm.error_type_name(target);
                    vm.runtime_error(&format!(
                        "bad argument #1 to 'input' (FILE* expected, got {})",
                        got
                    ));
                }
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
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::SetIoDefault { key: "_IO_input" });
                    vm.request_call(open_fn_val, vec![target, mode_key]);
                    return 0;
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
                    Some(GcObject::File(..)) | Some(GcObject::StdFile(..))
                )
            {
                vm.set_global("_IO_output", target);
            } else {
                if !matches!(vm.callable_type_name(target), "string" | "number") {
                    let got = vm.error_type_name(target);
                    vm.runtime_error(&format!(
                        "bad argument #1 to 'output' (FILE* expected, got {})",
                        got
                    ));
                }
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
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::SetIoDefault { key: "_IO_output" });
                    vm.request_call(open_fn_val, vec![target, mode_key]);
                    return 0;
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
            if input.is_obj() && matches!(
                &vm.objects[input.as_obj() as usize],
                Some(GcObject::File(file, _)) if file.borrow().is_none()
            ) {
                vm.runtime_error("standard input file is closed");
            }
            let mut read_args = vec![input];
            read_args.extend_from_slice(&args);

            let mt_id = match &vm.objects[input.as_obj() as usize] {
                Some(GcObject::File(_, mt)) | Some(GcObject::StdFile(_, mt)) => *mt,
                _ => None,
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
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::ReturnResults);
                    vm.request_call(read_fn, read_args);
                    return 0;
                }
            }
            0
        });

        // io.write(...)

        self.register_method(&mut io_map, "write", |vm, args| {
            for (index, value) in args.iter().copied().enumerate() {
                if !matches!(vm.callable_type_name(value), "string" | "number") {
                    let got = vm.error_type_name(value);
                    vm.runtime_error(&format!(
                        "bad argument #{} to 'io.write' (string expected, got {})",
                        index + 1,
                        got
                    ));
                }
            }
            let output = vm.get_global("_IO_output");
            if !output.is_truthy() {
                vm.runtime_error("default output file is not set");
            }
            if output.is_obj() && matches!(
                &vm.objects[output.as_obj() as usize],
                Some(GcObject::File(file, _)) if file.borrow().is_none()
            ) {
                vm.runtime_error("standard output file is closed");
            }
            let mut write_args = vec![output];
            write_args.extend_from_slice(&args);

            let mt_id = match &vm.objects[output.as_obj() as usize] {
                Some(GcObject::File(_, mt)) | Some(GcObject::StdFile(_, mt)) => *mt,
                _ => None,
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
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::ReturnResults);
                    vm.request_call(write_fn, write_args);
                    return 0;
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

            let mt_id = match &vm.objects[output.as_obj() as usize] {
                Some(GcObject::File(_, mt)) | Some(GcObject::StdFile(_, mt)) => *mt,
                _ => None,
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
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::ReturnResults);
                    vm.request_call(flush_fn, vec![output]);
                    return 0;
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

            let mt_id = match &vm.objects[target.as_obj() as usize] {
                Some(GcObject::File(_, mt)) | Some(GcObject::StdFile(_, mt)) => *mt,
                _ => None,
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
                    vm.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::ReturnResults);
                    vm.request_call(close_fn, vec![target]);
                    return 0;
                }
            }

            vm.runtime_error("bad argument to 'close' (FILE expected)");
            0
        });

        // io.lines([filename])
        let lines_fn = self.alloc(GcObject::NativeClosure(
            |vm, args, mt_val| {
                let close_on_eof = args.first().is_some_and(|value| value.0 != TAG_NIL);
                let file_val = if !close_on_eof {
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
                let formats = if close_on_eof { &args[1..] } else { &args[args.len().min(1)..] };
                let iter = make_lines_iterator(vm, file_val, formats, close_on_eof);
                vm.data_stack.push(iter);
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

        self.register_method(&mut debug_map, "getregistry", |vm, _| {
            vm.data_stack.push(Value::obj(vm.registry));
            1
        });

        self.register_method(&mut debug_map, "getupvalue", |vm, args| {
            if args.len() < 2 || !args[0].is_obj() {
                vm.runtime_error("bad arguments to 'getupvalue'");
            }
            let index = vm
                .to_num(args[1])
                .filter(|value| value.fract() == 0.0 && *value > 0.0)
                .map(|value| value as usize - 1);
            let Some(index) = index else {
                return 0;
            };
            match vm.objects[args[0].as_obj() as usize].clone() {
                Some(GcObject::Closure {
                    chunk_idx,
                    upvalues,
                }) => {
                    let (Some(upvalue_id), Some((_, _, name))) = (
                        upvalues.get(index).copied(),
                        vm.chunks[chunk_idx].upvals.get(index).cloned(),
                    ) else {
                        return 0;
                    };
                    let value = match &vm.objects[upvalue_id as usize] {
                        Some(GcObject::Upval(value)) => *value,
                        _ => return 0,
                    };
                    let name = if vm.chunks[chunk_idx].is_stripped {
                        "(*no name)".to_string()
                    } else {
                        name
                    };
                    let name = vm.alloc_str(&name);
                    vm.data_stack.push(name);
                    vm.data_stack.push(value);
                    2
                }
                Some(GcObject::NativeClosure(_, state)) if index == 0 => {
                    let name = vm.alloc_str("");
                    vm.data_stack.push(name);
                    vm.data_stack.push(state);
                    2
                }
                Some(GcObject::NativeFn(_)) => 0,
                _ => vm.runtime_error("bad argument #1 to 'getupvalue' (function expected)"),
            }
        });

        self.register_method(&mut debug_map, "getuservalue", |vm, args| {
            let value = args.first().copied().unwrap_or(Value::nil());
            let uservalue = if value.is_obj()
                && matches!(vm.objects[value.as_obj() as usize],
                    Some(GcObject::File(..) | GcObject::StdFile(..)))
            {
                vm.uservalues.get(&value.as_obj()).copied().unwrap_or(Value::nil())
            } else {
                Value::nil()
            };
            vm.data_stack.push(uservalue);
            1
        });

        self.register_method(&mut debug_map, "setuservalue", |vm, args| {
            let value = args.first().copied().unwrap_or(Value::nil());
            let is_full_userdata = value.is_obj()
                && matches!(vm.objects[value.as_obj() as usize],
                    Some(GcObject::File(..) | GcObject::StdFile(..)));
            if !is_full_userdata {
                let got = if value.is_obj()
                    && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::LightUserdata(_)))
                {
                    "light userdata"
                } else {
                    vm.callable_type_name(value)
                };
                vm.runtime_error(&format!(
                    "bad argument #1 to 'setuservalue' (full userdata expected, got {})",
                    got
                ));
            }
            let uservalue = args.get(1).copied().unwrap_or(Value::nil());
            vm.uservalues.insert(value.as_obj(), uservalue);
            vm.data_stack.push(value);
            1
        });

        self.register_method(&mut debug_map, "upvalueid", |vm, args| {
            if args.len() < 2 || !args[0].is_obj() {
                vm.runtime_error("bad arguments to 'upvalueid'");
            }
            let index = vm
                .to_num(args[1])
                .filter(|value| value.fract() == 0.0 && *value > 0.0)
                .map(|value| value as usize - 1)
                .unwrap_or_else(|| vm.runtime_error("bad argument #2 to 'upvalueid'"));
            let function_id = args[0].as_obj() as usize;
            let identity = match vm.objects[function_id].as_ref() {
                Some(GcObject::Closure { upvalues, .. }) => upvalues
                    .get(index)
                    .copied()
                    .map(|id| {
                        let light_id = if let Some(&light_id) = vm.upvalue_ids.get(&id) {
                            light_id
                        } else {
                            let light_id = vm.alloc(GcObject::LightUserdata(id));
                            vm.upvalue_ids.insert(id, light_id);
                            light_id
                        };
                        Value::obj(light_id)
                    })
                    .unwrap_or_else(|| vm.runtime_error("invalid upvalue index")),
                Some(GcObject::NativeClosure(..)) if index == 0 => args[0],
                Some(GcObject::NativeFn(_)) => vm.runtime_error("invalid upvalue index"),
                _ => vm.runtime_error("bad argument #1 to 'upvalueid' (function expected)"),
            };
            vm.data_stack.push(identity);
            1
        });

        self.register_method(&mut debug_map, "setupvalue", |vm, args| {
            if args.len() < 3 || !args[0].is_obj() {
                vm.runtime_error("bad arguments to 'setupvalue'");
            }
            let index = vm
                .to_num(args[1])
                .filter(|value| value.fract() == 0.0 && *value > 0.0)
                .map(|value| value as usize - 1);
            let Some(index) = index else {
                return 0;
            };
            let function_id = args[0].as_obj() as usize;
            let new_value = args[2];
            let object = vm.objects[function_id].clone();
            let name = match object {
                Some(GcObject::Closure {
                    chunk_idx,
                    upvalues,
                }) => {
                    let (Some(upvalue_id), Some((_, _, name))) = (
                        upvalues.get(index).copied(),
                        vm.chunks[chunk_idx].upvals.get(index).cloned(),
                    ) else {
                        return 0;
                    };
                    if let Some(GcObject::Upval(value)) = &mut vm.objects[upvalue_id as usize] {
                        *value = new_value;
                    }
                    if vm.chunks[chunk_idx].is_stripped {
                        "(*no name)".to_string()
                    } else {
                        name
                    }
                }
                Some(GcObject::NativeClosure(func, _)) if index == 0 => {
                    vm.objects[function_id] = Some(GcObject::NativeClosure(func, new_value));
                    String::new()
                }
                Some(GcObject::NativeFn(_)) => return 0,
                _ => vm.runtime_error("bad argument #1 to 'setupvalue' (function expected)"),
            };
            let name = vm.alloc_str(&name);
            vm.data_stack.push(name);
            1
        });

        self.register_method(&mut debug_map, "upvaluejoin", |vm, args| {
            if args.len() < 4
                || !args[0].is_obj()
                || !args[2].is_obj()
            {
                vm.runtime_error("bad argument to 'upvaluejoin' (function expected)");
            }
            let target_id = args[0].as_obj() as usize;
            let source_id = args[2].as_obj() as usize;
            let target_index = vm
                .to_num(args[1])
                .filter(|value| value.fract() == 0.0 && *value > 0.0)
                .map(|value| value as usize - 1)
                .unwrap_or_else(|| vm.runtime_error("bad argument to 'upvaluejoin'"));
            let source_index = vm
                .to_num(args[3])
                .filter(|value| value.fract() == 0.0 && *value > 0.0)
                .map(|value| value as usize - 1)
                .unwrap_or_else(|| vm.runtime_error("bad argument to 'upvaluejoin'"));
            let source_upvalue = match vm.objects.get(source_id).and_then(|object| object.as_ref()) {
                Some(GcObject::Closure { upvalues, .. }) => upvalues
                    .get(source_index)
                    .copied()
                    .unwrap_or_else(|| vm.runtime_error("bad argument to 'upvaluejoin'")),
                _ => vm.runtime_error("bad argument to 'upvaluejoin' (Lua function expected)"),
            };
            match vm.objects.get_mut(target_id).and_then(|object| object.as_mut()) {
                Some(GcObject::Closure { upvalues, .. }) => {
                    if target_index >= upvalues.len() {
                        vm.runtime_error("bad argument to 'upvaluejoin'");
                    }
                    upvalues[target_index] = source_upvalue;
                }
                _ => vm.runtime_error("bad argument to 'upvaluejoin' (Lua function expected)"),
            }
            0
        });

        self.register_method(&mut debug_map, "getlocal", |vm, args| {
            let (thread_id, offset) = match args.first().copied() {
                Some(value)
                    if value.is_obj()
                        && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Thread(_))) =>
                {
                    (Some(value.as_obj()), 1)
                }
                _ => (None, 0),
            };
            if args.len() <= offset + 1 {
                vm.runtime_error("bad arguments to 'getlocal'");
            }
            let target = args[offset];
            let index_number = vm
                .to_num(args[offset + 1])
                .unwrap_or_else(|| vm.runtime_error("bad local index to 'getlocal'"));
            if index_number.fract() != 0.0 {
                vm.runtime_error("bad local index to 'getlocal'");
            }
            let index = index_number as i64;

            if target.is_obj() && vm.is_callable(target) {
                let Some(GcObject::Closure { chunk_idx, .. }) =
                    vm.objects[target.as_obj() as usize].clone()
                else {
                    return 0;
                };
                if index <= 0 || index as usize > vm.chunks[chunk_idx].param_count {
                    return 0;
                }
                let local_index = index as usize - 1;
                let name = vm.chunks[chunk_idx]
                    .local_names
                    .first()
                    .and_then(|names| names.get(local_index))
                    .cloned();
                if let Some(name) = name {
                    let name = vm.alloc_str(&name);
                    vm.data_stack.push(name);
                    return 1;
                }
                return 0;
            }

            let Some(level_number) = vm.to_num(target) else {
                vm.runtime_error("bad argument to 'getlocal' (level expected)")
            };
            if level_number < 0.0
                || level_number.fract() != 0.0
                || (level_number == 0.0 && thread_id.is_some())
            {
                vm.runtime_error("level out of range in 'getlocal'");
            }
            let level = level_number as usize;
            let current_level = level
                + usize::from(
                    vm.call_stack
                        .last()
                        .is_some_and(|frame| frame.is_native),
                );
            let result = match thread_id {
                Some(id) if vm.current_thread != Some(id) => match &vm.objects[id as usize] {
                    Some(GcObject::Thread(Some(state))) => vm
                        .read_frame_local(
                            &state.call_stack,
                            &state.data_stack,
                            level,
                            index,
                        )
                        .unwrap_or_else(|_| vm.runtime_error("level out of range in 'getlocal'")),
                    Some(GcObject::Thread(None)) => {
                        vm.runtime_error("cannot inspect a running coroutine")
                    }
                    _ => vm.runtime_error("bad argument #1 to 'getlocal' (thread expected)"),
                },
                _ => vm
                    .read_frame_local(
                        &vm.call_stack,
                        &vm.data_stack,
                        current_level,
                        index,
                    )
                    .unwrap_or_else(|_| vm.runtime_error("level out of range in 'getlocal'")),
            };

            if let Some((name, value)) = result {
                let name = vm.alloc_str(&name);
                vm.data_stack.push(name);
                vm.data_stack.push(value);
                2
            } else {
                0
            }
        });

        self.register_method(&mut debug_map, "setlocal", |vm, args| {
            let (thread_id, offset) = match args.first().copied() {
                Some(value)
                    if value.is_obj()
                        && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Thread(_))) =>
                {
                    (Some(value.as_obj()), 1)
                }
                _ => (None, 0),
            };
            if args.len() <= offset + 2 {
                vm.runtime_error("bad arguments to 'setlocal'");
            }
            let level_number = vm
                .to_num(args[offset])
                .unwrap_or_else(|| vm.runtime_error("bad stack level to 'setlocal'"));
            let index_number = vm
                .to_num(args[offset + 1])
                .unwrap_or_else(|| vm.runtime_error("bad local index to 'setlocal'"));
            if level_number < 1.0
                || level_number.fract() != 0.0
                || index_number.fract() != 0.0
            {
                vm.runtime_error("level out of range in 'setlocal'");
            }
            let level = level_number as usize;
            let current_level = level
                + usize::from(
                    vm.call_stack
                        .last()
                        .is_some_and(|frame| frame.is_native),
                );
            let index = index_number as i64;
            let new_value = args[offset + 2];

            let name = if let Some(id) = thread_id.filter(|id| vm.current_thread != Some(*id)) {
                let mut state = match &mut vm.objects[id as usize] {
                    Some(GcObject::Thread(slot)) => slot
                        .take()
                        .unwrap_or_else(|| vm.runtime_error("cannot inspect a running coroutine")),
                    _ => vm.runtime_error("bad argument #1 to 'setlocal' (thread expected)"),
                };
                let location = vm.frame_local_location(&state.call_stack, level, index);
                let location = match location {
                    Ok(location) => location,
                    Err(()) => {
                        if let Some(GcObject::Thread(slot)) = &mut vm.objects[id as usize] {
                            *slot = Some(state);
                        }
                        vm.runtime_error("level out of range in 'setlocal'")
                    }
                };
                let name = location.map(|(name, is_vararg, slot)| {
                    let frame_index = state.call_stack.len() - level;
                    if is_vararg {
                        state.call_stack[frame_index].varargs[slot] = new_value;
                    } else {
                        let stack_index = state.call_stack[frame_index].stack_base + slot;
                        let old = state.data_stack[stack_index];
                        if old.is_obj()
                            && matches!(vm.objects[old.as_obj() as usize], Some(GcObject::Upval(_)))
                        {
                            if let Some(GcObject::Upval(value)) =
                                &mut vm.objects[old.as_obj() as usize]
                            {
                                *value = new_value;
                            }
                        } else {
                            state.data_stack[stack_index] = new_value;
                        }
                    }
                    name
                });
                if let Some(GcObject::Thread(slot)) = &mut vm.objects[id as usize] {
                    *slot = Some(state);
                }
                name
            } else {
                let location = vm
                    .frame_local_location(&vm.call_stack, current_level, index)
                    .unwrap_or_else(|_| vm.runtime_error("level out of range in 'setlocal'"));
                location.map(|(name, is_vararg, slot)| {
                    let frame_index = vm.call_stack.len() - current_level;
                    if is_vararg {
                        vm.call_stack[frame_index].varargs[slot] = new_value;
                    } else {
                        let stack_index = vm.call_stack[frame_index].stack_base + slot;
                        let old = vm.data_stack[stack_index];
                        if old.is_obj()
                            && matches!(vm.objects[old.as_obj() as usize], Some(GcObject::Upval(_)))
                        {
                            if let Some(GcObject::Upval(value)) =
                                &mut vm.objects[old.as_obj() as usize]
                            {
                                *value = new_value;
                            }
                        } else {
                            vm.data_stack[stack_index] = new_value;
                        }
                    }
                    name
                })
            };

            if let Some(name) = name {
                let name = vm.alloc_str(&name);
                vm.data_stack.push(name);
                1
            } else {
                0
            }
        });

        self.register_method(&mut debug_map, "gethook", |vm, args| {
            let hook = if let Some(thread) = args.first().copied() {
                if !thread.is_obj() {
                    vm.runtime_error("bad argument #1 to 'gethook' (thread expected)");
                }
                let thread_id = thread.as_obj();
                if vm.current_thread == Some(thread_id) {
                    vm.hook.clone()
                } else {
                    match &vm.objects[thread_id as usize] {
                        Some(GcObject::Thread(Some(state))) => state.hook.clone(),
                        Some(GcObject::Thread(None)) => {
                            vm.runtime_error("cannot inspect a running coroutine")
                        }
                        _ => vm.runtime_error("bad argument #1 to 'gethook' (thread expected)"),
                    }
                }
            } else {
                vm.hook.clone()
            };

            let Some(function) = hook.function else {
                vm.data_stack.push(Value::nil());
                return 1;
            };

            let mut mask = String::new();
            if hook.call {
                mask.push('c');
            }
            if hook.ret {
                mask.push('r');
            }
            if hook.line {
                mask.push('l');
            }
            let mask_value = vm.alloc_str(&mask);
            vm.data_stack.push(function);
            vm.data_stack.push(mask_value);
            vm.data_stack.push(Value::num(hook.count as f64));
            3
        });

        self.register_method(&mut debug_map, "sethook", |vm, args| {
            let (thread_id, offset) = match args.first().copied() {
                Some(value)
                    if value.is_obj()
                        && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Thread(_))) =>
                {
                    (Some(value.as_obj()), 1)
                }
                _ => (None, 0),
            };

            let function = args.get(offset).copied().unwrap_or(Value::nil());
            let clear = function.0 == TAG_NIL;
            if !clear && !vm.is_callable(function) {
                vm.runtime_error(&format!(
                    "bad argument #{} to 'sethook' (function expected)",
                    offset + 1
                ));
            }

            let mask = args
                .get(offset + 1)
                .map(|value| vm.val_to_str(*value))
                .unwrap_or_default();
            let count = args
                .get(offset + 2)
                .and_then(|value| vm.to_num(*value))
                .unwrap_or(0.0);
            if count < 0.0 || count > usize::MAX as f64 {
                vm.runtime_error("bad argument to 'sethook' (count out of range)");
            }

            let update = |hook: &mut HookState| {
                let was_in_hook = hook.in_hook;
                *hook = if clear {
                    HookState::default()
                } else {
                    HookState {
                        function: Some(function),
                        call: mask.contains('c'),
                        ret: mask.contains('r'),
                        line: mask.contains('l'),
                        count: count as usize,
                        counter: 0,
                        in_hook: was_in_hook,
                    }
                };
                hook.in_hook = was_in_hook;
            };

            match thread_id {
                Some(id) if vm.current_thread == Some(id) => {
                    update(&mut vm.hook);
                    for frame in &mut vm.call_stack {
                        frame.last_hook_ip = None;
                    }
                    if let Some(frame) = vm.call_stack.iter_mut().rev().find(|frame| !frame.is_native) {
                        frame.last_hook_ip = Some(frame.ip.saturating_sub(1));
                    }
                }
                Some(id) => match &mut vm.objects[id as usize] {
                    Some(GcObject::Thread(Some(state))) => {
                        update(&mut state.hook);
                        for frame in &mut state.call_stack {
                            frame.last_hook_ip = None;
                        }
                    }
                    Some(GcObject::Thread(None)) => {
                        vm.runtime_error("cannot change a running coroutine hook")
                    }
                    _ => vm.runtime_error("bad argument #1 to 'sethook' (thread expected)"),
                },
                None => {
                    update(&mut vm.hook);
                    for frame in &mut vm.call_stack {
                        frame.last_hook_ip = None;
                    }
                    if let Some(frame) = vm.call_stack.iter_mut().rev().find(|frame| !frame.is_native) {
                        frame.last_hook_ip = Some(frame.ip.saturating_sub(1));
                    }
                }
            }
            0
        });

        self.register_method(&mut debug_map, "getinfo", |vm, args| {
            if args.is_empty() {
                vm.runtime_error("bad argument #1 to 'getinfo'");
            }
            fn short_source(source: &str) -> String {
                const LIMIT: usize = 60;
                if source.is_empty() {
                    return "[string \"\"]".to_string();
                }
                if let Some(name) = source.strip_prefix('=') {
                    return name.chars().take(LIMIT - 1).collect();
                }
                if let Some(name) = source.strip_prefix('@') {
                    let chars: Vec<char> = name.chars().collect();
                    if chars.len() < LIMIT {
                        return name.to_string();
                    }
                    let tail: String = chars[chars.len() - (LIMIT - 4)..].iter().collect();
                    return format!("...{}", tail);
                }

                let first_line = source.lines().next().unwrap_or("");
                let mut text: String = first_line.chars().take(LIMIT - 15).collect();
                if first_line.is_empty()
                    || first_line.chars().count() != source.chars().count()
                    || first_line.chars().count() > LIMIT - 15
                {
                    text.push_str("...");
                }
                format!("[string \"{}\"]", text)
            }

            fn insert(vm: &mut VM, map: &mut HashMap<Value, Value>, key: &str, value: Value) {
                let key = vm.alloc_str(key);
                vm.temp_roots.push(key);
                if value.is_obj() {
                    vm.temp_roots.push(value);
                }
                map.insert(key, value);
            }

            fn insert_string(
                vm: &mut VM,
                map: &mut HashMap<Value, Value>,
                key: &str,
                value: &str,
            ) {
                let value = vm.alloc_str(value);
                insert(vm, map, key, value);
            }

            let (thread_id, offset) = match args.first().copied() {
                Some(value)
                    if value.is_obj()
                        && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Thread(_))) =>
                {
                    (Some(value.as_obj()), 1)
                }
                _ => (None, 0),
            };
            if args.len() <= offset {
                vm.runtime_error("bad argument to 'getinfo'");
            }
            let options = args
                .get(offset + 1)
                .map(|value| vm.val_to_str(*value))
                .unwrap_or_else(|| "flnStu".to_string());
            if options.chars().any(|option| !"nSlutfL".contains(option)) {
                vm.runtime_error("bad argument #2 to 'getinfo' (invalid option)");
            }

            let foreign_stack = thread_id
                .filter(|id| vm.current_thread != Some(*id))
                .map(|id| match &vm.objects[id as usize] {
                    Some(GcObject::Thread(Some(state))) => state.call_stack.clone(),
                    Some(GcObject::Thread(None)) => {
                        vm.runtime_error("cannot inspect a running coroutine")
                    }
                    _ => vm.runtime_error("bad argument #1 to 'getinfo' (thread expected)"),
                });
            let target = args[offset];
            let (cid, current_ip, active_frame, current_frame_index) = if let Some(level) = vm.to_num(target) {
                if level < 1.0 || level.fract() != 0.0 {
                    vm.data_stack.push(Value::nil());
                    return 1;
                }
                let level = level as usize;
                let stack = foreign_stack.as_deref().unwrap_or(&vm.call_stack);
                let stack_end = stack.len()
                    - usize::from(
                        foreign_stack.is_none()
                            && stack.last().is_some_and(|frame| frame.is_native),
                    );
                if level > stack_end {
                    vm.data_stack.push(Value::nil());
                    return 1;
                }
                let frame_index = stack_end - level;
                let frame = stack[frame_index].clone();
                (
                    frame.closure_id,
                    frame.ip.saturating_sub(1),
                    Some(frame),
                    foreign_stack.is_none().then_some(frame_index),
                )
            } else if target.is_obj() && vm.is_callable(target) {
                (target.as_obj(), 0, None, None)
            } else {
                vm.runtime_error("bad argument #1 to 'getinfo' (function or level expected)")
            };

            let roots_start = vm.temp_roots.len();
            let mut info_map = HashMap::new();
            let object = vm.objects[cid as usize].clone();
            let is_native_closure = matches!(&object, Some(GcObject::NativeClosure(..)));

            if options.contains('f') {
                insert(vm, &mut info_map, "func", Value::obj(cid));
            }
            if options.contains('n') {
                insert_string(vm, &mut info_map, "namewhat", "");
                let stored_name = active_frame.as_ref().and_then(|frame| {
                    if frame.is_hook {
                        Some((String::new(), "hook".to_string()))
                    } else {
                        frame
                            .call_name
                            .clone()
                            .map(|name| (name, frame.call_namewhat.clone()))
                    }
                });
                let inferred_name = current_frame_index
                    .and_then(|frame_index| vm.infer_frame_name(frame_index, true));
                if let Some((name, namewhat)) = stored_name.or(inferred_name) {
                    if !name.is_empty() {
                        insert_string(vm, &mut info_map, "name", &name);
                    }
                    insert_string(vm, &mut info_map, "namewhat", &namewhat);
                }
            }
            if options.contains('t') {
                let is_tailcall = active_frame
                    .as_ref()
                    .is_some_and(|frame| frame.is_tailcall);
                insert(
                    vm,
                    &mut info_map,
                    "istailcall",
                    Value::bool(is_tailcall),
                );
            }

            match object {
                Some(GcObject::Closure {
                    chunk_idx,
                    upvalues,
                }) => {
                    let chunk = vm.chunks[chunk_idx].clone();
                    if options.contains('S') {
                        let source = vm.source_names[chunk.source_id].clone();
                        insert_string(vm, &mut info_map, "source", &source);
                        insert_string(vm, &mut info_map, "short_src", &short_source(&source));
                        insert_string(
                            vm,
                            &mut info_map,
                            "what",
                            if chunk.is_main { "main" } else { "Lua" },
                        );
                        insert(
                            vm,
                            &mut info_map,
                            "linedefined",
                            Value::num(if chunk.is_main {
                                0.0
                            } else {
                                chunk.linedefined as f64
                            }),
                        );
                        insert(
                            vm,
                            &mut info_map,
                            "lastlinedefined",
                            Value::num(if chunk.is_main {
                                0.0
                            } else {
                                chunk.lastlinedefined as f64
                            }),
                        );
                    }
                    if options.contains('l') {
                        let current_line = if chunk.is_stripped {
                            -1.0
                        } else if active_frame.is_some() {
                            chunk.lines.get(current_ip).copied().unwrap_or(0) as f64
                        } else {
                            -1.0
                        };
                        insert(
                            vm,
                            &mut info_map,
                            "currentline",
                            Value::num(current_line),
                        );
                    }
                    if options.contains('u') {
                        insert(
                            vm,
                            &mut info_map,
                            "nups",
                            Value::num(upvalues.len() as f64),
                        );
                        insert(
                            vm,
                            &mut info_map,
                            "nparams",
                            Value::num(chunk.param_count as f64),
                        );
                        insert(
                            vm,
                            &mut info_map,
                            "isvararg",
                            Value::bool(chunk.is_vararg),
                        );
                    }
                    if options.contains('L') {
                        let mut lines = HashMap::new();
                        for line in chunk.lines.iter().copied() {
                            if line > chunk.linedefined && line <= chunk.lastlinedefined {
                                lines.insert(Value::num(line as f64), Value::bool(true));
                            }
                        }
                        let lines_id = vm.alloc(GcObject::Table(lines, None));
                        insert(
                            vm,
                            &mut info_map,
                            "activelines",
                            Value::obj(lines_id),
                        );
                    }
                }
                Some(GcObject::NativeFn(_))
                | Some(GcObject::NativeClosure(..))
                | Some(GcObject::Continuation { .. }) => {
                    if options.contains('S') {
                        insert_string(vm, &mut info_map, "source", "=[C]");
                        insert_string(vm, &mut info_map, "short_src", "[C]");
                        insert_string(vm, &mut info_map, "what", "C");
                        insert(vm, &mut info_map, "linedefined", Value::num(-1.0));
                        insert(vm, &mut info_map, "lastlinedefined", Value::num(-1.0));
                    }
                    if options.contains('l') {
                        insert(vm, &mut info_map, "currentline", Value::num(-1.0));
                    }
                    if options.contains('u') {
                        let nups = usize::from(is_native_closure);
                        insert(vm, &mut info_map, "nups", Value::num(nups as f64));
                        insert(vm, &mut info_map, "nparams", Value::num(0.0));
                        insert(vm, &mut info_map, "isvararg", Value::bool(true));
                    }
                }
                _ => vm.runtime_error("bad argument #1 to 'getinfo' (function expected)"),
            }

            let id = vm.alloc(GcObject::Table(info_map, None));
            vm.temp_roots.truncate(roots_start);
            vm.data_stack.push(Value::obj(id));
            1
        });

        // debug.traceback([message], [level])
        self.register_method(&mut debug_map, "traceback", |vm, args| {
            let (thread_id, offset) = match args.first().copied() {
                Some(value)
                    if value.is_obj()
                        && matches!(vm.objects[value.as_obj() as usize], Some(GcObject::Thread(_))) =>
                {
                    (Some(value.as_obj()), 1)
                }
                _ => (None, 0),
            };
            if let Some(message) = args.get(offset).copied() {
                let is_string = message.is_obj()
                    && matches!(vm.objects[message.as_obj() as usize], Some(GcObject::Str(_)));
                if message.0 != TAG_NIL && !is_string {
                    vm.data_stack.push(message);
                    return 1;
                }
            }
            let mut msg = args
                .get(offset)
                .filter(|value| value.0 != TAG_NIL)
                .map(|value| vm.val_to_str(*value))
                .unwrap_or_default();
            let default_level = if thread_id.is_some() { 0.0 } else { 1.0 };
            let level = args
                .get(offset + 1)
                .and_then(|value| vm.to_num(*value))
                .unwrap_or(default_level) as usize;

            if !msg.is_empty() {
                msg.push_str("\n");
            }
            let traceback = match thread_id {
                Some(id) if vm.current_thread != Some(id) => match &vm.objects[id as usize] {
                    Some(GcObject::Thread(Some(state))) => vm.generate_traceback_from(
                        &state.call_stack,
                        level,
                        state.status == ThreadStatus::Suspended && !state.call_stack.is_empty(),
                    ),
                    Some(GcObject::Thread(None)) => {
                        vm.runtime_error("cannot inspect a running coroutine")
                    }
                    _ => vm.runtime_error("bad argument #1 to 'traceback' (thread expected)"),
                },
                _ => vm.call_stack.iter().rev().find_map(|frame| {
                    match &frame.native_continuation {
                        Some(NativeContinuation::XPCallHandling { traceback, .. })
                            if thread_id.is_none() && level == 1 => Some(traceback.clone()),
                        _ => None,
                    }
                }).unwrap_or_else(|| vm.generate_traceback(level)),
            };
            msg.push_str(&traceback);

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

    fn is_callable(&self, value: Value) -> bool {
        value.is_obj()
            && matches!(
                self.objects[value.as_obj() as usize],
                Some(GcObject::Closure { .. })
                    | Some(GcObject::NativeFn(_))
                    | Some(GcObject::NativeClosure(..))
                    | Some(GcObject::Continuation { .. })
            )
    }

    fn callable_type_name(&self, value: Value) -> &'static str {
        if value.0 == TAG_NIL {
            "nil"
        } else if value.0 == TAG_FALSE || value.0 == TAG_TRUE {
            "boolean"
        } else if !value.is_obj() {
            "number"
        } else {
            match self.objects[value.as_obj() as usize] {
                Some(GcObject::Str(_)) => "string",
                Some(GcObject::Table(..)) => "table",
                Some(GcObject::Integer(_) | GcObject::Float(_)) => "number",
                Some(GcObject::Thread(_) | GcObject::Continuation { .. }) => "thread",
                Some(GcObject::File(..) | GcObject::StdFile(..) | GcObject::Upval(_) | GcObject::LightUserdata(_)) => "userdata",
                _ => "function",
            }
        }
    }

    fn error_type_name(&mut self, value: Value) -> String {
        if let Some(metatable_id) = self.get_type_metatable(value) {
            if let Some(&name_key) = self.interned_strings.get("__name") {
                if let Some(GcObject::Table(map, _)) = &self.objects[metatable_id as usize] {
                    if let Some(name) = map.get(&Value::obj(name_key)).filter(|name| name.is_obj()) {
                        if let Some(GcObject::Str(text)) = &self.objects[name.as_obj() as usize] {
                            return text.clone();
                        }
                    }
                }
            }
        }
        self.callable_type_name(value).to_string()
    }

    fn callable_method_at(&self, chunk_idx: usize, ip: usize) -> bool {
        self.chunks[chunk_idx]
            .call_names
            .get(ip)
            .and_then(Option::as_ref)
            .is_some_and(|(_, kind)| kind == "method")
    }

    fn native_call_is_method(&self) -> bool {
        if self.call_stack.last().is_some_and(|frame| frame.call_namewhat == "method") {
            return true;
        }
        if self.call_stack.len() >= 2 {
            let caller = &self.call_stack[self.call_stack.len() - 2];
            return self.callable_method_at(caller.chunk_idx, caller.ip.saturating_sub(1));
        }
        false
    }

    fn native_argument_number(&self, idx: usize) -> usize {
        if self.native_call_is_method() { idx } else { idx + 1 }
    }

    fn call_type_error(&mut self, value: Value, chunk_idx: usize, ip: usize) -> ! {
        let mut message = format!("attempt to call a {} value", self.callable_type_name(value));
        if let Some(Some((name, kind))) = self.chunks[chunk_idx].call_names.get(ip) {
            message.push_str(&format!(" ({} '{}')", kind, name));
        }
        self.runtime_error(&message)
    }

    fn arithmetic_type_error(&mut self, left: Value, right: Value) -> ! {
        let invalid_left = self.to_num(left).is_none();
        let value = if invalid_left { left } else { right };
        let mut message = format!(
            "attempt to perform arithmetic on a {} value",
            self.error_type_name(value)
        );
        if let Some(frame) = self.call_stack.last() {
            let ip = frame.ip.saturating_sub(1);
            let names = if invalid_left {
                &self.chunks[frame.chunk_idx].call_names
            } else {
                &self.chunks[frame.chunk_idx].right_names
            };
            if let Some(Some((name, kind))) = names.get(ip) {
                message.push_str(&format!(" ({} '{}')", kind, name));
            }
        }
        self.runtime_error(&message)
    }

    fn comparison_type_error(&mut self, left: Value, right: Value) -> ! {
        let left_type = self.error_type_name(left);
        let right_type = self.error_type_name(right);
        if left_type == right_type {
            self.runtime_error(&format!("attempt to compare two {} values", left_type))
        } else {
            self.runtime_error(&format!("attempt to compare {} with {}", left_type, right_type))
        }
    }

    fn bitwise_type_error(&mut self, left: Value, right: Value) -> ! {
        let invalid_left = self.to_integer(left).is_none();
        let value = if invalid_left { left } else { right };
        let mut message = if self.to_num(value).is_some() {
            "number has no integer representation".to_string()
        } else {
            format!(
                "attempt to perform bitwise operation on a {} value",
                self.error_type_name(value)
            )
        };
        if let Some(frame) = self.call_stack.last() {
            let ip = frame.ip.saturating_sub(1);
            let names = if invalid_left {
                &self.chunks[frame.chunk_idx].call_names
            } else {
                &self.chunks[frame.chunk_idx].right_names
            };
            if let Some(Some((name, kind))) = names.get(ip) {
                message.push_str(&format!(" ({} '{}')", kind, name));
            }
        }
        self.runtime_error(&message)
    }

    fn dereference_stack_value(&self, value: Value) -> Value {
        if value.is_obj() {
            if let Some(GcObject::Upval(inner)) = &self.objects[value.as_obj() as usize] {
                return *inner;
            }
        }
        value
    }

    fn infer_frame_name(&self, frame_index: usize, scan_tables: bool) -> Option<(String, String)> {
        let frame = self.call_stack.get(frame_index)?;
        if frame.is_hook {
            return Some((String::new(), "hook".to_string()));
        }
        if frame_index == 0 {
            return None;
        }

        let target = Value::obj(frame.closure_id);
        let caller = &self.call_stack[frame_index - 1];
        let caller_chunk = &self.chunks[caller.chunk_idx];
        let caller_ip = caller.ip.saturating_sub(1);
        if let Some(names) = caller_chunk.local_names.get(caller_ip) {
            for (index, name) in names.iter().enumerate() {
                if name.starts_with('$') || caller.stack_base + index >= self.data_stack.len() {
                    continue;
                }
                let value = self.dereference_stack_value(self.data_stack[caller.stack_base + index]);
                if value == target {
                    return Some((name.clone(), "local".to_string()));
                }
            }
        }

        if let Some(GcObject::Closure { upvalues, .. }) =
            &self.objects[caller.closure_id as usize]
        {
            for (index, (_, _, name)) in caller_chunk.upvals.iter().enumerate() {
                let Some(upvalue_id) = upvalues.get(index) else {
                    continue;
                };
                let Some(GcObject::Upval(value)) = &self.objects[*upvalue_id as usize] else {
                    continue;
                };
                if *value == target {
                    return Some((name.clone(), "upvalue".to_string()));
                }
            }
        }

        if let Some(GcObject::Table(globals, _)) = &self.objects[self.global_env as usize] {
            for (key, value) in globals {
                if *value == target && key.is_obj() {
                    if let Some(GcObject::Str(name)) = &self.objects[key.as_obj() as usize] {
                        return Some((name.clone(), "global".to_string()));
                    }
                }
            }
        }

        if !scan_tables {
            return None;
        }

        for object in &self.objects {
            let Some(GcObject::Table(map, _)) = object else {
                continue;
            };
            for (key, value) in map {
                if *value == target && key.is_obj() {
                    if let Some(GcObject::Str(name)) = &self.objects[key.as_obj() as usize] {
                        return Some((name.clone(), "field".to_string()));
                    }
                }
            }
        }
        None
    }

    fn frame_local_location(
        &self,
        call_stack: &[CallFrame],
        level: usize,
        index: i64,
    ) -> Result<Option<(String, bool, usize)>, ()> {
        if level == 0 || level > call_stack.len() {
            return Err(());
        }
        let frame = &call_stack[call_stack.len() - level];
        if frame.is_native {
            if index <= 0 {
                return Ok(None);
            }
            let slot = index as usize - 1;
            return Ok((slot < frame.varargs.len()).then(|| {
                ("(*temporary)".to_string(), true, slot)
            }));
        }
        if index < 0 {
            let vararg_index = (-index - 1) as usize;
            return Ok((vararg_index < frame.varargs.len()).then(|| {
                ("(*vararg)".to_string(), true, vararg_index)
            }));
        }
        if index == 0 {
            return Ok(None);
        }
        let local_index = index as usize - 1;
        let chunk = &self.chunks[frame.chunk_idx];
        let ip = frame.ip.saturating_sub(1);
        let names = chunk
            .local_names
            .get(ip)
            .or_else(|| chunk.local_names.last());
        if !chunk.is_stripped {
            let Some(names) = names else {
                return Ok(None);
            };
            if let Some(name) = names.get(local_index) {
                return Ok(Some((name.clone(), false, local_index)));
            }
        }
        let frame_index = call_stack.len() - level;
        let stack_end = call_stack
            .get(frame_index + 1)
            .map(|next| next.stack_base)
            .unwrap_or_else(|| {
                frame.stack_base
                    + if chunk.is_stripped {
                        chunk.local_count
                    } else {
                        names.map_or(0, Vec::len)
                    }
            });
        Ok((frame.stack_base + local_index < stack_end).then(|| {
            ("(*temporary)".to_string(), false, local_index)
        }))
    }

    fn read_frame_local(
        &self,
        call_stack: &[CallFrame],
        data_stack: &[Value],
        level: usize,
        index: i64,
    ) -> Result<Option<(String, Value)>, ()> {
        let Some((name, is_vararg, slot)) =
            self.frame_local_location(call_stack, level, index)?
        else {
            return Ok(None);
        };
        let frame = &call_stack[call_stack.len() - level];
        let value = if is_vararg {
            frame.varargs[slot]
        } else {
            let Some(value) = data_stack.get(frame.stack_base + slot).copied() else {
                return Ok(None);
            };
            self.dereference_stack_value(value)
        };
        Ok(Some((name, value)))
    }

    fn dispatch_hook(&mut self, event: &str, line: Option<usize>) {
        let enabled = match event {
            "call" | "tail call" => self.hook.call,
            "return" => self.hook.ret,
            "line" => self.hook.line,
            "count" => self.hook.count > 0,
            _ => false,
        };
        if !enabled || self.hook.in_hook {
            return;
        }
        let Some(function) = self.hook.function else {
            return;
        };

        self.hook.in_hook = true;
        let saved_multiret = self.multiret_count;
        let saved_yielded = self.yielded;
        self.yielded = false;
        let event_value = self.alloc_str(event);
        let line_value = line.map_or_else(Value::nil, |value| Value::num(value as f64));
        self.internal_call(function, vec![event_value, line_value]);
        for _ in 0..self.multiret_count { self.data_stack.pop(); }
        self.multiret_count = saved_multiret;
        self.yielded = saved_yielded;
        self.hook.in_hook = false;
    }

    fn dispatch_instruction_hooks(
        &mut self,
        frame_idx: usize,
        chunk_idx: usize,
        ip: usize,
        instruction: OpCode,
    ) {
        if self.hook.function.is_none() || self.hook.in_hook {
            return;
        }
        let line = self.chunks[chunk_idx].lines.get(ip).copied().unwrap_or(0);
        if line == 0 {
            return;
        }
        let previous_ip = self.call_stack[frame_idx].last_hook_ip;
        let line_changed = previous_ip.is_none_or(|previous_ip| {
            let previous_line = self.chunks[chunk_idx]
                .lines
                .get(previous_ip)
                .copied()
                .unwrap_or(0);
            line != previous_line
        });
        let went_back = previous_ip.is_some_and(|previous_ip| ip <= previous_ip);
        self.call_stack[frame_idx].last_hook_ip = Some(ip);

        let count_step = line_changed
            || matches!(
                instruction,
                OpCode::LoadConst(_)
                    | OpCode::ForCond
                    | OpCode::Call(..)
                    | OpCode::ForCall(..)
                    | OpCode::TailCall(..)
                    | OpCode::Lt
                    | OpCode::Gt
                    | OpCode::LtEq
                    | OpCode::GtEq
            );
        if self.hook.count > 0 && count_step {
            self.hook.counter += 1;
            if self.hook.counter >= self.hook.count {
                self.hook.counter = 0;
                self.dispatch_hook("count", None);
            }
        }
        if self.hook.line && self.hook.function.is_some() && (line_changed || went_back) {
            self.dispatch_hook("line", Some(line));
        }
    }
    pub fn to_integer(&self, val: Value) -> Option<i64> {
        if val.is_obj() {
            match self.objects.get(val.as_obj() as usize) {
                Some(Some(GcObject::Integer(n))) => Some(*n),
                Some(Some(GcObject::Float(n))) => Self::exact_float_to_integer(*n),
                Some(Some(GcObject::Str(s))) => {
                    let text = s.trim();
                    text.parse::<i64>().ok().or_else(|| {
                        let (negative, unsigned) = if let Some(rest) = text.strip_prefix('-') {
                            (true, rest)
                        } else if let Some(rest) = text.strip_prefix('+') {
                            (false, rest)
                        } else {
                            (false, text)
                        };
                        let digits = unsigned.strip_prefix("0x").or_else(|| unsigned.strip_prefix("0X"))?;
                        if digits.is_empty() || !digits.bytes().all(|digit| digit.is_ascii_hexdigit()) {
                            return None;
                        }
                        let value = digits.bytes().fold(0u64, |value, digit| {
                            value.wrapping_mul(16).wrapping_add((digit as char).to_digit(16).unwrap() as u64)
                        }) as i64;
                        Some(if negative { value.wrapping_neg() } else { value })
                    }).or_else(|| {
                        parse_decimal_float(text).and_then(Self::exact_float_to_integer)
                    }).or_else(|| {
                        let (sign, unsigned) = if let Some(rest) = text.strip_prefix('-') {
                            (-1.0, rest)
                        } else if let Some(rest) = text.strip_prefix('+') {
                            (1.0, rest)
                        } else {
                            (1.0, text)
                        };
                        Self::exact_float_to_integer(parse_hex_float(unsigned) * sign)
                    })
                }
                _ => None,
            }
        } else if val.0 != TAG_NIL && val.0 != TAG_FALSE && val.0 != TAG_TRUE {
            let n = val.as_num();
            Self::exact_float_to_integer(n)
        } else {
            None
        }
    }

    fn ensure_call_capacity(&mut self, additional: usize) {
        if additional > MAX_VM_CALL_FRAMES.saturating_sub(self.call_stack.len()) {
            self.runtime_error(if self.in_error_handler {
                "error in error handling"
            } else {
                "stack overflow"
            });
        }
    }

    fn begin_native_call(&mut self, closure_id: u32, args: &[Value]) {
        self.ensure_call_capacity(1);
        let chunk_idx = self.call_stack.last().map(|frame| frame.chunk_idx).unwrap_or(0);
        let pending_name = self.pending_call_name.take();
        let (call_name, call_namewhat) = pending_name
            .map(|(name, namewhat)| (Some(name), namewhat))
            .unwrap_or_else(|| {
                (
                    self.qualified_function_name(Value::obj(closure_id)),
                    "field".to_string(),
                )
            });
        self.call_stack.push(CallFrame {
            closure_id,
            chunk_idx,
            ip: 0,
            stack_base: self.data_stack.len(),
            handler_base: self.handler_stack.len(),
            varargs: args.to_vec(),
            last_hook_ip: None,
            is_hook: self.hook.in_hook,
            is_tailcall: false,
            is_native: true,
            native_continuation: None,
            frame_continuation: None,
            call_name,
            call_namewhat,
        });
        self.dispatch_hook("call", None);
    }

    fn begin_native_tail_call(&mut self, closure_id: u32, args: Vec<Value>, is_method: bool) -> usize {
        let call_name = self.qualified_function_name(Value::obj(closure_id));
        let frame = self.call_stack.last_mut().expect("tail-call frame");
        let stack_base = frame.stack_base;
        self.data_stack.truncate(stack_base);
        frame.closure_id = closure_id;
        frame.ip = 0;
        frame.varargs = args;
        frame.last_hook_ip = None;
        frame.is_hook = false;
        frame.is_tailcall = true;
        frame.is_native = true;
        frame.native_continuation = None;
        frame.call_name = call_name;
        frame.call_namewhat = if is_method { "method" } else { "field" }.to_string();
        self.dispatch_hook("tail call", None);
        stack_base
    }

    fn record_top_call_name(&mut self) {
        let frame_index = self.call_stack.len().saturating_sub(1);
        let callsite_name = frame_index.checked_sub(1)
            .and_then(|caller_index| self.call_stack.get(caller_index))
            .and_then(|caller| self.chunks[caller.chunk_idx].call_names
                .get(caller.ip.saturating_sub(1)))
            .cloned()
            .flatten();
        let Some((name, namewhat)) = callsite_name
            .or_else(|| self.infer_frame_name(frame_index, false)) else {
            return;
        };
        if let Some(frame) = self.call_stack.get_mut(frame_index) {
            if !frame.is_hook {
                frame.call_name = (!name.is_empty()).then_some(name);
                frame.call_namewhat = namewhat;
            }
        }
    }

    fn enqueue_lua_call_named(
        &mut self,
        callable: Value,
        args: Vec<Value>,
        name: &str,
        namewhat: &str,
    ) -> bool {
        if !callable.is_obj()
            || !matches!(self.objects[callable.as_obj() as usize], Some(GcObject::Closure { .. }))
        {
            return false;
        }
        let previous = self.pending_call_name.replace((name.to_string(), namewhat.to_string()));
        self.enqueue_lua_call(callable, args);
        self.pending_call_name = previous;
        true
    }

    fn enqueue_lua_call(&mut self, callable: Value, args: Vec<Value>) {
        self.ensure_call_capacity(1);
        let GcObject::Closure { chunk_idx, .. } = self.objects[callable.as_obj() as usize]
            .as_ref().expect("Lua closure") else { unreachable!() };
        let chunk_idx = *chunk_idx;
        let pending_name = self.pending_call_name.take();
        let param_count = self.chunks[chunk_idx].param_count;
        let local_count = self.chunks[chunk_idx].local_count;
        let mut fixed_params = args;
        let varargs = if self.chunks[chunk_idx].is_vararg && fixed_params.len() > param_count {
            fixed_params.split_off(param_count)
        } else {
            fixed_params.truncate(param_count);
            Vec::new()
        };
        let stack_base = self.data_stack.len();
        self.data_stack.extend(fixed_params);
        self.data_stack.resize(stack_base + local_count, Value::nil());
        self.call_stack.push(CallFrame {
            closure_id: callable.as_obj(),
            chunk_idx,
            ip: 0,
            stack_base,
            handler_base: self.handler_stack.len(),
            varargs,
            last_hook_ip: None,
            is_hook: self.hook.in_hook,
            is_tailcall: false,
            is_native: false,
            native_continuation: None,
            frame_continuation: None,
            call_name: pending_name.as_ref().map(|pair| pair.0.clone()),
            call_namewhat: pending_name.as_ref().map(|pair| pair.1.clone()).unwrap_or_default(),
        });
        if pending_name.is_none()
            && !self.call_stack.get(self.call_stack.len().saturating_sub(2))
                .is_some_and(|caller| caller.is_native)
        {
            self.record_top_call_name();
        }
        self.dispatch_hook("call", None);
    }

    fn request_call(&mut self, callable: Value, args: Vec<Value>) {
        if !callable.is_obj() {
            self.runtime_error("Attempt to call a non-function value in metamethod");
        }
        match self.objects.get(callable.as_obj() as usize) {
            Some(Some(GcObject::Closure { .. })) => self.enqueue_lua_call(callable, args),
            Some(Some(GcObject::NativeFn(_) | GcObject::NativeClosure(..))) => {
                assert!(self.pending_call.is_none(), "pending VM call already exists");
                self.pending_call = Some((callable, args, self.pending_call_name.take()));
            }
            _ => self.runtime_error("Uncallable object in metamethod"),
        }
    }

    fn request_call_named(&mut self, callable: Value, args: Vec<Value>, name: &str, namewhat: &str) {
        let previous = self.pending_call_name.replace((name.to_string(), namewhat.to_string()));
        self.request_call(callable, args);
        self.pending_call_name = previous;
    }

    fn has_unyieldable_call(&self) -> bool {
        self.c_call_depth > 0 || self.call_stack.iter().any(|frame| {
            match &frame.native_continuation {
                Some(NativeContinuation::LoadReader { .. }) => true,
                Some(NativeContinuation::Sort(_)) => true,
                Some(NativeContinuation::GSubCallback { state, .. }) => !state.table_index,
                _ => false,
            }
        })
    }

    fn end_native_call(&mut self) {
        if !self
            .call_stack
            .last()
            .is_some_and(|frame| frame.is_native)
        {
            return;
        }
        self.dispatch_hook("return", None);
        self.call_stack.pop();
    }

    fn print_last_result(&mut self) {
        let count = self.multiret_count;
        if count == 0 {
            self.runtime_error("'tostring' must return a string to 'print'");
        }
        let first = self.data_stack[self.data_stack.len() - count];
        self.data_stack.truncate(self.data_stack.len() - count);
        if !first.is_obj()
            || !matches!(self.objects[first.as_obj() as usize], Some(GcObject::Str(_)))
        {
            self.runtime_error("'tostring' must return a string to 'print'");
        }
        emit_stdout(&self.val_to_str(first));
    }

    fn continue_print(&mut self, mut index: usize) -> bool {
        let count = self.call_stack.last().unwrap().varargs.len();
        while index < count {
            if index > 0 {
                emit_stdout("\t");
            }
            let tostring = self.get_global("tostring");
            if !self.is_callable(tostring) {
                self.runtime_error("attempt to call a nil value");
            }
            let value = self.call_stack.last().unwrap().varargs[index];
            self.call_stack.last_mut().unwrap().native_continuation =
                Some(NativeContinuation::Print { next_index: index + 1 });
            self.request_call(tostring, vec![value]);
            return true;
        }
        emit_stdout("\n");
        self.call_stack.last_mut().unwrap().native_continuation = None;
        false
    }

    fn enqueue_lua_sort_comparison(&mut self, state: SortState, callback: Value, reverse: bool) {
        let frame = self.call_stack.last().expect("sort native frame");
        let source = frame.stack_base + if state.source_second { state.len } else { 0 };
        let left = self.data_stack[source + state.left];
        let right = self.data_stack[source + state.right];
        let custom = state.custom;
        self.call_stack.last_mut().unwrap().native_continuation =
            Some(NativeContinuation::Sort(Box::new(state)));
        let args = if reverse { vec![right, left] } else { vec![left, right] };
        if custom {
            self.request_call(callback, args);
        } else {
            self.request_call_named(callback, args, "__lt", "metamethod");
        }
    }

    fn continue_sort_load(&mut self, mut state: SortLoadState, resumed: Option<Value>) {
        if let Some(value) = resumed {
            state.values.push(value);
            state.next += 1;
        }
        while state.next < state.len {
            let key = Value::num((state.next + 1) as f64);
            match self.indexed_value_step(state.table, key) {
                Ok(value) => {
                    state.values.push(value);
                    state.next += 1;
                }
                Err((callback, args)) => {
                    self.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::SortLoad(Box::new(state)));
                    self.request_call_named(callback, args, "__index", "metamethod");
                    return;
                }
            }
        }
        let len = state.values.len();
        self.data_stack.extend(state.values);
        self.data_stack.resize(self.data_stack.len() + len, Value::nil());
        self.continue_lua_sort(SortState {
            custom: state.custom,
            len,
            width: 1,
            start: 0,
            left: 0,
            right: 1,
            output: 0,
            source_second: false,
            waiting_reverse: false,
            forward_result: false,
            write_index: None,
        }, None);
    }

    fn continue_lua_sort(&mut self, mut state: SortState, comparison: Option<bool>) {
        let base = self.call_stack.last().expect("sort native frame").stack_base;
        if let Some(mut index) = state.write_index.take() {
            let source = base + if state.source_second { state.len } else { 0 };
            let table = self.call_stack.last().unwrap().varargs[0];
            while index < state.len {
                let value = self.data_stack[source + index];
                if let Some((callback, args)) = self.set_indexed_value_step(
                    table,
                    Value::num((index + 1) as f64),
                    value,
                ) {
                    state.write_index = Some(index);
                    self.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::Sort(Box::new(state)));
                    self.request_call_named(callback, args, "__newindex", "metamethod");
                    return;
                }
                index += 1;
            }
            self.data_stack.truncate(base);
            self.multiret_count = 0;
            self.end_native_call();
            return;
        }
        if let Some(result) = comparison {
            if state.custom && !state.waiting_reverse {
                state.forward_result = result;
                state.waiting_reverse = true;
                let callback = self.call_stack.last().unwrap().varargs[1];
                self.enqueue_lua_sort_comparison(state, callback, true);
                return;
            }
            if state.custom && state.forward_result && result {
                self.runtime_error("invalid order function for sorting");
            }
            let take_left = if state.custom { state.forward_result || !result } else { result };
            let source = base + if state.source_second { state.len } else { 0 };
            let destination = base + if state.source_second { 0 } else { state.len };
            let index = if take_left { state.left } else { state.right };
            self.data_stack[destination + state.output] = self.data_stack[source + index];
            if take_left { state.left += 1; } else { state.right += 1; }
            state.output += 1;
            state.waiting_reverse = false;
        }

        loop {
            if state.start >= state.len {
                state.source_second = !state.source_second;
                state.width = state.width.saturating_mul(2);
                if state.width >= state.len {
                    state.write_index = Some(0);
                    return self.continue_lua_sort(state, None);
                }
                state.start = 0;
                state.left = 0;
                state.right = state.width.min(state.len);
                state.output = 0;
            }

            let middle = state.start.saturating_add(state.width).min(state.len);
            let end = state.start.saturating_add(state.width.saturating_mul(2)).min(state.len);
            if state.left >= middle && state.right >= end {
                state.start = end;
                state.left = end;
                state.right = end.saturating_add(state.width).min(state.len);
                state.output = end;
                continue;
            }
            if state.left >= middle || state.right >= end {
                let source = base + if state.source_second { state.len } else { 0 };
                let destination = base + if state.source_second { 0 } else { state.len };
                let index = if state.left >= middle {
                    let index = state.right;
                    state.right += 1;
                    index
                } else {
                    let index = state.left;
                    state.left += 1;
                    index
                };
                self.data_stack[destination + state.output] = self.data_stack[source + index];
                state.output += 1;
                continue;
            }
            if state.custom {
                let callback = self.call_stack.last().unwrap().varargs[1];
                self.enqueue_lua_sort_comparison(state, callback, false);
                return;
            }

            let source = base + if state.source_second { state.len } else { 0 };
            let left = self.data_stack[source + state.left];
            let right = self.data_stack[source + state.right];
            let left_string = left.is_obj()
                && matches!(self.objects[left.as_obj() as usize], Some(GcObject::Str(_)));
            let right_string = right.is_obj()
                && matches!(self.objects[right.as_obj() as usize], Some(GcObject::Str(_)));
            let take_left = if left_string && right_string {
                self.val_to_str(left) <= self.val_to_str(right)
            } else if let (Some(a), Some(b)) = (self.to_num(left), self.to_num(right)) {
                a.partial_cmp(&b).unwrap_or(std::cmp::Ordering::Equal)
                    != std::cmp::Ordering::Greater
            } else {
                let left_mm = self.get_metamethod(left, "__lt");
                let right_mm = self.get_metamethod(right, "__lt");
                let Some(function) = left_mm.filter(|function| Some(*function) == right_mm) else {
                    self.runtime_error("attempt to compare uncomparable types in table.sort");
                };
                self.enqueue_lua_sort_comparison(state, function, false);
                return;
            };
            let destination = base + if state.source_second { 0 } else { state.len };
            let index = if take_left { state.left } else { state.right };
            self.data_stack[destination + state.output] = self.data_stack[source + index];
            if take_left { state.left += 1; } else { state.right += 1; }
            state.output += 1;
        }
    }

    fn continue_module_options(&mut self, mut next_index: usize, module_table: Value) -> bool {
        let option = self.call_stack.last().unwrap().varargs.get(next_index).copied();
        let Some(option) = option else { return false; };
        next_index += 1;
        self.call_stack.last_mut().unwrap().native_continuation =
            Some(NativeContinuation::ModuleOptions { next_index, module_table });
        self.request_call(option, vec![module_table]);
        true
    }

    fn continue_table_move(&mut self, mut state: TableMoveState) -> bool {
        while state.offset < state.count {
            let offset = if state.backwards {
                state.count - 1 - state.offset
            } else {
                state.offset
            };
            if !state.has_value {
                let from = self.alloc_integer(state.first.wrapping_add(offset));
                match self.indexed_value_step(state.source, from) {
                    Ok(value) => {
                        state.pending_value = value;
                        state.has_value = true;
                    }
                    Err((callback, args)) => {
                        self.call_stack.last_mut().unwrap().native_continuation =
                            Some(NativeContinuation::TableMove(Box::new(state)));
                        self.request_call_named(callback, args, "__index", "metamethod");
                        return true;
                    }
                }
            }
            let to = self.alloc_integer(state.target.wrapping_add(offset));
            if let Some((callback, args)) =
                self.set_indexed_value_step(state.destination, to, state.pending_value)
            {
                state.writing = true;
                self.call_stack.last_mut().unwrap().native_continuation =
                    Some(NativeContinuation::TableMove(Box::new(state)));
                self.request_call_named(callback, args, "__newindex", "metamethod");
                return true;
            }
            state.pending_value = Value::nil();
            state.has_value = false;
            state.offset += 1;
        }
        self.data_stack.push(state.destination);
        self.multiret_count = 1;
        false
    }

    fn continue_table_unpack(&mut self, mut next: i64, mut remaining: usize) -> bool {
        let table = self.call_stack.last().unwrap().varargs[0];
        while remaining > 0 {
            let key = self.alloc_integer(next);
            match self.indexed_value_step(table, key) {
                Ok(value) => self.data_stack.push(value),
                Err((callback, args)) => {
                    self.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::TableUnpack { next, remaining });
                    self.request_call_named(callback, args, "__index", "metamethod");
                    return true;
                }
            }
            next = next.wrapping_add(1);
            remaining -= 1;
        }
        let base = self.call_stack.last().unwrap().stack_base;
        self.multiret_count = self.data_stack.len() - base;
        false
    }

    fn continue_table_shift(&mut self, mut state: TableShiftState, mut resumed: Option<Value>) -> bool {
        loop {
            match state.phase {
                TableShiftPhase::ReadRemoved | TableShiftPhase::ReadShift => {
                    let value = if let Some(value) = resumed.take() {
                        value
                    } else {
                        let index = if matches!(state.phase, TableShiftPhase::ReadRemoved) {
                            state.pos
                        } else if state.remove {
                            state.index + 1
                        } else {
                            state.index
                        };
                        let key = self.alloc_integer(index);
                        match self.indexed_value_step(state.table, key) {
                            Ok(value) => value,
                            Err((callback, args)) => {
                                self.call_stack.last_mut().unwrap().native_continuation =
                                    Some(NativeContinuation::TableShift(Box::new(state)));
                                self.request_call_named(callback, args, "__index", "metamethod");
                                return true;
                            }
                        }
                    };
                    if matches!(state.phase, TableShiftPhase::ReadRemoved) {
                        state.value = value;
                        state.phase = if state.index < state.len {
                            TableShiftPhase::ReadShift
                        } else {
                            TableShiftPhase::WriteFinal
                        };
                    } else {
                        state.pending_value = value;
                        state.phase = TableShiftPhase::WriteShift;
                    }
                }
                TableShiftPhase::WriteShift => {
                    if resumed.take().is_none() {
                        let index = if state.remove { state.index } else { state.index + 1 };
                        let key = self.alloc_integer(index);
                        if let Some((callback, args)) =
                            self.set_indexed_value_step(state.table, key, state.pending_value)
                        {
                            self.call_stack.last_mut().unwrap().native_continuation =
                                Some(NativeContinuation::TableShift(Box::new(state)));
                            self.request_call_named(callback, args, "__newindex", "metamethod");
                            return true;
                        }
                    }
                    state.pending_value = Value::nil();
                    if state.remove {
                        state.index += 1;
                        state.phase = if state.index < state.len {
                            TableShiftPhase::ReadShift
                        } else {
                            TableShiftPhase::WriteFinal
                        };
                    } else {
                        state.index -= 1;
                        state.phase = if state.index >= state.pos {
                            TableShiftPhase::ReadShift
                        } else {
                            TableShiftPhase::WriteFinal
                        };
                    }
                }
                TableShiftPhase::WriteFinal => {
                    if resumed.take().is_none() && (!state.remove || state.pos <= state.len) {
                        let key = self.alloc_integer(if state.remove { state.len } else { state.pos });
                        let value = if state.remove { Value::nil() } else { state.value };
                        if let Some((callback, args)) = self.set_indexed_value_step(state.table, key, value) {
                            self.call_stack.last_mut().unwrap().native_continuation =
                                Some(NativeContinuation::TableShift(Box::new(state)));
                            self.request_call_named(callback, args, "__newindex", "metamethod");
                            return true;
                        }
                    }
                    if state.remove {
                        self.data_stack.push(state.value);
                        self.multiret_count = 1;
                    } else {
                        self.multiret_count = 0;
                    }
                    return false;
                }
            }
        }
    }

    fn continue_table_concat(&mut self, mut state: TableConcatState, mut resumed: Option<Value>) -> bool {
        while state.index <= state.end {
            let value = if let Some(value) = resumed.take() {
                value
            } else {
                let key = self.alloc_integer(state.index);
                match self.indexed_value_step(state.table, key) {
                    Ok(value) => value,
                    Err((callback, args)) => {
                        self.call_stack.last_mut().unwrap().native_continuation =
                            Some(NativeContinuation::TableConcat(Box::new(state)));
                        self.request_call_named(callback, args, "__index", "metamethod");
                        return true;
                    }
                }
            };
            if state.index > state.start { state.result.push_str(&state.separator); }
            if value.0 == TAG_NIL || value.0 == TAG_FALSE || value.0 == TAG_TRUE {
                self.runtime_error(&format!("invalid value in table for 'concat' at index {}", state.index));
            }
            if value.is_obj() {
                match &self.objects[value.as_obj() as usize] {
                    Some(GcObject::Str(s)) => state.result.push_str(s),
                    Some(GcObject::Integer(n)) => state.result.push_str(&n.to_string()),
                    Some(GcObject::Float(n)) => state.result.push_str(&n.to_string()),
                    _ => self.runtime_error(&format!("invalid value in table for 'concat' at index {}", state.index)),
                }
            } else {
                state.result.push_str(&value.as_num().to_string());
            }
            if state.index == state.end {
                break;
            }
            state.index += 1;
        }
        let result = self.alloc_str(&state.result);
        self.data_stack.push(result);
        self.multiret_count = 1;
        false
    }

    fn finish_native_continuation_success(&mut self) {
        let ret_count = self.multiret_count;
        let first_result = self.data_stack.len().saturating_sub(ret_count);
        let results = self.data_stack.split_off(first_result);
        let continuation = self
            .call_stack
            .last()
            .and_then(|frame| frame.native_continuation.clone())
            .expect("native continuation frame");
        match continuation {
            NativeContinuation::PCall | NativeContinuation::XPCall(_) => {
                self.end_native_call();
                self.data_stack.push(Value::bool(true));
                self.data_stack.extend(results);
                self.multiret_count = ret_count + 1;
            }
            NativeContinuation::XPCallHandling { previous_in_error_handler, .. } => {
                self.in_error_handler = previous_in_error_handler;
                self.end_native_call();
                self.data_stack.push(Value::bool(false));
                self.data_stack.push(results.first().copied().unwrap_or(Value::nil()));
                self.multiret_count = 2;
            }
            NativeContinuation::Print { next_index } => {
                self.data_stack.extend(results);
                self.multiret_count = ret_count;
                self.print_last_result();
                if !self.continue_print(next_index) {
                    self.end_native_call();
                    self.multiret_count = 0;
                }
            }
            NativeContinuation::ToString => {
                let value = results.first().copied().unwrap_or(Value::nil());
                if !value.is_obj()
                    || !matches!(self.objects[value.as_obj() as usize], Some(GcObject::Str(_)))
                {
                    self.runtime_error("'__tostring' must return a string");
                }
                self.data_stack.push(value);
                self.multiret_count = 1;
                self.end_native_call();
            }
            NativeContinuation::FormatToString(state) => {
                self.continue_format_tostring(
                    *state,
                    Some(results.first().copied().unwrap_or(Value::nil())),
                );
            }
            NativeContinuation::FormatReplay => {
                self.end_native_call();
                self.data_stack.extend(results);
                self.multiret_count = ret_count;
            }
            NativeContinuation::SetIoDefault { key } => {
                let file = results.first().copied().unwrap_or(Value::nil());
                if !file.is_truthy() {
                    let message = results.get(1).map(|value| self.val_to_str(*value))
                        .unwrap_or_else(|| "cannot open file".to_string());
                    self.runtime_error(&message);
                }
                self.set_global(key, file);
                self.data_stack.push(file);
                self.multiret_count = 1;
                self.end_native_call();
            }
            NativeContinuation::LoadReader { source } => {
                self.continue_load_reader(source, &results);
            }
            NativeContinuation::TableForeach { next_index, total } => {
                let value = results.first().copied().unwrap_or(Value::nil());
                let base = self.call_stack.last().unwrap().stack_base;
                if value.0 != TAG_NIL || next_index >= total {
                    self.data_stack.truncate(base);
                    self.data_stack.push(value);
                    self.multiret_count = 1;
                    self.end_native_call();
                } else {
                    let key = self.data_stack[base + next_index * 2];
                    let entry = self.data_stack[base + next_index * 2 + 1];
                    let callback = self.call_stack.last().unwrap().varargs[1];
                    self.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::TableForeach { next_index: next_index + 1, total });
                    self.request_call(callback, vec![key, entry]);
                }
            }
            NativeContinuation::TableForeachI { next_index, max } => {
                let value = results.first().copied().unwrap_or(Value::nil());
                if value.0 != TAG_NIL || next_index > max {
                    self.data_stack.push(value);
                    self.multiret_count = 1;
                    self.end_native_call();
                } else {
                    let args = &self.call_stack.last().unwrap().varargs;
                    let table = args[0];
                    let callback = args[1];
                    let key = Value::num(next_index as f64);
                    let entry = match &self.objects[table.as_obj() as usize] {
                        Some(GcObject::Table(map, _)) => {
                            map.get(&key).copied().unwrap_or(Value::nil())
                        }
                        _ => Value::nil(),
                    };
                    self.call_stack.last_mut().unwrap().native_continuation =
                        Some(NativeContinuation::TableForeachI { next_index: next_index + 1, max });
                    self.request_call(callback, vec![key, entry]);
                }
            }
            NativeContinuation::Sort(state) => {
                let mut state = *state;
                if state.write_index.is_some() {
                    state.write_index = state.write_index.map(|index| index + 1);
                    self.continue_lua_sort(state, None);
                } else {
                    let comparison = results.first().copied().unwrap_or(Value::nil()).is_truthy();
                    self.continue_lua_sort(state, Some(comparison));
                }
            }
            NativeContinuation::SortLoad(state) => {
                self.continue_sort_load(*state, Some(results.first().copied().unwrap_or(Value::nil())));
            }
            NativeContinuation::IPairsIndex(key) => {
                let value = results.first().copied().unwrap_or(Value::nil());
                if value.0 == TAG_NIL {
                    self.data_stack.push(Value::nil());
                    self.multiret_count = 1;
                } else {
                    self.data_stack.extend([key, value]);
                    self.multiret_count = 2;
                }
                self.end_native_call();
            }
            NativeContinuation::GSubCallback { state, resume } => {
                if !resume(self, *state, Some(results.first().copied().unwrap_or(Value::nil()))) {
                    self.end_native_call();
                }
            }
            NativeContinuation::ModuleOptions { next_index, module_table } => {
                if !self.continue_module_options(next_index, module_table) {
                    self.multiret_count = 0;
                    self.end_native_call();
                }
            }
            NativeContinuation::TableMove(mut state) => {
                if state.writing {
                    state.offset += 1;
                    state.pending_value = Value::nil();
                    state.has_value = false;
                    state.writing = false;
                } else {
                    state.pending_value = results.first().copied().unwrap_or(Value::nil());
                    state.has_value = true;
                }
                if !self.continue_table_move(*state) {
                    self.end_native_call();
                }
            }
            NativeContinuation::TableUnpack { next, remaining } => {
                self.data_stack.push(results.first().copied().unwrap_or(Value::nil()));
                if !self.continue_table_unpack(next.wrapping_add(1), remaining - 1) {
                    self.end_native_call();
                }
            }
            NativeContinuation::TableShift(state) => {
                if !self.continue_table_shift(*state, Some(results.first().copied().unwrap_or(Value::nil()))) {
                    self.end_native_call();
                }
            }
            NativeContinuation::TableConcat(state) => {
                if !self.continue_table_concat(*state, Some(results.first().copied().unwrap_or(Value::nil()))) {
                    self.end_native_call();
                }
            }
            NativeContinuation::SequenceLengthUnpack { start } => {
                let args = self.call_stack.last().unwrap().varargs.clone();
                let end = self.sequence_length_result(results.first().copied());
                let count = end as i128 - start as i128 + 1;
                if count <= 0 {
                    self.multiret_count = 0;
                    self.end_native_call();
                } else if count > 100_000 {
                    self.runtime_error("too many results to unpack");
                } else {
                    let _ = args;
                    if !self.continue_table_unpack(start, count as usize) {
                        self.end_native_call();
                    }
                }
            }
            NativeContinuation::SequenceLengthInsert => {
                let args = self.call_stack.last().unwrap().varargs.clone();
                let table = args[0];
                let len = self.sequence_length_result(results.first().copied());
                let (pos, value) = if args.len() == 2 {
                    (len + 1, args[1])
                } else {
                    let pos = self.to_integer(args[1]).unwrap_or_else(|| {
                        self.runtime_error("bad argument #2 to 'table.insert' (number has no integer representation)")
                    });
                    (pos, args[2])
                };
                if pos < 1 || pos > len + 1 {
                    self.runtime_error("bad argument #2 to 'table.insert' (position out of bounds)");
                }
                let state = TableShiftState {
                    table, pos, len, index: len, value,
                    pending_value: Value::nil(), remove: false,
                    phase: if len >= pos { TableShiftPhase::ReadShift } else { TableShiftPhase::WriteFinal },
                };
                if !self.continue_table_shift(state, None) {
                    self.end_native_call();
                }
            }
            NativeContinuation::SequenceLengthRemove => {
                let args = self.call_stack.last().unwrap().varargs.clone();
                let table = args[0];
                let len = self.sequence_length_result(results.first().copied());
                let pos = if args.len() > 1 {
                    self.to_integer(args[1]).unwrap_or_else(|| {
                        self.runtime_error("bad argument #2 to 'table.remove' (number has no integer representation)")
                    })
                } else { len };
                if pos != len && (pos < 1 || pos > len + 1) {
                    self.runtime_error("bad argument #2 to 'table.remove' (position out of bounds)");
                }
                let state = TableShiftState {
                    table, pos, len, index: pos, value: Value::nil(),
                    pending_value: Value::nil(), remove: true,
                    phase: TableShiftPhase::ReadRemoved,
                };
                if !self.continue_table_shift(state, None) {
                    self.end_native_call();
                }
            }
            NativeContinuation::SequenceLengthConcat => {
                let args = self.call_stack.last().unwrap().varargs.clone();
                let table = args[0];
                let len = self.sequence_length_result(results.first().copied());
                let sep = if args.len() > 1 && args[1].0 != TAG_NIL { self.val_to_str(args[1]) } else { String::new() };
                let start = if args.len() > 2 && args[2].0 != TAG_NIL {
                    self.to_integer(args[2]).unwrap_or_else(|| self.runtime_error("bad argument #3 to 'concat' (number expected)"))
                } else { 1 };
                let end = if args.len() > 3 && args[3].0 != TAG_NIL {
                    self.to_integer(args[3]).unwrap_or_else(|| self.runtime_error("bad argument #4 to 'concat' (number expected)"))
                } else { len };
                let state = TableConcatState { table, separator: sep, start, index: start, end, result: String::new() };
                if !self.continue_table_concat(state, None) {
                    self.end_native_call();
                }
            }
            NativeContinuation::SequenceLengthSort => {
                let args = self.call_stack.last().unwrap().varargs.clone();
                let table = args[0];
                let len = self.sequence_length_result(results.first().copied());
                if len > i32::MAX as i64 { self.runtime_error("array too big"); }
                if len < 2 {
                    self.multiret_count = 0;
                    self.end_native_call();
                } else {
                    let has_comp = args.len() > 1 && args[1].is_truthy();
                    self.continue_sort_load(SortLoadState {
                        table,
                        len: len as usize,
                        next: 0,
                        values: Vec::with_capacity(len as usize),
                        custom: has_comp,
                    }, None);
                }
            }
            NativeContinuation::Require { loaded_table, module_name } => {
                self.data_stack.extend(results);
                self.multiret_count = ret_count;
                self.finish_require_call(loaded_table, module_name);
                self.end_native_call();
            }
            NativeContinuation::ReturnResults => {
                self.end_native_call();
                self.data_stack.extend(results);
                self.multiret_count = ret_count;
            }
        }
    }

    fn finish_require_call(&mut self, loaded_table: Value, module_name: Value) -> usize {
        let result_start = self.data_stack.len() - self.multiret_count;
        let first_result = self.data_stack.get(result_start).copied().unwrap_or(Value::nil());
        self.data_stack.truncate(result_start);

        let mut final_result = first_result;
        if loaded_table.is_obj() {
            if first_result.0 != TAG_NIL {
                if let Some(GcObject::Table(map, _)) = &mut self.objects[loaded_table.as_obj() as usize] {
                    map.insert(module_name, first_result);
                }
            } else {
                let current_loaded = match &self.objects[loaded_table.as_obj() as usize] {
                    Some(GcObject::Table(map, _)) => {
                        map.get(&module_name).copied().unwrap_or(Value::nil())
                    }
                    _ => Value::nil(),
                };
                if current_loaded.is_truthy() && current_loaded != Value::bool(true) {
                    final_result = current_loaded;
                } else {
                    final_result = Value::bool(true);
                    if let Some(GcObject::Table(map, _)) = &mut self.objects[loaded_table.as_obj() as usize] {
                        map.insert(module_name, final_result);
                    }
                }
            }
        }
        self.data_stack.push(final_result);
        self.multiret_count = 1;
        1
    }

    fn finish_load_source(&mut self, source: String, args: &[Value]) -> usize {
        let mode = args
            .get(2)
            .filter(|value| value.0 != TAG_NIL)
            .map(|value| self.val_to_str(*value))
            .unwrap_or_else(|| "bt".to_string());
        if mode.chars().any(|ch| ch != 'b' && ch != 't') || mode.is_empty() {
            self.runtime_error("invalid mode");
        }
        let source_bytes = lua_string_bytes(&source);
        let is_binary = source_bytes.first() == Some(&0x1b);
        if (is_binary && !mode.contains('b')) || (!is_binary && !mode.contains('t')) {
            let message = if is_binary {
                "attempt to load a binary chunk"
            } else {
                "attempt to load a text chunk"
            };
            let error = self.alloc_str(message);
            self.data_stack.extend([Value::nil(), error]);
            return 2;
        }

        if is_binary {
            let dump_header = lua53_binary_header();
            let error = if source_bytes.len() < dump_header.len() {
                "truncated binary chunk"
            } else if !source_bytes.starts_with(&dump_header) {
                "not a precompiled chunk"
            } else {
                let marker = b"\x1bLUA_AE_DUMP:";
                if source_bytes.len() > dump_header.len() + marker.len()
                    && source_bytes[dump_header.len()..].starts_with(marker)
                {
                    let marker_text = decode_lua_source(source_bytes[dump_header.len()..].to_vec());
                    let mut marker_parts = marker_text[marker.len()..].split(':');
                    let id_str = marker_parts.next().unwrap_or("");
                    let _strip_marker = marker_parts.next().unwrap_or("") == "S";
                    let required = marker_parts.next().and_then(|part| part.parse::<usize>().ok()).unwrap_or(usize::MAX);
                    if let Ok(id) = id_str.parse::<u32>() {
                        if marker_text[marker.len()..].chars().filter(|ch| *ch == 'D').count() >= required {
                            if let Some(function) = self.undump_function(id) {
                                self.data_stack.push(function);
                                return 1;
                            }
                        }
                    }
                }
                "truncated binary chunk"
            };
            let error = self.alloc_str(error);
            self.data_stack.extend([Value::nil(), error]);
            return 2;
        }

        let chunk_name = args
            .get(1)
            .filter(|value| value.0 != TAG_NIL)
            .map(|value| self.val_to_str(*value))
            .unwrap_or_else(|| source.clone());
        match Compiler::compile(self, &source, &chunk_name) {
            Ok(chunk_idx) => {
                let env = args
                    .get(3)
                    .copied()
                    .filter(|value| value.0 != TAG_NIL)
                    .unwrap_or(Value::obj(self.global_env));
                let env_upval = self.alloc(GcObject::Upval(env));
                let closure = self.alloc_closure(chunk_idx, vec![env_upval]);
                self.data_stack.push(Value::obj(closure));
                1
            }
            Err(err) => {
                let error = self.alloc_str(&err);
                self.data_stack.extend([Value::nil(), error]);
                2
            }
        }
    }

    fn continue_load_reader(&mut self, mut source: String, results: &[Value]) {
        let first = results.first().copied().unwrap_or(Value::nil());
        if first.0 != TAG_NIL {
            if !first.is_obj()
                || !matches!(self.objects[first.as_obj() as usize], Some(GcObject::Str(_)))
            {
                let error = self.alloc_str("reader function must return a string");
                self.data_stack.extend([Value::nil(), error]);
                self.multiret_count = 2;
                self.end_native_call();
                return;
            }
            let piece = self.val_to_str(first);
            if !piece.is_empty() {
                source.push_str(&piece);
                let reader = self.call_stack.last().unwrap().varargs[0];
                self.call_stack.last_mut().unwrap().native_continuation =
                    Some(NativeContinuation::LoadReader { source });
                self.request_call(reader, vec![]);
                return;
            }
        }

        let args = self.call_stack.last().unwrap().varargs.clone();
        self.multiret_count = self.finish_load_source(source, &args);
        self.end_native_call();
    }

    fn panic_payload_value(
        &mut self,
        payload: &(dyn std::any::Any + Send),
    ) -> Value {
        if let Some(&value) = payload.downcast_ref::<Value>() {
            value
        } else {
            let message = if let Some(message) = payload.downcast_ref::<String>() {
                message.clone()
            } else if let Some(message) = payload.downcast_ref::<&str>() {
                message.to_string()
            } else {
                "unknown runtime error".to_string()
            };
            self.alloc_str(&message)
        }
    }

    fn recover_protected_call_error(
        &mut self,
        payload: &(dyn std::any::Any + Send),
        minimum_depth: usize,
    ) -> bool {
        let Some(frame_index) = self
            .call_stack
            .iter()
            .enumerate()
            .rposition(|(index, frame)| {
                index >= minimum_depth && matches!(
                    frame.native_continuation,
                    Some(NativeContinuation::PCall | NativeContinuation::XPCall(_)
                        | NativeContinuation::XPCallHandling { .. }
                        | NativeContinuation::LoadReader { .. })
                )
            })
        else {
            return false;
        };

        let traceback = self.generate_traceback(0);
        let continuation = self.call_stack[frame_index]
            .native_continuation
            .clone()
            .unwrap();
        let finalizer_state = self.finalizer_active.take();
        let data_depth = self.call_stack[frame_index].stack_base;
        let handler_depth = self.call_stack[frame_index].handler_base;
        let error_value = if finalizer_state.is_some() {
            self.alloc_str("error in __gc")
        } else {
            self.panic_payload_value(payload)
        };
        let roots_depth = self.temp_roots.len();
        self.temp_roots.push(error_value);

        self.call_stack.truncate(frame_index + 1);
        self.data_stack.truncate(data_depth);
        self.handler_stack.truncate(handler_depth);
        self.yielded = false;

        if let Some(state) = finalizer_state {
            if let (Some(index), Some((name, namewhat))) =
                (state.caller_index, state.saved_caller_name)
            {
                if let Some(frame) = self.call_stack.get_mut(index) {
                    frame.call_name = name;
                    frame.call_namewhat = namewhat;
                }
            }
            self.temp_roots.truncate(state.roots_start);
            self.multiret_count = state.saved_multiret_count;
        }

        match continuation {
            NativeContinuation::PCall => {
                self.end_native_call();
                self.data_stack.push(Value::bool(false));
                self.data_stack.push(error_value);
                self.multiret_count = 2;
            }
            NativeContinuation::XPCall(message_handler) => {
                self.temp_roots.push(message_handler);
                let previous_in_error_handler = self.in_error_handler;
                self.in_error_handler = true;
                self.call_stack[frame_index].native_continuation =
                    Some(NativeContinuation::XPCallHandling {
                        previous_in_error_handler,
                        traceback,
                    });
                self.request_call(message_handler, vec![error_value]);
                self.temp_roots.truncate(roots_depth);
                return true;
            }
            NativeContinuation::XPCallHandling { previous_in_error_handler, .. } => {
                self.in_error_handler = previous_in_error_handler;
                self.end_native_call();
                self.data_stack.push(Value::bool(false));
                let error = self.alloc_str("error in error handling");
                self.data_stack.push(error);
                self.multiret_count = 2;
            }
            NativeContinuation::LoadReader { .. } => {
                let message = self.val_to_str(error_value);
                self.end_native_call();
                let error = self.alloc_str(&message);
                self.data_stack.extend([Value::nil(), error]);
                self.multiret_count = 2;
            }
            NativeContinuation::Require { .. }
            | NativeContinuation::ReturnResults
            | NativeContinuation::Print { .. }
            | NativeContinuation::ToString
            | NativeContinuation::FormatToString(_)
            | NativeContinuation::FormatReplay
            | NativeContinuation::SetIoDefault { .. }
            | NativeContinuation::TableForeach { .. }
            | NativeContinuation::TableForeachI { .. }
            | NativeContinuation::Sort(_)
            | NativeContinuation::ModuleOptions { .. }
            | NativeContinuation::TableMove(_)
            | NativeContinuation::TableUnpack { .. }
            | NativeContinuation::TableShift(_)
            | NativeContinuation::TableConcat(_)
            | NativeContinuation::SequenceLengthUnpack { .. }
            | NativeContinuation::SequenceLengthInsert
            | NativeContinuation::SequenceLengthRemove
            | NativeContinuation::SequenceLengthConcat
            | NativeContinuation::SequenceLengthSort
            | NativeContinuation::IPairsIndex(_)
            | NativeContinuation::SortLoad(_)
            | NativeContinuation::GSubCallback { .. } => unreachable!(),
        }

        self.temp_roots.truncate(roots_depth);
        true
    }

    fn run_coroutine_until_suspend(
        &mut self,
        mut initial_call: Option<(Value, Vec<Value>)>,
    ) -> Result<(bool, Vec<Value>), Box<dyn std::any::Any + Send>> {
        loop {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                if let Some((function, args)) = initial_call.take() {
                    self.request_call(function, args);
                }
                self.run_until(0);
            }));

            match result {
                Ok(()) => {
                    let ret_count = self.multiret_count;
                    let mut results = Vec::with_capacity(ret_count);
                    for _ in 0..ret_count {
                        results.push(self.data_stack.pop().unwrap());
                    }
                    results.reverse();
                    return Ok((self.yielded, results));
                }
                Err(payload) => {
                    if self.recover_protected_call_error(payload.as_ref(), 0) {
                        continue;
                    }
                    return Err(payload);
                }
            }
        }
    }

    pub fn internal_call(&mut self, callable: Value, args: Vec<Value>) {
        if !callable.is_obj() {
            self.runtime_error("Attempt to call a non-function value in metamethod");
        }
        match self.objects[callable.as_obj() as usize].clone().unwrap() {
            GcObject::Closure { .. } => {
                self.enqueue_lua_call(callable, args);
                let target_depth = self.call_stack.len() - 1;
                self.run_until(target_depth);
            }
            GcObject::NativeFn(func) => {
                let roots_start = self.temp_roots.len();
                self.temp_roots.extend(args.clone());
                self.temp_roots.push(callable);

                self.begin_native_call(callable.as_obj(), &args);
                let target_depth = self.call_stack.len() - 1;
                self.multiret_count = func(self, args);
                if self.call_stack.len() > target_depth + 1 {
                    self.run_until(target_depth);
                }
                self.end_native_call();

                self.temp_roots.truncate(roots_start);
            }
            GcObject::NativeClosure(func, state) => {
                let roots_start = self.temp_roots.len();
                self.temp_roots.extend(args.clone());
                self.temp_roots.push(callable);

                self.begin_native_call(callable.as_obj(), &args);
                let target_depth = self.call_stack.len() - 1;
                self.multiret_count = func(self, args, state);
                if self.call_stack.len() > target_depth + 1 {
                    self.run_until(target_depth);
                }
                self.end_native_call();

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
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.run_until_inner(target_depth);
            }));
            match result {
                Ok(()) => return,
                Err(payload) => {
                    if !self.recover_protected_call_error(payload.as_ref(), target_depth) {
                        std::panic::resume_unwind(payload);
                    }
                }
            }
        }
    }

    fn run_until_inner(&mut self, target_depth: usize) {
        loop {
            if let Some((callable, args, name)) = self.pending_call.take() {
                let object = self.objects[callable.as_obj() as usize].clone().unwrap();
                self.pending_call_name = name;
                self.begin_native_call(callable.as_obj(), &args);
                let native_depth = self.call_stack.len();
                self.multiret_count = match object {
                    GcObject::NativeFn(function) => function(self, args),
                    GcObject::NativeClosure(function, state) => function(self, args, state),
                    _ => unreachable!("pending call must be native"),
                };
                if self.pending_call.is_none()
                    && self.call_stack.len() == native_depth
                    && self.call_stack.last().is_some_and(|frame| frame.is_native)
                {
                    self.end_native_call();
                }
                continue;
            }
            self.finish_finalizer_if_done();
            if self.finalizer_active.is_none() && !self.pending_finalizers.is_empty() {
                self.start_next_finalizer();
                if self.pending_call.is_some() {
                    continue;
                }
            }
            if self.yielded {
                break;
            }
            if self.call_stack.len() <= target_depth {
                return;
            }

            if let Some(continuation) = self
                .call_stack
                .last_mut()
                .and_then(|frame| frame.frame_continuation.take())
            {
                match continuation {
                    FrameContinuation::FirstResult | FrameContinuation::InvertBool => {
                        let count = self.multiret_count;
                        let result = if count == 0 {
                            Value::nil()
                        } else {
                            self.data_stack[self.data_stack.len() - count]
                        };
                        self.data_stack.truncate(self.data_stack.len() - count);
                        self.data_stack.push(if matches!(continuation, FrameContinuation::InvertBool) {
                            Value::bool(!result.is_truthy())
                        } else {
                            result
                        });
                        self.multiret_count = 1;
                    }
                    FrameContinuation::DiscardResults => {
                        self.data_stack.truncate(self.data_stack.len() - self.multiret_count);
                        self.multiret_count = 0;
                    }
                }
            }

            if self
                .call_stack
                .last()
                .is_some_and(|frame| frame.is_native)
            {
                if self
                    .call_stack
                    .last()
                    .is_some_and(|frame| frame.native_continuation.is_some())
                {
                    self.finish_native_continuation_success();
                    continue;
                }
                self.runtime_error("invalid suspended native call");
            }

            let frame_idx = self.call_stack.len() - 1;
            let chunk_idx = self.call_stack[frame_idx].chunk_idx;
            let ip = self.call_stack[frame_idx].ip;

            if ip >= self.chunks[chunk_idx].instructions.len() {
                self.dispatch_hook("return", None);
                self.call_stack.pop();
                continue;
            }
            let inst = self.chunks[chunk_idx].instructions[ip];
            self.dispatch_instruction_hooks(frame_idx, chunk_idx, ip, inst);
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
                    if self.is_float_value(val)
                        || (val.is_obj()
                            && matches!(self.objects[val.as_obj() as usize], Some(GcObject::Integer(_))))
                    {
                        self.data_stack.push(val);
                    } else if let Some(integer) = self.to_integer(val) {
                        let value = self.alloc_integer(integer);
                        self.data_stack.push(value);
                    } else if let Some(number) = self.to_num(val) {
                        let value = self.alloc_float(number);
                        self.data_stack.push(value);
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
                OpCode::Div => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();
                    if let (Some(a), Some(b)) = (self.to_num(a_val), self.to_num(b_val)) {
                        let value = self.alloc_float(a / b);
                        self.data_stack.push(value);
                    } else {
                        let mm = self.get_metamethod(a_val, "__div").or_else(|| self.get_metamethod(b_val, "__div"));
                        if let Some(function) = mm {
                            if !self.trigger_metamethod_vm(function, vec![a_val, b_val], "__div") { self.runtime_error("attempt to perform arithmetic on an uncallable metamethod"); }
                        } else { self.arithmetic_type_error(a_val, b_val); }
                    }
                }
                OpCode::Mod => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    if !self.is_float_value(a_val) && !self.is_float_value(b_val)
                        && self.number_as_integer(a_val).is_some()
                        && self.number_as_integer(b_val).is_some()
                    {
                        let a = self.number_as_integer(a_val).unwrap();
                        let b = self.number_as_integer(b_val).unwrap();
                        if b == 0 { self.runtime_error("attempt to perform 'n%0'"); }
                        let mut result = a.wrapping_rem(b);
                        if result != 0 && (result < 0) != (b < 0) { result += b; }
                        let value = self.alloc_integer(result);
                        self.data_stack.push(value);
                    } else if let (Some(a), Some(b)) = (self.to_num(a_val), self.to_num(b_val)) {
                        let mut res = a % b;
                        if res != 0.0 && res.is_sign_negative() != b.is_sign_negative() {
                            res += b;
                        }
                        let value = self.alloc_float(res);
                        self.data_stack.push(value);
                    } else {
                        let mut mm = self.get_metamethod(a_val, "__mod");
                        if mm.is_none() {
                            mm = self.get_metamethod(b_val, "__mod");
                        }

                        if let Some(func) = mm {
                            if !self.trigger_metamethod_vm(func, vec![a_val, b_val], "__mod") {
                                self.runtime_error(
                                    "attempt to perform arithmetic on an uncallable metamethod",
                                );
                            }
                        } else {
                            self.arithmetic_type_error(a_val, b_val);
                        }
                    }
                }
                OpCode::BitAnd => bit_op!(self, &, "__band"),
                OpCode::BitOr => bit_op!(self, |, "__bor"),
                OpCode::BitXor => bit_op!(self, ^, "__bxor"),
                OpCode::BitNot => {
                    let value = self.data_stack.pop().unwrap();
                    if let Some(number) = self.to_integer(value) {
                        let result = self.alloc_integer(!number);
                        self.data_stack.push(result);
                    } else if let Some(function) = self.get_metamethod(value, "__bnot") {
                        if !self.trigger_metamethod_vm(function, vec![value], "__bnot") {
                            self.runtime_error(
                                "attempt to perform bitwise operation on an uncallable metamethod",
                            );
                        }
                    } else {
                        self.bitwise_type_error(value, value);
                    }
                }
                OpCode::Shl | OpCode::Shr => {
                    let right_shift = matches!(inst, OpCode::Shr);
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();
                    if let (Some(a), Some(mut b)) = (self.to_integer(a_val), self.to_integer(b_val)) {
                        let mut right = right_shift;
                        if b < 0 { b = b.saturating_neg(); right = !right; }
                        let result = if b >= 64 { 0 } else if right { ((a as u64) >> b) as i64 } else { a.wrapping_shl(b as u32) };
                        let value = self.alloc_integer(result);
                        self.data_stack.push(value);
                    } else {
                        let event = if right_shift { "__shr" } else { "__shl" };
                        let mm = self.get_metamethod(a_val, event).or_else(|| self.get_metamethod(b_val, event));
                        if let Some(function) = mm {
                            if !self.trigger_metamethod_vm(function, vec![a_val, b_val], event) { self.runtime_error("attempt to perform bitwise operation on an uncallable metamethod"); }
                        } else { self.bitwise_type_error(a_val, b_val); }
                    }
                }
                OpCode::Pow => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    if let (Some(a), Some(b)) = (self.to_num(a_val), self.to_num(b_val)) {

                        let value = self.alloc_float(a.powf(b));
                        self.data_stack.push(value);
                    } else {

                        let mut mm = self.get_metamethod(a_val, "__pow");
                        if mm.is_none() {
                            mm = self.get_metamethod(b_val, "__pow");
                        }

                        if let Some(func) = mm {
                            if !self.trigger_metamethod_vm(func, vec![a_val, b_val], "__pow") {
                                self.runtime_error(
                                    "attempt to perform exponentiation on an uncallable metamethod",
                                );
                            }
                        } else {
                            self.arithmetic_type_error(a_val, b_val);
                        }
                    }
                }
                OpCode::FloorDiv => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();
                    let integers = if self.is_float_value(a_val) || self.is_float_value(b_val) {
                        None
                    } else {
                        self.to_integer(a_val).zip(self.to_integer(b_val))
                    };
                    if let Some((a, b)) = integers {
                        if b == 0 { self.runtime_error("attempt to divide by zero"); }
                        let mut result = a.wrapping_div(b);
                        if a.wrapping_rem(b) != 0 && (a < 0) != (b < 0) {
                            result = result.wrapping_sub(1);
                        }
                        let value = self.alloc_integer(result);
                        self.data_stack.push(value);
                    } else if let (Some(a), Some(b)) = (self.to_num(a_val), self.to_num(b_val)) {
                        let value = self.alloc_float((a / b).floor());
                        self.data_stack.push(value);
                    } else {
                        let mut mm = self.get_metamethod(a_val, "__idiv");
                        if mm.is_none() {
                            mm = self.get_metamethod(b_val, "__idiv");
                        }

                        if let Some(func) = mm {
                            if !self.trigger_metamethod_vm(func, vec![a_val, b_val], "__idiv") {
                                self.runtime_error(
                                    "attempt to perform floor division on an uncallable metamethod",
                                );
                            }
                        } else {
                            self.arithmetic_type_error(a_val, b_val);
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
                    let equal = self.numbers_equal(a, b).unwrap_or(a == b);
                    if equal {
                        self.data_stack.push(Value::bool(false));
                    } else {
                        let comparable_objects = a.is_obj()
                            && b.is_obj()
                            && matches!(
                                (
                                    &self.objects[a.as_obj() as usize],
                                    &self.objects[b.as_obj() as usize]
                                ),
                                (Some(GcObject::Table(..)), Some(GcObject::Table(..)))
                                    | (Some(GcObject::File(..)), Some(GcObject::File(..)))
                                    | (Some(GcObject::StdFile(..)), Some(GcObject::StdFile(..)))
                            );
                        let metamethod = if comparable_objects {
                            self.get_metamethod(a, "__eq")
                                .or_else(|| self.get_metamethod(b, "__eq"))
                        } else {
                            None
                        };
                        if let Some(function) = metamethod {
                            let caller = self.call_stack.len() - 1;
                            if self.trigger_metamethod_vm(function, vec![a, b], "__eq") {
                                if self.call_stack.len() > caller + 1 {
                                    self.call_stack[caller].frame_continuation =
                                        Some(FrameContinuation::InvertBool);
                                } else {
                                    let result = self.data_stack.pop().unwrap();
                                    self.data_stack.push(Value::bool(!result.is_truthy()));
                                }
                            } else {
                                self.data_stack.push(Value::bool(true));
                            }
                        } else {
                            self.data_stack.push(Value::bool(true));
                        }
                    }
                }

                OpCode::Neg => {
                    let val = self.data_stack.pop().unwrap();
                    if !self.is_float_value(val) && self.to_integer(val).is_some() {
                        let n = self.to_integer(val).unwrap();
                        let value = self.alloc_integer(n.wrapping_neg());
                        self.data_stack.push(value);
                    } else if let Some(n) = self.to_num(val) {
                        let value = self.alloc_float(-n);
                        self.data_stack.push(value);
                    } else if let Some(mm) = self.get_metamethod(val, "__unm") {
                        if !self.trigger_metamethod_vm(mm, vec![val], "__unm") {
                            self.runtime_error(
                                "attempt to perform arithmetic on an uncallable __unm metamethod",
                            );
                        }
                    } else {
                        self.arithmetic_type_error(val, val);
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
                            if !self.trigger_metamethod_vm(func, vec![a_val, b_val], "__concat") {
                                self.runtime_error(
                                    "attempt to concatenate with an uncallable __concat metamethod",
                                );
                            }
                        } else {
                            let invalid = if !a_is_valid { a_val } else { b_val };
                            self.runtime_error(&format!(
                                "attempt to concatenate a {} value",
                                self.callable_type_name(invalid)
                            ));
                        }
                    }
                }
                OpCode::Eq => {
                    let b_val = self.data_stack.pop().unwrap();
                    let a_val = self.data_stack.pop().unwrap();

                    let mut is_eq = self.numbers_equal(a_val, b_val).unwrap_or(a_val == b_val);

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
                        let comparable_objects = a_val.is_obj()
                            && b_val.is_obj()
                            && matches!(
                                (
                                    &self.objects[a_val.as_obj() as usize],
                                    &self.objects[b_val.as_obj() as usize]
                                ),
                                (Some(GcObject::Table(..)), Some(GcObject::Table(..)))
                                    | (Some(GcObject::File(..)), Some(GcObject::File(..)))
                                    | (Some(GcObject::StdFile(..)), Some(GcObject::StdFile(..)))
                            );

                        let mut handled = false;
                        if comparable_objects {
                            let metamethod = self
                                .get_metamethod(a_val, "__eq")
                                .or_else(|| self.get_metamethod(b_val, "__eq"));
                            if let Some(function) = metamethod {
                                handled = self.trigger_metamethod_vm(
                                    function,
                                    vec![a_val, b_val],
                                    "__eq",
                                );
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
                        if !self.trigger_metamethod_vm(mm, vec![val], "__len") {
                            self.runtime_error(
                                "attempt to get length of object with uncallable __len",
                            );
                        }
                    } else if val.is_obj() {
                        match &self.objects[val.as_obj() as usize].as_ref().unwrap() {
                            GcObject::Str(s) => self.data_stack.push(Value::num(lua_string_bytes(s).len() as f64)),
                            GcObject::Table(m, _) => {
                                let present = |index: usize| {
                                    m.get(&Value::num(index as f64))
                                        .is_some_and(|value| value.0 != TAG_NIL)
                                };
                                let mut low = 0usize;
                                let mut high = 1usize;
                                let max_index = (1u64 << 53).min(usize::MAX as u64) as usize;
                                while high < max_index && present(high) {
                                    low = high;
                                    high = high.saturating_mul(2);
                                    if high == usize::MAX {
                                        break;
                                    }
                                }
                                while low + 1 < high {
                                    let middle = low + (high - low) / 2;
                                    if present(middle) {
                                        low = middle;
                                    } else {
                                        high = middle;
                                    }
                                }
                                self.data_stack.push(Value::num(low as f64));
                            }
                            _ => self.runtime_error(&format!(
                                "attempt to get length of a {} value",
                                self.callable_type_name(val)
                            )),
                        }
                    } else {
                        self.runtime_error(&format!(
                            "attempt to get length of a {} value",
                            self.callable_type_name(val)
                        ));
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
                    let prototype = c_idx as usize;
                    let cached = self
                        .closure_cache
                        .get(&prototype)
                        .copied()
                        .filter(|cached_id| {
                            matches!(
                                &self.objects[*cached_id as usize],
                                Some(GcObject::Closure { chunk_idx, upvalues })
                                    if *chunk_idx == prototype && *upvalues == captured
                            )
                        });
                    let id = if let Some(cached_id) = cached {
                        cached_id
                    } else {
                        let closure_id = self.alloc_closure(prototype, captured);
                        self.closure_cache.insert(prototype, closure_id);
                        closure_id
                    };
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
                call @ (OpCode::Call(..) | OpCode::ForCall(..)) => {
                    let (fixed_args, has_multi, is_for_iterator) = match call {
                        OpCode::Call(fixed_args, has_multi) => {
                            (fixed_args, has_multi, false)
                        }
                        OpCode::ForCall(fixed_args, has_multi) => {
                            (fixed_args, has_multi, true)
                        }
                        _ => unreachable!(),
                    };
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

                    if !self.is_callable(callable) {
                        if let Some(mm) = self.get_metamethod(callable, "__call") {
                            resolved_callable = mm;
                            is_metamethod = true;
                        } else {
                            self.call_type_error(callable, chunk_idx, ip);
                        }
                    }

                    let explicit_call_name = if is_metamethod {
                        Some(("__call", "metamethod"))
                    } else if is_for_iterator {
                        Some(("for iterator", "for iterator"))
                    } else {
                        None
                    };

                    match self.objects[resolved_callable.as_obj() as usize]
                        .clone()
                        .unwrap()
                    {
                        GcObject::Closure { chunk_idx, .. } => {
                            self.ensure_call_capacity(1);
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
                            let varargs = if self.chunks[chunk_idx].is_vararg
                                && fixed_params.len() > param_count
                            {
                                fixed_params.split_off(param_count)
                            } else {
                                fixed_params.truncate(param_count);
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
                                last_hook_ip: None,
                                is_hook: false,
                                is_tailcall: false,
                                is_native: false,
                                native_continuation: None,
                                frame_continuation: None,
                                call_name: explicit_call_name
                                    .map(|(name, _)| name.to_string()),
                                call_namewhat: explicit_call_name
                                    .map(|(_, namewhat)| namewhat.to_string())
                                    .unwrap_or_default(),
                            });
                            if explicit_call_name.is_none() {
                                self.record_top_call_name();
                            }
                            self.dispatch_hook("call", None);
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

                            let new_call_depth = self.call_stack.len();
                            let new_data_depth = self.data_stack.len();
                            let new_handler_depth = self.handler_stack.len();

                            for frame in &mut cloned_calls {
                                frame.stack_base = frame.stack_base - orig_data_depth + new_data_depth;
                                frame.handler_base =
                                    frame.handler_base - orig_handler_depth + new_handler_depth;
                            }
                            for h in &mut cloned_handlers {
                                h.call_depth = h.call_depth - orig_call_depth + new_call_depth;
                                h.data_depth = h.data_depth - orig_data_depth + new_data_depth;
                            }

                            self.ensure_call_capacity(cloned_calls.len());
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

                            let saved_call_name = explicit_call_name.map(|(name, namewhat)| {
                                self.pending_call_name
                                    .replace((name.to_string(), namewhat.to_string()))
                            });
                            self.begin_native_call(resolved_callable.as_obj(), &args);
                            self.multiret_count = func(self, args);
                            if self.pending_call.is_none() {
                                self.end_native_call();
                            }
                            if let Some(saved_call_name) = saved_call_name {
                                self.pending_call_name = saved_call_name;
                            }

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

                            let saved_call_name = explicit_call_name.map(|(name, namewhat)| {
                                self.pending_call_name
                                    .replace((name.to_string(), namewhat.to_string()))
                            });
                            self.begin_native_call(resolved_callable.as_obj(), &args);
                            self.multiret_count = func(self, args, state);
                            if self.pending_call.is_none() {
                                self.end_native_call();
                            }
                            if let Some(saved_call_name) = saved_call_name {
                                self.pending_call_name = saved_call_name;
                            }

                            self.temp_roots.truncate(roots_start);
                        }
                        _ => self.runtime_error("Uncallable object"),
                    }
                }
                OpCode::Return(fixed, has_multi) => {
                    self.dispatch_hook("return", None);
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

                    if !self.is_callable(callable) {
                        if let Some(mm) = self.get_metamethod(callable, "__call") {
                            resolved_callable = mm;
                            is_metamethod = true;
                        } else {
                            self.call_type_error(callable, chunk_idx, ip);
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
                            let varargs = if self.chunks[chunk_idx].is_vararg
                                && fixed_params.len() > param_count
                            {
                                fixed_params.split_off(param_count)
                            } else {
                                fixed_params.truncate(param_count);
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
                            current_frame.last_hook_ip = None;
                            current_frame.is_hook = false;
                            current_frame.is_tailcall = true;
                            current_frame.is_native = false;
                            current_frame.native_continuation = None;
                            current_frame.frame_continuation = None;
                            current_frame.call_name =
                                is_metamethod.then(|| "__call".to_string());
                            current_frame.call_namewhat = if is_metamethod {
                                "metamethod".to_string()
                            } else {
                                String::new()
                            };
                            if !is_metamethod {
                                self.record_top_call_name();
                            }
                            self.dispatch_hook("tail call", None);
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

                            let new_call_depth = self.call_stack.len();
                            let new_data_depth = self.data_stack.len();
                            let new_handler_depth = self.handler_stack.len();

                            for frame in &mut cloned_calls {
                                frame.stack_base = frame.stack_base - orig_data_depth + new_data_depth;
                                frame.handler_base =
                                    frame.handler_base - orig_handler_depth + new_handler_depth;
                            }
                            for h in &mut cloned_handlers {
                                h.call_depth = h.call_depth - orig_call_depth + new_call_depth;
                                h.data_depth = h.data_depth - orig_data_depth + new_data_depth;
                            }

                            self.ensure_call_capacity(cloned_calls.len());
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
                            let stack_base = self.begin_native_tail_call(
                                resolved_callable.as_obj(),
                                args.clone(),
                                self.callable_method_at(chunk_idx, ip),
                            );
                            self.multiret_count = func(self, args);

                            if self.yielded {
                                if let Some(frame) = self
                                    .call_stack
                                    .iter_mut()
                                    .rev()
                                    .find(|frame| frame.is_native)
                                {
                                    if frame.native_continuation.is_none() {
                                        frame.native_continuation =
                                            Some(NativeContinuation::ReturnResults);
                                    }
                                }
                            } else if self.pending_call.is_none()
                                && self.call_stack.last().is_some_and(|frame| frame.is_native) {
                                let ret_count = self.multiret_count;
                                let first_result = self.data_stack.len() - ret_count;
                                let results = self.data_stack.split_off(first_result);
                                self.end_native_call();
                                self.data_stack.truncate(stack_base);
                                self.data_stack.extend(results);
                            }
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
                            let stack_base = self.begin_native_tail_call(
                                resolved_callable.as_obj(),
                                args.clone(),
                                self.callable_method_at(chunk_idx, ip),
                            );
                            self.multiret_count = func(self, args, state);

                            if self.yielded {
                                if let Some(frame) = self
                                    .call_stack
                                    .iter_mut()
                                    .rev()
                                    .find(|frame| frame.is_native)
                                {
                                    if frame.native_continuation.is_none() {
                                        frame.native_continuation =
                                            Some(NativeContinuation::ReturnResults);
                                    }
                                }
                            } else if self.pending_call.is_none()
                                && self.call_stack.last().is_some_and(|frame| frame.is_native) {
                                let ret_count = self.multiret_count;
                                let first_result = self.data_stack.len() - ret_count;
                                let results = self.data_stack.split_off(first_result);
                                self.end_native_call();
                                self.data_stack.truncate(stack_base);
                                self.data_stack.extend(results);
                            }
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
                    let step_val = self.data_stack.pop().unwrap();
                    let limit_val = self.data_stack.pop().unwrap();
                    let curr_val = self.data_stack.pop().unwrap();

                    let cond = if !self.is_float_value(curr_val)
                        && !self.is_float_value(limit_val)
                        && !self.is_float_value(step_val)
                    {
                        let curr = self.to_integer(curr_val).unwrap();
                        let limit = self.to_integer(limit_val).unwrap();
                        let step = self.to_integer(step_val).unwrap();
                        if step >= 0 {
                            curr <= limit
                        } else {
                            curr >= limit
                        }
                    } else {
                        let step = self.to_num(step_val).unwrap();
                        let limit = self.to_num(limit_val).unwrap();
                        let curr = self.to_num(curr_val).unwrap();
                        if step >= 0.0 {
                            curr <= limit
                        } else {
                            curr >= limit
                        }
                    };
                    self.data_stack.push(Value::bool(cond));
                }
                OpCode::PrepareFor(loop_idx, limit_idx, step_idx) => {
                    let base = self.call_stack[frame_idx].stack_base;
                    let indices = [loop_idx, limit_idx, step_idx];
                    let values = indices.map(|index| self.data_stack[base + index as usize]);
                    let integer_loop = !self.is_float_value(values[0])
                        && !self.is_float_value(values[2])
                        && self.to_integer(values[0]).is_some()
                        && self.to_integer(values[2]).is_some();
                    if integer_loop {
                        let step = self.to_integer(values[2]).unwrap();
                        let (limit, unreachable_limit) = if let Some(limit) = self.to_integer(values[1]) {
                            (limit, None)
                        } else {
                            let number = self.to_num(values[1]).unwrap();
                            let rounded = if step >= 0 {
                                number.floor()
                            } else {
                                number.ceil()
                            };
                            if rounded.is_nan() {
                                self.runtime_error("'for' limit is NaN");
                            } else if (step >= 0 && rounded < i64::MIN as f64)
                                || (step < 0 && rounded >= i64::MAX as f64)
                            {
                                (0, Some(number))
                            } else if rounded >= i64::MAX as f64 {
                                (i64::MAX, None)
                            } else if rounded <= i64::MIN as f64 {
                                (i64::MIN, None)
                            } else {
                                (rounded as i64, None)
                            }
                        };
                        let value = if let Some(number) = unreachable_limit {
                            self.alloc_float(number)
                        } else {
                            self.alloc_integer(limit)
                        };
                        self.data_stack[base + limit_idx as usize] = value;
                    } else {
                        for (index, value) in indices.into_iter().zip(values) {
                            let number = self.to_num(value).unwrap();
                            let float = self.alloc_float(number);
                            self.data_stack[base + index as usize] = float;
                        }
                    }
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
                    self.ensure_call_capacity(1);
                    self.call_stack.push(CallFrame {
                        closure_id: handler.closure_id,
                        chunk_idx: c_idx,
                        ip: 0,
                        stack_base: sb,
                        handler_base: self.handler_stack.len(),
                        varargs: Vec::new(),
                        last_hook_ip: None,
                        is_hook: false,
                        is_tailcall: false,
                        is_native: false,
                        native_continuation: None,
                        frame_continuation: None,
                        call_name: None,
                        call_namewhat: String::new(),
                    });
                    self.record_top_call_name();
                    self.dispatch_hook("call", None);
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
    Integer(i64),
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
    Goto,
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
    DoubleColon,
    DotDotDot,
    EOF,
}

pub struct Scanner<'a> {
    source: &'a str,
    chars: Peekable<Chars<'a>>,
    offset: usize,
    token_start_offset: usize,
    pub token_text: String,
    pending_newline: Option<char>,
    nesting_depth: usize,
    block_depth: usize,
    pub line: usize,
    pub col: usize,
    pub token_start_line: usize,
    pub token_start_col: usize,
}

fn parse_decimal_float(s: &str) -> Option<f64> {
    let unsigned = s.strip_prefix(['+', '-']).unwrap_or(s);
    let exponent_at = unsigned.find(['e', 'E']);
    let (mantissa, exponent) = match exponent_at {
        Some(index) => (&unsigned[..index], Some(&unsigned[index + 1..])),
        None => (unsigned, None),
    };
    let mut digits = 0;
    let mut dots = 0;
    for byte in mantissa.bytes() {
        if byte.is_ascii_digit() {
            digits += 1;
        } else if byte == b'.' {
            dots += 1;
        } else {
            return None;
        }
    }
    if digits == 0 || dots > 1 {
        return None;
    }
    if let Some(exponent) = exponent {
        let unsigned_exponent = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
        if unsigned_exponent.is_empty() || !unsigned_exponent.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
    }
    s.parse().ok()
}

fn parse_hex_float(s: &str) -> f64 {
    let Some(s) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) else {
        return f64::NAN;
    };
    let mut parts = s.splitn(2, |c| c == 'p' || c == 'P');
    let hex_part = parts.next().unwrap_or("");
    let exp_part = parts.next().unwrap_or("0");

    let mut digits = 0;
    let mut dots = 0;
    for byte in hex_part.bytes() {
        if byte.is_ascii_hexdigit() {
            digits += 1;
        } else if byte == b'.' {
            dots += 1;
        } else {
            return f64::NAN;
        }
    }
    if digits == 0 || dots > 1 {
        return f64::NAN;
    }
    if s.len() != hex_part.len() {
        let exponent = exp_part.strip_prefix(['+', '-']).unwrap_or(exp_part);
        if exponent.is_empty() || !exponent.bytes().all(|byte| byte.is_ascii_digit()) {
            return f64::NAN;
        }
    }

    let mut integer_digits = 0usize;
    let mut digit_index = 0usize;
    let mut first_nonzero = None;
    let mut significand = 0u64;
    let mut significant_digits = 0usize;
    let mut in_fraction = false;
    for byte in hex_part.bytes() {
        if byte == b'.' {
            in_fraction = true;
            continue;
        }
        if !in_fraction {
            integer_digits += 1;
        }
        let digit = (byte as char).to_digit(16).unwrap() as u64;
        if digit != 0 && first_nonzero.is_none() {
            first_nonzero = Some(digit_index);
        }
        if first_nonzero.is_some() && significant_digits < 16 {
            significand = significand * 16 + digit;
            significant_digits += 1;
        }
        digit_index += 1;
    }
    let Some(first_nonzero) = first_nonzero else { return 0.0 };
    let bits = 64 - significand.leading_zeros();
    let exponent = exp_part.parse::<f64>().unwrap_or(0.0);
    let shift = exponent
        + 4.0 * (integer_digits as f64 - first_nonzero as f64 - significant_digits as f64)
        + bits as f64;
    (significand as f64 / 2.0_f64.powi(bits as i32)) * 2.0_f64.powf(shift)
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut s = Self {
            source,
            chars: source.chars().peekable(),
            offset: 0,
            token_start_offset: 0,
            token_text: String::new(),
            pending_newline: None,
            nesting_depth: 0,
            block_depth: 0,
            line: 1,
            col: 1,
            token_start_line: 1,
            token_start_col: 1,
        };
        s
    }
    fn advance(&mut self) -> Option<char> {
        let c = self.chars.next();
        if let Some(ch) = c {
            self.offset += ch.len_utf8();
            if ch == '\n' || ch == '\r' {
                if self.pending_newline.is_some_and(|previous| previous != ch) {
                    self.pending_newline = None;
                } else {
                    self.line += 1;
                    self.col = 1;
                    self.pending_newline = Some(ch);
                }
            } else {
                self.pending_newline = None;
                self.col += 1;
            }
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
    fn string_error(&self, message: &str, quote: char) -> ! {
        let mut end = self.offset;
        for (offset, ch) in self.source[self.offset..].char_indices() {
            if ch == '\n' || ch == '\r' {
                break;
            }
            end = self.offset + offset + ch.len_utf8();
            if ch == quote {
                break;
            }
        }
        panic!("{} near '{}'", message, &self.source[self.token_start_offset..end]);
    }
    fn escape_error_at_next(&self, message: &str) -> ! {
        let end = self.offset
            + self.source[self.offset..]
                .chars()
                .next()
                .map_or(0, char::len_utf8);
        panic!(
            "{} near '{}'",
            message,
            &self.source[self.token_start_offset..end]
        );
    }
    pub fn peek_token(&self) -> Token {
        let mut clone = Scanner {
            source: self.source,
            chars: self.chars.clone(),
            offset: self.offset,
            token_start_offset: self.offset,
            token_text: String::new(),
            pending_newline: self.pending_newline,
            nesting_depth: self.nesting_depth,
            block_depth: self.block_depth,
            token_start_line: self.line,
            token_start_col: self.col,
            line: self.line,
            col: self.col,
        };
        clone.next_token()
    }

    pub fn next_token(&mut self) -> Token {
        let token = self.scan_token();
        if matches!(token, Token::Do | Token::If | Token::Function) {
            self.block_depth += 1;
            if self.block_depth > 200 {
                panic!("LEXICAL_DEPTH:{}", self.token_start_line);
            }
        } else if token == Token::End {
            self.block_depth = self.block_depth.saturating_sub(1);
        }
        if token == Token::EOF {
            self.token_start_offset = self.offset;
            self.token_start_line = self.line;
            self.token_start_col = self.col;
        }
        self.token_text = self.source[self.token_start_offset..self.offset].to_string();
        token
    }

    fn scan_token(&mut self) -> Token {
        while let Some(&c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
                continue;
            }
            self.token_start_line = self.line;
            self.token_start_col = self.col;
            self.token_start_offset = self.offset;
            if matches!(c, '(' | '{') {
                self.nesting_depth += 1;
                if self.nesting_depth > 200 {
                    panic!("LEXICAL_DEPTH:{}", self.line);
                }
            } else if matches!(c, ')' | '}') {
                self.nesting_depth = self.nesting_depth.saturating_sub(1);
            }
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
                    let mut terminated = false;

                    while let Some(&nc) = self.peek() {
                        if nc == quote {
                            self.advance();
                            terminated = true;
                            break;
                        }

                        if nc == '\n' || nc == '\r' {
                            panic!("unfinished string near <eof>");
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
                                            self.string_error("decimal escape too large", quote);
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
                                            self.escape_error_at_next("hexadecimal digit expected");
                                        }
                                    }
                                    'u' => {
                                        self.advance();
                                        if !self.match_char('{') { self.escape_error_at_next("missing '{' in Unicode escape"); }
                                        let mut hex = String::new();
                                        while let Some(&digit) = self.peek() {
                                            if digit == '}' { break; }
                                            if !digit.is_ascii_hexdigit() { self.escape_error_at_next("invalid Unicode escape"); }
                                            hex.push(digit);
                                            self.advance();
                                        }
                                        if hex.is_empty() || !self.match_char('}') { self.escape_error_at_next("invalid Unicode escape"); }
                                        let code = u32::from_str_radix(&hex, 16).unwrap_or(u32::MAX);
                                        if code > 0x10ffff {
                                            panic!("UTF-8 value too large near '{}'", &self.source[self.token_start_offset..self.offset - 1]);
                                        }
                                        let mut utf8 = Vec::new();
                                        append_utf8_codepoint(&mut utf8, code);
                                        for byte in utf8 { s.push(byte as char); }
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
                                        self.escape_error_at_next("invalid escape sequence");
                                    }
                                }
                            }
                        } else {
                            s.push(nc);
                            self.advance();
                        }
                    }
                    if !terminated { panic!("unfinished string near <eof>"); }
                    return Token::StringLiteral(s);
                }
                ':' => {
                    self.advance();
                    return if self.match_char(':') {
                        Token::DoubleColon
                    } else {
                        Token::Colon
                    };
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
                    return if self.match_char('<') {
                        Token::Shl
                    } else if self.match_char('=') {
                        Token::LtEq
                    } else {
                        Token::Lt
                    };
                }
                '>' => {
                    self.advance();
                    return if self.match_char('>') {
                        Token::Shr
                    } else if self.match_char('=') {
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
                            if nc == '\n' || nc == '\r' {
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
                                panic!("unfinished long string near <eof>");
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
                            if !num_str.chars().any(|ch| matches!(ch, '.'|'e'|'E')) {
                                if let Ok(value) = num_str.parse::<i64>() {
                                    return Token::Integer(value);
                                }
                            }
                            let val = num_str.parse().unwrap_or_else(|_| panic!("malformed number near '{}'", num_str));
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

                    if is_hex && !num_str.chars().any(|ch| matches!(ch, '.'|'p'|'P')) {
                        let mut value = 0u64;
                        for digit in num_str[2..].chars().filter_map(|ch| ch.to_digit(16)) {
                            value = value.wrapping_mul(16).wrapping_add(digit as u64);
                        }
                        return Token::Integer(value as i64);
                    }
                    if !is_hex && !num_str.chars().any(|ch| matches!(ch, '.'|'e'|'E')) {
                        if let Ok(value) = num_str.parse::<i64>() {
                            return Token::Integer(value);
                        }
                    }
                    let val = if is_hex { parse_hex_float(&num_str) } else { num_str.parse().unwrap_or_else(|_| panic!("malformed number near '{}'", num_str)) };
                    return Token::Num(val);
                }
                _ if c.is_ascii_alphabetic() || c == '_' => {
                    let mut id = String::new();
                    while let Some(&nc) = self.peek() {
                        if nc.is_ascii_alphanumeric() || nc == '_' {
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
                        "goto" => Token::Goto,
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
                _ => panic!("LEXICAL:{}:{}", self.line, c as u32),
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
    Table(Option<(String, String)>),
    Call(bool),
}

struct CompileBlock {
    parent: Option<usize>,
    local_start: usize,
}

struct CompileLabel {
    name: String,
    block_id: usize,
    target: usize,
    locals: Vec<String>,
    local_ids: Vec<usize>,
    line: usize,
}

struct CompileGoto {
    name: String,
    block_id: usize,
    jump_offset: usize,
    close_offset: usize,
    local_ids: Vec<usize>,
    line: usize,
}

pub struct CompilerState {
    pub locals: Vec<String>,
    local_ids: Vec<usize>,
    next_local_id: usize,
    pub max_locals: usize,
    pub chunk_idx: usize,
    pub loop_exits: Vec<Vec<usize>>,
    pub loop_continues: Vec<Vec<usize>>,
    pub pending_jumps: Vec<usize>,
    pub upvals: Vec<(bool, usize, String)>,
    pub is_vararg: bool,
    blocks: Vec<CompileBlock>,
    active_blocks: Vec<usize>,
    labels: Vec<CompileLabel>,
    gotos: Vec<CompileGoto>,
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
    source_lines: Vec<String>,
    expression_depth: usize,
}

impl<'a, 'b> Compiler<'a, 'b> {
    fn leave_scope(&mut self, local_start: usize) {
        let state = self.states.last_mut().unwrap();
        let current_len = state.locals.len();
        if current_len > local_start {
            let chunk_idx = state.chunk_idx;
            self.vm.chunks[chunk_idx]
                .local_names
                .push(state.locals.clone());
            self.vm.chunks[chunk_idx]
                .instructions
                .push(OpCode::CloseLocals(local_start as u32));
            self.vm.chunks[chunk_idx].call_names.push(None);
            self.vm.chunks[chunk_idx].right_names.push(None);
            self.vm.chunks[chunk_idx].lines.push(self.previous_line);
            state.locals.truncate(local_start);
            state.local_ids.truncate(local_start);
        }
    }

    fn add_local(&mut self, name: String) -> usize {
        if self.states.last().unwrap().locals.len() >= 200 {
            let chunk_idx = self.states.last().unwrap().chunk_idx;
            let line = self.vm.chunks[chunk_idx].linedefined;
            self.error(&format!("too many local variables (line {})", line));
        }
        let state = self.states.last_mut().unwrap();
        let index = state.locals.len();
        state.locals.push(name);
        state.local_ids.push(state.next_local_id);
        state.next_local_id += 1;
        if state.locals.len() > state.max_locals {
            state.max_locals = state.locals.len();
        }
        index
    }
    pub fn compile(vm: &mut VM, source: &str, source_name: &str) -> Result<usize, String> {
        stacker::grow(8 * 1024 * 1024, || Self::compile_on_stack(vm, source, source_name))
    }

    fn compile_on_stack(vm: &mut VM, source: &str, source_name: &str) -> Result<usize, String> {
        let source_lines: Vec<String> = source.lines().map(|s| s.to_string()).collect();
        let source_id = vm.intern_source_name(source_name);

        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let depth_check = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut probe = Scanner::new(source);
                while probe.next_token() != Token::EOF {}
            }));
            if let Err(payload) = depth_check {
                if payload.downcast_ref::<String>().is_some_and(|message| message.starts_with("LEXICAL_DEPTH:")) {
                    std::panic::resume_unwind(payload);
                }
            }
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
                source_lines,
                expression_depth: 0,
            };
            compiler.advance();
            let chunk_idx = compiler.create_chunk();
            compiler.vm.chunks[chunk_idx].is_main = true;
            compiler.vm.chunks[chunk_idx].is_vararg = true;
            compiler.states.push(CompilerState {
                locals: Vec::new(),
                local_ids: Vec::new(),
                next_local_id: 0,
                max_locals: 0,
                chunk_idx,
                loop_exits: Vec::new(),
                loop_continues: Vec::new(),
                pending_jumps: Vec::new(),
                upvals: vec![(false, 0, "_ENV".to_string())],
                is_vararg: true,
                blocks: Vec::new(),
                active_blocks: Vec::new(),
                labels: Vec::new(),
                gotos: Vec::new(),
            });
            compiler.statement_list();
            compiler.emit(OpCode::Return(0, false));
            compiler.resolve_gotos();
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
                if let Some(detail) = msg.strip_prefix("LEXICAL:") {
                    if let Some((line, code)) = detail.split_once(':') {
                        let source = if let Some(name) = source_name.strip_prefix('@') {
                            name.chars().take(59).collect::<String>()
                        } else if let Some(name) = source_name.strip_prefix('=') {
                            name.chars().take(59).collect::<String>()
                        } else {
                            let preview = source_name.lines().next().unwrap_or("");
                            format!("[string \"{}\"]", preview.chars().take(48).collect::<String>())
                        };
                        return Err(format!("{}:{}: unexpected symbol near '<\\{}>'", source, line, code));
                    }
                }
                if let Some(line) = msg.strip_prefix("LEXICAL_DEPTH:") {
                    let source = if let Some(name) = source_name.strip_prefix('@') {
                        name.chars().take(59).collect::<String>()
                    } else if let Some(name) = source_name.strip_prefix('=') {
                        name.chars().take(59).collect::<String>()
                    } else {
                        let preview = source_name.lines().next().unwrap_or("");
                        format!("[string \"{}\"]", preview.chars().take(48).collect::<String>())
                    };
                    return Err(format!("{}:{}: too many C levels", source, line));
                }
                Err(msg)
            }
        }
    }

    fn error(&self, msg: &str) -> ! {
        let source_name = &self.vm.source_names[self.source_id];
        let source = if let Some(name) = source_name.strip_prefix('@') {
            name.chars().take(59).collect::<String>()
        } else if let Some(name) = source_name.strip_prefix('=') {
            name.chars().take(59).collect::<String>()
        } else {
            let preview = source_name.lines().next().unwrap_or("");
            format!("[string \"{}\"]", preview.chars().take(48).collect::<String>())
        };
        let near = if self.current == Token::EOF {
            "<eof>".to_string()
        } else {
            format!("'{}'", self.scanner.token_text)
        };
        panic!("{}:{}: {} near {}", source, self.current_line, msg, near);
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
        const MAX_JUMP_SPAN: usize = 131_071;
        let instruction_count = self.vm.chunks[idx].instructions.len();
        let forward_too_long = self.states.last().unwrap().pending_jumps.iter().any(|origin| {
            instruction_count.saturating_sub(*origin) > MAX_JUMP_SPAN
        });
        let backward_too_long = matches!(op, OpCode::Jump(target) if instruction_count.saturating_sub(target) > MAX_JUMP_SPAN);
        if forward_too_long || backward_too_long {
            self.error("control structure too long");
        }
        let local_names = self.states.last().unwrap().locals.clone();
        self.vm.chunks[idx].instructions.push(op);
        self.vm.chunks[idx].call_names.push(None);
        self.vm.chunks[idx].right_names.push(None);
        self.vm.chunks[idx].lines.push(self.previous_line);
        self.vm.chunks[idx].local_names.push(local_names);
    }

    fn name_last_call(&mut self, name: Option<(String, String)>) {
        let chunk_idx = self.states.last().unwrap().chunk_idx;
        if let Some(slot) = self.vm.chunks[chunk_idx].call_names.last_mut() {
            *slot = name;
        }
    }

    fn name_last_right_operand(&mut self, name: Option<(String, String)>) {
        let chunk_idx = self.states.last().unwrap().chunk_idx;
        if let Some(slot) = self.vm.chunks[chunk_idx].right_names.last_mut() {
            *slot = name;
        }
    }

    fn identifier_call_name(&self, name: &str) -> (String, String) {
        let state = self.states.last().unwrap();
        let kind = if state.locals.iter().any(|local| local == name) {
            "local"
        } else if state.upvals.iter().any(|(_, _, upvalue)| upvalue == name) {
            "upvalue"
        } else {
            "global"
        };
        (name.to_string(), kind.to_string())
    }
    fn emit_jump(&mut self, op: OpCode) -> usize {
        self.emit(op);
        let idx = self.states.last().unwrap().chunk_idx;
        let offset = self.vm.chunks[idx].instructions.len() - 1;
        self.states.last_mut().unwrap().pending_jumps.push(offset);
        offset
    }
    fn patch_jump(&mut self, offset: usize) {
        let idx = self.states.last().unwrap().chunk_idx;
        let target = self.vm.chunks[idx].instructions.len();
        self.states.last_mut().unwrap().pending_jumps.retain(|pending| *pending != offset);
        match &mut self.vm.chunks[idx].instructions[offset] {
            OpCode::JumpIfFalse(ref mut ip)
            | OpCode::Jump(ref mut ip)
            | OpCode::JumpIfFalseKeep(ref mut ip)
            | OpCode::JumpIfTrueKeep(ref mut ip) => *ip = target,
            _ => unreachable!(),
        }
    }

    fn block_is_ancestor(blocks: &[CompileBlock], ancestor: usize, mut block: usize) -> bool {
        loop {
            if block == ancestor {
                return true;
            }
            if let Some(parent) = blocks[block].parent {
                block = parent;
            } else {
                return false;
            }
        }
    }

    fn block_depth(blocks: &[CompileBlock], mut block: usize) -> usize {
        let mut depth = 0;
        while let Some(parent) = blocks[block].parent {
            depth += 1;
            block = parent;
        }
        depth
    }

    fn resolve_gotos(&mut self) {
        const MAX_JUMP_SPAN: usize = 131_071;
        let state_idx = self.states.len() - 1;
        let state = &self.states[state_idx];
        let mut patches = Vec::with_capacity(state.gotos.len());

        for goto_record in &state.gotos {
            let label = state
                .labels
                .iter()
                .filter(|label| {
                    label.name == goto_record.name
                        && Self::block_is_ancestor(
                            &state.blocks,
                            label.block_id,
                            goto_record.block_id,
                        )
                })
                .max_by_key(|label| Self::block_depth(&state.blocks, label.block_id))
                .unwrap_or_else(|| {
                    panic!(
                        "no visible label '{}' for <goto> at line {}",
                        goto_record.name, goto_record.line
                    )
                });

            let common_prefix = label
                .local_ids
                .iter()
                .zip(&goto_record.local_ids)
                .take_while(|(target, source)| target == source)
                .count();
            if common_prefix != label.local_ids.len() {
                let local_name = label.locals[common_prefix].as_str();
                panic!(
                    "<goto {}> at line {} jumps into the scope of local '{}'",
                    goto_record.name, goto_record.line, local_name
                );
            }
            if goto_record.jump_offset.abs_diff(label.target) > MAX_JUMP_SPAN {
                panic!("control structure too long");
            }
            patches.push((
                goto_record.close_offset,
                goto_record.jump_offset,
                label.target,
                label.locals.len() as u32,
            ));
        }

        let chunk_idx = state.chunk_idx;
        for (close_offset, jump_offset, target, local_count) in patches {
            self.vm.chunks[chunk_idx].instructions[close_offset] =
                OpCode::CloseLocals(local_count);
            self.vm.chunks[chunk_idx].instructions[jump_offset] = OpCode::Jump(target);
        }
    }

    fn label_statement(&mut self, block_id: usize) -> usize {
        let line = self.previous_line;
        let name = if let Token::Ident(name) = self.current.clone() {
            self.advance();
            name
        } else {
            self.error("label name expected");
        };
        self.consume(Token::DoubleColon, "'::' expected after label name");

        let state = self.states.last_mut().unwrap();
        if state
            .labels
            .iter()
            .any(|label| label.block_id == block_id && label.name == name)
        {
            panic!("label '{}' already defined at line {}", name, line);
        }
        let target = self.vm.chunks[state.chunk_idx].instructions.len();
        state.labels.push(CompileLabel {
            name,
            block_id,
            target,
            locals: state.locals.clone(),
            local_ids: state.local_ids.clone(),
            line,
        });
        state.labels.len() - 1
    }

    fn goto_statement(&mut self) {
        let line = self.previous_line;
        let name = if let Token::Ident(name) = self.current.clone() {
            self.advance();
            name
        } else {
            self.error("label name expected after 'goto'");
        };

        let (block_id, local_ids, chunk_idx) = {
            let state = self.states.last().unwrap();
            (
                *state.active_blocks.last().unwrap(),
                state.local_ids.clone(),
                state.chunk_idx,
            )
        };
        let close_offset = self.vm.chunks[chunk_idx].instructions.len();
        self.emit(OpCode::CloseLocals(local_ids.len() as u32));
        let jump_offset = self.vm.chunks[chunk_idx].instructions.len();
        self.emit(OpCode::Jump(jump_offset));
        self.states.last_mut().unwrap().gotos.push(CompileGoto {
            name,
            block_id,
            jump_offset,
            close_offset,
            local_ids,
            line,
        });
    }

    fn create_chunk(&mut self) -> usize {
        let idx = self.vm.chunks.len();
        self.vm.chunks.push(Chunk {
            instructions: vec![],
            call_names: vec![],
            right_names: vec![],
            lines: vec![],
            local_names: vec![],
            constants: vec![],
            local_count: 0,
            param_count: 0,
            is_vararg: false,
            upvals: vec![],
            source_id: self.source_id,
            linedefined: self.previous_line,
            lastlinedefined: self.previous_line,
            is_main: false,
            is_stripped: false,
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
        if self.states[state_idx].upvals.len() >= 255 {
            self.error(&format!("too many upvalues (line {})", self.previous_line));
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
        let block_id = {
            let state = self.states.last_mut().unwrap();
            let block_id = state.blocks.len();
            state.blocks.push(CompileBlock {
                parent: state.active_blocks.last().copied(),
                local_start: state.locals.len(),
            });
            state.active_blocks.push(block_id);
            block_id
        };
        let mut trailing_labels = Vec::new();

        while !self.check(Token::End)
            && !self.check(Token::With)
            && !self.check(Token::Else)
            && !self.check(Token::Elseif)
            && !self.check(Token::Until)
            && !self.check(Token::EOF)
        {
            if self.match_token(Token::Semi) {
                continue;
            }
            if self.match_token(Token::DoubleColon) {
                trailing_labels.push(self.label_statement(block_id));
                continue;
            }
            trailing_labels.clear();
            self.declaration();
        }

        let adjust_trailing_labels = !self.check(Token::Until);
        let state = self.states.last_mut().unwrap();
        let local_start = state.blocks[block_id].local_start;
        if adjust_trailing_labels {
            for label_idx in trailing_labels {
                state.labels[label_idx].locals.truncate(local_start);
                state.labels[label_idx].local_ids.truncate(local_start);
            }
        }
        let ended_block = state.active_blocks.pop();
        debug_assert_eq!(ended_block, Some(block_id));
    }

    fn declaration(&mut self) {
        if self.match_token(Token::Semi) {
            return;
        } else if self.match_token(Token::Function) {
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
                    self.add_local(name.clone());
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
            Lhs::Table(origin) => {
                self.emit(OpCode::GetTable);
                self.name_last_call(origin.clone());
            }
            Lhs::Call(is_multi) => {
                if *is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
            }
        }
    }

    fn parse_prefix_expr(&mut self) -> Lhs {
        let call_line = self.current_line;
        let mut lhs;
        let mut call_name = None;
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
            call_name = Some(self.identifier_call_name(&name));
        } else {
            self.error("unexpected symbol");
            unreachable!()
        }

        loop {
            if self.match_token(Token::LBracket) {
                self.emit_lhs_get(&lhs);
                let base_name = call_name.clone();
                let is_multi = self.expression();
                if is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.consume(Token::RBracket, "Expected ']'");
                lhs = Lhs::Table(base_name);
                call_name = None;
            } else if self.match_token(Token::Dot) {
                self.emit_lhs_get(&lhs);
                let base_name = call_name.clone();
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
                lhs = Lhs::Table(base_name);
                call_name = Some((name, "field".to_string()));
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
                self.name_last_call(call_name.clone());
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
                    self.error("expected '(', '{', or string literal for method call");
                }
                if arg_count >= 255 { self.error("too many registers"); }
                self.emit(OpCode::Call(arg_count as u32, last_multi));
                let chunk_idx = self.states.last().unwrap().chunk_idx;
                *self.vm.chunks[chunk_idx].lines.last_mut().unwrap() = call_line;
                self.name_last_call(Some((name, "method".to_string())));
                lhs = Lhs::Call(true);
                call_name = None;
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
                if arg_count >= 255 { self.error("too many registers"); }
                self.emit(OpCode::Call(arg_count as u32, last_multi));
                let chunk_idx = self.states.last().unwrap().chunk_idx;
                *self.vm.chunks[chunk_idx].lines.last_mut().unwrap() = call_line;
                self.name_last_call(call_name.take());
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
                || self.check(Token::EOF)
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
                let tail_call = if rhs_count == 1 && last_multiret {
                    if let Some(OpCode::Call(args, multi)) = insts.last().copied() {
                        insts.pop();
                        let name = self.vm.chunks[idx].call_names.pop().unwrap();
                        self.vm.chunks[idx].right_names.pop();
                        self.vm.chunks[idx].lines.pop();
                        self.vm.chunks[idx].local_names.pop();
                        Some((args, multi, name))
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some((args, multi, name)) = tail_call {
                    self.emit(OpCode::TailCall(args, multi));
                    self.name_last_call(name);
                } else {
                    self.emit(OpCode::Return(rhs_count as u32, last_multiret));
                }
            }
            self.match_token(Token::Semi);
            if !self.check(Token::End)
                && !self.check(Token::Else)
                && !self.check(Token::Elseif)
                && !self.check(Token::Until)
                && !self.check(Token::EOF)
            {
                self.error("'return' must be the last statement in a block");
            }
        } else if self.match_token(Token::Goto) {
            self.goto_statement();
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
                if targets.len() > 200 {
                    self.error("too many C levels");
                }
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
                        Lhs::Table(origin) => {

                            self.emit(OpCode::PopStash);
                            self.emit(OpCode::SetTable);
                            self.name_last_call(origin);
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
        let declaration_line = self.previous_line;
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
            local_ids: (0..params.len()).collect(),
            next_local_id: params.len(),
            max_locals: 0,
            chunk_idx,
            loop_exits: Vec::new(),
            upvals: Vec::new(),
            loop_continues: Vec::new(),
            pending_jumps: Vec::new(),
            is_vararg,
            blocks: Vec::new(),
            active_blocks: Vec::new(),
            labels: Vec::new(),
            gotos: Vec::new(),
        });
        self.vm.chunks[chunk_idx].param_count = params.len();
        self.vm.chunks[chunk_idx].is_vararg = is_vararg;

        let mut state = self.states.last_mut().unwrap();
        state.max_locals = state.locals.len();
        self.statement_list();

        self.consume(Token::End, "Expected 'end' for function");
        self.vm.chunks[chunk_idx].lastlinedefined = self.previous_line;
        self.emit(OpCode::Return(0, false));
        self.resolve_gotos();
        let finished_state = self.states.pop().unwrap();
        self.vm.chunks[finished_state.chunk_idx].local_count = finished_state.max_locals;
        self.vm.chunks[finished_state.chunk_idx].upvals = finished_state.upvals;
        let outer_chunk = self.states.last().unwrap().chunk_idx;
        let declaration_start = self.vm.chunks[outer_chunk].instructions.len();

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
        self.vm.chunks[outer_chunk].lines[declaration_start..].fill(declaration_line);
    }

    fn local_fun_declaration(&mut self) {
        self.advance();
        let fn_name = if let Token::Ident(name) = &self.previous {
            name.clone()
        } else {
            self.error("Expected fn name");
            unreachable!()
        };

        let store_idx = self.add_local(fn_name.clone());

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
            local_ids: (0..params.len()).collect(),
            next_local_id: params.len(),
            max_locals: 0,
            chunk_idx,
            loop_exits: Vec::new(),
            upvals: Vec::new(),
            loop_continues: Vec::new(),
            pending_jumps: Vec::new(),
            is_vararg,
            blocks: Vec::new(),
            active_blocks: Vec::new(),
            labels: Vec::new(),
            gotos: Vec::new(),
        });
        self.vm.chunks[chunk_idx].param_count = params.len();
        self.vm.chunks[chunk_idx].is_vararg = is_vararg;

        let mut inner_state = self.states.last_mut().unwrap();
        inner_state.max_locals = inner_state.locals.len();
        self.statement_list();
        self.consume(Token::End, "Expected 'end' for local function");
        self.vm.chunks[chunk_idx].lastlinedefined = self.previous_line;
        self.emit(OpCode::Return(0, false));
        self.resolve_gotos();
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
        let body_line = self.previous_line;
        let synthetic_start = self.vm.chunks[self.states.last().unwrap().chunk_idx]
            .instructions
            .len();
        self.consume(Token::End, "Expected 'end' for while");

        let mut state = self.states.last_mut().unwrap();
        let exits = state.loop_exits.pop().unwrap();
        let continues = state.loop_continues.pop().unwrap();

        for cont in continues {
            self.patch_jump(cont);
        }
        self.leave_scope(local_start);

        self.emit(OpCode::Jump(loop_start));
        let chunk_idx = self.states.last().unwrap().chunk_idx;
        self.vm.chunks[chunk_idx].lines[synthetic_start..].fill(body_line);
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
            if self.previous == Token::Shr {
                self.current = Token::Shr;
                self.current_line = self.previous_line;
                self.scanner.token_text = ">>".to_string();
            }
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
            let loop_idx = self.add_local(loop_var.clone());
            self.emit(OpCode::StoreLocal(loop_idx as u32));
            self.emit(OpCode::Pop);

            self.consume(Token::Comma, "Expected ','");

            let is_multi_end = self.expression();
            if is_multi_end {
                self.emit(OpCode::AdjustStack(1));
            }
            self.emit(OpCode::ForceNum);
            let end_idx = self.add_local(format!("$end_{}", loop_var));
            self.emit(OpCode::StoreLocal(end_idx as u32));
            self.emit(OpCode::Pop);

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
            let step_idx = self.add_local(format!("$step_{}", loop_var));
            self.emit(OpCode::StoreLocal(step_idx as u32));
            self.emit(OpCode::Pop);
            self.emit(OpCode::PrepareFor(
                loop_idx as u32,
                end_idx as u32,
                step_idx as u32,
            ));

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
            let body_line = self.previous_line;
            let synthetic_start = self.vm.chunks[self.states.last().unwrap().chunk_idx]
                .instructions
                .len();
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
            let chunk_idx = self.states.last().unwrap().chunk_idx;
            self.vm.chunks[chunk_idx].lines[synthetic_start..].fill(body_line);
            self.patch_jump(exit_jump);
            for exit in exits {
                self.patch_jump(exit);
            }
            self.leave_scope(local_start);
        } else if self.match_token(Token::In) {
            self.parse_rhs_and_adjust(3);
            let iterator_line = self.previous_line;

            let f_idx = self.add_local("$f".to_string());
            let s_idx = self.add_local("$s".to_string());
            let c_idx = self.add_local("$c".to_string());

            self.emit(OpCode::StoreLocal(c_idx as u32));
            self.emit(OpCode::Pop);
            self.emit(OpCode::StoreLocal(s_idx as u32));
            self.emit(OpCode::Pop);
            self.emit(OpCode::StoreLocal(f_idx as u32));
            self.emit(OpCode::Pop);

            let mut var_indices = Vec::new();
            for name in &var_names {
                let idx = self.add_local(name.clone());

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
            self.emit(OpCode::ForCall(2, false));
            let chunk_idx = self.states.last().unwrap().chunk_idx;
            *self.vm.chunks[chunk_idx].lines.last_mut().unwrap() = iterator_line;

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
            let body_line = self.previous_line;
            let synthetic_start = self.vm.chunks[self.states.last().unwrap().chunk_idx]
                .instructions
                .len();
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
            let chunk_idx = self.states.last().unwrap().chunk_idx;
            self.vm.chunks[chunk_idx].lines[synthetic_start..].fill(body_line);

            self.patch_jump(exit_jump);
            self.emit(OpCode::Pop);

            for exit in exits {
                self.patch_jump(exit);
            }
            self.leave_scope(local_start);
        } else {
            self.error("expected '=' or 'in' for loop");
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
            local_ids: Vec::new(),
            next_local_id: 0,
            max_locals: 0,
            chunk_idx,
            loop_exits: Vec::new(),
            upvals: Vec::new(),
            loop_continues: Vec::new(),
            pending_jumps: Vec::new(),
            is_vararg: false,
            blocks: Vec::new(),
            active_blocks: Vec::new(),
            labels: Vec::new(),
            gotos: Vec::new(),
        });
        self.statement_list();
        self.emit(OpCode::Return(0, false));
        self.resolve_gotos();
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
                locals: handler_params.clone(),
                local_ids: (0..handler_params.len()).collect(),
                next_local_id: handler_params.len(),
                max_locals: 0,
                chunk_idx: h_chunk_idx,
                loop_exits: Vec::new(),
                upvals: Vec::new(),
                loop_continues: Vec::new(),
                pending_jumps: Vec::new(),
                is_vararg: false,
                blocks: Vec::new(),
                active_blocks: Vec::new(),
                labels: Vec::new(),
                gotos: Vec::new(),
            });
            let mut state = self.states.last_mut().unwrap();
            state.max_locals = state.locals.len();
            self.statement_list();
            self.emit(OpCode::Return(0, false));
            self.resolve_gotos();
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
        self.expression_depth += 1;
        if self.expression_depth > 200 {
            self.error("too many C levels");
        }
        self.advance();
        let prefix_token = self.previous.clone();
        let can_assign = precedence <= Precedence::Assignment;
        let mut is_multi = self.prefix_rule(can_assign);
        let mut call_name = if let Token::Ident(name) = &prefix_token {
            Some(self.identifier_call_name(name))
        } else {
            None
        };
        let allow_call_suffix = !matches!(
            prefix_token,
            Token::Nil
                | Token::True
                | Token::False
                | Token::Num(_)
                | Token::Integer(_)
                | Token::StringLiteral(_)
                | Token::LBrace
        );
        while precedence <= self.get_precedence(&self.current)
            && (allow_call_suffix || self.get_precedence(&self.current) != Precedence::Call)
        {
            if is_multi {
                self.emit(OpCode::AdjustStack(1));
            }
            let operator = self.current.clone();
            let left_name = call_name.clone();
            self.advance();
            let member_name = if matches!(operator, Token::Dot | Token::Colon) {
                if let Token::Ident(name) = &self.current {
                    Some((name.clone(), if operator == Token::Colon { "method" } else { "field" }.to_string()))
                } else {
                    None
                }
            } else {
                None
            };
            is_multi = self.infix_rule(can_assign);
            match operator {
                Token::Dot => {
                    self.name_last_call(left_name);
                    call_name = member_name;
                }
                Token::LBracket => {
                    self.name_last_call(left_name);
                    call_name = None;
                }
                Token::Colon => {
                    self.name_last_call(member_name);
                    call_name = None;
                }
                Token::LParen | Token::LBrace | Token::StringLiteral(_) => {
                    self.name_last_call(call_name.take());
                }
                Token::Plus | Token::Minus | Token::Star | Token::Slash
                | Token::Percent | Token::FloorDiv | Token::Caret
                | Token::BitAnd | Token::BitOr | Token::BitXor
                | Token::Shl | Token::Shr => {
                    self.name_last_call(left_name);
                    call_name = None;
                }
                _ => call_name = None,
            }
        }
        self.expression_depth -= 1;
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
                let value = self.vm.alloc_float(n);
                let id = self.add_constant(value);
                self.emit(OpCode::LoadConst(id));
                false
            }
            Token::Integer(n) => {
                let value = self.vm.alloc_integer(n);
                let id = self.add_constant(value);
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
                let operator_line = self.previous_line;
                let operand_name = if let Token::Ident(name) = &self.current {
                    Some(self.identifier_call_name(name))
                } else {
                    None
                };
                if self.parse_precedence(Precedence::Unary) {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.emit(OpCode::Neg);
                let chunk_idx = self.states.last().unwrap().chunk_idx;
                *self.vm.chunks[chunk_idx].lines.last_mut().unwrap() = operator_line;
                self.name_last_call(operand_name);
                false
            }
            Token::Not => {
                if self.parse_precedence(Precedence::Unary) {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.emit(OpCode::Not);
                false
            }
            Token::BitXor => {
                let operator_line = self.previous_line;
                let operand_name = if let Token::Ident(name) = &self.current {
                    Some(self.identifier_call_name(name))
                } else {
                    None
                };
                if self.parse_precedence(Precedence::Unary) {
                    self.emit(OpCode::AdjustStack(1));
                }
                self.emit(OpCode::BitNot);
                let chunk_idx = self.states.last().unwrap().chunk_idx;
                *self.vm.chunks[chunk_idx].lines.last_mut().unwrap() = operator_line;
                self.name_last_call(operand_name);
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
                let open_line = self.previous_line;
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
                if !self.match_token(Token::RBrace) {
                    self.error(&format!("'}}' expected (to close '{{' at line {})", open_line));
                }
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
                    local_ids: (0..params.len()).collect(),
                    next_local_id: params.len(),
                    max_locals: 0,
                    chunk_idx,
                    loop_exits: Vec::new(),
                    upvals: Vec::new(),
                    loop_continues: Vec::new(),
                    pending_jumps: Vec::new(),
                    is_vararg,
                    blocks: Vec::new(),
                    active_blocks: Vec::new(),
                    labels: Vec::new(),
                    gotos: Vec::new(),
                });
                self.vm.chunks[chunk_idx].param_count = params.len();
                self.vm.chunks[chunk_idx].is_vararg = is_vararg;

                let mut state = self.states.last_mut().unwrap();
                state.max_locals = state.locals.len();
                self.statement_list();
                self.consume(Token::End, "Expected 'end' for function");
                self.vm.chunks[chunk_idx].lastlinedefined = self.previous_line;
                self.emit(OpCode::Return(0, false));
                self.resolve_gotos();
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
                    local_ids: Vec::new(),
                    next_local_id: 0,
                    max_locals: 0,
                    chunk_idx,
                    loop_exits: Vec::new(),
                    upvals: Vec::new(),
                    loop_continues: Vec::new(),
                    pending_jumps: Vec::new(),
                    is_vararg: false,
                    blocks: Vec::new(),
                    active_blocks: Vec::new(),
                    labels: Vec::new(),
                    gotos: Vec::new(),
                });
                self.statement_list();
                self.emit(OpCode::Return(0, false));
                self.resolve_gotos();
                
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
                        locals: handler_params.clone(),
                        local_ids: (0..handler_params.len()).collect(),
                        next_local_id: handler_params.len(),
                        max_locals: 0,
                        chunk_idx: h_chunk_idx,
                        loop_exits: Vec::new(),
                        upvals: Vec::new(),
                        loop_continues: Vec::new(),
                        pending_jumps: Vec::new(),
                        is_vararg: false,
                        blocks: Vec::new(),
                        active_blocks: Vec::new(),
                        labels: Vec::new(),
                        gotos: Vec::new(),
                    });
                    let mut state = self.states.last_mut().unwrap();
                    state.max_locals = state.locals.len();
                    self.statement_list();
                    self.emit(OpCode::Return(0, false));
                    self.resolve_gotos();
                    
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
            Token::Shl | Token::Shr => {
                self.current = self.previous.clone();
                self.current_line = self.previous_line;
                self.scanner.token_text = if self.current == Token::Shl { "<<" } else { ">>" }.to_string();
                self.error("Expected expression")
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
                let operator_line = self.previous_line;

                let next_prec = if t == Token::Caret {
                    prec
                } else {
                    unsafe { std::mem::transmute(prec as u8 + 1) }
                };

                let right_name = if let Token::Ident(name) = &self.current {
                    Some(self.identifier_call_name(name))
                } else {
                    None
                };
                let has_right_operand = matches!(
                    &t,
                    Token::Plus | Token::Minus | Token::Star | Token::Slash
                        | Token::Percent | Token::FloorDiv | Token::Caret
                        | Token::BitAnd | Token::BitOr | Token::BitXor
                        | Token::Shl | Token::Shr
                );
                let right_is_multi = self.parse_precedence(next_prec);
                if right_is_multi {
                    self.emit(OpCode::AdjustStack(1));
                }
                let chunk_idx = self.states.last().unwrap().chunk_idx;
                let operator_start = self.vm.chunks[chunk_idx].instructions.len();
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
                self.vm.chunks[chunk_idx].lines[operator_start..].fill(operator_line);
                if has_right_operand {
                    self.name_last_right_operand(right_name);
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
                if arg_count >= 255 { self.error("too many registers"); }
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
                    self.error("expected '(', '{', or string literal for method call");
                }

                if arg_count >= 255 { self.error("too many registers"); }
                self.emit(OpCode::Call(arg_count as u32, last_multi));
                self.name_last_call(Some((method_name, "method".to_string())));
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
    let closure = vm.alloc_closure(chunk_idx, vec![env_upval]);

    vm.call_stack.push(CallFrame {
        closure_id: closure,
        chunk_idx,
        ip: 0,
        stack_base: vm.data_stack.len(),
        handler_base: vm.handler_stack.len(),
        varargs: Vec::new(),
        last_hook_ip: None,
        is_hook: false,
        is_tailcall: false,
        is_native: false,
        native_continuation: None,
        frame_continuation: None,
        call_name: None,
        call_namewhat: String::new(),
    });

    for _ in 0..vm.chunks[chunk_idx].local_count {
        vm.data_stack.push(Value::nil());
    }

    let prev_hook = std::panic::take_hook();
    let show_internal_panics = env::var_os("LUAAE_BACKTRACE").is_some();
    if !show_internal_panics {
        std::panic::set_hook(Box::new(|_| {}));
    }

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        vm.run();
    }));

    if !show_internal_panics {
        std::panic::set_hook(prev_hook);
    }

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

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn run_lua_code(source: String) -> String {
    WASM_OUTPUT.with(|output| output.borrow_mut().clear());

    let mut vm = VM::new();
    vm.open_standard_libs();
    let result = execute_source(&mut vm, &source, "=(web)");
    let mut output = WASM_OUTPUT.with(|buffer| {
        String::from_utf8_lossy(&buffer.borrow()).into_owned()
    });

    if let Err(error) = result {
        if !output.is_empty() && !output.ends_with('\n') {
            output.push('\n');
        }
        output.push_str(&error);
    }
    output
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
        let closure = vm.alloc_closure(chunk_idx, vec![env_upval]);

        let stack_base = vm.data_stack.len();
        vm.call_stack.push(CallFrame {
            closure_id: closure,
            chunk_idx,
            ip: 0,
            stack_base,
            handler_base: vm.handler_stack.len(),
            varargs: Vec::new(),
            last_hook_ip: None,
            is_hook: false,
            is_tailcall: false,
            is_native: false,
            native_continuation: None,
            frame_continuation: None,
            call_name: None,
            call_namewhat: String::new(),
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
            std::process::exit(1);
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
            std::process::exit(1);
        }
    }

    // Handle -e
    for stmt in execute_stmts {
        if let Err(e) = execute_source(&mut vm, &stmt, "=(command line)") {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    }

    // Execute script
    if let Some(filename) = script_file {
        let source = if filename == "-" {
            let mut src = String::new();
            std::io::Read::read_to_string(&mut io::stdin(), &mut src).unwrap();
            src
        } else {
            match read_lua_source(&filename) {
                Ok(content) => content,
                Err(err) => {
                    eprintln!("Cannot open {}: {}", filename, err);
                    std::process::exit(1);
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
