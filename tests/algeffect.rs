use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn cases_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/algeffect")
}

fn run_case(name: &str) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_luaae"))
        .arg(cases_dir().join(name))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .unwrap_or_else(|error| panic!("failed to execute {name}: {error}"))
}

#[test]
fn algebraic_effect_cases_pass() {
    let mut cases: Vec<_> = fs::read_dir(cases_dir())
        .expect("read algeffect cases")
        .map(|entry| entry.expect("read algeffect entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "lua"))
        .filter(|path| !path.file_name().is_some_and(|name| name == "unhandled.lua"))
        .collect();
    cases.sort();

    assert!(!cases.is_empty(), "no algeffect cases were discovered");
    let mut failures = String::new();
    for case in cases {
        let name = case.file_name().unwrap().to_string_lossy();
        let output = run_case(&name);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        if !output.status.success() || stdout.lines().last() != Some("OK") {
            failures.push_str(&format!(
                "\n{name} failed (status {}):\nstdout:\n{stdout}\nstderr:\n{stderr}\n",
                output.status
            ));
        }
    }
    assert!(failures.is_empty(), "{failures}");
}

#[test]
fn unhandled_effect_is_an_error() {
    let output = run_case("unhandled.lua");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "unhandled effect unexpectedly succeeded"
    );
    assert!(
        stderr.contains("unhandled effect 'Missing'"),
        "unexpected diagnostic:\n{stderr}"
    );
    assert!(
        stderr.contains("stack traceback:"),
        "missing traceback:\n{stderr}"
    );
}
