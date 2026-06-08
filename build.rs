fn main() {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let out = std::process::Command::new(rustc)
        .arg("--print=sysroot")
        .output()
        .expect("failed to run `rustc --print=sysroot`");
    let sysroot = String::from_utf8(out.stdout)
        .expect("sysroot path is not valid UTF-8")
        .trim()
        .to_string();
    println!("cargo:rustc-link-arg=-Wl,-rpath,{sysroot}/lib");
    println!("cargo:rerun-if-changed=rust-toolchain.toml");
}
