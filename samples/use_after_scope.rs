pub fn dangle() -> i32 {
    let p: *const i32;
    { let x = 5; p = &raw const x; }
    unsafe { *p }
}
