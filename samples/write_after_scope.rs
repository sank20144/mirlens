pub fn clobber() {
    let p: *mut i32;
    { let mut x = 5; p = &raw mut x; }
    unsafe { *p = 9; }
}
