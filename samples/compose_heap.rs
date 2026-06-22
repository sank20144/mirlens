fn set(p: &mut i32, v: i32) { *p = v; }
pub fn caller() -> i32 {
    let mut x = 1;
    set(&mut x, 7);
    x
}
