// summary: returns 7  (write through a reference)
pub fn h() -> i32 { let mut x = 1; let r = &mut x; *r = 7; x }
