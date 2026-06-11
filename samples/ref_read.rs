// summary: returns 5  (read through a reference)
pub fn g() -> i32 { let x = 5; let r = &x; *r }
