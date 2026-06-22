pub fn two_refs() -> i32 { let x = 5; let a = &x; let b = &x; *a + *b }
