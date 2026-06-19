pub fn outer(x: i32) -> i32 { inner(x) + 1 }
fn inner(y: i32) -> i32 { y * 2 }
