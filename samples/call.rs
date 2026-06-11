// summary: returns (inner(x) + 1)   (outer; inner itself reports (y * 2))
pub fn outer(x: i32) -> i32 { inner(x) + 1 }
fn inner(y: i32) -> i32 { y * 2 }
