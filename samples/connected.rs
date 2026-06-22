pub fn double(x: i32) -> i32 { x * 2 }
pub fn inc(x: i32) -> i32 { x + 1 }
fn scale(x: i32) -> i32 { double(x) + inc(x) }
fn combo(x: i32) -> i32 { scale(double(x)) }
pub fn top(x: i32) -> i32 { combo(x) + scale(x) }
