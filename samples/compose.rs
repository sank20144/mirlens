pub fn quad(x: i32) -> i32 { double(double(x)) }
fn double(x: i32) -> i32 { x * 2 }

pub fn ten() -> i32 { add(4, 6) }
fn add(a: i32, b: i32) -> i32 { a + b }
