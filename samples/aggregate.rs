// summary: returns 3   (build a struct, then read a field back out)
pub struct Point { pub x: i32, pub y: i32 }
pub fn build() -> i32 { let p = Point { x: 3, y: 4 }; p.x }
