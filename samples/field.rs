// summary: returns p.x   (read a struct field of an argument)
pub struct Point { pub x: i32, pub y: i32 }
pub fn get_x(p: Point) -> i32 { p.x }
