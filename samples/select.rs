// summary: returns (if c { (x + 1) } else { (x - 1) })
// Both arms are followed and merged back into the branch they came from.
pub fn step(c: bool, x: i32) -> i32 { if c { x + 1 } else { x - 1 } }
