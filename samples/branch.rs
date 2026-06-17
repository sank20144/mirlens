// summary: returns (if c { 1 } else { 2 })
// The two arms are followed separately and merged back into a conditional.
pub fn pick(c: bool) -> i32 { if c { 1 } else { 2 } }
