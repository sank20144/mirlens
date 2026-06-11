// summary: returns 2  (approximate: branches not modelled)
// The walk has no control-flow merge, so it just reports the last block's value.
pub fn pick(c: bool) -> i32 { if c { 1 } else { 2 } }
