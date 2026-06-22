fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo { lo } else if x > hi { hi } else { x }
}

fn sum_to(n: i32) -> i32 {
    let mut total = 0;
    let mut i = 0;
    while i < n {
        total += i;
        i += 1;
    }
    total
}

fn grade(score: i32) -> i32 {
    match score {
        0 => 1,
        1 => 2,
        _ => 0,
    }
}

pub fn run(flag: bool) -> i32 {
    let base = clamp(7, 0, 5);
    let s = sum_to(3);
    let g = grade(1);
    if flag { base + s + g } else { base - s }
}

pub fn maybe_dangle(c: bool) -> i32 {
    let outer = 10;
    let p: *const i32;
    {
        let inner = 20;
        p = if c { &raw const inner } else { &raw const outer };
    }
    unsafe { *p }
}
