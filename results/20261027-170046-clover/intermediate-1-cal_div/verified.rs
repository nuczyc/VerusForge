vstd::prelude::verus! {
    use vstd::prelude::*;

    fn cal_div() -> (r: (u32, u32))
        ensures
            r.0 == 27,
            r.1 == 2,
    {
        let mut x: u32 = 0;
        let mut y: u32 = 191;
        while 7 <= y
            invariant
                x <= 27,
                y == 191 - 7 * x,
                7 * x <= 191,
                y <= 191,
            decreases y,
        {
            x = x + 1;
            y = 191 - 7 * x;
        }
        (x, y)
    }

    fn main() {}
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True
