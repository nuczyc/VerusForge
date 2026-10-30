vstd::prelude::verus! {
    use vstd::prelude::*;

    spec fn max(x: u64, y: u64) -> u64 {
        if x > y {
            x
        } else {
            y
        }
    }

    fn slow_max(a: u64, b: u64) -> (z: u64)
        ensures
            z == max(a, b),
    {
        let mut x = a;
        let mut y = b;
        let mut counter: u64 = 0;
        while x > 0 && y > 0
            invariant
                counter <= a,
                counter <= b,
                x == a - counter,
                y == b - counter,
            decreases
                counter,
        {
            x -= 1;
            y -= 1;
            counter = counter.wrapping_add(1);
        }
        let m = if x > y {
            x
        } else {
            y
        };
        counter.wrapping_add(m)
    }

    fn main() {}
}

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True
