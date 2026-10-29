vstd::prelude::verus! {
    use vstd::prelude::*;

    fn main() {}

    fn binary_search(v: & Vec < u64 >, k: u64) -> (r: usize)
        requires
            forall | i: int,
            j: int | 0 <= i <= j < v.len() ==> v[i] <= v[j],
            exists | i: int | 0 <= i < v.len() && k == v[i],
        ensures
            r < v.len(),
            k == v[r as int],
    {
        let mut i1: usize = 0;
        let mut i2: usize = v.len() - 1;
        while i1 != i2
            invariant
                true,
                forall | i: int,
                j: int | 0 <= i <= j < v.len() ==> v[i] <= v[j],
                exists | i: int | 0 <= i < v.len() && k == v[i],
                i1 <= i2,
                i2 < v.len(),
                exists | i: int | i1 <= i <= i2 && k == v[i],
            decreases i2 - i1
        {
            let ghost d = i2 - i1;
            let ix = i1 +(i2 - i1) / 2;
            if v[ix] < k {
                i1 = ix + 1;
            } else {
                i2 = ix;
            }
        }
        i1
    }
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True
