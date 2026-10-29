vstd::prelude::verus! {
    use vstd::prelude::*;

    fn main() {}

    pub fn linear_search(a: & Vec < i32 >, e: i32) -> (n: usize)
        requires
            exists | i: int |(0 <= i < a.len() as int) && a[i] == e,
        ensures
            0 <= n < a.len(),
            a[n as int] == e,
            forall | k: int |(0 <= k < n as int) ==> a[k] != e,
    {
        let mut n: usize = 0;
        while n != a.len()
            invariant
                true,
                n <= a.len(),
                exists | i: int |(0 <= i < a.len() as int) && a[i] == e,
                forall | k: int |(0 <= k < n as int) ==> a[k] != e,
            decreases a.len() - n
        {
            if a[n] == e {
                return n;
            }
            n = n + 1;
        }
        n
    }
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True
