vstd::prelude::verus! {
    use vstd::prelude::*;

    fn main() {}

    fn copy(a: & Vec < u64 >) -> (b: Vec < u64 >)
        requires
            a.len() <= 100,
        ensures
            b @.len() == a @.len(),
            forall | i: int |(0 <= i && i < a.len()) ==> b[i] == a[i],
    {
        let mut b = Vec::with_capacity(a.len());
        let mut n: usize = 0;
        let len: usize = a.len();
        while n != len
            invariant
                true,
                a.len() <= 100,
                len == a.len(),
                n <= len,
                b@.len() == n,
                forall |i: int| 0 <= i < n ==> b[i] == a[i],
            decreases len - n
        {
            b.push(a[n]);
            n = n + 1;
        }
        b
    }
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True
