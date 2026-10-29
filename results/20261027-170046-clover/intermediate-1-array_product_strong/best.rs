vstd::prelude::verus! {
    use vstd::prelude::*;

    fn main() {}

    fn product(a: & Vec < u32 >, b: & Vec < u32 >) -> (c: Vec < u32 >)
        requires
            a.len() <= 100 && a.len() == b.len(),
            forall | i: int |(0 <= i && i < a.len()) ==>(a[i] * b[i] < 1000),
        ensures
            c @.len() == a @.len(),
            forall | i: int |(0 <= i && i < a.len()) ==> c[i] ==#[trigger] a[i] *#[trigger] b[i],
    {
        let mut c = Vec::with_capacity(a.len());
        let mut n: usize = 0;
        let len: usize = a.len();
        while n != len
            invariant
                true,
                a.len() <= 100 && a.len() == b.len(),
                forall | i: int |(0 <= i && i < a.len()) ==>(a[i] * b[i] < 1000),
                n <= len,
                len == a.len(),
                len == b.len(),
                c@.len() == n,
                forall | i: int | (0 <= i && i < n) ==> c[i] == #[trigger] a[i] * #[trigger] b[i],
            decreases
                len - n
        {
            let product: u32 = a[n] * b[n];
            c.push(product);
            n = n + 1;
        }
        c
    }
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True
