
use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn copy(a: &Vec<u64>) -> (b: Vec<u64>)
    requires
        a.len() <= 100,
    ensures
        b@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> b[i] == a[i],
{
    let mut b = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    proof {
        assert(n >= 0);
        assert(n <= len);
    }
    while n != len
        invariant
            a.len() <= 100,
            b.len() == n, // Corrected by AI
            forall |k: int| 0 <= k < n ==> b[k] == a[k], // Corrected by AI
            a.len() == len,
            n >= 0,
            n <= len,
        decreases len - n
    {
        b.push(a[n]);
        n = n + 1;
    }
    b
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True