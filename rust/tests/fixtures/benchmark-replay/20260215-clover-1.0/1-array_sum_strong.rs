use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn sum(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] + b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] + #[trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    assert(n <= len); // Updated by AI to ensure the loop invariant is initially met
    while n != len
        invariant
            a.len() <= 100 && a.len() == b.len(),
            a.len() == len,
            b.len() == len,
            c.len() == n,
            forall|k: int| 0 <= k < len ==> a[k] + b[k] < 1000,
            0 <= n,
            n <= len, // Fixed by AI
            forall|k: int| (0 <= k && k < n) ==> c[k] == a[k] + b[k], // Added by AI
        decreases len - n,
    {
        assert(n < len); // Added by AI
        let sum: u32 = a[n] + b[n];
        c.push(sum);
        n = n + 1;
    }
    c
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True