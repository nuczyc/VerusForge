use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] * #[trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    while n != len
        invariant
            a.len() <= 100,
            a.len() == b.len(),
            c.len() <= n, 
            n <= a.len(),
            a.len() == len,
            b.len() == len,
            forall |k: int| 0 <= k < c.len() ==> c[k] == a[k] * b[k], // Added by AI
            forall |k: int| 0 <= k < a.len() ==> a[k] * b[k] < 1000,
        decreases len - n
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
        proof {
            assert(c.len() <= n);
            assert(n <= a.len());
            assert(forall |k: int| 0 <= k < c.len() ==> c[k] == a[k] * b[k]);
        }
    }
    proof {
    assert(forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i] * b[i]);  // Add proof computation
    assert(forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i] * b[i]);  // Add proof computation
    assert(forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i] * b[i]);  // Add proof computation
        assert(forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i] * b[i]);
    } // Added by AI
    c
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True