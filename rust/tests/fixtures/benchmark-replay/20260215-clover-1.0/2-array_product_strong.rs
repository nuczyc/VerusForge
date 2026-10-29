
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
    assert(n < a.len()); // Added by AI
    while n != len
        invariant
            a.len() <= 100 && a.len() == b.len(), // Repeated invariant
            a.len() == len, // Invariant for the length of array a
            b.len() == len, // Invariant for the length of array b
            0 <= n, // Invariant to specify the array index is not under bound
            n <= a.len(), // Invariant to specify the array index is within bounds
            c.len() <= len, // Invariant for the length of array c, as it grows
            forall|i: int| (0 <= i && i < n) ==> c[i] == #[trigger] a[i] * #[trigger] b[i], // Ensures c's current elements are the products
            forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000), // Invariant ensuring every element in a and b upholds the property
        decreases (len - n) // Added by AI: Decreases clause to help prove termination
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
        
        proof {
            assert(c.len() == n); // Assertion adjusted to use equality for better verification context
        }
    }
    c
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True