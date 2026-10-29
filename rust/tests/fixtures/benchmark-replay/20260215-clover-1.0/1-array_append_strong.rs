
use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn append(v: &Vec<u64>, elem: u64) -> (c: Vec<u64>)
    requires
        v.len() <= 100,
    ensures
        c@.len() == v@.len() + 1,
        forall|i: int| (0 <= i && i < v.len()) ==> c[i] == v[i],
        c@.last() == elem,
{
    let mut c = Vec::with_capacity(v.len() + 1);
    let mut n: usize = 0;
    let len: usize = v.len();
    assert(n <= len); // Fixed by AI
    while n != len
        invariant
            v.len() <= 100,
            c.len() == n,
            v.len() == len,
            forall|k: int| 0 <= k < v.len() ==> c.len() > k ==> c[k] == v[k],
            v.len() == len, // Invariant specifying the array length.
            n >= 0, // Invariant about the array index not under bound.
            n <= len, // Fixed invariant for ensuring index is within bounds.
            n <= len  // Preserve relation,
        decreases len - n
    {
        c.push(v[n]);
        n = n + 1;
    }
    c.push(elem);
    c
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True