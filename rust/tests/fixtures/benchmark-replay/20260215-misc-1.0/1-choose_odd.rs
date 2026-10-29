
use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut j: usize = 0;
    while (j < v.len())
        invariant
            v.len() == v.len(), // invariant about unchanged length
            forall |k: int| 0 <= k < v.len() ==> v[k] == v[k], // invariant about unchanged elements
            0 <= j && j <= v.len(), // loop counter within bounds
            exists |q: int| j <= q < v.len() && v[q] % 2 == 1, // there is still an odd number to be found
            decreases(v.len() - j) // decreases function for termination check
    {
        if v[j] % 2 == 1 {
            return j;
        }
        j = j + 1;
    }
    j
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True