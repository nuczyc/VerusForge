
use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires 
        forall |k1:int, k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{  
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while (i < v.len()) 
    invariant
        0 <= i <= v.len(),
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        result.len() <= i, // Corrected by AI
        v.len() == vlen,
        decreases(v.len() - i),
    {  
        if (v[i] <= e) { 
            result.push(v[i]); 
        }
        i = i + 1;
    }
    proof {
        assert(result.len() <= i);
    } 

    result
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True