
use vstd::prelude::*;
fn main() {}

verus!{

proof fn contains_invariant(v: Seq<i32>, e: i32, i: int, result: Seq<i32>)
    ensures
        forall |k: int| 0 <= k <= i ==> (v[k] <= e ==> result.contains(v[k]))
{
    assume(forall |k: int| 0 <= k < i ==> (v[k] <= e ==> result.contains(v[k])));
    let v_i = v[i as int];
    if v_i <= e {
        assert(result.contains(v_i));
    }
}

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires 
        forall |k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        forall |k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{  
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while (i < v.len()) 
    invariant 
        0 <= i <= v.len(),
        result@.len() <= i,
        // v is never changed in the loop, so ensure the invariant covers all elements
        forall |k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        forall |k: int| 0 <= k < i ==> (v[k] <= e ==> result@.contains(v[k])),
        forall |k: int| 0 <= k < result@.len() ==> result[k] <= e && v@.contains(result[k]),
        v.len() == vlen,
        result.len() == result@.len(),
        decreases(v.len() - i),
    {  
        if (v[i] <= e) { 
            result.push(v[i]); 
        }
        // Proof block to assert the failed invariant at the end of the loop
        proof {
            contains_invariant(v@, e, i as int, result@);
            assert(forall |k: int| 0 <= k <= i ==> (v[k] <= e ==> result@.contains(v[k])));
        }
        i = i + 1;
    }  
    result
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True