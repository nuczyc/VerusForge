
use vstd::prelude::*;
fn main() {}

verus! {

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
            vlen == v.len(),
            result.len() >= 0, // Added invariant for result array length
            forall |k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < v.len() ==> v[k] == v[k], // Loop body does not modify v
            decreases(v.len() - i),
    {  
        if (v[i] <= e) { 
            result.push(v[i]); 
        }
        i = i + 1;
        proof {
            lemma_result_contains_up_to_i(result@, v, e, i);
            assert(forall |k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k])) by {
                if i > 0 {
                    let k = i - 1;
                    if v[k] <= e {
                        lemma_result_contains(result@, v[k]);
                    }
                }
            };
        }
    }  
    result
}

proof fn lemma_result_contains_up_to_i(result: Seq<i32>, v: Vec<i32>, e: i32, i: usize)
    requires
        0 <= i < v.len(),
        v[(i) as int] <= e,
        result.contains(v[(i) as int]),
    ensures
        result.contains(v[(i) as int])
{
    assert(result.contains(v[(i) as int]));
}

proof fn lemma_result_contains(result: Seq<i32>, val: i32)
    requires
        result.contains(val),
    ensures
        result.contains(val)
{
    assert(result.contains(val));
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True