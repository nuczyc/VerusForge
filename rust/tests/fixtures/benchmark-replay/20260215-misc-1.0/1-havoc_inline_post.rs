
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
    requires 
        forall |k:int| 0 <= k < old(v).len() ==> old(v)[k] > 0,
        a > 0,
        b == false,
{  
    // Variables a and v are havocked. Their values are randomly reset, but their new values follow the following assumptions.
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);

    let c: bool = !b;
    let mut idx: usize = v.len();
    while (idx > 0)
    invariant a > 0, // The array v is modified through v.set(), so the invariant remains unchanged.
    decreases idx, // Added by AI
    {
        idx = idx - 1;
        v.set(idx, v[idx] + a);
    }
    
    proof {  // inline postcondition
        assert(20 < 2*a < 40);
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(c == true);
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True