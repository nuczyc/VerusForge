
use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_int_addition_does_not_overflow(v: u32, a: u32)
    requires 
        v == 1,
        10 < a < 20,
    ensures
        v + a <= u32::MAX,
{
    assert(v + a == 1 + a);
    assert(1 + a <= 1 + 19);
    assert(1 + 19 <= u32::MAX);
}

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
    invariant
        a > 0,
        v.len() == v.len(), 
        idx <= v.len(),
        forall |k:int| 0 <= k < v.len() - idx ==> v[k] == 1 + a,
        decreases(idx),
    {
        idx = idx - 1;

        // Asserting that the addition will not overflow
        proof {
            assert(v[( idx ) as int] == 1);
        } // Added by AI
        assert(v[( idx ) as int] + a <= u32::MAX) by {
            lemma_int_addition_does_not_overflow(v[( idx ) as int], a);
        }

        v.set(idx, v[idx] + a);
    }
    
    proof {  // inline postcondition
        assert(20 < 2*a < 40);
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(c == true);
    }
}

}


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True