
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun2(x: &mut Vec<i32>) 
requires 
    forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
ensures 
    x@.len() == old(x)@.len(),
    forall |k:int| 0 <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k] + 4,
{
    let mut i: usize = 0;
    let xlen: usize = x.len();
    while (i < xlen) 
    invariant
        x.len() == xlen,
        0 <= i && i <= xlen,
        forall |k: int| 0 <= k < i ==> x[k as int] == old(x)[k as int] + 4,
        // Not making changes to the next invariant because x is modified in the loop
        forall |k: int| i <= k < x.len() ==> x[k as int] == old(x)[k as int],
        // Not making changes to the next invariant because x is modified in the loop
        forall |k: int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB, 
        decreases(xlen - i),
    { 
        x.set(i, x[i] + 4);  
        i = i + 1;
    }  
}
}
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True