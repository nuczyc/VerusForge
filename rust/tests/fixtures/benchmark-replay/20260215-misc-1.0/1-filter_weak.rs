
use vstd::prelude::*;
fn main() {}

verus!{

pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while (i < xlen)
    invariant
        old(y).len() == 0,
        0 <= i && i <= xlen, // Upper bound invariant
        forall |k: int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
        0 <= i && i <= xlen,
        x.len() == xlen,
        0 <= y.len(),
        decreases(xlen - i),
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        i = i + 1;
    }
 }
}

// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True