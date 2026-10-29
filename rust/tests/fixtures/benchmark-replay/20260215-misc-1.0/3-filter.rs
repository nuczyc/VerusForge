
use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while (i < xlen)
    invariant 
        old(y).len() == 0,
        0 <= i <= xlen,
        x.len() == xlen,
        y.len() == y.len(), // Assuming the length is invariant within each loop step.
        forall |k: int| 0 <= k < i ==> (
            if x[k as int] % 3 == 0 {
                exists |j: int| 0 <= j < y.len() && y[j] == x[k as int]
            } else {
                forall |j: int| 0 <= j < y.len() ==> y[j] != x[k as int]
            }
        ),
        forall |j: int| 0 <= j < y.len() ==> y[j] % 3 == 0,
    decreases(xlen - i),
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        i = i + 1;
        proof {
            let x_last_index = i as int - 1;
            assert(forall |k: int| 0 <= k <= x_last_index ==> (
                if x[k] % 3 == 0 {
                    exists |j: int| 0 <= j < y.len() && y[j] == x[k]
                } else {
                    forall |j: int| 0 <= j < y.len() ==> y[j] != x[k]
                }
            )) by {
                // Handle existing invariants for all k < i - 1
                assert(forall |k: int| 0 <= k < x_last_index ==> (
                    if x[k] % 3 == 0 {
                        exists |j: int| 0 <= j < y.len() && y[j] == x[k]
                    } else {
                        forall |j: int| 0 <= j < y.len() ==> y[j] != x[k]
                    }
                ));

                // Handle for k = i - 1
                if x[x_last_index] % 3 == 0 {
                    assert(y.len() > 0);
                    let j = y.len() - 1;
                    assert(y[j] == x[x_last_index]);
                } else {
                    assert(forall |j: int| 0 <= j < y.len() ==> y[j] != x[x_last_index]);
                }
            };
        }
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True