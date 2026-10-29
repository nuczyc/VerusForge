
use vstd::prelude::*;
fn main() {}

verus!{

proof fn filter_property(x: Seq<u64>, y: Seq<u64>)
    requires
        y == x.filter(|k: u64| k % 3 == 0),
    ensures
        forall |k: int|
            0 <= k < x.len() ==> 
            ((x[k] % 3 == 0 && exists |m: int| 0 <= m < y.len() && y[m] == x[k]) || 
             (x[k] % 3 != 0 && !exists |m: int| 0 <= m < y.len() && y[m] == x[k]))
{
    assert forall |k: int| 0 <= k < x.len() implies 
        ((x[k] % 3 == 0 && exists |m: int| 0 <= m < y.len() && y[m] == x[k]) || 
         (x[k] % 3 != 0 && !exists |m: int| 0 <= m < y.len() && y[m] == x[k]))
    by {
        if x[k] % 3 == 0 {
            assert( exists |m: int| 0 <= m < y.len() && y[m] == x[k] );
        } else {
            assert( !exists |m: int| 0 <= m < y.len() && y[m] == x[k] );
        }
    }
}

#[verifier::loop_isolation(false)]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k: u64| k % 3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while (i < xlen) 
    invariant
        0 <= i && i <= xlen,
        forall |k: int| 0 <= k < y.len() ==> y[k] % 3 == 0,
        forall |k: int| 0 <= k < x.len() ==>
            ((x[k] % 3 == 0 && exists |m: int| 0 <= m < y.len() && y[m] == x[k]) || 
             (x[k] % 3 != 0 && !exists |m: int| 0 <= m < y.len() && y[m] == x[k])),
        y.len() <= i,
        old(y).len() == 0,
        y == y,
        x == x,
        x.len() == xlen,
        decreases(xlen - i),
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        i = i + 1;
    }
    proof {
        filter_property(x@, y@);
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True