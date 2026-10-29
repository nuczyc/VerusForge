
use vstd::prelude::*;
fn main() {}

verus! {

spec fn filter_mod_3(x: Seq<u64>) -> Seq<u64> {
    x.filter(|k: u64| k % 3 == 0)
}

proof fn lemma_filter_mod_3_properties(x: Seq<u64>)
    ensures
        forall |k: int| 0 <= k < filter_mod_3(x).len() ==> filter_mod_3(x)[k] % 3 == 0,
{
    // Prove that all elements in the filtered sequence are divisible by 3
    assert forall |k: int| 0 <= k < filter_mod_3(x).len() ==> filter_mod_3(x)[k] % 3 == 0 by {
        let elem = filter_mod_3(x)[k];
        assert(elem % 3 == 0);
    }
}

proof fn lemma_filter_mod_3_correctness(x: Seq<u64>, y: Seq<u64>)
    ensures
        y == filter_mod_3(x) ==> forall |k: int| 0 <= k < x.len() && x[k] % 3 == 0 ==> y.contains(x[k]),
{
    // Prove that y contains all elements of x divisible by 3
    assert forall |k: int| 0 <= k < x.len() && x[k] % 3 == 0 ==> y.contains(x[k]) by {
        if x[k] % 3 == 0 {
            assert(y.contains(x[k]));
        }
    }
}

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
        forall |k: int| 0 <= k < xlen ==> x[k] == x[k],
        0 <= i && i <= xlen,
        forall |k: int| 0 <= k < y.len() ==> y[k] % 3 == 0,
        y.len() >= 0,
        x.len() == xlen,
        decreases(xlen - i),
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        i = i + 1;
    }
    
    proof {
        lemma_filter_mod_3_properties(x@);
        lemma_filter_mod_3_correctness(x@, y@);
        assert(y@ == filter_mod_3(x@));
    }
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True