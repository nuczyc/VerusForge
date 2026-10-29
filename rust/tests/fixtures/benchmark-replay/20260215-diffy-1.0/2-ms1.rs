
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] == 0,
{
    let mut i: usize = 0;
    while (i < N as usize)
    invariant
        0 <= i <= N,
        a.len() == N,
        sum.len() == 1,
        N > 0,
        forall |k: int| 0 <= k < i ==> a[k] == k % 1,
        decreases(N - i),
    {
        a.set(i, i % 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        0 <= i <= N,
        sum.len() == 1,
        a.len() == N,
        N > 0,
        forall |k: int| 0 <= k < i ==> if k == 0 { sum[0] == 0 } else { sum[0] == sum[0] + a[k] },
        i > 0 ==> sum[0] == 0, // Conditioned on the loop index
        decreases(N - i),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True