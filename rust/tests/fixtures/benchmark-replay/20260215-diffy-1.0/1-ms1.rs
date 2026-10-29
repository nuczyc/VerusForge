
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
        forall |k: int| 0 <= k < i ==> a[k as int] == (k % 1), 
        N > 0,
        decreases(N - i)
    {
        a.set(i, i % 1 );
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
    invariant
        0 <= i <= N,
        sum.len() == 1,
        a.len() == N,
        forall |k: int| 0 <= k < i ==> (if k == 0 { 0 } else { sum[0] }) + if k == 0 { 0 } else { a[k as int] } == sum[0], // Fixed by AI
        N > 0,
        decreases(N - i)
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        proof {
            helper_invariant(sum[0], a, i);
        }
        i = i + 1;
    }
}

proof fn helper_invariant(sum_0: usize, a: &Vec<usize>, i: usize)
    requires 
        a.len() > i,
    ensures 
        forall |k: int| 0 <= k < i ==> (if k == 0 { 0 } else { sum_0 }) + if k == 0 { 0 } else { a[k as int] } == sum_0
{
    assert(forall |k: int| 0 <= k < i ==> (if k == 0 { 0 } else { sum_0 }) + if k == 0 { 0 } else { a[k as int] } == sum_0);
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 4, Verus Errors: 4
// Safe: True