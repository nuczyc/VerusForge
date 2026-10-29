
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
    invariant 
        i <= N as usize,
        old(a).len() == N,
        sum.len() == 1,
        a.len() == N,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1,
        decreases(N as usize - i)
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant 
        i <= N as usize,
        old(a).len() == N,
        sum.len() == 1,
        a.len() == N,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 4,
        decreases(N as usize - i)
    {
        proof {
            assert(forall |k: usize| 0 <= k < N as usize ==> a[k as int] == 1);
            assert(a[( i ) as int] == 1); // Value set to 1 in the previous loop
        }
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            assert(a[( i ) as int] > 1); // Assertion to prevent underflow
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant 
        i <= N as usize,
        old(sum).len() == 1,
        sum.len() == 1,
        old(a).len() == N,
        a.len() == N,
        forall |k: usize| 0 <= k < a.len() ==> a[( k ) as int] == 4,
        sum[0] == 4 * i,
        decreases(N as usize - i)
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True