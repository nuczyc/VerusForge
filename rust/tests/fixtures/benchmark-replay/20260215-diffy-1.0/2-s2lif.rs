
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
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
    invariant
        a.len() == N,
        sum.len() == 1,
        0 <= i <= N,
        forall |k: int| 0 <= k < i ==> a[k] == 1,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        a.len() == N,
        sum.len() == 1,
        0 <= i <= N,
        forall |k: int| 0 <= k < i ==> a[k] == 3,
        a[( i ) as int] == 1 || a[( i ) as int] == 3,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            assert(a[( i ) as int] == 3); 
            assert(a[( i ) as int] >= 1); 
            a.set(i, a[i] - 1);
        }
        i = i + 1;
        proof {
            // Establishing a proof that a[i - 1] == 3
            if i > 0 {
                assert(a[( i - 1 ) as int] == 3);
            }
        }
    }

    i = 0;
    while (i < N as usize)
    invariant
        a.len() == N,
        sum.len() == 1,
        0 <= i <= N,
        sum[0] == 3 * (i as i32),
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True