
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
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            // Critical Loop Invariants Added
            a.len() == N,
            sum.len() == 1,
            0 <= i <= N,
            // Specific invariant about the write pattern of 'a'
            forall |k: int| 0 <= k < i ==> a[k] == 3,
            // Preconditions
            old(a).len() == N,
            old(sum).len() == 1,
            N < 1000,
            N > 0,
        decreases(N - i as i32)
    {
        a.set(i, 3);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            // Critical Loop Invariants Added
            a.len() == N,
            sum.len() == 1,
            0 <= i <= N,
            // Specific invariant about the write pattern of 'a'
            forall |k: int| 0 <= k < N ==> a[k] == 3, // `a` is never modified in this loop
            // Tracking current value of sum
            sum[0] == 3 * i,
            // Preconditions
            old(a).len() == N,
            old(sum).len() == 1,
            N < 1000,
            N > 0,
        decreases(N - i as i32)
    {
        if (a[i] == 3) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True