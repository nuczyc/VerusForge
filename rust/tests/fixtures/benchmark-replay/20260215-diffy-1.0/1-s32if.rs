
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
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
    while (i < N)
        invariant 
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            // all indices before i have been set to 1
            forall |k: usize| 0 <= k < i ==> a[(k) as int] == 1,
            N > 0,
            N < 1000,
            decreases(N - i)
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N)
        invariant 
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            // all indices before i have been incremented to 4
            forall |k: usize| 0 <= k < i ==> a[(k) as int] == 4,
            N > 0,
            N < 1000,
            decreases(N - i)
    {
        proof {
            assert(forall |k: usize| 0 <= k < N ==> a[(k) as int] == 1 || a[(k) as int] == 4);
            // At the first iteration, a[i] is 1; in the following steps, previous loop invariant shows those indices
            // are turned from 1 to 4.
        }
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            assert(a[(i) as int] == 4);
            assert(a[(i) as int] > 1);
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N)
        invariant 
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            // sum value is the sum of all 4 values from a[0..i]
            sum[0] == 4 * i,
            N > 0,
            N < 1000,
            decreases(N - i)
    {
        if (a[i] == 4) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True