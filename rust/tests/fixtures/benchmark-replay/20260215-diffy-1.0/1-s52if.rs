
use vstd::prelude::*;
fn main() {}

verus!{
    pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
        requires
            N > 0,
            old(a).len() == N,
            old(sum).len() == 1,
            N < 1000,
        ensures
            sum[0] == 6 * N,
    {
        let mut i: usize = 0;
        sum.set(0, 0);

        while (i < N)
        invariant
            0 <= i <= N,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1,
            forall |k: usize| i <= k < N ==> old(a)[( k ) as int] == a[( k ) as int],
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            decreases(N - i),
        {
            a.set(i, 1);
            i = i + 1;
        }

        i = 0;
        while (i < N)
        invariant
            0 <= i <= N,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 6,
            forall |k: usize| i <= k < N ==> a[( k ) as int] == 1,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            decreases(N - i),
        {
            if (a[i] == 1) {
                a.set(i, a[i] + 5);
            } else {
                a.set(i, a[i] - 1);
            }
            i = i + 1;
        }

        i = 0;
        while (i < N)
        invariant
            0 <= i <= N,
            sum[0] == 6 * i,
            forall |k: usize| 0 <= k < N ==> a[( k ) as int] == 6,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            decreases(N - i),
        {
            if (a[i] == 6) {
                sum.set(0, sum[0] + a[i]);
            } else {
                sum.set(0, sum[0] * a[i]);
            }
            i = i + 1;
        }
    }
}

// Score: Compilation Error: False, Verified: 4, Errors: 0, Verus Errors: 0
// Safe: True