
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 5 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            0 <= i <= N,
            old(a).len() == a.len(),
            sum.len() == 1,
            a.len() == N as usize,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1,
            forall |k: usize| i <= k < a.len() ==> a[( k ) as int] == old(a)[( k ) as int],
            N > 0,
            N < 1000,
            decreases(N as usize - i),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            old(a).len() == a.len(),
            sum.len() == 1,
            a.len() == N as usize,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 5,
            forall |k: usize| i <= k < a.len() ==> a[( k ) as int] == 1,
            N > 0,
            N < 1000,
            decreases(N as usize - i),
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 4);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            old(a).len() == a.len(),
            sum.len() == 1,
            a.len() == N as usize,
            sum[0] == i * 5,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 5,
            forall |k: usize| i <= k < a.len() ==> a[( k ) as int] == 5,
            N > 0,
            N < 1000,
            decreases(N as usize - i),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 4, Errors: 0, Verus Errors: 0
// Safe: True