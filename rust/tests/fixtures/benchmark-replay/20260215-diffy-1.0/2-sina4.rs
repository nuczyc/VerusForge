
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k:int| 0 <= k < N ==> b[k] == N + 2,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
    invariant
        i <= N as usize,
        a.len() == N as usize,
        b.len() == N as usize,
        sum.len() == 1,
        forall |k: int| 0 <= k < i ==> a[k as int] == 1,
        N > 0, N < 1000,
        decreases(N as usize - i),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        i <= N as usize,
        a.len() == N as usize,
        sum.len() == 1,
        b.len() == N as usize,
        sum[0] == i as i32,
        forall |k: int| 0 <= k < N ==> a[k as int] == 1, // `a` is not changed in this loop
        N > 0, N < 1000,
        decreases(N as usize - i),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        i <= N as usize,
        a.len() == N as usize,
        b.len() == N as usize,
        sum.len() == 1,
        forall |k: int| 0 <= k < i ==> a[k as int] == N + 1, // `a` is modified in this loop
        sum[0] == N,
        N > 0, N < 1000,
        decreases(N as usize - i),
    {
        assert(a[i as int] == 1);
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        i <= N as usize,
        a.len() == N as usize,
        b.len() == N as usize,
        sum.len() == 1,
        forall |k: int| 0 <= k < N ==> a[k as int] == N + 1, // `a` is not changed in this loop
        forall |k: int| 0 <= k < i ==> b[k as int] == N + 2, // `b` is modified in this loop
        N > 0, N < 1000,
        decreases(N as usize - i),
    {
        b.set(i, a[i] + 1);
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True