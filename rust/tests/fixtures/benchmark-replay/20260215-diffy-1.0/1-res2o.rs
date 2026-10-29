
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
    invariant
        // Precondition
        N > 0 &&
        old(a).len() == N &&
        i <= N as usize &&
        old(b).len() == N &&
        old(c).len() == N &&
        old(sum).len() == 1 &&
        N < 1000,
        // Loop Specific Invariants
        a.len() == N as usize,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1,
        decreases(N as usize - i),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        // Precondition
        N > 0 &&
        old(b).len() == N &&
        i <= N as usize &&
        old(a).len() == N &&
        old(c).len() == N &&
        old(sum).len() == 1 &&
        N < 1000,
        // Loop Specific Invariants
        b.len() == N as usize,
        forall |k: usize| 0 <= k < i ==> b[( k ) as int] == 1,
        decreases(N as usize - i),
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        // Precondition
        N > 0 &&
        old(c).len() == N &&
        i <= N as usize &&
        old(a).len() == N &&
        old(b).len() == N &&
        old(sum).len() == 1 &&
        N < 1000,
        // Loop Specific Invariants
        c.len() == N as usize,
        forall |k: usize| 0 <= k < i ==> c[( k ) as int] == 1,
        decreases(N as usize - i),
    {
        c.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        // Precondition
        N > 0 &&
        old(sum).len() == 1 &&
        i <= N as usize &&
        old(a).len() == N &&
        old(b).len() == N &&
        old(c).len() == N &&
        N < 1000,
        // Loop Specific Invariants
        sum.len() == 1,
        a.len() == N as usize,
        0 <= sum[0] <= i,
        decreases(N as usize - i),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        // Precondition
        N > 0 &&
        old(sum).len() == 1 &&
        i <= N as usize &&
        old(a).len() == N &&
        old(b).len() == N &&
        old(c).len() == N &&
        N < 1000,
        // Loop Specific Invariants
        sum.len() == 1,
        b.len() == N as usize,
        0 <= sum[0] <= N + i,
        decreases(N as usize - i),
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        // Precondition
        N > 0 &&
        old(sum).len() == 1 &&
        i <= N as usize &&
        old(a).len() == N &&
        old(b).len() == N &&
        old(c).len() == N &&
        N < 1000,
        // Loop Specific Invariants
        sum.len() == 1,
        c.len() == N as usize,
        0 <= sum[0] <= 2 * N + i,
        decreases(N as usize - i),
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}
}
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True