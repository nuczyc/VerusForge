
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
            0 <= i as int <= N,
            // Invariant tracking the value in `a` for indices less than `i`; `a` is modified in this loop
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            old(a).len() == a.len(),
            sum.len() == 1,
            1 == 1,
            3 == 3,
            a.len() == N,
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
            0 <= i as int <= N,
            // Invariant tracking the value in `a` for indices less than `i`; `a` is modified in this loop
            forall |k: int| 0 <= k < i ==> a[k] == 4,
            old(a).len() == a.len(),
            sum.len() == 1,
            1 == 1,
            3 == 3,
            a.len() == N,
            N > 0,
            N < 1000,
            decreases(N as int - i as int),
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            // Assert that subtraction will not cause underflow
            proof {
                assert(a[(i) as int] == 4); // Corrected condition for established value
                assert(a[(i) as int] >= 1); // Therefore, value must be at least 1
            }
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i as int <= N,
            // Invariant tracking the sum computed so far; `a` is not modified in this loop
            forall |k: int| 0 <= k < a.len() ==> a[k] == 4, // Ensures coverage over every element
            sum[0] == 4 * i as int,
            old(a).len() == a.len(),
            sum.len() == 1,
            1 == 1,
            3 == 3,
            a.len() == N,
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