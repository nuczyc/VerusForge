
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;

    while (i < N as usize)
    invariant
        // Basic invariant establishment
        0 <= i <= N as usize,
        // Maintain the lengths of the arrays
        a.len() == N as usize,
        sum.len() == 1,
        // Array writing pattern: a[k] == k % 3 for all processed indices
        forall |k: int| 0 <= k < i ==> a[k as int] == (k % 3) as i32,
        // Decrease clause
        decreases(N as usize - i),
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }

    i = 0;

    while (i < N as usize)
    invariant
        // Basic invariant establishment
        0 <= i <= N as usize,
        // Ensure initial condition and accumulative sum
        sum.len() == 1,
        a.len() == N as usize,
        // Modified loop invariant to cover all elements `j` in array `a` since there is no `a.set()` in this loop
        forall |j: int| 0 <= j < a.len() ==> if j == 0 { sum[0] == 0 } else { sum[0] == old(sum)[0] + a[j as int] },
        // Ensure partial sum correctness: sum[0] <= 2 * i
        sum[0] <= 2 * i as i32,
        // Decrease clause
        decreases(N as usize - i),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True