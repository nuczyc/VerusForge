
use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 4 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == (k % 5) as i32,
            // Ensuring that the values are set correctly in a
            N > 0,
            N < 1000,
            decreases(N as usize - i),
    {
        a.set(i, (i % 5) as i32);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum.len() == 1,
            a.len() == N as usize,
            forall |k: usize| 0 <= k < N as usize ==> a[( k ) as int] == (k % 5) as i32,
            // a is not modified in this loop, ensuring complete coverage of a
            i > 0 ==> sum[0] <= 4 * i as i32,
            // The sum invariant tracks the sum of a, verifying it accumulates correctly
            N > 0,
            N < 1000,
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

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True