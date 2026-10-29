
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    ensures
        sum <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
    invariant
        0 <= i <= N as usize,
        old(a).len() == a.len(),
        a.len() == N as usize,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] <= 2,
        forall |k: usize| i <= k < N as usize ==> old(a)[( k ) as int] == a[( k ) as int],
        N <= 0x7FFF_FFFF,
        decreases(N as int - i as int),
    {
        if a[i] > 2 
        {
            a.set(i, 2);
        } 
        i = i + 1;
    }

    i = 0;
    let mut sum: u32 = 0;
    
    while (i < N as usize)
    invariant
        0 <= i <= N as usize,
        sum <= 2 * i as u32,
        old(a).len() == a.len(),
        a.len() == N as usize,
        forall |k: usize| 0 <= k < N as usize ==> a[( k ) as int] <= 2,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] <= 2,
        N <= 0x7FFF_FFFF,
        decreases(N as int - i as int),
    {
        sum = sum + a[i];
        i = i + 1;
    }

    sum
}
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True