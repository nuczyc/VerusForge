
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N as usize,
        old(sum).len() == 1,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1 || a[( k ) as int] == 0,
            forall |k: usize| i <= k < N as usize ==> old(a)[( k ) as int] == a[( k ) as int],
            N > 0,
            decreases(N as usize - i),
    {
        if (i % 1 == 0) {
            a.set(i, 1);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            i > 0 ==> sum[0] <= i as i32,
            N > 0,
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


// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: False