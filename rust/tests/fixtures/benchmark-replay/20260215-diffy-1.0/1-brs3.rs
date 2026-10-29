
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
        sum[0] <= 3 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall |k: usize| 0 <= k < i ==> if k % 3 == 0 { a[( k ) as int] == 3 } else { a[( k ) as int] == 0 },
            old(a).len() == N,
            old(sum).len() == 1,
            N > 0,
            N < 1000,
            decreases(N as isize - i as isize),
    {
        if (i % 3 == 0) {
            a.set(i, 3);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }

    i = 0;
    proof {
        initial_sum_bound(sum, i);
    }
    while (i < N as usize)
        invariant
            sum.len() == 1,
            sum[0] <= 3 * i as i32,
            a.len() == N,
            forall |k: usize| 0 <= k < N as usize ==> if k % 3 == 0 { a[( k ) as int] == 3 } else { a[( k ) as int] == 0 },
            old(a).len() == N,
            old(sum).len() == 1,
            N > 0,
            N < 1000,
            decreases(N as isize - i as isize),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
    proof {
        assert_final_sum_bound(sum, N);
        assert(sum[0] <= 3 * N);
    }
}

proof fn initial_sum_bound(sum: &Vec<i32>, i: usize) 
    ensures
        sum[0] <= 3 * i as i32,
{
    if sum.len() == 1 && i == 0 {
        assert(sum[0] <= 0); // At this point, sum[0] should be initialized or considered 0
    }
}

proof fn assert_final_sum_bound(sum: &Vec<i32>, N: i32)
    ensures
        sum[0] <= 3 * N,
{
    assert(sum[0] <= 3 * N);
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True