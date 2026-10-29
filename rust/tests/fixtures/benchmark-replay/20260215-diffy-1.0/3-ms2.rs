
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]

/// helper function to show sum cannot exceed N 
proof fn lemma_sum_plus_one_leq_N(sum: usize, N: usize) 
    requires sum <= N
    ensures sum + 1 <= N + 1
{
    assert(sum <= N);
    assert(sum + 1 <= N + 1);
}

/// helper function specifically for proving sum[0] + 1 <= N
proof fn lemma_sum_plus_one_leq_N_specific(sum: usize, N: usize)
    requires sum <= N
    ensures sum + 1 <= N
{
    assert(sum < N); // Since sum == N would have sum + 1 > N
}

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
    invariant 
        a.len() == N,
        i <= N,
        N > 0,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == k % 2,
        decreases(N - i)
    {
        a.set(i, i % 2 );
        i = i + 1;
    }

    i = 0;
    assert(sum[0] <= N); // Added by AI
    
    while (i < N as usize)
    invariant 
        sum.len() == 1,
        a.len() == N,
        i <= N,
        sum[0] <= N,
        N > 0,
        forall |k: usize| 0 <= k < N ==> a[( k ) as int] == k % 2, // 'a' is not modified in this loop
        sum[0] == sum[0],
        decreases(N - i)
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            // Proof for asserting that adding a[i] will not cause an overflow
            assert(a[(i) as int] <= 1);  // since k % 2 is either 0 or 1
            assert(sum[0] + a[(i) as int] <= sum[0] + 1);  // since a[i] <= 1
            
            proof {
                lemma_sum_plus_one_leq_N(sum[0], N);
                lemma_sum_plus_one_leq_N_specific(sum[0], N);
            }

            assert(sum[0] + 1 <= N);  // since sum[0] <= N and a[i] is 0 or 1
            assert(sum[0] + a[(i) as int] <= N);
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 2
// Safe: True