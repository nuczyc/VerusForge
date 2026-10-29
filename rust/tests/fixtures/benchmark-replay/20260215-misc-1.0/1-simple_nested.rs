
use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_after_inner_loop(a: &Vec<i32>, b: &Vec<i32>, i: usize, j: usize)
    requires
        a.len() == b.len(),
        j == i,
        forall |k: usize| 0 <= k < i ==> a[(k) as int] == b[(k) as int],
        a[(i) as int] == b[(i) as int] + 1 - j,
    ensures
        a[(i) as int] == b[(i) as int],
        forall |k: usize| 0 <= k <= i ==> a[(k) as int] == b[(k) as int]
{
    assert(a[(i) as int] == b[(i) as int] + 1 - i);
    assert(b[(i) as int] == b[(i) as int] + 1 - i);
    assert(a[(i) as int] == b[(i) as int]);
    assert(forall |k: usize| 0 <= k < i ==> a[(k) as int] == b[(k) as int]);
    assert(forall |k: usize| 0 <= k <= i ==> a[(k) as int] == b[(k) as int]);
}

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2*N
{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize) 
    invariant
        0 <= i <= N,
        N <= sum + (N - i) && sum + (N - i) <= 2 * N,
        a.len() == N,
        b.len() == N,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == b[( k ) as int],
        N <= 0x3FFF_FFFF,
        decreases(N as int - i as int)
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
        invariant
            0 <= j <= i,
            a.len() == N,
            b.len() == N,
            a[( i ) as int] == b[( i ) as int] + 1 - j,
            forall |k: usize| 0 <= k < i ==> a[( k ) as int] == b[( k ) as int],
            N <= 0x3FFF_FFFF,
            decreases(i as int - j as int)
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];

        proof {
            let a_val = b[( i ) as int] + 1 - j;
            if i == j {
                lemma_after_inner_loop(a, b, i, j);
                assert(a_val == b[( i ) as int]);
            } else {
                assert(a[( i ) as int] == a_val);
            }
            assert(forall |k: usize| 0 <= k < i ==> a[( k ) as int] == b[( k ) as int]);
            if a_val == b[( i ) as int] {
                assert(forall |k: usize| 0 <= k < i + 1 ==> a[( k ) as int] == b[( k ) as int]);
            }
        }

        i = i + 1;

        proof {
    assert(0 <= sum);  // Establish lower bound
    assert(N <= sum + (N - i) && sum + (N - i) <= 2 * N);  // Add proof computation
            assert(N <= sum + (N - i) && sum + (N - i) <= 2 * N);
        }
    }  

    sum
}
}
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True