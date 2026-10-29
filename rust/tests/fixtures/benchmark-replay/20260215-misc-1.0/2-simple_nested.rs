
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::proof]
proof fn sum_plus_one_le_twice_plus_one(sum: int, i: int)
    requires
        sum <= 2 * i,
        i >= 0,
    ensures
        sum + (i + 1) <= 2 * (i + 1)
{
    assert(sum + (i + 1) == sum + i + 1);
    assert(sum + i + 1 <= 2 * i + 1);
    assert(2 * i + 1 <= 2 * i + 2);
    assert(sum + i + 1 <= 2 * i + 2);
    assert(2 * i + 2 == 2 * (i + 1));
    assert(sum + (i + 1) <= 2 * (i + 1));
}

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k: int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
    invariant
        i <= N,
        sum <= 2 * i as i32,
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == b[( k ) as int] + 1,
        forall |k: usize| 0 <= k < i ==> b[( k ) as int] <= k as i32 + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
        a.len() == N,
        i >= 0,
        decreases(N as usize - i)
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
        invariant
            j <= i,
            a[( i ) as int] >= b[( i ) as int],
            old(a).len() == N,
            b.len() == N,
            N <= 0x3FFF_FFFF,
            a.len() == N,
            j >= 0,
            decreases(i - j)
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }

        assert(sum + a[( i ) as int] <= 2 * (i as i32 + 1)) by {
            assert(a[( i ) as int] <= (i as i32 + 1)); // Based on the invariant b[k] <= k + 1
            assert(sum <= 2 * i as i32); // Reiterate from loop invariant
            sum_plus_one_le_twice_plus_one(sum as int, i as int);
            assert(sum + a[( i ) as int] <= sum + (i as i32 + 1)); // Transitivity
        };

        sum = sum + a[i];
        i = i + 1;
    }  
    sum
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True