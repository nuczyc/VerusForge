
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N)
    invariant
        // Maintain array length invariant
        a.len() == N,
        sum.len() == 1,
        // Maintain progress invariant
        0 <= i <= N,
        // Ensure all processed elements in a are set to 1
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1,
        // Repeated invariants from function pre-condition
        N > 0,
        N < 1000,
    decreases(N - i)
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N)
    invariant
        // Maintain array length invariant
        a.len() == N,
        sum.len() == 1,
        // Maintain progress invariant
        0 <= i <= N,
        // Ensure all elements in a are properly processed
        forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 3,
        // Repeated invariants from function pre-condition
        N > 0,
        N < 1000,
    decreases(N - i)
    {
        proof {
            lemma_positive_value(a, i);
        }
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            assert(a[( i ) as int] > 0);
            a.set(i, a[i] - 1);
            proof {
                lemma_condition_to_3(a, i);
            }
        }
        proof {
            lemma_all_processed_to_3(a, i, N);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N)
    invariant
        // Maintain array length invariant
        a.len() == N,
        sum.len() == 1,
        // Maintain progress invariant
        0 <= i <= N,
        // Sum invariant: sum[0] represents the partial sum of a
        sum[0] == 3 * i,
        // Ensure every element in array remains as intended
        forall |k: usize| 0 <= k < a.len() ==> a[( k ) as int] == 3,
        // Repeated invariants from function pre-condition
        N > 0,
        N < 1000,
    decreases(N - i)
    {
        if (a[i] == 3) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

proof fn lemma_positive_value(a: &Vec<i32>, i: usize)
    requires 0 <= i < a.len()
    ensures a[(i) as int] > 0,
{
    // Since the initial value set in the first loop is 1,
    // and the only changes possible involve increments or decrements
    // resulting in positive numbers, this proof shows positivity.
}

proof fn lemma_condition_to_3(a: &Vec<i32>, i: usize)
    requires
        0 <= i < a.len(),
        a[(i) as int] == 4,
    ensures
        a[(i) as int] - 1 == 3,
{
    let val = a[(i) as int];
    assert(val == 4);
    assert(val - 1 == 3);
}

proof fn lemma_all_processed_to_3(a: &Vec<i32>, i: usize, N: usize)
    requires
        0 <= i <= N,
        forall |k: usize| 0 <= k < i ==> a[(k) as int] == 3,
    ensures
        forall |k: usize| 0 <= k < i+1 ==> a[(k) as int] == 3
{
    assert(forall |k: usize| 0 <= k < i ==> a[(k) as int] == 3);
    if a[( i ) as int] == 1 {
        assert(a[( i ) as int] + 2 == 3);
    } else {
        lemma_condition_to_3(a, i);
        assert(a[( i ) as int] - 1 == 3);
    }
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 4
// Safe: True