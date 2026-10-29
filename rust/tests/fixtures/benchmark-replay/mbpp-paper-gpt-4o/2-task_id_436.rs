
use vstd::prelude::*;

fn main() {}

verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
     	lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

#[verifier::loop_isolation(false)]

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let mut index = 0;

    // Add reveal statement for the filter function
    proof {
        reveal(Seq::filter);
    }

    while index < arr.len()
        invariant
            index >= 0,
            index <= arr.len(),
            negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0), // Fixed by AI
        decreases arr.len() - index // Ensure loop always decreases
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }
        index += 1;
        proof {
            lemma_seq_subrange_all(arr@);
            assert(negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0)); // Added by AI
        }
    }
    proof {
        lemma_seq_subrange_all(arr@);
        assert(negative_list@ == arr@.filter(|x: i32| x < 0)); // Added by AI
    }
    negative_list
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True