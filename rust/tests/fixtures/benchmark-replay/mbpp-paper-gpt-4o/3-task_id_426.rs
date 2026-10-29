
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

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            index >= 0,
            arr.len() == input_len,
            odd_list.len() <= index,
            forall |k: int| 0 <= k < arr.len() ==> arr[k] % 2 == arr@[k] % 2,
            odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0), // Corrected by AI
        decreases
            arr.len() - index, // Added by AI
    {
        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);
        }
        index += 1;
    }
    proof {
        reveal(Seq::filter); // Added to help Verus understand `filter`
        lemma_seq_subrange_all(arr@); // Added invocation for the lemma function
        assert(odd_list@ == arr@.filter(|x: u32| x % 2 != 0)); // Added by AI
    }
    odd_list
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True