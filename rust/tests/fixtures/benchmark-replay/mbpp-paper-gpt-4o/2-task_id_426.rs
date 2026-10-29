
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
                input_len == arr.len(),
                arr.len() == input_len,
                odd_list.len() <= index, 
                forall |i: int| 0 <= i < index ==> odd_list@[i] == arr@[i] && odd_list[i] % 2 != 0,
            decreases arr.len() - index, 
        {
            if (arr[index] % 2 != 0) {
                odd_list.push(arr[index]);
            }
            index += 1;
        }
        proof {
            reveal(Seq::filter); // This line allows Verus to understand and unfold the Seq::filter method.
            lemma_seq_subrange_all(arr@);
            lemma_seq_subrange_all(odd_list@);
            assert(odd_list@ == arr@.filter(|x: u32| x % 2 != 0));
        }
        odd_list
    }
} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True