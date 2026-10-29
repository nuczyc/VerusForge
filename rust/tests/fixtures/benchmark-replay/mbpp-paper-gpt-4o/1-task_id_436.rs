
use vstd::prelude::*;

fn main() {}

verus! {
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
        reveal(Seq::filter); // Reveal Seq::filter at the beginning of the function

        let mut negative_list: Vec<i32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                arr.len() >= 0,
                negative_list.len() >= 0,
                forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
                negative_list@ == arr@.subrange(0, index as int).filter(|x: i32| x < 0),
            decreases arr.len() - index,
        {
            if (arr[index] < 0) {
                negative_list.push(arr[index]);
            }
            index += 1;
        }
        proof {
            lemma_seq_subrange_all(arr@);
            lemma_seq_subrange_all(negative_list@);
            // Using the invariant and the fact that index == arr.len() at the end of the loop
            assert(arr@ == arr@.subrange(0, arr.len() as int));
            assert(negative_list@ == arr@.filter(|x: i32| x < 0));
        }
        negative_list
    }
} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True