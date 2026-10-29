
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant 
            forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array 'arr' is not changed in the loop
            counter as usize <= arr.len(), // Ensure counter never exceeding arr length
        decreases arr.len() - index // Added by AI
    {
        if (arr[index] == key) {
            // Assert that counter can be incremented without overflow
            assert(counter < usize::MAX); // usize::MAX provides the maximum value for usize

            counter += 1;
        }
        index += 1;
    }
    counter
}

proof fn lemma_filter_correctness<A>(
    seq: Seq<A>,
    f: FnSpec(A) -> bool,
) 
    ensures 
        forall |i: int| 0 <= i < seq.filter(f).len() ==> #[trigger] f(seq.filter(f)[i]),
        forall |i: int| 0 <= i < seq.len() && f(seq[i]) ==> exists |j: int| 0 <= j < seq.filter(f).len() && seq[i] === seq.filter(f)[j],
    decreases seq.len()
{
    if seq.len() > 0 {
        if f(seq.last()) {
            lemma_filter_correctness(seq.drop_last(), f);
            assert(f(seq.last()));
            assert(exists |j: int| 0 <= j < seq.filter(f).len() && seq.last() === seq.filter(f)[j]);
        } else {
            lemma_filter_correctness(seq.drop_last(), f);
        }
    }
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr@[k] // The array 'arr' is not changed in the loop
        decreases arr.len() - index // Added by AI
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        let computed_unique = arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1);
        lemma_filter_correctness(arr@, |x: i32| count_frequency_rcr(arr@, x) == 1);
        assert(forall |i: int| 0 <= i < unique_arr@.len() ==> unique_arr@[i] == computed_unique[i]);
        assert(unique_arr@ === computed_unique);
    }
    unique_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 7, Verus Errors: 7
// Safe: True