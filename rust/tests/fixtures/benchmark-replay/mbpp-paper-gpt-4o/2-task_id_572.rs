
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

proof fn lemma_count_frequency_rcr_filter(seq: Seq<i32>)
    ensures
        seq.filter(|x: i32| count_frequency_rcr(seq, x) == 1) == seq.filter(|x: i32| count_frequency_rcr(seq, x) == 1),
    decreases seq.len()
{
    if seq.len() > 0 {
        lemma_count_frequency_rcr_filter(seq.drop_last());
        let x = seq.last();
        if count_frequency_rcr(seq, x) == 1 {
            assert(seq.drop_last().filter(|y: i32| count_frequency_rcr(seq.drop_last(), y) == 1).contains(x) == false);
            assert(seq.filter(|y: i32| count_frequency_rcr(seq, y) == 1).contains(x));
        } else {
            assert(seq.filter(|y: i32| count_frequency_rcr(seq, y) == 1).contains(x) == false);
        }
    }
}

proof fn lemma_count_frequency_equiv_filter(seq: Seq<i32>, key: i32)
    ensures
        seq.filter(|x: i32| count_frequency_rcr(seq, x) == 1).contains(key) == (count_frequency_rcr(seq, key) == 1)
    decreases seq.len()
{
    if seq.len() > 0 {
        lemma_count_frequency_equiv_filter(seq.drop_last(), key);
    }
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len() 
        invariant arr.len() >= 0, key == key, arr.len() == arr.len(), forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k]
        decreases (arr.len() - index)
    {
        if (arr[index] == key) {
            assert(counter < usize::MAX);
            counter += 1;
        }
        index += 1;
    }
    counter
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len() 
        invariant arr.len() >= 0, input_len >= 0, arr.len() == arr.len(), unique_arr.len() >= 0, forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k]
        decreases (arr.len() - index)
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        lemma_count_frequency_rcr_filter(arr@);
        lemma_count_frequency_equiv_filter(arr@, arr@[index as int]);
        assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    }
    unique_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 4
// Safe: True