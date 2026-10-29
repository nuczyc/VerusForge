
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
        invariant forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k]
        decreases (arr.len() as int) - (index as int)
    {
        if (arr[index] == key) {
            assert(counter < usize::MAX);
            counter += 1;
        }
        index += 1;
    }
    counter
}

proof fn lemma_count_frequency_rcr_filter(seq: Seq<i32>, key: i32)
    ensures
        seq.filter(|x| count_frequency_rcr(seq, x) == 1).contains(( &key ) as i32) == (count_frequency_rcr(seq, key) == 1)
    decreases seq.len()
{
    if seq.len() > 0 {
        let last = seq.last();
        let rest = seq.drop_last();
        lemma_count_frequency_rcr_filter(rest, key);

        if last == key {
            assert(seq.filter(|x| count_frequency_rcr(seq, x) == 1).contains(( &key ) as i32) == false ==> count_frequency_rcr(seq, key) != 1);
            assert(seq.filter(|x| count_frequency_rcr(seq, x) == 1).contains(( &key ) as i32) == true <==> count_frequency_rcr(rest, last) == 0);
        } else {
            assert(seq.filter(|x| count_frequency_rcr(seq, x) == 1).contains(( &key ) as i32) == rest.filter(|x| count_frequency_rcr(rest, x) == 1).contains(( &key ) as i32));
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
        invariant forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k]
        decreases (arr.len() as int) - (index as int)
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        lemma_count_frequency_rcr_filter(arr@, 0); // Example invocation, adapt as needed
        assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    }
    unique_arr
}

} // verus!






// Score: Compilation Error: False, Verified: 2, Errors: 4, Verus Errors: 4
// Safe: True