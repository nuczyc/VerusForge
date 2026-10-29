
use vstd::prelude::*;

fn main() {}

verus! {
/*
 This lemma is often useful before a vector-remove call, and it can be useful to prove what element is contained in a vector.
 The parameters to this lemma function should match the executable code after it.
 Do NOT pass `old(..)' to this lemma as parameter.
 Example usage:
    proof{
    lemma_vec_remove(vec@, index);
    }
    vec.remove(index);
 */
proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
{

}

/*
 This lemma is often useful before a vector-push call, and it can be useful to prove what element is contained in a vector.
 Example usage:
    proof{
    lemma_vec_push(vec@, value, vec.len());
    }
    vec.push(value);
 */
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

/*
 This lemma helps prove that if a sequence contains an element, then another sequence with no duplicates does not contain it.
 */
proof fn lemma_no_duplicate_contains<T>(seq1: Seq<T>, seq2: Seq<T>)
    requires
        seq2.no_duplicates(),
    ensures
        forall|k: int| 0 <= k < seq1.len() ==> !seq2.contains(seq1[k]),
{
    assert(forall|k: int| 0 <= k < seq1.len() ==> !seq2.contains(seq1[k])) by {
        assert(forall|m: int, n: int| 0 <= m < n && n < seq2.len() ==> seq2[m] != seq2[n]);
    };
}

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            arr.len() == arr.len(),
            forall|k: int| 0 <= #[trigger] arr[k] < arr.len() ==> arr.len() == arr.len(),
        decreases arr.len() - i
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
{
    let mut index = 0;
    while index < arr1.len()
        invariant 
            0 <= index <= arr1.len(),
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
            forall|k: int| 0 <= #[trigger] arr1[k] < arr1.len() ==> arr1.len() == arr1.len(),
            forall|k: int| 0 <= #[trigger] arr2[k] < arr2.len() ==> arr2.len() == arr2.len(),
        decreases arr1.len() - index
    {
        if (contains(arr2, arr1[index])) {
            return true;
        }
        index += 1;
    }
    proof {
        lemma_no_duplicate_contains(arr1@, arr2@);
        assert(forall|k: int| 0 <= k < arr1.len() ==> !arr2@.contains(arr1[k]));
        assert(!exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k]));
    }
    false
}

}

// Score: Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 3
// Safe: True