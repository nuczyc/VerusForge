
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

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len() 
        invariant i >= 0,
        decreases arr.len() - i,
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
        invariant index >= 0,
        decreases arr1.len() - index,
    {
        if (contains(arr2, arr1[index])) {
            return true;
        }
        index += 1;
    }
    proof {
        assert_forall_by(|k: int| {
            requires(0 <= k && k < arr1.len());
            ensures(!arr2@.contains(arr1[k]));
            if index < arr2.len() {
                lemma_vec_remove(arr2@, (index) as int);
            }
            lemma_vec_push(arr1@, arr1[(index) as int], arr1.len());
        });
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 2
// Safe: True