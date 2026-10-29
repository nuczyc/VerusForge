
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn shift32_spec(c: u8) -> u8 {
    (c + 32) as u8
}

proof fn lemma_to_lowercase_correct(str1: Seq<u8>, lower_case: Seq<u8>, index: int)
    requires
        0 <= index <= str1.len(),
        lower_case.len() == index,
        forall|i: int| 0 <= i < index ==> lower_case[i] == (if is_upper_case(str1[i]) {
            shift32_spec(str1[i])
        } else {
            str1[i]
        }),
    ensures
        forall|i: int| 0 <= i < str1.len() ==> lower_case.push(if is_upper_case(str1[index]) {
            shift32_spec(str1[index])
        } else {
            str1[index]
        })[i] == (if is_upper_case(str1[i]) {
            shift32_spec(str1[i])
        } else {
            str1[i]
        }),
    decreases str1.len() - index
{
    assert(forall|i: int| 0 <= i < index ==> lower_case[i] == (if is_upper_case(str1[i]) {
        shift32_spec(str1[i])
    } else {
        str1[i]
    }));

    if index < str1.len() {
        let new_element = if is_upper_case(str1[index]) {
            shift32_spec(str1[index])
        } else {
            str1[index]
        };
        let updated_lower_case = lower_case.push(new_element);
        assert(updated_lower_case.len() == index + 1);

        lemma_to_lowercase_correct(str1, updated_lower_case, index + 1);
    }
}

fn to_lowercase(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int| 0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
{
    let mut lower_case: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
    invariant
        lower_case@.len() == index,
        forall|i: int| 0 <= i < index ==> lower_case@[i] == (if is_upper_case(str1@[i]) {
            shift32_spec(str1@[i])
        } else {
            str1@[i]
        }),
    decreases str1.len() - index
    {
        assert(0 <= index && index < str1.len());
        
        if (str1[index] >= 65 && str1[index] <= 90) {
            lower_case.push((str1[index] + 32) as u8);
        } else {
            lower_case.push(str1[index]);
        }
        index += 1;
    }
    proof {
        lemma_to_lowercase_correct(str1@, lower_case@, ( index ) as int);
        assert(forall|i: int| 0 <= i < str1.len() ==> lower_case@[i] == (if is_upper_case(#[trigger] str1@[i]) {
            shift32_spec(str1@[i])
        } else {
            str1@[i]
        }));
    }
    lower_case
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True