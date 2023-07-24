pragma circom 2.0.3;

include "circuits/comparators.circom";
include "circuits/bitify.circom";

// NB: RangeProof is inclusive.
// input: field element, whose abs is claimed to be <= than max_abs_value
// output: none
// also checks that both max and abs(in) are expressible in `bits` bits
template RangeProof(bits) {
    signal input in;
    signal input max_abs_value;

    /* check that both max and abs(in) are expressible in `bits` bits  */
    component n2b1 = Num2Bits(bits+1);
    n2b1.in <== in + (1 << bits);
    component n2b2 = Num2Bits(bits);
    n2b2.in <== max_abs_value;

    /* check that in + max is between 0 and 2*max */
    component lowerBound = LessThan(bits+1);
    component upperBound = LessThan(bits+1);

    signal {maxbit} aux; aux.maxbit = bits+1; aux <== max_abs_value + in;
    signal {maxbit} zero; zero.maxbit = bits+1; zero <== 0;
    lowerBound.in[0] <== aux;
    lowerBound.in[1] <== zero;
    lowerBound.out === 0;

    signal {maxbit} aux2; aux2.maxbit = bits+1; aux2 <== 2*max_abs_value;
    upperBound.in[0] <== aux2;
    upperBound.in[1] <== aux;
    upperBound.out === 0;
    spec_postcondition (in <= max_abs_value) ||
                (21888242871839275222246405745257275088548364400416034343698204186575808495617 - in <= max_abs_value);
}


// input: n field elements, whose abs are claimed to be less than max_abs_value
// output: none
template MultiRangeProof(n, max_abs) {
    signal input in[n];
    for (var i = 0; i < n; i++) {
        _ <== AddMaxAbsValueTag(max_abs)(in[i]);
        spec_postcondition (in[i] <= max_abs) ||
                (21888242871839275222246405745257275088548364400416034343698204186575808495617 - in[i] <= max_abs);
    }
}

/*
template RPTester() {
    signal input a;
    component rp = RangeProof(10);
    rp.in <== a;
    rp.max_abs_value <== 100;
}

component main = RPTester();
*/

