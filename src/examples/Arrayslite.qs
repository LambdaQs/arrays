// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

namespace Microsoft.Quantum.Arrays {
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Logical;



   function LookupFunction<'T> (array : 'T[]) : (Int -> 'T) {
        return ElementAt(_, array);
    }


    function Tail<'A> (array : 'A[]) : 'A {
        EqualityFactB(Length(array) > 0, true, $"Array must be of the length at least 1");
        return array[Length(array) - 1];
    }


    function Head<'A> (array : 'A[]) : 'A {
        EqualityFactB(Length(array) > 0, true, $"Array must be of the length at least 1");
        return array[0];
    }


    function HeadAndRest<'A>(array : 'A[]) : ('A, 'A[]) {
        return (Head(array), Rest(array));
    }


    function MostAndTail<'A>(array : 'A[]) : ('A[], 'A) {
        return (Most(array), Tail(array));
    }


    function ConstantArray<'T> (length : Int, value : 'T) : 'T[] {
        return [value, size = length];
    }


}
