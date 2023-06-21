// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

namespace Microsoft.Quantum.Arrays {
    // open Microsoft.Quantum.Convert;
    // open Microsoft.Quantum.Diagnostics;
    // open Microsoft.Quantum.Intrinsic;
    // open Microsoft.Quantum.Math;
    // open Microsoft.Quantum.Logical;



//    function LookupFunction<'T> (array : 'T[]) : (Int -> 'T) {
//         return ElementAt(_, array);
//     }


    // function Tail<'A> (array : 'A[]) : 'A {
    //     EqualityFactB(Length(array) == 0, true, 1);
    //     return array[Length(array) - 1];
    // }






    // // Interesting polymorphic scenario
    // function Map<'A, 'B> (array : 'A[], f : 'A -> 'B) : 'B[] {
    //     return([f(array[0])]);
    // }

    // function TestTypes<'D>(array : Int[]) : (Int -> 'D) -> 'D[] {
    //     return(Map(array));
    // }

    // function Head<'A> (array : 'A[], def : 'A) : 'A {
    //     if (Length(array) == 0) {
    //         return def;
    //     }
    //     else {
    //         return array[0];
    //     }
    // }

    function Rest<'T> (array : 'T[]) : 'T[] {
        return array[1 ...];
    }


    function HeadAndRest<'U> (array : 'U[]) : ('U[]) {
        return (Rest(array));
    }




    // function MostAndTail<'A>(array : 'A[]) : ('A[], 'A) {
    //     return (Most(array), Tail(array));
    // }


    // function ConstantArray<'T> (length : Int, value : 'T) : 'T[] {
    //     return [value, size = length];
    // }


}
