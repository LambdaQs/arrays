
namespace LambdaQs.Arrays {

    operation X (qubit : Qubit) : Unit is Adj + Ctl {
        body intrinsic;
        adjoint self;
    }

    operation CNOT (control : Qubit, target : Qubit) : Unit is Adj + Ctl {
        body (...) {
            Controlled X([control], target);
        }
        adjoint self;
    }

    function Most<'T> (array : 'T[]) : 'T[] {
        return array[... Length(array) - 2];
    }

    function Rest<'T> (array : 'T[]) : 'T[] {
        return array[1 ...];
    }


    // function Zipped<'T, 'U>(left : 'T[], right : 'U[]) : ('T, 'U)[] {
    //     let nElements = Length(left) < Length(right)
    //                     ? Length(left)
    //                     | Length(right);

    //     if nElements == 0 {
    //         return [];
    //     }

    //     mutable output = [(left[0], right[0]), size = nElements];

    //     for idxElement in 1 .. nElements - 1 {
    //         set output w/= idxElement <- (left[idxElement], right[idxElement]);
    //     }

    //     return output;
    // }

    // function IndexRange<'TElement>(array : 'TElement[]) : Range {
    //    return 0..(Length(array) - 1);
    // }

    // //if singleElementOperation has a constraint on 'T then register must satisfy for all i in register
    // //'T can be thought of as 'T + constraint C
    // //'T = (Qubit<a>, Qubit<b>)
    // operation ApplyToEachCA<'T> (singleElementOperation : ('T => Unit is Adj + Ctl), register : 'T[])
    // : Unit is Adj + Ctl {
    //     for idxQubit in IndexRange(register) {
    //         singleElementOperation(register[idxQubit]);
    //     }
    // }

    // operation ApplyCNOTChain(qubits : Qubit[]) : Unit is Adj + Ctl {
    //     ApplyToEachCA(CNOT, Zipped(Most(qubits), Rest(qubits)));
    // }

    // //ApplyToEachCA(Zipped(Most(qubits), Rest(qubits)), CNOT);

    // CNOT[qubits[i], qubit[i+1]]


    // // CNOT expects (p,q) where p /= q
    // // (ApplyToEachCA CNOT) expects [(p,q)] where p /= q






}
