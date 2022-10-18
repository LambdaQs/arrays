namespace IfsExample {
    open Microsoft.Quantum.Intrinsic;


    function test (a : Int) : Int {

        if a == 1 {
            return a;
        }
        elif a == 2 {
            return a + a;
        }
        elif a == 3 {
            return a + 7;
        }


        else {
             return a + a + 10;
         }



    }

    // operation ApplyH (q : Qubit) : Unit {
    //     H(q);
    // }

    // operation ApplyX (q : Qubit) : Unit is Adj+Ctl {
    //     X(q);
    // }

    // operation ApplyCNOT (q1 : Qubit, q2 : Qubit) : Unit {
    //     CNOT(q1, q2);
    // }
}