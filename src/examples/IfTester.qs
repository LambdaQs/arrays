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

}
