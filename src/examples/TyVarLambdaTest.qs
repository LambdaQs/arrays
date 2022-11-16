namespace Microsoft.Quantum.Arrays {
    open Microsoft.Quantum.Logical;


    function All<'T> (predicate : ('T -> Bool), array : 'T[]) : Bool {
       return Fold(And, true, Mapped(predicate, array));
    }

    function simple_fun (a : Int) : Bool {
        return (a > 0);
    }


    function main (input : String) : Bool {
        let sample = [0,1,2,3,4,5];
        return All(simple_fun, sample);
    }


}
