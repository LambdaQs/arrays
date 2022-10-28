namespace ImpureClassicalExample {
    open Microsoft.Quantum.Intrinsic;

    function Tail<'A> (array : 'A[]) : 'A {
        EqualityFactB(Length(array) > 0, true, $"Array must be of the length at least 1");
        return array[Length(array) - 1];
    }

}
