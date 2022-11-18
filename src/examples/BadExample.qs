

namespace QAlgol {
  operation NewQubit () : Qubit {
    use q = Qubit ();
    return q;
  }

  operation Clone () : Unit {
    use q1 = Qubit ();
    let q2 = q1 ;
    CNOT ( q1 , q2 );
  }
}
