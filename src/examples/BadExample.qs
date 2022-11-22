

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

  //should be like a sum type. no access to ANY other qubits, so only returns what is in the param
  // can be like: AnotherExample(q: Qubit[k], q1: Qubit[k1]): Qubit<k,k1>
  // where <k,k1> is a set (note this must be differentiable from an array of qubits)
  operation AnotherExample (q : Qubit, q1 : Qubit, q2 : Qubit, a : Int) : Int {

    if a == 1 {
      return q;
    }
    elif a == 2 {
      return q1;
    }

    return q2;

  }

}
