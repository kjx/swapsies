class Animal {
  predicate domesticated() {false}
}

class Rat {

 predicate happy() {true}
}


class Farm {
  var animals : set<Animal>
  constructor() { animals := {}; }
  predicate valid() { forall r : Rat <- animals :: r.happy() }
}