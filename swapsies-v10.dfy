///swapsisies-v7.dfy - attempt to use the "Unreliable Conctracts"
///             to model a Purse via the UPurse trait
///             Mint class left as is at this point
///             Purse's Mint is not abstracted over, no Repr, need it


trait UPurse {

  ghost predicate obeys()

  const myMint : Mint
  var myBalance : nat  //my idea of what my balance is!
     //I'm going to assume this is 100% private for now.  KIND OF
     //possibly we need a ghost shadow version...?

  ghost predicate Valid() : (b : bool)
     reads this,myMint
     ensures obeys() ==> (b == ((this in myMint.ledger) && (myBalance == myMint.ledger[this])))

  method sprout() returns (p : UPurse)
    modifies myMint`ledger

    ensures obeys() ==> p.obeys()

    ensures obeys() ==> (p in myMint.ledger)
    ensures obeys() ==> (p.myMint == myMint)
    ensures obeys() ==> (p.Valid())
    ensures obeys() ==> (fresh(p))
    ensures obeys() ==> (myMint.ledger == old(myMint.ledger)[p := 0])

  method deposit(amount : nat, source : UPurse) returns (b : bool)
    requires obeys() ==> (Valid())
    requires obeys() ==> (source.Valid())
    requires obeys() && source.obeys() ==> (this != source)
    requires ((obeys() && source.obeys() && source.Valid()) ==> (amount <= source.myBalance))
    requires ((obeys() && source.obeys() && Valid() && source.Valid()) ==> (myMint == source.myMint))

    modifies myMint`ledger, source`myBalance, `myBalance

    ensures (obeys() && source.obeys()) ==> (b ==>   old(myMint.depositWouldBeOK(this, amount, source)))

    ensures (obeys() && source.obeys() && old(Valid()) && old(source.Valid()) && (source is Purse)) ==> (b ==>
                   (myMint.ledger == old(myMint.ledger
                             [source := (myMint.ledger[source] - amount)]
                             [this := (myMint.ledger[this] + amount)] ) ))

    ensures (obeys() && source.obeys() && (source is Purse)) ==> (not(b) ==> unchanged(myMint))
    ensures obeys() ==> (Valid())
    ensures obeys() ==> (source.Valid())

  ensures (obeys() && Valid() && source.obeys() && source.Valid()) ==> (b ==> (this.balance() ==   (old(this.balance()) + amount)))
  ensures (obeys() && Valid() && source.obeys() && source.Valid()) ==> (b ==> (source.balance() == (old(source.balance()) - amount)))
  //ensures obeys() ==> (forall p <- myMint.ledger :: p !in {this, source} ==>
  //    (old(p.Valid()) ==> (p.balance() == old(p.balance()))))

  ensures forall p <- old(myMint.ledger) :: p !in {this, source} ==>
     (old(p.Valid() && p.obeys()) ==> p.Valid())

  ensures forall p <- old(myMint.ledger) :: p !in {this, source} ==>
     (old(p.Valid()) && p.obeys() ==> (p.balance() == old(p.balance())))



  function balance() : (bal : nat)
    requires obeys() ==> (Valid())
    ensures obeys() ==> ((this in myMint.ledger) && (bal == myMint.ledger[this]))
    reads this,myMint

  predicate {:isolate_assertions} {:timeLimit 60} shellBeRight(into : UPurse, amount : nat, from : UPurse) : (b : bool)
    //sophia can think of this as "CanTrade"
      reads from, into, from.myMint`ledger, into.myMint`ledger, from.myMint, into.myMint
   requires ((from.obeys() && into.obeys() && from.Valid()) ==> (amount <= from.myBalance))
   requires (from.obeys() && into.obeys()) ==> (into != from)
   requires (from.obeys() && into.obeys() && from.Valid() && into.Valid()) ==> (into.myMint == from.myMint)
   requires (from.obeys() && into.obeys()) ==> (from.myBalance >= amount)

   ensures b ==> (into != from)

   ensures (from.obeys() && into.obeys() && from.Valid() && into.Valid() && (from is Purse) && (into is Purse)) ==>
     (
    && (into.myMint == from.myMint)
    && (from in into.myMint.ledger) //these amount to dynamic ownership checks...
    && (into != from)  //this check not in the original paper!
     )

   ensures (from.obeys() && into.obeys() && from.Valid() && into.Valid() && (from is Purse) && (into is Purse)) ==>
      (b == (&& into.myMint.depositWouldBeOK(into,amount,from)
             && from.myMint.depositWouldBeOK(into,amount,from)))


 reads `myBalance, from`myBalance, from.myMint`ledger, into.myMint`ledger, this, into
  {
    && (from is Purse)
    && (into is Purse)
    // && from.obeys()
    // && into.obeys()
    && (amount >=0)
    && (into.myMint == from.myMint)
    // && from in into.myMint.ledger //these amount to dynamic ownership checks...
    // && into in from.myMint.ledger
    && (from.myBalance >= amount)
    && (into != from  )//this check not in the original paper!
  }
}


class Purse extends UPurse {

  ghost predicate obeys() {true}

  ghost predicate Valid() : (b : bool)
   reads myMint`ledger
     ensures obeys() ==> (b == ((this in myMint.ledger) && (myBalance == myMint.ledger[this])))

     reads this
   {
      ((this in myMint.ledger) && (myBalance == myMint.ledger[this]))
   }

  // const myMint : Mint //I'm going to assume this is 100% private for now.

  constructor(aMint : Mint)
    modifies aMint`ledger
    ensures  this in myMint.ledger
    ensures  myMint == aMint
    ensures  Valid()
    ensures  fresh(this)
    ensures  myMint.ledger == old(aMint.ledger)[this := 0]

    { myMint := aMint;
      myBalance := 0;
      new;
      myMint.ledger := myMint.ledger[this := 0];
    }

  method sprout() returns (p : UPurse)
    modifies myMint`ledger
    ensures p in myMint.ledger
    ensures p.myMint == myMint
    ensures p.Valid()
    ensures fresh(p)
    ensures myMint.ledger == old(myMint.ledger)[p := 0]

   ensures p.obeys()

    { p := myMint.newPurse(0); }

  method {:isolate_assertions} {:timeLimit 120} deposit(amount : nat, source : UPurse) returns (b : bool)
    requires obeys() ==> (Valid())
    requires obeys() ==> (source.Valid())
    requires obeys() && source.obeys() ==> (this != source)
    requires ((obeys() && source.obeys() && source.Valid()) ==> (amount <= source.myBalance))
    requires ((obeys() && source.obeys() && Valid() && source.Valid()) ==> (myMint == source.myMint))

    modifies myMint`ledger, source`myBalance, `myBalance

    ensures (obeys() && source.obeys()) ==> (b ==>   old(myMint.depositWouldBeOK(this, amount, source)))

    ensures (obeys() && source.obeys() && old(Valid()) && old(source.Valid()) && (source is Purse) ) ==> (b ==>      // && old(Valid()) && old(source.Valid())
                   (myMint.ledger == old(myMint.ledger
                             [source := (myMint.ledger[source] - amount)]
                             [this := (myMint.ledger[this] + amount)] ) ))

    ensures (obeys() && source.obeys() && Valid() && source.Valid()  && (source is Purse) ) ==> (not(b) ==> unchanged(myMint))
    ensures obeys() ==> (Valid())
    ensures obeys() ==> (source.Valid())


  // ensures b ==> (this.balance() == (old(this.balance()) + amount))
  // ensures b ==> (source.balance() == (old(source.balance()) - amount))
  // ensures forall p <- old(myMint.ledger) :: p !in {this, source} ==>
  //     (old(p.Valid()) ==> p.Valid())

  ensures (obeys() && Valid() && source.obeys() && source.Valid()) ==> (b ==> (this.balance() ==   (old(this.balance()) + amount)))
  ensures (obeys() && Valid() && source.obeys() && source.Valid()) ==> (b ==> (source.balance() == (old(source.balance()) - amount)))
  //ensures obeys() ==> (forall p <- myMint.ledger :: p !in {this, source} ==>
  //    (old(p.Valid()) ==> (p.balance() == old(p.balance()))))

  ensures forall p <- old(myMint.ledger) :: p !in {this, source} ==>
     (old(p.Valid() && p.obeys()) ==> p.Valid())

  ensures forall p <- old(myMint.ledger) :: p !in {this, source} ==>
     (old(p.Valid()) && p.obeys() ==> (p.balance() == old(p.balance())))

  {
    b := source.shellBeRight(this,amount,source);
    // if ((source is Purse) && (source in myMint.ledger))
    //    { b := source.shellBeRight(this,amount,source); }
    //    else { b := false; }
    assert (obeys() && Valid() && source.obeys() && source.Valid()) ==> (myMint == source.myMint);

    if (not(source is Purse)) { return false; }

    b := myMint.deposit(this, amount, source as Purse); //*has to be done somewhere, right?

  }

  function balance() : (bal : nat)
    requires Valid()
    reads myMint`ledger, `myBalance, this
      requires obeys() ==> (Valid())
       ensures obeys() ==> ((Valid()) ==> ((this in myMint.ledger) && (bal == myMint.ledger[this])))
      { // assert obeys() ==> ((Valid()) ==> ((this in myMint.ledger) && (bal == myMint.ledger[this])));
        myBalance }
  //      { if this in myMint.ledger then myMint.ledger[this] else 0 }
}


class Mint {
  ghost var ledger : map<UPurse,nat>
  constructor()
     ensures fresh(this) {
     ledger := map[];
  }
  method {:isolate_assertions} newPurse(balance : nat) returns ( p : UPurse )
    modifies `ledger
    ensures p.obeys() ==> p.Valid()
    ensures p !in old(ledger)
    ensures ledger == old(ledger)[p:=balance]
    ensures p.balance() == balance
    ensures fresh(p)
    ensures p.myMint == this
    ensures p.obeys() //EVIL EVIL SUPER FUCKING EVIL?
    ensures forall x <- old(ledger) :: old(ledger[x]) == ledger[x]
    //ensures forall x <- old(ledger) :: old(x.Valid() && x.obeys()) ==> x.Valid()
  {
    p := new Purse(this);
    p.myBalance := balance;
    ledger := ledger[p:=balance];
  }

 method deposit(into : Purse, amount : nat, from : Purse) returns (b : bool)
  requires into.Valid()
  requires from.Valid()
  requires into != from
  requires this == into.myMint
  requires this == from.myMint
  requires ledger[from] >= amount
  requires from in ledger.Keys
  requires into in ledger.Keys



  modifies `ledger
  ensures (into.obeys() && from.obeys()) ==> (b ==> old(depositWouldBeOK(into, amount, from)))
  ensures (into.obeys() && from.obeys()) ==> (b ==> (ledger == old(ledger)
                             [from := (old(ledger[from]) - amount)]
                             [into := (old(ledger[into]) + amount)]  ))
  //ensures not(b) ==> (ledger == old(ledger))
  ensures (into.obeys() && from.obeys() && old(into.Valid())) ==> into.Valid()
  ensures (into.obeys() && from.obeys() && old(from.Valid())) ==> from.Valid()
  //ensures forall a <- old(ledger) :: a !in {into, from} ==> (old(a.Valid()) == a.Valid())   //don't break stuff
  ensures (into.obeys() && from.obeys() && b) ==> forall a <- old(ledger) :: a !in {into, from} ==> ledger[a] == old(ledger[a])
 // ensures forall a <- old(ledger) :: a !in {into, from} ==>
 //     (old(a.Valid())  ==> (a.balance() == old(a.balance())))


 //ensures forall a <- old(ledger) :: (a.Valid() && a.obeys()) ==> (ledger[a] == a.balance())

   ensures forall p <- old(ledger) :: p !in {into, from} ==>
     (old(p.Valid() && p.obeys()) ==> p.Valid())

 ensures forall p <- ledger :: (p !in {into, from} && old(allocated(p))) ==>
     (old(p.Valid()) && p.obeys() ==> (p.balance() == old(p.balance())))
  ensures b ==> (into.balance() == (old(into.balance()) + amount))
  ensures b ==> (from.balance() == (old(from.balance()) - amount))
  ensures not(b) ==> unchanged(`ledger)
   modifies from`myBalance, into`myBalance, `ledger

  {
    b := false;

    if (
      && (0 <= amount <= from.myBalance)
      && (into.myMint == from.myMint == this) //these amount to dynamic ownership checks...
      // && from in ledger //these amount to dynamic ownership checks...
      // && into in ledger //these amount to dynamic ownership checks...
     ) {
         from.myBalance := from.myBalance - amount;
         into.myBalance := into.myBalance + amount;
         ledger := ledger[from := (old(ledger[from]) - amount)]
                         [into := (old(ledger[into]) + amount)];
         b := true;
     } else {
      assert not(b);
      assert ledger == old(ledger);
     }
}

ghost predicate depositWouldBeOK(into : UPurse, amount : nat, from : UPurse)
    //pretty much "canTrade"
 reads `ledger, into, into.myMint, from, from.myMint
 {
    && from.obeys()
    && into.obeys()
    && amount >=0
    && into.myMint == this
    && from.myMint == this
    && from in ledger //these amount to dynamic ownership checks...
    && into in ledger
    && ledger[from] >= amount
    && into != from  //this check not in the original paper!
    //
    // && into is Purse //EVIL EVIL
    // && from is Purse //EVIL EVIL
 }

}

method Main() {

  //money sm is seller, bm is buyer
  var m1 := new Mint();
  var sm : UPurse := m1.newPurse(10);

  assert sm.obeys();
  assert sm.Valid();

  assert sm.obeys() ==> sm.Valid();

  var bm : UPurse := m1.newPurse(20);

  assert sm.obeys() || sm.Valid();

  assert sm.obeys();

  assert sm.Valid();

  assert sm.obeys() ==> sm.Valid();

  print "sm=",sm.balance(),"  bm=",bm.balance(),"\n";

  assert sm.balance()==10;

  assert bm.balance()==20;

  var b :=  sm.deposit(7,bm);

  assert sm.obeys();
  assert bm.obeys();


  print "b=",b," sm=",sm.balance(),"  bm=",bm.balance(),"\n";

  if not(b) {return;}

  assert sm.obeys();
  assert sm.Valid();
  assert sm.balance()==17;
  assert bm.balance()==13;


//goods.  sg is seller, bg is buyer
  var m2 := new Mint();
  var sg := m2.newPurse(3);
  var bg := m2.newPurse(0);

  assert sg.balance()==3;
  assert bg.balance()==0;


  print "sg=",sg.balance(),"  bg=",bg.balance(),"\n";

  assert m1 != m2;
  assert sm.myMint == m1;
  assert bg.myMint == m2;
  assert bg.myMint == m2;

  //  if (sm.myMint.depositWouldBeOK(sm, 10, bm) &&
  //   bg.myMint.depositWouldBeOK(bg, 2, sg))

  if (sm.shellBeRight(sm, 10, bm) &&
      bg.shellBeRight(bg, 2, sg))
     {
  b := dealV0(sm,sg,10, bm, bg, 2);
    } else {
  b := false;
    }
    if not(b) {return;}

     //dealV0(sellerMoney : Purse, sellerGoods : Purse, price : nat,
     //       buyerMoney : Purse, buyerGoods : Purse,  amount : nat)

  print "b=",b,"\n";
  print "sm=",sm.balance(),"  bm=",bm.balance(),"\n";
  print "sg=",sg.balance(),"  bg=",bg.balance(),"\n";


//  assert sm.balance()==27;
//   assert bm.balance()==3;
//   assert sg.balance()==1;
//   assert bg.balance()==2;




}


method doit(m1 : Mint, sm : UPurse, bm : UPurse) returns (b : bool)

  requires sm.obeys() && bm.obeys()
  requires sm != bm
  requires sm.Valid()
  requires bm.Valid()
  requires bm.myBalance == 100
  requires ((bm.obeys() && sm.obeys() && bm.Valid() && sm.Valid()) ==> (bm.myMint == sm.myMint))


  modifies sm, bm, m1, m1`ledger, sm.myMint`ledger, bm.myMint`ledger
  ensures  sm.Valid()
  ensures  bm.Valid()

  ensures  b ==> ( sm.balance() == old(sm.balance()) + 7)
{
  print "sm=",sm.balance(),"  bm=",bm.balance(),"\n";

  b :=  sm.deposit(7,bm);

  print "b=",b," sm=",sm.balance(),"  bm=",bm.balance(),"\n";
}


method dealV0(sellerMoney : UPurse, sellerGoods : UPurse, price : nat,
               buyerMoney : UPurse, buyerGoods : UPurse,  amount : nat) returns ( b : bool )



   requires sellerMoney.obeys() && sellerGoods.obeys()
   requires buyerMoney.obeys()  && buyerGoods.obeys()

   requires sellerMoney.Valid()
   requires sellerGoods.Valid()
   requires buyerMoney.Valid()
   requires buyerGoods.Valid()
  //  requires sellerGoods.balance() >= amount
  //  requires buyerMoney.balance() >= price

   requires sellerMoney.myMint.depositWouldBeOK(sellerMoney, price, buyerMoney)
   requires buyerGoods.myMint.depositWouldBeOK(buyerGoods, amount, sellerGoods)

  //  requires sellerMoney.myMint == buyerMoney.myMint
  //  requires sellerGoods.myMint == buyerGoods.myMint
   requires (sellerMoney.myMint != buyerGoods.myMint)
   requires (sellerGoods.myMint != buyerMoney.myMint)

   // modifies sellerMoney, buyerMoney, sellerGoods, buyerGoods
   modifies sellerMoney`myBalance, buyerMoney`myBalance
   modifies sellerGoods`myBalance, buyerGoods`myBalance
   modifies sellerMoney.myMint`ledger, buyerMoney.myMint`ledger
   modifies sellerGoods.myMint`ledger, buyerGoods.myMint`ledger

   ensures  sellerMoney.Valid() && sellerGoods.Valid()
   ensures  buyerMoney.Valid()  && buyerGoods.Valid()
   ensures  b ==> (sellerMoney.balance() == old(sellerMoney.balance()) + price)
   ensures  b ==> (buyerMoney.balance() == old(buyerMoney.balance()) - price)
   ensures  b ==> (buyerGoods.balance() == old(buyerGoods.balance()) + amount)
   ensures  b ==> (sellerGoods.balance() == old(sellerGoods.balance()) - amount)
  {

assert buyerMoney.Valid();
assert sellerMoney.Valid();
assert buyerGoods.Valid();
assert sellerGoods.Valid();

assert sellerMoney.myMint.depositWouldBeOK(sellerMoney, price, buyerMoney);
assert buyerGoods.myMint.depositWouldBeOK(buyerGoods, amount, sellerGoods);

var b1 := sellerMoney.deposit(price, buyerMoney);

if (! b1) { return false; }

assert buyerMoney.Valid();
assert sellerMoney.Valid();
assert buyerGoods.Valid();
assert sellerGoods.Valid();


assert sellerMoney.balance() == old(sellerMoney.balance()) + price;
assert buyerMoney.balance()  == old(buyerMoney.balance())  - price;

assert buyerGoods.myMint.depositWouldBeOK(buyerGoods, amount, sellerGoods);



var b2 := buyerGoods.deposit(amount, sellerGoods);

if (! b2) { return false; }


b := b1 && b2;
assert b;

}


predicate not(x : bool) {!x}