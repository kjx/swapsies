//a more minimal attempt

// we have (good and bad) banks and acounts
// banks hold ledgers
//

trait Bank extends object {
   var ledger : map<Account,nat>
 }


trait Account extends object {
//
  ghost var Repr: set<object>
//
//   ghost function Inside() : (insides : set<object>)
//     ensures this in insides
//     ensures Repr <= insides

  opaque ghost predicate obeys() //not reading anything makes life easier
    // reads Repr

  ghost predicate valid() : (b : bool)
     //validity predicate
     //interesting question: should this be guarded by obeys() or not?
     //if I remember, calls to valid() itself should not generally be guarded by obeys()
     //we may as well just require or ensure valid() and then let the deatils sort themselves out inside
     //
     //thus should this be tagged on obeys90
       reads this, Repr
     ensures b ==> (this in Repr)
     ensures b ==> (myBank in Repr)
     ensures b ==> (this in myBank.ledger.Keys)
    //the choice here is a lot about how much we (directly) trust the Repr of potentially evil objects
  //  ensures obeys() ==> (this in Repr)
  //  ensures obeys() ==> (myBank in Repr)
  //  ensures obeys() ==> (this in myBank.ledger.Keys)

  //note this *does not* check all the other accounts in the bank
      // && (forall a <- myBank.ledger.Keys | a != this :: a.valid())   ///no obeys obn here cos it's validity
      // && (forall a <- myBank.ledger.Keys | a != this :: (a.myBank == myBank) && (a is GoodAccount) && (a.valid()))

  const myBank : Bank //Dafny won't easilly let us say this, but let's assume this is instance-private
     //it's a CONST.  I wanna say "invariant (myBank in Repr)"
     //but sticking it in Repr spreads the damage around…

  method sprout() returns (account : Account)
    requires valid()
    requires (forall a <- myBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    requires (forall a <- myBank.ledger.Keys :: (a.myBank == myBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()

    ensures obeys() ==> account.obeys()
    ensures valid()

    ensures account.valid()
    ensures account.myBank == myBank
    ensures obeys() ==> (account in myBank.ledger)
    ensures obeys() ==> (fresh(account))

    ensures obeys() ==> account.obeys()

    ensures obeys() ==> (myBank.ledger == old(myBank.ledger)[account := 0])
    ensures obeys() ==> (forall k <- old(myBank.ledger.Keys) :: myBank.ledger[k] == old(myBank.ledger[k]))
    ensures obeys() ==> (forall account <- myBank.ledger :: account.valid())

    ensures myBank.ledger.Keys >= old(myBank.ledger.Keys)
    ensures valid()

   modifies Repr // myBank`ledger


  method deposit(amount : nat, from : Account) returns (b : bool)
    requires valid()
    requires (forall a <- myBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    requires (forall a <- myBank.ledger.Keys :: (a.myBank == myBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()

    modifies this,Repr,from.Repr

     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from)) ==> b)
     ensures (obeys() && b && old(canDepositFrom(amount, from))) ==> from.obeys()

     ensures (obeys() ==> not(b) ==> unchanged(myBank`ledger))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (this in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (from in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[this] == (old(myBank.ledger[this]  ) + amount)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[from] == (old(myBank.ledger[from]) - amount)))
     ensures forall a <- old(myBank.ledger) | (a !in {this, from}) && a.obeys() :: a in myBank.ledger.Keys && myBank.ledger[a] == old(myBank.ledger[a])
     ensures obeys() ==> (forall a <- myBank.ledger :: a.valid())
     ensures valid()


  function balance() : (b : nat)
       reads this,Repr,myBank`ledger,myBank.ledger.Keys
//    requires valid()  //fails in Main() line 345 ff
             {if (this in myBank.ledger.Keys) then (myBank.ledger[this]) else (0)}

ghost function desmesnes() : set<object> reads this,Repr,myBank,myBank`ledger,myBank.ledger.Keys,myBank.ledger.Keys`Repr  { {this} + Repr + myBank.ledger.Keys + (set a <- myBank.ledger.Keys, aa <- a.Repr+{a} :: aa )}

  twostate predicate everyGoodBankPreservesBalances( except : set<Account> )
       reads *
     // reads this,Repr,myBank.ledger.Keys,myBank.ledger.Keys`Repr //COULDN'T GET THIS TO WORK OTHERWISE :-(
     // reads desmesnes()
    requires valid()
    requires (forall a <- myBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    requires (forall a <- myBank.ledger.Keys :: (a.myBank == myBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()
     { obeys() ==> (
         && (myBank.ledger.Keys >= old(myBank.ledger.Keys))
         && (forall a <- old(myBank.ledger.Keys) | a !in except :: myBank.ledger[a] == old(myBank.ledger[a]))
         ) }

    predicate canDepositFrom(amount : nat, from : Account) : (b : bool)
      requires valid()
         reads this,Repr  //reads myBank`ledger
       ensures obeys() ==> b ==> (this in (myBank.ledger.Keys))
       ensures obeys() ==> b ==> (from in (myBank.ledger.Keys))
       ensures obeys() ==> b ==> (this.myBank.ledger == from.myBank.ledger)
    {  //should this acutally have a body here?
              && (this != from)
              && (myBank == from.myBank)
              && (this in (myBank.ledger.Keys))
              && (from in (myBank.ledger.Keys))
              && ((myBank.ledger[from] >= amount))
    }

} //end trait Account


lemma GoodAccountObeys(account : Account)
  ensures (account is GoodAccount) ==> (account.obeys())
  {
    if (account is GoodAccount) { var gp := account as GoodAccount; reveal gp.obeys(); }
  }

lemma AllGoodAccounts(bank : Bank)
 //there is something rather weird going on here!  -- yeah, doesen't make sense (17 Nov 2026)
  requires forall account <- bank.ledger :: account is GoodAccount
   ensures forall account : GoodAccount <- bank.ledger :: account.obeys()
  {
    assert forall account <- bank.ledger :: account is GoodAccount;

    forall account : GoodAccount <- bank.ledger ensures account.obeys()
     {
       assert account is GoodAccount;
       var gp := account as GoodAccount;
       reveal gp.obeys();
       assert gp.obeys();
    }
    assert forall account : GoodAccount <- bank.ledger :: account.obeys();

   // if (account is GoodAccount) { var gp := account as GoodAccount; reveal gp.obeys(); }
  }


class GoodAccount extends Account {

  opaque ghost predicate obeys() {true} //reads Inside(this)  {true}

  ghost predicate valid() : (b : bool)
       reads this, Repr
     ensures b ==> (this in Repr)
     ensures b ==> (myBank in Repr)
     ensures b ==> (this in myBank.ledger.Keys)
     {
      && (this in Repr)
      && (myBank in Repr)
      && (myBank is GoodBank)
      && (this in myBank.ledger.Keys)
      }


  constructor(aBank : Bank)  //assumed called only from the Bank
    modifies aBank`ledger     //should ideally be aBank.Repr?
    requires aBank is GoodBank
    requires (forall a <- aBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    requires (forall a <- aBank.ledger.Keys :: (a.myBank == aBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()
    ensures this in myBank.ledger
     ensures myBank == aBank
     ensures fresh(this)
     ensures myBank.ledger == old(aBank.ledger)[this := 0]
     ensures obeys()
     ensures myBank is GoodBank
     ensures obeys() ==> (forall account <- myBank.ledger.Keys :: account.valid())   //which of these should have obeys()
     ensures aBank.ledger.Keys >= old(aBank.ledger.Keys)
     ensures valid()
    {
      myBank := aBank;
      Repr := {this, aBank};
      new;
      assert this !in aBank.ledger.Keys;
      myBank.ledger := myBank.ledger[this := 0];
      assert myBank.ledger.Keys >= old(aBank.ledger.Keys);
      reveal obeys();  //needed to prove ensures obeys()
      assert valid();
    }

  method sprout() returns (account : Account)
    requires valid()
    requires (forall a <- myBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    requires (forall a <- myBank.ledger.Keys :: (a.myBank == myBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()

    modifies Repr // myBank`ledger

    ensures account.valid()
    ensures account.myBank == myBank
    ensures obeys() ==> (account in myBank.ledger)
    ensures obeys() ==> (fresh(account))

    ensures obeys() ==> account.obeys()

    ensures obeys() ==> (myBank.ledger == old(myBank.ledger)[account := 0])
    ensures obeys() ==> (forall k <- old(myBank.ledger.Keys) :: myBank.ledger[k] == old(myBank.ledger[k]))
    ensures obeys() ==> (forall account <- myBank.ledger :: account.valid())
    ensures myBank.ledger.Keys >= old(myBank.ledger.Keys)

    ensures valid()
    {
      reveal obeys();
      account := new GoodAccount(myBank);
    }


  method deposit(amount : nat, from : Account) returns (b : bool)
    requires valid()
    requires (forall a <- myBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    requires (forall a <- myBank.ledger.Keys :: (a.myBank == myBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()

    modifies this,Repr,from.Repr,myBank`ledger

     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from)) ==> b)
     ensures (obeys() && b && old(canDepositFrom(amount, from))) ==> from.obeys()

     ensures (obeys() ==> not(b) ==> unchanged(myBank))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (this in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (from in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[this]   == (old(myBank.ledger[this]  ) + amount)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[from] == (old(myBank.ledger[from]) - amount)))
     ensures forall a <- old(myBank.ledger) | (a !in {this, from}) && a.obeys() :: a in myBank.ledger.Keys && myBank.ledger[a] == old(myBank.ledger[a])
     ensures obeys() ==> (forall a <- myBank.ledger :: a.valid())
     ensures valid()

  {
    reveal obeys();

    assert valid();
    assert (forall a <- myBank.ledger | a != this :: a.valid());

  b := false;

  if (canDepositFrom(amount,from))
    {
        myBank.ledger := myBank.ledger
            [from := ((myBank.ledger[from]) - amount)]
            [this := ((myBank.ledger[this]) + amount)];

        assert valid();
        assert (forall account <- myBank.ledger.Keys :: (account.myBank == myBank) && (account is GoodAccount) && account.obeys());
        assert (forall account <- myBank.ledger :: account.valid());
        assert obeys() ==> (forall account <- myBank.ledger :: account.valid());

        assert from in myBank.ledger.Keys;
        assert from.myBank == myBank;

        assert from.obeys();
        b := true;
    }
}

  /// moved up into Account so we can't define it here...
  // function balance() : (b : nat)
  //      reads myBank  {if (this in myBank.ledger.Keys) then (myBank.ledger[this]) else (0)}
}










class GoodBank extends Bank {
  //what are good Accounts made of?  sugar, spice, and all things nice.
  //that's what good Accounts are made of

  constructor()
     ensures fresh(this)
     ensures (forall a <- ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
     ensures (forall a <- ledger.Keys :: (a.myBank == this) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys(
     { ledger := map[]; }

  method {:isolate_assertions} newAccount(balance : nat) returns ( account : Account )
    modifies `ledger
    requires (forall a <- ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    requires (forall a <- ledger.Keys :: (a.myBank == this) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys(
    ensures fresh(account)
    ensures account !in old(ledger)
    ensures ledger == old(ledger)[account:=balance]
    ensures account.myBank == this
    ensures account.obeys()
    ensures account.valid()
    ensures (forall x <- old(ledger.Keys) :: old(ledger[x]) == ledger[x])
    ensures (forall a <- ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
    ensures (forall a <- ledger.Keys :: (a.myBank == this) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys(
  {
    account := new GoodAccount(this); ///where do good Accounts come from?  from a GOOD BANK
    ledger := ledger[account:=balance];
  }

} //end GoodBank




method Main()
  modifies set x : object :: x
{
  //money sm is seller, bm is buyer
  var m1 := new GoodBank();


assert forall a <- m1.ledger.Keys :: (a.myBank == m1) && (a is GoodAccount) && a.valid();

  var sm : Account := m1.newAccount(10);


  assert sm.obeys(); assert sm.valid();


  var bm : Account := m1.newAccount(20);

  assert bm.balance()==20;

    assert sm.obeys();  assert sm.valid();
    assert bm.obeys();  assert bm.valid();

var b := false;

//  opaque
//     modifies sm,bm,sm.myBank,bm.myBank,sm.myBank`ledger,bm.myBank`ledger,sm.myBank.ledger.Keys,bm.myBank.ledger.Keys
//      ensures sm.valid()
//      ensures bm.valid()


   b :=  sm.deposit(7,bm);


  print "b=",b," sm=",sm.balance(),"  bm=",bm.balance(),"\n";

  if not(b) {return;}

  assert sm.obeys();
  assert sm.valid();
  assert bm.balance()==13;


//goods.  sg is seller, bg is buyer
  var m2 := new GoodBank();
  var sg := m2.newAccount(3);
  var bg := m2.newAccount(0);

  print "sg=",sg.balance(),"  bg=",bg.balance(),"\n";

  b := dealV0(sm,sg,10, bm, bg, 2);


  print "b=",b,"\n";
  print "sm=",sm.balance(),"  bm=",bm.balance(),"\n";
  print "sg=",sg.balance(),"  bg=",bg.balance(),"\n";

//  assert sm.balance()==27;
//   assert bm.balance()==3;
//   assert sg.balance()==1;
//   assert bg.balance()==2;


}


method doit(m1 : Bank, sm : Account, bm : Account) returns (b : bool)
 //another "verification sanity test"  method what never gets run
  requires sm.obeys() && bm.obeys()   //?????
  requires sm.valid() && bm.valid()

  requires (forall a <- sm.myBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
  requires (forall a <- sm.myBank.ledger.Keys :: (a.myBank == sm.myBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()

  requires (forall a <- bm.myBank.ledger.Keys :: a.valid())   ///no obeys obn here cos it's validity
  requires (forall a <- bm.myBank.ledger.Keys :: (a.myBank == bm.myBank) && (a is GoodAccount) && (a.valid()))   //also used to have account.obeys()


  requires sm.canDepositFrom(7,bm)
  requires sm != bm
  requires bm.balance() == 100

//  modifies m1`ledger, sm.myBank`ledger, bm.myBank`ledger
  modifies m1, sm,sm.Repr,sm.myBank`ledger, bm,bm.Repr, bm.myBank`ledger

  ensures  b ==> ( sm.balance() == old(sm.balance()) + 7)
{
  print "sm=",sm.balance(),"  bm=",bm.balance(),"\n";

assert sm.obeys() && bm.obeys();
assert sm.canDepositFrom(7,bm);

assert HERE:  (sm.obeys() && bm.obeys() && old(sm.canDepositFrom(7, bm)));
  b :=  sm.deposit(7,bm);

  assert old@HERE(sm.obeys() && bm.obeys() && (sm.canDepositFrom(7, bm)));

  assert  (sm.obeys() && bm.obeys() && old(sm.canDepositFrom(7, bm)));

assert b;

  print "b=",b," sm=",sm.balance(),"  bm=",bm.balance(),"\n";
}




method dealV0(sellerMoney : Account, sellerGoods : Account, price : nat,
               buyerMoney : Account, buyerGoods : Account,  amount : nat) returns ( b : bool )
//a non-escrow deal!
//works if we require all Accounts are good;
//doesn't work without that requirement.

   requires sellerMoney.obeys()
   requires sellerGoods.obeys()
   requires buyerMoney.obeys()
   requires buyerGoods.obeys()

   requires sellerMoney.obeys() ==> sellerMoney.valid()
   requires sellerGoods.obeys() ==> sellerGoods.valid()
   requires buyerMoney.obeys()  ==> buyerMoney.valid()
   requires buyerGoods.obeys()  ==> buyerGoods.valid()

   requires sellerMoney.canDepositFrom(price, buyerMoney)
   requires buyerGoods.canDepositFrom(amount, sellerGoods)

   requires (sellerMoney.myBank != buyerGoods.myBank)
   requires (sellerGoods.myBank != buyerMoney.myBank)

   requires forall a <- sellerMoney.myBank.ledger.Keys :: (a.myBank == sellerMoney.myBank) && (a is GoodAccount) && (a.valid())
   requires forall a <- buyerMoney.myBank.ledger.Keys  :: (a.myBank == buyerMoney.myBank)  && (a is GoodAccount) && (a.valid())
   requires forall a <- sellerGoods.myBank.ledger.Keys :: (a.myBank == sellerGoods.myBank) && (a is GoodAccount) && (a.valid())
   requires forall a <- buyerGoods.myBank.ledger.Keys  :: (a.myBank == buyerGoods.myBank)  && (a is GoodAccount) && (a.valid())


  //  modifies sellerMoney.myBank`ledger, buyerMoney.myBank`ledger
  //  modifies sellerGoods.myBank`ledger, buyerGoods.myBank`ledger
   modifies sellerMoney.Repr, buyerMoney.Repr
   modifies sellerGoods, sellerGoods.Repr, buyerGoods, buyerGoods.Repr

  //  ensures  sellerMoney.obeys() ==> b ==> (sellerMoney.balance() == old(sellerMoney.balance()) + price)
  //  ensures  buyerMoney.obeys()  ==> b ==> (buyerMoney.balance() == old(buyerMoney.balance()) - price)
  //  ensures  buyerGoods.obeys()  ==> b ==> (buyerGoods.balance() == old(buyerGoods.balance()) + amount)
  //  ensures  sellerGoods.obeys() ==> b ==> (sellerGoods.balance() == old(sellerGoods.balance()) - amount)
  {

assert buyerGoods.obeys();
assert buyerGoods.valid();
assert (forall a <- buyerGoods.myBank.ledger.Keys :: a.valid());
assert (forall a <- buyerGoods.myBank.ledger.Keys :: (a.myBank == buyerGoods.myBank) && (a is GoodAccount) && (a.valid()));

      var b1 := sellerMoney.deposit(price, buyerMoney);

      if (! b1) { return false; }

assert buyerGoods.obeys();
assert buyerGoods.valid();
assert (forall a <- buyerGoods.myBank.ledger.Keys :: a.valid());
assert (forall a <- buyerGoods.myBank.ledger.Keys :: (a.myBank == buyerGoods.myBank) && (a is GoodAccount) && (a.valid()));


      var b2 := buyerGoods.deposit(amount, sellerGoods);



      if (! b2) { return false; }

      b := b1 && b2;
      assert b;
}



method {:isolate_assertions} dealV2(sellerMoney : Account, sellerGoods : Account, price : nat,
               buyerMoney : Account, buyerGoods : Account,  amount : nat) returns ( res : bool )


//escrow deal - highly sequential version
//note **doesn't handle exceptions properly**
//if Dafny has "exceptions" which I don't think it really does

   requires sellerMoney.valid()
   requires sellerGoods.valid()
   requires buyerMoney.valid()
   requires buyerGoods.valid()
//
//    requires sellerMoney.obeys() ==> sellerMoney.valid()
//    requires sellerGoods.obeys() ==> sellerGoods.valid()
//    requires buyerMoney.obeys()  ==> buyerMoney.valid()
//    requires buyerGoods.obeys()  ==> buyerGoods.valid()



  //  requires sellerMoney.canDepositFrom(price, buyerMoney)
  //  requires buyerGoods.canDepositFrom(amount, sellerGoods)

   requires (sellerMoney.myBank != buyerGoods.myBank)
   requires (sellerGoods.myBank != buyerMoney.myBank)

   modifies sellerMoney.myBank`ledger, buyerMoney.myBank`ledger
   modifies sellerGoods.myBank`ledger, buyerGoods.myBank`ledger

  //  ensures  b ==> (sellerMoney.balance() == old(sellerMoney.balance()) + price)
  //  ensures  b ==> (buyerMoney.balance() == old(buyerMoney.balance()) - price)
  //  ensures  b ==> (buyerGoods.balance() == old(buyerGoods.balance()) + amount)
  //  ensures  b ==> (sellerGoods.balance() == old(sellerGoods.balance()) - amount)
  {

  //setup and validate Money purses
                                                          assert sellerMoney.valid();
//    assume sellerMoney is GoodAccount;
      assert (sellerMoney.myBank is GoodBank);
      assert (sellerMoney in sellerMoney.myBank.ledger.Keys);
      assert (forall account <- sellerMoney.myBank.ledger.Keys :: (account.myBank == sellerMoney.myBank) && (account is GoodAccount) && account.obeys());

 assert buyerMoney.valid();
 assert buyerMoney in buyerMoney.myBank.ledger.Keys;

  var escrowMoney := sellerMoney.sprout();

  assert escrowMoney.valid();
  assert sellerMoney.valid();
//  assert buyerMoney.valid();

  if (buyerMoney.myBank == sellerMoney.myBank)
     {
      assert buyerMoney.myBank.ledger == sellerMoney.myBank.ledger;

      assert buyerMoney in buyerMoney.myBank.ledger.Keys;
      assert buyerMoney in sellerMoney.myBank.ledger.Keys;
      assert buyerMoney.valid();
     }
else
{
  assert unchanged(buyerMoney.myBank`ledger);
  assert buyerMoney.valid();
}
                                                          assert sellerMoney.obeys() ==> sellerMoney.valid();
                                                          assert sellerMoney.obeys() ==> escrowMoney.obeys();
                                                          assert sellerMoney.obeys() ==> (escrowMoney.obeys() ==> escrowMoney.valid());
                                                          assert (sellerMoney.obeys() && escrowMoney.obeys()) ==> (sellerMoney.obeys() ==> escrowMoney.valid());
                                                          assert (sellerMoney.obeys() ==> escrowMoney.valid());
                                                          assert  sellerMoney.obeys() ==> (sellerMoney.myBank == escrowMoney.myBank);
                                                          assert buyerMoney.valid();

  res := escrowMoney.deposit(0,sellerMoney);
  if (!res)  {return false;}
                                                          assert buyerMoney.valid();
  res := buyerMoney.deposit(0,escrowMoney);
  if (!res)  {return false;}
  res := escrowMoney.deposit(0,buyerMoney);
  if (!res)  {return false;}

  //setup and validate Goods purses
  var escrowGoods := buyerGoods.sprout();
  res := escrowGoods.deposit(0,buyerGoods);
  if (!res)  {return false;}
  res := sellerGoods.deposit(0,escrowGoods);
  if (!res)  {return false;}
  res := escrowGoods.deposit(0,sellerGoods);
  if (!res)  {return false;}

  res := escrowMoney.deposit(price,buyerMoney);
  if (!res)  {return false;}
  res := escrowGoods.deposit(amount,sellerGoods);
  if (!res)  {
    var tmp1 := buyerMoney.deposit(price,escrowMoney);
    return false;}

  var tmp2 := sellerMoney.deposit(price,escrowMoney);
  var tmp3 := buyerGoods.deposit(amount,escrowGoods);

  return true;
}

































class BadBank extends Bank {
  //what are bad Accounts made of?  slugs and snails and puppydogs' tails.
  //that's what bad Accounts are made of.
  //
  //reaching for BadBankOn joke and flailing at the shuttlecock…

  constructor()
     ensures fresh(this)
     { ledger := map[]; }

  method {:isolate_assertions} newAccount(balance : nat) returns ( account : Account )
   requires forall account <- ledger.Keys :: (account.myBank == this)
   modifies `ledger
    ensures fresh(account)
    ensures account.obeys() ==> (account !in old(ledger))
    ensures account.obeys() ==> (ledger == old(ledger)[account:=balance])
    ensures account.myBank == this
    ensures account.obeys() ==> account.valid()
    ensures account.obeys() ==> (forall x <- old(ledger.Keys) :: old(ledger[x]) == ledger[x])
    ensures forall account <- ledger.Keys :: (account.myBank == this)
  {
    account := new BadAccount(this); ///where do bad Accounts come from?  from a BAD BANK
    ledger := ledger[account:=balance];
  }
}


class BadAccount extends Account {

  opaque ghost predicate obeys() {false} //reads Inside(this)  {false}
     //assumed instance-private

  ghost predicate valid()
    reads myBank`ledger { true }

  constructor(aBank : BadBank)  //assumed called only from the Bank
    modifies aBank`ledger
    requires aBank is BadBank
 //   requires (forall account <- aBank.ledger.Keys :: (account.myBank == aBank) && (account is BadAccount))
     ensures this in myBank.ledger
     ensures myBank == aBank
     ensures fresh(this)
     ensures myBank.ledger == old(aBank.ledger)[this := 0]
     ensures myBank is BadBank
     ensures valid()
    { myBank := aBank;
      new;
      myBank.ledger := myBank.ledger[this := 0];
      reveal obeys();
    }

  method {:isolate_assertions} sprout() returns (account : Account)
    requires valid()
    requires obeys() ==> (forall account <- myBank.ledger :: account.valid())

   modifies myBank`ledger

    ensures account.valid()
    ensures account.myBank == myBank
    ensures obeys() ==> (account in myBank.ledger)
    ensures obeys() ==> (fresh(account))

    ensures obeys() ==> account.obeys()

    ensures obeys() ==> (myBank.ledger == old(myBank.ledger)[account := 0])
    ensures obeys() ==> (forall k <- old(myBank.ledger.Keys) :: myBank.ledger[k] == old(myBank.ledger[k]))
    ensures obeys() ==> (forall account <- myBank.ledger :: account.valid())

    ensures myBank.ledger.Keys >= old(myBank.ledger.Keys)
    ensures valid()

    {
      reveal obeys();

      if (myBank is BadBank)
        { account := new BadAccount(myBank as BadBank); }
      else
        { account := this; }
    }


  method {:isolate_assertions} deposit(amount : nat, from : Account) returns (b : bool)
    requires obeys() ==> valid()

    modifies myBank`ledger

     ensures (obeys() && old(canDepositFrom(amount, from)) ==> b)
     ensures (obeys() && b) ==> from.obeys()

     ensures (obeys() ==> not(b) ==> unchanged(myBank))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (this in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (from in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[this]   == (old(myBank.ledger[this]  ) + amount)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[from] == (old(myBank.ledger[from]) - amount)))
     ensures forall account <- old(myBank.ledger) | (account !in {this, from}) && account.obeys() :: account in myBank.ledger.Keys && myBank.ledger[account] == old(myBank.ledger[account])
     ensures obeys() ==> valid()
     ensures obeys() ==> (forall account <- myBank.ledger :: account.valid())
  {
    reveal obeys();

  b := false;

  if (canDepositFrom(amount,from))
    {
        myBank.ledger := myBank.ledger
            [from := ((myBank.ledger[from]) - amount)]
            [this := ((myBank.ledger[this]) + (amount * 2))];

        assert valid();

        b := true;
    }
}

  /// moved up into Account so we can't define it here...
  // function balance() : (b : nat)
  //      reads myBank  {if (this in myBank.ledger.Keys) then (myBank.ledger[this]) else (0)}
}



























































































predicate not(x : bool) {!x}
