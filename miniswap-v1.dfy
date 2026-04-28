//a more minimal attempt

trait Bank {
   var ledger : map<Account,nat>
 }


trait Account {

  opaque ghost predicate obeys() //reads this

  ghost predicate valid() reads myBank`ledger
 //validity predicate

  const myBank : Bank //Dafny won't easilly let us say this, but let's assume this is instance-private

  method sprout() returns (account : Account)
    requires obeys() ==> valid()

    modifies myBank`ledger

    ensures obeys() ==> account.obeys() && account.valid()

    ensures obeys() ==> (account.myBank == myBank)
    ensures obeys() ==> (account in myBank.ledger)
    ensures obeys() ==> (fresh(account))
    ensures obeys() ==> (myBank.ledger == old(myBank.ledger)[account := 0])
    ensures obeys() ==> (forall k <- old(myBank.ledger.Keys) :: myBank.ledger[k] == old(myBank.ledger[k]))
    ensures obeys() ==> valid()


  method deposit(amount : nat, from : Account) returns (b : bool)
    requires obeys() ==> valid()

    modifies myBank`ledger

     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from)) ==> b)
     ensures (obeys() && b && old(canDepositFrom(amount, from))) ==> from.obeys()

     ensures (obeys() ==> not(b) ==> unchanged(myBank`ledger))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (this in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (from in (myBank.ledger)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[this] == (old(myBank.ledger[this]  ) + amount)))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (myBank.ledger[from] == (old(myBank.ledger[from]) - amount)))
     ensures forall account <- old(myBank.ledger) | (account !in {this, from}) && account.obeys() :: account in myBank.ledger.Keys && myBank.ledger[account] == old(myBank.ledger[account])
     ensures obeys() ==> valid()


  function balance() : (b : nat)
     // requires obeys() ==> valid()
       reads myBank  {if (this in myBank.ledger.Keys) then (myBank.ledger[this]) else (0)}

//twostate
    predicate canDepositFrom(amount : nat, from : Account) : (b : bool)
      requires obeys() ==> valid()

         reads myBank`ledger
       ensures obeys() ==> b ==> (this in (myBank.ledger.Keys))
       ensures obeys() ==> b ==> (from in (myBank.ledger.Keys))
       ensures obeys() ==> b ==> (this.myBank.ledger == from.myBank.ledger)
    {
              && (this != from)
              && (myBank == from.myBank)
              // && (this in old(myBank.ledger.Keys))
              // && (from in old(myBank.ledger.Keys))
              && (this in (myBank.ledger.Keys))
              && (from in (myBank.ledger.Keys))
//            && (old(myBank.ledger[from] >= amount))GoodAccount
              && ((myBank.ledger[from] >= amount))
    }



} //end trait Account


lemma GoodAccountObeys(account : Account)
  ensures (account is GoodAccount) ==> (account.obeys())
  {
    if (account is GoodAccount) { var gp := account as GoodAccount; reveal gp.obeys(); }
  }

lemma AllGoodAccounts(bank : Bank)
 //there is something rather weird going on here!
 // requires forall account <- bank.ledger :: account is GoodAccount
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

  opaque ghost predicate obeys() {true} //reads this  {true}
     //assumed instance-private


  ghost predicate valid()
    reads myBank`ledger {
      && (myBank is GoodBank)
      && (this in myBank.ledger.Keys)
      && (forall account <- myBank.ledger.Keys :: (account.myBank == myBank) && (account is GoodAccount) && account.obeys())
  }


  constructor(aBank : Bank)  //assumed called only from the Bank
    modifies aBank`ledger
    requires aBank is GoodBank
    requires (forall account <- aBank.ledger.Keys :: (account.myBank == aBank) && (account is GoodAccount) && account.obeys())
     ensures this in myBank.ledger
     ensures myBank == aBank
     ensures fresh(this)
     ensures myBank.ledger == old(aBank.ledger)[this := 0]
     ensures obeys()
     ensures myBank is GoodBank
     ensures valid()
    { myBank := aBank;
      new;
      myBank.ledger := myBank.ledger[this := 0];
      reveal obeys();
    }

  method sprout() returns (account : Account)
    requires obeys() ==> valid()

    modifies myBank`ledger
     ensures account in myBank.ledger
     ensures account.myBank == myBank
     ensures fresh(account)
     ensures myBank.ledger == old(myBank.ledger)[account := 0]

    ensures account.obeys()

    {
      reveal obeys();
      account := new GoodAccount(myBank);
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

  {
    reveal obeys();

  b := false;

  if (canDepositFrom(amount,from))
    {
        myBank.ledger := myBank.ledger
            [from := ((myBank.ledger[from]) - amount)]
            [this := ((myBank.ledger[this]) + amount)];

        assert valid();
        assert (forall account <- myBank.ledger.Keys :: (account.myBank == myBank) && (account is GoodAccount) && account.obeys());
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
     ensures forall account <- ledger.Keys :: (account.myBank == this) &&  account is GoodAccount  && account.obeys()
     { ledger := map[]; }

  method {:isolate_assertions} newAccount(balance : nat) returns ( account : Account )
    modifies `ledger
    requires forall account <- ledger.Keys :: (account.myBank == this) &&  account is GoodAccount  && account.obeys()
    ensures fresh(account)
    ensures account !in old(ledger)
    ensures ledger == old(ledger)[account:=balance]
    ensures account.myBank == this
    ensures account.obeys()
    ensures account.valid()
    ensures (forall x <- old(ledger.Keys) :: old(ledger[x]) == ledger[x])
    ensures  forall account <- ledger.Keys :: (account.myBank == this) && (account is GoodAccount) && account.obeys()
  {
    account := new GoodAccount(this); ///where do bad Accounts come from?  from a BAD BANK
    ledger := ledger[account:=balance];
  }

} //end GoodBank




method {:isolate_assertions} Main() {

  //money sm is seller, bm is buyer
  var m1 := new GoodBank();


assert forall account <- m1.ledger.Keys :: (account.myBank == m1) && (account is GoodAccount) && account.obeys();

  var sm : Account := m1.newAccount(10);


  assert sm.obeys(); assert sm.valid();


  var bm : Account := m1.newAccount(20);


    assert sm.obeys();  assert sm.valid();
    assert bm.obeys();  assert bm.valid();

  var b :=  sm.deposit(7,bm);

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
  requires sm.obeys() && bm.obeys()
  requires sm.valid() && bm.valid()
  requires sm.canDepositFrom(7,bm)
  requires sm != bm
  requires bm.balance() == 100

  modifies m1`ledger, sm.myBank`ledger, bm.myBank`ledger

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

   modifies sellerMoney.myBank`ledger, buyerMoney.myBank`ledger
   modifies sellerGoods.myBank`ledger, buyerGoods.myBank`ledger

   ensures  b ==> (sellerMoney.balance() == old(sellerMoney.balance()) + price)
   ensures  b ==> (buyerMoney.balance() == old(buyerMoney.balance()) - price)
   ensures  b ==> (buyerGoods.balance() == old(buyerGoods.balance()) + amount)
   ensures  b ==> (sellerGoods.balance() == old(sellerGoods.balance()) - amount)
  {
      var b1 := sellerMoney.deposit(price, buyerMoney);

      if (! b1) { return false; }

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

   requires sellerMoney.obeys() ==> sellerMoney.valid()
   requires sellerGoods.obeys() ==> sellerGoods.valid()
   requires buyerMoney.obeys()  ==> buyerMoney.valid()
   requires buyerGoods.obeys()  ==> buyerGoods.valid()

   requires sellerMoney.canDepositFrom(price, buyerMoney)
   requires buyerGoods.canDepositFrom(amount, sellerGoods)

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
  var escrowMoney := sellerMoney.sprout();
                                                          assert sellerMoney.obeys() ==> sellerMoney.valid();
                                                          assert sellerMoney.obeys() ==> escrowMoney.obeys();
                                                          assert sellerMoney.obeys() ==> (escrowMoney.obeys() ==> escrowMoney.valid());
                                                          assert (sellerMoney.obeys() && escrowMoney.obeys()) ==> (sellerMoney.obeys() ==> escrowMoney.valid());
                                                          assert (sellerMoney.obeys() ==> escrowMoney.valid());
                                                          assert  sellerMoney.obeys() ==> (sellerMoney.myBank == escrowMoney.myBank);
assume sellerMoney.obeys();

  res := escrowMoney.deposit(0,sellerMoney);
  if (!res)  {return false;}
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

  opaque ghost predicate obeys() {false} //reads this  {false}
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

  method sprout() returns (account : Account)

    requires obeys() ==> valid()

    modifies myBank`ledger

    ensures obeys() ==> account.obeys()

    ensures obeys() ==> (account in myBank.ledger)
    ensures obeys() ==> (fresh(account))
    ensures obeys() ==> (myBank.ledger == old(myBank.ledger)[account := 0])
    ensures obeys() ==> (forall k <- old(myBank.ledger.Keys) :: myBank.ledger[k] == old(myBank.ledger[k]))
    ensures obeys() ==> valid()

    requires obeys() ==> valid()

    modifies myBank`ledger
     ensures account.myBank == myBank
     ensures account.obeys() ==> (account in myBank.ledger)
     ensures account.obeys() ==> fresh(account)
     ensures account.obeys() ==> (myBank.ledger == old(myBank.ledger)[account := 0])

    ensures obeys() ==> valid()

    {
      reveal obeys();

      if (myBank is BadBank)
        { account := new BadAccount(myBank); }
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
