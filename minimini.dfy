//a more minimal attempt

trait Account extends object {

  opaque ghost predicate obeys() //reads this

  method sprout() returns (account : Account)
    ensures fresh(account) //THIS IS LESS THAN IDEAL INNI
    ensures obeys() ==> account.obeys()
    ensures balance() == old(balance())      ///WHOOPS HSOUDL HAEV OBEYS
    ensures account.balance() == 0           ///WHOOPS HSOUDL HAEV OBEYS
    ensures this.obeys() ==> account.canDepositFrom(0, this)
    ensures this.obeys() ==> this.canDepositFrom(0, account)


  method deposit(amount : nat, from : Account) returns (b : bool)
    modifies this, from

     ensures (obeys() && b) ==> from.obeys()
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from)) ==> b)
     ensures (obeys() && b && old(canDepositFrom(amount, from))) ==> from.obeys()
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (    b  ==> (this.balance() == old(this.balance()) + amount))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (    b  ==> (from.balance() == old(from.balance()) - amount))
     ensures (obeys() && (not(from.obeys()) || not(old(canDepositFrom(0, from))))) ==> (not(b) ==> (this.balance() == old(this.balance())         ))   //>>?WTF
     ensures (obeys() && from.obeys() && old(canDepositFrom(0, from)))             ==> (not(b) ==> (from.balance() == old(from.balance())         ))   //>>?WTF

     ensures (obeys()                 && (amount == 0) ==> (this.balance() == old(this.balance()) )) //KJX paranoia?
     ensures (obeys() && from.obeys() && (amount == 0) ==> (from.balance() == old(from.balance()) )) //KJX paranoia?

     ensures (obeys() && not(old(canDepositFrom(amount, from)))) ==> not(b)
     ensures ((obeys() && b) ==> canDepositFrom(0, from))

  function balance() : nat  reads this

 ghost predicate canDepositFrom(amount : nat, from : Account) : (b : bool)
       reads from
    //  ensures b ==> canDepositFrom(0, from)
    //  ensures (b ==> from is GoodAccount)
    //  ensures (b ==> (amount <= (from.balance())))
        { canTrade(from) && (from.balance() >= amount) }

ghost predicate canTrade(from : Account) : (b : bool)
       reads {}
   decreases 1

} //end trait Account

































































class GoodAccount extends Account {

  opaque ghost predicate obeys() : (r : bool) ensures r {true}
     //assumed instance-private

   var myBalance : nat


  constructor(initial : nat)  //assumed called only from the Bank
     ensures obeys()
     ensures obeys() ==> balance() == initial
     ensures fresh(this)
    {
      myBalance := initial;
      new;
      reveal obeys();
    }

  method sprout() returns (account : Account)
    ensures fresh(account) //THIS IS LESS THAN IDEAL INNI
    ensures obeys() ==> account.obeys()
    ensures balance() == old(balance())      ///WHOOPS HSOUDL HAEV OBEYS
    ensures account.balance() == 0           ///WHOOPS HSOUDL HAEV OBEYS
    ensures account.canDepositFrom(0, this)  ///WHOOPS HSOUDL HAEV OBEYS
    ensures this.canDepositFrom(0, account)  ///WHOOPS HSOUDL HAEV OBEYS
    ensures account is GoodAccount
    {
      account := new GoodAccount(0);
    }


  method {:isolate_assertions} deposit(amount : nat, from : Account) returns (b : bool)

    modifies this, from


     ensures (obeys() && b) ==> from.obeys()
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from)) ==> b)
     ensures (obeys() && b && old(canDepositFrom(amount, from))) ==> from.obeys()
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (    b  ==> (this.balance() == old(this.balance()) + amount))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (    b  ==> (from.balance() == old(from.balance()) - amount))
     ensures (obeys() && (not(from.obeys()) || not(old(canDepositFrom(0, from))))) ==> (not(b) ==> (this.balance() == old(this.balance())         ))   //>>?WTF
     ensures (obeys() && from.obeys() && old(canDepositFrom(0, from))) ==> (not(b) ==> (from.balance() == old(from.balance())         ))   //>>?WTF

     ensures ((obeys()                 && (amount == 0)) ==> (this.balance() == old(this.balance()) )) //KJX paranoia?
     ensures ((obeys() && from.obeys() && (amount == 0)) ==> (from.balance() == old(from.balance()) )) //KJX paranoia?

     ensures (obeys() && not(old(canDepositFrom(amount, from)))) ==> not(b)
     ensures ((obeys() && b) ==> canDepositFrom(0, from))

     ensures ((this == from)) ==> not(b)
     ensures ((from is GoodAccount) ==> from.obeys())

//versions without this.obeys()  (but it's there implicitly anyway)
    //  ensures (from.obeys() && old(canDepositFrom(amount, from)) ==> b)
    //  ensures (b && old(canDepositFrom(amount, from))) ==> from.obeys()
    //  ensures (from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (this.balance() == old(this.balance()) + amount))
    //  ensures (from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (from.balance() == old(from.balance()) - amount))
    //  ensures (b ==> canDepositFrom(0, from))

{
  b := false;
  if (this == from) { assert not(canDepositFrom(amount, from));  return; }
  var oldBalance := balance();                     assert oldBalance == myBalance == balance();

  if not(from is GoodAccount)  { assert not(canDepositFrom(amount, from)); return; }

  var good := (from as GoodAccount);
                                                   assert good.obeys() by { reveal good.obeys(); }
  if (good.balance() < amount) { assert not(canDepositFrom(amount, from)); return; }
                                                   assert good.myBalance >= amount;
  this.myBalance := this.myBalance + amount;
  good.myBalance := good.myBalance - amount;

  assert myBalance == oldBalance + amount;

  assert obeys();
  assert old(canDepositFrom(amount, from));
  b := true;
}


  function balance() : nat  reads this {myBalance}

  ghost predicate canTrade(from : Account) : (b : bool)
      decreases 0
     reads {}    {(this != from) && (from is GoodAccount)}

}























method {:isolate_assertions} Main() {

  var sm : Account := new GoodAccount(10);

  var bm : Account := new GoodAccount(20);

  var b :=  sm.deposit(7,bm);

  print "b=",b," sm=",sm.balance(),"  bm=",bm.balance(),"\n";

  if not(b) {return;}

  assert sm.obeys();
  assert bm.balance() == 13;


//goods.  sg is seller, bg is buyer
  var sg := new GoodAccount(3);
  var bg := new GoodAccount(0);

  print "sg=",sg.balance(),"  bg=",bg.balance(),"\n";

  b := dealV0(sm,sg,10, bm, bg, 2);

  print "b=",b,"\n";
  print "sm=",sm.balance(),"  bm=",bm.balance(),"\n";
  print "sg=",sg.balance(),"  bg=",bg.balance(),"\n";


  sm := new GoodAccount(10);
  bm := new GoodAccount(20);


  b := dealV2(sm,sg,10, bm, bg, 2);


//  assert sm.balance()==27;
//   assert bm.balance()==3;
//   assert sg.balance()==1;
//   assert bg.balance()==2;
}




method dealV0(sellerMoney : Account, sellerGoods : Account, price : nat,
               buyerMoney : Account, buyerGoods  : Account, amount : nat) returns ( b : bool )
//a non-escrow deal!
//works if we require all Accounts are good;
//doesn't work without that requirement.

   requires sellerMoney.obeys()
   requires sellerGoods.obeys()
   requires buyerMoney.obeys()
   requires buyerGoods.obeys()

   requires {sellerMoney} !! {sellerGoods} !! {buyerMoney} !! {buyerGoods}

   requires sellerMoney.canDepositFrom(price, buyerMoney)
   requires buyerGoods.canDepositFrom(amount, sellerGoods)

   modifies sellerMoney, buyerMoney
   modifies sellerGoods, buyerGoods

    ensures b ==> (sellerMoney.balance() == old(sellerMoney.balance()) + price)
    ensures b ==> (buyerMoney.balance() == old(buyerMoney.balance()) - price)
    ensures b ==> (buyerGoods.balance() == old(buyerGoods.balance()) + amount)
    ensures b ==> (sellerGoods.balance() == old(sellerGoods.balance()) - amount)
  {
      var b1 := sellerMoney.deposit(price, buyerMoney);

      assert b1 ==> (sellerMoney.balance() == old(sellerMoney.balance()) + price);
      assert b1 ==> (buyerMoney.balance() == old(buyerMoney.balance()) - price);

      if (! b1) { return false; }

      assert (sellerMoney.balance() == old(sellerMoney.balance()) + price);
      assert (buyerMoney.balance() == old(buyerMoney.balance()) - price);

      var b2 := buyerGoods.deposit(amount, sellerGoods);

      assert (sellerMoney.balance() == old(sellerMoney.balance()) + price);
      assert (buyerMoney.balance() == old(buyerMoney.balance()) - price);

      if (! b2) { return false; }

      b := b1 && b2;
      assert b;
}



method {:isolate_assertions} dealV2(sellerMoney : Account, sellerGoods : Account, price : nat,
               buyerMoney : Account, buyerGoods : Account,  amount : nat) returns ( res : bool )
//escrow deal - highly sequential version
//note **doesn't handle exceptions properly**
//if Dafny has "exceptions" which I don't think it really does

   modifies sellerMoney, buyerMoney
   modifies sellerGoods, buyerGoods

   requires {sellerMoney} !! {sellerGoods} !! {buyerMoney} !! {buyerGoods}

  // ensures sellerMoney != buyerGoods
  // ensures |{sellerMoney,sellerGoods,buyerMoney,buyerGoods}| == 4

   ensures  ( //Sophia's 1st case
             && (res)
             && (sellerMoney.obeys())
             && (buyerMoney.obeys())
             && (old(sellerMoney.canDepositFrom(price, buyerMoney)))
             && (sellerGoods.obeys())
             && (buyerGoods.obeys())
             && (old(buyerGoods.canDepositFrom(amount, sellerGoods)))
           ) ==> (
             && (buyerMoney.balance()  == old(buyerMoney.balance())   - price)
             && (sellerMoney.balance() == old(sellerMoney.balance())  + price)
             && (buyerGoods.balance()  == old(buyerGoods.balance())   + amount)
             && (sellerGoods.balance()  == old(sellerGoods.balance()) - amount)
             && (forall a : Account | a !in {sellerMoney,sellerGoods,buyerMoney,buyerGoods} && old(allocated(a)) :: a.balance() == old(a.balance()) )
           )

   ensures  ( //ignoring the return value - this combines Sophia's 2nd and 4th case.
             // && (res)
             && ( not(sellerMoney.obeys() && sellerGoods.obeys()) && not(buyerMoney.obeys() && buyerGoods.obeys()) )
           ) ==> (
             && (forall a : Account | a !in {sellerMoney,sellerGoods,buyerMoney,buyerGoods} && old(allocated(a)) :: a.balance() == old(a.balance()) )
           )

   ensures  ( //Sophia's 3rd case
             && not(res)
             && (|| (sellerMoney.obeys() && sellerGoods.obeys()) != (buyerMoney.obeys() && buyerGoods.obeys())   //!= is XOR
                 ||  not(old(sellerMoney.canDepositFrom(price, buyerMoney)))
                 ||  not(old(buyerGoods.canDepositFrom(amount, sellerGoods))) )
           ) ==> (
             && (forall a : Account | a !in {sellerMoney,sellerGoods,buyerMoney,buyerGoods} && old(allocated(a)) :: a.balance() == old(a.balance()) )
           )

    ensures ( //James' take on the 3rd case part I
             && not(res)
             && (  || (sellerMoney.obeys() != buyerMoney.obeys() )                    //!= is XOR
                   ||  not(old(sellerMoney.canDepositFrom(price, buyerMoney)))  )
           ) ==> (
             && (sellerMoney.obeys() ==> sellerMoney.balance() == old(sellerMoney.balance()) )
             && (buyerMoney.obeys()  ==> buyerMoney.balance()  == old(buyerMoney.balance())  )
           )

    ensures ( //James' take on the 3rd case part II
             && not(res)
             && (  || (sellerGoods.obeys() != buyerGoods.obeys() )                    //!= is XOR
                   ||  not(old(sellerGoods.canDepositFrom(price, buyerGoods)))  )
           ) ==> (
             && (sellerGoods.obeys() ==> sellerGoods.balance() == old(sellerGoods.balance()) )
             && (buyerGoods.obeys()  ==> buyerGoods.balance()  == old(buyerGoods.balance())  )
           )

//
//    ensures  (
//              && res
//              && sellerMoney.obeys()
//              && buyerMoney.obeys()
//              && old(sellerMoney.canDepositFrom(price, buyerMoney))
//              && sellerGoods.obeys()
//              && buyerGoods.obeys()
//              && old(buyerGoods.canDepositFrom(amount, sellerGoods))
//              )
//               ==> (buyerMoney.balance() == old(buyerMoney.balance()) - price)
  //  )
{
   var escrowMoney := sellerMoney.sprout();
                                                  // assert sellerMoney.obeys() ==> escrowMoney.obeys();
                                                  // assert sellerMoney.obeys() ==> (escrowMoney !in {sellerMoney, sellerGoods, buyerMoney, buyerGoods});
                                                  // // assert escrowMoney.canDepositFrom(0, sellerMoney);
                                                  // // assert sellerMoney.canDepositFrom(0, escrowMoney);
  res := escrowMoney.deposit(0,sellerMoney);
  if (!res) {return false;}
                                                //  assert                          sellerMoney.obeys() <==> escrowMoney.obeys();
                                                //  assert sellerMoney.obeys() ==> (sellerMoney.balance() == old(sellerMoney.balance()));
                                                //  assert                         (buyerMoney.balance() == old(buyerMoney.balance()));
                                                //  assert                         (buyerGoods.balance() == old(buyerGoods.balance()));
                                                //  assert                         (sellerGoods.balance() == old(sellerGoods.balance()));

  assert buyerMoney != escrowMoney;

                                                //  assert                         (buyerMoney.balance() == old(buyerMoney.balance()));
  res := buyerMoney.deposit(0,escrowMoney);
                                                //  assert sellerMoney.obeys() ==> (sellerMoney.balance() == old(sellerMoney.balance()));
                                                //  assert buyerMoney.obeys()  ==> (buyerMoney.balance()  == old(buyerMoney.balance()));
  if (!res)  {return false;}
                                                //  assert (buyerMoney != escrowMoney);
                                                //  assert buyerMoney.obeys() ==> escrowMoney.obeys();
                                                //  assert sellerMoney.obeys() ==> (sellerMoney.balance() == old(sellerMoney.balance()));
                                                //  assert buyerMoney.obeys()  ==> (buyerMoney.balance() == old(buyerMoney.balance()));
                                                //  assert                         (buyerGoods.balance() == old(buyerGoods.balance()));
                                                //  assert                         (sellerGoods.balance() == old(sellerGoods.balance()));

  res := escrowMoney.deposit(0,buyerMoney);
  if (!res)  {return false;}

                                                // assert buyerMoney.obeys() <==> escrowMoney.obeys();
                                                // assert                         escrowMoney.obeys() <==> sellerMoney.obeys();
                                                // assert buyerMoney.obeys()                          <==> sellerMoney.obeys();
                                                //  //
                                                //  // // assert buyerMoney.obeys() <==> escrowMoney.obeys() <==> sellerMoney.obeys(); // means something stupid
                                                //  assert buyerMoney.obeys()  ==  escrowMoney.obeys()  ==  sellerMoney.obeys(); // note == not <==>
                                                //  //
                                                //  assert sellerMoney.obeys() ==> (sellerMoney.balance() == old(sellerMoney.balance()));
                                                //  assert buyerMoney.obeys()  ==> (buyerMoney.balance() == old(buyerMoney.balance()));
                                                //  assert                         (buyerGoods.balance() == old(buyerGoods.balance()));
                                                //  assert                         (sellerGoods.balance() == old(sellerGoods.balance()));
                                                //  //
                                                //  assert sellerMoney.obeys() ==> (escrowMoney.balance() == 0);

  //setup and validate Goods purses
  var escrowGoods := buyerGoods.sprout();
  res := escrowGoods.deposit(0,buyerGoods);
  if (!res)  {return false;}
  res := sellerGoods.deposit(0,escrowGoods);
  if (!res)  {return false;}
  res := escrowGoods.deposit(0,sellerGoods);
  if (!res)  {return false;}

//                                                  assert sellerMoney.obeys() ==> (sellerMoney.balance() == old(sellerMoney.balance()));
//                                                  assert buyerMoney.obeys()  ==> (buyerMoney.balance()  == old(buyerMoney.balance()));
//                                                  assert buyerGoods.obeys()  ==> (buyerGoods.balance()  == old(buyerGoods.balance()));
//                                                  assert sellerGoods.obeys() ==> (sellerGoods.balance() == old(sellerGoods.balance()));
//
//                                                  assert sellerMoney.obeys() ==> (escrowMoney.balance() == 0);


//ROCK and ROLL!!l
                                                    // assert escrowMoney.obeys() ==> escrowMoney.canDepositFrom(0,buyerMoney);
  res := escrowMoney.deposit(price,buyerMoney);
  if (!res)  {
                                                    //  assert buyerMoney.obeys()  ==> (buyerMoney.balance()   == old(buyerMoney.balance()));
       return false;}


  res := escrowGoods.deposit(amount,sellerGoods);


                                                    //  assert buyerMoney.obeys()  ==> (buyerMoney.balance()  == old(buyerMoney.ba                            lance()) - price);
                                                    //  assert escrowMoney.obeys() ==> (escrowMoney.balance()  ==price);
                                                    //  if (res) {
                                                    //      assert sellerGoods.obeys() ==> (sellerGoods.balance()  == old(sellerGoods.balance()) - amount);
                                                    //      assert escrowGoods.obeys() ==> (escrowGoods.balance()  ==                              amount);
                                                    //   }

  if (!res)  {
                                                    //  assert buyerMoney.obeys()  ==> (buyerMoney.balance()  == old(buyerMoney.balance()) - price);
                                                    //  assert escrowMoney.obeys() ==> (escrowMoney.balance()  ==                            price);
                                                    //  //
                                                    //  assert buyerMoney != escrowMoney;
                                                    //  assert escrowMoney.obeys() ==> (escrowMoney.balance() >= price);
                                                    //  //assert escrowMoney.obeys() ==> ((escrowMoney as object) is GoodAccount);
                                                    //  assert escrowMoney.obeys() ==> buyerMoney.canTrade(escrowMoney);
                                                    //  assert escrowMoney.obeys() ==> buyerMoney.canDepositFrom(price,escrowMoney);
    var tmp1 := buyerMoney.deposit(price,escrowMoney);
                                                    //  assert (buyerMoney.obeys() && escrowMoney.obeys())  ==> (buyerMoney.balance()   == old(buyerMoney.balance())        );
                                                    //  assert escrowMoney.obeys() ==> (escrowMoney.balance()  ==                                 0);
    return false;}

  var tmp2 := sellerMoney.deposit(price,escrowMoney);
  var tmp3 := buyerGoods.deposit(amount,escrowGoods);

  assert res;

  return res;
}





















































































class OtherAccount extends Account {

  opaque ghost predicate obeys() : (r : bool) ensures r {true}
     //assumed instance-private

   var myBalance : nat


  constructor(initial : nat)  //assumed called only from the Bank
     ensures obeys()
     ensures obeys() ==> balance() == initial
     ensures fresh(this)
    {
      myBalance := initial;
      new;
      reveal obeys();
    }

  method sprout() returns (account : Account)
    ensures fresh(account) //THIS IS LESS THAN IDEAL INNI
    ensures obeys() ==> account.obeys()
    ensures balance() == old(balance())      ///WHOOPS HSOUDL HAEV OBEYS
    ensures account.balance() == 0           ///WHOOPS HSOUDL HAEV OBEYS
    ensures account.canDepositFrom(0, this)  ///WHOOPS HSOUDL HAEV OBEYS
    ensures this.canDepositFrom(0, account)  ///WHOOPS HSOUDL HAEV OBEYS
    ensures account is OtherAccount
    {
      account := new OtherAccount(0);
    }


  method {:isolate_assertions} deposit(amount : nat, from : Account) returns (b : bool)

    modifies this, from


     ensures (obeys() && b) ==> from.obeys()
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from)) ==> b)
     ensures (obeys() && b && old(canDepositFrom(amount, from))) ==> from.obeys()
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (    b  ==> (this.balance() == old(this.balance()) + amount))
     ensures (obeys() && from.obeys() && old(canDepositFrom(amount, from))) ==> (    b  ==> (from.balance() == old(from.balance()) - amount))
     ensures (obeys() && (not(from.obeys()) || not(old(canDepositFrom(0, from))))) ==> (not(b) ==> (this.balance() == old(this.balance())         ))   //>>?WTF
     ensures (obeys() && from.obeys() && old(canDepositFrom(0, from))) ==> (not(b) ==> (from.balance() == old(from.balance())         ))   //>>?WTF

     ensures ((obeys()                 && (amount == 0)) ==> (this.balance() == old(this.balance()) )) //KJX paranoia?
     ensures ((obeys() && from.obeys() && (amount == 0)) ==> (from.balance() == old(from.balance()) )) //KJX paranoia?

     ensures (obeys() && not(old(canDepositFrom(amount, from)))) ==> not(b)
     ensures ((obeys() && b) ==> canDepositFrom(0, from))

     ensures ((this == from)) ==> not(b)
     ensures ((from is OtherAccount) ==> from.obeys())

//versions without this.obeys()  (but it's there implicitly anyway)
    //  ensures (from.obeys() && old(canDepositFrom(amount, from)) ==> b)
    //  ensures (b && old(canDepositFrom(amount, from))) ==> from.obeys()
    //  ensures (from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (this.balance() == old(this.balance()) + amount))
    //  ensures (from.obeys() && old(canDepositFrom(amount, from))) ==> (b ==> (from.balance() == old(from.balance()) - amount))
    //  ensures (b ==> canDepositFrom(0, from))

{
  b := false;
  if (this == from) { assert not(canDepositFrom(amount, from));  return; }
  var oldBalance := balance();                     assert oldBalance == myBalance == balance();

  if not(from is OtherAccount)  { assert not(canDepositFrom(amount, from)); return; }

  var Other := (from as OtherAccount);
                                                   assert Other.obeys() by { reveal Other.obeys(); }
  if (Other.balance() < amount) { assert not(canDepositFrom(amount, from)); return; }
                                                   assert Other.myBalance >= amount;
  this.myBalance := this.myBalance + amount;
  Other.myBalance := Other.myBalance - amount;

  assert myBalance == oldBalance + amount;

  assert obeys();
  assert old(canDepositFrom(amount, from));
  b := true;
}


  function balance() : nat  reads this {myBalance}

  ghost predicate canTrade(from : Account) : (b : bool)
      decreases 0
     reads {}    {(this != from) && (from is OtherAccount)}

}






predicate not(x : bool) {!x}
