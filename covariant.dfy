trait Bank extends object {
      opaque ghost predicate obeys() //not reading anything makes life easier

       const magic : nat
         var ledger : map<Account,nat>

    function demesne() : set<object>  reads this { {this}+ledger.Keys }  //mustn't call demesne on accounts
      //in general should be recursive. but dont' see how to set that up

   predicate valid()
       reads this,demesne()

   predicate validateAccount(a : Account) : (b : bool) reads `ledger
    function balanceOfAccount(a : Account) : nat reads `ledger  requires validateAccount(a)

   predicate canDepositIntoFromAccount(t : Account, n : nat, f : Account) : (b : bool)
         requires valid()
            reads this,demesne(),t,f
          ensures obeys() ==> b ==> (validateAccount(f))
          ensures obeys() ==> b ==> (validateAccount(t))
          ensures obeys() ==> b ==> (t.bank == f.bank  == this)
          ensures obeys() ==> b ==> (balanceOfAccount(f) >= n)
          ensures valid()

      method depositIntoFromAccount(t : Account, n : nat, f : Account) returns (b : bool)
         requires valid()
         modifies this,demesne()
         requires (validateAccount(f) && validateAccount(t))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f)) ==> b)
          ensures (t.obeys() && b && old(canDepositIntoFromAccount(t,n,f))) ==> f.obeys()
          ensures (t.obeys() ==> not(b) ==> unchanged(old(demesne())))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (validateAccount(t))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (validateAccount(f))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (b ==> (balanceOfAccount(t) == (old(balanceOfAccount(t)) + n)))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (b ==> (balanceOfAccount(f) == (old(balanceOfAccount(f)) - n)))
          ensures (t.obeys() ==> (forall a <- old(ledger) | (a !in {t, f}) :: a in ledger.Keys && ledger[a] == old(ledger[a])))
          ensures valid()
}

trait Account extends object {
         var bank : Bank   //const or var?   /start const, change to var??
         var magic : nat
    function demesne() : set<object> reads this,bank { {this}+bank.demesne() }
    opaque ghost predicate obeys() reads this,demesne() { bank.obeys() }
    predicate valid()
        reads this,demesne() {bank.validateAccount(this)}
}


///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////

class GoodBank extends Bank {
    constructor(n : nat)
       ensures goodBankValid()
    {
        magic := n;
        ledger := map[];
    }

    opaque ghost predicate obeys() {true}

    predicate goodBankValid()
       reads this, demesne()
    {
        forall a <- ledger.Keys :: (
             && (a.bank == this)
             && (a.magic == magic)
             && (a is GoodAccount)
            )
    }

    predicate valid() reads this,demesne() {goodBankValid()}

    method newGoodBankAccount() returns (a : Account)
      requires goodBankValid()
       ensures goodBankValid()
      modifies `ledger
     {
       var ga := new GoodAccount(this);

       ledger := ledger[ga:=0];
       a := ga;
     }

   predicate validateAccount(a : Account) reads `ledger  {a in ledger.Keys}
    function balanceOfAccount(a : Account) : nat reads `ledger  requires validateAccount(a) {ledger[a]}


   predicate canDepositIntoFromAccount(t : Account, n : nat, f : Account) : (b : bool)
      requires valid()
         reads this,demesne()
       ensures obeys() ==> b ==> (validateAccount(f))
       ensures obeys() ==> b ==> (validateAccount(t))
       ensures obeys() ==> b ==> (t.bank == f.bank  == this)
       ensures obeys() ==> b ==> (balanceOfAccount(f) >= n)
       ensures valid()
    {
              && (t != f)
              && (validateAccount(t))
              && (validateAccount(f))
              && (balanceOfAccount(f) >= n)
    }

   method depositIntoFromAccount(t : Account, n : nat, f : Account) returns (b : bool)
         requires valid()
         modifies this,demesne()
         requires (validateAccount(f) && validateAccount(t))

          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f)) ==> b)
          ensures (t.obeys() && b && old(canDepositIntoFromAccount(t,n,f))) ==> f.obeys()
          ensures (t.obeys() ==> not(b) ==> unchanged(old(demesne())))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (validateAccount(t))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (validateAccount(f))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (b ==> (balanceOfAccount(t) == (old(balanceOfAccount(t)) + n)))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (b ==> (balanceOfAccount(f) == (old(balanceOfAccount(f)) - n)))
          ensures (t.obeys() ==> (forall a <- old(ledger) | (a !in {t, f}) :: a in ledger.Keys && ledger[a] == old(ledger[a])))
          ensures valid()
      {
        reveal this.obeys(), f.obeys();  //really? yup/..
        assert valid();

        b := false;

        if (canDepositIntoFromAccount(t,n,f))
          {
              ledger := ledger[f:= ((ledger[f]) - n)][t:= ((ledger[t]) + n)];
              assert valid();
              assert goodBankValid();
              assert forall a <- ledger.Keys :: ((a.obeys()) && (a is GoodAccount));
              assert f in ledger.Keys;
              assert f is GoodAccount;
              assert this.obeys() by { reveal this.obeys(); }
              assert f.bank == this;
              assert f.obeys();
              b := true;
          }
      }
}

class GoodAccount extends Account {
    constructor(b : GoodBank)
      ensures bank == b
      ensures magic == b.magic
    {
        bank := b;
        magic := b.magic;
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////


class BadBank extends Bank {
    var pot : BadAccount?
    constructor(n : nat)
        ensures ledger == map[]
    {
        magic := n;
        ledger := map[];
        pot := null;
        new;
    }
    method init()
       requires ledger == map[]
        ensures badBankValid()
       modifies `pot, `ledger
     {
        pot := new BadAccount(this);
        assert pot != null;
        assert pot.bank == this;
        assert pot.magic == magic;
        ledger := map[pot:=0];

    }

    opaque ghost predicate obeys() {false}

    predicate valid() reads this,demesne() {badBankValid()}

    predicate badBankValid()
       reads this, demesne()
    {
       && (forall a <- ledger.Keys :: (a.bank == this) && (a.magic == magic) && (a is BadAccount))
       && ((pot != null))
       && ((pot in ledger.Keys))
    }

   predicate validateAccount(a : Account) reads `ledger  {true}
    function balanceOfAccount(a : Account) : nat reads `ledger
      requires validateAccount(a)  { if (a in ledger.Keys) then ledger[a] else 0 }


   predicate canDepositIntoFromAccount(t : Account, n : nat, f : Account) : (b : bool)
         requires valid()
            reads this,demesne()
          ensures obeys() ==> b ==> (validateAccount(f))
          ensures obeys() ==> b ==> (validateAccount(t))
          ensures obeys() ==> b ==> (t.bank == f.bank  == this)
          ensures obeys() ==> b ==> (balanceOfAccount(f) >= n)
          ensures valid()
            { reveal obeys();
                ({f,t} <= ledger.Keys)}  //was true

      method depositIntoFromAccount(t : Account, n : nat, f : Account) returns (b : bool)
         requires valid()
         modifies this,demesne()
         requires (validateAccount(f) && validateAccount(t))

          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f)) ==> b)
          ensures (t.obeys() && b && old(canDepositIntoFromAccount(t,n,f))) ==> f.obeys()
          ensures (t.obeys() ==> not(b) ==> unchanged(old(demesne())))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (validateAccount(t))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (validateAccount(f))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (b ==> (balanceOfAccount(t) == (old(balanceOfAccount(t)) + n)))
          ensures (t.obeys() && f.obeys() && old(canDepositIntoFromAccount(t,n,f))) ==> (b ==> (balanceOfAccount(f) == (old(balanceOfAccount(f)) - n)))
          ensures (t.obeys() ==> (forall a <- old(ledger) | (a !in {t, f}) :: a in ledger.Keys && ledger[a] == old(ledger[a])))
          ensures valid()
            {
            reveal f.obeys(), t.obeys(), this.obeys();
            b := false;

            if (not({f,t} <= ledger.Keys)) { return; }

                {
                 assert valid();
                 assert badBankValid();
                 assert forall a <- ledger.Keys :: ((a is BadAccount));
                 assert f.bank == this;
                 assert f.obeys() == f.bank.obeys() == false;
                 var s := ledger[f];
                 var p := ledger[pot];
                 ledger := ledger[f:=0][pot:=p+s];
                }

{
                 assert valid();
                 assert badBankValid();
                 assert forall a <- ledger.Keys :: ((a is BadAccount));
                 assert t.bank == this;
                 assert t.obeys() == this.obeys() == false;
                 var s := ledger[t];
                 var p := ledger[pot];
                 ledger := ledger[t:=0][pot:=p+s];
}



              assert valid();
              assert badBankValid();


              b := true;
              assert not(t.obeys());
              assert t.obeys() ==> f.obeys();
assert (t.obeys() && b && old(canDepositIntoFromAccount(t,n,f))) ==> f.obeys();

            }


}
class BadAccount extends Account {
    constructor(b : BadBank)
      ensures bank == b
      ensures magic == b.magic
    {
        bank := b;
        magic := b.magic;
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////

























































































predicate not(x : bool) {!x}