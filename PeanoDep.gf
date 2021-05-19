abstract PeanoDep = {

  cat
    S SCat ;
    SCat ;
    Nat ;
    Eq Nat Nat ;

  data
    Zero : Nat ;
    Suc : Nat -> Nat ;
    -- Plus : Nat -> Nat -> Nat ;

    -- training wheels: define Refl
    Refl : (n : Nat) -> Eq n n ;

    -- PeanoDep> gr -cat="Eq Zero Zero"
    -- Refl Zero

    -- Can't use Type in abstract syntax, so we need to do this inconvenient hack
    scNat : SCat;
    scEq : SCat ;

    nS : Nat -> S scNat ;
    eS : (m,n : Nat) -> Eq m n -> S scEq ;


    fun one, two, three : Nat ;
  def
    one = Suc Zero ;
    two = Suc (Suc Zero) ;
    three = Suc (Suc (Suc Zero)) ;

  fun
    unNS : S scNat -> Nat ;
  def
    unNS (nS x) = x ;
  fun
    natrec : (X : SCat) -> (Nat -> S X -> S X) -> S X -> Nat -> S X ;
   def
     natrec T f y Zero = y ;
     natrec T f y (Suc n) = f n (natrec T f y n) ;

  fun
    double : Nat -> Nat ;
  def
    double n = unNS (natrec scNat (\ x, y -> nS (Suc (Suc (unNS y)))) (nS Zero) n) ;

    -- This works in GF shell:
    -- PeanoDep> pt -compute double three
    -- Suc (Suc (Suc (Suc (Suc (Suc Zero)))))

  fun
    Plus : Nat -> Nat -> Nat ;
  def
    Plus Zero m = m ;
    Plus (Suc n) m = Suc (Plus n m) ;


  -----------------------
  -- Anka's WIP

  -- TODO:
  -- natind : (C : Nat -> Type) -> C Zero -> ((n : Nat) -> C n -> C (Suc n)) -> (n : Nat) -> C n ;

  fun
    zeroLeft : (p : Nat) -> Eq (Plus Zero p) p ;
    plusSuc : (n, m : Nat) -> Eq (Plus (Suc n) m) (Suc (Plus n m));

  fun
    ap : (a , b : Nat) -> (f : Nat -> Nat) -> Eq a b -> Eq (f a) (f b) ;
    trans : (a , b , c : Nat) -> Eq a b -> Eq b c -> Eq a c ;
  -- def
  --   ap a b f Refl = Refl ;
  fun
    zeroRight : (p : Nat) -> Eq (Plus p Zero) p ;
  def
    zeroRight (Suc n) = trans (Plus (Suc n) Zero) (Suc (Plus n Zero)) (Suc n) (plusSuc n Zero) (ap (Plus n Zero) n (Suc) (zeroRight n)) ;
    zeroRight Zero = zeroLeft Zero ;

  -- TODO: Define subst (and possibly J-rule)

}
