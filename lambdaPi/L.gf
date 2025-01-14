abstract L = {

flags startcat = Exp ;

cat
  Exp ;
  Var ;
  -- Decl ; --Ext
  Tele ;
  [Var]{0} ;
  [Tele]{0} ;

fun
  -- previously types
  Earr : Exp -> Exp -> Exp ;
  Epi : [Tele] -> Exp -> Exp ;
  Eid : Exp -> Exp -> Exp -> Exp ;
  Eid2 : Exp -> Exp -> Exp ;
  Enat : Exp ;
  Euni : Exp ;

  Evar : Var -> Exp ;
  Elam : [Tele] -> Exp -> Exp ;
  Eapp : Exp -> Exp -> Exp ;

  Erefl : Exp ;
  -- Eidind : Exp -> Exp -> Exp -> Exp -> Exp -> Exp ;

  Ezer : Exp ;
  Esuc : Exp -> Exp ;
  Enatind : Exp -> Exp -> Exp -> Exp -> Exp ;

  F : Var ;
  G : Var ;
  N : Var ;
  X : Var ;
  Y : Var ;
  Z : Var ;
  Und : Var ;
  IntV : Int -> Var ;

  TeleC : Var -> [Var] -> Exp -> Tele ;
  -- TeleC : Exp -> Exp -> Tele ; -- ( x : Set ) -- ( y : x -> Set )" -- ( x : f y z )"

  -- DtypDef : Decl -> Decl -> Decl ;
  -- Dtyp : Var -> Typ -> Decl ;
  -- Ddef : Var -> Exp -> Decl ;

  Double : Var ;
  Plus : Var ;
  Times : Var ;
  Assoc : Var ;
  Ap : Var ;

}
