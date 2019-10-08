From MetaCoq Require Import Template.Ast Template.Loader.
Require Import List String. Import ListNotations.

Set Primitive Projections.

Record sigma A B :=
  mk_sig { π1 : A ; π2 : B π1 }.

Arguments π1 {A B} _.
Arguments π2 {A B} _.
Arguments mk_sig {A B} _ _.

Notation "{ x  &&  P }" := (sigma (fun x => P)) : type_scope.
Notation "{ t : A && P }" := (sigma A (fun t => P)) : type_scope.
Notation "( x ; y )" := (mk_sig x y) : sigma_scope.
Notation "x .1" := (π1 x) (at level 2, left associativity, format "x .1") : sigma_scope.
Notation "x .2" := (π2 x) (at level 2, left associativity, format "x .2") : sigma_scope.
Notation "'∃' x .. y , p" := (sigma _ (fun x => .. (sigma _ (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∃'  '/  ' x  ..  y ,  '/  ' p ']'")
                                  : type_scope.

Notation " A × B " := (sigma A (fun _ => B)) (at level 80, right associativity) : type_scope.


MetaCoq Quote Definition tSigma := sigma.
MetaCoq Quote Definition tPair := @mk_sig.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].
Definition sigma_ind := Eval compute in match tSigma with tInd i _ => i | _ =>  mkInd "bug: sigma not an inductive"%string 0 end.
Definition proj1 (t : term) : term
  := tProj (sigma_ind, 2, 0) t.
Definition proj2 (t : term) : term
  := tProj (sigma_ind, 2, 1) t.
Definition proj (b : bool) (t : term) : term
  := tProj (sigma_ind, 2, if b then 0 else 1) t.
