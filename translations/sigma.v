Set Primitive Projections.

Record sigma A B :=
  mk_sig { π1 : A ; π2 : B π1 }.

Arguments π1 {A B} _.
Arguments π2 {A B} _.
Arguments mk_sig {A B} _ _.

Notation "{ t : A & P }" := (sigma A (fun t => P)) : type_scope.
Notation "( x ; y )" := (mk_sig x y) : sigma_scope.
Notation "x .1" := (π1 x) (at level 3, format "x '.1'") : sigma_scope.
Notation "x .2" := (π2 x) (at level 3, format "x '.2'") : sigma_scope.
Notation "'exists' x .. y , p" := (sigma _ (fun x => .. (sigma _ (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
                                  : type_scope.

Notation " A × B " := (sigma A (fun _ => B)) (at level 30) : type_scope.
