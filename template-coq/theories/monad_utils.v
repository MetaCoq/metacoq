(* todo(gmm): This file should really be replaced by a real
 * monad library.
 *)
Require Import List.
From MetaCoq.Template Require Import All_Forall.

Import ListNotations.

Set Universe Polymorphism.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Class MonadExc E (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.


Module MonadNotation.
  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

  Notation "'mlet' x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.

  Notation "'mlet' ' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.
End MonadNotation.

Import MonadNotation.

Instance option_monad : Monad option :=
  {| ret A a := Some a ;
     bind A B m f :=
       match m with
       | Some a => f a
       | None => None
       end
  |}.

Open Scope monad.

Section MapOpt.
  Context {A} (f : A -> option A).

  Fixpoint mapopt (l : list A) : option (list A) :=
    match l with
    | nil => ret nil
    | x :: xs => x' <- f x ;;
                xs' <- mapopt xs ;;
                ret (x' :: xs')
    end.
End MapOpt.

Section MonadOperations.
  Context {T} {M : Monad T}.
  Context {A B} (f : A -> T B).
  Fixpoint monad_map (l : list A)
    : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- f x ;;
                  l' <- monad_map l ;;
                  ret (x' :: l')
       end.

  Context (g : A -> B -> T A).
  Fixpoint monad_fold_left (l : list B) (x : A) : T A
    := match l with
       | nil => ret x
       | y :: l => x' <- g x y ;;
                   monad_fold_left l x'
       end.
  
  Fixpoint monad_fold_right (l : list B) (x : A) : T A
       := match l with
          | nil => ret x
          | y :: l => l' <- monad_fold_right l x ;;
                      g l' y
          end.
   
  Context (h : nat -> A -> T B).
  Fixpoint monad_map_i_aux (n0 : nat) (l : list A) : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- (h n0 x) ;;
                   l' <- (monad_map_i_aux (S n0) l) ;;
                   ret (x' :: l')
       end.

  Definition monad_map_i := @monad_map_i_aux 0.
End MonadOperations.


Definition monad_iter {T : Type -> Type} {M A} (f : A -> T unit) (l : list A) : T unit
  := @monad_fold_left T M _ _ (fun _ => f) l tt.

Fixpoint monad_All {T} {M : Monad T} {A} {P} (f : forall x, T (P x)) l : T (@All A P l) := match l with
   | [] => ret All_nil
   | a :: l => X <- f a ;;
              Y <- monad_All f l ;;
              ret (All_cons X Y)
   end.

Fixpoint monad_All2 {T E} {M : Monad T} {M' : MonadExc E T} wrong_sizes
  {A B R} (f : forall x y, T (R x y)) l1 l2 : T (@All2 A B R l1 l2) := 
  match l1, l2 with
   | [], [] => ret All2_nil
   | a :: l1, b :: l2 => X <- f a b ;;
                        Y <- monad_All2 wrong_sizes f l1 l2 ;;
                        ret (All2_cons X Y)
   | _, _ => raise wrong_sizes
   end.

Definition monad_prod {T} {M : Monad T} {A B} (x : T A) (y : T B): T (A * B)%type
  := X <- x ;; Y <- y ;; ret (X, Y).
 

