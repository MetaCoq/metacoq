From Template Require Import
     Ast
     Loader
     TemplateMonad.Extractable.


Definition showoff : TM unit :=
  tmMsg "running from an extracted plugin!".


Require Import ExtLib.Structures.Functor.

Set Primitive Projections.

Record Lens (a b c d : Type) : Type :=
{ view : a -> c
; over : (c -> d) -> a -> b
}.

Arguments over {_ _ _ _} _ _ _.
Arguments view {_ _ _ _} _ _.

Definition lens_compose {a b c d e f : Type}
           (l1 : Lens a b c d) (l2 : Lens c d e f)
: Lens a b e f :=
{| view := fun x : a => view l2 (view l1 x)
 ; over := fun f0 : e -> f => over l1 (over l2 f0) |}.

Infix "∙" := lens_compose (at level 90, left associativity).

Section ops.
  Context {a b c d : Type} (l : Lens a b c d).

  Definition set (new : d) : a -> b :=
    l.(over) (fun _ => new).
End ops.


Set Primitive Projections.
Set Universe Polymorphism.

Record Info : Set :=
{ type : ident
; ctor : ident
; fields : list (ident * term)
}.

Fixpoint countTo (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => countTo m ++ (m :: nil)
  end.

Require Import String.
Open Scope string_scope.
Definition prepend (ls : string) (i : ident) : ident :=
  ls ++ i.

Quote Definition cBuild_Lens := Build_Lens.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.


(* check to see if Var 0 is referenced in any of the terms *)
Definition mentions (v : nat) (ls : list (ident * term)) : bool :=
  false.


Definition mkLens (At : term) (fields : list (ident * term)) (i : nat)
: option (ident * term) :=
  match At with
  | tInd ind args =>
    let ctor := tConstruct ind 0 args in
    match nth_error fields i with
    | None => None
    | Some (name, Bt) =>
      if mentions 1 (skipn (S i) fields)
      then None
      else
        let p (x : nat) : projection := (ind, 0, x) in
        let get_body := tProj (p i) (tRel 0) in
        let f x :=
            let this := tProj (p x) (tRel 0) in
            if PeanoNat.Nat.eqb x i
            then tApp (tRel 1) (this :: nil)
            else this
        in
        let update_body :=
            tApp ctor (map f (countTo (List.length fields)))
        in
        Some ( prepend "_" name
             , tApp cBuild_Lens
                    (At :: At :: Bt :: Bt ::
                        tLambda nAnon At get_body ::
                        tLambda nAnon (tProd nAnon Bt Bt) (tLambda nAnon At update_body) ::
                        nil))
    end
  | _ => None
  end.

Definition getFields (mi : mutual_inductive_body)
: option Info :=
  match mi.(ind_bodies) with
  | oib :: nil =>
    match oib.(ind_ctors) with
    | ctor :: nil =>
      Some {| type := oib.(ind_name)
            ; ctor := let '(x,_,_) := ctor in x
            ; fields := oib.(ind_projs)
           |}
    | _ => None
    end
  | _ => None
  end.

Import TemplateMonad.Extractable.
Require Import Template.BasicAst Template.AstUtils Ast.
Let TemplateMonad := TM.
Fixpoint mconcat (ls : list (TemplateMonad unit)) : TemplateMonad unit :=
  match ls with
  | nil => tmReturn tt
  | m :: ms => tmBind m (fun _ => mconcat ms)
  end.


(* baseName should not contain any paths. For example, if the full name
is A.B.C#D#E#F, baseName should be F. Also, by import ordering,
ensure that F resolves to  A.B.C#D#E#F. Use Locate to check this.

If the definition of F refers to any other inductive, they should not
be in the current section(s).
 *)

Definition genLensN (baseName : String.string) : TM unit :=
  let name := baseName in
  let ty :=
      (Ast.tInd
   {|
   BasicAst.inductive_mind := name;
   BasicAst.inductive_ind := 0 (* TODO: fix for mutual records *) |} List.nil) in
   tmBind (tmQuoteInductive name) (fun ind =>
    match getFields ind with
    | Some info =>
      let gen i :=
          match mkLens ty info.(fields) i return TemplateMonad unit with
          | None => tmFail "failed to build lens"
          | Some x =>
            tmBind (tmEval Common.cbv (snd x))
                   (fun d =>
                      tmBind
                        (tmDefinition (fst x) None d)
                                     (fun _ => tmReturn tt))
          end
      in
      mconcat (map gen (countTo (List.length info.(fields))))
    | None => tmFail "failed to get info"
    end).

Definition genLensNInst  : TM unit := genLensN "Point".
