Require Import Coq.Lists.List.
From Template Require Import
     Ast
     Loader
     TemplateMonad.Extractable.
Import TemplateMonad.Extractable.
Require Import Template.BasicAst Template.AstUtils Ast.


Let TemplateMonad := TM.
Fixpoint mconcat (ls : list (TemplateMonad unit)) : TemplateMonad unit :=
  match ls with
  | nil => tmReturn tt
  | m :: ms => tmBind m (fun _ => mconcat ms)
  end.

Fixpoint print_all_kns (t : Ast.term) : TM unit :=
  match t with
  | tEvar _ ls =>
    mconcat (List.map print_all_kns ls)
  | tCast a _ b
  | tProd _ a b
  | tLambda _ a b =>
    tmBind (print_all_kns a) (fun _ => print_all_kns b)
  | tApp a b =>
    tmBind (print_all_kns a) (fun _ => mconcat (List.map print_all_kns b))
  | tLetIn _ a b c =>
    tmBind (print_all_kns a) (fun _ => tmBind (print_all_kns b) (fun _ => print_all_kns c))
  | tConst c _ => tmMsg c
  | tInd i _ => tmMsg i.(inductive_mind)
  | tConstruct i _ _ => tmMsg i.(inductive_mind)
  | tProj (i,_,_) b =>
    tmBind (tmMsg i.(inductive_mind)) (fun _ => print_all_kns b)
  | _ => tmReturn tt
  end.

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).


Definition gr_to_kername (gr : global_reference) : kername :=
  match gr with
  | ConstRef kn => kn
  | IndRef ind => ind.(inductive_mind)
  | ConstructRef ind _ => ind.(inductive_mind)
  end.

Definition tmResolve (nm : String.string) : TM (option kername) :=
  tmBind (tmAbout nm)
         (fun gr =>
            match gr with
            | None => tmReturn None
            | Some (ConstRef kn) => tmReturn (Some kn)
            | Some (IndRef ind) => tmReturn (Some ind.(inductive_mind))
            | Some (ConstructRef ind _) => tmReturn (Some ind.(inductive_mind))
            end).


(* ^^ Everything above here is generic *)

Require Import Lens.Lens.


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

Definition cBuild_Lens := <% Build_Lens %>.

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

(* baseName should not contain any paths. For example, if the full name
is A.B.C#D#E#F, baseName should be F. Also, by import ordering,
ensure that F resolves to  A.B.C#D#E#F. Use Locate to check this.

If the definition of F refers to any other inductive, they should not
be in the current section(s).
 *)

Definition opBind {A B} (a: option A) (f: A -> option B) : option B :=
  match a with
  | Some a => f a
  | None  => None
  end.

Definition genLensN (baseName : String.string) : TM unit :=
  tmBind (tmAbout baseName) (fun gr =>
    match gr with
    | Some (IndRef kn) =>
      let name := kn.(inductive_mind) in
      let ty := Ast.tInd
        {| BasicAst.inductive_mind := name
         ; BasicAst.inductive_ind := 0 (* TODO: fix for mutual records *) |} List.nil in
      tmBind (tmQuoteInductive name) (fun ind =>
          match getFields ind with
          | Some info =>
            let gen i :=
                match mkLens ty info.(fields) i return TemplateMonad unit with
                | None => tmFail "failed to build lens"
                | Some x =>
                  tmBind (tmEval Common.cbv (snd x)) (fun d =>
                  tmBind (tmDefinition (fst x) None d) (fun _ =>
                  tmReturn tt))
                end
            in
            mconcat (map gen (countTo (List.length info.(fields))))
          | None => tmFail ("failed to get inductive info but quote succeeded")
          end)
    | _ => tmFail "not an inductive"
    end).


Definition tmQuoteConstantR (nm : String.string) (bypass : bool) : TM _ :=
  tmBind (tmAbout nm)
         (fun gr =>
            match gr with
            | Some (ConstRef kn) =>
              tmBind (tmQuoteConstant kn bypass)
                     (fun x => tmReturn (Some x))
            | _ => tmReturn None
            end).

Definition lookupPrint (baseName : String.string) : TM unit :=
  tmBind (tmQuoteConstantR baseName true)
         (fun b =>
            match b with
            | None => tmFail "not a constant"
            | Some b =>
              match b with
              | ParameterEntry _ => tmReturn tt
              | DefinitionEntry d =>
                tmPrint (definition_entry_body d)
              end
            end).

Definition x := <% 0 %>.

Definition lookup (baseName : String.string) : TM unit :=
  tmBind (tmQuoteConstant baseName true)
         (fun b => tmReturn tt).

Definition genLensNInst  : TM unit := genLensN "Point".


Definition showoffOld : TM unit :=
  tmBind (tmMsg "showing off tmDefn" )
         (fun _ =>
            tmBind (tmDefinition "zeroE" None x)
                   (fun _ => tmReturn tt)).

Definition showoff : TM unit := genLensNInst.
