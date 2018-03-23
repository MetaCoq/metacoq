(* Reducing ITT terms *)

(* We're only reducing the decorations that are induced by translation, not the
   usual redexes. *)

From Coq Require Import Bool String List BinPos Compare_dec Omega Bool_nat.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils LiftSubst Typing.
From Translation Require Import SAst SInduction SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingMore.

Definition proj_1 {A} {P : A -> Prop} : {a:A | P a} -> A :=
  fun X => match X with exist _ a _ => a end.

Fixpoint sterm_eq (t u : sterm) : bool :=
  match t, u with
  | sRel n, sRel m =>
      proj_1 (nat_eq_bool n m)
  | sSort s, sSort s' =>
      proj_1 (nat_eq_bool s s')
  | sProd n A B, sProd n' A' B' =>
      sterm_eq A A' && sterm_eq B B'
  | sLambda nx A B t, sLambda nx' A' B' t' =>
      sterm_eq A A' && sterm_eq B B' && sterm_eq t t'
  | sApp u n A B v,  sApp u' n' A' B' v' =>
      sterm_eq A A' && sterm_eq B B' && sterm_eq u u' && sterm_eq v v'
  | sEq A u v,  sEq A' u' v' =>
      sterm_eq A A' && sterm_eq u u' && sterm_eq v v'
  | sRefl A u, sRefl A' u' =>
      sterm_eq A A' && sterm_eq u u'
  | sJ A u P w v p, sJ A' u' P' w' v' p' =>
      sterm_eq A A' && sterm_eq u u' && sterm_eq P P' &&
      sterm_eq v v' && sterm_eq w w' && sterm_eq p p'
  | sTransport T1 T2 p t, sTransport T1' T2' p' t' =>
      sterm_eq T1 T1' && sterm_eq T2 T2' && sterm_eq p p' && sterm_eq t t'
  | sHeq A a B b, sHeq A' a' B' b' =>
      sterm_eq A A' && sterm_eq B B' && sterm_eq a a' && sterm_eq b b'
  | sHeqToEq p, sHeqToEq p' =>
      sterm_eq p p'
  | sHeqRefl A a, sHeqRefl A' a' =>
      sterm_eq A A' && sterm_eq a a'
  | sHeqSym p, sHeqSym p' =>
      sterm_eq p p'
  | sHeqTrans p q, sHeqTrans p' q' =>
      sterm_eq p p' && sterm_eq q q'
  | sHeqTransport p t, sHeqTransport p' t' =>
      sterm_eq p p' && sterm_eq t t'
  | sCongProd B1 B2 pA pB, sCongProd B1' B2' pA' pB' =>
      sterm_eq B1 B1' && sterm_eq B2 B2' && sterm_eq pA pA' && sterm_eq pB pB'
  | sCongLambda B1 B2 t1 t2 pA pB pt, sCongLambda B1' B2' t1' t2' pA' pB' pt' =>
      sterm_eq B1 B1' && sterm_eq B2 B2' && sterm_eq t1 t1' && sterm_eq t2 t2' &&
      sterm_eq pA pA' && sterm_eq pB pB && sterm_eq pt pt'
  | sCongApp B1 B2 pu pA pB pv , sCongApp B1' B2' pu' pA' pB' pv'=>
      sterm_eq B1 B1' && sterm_eq B2 B2' && sterm_eq pA pA' && sterm_eq pB pB &&
      sterm_eq pu pu' && sterm_eq pv pv'
  | sCongEq pA pu pv, sCongEq pA' pu' pv' =>
      sterm_eq pA pA' && sterm_eq pu pu' && sterm_eq pv pv'
  | sCongRefl pA pu, sCongRefl pA' pu' =>
      sterm_eq pA pA' && sterm_eq pu pu'
  | sEqToHeq p, sEqToHeq p' =>
      sterm_eq p p'
  | sHeqTypeEq p, sHeqTypeEq p' =>
      sterm_eq p p'
  | sPack A1 A2, sPack A1' A2' =>
      sterm_eq A1 A1' && sterm_eq A2 A2'
  | sProjT1 p, sProjT1 p' =>
      sterm_eq p p'
  | sProjT2 p, sProjT2 p' =>
      sterm_eq p p'
  | sProjTe p, sProjTe p' =>
      sterm_eq p p'
  | sInd i, sInd i' =>
      eq_ind i i'
  | sConstruct i k, sConstruct i' k' =>
      eq_ind i i' && eq_nat k k'
  | _ , _ => false
  end.


Fixpoint reduce (t : sterm) : sterm :=
  match t with
  | sRel n => sRel n
  | sSort s => sSort s
  | sProd n A B =>
    let A' := reduce A in
    let B' := reduce B in
    sProd n A' B'
  | sLambda nx A B t =>
    let A' := reduce A in
    let B' := reduce B in
    let t' := reduce t in
    sLambda nx A' B' t'
  | sApp u n A B v =>
    let u' := reduce u in
    let A' := reduce A in
    let B' := reduce B in
    let v' := reduce v in
    sApp u' n A' B' v'
  | sEq A u v =>
    let A' := reduce A in
    let u' := reduce u in
    let v' := reduce v in
    sEq A' u' v'
  | sRefl A u =>
    let A' := reduce A in
    let u' := reduce u in
    sRefl A' u'
  | sJ A u P w v p =>
    let A' := reduce A in
    let u' := reduce u in
    let P' := reduce P in
    let w' := reduce w in
    let v' := reduce v in
    let p' := reduce p in
    sJ A' u' P' w' v' p'
  | sTransport T1 T2 p t =>
    let T1' := reduce T1 in
    let T2' := reduce T2 in
    let p' := reduce p in
    let t' := reduce t in
    if sterm_eq T1' T2' then t' else sTransport T1' T2' p' t'
    (*    match p' with *)
    (* | sRefl _ _ => t' *)
    (* | _ => *)
    (*   let T1' := reduce T1 in *)
    (*   let T2' := reduce T2 in *)
    (*   sTransport T1' T2' p' t' *)
    (* end *)
  | sHeq A a B b =>
    let A' := reduce A in
    let a' := reduce a in
    let B' := reduce B in
    let b' := reduce b in
    sHeq A' a' B' b'
  | sHeqToEq p =>
    let p' := reduce p in
    match p' with
    | sHeqRefl A a => sRefl A a
    | sEqToHeq a => a
    | _ => sHeqToEq p'
    end
  | sHeqRefl A a =>
    let A' := reduce A in
    let a' := reduce a in
    sHeqRefl A' a'
  | sHeqSym p =>
    let p' := reduce p in
    match p' with
    | sHeqRefl A a => sHeqRefl A a
    | _ => sHeqSym p'
    end
  | sHeqTrans p q =>
    let p' := reduce p in
    let q' := reduce q in
    match p' with
    | sHeqRefl A a =>
      match q' with
      | sHeqRefl _ _ => sHeqRefl A a
      | _ => q'
      end
    | _ =>
      match q' with
      | sHeqRefl _ _ => p'
      | _ => sHeqTrans p' q'
      end
    end
  | sHeqTransport p t =>
    let p' := reduce p in
    let t' := reduce t in
    match p' with
    (* bad version of Théo !! *)
    (* | sRefl A a => sHeqRefl A a *)
    | sRefl s A => sHeqRefl A t'
    | _ =>
      sHeqTransport p' t'
    end
  | sCongProd B1 B2 pA pB =>
    let pA' := reduce pA in
    let pB' := reduce pB in
    let B1' := reduce B1 in
    let B2' := reduce B2 in
    match pA', pB' with
    | sHeqRefl (sSort s) A', sHeqRefl (sSort z) B' =>
      (* We use nAnon here because we don't care! *)
      sHeqRefl (sSort (max_sort s z)) (sProd nAnon A' B')
    | _,_ => sCongProd B1' B2' pA' pB'
    end
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    let pA' := reduce pA in
    let pB' := reduce pB in
    let pt' := reduce pt in
    let B1' := reduce B1 in
    let B2' := reduce B2 in
    let t1' := reduce t1 in
    let t2' := reduce t2 in
    match pA', pB', pt' with
    | sHeqRefl _ A', sHeqRefl _ _, sHeqRefl _ _ =>
      sHeqRefl (sProd nAnon A' B1') (sLambda nAnon A' B1' t1')
    | _,_,_ => sCongLambda B1' B2' t1' t2' pA' pB' pt'
    end
  | sCongApp B1 B2 pu pA pB pv =>
    let pA' := reduce pA in
    let pB' := reduce pB in
    let pu' := reduce pu in
    let pv' := reduce pv in
    let B1' := reduce B1 in
    let B2' := reduce B2 in
    match pA', pB', pu', pv' with
    | sHeqRefl _ A', sHeqRefl _ _, sHeqRefl _ u', sHeqRefl _ v' =>
      sHeqRefl (B1'{ 0 := v' }) (sApp u' nAnon A' B1' v')
    | _,_,_,_ => sCongApp B1' B2' pu' pA' pB' pv'
    end
  | sCongEq pA pu pv =>
    let pA' := reduce pA in
    let pu' := reduce pu in
    let pv' := reduce pv in
    match pA', pu', pv' with
    | sHeqRefl S' A', sHeqRefl _ u', sHeqRefl _ v' =>
      sHeqRefl S' (sEq A' u' v')
    | _,_,_ => sCongEq pA' pu' pv'
    end
  | sCongRefl pA pu =>
    let pA' := reduce pA in
    let pu' := reduce pu in
    match pA', pu' with
    | sHeqRefl _ A', sHeqRefl _ u' =>
      sHeqRefl (sEq A' u' u') (sRefl A' u')
    | _,_ => sCongRefl pA' pu'
    end
  | sEqToHeq p =>
    let p' := reduce p in
    match p' with
    | sRefl A' x' => sHeqRefl A' x'
    | _ => sEqToHeq p'
    end
  | sHeqTypeEq p =>
    let p' := reduce p in
    (* Not enough annotation. *)
    (* match p' with *)
    (* | sHeqRefl A' x' => sHeqRefl A' x' *)
    (* | _ => sHeqTypeEq p' *)
    (* end *)
    sHeqTypeEq p'
  | sPack A1 A2 =>
    let A1' := reduce A1 in
    let A2' := reduce A2 in
    sPack A1' A2'
  | sProjT1 p =>
    let p' := reduce p in
    sProjT1 p'
  | sProjT2 p =>
    let p' := reduce p in
    sProjT2 p'
  | sProjTe p =>
    let p' := reduce p in
    sProjTe p'
  | sInd ind => sInd ind
  | sConstruct ind i => sConstruct ind i
  | sCase indn p c brs =>
    let p' := reduce p in
    let c' := reduce c in
    let brs' := map (on_snd reduce) brs in
    sCase indn p' c' brs'
  end.
