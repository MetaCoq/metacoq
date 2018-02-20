(* Reducing ITT terms *)

(* We're only reducing the decorations that are induced by translation, not the
   usual redexes. *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils LiftSubst Typing.
From Translation Require Import SAst SLiftSubst SCommon ITyping.

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
    let p' := reduce p in
    let t' := reduce t in
    match p' with
    | sRefl _ _ => t'
    | _ =>
      let T1' := reduce T1 in
      let T2' := reduce T2 in
      sTransport T1' T2' p' t'
    end
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
    match p' with
    | sRefl A a => sHeqRefl A a
    | _ =>
      let t' := reduce t in
      sHeqTransport p' t'
    end
  | sCongProd B1 B2 pA pB =>
    let pA' := reduce pA in
    let pB' := reduce pB in
    let B1' := reduce B1 in
    let B2' := reduce B2 in
    match pA', pB' with
    | sHeqRefl (sSort s) A', sHeqRefl (sSort z) _ =>
      (* We use nAnon here because we don't care! *)
      sHeqRefl (sSort (max_sort s z)) (sProd nAnon A' B1')
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
  end.


(* TODO: Show soundness/subject-reduction.

   There are several options.
   One of them is to show that t : A implies red t : red A.
   Another is to add all these equations to ITyping and then show
   t = red t. The wanted result will be derived from eq_typing.

 *)

Definition red_decl (d : scontext_decl) :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map reduce (sdecl_body d) ;
     sdecl_type := reduce (sdecl_type d)
  |}.

Fixpoint red (Γ : scontext) : scontext :=
  match Γ with
  | [] => []
  | a :: Γ => red_decl a :: red Γ
  end.

(* It seems this presentation is the wrong one. I believe now that these rules
   should be added to the conversion.
 *)
Lemma validity :
  forall {Σ t Γ A},
    Σ ;;; Γ |-i t : A ->
    Σ ;;; red Γ |-i reduce t : reduce A.
Proof.
  intros Σ t Γ A ht.
  induction ht.
  - cbn. admit.
  - cbn. eapply type_Sort. admit.
  - cbn. eapply type_Prod.
    + apply IHht1.
    + apply IHht2.
  - cbn. eapply type_Lambda.
    + apply IHht1.
    + apply IHht2.
    + apply IHht3.
  - cbn. admit.
  - cbn. eapply type_Eq ; assumption.
  - cbn. eapply type_Refl ; eassumption.
  - cbn. admit.
  - cbn. destruct (reduce p).
    all: try (eapply type_Transport ; eassumption).
    destruct (inversionRefl IHht3) as [s' [[? ?] h]].
    cbn in h.
    (* This probably requires injectivity of Eq. *)
    admit.
  - cbn. eapply type_Heq ; eassumption.
  - cbn. destruct (reduce p).
    all: try (eapply type_HeqToEq ; eassumption).
    (* pose (inversionHeqRefl IHht1). *)
    (* I would also need inversion of HeqRefl, and then some injectivity... *)
    admit.
  - cbn. eapply type_HeqRefl ; eassumption.
  - cbn. destruct (reduce p).
    all: try (eapply type_HeqSym ; eassumption).
    cbn in IHht5.
    (* Same kind of troubles *)
    admit.
Abort.