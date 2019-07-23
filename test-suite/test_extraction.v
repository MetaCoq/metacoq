(** Extraction setup for the safechecker phase of MetaCoq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import FSets.
(* Require Import ExtrOcamlString ExtrOcamlZInt. *)
From MetaCoq.Template Require Import All.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker PCUICSafeConversion.
From MetaCoq.Extraction Require Import ErasureFunction.


(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
(* Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)". *)

(* Extract Constant utils.ascii_compare => *)
(*  "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt". *)

Extraction Blacklist config uGraph universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Classes.
Set Warnings "-extraction-opaque-accessed".

Extraction Inline PCUICSafeConversion.Ret.

Quote Recursively Definition foo := (2 + 3)%nat.
Require Import Strings.String.
Definition string_of_env_error e : string :=
  match e with
  | IllFormedDecl e t =>
    "Ill-formed declaration of \'" ++ e ++ "\':" ++ string_of_type_error t
  | AlreadyDeclared id =>
    "Ill-formed environment: \'" ++ id ++ "\' is already declared"
  end.

Program
Definition erase_program (p : Ast.program) : String.string :=
  let Σ' := trans_global_decls p.1 in
  match check_wf_env (List.rev Σ') with
  | CorrectDecl (existT graph H) =>
    let p' := trans p.2 in
    match erase (empty_ext (List.rev Σ')) _ nil _ p' with
    | Checked eterm => "erasure succeeded"
    | TypeError e => string_of_type_error e
    end
  | EnvError e => string_of_env_error e
  end.

Next Obligation.
  destruct s. constructor.
  split. simpl. apply w.
  simpl. red. simpl.
  split. todo "constraints proof".
  todo "constraints proof".
Defined.
Next Obligation.
  destruct s. constructor. constructor.
Defined.

Definition erase_prog := erase_program foo.

(* Cd "src". *)

Extraction Language Scheme.
Extract Inductive Equations.Init.sigma => "(,)" ["(,)"].
Extract Constant PCUICTyping.fix_guard => "(lambda (x) `True)".
Extract Constant PCUICTyping.ind_guard => "(lambda (x) `True)".

Extract Constant check_one_ind_body => "(lambdas (_ _ _ _ _ _ _) `(@ret env_monad __))".
Extract Constant erase_mfix_obligation_1 => "(lambdas (_ _ _ _) (@ret typing_monad __))".
(*
import qualified Data.Bits
import qualified Data.Char
*)
Extraction "erase.scm" erase_prog.

(* Require Import ExtrHaskellBasic ExtrHaskellString. *)
(* Extraction Language Haskell. *)
(* Extract Inductive Equations.Init.sigma => "(,)" ["(,)"]. *)
(* Extract Constant PCUICTyping.fix_guard => "\ _ -> Prelude.True". *)
(* Extract Constant PCUICTyping.ind_guard => "\ _ -> Prelude.True". *)

(*


;; Because of fixed arity, we always use unary lambda
;; (lambdas (a b) c) ==> (lambda (a) (lambda (b) c))

(define-syntax lambdas
  (syntax-rules ()
    ((lambdas () c) c)
    ((lambdas (a b ...) c) (lambda (a) (lambdas (b ...) c)))))

;; Hence all applications should be unary: ((f x) y)
;; to remove some parenthesis, we introduce a macro: (@ f x y) = ((f x) y)

(define-syntax @
  (syntax-rules  ()
    ((@ f) (f))
    ((@ f x) (f x))
    ((@ f x . l) (@ (f x) . l))))

;; Bigloo provides a native pattern matching construct named
;; match-case. But its patterns use some ? that cannot easily
;; be emulated in other (r5rs) scheme implementations.
;; Hence we extract to a simplier syntax without ? and then
;; adapt it here to the bigloo style, using a lisp-like macro.
;; Example: predecessor should be written
;;    (define (pred n)
;;       (match n
;;          ((O) '(O))
;;          ((S n) n)))

(define-macro (match e . br)
  (let*
      ((add-?
        (lambda (id) (string->symbol (string-append "?" (symbol->string id)))))
       (fixbr (lambda (l) `((,(caar l) ,@(map add-? (cdar l))) ,@(cdr l)))))
    `(match-case ,e ,@(map fixbr br))))

;; The extracted code uses a unary error function

(define !error error)
(define (error m) (!error "" "" m))

;;;;;;;;; end of macros;;;;;;;



(define andb (lambda (x y) (match x
                                  ((`True) y)
                                  ((`False) `(False)))))
(define orb (lambda (x y) (match x
                                 ((`True) (`True))
                                 ((`False) y))))
*)
(* Extract Constant check_one_ind_body => "\_ _ _ _ _ _ _ -> CorrectDecl ()". *)
(* Extract Constant erase_mfix_obligation_1 => "\_ _ _ _ -> Checked ()". *)
(* (* *)
(* import qualified Data.Bits *)
(* import qualified Data.Char *)
(* *) *)
(* Extraction "erase.hs" erase_prog. *)

Cd "..".