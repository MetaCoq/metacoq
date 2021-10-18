

1) Define cumul mutually with typing as:

   Σ ; Γ ⊢ t, u : T    Σ ; Γ ⊢ t ≤[true] u
   ---------------------------------------
    Σ ; Γ ⊢ t ≤ u : T

   Σ ; Γ ⊢ t, u, v : T    Σ ; Γ ⊢ t ⇝ u   Σ ; Γ ⊢ u ≤ v : T
   ---------------------------------------------------------
    Σ ; Γ ⊢ t ≤ v : T

   Σ ; Γ ⊢ t, u, v : T    Σ ; Γ ⊢ v ⇝ u   Σ ; Γ ⊢ t ≤ u : T
   ---------------------------------------------------------
    Σ ; Γ ⊢ t ≤ v : T

2) To prove SR for this system we need:

    Σ ; Γ ⊢ Π A B ≤ Π A' B' : s
    ----------------------------
    Σ ; Γ ⊢ A = A' : s1 /\ Σ ; Γ ⊢ B ≤ B' : s2

    Relying on confluence for red.

    So show:
    Σ ; Γ ⊢ t ≤ u : T ->
    ∑ t' u', Σ ; Γ ⊢ t ⇝ t' : T × Γ ⊢ u ⇝ u' : T × Σ ; Γ ⊢ t' ≤[true] u'. (easy)

    and transitivity:
    Σ ; Γ ⊢ t ≤ u : T -> Σ ; Γ ⊢ u ≤ v : T -> Σ ; Γ ⊢ t ≤ v : T

    ∑ t' u', Σ ; Γ ⊢ t ⇝ t' : T × Γ ⊢ u ⇝ u' : T × Σ ; Γ ⊢ t' ≤[true] u'.
    ∑ u'' v', Σ ; Γ ⊢ u ⇝ u'' : T × Γ ⊢ v ⇝ v' : T × Σ ; Γ ⊢ u'' ≤[true] v'. 
    => 
    ∑ t' v', Σ ; Γ ⊢ t ⇝ t' : T × Γ ⊢ v ⇝ v' : T × Σ ; Γ ⊢ t' ≤[true] v'.

    Need confluence of typed reduction: 

    Σ ; Γ ⊢ t ⇝ t' : T × Γ ⊢ t ⇝ t'' : T =>
    ∑ nf, Σ ; Γ ⊢ t' ⇝ nf : T × Γ ⊢ t'' ⇝ nf : T.

    This is the hard part, as we need to show that rho preserves typing:

    Σ ; Γ |- t : T ->
    Σ ; Γ |- t ⇝ rho Γ t : T.

    By induction on typing. 
    


    



 Show Σ ; Γ ⊢ t ≤ u : T -> Σ ; Γ ⊢ t ≤ u (easy)

2) Show Σ ; Γ |- t, u : T and Σ ; Γ ⊢ t ≤ u implies Σ ; Γ ⊢ t ≤ u : T.
