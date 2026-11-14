/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Interpretation

/-!
# Composition of first-order reductions (transitivity)

The composite of two FO interpretations is an FO interpretation
(`DescriptiveComplexity.FOInterpretation.comp`), and hence FO reducibility is transitive
(`DescriptiveComplexity.FOReduction.trans`): from `P ≤ᶠᵒ Q` and `Q ≤ᶠᵒ R` one gets
`P ≤ᶠᵒ R`.

The composite of an interpretation `I : FOInterpretation L₁ L₂ Tag₁ d₁` with
`J : FOInterpretation L₂ L₃ Tag₂ d₂` has tags `Tag₂ × (Fin d₂ → Tag₁)` and
dimension `d₂ * d₁`: an element of the composite universe carries the outer
tag, one inner tag per outer coordinate, and a `d₂ × d₁` matrix of elements.
Its defining formulas are obtained by *pulling back* the defining `L₂`-formulas
of `J` through `I` (`DescriptiveComplexity.FOInterpretation.pull`): atoms become the
defining formulas of `I`, equality becomes componentwise equality (with tags
compared statically), and a quantifier over the universe of `I.Map A` becomes
a finite conjunction/disjunction over `Tag₁` of a block of `d₁` quantifiers
over `A`.

Two points deserve attention:

* the composite's universe `(Tag₂ × (Fin d₂ → Tag₁)) × A^(d₂·d₁)` is only
  *isomorphic* (`DescriptiveComplexity.FOInterpretation.compLEquiv`), not equal, to the
  twice-interpreted `J.Map (I.Map A)`; transitivity therefore uses the
  isomorphism-invariance of the target problem, which is part of the notion
  of `DecisionProblem`;
* pulling back quantifiers requires enumerating the (finitely many) inner
  tags, so composite formulas are noncomputable (they are built with
  `BoundedFormula.iInf`); this does not affect any of the theorems.
-/

@[expose] public section

/-! ### Terms of a relational language are variables

These extend Mathlib's `FirstOrder.Language.Term` and live in its namespace
(where Mathlib would want them, and where dot notation finds them). -/

namespace FirstOrder

open Language

variable {L₂ : Language.{0, 0}}

/-- In a relational language, every term is a variable. -/
def Language.Term.varOf [L₂.IsRelational] {γ : Type*} : L₂.Term γ → γ
  | .var x => x
  | .func f _ => isEmptyElim f

@[simp]
theorem Language.Term.varOf_var [L₂.IsRelational] {γ : Type*} (x : γ) :
    (Term.var x : L₂.Term γ).varOf = x :=
  rfl

@[simp]
theorem Language.Term.realize_varOf [L₂.IsRelational] {γ : Type*} {M : Type*} [L₂.Structure M]
    {v : γ → M} (t : L₂.Term γ) : t.realize v = v t.varOf := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

/-! ### Pulling back a formula through an interpretation -/

section Pull

variable {Tag : Type} {d : ℕ} (I : FOInterpretation L₁ L₂ Tag d) {β : Type}

/-- The environment of the interpreted structure induced by tags `τ` and an
environment `v` for the individual coordinates. -/
def FOInterpretation.liftEnv (I : FOInterpretation L₁ L₂ Tag d) {A : Type} {γ : Type}
    (τ : γ → Tag) (v : γ × Fin d → A) (b : γ) : I.Map A :=
  (τ b, fun j => v (b, j))

/-- Relabeling that splits off the coordinates of the last bound variable. -/
def splitLast {β : Type} {d n : ℕ} :
    (β ⊕ Fin (n + 1)) × Fin d → ((β ⊕ Fin n) × Fin d) ⊕ Fin d
  | (.inl b, j) => .inl (.inl b, j)
  | (.inr i, j) => Fin.lastCases (.inr j) (fun i' => .inl (.inr i', j)) i

/-- Extending a tag assignment to one more bound variable. -/
def extendTag {β : Type} {n : ℕ} (τ : (β ⊕ Fin n) → Tag) (t : Tag) :
    (β ⊕ Fin (n + 1)) → Tag :=
  Sum.elim (fun b => τ (.inl b)) (Fin.snoc (fun i => τ (.inr i)) t)

open Classical in
/-- Pullback of an `L₂`-formula through the interpretation `I`, given a static
assignment of tags to its (free and bound) variables: an `L₁`-formula on the
coordinates which realizes in `A` exactly as the original formula realizes in
`I.Map A` (see `FOInterpretation.realize_pull`). Quantified variables are
expanded into a conjunction over the (finitely many) tags of a block of `d`
quantifiers. -/
noncomputable def FOInterpretation.pull (I : FOInterpretation L₁ L₂ Tag d)
    [L₂.IsRelational] [Finite Tag] :
    ∀ {n : ℕ}, L₂.BoundedFormula β n → ((β ⊕ Fin n) → Tag) → L₁.Formula ((β ⊕ Fin n) × Fin d)
  | _, .falsum, _ => ⊥
  | _, .equal t₁ t₂, τ =>
      if τ t₁.varOf = τ t₂.varOf then
        Formula.iInf fun j : Fin d =>
          Term.equal (Term.var (t₁.varOf, j)) (Term.var (t₂.varOf, j))
      else ⊥
  | _, .rel R ts, τ =>
      (I.relFormula R fun i => τ (ts i).varOf).relabel fun p => ((ts p.1).varOf, p.2)
  | _, .imp φ ψ, τ =>
      (FOInterpretation.pull I φ τ).imp (FOInterpretation.pull I ψ τ)
  | _, .all φ, τ =>
      Formula.iInf fun t : Tag =>
        ((FOInterpretation.pull I φ (extendTag τ t)).relabel splitLast).iAlls (Fin d)

theorem FOInterpretation.realize_pull [L₂.IsRelational] [Finite Tag] {A : Type}
    [L₁.Structure A] {n : ℕ} (φ : L₂.BoundedFormula β n) (τ : (β ⊕ Fin n) → Tag)
    (v : ((β ⊕ Fin n) × Fin d) → A) :
    (I.pull φ τ).Realize v ↔
      φ.Realize (M := I.Map A) (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) := by
  induction φ with
  | falsum =>
    simp only [FOInterpretation.pull, Formula.realize_bot, false_iff]
    exact fun h => h
  | equal t₁ t₂ =>
    have hRHS : (BoundedFormula.equal t₁ t₂).Realize (M := I.Map A)
        (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
        I.liftEnv τ v t₁.varOf = I.liftEnv τ v t₂.varOf := by
      rw [show (BoundedFormula.equal t₁ t₂).Realize (M := I.Map A)
          (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
          t₁.realize (Sum.elim (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr)) =
            t₂.realize (Sum.elim (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr)) from
          Iff.rfl]
      simp [Sum.elim_comp_inl_inr]
    rw [hRHS]
    simp only [FOInterpretation.pull]
    split_ifs with h
    · rw [Formula.realize_iInf]
      simp only [Formula.realize_equal, Term.realize_var]
      exact ⟨fun hj => Prod.ext_iff.mpr ⟨h, funext hj⟩,
        fun hpq j => congrFun (congrArg Prod.snd hpq) j⟩
    · simp only [Formula.realize_bot, false_iff]
      exact fun hpq => h (congrArg Prod.fst hpq)
  | rel R ts =>
    have hRHS : (BoundedFormula.rel R ts).Realize (M := I.Map A)
        (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
        RelMap (M := I.Map A) R fun i => I.liftEnv τ v (ts i).varOf := by
      rw [show (BoundedFormula.rel R ts).Realize (M := I.Map A)
          (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
          RelMap (M := I.Map A) R fun i =>
            (ts i).realize (Sum.elim (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr)) from
          Iff.rfl]
      simp [Sum.elim_comp_inl_inr]
    rw [hRHS, FOInterpretation.relMap_map]
    simp only [FOInterpretation.pull, Formula.realize_relabel]
    exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    simp only [FOInterpretation.pull, Formula.realize_imp, BoundedFormula.realize_imp,
      ihφ, ihψ]
  | all φ ih =>
    simp only [FOInterpretation.pull, Formula.realize_iInf, Formula.realize_iAlls,
      Formula.realize_relabel, BoundedFormula.realize_all]
    have hE₁ : ∀ (t : Tag) (w : Fin d → A),
        I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) ∘ Sum.inl =
          I.liftEnv τ v ∘ Sum.inl := by
      intro t w
      funext b
      rfl
    -- `Fin.snoc` lemmas, instantiated at the interpreted universe with
    -- variable arguments (so that they elaborate without pair literals in
    -- `I.Map A`-typed positions, which `simp`/`rw` matching cannot handle)
    have hlast : ∀ {m : ℕ} (g : Fin m → I.Map A) (a : I.Map A),
        Fin.snoc (α := fun _ => I.Map A) g a (Fin.last m) = a := fun g a => by simp
    have hcs : ∀ {m : ℕ} (g : Fin m → I.Map A) (a : I.Map A) (i' : Fin m),
        Fin.snoc (α := fun _ => I.Map A) g a i'.castSucc = g i' := fun g a i' => by simp
    have hE₂ : ∀ (t : Tag) (w : Fin d → A),
        I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) ∘ Sum.inr =
          Fin.snoc (I.liftEnv τ v ∘ Sum.inr) (t, w) := by
      intro t w
      funext i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Eq.trans ?_ (hlast _ _).symm
        change I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) (Sum.inr (Fin.last _)) =
          (t, w)
        unfold FOInterpretation.liftEnv extendTag
        congr 1
        · simp
        · funext j
          simp [splitLast]
      · refine Eq.trans ?_ (hcs _ _ _).symm
        change I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) (Sum.inr i'.castSucc) =
          I.liftEnv τ v (Sum.inr i')
        unfold FOInterpretation.liftEnv extendTag
        congr 1
        · simp
        · funext j
          simp [splitLast]
    constructor
    · rintro h ⟨t, w⟩
      have := (ih (extendTag τ t) (Sum.elim v w ∘ splitLast)).mp (h t w)
      rwa [hE₁, hE₂] at this
    · intro h t w
      refine (ih (extendTag τ t) (Sum.elim v w ∘ splitLast)).mpr ?_
      rw [hE₁, hE₂]
      exact h (t, w)

end Pull

/-! ### Composition of interpretations -/

section Comp

variable {Tag₁ Tag₂ : Type} {d₁ d₂ : ℕ}
variable [L₂.IsRelational] [L₃.IsRelational] [Finite Tag₁]
variable (J : FOInterpretation L₂ L₃ Tag₂ d₂) (I : FOInterpretation L₁ L₂ Tag₁ d₁)

/-- The composite of two FO interpretations: tags are an outer tag together
with one inner tag per outer coordinate, and dimensions multiply. Its
interpretation of a structure `A` is isomorphic to `J.Map (I.Map A)`
(`FOInterpretation.compLEquiv`). -/
noncomputable def FOInterpretation.comp :
    FOInterpretation L₁ L₃ (Tag₂ × (Fin d₂ → Tag₁)) (d₂ * d₁) where
  relFormula {_n} R T :=
    (I.pull (J.relFormula R fun i => (T i).1)
        (Sum.elim (fun p => (T p.1).2 p.2) Fin.elim0)).relabel
      fun q =>
        match q.1 with
        | .inl p => (p.1, finProdFinEquiv (p.2, q.2))
        | .inr i => i.elim0

variable (A : Type) [L₁.Structure A]

/-- The universe of the composite interpretation is equivalent to the
twice-interpreted universe. -/
def FOInterpretation.compEquiv : (J.comp I).Map A ≃ J.Map (I.Map A) where
  toFun x := (x.1.1, fun k => (x.1.2 k, fun j => x.2 (finProdFinEquiv (k, j))))
  invFun y :=
    ((y.1, fun k => (y.2 k).1),
      fun m => (y.2 (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2)
  left_inv := by
    rintro ⟨⟨t, tg⟩, w⟩
    refine Prod.ext (Prod.ext rfl rfl) (funext fun m => ?_)
    change w (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)) = w m
    rw [show ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2) =
      finProdFinEquiv.symm m from rfl, Equiv.apply_symm_apply]
  right_inv := by
    rintro ⟨t, u⟩
    refine Prod.ext rfl (funext fun k => Prod.ext rfl (funext fun j => ?_))
    change (u (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).2
        (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2 = (u k).2 j
    rw [Equiv.symm_apply_apply]

theorem FOInterpretation.relMap_comp {n : ℕ} (R : L₃.Relations n)
    (x : Fin n → (J.comp I).Map A) :
    RelMap (M := (J.comp I).Map A) R x ↔
      RelMap (M := J.Map (I.Map A)) R (J.compEquiv I A ∘ x) := by
  rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
  simp only [FOInterpretation.comp, Formula.realize_relabel]
  rw [I.realize_pull]
  refine iff_of_eq ?_
  congr 1
  funext i
  exact i.elim0

end Comp

/-! ### Transitivity of FO reductions -/

section Trans

variable {Tag₁ Tag₂ : Type} {d₁ d₂ : ℕ}
variable [L₂.IsRelational] [L₃.IsRelational] [Finite Tag₁]

/-- The universe equivalence of the composite interpretation is an
`L₃`-isomorphism. -/
noncomputable def FOInterpretation.compLEquiv (J : FOInterpretation L₂ L₃ Tag₂ d₂)
    (I : FOInterpretation L₁ L₂ Tag₁ d₁) (A : Type) [L₁.Structure A] :
    (J.comp I).Map A ≃[L₃] J.Map (I.Map A) where
  toEquiv := J.compEquiv I A
  map_fun' := fun f => isEmptyElim f
  map_rel' := fun R x => (J.relMap_comp I A R x).symm

/-- **Transitivity of FO reductions**: if `P ≤ᶠᵒ Q` and `Q ≤ᶠᵒ R`, then
`P ≤ᶠᵒ R`. The composite interpretation is only isomorphic, not equal, to the
twice-applied one, so the isomorphism-invariance built into `DecisionProblem`
is used to conclude. -/
noncomputable def FOReduction.trans [L₁.IsRelational] {P : DecisionProblem L₁}
    {Q : DecisionProblem L₂} {R : DecisionProblem L₃} (g : P ≤ᶠᵒ Q) (f : Q ≤ᶠᵒ R) :
    P ≤ᶠᵒ R :=
  letI := f.tagFinite
  letI := g.tagFinite
  letI := f.tagNonempty
  letI := g.tagNonempty
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toInterpretation := f.toInterpretation.comp g.toInterpretation
    correct := fun A _ _ _ =>
      haveI := g.toInterpretation.map_nonempty (A := A)
      haveI := g.toInterpretation.map_finite A
      ((g.correct A).trans (f.correct (g.toInterpretation.Map A))).trans
        (R.iso_invariant (f.toInterpretation.compLEquiv g.toInterpretation A)).symm }

/-- `Trans` instance for FO reductions, enabling `calc` chains
`P ≤ᶠᵒ Q ≤ᶠᵒ R`. -/
noncomputable instance [L₁.IsRelational] :
    Trans (α := DecisionProblem L₁) (β := DecisionProblem L₂) (γ := DecisionProblem L₃)
      FOReduction FOReduction FOReduction where
  trans g f := g.trans f

end Trans

/-! ### Reflexivity and the preorder structure -/

section Refl

variable (L : Language.{0, 0})

/-- The identity interpretation of a language in itself (one tag, dimension
one). -/
def FOInterpretation.refl : FOInterpretation L L Unit 1 where
  relFormula {_n} R := fun _ => R.formula fun i => Term.var (i, 0)

variable [L.IsRelational] (A : Type) [L.Structure A]

/-- The identity interpretation of a structure is isomorphic to the structure
itself. -/
def FOInterpretation.reflLEquiv : (FOInterpretation.refl L).Map A ≃[L] A where
  toFun x := x.2 0
  invFun a := ((), fun _ => a)
  left_inv := fun x =>
    Prod.ext_iff.mpr ⟨rfl, funext fun j => congrArg x.2 (Subsingleton.elim 0 j)⟩
  right_inv := fun _ => rfl
  map_fun' := fun f => isEmptyElim f
  map_rel' := fun _ _ => Iff.rfl

variable {L} {A}

/-- **Reflexivity of FO reductions**: every decision problem (over a
relational language) reduces to itself, via the identity interpretation. -/
def FOReduction.refl (P : DecisionProblem L) : P ≤ᶠᵒ P where
  Tag := Unit
  dim := 1
  toInterpretation := FOInterpretation.refl L
  correct A _ _ _ := (P.iso_invariant (FOInterpretation.reflLEquiv L A)).symm

/-- **FO reducibility is a preorder** on the decision problems over a fixed
relational language, with `P ≤ Q` the propositional truncation of `P ≤ᶠᵒ Q`.
(Across different languages, reflexivity `FOReduction.refl` and transitivity
`FOReduction.trans` express the same fact in heterogeneous form.) -/
instance : Preorder (DecisionProblem L) where
  le P Q := Nonempty (P ≤ᶠᵒ Q)
  le_refl P := ⟨.refl P⟩
  le_trans _ _ _ := fun ⟨g⟩ ⟨f⟩ => ⟨g.trans f⟩

theorem DecisionProblem.le_def {P Q : DecisionProblem L} :
    P ≤ Q ↔ Nonempty (P ≤ᶠᵒ Q) :=
  Iff.rfl

end Refl

end DescriptiveComplexity
