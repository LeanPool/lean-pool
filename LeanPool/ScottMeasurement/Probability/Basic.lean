/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import LeanPool.ScottMeasurement.FinHead

/-!
# Finitely additive probabilities on Boolean algebras

Scott's probabilities are real-valued and finitely additive.  This file deliberately
does not use Mathlib's countably additive `MeasureTheory.Measure`: the source works
with an arbitrary Boolean algebra and only finite disjoint unions.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

open scoped BigOperators

/-- A normalized finitely additive probability on a Boolean algebra. -/
structure IsProbability {B : Type u} [BooleanAlgebra B] (μ : B → ℝ) : Prop where
  bot : μ ⊥ = 0
  top : μ ⊤ = 1
  additive : ∀ x y, Disjoint x y → μ (x ⊔ y) = μ x + μ y
  nonnegative : ∀ x, 0 ≤ μ x

/-- A finitely additive signed charge.  Unlike `IsProbability`, no
nonnegativity or normalization is imposed. -/
structure IsSignedCharge {B : Type u} [BooleanAlgebra B] (μ : B → ℝ) : Prop where
  bot : μ ⊥ = 0
  additive : ∀ x y, Disjoint x y → μ (x ⊔ y) = μ x + μ y

/-- Nonnegativity of a finitely additive set function. -/
def IsNonnegative {B : Type u} (μ : B → ℝ) : Prop :=
  ∀ x, 0 ≤ μ x

/-- Compatibility name for a finitely additive probability. -/
def IsFinitelyAdditiveProbability {B : Type u} [BooleanAlgebra B] (μ : B → ℝ) : Prop :=
  IsProbability μ

/-- A qualitative ordering is represented exactly by a normalized additive function. -/
def RealizableProbability {B : Type u} [BooleanAlgebra B] (R : B → B → Prop) : Prop :=
  ∃ μ : B → ℝ, IsProbability μ ∧ ∀ x y, R x y ↔ μ x ≥ μ y

/-- A qualitative relation is represented by a finitely additive signed
charge, with no normalization or positivity requirement. -/
def RealizableSignedCharge {B : Type u} [BooleanAlgebra B]
    (R : B → B → Prop) : Prop :=
  ∃ μ : B → ℝ, IsSignedCharge μ ∧ ∀ x y, R x y ↔ μ x ≥ μ y

/-- Scott's strict notation: `x ≻ y` means that `y` is not weakly preferred to `x`. -/
def StrictlyPreferred {B : Type u} (R : B → B → Prop) (x y : B) : Prop :=
  ¬R y x

/-- Scott 1964, condition `(1_B)`: the certain event is strictly above the null event. -/
def ProbNontrivial {B : Type u} [BooleanAlgebra B] (R : B → B → Prop) : Prop :=
  R ⊤ ⊥ ∧ ¬R ⊥ ⊤

/-- Scott 1964, condition `(2_B)`: every event is at least as likely as null. -/
def ProbNonneg {B : Type u} [BooleanAlgebra B] (R : B → B → Prop) : Prop :=
  ∀ x, R x ⊥

/-- Scott 1964, condition `(3_B)`: qualitative probabilities are comparable. -/
def ProbTotal {B : Type u} (R : B → B → Prop) : Prop :=
  ∀ x y, R x y ∨ R y x

open Classical in
/-- Scott 1964, condition `(4_B)`.  The equality says that every atom occurs
equally often on the two sides. -/
def ProbCancellation {B : Type u} [BooleanAlgebra B]
    (R : B → B → Prop) : Prop :=
  ∀ (n : ℕ) (x y : Fin (n + 1) → B),
    (∀ a : B, IsAtom a →
        (∑ i, if a ≤ x i then 1 else 0) =
          (∑ i, if a ≤ y i then 1 else 0 : ℕ)) →
      (∀ i, i ≠ finHead n → R (x i) (y i)) → R (y (finHead n)) (x (finHead n))

/-- Transitivity, de Finetti's condition (iv). -/
def ProbTransitive {B : Type u} (R : B → B → Prop) : Prop :=
  ∀ ⦃x y z⦄, R x y → R y z → R x z

/-- Invariance under adjoining one event disjoint from both sides, de Finetti's
condition (v). -/
def ProbDisjointUnionInvariant {B : Type u} [BooleanAlgebra B]
    (R : B → B → Prop) : Prop :=
  ∀ ⦃x y z⦄, Disjoint z x → Disjoint z y →
    (R x y ↔ R (x ⊔ z) (y ⊔ z))

/-- De Finetti's five qualitative-probability axioms.  Condition (i) is
literally `¬ R ⊥ ⊤`; it does not include Scott's additional `R ⊤ ⊥`
conjunct from `(1_B)`. -/
structure DeFinettiAxioms {B : Type u} [BooleanAlgebra B]
    (R : B → B → Prop) : Prop where
  nontrivial : ¬R ⊥ ⊤
  bottom : ∀ x, R x ⊥
  total : ProbTotal R
  transitive : ProbTransitive R
  disjointUnionInvariant : ProbDisjointUnionInvariant R

theorem IsProbability.compl {B : Type u} [BooleanAlgebra B] {μ : B → ℝ}
    (hμ : IsProbability μ) (x : B) : μ xᶜ = 1 - μ x := by
  classical
  have hd : Disjoint x xᶜ := disjoint_compl_right
  have h := hμ.additive x xᶜ hd
  rw [sup_compl_eq_top, hμ.top] at h
  linarith

theorem IsProbability.mono_of_nonnegative {B : Type u} [BooleanAlgebra B]
    {μ : B → ℝ} (hμ : IsProbability μ) (hn : IsNonnegative μ)
    ⦃x y : B⦄ (hxy : x ≤ y) : μ x ≤ μ y := by
  classical
  have hd : Disjoint x (y \ x) := by
    classical
    rw [disjoint_iff_inf_le]
    simp
  have hy : x ⊔ (y \ x) = y := by
    classical
    exact sup_sdiff_cancel_right hxy
  rw [← hy, hμ.additive _ _ hd]
  exact le_add_of_nonneg_right (hn _)

theorem IsProbability.mono {B : Type u} [BooleanAlgebra B]
    {μ : B → ℝ} (hμ : IsProbability μ) ⦃x y : B⦄ (hxy : x ≤ y) :
    μ x ≤ μ y :=
  hμ.mono_of_nonnegative hμ.nonnegative hxy

theorem IsProbability.le_one_of_nonnegative {B : Type u} [BooleanAlgebra B]
    {μ : B → ℝ} (hμ : IsProbability μ) (hn : IsNonnegative μ) (x : B) :
    μ x ≤ 1 := by
  classical
  simpa [hμ.top] using hμ.mono_of_nonnegative hn (show x ≤ (⊤ : B) from le_top)

theorem IsProbability.le_one {B : Type u} [BooleanAlgebra B]
    {μ : B → ℝ} (hμ : IsProbability μ) (x : B) : μ x ≤ 1 :=
  hμ.le_one_of_nonnegative hμ.nonnegative x

theorem RealizableProbability.nonnegative {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : RealizableProbability R) :
    ∃ μ : B → ℝ, IsFinitelyAdditiveProbability μ ∧
      ∀ x y, R x y ↔ μ x ≥ μ y :=
  hR

theorem RealizableProbability.probNonneg {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : RealizableProbability R) :
    ProbNonneg R := by
  classical
  rcases hR with ⟨μ, hμ, hrep⟩
  intro x
  apply (hrep x ⊥).2
  simpa [hμ.bot] using hμ.nonnegative x

theorem RealizableProbability.probTotal {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : RealizableProbability R) : ProbTotal R := by
  classical
  rcases hR with ⟨μ, -, hrep⟩
  intro x y
  rcases le_total (μ y) (μ x) with h | h
  · exact Or.inl ((hrep x y).2 h)
  · exact Or.inr ((hrep y x).2 h)

theorem RealizableProbability.probNontrivial {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : RealizableProbability R) :
    ProbNontrivial R := by
  classical
  rcases hR with ⟨μ, hμ, hrep⟩
  constructor
  · exact (hrep ⊤ ⊥).2 (by rw [hμ.top, hμ.bot]; norm_num)
  · intro h
    have := (hrep ⊥ ⊤).1 h
    rw [hμ.top, hμ.bot] at this
    norm_num at this

theorem RealizableProbability.probTransitive {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : RealizableProbability R) : ProbTransitive R := by
  classical
  rcases hR with ⟨μ, -, hrep⟩
  intro x y z hxy hyz
  exact (hrep x z).2 (((hrep y z).1 hyz).trans ((hrep x y).1 hxy))

theorem RealizableProbability.disjointUnionInvariant {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : RealizableProbability R) :
    ProbDisjointUnionInvariant R := by
  classical
  rcases hR with ⟨μ, hμ, hrep⟩
  intro x y z hzx hzy
  rw [hrep x y, hrep (x ⊔ z) (y ⊔ z)]
  rw [hμ.additive x z hzx.symm, hμ.additive y z hzy.symm]
  constructor <;> intro h <;> linarith

end Scott1964.MeasurementStructures
