/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

noncomputable section

namespace FiniteLaw

theorem map_mass_mul_conditional_map {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (f : A → B) (g : A → C) (b : B) (c : C) :
    (p.map f).mass b * ((p.conditional f b).map g).mass c =
      (p.map (fun a => (f a, g a))).mass (b, c) := by
  classical
  rw [map_mass (p.conditional f b) g c, Finset.mul_sum,
    map_mass p (fun a => (f a, g a)) (b, c)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hgc : g a = c
  · rw [ite_eq_left hgc, map_mass_mul_conditional]
    simp only [Prod.mk.injEq, hgc, and_true]
  · rw [ite_eq_right hgc, mul_zero]
    have hpair : (f a, g a) ≠ (b, c) :=
      fun he => hgc (congrArg Prod.snd he)
    rw [ite_eq_right hpair]

end FiniteLaw

/-- A finite record of labels from the first n levels of a hierarchy. -/
def LabelRecord (Label : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => LabelRecord Label n × Label n

instance labelRecordFintype (Label : ℕ → Type u) [∀ n, Fintype (Label n)] :
    (n : ℕ) → Fintype (LabelRecord Label n)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | n + 1 => by
      letI := labelRecordFintype Label n
      change Fintype (LabelRecord Label n × Label n)
      infer_instance

/-- Collect the first n labels of a source point into a label record. -/
def labelRecordOf {A : Type v} {Label : ℕ → Type u}
    (labels : ∀ n, A → Label n) : (n : ℕ) → A → LabelRecord Label n
  | 0, _ => PUnit.unit
  | n + 1, a => (labelRecordOf labels n a, labels n a)

/-- Conditional probability laws describing successive refinements of finite labels. -/
structure FiniteLabelHierarchy (Label : ℕ → Type u) [∀ n, Fintype (Label n)]
    (depth : ℕ) where
  /-- The next-label law conditioned on an existing prefix. -/
  conditional : ∀ n, n < depth → LabelRecord Label n → FiniteLaw (Label n)

namespace FiniteLabelHierarchy

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)] {depth : ℕ}

/-- The probability law on label prefixes induced by the successive conditional laws. -/
def prefixLaw (h : FiniteLabelHierarchy Label depth) :
    (n : ℕ) → n ≤ depth → FiniteLaw (LabelRecord Label n)
  | 0, _ =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := by
          classical
          refine Finset.sum_eq_single_of_mem (PUnit.unit : LabelRecord Label 0)
            (Finset.mem_univ _) ?_
          intro r _ hr
          cases r
          exact (hr rfl).elim }
  | n + 1, hn =>
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn))

@[simp] theorem prefixLaw_zero_mass (h : FiniteLabelHierarchy Label depth)
    (hn : 0 ≤ depth) (r : LabelRecord Label 0) :
    (h.prefixLaw 0 hn).mass r = 1 := rfl

@[simp] theorem prefixLaw_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    h.prefixLaw (n + 1) hn =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn)) := rfl

theorem prefixLaw_succ_mass (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) (r : LabelRecord Label n) (s : Label n) :
    (h.prefixLaw (n + 1) hn).mass (r, s) =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).mass r *
        (h.conditional n (Nat.lt_of_succ_le hn) r).mass s := rfl

/-- Expected conditional entropy contributed by one hierarchy refinement. -/
def refinementEntropy (h : FiniteLabelHierarchy Label depth) (n : ℕ) : ℝ :=
  if hn : n < depth then
    ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
      finiteEntropy (h.conditional n hn r).mass
  else 0

theorem refinementEntropy_eq (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n < depth) :
    h.refinementEntropy n =
      ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
        finiteEntropy (h.conditional n hn r).mass := by
  simp only [refinementEntropy, dite_eq_left hn]

@[simp] theorem refinementEntropy_eq_zero_of_le
    (h : FiniteLabelHierarchy Label depth) {n : ℕ} (hn : depth ≤ n) :
    h.refinementEntropy n = 0 := by
  simp only [refinementEntropy, dite_eq_right (Nat.not_lt.mpr hn)]

theorem zero_prefix_contribution (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n < depth) (r : LabelRecord Label n)
    (hr : (h.prefixLaw n (Nat.le_of_lt hn)).mass r = 0) :
    (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
      finiteEntropy (h.conditional n hn r).mass = 0 := by
  rw [hr, zero_mul]

theorem prefixLaw_entropy_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    finiteEntropy (h.prefixLaw (n + 1) hn).mass =
      finiteEntropy (h.prefixLaw n (Nat.le_of_succ_le hn)).mass +
        h.refinementEntropy n := by
  rw [refinementEntropy_eq h n (Nat.lt_of_succ_le hn)]
  exact FiniteLaw.joint_entropy (h.prefixLaw n (Nat.le_of_succ_le hn))
    (h.conditional n (Nat.lt_of_succ_le hn))

theorem prefixLaw_entropy (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n ≤ depth) :
    finiteEntropy (h.prefixLaw n hn).mass =
      ∑ j ∈ Finset.range n, h.refinementEntropy j := by
  induction n with
  | zero =>
      simp [prefixLaw, finiteEntropy, entropyTerm, LabelRecord]
  | succ n ih =>
      rw [prefixLaw_entropy_succ h n hn,
        ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]

/-- The induced probability law on complete label records. -/
def recordLaw (h : FiniteLabelHierarchy Label depth) :
    FiniteLaw (LabelRecord Label depth) := h.prefixLaw depth le_rfl

theorem recordLaw_entropy (h : FiniteLabelHierarchy Label depth) :
    finiteEntropy h.recordLaw.mass =
      ∑ j ∈ Finset.range depth, h.refinementEntropy j :=
  h.prefixLaw_entropy depth le_rfl

theorem refinementEntropy_sum_of_injective_record
    {A : Type v} [Fintype A] (h : FiniteLabelHierarchy Label depth)
    (p : FiniteLaw A) (record : A → LabelRecord Label depth)
    (hinjective : Function.Injective record)
    (hmass : h.recordLaw.mass = (p.map record).mass) :
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) = finiteEntropy p.mass := by
  calc
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) =
        finiteEntropy h.recordLaw.mass := h.recordLaw_entropy.symm
    _ = finiteEntropy (p.map record).mass := congrArg finiteEntropy hmass
    _ = finiteEntropy p.mass := p.map_entropy_of_injective record hinjective

/-- Build a hierarchy by conditioning a source law on its successive label prefixes. -/
def ofLawLabels {A : Type v} [Fintype A] (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ) : FiniteLabelHierarchy Label depth where
  conditional n _ r := (p.conditional (labelRecordOf labels n) r).map (labels n)

theorem ofLawLabels_prefixLaw_mass {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n ≤ depth) :
    ((ofLawLabels p labels depth).prefixLaw n hn).mass =
      (p.map (labelRecordOf labels n)).mass := by
  classical
  induction n with
  | zero =>
      funext r
      rw [prefixLaw_zero_mass, FiniteLaw.map_mass]
      refine p.total.symm.trans ?_
      apply Finset.sum_congr rfl
      intro a _
      rw [ite_eq_left (show labelRecordOf labels 0 a = r by cases r; rfl)]
  | succ n ih =>
      funext rs
      rcases rs with ⟨r, s⟩
      rw [prefixLaw_succ_mass]
      change ((ofLawLabels p labels depth).prefixLaw n
          (Nat.le_of_succ_le hn)).mass r *
        ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass s =
          (p.map (labelRecordOf labels (n + 1))).mass (r, s)
      rw [ih (Nat.le_of_succ_le hn)]
      exact p.map_mass_mul_conditional_map
        (labelRecordOf labels n) (labels n) r s

theorem ofLawLabels_refinementEntropy_eq {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n < depth) :
    (ofLawLabels p labels depth).refinementEntropy n =
      ∑ r : LabelRecord Label n, (p.map (labelRecordOf labels n)).mass r *
        finiteEntropy ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass := by
  rw [refinementEntropy_eq _ n hn,
    ofLawLabels_prefixLaw_mass p labels depth n (Nat.le_of_lt hn)]
  rfl

theorem ofLawLabels_refinementEntropy_sum {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ j ∈ Finset.range depth,
      (ofLawLabels p labels depth).refinementEntropy j) = finiteEntropy p.mass := by
  apply (ofLawLabels p labels depth).refinementEntropy_sum_of_injective_record
    p (labelRecordOf labels depth) hinjective
  exact ofLawLabels_prefixLaw_mass p labels depth depth le_rfl

theorem entropy_eq_sum_conditional_labels {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    finiteEntropy p.mass =
      ∑ j ∈ Finset.range depth, ∑ r : LabelRecord Label j,
        (p.map (labelRecordOf labels j)).mass r *
          finiteEntropy ((p.conditional (labelRecordOf labels j) r).map (labels j)).mass := by
  rw [← ofLawLabels_refinementEntropy_sum p labels depth hinjective]
  apply Finset.sum_congr rfl
  intro j hj
  exact ofLawLabels_refinementEntropy_eq p labels depth j (Finset.mem_range.mp hj)

end FiniteLabelHierarchy

end
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
