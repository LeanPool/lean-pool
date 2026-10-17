/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalTypeCounting

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

/-- Sum letter populations over the fibers of a labelling map. -/
def pushforwardCounts {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (b : B) : ℕ := by
  classical
  exact ∑ a, if label a = b then counts a else 0

theorem pushforwardCounts_sum {A B : Type*} [Fintype A] [Fintype B]
    (counts : A → ℕ) (label : A → B) :
    (∑ b, pushforwardCounts counts label b) = ∑ a, counts a := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  simp

theorem pushforwardCounts_apply {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (hinjective : Function.Injective label)
    (a : A) : pushforwardCounts counts label (label a) = counts a := by
  classical
  simp [pushforwardCounts, hinjective.eq_iff]

theorem pushforwardCounts_sum_pair {A B C : Type*}
    [Fintype A] [Fintype C] (counts : A → ℕ)
    (coarse : A → B) (fine : A → C) (b : B) :
    (∑ c, pushforwardCounts counts (fun a => (coarse a, fine a)) (b, c)) =
      pushforwardCounts counts coarse b := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : coarse a = b
  · simp [Prod.mk.injEq, hab]
  · simp [Prod.mk.injEq, hab]

theorem pushforwardCounts_factorial_prod_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    (∏ b, (pushforwardCounts counts label b).factorial) =
      ∏ a, (counts a).factorial := by
  classical
  have hfactor (b : B) : (pushforwardCounts counts label b).factorial =
      ∏ a, if label a = b then (counts a).factorial else 1 := by
    by_cases hb : ∃ a, label a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [pushforwardCounts_apply counts label hinjective]
      simp [hinjective.eq_iff]
    · simp [pushforwardCounts, not_exists.mp hb]
  simp_rw [hfactor]
  rw [Finset.prod_comm]
  simp

theorem multinomial_pushforwardCounts_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    Nat.multinomial Finset.univ (pushforwardCounts counts label) =
      Nat.multinomial Finset.univ counts := by
  simp only [Nat.multinomial, pushforwardCounts_sum,
    pushforwardCounts_factorial_prod_of_injective counts label hinjective]

namespace LabelHierarchyCounts

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)]

/-- Product of multinomial counts for refining every prefix by one additional label. -/
def refinementCount (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ) : ℕ :=
  ∏ r : LabelRecord Label n,
    Nat.multinomial Finset.univ (fun s : Label n => counts (n + 1) (r, s))

theorem multinomial_succ (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ)
    (compatible : ∀ r, counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts (n + 1)) =
      Nat.multinomial Finset.univ (counts n) * refinementCount counts n := by
  classical
  have hrows : (fun r => ∑ s : Label n, counts (n + 1) (r, s)) = counts n :=
    funext fun r => (compatible r).symm
  exact (multinomial_prod_counts
    (A := LabelRecord Label n) (B := Label n) (counts (n + 1))).trans
      (congrArg (fun rows : LabelRecord Label n → ℕ =>
        Nat.multinomial Finset.univ rows * refinementCount counts n) hrows)

theorem pool_multinomial_eq_one_of_zero
    (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ)
    (compatible : ∀ r, counts n r = ∑ s : Label n, counts (n + 1) (r, s))
    (r : LabelRecord Label n) (hzero : counts n r = 0) :
    Nat.multinomial Finset.univ (fun s : Label n => counts (n + 1) (r, s)) = 1 := by
  have hchild (s : Label n) : counts (n + 1) (r, s) = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      counts (n + 1) (r, s) ≤ ∑ t : Label n, counts (n + 1) (r, t) :=
        Finset.single_le_sum (f := fun t : Label n => counts (n + 1) (r, t))
          (fun t _ => Nat.zero_le _) (Finset.mem_univ s)
      _ = 0 := (compatible r).symm.trans hzero
  simp [Nat.multinomial, hchild]

theorem multinomial_eq_refinementCount_product
    (counts : ∀ n, LabelRecord Label n → ℕ) (depth : ℕ)
    (compatible : ∀ n < depth, ∀ r,
      counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts depth) =
      ∏ n ∈ Finset.range depth, refinementCount counts n := by
  classical
  induction depth with
  | zero =>
      exact Nat.multinomial_singleton (PUnit.unit : LabelRecord Label 0) (counts 0)
  | succ depth ih =>
      rw [multinomial_succ counts depth (compatible depth (Nat.lt_succ_self depth))]
      rw [ih (fun n hn => compatible n (Nat.lt_trans hn (Nat.lt_succ_self depth))),
        Finset.prod_range_succ]

/-- Push source letter populations forward to their first n labels. -/
def sourcePrefixCounts {A : Type v} [Fintype A] (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) : LabelRecord Label n → ℕ :=
  pushforwardCounts counts (labelRecordOf labels n)

theorem sourcePrefixCounts_compatible {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) :
    sourcePrefixCounts counts labels n r =
      ∑ s : Label n, sourcePrefixCounts counts labels (n + 1) (r, s) :=
  (pushforwardCounts_sum_pair counts (labelRecordOf labels n) (labels n) r).symm

theorem source_refinementCount_product {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Nat.multinomial Finset.univ counts := by
  calc
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
        Nat.multinomial Finset.univ (sourcePrefixCounts counts labels depth) :=
      (multinomial_eq_refinementCount_product (sourcePrefixCounts counts labels) depth
        (fun n _ r => sourcePrefixCounts_compatible counts labels n r)).symm
    _ = Nat.multinomial Finset.univ counts :=
      multinomial_pushforwardCounts_of_injective counts
        (labelRecordOf labels depth) hinjective

theorem source_refinementCount_product_eq_exactWords_card
    {A : Type v} [Fintype A] [DecidableEq A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Fintype.card (ExactWords counts) := by
  rw [source_refinementCount_product counts labels depth hinjective, exactWords_card]

end LabelHierarchyCounts
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
