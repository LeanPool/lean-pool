/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Entropy optimization for finitely many sectors

The normalized weights `q = A / (A + B)` and `1 - q = B / (A + B)`
make the entropy-weighted geometric mean equal to `A + B`. This is the
scalar identity used in Section 5.1 of the auxiliary-separation argument.
The same calculation also applies to an arbitrary nonempty finite family.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- The logarithmic form of the entropy identity at the normalized weights. -/
theorem binary_entropy_log_partition {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.binEntropy (A / (A + B)) +
        Real.log A * (A / (A + B)) +
        Real.log B * (1 - A / (A + B)) = Real.log (A + B) := by
  have hsum : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
  have hcomplement : 1 - A / (A + B) = B / (A + B) := by
    field_simp
    ring
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  rw [hcomplement, Real.log_div hA.ne' hsum, Real.log_div hB.ne' hsum]
  field_simp
  ring

/-- Entropy compensates the weighted geometric mean at the normalized weights. -/
theorem binary_entropy_variational_identity {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.exp (Real.binEntropy (A / (A + B))) *
        A ^ (A / (A + B)) * B ^ (1 - A / (A + B)) = A + B := by
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB,
    ← Real.exp_add, ← Real.exp_add, binary_entropy_log_partition hA hB,
    Real.exp_log (add_pos hA hB)]

/-- The identity with an explicitly named optimizing proportion. -/
theorem binary_entropy_variational_identity_of_ratio {A B q : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hq : q = A / (A + B)) :
    Real.exp (-q * Real.log q - (1 - q) * Real.log (1 - q)) *
        A ^ q * B ^ (1 - q) = A + B := by
  subst q
  have hentropy :
      -(A / (A + B)) * Real.log (A / (A + B)) -
          (1 - A / (A + B)) * Real.log (1 - A / (A + B)) =
        Real.binEntropy (A / (A + B)) := by
    simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
    ring
  rw [hentropy]
  exact binary_entropy_variational_identity hA hB

/-- The logarithmic entropy identity for positive weights on a finite set. -/
theorem finite_entropy_log_partition {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hs : s.Nonempty) (hA : ∀ i ∈ s, 0 < A i) :
    -(∑ i ∈ s, (A i / (∑ j ∈ s, A j)) * Real.log (A i / (∑ j ∈ s, A j))) +
        (∑ i ∈ s, Real.log (A i) * (A i / (∑ j ∈ s, A j))) =
      Real.log (∑ j ∈ s, A j) := by
  have hsum : 0 < ∑ j ∈ s, A j := Finset.sum_pos hA hs
  calc
    _ = ∑ i ∈ s, (A i / (∑ j ∈ s, A j)) * Real.log (∑ j ∈ s, A j) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_div (hA i hi).ne' hsum.ne']
      ring
    _ = (∑ i ∈ s, A i / (∑ j ∈ s, A j)) * Real.log (∑ j ∈ s, A j) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [← Finset.sum_div, div_self hsum.ne', one_mul]

/-- Normalizing any positive finite family attains its sum in the entropy formula. -/
theorem finite_entropy_variational_identity {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hs : s.Nonempty) (hA : ∀ i ∈ s, 0 < A i) :
    Real.exp (-(∑ i ∈ s, (A i / (∑ j ∈ s, A j)) *
        Real.log (A i / (∑ j ∈ s, A j)))) *
        (∏ i ∈ s, (A i) ^ (A i / (∑ j ∈ s, A j))) = ∑ j ∈ s, A j := by
  have hsum : 0 < ∑ j ∈ s, A j := Finset.sum_pos hA hs
  have hprod : (∏ i ∈ s, (A i) ^ (A i / (∑ j ∈ s, A j))) =
      Real.exp (∑ i ∈ s, Real.log (A i) * (A i / (∑ j ∈ s, A j))) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.rpow_def_of_pos (hA i hi) _
  rw [hprod, ← Real.exp_add, finite_entropy_log_partition s A hs hA,
    Real.exp_log hsum]

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
