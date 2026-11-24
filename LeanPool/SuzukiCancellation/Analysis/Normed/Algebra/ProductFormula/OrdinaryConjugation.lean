/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.CommutatorExpansion

/-!
# Finite conjugation bounds from exponential contractions

The finite commutator expansion has no growth loss when each exponential is a
contraction for every real parameter. The coefficients, ordering and factorial
weights are those of `commutatorExpansion_conj`; no new expansion is introduced.

## Main results

* `norm_multiConj_eq_of_le_one`: finite ordered conjugation preserves the norm.
* `norm_multiConj_sub_sum_le_of_le_one`: the finite Taylor bound for every real step.
* `norm_multiConj_sub_sum_le_of_skewAdjoint`: the C*-algebra specialization.
-/

@[expose] public noncomputable section

open NormedSpace Finset
open scoped RealScalar algebraMap

namespace TrotterError

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- An ordered conjugation by a finite family of contractive exponential groups
preserves the norm. -/
theorem norm_multiConj_eq_of_le_one {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸)
    (hA : ∀ i (t : ℝ), ‖exp (t • A i)‖ ≤ 1) (t : ℝ) : ‖multiConj A B t‖ = ‖B‖ := by
  simpa only [multiConj, List.map_ofFn, Function.comp_def] using
    norm_list_exp_conj_eq_of_le_one A hA (List.ofFn fun i ↦ i) B t

/-- The finite Taylor polynomial of an ordered composition of conjugations has
the original multinomial remainder bound for every real parameter. -/
theorem norm_multiConj_sub_sum_le_of_le_one {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) (hp : 1 ≤ p) (t : ℝ)
    (hA : ∀ i (u : ℝ), ‖exp (u • A i)‖ ≤ 1) :
    ‖multiConj A B t - ∑ k ∈ range p, conjCoeff A B k * (t ^ k : 𝔸)‖ ≤
      αCommConj A B p * |t| ^ p / (Nat.factorial p : ℝ) := by
  rw [commutatorExpansion_conj A B p t hp, add_sub_cancel_left]
  exact norm_commutatorRemainder_le_of_le_one A B p t hA

/-- In a C*-algebra, skew-adjoint generators automatically satisfy the
exponential contraction assumptions of the finite Taylor bound. -/
theorem norm_multiConj_sub_sum_le_of_skewAdjoint [StarRing 𝔸] [CStarRing 𝔸]
    [StarModule ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (hp : 1 ≤ p)
    (t : ℝ) (hA : ∀ i, star (A i) = -A i) :
    ‖multiConj A B t - ∑ k ∈ range p, conjCoeff A B k * (t ^ k : 𝔸)‖ ≤
      αCommConj A B p * |t| ^ p / (Nat.factorial p : ℝ) :=
  norm_multiConj_sub_sum_le_of_le_one A B p hp t
    (fun i ↦ norm_exp_smul_le_one_of_skewAdjoint (hA i))

end

/-- The multinomial commutator constant of an empty generator list vanishes
at every positive order. -/
theorem αCommConj_empty {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    (A : Fin 0 → 𝔸) (B : 𝔸) (p : ℕ) (hp : 1 ≤ p) :
    αCommConj A B p = 0 := by
  have hempty : finAntidiagonal 0 p = ∅ := by
    ext q
    simp only [mem_finAntidiagonal, Finset.sum_empty, Finset.univ_eq_empty,
      Finset.notMem_empty, iff_false]
    lia
  simp [αCommConj, hempty]

end TrotterError
