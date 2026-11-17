/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.NoncommRing

/-!
# Trace inequalities for real spectral powers
-/

@[expose] public section

open Matrix

namespace FunctionalInequalities.Analysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Rearrangement for two powers: `a^α b^β + a^β b^α ≤ a^{α+β} + b^{α+β}` for `a, b > 0` and
`α, β ≥ 0`, since `(a^α - b^α)(a^β - b^β) ≥ 0`. -/
theorem rpow_mul_rpow_add_rpow_mul_rpow_le {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) :
    a ^ α * b ^ β + a ^ β * b ^ α ≤ a ^ (α + β) + b ^ (α + β) := by
  rw [Real.rpow_add ha, Real.rpow_add hb]
  rcases le_total a b with hab | hba
  · have hαab : a ^ α ≤ b ^ α := Real.rpow_le_rpow ha.le hab hα
    have hβab : a ^ β ≤ b ^ β := Real.rpow_le_rpow ha.le hab hβ
    have hprod : 0 ≤ (a ^ α - b ^ α) * (a ^ β - b ^ β) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hαab) (sub_nonpos.mpr hβab)
    nlinarith
  · have hαba : b ^ α ≤ a ^ α := Real.rpow_le_rpow hb.le hba hα
    have hβba : b ^ β ≤ a ^ β := Real.rpow_le_rpow hb.le hba hβ
    have hprod : 0 ≤ (b ^ α - a ^ α) * (b ^ β - a ^ β) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hαba) (sub_nonpos.mpr hβba)
    nlinarith

/-- The trace inequality in an eigenbasis: for `d > 0` and a symmetric `B`,
`Tr(D^α B D^β B) ≤ Tr(D^{α+β} B²)` with `D = diag d`. -/
theorem trace_diagonal_rpow_mul_le {d : n → ℝ} (hd : ∀ i, 0 < d i) {B : Matrix n n ℝ}
    (hB : B.IsSymm) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (diagonal (fun i => d i ^ α) * B * diagonal (fun i => d i ^ β) * B).trace ≤
      (diagonal (fun i => d i ^ (α + β)) * B ^ 2).trace := by
  have hsymm : ∀ i j, B j i = B i j := by
    intro i j
    exact congrFun (congrFun hB i) j
  have hsquare : ∀ i j, (B i j) ^ 2 = (B j i) ^ 2 := by
    intro i j
    rw [hsymm i j]
  have hLraw :
      (diagonal (fun i => d i ^ α) * B * diagonal (fun i => d i ^ β) * B).trace =
        ∑ i, ∑ j, d i ^ α * B i j * d j ^ β * B j i := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  have hRraw :
      (diagonal (fun i => d i ^ (α + β)) * B ^ 2).trace =
        ∑ i, ∑ j, d i ^ (α + β) * B i j * B j i := by
    simp only [trace, pow_two, diag_apply, Matrix.mul_apply, diagonal_apply, Finset.mul_sum,
      ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hL :
      (diagonal (fun i => d i ^ α) * B * diagonal (fun i => d i ^ β) * B).trace =
        ∑ i, ∑ j, d i ^ α * d j ^ β * (B i j) ^ 2 := by
    rw [hLraw]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm i j]
    ring
  have hR :
      (diagonal (fun i => d i ^ (α + β)) * B ^ 2).trace =
        ∑ i, ∑ j, d i ^ (α + β) * (B i j) ^ 2 := by
    rw [hRraw]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm i j]
    ring
  have hswap (p q : ℝ) :
      (∑ i, ∑ j, d i ^ p * d j ^ q * (B i j) ^ 2) =
        ∑ i, ∑ j, d i ^ q * d j ^ p * (B i j) ^ 2 := by
    calc
      (∑ i, ∑ j, d i ^ p * d j ^ q * (B i j) ^ 2) =
          ∑ j, ∑ i, d i ^ p * d j ^ q * (B i j) ^ 2 := by
            rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, d j ^ q * d i ^ p * (B j i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsquare i j]
            ring
      _ = ∑ i, ∑ j, d i ^ q * d j ^ p * (B i j) ^ 2 := by
            rw [Finset.sum_comm]
  have h2L :
      2 * (∑ i, ∑ j, d i ^ α * d j ^ β * (B i j) ^ 2) =
        ∑ i, ∑ j,
          (d i ^ α * d j ^ β + d i ^ β * d j ^ α) * (B i j) ^ 2 := by
    calc
      2 * (∑ i, ∑ j, d i ^ α * d j ^ β * (B i j) ^ 2) =
          (∑ i, ∑ j, d i ^ α * d j ^ β * (B i j) ^ 2) +
            (∑ i, ∑ j, d i ^ α * d j ^ β * (B i j) ^ 2) := by ring
      _ = (∑ i, ∑ j, d i ^ α * d j ^ β * (B i j) ^ 2) +
            (∑ i, ∑ j, d i ^ β * d j ^ α * (B i j) ^ 2) := by
            rw [hswap α β]
      _ = ∑ i, ∑ j,
          (d i ^ α * d j ^ β + d i ^ β * d j ^ α) * (B i j) ^ 2 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  have h2R :
      2 * (∑ i, ∑ j, d i ^ (α + β) * (B i j) ^ 2) =
        ∑ i, ∑ j,
          (d i ^ (α + β) + d j ^ (α + β)) * (B i j) ^ 2 := by
    have hswapR :
        (∑ i, ∑ j, d i ^ (α + β) * (B i j) ^ 2) =
          ∑ i, ∑ j, d j ^ (α + β) * (B i j) ^ 2 := by
      simpa [Real.rpow_zero] using hswap (α + β) 0
    calc
      2 * (∑ i, ∑ j, d i ^ (α + β) * (B i j) ^ 2) =
          (∑ i, ∑ j, d i ^ (α + β) * (B i j) ^ 2) +
            (∑ i, ∑ j, d i ^ (α + β) * (B i j) ^ 2) := by ring
      _ = (∑ i, ∑ j, d i ^ (α + β) * (B i j) ^ 2) +
            (∑ i, ∑ j, d j ^ (α + β) * (B i j) ^ 2) := by
            rw [hswapR]
      _ = ∑ i, ∑ j,
          (d i ^ (α + β) + d j ^ (α + β)) * (B i j) ^ 2 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  have hsum :
      (∑ i, ∑ j,
          (d i ^ α * d j ^ β + d i ^ β * d j ^ α) * (B i j) ^ 2) ≤
        ∑ i, ∑ j,
          (d i ^ (α + β) + d j ^ (α + β)) * (B i j) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hpow := rpow_mul_rpow_add_rpow_mul_rpow_le
      (hd i) (hd j) hα hβ
    have hnonneg : 0 ≤ (B i j) ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_right hpow hnonneg
  rw [hL, hR]
  linarith

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The functional calculus of a real symmetric matrix in its orthonormal eigenbasis. -/
theorem cfc_eq_mul_diagonal_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  have hdiag :
      diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) =
        diagonal (fun i => f (hA.eigenvalues i)) := by
    apply congrArg (fun g : n → ℝ => diagonal g)
    funext i
    simp [Function.comp_def, RCLike.ofReal_real_eq_id]
  have hstar :
      star (hA.eigenvectorUnitary : Matrix n n ℝ) =
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
  change
    (hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) =
      (hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal (fun i => f (hA.eigenvalues i)) *
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ
  rw [hdiag, hstar]

/-- Lee–Vempala (2024), Lemma 42 (Eldan): for a positive definite real matrix `A`, a symmetric
matrix `Δ` and `α, β ≥ 0`, `Tr(A^α Δ A^β Δ) ≤ Tr(A^{α+β} Δ²)`. -/
theorem trace_rpow_mul_rpow_mul_le {A Δ : Matrix n n ℝ} (hA : A.PosDef) (hΔ : Δ.IsSymm)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (cfc (fun x : ℝ => x ^ α) A * Δ * cfc (fun x : ℝ => x ^ β) A * Δ).trace ≤
      (cfc (fun x : ℝ => x ^ (α + β)) A * Δ ^ 2).trace := by
  let hH : A.IsHermitian := hA.isHermitian
  let u := hH.eigenvectorUnitary
  let U : Matrix n n ℝ := u
  let Dα : Matrix n n ℝ :=
    diagonal (fun i => hH.eigenvalues i ^ α)
  let Dβ : Matrix n n ℝ :=
    diagonal (fun i => hH.eigenvalues i ^ β)
  let Dγ : Matrix n n ℝ :=
    diagonal (fun i => hH.eigenvalues i ^ (α + β))
  let B : Matrix n n ℝ := Uᵀ * Δ * U
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUU : U * Uᵀ = 1 := by
    have h :=
      Unitary.mul_star_self_of_mem (U := U) (by
        exact u.2)
    rw [hstar] at h
    exact h
  have hUtU : Uᵀ * U = 1 := by
    have h :=
      Unitary.star_mul_self_of_mem (U := U) (by
        exact u.2)
    rw [hstar] at h
    exact h
  have hB : B.IsSymm := by
    change (Uᵀ * Δ * U)ᵀ = Uᵀ * Δ * U
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hΔ]
    simp [Matrix.mul_assoc]
  have hleft :
      (U * Dα * Uᵀ * Δ * U * Dβ * Uᵀ * Δ).trace =
        (Dα * B * Dβ * B).trace := by
    calc
      (U * Dα * Uᵀ * Δ * U * Dβ * Uᵀ * Δ).trace =
          (Dα * Uᵀ * Δ * U * Dβ * Uᵀ * Δ * U).trace := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_comm U
                (Dα * Uᵀ * Δ * U * Dβ * Uᵀ * Δ))
      _ = (Dα * B * Dβ * B).trace := by
        simp [B, Matrix.mul_assoc]
  have hBB :
      B * B = Uᵀ * Δ * Δ * U := by
    calc
      B * B = Uᵀ * Δ * (U * Uᵀ) * Δ * U := by
        simp [B, Matrix.mul_assoc]
      _ = Uᵀ * Δ * Δ * U := by
        rw [hUU]
        simp [Matrix.mul_assoc]
  have haux : Uᵀ * Δ ^ 2 * U = B * B := by
    simpa [pow_two, Matrix.mul_assoc] using hBB.symm
  have hright :
      (U * Dγ * Uᵀ * Δ ^ 2).trace =
        (Dγ * B ^ 2).trace := by
    calc
      (U * Dγ * Uᵀ * Δ ^ 2).trace =
          (U * (Dγ * Uᵀ * Δ ^ 2)).trace := by
            simp [Matrix.mul_assoc]
      _ = (Dγ * Uᵀ * Δ ^ 2 * U).trace := by
            exact Matrix.trace_mul_comm U (Dγ * Uᵀ * Δ ^ 2)
      _ = (Dγ * (B * B)).trace := by
            simpa [Matrix.mul_assoc] using
              congrArg (fun X : Matrix n n ℝ => (Dγ * X).trace) haux
      _ = (Dγ * B ^ 2).trace := by
            rw [pow_two]
  have hcfa :
      cfc (fun x : ℝ => x ^ α) A = U * Dα * Uᵀ := by
    simpa [U, Dα] using
      (cfc_eq_mul_diagonal_mul hH (fun x : ℝ => x ^ α))
  have hcfb :
      cfc (fun x : ℝ => x ^ β) A = U * Dβ * Uᵀ := by
    simpa [U, Dβ] using
      (cfc_eq_mul_diagonal_mul hH (fun x : ℝ => x ^ β))
  have hcfg :
      cfc (fun x : ℝ => x ^ (α + β)) A = U * Dγ * Uᵀ := by
    simpa [U, Dγ] using
      (cfc_eq_mul_diagonal_mul hH (fun x : ℝ => x ^ (α + β)))
  have hineq :
      (Dα * B * Dβ * B).trace ≤
        (Dγ * B ^ 2).trace := by
    apply trace_diagonal_rpow_mul_le
      (d := hH.eigenvalues)
      (fun i => hA.eigenvalues_pos i)
      hB hα hβ
  calc
    (cfc (fun x : ℝ => x ^ α) A * Δ *
        cfc (fun x : ℝ => x ^ β) A * Δ).trace =
        (U * Dα * Uᵀ * Δ * U * Dβ * Uᵀ * Δ).trace := by
          rw [hcfa, hcfb]
          simp [Matrix.mul_assoc]
    _ = (Dα * B * Dβ * B).trace := hleft
    _ ≤ (Dγ * B ^ 2).trace := hineq
    _ = (U * Dγ * Uᵀ * Δ ^ 2).trace := hright.symm
    _ = (cfc (fun x : ℝ => x ^ (α + β)) A * Δ ^ 2).trace := by
          rw [hcfg]


end FunctionalInequalities.Analysis
