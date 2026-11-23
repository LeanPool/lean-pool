/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Basic.GroundState
public import Mathlib.Analysis.Matrix.Spectrum
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Linarith

/-!
# Existence of ground states and the ground-state energy

* `qf_ge_of_diagonalisation`: if an orthogonal matrix `P` diagonalises `H` (`H P = P diag λ`), then
  `⟨ψ, H ψ⟩ ≥ (min λ) ‖ψ‖²`.
* `exists_groundState`: every symmetric matrix on a nonempty finite index type has a normalised
  ground state (spectral theorem).
* `gsEnergy H`: the ground-state energy; `gsEnergy_le`: it is a lower bound on normalised
  expectation values; `qf_groundState_eq`: it is attained by every normalised ground state.
-/

@[expose] public section

namespace DFT

open Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem qf_ge_of_diagonalisation {H P : Matrix C C ℝ} {lam : C → ℝ} (hP : Pᵀ * P = 1)
    (hHP : H * P = P * diagonal lam) {E : ℝ} (hE : ∀ a, E ≤ lam a) (v : C → ℝ) :
    E * (v ⬝ᵥ v) ≤ qf H v := by
  have hPP : P * Pᵀ = 1 := mul_eq_one_comm.mp hP
  have hdot : ∀ x y : C → ℝ, (P *ᵥ x) ⬝ᵥ (P *ᵥ y) = x ⬝ᵥ y := by
    intro x y
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hP, vecMul_one]
  obtain ⟨c, rfl⟩ : ∃ c, v = P *ᵥ c := ⟨Pᵀ *ᵥ v, by rw [mulVec_mulVec, hPP, one_mulVec]⟩
  have hq : qf H (P *ᵥ c) = c ⬝ᵥ (diagonal lam *ᵥ c) := by
    unfold qf
    rw [mulVec_mulVec, hHP, ← mulVec_mulVec, hdot]
  rw [hq, hdot]
  simp only [dotProduct, mulVec, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ,
    ite_true, Finset.mul_sum]
  apply Finset.sum_le_sum; intro a _
  nlinarith [hE a, mul_self_nonneg (c a)]

/-- Orthonormal eigenvectors of a symmetric real matrix, as an orthogonal matrix diagonalising it.
-/
theorem exists_diagonalisation {H : Matrix C C ℝ} (hS : H.IsSymm) :
    ∃ (P : Matrix C C ℝ) (lam : C → ℝ), Pᵀ * P = 1 ∧ H * P = P * diagonal lam := by
  have hH : H.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]; exact hS
  refine ⟨Matrix.of fun x a => (hH.eigenvectorBasis a) x, hH.eigenvalues, ?_, ?_⟩
  · ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) a b
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
    simp only [transpose_apply, of_apply]
    rw [← h1]
    simp [dotProduct, mul_comm]
  · ext x a
    have := congrFun (hH.mulVec_eigenvectorBasis a) x
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [of_apply, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [this, mul_comm]

omit [DecidableEq C] in
/-- **Existence of a normalised ground state.** -/
theorem exists_groundState [Nonempty C] {H : Matrix C C ℝ} (hS : H.IsSymm) :
    ∃ ψ, IsGroundState H ψ ∧ ψ ⬝ᵥ ψ = 1 := by
  classical
  obtain ⟨P, lam, hP, hHP⟩ := exists_diagonalisation hS
  obtain ⟨a0, -, hmin⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  have hlow := qf_ge_of_diagonalisation hP hHP (fun a => hmin a (Finset.mem_univ a))
  set ψ : C → ℝ := fun x => P x a0
  have hnorm : ψ ⬝ᵥ ψ = 1 := by
    have := congrFun (congrFun hP a0) a0
    simpa [Matrix.mul_apply, dotProduct, ψ] using this
  have heig : H *ᵥ ψ = lam a0 • ψ := by
    funext x
    have := congrFun (congrFun hHP x) a0
    simp only [Matrix.mul_apply, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ,
      ite_true] at this
    simpa [mulVec, dotProduct, ψ, mul_comm] using this
  have hq : qf H ψ = lam a0 := by
    unfold qf; rw [heig, dotProduct_smul, hnorm, smul_eq_mul, mul_one]
  refine ⟨ψ, ⟨fun h0 => by rw [h0] at hnorm; simp at hnorm, fun φ => ?_⟩, hnorm⟩
  rw [hq, hnorm, mul_one]; exact hlow φ

/-- The ground-state energy. -/
noncomputable def gsEnergy [Nonempty C] (H : Matrix C C ℝ) : ℝ :=
  if hS : H.IsSymm then qf H (Classical.choose (exists_groundState hS)) else 0

omit [DecidableEq C] in
theorem gsEnergy_le [Nonempty C] {H : Matrix C C ℝ} (hS : H.IsSymm) {φ : C → ℝ} (hφ : φ ⬝ᵥ φ = 1) :
    gsEnergy H ≤ qf H φ := by
  obtain ⟨hg, hn⟩ := Classical.choose_spec (exists_groundState hS)
  have := hg.2 φ
  rw [hn, mul_one, hφ, mul_one] at this
  simpa [gsEnergy, hS] using this

omit [DecidableEq C] in
theorem qf_groundState_eq [Nonempty C] {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ}
    (hψ : IsGroundState H ψ) (hn : ψ ⬝ᵥ ψ = 1) : qf H ψ = gsEnergy H := by
  apply le_antisymm
  · obtain ⟨hg, hn0⟩ := Classical.choose_spec (exists_groundState hS)
    have := hψ.2 (Classical.choose (exists_groundState hS))
    rw [hn, hn0, mul_one, mul_one] at this
    simpa [gsEnergy, hS] using this
  · exact gsEnergy_le hS hn

omit [DecidableEq C] in
theorem isGroundState_of_qf_eq [Nonempty C] {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ}
    (hn : ψ ⬝ᵥ ψ = 1) (hq : qf H ψ = gsEnergy H) : IsGroundState H ψ := by
  refine ⟨fun h0 => by rw [h0] at hn; simp at hn, fun φ => ?_⟩
  rw [hq, hn, mul_one]
  by_cases hφ : φ ⬝ᵥ φ = 0
  · have : φ = 0 := dotProduct_self_eq_zero.mp hφ
    subst this; simp [hφ, qf]
  · have hpos : 0 < φ ⬝ᵥ φ := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm hφ)
    set r := Real.sqrt (φ ⬝ᵥ φ)
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hrr : r * r = φ ⬝ᵥ φ := Real.mul_self_sqrt hpos.le
    have hn' : (r⁻¹ • φ) ⬝ᵥ (r⁻¹ • φ) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hrr]; field_simp
    have := gsEnergy_le hS hn'
    unfold qf at this ⊢
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    have h2 : gsEnergy H * (r * r) ≤ φ ⬝ᵥ (H *ᵥ φ) := by
      have := mul_le_mul_of_nonneg_right this (mul_self_nonneg r)
      calc gsEnergy H * (r * r) ≤ r⁻¹ * (r⁻¹ * (φ ⬝ᵥ (H *ᵥ φ))) * (r * r) := this
        _ = φ ⬝ᵥ (H *ᵥ φ) := by field_simp
    rw [← hrr]; linarith

end DFT
