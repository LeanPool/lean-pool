/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.HK.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
meta import Mathlib.Tactic.Abel
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.LinearCombination
meta import Mathlib.Tactic.Ring

/-!
# Gapped ground states and invisible potential directions

* `unique_of_gap`: a gapped ground state is unique up to scale.
* `persist_of_gap`: if `W = Σ_i w_i n_i` is constant on the support of a gapped ground state, the
  state remains the ground state of `H(v + ε w)` for all `|ε| · max|W − κ| ≤ gap` (both signs of
  `ε`).
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

omit [DecidableEq C] in
lemma decomp {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ} (hN : ψ ⬝ᵥ ψ = 1)
    (hE : H *ᵥ ψ = (qf H ψ) • ψ) (φ : C → ℝ) :
    ψ ⬝ᵥ (φ - (ψ ⬝ᵥ φ) • ψ) = 0 ∧
    φ ⬝ᵥ φ = (ψ ⬝ᵥ φ) ^ 2 + (φ - (ψ ⬝ᵥ φ) • ψ) ⬝ᵥ (φ - (ψ ⬝ᵥ φ) • ψ) ∧
    qf H φ = (ψ ⬝ᵥ φ) ^ 2 * qf H ψ + qf H (φ - (ψ ⬝ᵥ φ) • ψ) := by
  set a := ψ ⬝ᵥ φ
  set χ := φ - a • ψ with hχ
  have hφ : φ = a • ψ + χ := by rw [hχ]; abel
  have h0 : ψ ⬝ᵥ χ = 0 := by
    rw [hχ, dotProduct_sub, dotProduct_smul, hN, smul_eq_mul]; ring
  -- ψ ⬝ (H χ) = (H ψ) ⬝ χ by symmetry
  have hsym : ψ ⬝ᵥ (H *ᵥ χ) = (H *ᵥ ψ) ⬝ᵥ χ := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq]
  refine ⟨h0, ?_, ?_⟩
  · conv_lhs => rw [hφ]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, hN,
        h0,
      dotProduct_comm χ ψ]
    ring
  · have hχψ : χ ⬝ᵥ (H *ᵥ ψ) = 0 := by rw [hE, dotProduct_smul, dotProduct_comm, h0, smul_zero]
    have hψχ : ψ ⬝ᵥ (H *ᵥ χ) = 0 := by rw [hsym, hE, smul_dotProduct, h0, smul_zero]
    have hq : qf H ψ = ψ ⬝ᵥ (H *ᵥ ψ) := rfl
    unfold qf
    conv_lhs => rw [hφ]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hχψ, hψχ, ← hq]
    ring

omit [DecidableEq C] in
lemma dot_self_nonneg (χ : C → ℝ) : 0 ≤ χ ⬝ᵥ χ := by
  simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

omit [DecidableEq C] in
/-- A ground state with a spectral gap `g > 0` (in the variational sense) is unique up to scale. -/
theorem unique_of_gap {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ} (hψ : IsGroundState H ψ)
    (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf H ψ + g) * (χ ⬝ᵥ χ) ≤ qf H χ)
    {φ : C → ℝ} (hφ : IsGroundState H φ) : φ = (ψ ⬝ᵥ φ) • ψ := by
  classical
  have hE : H *ᵥ ψ = (qf H ψ) • ψ := by
    have := isGroundState_eigen hS hψ; rwa [hN, div_one] at this
  obtain ⟨h0, hn, hq⟩ := decomp hS hN hE φ
  set χ := φ - (ψ ⬝ᵥ φ) • ψ
  have h1 := hφ.2 ψ
  have h2 := hgap χ h0
  rw [hN, mul_one, hq, hn] at h1
  have hχ : χ ⬝ᵥ χ = 0 := by nlinarith [dot_self_nonneg χ]
  have : χ = 0 := dotProduct_self_eq_zero.mp hχ
  rw [sub_eq_zero] at this; exact this

/-- Variational spectral gap `g` above the normalised state `ψ`. -/
def HasGap (H : Matrix C C ℝ) (ψ : C → ℝ) (g : ℝ) : Prop :=
  ∀ χ, ψ ⬝ᵥ χ = 0 → (qf H ψ + g) * (χ ⬝ᵥ χ) ≤ qf H χ

/-- The ground state persists under an invisible perturbation, with gap reduced by at most
`|ε| * m`. -/
theorem persist_gap {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {v w : V → ℝ}
    {ψ : C → ℝ} (hψ : IsGroundState (hamN H0 n v) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g κ m ε : ℝ}
    (hgap : HasGap (hamN H0 n v) ψ g)
    (hsupp : ∀ c, ψ c ≠ 0 → ∑ i, w i * n i c = κ)
    (hm : ∀ c, |∑ i, w i * n i c - κ| ≤ m) (hε : |ε| * m ≤ g) :
    IsGroundState (hamN H0 n (v + ε • w)) ψ ∧
      HasGap (hamN H0 n (v + ε • w)) ψ (g - |ε| * m) := by
  set H := hamN H0 n v
  have hS : H.IsSymm := hamN_isSymm hH0 n v
  have hE : H *ᵥ ψ = (qf H ψ) • ψ := by
    have := isGroundState_eigen hS hψ; rwa [hN, div_one] at this
  set W : C → ℝ := fun c => ∑ i, w i * n i c
  have hsplit : ∀ φ : C → ℝ,
      qf (hamN H0 n (v + ε • w)) φ = qf H φ + ε * (κ * (φ ⬝ᵥ φ) + ∑ c, (W c - κ) * φ c ^ 2) := by
    intro φ
    have e1 : ∑ i, w i * dens n φ i = ∑ c, W c * φ c ^ 2 := dens_weighted n w φ
    have e2 : ∑ c, W c * φ c ^ 2 = κ * (φ ⬝ᵥ φ) + ∑ c, (W c - κ) * φ c ^ 2 := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro c _; ring
    rw [qf_hamN_add, dotProduct, e1, e2]
  -- pointwise: (W c - κ) ψ c = 0
  have hz : ∀ c, (W c - κ) * ψ c = 0 := by
    intro c; by_cases h : ψ c = 0
    · simp [h]
    · simp [W, hsupp c h]
  have hWψ : ∑ c, (W c - κ) * ψ c ^ 2 = 0 :=
    Finset.sum_eq_zero (fun c _ => by have := hz c; linear_combination ψ c * this)
  have hbound (χ : C → ℝ) : |∑ c, (W c - κ) * χ c ^ 2| ≤ m * (χ ⬝ᵥ χ) := by
    calc |∑ c, (W c - κ) * χ c ^ 2| ≤ ∑ c, |(W c - κ) * χ c ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, m * (χ c * χ c) := by
          apply Finset.sum_le_sum; intro c _
          rw [abs_mul, abs_of_nonneg (sq_nonneg (χ c)), sq]
          exact mul_le_mul_of_nonneg_right (hm c) (mul_self_nonneg _)
      _ = m * (χ ⬝ᵥ χ) := by simp [dotProduct, Finset.mul_sum]
  have hεW (χ : C → ℝ) :
      -(|ε| * m * (χ ⬝ᵥ χ)) ≤ ε * ∑ c, (W c - κ) * χ c ^ 2 := by
    have h := abs_le.mp (hbound χ)
    rcases le_total 0 ε with he | he
    · rw [abs_of_nonneg he]; nlinarith [h.1, dot_self_nonneg χ]
    · rw [abs_of_nonpos he]; nlinarith [h.2, dot_self_nonneg χ]
  refine ⟨⟨hψ.1, fun φ => ?_⟩, fun χ hχ => ?_⟩
  · obtain ⟨h0, hn, hq⟩ := decomp hS hN hE φ
    set a := ψ ⬝ᵥ φ
    set χ := φ - a • ψ with hχ
    -- the W-term only sees χ
    have hWφ : ∑ c, (W c - κ) * φ c ^ 2 = ∑ c, (W c - κ) * χ c ^ 2 := by
      apply Finset.sum_congr rfl; intro c _
      have : φ c = a * ψ c + χ c := by simp [hχ]
      rw [this]; have := hz c; linear_combination (a ^ 2 * ψ c + 2 * a * χ c) * this
    have hg := hgap χ h0
    have hperturbation := mul_le_mul_of_nonneg_right hε (dot_self_nonneg χ)
    rw [hsplit, hsplit, hWψ, hWφ, hN, mul_one, hn, hq]
    nlinarith only [hg, hεW χ, hperturbation]
  · have hg := hgap χ hχ
    rw [hsplit, hsplit, hWψ, hN]
    nlinarith only [hg, hεW χ]

/-- Invisible direction around a gapped ground state (both signs of ε). -/
theorem persist_of_gap {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {v w : V → ℝ}
    {ψ : C → ℝ} (hψ : IsGroundState (hamN H0 n v) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g κ m ε : ℝ}
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamN H0 n v) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamN H0 n v) χ)
    (hsupp : ∀ c, ψ c ≠ 0 → ∑ i, w i * n i c = κ)
    (hm : ∀ c, |∑ i, w i * n i c - κ| ≤ m) (hε : |ε| * m ≤ g) :
    IsGroundState (hamN H0 n (v + ε • w)) ψ :=
  (persist_gap hH0 hψ hN hgap hsupp hm hε).1

end

end DFT
