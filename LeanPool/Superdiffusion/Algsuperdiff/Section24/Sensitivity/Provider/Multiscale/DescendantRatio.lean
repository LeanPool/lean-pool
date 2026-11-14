/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Series

/-!
# DescendantRatio

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Per-cube ratio aggregation for the lower coarse-grained ellipticity

The conditional sensitivity estimate for `lambda_{s,q}` is obtained by applying
a *one-cube* estimate to every triadic descendant `z + cube_n` of the unit cube
and then aggregating.  The aggregation step is purely structural: if the
one-cube observable `|sigma_*^{-1}|` of the perturbed field is bounded by a
fixed factor `rho` times that of the base field on every descendant, then the
same factor passes to the multiscale aggregate `lambda_{s,q}^{-1}` for every `s
> 0` and every admissible `q`, including the endpoint `q = infinity`.

This is the exact replacement for the source's differentiation of
`lambda_{s,q}^{-1}` in the perturbation parameter: the aggregate is an infinite
weighted aggregate of finite maxima and is never claimed to be classically
differentiable.  Only per-cube ratio estimates enter.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.  The hypothesis `hdesc` is the per-cube analytic input supplied by
the neighbouring modules; it must be discharged at every application.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Bridge between CoarseGraining's explicit `Real.rpow` applications and the `^`
notation used by Mathlib's `rpow` lemmas. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

omit [NeZero d] in
/-- A per-descendant ratio estimate passes to the finite descendant maxima. -/
theorem maxDescendantSigmaStarInv_le_of_descendant_ratio
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {k : ℤ} (hk : k ≤ Q.scale)
    (hdesc : ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm R A₁ ≤ ρ * coarseSigmaStarInvMatrixNorm R A₀) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k A₁ ≤
      ρ * maxDescendantSigmaStarInvMatrixNormAtScale Q k A₀ := by
  refine finsetSupReal_le _ (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  refine (hdesc R hR).trans (mul_le_mul_of_nonneg_left ?_ hρ)
  exact coarseSigmaStarInvMatrixNorm_le_maxDescendantNorm_atScale
    A₀ hR

/-- Finite-exponent ratio aggregation. -/
theorem lambdaSqFinite_inv_le_of_descendant_ratio
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {ρ s q : ℝ}
    (hρ : 0 ≤ ρ) (hs : 0 < s) (hq : 1 ≤ q)
    (hdesc : ∀ (k : ℤ), k ≤ Q.scale → ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm R A₁ ≤ ρ * coarseSigmaStarInvMatrixNorm R A₀) :
    (Ch02.lambdaSq Q s (.finite q) A₁)⁻¹ ≤ ρ * (Ch02.lambdaSq Q s (.finite q) A₀)⁻¹ := by
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hp : (0 : ℝ) < q / 2 := by positivity
  have hsq : (0 : ℝ) ≤ s * q := mul_nonneg hs.le hqpos.le
  set X : ℝ := (Ch02.lambdaSq Q s (.finite q) A₁)⁻¹ with hX
  set Y : ℝ := (Ch02.lambdaSq Q s (.finite q) A₀)⁻¹ with hY
  have hX0 : 0 ≤ X := inv_nonneg.mpr (lambdaSq_finite_nonneg Q A₁ hs hq)
  have hY0 : 0 ≤ Y := inv_nonneg.mpr (lambdaSq_finite_nonneg Q A₀ hs hq)
  -- The `(-q/2)`-power of `lambdaSq` is the `(q/2)`-power of its inverse.
  have hpow : ∀ A : TriadicCoeffFamily d,
      ((Ch02.lambdaSq Q s (.finite q) A)⁻¹) ^ (q / 2) =
        ∑' n : ℕ, Ch02.geometricWeight s q n *
          (maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) A) ^ (q / 2) := by
    intro A
    have hser := lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s q A hqpos hsq
    simp only [rpow_eq_pow] at hser
    rw [← hser, show (-q / 2 : ℝ) = -(q / 2) by ring,
      Real.rpow_neg (lambdaSq_finite_nonneg Q A hs hq),
      Real.inv_rpow (lambdaSq_finite_nonneg Q A hs hq)]
  have hsum0 := summable_sigmaStarInv_series_pointwiseCoeffField Q A₀ hs hqpos
  have hsum1 := summable_sigmaStarInv_series_pointwiseCoeffField Q A₁ hs hqpos
  simp only [rpow_eq_pow] at hsum0 hsum1
  have hterm : ∀ n : ℕ,
      Ch02.geometricWeight s q n *
          (maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) A₁) ^ (q / 2) ≤
        ρ ^ (q / 2) * (Ch02.geometricWeight s q n *
          (maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) A₀) ^ (q / 2)) := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hmax := maxDescendantSigmaStarInv_le_of_descendant_ratio Q A₀ A₁ hρ hk
      (hdesc (Q.scale - (n : ℤ)) hk)
    have hM0 : 0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀ :=
      maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk A₀
    have hM1 : 0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ :=
      maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk A₁
    have hw : 0 ≤ Ch02.geometricWeight s q n := by
      simpa [geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_nonneg n hsq
    have hrpow :
        (maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) A₁) ^ (q / 2) ≤
          ρ ^ (q / 2) *
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A₀) ^ (q / 2) := by
      rw [← Real.mul_rpow hρ hM0]
      exact Real.rpow_le_rpow hM1 hmax hp.le
    calc Ch02.geometricWeight s q n *
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A₁) ^ (q / 2)
        ≤ Ch02.geometricWeight s q n * (ρ ^ (q / 2) *
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A₀) ^ (q / 2)) :=
          mul_le_mul_of_nonneg_left hrpow hw
      _ = ρ ^ (q / 2) * (Ch02.geometricWeight s q n *
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A₀) ^ (q / 2)) := by ring
  have hcompare : X ^ (q / 2) ≤ (ρ * Y) ^ (q / 2) := by
    rw [Real.mul_rpow hρ hY0, hX, hY, hpow A₁, hpow A₀]
    calc (∑' n : ℕ, Ch02.geometricWeight s q n *
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A₁) ^ (q / 2))
        ≤ ∑' n : ℕ, ρ ^ (q / 2) * (Ch02.geometricWeight s q n *
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A₀) ^ (q / 2)) :=
          Summable.tsum_le_tsum hterm hsum1 (hsum0.mul_left _)
      _ = ρ ^ (q / 2) * ∑' n : ℕ, Ch02.geometricWeight s q n *
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A₀) ^ (q / 2) := hsum0.tsum_mul_left _
  -- Undo the `(q/2)`-power.
  have hρY : 0 ≤ ρ * Y := mul_nonneg hρ hY0
  have hinvpow : ∀ z : ℝ, 0 ≤ z → (z ^ (q / 2)) ^ (2 / q) = z := by
    intro z hz
    rw [← Real.rpow_mul hz, show q / 2 * (2 / q) = 1 by field_simp]
    exact Real.rpow_one z
  calc X = (X ^ (q / 2)) ^ (2 / q) := (hinvpow X hX0).symm
    _ ≤ ((ρ * Y) ^ (q / 2)) ^ (2 / q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hcompare (by positivity)
    _ = ρ * Y := hinvpow (ρ * Y) hρY

/-- Endpoint (`q = infinity`) ratio aggregation. -/
theorem lambdaSqInfinity_inv_le_of_descendant_ratio
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {ρ s : ℝ}
    (hρ : 0 ≤ ρ) (hs : 0 < s)
    (hdesc : ∀ (k : ℤ), k ≤ Q.scale → ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm R A₁ ≤ ρ * coarseSigmaStarInvMatrixNorm R A₀) :
    (Ch02.lambdaSq Q s .infinity A₁)⁻¹ ≤ ρ * (Ch02.lambdaSq Q s .infinity A₀)⁻¹ := by
  set S : TriadicCoeffFamily d → Set ℝ := fun A =>
    { M : ℝ | ∃ n : ℕ, M = Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A } with hS
  have hval : ∀ A : TriadicCoeffFamily d,
      (Ch02.lambdaSq Q s .infinity A)⁻¹ = sSup (S A) := by
    intro A
    rw [Ch02.lambdaSq_infinity]
    change ((sSup (S A))⁻¹)⁻¹ = sSup (S A)
    exact inv_inv _
  have hbdd0 : BddAbove (S A₀) := lambdaSqInfinity_denominator_valueSet_bddAbove Q A₀ hs.le
  have hne1 : (S A₁).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  rw [hval A₁, hval A₀]
  refine csSup_le hne1 ?_
  rintro _ ⟨n, rfl⟩
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hmax := maxDescendantSigmaStarInv_le_of_descendant_ratio Q A₀ A₁ hρ hk
    (hdesc (Q.scale - (n : ℤ)) hk)
  have hweight : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmem : Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀ ∈ S A₀ :=
    ⟨n, rfl⟩
  calc Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁
      ≤ Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          (ρ * maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀) :=
        mul_le_mul_of_nonneg_left hmax hweight
    _ = ρ * (Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀) := by ring
    _ ≤ ρ * sSup (S A₀) := mul_le_mul_of_nonneg_left (le_csSup hbdd0 hmem) hρ

/-- **Per-cube ratio aggregation.**  A uniform per-descendant ratio bound on the
one-cube observable `|sigma_*^{-1}|` transfers verbatim to the multiscale
aggregate `lambda_{s,q}^{-1}`, for every `s > 0` and every admissible `q`
(finite or the endpoint `infinity`).  This is the aggregation step of the
conditional `lambda_{s,q}` sensitivity estimate. -/
theorem lambdaSq_inv_le_of_descendant_ratio
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {ρ s : ℝ}
    {q : Ch02.MultiscaleExponent} (hρ : 0 ≤ ρ) (hs : 0 < s) (hq : q.IsAdmissible)
    (hdesc : ∀ (k : ℤ), k ≤ Q.scale → ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm R A₁ ≤ ρ * coarseSigmaStarInvMatrixNorm R A₀) :
    (Ch02.lambdaSq Q s q A₁)⁻¹ ≤ ρ * (Ch02.lambdaSq Q s q A₀)⁻¹ := by
  cases q with
  | finite q => exact lambdaSqFinite_inv_le_of_descendant_ratio Q A₀ A₁ hρ hs hq hdesc
  | infinity => exact lambdaSqInfinity_inv_le_of_descendant_ratio Q A₀ A₁ hρ hs hdesc

end

end Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
