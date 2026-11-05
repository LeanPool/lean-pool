/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Moments

/-!
# P4UpperMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Upper-envelope moments for the genuine cutoff

The random upper ellipticity envelope is a polynomial in the nonnegative local
cutoff control.  This module first exposes every finite polynomial moment of `1
+ cutoffLocalControl`; later assembly may use it only through the proved
samplewise bound.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-- Every natural power of the nonnegative cutoff local control is integrable
under its actual lower-tail law. -/
theorem integrable_cutoffLocalControl_pow (M : ABKModel d) (ell m : ℤ)
    (p : ℕ) :
    Integrable (fun omega : CutoffSample d => cutoffLocalControl ell m omega ^ p)
      (cutoffSampleLaw M).toMeasure := by
  by_cases hp : p = 0
  · subst p
    simp
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
  have hmoment := hasGammaMomentGrowthWith_cutoffLocalControl M ell m hp_one
  simpa only [abs_of_nonneg (cutoffLocalControl_nonneg ell m _),
    Real.rpow_natCast] using hmoment.1

/-- Every natural power of `1 + cutoffLocalControl` is integrable.  The proof
uses the finite binomial expansion, so no informal closure-under-polynomials
principle is assumed. -/
theorem integrable_one_add_cutoffLocalControl_pow (M : ABKModel d) (ell m : ℤ)
    (p : ℕ) :
    Integrable (fun omega : CutoffSample d =>
      (1 + cutoffLocalControl ell m omega) ^ p) (cutoffSampleLaw M).toMeasure := by
  let f : ℕ → CutoffSample d → ℝ := fun j omega =>
    cutoffLocalControl ell m omega ^ (p - j) * (p.choose j : ℝ)
  have hf : ∀ j ∈ Finset.range (p + 1), Integrable (f j) (cutoffSampleLaw M).toMeasure := by
    intro j _hj
    have hterm := integrable_cutoffLocalControl_pow M ell m (p - j)
    simpa only [f] using hterm.mul_const (p.choose j : ℝ)
  have hfun : (fun omega : CutoffSample d => (1 + cutoffLocalControl ell m omega) ^ p) =
      fun omega => ∑ j ∈ Finset.range (p + 1), f j omega := by
    funext omega
    rw [add_pow]
    simp only [one_pow, one_mul, f]
  rw [hfun]
  exact integrable_finsetSum (Finset.range (p + 1)) hf

/-- A deterministic polynomial majorant for the actual random upper
ellipticity constant on a cube.  It is deliberately stated in terms of the
same local control that has the Γ₂ tail. -/
noncomputable def cutoffUpperEllipticityMajorant (M : ABKModel d) : ℝ :=
  ((d : ℝ) * (d : ℝ) * (M.nu + 1) ^ 2 + M.nu ^ 2) / M.nu

theorem coefficientCutoffCubeEllipticityUpper_le_majorant
    (M : ABKModel d) (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) :
    coefficientCutoffCubeEllipticityUpper M m omega Q ≤
      cutoffUpperEllipticityMajorant M *
        (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 := by
  let u : ℝ := cutoffLocalControl (cubeOriginCoverScale Q) m omega
  have hu : 0 ≤ u := cutoffLocalControl_nonneg _ _ _
  have hnu : 0 < M.nu := M.nu_pos
  have hd : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hbase : M.nu + u ≤ (M.nu + 1) * (1 + u) := by
    nlinarith [mul_nonneg hnu.le hu]
  have hleft : 0 ≤ M.nu + u := by positivity
  have hright : 0 ≤ (M.nu + 1) * (1 + u) := by positivity
  have hsq : (M.nu + u) ^ 2 ≤ ((M.nu + 1) * (1 + u)) ^ 2 :=
    (sq_le_sq₀ hleft hright).mpr hbase
  have hone : 1 ≤ (1 + u) ^ 2 := by
    nlinarith [sq_nonneg u]
  unfold coefficientCutoffCubeEllipticityUpper cutoffUpperEllipticityMajorant
  dsimp only [u] at hu hbase hleft hright hsq hone ⊢
  have hnum :
    (d : ℝ) * (d : ℝ) *
        (M.nu + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 + M.nu ^ 2
        ≤ ((d : ℝ) * (d : ℝ) * (M.nu + 1) ^ 2 + M.nu ^ 2) *
          (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 := by
    calc
      (d : ℝ) * (d : ℝ) *
          (M.nu + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 + M.nu ^ 2
          ≤ (d : ℝ) * (d : ℝ) *
          ((M.nu + 1) * (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega)) ^ 2 +
            M.nu ^ 2 := by
          gcongr
      _ = (d : ℝ) * (d : ℝ) * (M.nu + 1) ^ 2 *
          (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 + M.nu ^ 2 := by
          ring
      _ ≤ (d : ℝ) * (d : ℝ) * (M.nu + 1) ^ 2 *
          (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 +
            M.nu ^ 2 * (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 := by
          gcongr
          simpa using mul_le_mul_of_nonneg_left hone (sq_nonneg M.nu)
      _ = ((d : ℝ) * (d : ℝ) * (M.nu + 1) ^ 2 + M.nu ^ 2) *
          (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 := by
          ring
  calc
    ((d : ℝ) * (d : ℝ) *
        (M.nu + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 + M.nu ^ 2) / M.nu
        ≤ (((d : ℝ) * (d : ℝ) * (M.nu + 1) ^ 2 + M.nu ^ 2) *
          (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2) / M.nu :=
      (div_le_div_iff_of_pos_right hnu).mpr hnum
    _ = ((d : ℝ) * (d : ℝ) * (M.nu + 1) ^ 2 + M.nu ^ 2) / M.nu *
        (1 + cutoffLocalControl (cubeOriginCoverScale Q) m omega) ^ 2 := by
      field_simp [hnu.ne']

/-- Every finite moment of the realised upper ellipticity constant on a fixed cube
is integrable.  This is the exact Γ₂-to-polynomial step required for the upper
`(P4)` moment. -/
theorem integrable_coefficientCutoffCubeEllipticityUpper_pow
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) (p : ℕ) :
    Integrable (fun omega : CutoffSample d =>
      coefficientCutoffCubeEllipticityUpper M m omega Q ^ p)
      (cutoffSampleLaw M).toMeasure := by
  let u : CutoffSample d → ℝ := fun omega =>
    cutoffLocalControl (cubeOriginCoverScale Q) m omega
  let K : ℝ := cutoffUpperEllipticityMajorant M
  have hK_nonneg : 0 ≤ K := by
    dsimp [K, cutoffUpperEllipticityMajorant]
    apply div_nonneg
    · positivity
    · exact M.nu_pos.le
  have hdom : Integrable (fun omega : CutoffSample d =>
      K ^ p * (1 + u omega) ^ (2 * p)) (cutoffSampleLaw M).toMeasure := by
    have hbase := integrable_one_add_cutoffLocalControl_pow M
      (cubeOriginCoverScale Q) m (2 * p)
    exact hbase.const_mul (K ^ p)
  refine Integrable.mono' hdom
    ((measurable_coefficientCutoffCubeEllipticityUpper M m Q).pow_const p).aestronglyMeasurable ?_
  filter_upwards with omega
  have hu : 0 ≤ u omega := cutoffLocalControl_nonneg _ _ _
  have hL_nonneg : 0 ≤ coefficientCutoffCubeEllipticityUpper M m omega Q := by
    unfold coefficientCutoffCubeEllipticityUpper
    apply div_nonneg
    · positivity
    · exact M.nu_pos.le
  have hmajor := coefficientCutoffCubeEllipticityUpper_le_majorant M m omega Q
  have hbase : coefficientCutoffCubeEllipticityUpper M m omega Q ≤
      K * (1 + u omega) ^ 2 := by
    simpa only [u, K] using hmajor
  have hpw := pow_le_pow_left₀ hL_nonneg hbase p
  have hright_nonneg : 0 ≤ K ^ p * (1 + u omega) ^ (2 * p) := by positivity
  have hrewrite : (K * (1 + u omega) ^ 2) ^ p =
      K ^ p * (1 + u omega) ^ (2 * p) := by
    rw [mul_pow]
    rw [← pow_mul]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL_nonneg p),
    abs_of_nonneg hright_nonneg, hrewrite] using hpw

end

end Algsuperdiff.Section3.Cutoff
