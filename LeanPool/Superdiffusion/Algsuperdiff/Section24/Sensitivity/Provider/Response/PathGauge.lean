/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Spine
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CrudeBound

/-!
# PathGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform control of the coarse gauge along the perturbation segment

The `J` sensitivity estimate applies the `D_h` bound at *every* point `t` of the
segment `a + t h`, `t ∈ [0,1]`, but its statement involves only the coarse gauge
`lambda_{3/8,2}^{-1}` of the **base** coefficient.  The source closes this gap
by quoting the conditional `lambda` sensitivity estimate along the segment; in
the present formalization the same content is produced directly by the
self-referential bootstrap of `Provider.Lambda.Bootstrap`, which shows that
under the frozen smallness gate the coarse gauge never more than doubles along
the segment.

The single analytic input is `hcube`, the `p = 0` specialization of the `D_h`
bound on every triadic descendant of the unit cube with the *root* gauge as
coefficient — exactly the `hcube` premise of
`Provider.Lambda.Spine.unitCubeLambda_inv_perturb_le_of_cube_dhFluxForm_bound`.
It is a premise here and is discharged where this lemma is used.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Response

open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The coarse gauge at most doubles along the perturbation segment.**

Given the per-descendant pure-flux `D_h` bound with the root gauge as
coefficient (`hcube`) and the smallness gate `4 K lambda^{-1}(a) ≤ 1/2`, the
coarse gauge `lambda_{3/8,2}^{-1}` at every point of the segment `a + tau h`,
`tau ∈ [0,1]`, is at most twice its value at the base point.

This is the bootstrap conclusion `Psi tau ≤ Psi 0 / (1 - 4 K Psi 0)` of
`Provider.Lambda.Bootstrap.le_riccati_of_ratio_engine` fed by the ratio engine
of `Provider.Lambda.Engine`; the crude a-priori bound needed to run the engine
is discharged here by `Provider.Lambda.CrudeBound`. -/
theorem pathGauge_le_two_mul_of_cube_dhFluxForm_bound [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) {K : ℝ} (hK : 0 ≤ K)
    (hcube : ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      ∀ k : ℤ, ∀ hk : k ≤ (originCube d 0).scale,
        ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtScale (originCube d 0) k,
          ∀ (τ : ℝ) (w : Vec d),
            |dhFluxForm (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR h) τ) (descendantField hk hR h) w| ≤
              2 * (K * pathGauge a h τ) * responseJ (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR h) τ) 0 w)
    (hsmall : 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤ 1 / 2)
    (τ : ℝ) (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) :
    pathGauge a h τ ≤ 2 * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by
  have hgauge0 : pathGauge a h 0 = (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
    pathGauge_zero a h
  have hΨ : ∀ t, 0 ≤ pathGauge a h t := pathGauge_nonneg a h
  obtain ⟨B, hB0, hB⟩ := exists_crude_pathGauge_bound a h
  have hengine : ∀ t₁ t₂ C : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 →
      (∀ σ, t₁ ≤ σ → σ ≤ t₂ → pathGauge a h σ ≤ C) →
      pathGauge a h t₂ ≤ Real.exp (K * C * (t₂ - t₁)) * pathGauge a h t₁ := by
    intro t₁ t₂ C h1 h12 h2 hC
    have := pathLambdaInv_ratio_engine dimension a h (K := K)
      (s := (3 / 8 : ℝ)) (q := .finite 2) (by norm_num)
      (by simp [Ch02.MultiscaleExponent.IsAdmissible]) hcube t₁ t₂ C h1 h12 h2 hK hC
    rwa [pathLambdaInv_gauge] at this
  have hstrict : 4 * K * pathGauge a h 0 < 1 := by rw [hgauge0]; linarith
  have hric := le_riccati_of_ratio_engine hΨ hK hB0 hB hengine hstrict hτ₀ hτ₁
  rw [hgauge0] at hric
  refine hric.trans ?_
  have hLnn : (0 : ℝ) ≤ (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by
    rw [← hgauge0]; exact hΨ 0
  have hpos : (0 : ℝ) < 1 - 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by
    linarith
  rw [div_le_iff₀ hpos]
  nlinarith [hsmall, hLnn, hK]

end

end Algsuperdiff.Section24.Sensitivity.Provider.Response
