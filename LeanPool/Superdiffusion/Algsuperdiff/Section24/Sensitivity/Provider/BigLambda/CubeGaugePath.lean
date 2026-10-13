/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Response.PathGauge

/-!
# CubeGaugePath

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Descendant-gauge control along the perturbation path

Source: ABK26, the scaled-norm inequalities that precede the descendant
`b`-matrix estimate.

The pure-potential `D_h` bound of `BigLambda.CubePotentialDh` prices its Term A
against the **descendant** gauge `λ_{3/8,2}^{-1}(R; a + τh)`, so the
Young/Grönwall absorption at the cube `R` needs that gauge to stay comparable to
its value at the base point `τ = 0`.

The proof does **not** rerun the `lambda_{s,q}` spine at `R`: it reuses the
per-descendant pure-flux estimate `Provider.Lambda.abs_dhFluxForm_le_root_gauge`
(which already prices everything against the *root* gauge), turns it into the
per-cube response ratio with `Provider.Lambda.Engine`, converts that into the
one-cube `σ_*^{-1}` ratio with `Provider.Lambda.DescendantBridge`, and finally
aggregates *at `R`* with the general-cube
`Provider.Multiscale.lambdaSq_inv_le_of_descendant_ratio`.  The aggregation is
legitimate because every descendant of `R` is a descendant of the unit cube
(`Homogenization.mem_descendantsAtScale_trans`).

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open Algsuperdiff.Section24.Sensitivity.Provider.Response
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The flux-based threshold constant for the cube gauge estimate. -/
def gaugeGateConst (d : ℕ) [NeZero d] : ℝ := 8 * fluxSpineConst d

theorem gaugeGateConst_pos (d : ℕ) [NeZero d] : 0 < gaugeGateConst d := by
  have := fluxSpineConst_pos d
  unfold gaugeGateConst
  positivity


/-- The frozen gate in multiplicative form. -/
theorem gate_mul_lambdaSq_inv_le [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (gaugeGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a) :
    h.gradientW1Infinity * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤
      (8 * fluxSpineConst d)⁻¹ := by
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  have hLinvnn : (0 : ℝ) ≤ (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
    (inv_pos.mpr hlampos).le
  have hstep := mul_le_mul_of_nonneg_right hgate hLinvnn
  rwa [gaugeGateConst, mul_assoc, mul_inv_cancel₀ hlampos.ne', mul_one] at hstep

/-- The pure-flux descendant `D_h` bound in the exact shape consumed by the
spine and by `Provider.Response.PathGauge`. -/
theorem dhFluxForm_root_gauge_bound [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d) :
    ∀ F' : Ch03.CoeffFamily d,
      CoeffOn.AEEq (F'.coeffOn (originCube d 0)) a →
      ∀ l : ℤ, ∀ hl : l ≤ (originCube d 0).scale,
        ∀ T : TriadicCube d, ∀ hT : T ∈ descendantsAtScale (originCube d 0) l,
          ∀ (σ : ℝ) (w : Vec d),
            |dhFluxForm (cubeDomain T)
                (perturbCoeffOn (cubeDomain T) (F'.coeffOn T)
                  (descendantField hl hT h.toLInfSkewMatrixFieldOn) σ)
                (descendantField hl hT h.toLInfSkewMatrixFieldOn) w| ≤
              2 * ((fluxSpineConst d * h.gradientW1Infinity) *
                  pathGauge a h.toLInfSkewMatrixFieldOn σ) *
                responseJ (cubeDomain T)
                  (perturbCoeffOn (cubeDomain T) (F'.coeffOn T)
                    (descendantField hl hT h.toLInfSkewMatrixFieldOn) σ) 0 w := by
  intro F' hF' l hl T hT σ w
  have := abs_dhFluxForm_le_root_gauge a h F' hF' hl hT σ w
  simpa [mul_assoc] using this

/-- The smallness gate in the shape consumed by the spine. -/
theorem four_mul_gate_le [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (gaugeGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a) :
    4 * (fluxSpineConst d * h.gradientW1Infinity) *
      (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤ 1 / 2 := by
  have hC₀pos : 0 < fluxSpineConst d := fluxSpineConst_pos d
  have hgateinv := gate_mul_lambdaSq_inv_le a h hgate
  have heq : 4 * (fluxSpineConst d * h.gradientW1Infinity) *
      (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ =
      (4 * fluxSpineConst d) * (h.gradientW1Infinity *
        (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) := by ring
  rw [heq]
  have h4 : (0 : ℝ) ≤ 4 * fluxSpineConst d := by positivity
  refine (mul_le_mul_of_nonneg_left hgateinv h4).trans (le_of_eq ?_)
  have hne : fluxSpineConst d ≠ 0 := hC₀pos.ne'
  have hcancel : fluxSpineConst d * (fluxSpineConst d)⁻¹ = 1 := mul_inv_cancel₀ hne
  rw [mul_inv]
  calc 4 * fluxSpineConst d * (8⁻¹ * (fluxSpineConst d)⁻¹)
      = (fluxSpineConst d * (fluxSpineConst d)⁻¹) * (4 * 8⁻¹) := by ring
    _ = 1 / 2 := by rw [hcancel]; norm_num

/-- **The root gauge at most doubles along the path.** -/
theorem pathGauge_le_two_mul_of_gate [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (gaugeGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    pathGauge a h.toLInfSkewMatrixFieldOn σ ≤
      2 * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by
  have hgnn : 0 ≤ h.gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have hKnn : (0 : ℝ) ≤ fluxSpineConst d * h.gradientW1Infinity :=
    mul_nonneg (fluxSpineConst_pos d).le hgnn
  exact pathGauge_le_two_mul_of_cube_dhFluxForm_bound dimension a
    h.toLInfSkewMatrixFieldOn hKnn (dhFluxForm_root_gauge_bound a h)
    (four_mul_gate_le a h hgate) σ hσ0 hσ1

/-- Descendants of the unit cube have side length at most one. -/
theorem cubeScaleFactor_le_one_of_mem_descendantsAtScale {k : ℤ}
    (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    cubeScaleFactor R ≤ 1 := by
  have hscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
  have hk0 : k ≤ 0 := by simpa using! hk
  have hrp : Real.rpow (3 : ℝ) ((k : ℝ)) = (3 : ℝ) ^ k := Real.rpow_intCast 3 k
  have hfac : cubeScaleFactor R = Real.rpow (3 : ℝ) ((k : ℝ)) := by
    rw [cubeScaleFactor, hscale]
    exact hrp.symm
  rw [hfac]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  exact_mod_cast hk0

/-- **Descendant-gauge doubling along the path.**

Under the frozen smallness gate, at every triadic descendant `R` of the unit
cube the coarse gauge at the endpoint `a + h` is at most twice its value at the
base point `a`. -/
theorem lambdaSq_inv_perturb_cube_le_two_mul [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (gaugeGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a)
    (F G : Ch03.CoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn τ))
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ ≤
      2 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set C₀ : ℝ := fluxSpineConst d with hC₀
  have hC₀pos : 0 < C₀ := fluxSpineConst_pos d
  have hgnn : 0 ≤ h.gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg h
  set K : ℝ := C₀ * h.gradientW1Infinity with hK
  have hKnn : 0 ≤ K := mul_nonneg hC₀pos.le hgnn
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  have hLinvnn : (0 : ℝ) ≤ (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
    (inv_pos.mpr hlampos).le
  -- the smallness gate in multiplicative form
  have hgateinv : h.gradientW1Infinity * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤
      (8 * C₀)⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_right hgate hLinvnn
    rwa [gaugeGateConst, ← hC₀, mul_assoc, mul_inv_cancel₀ hlampos.ne', mul_one] at hstep
  have hsmall : 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤ 1 / 2 := by
    have heq : 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ =
        (4 * C₀) * (h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) := by rw [hK]; ring
    rw [heq]
    have h4 : (0 : ℝ) ≤ 4 * C₀ := by positivity
    refine (mul_le_mul_of_nonneg_left hgateinv h4).trans (le_of_eq ?_)
    field_simp
    ring
  -- the descendant pure-flux `D_h` bound against the root gauge
  have hcube : ∀ F' : Ch03.CoeffFamily d,
      CoeffOn.AEEq (F'.coeffOn (originCube d 0)) a →
      ∀ l : ℤ, ∀ hl : l ≤ (originCube d 0).scale,
        ∀ T : TriadicCube d, ∀ hT : T ∈ descendantsAtScale (originCube d 0) l,
          ∀ (τ : ℝ) (w : Vec d),
            |dhFluxForm (cubeDomain T)
                (perturbCoeffOn (cubeDomain T) (F'.coeffOn T)
                  (descendantField hl hT g) τ) (descendantField hl hT g) w| ≤
              2 * (K * pathGauge a g τ) * responseJ (cubeDomain T)
                (perturbCoeffOn (cubeDomain T) (F'.coeffOn T)
                  (descendantField hl hT g) τ) 0 w := by
    intro F' hF' l hl T hT τ w
    have := abs_dhFluxForm_le_root_gauge a h F' hF' hl hT τ w
    rw [hK, hgdef]
    simpa [mul_assoc] using this
  -- the path gauge at most doubles
  set Cgauge : ℝ := 2 * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hCgauge
  have hpath : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → pathGauge a g σ ≤ Cgauge := fun σ h0 h1 =>
    pathGauge_le_two_mul_of_cube_dhFluxForm_bound dimension a g hKnn hcube hsmall σ h0 h1
  -- the ratio constant
  set ρ : ℝ := Real.exp (K * Cgauge * (τ - 0)) with hρdef
  have hρnn : 0 ≤ ρ := (Real.exp_pos _).le
  have hKC : K * Cgauge ≤ 1 / 2 := by
    have heq : K * Cgauge = (2 * C₀) *
        (h.gradientW1Infinity * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) := by
      rw [hK, hCgauge]; ring
    rw [heq]
    have h2 : (0 : ℝ) ≤ 2 * C₀ := by positivity
    have hstep := mul_le_mul_of_nonneg_left hgateinv h2
    have hval : (2 * C₀) * (8 * C₀)⁻¹ = 1 / 4 := by
      have hne : C₀ ≠ 0 := hC₀pos.ne'
      have hcancel : C₀ * C₀⁻¹ = 1 := mul_inv_cancel₀ hne
      rw [mul_inv]
      calc 2 * C₀ * (8⁻¹ * C₀⁻¹) = (C₀ * C₀⁻¹) * (2 * 8⁻¹) := by ring
        _ = 1 / 4 := by rw [hcancel]; norm_num
    linarith [hstep, hval]
  have hKCnn : 0 ≤ K * Cgauge := by
    have : (0 : ℝ) ≤ Cgauge := by rw [hCgauge]; positivity
    exact mul_nonneg hKnn this
  have hρ2 : ρ ≤ 2 := by
    rw [hρdef, sub_zero]
    refine ((Real.exp_le_exp.mpr ?_).trans exp_half_le_two)
    nlinarith [hKC, hKCnn, hτ0, hτ1]
  -- the per-descendant one-cube `σ_*^{-1}` ratio
  have hF0 : CoeffOn.AEEq (F.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a g 0) :=
    hF.trans (perturbCoeffOn_zero_aeeq a g).symm
  have hG1 : CoeffOn.AEEq (G.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ) := hG
  have hdesc : ∀ l : ℤ, l ≤ (originCube d 0).scale →
      ∀ T ∈ descendantsAtScale (originCube d 0) l,
        Ch02.coarseSigmaStarInvMatrixNorm T G ≤
          ρ * Ch02.coarseSigmaStarInvMatrixNorm T F := by
    intro l hl T hT
    refine coarseSigmaStarInvMatrixNorm_le_of_cube_responseJ_ratio a g 0 τ F F G
      hF hF0 hG1 hρnn hl hT ?_
    intro w
    refine responseJ_cube_ratio_of_dhFluxForm_bound dimension a g F hl hT w
      hτ0 ?_
    intro σ hσ0 hσ1
    refine (hcube F hF l hl T hT σ w).trans ?_
    have hJnn : (0 : ℝ) ≤ responseJ (cubeDomain T)
        (perturbCoeffOn (cubeDomain T) (F.coeffOn T) (descendantField hl hT g) σ) 0 w :=
      Ch02.responseJ_nonneg _ _ 0 w
    refine mul_le_mul_of_nonneg_right ?_ hJnn
    have := hpath σ hσ0 (le_trans hσ1 hτ1)
    nlinarith [hKnn, this]
  -- aggregate at the descendant cube `R`
  have hRscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
  have hmain := lambdaSq_inv_le_of_descendant_ratio R F G (ρ := ρ)
    (s := (3 / 8 : ℝ)) (q := .finite 2) hρnn (by norm_num)
    (by simp [Ch02.MultiscaleExponent.IsAdmissible]) ?_
  · refine hmain.trans ?_
    have hbase : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
      inv_nonneg.mpr (Ch02.lambdaSq_nonneg R F (by norm_num)
        (by simp [Ch02.MultiscaleExponent.IsAdmissible]))
    exact mul_le_mul_of_nonneg_right hρ2 hbase
  · intro l hl T hT
    have hlroot : l ≤ (originCube d 0).scale := by
      rw [hRscale] at hl
      exact le_trans hl hk
    exact hdesc l hlroot T (mem_descendantsAtScale_trans hR hT)

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
