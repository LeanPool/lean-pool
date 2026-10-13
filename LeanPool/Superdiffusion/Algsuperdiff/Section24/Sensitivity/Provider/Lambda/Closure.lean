/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CrudeBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Spine
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeColoring

/-!
# Closure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional `lambda_{s,q}` sensitivity provider

Source: ABK26 (`l.lambda.sensitivity`).

This module discharges the two inputs of
`Provider.Lambda.Spine.unitCubeLambda_inv_perturb_le_of_cube_dhFluxForm_bound`
and assembles the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.lambda_sensitivity`.

## The descendant scaling

`Provider.Lambda.CubeBound` gives, on every triadic descendant `R` of the unit
cube at scale `k ≤ 0`,

```
|D_h(R)[(0,-w)]| ≤ C(d) ‖∇h‖ · 3^k · λ_{3/8,2}^{-1}(R) · J(R) .
```

```
3^k · 3^{-3k/4} = 3^{k/4} ≤ 1   for k ≤ 0 ,
```

so the whole descendant family obeys the *root-gauge* bound consumed by the
spine.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes multiscale weights with explicit `Real.rpow`. -/
private theorem rpow_eq_pow' (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## Descendant scaling of the coarse gauge -/

theorem le_finsetSupReal' {α : Type*} (s : Finset α) (f : α → ℝ) {R : α}
    (hR : R ∈ s) : f R ≤ Ch02.finsetSupReal s f := by
  classical
  unfold Ch02.finsetSupReal
  have hbdd : BddAbove (f '' (↑s : Set α)) := ((Set.toFinite _).image f).bddAbove
  exact le_csSup hbdd ⟨R, hR, rfl⟩

/-- **The descendant scaling identity.**  On a triadic descendant of the unit
cube at a nonpositive scale, the cube diameter exactly compensates the
descendant loss of the coarse gauge. -/
theorem cubeScaleFactor_mul_multiscaleDescendantWeight_le_one
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    cubeScaleFactor R *
        Ch02.multiscaleDescendantWeight (originCube d 0) k (3 / 8 : ℝ) ≤ 1 := by
  have hscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
  have hk0 : k ≤ 0 := by simpa using! hk
  have hfac : cubeScaleFactor R = Real.rpow (3 : ℝ) ((k : ℝ)) := by
    rw [cubeScaleFactor, hscale]
    simp only [rpow_eq_pow']
    rw [Real.rpow_intCast]
  have hweight : Ch02.multiscaleDescendantWeight (originCube d 0) k (3 / 8 : ℝ) =
      Real.rpow (3 : ℝ) (-(3 / 4 : ℝ) * (k : ℝ)) := by
    rw [Ch02.multiscaleDescendantWeight]
    congr 1
    have h0 : ((originCube d 0).scale : ℤ) = 0 := rfl
    push_cast [h0]
    ring
  rw [hfac, hweight]
  simp only [rpow_eq_pow']
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
  linarith

/-- **Root-gauge control of the descendant gauge.** -/
theorem cubeScaleFactor_mul_lambdaSq_inv_le [NeZero d] (G : Ch03.CoeffFamily d)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ ≤
      (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹ := by
  have hadm : (Ch02.MultiscaleExponent.finite 2).IsAdmissible := by
    simp [Ch02.MultiscaleExponent.IsAdmissible]
  have hloc := Ch02.maxDescendant_lambdaSq_inv_le (originCube d 0) G
    (k := k) (s := (3 / 8 : ℝ)) (q := .finite 2) hk (by norm_num) hadm
  have hmem : (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ ≤
      Ch02.maxDescendantLowerEllipticityInvAtScale (originCube d 0) k (3 / 8)
        (.finite 2) G :=
    le_finsetSupReal' _ (fun T => (Ch02.lambdaSq T (3 / 8) (.finite 2) G)⁻¹) hR
  have hchain : (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ ≤
      Ch02.multiscaleDescendantWeight (originCube d 0) k (3 / 8) *
        (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹ := hmem.trans hloc
  have hLnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have hrootnn : (0 : ℝ) ≤ (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_nonneg _ G (by norm_num) hadm)
  have hstep := mul_le_mul_of_nonneg_left hchain hLnn
  refine hstep.trans ?_
  have hw := cubeScaleFactor_mul_multiscaleDescendantWeight_le_one hk hR
  calc cubeScaleFactor R *
        (Ch02.multiscaleDescendantWeight (originCube d 0) k (3 / 8) *
          (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹)
      = (cubeScaleFactor R *
          Ch02.multiscaleDescendantWeight (originCube d 0) k (3 / 8)) *
          (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹ := by ring
    _ ≤ 1 * (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹ :=
        mul_le_mul_of_nonneg_right hw hrootnn
    _ = _ := one_mul _

/-! ## The spine constant -/

/-- The constant of the pure-flux descendant `D_h` bound, normalized so that it
is at least one. -/
def fluxSpineConst (d : ℕ) : ℝ  := max 1 (fluxCubeConst d / 2)

theorem one_le_fluxSpineConst (d : ℕ) : 1 ≤ fluxSpineConst d  :=
  le_max_left _ _

theorem fluxSpineConst_pos (d : ℕ) : 0 < fluxSpineConst d  :=
  lt_of_lt_of_le zero_lt_one (one_le_fluxSpineConst d)

theorem fluxCubeConst_le_two_mul_fluxSpineConst (d : ℕ) : fluxCubeConst d ≤ 2 * fluxSpineConst d  := by
  have := le_max_right (1 : ℝ) (fluxCubeConst d / 2)
  unfold fluxSpineConst
  linarith [this]

/-! ## The descendant `D_h` bound with the root gauge -/

/-- **The `hcube` input of the spine.**  On every triadic descendant of the unit
cube, along the whole perturbation path, the pure-flux `D_h` form is controlled
by the *root* coarse gauge. -/
theorem abs_dhFluxForm_le_root_gauge [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : Ch03.CoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) (τ : ℝ) (w : Vec d) :
    |dhFluxForm (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) w| ≤
      2 * (fluxSpineConst d * h.gradientW1Infinity *
            pathGauge a h.toLInfSkewMatrixFieldOn τ) *
        responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) 0 w := by
  classical
  set hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR with hsubdef
  set b : CoeffOn (cubeDomain R) :=
    perturbCoeffOn (cubeDomain R) (F.coeffOn R)
      (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ with hbdef
  -- a family representing the perturbed root coefficient
  obtain ⟨G, hG⟩ := exists_compatibleTriadicCoeffFamily
    (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn τ)
  have hGR : CoeffOn.AEEq (G.coeffOn R) b :=
    coeffOn_descendant_aeeq_perturbCoeffOn a h.toLInfSkewMatrixFieldOn τ F G hF hG hk hR
  have hL : cubeScaleFactor R ≤ 1 := by
    have hw := cubeScaleFactor_mul_multiscaleDescendantWeight_le_one hk hR
    have hscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
    have hk0 : k ≤ 0 := by simpa using! hk
    have : cubeScaleFactor R = Real.rpow (3 : ℝ) ((k : ℝ)) := by
      rw [cubeScaleFactor, hscale]
      simp only [rpow_eq_pow']
      rw [Real.rpow_intCast]
    rw [this]
    simp only [rpow_eq_pow']
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    exact_mod_cast hk0
  have hmain := abs_dhFluxForm_cube_le h hsub hL b G hGR w
  -- descendant gauge to root gauge
  have hJnn : (0 : ℝ) ≤ responseJ (cubeDomain R) b 0 w := Ch02.responseJ_nonneg _ b 0 w
  have hgnn : 0 ≤ h.gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have hCnn : (0 : ℝ) ≤ fluxCubeConst d := fluxCubeConst_nonneg d
  have hscaleGauge := cubeScaleFactor_mul_lambdaSq_inv_le G hk hR
  have hroot : (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹ =
      pathGauge a h.toLInfSkewMatrixFieldOn τ := by
    rw [pathGauge, unitCubeLambda_characterization (3 / 8 : ℝ) (.finite 2) _ G hG]
  have hgaugennn : (0 : ℝ) ≤ pathGauge a h.toLInfSkewMatrixFieldOn τ :=
    pathGauge_nonneg a h.toLInfSkewMatrixFieldOn τ
  refine hmain.trans ?_
  have hstep1 :
      fluxCubeConst d * h.gradientW1Infinity * cubeScaleFactor R *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ *
          responseJ (cubeDomain R) b 0 w ≤
        fluxCubeConst d * h.gradientW1Infinity *
          pathGauge a h.toLInfSkewMatrixFieldOn τ *
          responseJ (cubeDomain R) b 0 w := by
    have hcoef : (0 : ℝ) ≤ fluxCubeConst d * h.gradientW1Infinity :=
      mul_nonneg hCnn hgnn
    have hgauge : cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ ≤
        pathGauge a h.toLInfSkewMatrixFieldOn τ := by
      rw [← hroot]; exact hscaleGauge
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgauge hcoef) hJnn
    calc fluxCubeConst d * h.gradientW1Infinity * cubeScaleFactor R *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ *
          responseJ (cubeDomain R) b 0 w
        = fluxCubeConst d * h.gradientW1Infinity *
            (cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
            responseJ (cubeDomain R) b 0 w := by ring
      _ ≤ fluxCubeConst d * h.gradientW1Infinity *
            pathGauge a h.toLInfSkewMatrixFieldOn τ *
            responseJ (cubeDomain R) b 0 w := this
  refine hstep1.trans ?_
  have hconst := fluxCubeConst_le_two_mul_fluxSpineConst d
  have hrest : (0 : ℝ) ≤ h.gradientW1Infinity *
      pathGauge a h.toLInfSkewMatrixFieldOn τ * responseJ (cubeDomain R) b 0 w := by
    exact mul_nonneg (mul_nonneg hgnn hgaugennn) hJnn
  nlinarith [hconst, hrest]

/-! ## The provider -/

/-- **The conditional `lambda_{s,q}` sensitivity estimate.**

This is the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.lambda_sensitivity`, with exactly the frozen
binders. -/
theorem lambda_sensitivity {d : ℕ} (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (s : ℝ) (q : Book.Ch02.MultiscaleExponent),
        0 < s → s ≤ 1 / 2 → q.IsAdmissible →
        (unitCubeLambda s q
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1))⁻¹
          ≤ (1 + C * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            (unitCubeLambda s q a)⁻¹ := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hspos : 0 < fluxSpineConst d := fluxSpineConst_pos d
  refine ⟨8 * fluxSpineConst d, by positivity, ?_⟩
  intro a h hgate s q hs _hs2 hq
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
  -- the crude bound
  obtain ⟨B, hB0, hB⟩ := exists_crude_pathGauge_bound a g
  -- the smallness gate
  have hgateinv : h.gradientW1Infinity * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤
      (8 * C₀)⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_right hgate hLinvnn
    rwa [mul_assoc, mul_inv_cancel₀ hlampos.ne', mul_one] at hstep
  have hsmall : 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤ 1 / 2 := by
    have heq : 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ =
        (4 * C₀) * (h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) := by rw [hK]; ring
    rw [heq]
    have h4 : (0 : ℝ) ≤ 4 * C₀ := by positivity
    refine (mul_le_mul_of_nonneg_left hgateinv h4).trans (le_of_eq ?_)
    field_simp
    ring
  -- the descendant `D_h` bound
  have hcube : ∀ F : Ch03.CoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      ∀ k : ℤ, ∀ hk : k ≤ (originCube d 0).scale,
        ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtScale (originCube d 0) k,
          ∀ (τ : ℝ) (w : Vec d),
            |dhFluxForm (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR g) τ) (descendantField hk hR g) w| ≤
              2 * (K * pathGauge a g τ) * responseJ (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR g) τ) 0 w := by
    intro F hF k hk R hR τ w
    have := abs_dhFluxForm_le_root_gauge a h F hF hk hR τ w
    rw [hK, hgdef]
    simpa [mul_assoc] using this
  have hspine := unitCubeLambda_inv_perturb_le_of_cube_dhFluxForm_bound dimension a g
    (K := K) (B := B) hKnn hB0 hB hcube hsmall s q hs hq
  refine hspine.trans ?_
  have hYnn : (0 : ℝ) ≤ (unitCubeLambda s q a)⁻¹ :=
    (inv_pos.mpr (unitCubeLambda_pos a hs hq)).le
  refine mul_le_mul_of_nonneg_right ?_ hYnn
  have hterm : (0 : ℝ) ≤ C₀ * h.gradientW1Infinity *
      (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
    mul_nonneg (mul_nonneg hC₀pos.le hgnn) hLinvnn
  rw [hK]
  nlinarith [hterm]

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
