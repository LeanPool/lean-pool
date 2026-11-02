/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Response.PathDerivative
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Response.PathGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.BoundProvider
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.DiscreteCompounding

/-!
# Closure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional sensitivity estimate for the response functional

The source argument is, with `M := max_{t ∈ [0,1]} J(a + t h)` and

```
E := |p|² ‖h‖_{W^{1,∞}}² λ⁻¹ + |p·q| ‖∇h‖_{W^{1,∞}}² λ⁻²  ,
```

1. the coarse-grained derivative bound `l.Dh.bound` at the point `a + t h`,
   together with the conditional `lambda` sensitivity estimate (which keeps the
   gauge along the segment within a factor two of the base gauge), gives
   ```
   |d/dt J(a + t h)| ≤ C E^{1/2} M^{1/2} + C ‖∇h‖ λ⁻¹ M   for all t ∈ [0,1];
   ```

2. integration in `t` turns this into the self-referential bound
   ```
   M ≤ J(a) + C E^{1/2} M^{1/2} + C ‖∇h‖ λ⁻¹ M;
   ```

3. Young's inequality absorbs the two `M` terms on the right, which under the
   smallness gate `‖∇h‖ ≤ C⁻¹ λ` yields the frozen conclusion.

Step 1 uses the `D_h` bound `Provider.DhBound.coarseMatrixDerivative_bound`,
which holds at *every* coefficient field on the unit cube, hence in particular
at every point of the segment; the derivative itself is the
`Provider.Path.responseJ_derivative` transported along the path semigroup
(`Response.PathDerivative`).  Step 2 is the mean-value step
`Response.le_add_of_hasDerivAt_le` applied at the maximum point, which exists
because `t ↦ J(a + t h)` is differentiable, hence continuous, on the compact
segment.  Step 3 is
`Provider.Multiscale.DiscreteCompounding.self_bound_le_closed`.

The gauge control of step 1 is supplied by
`Response.pathGauge_le_two_mul_of_cube_dhFluxForm_bound`, whose single analytic
input `hcube` (the pure-flux `D_h` bound on all triadic descendants of the unit
cube, with the root gauge as coefficient) is a premise of the provider below.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Response

open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Arithmetic of the pointwise derivative bound -/

/-- `√2 ≤ 2`. -/
private theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  calc Real.sqrt 2 ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 2 := Real.sqrt_sq (by norm_num)

/-- The two-term budget `x + y` is at most `√2 √(x² + y²)`. -/
private theorem add_le_sqrt_two_mul_sqrt_sq_add_sq {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    x + y ≤ Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) := by
  have hxy : 0 ≤ x + y := by linarith only [hx, hy]
  have hsq : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    linarith only [sq_nonneg (x - y)]
  calc x + y = Real.sqrt ((x + y) ^ 2) := (Real.sqrt_sq hxy).symm
    _ ≤ Real.sqrt (2 * (x ^ 2 + y ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) :=
        Real.sqrt_mul (by norm_num) _

/-- **The pointwise derivative fold.**

The `D_h` bound at the point `a + τ h` of the segment, together with the
doubling control `λ⁻¹(a + τ h) ≤ 2 λ⁻¹(a)` and the maximality `J(a + τ h) ≤ M`,
folds into the source's shape `c √E √M + r M` with `c = √2 C` and
`r = C ‖∇h‖ λ⁻¹(a)`. -/
private theorem path_deriv_fold {C₁ np w gr L Lτ Jτ M spq : ℝ}
    (hC₁ : 0 ≤ C₁) (hnp : 0 ≤ np) (hw : 0 ≤ w) (hgr : 0 ≤ gr)
    (hL : 0 ≤ L) (hLτ0 : 0 ≤ Lτ) (hLτ : Lτ ≤ 2 * L)
    (hJτ0 : 0 ≤ Jτ) (hJτ : Jτ ≤ M) (hspq : 0 ≤ spq) :
    (1 / 2 : ℝ) *
        (C₁ * (np * w * Real.sqrt Lτ + spq * gr * Lτ) * Real.sqrt Jτ +
          C₁ * gr * Lτ * Jτ) ≤
      Real.sqrt 2 * C₁ *
          Real.sqrt ((np * w * Real.sqrt L) ^ 2 + (spq * gr * L) ^ 2) *
          Real.sqrt M + C₁ * gr * L * M := by
  have hM : 0 ≤ M := le_trans hJτ0 hJτ
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hsM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hstepL : Real.sqrt Lτ ≤ Real.sqrt 2 * Real.sqrt L := by
    calc Real.sqrt Lτ ≤ Real.sqrt (2 * L) := Real.sqrt_le_sqrt hLτ
      _ = Real.sqrt 2 * Real.sqrt L := Real.sqrt_mul (by norm_num) _
  have hstepJ : Real.sqrt Jτ ≤ Real.sqrt M := Real.sqrt_le_sqrt hJτ
  set x : ℝ := np * w * Real.sqrt L with hx
  set y : ℝ := spq * gr * L with hy
  have hxnn : 0 ≤ x := by rw [hx]; positivity
  have hynn : 0 ≤ y := by rw [hy]; positivity
  have hbudget : np * w * Real.sqrt Lτ + spq * gr * Lτ ≤
      Real.sqrt 2 * x + 2 * y := by
    have h1 : np * w * Real.sqrt Lτ ≤ np * w * (Real.sqrt 2 * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hstepL (mul_nonneg hnp hw)
    have h2 : spq * gr * Lτ ≤ spq * gr * (2 * L) :=
      mul_le_mul_of_nonneg_left hLτ (mul_nonneg hspq hgr)
    rw [hx, hy]
    linarith only [h1, h2]
  have hbudgetnn : (0 : ℝ) ≤ np * w * Real.sqrt Lτ + spq * gr * Lτ := by
    have h1 : (0 : ℝ) ≤ np * w * Real.sqrt Lτ := by positivity
    have h2 : (0 : ℝ) ≤ spq * gr * Lτ := by positivity
    linarith only [h1, h2]
  have hterm1 : C₁ * (np * w * Real.sqrt Lτ + spq * gr * Lτ) * Real.sqrt Jτ ≤
      C₁ * (Real.sqrt 2 * x + 2 * y) * Real.sqrt M := by
    have hA : C₁ * (np * w * Real.sqrt Lτ + spq * gr * Lτ) ≤
        C₁ * (Real.sqrt 2 * x + 2 * y) := mul_le_mul_of_nonneg_left hbudget hC₁
    have hAnn : (0 : ℝ) ≤ C₁ * (np * w * Real.sqrt Lτ + spq * gr * Lτ) :=
      mul_nonneg hC₁ hbudgetnn
    exact mul_le_mul hA hstepJ (Real.sqrt_nonneg _) (le_trans hAnn hA)
  have hterm2 : C₁ * gr * Lτ * Jτ ≤ C₁ * gr * (2 * L) * M := by
    have hA : C₁ * gr * Lτ ≤ C₁ * gr * (2 * L) :=
      mul_le_mul_of_nonneg_left hLτ (mul_nonneg hC₁ hgr)
    have hAnn : (0 : ℝ) ≤ C₁ * gr * Lτ := by positivity
    exact mul_le_mul hA hJτ hJτ0 (le_trans hAnn hA)
  have hE : x + y ≤ Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) :=
    add_le_sqrt_two_mul_sqrt_sq_add_sq hxnn hynn
  have hcoef : Real.sqrt 2 / 2 * x + y ≤
      Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) := by
    have hhalf : Real.sqrt 2 / 2 * x ≤ x := by
      have h1 : Real.sqrt 2 / 2 ≤ 1 := by
        rw [div_le_one (by norm_num : (0 : ℝ) < 2)]
        exact sqrt_two_le_two
      calc Real.sqrt 2 / 2 * x ≤ 1 * x := mul_le_mul_of_nonneg_right h1 hxnn
        _ = x := one_mul x
    linarith only [hhalf, hE]
  have hfinal : (Real.sqrt 2 / 2 * x + y) * Real.sqrt M ≤
      Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) * Real.sqrt M :=
    mul_le_mul_of_nonneg_right hcoef hsM
  have hscaled : C₁ * ((Real.sqrt 2 / 2 * x + y) * Real.sqrt M) ≤
      C₁ * (Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) * Real.sqrt M) :=
    mul_le_mul_of_nonneg_left hfinal hC₁
  linarith only [hterm1, hterm2, hscaled]

/-! ## The self-referential bound along the segment -/

/-- **The maximum of the response along the segment obeys the source's
self-referential bound.**

Given the `D_h` bound (as the hypothesis `hDh`, with explicit constant `C₁`)
and the doubling control `hpath` for the coarse gauge along the segment, the
maximum `M` of `t ↦ J(a + t h, p, q)` over `[0,1]` satisfies

```
M ≤ J(a, p, q) + √2 C₁ √E √M + C₁ ‖∇h‖ λ⁻¹ M ,
```

which is the display of ABK26. -/
private theorem exists_pathMax_self_bound [NeZero d] (dimension : 2 ≤ d)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hDh : ∀ (b : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (p q : Vec d),
      |blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative (cubeDomain (originCube d 0)) b
          h.toLInfSkewMatrixFieldOn.1) (p, -q))|
        ≤ C₁ * (vecNorm p * h.w1Infinity *
              Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) b)⁻¹) +
            Real.sqrt |vecDot p q| * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) b)⁻¹) *
            Real.sqrt (responseJ (cubeDomain (originCube d 0)) b p q) +
          C₁ * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) b)⁻¹ *
            responseJ (cubeDomain (originCube d 0)) b p q)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (p q : Vec d)
    (hpath : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      pathGauge a h.toLInfSkewMatrixFieldOn τ ≤
        2 * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) :
    ∃ M : ℝ, 0 ≤ M ∧
      responseJ (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a
            h.toLInfSkewMatrixFieldOn 1) p q ≤ M ∧
      M ≤ responseJ (cubeDomain (originCube d 0)) a p q +
        Real.sqrt 2 * C₁ *
          Real.sqrt (vecNormSq p * h.w1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
            |vecDot p q| * h.gradientW1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2) * Real.sqrt M +
        C₁ * h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ * M := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set np : ℝ := vecNorm p with hnpdef
  set w : ℝ := h.w1Infinity with hwdef
  set gr : ℝ := h.gradientW1Infinity with hgrdef
  set L : ℝ := (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hLdef
  set f : ℝ → ℝ := fun τ =>
    responseJ (cubeDomain (originCube d 0)) (perturbCoeffOn
      (cubeDomain (originCube d 0)) a g τ) p q with hfdef
  have hnpnn : 0 ≤ np := vecNorm_nonneg p
  have hwnn : 0 ≤ w := DhBound.Lipschitz.w1Infinity_nonneg h
  have hgrnn : 0 ≤ gr := DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    exact (inv_pos.mpr (DhBound.Discharge.unitCubeLambda_sensitivity_pos a)).le
  have hfnn : ∀ τ : ℝ, 0 ≤ f τ := fun τ => Ch02.responseJ_nonneg _ _ p q
  -- the derivative of the response along the segment
  have hderiv : ∀ τ : ℝ, HasDerivAt f
      ((1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ) g.1) (p, -q))) τ :=
    fun τ => hasDerivAt_responseJ_perturbCoeffOn_pair dimension _ a g p q τ
  have hcont : Continuous f :=
    continuous_iff_continuousAt.2 fun τ => (hderiv τ).continuousAt
  obtain ⟨τ₀, hτ₀mem, hτ₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (zero_le_one (α := ℝ)))
      hcont.continuousOn
  set M : ℝ := f τ₀ with hMdef
  have hMnn : 0 ≤ M := hfnn τ₀
  have hMmax : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → f τ ≤ M := fun τ h₀ h₁ =>
    hτ₀max (Set.mem_Icc.2 ⟨h₀, h₁⟩)
  set spq : ℝ := Real.sqrt |vecDot p q| with hspqdef
  have hspqnn : 0 ≤ spq := Real.sqrt_nonneg _
  set E : ℝ := vecNormSq p * w ^ 2 * L + |vecDot p q| * gr ^ 2 * L ^ 2 with hEdef
  have hEsplit : (np * w * Real.sqrt L) ^ 2 + (spq * gr * L) ^ 2 = E := by
    have h1 : (np * w * Real.sqrt L) ^ 2 = vecNormSq p * w ^ 2 * L := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hLnn, hnpdef, Ch02.vecNorm_sq_eq_vecNormSq]
    have h2 : (spq * gr * L) ^ 2 = |vecDot p q| * gr ^ 2 * L ^ 2 := by
      rw [mul_pow, mul_pow, hspqdef, Real.sq_sqrt (abs_nonneg _)]
    rw [h1, h2, hEdef]
  set B : ℝ := Real.sqrt 2 * C₁ * Real.sqrt E * Real.sqrt M +
    C₁ * gr * L * M with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : (0 : ℝ) ≤ Real.sqrt 2 * C₁ * Real.sqrt E * Real.sqrt M := by
      have := Real.sqrt_nonneg E
      have h2 := Real.sqrt_nonneg M
      have h3 := Real.sqrt_nonneg (2 : ℝ)
      positivity
    have h4 : (0 : ℝ) ≤ C₁ * gr * L * M := by positivity
    linarith only [h1, h4]
  -- the uniform derivative bound on the segment
  have hderivbd : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      (1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ) g.1) (p, -q)) ≤ B := by
    intro τ hτ0 hτ1
    have hbound := hDh (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ) h p q
    have hgauge : (unitCubeLambda (3 / 8) (.finite 2)
        (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ))⁻¹ =
        pathGauge a g τ := rfl
    rw [hgauge] at hbound
    have hle := (le_abs_self _).trans hbound
    have hfold := path_deriv_fold (C₁ := C₁) (np := np) (w := w) (gr := gr)
      (L := L) (Lτ := pathGauge a g τ) (Jτ := f τ) (M := M) (spq := spq)
      hC₁ hnpnn hwnn hgrnn hLnn (pathGauge_nonneg a g τ)
      (hpath τ hτ0 hτ1) (hfnn τ) (hMmax τ hτ0 hτ1) hspqnn
    rw [hEsplit] at hfold
    rw [hBdef]
    linarith only [hle, hfold]
  -- integrate at the maximum point
  have hmem := Set.mem_Icc.1 hτ₀mem
  have hstep := le_add_of_hasDerivAt_le (y := f) hderiv (B := B) (t₁ := 0)
    (t₂ := τ₀) (fun σ h₁ h₂ => hderivbd σ h₁ (le_trans h₂ hmem.2)) hmem.1
  have hτle : B * (τ₀ - 0) ≤ B := by
    rw [sub_zero]
    exact mul_le_of_le_one_right hBnn hmem.2
  have hf0 : f 0 = responseJ (cubeDomain (originCube d 0)) a p q := by
    rw [hfdef]
    exact responseJ_eq_ofAEEq (perturbCoeffOn_zero_aeeq a g) p q
  refine ⟨M, hMnn, hMmax 1 zero_le_one le_rfl, ?_⟩
  have hMle : M ≤ f 0 + B := by rw [hMdef]; linarith only [hstep, hτle]
  rw [hf0, hBdef] at hMle
  linarith only [hMle]

/-! ## The provider, given the descendant pure-flux `D_h` bound -/

/-- **The conditional sensitivity estimate for the response functional**, given
the per-descendant pure-flux `D_h` bound `hcube` with the root gauge as
coefficient.

The conclusion is exactly the frozen statement
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity`, with exactly the frozen
binders; the only extra hypothesis is `hcube`, which is a *consumption point*
and carries no proof step of the frozen statement: it is the `p = 0`
specialization of the `D_h` bound applied on all triadic descendants of the
unit cube, i.e. the `hcube` input of
`Provider.Lambda.Spine.unitCubeLambda_inv_perturb_le_of_cube_dhFluxForm_bound`.

The explicit constant is `C = 8 K₀ + 4 C₁ + 4 C₁²`, where `C₁` is the constant
of the `D_h` bound and `K₀` the constant of `hcube`. -/
theorem responseJ_sensitivity_of_cube_dhFluxForm_bound {d : ℕ} (dimension : 2 ≤ d)
    {K₀ : ℝ} (hK₀ : 0 < K₀)
    (hcube : ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (F : TriadicCoeffFamily d),
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      ∀ k : ℤ, ∀ hk : k ≤ (originCube d 0).scale,
        ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtScale (originCube d 0) k,
          ∀ (τ : ℝ) (w : Vec d),
            |dhFluxForm (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
                (descendantField hk hR h.toLInfSkewMatrixFieldOn) w| ≤
              2 * (K₀ * h.gradientW1Infinity *
                  pathGauge a h.toLInfSkewMatrixFieldOn τ) *
                responseJ (cubeDomain R)
                  (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                    (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) 0 w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (p q : Vec d) (δ : ℝ), 0 < δ → δ ≤ 1 →
      responseJ (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1) p q
        ≤ (1 + δ + C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            responseJ (cubeDomain (originCube d 0)) a p q +
          C * δ⁻¹ * (vecNormSq p * h.w1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
            |vecDot p q| * h.gradientW1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C₁, hC₁pos, hDh⟩ := DhBound.coarseMatrixDerivative_bound dimension
  refine ⟨8 * K₀ + 4 * C₁ + 4 * C₁ ^ 2, by positivity, ?_⟩
  intro a h hgate p q δ hδ hδ'
  set C : ℝ := 8 * K₀ + 4 * C₁ + 4 * C₁ ^ 2 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have h8K : 8 * K₀ ≤ C := by
    rw [hC]; linarith only [hC₁pos, sq_nonneg C₁]
  have h2C : 2 * C₁ ≤ C := by
    rw [hC]; linarith only [hK₀, sq_nonneg C₁, hC₁pos]
  have h4C : 4 * C₁ ≤ C := by
    rw [hC]; linarith only [hK₀, sq_nonneg C₁]
  have h4C2 : 4 * C₁ ^ 2 ≤ C := by
    rw [hC]; linarith only [hK₀, hC₁pos]
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set gr : ℝ := h.gradientW1Infinity with hgrdef
  set L : ℝ := (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hLdef
  have hgrnn : 0 ≤ gr := DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    DhBound.Discharge.unitCubeLambda_sensitivity_pos a
  have hLnn : 0 ≤ L := by rw [hLdef]; exact (inv_pos.mpr hlampos).le
  -- the smallness gate in inverse form
  have hgateinv : gr * L ≤ C⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_right hgate hLnn
    rwa [hLdef, mul_assoc, mul_inv_cancel₀ hlampos.ne', mul_one] at hstep
  -- the coarse gauge at most doubles along the segment
  have hpath : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → pathGauge a g τ ≤ 2 * L := by
    have hsmall : 4 * (K₀ * gr) * L ≤ 1 / 2 := by
      have hstep : (4 * K₀) * (gr * L) ≤ (4 * K₀) * C⁻¹ :=
        mul_le_mul_of_nonneg_left hgateinv (by positivity)
      have hle : (4 * K₀) * C⁻¹ ≤ 1 / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hCpos]
        linarith only [h8K]
      calc 4 * (K₀ * gr) * L = (4 * K₀) * (gr * L) := by ring
        _ ≤ (4 * K₀) * C⁻¹ := hstep
        _ ≤ 1 / 2 := hle
    intro τ hτ₀ hτ₁
    exact pathGauge_le_two_mul_of_cube_dhFluxForm_bound dimension a g
      (K := K₀ * gr) (mul_nonneg hK₀.le hgrnn)
      (fun F hF k hk R hR σ v => hcube a h F hF k hk R hR σ v)
      hsmall τ hτ₀ hτ₁
  -- the self-referential bound for the maximum along the segment
  obtain ⟨M, hMnn, hM1, hMself⟩ :=
    exists_pathMax_self_bound dimension hC₁pos.le hDh a h p q hpath
  rw [← hgrdef, ← hLdef] at hMself
  set E : ℝ := vecNormSq p * h.w1Infinity ^ 2 * L + |vecDot p q| * gr ^ 2 * L ^ 2
    with hEdef
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    have h1 : (0 : ℝ) ≤ vecNormSq p * h.w1Infinity ^ 2 * L := by
      have := vecNormSq_nonneg p
      positivity
    have h2 : (0 : ℝ) ≤ |vecDot p q| * gr ^ 2 * L ^ 2 := by positivity
    linarith only [h1, h2]
  set r : ℝ := C₁ * gr * L with hrdef
  have hrnn : 0 ≤ r := by rw [hrdef]; positivity
  have hrle : r ≤ 1 / 4 := by
    have hstep : C₁ * (gr * L) ≤ C₁ * C⁻¹ :=
      mul_le_mul_of_nonneg_left hgateinv hC₁pos.le
    have hle : C₁ * C⁻¹ ≤ 1 / 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hCpos]
      linarith only [h4C]
    calc r = C₁ * (gr * L) := by rw [hrdef]; ring
      _ ≤ C₁ * C⁻¹ := hstep
      _ ≤ 1 / 4 := hle
  have hJnn : 0 ≤ responseJ (cubeDomain (originCube d 0)) a p q :=
    Ch02.responseJ_nonneg _ a p q
  have hclosed := self_bound_le_closed (M := M)
    (J := responseJ (cubeDomain (originCube d 0)) a p q) (E := E)
    (c := Real.sqrt 2 * C₁) (r := r) (δ := δ) hMnn hJnn hEnn hrnn hrle hδ hδ'
    hMself
  have hc2 : (Real.sqrt 2 * C₁) ^ 2 = 2 * C₁ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hc2] at hclosed
  refine le_trans hM1 (hclosed.trans ?_)
  have hδinv : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hgrL : 0 ≤ gr * L := mul_nonneg hgrnn hLnn
  have hJcoef : (1 + δ + 2 * r) * responseJ (cubeDomain (originCube d 0)) a p q ≤
      (1 + δ + C * gr * L) * responseJ (cubeDomain (originCube d 0)) a p q := by
    refine mul_le_mul_of_nonneg_right ?_ hJnn
    have hrw : 2 * r = 2 * C₁ * (gr * L) := by rw [hrdef]; ring
    rw [hrw]
    linarith only [mul_le_mul_of_nonneg_right h2C hgrL]
  have hEcoef : 2 * δ⁻¹ * (2 * C₁ ^ 2) * E ≤ C * δ⁻¹ * E := by
    have hprod : 0 ≤ δ⁻¹ * E := mul_nonneg hδinv.le hEnn
    linarith only [mul_le_mul_of_nonneg_right h4C2 hprod]
  rw [hEdef] at hEcoef
  linarith only [hJcoef, hEcoef]

/-! ## The provider -/

/-- **The conditional sensitivity estimate for the response functional.**

This is the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity`, with exactly the frozen
binders.  The premise `hcube` of
`responseJ_sensitivity_of_cube_dhFluxForm_bound` is discharged here by
`Provider.Lambda.Closure.abs_dhFluxForm_le_root_gauge`, the descendant `D_h`
bound with the root coarse gauge that also drives the `lambda` sensitivity
provider.

The explicit constant is `C = 8 C₀(d) + 4 C₁(d) + 4 C₁(d)²`, where `C₁(d)` is
the constant `Provider.DhBound.dhBoundConst d` of the `D_h` bound and `C₀(d) =
Provider.Lambda.fluxSpineConst d`. -/
theorem responseJ_sensitivity {d : ℕ} (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (p q : Vec d) (δ : ℝ), 0 < δ → δ ≤ 1 →
      responseJ (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1) p q
        ≤ (1 + δ + C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            responseJ (cubeDomain (originCube d 0)) a p q +
          C * δ⁻¹ * (vecNormSq p * h.w1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
            |vecDot p q| * h.gradientW1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2) := by
  have : NeZero d := ⟨by omega⟩
  exact responseJ_sensitivity_of_cube_dhFluxForm_bound dimension
    (fluxSpineConst_pos d)
    (fun a h F hF _k hk _R hR τ w => abs_dhFluxForm_le_root_gauge a h F hF hk hR τ w)

end

end Algsuperdiff.Section24.Sensitivity.Provider.Response
