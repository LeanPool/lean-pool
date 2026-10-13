/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.Aggregation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Localization

/-!
# Closure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `Lambda_{s,2}` sensitivity providers

Source: ABK26 (`e.big.Lambda.sensitivity`).

Both provider results are assembled from

* the descendant `b`-matrix estimate `BigLambda.coarseBMatrixNorm_perturb_le`,
* the geometric resummation of `Provider.Multiscale.GeometricResummation` (the
  fixed-factor version) resp. its general-coefficient form
  `BigLambda.LambdaSq_two_le_of_descendant_bound_coeff`, and
* the root transfer `Provider.Multiscale.unitCubeBigLambda_le_of_family_bound`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal

noncomputable section

/-! ## The frozen constant -/

def bigLambdaConst (d : ℕ) [NeZero d] : ℝ :=
  max (bigLambdaGateConst d) (max (2 * potCubeConstA d ^ 2) (2 * potCubeConstB d))

theorem bigLambdaConst_pos (d : ℕ) [NeZero d] : 0 < bigLambdaConst d :=
  lt_of_lt_of_le (bigLambdaGateConst_pos d) (le_max_left _ _)

theorem bigLambdaGateConst_le_bigLambdaConst (d : ℕ) [NeZero d] :
    bigLambdaGateConst d ≤ bigLambdaConst d := le_max_left _ _

theorem two_mul_potCubeConstA_sq_le_bigLambdaConst (d : ℕ) [NeZero d] :
    2 * potCubeConstA d ^ 2 ≤ bigLambdaConst d :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem two_mul_potCubeConstB_le_bigLambdaConst (d : ℕ) [NeZero d] :
    2 * potCubeConstB d ≤ bigLambdaConst d :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- The frozen gate implies the gate of `BigLambda.CubeJSensitivity`. -/
theorem bigLambdaGate_of_frozen_gate {d : ℕ} [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (bigLambdaConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a) :
    h.gradientW1Infinity ≤
      (bigLambdaGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a := by
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  refine hgate.trans (mul_le_mul_of_nonneg_right ?_ hlampos.le)
  exact inv_anti₀ (bigLambdaGateConst_pos d) (bigLambdaGateConst_le_bigLambdaConst d)

/-! ## The fixed-factor provider -/

/-- **Fixed-factor sensitivity of `Lambda_{s,2}`.**

This is the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.bigLambda_sensitivity`, with exactly the frozen
binders. -/
theorem bigLambda_sensitivity {d : ℕ} (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (s : ℝ), 0 < s → s < 3 / 8 →
      unitCubeBigLambda s (.finite 2)
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
        ≤ 4 * unitCubeBigLambda s (.finite 2) a +
          C * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
            (unitCubeLambda s (.finite 2) a)⁻¹ := by
  classical
  have : NeZero d := ⟨by omega⟩
  refine ⟨bigLambdaConst d, bigLambdaConst_pos d, ?_⟩
  intro a h hgate s hs0 hs
  have hgate' := bigLambdaGate_of_frozen_gate a h hgate
  have hwnn : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hAnn : (0 : ℝ) ≤ potCubeConstA d := potCubeConstA_nonneg d
  have hBnn : (0 : ℝ) ≤ potCubeConstB d := potCubeConstB_nonneg d
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  set K : ℝ := 2 * potCubeConstA d ^ 2 * h.w1Infinity ^ 2 with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  -- the family-level bound
  have hfam : ∀ F G : Ch02.TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      CoeffOn.AEEq (G.coeffOn (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1) →
      Ch02.LambdaSq (originCube d 0) s (.finite 2) G ≤
        4 * Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
          bigLambdaConst d * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
            (unitCubeLambda s (.finite 2) a)⁻¹ := by
    intro F G hF hG
    have hdesc : ∀ n : ℕ, ∀ R ∈ descendantsAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)),
        coarseBMatrixNorm R G ≤
          4 * coarseBMatrixNorm R F +
            K * (Ch02.lambdaSq R (3 / 8 : ℝ) (.finite 2) F)⁻¹ := by
      intro n R hR
      have hk : (originCube d 0).scale - (n : ℤ) ≤ (originCube d 0).scale :=
        sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      have hmain := coarseBMatrixNorm_perturb_le dimension a h hgate' F G hF hG hk hR
        (δ := 1) (by norm_num) le_rfl
      -- the gate bounds the descendant coefficient by `4`
      have hβle : potCubeConstB d * h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤ 1 / 4 := by
        have hlrootnn : (0 : ℝ) ≤ (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
          (inv_pos.mpr hlampos).le
        have hgateinv : h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤ (bigLambdaGateConst d)⁻¹ := by
          have hstep := mul_le_mul_of_nonneg_right hgate' hlrootnn
          rwa [mul_assoc, mul_inv_cancel₀ hlampos.ne', mul_one] at hstep
        have hM : 0 < bigLambdaGateConst d := bigLambdaGateConst_pos d
        have hstep : potCubeConstB d * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤
            potCubeConstB d * (bigLambdaGateConst d)⁻¹ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hgateinv hBnn
        refine hstep.trans ?_
        rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hM]
        have hkey : 4 * potCubeConstB d ≤ bigLambdaGateConst d :=
          four_mul_potCubeConstB_le_bigLambdaGateConst d
        linarith
      have hbFnn : 0 ≤ coarseBMatrixNorm R F := coarseBMatrixNorm_nonneg R F
      refine hmain.trans ?_
      have hcoef : (1 + 1 + 2 * (potCubeConstB d * h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹)) ≤ 4 := by linarith
      have hfirst := mul_le_mul_of_nonneg_right hcoef hbFnn
      have hsecond : 2 * (1 : ℝ)⁻¹ * potCubeConstA d ^ 2 * h.w1Infinity ^ 2 = K := by
        rw [hK]; norm_num
      rw [hsecond]
      linarith [hfirst]
    have hmain := LambdaSq_two_le_of_descendant_bound (originCube d 0) F G hKnn hs0 hs hdesc
    have hgaugeF : unitCubeLambda s (.finite 2) a =
        Ch02.lambdaSq (originCube d 0) s (.finite 2) F :=
      unitCubeLambda_characterization s (.finite 2) a F hF
    rw [← hgaugeF] at hmain
    refine hmain.trans ?_
    have hpolenn : (0 : ℝ) ≤ (3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹ := by
      have h1 : (0 : ℝ) ≤ (3 / 8 - s)⁻¹ := by
        refine inv_nonneg.mpr ?_; linarith
      have h2 : (0 : ℝ) ≤ (unitCubeLambda s (.finite 2) a)⁻¹ :=
        inv_nonneg.mpr (unitCubeLambda_pos a hs0
          (by simp [Ch02.MultiscaleExponent.IsAdmissible])).le
      positivity
    have hKle : K ≤ bigLambdaConst d * h.w1Infinity ^ 2 := by
      rw [hK]
      exact mul_le_mul_of_nonneg_right
        (two_mul_potCubeConstA_sq_le_bigLambdaConst d) (sq_nonneg _)
    have := mul_le_mul_of_nonneg_right hKle hpolenn
    calc 4 * Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
          K * (3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹
        = 4 * Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
            K * ((3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹) := by ring
      _ ≤ 4 * Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
            (bigLambdaConst d * h.w1Infinity ^ 2) *
              ((3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹) := by linarith
      _ = 4 * Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
            bigLambdaConst d * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
              (unitCubeLambda s (.finite 2) a)⁻¹ := by ring
  exact unitCubeBigLambda_le_of_family_bound a _ s (.finite 2) 4 _ hfam

/-! ## The free-`δ` provider -/

/-- **Free-`δ` sensitivity of `Lambda_{s,2}`.**

This is the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.bigLambda_sensitivity_at_delta`, with exactly the
frozen binders and the range `0 < δ ≤ 1`. -/
theorem bigLambda_sensitivity_at_delta {d : ℕ} (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (s δ : ℝ), 0 < s → s < 3 / 8 → 0 < δ → δ ≤ 1 →
      unitCubeBigLambda s (.finite 2)
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
        ≤ (1 + δ + C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            unitCubeBigLambda s (.finite 2) a +
          C * δ⁻¹ * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
            (unitCubeLambda s (.finite 2) a)⁻¹ := by
  classical
  have : NeZero d := ⟨by omega⟩
  refine ⟨bigLambdaConst d, bigLambdaConst_pos d, ?_⟩
  intro a h hgate s δ hs0 hs hδ0 hδ1
  have hgate' := bigLambdaGate_of_frozen_gate a h hgate
  have hwnn : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hAnn : (0 : ℝ) ≤ potCubeConstA d := potCubeConstA_nonneg d
  have hBnn : (0 : ℝ) ≤ potCubeConstB d := potCubeConstB_nonneg d
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  have hlrootnn : (0 : ℝ) ≤ (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
    (inv_pos.mpr hlampos).le
  have hδinv : (0 : ℝ) ≤ δ⁻¹ := (inv_pos.mpr hδ0).le
  set β : ℝ := potCubeConstB d * h.gradientW1Infinity *
    (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hβ
  have hβnn : 0 ≤ β := by rw [hβ]; positivity
  set c : ℝ := 1 + δ + 2 * β with hc
  have hcnn : 0 ≤ c := by rw [hc]; linarith
  set K : ℝ := 2 * δ⁻¹ * potCubeConstA d ^ 2 * h.w1Infinity ^ 2 with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hfam : ∀ F G : Ch02.TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      CoeffOn.AEEq (G.coeffOn (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1) →
      Ch02.LambdaSq (originCube d 0) s (.finite 2) G ≤
        (1 + δ + bigLambdaConst d * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
          bigLambdaConst d * δ⁻¹ * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
            (unitCubeLambda s (.finite 2) a)⁻¹ := by
    intro F G hF hG
    have hdesc : ∀ n : ℕ, ∀ R ∈ descendantsAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)),
        coarseBMatrixNorm R G ≤
          c * coarseBMatrixNorm R F +
            K * (Ch02.lambdaSq R (3 / 8 : ℝ) (.finite 2) F)⁻¹ := by
      intro n R hR
      have hk : (originCube d 0).scale - (n : ℤ) ≤ (originCube d 0).scale :=
        sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      exact coarseBMatrixNorm_perturb_le dimension a h hgate' F G hF hG hk hR hδ0 hδ1
    have hmain := LambdaSq_two_le_of_descendant_bound_coeff (originCube d 0) F G
      hKnn hcnn hs0 hs hdesc
    have hgaugeF : unitCubeLambda s (.finite 2) a =
        Ch02.lambdaSq (originCube d 0) s (.finite 2) F :=
      unitCubeLambda_characterization s (.finite 2) a F hF
    rw [← hgaugeF] at hmain
    refine hmain.trans ?_
    have hLnn : (0 : ℝ) ≤ Ch02.LambdaSq (originCube d 0) s (.finite 2) F :=
      Ch02.LambdaSq_nonneg (originCube d 0) F hs0
        (by simp [Ch02.MultiscaleExponent.IsAdmissible])
    have hpolenn : (0 : ℝ) ≤ (3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹ := by
      have h1 : (0 : ℝ) ≤ (3 / 8 - s)⁻¹ := by
        refine inv_nonneg.mpr ?_; linarith
      have h2 : (0 : ℝ) ≤ (unitCubeLambda s (.finite 2) a)⁻¹ :=
        inv_nonneg.mpr (unitCubeLambda_pos a hs0
          (by simp [Ch02.MultiscaleExponent.IsAdmissible])).le
      positivity
    -- the coefficient comparison
    have hccomp : c ≤ 1 + δ + bigLambdaConst d * h.gradientW1Infinity *
        (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by
      have hBle : 2 * potCubeConstB d ≤ bigLambdaConst d :=
        two_mul_potCubeConstB_le_bigLambdaConst d
      have hgL : (0 : ℝ) ≤ h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by positivity
      have h2β : 2 * β = (2 * potCubeConstB d) *
          (h.gradientW1Infinity * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) := by
        rw [hβ]; ring
      have := mul_le_mul_of_nonneg_right hBle hgL
      rw [hc, h2β, mul_assoc (bigLambdaConst d) h.gradientW1Infinity
        (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹]
      exact add_le_add le_rfl this
    -- the energy comparison
    have hKle : K ≤ bigLambdaConst d * δ⁻¹ * h.w1Infinity ^ 2 := by
      have hAle : 2 * potCubeConstA d ^ 2 ≤ bigLambdaConst d :=
        two_mul_potCubeConstA_sq_le_bigLambdaConst d
      have hrest : (0 : ℝ) ≤ δ⁻¹ * h.w1Infinity ^ 2 := by positivity
      rw [hK]
      calc 2 * δ⁻¹ * potCubeConstA d ^ 2 * h.w1Infinity ^ 2
          = 2 * potCubeConstA d ^ 2 * (δ⁻¹ * h.w1Infinity ^ 2) := by ring
        _ ≤ bigLambdaConst d * (δ⁻¹ * h.w1Infinity ^ 2) :=
            mul_le_mul_of_nonneg_right hAle hrest
        _ = bigLambdaConst d * δ⁻¹ * h.w1Infinity ^ 2 := by ring
    have hfirst := mul_le_mul_of_nonneg_right hccomp hLnn
    have hsecond := mul_le_mul_of_nonneg_right hKle hpolenn
    calc c * Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
          K * (3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹
        = c * Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
            K * ((3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹) := by ring
      _ ≤ (1 + δ + bigLambdaConst d * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
              Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
            (bigLambdaConst d * δ⁻¹ * h.w1Infinity ^ 2) *
              ((3 / 8 - s)⁻¹ * (unitCubeLambda s (.finite 2) a)⁻¹) := by
          linarith [hfirst, hsecond]
      _ = (1 + δ + bigLambdaConst d * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
              Ch02.LambdaSq (originCube d 0) s (.finite 2) F +
            bigLambdaConst d * δ⁻¹ * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
              (unitCubeLambda s (.finite 2) a)⁻¹ := by ring
  exact unitCubeBigLambda_le_of_family_bound a _ s (.finite 2) _ _ hfam

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
