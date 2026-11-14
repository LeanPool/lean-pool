/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Engine
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincare.Setup.UniformBounds
public import LeanPool.HighContrastHomogenization.Support.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometric

/-!
# CrudeBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A crude uniform bound for the coarse gauge along the perturbation path

Source: ABK26.  The self-referential bootstrap of `Provider.Lambda.Bootstrap`
runs the ratio engine on a grid whose mesh is chosen from *some* finite
a-priori bound for the coarse gauge along the segment.  This module supplies
such a bound.

## The microscopic gauge is confined to the mesh

The bound produced here involves the **microscopic** ellipticity constant
`a.lam` of the base coefficient, times a dimensional factor.  By the design of
`Provider.Lambda.Bootstrap` this quantity enters *only* through the choice of
the grid mesh and is entirely absent from the conclusions of
`le_riccati_of_ratio_engine` and `le_one_add_four_mul_of_ratio_engine`.

## The mechanism

The frozen perturbation `perturbCoeffOn U a h t` is defined with `lam:= a.lam`,
uniformly in `t`, because `h` is skew and therefore does not change the
symmetric part.  CoarseGraining's deterministic uniform bound

```
maxDescendantSigmaStarInvNormAtScale Q (Q.scale - n) A ≤ 4 d lam⁻¹
```

therefore holds along the whole segment with a `t`-independent constant, and
summing the geometric weights (which have total mass one) turns it into a bound
for `lambda_{s,q}^{-1}(Q; ·)`.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.UnitCubeMultiscale

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes multiscale weights with explicit `Real.rpow`; Mathlib's
`^`-notation lemmas do not rewrite against it. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## A compatible family that remembers the root ellipticity constants -/

/-- The pointwise representative of a root coefficient is elliptic at *every*
point, with the constants of the coefficient. -/
theorem isEllipticMatrix_pointwiseCoeffField
    (a : CoeffOn (cubeDomain (originCube d 0))) (x : Vec d) :
    IsEllipticMatrix a.lam a.Lam
      (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField
        (cubeDomain (originCube d 0)) a x) := by
  classical
  by_cases hx : x ∈
      (HCPolySupport.Internal.Ch02.BookCh02.goodSetData
        (cubeDomain (originCube d 0)) a).set
  · simpa [HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField, hx] using
      (HCPolySupport.Internal.Ch02.BookCh02.goodSetData
        (cubeDomain (originCube d 0)) a).elliptic x hx
  · simpa [HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField, hx] using
      HCPolySupport.Internal.Ch02.BookCh02.isEllipticMatrix_smul_one
        (d := d) a.lam_pos a.lam_le_Lam

/-- The constant CoarseGraining triadic family built from the pointwise
representative of a root coefficient.  Unlike the anonymous family produced by
`exists_compatibleTriadicCoeffFamily`, this one exposes its ellipticity
constants: they are those of the root coefficient itself. -/
def rootCoeffFamily (a : CoeffOn (cubeDomain (originCube d 0))) :
    TriadicCoeffFamily d where
  coeffOn := fun Q =>
    { toCoeffField :=
        HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain (originCube d 0)) a
      lam := a.lam
      Lam := a.Lam
      lam_pos := a.lam_pos
      lam_le_Lam := a.lam_le_Lam
      aeStronglyMeasurable := by
        classical
        intro i j
        have hrep := HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField_measurable
          (cubeDomain (originCube d 0)) a
        have hite : Measurable fun x : Vec d =>
            if x ∈ openCubeSet Q then
              HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField
                (cubeDomain (originCube d 0)) a x i j
            else 0 :=
          Measurable.ite (measurableSet_openCubeSet Q)
            ((measurable_pi_iff.1 (measurable_pi_iff.1 hrep i)) j) measurable_const
        have hmeas : Measurable fun x : Vec d =>
            restrictCoeffField (openCubeSet Q)
              (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField
                (cubeDomain (originCube d 0)) a) x i j := by
          convert hite using 1
          funext x
          by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
        exact hmeas.aestronglyMeasurable
      aeElliptic := by
        filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x _
        exact isEllipticMatrix_pointwiseCoeffField a x }
  restrictsTo_of_subset := by
    intro Q R _
    exact Filter.EventuallyEq.rfl

@[simp] theorem rootCoeffFamily_lam (a : CoeffOn (cubeDomain (originCube d 0)))
    (Q : TriadicCube d) : ((rootCoeffFamily a).coeffOn Q).lam = a.lam := rfl

theorem rootCoeffFamily_aeeq (a : CoeffOn (cubeDomain (originCube d 0))) :
    CoeffOn.AEEq ((rootCoeffFamily a).coeffOn (originCube d 0)) a := by
  change HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField
      (cubeDomain (originCube d 0)) a
    =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))] a.toCoeffField
  simpa using
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
      (cubeDomain (originCube d 0)) a

/-! ## The deterministic uniform one-cube bound -/

/-- **The uniform descendant bound.**  For any CoarseGraining triadic family, every
descendant maximum of `|sigma_*^{-1}|` is bounded by `4 d` times the inverse of
the *root* microscopic ellipticity constant of the family. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_uniform [NeZero d]
    (Q : TriadicCube d) (F : TriadicCoeffFamily d) (n : ℕ) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F ≤
      4 * (d : ℝ) * ((F.coeffOn Q).lam)⁻¹ := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hEll : IsEllipticFieldOn (F.coeffOn Q).lam (F.coeffOn Q).Lam (openCubeSet Q)
      (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField
        (cubeDomain Q) (F.coeffOn Q)) := by
    simpa [Ch02.cubeDomain_coe] using
      HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (F.coeffOn Q)
  have hData := Ch02.pointwiseCoeffField_openCube_descendant_data Q (F.coeffOn Q)
  refine (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
    F Q hk).trans ?_
  simpa using
    HCPolySupport.maxDescendantSigmaStarInvNorm_le_uniform_of_ellipticField_openCubeSet
      Q _ hEll hData n

/-! ## Aggregation of a uniform one-cube bound -/

/-- **Uniform aggregation.**  A uniform bound on all descendant maxima of
`|sigma_*^{-1}|` transfers verbatim to `lambda_{s,q}^{-1}` at every finite
admissible exponent.  This mirrors the ratio aggregation of
`Multiscale.DescendantRatio`, with a constant in place of a ratio. -/
theorem lambdaSqFinite_inv_le_of_uniform_maxDescendant [NeZero d]
    (Q : TriadicCube d) (F : TriadicCoeffFamily d) {s q M : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hbd : ∀ n : ℕ,
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F ≤ M) :
    (Ch02.lambdaSq Q s (.finite q) F)⁻¹ ≤ M := by
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hp : (0 : ℝ) < q / 2 := by positivity
  have hsq : (0 : ℝ) ≤ s * q := mul_nonneg hs.le hqpos.le
  have hsqpos : (0 : ℝ) < s * q := mul_pos hs hqpos
  set X : ℝ := (Ch02.lambdaSq Q s (.finite q) F)⁻¹ with hX
  have hX0 : 0 ≤ X := inv_nonneg.mpr (Ch02.lambdaSq_finite_nonneg Q F hs hq)
  have hpow : X ^ (q / 2) =
      ∑' n : ℕ, Ch02.geometricWeight s q n *
        (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F)
          ^ (q / 2) := by
    have hser := Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s q F hqpos hsq
    simp only [rpow_eq_pow] at hser
    rw [hX, ← hser, show (-q / 2 : ℝ) = -(q / 2) by ring,
      Real.rpow_neg (Ch02.lambdaSq_finite_nonneg Q F hs hq),
      Real.inv_rpow (Ch02.lambdaSq_finite_nonneg Q F hs hq)]
  have hsumL := Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q F hs hqpos
  simp only [rpow_eq_pow] at hsumL
  have hsumR : Summable fun n : ℕ =>
      Ch02.geometricWeight s q n * M ^ (q / 2) := by
    have := (HCPolySupport.summable_geometricWeight (s := s) (q := q) hsqpos).mul_right
      (M ^ (q / 2))
    simpa [Ch02.geometricWeight_eq_old] using this
  have hterm : ∀ n : ℕ,
      Ch02.geometricWeight s q n *
          (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F)
            ^ (q / 2) ≤
        Ch02.geometricWeight s q n * M ^ (q / 2) := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hM0 : 0 ≤ Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) F :=
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk F
    have hw : 0 ≤ Ch02.geometricWeight s q n := by
      simpa [Ch02.geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_nonneg n hsq
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0 (hbd n) hp.le) hw
  have hcompare : X ^ (q / 2) ≤ M ^ (q / 2) := by
    rw [hpow]
    refine (Summable.tsum_le_tsum hterm hsumL hsumR).trans (le_of_eq ?_)
    have hone : ∑' n : ℕ, Ch02.geometricWeight s q n = 1 := by
      simpa [Ch02.geometricWeight_eq_old] using
        HCPolySupport.tsum_geometricWeight_eq_one (s := s) (q := q) hsqpos
    rw [tsum_mul_right, hone, one_mul]
  have hinvpow : ∀ z : ℝ, 0 ≤ z → (z ^ (q / 2)) ^ (2 / q) = z := by
    intro z hz
    rw [← Real.rpow_mul hz, show q / 2 * (2 / q) = 1 by field_simp]
    exact Real.rpow_one z
  calc X = (X ^ (q / 2)) ^ (2 / q) := (hinvpow X hX0).symm
    _ ≤ (M ^ (q / 2)) ^ (2 / q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hcompare (by positivity)
    _ = M := hinvpow M hM

/-! ## The crude bound -/

/-- **The crude uniform path-gauge bound.**

Along the whole segment `a + t h`, `t ∈ [0,1]`, the frozen coarse gauge
`lambda_{3/8,2}^{-1}` is bounded by the single constant `4 d a.lam⁻¹`.

The microscopic constant `a.lam` appears here and only here; by the design of
`Provider.Lambda.Bootstrap` it is consumed by the choice of the compounding mesh
and never enters the conclusion. -/
theorem exists_crude_pathGauge_bound [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → pathGauge a h t ≤ B := by
  classical
  have hlam0 : (0 : ℝ) < a.lam := a.lam_pos
  have hMnn : (0 : ℝ) ≤ 4 * (d : ℝ) * (a.lam)⁻¹ := by positivity
  refine ⟨4 * (d : ℝ) * (a.lam)⁻¹, hMnn, ?_⟩
  intro t _ _
  set b : CoeffOn (cubeDomain (originCube d 0)) :=
    perturbCoeffOn (cubeDomain (originCube d 0)) a h t with hb
  have hlam : b.lam = a.lam := rfl
  have hgauge : unitCubeLambda (3 / 8) (.finite 2) b =
      Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) (rootCoeffFamily b) :=
    unitCubeLambda_characterization (3 / 8 : ℝ) (.finite 2) b (rootCoeffFamily b)
      (rootCoeffFamily_aeeq b)
  have hbd : ∀ n : ℕ,
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)) (rootCoeffFamily b) ≤
        4 * (d : ℝ) * (a.lam)⁻¹ := by
    intro n
    have := maxDescendantSigmaStarInvMatrixNormAtScale_le_uniform (originCube d 0)
      (rootCoeffFamily b) n
    rwa [rootCoeffFamily_lam, hlam] at this
  rw [pathGauge, ← hb, hgauge]
  exact lambdaSqFinite_inv_le_of_uniform_maxDescendant (originCube d 0)
    (rootCoeffFamily b) (by norm_num) (by norm_num) hMnn hbd

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
