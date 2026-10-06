/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Space-time integration by parts

The compactly supported spatial Laplacian pairing identity used in
`prop:carleman-gauss` of the Escauriaza–Seregin–Šverák manuscript and `lem:caccioppoli`.
-/

public section

open MeasureTheory
open CKN
open CKN.Foundation.Parabolic

namespace CKN

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

/-- The product topology on spatial points and time used for space-time calculus. -/
local instance (priority := high) : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd

private theorem spatialPartial_eq_fderiv
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (z : Vec3 × ℝ) (i : Fin 3) :
    spatialPartial (show ParabolicPoint → ℝ from f) i z =
      fderiv ℝ f z (basisVec i, 0) := by
  have hF : HasFDerivAt f (fderiv ℝ f z) z :=
    ((hf.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  let G : Vec3 → Vec3 × ℝ := fun x => (x, z.2)
  have hG : HasFDerivAt (fun x : Vec3 => (x, z.2))
      ((ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ)) z.1 := by
    exact (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) z.2 z.1)
  have hc := hF.comp z.1 hG
  have hfun : (fun x : Vec3 => f (x, z.2)) = f ∘ G := rfl
  change (fderiv ℝ (fun x : Vec3 => f (x, z.2)) z.1) (basisVec i) = _
  rw [hfun, hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

private theorem spatialPartial_contDiff_one
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial f i z) := by
  let F : (Vec3 × ℝ) → Vec3 → ℝ := fun z x => f (x, z.2)
  have hmap : ContDiff ℝ (2 : ℕ∞)
      (fun q : (Vec3 × ℝ) × Vec3 => (q.2, q.1.2)) := by
    fun_prop
  have hF : ContDiff ℝ (2 : ℕ∞) (Function.uncurry F) := by
    convert hf.comp hmap using 1
    funext q
    rfl
  have hderiv := hF.fderiv_apply
    (contDiff_fst (𝕜 := ℝ) (n := (1 : ℕ∞)))
    (contDiff_const (𝕜 := ℝ) (n := (1 : ℕ∞)) (c := basisVec i))
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  simpa only [F, spatialPartial, Function.uncurry] using hderiv

private theorem spatialPartial_hasCompactSupport
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (hfc : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from f) i z) := by
  let v : Vec3 × ℝ := (basisVec i, 0)
  have heq : (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from f) i z) = fun z => fderiv ℝ f z v := by
    funext z
    exact spatialPartial_eq_fderiv hf z i
  rw [heq]
  exact hfc.fderiv_apply (𝕜 := ℝ) v

private theorem spatialPartial_continuous
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (i : Fin 3) :
    Continuous (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from f) i z) := by
  let v : Vec3 × ℝ := (basisVec i, 0)
  have heq : (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from f) i z) = fun z => fderiv ℝ f z v := by
    funext z
    exact spatialPartial_eq_fderiv hf z i
  have hfd := hf.contDiff_fderiv_apply (m := (0 : WithTop ℕ∞))
    (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  have hmap : ContDiff ℝ (0 : WithTop ℕ∞)
      (fun z : Vec3 × ℝ => (z, v)) := by
    fun_prop
  have hcont : Continuous (fun z : Vec3 × ℝ => fderiv ℝ f z v) :=
    (hfd.comp hmap).continuous
  rw [heq]
  exact hcont

private theorem integral_spatialPartial_mul_eq_neg
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (hg : ContDiff ℝ (1 : ℕ∞) g) (hgc : HasCompactSupport g)
    (i : Fin 3) :
    ∫ z : Vec3 × ℝ, spatialPartial f i z * g z ∂volume =
      -∫ z : Vec3 × ℝ, f z * spatialPartial g i z ∂volume := by
  let v : Vec3 × ℝ := (basisVec i, 0)
  have hDf : Continuous (fun z : Vec3 × ℝ => fderiv ℝ f z v) := by
    have h := hf.contDiff_fderiv_apply (m := (0 : ℕ∞)) (by norm_num)
    have hc : ContDiff ℝ (0 : ℕ∞) (fun z : Vec3 × ℝ => (z, v)) := by fun_prop
    exact (h.comp hc).continuous
  have hDg : Continuous (fun z : Vec3 × ℝ => fderiv ℝ g z v) := by
    have h := hg.contDiff_fderiv_apply (m := (0 : ℕ∞)) (by norm_num)
    have hc : ContDiff ℝ (0 : ℕ∞) (fun z : Vec3 × ℝ => (z, v)) := by fun_prop
    exact (h.comp hc).continuous
  have hDgc : HasCompactSupport (fun z : Vec3 × ℝ => fderiv ℝ g z v) :=
    hgc.fderiv_apply (𝕜 := ℝ) v
  have hfg : Integrable (fun z : Vec3 × ℝ => f z * g z) volume :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left)
  have hfg' : Integrable (fun z : Vec3 × ℝ => f z * fderiv ℝ g z v) volume :=
    (hf.continuous.mul hDg).integrable_of_hasCompactSupport (hDgc.mul_left)
  have hf'g : Integrable (fun z : Vec3 × ℝ => fderiv ℝ f z v * g z) volume :=
    (hDf.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hf'g hfg' hfg
    (fun z hz => (hf.differentiable (by norm_num)).differentiableAt)
    (fun z hz => (hg.differentiable (by norm_num)).differentiableAt)
  have hleft : (fun z : Vec3 × ℝ => f z * fderiv ℝ g z v) =
      fun z => f z * spatialPartial (show ParabolicPoint → ℝ from g) i z := by
    funext z
    exact congrArg (fun d : ℝ => f z * d)
      (spatialPartial_eq_fderiv hg z i).symm
  have hright : (∫ z : Vec3 × ℝ, fderiv ℝ f z v * g z ∂volume) =
      ∫ z : Vec3 × ℝ, spatialPartial (show ParabolicPoint → ℝ from f) i z * g z ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact congrArg (fun d : ℝ => d * g z) (spatialPartial_eq_fderiv hf z i).symm
  rw [hleft, hright] at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

private theorem integral_spatialSecondPartial_mul_eq_neg_gradient
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ∞) f)
    (hg : ContDiff ℝ (2 : ℕ∞) g) (hgc : HasCompactSupport g)
    (i : Fin 3) :
    ∫ z : Vec3 × ℝ, spatialSecondPartial
      (show ParabolicPoint → ℝ from f) i i z * g z ∂volume =
      -∫ z, spatialPartial (show ParabolicPoint → ℝ from f) i z *
        spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume := by
  have hf1 : ContDiff ℝ (1 : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from f) i z) :=
    spatialPartial_contDiff_one hf i
  have hg1 : ContDiff ℝ (1 : ℕ∞) g := hg.of_le (by norm_num)
  have h := integral_spatialPartial_mul_eq_neg hf1 hg1 hgc i
  exact h

private theorem integral_spatialLaplacian_mul_eq_neg_gradient_pairing
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ∞) f)
    (hg : ContDiff ℝ (2 : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from f) i i z) * g z ∂volume =
      -∫ z : Vec3 × ℝ, ∑ i : Fin 3,
        spatialPartial (show ParabolicPoint → ℝ from f) i z *
          spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume := by
  have hf1 : ContDiff ℝ (1 : ℕ∞) f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ (1 : ℕ∞) g := hg.of_le (by norm_num)
  have hgpc (i : Fin 3) : HasCompactSupport (fun z : Vec3 × ℝ =>
      spatialPartial (show ParabolicPoint → ℝ from g) i z) :=
    spatialPartial_hasCompactSupport hg1 hgc i
  have hAint (i : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      spatialSecondPartial (show ParabolicPoint → ℝ from f) i i z * g z) volume := by
    have hpi := spatialPartial_contDiff_one hf i
    have hppi : Continuous (fun z : Vec3 × ℝ => spatialSecondPartial
        (show ParabolicPoint → ℝ from f) i i z) := by
      change Continuous (fun z : Vec3 × ℝ => spatialPartial
        (fun w => spatialPartial (show ParabolicPoint → ℝ from f) i w) i z)
      exact spatialPartial_continuous hpi i
    exact (hppi.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left (f := fun z => spatialSecondPartial
        (show ParabolicPoint → ℝ from f) i i z))
  have hBint (i : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      spatialPartial (show ParabolicPoint → ℝ from f) i z *
        spatialPartial (show ParabolicPoint → ℝ from g) i z) volume := by
    have hpi := spatialPartial_contDiff_one hf i
    have hqi := spatialPartial_contDiff_one hg i
    exact (hpi.continuous.mul hqi.continuous).integrable_of_hasCompactSupport
      (hgpc i |>.mul_left (f := fun z => spatialPartial
        (show ParabolicPoint → ℝ from f) i z))
  have hsumA :
      ∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from f) i i z) * g z ∂volume =
        ∑ i : Fin 3, ∫ z : Vec3 × ℝ, spatialSecondPartial
          (show ParabolicPoint → ℝ from f) i i z * g z ∂volume := by
    simp_rw [Finset.sum_mul]
    simpa using (integral_finsetSum (μ := volume) Finset.univ
      (f := fun (i : Fin 3) (z : Vec3 × ℝ) => spatialSecondPartial
        (show ParabolicPoint → ℝ from f) i i z * g z)
      (by intro i hi; exact hAint i))
  have hsumB :
      ∫ z : Vec3 × ℝ, ∑ i : Fin 3,
        spatialPartial (show ParabolicPoint → ℝ from f) i z *
          spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume =
        ∑ i : Fin 3, ∫ z : Vec3 × ℝ,
          spatialPartial (show ParabolicPoint → ℝ from f) i z *
            spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume := by
    simpa using (integral_finsetSum (μ := volume) Finset.univ
      (f := fun (i : Fin 3) (z : Vec3 × ℝ) => spatialPartial
        (show ParabolicPoint → ℝ from f) i z * spatialPartial
        (show ParabolicPoint → ℝ from g) i z)
      (by intro i hi; exact hBint i))
  calc
    ∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from f) i i z) * g z ∂volume
      = ∑ i : Fin 3, ∫ z : Vec3 × ℝ, spatialSecondPartial
          (show ParabolicPoint → ℝ from f) i i z * g z ∂volume := hsumA
    _ = ∑ i : Fin 3, -(∫ z : Vec3 × ℝ,
          spatialPartial (show ParabolicPoint → ℝ from f) i z *
            spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact integral_spatialSecondPartial_mul_eq_neg_gradient hf hg hgc i
    _ = -∫ z : Vec3 × ℝ, ∑ i : Fin 3,
          spatialPartial (show ParabolicPoint → ℝ from f) i z *
            spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume := by
          rw [hsumB]
          simp [Finset.sum_neg_distrib]

theorem integral_spatial_laplacian_pairing
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ∞) f)
    (hg : ContDiff ℝ (2 : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from f) i i z) * g z ∂volume) =
      -(∫ z : Vec3 × ℝ, ∑ i : Fin 3,
        spatialPartial (show ParabolicPoint → ℝ from f) i z *
          spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume) ∧
    -(∫ z : Vec3 × ℝ, ∑ i : Fin 3,
        spatialPartial (show ParabolicPoint → ℝ from f) i z *
          spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume) =
      ∫ z : Vec3 × ℝ, f z *
        (∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from g) i i z) ∂volume := by
  have hfirst := integral_spatialLaplacian_mul_eq_neg_gradient_pairing hf hg hgc
  have hswap := integral_spatialLaplacian_mul_eq_neg_gradient_pairing hg hf hfc
  have hgrad :
      (∫ z : Vec3 × ℝ, ∑ i : Fin 3,
        spatialPartial (show ParabolicPoint → ℝ from g) i z *
          spatialPartial (show ParabolicPoint → ℝ from f) i z ∂volume) =
        ∫ z : Vec3 × ℝ, ∑ i : Fin 3,
          spatialPartial (show ParabolicPoint → ℝ from f) i z *
            spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with z
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlap :
      (∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from g) i i z) * f z ∂volume) =
        ∫ z : Vec3 × ℝ, f z *
          (∑ i : Fin 3, spatialSecondPartial
            (show ParabolicPoint → ℝ from g) i i z) ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  constructor
  · exact hfirst
  · calc
      -(∫ z : Vec3 × ℝ, ∑ i : Fin 3,
          spatialPartial (show ParabolicPoint → ℝ from f) i z *
            spatialPartial (show ParabolicPoint → ℝ from g) i z ∂volume)
          = -(∫ z : Vec3 × ℝ, ∑ i : Fin 3,
              spatialPartial (show ParabolicPoint → ℝ from g) i z *
                spatialPartial (show ParabolicPoint → ℝ from f) i z ∂volume) := by
                exact congrArg Neg.neg hgrad.symm
      _ = ∫ z : Vec3 × ℝ,
          (∑ i : Fin 3, spatialSecondPartial
            (show ParabolicPoint → ℝ from g) i i z) * f z ∂volume := hswap.symm
      _ = ∫ z : Vec3 × ℝ, f z *
          (∑ i : Fin 3, spatialSecondPartial
            (show ParabolicPoint → ℝ from g) i i z) ∂volume := hlap

end CKN
