/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergySwap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData

/-!
# Convolution calculus for the local energy inequality

Convolutions of square-integrable fields with a smooth compactly supported
kernel are smooth, their partial derivatives are the convolutions with the
partial derivatives of the kernel, integration by parts moves these
derivatives onto a smooth compactly supported factor, and the convolution of a
weakly divergence-free field with the kernel gradient has zero trace. These
are the spatial computations of `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution

noncomputable section

namespace CKN.Leray

/-- The scalar convolution `κ ⋆ g`. -/
@[expose]
def leConv (κ g : Vec3 → ℝ) : Vec3 → ℝ := κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

section Conv

variable {κ : Vec3 → ℝ}

theorem leConv_contDiff (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) {g : Vec3 → ℝ}
    (hg : LocallyIntegrable g volume) : ContDiff ℝ (⊤ : ℕ∞) (leConv κ g) :=
  hκc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hg

theorem fderiv_leConv (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) {g : Vec3 → ℝ}
    (hg : MemLp g 2 volume) (x : Vec3) (j : Fin 3) :
    fderiv ℝ (leConv κ g) x (CKN.basisVec j) = leConv (CKN.spatialDeriv κ j) g x := by
  have h := regularisedScalarConvolution_iterated_derivative 1 (fun _ => j) κ hκ hκc hg x
  simp only [iteratedFDeriv_one_apply] at h
  exact h

theorem integral_mul_reflect_eq_leConv (g κ' : Vec3 → ℝ) (x : Vec3) :
    ∫ y, g y * κ' (x - y) = leConv κ' g x :=
  integral_mul_reflect_eq_convolution g κ' x

/-- Integration by parts of a kernel derivative against a smooth compactly
supported factor. -/
theorem integral_mul_leConv_spatialDeriv (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) {g : Vec3 → ℝ} (hg : MemLp g 2 volume) {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hac : HasCompactSupport a) (j : Fin 3) :
    ∫ x, a x * leConv (CKN.spatialDeriv κ j) g x =
      -∫ x, fderiv ℝ a x (CKN.basisVec j) * leConv κ g x := by
  have hc := leConv_contDiff hκ hκc (hg.locallyIntegrable (by norm_num))
  have hderiv : ∀ x, fderiv ℝ (leConv κ g) x (CKN.basisVec j) =
      leConv (CKN.spatialDeriv κ j) g x := fun x => fderiv_leConv hκ hκc hg x j
  have hda : Continuous fun x => fderiv ℝ a x (CKN.basisVec j) :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdac : HasCompactSupport fun x => fderiv ℝ a x (CKN.basisVec j) :=
    hac.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have h1 : Integrable fun x => fderiv ℝ a x (CKN.basisVec j) * leConv κ g x :=
    (hda.mul hc.continuous).integrable_of_hasCompactSupport (hdac.mul_right)
  have h2 : Integrable fun x => a x * fderiv ℝ (leConv κ g) x (CKN.basisVec j) := by
    simp_rw [hderiv]
    have hc' : Continuous (leConv (CKN.spatialDeriv κ j) g) :=
      (leConv_contDiff (CKN.contDiff_spatialDeriv_smooth hκ j)
        (CKN.hasCompactSupport_spatialDeriv hκc j) (hg.locallyIntegrable (by norm_num))).continuous
    exact (ha.continuous.mul hc').integrable_of_hasCompactSupport hac.mul_right
  have h3 : Integrable fun x => a x * leConv κ g x :=
    (ha.continuous.mul hc.continuous).integrable_of_hasCompactSupport hac.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := a) (g := leConv κ g) (v := CKN.basisVec j) h1 h2 h3
    (fun x _ => (ha.differentiable (by simp)) x)
    (fun x _ => (hc.differentiable (by simp)) x)
  simp_rw [hderiv] at hibp
  exact hibp

/-- The convolution of a weakly divergence-free field with the kernel gradient
has zero trace. -/
theorem sum_leConv_spatialDeriv_eq_zero (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    {u : Vec3 → Vec3} (hu : CKN.IsWeakDivFreeL2 u) (x : Vec3) :
    ∑ k : Fin 3, leConv (CKN.spatialDeriv κ k) (fun y => u y k) x = 0 := by
  let ψ : CKN.WeakTestFunction (Set.univ : Set Vec3) :=
    ⟨fun y => κ (x - y), hκ.comp (contDiff_const.sub contDiff_id),
      hκc.comp_homeomorph (Homeomorph.subLeft x), Set.subset_univ _⟩
  have hψderiv (y : Vec3) (i : Fin 3) :
      ψ.partialDeriv i y = -CKN.spatialDeriv κ i (x - y) := by
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (-(1 : Vec3 →L[ℝ] Vec3)) y := (hasFDerivAt_id y).const_sub x
    have houter : HasFDerivAt κ (fderiv ℝ κ (x - y)) (x - y) :=
      (hκ.differentiable (by simp) (x - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    change (fderiv ℝ (fun z => κ (x - z)) y) (CKN.basisVec i) = _
    simpa [ContinuousLinearMap.comp_apply, Function.comp_def, CKN.spatialDeriv] using
      congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) hcomp.fderiv
  have h := hu.2 ψ
  have hint : ∀ i : Fin 3, Integrable fun y => u y i * CKN.spatialDeriv κ i (x - y) := fun i =>
    integrable_mul_reflect (hu.1.eval i) (CKN.contDiff_spatialDeriv_smooth hκ i).continuous
      (CKN.hasCompactSupport_spatialDeriv hκc i) x
  simp_rw [hψderiv, mul_neg, Finset.sum_neg_distrib, integral_neg,
    integral_finsetSum _ fun i _ => hint i, neg_eq_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => (integral_mul_reflect_eq_leConv _ _ x).symm

end Conv

end CKN.Leray

end
