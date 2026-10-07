/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildNonlinearity
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierAllDerivatives

/-!
# Smoothness of regularized L² fields

Convolution by the fixed smooth compactly supported mollifier maps every
spatial L² field into a smooth coordinate field. The input need not be
divergence free when it is a difference in the local Lipschitz estimate.
-/

public section

open MeasureTheory
open scoped Convolution ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Mollification of an arbitrary coordinate L² field is spatially smooth. -/
theorem regUniformMollifiedInitial_contDiff_of_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (regUniformMollifiedInitial ρ ε hε a) := by
  let f := regUniformSpatialField a
  have hinput : MemLp f (2 : ℝ≥0∞) volume :=
    lerayHopfLimit_initialField_memLp a ha
  have hloc : LocallyIntegrable f volume := hinput.locallyIntegrable (by norm_num)
  have hkernelSmooth : ContDiff ℝ (⊤ : ℕ∞) (regMollifierKernel ρ ε hε) := by
    have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun y : L2Vec3 => ε⁻¹ • y) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : L2Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
    exact contDiff_const.mul (ρ.smooth.comp hscale)
  have hkernelCompact : HasCompactSupport (regMollifierKernel ρ ε hε) := by
    unfold regMollifierKernel
    have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
    have hcomp := ρ.compact.comp_homeomorph
      (Homeomorph.smulOfNeZero ε⁻¹ hscaleNe)
    exact hcomp.mul_left
  have hconv : ContDiff ℝ (⊤ : ℕ∞)
      (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        allDerivativeScalarVectorAction volume) :=
    hkernelCompact.contDiff_convolution_left
      (L := allDerivativeScalarVectorAction) hkernelSmooth hloc
  have hto : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => WithLp.toLp 2 x) := by
    fun_prop
  let e : L2Vec3 ≃L[ℝ] Vec3 := PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 => ℝ)
  have hcoordinate : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
      e (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        allDerivativeScalarVectorAction volume (WithLp.toLp 2 x))) := by
    exact e.toContinuousLinearMap.contDiff.comp (hconv.comp hto)
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
    e (regMollifyVector ρ ε hε f (WithLp.toLp 2 x)))
  exact hcoordinate

end CKN.Leray

end
