/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyMollifier
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceTrilinear
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Solenoidal slices: mollified divergence and gradient trace

The mollification of a weakly divergence-free field is divergence free, and the
trace of the weak gradient of a weakly divergence-free field vanishes
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The mollification of a weakly divergence-free field is pointwise
divergence free. -/
theorem lps_conv_div_free {a : Vec3 → Vec3} (ha : CKN.IsWeakDivFreeL2 a)
    {η : Vec3 → ℝ} (hη : IsVlKernel η) (x : Vec3) :
    ∑ i : Fin 3, vlConv (vlDeriv η i) (fun y => a y i) x = 0 := by
  let ψ : WeakTestFunction (Set.univ : Set Vec3) :=
    { toFun := fun y => η (x - y)
      contDiff := hη.1.comp (contDiff_const.sub contDiff_id)
      hasCompactSupport := hη.2.comp_homeomorph (Homeomorph.subLeft x)
      tsupport_subset := Set.subset_univ _ }
  have hψ := ha.2 ψ
  have hpartial : ∀ (i : Fin 3) (y : Vec3), ψ.partialDeriv i y = -vlDeriv η i (x - y) := by
    intro i y
    have hkd : HasFDerivAt η (fderiv ℝ η (x - y)) (x - y) :=
      ((hη.1.differentiable (by simp)) (x - y)).hasFDerivAt
    have hin : HasFDerivAt (fun z : Vec3 => x - z) (-ContinuousLinearMap.id ℝ Vec3) y :=
      (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x
    have hcomp := hkd.comp y hin
    have hfd := hcomp.fderiv
    simp only [Function.comp_def] at hfd
    simp only [WeakTestFunction.partialDeriv, ψ]
    rw [hfd]
    simp [vlDeriv]
  have hint : ∀ i : Fin 3, Integrable (fun y => a y i * vlDeriv η i (x - y)) volume := by
    intro i
    have h1 : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
    have h2 : MemLp (fun y => vlDeriv η i (x - y)) 2 volume := by
      have hcont : Continuous (fun y : Vec3 => vlDeriv η i (x - y)) :=
        (hη.deriv i).continuous.comp (continuous_const.sub continuous_id)
      exact hcont.memLp_of_hasCompactSupport
        ((hη.deriv i).2.comp_homeomorph (Homeomorph.subLeft x))
    exact h1.integrable_mul h2
  have hsum : ∑ i : Fin 3, vlConv (vlDeriv η i) (fun y => a y i) x =
      ∫ y, ∑ i : Fin 3, a y i * vlDeriv η i (x - y) := by
    rw [integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl fun i _ => vlConv_apply_swap _ _ _
  rw [hsum]
  have hneg : ∫ y, ∑ i : Fin 3, a y i * ψ.partialDeriv i y =
      -∫ y, ∑ i : Fin 3, a y i * vlDeriv η i (x - y) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hpartial, mul_neg, Finset.sum_neg_distrib]
  rw [hneg] at hψ
  linarith only [hψ]

/-- The trace of the weak gradient of a weakly divergence-free field vanishes
almost everywhere. -/
theorem lps_weak_gradient_trace_zero {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hw : CKN.IsWeakDivFreeL2 w) (hDw : MemLp Dw 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i)) :
    ∀ᵐ x ∂(volume : Measure Vec3), ∑ j : Fin 3, Dw x j j = 0 := by
  have hDj : ∀ j : Fin 3, MemLp (fun x => Dw x j j) 2 volume := fun j =>
    memLp_pi_iff.1 (memLp_pi_iff.1 hDw j) j
  have hsum : LocallyIntegrable (fun x => ∑ j : Fin 3, Dw x j j) volume :=
    (memLp_finsetSum Finset.univ fun j _ => hDj j).locallyIntegrable (by norm_num)
  have hzero := isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) (hsum.locallyIntegrableOn univ) (fun g hg hgc _ => by
      let ψ : WeakTestFunction (Set.univ : Set Vec3) :=
        { toFun := g, contDiff := hg, hasCompactSupport := hgc,
          tsupport_subset := Set.subset_univ _ }
      have hdiv := hw.2 ψ
      have hj : ∀ j : Fin 3, ∫ x, w x j * ψ.partialDeriv j x = -∫ x, Dw x j j * g x := by
        intro j
        have := hgrad j j g hg hgc (Set.subset_univ _)
        simpa [Measure.restrict_univ, WeakTestFunction.partialDeriv, ψ] using this
      have hgL2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
      have hint : ∀ j : Fin 3, Integrable (fun x => Dw x j j * g x) volume := fun j =>
        (hDj j).integrable_mul hgL2
      have hint2 : ∀ j : Fin 3, Integrable (fun x => w x j * ψ.partialDeriv j x) volume := by
        intro j
        have h1 : MemLp (fun x => w x j) 2 volume := memLp_pi_iff.1 hw.1 j
        have hcont : Continuous (fun x : Vec3 => ψ.partialDeriv j x) :=
          (hg.continuous_fderiv (by simp)).clm_apply continuous_const
        have hsupp : HasCompactSupport (fun x : Vec3 => ψ.partialDeriv j x) :=
          hgc.fderiv_apply (𝕜 := ℝ) _
        have h2 : MemLp (fun x : Vec3 => ψ.partialDeriv j x) 2 volume :=
          hcont.memLp_of_hasCompactSupport hsupp
        exact h1.integrable_mul h2
      simp only [smul_eq_mul]
      have e1 : ∫ x, g x * ∑ j : Fin 3, Dw x j j = ∑ j : Fin 3, ∫ x, Dw x j j * g x := by
        rw [← integral_finsetSum _ (fun j _ => hint j)]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        change g x * ∑ j : Fin 3, Dw x j j = ∑ j : Fin 3, Dw x j j * g x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have e2 : ∫ x, ∑ j : Fin 3, w x j * ψ.partialDeriv j x =
          ∑ j : Fin 3, ∫ x, w x j * ψ.partialDeriv j x :=
        integral_finsetSum _ (fun j _ => hint2 j)
      rw [e1]
      simp only [hj] at e2
      rw [Finset.sum_neg_distrib] at e2
      linarith only [hdiv, e2])
  filter_upwards [hzero] with x hx
  exact hx (Set.mem_univ x)

end ESS.LPS

end
