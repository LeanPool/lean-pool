/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedCancellation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The mollified transport field

The transport velocity `J_ε a` of `eq:reg-mild-forced` is the convolution of
a divergence-free `L²` field with a smooth compactly supported kernel. It is
smooth, bounded with bounded first derivatives, and divergence free at every
point; these are the hypotheses of the transport cancellation.
-/

public section

open MeasureTheory Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology Convolution

noncomputable section

namespace CKN.Leray

/-- The physical form of the regularizing kernel. -/
@[expose]
def forcedTransportKernel (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) : Vec3 → ℝ :=
  fun y => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)

theorem forcedTransportKernel_contDiff (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (forcedTransportKernel ρ ε hε) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (regMollifierKernel ρ ε hε) := by
    have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun x : L2Vec3 => ε⁻¹ • x) := by fun_prop
    exact contDiff_const.mul (ρ.smooth.comp hscale)
  exact hk.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff

theorem forcedTransportKernel_hasCompactSupport (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) : HasCompactSupport (forcedTransportKernel ρ ε hε) := by
  have hk : HasCompactSupport (regMollifierKernel ρ ε hε) := by
    have hcompact := ρ.compact.comp_homeomorph
      (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε.ne'))
    change HasCompactSupport (fun x => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • x))
    exact hcompact.mul_left
  exact hk.comp_homeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph

theorem forcedTransport_component_eq {ρ : RegMollifierProfile} {ε : ℝ} (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a 2 volume) (x : Vec3) (i : Fin 3) :
    regUniformMollifiedInitial ρ ε hε a x i =
      (forcedTransportKernel ρ ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y => a y i) x :=
  regUniformMollifiedInitial_component_convolution ρ ε hε ha x i

/-- The components of the mollified transport field are smooth. -/
theorem forcedTransport_contDiff {ρ : RegMollifierProfile} {ε : ℝ} (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a 2 volume) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => regUniformMollifiedInitial ρ ε hε a x i) := by
  have hloc : LocallyIntegrable (fun y => a y i) volume :=
    (ha.eval i).locallyIntegrable (by norm_num)
  have h := (forcedTransportKernel_hasCompactSupport ρ ε hε).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := 1)
    ((forcedTransportKernel_contDiff ρ ε hε).of_le (by simp)) hloc
  have hfun : (fun x => regUniformMollifiedInitial ρ ε hε a x i) =
      (forcedTransportKernel ρ ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y => a y i) := by
    funext x
    exact forcedTransport_component_eq hε ha x i
  rw [hfun]
  exact h

/-- A scalar convolution of an `L²` kernel with an `L²` function is bounded by
the product of the norms. -/
theorem norm_convolution_le_of_memLp_two {κ f : Vec3 → ℝ} (hκ : MemLp κ 2 volume)
    (hf : MemLp f 2 volume) (x : Vec3) :
    ‖(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖ ≤
      (eLpNorm κ 2 volume * eLpNorm f 2 volume).toReal := by
  have h := enorm_convolution_le (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (p := 2) (q := 2) hκ.aestronglyMeasurable hf.aestronglyMeasurable x
  have hL : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    have hn : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_lsmul_le
    exact ENNReal.ofReal_le_one.2 hn
  have hfin : eLpNorm κ 2 volume * eLpNorm f 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top hκ.eLpNorm_ne_top hf.eLpNorm_ne_top
  have h' : ‖(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖ₑ ≤
      eLpNorm κ 2 volume * eLpNorm f 2 volume := by
    refine h.trans ?_
    rw [mul_assoc]
    calc ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ *
          (eLpNorm κ 2 volume * eLpNorm f 2 volume)
        ≤ 1 * (eLpNorm κ 2 volume * eLpNorm f 2 volume) := by gcongr
      _ = eLpNorm κ 2 volume * eLpNorm f 2 volume := one_mul _
  rw [← ofReal_norm] at h'
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h'

/-- The kernel derivative in a coordinate direction is square integrable. -/
theorem forcedTransportKernel_deriv_memLp (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (i : Fin 3) :
    MemLp (fun y => fderiv ℝ (forcedTransportKernel ρ ε hε) y (CKN.basisVec i)) 2 volume := by
  have hcont : Continuous fun y => fderiv ℝ (forcedTransportKernel ρ ε hε) y (CKN.basisVec i) :=
    ((forcedTransportKernel_contDiff ρ ε hε).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hsupp : HasCompactSupport fun y =>
      fderiv ℝ (forcedTransportKernel ρ ε hε) y (CKN.basisVec i) :=
    ((forcedTransportKernel_hasCompactSupport ρ ε hε).fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) (by simp)
  exact hcont.memLp_of_hasCompactSupport hsupp

/-- The coordinate derivative of a transport component is the convolution
with the kernel derivative. -/
theorem forcedTransport_fderiv_eq {ρ : RegMollifierProfile} {ε : ℝ} (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a 2 volume) (x : Vec3) (i k : Fin 3) :
    fderiv ℝ (fun y => regUniformMollifiedInitial ρ ε hε a y i) x (CKN.basisVec k) =
      ((fun y => fderiv ℝ (forcedTransportKernel ρ ε hε) y (CKN.basisVec k)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => a y i) x := by
  have hfun : (fun y => regUniformMollifiedInitial ρ ε hε a y i) =
      (forcedTransportKernel ρ ε hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y => a y i) := by
    funext y
    exact forcedTransport_component_eq hε ha y i
  have h := regularisedScalarConvolution_iterated_derivative 1 (fun _ => k)
    (forcedTransportKernel ρ ε hε) (forcedTransportKernel_contDiff ρ ε hε)
    (forcedTransportKernel_hasCompactSupport ρ ε hε) (ha.eval i) x
  simp only [iteratedFDeriv_one_apply] at h
  rw [hfun]
  exact h

/-- The mollified transport field and its diagonal derivatives are uniformly
bounded. -/
theorem forcedTransport_bounded {ρ : RegMollifierProfile} {ε : ℝ} (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a 2 volume) :
    ∃ M : ℝ, (∀ x i, ‖regUniformMollifiedInitial ρ ε hε a x i‖ ≤ M) ∧
      ∀ x i, ‖fderiv ℝ (fun y => regUniformMollifiedInitial ρ ε hε a y i) x
        (CKN.basisVec i)‖ ≤ M := by
  have hκ : MemLp (forcedTransportKernel ρ ε hε) 2 volume :=
    (forcedTransportKernel_contDiff ρ ε hε).continuous.memLp_of_hasCompactSupport
      (forcedTransportKernel_hasCompactSupport ρ ε hε)
  let M0 : Fin 3 → ℝ := fun i => (eLpNorm (forcedTransportKernel ρ ε hε) 2 volume *
    eLpNorm (fun y => a y i) 2 volume).toReal
  let M1 : Fin 3 → ℝ := fun i =>
    (eLpNorm (fun y => fderiv ℝ (forcedTransportKernel ρ ε hε) y (CKN.basisVec i)) 2 volume *
      eLpNorm (fun y => a y i) 2 volume).toReal
  refine ⟨∑ i, (M0 i + M1 i), fun x i => ?_, fun x i => ?_⟩
  · rw [forcedTransport_component_eq hε ha]
    refine (norm_convolution_le_of_memLp_two hκ (ha.eval i) x).trans ?_
    exact (le_add_of_nonneg_right ENNReal.toReal_nonneg).trans
      (Finset.single_le_sum (f := fun i => M0 i + M1 i)
        (fun j _ => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (Finset.mem_univ i))
  · rw [forcedTransport_fderiv_eq hε ha]
    refine (norm_convolution_le_of_memLp_two (forcedTransportKernel_deriv_memLp ρ ε hε i)
      (ha.eval i) x).trans ?_
    exact (le_add_of_nonneg_left ENNReal.toReal_nonneg).trans
      (Finset.single_le_sum (f := fun i => M0 i + M1 i)
        (fun j _ => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (Finset.mem_univ i))

/-- The mollified transport field of a divergence-free field is divergence
free at every point. -/
theorem forcedTransport_div_eq_zero {ρ : RegMollifierProfile} {ε : ℝ} (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) (x : Vec3) :
    ∑ i : Fin 3, fderiv ℝ (fun y => regUniformMollifiedInitial ρ ε hε a y i) x
      (CKN.basisVec i) = 0 := by
  set V := regUniformMollifiedInitial ρ ε hε a with hVdef
  have hVJ : CKN.IsWeakDivFreeL2 V :=
    CKN.isInJ_iff_weakDivFree.1 (regMollifiedInitial_isInJ ρ ε hε ha)
  have hsmooth : ∀ i, ContDiff ℝ 1 (fun y => V y i) := fun i => forcedTransport_contDiff hε ha.1 i
  have hdcont : ∀ i, Continuous fun y => fderiv ℝ (fun z => V z i) y (CKN.basisVec i) :=
    fun i => ((hsmooth i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  let d : Vec3 → ℝ := fun y => ∑ i : Fin 3, fderiv ℝ (fun z => V z i) y (CKN.basisVec i)
  have hd : Continuous d := continuous_finsetSum _ fun i _ => hdcont i
  have hae : ∀ᵐ y ∂(volume : Measure Vec3), d y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hd.locallyIntegrable fun g hg hgc => ?_
    have hgd : ∀ i, Continuous fun y => fderiv ℝ g y (CKN.basisVec i) := fun i =>
      (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    have hgdc : ∀ i, HasCompactSupport fun y => fderiv ℝ g y (CKN.basisVec i) := fun i =>
      (hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) (by simp)
    have hibp : ∀ i, ∫ y, g y * fderiv ℝ (fun z => V z i) y (CKN.basisVec i) =
        -∫ y, fderiv ℝ g y (CKN.basisVec i) * V y i := by
      intro i
      refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (f := g) (g := fun z => V z i) (v := CKN.basisVec i) ?_ ?_ ?_
        (fun y _ => hg.differentiable (by simp) y)
        (fun y _ => (hsmooth i).differentiable one_ne_zero y)
      · exact ((hgd i).mul (hsmooth i).continuous).integrable_of_hasCompactSupport
          ((hgdc i).mul_right)
      · exact (hg.continuous.mul (hdcont i)).integrable_of_hasCompactSupport hgc.mul_right
      · exact (hg.continuous.mul (hsmooth i).continuous).integrable_of_hasCompactSupport
          hgc.mul_right
    have hweak := hVJ.2 ⟨g, hg, hgc, Set.subset_univ _⟩
    have hint : ∀ i, Integrable fun y => g y * fderiv ℝ (fun z => V z i) y (CKN.basisVec i) :=
      fun i => (hg.continuous.mul (hdcont i)).integrable_of_hasCompactSupport hgc.mul_right
    have hint2 : ∀ i, Integrable fun y => fderiv ℝ g y (CKN.basisVec i) * V y i := fun i =>
      ((hgd i).mul (hsmooth i).continuous).integrable_of_hasCompactSupport ((hgdc i).mul_right)
    calc ∫ y, g y • d y = ∑ i : Fin 3, ∫ y, g y * fderiv ℝ (fun z => V z i) y (CKN.basisVec i) := by
          rw [← integral_finsetSum _ fun i _ => hint i]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [d, smul_eq_mul, Finset.mul_sum]
      _ = -∑ i : Fin 3, ∫ y, fderiv ℝ g y (CKN.basisVec i) * V y i := by
          simp_rw [hibp, Finset.sum_neg_distrib]
      _ = -∫ y, ∑ i : Fin 3, V y i * CKN.WeakTestFunction.partialDeriv
            ⟨g, hg, hgc, Set.subset_univ _⟩ i y := by
          rw [integral_finsetSum _ fun i _ => ?_]
          · congr 1
            refine Finset.sum_congr rfl fun i _ => integral_congr_ae
              (Eventually.of_forall fun y => ?_)
            simp only [CKN.WeakTestFunction.partialDeriv]
            ring
          · refine (hint2 i).congr (Eventually.of_forall fun y => ?_)
            simp only [CKN.WeakTestFunction.partialDeriv]
            ring
      _ = 0 := by rw [hweak, neg_zero]
  have heq : d = fun _ => 0 := (Continuous.ae_eq_iff_eq volume hd continuous_const).1 hae
  exact congrFun heq x

end CKN.Leray

end
