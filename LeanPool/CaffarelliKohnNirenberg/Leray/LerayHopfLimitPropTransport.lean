/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropSpatialIBP
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The regularized transport velocity on one time slice

On each time slice the transport velocity `J_ε u` of `thm:regularised` is the
spatial convolution of the velocity slice with the smooth compactly
supported profile. It is therefore smooth, pointwise divergence-free when the
slice is weakly divergence-free, and bounded in `L²` by the slice. These are
the properties of `J_ε u` used in the proof of `lem:reg-equicontinuity`.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The square integral of a real `L²` function is its squared `L²` norm. -/
theorem lerayHopfLimit_integral_sq_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : MemLp h 2 μ) :
    ∫ x, h x ^ 2 ∂μ = (eLpNorm h 2 μ).toReal ^ 2 := by
  have h1 : ‖hh.toLp h‖ ^ 2 = inner ℝ (hh.toLp h) (hh.toLp h) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [Lp.norm_toLp] at h1
  rw [h1, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp] with x hx
  rw [hx]
  simp [pow_two]

/-- A coordinate of a square-integrable Euclidean field has square integral at
most the squared `L²` norm of the field. -/
theorem lerayHopfLimit_integral_component_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → L2Vec3} (hg : MemLp g 2 μ) (j : Fin 3) :
    MemLp (fun x => g x j) 2 μ ∧
      ∫ x, g x j ^ 2 ∂μ ≤ (eLpNorm g 2 μ).toReal ^ 2 := by
  have hj : MemLp (fun x => g x j) 2 μ :=
    hg.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)
  refine ⟨hj, ?_⟩
  rw [lerayHopfLimit_integral_sq_eq hj]
  have hle : eLpNorm (fun x => g x j) 2 μ ≤ eLpNorm g 2 μ := by
    refine eLpNorm_mono hj.aestronglyMeasurable (fun x => ?_)
    exact PiLp.norm_apply_le (g x) j
  have hmono := ENNReal.toReal_mono hg.eLpNorm_ne_top hle
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hmono 2

/-- The Euclidean representative of a coordinate field in `L²`. -/
theorem lerayHopfLimit_toLp_memLp {f : Vec3 → Vec3} (hf : MemLp f 2 volume) :
    MemLp (fun x => (WithLp.toLp 2 (f x) : L2Vec3)) 2 volume :=
  hf.continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

private theorem physicalKernel_contDiff (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => (WithLp.toLp 2 y : L2Vec3)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff
  have hK : ContDiff ℝ (⊤ : ℕ∞) (regMollifierKernel ρ ε hε) := by
    unfold regMollifierKernel
    exact contDiff_const.mul (ρ.smooth.comp (contDiff_const_smul _))
  exact hK.comp hL

private theorem physicalKernel_compact (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport
      (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) := by
  have hK : HasCompactSupport (regMollifierKernel ρ ε hε) := by
    unfold regMollifierKernel
    exact (ρ.compact.comp_smul (inv_ne_zero hε.ne')).mul_left
  exact hK.comp_homeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph

/-- Each coordinate of the mollified field is smooth. -/
theorem lerayHopfLimit_mollifiedInitial_contDiff
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : Vec3 → Vec3} (hf : MemLp f 2 volume) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => regUniformMollifiedInitial ρ ε hε f x i) := by
  have heq : (fun x => regUniformMollifiedInitial ρ ε hε f x i) =
      MeasureTheory.convolution
        (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y))
        (fun y : Vec3 => f y i) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    exact regUniformMollifiedInitial_component_convolution ρ ε hε hf x i
  rw [heq]
  exact (physicalKernel_compact ρ ε hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (physicalKernel_contDiff ρ ε hε)
    ((hf.eval i).locallyIntegrable (by norm_num))

/-- A continuously differentiable field whose weak divergence vanishes against
every smooth compactly supported test is pointwise divergence-free. -/
theorem lerayHopfLimit_divergence_eq_zero_of_weak
    (F : Vec3 → Vec3) (hF : ∀ i, ContDiff ℝ 1 (fun x => F x i))
    (hweak : ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x, ∑ i : Fin 3, F x i * ψ.partialDeriv i x = 0) :
    ∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => F y i) x (basisVec i) = 0 := by
  let d : Vec3 → ℝ := fun x => ∑ i : Fin 3, fderiv ℝ (fun y => F y i) x (basisVec i)
  have hdi : ∀ i, Continuous (fun x => fderiv ℝ (fun y => F y i) x (basisVec i)) :=
    fun i => ((hF i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hd : Continuous d := continuous_finsetSum _ (fun i _ => hdi i)
  have hFc : ∀ i, Continuous (fun x => F x i) := fun i => (hF i).continuous
  have hFd : ∀ i x, DifferentiableAt ℝ (fun y => F y i) x :=
    fun i x => ((hF i).differentiable (by norm_num)) x
  have hzero : ∀ g : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∫ x, g x • d x = 0 := by
    intro g hg hgc
    have hgd : ∀ i, Continuous (fun x => fderiv ℝ g x (basisVec i)) :=
      fun i => (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    have hgdc : ∀ i, HasCompactSupport (fun x => fderiv ℝ g x (basisVec i)) :=
      fun i => hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hibp : ∀ i, ∫ x, F x i * fderiv ℝ g x (basisVec i) =
        -∫ x, fderiv ℝ (fun y => F y i) x (basisVec i) * g x := by
      intro i
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (lerayHopfLimit_integrable_mul_compact (hdi i) hg.continuous hgc)
        (lerayHopfLimit_integrable_mul_compact (hFc i) (hgd i) (hgdc i))
        (lerayHopfLimit_integrable_mul_compact (hFc i) hg.continuous hgc)
        (fun x _ => hFd i x) (fun x _ => (hg.differentiable (by simp)) x)
    let ψ : WeakTestFunction (Set.univ : Set Vec3) :=
      ⟨g, hg, hgc, Set.subset_univ _⟩
    have hw := hweak ψ
    have hsplit : ∫ x, ∑ i : Fin 3, F x i * ψ.partialDeriv i x =
        ∑ i : Fin 3, ∫ x, F x i * fderiv ℝ g x (basisVec i) := by
      rw [integral_finsetSum]
      · rfl
      · intro i _
        exact lerayHopfLimit_integrable_mul_compact (hFc i) (hgd i) (hgdc i)
    have hsplit2 : ∫ x, g x • d x =
        ∑ i : Fin 3, ∫ x, fderiv ℝ (fun y => F y i) x (basisVec i) * g x := by
      rw [← integral_finsetSum]
      · congr 1
        funext x
        simp only [d, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      · intro i _
        exact lerayHopfLimit_integrable_mul_compact (hdi i) hg.continuous hgc
    rw [hsplit2]
    rw [hsplit] at hw
    simp only [hibp, Finset.sum_neg_distrib] at hw
    linarith only [hw]
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hd.locallyIntegrable) hzero
  have heq : d = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq volume hd continuous_const).mp hae
  intro x
  exact congrFun heq x

/-- The mollification of a weakly divergence-free `L²` field is pointwise
divergence-free. -/
theorem lerayHopfLimit_mollifiedInitial_divergence_eq_zero
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : Vec3 → Vec3} (hf : IsWeakDivFreeL2 f) :
    ∀ x, ∑ j : Fin 3,
      fderiv ℝ (fun y => regUniformMollifiedInitial ρ ε hε f y j) x (basisVec j) = 0 := by
  have hJ : IsInJ (regUniformMollifiedInitial ρ ε hε f) :=
    regMollifiedInitial_isInJ ρ ε hε (weakDivFreeL2_isInJ hf)
  exact lerayHopfLimit_divergence_eq_zero_of_weak _
    (fun i => (lerayHopfLimit_mollifiedInitial_contDiff ρ ε hε hf.1 i).of_le
      (by exact_mod_cast le_top))
    (isInJ_weakDivFree hJ).2

/-- The coordinates of the mollified field are square integrable, with
square integral bounded by the squared `L²` norm of the field. -/
theorem lerayHopfLimit_mollifiedInitial_component_sq_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : Vec3 → Vec3} (hf : MemLp f 2 volume) (j : Fin 3) :
    MemLp (fun x => regUniformMollifiedInitial ρ ε hε f x j) 2 volume ∧
      ∫ x, regUniformMollifiedInitial ρ ε hε f x j ^ 2 ≤
        (eLpNorm (regUniformSpatialField f) 2 volume).toReal ^ 2 := by
  have hF : MemLp (regUniformSpatialField f) 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => f (WithLp.ofLp x)) 2 volume :=
      hf.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  let G : L2Vec3 → L2Vec3 := regMollifyVector ρ ε hε (regUniformSpatialField f)
  have hGle : eLpNorm G 2 volume ≤ eLpNorm (regUniformSpatialField f) 2 volume :=
    regMollifyVector_eLpNorm_two_le ρ ε hε hF
  have hG : MemLp G 2 volume :=
    memLp_iff.mpr (hGle.trans_lt hF.eLpNorm_lt_top)
  have hcomp : MemLp (fun x : Vec3 => G (WithLp.toLp 2 x)) 2 volume :=
    hG.comp_measurePreserving vec3ToL2Vec3_measurePreserving
  have hcompNorm : eLpNorm (fun x : Vec3 => G (WithLp.toLp 2 x)) 2 volume =
      eLpNorm G 2 volume :=
    eLpNorm_comp_measurePreserving hG.aestronglyMeasurable
      vec3ToL2Vec3_measurePreserving
  obtain ⟨hmem, hle⟩ := lerayHopfLimit_integral_component_sq_le hcomp j
  refine ⟨hmem, ?_⟩
  refine hle.trans ?_
  rw [hcompNorm]
  have hmono := ENNReal.toReal_mono hF.eLpNorm_ne_top hGle
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hmono 2

end CKN.Leray

end
