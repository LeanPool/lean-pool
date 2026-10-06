/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorDerivative
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Reg Uniform Momentum

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal Convolution

noncomputable section

namespace CKN.Leray

local instance : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

private theorem regularised_parameter_convolution_continuous
    {κ : Vec3 → ℝ} {S : Set (Vec3 × ℝ)} {F : Vec3 × ℝ → ℝ}
    (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hF : ContinuousOn F S)
    (hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S) :
    ContinuousOn (fun z : Vec3 × ℝ =>
      ∫ y : Vec3, κ y * F (z.1 - y, z.2) ∂volume) S := by
  let G : (Vec3 × ℝ) → Vec3 → ℝ := fun z y => κ y * F (z.1 - y, z.2)
  have hG : ContinuousOn G.uncurry (S ×ˢ Set.univ) := by
    have hshift : Continuous
        (fun q : (Vec3 × ℝ) × Vec3 => (q.1.1 - q.2, q.1.2)) := by
      fun_prop
    have hshiftS : Set.MapsTo (fun q : (Vec3 × ℝ) × Vec3 =>
        (q.1.1 - q.2, q.1.2)) (S ×ˢ Set.univ) S := by
      rintro ⟨z, y⟩ ⟨hz, hy⟩
      exact hSshift z hz y
    have hFcomp : ContinuousOn
        (fun q : (Vec3 × ℝ) × Vec3 => F (q.1.1 - q.2, q.1.2))
        (S ×ˢ Set.univ) := by
      exact hF.comp (hshift.continuousOn) hshiftS
    have hκcomp : ContinuousOn
        (fun q : (Vec3 × ℝ) × Vec3 => κ q.2) (S ×ˢ Set.univ) :=
      (hκ.comp continuous_snd).continuousOn
    change ContinuousOn
      (fun q : (Vec3 × ℝ) × Vec3 => κ q.2 * F (q.1.1 - q.2, q.1.2))
      (S ×ˢ Set.univ)
    exact hκcomp.mul hFcomp
  have hGzero : ∀ z : Vec3 × ℝ, ∀ y : Vec3, z ∈ S →
      y ∉ tsupport κ → G z y = 0 := by
    intro z y hz hy
    simp [G, image_eq_zero_of_notMem_tsupport hy]
  exact continuousOn_integral_of_compact_support hκc hG hGzero

@[expose]
def regUniformPhysicalKernel (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) : Vec3 → ℝ :=
  fun x => regMollifierKernel ρ ε hε (WithLp.toLp 2 x)

private theorem regUniformPhysicalKernel_smooth
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regUniformPhysicalKernel ρ ε hε) := by
  have hto : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => WithLp.toLp 2 x) := by
    fun_prop
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • WithLp.toLp 2 x))
  exact contDiff_const.mul
    (ρ.smooth.comp ((contDiff_const_smul ε⁻¹).comp hto))

private theorem regUniformPhysicalKernel_compact
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (regUniformPhysicalKernel ρ ε hε) := by
  have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
  let hhomeo : Vec3 ≃ₜ L2Vec3 := CKN.Foundation.Parabolic.vec3Homeomorph
  let hscale : L2Vec3 ≃ₜ L2Vec3 := Homeomorph.smulOfNeZero ε⁻¹ hscaleNe
  have hcompact : HasCompactSupport (fun x : Vec3 => ρ.rho (hscale (hhomeo x))) :=
    ρ.compact.comp_homeomorph (hhomeo.trans hscale)
  change HasCompactSupport
    (fun x : Vec3 => (ε ^ 3)⁻¹ * ρ.rho (hscale (hhomeo x)))
  exact hcompact.mul_left

private theorem regUniformMollifiedVelocity_component_convolution
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hSlice : MemLp (fun x : Vec3 => u (x, t)) (2 : ℝ≥0∞) volume)
    (x : Vec3) (i : Fin 3) :
    regUniformMollifiedVelocity ρ ε hε u (x, t) i =
      ∫ y : Vec3, regUniformPhysicalKernel ρ ε hε y * u (x - y, t) i ∂volume := by
  have h := regUniformMollifiedInitial_component_convolution ρ ε hε
    (a := fun y : Vec3 => u (y, t)) hSlice x i
  change WithLp.ofLp
      (regMollifyVector ρ ε hε
        (regUniformSpatialField (fun y : Vec3 => u (y, t))) (WithLp.toLp 2 x)) i = _
  exact h

/-- Spatial convolution of a regularized velocity is continuous on positive time. -/
theorem regUniform_mollified_velocity_continuousOn
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {u : ParabolicPoint → Vec3} {S : Set (Vec3 × ℝ)}
    (hSlice : ∀ t : ℝ, 0 < t →
      MemLp (fun x : Vec3 => u (x, t)) (2 : ℝ≥0∞) volume)
    (hU : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i) S)
    (hSpositive : ∀ z ∈ S, 0 < z.2)
    (hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S) :
    ∀ i : Fin 3,
      ContinuousOn (fun z : Vec3 × ℝ =>
        regUniformMollifiedVelocity ρ ε hε u z i) S := by
  intro i
  have hF : ContinuousOn (fun z : Vec3 × ℝ => u z i) S := (hU i).continuousOn
  have hconv := regularised_parameter_convolution_continuous
    (regUniformPhysicalKernel_smooth ρ ε hε).continuous
    (regUniformPhysicalKernel_compact ρ ε hε) hF hSshift
  apply hconv.congr
  intro z hz
  exact regUniformMollifiedVelocity_component_convolution
    ρ ε hε u z.2 (hSlice z.2 (hSpositive z hz)) z.1 i

private theorem regUniformMollifiedVelocity_spatialPartial_convolution
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hSlice : MemLp (fun x : Vec3 => u (x, t)) (2 : ℝ≥0∞) volume)
    (x : Vec3) (i j : Fin 3) :
    spatialPartial (fun y => regUniformMollifiedVelocity ρ ε hε u y i) j
      (x, t) =
        ∫ y : Vec3,
          (fderiv ℝ (regUniformPhysicalKernel ρ ε hε) y) (basisVec j) *
            u (x - y, t) i ∂volume := by
  let κ := regUniformPhysicalKernel ρ ε hε
  let f : Vec3 → ℝ := fun y => u (y, t) i
  have hκsmooth : ContDiff ℝ 2 κ :=
    (regUniformPhysicalKernel_smooth ρ ε hε).of_le (by norm_num)
  have hκcompact : HasCompactSupport κ := regUniformPhysicalKernel_compact ρ ε hε
  have hloc : LocallyIntegrable f volume :=
    (memLp_pi_iff.mp hSlice i).locallyIntegrable (by norm_num)
  have hkernel1 : ContDiff ℝ 1 κ := hκsmooth.of_le (by norm_num)
  have hfd := hκcompact.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hkernel1 hloc x
  have hconvD : ConvolutionExists (fderiv ℝ κ) f
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3) volume := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec3) (E := Vec3 →L[ℝ] ℝ) (E' := ℝ)
      (F := Vec3 →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3)
      (hκcompact.fderiv (𝕜 := ℝ))
      (hκsmooth.continuous_fderiv (by norm_num)) hloc
  have hvalue (y : Vec3) :
      regUniformMollifiedVelocity ρ ε hε u (y, t) i =
        MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ)
          volume y := by
    simpa [κ, f, MeasureTheory.convolution] using
      regUniformMollifiedVelocity_component_convolution
        ρ ε hε u t hSlice y i
  change (fderiv ℝ
      (fun y : Vec3 => regUniformMollifiedVelocity ρ ε hε u (y, t) i) x)
      (basisVec j) = _
  rw [show (fun y : Vec3 => regUniformMollifiedVelocity ρ ε hε u (y, t) i) =
      fun y => MeasureTheory.convolution κ f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume y from funext hvalue]
  rw [hfd.fderiv, MeasureTheory.convolution,
    ContinuousLinearMap.integral_apply (hconvD x) (basisVec j)]
  simp [κ, f, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- Spatial derivatives of the regularized transport velocity are continuous on positive time. -/
theorem regUniform_mollified_velocity_spatialPartial_continuousOn
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {u : ParabolicPoint → Vec3} {S : Set (Vec3 × ℝ)}
    (hSlice : ∀ t : ℝ, 0 < t →
      MemLp (fun x : Vec3 => u (x, t)) (2 : ℝ≥0∞) volume)
    (hU : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i) S)
    (hSpositive : ∀ z ∈ S, 0 < z.2)
    (hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S) :
    ∀ i j : Fin 3,
      ContinuousOn
        (fun z : Vec3 × ℝ => spatialPartial
          (fun y => regUniformMollifiedVelocity ρ ε hε u y i) j z) S := by
  intro i j
  let κ := regUniformPhysicalKernel ρ ε hε
  let κj : Vec3 → ℝ := fun y => (fderiv ℝ κ y) (basisVec j)
  have hκjCont : Continuous κj := by
    exact (regUniformPhysicalKernel_smooth ρ ε hε).continuous_fderiv
      (by norm_num) |>.clm_apply continuous_const
  have hκjCompact : HasCompactSupport κj :=
    (regUniformPhysicalKernel_compact ρ ε hε).fderiv_apply
      (𝕜 := ℝ) (basisVec j)
  have hF : ContinuousOn (fun z : Vec3 × ℝ => u z i) S := (hU i).continuousOn
  have hconv := regularised_parameter_convolution_continuous
    hκjCont hκjCompact hF hSshift
  apply hconv.congr
  intro z hz
  exact regUniformMollifiedVelocity_spatialPartial_convolution
    ρ ε hε u z.2 (hSlice z.2 (hSpositive z hz)) z.1 i j

/-- A continuously differentiable weakly divergence-free field has zero
classical divergence at every point. -/
theorem regUniform_weakDivFree_contDiff_divergence_eq_zero
    {f : Vec3 → Vec3}
    (hC1 : ∀ i : Fin 3, ContDiff ℝ 1 (fun x : Vec3 => f x i))
    (hdiv : CKN.IsWeakDivFreeL2 f) :
    ∀ x : Vec3, ∑ i : Fin 3,
      (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i) = 0 := by
  let divF : Vec3 → ℝ := fun x => ∑ i : Fin 3,
    (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i)
  have hderivCont (i : Fin 3) : Continuous
      (fun x : Vec3 => (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i)) := by
    exact (hC1 i).continuous_fderiv (by norm_num) |>.clm_apply continuous_const
  have hdivCont : Continuous divF := by
    exact continuous_finsetSum Finset.univ fun i _ => hderivCont i
  have hdivLoc : LocallyIntegrable divF volume := hdivCont.locallyIntegrable
  have hpair (ψ : Vec3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hψc : HasCompactSupport ψ) : ∫ x : Vec3, ψ x * divF x ∂volume = 0 := by
    let ψW : CKN.WeakTestFunction (Set.univ : Set Vec3) :=
      ⟨ψ, hψ, hψc, Set.subset_univ _⟩
    have hweak := hdiv.2 ψW
    have hparts (i : Fin 3) :
        ∫ x : Vec3, (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i) * ψ x ∂volume =
          -∫ x : Vec3, f x i * (fderiv ℝ ψ x) (basisVec i) ∂volume := by
      let Fi : Vec3 → ℝ := fun x => f x i
      let Di : Vec3 → ℝ := fun x => (fderiv ℝ Fi x) (basisVec i)
      let Dψ : Vec3 → ℝ := fun x => (fderiv ℝ ψ x) (basisVec i)
      have hDψCont : Continuous Dψ :=
        (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hDψCompact : HasCompactSupport Dψ :=
        hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)
      have hDiCont : Continuous Di := by
        change Continuous (fun x : Vec3 =>
          (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i))
        exact hderivCont i
      have hFiCont : Continuous Fi := by
        change Continuous (fun x : Vec3 => f x i)
        exact (hC1 i).continuous
      have hIntDiψ : Integrable (fun x : Vec3 => Di x * ψ x) volume := by
        have hcont : Continuous (fun x : Vec3 => Di x * ψ x) := by
          exact hDiCont.mul hψ.continuous
        exact hcont.integrable_of_hasCompactSupport (hψc.mul_left)
      have hIntFiDψ : Integrable (fun x : Vec3 => Fi x * Dψ x) volume := by
        have hcont : Continuous (fun x : Vec3 => Fi x * Dψ x) := by
          exact hFiCont.mul hDψCont
        exact hcont.integrable_of_hasCompactSupport (hDψCompact.mul_left)
      have hIntFiψ : Integrable (fun x : Vec3 => Fi x * ψ x) volume := by
        have hcont : Continuous (fun x : Vec3 => Fi x * ψ x) := by
          exact hFiCont.mul hψ.continuous
        exact hcont.integrable_of_hasCompactSupport (hψc.mul_left)
      have hIBP := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        (B := ContinuousLinearMap.mul ℝ ℝ)
        (f := Fi) (f' := Di) (g := ψ) (g' := Dψ) (v := basisVec i)
        hIntDiψ hIntFiDψ hIntFiψ
        (fun x hx => by
          simpa [Fi, Di] using
            (((hC1 i).differentiable (by norm_num) x).hasFDerivAt
              |>.hasLineDerivAt (basisVec i)))
        (fun x hx => by
          simpa [Dψ] using
            ((hψ.differentiable (by norm_num) x).hasFDerivAt
              |>.hasLineDerivAt (basisVec i)))
      have hIBP' := congrArg (fun r : ℝ => -r) hIBP
      simpa [Fi, Di, Dψ] using hIBP'.symm
    have hsum : (∑ i : Fin 3, ∫ x : Vec3,
        (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i) * ψ x ∂volume) =
        -∑ i : Fin 3, ∫ x : Vec3,
          f x i * (fderiv ℝ ψ x) (basisVec i) ∂volume := by
      calc
        _ = ∑ i : Fin 3, -(∫ x : Vec3,
            f x i * (fderiv ℝ ψ x) (basisVec i) ∂volume) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hparts i
        _ = _ := by rw [Finset.sum_neg_distrib]
    have hweak' : ∑ i : Fin 3, ∫ x : Vec3,
        f x i * (fderiv ℝ ψ x) (basisVec i) ∂volume = 0 := by
      have hsumInt : ∫ x : Vec3, ∑ i : Fin 3,
          f x i * (fderiv ℝ ψ x) (basisVec i) ∂volume =
          ∑ i : Fin 3, ∫ x : Vec3,
            f x i * (fderiv ℝ ψ x) (basisVec i) ∂volume := by
        apply integral_finsetSum
        intro i hi
        have hDψCont : Continuous
            (fun x : Vec3 => (fderiv ℝ ψ x) (basisVec i)) :=
          (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
        have hDψCompact : HasCompactSupport
            (fun x : Vec3 => (fderiv ℝ ψ x) (basisVec i)) :=
          hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)
        have hFiCont : Continuous (fun x : Vec3 => f x i) := (hC1 i).continuous
        exact (hFiCont.mul hDψCont).integrable_of_hasCompactSupport
          (hDψCompact.mul_left)
      rw [← hsumInt]
      simpa [ψW, CKN.WeakTestFunction.partialDeriv] using hweak
    rw [hweak'] at hsum
    have hdivIntegral : ∫ x : Vec3, divF x * ψ x ∂volume = 0 := by
      have hsumDiv : (∫ x : Vec3, divF x * ψ x ∂volume) =
          ∑ i : Fin 3, ∫ x : Vec3,
            (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i) * ψ x ∂volume := by
        calc
          _ = ∫ x : Vec3, ∑ i : Fin 3,
              (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i) * ψ x ∂volume := by
                apply integral_congr_ae
                filter_upwards [] with x
                simp [divF, Finset.sum_mul]
          _ = _ := by
            apply integral_finsetSum (μ := volume) Finset.univ
            intro i hi
            have hcont : Continuous (fun x : Vec3 =>
                (fderiv ℝ (fun y : Vec3 => f y i) x) (basisVec i) * ψ x) :=
              (hderivCont i).mul hψ.continuous
            exact hcont.integrable_of_hasCompactSupport (hψc.mul_left)
      rw [hsumDiv, hsum]
      simp
    simpa [mul_comm] using hdivIntegral
  have hae : ∀ᵐ x ∂volume, divF x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hdivLoc
    intro ψ hψ hψc
    simpa [smul_eq_mul] using hpair ψ hψ hψc
  have hzero : divF = 0 := Measure.eq_of_ae_eq hae hdivCont continuous_const
  intro x
  simpa [divF] using congrFun hzero x

/-- The regularized transport velocity is classically divergence free
on each positive-time slice. -/
theorem regUniform_mollified_velocity_divergence_eq_zero
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hdiv : CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t))) :
    ∀ x : Vec3, ∑ j : Fin 3,
      spatialPartial (fun y => regUniformMollifiedVelocity ρ ε hε u y j)
        j (x, t) = 0 := by
  let aₜ : Vec3 → Vec3 := fun x => u (x, t)
  have haₜ : CKN.IsInJ aₜ := CKN.weakDivFreeL2_isInJ hdiv
  have hJ : CKN.IsInJ (regUniformMollifiedInitial ρ ε hε aₜ) :=
    regMollifiedInitial_isInJ ρ ε hε haₜ
  have hJweak : CKN.IsWeakDivFreeL2
      (regUniformMollifiedInitial ρ ε hε aₜ) :=
    (CKN.isInJ_iff_weakDivFree).1 hJ
  have hJsmooth := regUniformMollifiedInitial_contDiff ρ ε hε haₜ
  have hC1 : ∀ j : Fin 3, ContDiff ℝ 1
      (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε aₜ x j) := by
    intro j
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε aₜ x j) := by
      exact hJsmooth.continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) j)
    exact hcoord.of_le (by simp)
  have hclassical := regUniform_weakDivFree_contDiff_divergence_eq_zero hC1 hJweak
  intro x
  have hslice (y : Vec3) :
      regUniformMollifiedVelocity ρ ε hε u (y, t) =
        regUniformMollifiedInitial ρ ε hε aₜ y := by
    rfl
  simp only [spatialPartial]
  simpa [hslice] using hclassical x

end CKN.Leray

end
