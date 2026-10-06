/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionKernel
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ

/-!
# Spatial derivatives of the heat orbit of an `L²` datum

At a positive time the Gaussian convolution of an `L²` datum is differentiable,
and its derivative is the convolution with the kernel derivative: smooth
compactly supported approximants have this property, and their derivatives
converge uniformly by the Cauchy–Schwarz bound for the kernel derivative.
Consequently the heat orbit of a datum in `J` has measurable classical
gradient on every slab, this gradient is a weak gradient at each positive
time, and the heat orbit is divergence free.  These are the measurability,
weak-gradient and divergence clauses of the heat orbit in
`prop:pv-local-solution`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

private theorem clm_apply_eq_sum_basisVec (L : Vec3 →L[ℝ] ℝ) (v : Vec3) :
    L v = ∑ j : Fin 3, v j * L (basisVec j) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (Pi.single j (v j) : Vec3) = v j • basisVec j := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp [basisVec]
    · simp [basisVec, hk]
  rw [hs, map_smul, smul_eq_mul]

private theorem sum_proj_apply (c : Fin 3 → ℝ) (v : Vec3) :
    (∑ j : Fin 3, c j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j) v =
      ∑ j : Fin 3, c j * v j := by
  simp

/-- At a positive time the Gaussian convolution of an `L²` datum is
differentiable, with derivative given by convolution with the kernel
derivatives. -/
theorem heatConv_hasFDerivAt_of_memLp {f : Vec3 → ℝ} (hf : MemLp f 2 volume) {t : ℝ}
    (ht : 0 < t) (x : Vec3) :
    HasFDerivAt (heatConv t f)
      (∑ j : Fin 3, heatConvGrad t f j x •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j) x := by
  obtain ⟨fs, hfs, hlim⟩ := exists_smooth_compact_tendsto_eLpNorm (p := 2)
    (by norm_num) (by norm_num) hf
  obtain ⟨hK, hD⟩ := heatKernel_memLp_two ht
  obtain ⟨B, hB, hbound⟩ := heatKernel_eLpNorm_two_uniform ht
  have hmem (n : ℕ) : MemLp (fs n) 2 volume :=
    (hfs n).1.continuous.memLp_of_hasCompactSupport (hfs n).2
  let P : Fin 3 → Vec3 →L[ℝ] ℝ := fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j
  let F' : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun n y => ∑ j : Fin 3, heatConvGrad t (fs n) j y • P j
  let G' : Vec3 → Vec3 →L[ℝ] ℝ := fun y => ∑ j : Fin 3, heatConvGrad t f j y • P j
  have hderiv (n : ℕ) (y : Vec3) : HasFDerivAt (heatConv t (fs n)) (F' n y) y := by
    have hd := (((heatConv_smooth_input (hfs n).1 (hfs n).2 ht).differentiable
      (by simp)) y).hasFDerivAt
    convert hd using 1
    ext v
    rw [clm_apply_eq_sum_basisVec (fderiv ℝ (heatConv t (fs n)) y) v]
    simp only [F', P, sum_proj_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [heatConv_fderiv (hfs n).1 (hfs n).2 ht y (basisVec j),
      heatConv_spatial_kernel_transfer (hfs n).1 (hfs n).2 ht j y, heatConvGrad]
    ring
  have hgradLip (n : ℕ) (y : Vec3) (j : Fin 3) :
      |heatConvGrad t f j y - heatConvGrad t (fs n) j y| ≤
        (B * eLpNorm (fs n - f) 2 volume).toReal := by
    have hfin : B * eLpNorm (fs n - f) 2 volume ≠ ∞ :=
      (ENNReal.mul_lt_top hB (hmem n |>.sub hf).eLpNorm_lt_top).ne
    rw [← Real.norm_eq_abs, ← toReal_enorm]
    apply ENNReal.toReal_mono hfin
    refine (integral_mul_sub_sub_enorm_le (hD j) hf (hmem n) y).trans ?_
    rw [eLpNorm_sub_comm]
    gcongr
    exact (hbound t le_rfl).2 j
  have hbTend : Tendsto (fun n => 3 * (B * eLpNorm (fs n - f) 2 volume).toReal) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => B * eLpNorm (fs n - f) 2 volume) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hB.ne)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa using h2.const_mul 3
  have hunif : TendstoUniformly F' G' atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hbTend).2 ε hε] with n hn y
    rw [dist_eq_norm]
    refine lt_of_le_of_lt ?_ hn
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [sub_apply]
    simp only [G', F', P, sum_proj_apply]
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ j : Fin 3, (heatConvGrad t f j y * v j - heatConvGrad t (fs n) j y * v j)‖ ≤
          ∑ j : Fin 3, ‖heatConvGrad t f j y * v j - heatConvGrad t (fs n) j y * v j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, (B * eLpNorm (fs n - f) 2 volume).toReal * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [← sub_mul, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hgradLip n y j) (norm_le_pi_norm v j) (norm_nonneg _)
          ENNReal.toReal_nonneg
      _ = 3 * (B * eLpNorm (fs n - f) 2 volume).toReal * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hpt (y : Vec3) : Tendsto (fun n => heatConv t (fs n) y) atTop (𝓝 (heatConv t f y)) := by
    have hA : eLpNorm (fun z : Vec3 => heatKernel z t) 2 volume ≠ ∞ := hK.eLpNorm_ne_top
    have hbd : Tendsto (fun n => eLpNorm (fun z : Vec3 => heatKernel z t) 2 volume *
        eLpNorm (fs n - f) 2 volume) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hA)
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbd
      (fun _ => bot_le) fun n => ?_
    rw [edist_eq_enorm_sub, heatConv_eq_integral, heatConv_eq_integral]
    exact integral_mul_sub_sub_enorm_le hK (hmem n) hf y
  exact hasFDerivAt_of_tendstoUniformly hunif hderiv hpt x

/-- At a positive time the `j`th classical derivative of the Gaussian
convolution of an `L²` datum is `heatConvGrad`. -/
theorem heatConv_fderiv_basisVec_of_memLp {f : Vec3 → ℝ} (hf : MemLp f 2 volume) {t : ℝ}
    (ht : 0 < t) (x : Vec3) (j : Fin 3) :
    fderiv ℝ (heatConv t f) x (basisVec j) = heatConvGrad t f j x := by
  rw [(heatConv_hasFDerivAt_of_memLp hf ht x).fderiv, sum_proj_apply]
  simp [basisVec, Pi.single_apply]

/-- At a positive time the classical spatial derivatives of the heat orbit of
an `L²` datum are the kernel-derivative convolutions of its components. -/
theorem heatOrbit_spatialDeriv_eq {a : Vec3 → Vec3} (ha : MemLp a 2 volume) {t : ℝ}
    (ht : 0 < t) (x : Vec3) (i j : Fin 3) :
    spatialDeriv (fun y => heatOrbit a (y, t) i) j x = heatConvGrad t (fun y => a y i) j x :=
  heatConv_fderiv_basisVec_of_memLp (memLp_pi_iff.1 ha i) ht x j

/-- The smooth divergence-free approximants of a datum in `J`, component by
component: each component is smooth, compactly supported and square
integrable, and converges in `L²` to the corresponding component of the datum. -/
theorem isInJ_component_approx {a : Vec3 → Vec3} (ha : IsInJ a) :
    ∃ aSeq : ℕ → Vec3 → Vec3,
      (∀ k i, ContDiff ℝ (⊤ : ℕ∞) (fun x => aSeq k x i)) ∧
      (∀ k i, HasCompactSupport (fun x => aSeq k x i)) ∧
      (∀ k x, ∑ i : Fin 3, spatialDeriv (fun y => aSeq k y i) i x = 0) ∧
      (∀ i, Tendsto (fun k => eLpNorm ((fun x => aSeq k x i) - fun x => a x i) 2 volume)
        atTop (𝓝 0)) ∧
      Tendsto (fun k => eLpNorm (fun x => aSeq k x - a x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨ha2, aSeq, hsm, hcs, hdiv, hlim⟩ := ha
  refine ⟨aSeq, fun k i => contDiff_pi.1 (hsm k) i,
    fun k i => (hcs k).comp_left (g := fun v : Vec3 => v i) rfl, hdiv, fun i => ?_, hlim⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) fun k => ?_
  have hmeas : AEStronglyMeasurable ((fun x => aSeq k x i) - fun x => a x i) volume :=
    ((contDiff_pi.1 (hsm k) i).continuous.aestronglyMeasurable).sub
      (memLp_pi_iff.1 ha2 i).aestronglyMeasurable
  refine eLpNorm_mono hmeas fun x => ?_
  simpa using norm_le_pi_norm (aSeq k x - a x) i

/-- (h1) The heat orbit of a datum in `J` and its classical spatial gradient
are almost everywhere strongly measurable on every slab `ℝ³ × (0, τ)`. -/
theorem heatOrbit_grad_aestronglyMeasurable {a : Vec3 → Vec3} (ha : IsInJ a) (τ : ℝ) :
    AEStronglyMeasurable (heatOrbit a)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      AEStronglyMeasurable
        (fun z : ParabolicPoint => fun i j => spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  have hai (i : Fin 3) : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
  have hh : Measurable (heatOrbit a) := by
    have heq : heatOrbit a = fun z : ParabolicPoint => fun i =>
        ∫ y : Vec3, heatKernel (y, z.2).1 (y, z.2).2 * a (z.1 - y) i := by
      funext z i
      change heatConv z.2 (fun y => a y i) z.1 = _
      exact heatConv_eq_integral _ _ _
    rw [heq]
    exact measurable_pi_iff.2 fun i =>
      (stronglyMeasurable_integral_kernel_mul_sub heatKernel_vecTime_measurable
        (hai i).aestronglyMeasurable).measurable
  refine ⟨hh.aestronglyMeasurable, ?_⟩
  have hG : Measurable (fun z : ParabolicPoint => fun i j => heatConvGrad z.2 (fun y => a y i) j
    z.1) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      (stronglyMeasurable_integral_kernel_mul_sub
        (heatKernelSpaceDerivative_vecTime_measurable j) (hai i).aestronglyMeasurable).measurable
  refine hG.aestronglyMeasurable.congr ?_
  have hQ : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  filter_upwards [ae_restrict_mem hQ] with z hz
  funext i j
  exact (heatOrbit_spatialDeriv_eq ha.1 hz.2.1 z.1 i j).symm

/-- (h4) At each positive time the classical spatial gradient of each
component of the heat orbit of a datum in `J` is its weak gradient on `ℝ³`. -/
theorem heatOrbit_hasWeakGradientOn {a : Vec3 → Vec3} (ha : IsInJ a) {t : ℝ} (ht : 0 < t)
    (i : Fin 3) :
    HasWeakGradientOn (Set.univ : Set Vec3) (fun x => heatOrbit a (x, t) i)
      (fun x j => spatialDeriv (fun y => heatOrbit a (y, t) i) j x) := by
  have hai : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
  obtain ⟨M, hM, hbound⟩ := heatConv_heatConvGrad_bound ht hai
  set u : Vec3 → ℝ := heatConv t (fun y => a y i) with hu
  have hdiff : Differentiable ℝ u := fun x => (heatConv_hasFDerivAt_of_memLp hai ht
    x).differentiableAt
  intro j φ hφ hφc _
  simp only [Measure.restrict_univ]
  change ∫ x, u x * fderiv ℝ φ x (basisVec j) = -∫ x, fderiv ℝ u x (basisVec j) * φ x
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφI : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hdφ : Continuous (fun x => fderiv ℝ φ x (basisVec j)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφI : Integrable (fun x => fderiv ℝ φ x (basisVec j)) volume :=
    hdφ.integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hubd : ∀ᵐ x ∂(volume : Measure Vec3), ‖u x‖ ≤ M :=
    Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (hbound t le_rfl x).1
  have hdubd : ∀ᵐ x ∂(volume : Measure Vec3), ‖fderiv ℝ u x (basisVec j)‖ ≤ M :=
    Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, hu, heatConv_fderiv_basisVec_of_memLp hai ht x j]
      exact (hbound t le_rfl x).2 j
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hφI.bdd_mul (measurable_fderiv_apply_const ℝ u (basisVec j)).aestronglyMeasurable hdubd)
    (hdφI.bdd_mul hdiff.continuous.aestronglyMeasurable hubd)
    (hφI.bdd_mul hdiff.continuous.aestronglyMeasurable hubd)
    (fun x _ => hdiff x) (fun x _ => hφd x)

/-- At each positive time the heat orbit of a datum in `J` is pointwise
divergence free. -/
theorem heatOrbit_div_eq_zero {a : Vec3 → Vec3} (ha : IsInJ a) {t : ℝ} (ht : 0 < t)
    (x : Vec3) :
    ∑ i : Fin 3, spatialDeriv (fun y => heatOrbit a (y, t) i) i x = 0 := by
  obtain ⟨aSeq, hsm, hcs, hdiv, hlim, -⟩ := isInJ_component_approx ha
  have hai (i : Fin 3) : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
  obtain ⟨hK, hD⟩ := heatKernel_memLp_two ht
  have hmem (k : ℕ) (i : Fin 3) : MemLp (fun y => aSeq k y i) 2 volume :=
    (hsm k i).continuous.memLp_of_hasCompactSupport (hcs k i)
  have hzero (k : ℕ) : ∑ i : Fin 3, heatConvGrad t (fun y => aSeq k y i) i x = 0 := by
    let g : Fin 3 → Vec3 → ℝ := fun i y => fderiv ℝ (fun y => aSeq k y i) y (basisVec i)
    have hg (i : Fin 3) : MemLp (g i) 2 volume :=
      ((hsm k i).continuous_fderiv (by simp)).clm_apply continuous_const
        |>.memLp_of_hasCompactSupport ((hcs k i).fderiv_apply (𝕜 := ℝ) (basisVec i))
    have hconv (i : Fin 3) : heatConvGrad t (fun y => aSeq k y i) i x =
        ∫ y : Vec3, heatKernel y t * g i (x - y) := by
      rw [heatConvGrad, ← heatConv_spatial_kernel_transfer (hsm k i) (hcs k i) ht i x,
        heatConv_eq_integral]
    simp only [hconv]
    rw [← integral_finsetSum Finset.univ fun i _ => (integrable_mul_sub_enorm_le hK (hg i) x).1]
    have hpt : (fun y : Vec3 => ∑ i : Fin 3, heatKernel y t * g i (x - y)) = fun _ => 0 := by
      funext y
      rw [← Finset.mul_sum]
      have := hdiv k (x - y)
      simp only [spatialDeriv] at this
      simp only [g, this, mul_zero]
    rw [hpt, integral_zero]
  have hconv : Tendsto (fun k => ∑ i : Fin 3, heatConvGrad t (fun y => aSeq k y i) i x) atTop
      (𝓝 (∑ i : Fin 3, heatConvGrad t (fun y => a y i) i x)) := by
    apply tendsto_finsetSum
    intro i _
    have hA : eLpNorm (fun y : Vec3 => heatKernelSpaceDerivative y t i) 2 volume ≠ ∞ :=
      (hD i).eLpNorm_ne_top
    have hbd : Tendsto (fun k => eLpNorm (fun y : Vec3 => heatKernelSpaceDerivative y t i) 2
      volume *
        eLpNorm ((fun x => aSeq k x i) - fun x => a x i) 2 volume) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hlim i) (Or.inr hA)
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbd
      (fun _ => bot_le) fun k => ?_
    rw [edist_eq_enorm_sub]
    exact integral_mul_sub_sub_enorm_le (hD i) (hmem k i) (hai i) x
  simp only [hzero] at hconv
  rw [show (∑ i : Fin 3, spatialDeriv (fun y => heatOrbit a (y, t) i) i x) =
      ∑ i : Fin 3, heatConvGrad t (fun y => a y i) i x from
    Finset.sum_congr rfl fun i _ => heatOrbit_spatialDeriv_eq ha.1 ht x i i]
  exact tendsto_nhds_unique hconv tendsto_const_nhds

/-- (h5) At each positive time the heat orbit of a datum in `J` is weakly
divergence free on `ℝ³`. -/
theorem heatOrbit_weak_div_eq_zero {a : Vec3 → Vec3} (ha : IsInJ a) {t : ℝ} (ht : 0 < t)
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    ∫ x, ∑ i : Fin 3, heatOrbit a (x, t) i * ψ.partialDeriv i x = 0 := by
  have hai (i : Fin 3) : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha.1 i
  have hψI : Integrable ψ.toFun volume :=
    ψ.contDiff.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hdψI (i : Fin 3) : Integrable (ψ.partialDeriv i) volume :=
    ((ψ.contDiff.continuous_fderiv (by simp)).clm_apply
      continuous_const).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hterm (i : Fin 3) :
      Integrable (fun x => heatOrbit a (x, t) i * ψ.partialDeriv i x) volume ∧
        ∫ x, heatOrbit a (x, t) i * ψ.partialDeriv i x =
          -∫ x, spatialDeriv (fun y => heatOrbit a (y, t) i) i x * ψ.toFun x := by
    obtain ⟨M, _, hbound⟩ := heatConv_heatConvGrad_bound ht (hai i)
    have hdiff : Differentiable ℝ (fun x => heatOrbit a (x, t) i) := fun x =>
      (heatConv_hasFDerivAt_of_memLp (hai i) ht x).differentiableAt
    refine ⟨(hdψI i).bdd_mul hdiff.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (hbound t le_rfl x).1), ?_⟩
    have hw := (hasWeakPartialDerivOn_iff_forall_testFunction.1
      (heatOrbit_hasWeakGradientOn ha ht i i)) ψ
    simpa only [Measure.restrict_univ] using hw
  have hdivI (i : Fin 3) : Integrable
      (fun x => spatialDeriv (fun y => heatOrbit a (y, t) i) i x * ψ.toFun x) volume := by
    obtain ⟨M, _, hbound⟩ := heatConv_heatConvGrad_bound ht (hai i)
    refine hψI.bdd_mul (c := M) (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, heatOrbit_spatialDeriv_eq ha.1 ht x i i]
    exact (hbound t le_rfl x).2 i
  rw [integral_finsetSum Finset.univ fun i _ => (hterm i).1]
  simp only [fun i => (hterm i).2]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ fun i _ => hdivI i]
  have hpt : (fun x => ∑ i : Fin 3, spatialDeriv (fun y => heatOrbit a (y, t) i) i x *
      ψ.toFun x) = fun _ => 0 := by
    funext x
    rw [← Finset.sum_mul, heatOrbit_div_eq_zero ha ht x, zero_mul]
  rw [hpt, integral_zero, neg_zero]

end ESS

end
