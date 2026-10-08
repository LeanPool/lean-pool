/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedTransportField
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureL2
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildPathContinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfSlab

/-!
# The quadratic pressure of the forced regularized solution

The pressure `p_ε = P[J_ε u_ε ⊗ u_ε] + p_f` of `lem:regularised-forced`: at
each time the quadratic part is the Riesz pressure of the regularized tensor
of the solution. Since the tensor depends continuously on the solution curve,
the Riesz pressure is a continuous curve in `L²`, and the limit of its spatial
mollifications is a jointly measurable space-time pressure whose slices are
the Riesz pressures.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology Convolution

noncomputable section

namespace CKN.Leray

local instance : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩

/-- A coordinate entry of a real tensor `L²` field, in physical coordinates. -/
@[expose]
def forcedTensorComp (T : RealTensorL2) (i j : Fin 3) (x : Vec3) : ℝ :=
  (T : L2Vec3 → RealTensor3) (WithLp.toLp 2 x) i j

theorem ofReal_two_eq : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num

theorem norm_forcedTensorComp_le (T : RealTensorL2) (i j : Fin 3) (x : Vec3) :
    ‖forcedTensorComp T i j x‖ ≤ ‖(T : L2Vec3 → RealTensor3) (WithLp.toLp 2 x)‖ :=
  (PiLp.norm_apply_le _ j).trans (PiLp.norm_apply_le _ i)

theorem memLp_forcedTensorComp (T : RealTensorL2) (i j : Fin 3) :
    MemLp (forcedTensorComp T i j) (ENNReal.ofReal (2 : ℝ)) volume := by
  rw [ofReal_two_eq]
  have hT : MemLp (fun x : Vec3 => (T : L2Vec3 → RealTensor3) (WithLp.toLp 2 x)) 2 volume :=
    (Lp.memLp T).comp_measurePreserving vec3ToL2Vec3_measurePreserving
  refine hT.of_le_mul (c := 1) ?_ (Eventually.of_forall fun x => ?_)
  · have hc : Continuous fun S : RealTensor3 => S i j :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).comp
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => L2Vec3) i)
    exact hc.comp_aestronglyMeasurable hT.aestronglyMeasurable
  · rw [one_mul]
    exact norm_forcedTensorComp_le T i j x

theorem eLpNorm_forcedTensorComp_sub_le (T T' : RealTensorL2) (i j : Fin 3) :
    eLpNorm (forcedTensorComp T i j - forcedTensorComp T' i j) (ENNReal.ofReal (2 : ℝ)) volume ≤
      ENNReal.ofReal ‖T - T'‖ := by
  rw [ofReal_two_eq]
  have hsub : (forcedTensorComp T i j - forcedTensorComp T' i j) =ᵐ[volume]
      forcedTensorComp (T - T') i j := by
    have h := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae (Lp.coeFn_sub T T')
    filter_upwards [h] with x hx
    simp only [Pi.sub_apply, forcedTensorComp]
    rw [hx]
    rfl
  rw [eLpNorm_congr_ae hsub]
  have hle : eLpNorm (forcedTensorComp (T - T') i j) 2 volume ≤
      eLpNorm (fun x : Vec3 => (((T - T' : RealTensorL2)) : L2Vec3 → RealTensor3)
        (WithLp.toLp 2 x)) 2 volume :=
    eLpNorm_mono (memLp_forcedTensorComp (T - T') i j).aestronglyMeasurable
      fun x => norm_forcedTensorComp_le _ i j x
  refine hle.trans (le_of_eq ?_)
  have hcomp := eLpNorm_comp_measurePreserving (p := 2)
    (Lp.aestronglyMeasurable (T - T')) vec3ToL2Vec3_measurePreserving
  rw [show (fun x : Vec3 => (((T - T' : RealTensorL2)) : L2Vec3 → RealTensor3)
    (WithLp.toLp 2 x)) = ((T - T' : RealTensorL2) : L2Vec3 → RealTensor3) ∘
      (WithLp.toLp 2 : Vec3 → L2Vec3) from rfl, hcomp, Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_ne_top]

/-- The pressure tensor of a real tensor `L²` field, in physical coordinates. -/
@[expose]
def forcedPressureTensorLp (T : RealTensorL2) : PressureTensorLp 2 :=
  fun i j => (memLp_forcedTensorComp T i j).toLp (forcedTensorComp T i j)

theorem rieszPressureSlice_two_sub (F G : PressureTensorLp 2) :
    rieszPressureSlice 2 (by norm_num) F - rieszPressureSlice 2 (by norm_num) G =
      rieszPressureSlice 2 (by norm_num) (F - G) := by
  unfold rieszPressureSlice
  simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

theorem norm_forcedPressureTensorLp_sub_le (T T' : RealTensorL2) (i j : Fin 3) :
    ‖(forcedPressureTensorLp T - forcedPressureTensorLp T') i j‖ ≤ ‖T - T'‖ := by
  have : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by rw [ofReal_two_eq]; norm_num⟩
  simp only [Pi.sub_apply, forcedPressureTensorLp]
  rw [← MemLp.toLp_sub, Lp.norm_toLp]
  exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (eLpNorm_forcedTensorComp_sub_le T T' i j)

/-- The Riesz pressure of the tensor field is Lipschitz in the tensor. -/
theorem norm_forcedPressure_sub_le (T T' : RealTensorL2) :
    ‖rieszPressureSlice 2 (by norm_num) (forcedPressureTensorLp T) -
        rieszPressureSlice 2 (by norm_num) (forcedPressureTensorLp T')‖ ≤
      rieszPressureOperatorBound 2 (by norm_num) * (9 * ‖T - T'‖) := by
  rw [rieszPressureSlice_two_sub]
  refine (rieszPressureSlice_norm_le 2 (by norm_num) _).trans ?_
  have hB : 0 ≤ rieszPressureOperatorBound 2 (by norm_num) :=
    (norm_nonneg _).trans (rieszPressureOperator_norm_le 2 (by norm_num) 0 0)
  refine mul_le_mul_of_nonneg_left ?_ hB
  calc ∑ i : Fin 3, ∑ j : Fin 3, ‖(forcedPressureTensorLp T - forcedPressureTensorLp T') i j‖
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖T - T'‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          norm_forcedPressureTensorLp_sub_le T T' i j
    _ = 9 * ‖T - T'‖ := by simp; ring

/-- Mollifications of two square-integrable functions differ pointwise by at
most the kernel norm times the `L²` distance. -/
theorem abs_mollify_sub_le {g g' : Vec3 → ℝ} (hg : MemLp g 2 volume) (hg' : MemLp g' 2 volume)
    {δ : ℝ} (hδ : 0 < δ) (x : Vec3) :
    |CKN.mollify g δ hδ x - CKN.mollify g' δ hδ x| ≤
      (eLpNorm (CKN.mollifier (d := 3) δ hδ) 2 volume * eLpNorm (g - g') 2 volume).toReal := by
  have hm : MemLp (CKN.mollifier (d := 3) δ hδ) 2 volume :=
    (CKN.mollifier_contDiff (d := 3) hδ (n := 0)).continuous.memLp_of_hasCompactSupport
      (CKN.mollifier_hasCompactSupport hδ)
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hshift : ∀ {f : Vec3 → ℝ}, MemLp f 2 volume → MemLp (fun τ => f (x - τ)) 2 volume :=
    fun hf => hf.comp_measurePreserving hmp
  have hint : ∀ {f : Vec3 → ℝ}, MemLp f 2 volume →
      Integrable (fun τ => CKN.mollifier δ hδ τ * f (x - τ)) volume := fun hf =>
    hm.integrable_mul (hshift hf)
  rw [mollify_eq_integral hδ, mollify_eq_integral hδ, ← integral_sub (hint hg) (hint hg')]
  have heq : ∫ τ, (CKN.mollifier δ hδ τ * g (x - τ) - CKN.mollifier δ hδ τ * g' (x - τ)) =
      (CKN.mollifier δ hδ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (g - g')) x := by
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.sub_apply]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    ring
  rw [heq, ← Real.norm_eq_abs]
  exact norm_convolution_le_of_memLp_two hm (hg.sub hg') x

/-- The Riesz pressure curve of the regularized tensor of a velocity curve. -/
@[expose]
def forcedPressureCurve (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (U : ℝ → RealVectorL2)
    (t : ℝ) : Lp ℝ (ENNReal.ofReal (2 : ℝ)) (volume : Measure Vec3) :=
  rieszPressureSlice 2 (by norm_num)
    (forcedPressureTensorLp (regularizedMildTensor ρ ε hε (U t)))

theorem continuous_forcedPressureCurve (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {U : ℝ → RealVectorL2} (hU : Continuous U) :
    Continuous (forcedPressureCurve ρ ε hε U) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hT : Tendsto (fun t => regularizedMildTensor ρ ε hε (U t)) (𝓝 t₀)
      (𝓝 (regularizedMildTensor ρ ε hε (U t₀))) :=
    regularizedMildTensor_continuousAt ρ ε hε U (U t₀) (hU.tendsto t₀)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hT' := (tendsto_iff_norm_sub_tendsto_zero.1 hT).const_mul
    (rieszPressureOperatorBound 2 (by norm_num) * 9)
  rw [mul_zero] at hT'
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hT'
  refine (norm_forcedPressure_sub_le _ _).trans (le_of_eq ?_)
  ring

/-- The quadratic pressure field: the limit of the spatial mollifications of
the Riesz pressure slices. -/
@[expose]
def forcedQuadPressure (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (U : ℝ → RealVectorL2)
    (z : Vec3 × ℝ) : ℝ :=
  limUnder atTop fun n : ℕ =>
    CKN.mollify (rieszPressureSliceRepresentative 2 (by norm_num)
      (forcedPressureTensorLp (regularizedMildTensor ρ ε hε (U z.2))))
      (1 / ((n : ℝ) + 1)) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) z.1

theorem memLp_rieszPressureSliceRepresentative_two (F : PressureTensorLp 2) :
    MemLp (rieszPressureSliceRepresentative 2 (by norm_num) F) 2 volume := by
  have h := (Lp.memLp (rieszPressureSlice 2 (by norm_num) F)).ae_eq
    (rieszPressureSliceRepresentative_ae_eq 2 (by norm_num) F)
  rwa [ofReal_two_eq] at h

theorem forcedQuadPressure_slice (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (U : ℝ → RealVectorL2) (t : ℝ) :
    (fun x => forcedQuadPressure ρ ε hε U (x, t)) =ᵐ[volume]
      rieszPressureSliceRepresentative 2 (by norm_num)
        (forcedPressureTensorLp (regularizedMildTensor ρ ε hε (U t))) := by
  have hloc := (memLp_rieszPressureSliceRepresentative_two
    (forcedPressureTensorLp (regularizedMildTensor ρ ε hε (U t)))).locallyIntegrable
    (by norm_num)
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure Vec3)) (l := atTop) (K := 2)
    (φ := fun n : ℕ => CKN.standardMollifier (d := 3) (1 / ((n : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    (by simpa only [CKN.standardMollifier] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (Eventually.of_forall fun n => by
      simp only [CKN.standardMollifier]
      linarith only [(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))])
    hloc
  filter_upwards [hconv] with x hx
  exact hx.limUnder_eq

theorem eLpNorm_rieszRep_sub (F G : PressureTensorLp 2) :
    eLpNorm (rieszPressureSliceRepresentative 2 (by norm_num) F -
      rieszPressureSliceRepresentative 2 (by norm_num) G) 2 volume =
      ENNReal.ofReal ‖rieszPressureSlice 2 (by norm_num) F -
        rieszPressureSlice 2 (by norm_num) G‖ := by
  have hsub : (rieszPressureSliceRepresentative 2 (by norm_num) F -
      rieszPressureSliceRepresentative 2 (by norm_num) G) =ᵐ[volume]
      ((rieszPressureSlice 2 (by norm_num) F - rieszPressureSlice 2 (by norm_num) G :
        Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) : Vec3 → ℝ) := by
    filter_upwards [rieszPressureSliceRepresentative_ae_eq 2 (by norm_num) F,
      rieszPressureSliceRepresentative_ae_eq 2 (by norm_num) G, Lp.coeFn_sub
        (rieszPressureSlice 2 (by norm_num) F) (rieszPressureSlice 2 (by norm_num) G)]
      with x h1 h2 h3
    rw [h3, Pi.sub_apply, Pi.sub_apply, h1, h2]
  rw [eLpNorm_congr_ae hsub, Lp.norm_def, ← ofReal_two_eq, ENNReal.ofReal_toReal
    (Lp.memLp _).eLpNorm_ne_top]

/-- The quadratic pressure field of a continuous velocity curve is jointly
measurable. -/
theorem forcedQuadPressure_stronglyMeasurable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {U : ℝ → RealVectorL2} (hU : Continuous U) :
    StronglyMeasurable (forcedQuadPressure ρ ε hε U) := by
  refine StronglyMeasurable.limUnder fun n => ?_
  let δ := 1 / ((n : ℝ) + 1)
  have hδ : 0 < δ := (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
  let g : ℝ → Vec3 → ℝ := fun t => rieszPressureSliceRepresentative 2 (by norm_num)
    (forcedPressureTensorLp (regularizedMildTensor ρ ε hε (U t)))
  have hg : ∀ t, MemLp (g t) 2 volume := fun t => memLp_rieszPressureSliceRepresentative_two _
  refine (measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Vec3) (t : ℝ) => CKN.mollify (g t) δ hδ x) (fun t => ?_)
    (fun x => ?_)).stronglyMeasurable
  · exact CKN.mollify_continuous hδ ((hg t).locallyIntegrable (by norm_num))
  · refine Continuous.measurable ?_
    rw [continuous_iff_continuousAt]
    intro t₀
    have hP := continuous_forcedPressureCurve ρ ε hε hU
    have hlim : Tendsto (fun t => ‖forcedPressureCurve ρ ε hε U t -
        forcedPressureCurve ρ ε hε U t₀‖) (𝓝 t₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hP.tendsto t₀)
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hC := hlim.const_mul (eLpNorm (CKN.mollifier (d := 3) δ hδ) 2 volume).toReal
    rw [mul_zero] at hC
    refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hC
    rw [Real.norm_eq_abs]
    refine (abs_mollify_sub_le (hg t) (hg t₀) hδ x).trans (le_of_eq ?_)
    rw [eLpNorm_rieszRep_sub, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    rfl

theorem eLpNorm_rieszRep (F : PressureTensorLp 2) :
    eLpNorm (rieszPressureSliceRepresentative 2 (by norm_num) F) 2 volume =
      ENNReal.ofReal ‖rieszPressureSlice 2 (by norm_num) F‖ := by
  rw [eLpNorm_congr_ae (rieszPressureSliceRepresentative_ae_eq 2 (by norm_num) F).symm,
    Lp.norm_def, ← ofReal_two_eq, ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_ne_top]

/-- Tonelli's formula for the squared `L²` norm of a real field on a product
with a time measure. -/
theorem lintegral_eLpNorm_real_slice_sq {μt : Measure ℝ} [SFinite μt] {F : Vec3 × ℝ → ℝ}
    (hF : StronglyMeasurable F) :
    ∫⁻ t, eLpNorm (fun x : Vec3 => F (x, t)) 2 volume ^ (2 : ℝ) ∂μt =
      eLpNorm F 2 ((volume : Measure Vec3).prod μt) ^ (2 : ℝ) := by
  have hslice (t : ℝ) : AEStronglyMeasurable (fun x : Vec3 => F (x, t)) volume :=
    (hF.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hsq (x : ℝ≥0∞) : (x ^ (1 / (2 : ℝ))) ^ (2 : ℝ) = x := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hF.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, hsq]
  rw [lintegral_prod_symm' _ (hF.measurable.enorm.pow_const _)]
  apply lintegral_congr
  intro t
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hslice t)]
  simp only [ENNReal.toReal_ofNat, hsq]

/-- The quadratic pressure field of a continuous velocity curve is square
integrable on every bounded slab. -/
theorem memLp_forcedQuadPressure_slab (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {U : ℝ → RealVectorL2} (hU : Continuous U) (T : ℝ) :
    MemLp (forcedQuadPressure ρ ε hε U) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have hsm := forcedQuadPressure_stronglyMeasurable ρ ε hε hU
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_forcedPressureCurve ρ ε hε hU).norm.continuousOn
  have hslice : ∀ t, eLpNorm (fun x : Vec3 => forcedQuadPressure ρ ε hε U (x, t)) 2 volume =
      ENNReal.ofReal ‖forcedPressureCurve ρ ε hε U t‖ := by
    intro t
    rw [eLpNorm_congr_ae (forcedQuadPressure_slice ρ ε hε U t), eLpNorm_rieszRep]
    rfl
  have hfin : eLpNorm (forcedQuadPressure ρ ε hε U) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) ^ (2 : ℝ) < ⊤ := by
    rw [← lintegral_eLpNorm_real_slice_sq hsm]
    calc ∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => forcedQuadPressure ρ ε hε U (x, t)) 2
          volume ^ (2 : ℝ)
        ≤ ∫⁻ _t in Ioo 0 T, ENNReal.ofReal M ^ (2 : ℝ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
          rw [hslice]
          refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by norm_num)
          have := hM t (Ioo_subset_Icc_self ht)
          rwa [norm_norm] at this
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            ENNReal.ofReal_ne_top) (by simp [Real.volume_Ioo])
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hfin

/-- The velocity slice of a representative agrees almost everywhere with the
curve on the Euclidean carrier. -/
theorem regUniformVelocitySlice_ae_eq {U : ℝ → RealVectorL2} {u : Vec3 × ℝ → Vec3} {t : ℝ}
    (hrep : (fun x => u (x, t)) =ᵐ[volume] realVectorL2Representative (U t)) :
    regUniformVelocitySlice u t =ᵐ[volume] ((U t : RealVectorL2) : L2Vec3 → L2Vec3) := by
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae hrep
  filter_upwards [h] with y hy
  simp only [regUniformVelocitySlice]
  rw [hy]
  rfl

theorem regMollifyVector_velocitySlice_eq (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {U : ℝ → RealVectorL2} {u : Vec3 × ℝ → Vec3} {t : ℝ}
    (hrep : (fun x => u (x, t)) =ᵐ[volume] realVectorL2Representative (U t)) :
    regMollifyVector ρ ε hε (regUniformVelocitySlice u t) =
      regMollifyVector ρ ε hε ((U t : RealVectorL2) : L2Vec3 → L2Vec3) := by
  unfold regMollifyVector
  exact convolution_congr _ (ae_eq_refl _) (regUniformVelocitySlice_ae_eq hrep)

/-- The pressure tensor slice of a representative is the coordinate entry of
the regularized tensor of the curve. -/
theorem regPressureTensorSlice_ae_eq (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {U : ℝ → RealVectorL2} {u : Vec3 × ℝ → Vec3} {t : ℝ}
    (hrep : (fun x => u (x, t)) =ᵐ[volume] realVectorL2Representative (U t)) (i j : Fin 3) :
    regPressureTensorSlice ρ ε hε u t i j =ᵐ[volume]
      forcedTensorComp (regularizedMildTensor ρ ε hε (U t)) i j := by
  have hT : ((regularizedMildTensor ρ ε hε (U t) : RealTensorL2) : L2Vec3 → RealTensor3) =ᵐ[volume]
      regularizedMildTensorField ρ ε hε (U t) := MemLp.coeFn_toLp _
  have hT' := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hT
  filter_upwards [hT', hrep] with x hx hux
  simp only [regPressureTensorSlice, regUniformMollifiedVelocity, forcedTensorComp]
  rw [regMollifyVector_velocitySlice_eq ρ ε hε hrep, hx, hux]
  simp only [regularizedMildTensorField, regularizedTensorOuter, realVectorL2Representative]
  rfl

end CKN.Leray

end
