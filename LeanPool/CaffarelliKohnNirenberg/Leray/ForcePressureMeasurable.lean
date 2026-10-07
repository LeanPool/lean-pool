/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressurePairing
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# A jointly measurable force pressure

For a strongly measurable space-time force, apply the slice force pressure of
`lem:force-pressure` at every time. Each spatial mollification of the result
is continuous in space, and at a fixed point it is measurable in time, since
it is the pairing of the slice pressure with a fixed test function and hence
the L² pairing of the force slice with a fixed field. Such functions are
jointly measurable, and their pointwise limit as the mollification radius
shrinks is a jointly measurable function whose time slices are the slice
pressures almost everywhere.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

open Classical in
/-- The slice force pressure of a space-time field at one time, set to zero
when the time slice is not square integrable. -/
@[expose]
def forcePressureSliceOfField (F : Vec3 × ℝ → Vec3) (t : ℝ) : Vec3 → ℝ :=
  if h : MemLp (fun x : Vec3 => F (x, t)) 2 volume then
    forcePressureSlice (realVectorL2OfCoordinateFunction (fun x : Vec3 => F (x, t)) h)
  else 0

/-- The slice force pressure of a field is locally integrable in space. -/
theorem forcePressureSliceOfField_locallyIntegrable (F : Vec3 × ℝ → Vec3) (t : ℝ) :
    LocallyIntegrable (forcePressureSliceOfField F t) volume := by
  by_cases h : MemLp (fun x : Vec3 => F (x, t)) 2 volume
  · rw [forcePressureSliceOfField, dite_eq_left h]
    exact (forcePressureSlice_memLp _).locallyIntegrable (by norm_num)
  · rw [forcePressureSliceOfField, dite_eq_right h]
    exact locallyIntegrable_zero

private theorem forcePressure_mollify_eq_integral (u : Vec3 → ℝ) {ε : ℝ} (hε : 0 < ε)
    (x : Vec3) :
    mollify u ε hε x = ∫ z, u z * mollifier ε hε (x - z) := by
  change ∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (mollifier ε hε t) (u (x - t)) = _
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun z => u z * mollifier ε hε (x - z)) (μ := volume) x]
  congr 1
  funext z
  rw [sub_sub_cancel, mul_comm]

private theorem forcePressure_mollifierTest_memLp {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    MemLp (fun z => mollifier ε hε (x - z)) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  have hcont : Continuous fun z => mollifier ε hε (x - z) :=
    (mollifier_contDiff (d := 3) hε (n := 0)).continuous.comp
      (continuous_const.sub continuous_id)
  have hsupp : HasCompactSupport fun z => mollifier ε hε (x - z) := by
    simpa [Function.comp_def] using
      (mollifier_hasCompactSupport (d := 3) hε).comp_homeomorph (Homeomorph.subLeft x)
  exact hcont.memLp_of_hasCompactSupport hsupp

private theorem forcePressure_realVectorL2Representative_measurable (u : RealVectorL2) :
    Measurable (realVectorL2Representative u) := by
  have hLp : Measurable (fun x : Vec3 => u (WithLp.toLp 2 x)) :=
    (Lp.stronglyMeasurable u).measurable.comp vec3ToL2Vec3_measurePreserving.measurable
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.measurable.comp hLp

/-- The L² norm of the time slices of a strongly measurable field is
measurable in time. -/
theorem measurable_eLpNorm_two_slice {F : Vec3 × ℝ → Vec3} (hF : StronglyMeasurable F) :
    Measurable fun t : ℝ => eLpNorm (fun x : Vec3 => F (x, t)) 2 volume := by
  have hslice (t : ℝ) : AEStronglyMeasurable (fun x : Vec3 => F (x, t)) volume :=
    (hF.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have heq : (fun t : ℝ => eLpNorm (fun x : Vec3 => F (x, t)) 2 volume) =
      fun t => (∫⁻ x, ‖F (x, t)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    funext t
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hslice t)]
    simp
  rw [heq]
  refine Measurable.pow_const ?_ _
  exact Measurable.lintegral_prod_left'
    (f := fun q : Vec3 × ℝ => ‖F q‖ₑ ^ (2 : ℝ)) (hF.measurable.enorm.pow_const _)

/-- The set of times at which a strongly measurable field has a square
integrable slice is measurable. -/
theorem measurableSet_memLp_slice {F : Vec3 × ℝ → Vec3} (hF : StronglyMeasurable F) :
    MeasurableSet {t : ℝ | MemLp (fun x : Vec3 => F (x, t)) 2 volume} :=
  measurableSet_lt (measurable_eLpNorm_two_slice hF) measurable_const

/-- At a fixed point, a mollification of the slice force pressure is
measurable in time. -/
theorem measurable_mollify_forcePressureSliceOfField {F : Vec3 × ℝ → Vec3}
    (hF : StronglyMeasurable F) {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    Measurable fun t : ℝ => mollify (forcePressureSliceOfField F t) ε hε x := by
  let ψ : Vec3 → ℝ := fun z => mollifier ε hε (x - z)
  have hψ : MemLp ψ (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    forcePressure_mollifierTest_memLp hε x
  let H : Vec3 → Vec3 := realVectorL2Representative (forcePressurePairingField ψ hψ)
  have hH : Measurable H := forcePressure_realVectorL2Representative_measurable _
  let good : Set ℝ := {t : ℝ | MemLp (fun x : Vec3 => F (x, t)) 2 volume}
  have heq : (fun t : ℝ => mollify (forcePressureSliceOfField F t) ε hε x) =
      good.indicator fun t => ∫ z : Vec3, ∑ i : Fin 3, H z i * F (z, t) i := by
    funext t
    by_cases ht : MemLp (fun x : Vec3 => F (x, t)) 2 volume
    · rw [Set.indicator_of_mem (show t ∈ good from ht), forcePressure_mollify_eq_integral]
      rw [forcePressureSliceOfField, dite_eq_left ht, integral_forcePressureSlice_mul_eq ψ hψ]
      apply integral_congr_ae
      filter_upwards [realVectorL2OfCoordinateFunction_rep _ ht] with z hz
      rw [hz]
    · rw [Set.indicator_of_notMem (show t ∉ good from ht), forcePressure_mollify_eq_integral]
      rw [forcePressureSliceOfField, dite_eq_right ht]
      simp
  rw [heq]
  refine Measurable.indicator ?_ (measurableSet_memLp_slice hF)
  refine (StronglyMeasurable.integral_prod_left
    (f := fun (z : Vec3) (t : ℝ) => ∑ i : Fin 3, H z i * F (z, t) i) ?_).measurable
  apply Measurable.stronglyMeasurable
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp (hH.comp measurable_fst)).mul
    ((measurable_pi_apply i).comp hF.measurable)

/-- A mollification of the slice force pressure is jointly measurable in
space and time. -/
theorem measurable_mollify_forcePressureSliceOfField_spaceTime
    {F : Vec3 × ℝ → Vec3} (hF : StronglyMeasurable F) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun z : Vec3 × ℝ => mollify (forcePressureSliceOfField F z.2) ε hε z.1 :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Vec3) (t : ℝ) => mollify (forcePressureSliceOfField F t) ε hε x)
    (fun t => mollify_continuous hε (forcePressureSliceOfField_locallyIntegrable F t))
    (fun x => measurable_mollify_forcePressureSliceOfField hF hε x)

theorem forcePressure_radius_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by
  positivity

/-- The jointly measurable force pressure of a space-time field: the limit of
the spatial mollifications of its slice force pressures. -/
@[expose]
def forcePressureOfField (F : Vec3 × ℝ → Vec3) : Vec3 × ℝ → ℝ :=
  fun z => limUnder atTop fun n : ℕ =>
    mollify (forcePressureSliceOfField F z.2) (1 / ((n : ℝ) + 1))
      (forcePressure_radius_pos n) z.1

/-- The force pressure of a strongly measurable field is strongly
measurable. -/
theorem forcePressureOfField_stronglyMeasurable {F : Vec3 × ℝ → Vec3}
    (hF : StronglyMeasurable F) : StronglyMeasurable (forcePressureOfField F) :=
  StronglyMeasurable.limUnder fun n =>
    (measurable_mollify_forcePressureSliceOfField_spaceTime hF
      (forcePressure_radius_pos n)).stronglyMeasurable

/-- Every time slice of the force pressure of a field agrees almost
everywhere with the slice force pressure. -/
theorem forcePressureOfField_slice_ae_eq (F : Vec3 × ℝ → Vec3) (t : ℝ) :
    (fun x : Vec3 => forcePressureOfField F (x, t)) =ᵐ[volume]
      forcePressureSliceOfField F t := by
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure Vec3)) (l := atTop) (K := 2)
    (φ := fun n : ℕ => standardMollifier (d := 3) (1 / ((n : ℝ) + 1))
      (forcePressure_radius_pos n))
    (by simpa only [standardMollifier] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (Eventually.of_forall fun n => by
      simp only [standardMollifier]
      linarith only [forcePressure_radius_pos n])
    (forcePressureSliceOfField_locallyIntegrable F t)
  filter_upwards [hconv] with x hx
  exact hx.limUnder_eq

end CKN.Leray
