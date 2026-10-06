/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureLocalBound
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLocallySquareIntegrableForce

/-!
# The force pressure

This file proves `lem:force-pressure` in the form used by the forced Leray
existence assembly: for a force that is square integrable on every finite
slab, there is a jointly measurable pressure p_f with p_f(·, t) ∈ L⁶ and
weak gradient (I - ℙ) f(·, t) for almost every time, with
p_f ∈ L²_t L⁶_x on every slab and the local bound
`eq:force-pressure-local`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem forcePressure_toLp_norm_le (y : Vec3) :
    ‖(WithLp.toLp 2 y : L2Vec3)‖ ≤ 2 * ‖y‖ := by
  rw [PiLp.norm_eq_of_L2]
  have hsum : ∑ i : Fin 3, ‖(WithLp.toLp 2 y : L2Vec3) i‖ ^ 2 ≤ (2 * ‖y‖) ^ 2 := by
    calc
      ∑ i : Fin 3, ‖(WithLp.toLp 2 y : L2Vec3) i‖ ^ 2 ≤ ∑ _i : Fin 3, ‖y‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm y i) 2
      _ = 3 * ‖y‖ ^ 2 := by simp
      _ ≤ (2 * ‖y‖) ^ 2 := by nlinarith only [sq_nonneg ‖y‖]
  calc
    Real.sqrt (∑ i : Fin 3, ‖(WithLp.toLp 2 y : L2Vec3) i‖ ^ 2) ≤
        Real.sqrt ((2 * ‖y‖) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * ‖y‖ := Real.sqrt_sq (by positivity)

/-- The Hilbert field transferred from a coordinate L² field has at most
twice its L² norm. -/
theorem eLpNorm_realVectorL2OfCoordinateFunction_le (a : Vec3 → Vec3)
    (ha : MemLp a 2 volume) :
    eLpNorm (realVectorL2OfCoordinateFunction a ha) 2 volume ≤ 2 * eLpNorm a 2 volume := by
  set v := realVectorL2OfCoordinateFunction a ha
  rw [← eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable v)
    vec3ToL2Vec3_measurePreserving]
  have hbound := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := 2) (g := a) (p := 2)
    ((Lp.aestronglyMeasurable v).comp_measurePreserving vec3ToL2Vec3_measurePreserving)
    (by
      filter_upwards [realVectorL2OfCoordinateFunction_rep a ha] with x hx
      have hv : (v ∘ WithLp.toLp 2) x = WithLp.toLp 2 (realVectorL2Representative v x) := rfl
      rw [hv, hx]
      exact forcePressure_toLp_norm_le (a x))
  simpa using hbound

/-- The slice force pressure of a field is bounded in L⁶ by the L² norm of
the time slice. -/
theorem forcePressureSliceOfField_eLpNorm_le (F : Vec3 × ℝ → Vec3) (t : ℝ) :
    eLpNorm (forcePressureSliceOfField F t) 6 volume ≤
      4 * gagliardoNirenbergSobolevConstant * eLpNorm (fun x : Vec3 => F (x, t)) 2 volume := by
  by_cases h : MemLp (fun x : Vec3 => F (x, t)) 2 volume
  · rw [forcePressureSliceOfField, dite_eq_left h]
    set v := realVectorL2OfCoordinateFunction (fun x : Vec3 => F (x, t)) h
    have hg : eLpNorm (forcePressureGradientL2 v) 2 volume ≤ 2 * eLpNorm v 2 volume := by
      rw [← Lp.enorm_def, ← Lp.enorm_def, ← ofReal_norm, ← ofReal_norm]
      calc
        ENNReal.ofReal ‖forcePressureGradientL2 v‖ ≤ ENNReal.ofReal (2 * ‖v‖) :=
          ENNReal.ofReal_le_ofReal (forcePressureGradientL2_norm_le v)
        _ = 2 * ENNReal.ofReal ‖v‖ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    calc
      eLpNorm (forcePressureSlice v) 6 volume ≤
          gagliardoNirenbergSobolevConstant * eLpNorm (forcePressureGradientL2 v) 2 volume :=
        forcePressureSlice_eLpNorm_le v
      _ ≤ gagliardoNirenbergSobolevConstant * (2 * eLpNorm v 2 volume) := by gcongr
      _ ≤ gagliardoNirenbergSobolevConstant *
          (2 * (2 * eLpNorm (fun x : Vec3 => F (x, t)) 2 volume)) := by
        gcongr
        exact eLpNorm_realVectorL2OfCoordinateFunction_le _ h
      _ = 4 * gagliardoNirenbergSobolevConstant *
          eLpNorm (fun x : Vec3 => F (x, t)) 2 volume := by ring
  · rw [forcePressureSliceOfField, dite_eq_right h]
    simp

private theorem forcePressure_slab_measure_eq (T : ℝ) :
    (volume : Measure ParabolicPoint).restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) =
      (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
  change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) = _
  rw [← Measure.prod_restrict, Measure.restrict_univ]

private theorem forcePressure_box_measure_eq (K : Set Vec3) (I : Set ℝ) :
    (volume : Measure ParabolicPoint).restrict (spaceTimeSet K I) =
      ((volume : Measure Vec3).restrict K).prod ((volume : Measure ℝ).restrict I) := by
  change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (K ×ˢ I) = _
  rw [← Measure.prod_restrict]

private theorem forcePressure_ae_slices {μt : Measure ℝ} [SFinite μt]
    {p : Vec3 × ℝ → Prop}
    (h : ∀ᵐ z ∂((volume : Measure Vec3).prod μt), p z) :
    ∀ᵐ t ∂μt, ∀ᵐ x ∂(volume : Measure Vec3), p (x, t) := by
  have h' := (Measure.measurePreserving_swap (μ := μt)
    (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h'

/-- Tonelli's formula for the squared L² norm on a product with a time
measure, slice by slice. -/
theorem lintegral_eLpNorm_slice_sq_eq {μt : Measure ℝ} [SFinite μt]
    {F : Vec3 × ℝ → Vec3} (hF : StronglyMeasurable F) :
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

private theorem forcePressure_exists_modification {f : ParabolicPoint → Vec3}
    (hf : IsLocallySquareIntegrableForce f) :
    ∃ F : Vec3 × ℝ → Vec3, StronglyMeasurable F ∧
      ∀ T : ℝ, 0 < T → ∀ᵐ z ∂((volume : Measure Vec3).prod
        ((volume : Measure ℝ).restrict (Ioo 0 T))), F z = f z := by
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)
  have hSmeas : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioi
  have hunion : S = ⋃ n : ℕ, spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 ((n : ℝ) + 1)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_gt z.2
      exact mem_iUnion.2 ⟨n, ⟨mem_univ _, hz.2, by linarith only [hn]⟩⟩
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.1 hz
      exact ⟨mem_univ _, hn.2.1⟩
  have hfS : AEStronglyMeasurable f ((volume : Measure ParabolicPoint).restrict S) := by
    rw [hunion, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hf ((n : ℝ) + 1) (by positivity)).aestronglyMeasurable
  have hg : AEStronglyMeasurable (S.indicator f) (volume : Measure ParabolicPoint) :=
    (aestronglyMeasurable_indicator_iff hSmeas).2 hfS
  refine ⟨hg.mk _, hg.stronglyMeasurable_mk, fun T _ => ?_⟩
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) ⊆ S := by
    intro z hz
    exact ⟨hz.1, hz.2.1⟩
  have h : ∀ᵐ z ∂((volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))), hg.mk _ z = f z := by
    filter_upwards [ae_restrict_of_ae hg.ae_eq_mk.symm,
      ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioo)] with z hz hzS
    rw [hz, indicator_of_mem (hsub hzS)]
  rw [forcePressure_slab_measure_eq] at h
  exact h

/-- Existence in `lem:force-pressure`: a strongly measurable pressure whose
time slices lie in L²_t L⁶_x on every slab and have weak gradient
(I - ℙ) f(·, t) for almost every time. -/
theorem exists_forcePressure (f : ParabolicPoint → Vec3)
    (hf : IsLocallySquareIntegrableForce f) :
    ∃ P : Vec3 × ℝ → ℝ, StronglyMeasurable P ∧ ∀ T : ℝ, 0 < T →
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => P (x, t)) (ENNReal.ofReal (6 : ℝ))
          (volume : Measure Vec3) ^ (2 : ℝ) ∂(volume : Measure ℝ)) < ⊤ ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        ∃ hft : MemLp (fun x : Vec3 => f (x, t)) (2 : ℝ≥0∞) volume,
          HasWeakGradientOn (Set.univ : Set Vec3)
            (fun x : Vec3 => P (x, t))
            (fun x i => CKN.Leray.forcePressureGradientFunction
              (fun y : Vec3 => f (y, t)) hft x i)) := by
  obtain ⟨F, hF, hFf⟩ := forcePressure_exists_modification hf
  refine ⟨forcePressureOfField F, forcePressureOfField_stronglyMeasurable hF, ?_⟩
  intro T hT
  have hFmem : MemLp F 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
    have h := hf T hT
    rw [forcePressure_slab_measure_eq] at h
    exact h.ae_eq ((hFf T hT).mono fun z hz => hz.symm)
  have hslice_eq (t : ℝ) :
      eLpNorm (fun x : Vec3 => forcePressureOfField F (x, t)) (ENNReal.ofReal (6 : ℝ)) volume =
        eLpNorm (forcePressureSliceOfField F t) 6 volume := by
    rw [ENNReal.ofReal_ofNat]
    exact eLpNorm_congr_ae (forcePressureOfField_slice_ae_eq F t)
  constructor
  · calc
      (∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => forcePressureOfField F (x, t))
          (ENNReal.ofReal (6 : ℝ)) volume ^ (2 : ℝ)) ≤
          ∫⁻ t in Ioo 0 T, (4 * gagliardoNirenbergSobolevConstant) ^ (2 : ℝ) *
            eLpNorm (fun x : Vec3 => F (x, t)) 2 volume ^ (2 : ℝ) := by
        apply lintegral_mono
        intro t
        dsimp only
        rw [hslice_eq, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        gcongr
        exact forcePressureSliceOfField_eLpNorm_le F t
      _ = (4 * gagliardoNirenbergSobolevConstant) ^ (2 : ℝ) *
          eLpNorm F 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))
            ^ (2 : ℝ) := by
        rw [lintegral_const_mul' _ _ (by
          apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          exact ENNReal.mul_ne_top (by norm_num) gagliardoNirenbergSobolevConstant_ne_top),
          lintegral_eLpNorm_slice_sq_eq hF]
      _ < ⊤ := by
        apply ENNReal.mul_lt_top
        · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            (ENNReal.mul_ne_top (by norm_num) gagliardoNirenbergSobolevConstant_ne_top)
        · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hFmem.eLpNorm_lt_top.ne
  · -- slices of f and of the modification agree, and are square integrable
    have hslices := forcePressure_ae_slices (hFf T hT)
    have hfin : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
        eLpNorm (fun x : Vec3 => F (x, t)) 2 volume ^ (2 : ℝ) < ⊤ := by
      apply ae_lt_top'
      · exact ((measurable_eLpNorm_two_slice hF).pow_const _).aemeasurable
      · rw [lintegral_eLpNorm_slice_sq_eq hF]
        exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hFmem.eLpNorm_lt_top.ne).ne
    filter_upwards [hslices, hfin] with t ht htfin
    have hFt : MemLp (fun x : Vec3 => F (x, t)) 2 volume := by
      have h2 : eLpNorm (fun x : Vec3 => F (x, t)) 2 volume < ⊤ := by
        by_contra hcon
        rw [not_lt, top_le_iff] at hcon
        rw [hcon, ENNReal.top_rpow_of_pos (by norm_num)] at htfin
        exact lt_irrefl _ htfin
      exact h2
    have hft : MemLp (fun x : Vec3 => f (x, t)) 2 volume := hFt.ae_eq ht
    refine ⟨hft, ?_⟩
    have hclass : realVectorL2OfCoordinateFunction (fun x : Vec3 => F (x, t)) hFt =
        realVectorL2OfCoordinateFunction (fun x : Vec3 => f (x, t)) hft := by
      apply realVectorL2Representative_injective_ae
      filter_upwards [realVectorL2OfCoordinateFunction_rep _ hFt,
        realVectorL2OfCoordinateFunction_rep _ hft, ht] with x h1 h2 h3
      rw [h1, h2, h3]
    have hP := forcePressureOfField_slice_ae_eq F t
    rw [forcePressureSliceOfField, dite_eq_left hFt, hclass] at hP
    have hgrad := forcePressureSlice_hasWeakGradientOn
      (realVectorL2OfCoordinateFunction (fun x : Vec3 => f (x, t)) hft)
    exact hasWeakGradientOn_congr_ae_left hP.symm hgrad

/-- The force pressure p_f of `lem:force-pressure`: a jointly measurable
pressure whose time slices are the L⁶ pressures with weak gradient
(I - ℙ) f(·, t). -/
@[expose]
def forcePressure (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f) :
    ParabolicPoint → ℝ :=
  Classical.choose (exists_forcePressure f hf)

/-- `lem:force-pressure`, with `eq:force-pressure-identities` and
`eq:force-pressure-local`, in the form of the force-pressure input of the
forced Leray existence assembly: on every slab the force pressure is
measurable, lies in L²_t L⁶_x, has weak gradient (I - ℙ) f(·, t) for almost
every time, and satisfies the local L^{3/2} bound on every cylinder. -/
theorem forcePressure_spec :
    ∀ (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f) (T : ℝ), 0 < T →
      AEStronglyMeasurable (forcePressure f hf)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => forcePressure f hf (x, t)) (ENNReal.ofReal (6 : ℝ))
          (volume : Measure Vec3) ^ (2 : ℝ) ∂(volume : Measure ℝ)) < ⊤ ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        ∃ hft : MemLp (fun x : Vec3 => f (x, t)) (2 : ℝ≥0∞) volume,
          HasWeakGradientOn (Set.univ : Set Vec3)
            (fun x : Vec3 => forcePressure f hf (x, t))
            (fun x i => CKN.Leray.forcePressureGradientFunction
              (fun y : Vec3 => f (y, t)) hft x i)) ∧
      (∀ (K : Set Vec3) (I : Set ℝ), MeasurableSet K → MeasurableSet I →
        I ⊆ Ioo 0 T →
        eLpNorm (forcePressure f hf) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (spaceTimeSet K I)) ≤
          volume K ^ (1 / 2 : ℝ) * volume I ^ (1 / 6 : ℝ) *
            (∫⁻ t in Ioo 0 T,
              eLpNorm (fun x : Vec3 => forcePressure f hf (x, t))
                (ENNReal.ofReal (6 : ℝ)) (volume : Measure Vec3) ^ (2 : ℝ)
                ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ)) := by
  intro f hf T hT
  obtain ⟨hP, hslab⟩ := Classical.choose_spec (exists_forcePressure f hf)
  obtain ⟨hfin, hgrad⟩ := hslab T hT
  refine ⟨hP.aestronglyMeasurable, hfin, hgrad, ?_⟩
  intro K I _ _ hIT
  exact eLpNorm_threeHalves_cylinder_le hP K hIT

end CKN.Leray
