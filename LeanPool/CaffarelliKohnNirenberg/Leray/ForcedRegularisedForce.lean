/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildEquation
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMeasurableCurve
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfSlab
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLocallySquareIntegrableForce

/-!
# The force curve of the forced regularized construction

A locally square-integrable force has a strongly measurable modification on
positive times; its time slices form a strongly measurable curve of `L²`
fields whose squared norms are integrable on bounded time intervals. This is
the force entering the Duhamel term of `eq:reg-mild-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

theorem exists_forcedForceModification {f : ParabolicPoint → Vec3}
    (hf : CKN.IsLocallySquareIntegrableForce f) :
    ∃ F : Vec3 × ℝ → Vec3, StronglyMeasurable F ∧
      ∀ T : ℝ, 0 < T → ∀ᵐ z ∂((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))), F z = f z := by
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
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) ⊆ S := fun z hz => ⟨hz.1, hz.2.1⟩
  filter_upwards [ae_restrict_of_ae hg.ae_eq_mk.symm,
    ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioo)] with z hz hzS
  rw [hz, indicator_of_mem (hsub hzS)]

/-- A strongly measurable modification of a locally square-integrable force. -/
@[expose]
def forcedForceMod (f : ParabolicPoint → Vec3) (hf : CKN.IsLocallySquareIntegrableForce f) :
    Vec3 × ℝ → Vec3 :=
  Classical.choose (exists_forcedForceModification hf)

theorem forcedForceMod_stronglyMeasurable (f : ParabolicPoint → Vec3)
    (hf : CKN.IsLocallySquareIntegrableForce f) : StronglyMeasurable (forcedForceMod f hf) :=
  (Classical.choose_spec (exists_forcedForceModification hf)).1

theorem forcedForceMod_ae_eq (f : ParabolicPoint → Vec3)
    (hf : CKN.IsLocallySquareIntegrableForce f) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ z ∂((volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))), forcedForceMod f hf z = f z :=
  (Classical.choose_spec (exists_forcedForceModification hf)).2 T hT

/-- The class of a square-integrable coordinate field agrees on the Euclidean
carrier with the transferred field. -/
theorem realVectorL2OfCoordinateFunction_ae_eq_toLp (a : Vec3 → Vec3) (ha : MemLp a 2 volume) :
    ((realVectorL2OfCoordinateFunction a ha : RealVectorL2) : L2Vec3 → L2Vec3) =ᵐ[volume]
      fun y => WithLp.toLp 2 (a (WithLp.ofLp y)) := by
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (realVectorL2OfCoordinateFunction_rep a ha)
  filter_upwards [h] with y hy
  rw [← hy]
  rfl

/-- The force slice curve of a strongly measurable field is strongly
measurable. -/
theorem forcedForceSlice_stronglyMeasurable {F : Vec3 × ℝ → Vec3} (hF : StronglyMeasurable F) :
    StronglyMeasurable (forcedForceSlice F) := by
  classical
  let G : Set ℝ := {t : ℝ | MemLp (fun x : Vec3 => F (x, t)) 2 volume}
  have hG : MeasurableSet G := measurableSet_memLp_slice hF
  let Γ : L2Vec3 × ℝ → L2Vec3 := fun p =>
    G.indicator (fun s => WithLp.toLp 2 (F (WithLp.ofLp p.1, s))) p.2
  have hΓ : StronglyMeasurable Γ := by
    have hm : Measurable fun p : L2Vec3 × ℝ => WithLp.toLp 2 (F (WithLp.ofLp p.1, p.2)) := by
      have h1 : Measurable fun p : L2Vec3 × ℝ => (WithLp.ofLp p.1, p.2) :=
        ((PiLp.volume_preserving_ofLp (Fin 3)).measurable.comp measurable_fst).prodMk
          measurable_snd
      exact (PiLp.continuous_toLp 2 _).measurable.comp (hF.measurable.comp h1)
    have hm' : Measurable Γ := by
      have h2 := hm.indicator (measurable_snd hG)
      exact h2
    exact hm'.stronglyMeasurable
  refine stronglyMeasurable_of_jointRep Γ hΓ _ fun s => ?_
  by_cases hs : MemLp (fun x : Vec3 => F (x, s)) 2 volume
  · have heq : forcedForceSlice F s = realVectorL2OfCoordinateFunction _ hs := by
      unfold forcedForceSlice
      rw [dite_eq_left hs]
    rw [heq]
    have hsG : s ∈ G := hs
    filter_upwards [realVectorL2OfCoordinateFunction_ae_eq_toLp _ hs] with y hy
    simp only [Γ, indicator_of_mem hsG, hy]
  · have heq : forcedForceSlice F s = 0 := by
      unfold forcedForceSlice
      rw [dite_eq_right hs]
    rw [heq]
    have hsG : s ∉ G := hs
    filter_upwards [Lp.coeFn_zero L2Vec3 2 (volume : Measure L2Vec3)] with y hy
    simp only [Γ, indicator_of_notMem hsG, hy, Pi.zero_apply]

theorem norm_forcedForceSlice_le (F : Vec3 × ℝ → Vec3) (s : ℝ) :
    ‖forcedForceSlice F s‖ ≤ 2 * (eLpNorm (fun x : Vec3 => F (x, s)) 2 volume).toReal := by
  unfold forcedForceSlice
  by_cases hs : MemLp (fun x : Vec3 => F (x, s)) 2 volume
  · rw [dite_eq_left hs, Lp.norm_def]
    have h := eLpNorm_realVectorL2OfCoordinateFunction_le _ hs
    calc (eLpNorm (realVectorL2OfCoordinateFunction (fun x : Vec3 => F (x, s)) hs) 2
          volume).toReal
        ≤ (2 * eLpNorm (fun x : Vec3 => F (x, s)) 2 volume).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hs.eLpNorm_ne_top) h
      _ = 2 * (eLpNorm (fun x : Vec3 => F (x, s)) 2 volume).toReal := by
          rw [ENNReal.toReal_mul]; norm_num
  · rw [dite_eq_right hs, norm_zero]
    positivity

/-- The strongly measurable modification is square integrable on every
positive-time slab. -/
theorem memLp_forcedForceMod_prod (f : ParabolicPoint → Vec3)
    (hf : CKN.IsLocallySquareIntegrableForce f) {T : ℝ} (hT : 0 < T) :
    MemLp (forcedForceMod f hf) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have hmeas : ((volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
    rw [forcedHopf_slab_measure_eq_prod, Measure.restrict_univ]
  have h2 : eLpNorm (forcedForceMod f hf) 2 ((volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) < ⊤ := by
    rw [eLpNorm_congr_ae (forcedForceMod_ae_eq f hf hT)]
    exact hf T hT
  exact hmeas ▸ h2

/-- The squared norms of the force curve are integrable on bounded time
intervals. -/
theorem integrableOn_forcedForceSlice_sq (f : ParabolicPoint → Vec3)
    (hf : CKN.IsLocallySquareIntegrableForce f) (T : ℝ) :
    IntegrableOn (fun s => ‖forcedForceSlice (forcedForceMod f hf) s‖ ^ 2) (Ioc 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · rw [Ioc_eq_empty (not_lt.2 hT)]
    exact integrableOn_empty
  set F := forcedForceMod f hf with hFdef
  have hF := forcedForceMod_stronglyMeasurable f hf
  have hslab : eLpNorm F 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))
      < ⊤ := memLp_forcedForceMod_prod f hf hT
  have hlint : ∫⁻ s in Ioo 0 T, eLpNorm (fun x : Vec3 => F (x, s)) 2 volume ^ (2 : ℝ) ≠ ⊤ := by
    rw [lintegral_eLpNorm_slice_sq_eq hF]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hslab.ne).ne
  have hmeas : Measurable fun s => eLpNorm (fun x : Vec3 => F (x, s)) 2 volume ^ (2 : ℝ) :=
    (measurable_eLpNorm_two_slice hF).pow_const _
  have hint : IntegrableOn (fun s =>
      (eLpNorm (fun x : Vec3 => F (x, s)) 2 volume ^ (2 : ℝ)).toReal) (Ioo 0 T) :=
    integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hlint
  have hint' : IntegrableOn (fun s => ‖forcedForceSlice F s‖ ^ 2) (Ioo 0 T) := by
    refine Integrable.mono' (hint.const_mul 4) ?_ (Eventually.of_forall fun s => ?_)
    · exact ((forcedForceSlice_stronglyMeasurable hF).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← ENNReal.toReal_rpow]
      have h := norm_forcedForceSlice_le F s
      have h0 := norm_nonneg (forcedForceSlice F s)
      rw [show (eLpNorm (fun x : Vec3 => F (x, s)) 2 volume).toReal ^ (2 : ℝ) =
        (eLpNorm (fun x : Vec3 => F (x, s)) 2 volume).toReal ^ 2 from Real.rpow_two _]
      nlinarith only [h, h0]
  exact (integrableOn_Ioc_iff_integrableOn_Ioo).2 hint'

end CKN.Leray

end
