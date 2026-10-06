/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling

/-!
# Time translation of strong solutions

A strong solution on `[0, τ]` translated in time is a strong solution on `[a, a + τ]`
(`prop:lps-local-strong`). The weak-derivative and equation clauses transfer by the
measure-preserving time translation of the space-time slab.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS.LPS

private instance lpsShiftParabolicVolumeIsLocallyFinite :
    IsLocallyFiniteMeasure (volume : Measure ParabolicPoint) :=
  ⟨fun z => ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos,
    CKN.Foundation.Parabolic.volume_parabolicBall_lt_top one_pos⟩⟩

/-- The time translation `(x, s) ↦ (x, s - a)` of space-time. -/
@[expose] def lpsTimeShift (a : ℝ) (z : ParabolicPoint) : ParabolicPoint := (z.1, z.2 - a)

/-- The time translation preserves Lebesgue measure on space-time. -/
theorem lps_timeShift_measurePreserving (a : ℝ) :
    MeasurePreserving (lpsTimeShift a) (volume : Measure ParabolicPoint) volume := by
  have h := (MeasurePreserving.id (volume : Measure Vec3)).prod (measurePreserving_sub_right (volume : Measure ℝ) a)
  rw [← Measure.volume_eq_prod] at h
  exact h

/-- The time translation is a measurable embedding. -/
theorem lps_timeShift_measurableEmbedding (a : ℝ) : MeasurableEmbedding (lpsTimeShift a) := by
  have : lpsTimeShift a = Prod.map id (fun s : ℝ => s - a) := rfl
  rw [this]
  exact MeasurableEmbedding.id.prodMap (measurableEmbedding_subRight a)

/-- The preimage of a time interval under the time translation. -/
theorem lps_preimage_Ioo_shift (a τ : ℝ) :
    (fun s : ℝ => s - a) ⁻¹' Ioo 0 τ = Ioo a (a + τ) := by
  ext s
  simp only [Set.mem_preimage, Set.mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]

/-- Square integrability on a slab is preserved by the time translation. -/
theorem lps_memLp_timeShift {E : Type} [NormedAddCommGroup E] (a τ : ℝ) {f : ParabolicPoint → E}
    (hf : MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) :
    MemLp (fun z : ParabolicPoint => f (lpsTimeShift a z)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a (a + τ)))) := by
  have hpre : spaceTimeSet (Set.univ : Set Vec3) (Ioo a (a + τ)) =
      lpsTimeShift a ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) := by
    ext z
    rw [← lps_preimage_Ioo_shift a τ]
    exact Iff.rfl
  rw [hpre]
  exact hf.comp_measurePreserving
    ((lps_timeShift_measurePreserving a).restrict_preimage_emb
      (lps_timeShift_measurableEmbedding a) _)

/-- The time-translation homeomorphism `(x, s) ↦ (x, s + a)`. -/
@[expose] def lpsTimeTranslate (a : ℝ) : Vec3 × ℝ ≃ₜ Vec3 × ℝ :=
  Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addRight a)

/-- A translated space-time test function is a test function on the translated slab. -/
theorem lps_testFunction_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a τ : ℝ) {φ : Vec3 × ℝ → V}
    (hφ : φ ∈ spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo a (a + τ))) :
    (fun w : ParabolicPoint => φ (w.1, w.2 + a)) ∈
      spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo 0 τ) := by
  obtain ⟨hsm, hcpt, hts⟩ := hφ
  have hfun : (fun w : ParabolicPoint => φ (w.1, w.2 + a)) = φ ∘ (lpsTimeTranslate a) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    refine hsm.comp ?_
    exact (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  · rw [hfun]
    exact hcpt.comp_homeomorph _
  · rw [hfun, tsupport_comp_eq_preimage]
    intro w hw
    have := hts hw
    have e : (lpsTimeTranslate a w).2 = w.2 + a := rfl
    have h2 := this.2
    rw [e] at h2
    exact ⟨Set.mem_univ _, by constructor <;> linarith only [h2.1, h2.2]⟩

/-- Spatial partial derivatives commute with time translation. -/
theorem lps_spatialPartial_timeTranslate (a : ℝ) (g : ParabolicPoint → ℝ) (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w : ParabolicPoint => g (w.1, w.2 + a)) j z = spatialPartial g j (z.1, z.2 + a) :=
  rfl

/-- The time partial derivative commutes with time translation. -/
theorem lps_timePartial_timeTranslate (a : ℝ) (g : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    timePartial (fun w : ParabolicPoint => g (w.1, w.2 + a)) z = timePartial g (z.1, z.2 + a) := by
  unfold timePartial
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := fun s : ℝ => g (z.1, s)) (x := z.2) a
  simp only at this ⊢
  rw [this]


/-- Change of variables for the time translation on a slab. -/
theorem lps_shift_integral (a τ : ℝ) (g G : ParabolicPoint → ℝ)
    (hG : ∀ z, G z = g (lpsTimeShift a z)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a (a + τ)), G z) =
      ∫ w in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), g w := by
  have hGe : G = fun z => g (lpsTimeShift a z) := funext hG
  rw [hGe, ← lps_preimage_Ioo_shift a τ]
  have hpre : spaceTimeSet (Set.univ : Set Vec3) ((fun s => s - a) ⁻¹' Ioo 0 τ) =
      lpsTimeShift a ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) := by
    ext z
    exact Iff.rfl
  rw [hpre]
  exact (lps_timeShift_measurePreserving a).setIntegral_preimage_emb
    (lps_timeShift_measurableEmbedding a) g _

/-- A field in `L²` of a slab is locally integrable on it. -/
theorem lps_locallyIntegrableOn_of_memLp {E : Type} [NormedAddCommGroup E] {f : ParabolicPoint → E}
    {I : Set ℝ}
    (hf : MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I))) :
    LocallyIntegrableOn f (spaceTimeSet (Set.univ : Set Vec3) I) := by
  exact locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable (by norm_num))


/-- Spatial derivative of a translated test function. -/
theorem lps_phiShift_spatial (a : ℝ) (φ : ParabolicPoint → ℝ) (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w : ParabolicPoint => φ (w.1, w.2 + a)) j (lpsTimeShift a z) =
      spatialPartial φ j z := by
  rw [lps_spatialPartial_timeTranslate]
  simp [lpsTimeShift]
  rfl

/-- Time derivative of a translated test function. -/
theorem lps_phiShift_time (a : ℝ) (φ : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    timePartial (fun w : ParabolicPoint => φ (w.1, w.2 + a)) (lpsTimeShift a z) = timePartial φ z := by
  rw [lps_timePartial_timeTranslate]
  simp [lpsTimeShift]
  rfl

/-- Value of a translated test function. -/
theorem lps_phiShift_value (a : ℝ) (φ : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    (fun w : ParabolicPoint => φ (w.1, w.2 + a)) (lpsTimeShift a z) = φ z := by
  simp [lpsTimeShift]
  rfl

/-- Space-time weak derivatives transfer under time translation. -/
theorem lps_hasSpaceTimeWeakDerivs_shift {a τ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hw : CKN.HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo 0 τ) u Du D2u Dtu)
    (hu2 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hDu2 : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hD2u2 : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hDtu2 : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) :
    CKN.HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo a (a + τ))
      (fun z => u (lpsTimeShift a z)) (fun z i => Du (lpsTimeShift a z) i)
      (fun z i j => D2u (lpsTimeShift a z) i j) (fun z => Dtu (lpsTimeShift a z)) := by
  obtain ⟨-, -, -, -, hid⟩ := hw
  refine ⟨lps_locallyIntegrableOn_of_memLp (lps_memLp_timeShift a τ hu2),
    lps_locallyIntegrableOn_of_memLp (lps_memLp_timeShift a τ hDu2),
    lps_locallyIntegrableOn_of_memLp (lps_memLp_timeShift a τ hD2u2),
    lps_locallyIntegrableOn_of_memLp (lps_memLp_timeShift a τ hDtu2), ?_⟩
  intro φ hφ
  have hφ' := lps_testFunction_shift (V := ℝ) a τ hφ
  obtain ⟨h1, h2, h3⟩ := hid _ hφ'
  refine ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩
  · have e := h1 i j
    rw [← lps_shift_integral a τ (fun w => u w i * spatialPartial (fun w : ParabolicPoint => φ (w.1, w.2 + a)) j w)
        (fun z => u (lpsTimeShift a z) i * spatialPartial φ j z)
        (fun z => by rw [lps_phiShift_spatial])] at e
    rw [← lps_shift_integral a τ (fun w => Du w i j * (fun w : ParabolicPoint => φ (w.1, w.2 + a)) w)
        (fun z => Du (lpsTimeShift a z) i j * φ z)
        (fun z => by rw [lps_phiShift_value])] at e
    exact e
  · have e := h2 i j k
    rw [← lps_shift_integral a τ (fun w => Du w i j * spatialPartial (fun w : ParabolicPoint => φ (w.1, w.2 + a)) k w)
        (fun z => Du (lpsTimeShift a z) i j * spatialPartial φ k z)
        (fun z => by rw [lps_phiShift_spatial])] at e
    rw [← lps_shift_integral a τ (fun w => D2u w i j k * (fun w : ParabolicPoint => φ (w.1, w.2 + a)) w)
        (fun z => D2u (lpsTimeShift a z) i j k * φ z)
        (fun z => by rw [lps_phiShift_value])] at e
    exact e
  · have e := h3 i
    rw [← lps_shift_integral a τ (fun w => u w i * timePartial (fun w : ParabolicPoint => φ (w.1, w.2 + a)) w)
        (fun z => u (lpsTimeShift a z) i * timePartial φ z)
        (fun z => by rw [lps_phiShift_time])] at e
    rw [← lps_shift_integral a τ (fun w => Dtu w i * (fun w : ParabolicPoint => φ (w.1, w.2 + a)) w)
        (fun z => Dtu (lpsTimeShift a z) i * φ z)
        (fun z => by rw [lps_phiShift_value])] at e
    exact e

/-- A strong solution on `[0, τ]` translated by `a` is a strong solution on `[a, a + τ]` (`prop:lps-local-strong`). -/
theorem lps_isLpsStrongSolution_shift {a τ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (h : ESS.IsLpsStrongSolution 0 τ u Du p) :
    ESS.IsLpsStrongSolution a (a + τ) (fun z => u (lpsTimeShift a z))
      (fun z i => Du (lpsTimeShift a z) i) (fun z => p (lpsTimeShift a z)) := by
  obtain ⟨hτ, hslice, hcont, ⟨D2u, Dtu, hweak, hu2, hDu2, hD2u2, hDtu2⟩, hp2, heq⟩ := h
  refine ⟨by linarith only [hτ], ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h1 := hslice (t - a) ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    simp only [lpsTimeShift]
    exact h1
  · intro t ht
    have h1 := hcont (t - a) ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    have hmap : Tendsto (fun s : ℝ => s - a) (nhdsWithin t (Icc a (a + τ)))
        (nhdsWithin (t - a) (Icc 0 τ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (continuous_sub_right a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    simp only [lpsTimeShift]
    exact ⟨h1.1.comp hmap, h1.2.comp hmap⟩
  · refine ⟨fun z => D2u (lpsTimeShift a z), fun z => Dtu (lpsTimeShift a z), ?_, ?_, ?_, ?_, ?_⟩
    · exact lps_hasSpaceTimeWeakDerivs_shift hweak hu2 hDu2 hD2u2 hDtu2
    · exact lps_memLp_timeShift a τ hu2
    · exact lps_memLp_timeShift a τ hDu2
    · exact lps_memLp_timeShift a τ hD2u2
    · exact lps_memLp_timeShift a τ hDtu2
  · exact lps_memLp_timeShift a τ hp2
  · intro φ hφ
    have hφ' := lps_testFunction_shift (V := Vec3) a τ hφ
    have e := heq _ hφ'
    have hT (i : Fin 3) (z : ParabolicPoint) :
        timePartial (fun y : ParabolicPoint => φ (y.1, y.2 + a) i) (lpsTimeShift a z) =
          timePartial (fun y => φ y i) z := lps_phiShift_time a (fun y => φ y i) z
    have hS (i j : Fin 3) (z : ParabolicPoint) :
        spatialPartial (fun y : ParabolicPoint => φ (y.1, y.2 + a) i) j (lpsTimeShift a z) =
          spatialPartial (fun y => φ y i) j z := lps_phiShift_spatial a (fun y => φ y i) j z
    refine (lps_shift_integral a τ (fun w =>
        (-(∑ i : Fin 3, u w i * timePartial (fun y : ParabolicPoint => φ (y.1, y.2 + a) i) w))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u w i * u w j * spatialPartial (fun y : ParabolicPoint => φ (y.1, y.2 + a) i) j w
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du w i j * spatialPartial (fun y : ParabolicPoint => φ (y.1, y.2 + a) i) j w
          - p w * ∑ i : Fin 3, spatialPartial (fun y : ParabolicPoint => φ (y.1, y.2 + a) i) i w)
        (fun z =>
        (-(∑ i : Fin 3, u (lpsTimeShift a z) i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u (lpsTimeShift a z) i * u (lpsTimeShift a z) j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du (lpsTimeShift a z) i j * spatialPartial (fun y => φ y i) j z
          - p (lpsTimeShift a z) * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
        (fun z => by simp only [hT, hS])).trans e

end ESS.LPS
