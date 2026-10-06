/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Group.Measure

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Reflection of the time coordinate in the terminal face. -/
@[expose] def essLocalTimeReflection : ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans
    (Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.neg ℝ))).trans
    parabolicHomeomorph.symm

@[simp] theorem essLocalTimeReflection_apply (z : ParabolicPoint) :
    essLocalTimeReflection z = (z.1, -z.2) := rfl

/-- Translation of the spatial coordinate in parabolic space-time. -/
@[expose] def essLocalSpatialTranslate (c : Vec3) : ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans
    (Homeomorph.prodCongr (Homeomorph.addLeft c) (Homeomorph.refl ℝ))).trans
    parabolicHomeomorph.symm

@[simp] theorem essLocalSpatialTranslate_apply (c : Vec3) (z : ParabolicPoint) :
    essLocalSpatialTranslate c z = (c + z.1, z.2) := by
  simp [essLocalSpatialTranslate]
  rfl

/-- Translation of the time coordinate in parabolic space-time. -/
@[expose] def essLocalTimeTranslate (d : ℝ) : ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans
    (Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addLeft d))).trans
    parabolicHomeomorph.symm

@[simp] theorem essLocalTimeTranslate_apply (d : ℝ) (z : ParabolicPoint) :
    essLocalTimeTranslate d z = (z.1, d + z.2) := by
  simp [essLocalTimeTranslate]
  rfl

/-- Spatial translation preserves parabolic space-time volume. -/
theorem essLocalSpatialTranslate_measurePreserving (c : Vec3) :
    MeasurePreserving (essLocalSpatialTranslate c)
      (volume : Measure ParabolicPoint) (volume : Measure ParabolicPoint) := by
  have hspace : MeasurePreserving (Homeomorph.addLeft c)
      (volume : Measure Vec3) (volume : Measure Vec3) :=
    measurePreserving_add_left (volume : Measure Vec3) c
  have hprod : MeasurePreserving
      (Homeomorph.prodCongr (Homeomorph.addLeft c) (Homeomorph.refl ℝ))
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    hspace.prod (MeasurePreserving.id (volume : Measure ℝ))
  have h₁ := hprod.comp parabolicHomeomorph_measurePreserving
  have h₂ := parabolicHomeomorphSymm_measurePreserving.comp h₁
  change MeasurePreserving
    (parabolicHomeomorph.symm ∘
      Homeomorph.prodCongr (Homeomorph.addLeft c) (Homeomorph.refl ℝ) ∘
      parabolicHomeomorph) volume volume at h₂
  convert h₂ using 1
  funext z
  rfl

/-- Time translation preserves parabolic space-time volume. -/
theorem essLocalTimeTranslate_measurePreserving (d : ℝ) :
    MeasurePreserving (essLocalTimeTranslate d)
      (volume : Measure ParabolicPoint) (volume : Measure ParabolicPoint) := by
  have htime : MeasurePreserving (Homeomorph.addLeft d)
      (volume : Measure ℝ) (volume : Measure ℝ) :=
    measurePreserving_add_left (volume : Measure ℝ) d
  have hprod : MeasurePreserving
      (Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addLeft d))
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    (MeasurePreserving.id (volume : Measure Vec3)).prod htime
  have h₁ := hprod.comp parabolicHomeomorph_measurePreserving
  have h₂ := parabolicHomeomorphSymm_measurePreserving.comp h₁
  change MeasurePreserving
    (parabolicHomeomorph.symm ∘
      Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addLeft d) ∘
      parabolicHomeomorph) volume volume at h₂
  convert h₂ using 1
  funext z
  rfl

private theorem essLocal_locallyIntegrableOn_homeomorph
    {Qtarget Qsource : Set ParabolicPoint}
    (e : ParabolicPoint ≃ₜ ParabolicPoint)
    (hQtarget : IsOpen Qtarget) (himage : e '' Qtarget = Qsource)
    (hmp : MeasurePreserving e (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ParabolicPoint → E}
    (hf : LocallyIntegrableOn f Qsource volume) :
    LocallyIntegrableOn (fun z => f (e z)) Qtarget volume := by
  have hcompact : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  rw [locallyIntegrableOn_iff hQtarget.isLocallyClosed]
  intro K hKsub hKcompact
  have hsub : e '' K ⊆ Qsource := by
    rw [← himage]
    exact image_mono hKsub
  have hsource := hf.integrableOn_compact_subset hsub
    (hKcompact.image e.continuous)
  exact (hmp.integrableOn_image e.measurableEmbedding).mp hsource

/-- Reflection of time preserves parabolic space-time volume. -/
theorem essLocalTimeReflection_measurePreserving :
    MeasurePreserving essLocalTimeReflection
      (volume : Measure ParabolicPoint) (volume : Measure ParabolicPoint) := by
  let f : ℝ →ₗ[ℝ] ℝ := (-1 : ℝ) • LinearMap.id
  have hfdet : LinearMap.det f = -1 := by
    dsimp [f]
    rw [LinearMap.det_smul, LinearMap.det_id]
    simp
  have hnegMap : Measure.map (fun t : ℝ => -t) (volume : Measure ℝ) = volume := by
    have hdetne : LinearMap.det f ≠ 0 := by rw [hfdet]; norm_num
    have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (volume : Measure ℝ)) hdetne
    calc
      Measure.map (fun t : ℝ => -t) (volume : Measure ℝ) =
          Measure.map (f : ℝ → ℝ) (volume : Measure ℝ) := by
        congr 1
        funext t
        simp [f]
      _ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • volume := hmap
      _ = volume := by rw [hfdet]; norm_num
  have hneg : MeasurePreserving (Homeomorph.neg ℝ)
      (volume : Measure ℝ) (volume : Measure ℝ) := by
    refine ⟨(Homeomorph.neg ℝ).measurable, ?_⟩
    simp [hnegMap]
  have hprod : MeasurePreserving
      (Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.neg ℝ))
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact (MeasurePreserving.id (volume : Measure Vec3)).prod hneg
  have h₁ := hprod.comp parabolicHomeomorph_measurePreserving
  have h₂ := parabolicHomeomorphSymm_measurePreserving.comp h₁
  change MeasurePreserving
    (parabolicHomeomorph.symm ∘
      Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.neg ℝ) ∘
      parabolicHomeomorph) volume volume at h₂
  convert h₂ using 1
  funext z
  rfl

/-- Time reflection sends a positive interval to the corresponding past interval. -/
theorem essLocalTimeReflection_image
    (Ω : Set Vec3) (T : ℝ) :
    essLocalTimeReflection ''
      spaceTimeSet Ω (Ioo (0 : ℝ) T) =
      spaceTimeSet Ω (Ioo (-T) 0) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨y, hy, hzy⟩
    change (y.1, -y.2) = (x, t) at hzy
    have hfst : y.1 = x := congrArg Prod.fst hzy
    have hsnd : -y.2 = t := congrArg Prod.snd hzy
    change y.1 ∈ Ω ∧ 0 < y.2 ∧ y.2 < T at hy
    subst x
    subst t
    rcases hy with ⟨hyx, hyl, hyu⟩
    refine ⟨hyx, ?_⟩
    constructor
    · linarith only [hyu]
    · linarith only [hyl]
  · rintro ⟨hxt, htime⟩
    refine ⟨(x, -t), ?_, ?_⟩
    · change x ∈ Ω ∧ 0 < -t ∧ -t < T
      exact ⟨hxt, by
        constructor
        · linarith only [htime.2]
        · linarith only [htime.1]⟩
    · change (x, -(-t)) = (x, t)
      simp

private theorem essLocalTimeReflection_preimage
    (Ω : Set Vec3) (T : ℝ) :
    essLocalTimeReflection ⁻¹' spaceTimeSet Ω (Ioo (-T) 0) =
      spaceTimeSet Ω (Ioo (0 : ℝ) T) := by
  rw [← essLocalTimeReflection_image Ω T]
  exact (essLocalTimeReflection).preimage_image _

private theorem essLocal_timeReflection_spatialPartial
    {ψ : Vec3 × ℝ → ℝ} (i : Fin 3) (x : Vec3) (t : ℝ) :
    spatialPartial (fun z : Vec3 × ℝ => ψ (z.1, -z.2)) i (x, -t) =
      spatialPartial (fun z : Vec3 × ℝ => ψ z) i (x, t) := by
  simp [spatialPartial]

private theorem essLocal_timeReflection_timePartial
    {ψ : Vec3 × ℝ → ℝ} (x : Vec3) (t : ℝ) :
    timePartial (fun z : Vec3 × ℝ => ψ (z.1, -z.2)) (x, -t) =
      -timePartial (fun z : Vec3 × ℝ => ψ z) (x, t) := by
  change deriv (fun s : ℝ => ψ (x, -s)) (-t) =
    -deriv (fun s : ℝ => ψ (x, s)) t
  have h := deriv_comp_neg (f := fun s : ℝ => ψ (x, s)) (-t)
  simpa only [neg_neg] using h

/-- Space-time weak derivatives restrict to a smaller open spatial and time domain. -/
theorem essLocal_weakDerivs_restrict
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hΩ : Ω' ⊆ Ω) (hJ : J ⊆ I)
    (hQmeas : MeasurableSet (spaceTimeSet Ω I))
    (hweak : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs Ω' J w Dw D2w Dtw := by
  let Q := spaceTimeSet Ω I
  let Q' := spaceTimeSet Ω' J
  have hQsub : Q' ⊆ Q := by
    rintro z ⟨hx, ht⟩
    exact ⟨hΩ hx, hJ ht⟩
  rcases hweak with ⟨hwloc, hDwloc, hD2loc, hDtloc, hident⟩
  refine ⟨hwloc.mono_set hQsub, hDwloc.mono_set hQsub,
    hD2loc.mono_set hQsub, hDtloc.mono_set hQsub, ?_⟩
  intro ψ hψ
  have hψbig : ψ ∈ spaceTimeTestFunction Ω I :=
    ⟨hψ.1, hψ.2.1, hψ.2.2.trans hQsub⟩
  have hts : tsupport (show ParabolicPoint → ℝ from ψ) =
      tsupport (show Vec3 × ℝ → ℝ from ψ) :=
    CKN.tsupport_parabolic_eq (show Vec3 × ℝ → ℝ from ψ)
  have hψsupport : tsupport (show ParabolicPoint → ℝ from ψ) ⊆ Q' :=
    CKN.tsupport_parabolic_subset_spaceTimeSet hψ
  have hψzero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) : ψ z = 0 := by
    have hzprod : z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
      rw [← hts]
      exact hz
    change ψ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → ℝ from ψ) hzprod
  have hspzero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) (j : Fin 3) :
      spatialPartial ψ j z = 0 := by
    have hzprod : z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
      rw [← hts]
      exact hz
    exact spatialPartial_eq_zero_off_tsupport
      (ψ := show Vec3 × ℝ → ℝ from ψ) hzprod j
  have htimezero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
      timePartial ψ z = 0 := by
    have hzprod : z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
      rw [← hts]
      exact hz
    exact timePartial_eq_zero_off_tsupport
      (ψ := show Vec3 × ℝ → ℝ from ψ) hzprod
  have hnotSupport (z : ParabolicPoint) (hz : z ∉ Q') :
      z ∉ tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro hzsupport
    exact hz (hψsupport hzsupport)
  have hrestrict (F : ParabolicPoint → ℝ)
      (hF : ∀ z, z ∉ Q' → F z = 0) :
      (∫ z in Q, F z) = ∫ z in Q', F z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQmeas hQsub
    intro z hz
    exact hF z hz.2
  have ⟨hfirst, hsecond, htime⟩ := hident ψ hψbig
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    calc
      (∫ z in Q', w z i * spatialPartial ψ j z) =
          ∫ z in Q, w z i * spatialPartial ψ j z :=
        (hrestrict _ (fun z hz => by
          simp [hspzero z (hnotSupport z hz) j])).symm
      _ = -∫ z in Q, Dw z i j * ψ z := hfirst i j
      _ = -∫ z in Q', Dw z i j * ψ z := by
        rw [hrestrict _ (fun z hz => by
          simp [hψzero z (hnotSupport z hz)])]
  · intro i j k
    calc
      (∫ z in Q', Dw z i j * spatialPartial ψ k z) =
          ∫ z in Q, Dw z i j * spatialPartial ψ k z :=
        (hrestrict _ (fun z hz => by
          simp [hspzero z (hnotSupport z hz) k])).symm
      _ = -∫ z in Q, D2w z i j k * ψ z := hsecond i j k
      _ = -∫ z in Q', D2w z i j k * ψ z := by
        rw [hrestrict _ (fun z hz => by
          simp [hψzero z (hnotSupport z hz)])]
  · intro i
    calc
      (∫ z in Q', w z i * timePartial ψ z) =
          ∫ z in Q, w z i * timePartial ψ z :=
        (hrestrict _ (fun z hz => by
          simp [htimezero z (hnotSupport z hz)])).symm
      _ = -∫ z in Q, Dtw z i * ψ z := htime i
      _ = -∫ z in Q', Dtw z i * ψ z := by
        rw [hrestrict _ (fun z hz => by
          simp [hψzero z (hnotSupport z hz)])]

/-- Space-time weak derivatives transport under spatial translation. -/
theorem essLocal_spatialTranslate_weakDerivs
    {Ω : Set Vec3} {I : Set ℝ}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (c : Vec3) (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hweak : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs {y : Vec3 | c + y ∈ Ω} I
      (fun z => w (essLocalSpatialTranslate c z))
      (fun z i j => Dw (essLocalSpatialTranslate c z) i j)
      (fun z i j k => D2w (essLocalSpatialTranslate c z) i j k)
      (fun z i => Dtw (essLocalSpatialTranslate c z) i) := by
  let e := essLocalSpatialTranslate c
  let Ω' : Set Vec3 := {y : Vec3 | c + y ∈ Ω}
  let Qtarget := spaceTimeSet Ω' I
  let Qsource := spaceTimeSet Ω I
  have he : ∀ z, e z = (c + z.1, z.2) := essLocalSpatialTranslate_apply c
  have hΩ' : IsOpen Ω' := hΩ.preimage (continuous_const.add continuous_id)
  have hQtarget : IsOpen Qtarget := isOpen_spaceTimeSet Ω' I hΩ' hI
  have hQsource : IsOpen Qsource := isOpen_spaceTimeSet Ω I hΩ hI
  have himage : e '' Qtarget = Qsource := by
    ext z
    rcases z with ⟨x, t⟩
    constructor
    · rintro ⟨y, hy, hzy⟩
      change (c + y.1, y.2) = (x, t) at hzy
      have hfst : c + y.1 = x := congrArg Prod.fst hzy
      have hsnd : y.2 = t := congrArg Prod.snd hzy
      change c + y.1 ∈ Ω ∧ y.2 ∈ I at hy
      subst x
      subst t
      exact hy
    · rintro ⟨hx, ht⟩
      refine ⟨(x - c, t), ?_, ?_⟩
      · change c + (x - c) ∈ Ω ∧ t ∈ I
        rw [add_sub_cancel]
        exact ⟨hx, ht⟩
      · change (c + (x - c), t) = (x, t)
        rw [add_sub_cancel]
  have hmp : MeasurePreserving e (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint) := essLocalSpatialTranslate_measurePreserving c
  have hWloc : LocallyIntegrableOn (fun z => w (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.1
  have hDwloc : LocallyIntegrableOn (fun z => Dw (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.2.1
  have hD2loc : LocallyIntegrableOn (fun z => D2w (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.2.2.1
  have hDtloc : LocallyIntegrableOn (fun z => Dtw (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.2.2.2.1
  refine ⟨hWloc, hDwloc, hD2loc, hDtloc, ?_⟩
  intro (ψ : Vec3 × ℝ → ℝ) hψ
  let φ : Vec3 × ℝ → ℝ := fun z => ψ (z.1 - c, z.2)
  have hφ : φ ∈ spaceTimeTestFunction Ω I := by
    rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
    change tsupport ψ ⊆ Ω' ×ˢ I at hψsupport
    refine ⟨?_, hψcompact.comp_homeomorph
      (Homeomorph.prodCongr (Homeomorph.subRight c) (Homeomorph.refl ℝ)), ?_⟩
    · exact hψdiff.comp (by fun_prop)
    · change tsupport (ψ ∘
        Homeomorph.prodCongr (Homeomorph.subRight c) (Homeomorph.refl ℝ)) ⊆ Ω ×ˢ I
      rw [tsupport_comp_eq_preimage ψ
        (Homeomorph.prodCongr (Homeomorph.subRight c) (Homeomorph.refl ℝ))]
      intro z hz
      have hz' := hψsupport hz
      change z.1 - c ∈ Ω' ∧ z.2 ∈ I at hz'
      change z.1 ∈ Ω ∧ z.2 ∈ I
      exact ⟨by simpa [Ω'] using hz'.1, hz'.2⟩
  have hchange (F : ParabolicPoint → ℝ) :
      (∫ z in Qsource, F z) = ∫ z in Qtarget, F (e z) := by
    have h := hmp.setIntegral_image_emb e.measurableEmbedding F Qtarget
    calc
      (∫ z in Qsource, F z) = ∫ z in e '' Qtarget, F z := by rw [himage]
      _ = ∫ z in Qtarget, F (e z) := by simpa [e] using h
  have hφsp (i : Fin 3) (z : ParabolicPoint) :
      spatialPartial (show ParabolicPoint → ℝ from φ) i (e z) =
        spatialPartial ψ i z := by
    change spatialDeriv (fun y : Vec3 => ψ (y - c, z.2)) i (c + z.1) =
      spatialDeriv (fun y : Vec3 => ψ (y, z.2)) i z.1
    simpa only [add_sub_cancel_left] using
      vorticitySpatialDeriv_translate (fun y => ψ (y, z.2)) c (c + z.1) i
  have hφval (z : ParabolicPoint) : φ (e z) = ψ z := by
    rw [he z]
    change ψ ((c + z.1) - c, z.2) = ψ (z.1, z.2)
    simp only [add_sub_cancel_left]
  have hφtime (z : ParabolicPoint) :
      timePartial (show ParabolicPoint → ℝ from φ) (e z) = timePartial ψ z := by
    rw [he z]
    change deriv (fun s : ℝ => ψ ((c + z.1) - c, s)) z.2 =
      deriv (fun s : ℝ => ψ (z.1, s)) z.2
    simp only [add_sub_cancel_left]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hsource := (hweak.2.2.2.2 φ hφ).1 i j
    rw [hchange, hchange] at hsource
    simpa only [hφsp j, hφval] using hsource
  · intro i j k
    have hsource := (hweak.2.2.2.2 φ hφ).2.1 i j k
    rw [hchange, hchange] at hsource
    simpa only [hφsp k, hφval] using hsource
  · intro i
    have hsource := (hweak.2.2.2.2 φ hφ).2.2 i
    rw [hchange, hchange] at hsource
    simpa only [hφtime, hφval] using hsource

/-- Space-time weak derivatives transport under time translation. -/
theorem essLocal_timeTranslate_weakDerivs
    {Ω : Set Vec3} {I : Set ℝ}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (d : ℝ) (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hweak : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs Ω {s : ℝ | s + d ∈ I}
      (fun z => w (essLocalTimeTranslate d z))
      (fun z i j => Dw (essLocalTimeTranslate d z) i j)
      (fun z i j k => D2w (essLocalTimeTranslate d z) i j k)
      (fun z i => Dtw (essLocalTimeTranslate d z) i) := by
  let e := essLocalTimeTranslate d
  let I' : Set ℝ := {s : ℝ | s + d ∈ I}
  let Qtarget := spaceTimeSet Ω I'
  let Qsource := spaceTimeSet Ω I
  have he : ∀ z, e z = (z.1, z.2 + d) := by
    intro z
    simpa only [add_comm] using essLocalTimeTranslate_apply d z
  have hI' : IsOpen I' := hI.preimage (continuous_id.add continuous_const)
  have hQtarget : IsOpen Qtarget := isOpen_spaceTimeSet Ω I' hΩ hI'
  have hQsource : IsOpen Qsource := isOpen_spaceTimeSet Ω I hΩ hI
  have himage : e '' Qtarget = Qsource := by
    ext z
    rcases z with ⟨x, t⟩
    constructor
    · rintro ⟨y, hy, hzy⟩
      change (y.1, d + y.2) = (x, t) at hzy
      have hfst : y.1 = x := congrArg Prod.fst hzy
      have hsnd : d + y.2 = t := congrArg Prod.snd hzy
      change y.1 ∈ Ω ∧ y.2 ∈ I' at hy
      change y.1 ∈ Ω ∧ y.2 + d ∈ I at hy
      subst x
      subst t
      change y.1 ∈ Ω ∧ d + y.2 ∈ I
      exact ⟨hy.1, by simpa only [add_comm] using hy.2⟩
    · rintro ⟨hx, ht⟩
      let y : ParabolicPoint := (x, t - d)
      refine ⟨y, ?_, ?_⟩
      · change x ∈ Ω ∧ (t - d) ∈ I'
        change x ∈ Ω ∧ (t - d) + d ∈ I
        have htime : (t - d) + d = t := by ring
        rw [htime]
        exact ⟨hx, ht⟩
      · rw [he y]
        congr 1
        ring
  have hmp : MeasurePreserving e (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint) := essLocalTimeTranslate_measurePreserving d
  have hWloc : LocallyIntegrableOn (fun z => w (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.1
  have hDwloc : LocallyIntegrableOn (fun z => Dw (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.2.1
  have hD2loc : LocallyIntegrableOn (fun z => D2w (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.2.2.1
  have hDtloc : LocallyIntegrableOn (fun z => Dtw (e z)) Qtarget :=
    essLocal_locallyIntegrableOn_homeomorph e hQtarget himage hmp hweak.2.2.2.1
  refine ⟨hWloc, hDwloc, hD2loc, hDtloc, ?_⟩
  intro (ψ : Vec3 × ℝ → ℝ) hψ
  let H : (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
    Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addLeft (-d))
  let φ : Vec3 × ℝ → ℝ := ψ ∘ H
  have hφ : φ ∈ spaceTimeTestFunction Ω I := by
    rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
    change tsupport ψ ⊆ Ω ×ˢ I' at hψsupport
    refine ⟨?_, hψcompact.comp_homeomorph H, ?_⟩
    · change ContDiff ℝ (⊤ : ℕ∞)
        (ψ ∘ fun z : Vec3 × ℝ => (z.1, -d + z.2))
      exact hψdiff.comp (by fun_prop)
    · change tsupport (ψ ∘ H) ⊆ Ω ×ˢ I
      rw [tsupport_comp_eq_preimage ψ H]
      intro z hz
      have hz' := hψsupport hz
      change (z.1, -d + z.2) ∈ Ω ×ˢ I' at hz'
      change z.1 ∈ Ω ∧ (-d + z.2) ∈ I' at hz'
      change z.1 ∈ Ω ∧ (-d + z.2) + d ∈ I at hz'
      change z.1 ∈ Ω ∧ z.2 ∈ I
      have htime : (-d + z.2) + d = z.2 := by abel
      rw [htime] at hz'
      exact ⟨hz'.1, hz'.2⟩
  have hchange (F : ParabolicPoint → ℝ) :
      (∫ z in Qsource, F z) = ∫ z in Qtarget, F (e z) := by
    have h := hmp.setIntegral_image_emb e.measurableEmbedding F Qtarget
    calc
      (∫ z in Qsource, F z) = ∫ z in e '' Qtarget, F z := by rw [himage]
      _ = ∫ z in Qtarget, F (e z) := by simpa [e] using h
  have hφsp (i : Fin 3) (z : ParabolicPoint) :
      spatialPartial (show ParabolicPoint → ℝ from φ) i (e z) =
        spatialPartial ψ i z := by
    rw [he z]
    change spatialDeriv (fun y : Vec3 => ψ (y, -d + (z.2 + d))) i z.1 =
      spatialDeriv (fun y : Vec3 => ψ (y, z.2)) i z.1
    have htime : -d + (z.2 + d) = z.2 := by abel
    rw [htime]
  have hφval (z : ParabolicPoint) : φ (e z) = ψ z := by
    rw [he z]
    change ψ (z.1, -d + (z.2 + d)) = ψ (z.1, z.2)
    congr 1
    abel_nf
  have hφtime (z : ParabolicPoint) :
      timePartial (show ParabolicPoint → ℝ from φ) (e z) = timePartial ψ z := by
    rw [he z]
    change deriv (fun s : ℝ => ψ (z.1, -d + s)) (z.2 + d) =
      deriv (fun s : ℝ => ψ (z.1, s)) z.2
    have h := deriv_comp_const_add (fun s : ℝ => ψ (z.1, s)) (-d) (z.2 + d)
    have hpoint : -d + (z.2 + d) = z.2 := by abel
    simpa only [hpoint] using h
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hsource := (hweak.2.2.2.2 φ hφ).1 i j
    rw [hchange, hchange] at hsource
    simpa only [hφsp j, hφval] using hsource
  · intro i j k
    have hsource := (hweak.2.2.2.2 φ hφ).2.1 i j k
    rw [hchange, hchange] at hsource
    simpa only [hφsp k, hφval] using hsource
  · intro i
    have hsource := (hweak.2.2.2.2 φ hφ).2.2 i
    rw [hchange, hchange] at hsource
    simpa only [hφtime, hφval] using hsource

private theorem essLocal_locallyIntegrableOn_reflection
    {Qplus Qminus : Set ParabolicPoint}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hQplus : IsOpen Qplus)
    (himage : essLocalTimeReflection '' Qplus = Qminus)
    {f : ParabolicPoint → E}
    (hf : LocallyIntegrableOn f Qminus volume) :
    LocallyIntegrableOn (fun z => f (essLocalTimeReflection z)) Qplus volume := by
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  rw [locallyIntegrableOn_iff hQplus.isLocallyClosed]
  intro K hKsub hKcompact
  have hsub : essLocalTimeReflection '' K ⊆ Qminus := by
    rw [← himage]
    exact image_mono hKsub
  have hsource := hf.integrableOn_compact_subset hsub
    (hKcompact.image essLocalTimeReflection.continuous)
  exact (essLocalTimeReflection_measurePreserving.integrableOn_image
    essLocalTimeReflection.measurableEmbedding).mp hsource

/-- Distributional spatial and time derivatives transport across reflection
of the terminal face. -/
theorem essLocal_timeReflection_weakDerivs
    {Ω : Set Vec3}
    {T : ℝ}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hΩ : IsOpen Ω)
    (hweak : HasSpaceTimeWeakDerivs Ω (Ioo (-T) 0) w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs Ω (Ioo (0 : ℝ) T)
      (fun z => w (essLocalTimeReflection z))
      (fun z i j => Dw (essLocalTimeReflection z) i j)
      (fun z i j k => D2w (essLocalTimeReflection z) i j k)
      (fun z i => -Dtw (essLocalTimeReflection z) i) := by
  let e := essLocalTimeReflection
  let Qpos := spaceTimeSet Ω (Ioo (0 : ℝ) T)
  let Qneg := spaceTimeSet Ω (Ioo (-T) 0)
  have he : ∀ z, e z = (z.1, -z.2) := essLocalTimeReflection_apply
  have hQpos : IsOpen Qpos :=
    isOpen_spaceTimeSet Ω (Ioo (0 : ℝ) T) hΩ isOpen_Ioo
  have hQneg : IsOpen Qneg :=
    isOpen_spaceTimeSet Ω (Ioo (-T) 0) hΩ isOpen_Ioo
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  have himage : e '' Qpos = Qneg := by
    simpa only [e, Qpos, Qneg] using essLocalTimeReflection_image Ω T
  have hWloc : LocallyIntegrableOn (fun z => w (e z)) Qpos volume :=
    essLocal_locallyIntegrableOn_reflection hQpos himage hweak.1
  have hDwloc : LocallyIntegrableOn
      (fun z => Dw (e z)) Qpos volume :=
    essLocal_locallyIntegrableOn_reflection hQpos himage hweak.2.1
  have hD2loc : LocallyIntegrableOn
      (fun z => D2w (e z)) Qpos volume :=
    essLocal_locallyIntegrableOn_reflection hQpos himage hweak.2.2.1
  have hDtloc : LocallyIntegrableOn
      (fun z => -Dtw (e z)) Qpos volume := by
    have hDtw : LocallyIntegrableOn (fun z => Dtw (e z)) Qpos volume :=
      essLocal_locallyIntegrableOn_reflection hQpos himage hweak.2.2.2.1
    exact hDtw.neg
  refine ⟨hWloc, hDwloc, hD2loc, hDtloc, ?_⟩
  intro (ψ : Vec3 × ℝ → ℝ) hψ
  let φ : Vec3 × ℝ → ℝ := fun z => ψ (z.1, -z.2)
  have hφ : φ ∈ spaceTimeTestFunction Ω (Ioo (-T) 0) := by
    rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
    change tsupport ψ ⊆ Ω ×ˢ Ioo (0 : ℝ) T at hψsupport
    refine ⟨?_, hψcompact.comp_homeomorph
      (Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.neg ℝ)), ?_⟩
    · exact hψdiff.comp (by fun_prop)
    · change tsupport (ψ ∘
        Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.neg ℝ)) ⊆
        Ω ×ˢ Ioo (-T) 0
      rw [tsupport_comp_eq_preimage ψ
        (Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.neg ℝ))]
      intro z hz
      have hz' := hψsupport hz
      change z.1 ∈ Ω ∧ -z.2 ∈ Ioo (0 : ℝ) T at hz'
      change z.1 ∈ Ω ∧ z.2 ∈ Ioo (-T) 0
      exact ⟨hz'.1, by
        rcases hz'.2 with ⟨hzlo, hzhi⟩
        exact ⟨by linarith only [hzhi], by linarith only [hzlo]⟩⟩
  have hchange (F : ParabolicPoint → ℝ) :
      (∫ z in Qneg, F z) = ∫ z in Qpos, F (e z) := by
    have h := essLocalTimeReflection_measurePreserving.setIntegral_image_emb
      e.measurableEmbedding F Qpos
    calc
      (∫ z in Qneg, F z) = ∫ z in e '' Qpos, F z := by rw [himage]
      _ = ∫ z in Qpos, F (e z) := by simpa [e] using h
  have hφsp (i : Fin 3) (z : ParabolicPoint) :
      spatialPartial (show ParabolicPoint → ℝ from φ) i (e z) =
        spatialPartial ψ i z := by
    rcases z with ⟨x, t⟩
    exact essLocal_timeReflection_spatialPartial i x t
  have hφval (z : ParabolicPoint) : φ (e z) = ψ z := by
    rcases z with ⟨x, t⟩
    change ψ ((e (x, t)).1, -(e (x, t)).2) = ψ (x, t)
    rw [he (x, t)]
    simp
  have hφtime (z : ParabolicPoint) :
      timePartial (show ParabolicPoint → ℝ from φ) (e z) =
        -timePartial ψ z := by
    rcases z with ⟨x, t⟩
    exact essLocal_timeReflection_timePartial x t
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hsource := (hweak.2.2.2.2 φ hφ).1 i j
    rw [hchange, hchange] at hsource
    simpa only [hφsp j, hφval] using hsource
  · intro i j k
    have hsource := (hweak.2.2.2.2 φ hφ).2.1 i j k
    rw [hchange, hchange] at hsource
    simpa only [hφsp k, hφval] using hsource
  · intro i
    have hsource := (hweak.2.2.2.2 φ hφ).2.2 i
    rw [hchange, hchange] at hsource
    have hsource' :
      -(∫ z in Qpos, w (e z) i * timePartial ψ z) =
          -(∫ z in Qpos, Dtw (e z) i * ψ z) := by
      simpa only [hφtime, hφval, mul_neg, ← integral_neg] using hsource
    have hEq := congrArg (fun x : ℝ => -x) hsource'
    have hEq' : (∫ z in Qpos, w (e z) i * timePartial ψ z) =
        ∫ z in Qpos, Dtw (e z) i * ψ z := by simpa using hEq
    simpa only [integral_neg, neg_mul, neg_neg] using hEq'

/-- Multiplying a field and each of its weak derivatives by the same real
constant preserves the space-time weak-derivative identities. -/
theorem essLocal_scale_weakDerivs
    {Ω : Set Vec3} {I : Set ℝ}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (a : ℝ) (hweak : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs Ω I (fun z => a • w z)
      (fun z i j => a * Dw z i j)
      (fun z i j k => a * D2w z i j k)
      (fun z i => a * Dtw z i) := by
  refine ⟨hweak.1.smul a, hweak.2.1.smul a,
    hweak.2.2.1.smul a, hweak.2.2.2.1.smul a, ?_⟩
  intro φ hφ
  obtain ⟨hfirst, hsecond, htime⟩ := hweak.2.2.2.2 φ hφ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    calc
      (∫ z in spaceTimeSet Ω I, (a * w z i) * spatialPartial φ j z) =
          a * ∫ z in spaceTimeSet Ω I, w z i * spatialPartial φ j z := by
        rw [show (fun z : ParabolicPoint => (a * w z i) * spatialPartial φ j z) =
            fun z => a * (w z i * spatialPartial φ j z) by
          funext z
          ring,
          integral_const_mul]
      _ = a * (-∫ z in spaceTimeSet Ω I, Dw z i j * φ z) :=
        congrArg (fun x : ℝ => a * x) (hfirst i j)
      _ = -∫ z in spaceTimeSet Ω I, (a * Dw z i j) * φ z := by
        rw [show (fun z : ParabolicPoint => (a * Dw z i j) * φ z) =
            fun z => a * (Dw z i j * φ z) by
          funext z
          ring,
          integral_const_mul]
        ring
  · intro i j k
    calc
      (∫ z in spaceTimeSet Ω I, (a * Dw z i j) * spatialPartial φ k z) =
          a * ∫ z in spaceTimeSet Ω I, Dw z i j * spatialPartial φ k z := by
        rw [show (fun z : ParabolicPoint => (a * Dw z i j) * spatialPartial φ k z) =
            fun z => a * (Dw z i j * spatialPartial φ k z) by
          funext z
          ring,
          integral_const_mul]
      _ = a * (-∫ z in spaceTimeSet Ω I, D2w z i j k * φ z) :=
        congrArg (fun x : ℝ => a * x) (hsecond i j k)
      _ = -∫ z in spaceTimeSet Ω I, (a * D2w z i j k) * φ z := by
        rw [show (fun z : ParabolicPoint => (a * D2w z i j k) * φ z) =
            fun z => a * (D2w z i j k * φ z) by
          funext z
          ring,
          integral_const_mul]
        ring
  · intro i
    calc
      (∫ z in spaceTimeSet Ω I, (a * w z i) * timePartial φ z) =
          a * ∫ z in spaceTimeSet Ω I, w z i * timePartial φ z := by
        rw [show (fun z : ParabolicPoint => (a * w z i) * timePartial φ z) =
            fun z => a * (w z i * timePartial φ z) by
          funext z
          ring,
          integral_const_mul]
      _ = a * (-∫ z in spaceTimeSet Ω I, Dtw z i * φ z) :=
        congrArg (fun x : ℝ => a * x) (htime i)
      _ = -∫ z in spaceTimeSet Ω I, (a * Dtw z i) * φ z := by
        rw [show (fun z : ParabolicPoint => (a * Dtw z i) * φ z) =
            fun z => a * (Dtw z i * φ z) by
          funext z
          ring,
          integral_const_mul]
        ring

end ESS
