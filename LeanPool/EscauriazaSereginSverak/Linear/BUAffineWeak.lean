/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineTest
public import LeanPool.EscauriazaSereginSverak.Linear.BUWeakRestriction
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Weak derivatives in affine parabolic coordinates

Integration by parts transfers through the affine coordinates used in
`lem:bu-iterate`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The affine map as a homeomorphism of parabolic space-time. -/
@[expose] def buAffineParabolicHomeomorph (τ scale : ℝ) (hscale : 0 < scale) :
    ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans (buAffineHomeomorph τ scale hscale)).trans
    parabolicHomeomorph.symm

/-- The parabolic affine homeomorphism acts by the prescribed coordinate
formula. -/
theorem buAffineParabolicHomeomorph_eq
    (τ scale : ℝ) (hscale : 0 < scale) :
    ⇑(buAffineParabolicHomeomorph τ scale hscale) = buAffinePoint τ scale := by
  funext z
  change (buAffineHomeomorph τ scale hscale) (z.1, z.2) =
    (scale • z.1, τ + scale ^ 2 * z.2)
  exact congrFun (buAffineHomeomorph_eq τ scale hscale) _

/-- Local integrability transfers through the affine homeomorphism of a
positive half-space time slab. -/
theorem bu_affine_locallyIntegrableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ scale : ℝ) (hscale : 0 < scale)
    (f : ParabolicPoint → E)
    (hf : LocallyIntegrableOn f
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2))) volume) :
    LocallyIntegrableOn (f ∘ buAffinePoint τ scale)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)) volume := by
  let e := buAffineParabolicHomeomorph τ scale hscale
  let Q := spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)
  let S := spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2))
  have hQopen : IsOpen Q :=
    CKN.Foundation.Parabolic.isOpen_spaceTimeSet _ _
      (isOpen_lt continuous_const (continuous_apply 2)) isOpen_Ioo
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isOpenEmbedding.locallyCompactSpace
  apply (locallyIntegrableOn_iff hQopen.isLocallyClosed).2
  intro K hKsub hKcompact
  have himage : e '' K ⊆ S := by
    rintro z ⟨q, hq, rfl⟩
    rw [buAffineParabolicHomeomorph_eq]
    have hq' : q ∈ buAffinePoint τ scale ⁻¹' S := by
      rw [buAffinePoint_preimage_halfSlab τ scale hscale]
      exact hKsub hq
    exact hq'
  have hsource : IntegrableOn f (e '' K) volume :=
    hf.integrableOn_compact_subset himage (hKcompact.image e.continuous)
  have hcoef : ENNReal.ofReal (scale⁻¹ ^ 5) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmul : IntegrableOn f (e '' K)
      (ENNReal.ofReal (scale⁻¹ ^ 5) • volume) :=
    by rw [IntegrableOn, Measure.restrict_smul]; exact hsource.smul_measure hcoef
  have hmap : Measure.map e volume =
      ENNReal.ofReal (scale⁻¹ ^ 5) • (volume : Measure ParabolicPoint) := by
    rw [buAffineParabolicHomeomorph_eq, buAffinePoint_eq_scalingParabolic]
    exact CKN.map_scalingParabolic scale hscale ((0 : Vec3), τ)
  have htrans : IntegrableOn f (e '' K) (Measure.map e volume) := by
    rw [hmap]
    exact hsmul
  have hcomp := (integrableOn_map_equiv e.toMeasurableEquiv).1 htrans
  have hpre : e ⁻¹' (e '' K) = K := e.preimage_image K
  rw [Homeomorph.toMeasurableEquiv_coe, hpre] at hcomp
  simpa only [e, Homeomorph.toMeasurableEquiv_coe,
    buAffineParabolicHomeomorph_eq] using hcomp

/-- A scalar integration-by-parts identity transfers through affine
parabolic coordinates when the test derivative has its chain-rule factor. -/
theorem bu_affine_weak_identity
    (τ scale c d : ℝ) (hscale : 0 < scale) (hd : d ≠ 0)
    (f g : ParabolicPoint → ℝ)
    (D : (ParabolicPoint → ℝ) → ParabolicPoint → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)))))
    (hDcont : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) →
      Continuous (D φ))
    (hDpull : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      ∀ z : ParabolicPoint,
        D (show ParabolicPoint → ℝ from
          ψ ∘ (buAffineHomeomorph τ scale hscale).symm)
          (buAffinePoint τ scale z) = d⁻¹ * D ψ z)
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) →
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)), f z * D φ z) =
        -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo τ (τ + scale ^ 2)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo 0 1)) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      (c * f (buAffinePoint τ scale z)) * D ψ z) =
      -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        (c * d * g (buAffinePoint τ scale z)) * ψ z := by
  let ψhat : Vec3 × ℝ → ℝ :=
    ψ ∘ (buAffineHomeomorph τ scale hscale).symm
  have hψhat : ψhat ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) :=
    bu_affine_pullback_test τ scale hscale hψ
  have hS := hsource ψhat hψhat
  let Q := spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2))
  let A := fun z : ParabolicPoint => f z * D ψhat z
  let B := fun z : ParabolicPoint => g z * ψhat z
  have hhatC : Continuous (fun z : ParabolicPoint => ψhat z) := by
    have hc := hψhat.1.continuous.comp parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  have hAm : AEStronglyMeasurable A (volume.restrict Q) :=
    hf.mul (hDcont ψhat hψhat).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B (volume.restrict Q) :=
    hg.mul hhatC.aestronglyMeasurable
  have hAchange := bu_affine_integral_comp τ scale hscale A hAm
  have hBchange := bu_affine_integral_comp τ scale hscale B hBm
  have hhat_at (z : ParabolicPoint) :
      ψhat (buAffinePoint τ scale z) = ψ z := by
    change ψ ((buAffineHomeomorph τ scale hscale).symm
      (buAffinePoint τ scale z)) = ψ z
    have hp : buAffinePoint τ scale z =
        (buAffineHomeomorph τ scale hscale) (show Vec3 × ℝ from z) := by
      exact congrFun (buAffineHomeomorph_eq τ scale hscale).symm z
    rw [hp]
    exact congrArg ψ ((buAffineHomeomorph τ scale hscale).symm_apply_apply _)
  have hderiv' (z : ParabolicPoint) :
      D ψ z = d * D ψhat (buAffinePoint τ scale z) := by
    have hp := hDpull ψ hψ z
    change D ψhat (buAffinePoint τ scale z) = d⁻¹ * D ψ z at hp
    rw [hp]
    field_simp
  have hAint :
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        (c * f (buAffinePoint τ scale z)) * D ψ z) =
      c * d * (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        A (buAffinePoint τ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [A]
    rw [hderiv']
    ring
  have hBint :
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        (c * d * g (buAffinePoint τ scale z)) * ψ z) =
      c * d * (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        B (buAffinePoint τ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [B]
    rw [hhat_at]
    ring
  calc
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        (c * f (buAffinePoint τ scale z)) * D ψ z) =
      c * d * (scale⁻¹ ^ 5 * ∫ z in Q, A z) := by
        rw [hAint, hAchange]
    _ = -(c * d * (scale⁻¹ ^ 5 * ∫ z in Q, B z)) := by
      rw [hS]
      ring
    _ = -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        (c * d * g (buAffinePoint τ scale z)) * ψ z := by
      rw [hBint, hBchange]

/-- The scalar spatial weak derivative identity transfers with one power of
the affine spatial scale. -/
theorem bu_affine_spatial_weak_identity
    (τ scale c : ℝ) (hscale : 0 < scale)
    (f g : ParabolicPoint → ℝ) (j : Fin 3)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)))))
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) →
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)), f z * spatialPartial φ j z) =
        -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo τ (τ + scale ^ 2)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo 0 1)) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      (c * f (buAffinePoint τ scale z)) * spatialPartial ψ j z) =
      -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        (c * scale * g (buAffinePoint τ scale z)) * ψ z := by
  apply bu_affine_weak_identity τ scale c scale hscale hscale.ne'
    f g (fun φ z => spatialPartial φ j z) hf hg
  · intro φ hφ
    have hc := (spatialPartial_contDiff hφ.1 j).continuous.comp
      parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  · intro ψ hψ z
    rw [buAffineHomeomorph_symm_eq τ scale hscale]
    have hp := CKN.spatialPartial_pullback scale hscale
      ((0 : Vec3), τ) hψ.1 j z
    rw [← buAffinePoint_eq_scalingParabolic] at hp
    have heq : (show ParabolicPoint → ℝ from
        ψ ∘ fun q : Vec3 × ℝ =>
          (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ))) =
        ψ ∘ fun q : ParabolicPoint =>
          (scale⁻¹ • (q.1 - (0 : Vec3)),
            (scale ^ 2)⁻¹ * (q.2 - τ)) := by
      funext q
      change ψ (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ)) =
        ψ (scale⁻¹ • (q.1 - (0 : Vec3)), (scale ^ 2)⁻¹ * (q.2 - τ))
      simp only [sub_zero]
    rw [heq]
    exact hp
  · exact hsource
  · exact hψ

/-- The scalar weak time derivative identity transfers with two powers of
the affine spatial scale. -/
theorem bu_affine_time_weak_identity
    (τ scale c : ℝ) (hscale : 0 < scale)
    (f g : ParabolicPoint → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)))))
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) →
      (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2)), f z * timePartial φ z) =
        -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo τ (τ + scale ^ 2)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo 0 1)) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      (c * f (buAffinePoint τ scale z)) * timePartial ψ z) =
      -∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        (c * scale ^ 2 * g (buAffinePoint τ scale z)) * ψ z := by
  apply bu_affine_weak_identity τ scale c (scale ^ 2) hscale
    (sq_pos_of_pos hscale).ne' f g (fun φ z => timePartial φ z) hf hg
  · intro φ hφ
    have hc := (contDiff_timePartial hφ.1).continuous.comp
      parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  · intro ψ hψ z
    rw [buAffineHomeomorph_symm_eq τ scale hscale]
    have hp := CKN.timePartial_pullback scale hscale
      ((0 : Vec3), τ) hψ.1 z
    rw [← buAffinePoint_eq_scalingParabolic] at hp
    have heq : (show ParabolicPoint → ℝ from
        ψ ∘ fun q : Vec3 × ℝ =>
          (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ))) =
        ψ ∘ fun q : ParabolicPoint =>
          (scale⁻¹ • (q.1 - (0 : Vec3)),
            (scale ^ 2)⁻¹ * (q.2 - τ)) := by
      funext q
      change ψ (scale⁻¹ • q.1, (scale ^ 2)⁻¹ * (q.2 - τ)) =
        ψ (scale⁻¹ • (q.1 - (0 : Vec3)), (scale ^ 2)⁻¹ * (q.2 - τ))
      simp only [sub_zero]
    rw [heq]
    exact hp
  · exact hsource
  · exact hψ

/-- Weak spatial and time derivatives transfer to the normalized half-space
cylinder under an affine parabolic change of variables. -/
theorem bu_affine_weak_derivatives
    (τ scale : ℝ) (hτ : 0 ≤ τ) (hscale : 0 < scale)
    (hupper : τ + scale ^ 2 ≤ 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      (buAffineField τ scale w) (buAffineDw τ scale Dw)
      (buAffineD2w τ scale D2w) (buAffineDtw τ scale Dtw) := by
  let S := spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2))
  have hI : Ioo τ (τ + scale ^ 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_le_of_lt hτ ht.1, ht.2.trans_le hupper⟩
  have hweakS := bu_weak_restrict_time hI w Dw D2w Dtw hweak
  have hwloc : LocallyIntegrableOn (buAffineField τ scale w)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)) volume := by
    change LocallyIntegrableOn (w ∘ buAffinePoint τ scale) _ volume
    exact bu_affine_locallyIntegrableOn τ scale hscale w hweakS.1
  have hDwloc : LocallyIntegrableOn (buAffineDw τ scale Dw)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)) volume := by
    change LocallyIntegrableOn
      (scale • (Dw ∘ buAffinePoint τ scale)) _ volume
    exact (bu_affine_locallyIntegrableOn τ scale hscale Dw hweakS.2.1).smul scale
  have hD2loc : LocallyIntegrableOn (buAffineD2w τ scale D2w)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)) volume := by
    change LocallyIntegrableOn
      (scale ^ 2 • (D2w ∘ buAffinePoint τ scale)) _ volume
    exact (bu_affine_locallyIntegrableOn τ scale hscale D2w hweakS.2.2.1).smul
      (scale ^ 2)
  have hDtloc : LocallyIntegrableOn (buAffineDtw τ scale Dtw)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)) volume := by
    change LocallyIntegrableOn
      (scale ^ 2 • (Dtw ∘ buAffinePoint τ scale)) _ volume
    exact (bu_affine_locallyIntegrableOn τ scale hscale Dtw hweakS.2.2.2.1).smul
      (scale ^ 2)
  have hwm_i (i : Fin 3) : AEStronglyMeasurable (fun z => w z i)
      (volume.restrict S) :=
    (continuous_apply i).comp_aestronglyMeasurable
      hweakS.1.aestronglyMeasurable
  have hDwm_ij (i j : Fin 3) : AEStronglyMeasurable (fun z => Dw z i j)
      (volume.restrict S) :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable
        hweakS.2.1.aestronglyMeasurable)
  have hD2m_ijk (i j k : Fin 3) : AEStronglyMeasurable
      (fun z => D2w z i j k) (volume.restrict S) :=
    (continuous_apply k).comp_aestronglyMeasurable
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply i).comp_aestronglyMeasurable
          hweakS.2.2.1.aestronglyMeasurable))
  have hDtm_i (i : Fin 3) : AEStronglyMeasurable (fun z => Dtw z i)
      (volume.restrict S) :=
    (continuous_apply i).comp_aestronglyMeasurable
      hweakS.2.2.2.1.aestronglyMeasurable
  refine ⟨hwloc, hDwloc, hD2loc, hDtloc, ?_⟩
  intro ψ hψ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h := bu_affine_spatial_weak_identity τ scale 1 hscale
      (fun z => w z i) (fun z => Dw z i j) j
      (hwm_i i) (hDwm_ij i j)
      (fun φ hφ => (hweakS.2.2.2.2 φ hφ).1 i j) ψ hψ
    simpa only [buAffineField, buAffineDw, one_mul] using h
  · intro i j k
    have h := bu_affine_spatial_weak_identity τ scale scale hscale
      (fun z => Dw z i j) (fun z => D2w z i j k) k
      (hDwm_ij i j) (hD2m_ijk i j k)
      (fun φ hφ => (hweakS.2.2.2.2 φ hφ).2.1 i j k) ψ hψ
    simpa only [buAffineDw, buAffineD2w, pow_two, mul_assoc] using h
  · intro i
    have h := bu_affine_time_weak_identity τ scale 1 hscale
      (fun z => w z i) (fun z => Dtw z i)
      (hwm_i i) (hDtm_i i)
      (fun φ hφ => (hweakS.2.2.2.2 φ hφ).2.2 i) ψ hψ
    simpa only [buAffineField, buAffineDtw, one_mul] using h

end ESS
