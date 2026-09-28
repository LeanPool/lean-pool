/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development005
public import LeanPool.MovingSofa.Cap.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development005
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Gerver.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Gerver.CapIdentification`.
* `Gerver.Niche.Identification`.
* `Gerver.SurfaceDensity`.
* `Gerver.VelocityAndCapArea`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Cap Identification
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem gerver_cap_fiber_has_sofa_point
    (hKcomp : IsCompact gerverOuterCap) :
    ∀ q ∈ gerverOuterCap,
     ∃ p ∈ gerverLiteralSofa, p 0 = q 0 ∧ q 1 ≤ p 1 := by
  intro q hq
  have hFcomp : IsCompact (gerverOuterCap ∩ {z : Point |
      inner ℝ z (normalVector ((0 : ℝ) : Real.Angle)) =
        inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))}) :=
    hKcomp.inter_right (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
  obtain ⟨p, hpF, hpmax⟩ := hFcomp.exists_isMaxOn ⟨q, hq, rfl⟩
    (f := fun z : Point => inner ℝ z (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    (continuous_id.inner continuous_const).continuousOn
  have hpx : p 0 = q 0 := by
    have h : inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) =
      inner ℝ q (normalVector ((0 : ℝ) : Real.Angle)) := hpF.2
    rwa [inner_normalVector_zero, inner_normalVector_zero] at h
  have hpy : q 1 ≤ p 1 := by
    have h : inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hpmax ⟨hq, rfl⟩
    rwa [inner_normalVector_pi_div_two, inner_normalVector_pi_div_two] at h
  have hnofill : ∀ (f : ℝ → Point) (I : Set ℝ), (∀ t ∈ I, f t ∈ gerverOuterCap) →
      p ∉ strictVerticalFill f I := by
    rintro f I hf ⟨t, ht, h0, -, h2⟩
    have hmem : f t ∈ gerverOuterCap ∩ {z : Point |
        inner ℝ z (normalVector ((0 : ℝ) : Real.Angle)) =
          inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))} := by
      refine ⟨hf t ht, ?_⟩
      change inner ℝ (f t) (normalVector ((0 : ℝ) : Real.Angle)) =
        inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))
      rw [inner_normalVector_zero, inner_normalVector_zero, ← h0, hpx]
    have hle : inner ℝ (f t) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hpmax hmem
    rw [inner_normalVector_pi_div_two, inner_normalVector_pi_div_two] at hle
    linarith
  obtain ⟨hroofD, hroofx, hroofB⟩ := gerver_niche_roof_membership
  refine ⟨p, ⟨hpF.1, ?_⟩, hpx, hpy⟩
  rw [gerver_niche_vertical_fills]
  rintro ((h | h) | h)
  · exact hnofill _ _ hroofD h
  · exact hnofill _ _ hroofx h
  · exact hnofill _ _ hroofB h

private theorem gerver_cap_contact_faces (Kb : ConvexBody Point)
    (hKset : (Kb : Set Point) = gerverOuterCap)
    (hKcap : IsCap (Real.pi / 2) Kb)
    (hC1 : ContDiff ℝ 1 (GerverSofa.Romik.path GerverSofa.PartB.params))
    (hAn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1)
    (hAt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (tangentVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
       (paperGerverVelocityComponents t).1)
    (hCn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (normalVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) -
       (paperGerverVelocityComponents t).2)
    (hCt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1)
    (hsupK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
     supportValue gerverOuterCap (t : Real.Angle) =
       inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
     supportValue gerverOuterCap ((Real.pi / 2 + t : ℝ) : Real.Angle) =
       inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1)
    (hTpos : (0 : ℝ) < Real.pi / 2) :
    ∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
     (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
       exposedEdge K.val (t : Real.Angle) = {paperGerverContacts t 0} ∧
       exposedEdge K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2}) ∧
     paperGerverContacts 0 0 = (edgeVertices K.val (0 : Real.Angle)).1 ∧
     paperGerverContacts (Real.pi / 2) 0 =
       (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 ∧
     paperGerverContacts 0 2 = (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 ∧
     paperGerverContacts (Real.pi / 2) 2 = (edgeVertices K.val (Real.pi : Real.Angle)).2 := by
  -- a plane point is determined by its two frame coordinates
  have hpteq : ∀ (a : Real.Angle) (p q : Point),
      inner ℝ p (normalVector a) = inner ℝ q (normalVector a) →
      inner ℝ p (tangentVector a) = inner ℝ q (tangentVector a) → p = q := by
    intro a p q h1 h2
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p a,
      ← inner_normalVector_smul_add_inner_tangentVector_smul q a, h1, h2]
  have hdx : ∀ t : ℝ, HasDerivAt paperGerverPath (deriv paperGerverPath t) t := fun t => by
    rw [deriv_paperGerverPath hC1 t]
    exact hasDerivAt_paperGerverPath hC1 t
  -- exposed faces of the certified body, read in the cap's own description
  have hexp : ∀ (a : Real.Angle) (z : Point), z ∈ exposedEdge Kb a ↔
      (z ∈ gerverOuterCap ∧
        inner ℝ z (normalVector a) = supportValue gerverOuterCap a) := by
    intro a z
    constructor
    · intro h
      refine ⟨hKset ▸ h.1, ?_⟩
      have h2 : inner ℝ z (normalVector a) = supportValue (Kb : Set Point) a := h.2
      rwa [hKset] at h2
    · intro h
      refine ⟨hKset ▸ h.1, ?_⟩
      change inner ℝ z (normalVector a) = supportValue (Kb : Set Point) a
      rw [hKset]
      exact h.2
  have hsingleV : ∀ (a : Real.Angle) (p : Point), exposedEdge Kb a = {p} →
      (edgeVertices Kb a).1 = p ∧ (edgeVertices Kb a).2 = p := fun a p h =>
    ⟨Set.mem_singleton_iff.1 (h ▸ edgeVertices_fst_mem Kb a),
      Set.mem_singleton_iff.1 (h ▸ edgeVertices_snd_mem Kb a)⟩
  -- interior uniqueness in the normal family
  have hnormaledge : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ z ∈ gerverOuterCap,
      inner ℝ z (normalVector (t : Real.Angle)) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 →
      z = paperGerverContacts t 0 := by
    intro t ht z hz heq
    have hgd : HasDerivAt (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
          inner ℝ z (normalVector (s : Real.Angle)))
        ((inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
          (paperGerverVelocityComponents t).1) -
          inner ℝ z (tangentVector (t : Real.Angle))) t :=
      (((hdx t).inner ℝ (hasDerivAt_normalVector t)).add_const 1).sub
        (hasDerivAt_inner_normalVector z t)
    have hgmin : IsLocalMin (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
          inner ℝ z (normalVector (s : Real.Angle))) t := by
      refine IsMinOn.isLocalMin ?_ (Icc_mem_nhds ht.1 ht.2)
      intro s hs
      have h := (hz.2 s hs).1
      change (inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1) -
          inner ℝ z (normalVector (t : Real.Angle)) ≤
        (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
          inner ℝ z (normalVector (s : Real.Angle))
      linarith
    have hzero := hgmin.hasDerivAt_eq_zero hgd
    refine hpteq (t : Real.Angle) z (paperGerverContacts t 0) ?_ ?_
    · rw [hAn t]; exact heq
    · rw [hAt t]; linarith
  -- interior uniqueness in the tangent family
  have htangentedge : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ z ∈ gerverOuterCap,
      inner ℝ z (tangentVector (t : Real.Angle)) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 →
      z = paperGerverContacts t 2 := by
    intro t ht z hz heq
    have hzt : HasDerivAt (fun s : ℝ => inner ℝ z (tangentVector (s : Real.Angle)))
        (-inner ℝ z (normalVector (t : Real.Angle))) t := by
      simpa using (hasDerivAt_const t z).inner ℝ (hasDerivAt_tangentVector t)
    have hgd : HasDerivAt (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (s : Real.Angle)))
        ((inner ℝ (paperGerverPath t) (-normalVector (t : Real.Angle)) +
          (paperGerverVelocityComponents t).2) -
          -inner ℝ z (normalVector (t : Real.Angle))) t :=
      (((hdx t).inner ℝ (hasDerivAt_tangentVector t)).add_const 1).sub hzt
    have hgmin : IsLocalMin (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (s : Real.Angle))) t := by
      refine IsMinOn.isLocalMin ?_ (Icc_mem_nhds ht.1 ht.2)
      intro s hs
      have h := (hz.2 s hs).2
      change (inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (t : Real.Angle)) ≤
        (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (s : Real.Angle))
      linarith
    have hzero := hgmin.hasDerivAt_eq_zero hgd
    rw [inner_neg_right] at hzero
    refine hpteq (t : Real.Angle) z (paperGerverContacts t 2) ?_ ?_
    · rw [hCn t]; linarith
    · rw [hCt t]; exact heq
  -- the interior exposed faces are the two contact singletons
  have hedgeA : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      exposedEdge Kb (t : Real.Angle) = {paperGerverContacts t 0} := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self ht
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨(hexp _ _).2 ⟨gerver_outer_contact_A t htI, ?_⟩, fun z hz => ?_⟩
    · rw [hAn t, (hsupK t htI).1]
    · rw [hexp] at hz
      exact hnormaledge t ht z hz.1 (by rw [hz.2, (hsupK t htI).1])
  have hedgeC : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      exposedEdge Kb ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2} := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self ht
    have hang : ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        ((Real.pi / 2 + t : ℝ) : Real.Angle) := by rw [add_comm]
    have hsv : supportValue gerverOuterCap ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
      rw [hang]; exact (hsupK t htI).2
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨(hexp _ _).2 ⟨gerver_outer_contact_C t htI, ?_⟩, fun z hz => ?_⟩
    · rw [normalVector_add_pi_div_two_real, hCt t, hsv]
    · rw [hexp] at hz
      refine htangentedge t ht z hz.1 ?_
      have h := hz.2
      rwa [normalVector_add_pi_div_two_real, hsv] at h
  -- the four contact curves are continuous
  have hcontacts : Continuous paperGerverContacts := paperGerverContactData_properties.2.1
  have hcontA : Continuous fun s : ℝ => paperGerverContacts s 0 :=
    (continuous_apply 0).comp hcontacts
  have hcontC : Continuous fun s : ℝ => paperGerverContacts s 2 :=
    (continuous_apply 2).comp hcontacts
  -- vertex limits at the four endpoints
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have heventA : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      paperGerverContacts s 0 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsGT hTpos] with s hs
    exact ((hsingleV _ _ (hedgeA s hs)).1).symm
  have heventA' : ∀ᶠ s : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      paperGerverContacts s 0 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsLT hTpos] with s hs
    exact ((hsingleV _ _ (hedgeA s hs)).1).symm
  have hCshift : ∀ s : ℝ, s ∈ Set.Ioo (Real.pi / 2) Real.pi →
      paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
    intro s hs
    have hs' : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hang : ((s : ℝ) : Real.Angle) =
        ((s - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) := by rw [sub_add_cancel]
    rw [hang]
    exact ((hsingleV _ _ (hedgeC (s - Real.pi / 2) hs')).1).symm
  have heventC : ∀ᶠ s : ℝ in nhdsWithin (Real.pi / 2) (Set.Ioi (Real.pi / 2)),
      paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsGT (show Real.pi / 2 < Real.pi by linarith)] with s hs
    exact hCshift s hs
  have heventC' : ∀ᶠ s : ℝ in nhdsWithin Real.pi (Set.Iio Real.pi),
      paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 2 < Real.pi by linarith)] with s hs
    exact hCshift s hs
  have hcontCshift : Continuous fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2 :=
    hcontC.comp (continuous_id.sub continuous_const)
  refine ⟨⟨Kb, hKcap⟩, hKset, fun t ht => ⟨hedgeA t ht, hedgeC t ht⟩, ?_, ?_, ?_, ?_⟩
  · rw [← Real.Angle.coe_zero]
    refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb 0).1
    exact Filter.Tendsto.congr' heventA ((hcontA.tendsto 0).mono_left nhdsWithin_le_nhds)
  · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb (Real.pi / 2)).2.2.2.1
    exact Filter.Tendsto.congr' heventA'
      ((hcontA.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds)
  · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb (Real.pi / 2)).1
    have h : Filter.Tendsto (fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2)
        (nhdsWithin (Real.pi / 2) (Set.Ioi (Real.pi / 2)))
        (nhds (paperGerverContacts 0 2)) := by
      have := (hcontCshift.tendsto (Real.pi / 2)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (Real.pi / 2)))
      rwa [sub_self] at this
    exact Filter.Tendsto.congr' heventC h
  · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb Real.pi).2.2.2.1
    have h : Filter.Tendsto (fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2)
        (nhdsWithin Real.pi (Set.Iio Real.pi))
        (nhds (paperGerverContacts (Real.pi / 2) 2)) := by
      have := (hcontCshift.tendsto Real.pi).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio Real.pi))
      rwa [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at this
    exact Filter.Tendsto.congr' heventC' h

private theorem gerver_literal_standard_position
    (hTpos : (0 : ℝ) < Real.pi / 2)
    (hTmem : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (hGcomp : IsCompact gerverLiteralSofa)
    (hmotioncont : Continuous fun r : unitInterval =>
     rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
       (-paperGerverPath (r.val * (Real.pi / 2))))
    (hpath0 : paperGerverPath 0 = 0)
    (hpathTy : paperGerverPath (Real.pi / 2) 1 = 0)
    (hcapx1 : ∀ q ∈ gerverOuterCap, q 0 ≤ 1)
    (hcapy1 : ∀ q ∈ gerverOuterCap, q 1 ≤ 1)
    (hsv1 : supportValue gerverLiteralSofa ((Real.pi / 2 : ℝ) : Real.Angle) = 1) :
    IsStandardPosition gerverLiteralSofa (Real.pi / 2) := by
  -- ### Frame readers for the clockwise motion
  have hinnertan : ∀ (w : Point) (t : ℝ), inner ℝ w (tangentVector (t : Real.Angle)) =
      -(w 0 * Real.sin t) + w 1 * Real.cos t := by
    intro w t
    simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hmapply : ∀ (t : ℝ) (v p : Point),
      rotateTranslate ((-t : ℝ) : Real.Angle) (-v) p =
        rotationMap ((-t : ℝ) : Real.Angle) (p - v) := by
    intro t v p
    change (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle)) (p + -v) =
      (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle)) (p - v)
    rw [← sub_eq_add_neg]
  have hrotinv : ∀ (t : ℝ) (w : Point),
      rotationMap ((-t : ℝ) : Real.Angle) (rotationMap ((t : ℝ) : Real.Angle) w) = w := by
    intro t w
    change (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle))
      ((EuclideanGeometry.o.rotation ((t : ℝ) : Real.Angle)) w) = w
    rw [Real.Angle.coe_neg, ← Orientation.rotation_symm]
    exact (EuclideanGeometry.o.rotation ((t : ℝ) : Real.Angle)).symm_apply_apply w
  have hcoord0 : ∀ (t : ℝ) (w : Point), rotationMap ((-t : ℝ) : Real.Angle) w 0 =
      inner ℝ w (normalVector (t : Real.Angle)) := by
    intro t w
    rw [rotationMap_apply_zero, inner_normalVector_real, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_neg, Real.sin_neg]
    ring
  have hcoord1 : ∀ (t : ℝ) (w : Point), rotationMap ((-t : ℝ) : Real.Angle) w 1 =
      inner ℝ w (tangentVector (t : Real.Angle)) := by
    intro t w
    rw [rotationMap_apply_one, hinnertan, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_neg, Real.sin_neg]
    ring
  refine ⟨hGcomp, ⟨fun r => rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
      (-paperGerverPath (r.val * (Real.pi / 2))),
    ⟨gerver_literal_connected, hGcomp.isClosed, ?_, ⟨0, ?_⟩, ?_, ?_, ?_, ?_⟩,
    fun r => -(r.val * (Real.pi / 2)),
    (continuous_subtype_val.mul continuous_const).neg,
    by simp, by simp, ?_⟩,
    hTpos, le_rfl, hsv1, hsv1⟩
  · exact hmotioncont
  · -- the motion starts at the identity
    intro p
    rw [hmapply]
    simp only [Set.Icc.coe_zero, zero_mul, neg_zero, Real.Angle.coe_zero, hpath0,
      sub_zero, add_zero]
    change (EuclideanGeometry.o.rotation 0) p = p
    simp
  · -- each placement is a rotation followed by a translation
    intro r
    refine ⟨(((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle), fun p => ?_⟩
    rw [hmapply, hmapply]
    simp only [rotationMap, zero_sub, map_sub, map_neg]
    abel
  · -- the initial placement lands in the horizontal arm
    rintro _ ⟨z, hz, rfl⟩
    have heq : rotateTranslate
        ((-((0 : unitInterval).val * (Real.pi / 2)) : ℝ) : Real.Angle)
        (-paperGerverPath ((0 : unitInterval).val * (Real.pi / 2))) z = z := by
      rw [hmapply]
      simp only [Set.Icc.coe_zero, zero_mul, neg_zero, Real.Angle.coe_zero, hpath0,
        sub_zero]
      change (EuclideanGeometry.o.rotation 0) z = z
      simp
    rw [heq]
    exact mem_horizontalHallway_of_coordinates z (hcapx1 z hz.1)
      ⟨hz.1.1, hcapy1 z hz.1⟩
  · -- every intermediate placement lands in the hallway
    intro r
    rintro _ ⟨z, hz, rfl⟩
    have ht : r.val * (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨mul_nonneg r.2.1 hTpos.le, by
        nlinarith [r.2.2, hTpos]⟩
    have hzP : z ∈ paperGerverSofa := by rw [paperGerverSofa_eq_literal]; exact hz
    obtain ⟨w, hw, hwz⟩ :=
      Set.mem_iInter₂.1 hzP.2 (r.val * (Real.pi / 2)) ht
    rw [hmapply]
    have hzw : z - paperGerverPath (r.val * (Real.pi / 2)) =
        rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w := by
      rw [← hwz]
      change rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w +
          paperGerverPath (r.val * (Real.pi / 2)) -
          paperGerverPath (r.val * (Real.pi / 2)) =
        rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w
      abel
    rw [hzw, hrotinv]
    exact hw
  · -- the final placement lands in the vertical arm
    rintro _ ⟨z, hz, rfl⟩
    have hTm' : (1 : unitInterval).val * (Real.pi / 2) = Real.pi / 2 := by
      rw [Set.Icc.coe_one, one_mul]
    rw [hmapply]
    refine mem_verticalHallway_of_coordinates _ ⟨?_, ?_⟩ ?_
    · rw [hcoord0, hTm', inner_sub_left, inner_normalVector_pi_div_two,
        inner_normalVector_pi_div_two, hpathTy, sub_zero]
      exact hz.1.1
    · rw [hcoord0, hTm', inner_sub_left, inner_normalVector_pi_div_two,
        inner_normalVector_pi_div_two, hpathTy, sub_zero]
      exact hcapy1 z hz.1
    · rw [hcoord1, hTm', inner_sub_left]
      have h := (hz.1.2 (Real.pi / 2) hTmem).2
      linarith
  · -- the motion realizes the lifted clockwise angle
    intro r p
    rw [hmapply, hmapply]
    simp only [rotationMap, zero_sub, map_sub, map_neg]
    abel

private theorem gerver_literal_cap_eq
    (hsupG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverLiteralSofa (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverLiteralSofa ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1)
    (hcapy1 : ∀ q ∈ gerverOuterCap, q 1 ≤ 1) :
    capOfSofa gerverLiteralSofa (Real.pi / 2) = gerverOuterCap := by
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  have houter : ∀ t : ℝ,
      (rotatingHallwayParts gerverLiteralSofa (t : Real.Angle)).outerQuadrant =
        normalHalfPlane (t : Real.Angle)
            (supportValue gerverLiteralSofa (t : Real.Angle)) false false ∩
          normalHalfPlane ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
            (supportValue gerverLiteralSofa
              ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) false false :=
    fun t => (rotatingHallwayParts_formulas gerverLiteralSofa
      (t : Real.Angle)).2.2.2.2.2.2.2.1
  ext z
  constructor
  · rintro ⟨hstrip, hint⟩
    rw [mem_stripParallelogram_iff] at hstrip
    refine ⟨hstrip.1.1, fun t ht => ?_⟩
    have hq : z ∈ (rotatingHallwayParts gerverLiteralSofa (t : Real.Angle)).outerQuadrant :=
      Set.mem_iInter₂.1 hint t ht
    rw [houter t] at hq
    have h1 : inner ℝ z (normalVector (t : Real.Angle)) ≤
      supportValue gerverLiteralSofa (t : Real.Angle) := hq.1
    have h2 : inner ℝ z
        (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
      supportValue gerverLiteralSofa
        ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) := hq.2
    rw [normalVector_add_pi_div_two, hangsum t, (hsupG t ht).2] at h2
    rw [(hsupG t ht).1] at h1
    exact ⟨h1, h2⟩
  · intro hz
    refine ⟨?_, Set.mem_iInter₂.2 fun t ht => ?_⟩
    · rw [mem_stripParallelogram_iff, inner_normalVector_pi_div_two]
      exact ⟨⟨hz.1, hcapy1 z hz⟩, hz.1, hcapy1 z hz⟩
    · rw [houter t]
      refine ⟨?_, ?_⟩
      · change inner ℝ z (normalVector (t : Real.Angle)) ≤
          supportValue gerverLiteralSofa (t : Real.Angle)
        rw [(hsupG t ht).1]
        exact (hz.2 t ht).1
      · change inner ℝ z
            (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
          supportValue gerverLiteralSofa
            ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
        rw [normalVector_add_pi_div_two, hangsum t, (hsupG t ht).2]
        exact (hz.2 t ht).2

theorem gerver_capSupport_identification :
    (∀ q ∈ gerverOuterCap, ∃ p ∈ gerverLiteralSofa, p 0 = q 0 ∧ q 1 ≤ p 1) ∧
    paperGerverSofa = gerverLiteralSofa ∧
    IsStandardPosition gerverLiteralSofa (Real.pi / 2) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      supportValue gerverLiteralSofa (s : Real.Angle) = supportValue gerverOuterCap (s :
        Real.Angle)) ∧
    capOfSofa gerverLiteralSofa (Real.pi / 2) = gerverOuterCap ∧
    (∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        exposedEdge K.val (t : Real.Angle) = {paperGerverContacts t 0} ∧
        exposedEdge K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2}) ∧
      paperGerverContacts 0 0 = (edgeVertices K.val (0 : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 0 =
        (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 ∧
      paperGerverContacts 0 2 = (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 2 = (edgeVertices K.val (Real.pi : Real.Angle)).2) ∧
    (∀ S ∈ ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue S (t : Real.Angle) =
          inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
        supportValue S ((Real.pi / 2 + t : ℝ) : Real.Angle) =
          inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1) := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTmem : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  -- ### Path regularity and endpoints
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hC1 : ContDiff ℝ 1 (GerverSofa.Romik.path GerverSofa.PartB.params) := hreg.1
  have hpathcont : Continuous paperGerverPath := continuous_paperGerverPath hC1
  -- The clockwise motion used for the moving-sofa property, and its continuity.
  have hmotioncont : Continuous fun r : unitInterval =>
      rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
        (-paperGerverPath (r.val * (Real.pi / 2))) := by
    have hpair : Continuous fun r : unitInterval =>
        ((((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle),
          -paperGerverPath (r.val * (Real.pi / 2))) :=
      (Real.Angle.continuous_coe.comp (continuous_subtype_val.mul continuous_const).neg).prodMk
        ((hpathcont.comp (continuous_subtype_val.mul continuous_const)).neg)
    have heq : (fun r : unitInterval =>
          rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
            (-paperGerverPath (r.val * (Real.pi / 2)))) =
        (fun q : Real.Angle × Point => (AffineIsometryEquiv.vaddConst ℝ q.2).trans
          (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv) ∘
        (fun r : unitInterval => ((((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle),
          -paperGerverPath (r.val * (Real.pi / 2)))) := rfl
    rw [heq]
    exact continuous_vaddConst_trans_rotation.comp hpair
  have hpath0 : paperGerverPath 0 = 0 := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hpathTy : paperGerverPath (Real.pi / 2) 1 = 0 :=
    GerverSofa.Romik.path_end_y_zero_of_mem_box_and_equations
      GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  -- ### Coordinate images and compactness
  have hKimg : gerverOuterCap =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.Romik.K0 GerverSofa.PartB.params := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    exact Set.ext mem_gerverOuterCap_iff
  have hKcomp : IsCompact gerverOuterCap := by
    rw [hKimg]
    exact GerverSofa.PartC.Stage4.K_compact_direct.image
      GerverSofa.PartF.Coordinates.continuous_toPlane
  have hGimg : gerverLiteralSofa =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.PartC.G := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    exact Set.ext fun q =>
      and_congr (mem_gerverOuterCap_iff q) (not_congr (mem_gerverLiteralNiche_iff q))
  have hGcomp : IsCompact gerverLiteralSofa := by
    rw [hGimg]
    exact GerverSofa.PartC.Stage4.G_compact_direct.image
      GerverSofa.PartF.Coordinates.continuous_toPlane
  -- ### Contact coordinates in the moving frame
  have hvn : ∀ t : ℝ, inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (t : Real.Angle)) = 0 := fun t => by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  have hAn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_zero, inner_add_left, real_inner_smul_left,
      inner_normalVector_self, hvn t]
    ring
  have hAt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
        (paperGerverVelocityComponents t).1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_zero, inner_add_left, real_inner_smul_left,
      inner_tangentVector_self, inner_normalVector_tangentVector]
    ring
  have hCn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) -
        (paperGerverVelocityComponents t).2 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      inner_add_left, inner_sub_left, real_inner_smul_left, inner_normalVector_self, hvn t]
    ring
  have hCt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      inner_add_left, inner_sub_left, real_inner_smul_left, inner_tangentVector_self,
      inner_normalVector_tangentVector]
    ring
  -- ### The cap is the outer path constraint set
  have hOPCS : outerPathConstraintSet
      (fun t : Set.Icc (0 : ℝ) (Real.pi / 2) => paperGerverPath t.val) = gerverOuterCap := by
    ext q
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun t ht => h ⟨t, ht⟩⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun t => h t.val t.2⟩
  -- ### The two normalizing contacts
  have halpha0 : (paperGerverVelocityComponents 0).1 = 0 := by
    rw [paperGerverVelocityComponents_eq_alphaBetaAt 0 h0mem]
    have hab : GerverSofa.PartC.alphaBetaAt 0 =
        GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params 0 := by
      rw [GerverSofa.PartC.alphaBetaAt]
      simp [GerverSofa.PartC.Stage4.phi_pos.le]
    have ha2 := GerverSofa.Romik.a2_eq_neg_quarter_of_equations GerverSofa.PartB.params_equations
    rw [hab]
    simp only [GerverSofa.Romik.alphaBeta1, Real.sin_zero, Real.cos_zero, ha2]
    ring
  have hA0y : paperGerverContacts 0 0 1 = 0 := by
    have h := inner_tangentVector_zero (paperGerverContacts 0 0)
    rw [hAt 0, hpath0, inner_zero_left, halpha0] at h
    linarith
  have hC0y : paperGerverContacts 0 2 1 = 1 := by
    have h := inner_tangentVector_zero (paperGerverContacts 0 2)
    rw [hCt 0, hpath0, inner_zero_left] at h
    linarith
  obtain ⟨Kb, hKset, hKcap⟩ := outerPathConstraintSet_isCap
    (fun t : Set.Icc (0 : ℝ) (Real.pi / 2) => paperGerverPath t.val)
    (by simpa using hpath0)
    ⟨paperGerverContacts 0 0, by rw [hOPCS]; exact gerver_outer_contact_A 0 h0mem, hA0y⟩
    ⟨paperGerverContacts 0 2, by rw [hOPCS]; exact gerver_outer_contact_C 0 h0mem, hC0y⟩
  rw [hOPCS] at hKset
  -- ### Conjunct 1: every cap fibre has a sofa point at least as high
  have hfiber := gerver_cap_fiber_has_sofa_point hKcomp
  -- ### The support values of the cap
  have hcapy1 : ∀ q ∈ gerverOuterCap, q 1 ≤ 1 := by
    rintro q ⟨-, hc⟩
    have h := (hc 0 h0mem).2
    rw [hpath0, inner_zero_left, inner_tangentVector_zero] at h
    linarith
  have hcapx1 : ∀ q ∈ gerverOuterCap, q 0 ≤ 1 := by
    rintro q ⟨-, hc⟩
    have h := (hc 0 h0mem).1
    rw [hpath0, inner_zero_left, inner_normalVector_zero] at h
    linarith
  have hsupK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverOuterCap (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverOuterCap ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    intro t ht
    have hAmem := gerver_outer_contact_A t ht
    have hCmem := gerver_outer_contact_C t ht
    have hang : ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        ((t + Real.pi / 2 : ℝ) : Real.Angle) := by rw [add_comm]
    refine ⟨?_, ?_⟩
    · simp only [supportValue]
      refine IsGreatest.csSup_eq ⟨⟨paperGerverContacts t 0, hAmem, hAn t⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hz.2 t ht).1
    · rw [supportValue, hang, normalVector_add_pi_div_two_real]
      refine IsGreatest.csSup_eq ⟨⟨paperGerverContacts t 2, hCmem, hCt t⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hz.2 t ht).2
  -- ### Conjunct 4: the sofa and the cap have the same upper support
  have hGne : gerverLiteralSofa.Nonempty := gerver_literal_connected.1
  have hsupeq : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      supportValue gerverLiteralSofa (s : Real.Angle) =
        supportValue gerverOuterCap (s : Real.Angle) := by
    intro s hs
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 hs.2
    refine (supportValue_eq_of_subset_of_inner_le hGne (fun z hz => hz.1)
      (s : Real.Angle) ?_).symm
    intro z hz
    obtain ⟨w, hw, hwx, hwy⟩ := hfiber z hz
    have h1 : inner ℝ z (normalVector (s : Real.Angle)) ≤
        inner ℝ w (normalVector (s : Real.Angle)) := by
      rw [inner_normalVector_real, inner_normalVector_real, hwx]
      have := mul_le_mul_of_nonneg_right hwy hsin
      linarith
    exact h1.trans (inner_le_supportValue_of_isCompact hGcomp hw _)
  have hsupG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverLiteralSofa (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverLiteralSofa ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hsupeq t ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩]
      exact (hsupK t ht).1
    · rw [hsupeq (Real.pi / 2 + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
      exact (hsupK t ht).2
  -- ### Conjunct 3: standard position
  have hsv1 : supportValue gerverLiteralSofa ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    have h := (hsupG 0 h0mem).2
    rw [add_zero, hpath0, inner_zero_left] at h
    linarith
  have hstd := gerver_literal_standard_position hTpos hTmem hGcomp hmotioncont hpath0 hpathTy
    hcapx1 hcapy1 hsv1
  -- ### Conjunct 5: the paper cap of the sofa is the certified cap
  have hcapOf := gerver_literal_cap_eq hsupG hcapy1
  -- ### Conjunct 6: the cap representative and its contact faces
  have hfaces := gerver_cap_contact_faces Kb hKset hKcap hC1 hAn hAt hCn hCt hsupK hTpos
  refine ⟨hfiber, paperGerverSofa_eq_literal, hstd, hsupeq, hcapOf, hfaces, ?_⟩
  rintro S (rfl | rfl)
  · exact hsupK
  · exact hsupG

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Niche / Identification
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem gerver_paperNiche_identification :
    (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway gerverOuterCap (t : Real.Angle) =
        supportingHallway paperGerverSofa (t : Real.Angle) ∧
      supportingHallway paperGerverSofa (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway ∧
      (rotatingHallwayParts gerverOuterCap (t : Real.Angle)).innerCorner = paperGerverPath t) ∧
    (∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
      capNiche K = gerverLiteralNiche) ∧
    monotonization paperGerverSofa (Real.pi / 2) = paperGerverSofa ∧
    IsMonotoneSofa paperGerverSofa := by
  obtain ⟨-, hGeq, hstd, -, -, ⟨K, hKset, -⟩, hsup⟩ := gerver_capSupport_identification
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  -- ### The supporting placement is the paper motion
  have hplace : ∀ S ∈ ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement S (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t := by
    intro S hS t ht p
    rw [supportingPlacement, hangsum t, (hsup S hS t ht).1, (hsup S hS t ht).2,
      add_sub_cancel_right, add_sub_cancel_right, add_assoc,
      inner_normalVector_smul_add_inner_tangentVector_smul]
  have hplaceK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement gerverOuterCap (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t :=
    hplace gerverOuterCap (Or.inl rfl)
  have hplaceG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement paperGerverSofa (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t := by
    rw [hGeq]
    exact hplace gerverLiteralSofa (Or.inr rfl)
  have hhallG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway paperGerverSofa (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway :=
    fun t ht => Set.image_congr' (hplaceG t ht)
  have hhallK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway gerverOuterCap (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway :=
    fun t ht => Set.image_congr' (hplaceK t ht)
  -- ### The monotonization fixed point
  have hmono : monotonization paperGerverSofa (Real.pi / 2) = paperGerverSofa := by
    rw [monotonization, Set.iInter₂_congr hhallG]
    rfl
  refine ⟨fun t ht => ⟨(hhallK t ht).trans (hhallG t ht).symm, hhallG t ht, ?_⟩, ⟨K, hKset, ?_⟩,
    hmono, paperGerverSofa, Real.pi / 2, by rw [hGeq]; exact hstd, hmono.symm⟩
  · change supportingPlacement gerverOuterCap (t : Real.Angle) hallwayParts.innerCorner =
      paperGerverPath t
    rw [hplaceK t ht]
    change rotationMap (t : Real.Angle) 0 + paperGerverPath t = paperGerverPath t
    rw [rotationMap, map_zero, zero_add]
  -- ### The cap niche is the literal niche
  · have hfan : ∀ q : Point, q ∈ capFan (Real.pi / 2) ↔ 0 ≤ q 1 := by
      intro q
      have h : (q ∈ capFan (Real.pi / 2)) ↔
          ((0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ∧
            (0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))) := Iff.rfl
      rw [h, inner_normalVector_pi_div_two, and_self]
    have hquad : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ q : Point,
        q ∈ innerQuadrant gerverOuterCap t ↔
          inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
            inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0 := by
      intro t ht q
      have hang : ((t + Real.pi / 2 : ℝ) : Real.Angle) =
          ((Real.pi / 2 + t : ℝ) : Real.Angle) := by rw [add_comm]
      have h : (q ∈ innerQuadrant gerverOuterCap t) ↔
          (inner ℝ q (normalVector (t : Real.Angle)) <
              supportValue gerverOuterCap (t : Real.Angle) - 1 ∧
            inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
              supportValue gerverOuterCap ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := Iff.rfl
      rw [h, normalVector_add_pi_div_two_real, hang,
        (hsup gerverOuterCap (Or.inl rfl) t ht).1, (hsup gerverOuterCap (Or.inl rfl) t ht).2,
        add_sub_cancel_right, add_sub_cancel_right, inner_sub_left, inner_sub_left,
        sub_neg, sub_neg]
    rw [capNiche, hKset]
    ext q
    constructor
    · rintro ⟨hq, hmem⟩
      obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.1 hmem
      exact ⟨(hfan q).1 hq, t, ht, (hquad t (Set.Ioo_subset_Icc_self ht) q).1 hqt⟩
    · rintro ⟨hy, t, ht, hqt⟩
      exact ⟨(hfan q).2 hy,
        Set.mem_iUnion₂.2 ⟨t, ht, (hquad t (Set.Ioo_subset_Icc_self ht) q).2 hqt⟩⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Surface densities of the certified Gerver cap

The certified Gerver cap carries the two envelope densities `GerverSofa.PartC.Stage2.rhoA` and
`rhoC` of the vendor development: its surface-area measure is `rhoA (t) dt` on the angular arc
`[0, π/2)` and `rhoC (t - π/2) dt` on `(π/2, π]`.

The argument is stage by stage.  On each of the five closed stages the selected (positive) vertex
of the cap is a globally analytic branch of the certified phase curves, with derivative
`rhoA t • v t` for the first contact and `-rhoC t • u t` for the third, so
`surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt` identifies the surface measure with
the exact Lebesgue density on that stage.  The stages are then glued with
`measure_angleImage_eq_of_union`; only the last `rhoA` stage needs an interior exhaustion,
because the positive vertex jumps at `π/2`.

The same stagewise phase curves describe the two *inner* contacts, because `B = A - u` and
`D = C - v` differ from the outer contacts by a frame vector
(`paperGerverContacts_one_eq_sub`, `paperGerverContacts_three_eq_sub`).  Subtracting the frame
vector from a phase curve therefore produces a globally differentiable branch curve for `B` on
the last two stages and for `D` on the first two, with the nonnegative speeds `1 - rhoA` and
`1 - rhoC` (`exists_branch_paperGerverContacts_one`,
`exists_branch_paperGerverContacts_three`); the two speed bounds are again coarse box bounds on
the certified parameters.
-/

/-! ### Coordinate transport of derivatives -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace MovingSofa

open MeasureTheory Set
open scoped ENNReal

/-- The vendor coordinate identification is homogeneous. -/
private theorem toPlane_smul (c : ℝ) (q : GerverSofa.Point) :
    GerverSofa.PartF.Coordinates.toPlane (c • q) =
      c • GerverSofa.PartF.Coordinates.toPlane q := by
  ext i
  fin_cases i <;> rfl

/-! ### The certified switching angles -/

/-- The paper's two switching angles are the vendor parameter angles, strictly ordered. -/
private theorem paperGerver_switchAngles :
    GerverSofa.PartB.params.phi = GerversSofa.φ ∧
      GerverSofa.PartB.params.theta = GerversSofa.θ ∧
      GerverSofa.PartB.params.phi < GerverSofa.PartB.params.theta ∧
      GerverSofa.PartB.params.theta < Real.pi / 4 := by
  obtain ⟨-, hphi, htheta, -, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 GerverSofa.PartB.params GerverSofa.PartB.params_mem
      GerverSofa.PartB.params_equations
  have hphi' : GerverSofa.PartB.params.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : GerverSofa.PartB.params.theta = GerversSofa.θ := htheta.trans selected_theta
  refine ⟨hphi', htheta', ?_, ?_⟩
  · rw [hphi', htheta']; exact hphitheta
  · rw [htheta']; exact hthetalt

/-! ### The contact curves as transported certified phase curves -/

/-- The first contact of the paper Gerver cap is the transported point `x + α v + u`. -/
private theorem paperGerverContacts_zero_eq_toPlane {X W : ℝ → GerverSofa.Point} {t : ℝ}
    (hx : GerverSofa.Romik.path GerverSofa.PartB.params t = X t)
    (hw : paperGerverVelocityComponents t = W t) :
    paperGerverContacts t 0 =
      GerverSofa.PartF.Coordinates.toPlane (X t + (W t).1 • GerverSofa.v t + GerverSofa.u t) := by
  have hp : paperGerverPath t = GerverSofa.PartF.Coordinates.toPlane (X t) := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params t) = _
    rw [hx]
  simp only [paperGerverContacts, Matrix.cons_val_zero, hw, hp]
  ext i
  fin_cases i <;> rfl

/-- The third contact of the paper Gerver cap is the transported point `x - β u + v`. -/
private theorem paperGerverContacts_two_eq_toPlane {X W : ℝ → GerverSofa.Point} {t : ℝ}
    (hx : GerverSofa.Romik.path GerverSofa.PartB.params t = X t)
    (hw : paperGerverVelocityComponents t = W t) :
    paperGerverContacts t 2 =
      GerverSofa.PartF.Coordinates.toPlane (X t - (W t).2 • GerverSofa.u t + GerverSofa.v t) := by
  have hp : paperGerverPath t = GerverSofa.PartF.Coordinates.toPlane (X t) := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params t) = _
    rw [hx]
  simp only [paperGerverContacts, hw, hp]
  ext i
  fin_cases i <;> rfl

open GerverSofa.PartC.Stage2 GerverSofa.Romik in
/-- On each of the five stages the two contact curves are transported analytic phase curves whose
derivatives are `rA • v` and `-rC • u` for continuous factors agreeing with `rhoA`, `rhoC`. -/
private theorem exists_phaseCurves_of_stage (j : Fin 5) :
    ∃ (PA PC : ℝ → GerverSofa.Point) (rA rC : ℝ → ℝ),
      (∀ t, HasDerivAt PA (rA t • GerverSofa.v t) t) ∧
      (∀ t, HasDerivAt PC (-(rC t) • GerverSofa.u t) t) ∧
      Continuous rA ∧ Continuous rC ∧
      (∀ t ∈ gerverStageIntervals j,
        paperGerverContacts t 0 = GerverSofa.PartF.Coordinates.toPlane (PA t) ∧
        paperGerverContacts t 2 = GerverSofa.PartF.Coordinates.toPlane (PC t)) ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes j.castSucc) (gerverStageTimes j.succ),
        rhoA t = rA t ∧ rhoC t = rC t) := by
  classical
  obtain ⟨hphi', htheta', hφθ', hθq'⟩ := paperGerver_switchAngles
  have heqs : Equations GerverSofa.PartB.params := GerverSofa.PartB.params_equations
  have hφθ : GerversSofa.φ < GerversSofa.θ := by rw [← hphi', ← htheta']; exact hφθ'
  have hθq : GerversSofa.θ < Real.pi / 4 := by rw [← htheta']; exact hθq'
  have hθη : GerversSofa.θ ≤ Real.pi / 2 - GerversSofa.θ := by
    have := GerverSofa.PartC.switchOrder.theta_le_eta
    rw [htheta'] at this; exact this
  have hητ : Real.pi / 2 - GerversSofa.θ ≤ Real.pi / 2 - GerversSofa.φ := by linarith
  have heta : GerverSofa.PartC.eta = Real.pi / 2 - GerversSofa.θ := by
    simp only [GerverSofa.PartC.eta, GerverSofa.PartC.T, htheta']
  have htau : GerverSofa.PartC.tau = Real.pi / 2 - GerversSofa.φ := by
    simp only [GerverSofa.PartC.tau, GerverSofa.PartC.T, hphi']
  have hvel : ∀ (i : Fin 5), ∀ t ∈ gerverStageIntervals i,
      paperGerverVelocityComponents t = gerverBranchVelocityComponents i t :=
    paperGerverContactData_properties.2.2.2
  fin_cases j
  · refine ⟨phaseA1, phaseC1, fun _ ↦ 0, fun _ ↦ 1 / 2, fun t ↦ A1_hasDerivAt_public t,
      fun t ↦ C1_hasDerivAt_public t, continuous_const, continuous_const, ?_, ?_⟩
    · change ∀ t ∈ Set.Icc (0 : ℝ) GerversSofa.φ, _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path1 GerverSofa.PartB.params t :=
        path_eq_path1_of_mem_Icc _ (by rw [hphi']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta1 GerverSofa.PartB.params t :=
        hvel 0 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc (0 : ℝ) GerversSofa.φ, _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA2, phaseC2,
      fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.b1 * t +
        GerverSofa.PartC.params.b2 + 1 / 2,
      fun t ↦ t / 2 - GerverSofa.PartC.params.b1,
      fun t ↦ A2_hasDerivAt_public t, fun t ↦ C2_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · change ∀ t ∈ Set.Icc GerversSofa.φ GerversSofa.θ, _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path2 GerverSofa.PartB.params t :=
        path_eq_path2_of_mem_Icc heqs (by rw [hphi', htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta2 GerverSofa.PartB.params t :=
        hvel 1 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc GerversSofa.φ GerversSofa.θ, _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA3, phaseC3, fun t ↦ 1 + GerverSofa.PartC.params.c1 - t,
      fun t ↦ 1 + GerverSofa.PartC.params.c2 + t,
      fun t ↦ A3_hasDerivAt_public t, fun t ↦ C3_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · change ∀ t ∈ Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path3 GerverSofa.PartB.params t :=
        path_eq_path3_of_mem_Icc heqs hφθ' (by rw [htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta3 GerverSofa.PartB.params t :=
        hvel 2 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA4, phaseC4, fun t ↦ GerverSofa.PartC.params.d1 - t / 2,
      fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.d1 * t +
        GerverSofa.PartC.params.d2 + 1 / 2,
      fun t ↦ A4_hasDerivAt_public t, fun t ↦ C4_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · change ∀ t ∈ Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path4 GerverSofa.PartB.params t :=
        path_eq_path4_of_mem_Icc heqs hφθ' hθq' (by rw [hphi', htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta4 GerverSofa.PartB.params t :=
        hvel 3 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA5, phaseC5, fun _ ↦ 1 / 2, fun _ ↦ 0, fun t ↦ A5_hasDerivAt_public t,
      fun t ↦ by simpa using C5_hasDerivAt_public t, continuous_const, continuous_const, ?_, ?_⟩
    · change ∀ t ∈ Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path5 GerverSofa.PartB.params t :=
        path_eq_path5_of_mem_Icc heqs hφθ' hθq' (by rw [hphi']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta5 GerverSofa.PartB.params t :=
        hvel 4 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])

/-! ### Contact derivatives on the open stages -/

/-- A branch curve agreeing with a global curve on a closed stage computes the global derivative
at every interior parameter of that stage. -/
theorem hasDerivAt_of_eqOn_stage {G F : ℝ → Point} {w : ℝ → Point} {i : Fin 5}
    (hF : ∀ s, HasDerivAt F (w s) s) (hGF : ∀ t ∈ gerverStageIntervals i, G t = F t)
    {t : ℝ} (ht : t ∈ Set.Ioo (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)) :
    HasDerivAt G (w t) t :=
  (hF t).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
    fun u hu ↦ hGF u (Set.Ioo_subset_Icc_self hu))

/-- The transported phase curves of a stage are differentiable everywhere, with the two branch
speeds against the moving frame. -/
private theorem hasDerivAt_toPlane_phaseCurves {PA PC : ℝ → GerverSofa.Point}
    {rA rC : ℝ → ℝ} (hPA : ∀ t, HasDerivAt PA (rA t • GerverSofa.v t) t)
    (hPC : ∀ t, HasDerivAt PC (-(rC t) • GerverSofa.u t) t) :
    (∀ s, HasDerivAt (fun u ↦ GerverSofa.PartF.Coordinates.toPlane (PA u))
        (rA s • tangentVector (s : Real.Angle)) s) ∧
      ∀ s, HasDerivAt (fun u ↦ GerverSofa.PartF.Coordinates.toPlane (PC u))
        (-(rC s) • normalVector (s : Real.Angle)) s := by
  refine ⟨fun s ↦ ?_, fun s ↦ ?_⟩
  · have h := hasDerivAt_toPlane (hPA s)
    rwa [toPlane_smul] at h
  · have h := hasDerivAt_toPlane (hPC s)
    rwa [toPlane_smul] at h

/-- Inside each open stage the two contact curves are differentiable with the envelope
densities as their speed factors. -/
private theorem hasDerivAt_paperGerverContacts_of_mem_stage (j : Fin 5) {t : ℝ}
    (ht : t ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ)) :
    HasDerivAt (fun u ↦ paperGerverContacts u 0)
        (GerverSofa.PartC.Stage2.rhoA t • tangentVector (t : Real.Angle)) t ∧
      HasDerivAt (fun u ↦ paperGerverContacts u 2)
        (-(GerverSofa.PartC.Stage2.rhoC t) • normalVector (t : Real.Angle)) t := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, -, -, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  obtain ⟨hrA, hrC⟩ := hrho t (Set.Ioo_subset_Ioc_self ht)
  obtain ⟨hA, hC⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  refine ⟨?_, ?_⟩
  · rw [hrA]
    exact hasDerivAt_of_eqOn_stage hA (fun u hu ↦ (hmem u hu).1) ht
  · rw [hrC]
    exact hasDerivAt_of_eqOn_stage hC (fun u hu ↦ (hmem u hu).2) ht

/-! ### Singleton faces have no surface atom -/

/-- A face whose positive tangent endpoint does not exceed its negative one carries no surface
atom: the atom is exactly the tangential gap between the two endpoints. -/
private theorem surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le
    (K : ConvexBody Point) (t : Real.Angle)
    (h : inner ℝ (edgeVertices K t).1 (tangentVector t) ≤
      inner ℝ (edgeVertices K t).2 (tangentVector t)) :
    surfaceAreaMeasure K {t} = 0 := by
  have hfin : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hsplit := (surfaceAreaMeasure_atom_length K t).2.2
  have hone : inner ℝ (tangentVector t) (tangentVector t) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_tangentVector]
    norm_num
  have hinner : inner ℝ (edgeVertices K t).1 (tangentVector t) =
      inner ℝ (edgeVertices K t).2 (tangentVector t) +
        (surfaceAreaMeasure K {t}).toReal := by
    rw [hsplit, inner_add_left, real_inner_smul_left, hone, mul_one]
  have hle : (surfaceAreaMeasure K {t}).toReal ≤ 0 := by linarith
  have hzero : (surfaceAreaMeasure K {t}).toReal = 0 :=
    le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 hzero with h0 | htop
  · exact h0
  · exact absurd htop (measure_ne_top _ _)

/-! ### Measurability and boundedness of the two envelope densities -/

private theorem measurable_rhoA : Measurable GerverSofa.PartC.Stage2.rhoA := by
  unfold GerverSofa.PartC.Stage2.rhoA
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

private theorem measurable_rhoC : Measurable GerverSofa.PartC.Stage2.rhoC := by
  unfold GerverSofa.PartC.Stage2.rhoC
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

open GerverSofa.PartC.Stage2 in
/-- Each of the finitely many branch polynomials of the two envelope densities is continuous,
hence bounded on the compact physical interval. -/
private theorem exists_bound_rhoA_rhoC : ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    rhoA t ≤ M ∧ rhoC t ≤ M := by
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), f t ≤ M := by
    intro f hf
    obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.2 (show (0 : ℝ) ≤ Real.pi / 2 by linarith [Real.pi_pos]))
      hf.continuousOn
    exact ⟨f x, fun t ht ↦ isMaxOn_iff.1 hmax t ht⟩
  obtain ⟨M1, h1⟩ := key (fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.b1 * t +
    GerverSofa.PartC.params.b2 + 1 / 2) (by fun_prop)
  obtain ⟨M2, h2⟩ := key (fun t ↦ 1 + GerverSofa.PartC.params.c1 - t) (by fun_prop)
  obtain ⟨M3, h3⟩ := key (fun t ↦ GerverSofa.PartC.params.d1 - t / 2) (by fun_prop)
  obtain ⟨M4, h4⟩ := key (fun t ↦ t / 2 - GerverSofa.PartC.params.b1) (by fun_prop)
  obtain ⟨M5, h5⟩ := key (fun t ↦ 1 + GerverSofa.PartC.params.c2 + t) (by fun_prop)
  obtain ⟨M6, h6⟩ := key (fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.d1 * t +
    GerverSofa.PartC.params.d2 + 1 / 2) (by fun_prop)
  refine ⟨max (max (max M1 M2) (max M3 M4)) (max (max M5 M6) 1), fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [rhoA]
    split_ifs
    · exact le_trans (by norm_num) (le_max_right _ _ |>.trans' (le_max_right _ _))
    · exact (h1 t ht).trans (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
    · exact (h2 t ht).trans (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
    · exact (h3 t ht).trans (le_max_of_le_left (le_max_of_le_right (le_max_left _ _)))
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))
  · rw [rhoC]
    split_ifs
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))
    · exact (h4 t ht).trans (le_max_of_le_left (le_max_of_le_right (le_max_right _ _)))
    · exact (h5 t ht).trans (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
    · exact (h6 t ht).trans (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))

/-! ### Elementary facts about the stage endpoints and the frame -/

/-- The two Gerver switch angles satisfy `0 < φ < θ < π/4`. -/
private theorem gerver_switch_angle_bounds :
    (0 : ℝ) < GerversSofa.φ ∧ GerversSofa.φ < GerversSofa.θ ∧ GerversSofa.θ < Real.pi / 4 := by
  obtain ⟨-, -, -, hpos, hlt, hq, -⟩ :=
    gerver_parameter_identification.1 GerverSofa.PartB.params GerverSofa.PartB.params_mem
      GerverSofa.PartB.params_equations
  refine ⟨selected_phi ▸ hpos, ?_, selected_theta ▸ hq⟩
  rw [← selected_phi, ← selected_theta]
  exact hlt

private theorem gerverStageTimes_nonneg (k : Fin 6) : 0 ≤ gerverStageTimes k := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases k
  · change (0 : ℝ) ≤ 0
    exact le_refl 0
  · change (0 : ℝ) ≤ GerversSofa.φ
    linarith
  · change (0 : ℝ) ≤ GerversSofa.θ
    linarith
  · change (0 : ℝ) ≤ Real.pi / 2 - GerversSofa.θ
    linarith
  · change (0 : ℝ) ≤ Real.pi / 2 - GerversSofa.φ
    linarith
  · change (0 : ℝ) ≤ Real.pi / 2
    linarith

private theorem gerverStageTimes_le_pi_div_two (k : Fin 6) : gerverStageTimes k ≤ Real.pi / 2 := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases k
  · change (0 : ℝ) ≤ Real.pi / 2
    linarith
  · change GerversSofa.φ ≤ Real.pi / 2
    linarith
  · change GerversSofa.θ ≤ Real.pi / 2
    linarith
  · change Real.pi / 2 - GerversSofa.θ ≤ Real.pi / 2
    linarith
  · change Real.pi / 2 - GerversSofa.φ ≤ Real.pi / 2
    linarith
  · change Real.pi / 2 ≤ Real.pi / 2
    exact le_refl _

private theorem gerverStageTimes_lt_succ (j : Fin 5) :
    gerverStageTimes j.castSucc < gerverStageTimes j.succ := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases j
  · change (0 : ℝ) < GerversSofa.φ
    linarith
  · change GerversSofa.φ < GerversSofa.θ
    linarith
  · change GerversSofa.θ < Real.pi / 2 - GerversSofa.θ
    linarith
  · change Real.pi / 2 - GerversSofa.θ < Real.pi / 2 - GerversSofa.φ
    linarith
  · change Real.pi / 2 - GerversSofa.φ < Real.pi / 2
    linarith

private theorem gerverStageTimes_four_lt_pi_div_two : gerverStageTimes 4 < Real.pi / 2 := by
  have h : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_lt_succ 4
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  linarith

/-! ### Almost every parameter lies in an open stage -/

/-- A parameter of the rotation interval that is none of the six stage times lies in an open
stage. -/
theorem mem_openStage_of_mem_Ico {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (Real.pi / 2))
    (hne : ∀ k : Fin 6, t ≠ gerverStageTimes k) :
    ∃ j : Fin 5, t ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ) := by
  have hlow : gerverStageTimes 0 < t :=
    lt_of_le_of_ne (gerverStageTimes_zero ▸ ht.1) fun h ↦ hne 0 h.symm
  have hhigh : t < gerverStageTimes 5 := ht.2
  rcases lt_or_gt_of_ne (hne 1) with h1 | h1
  · exact ⟨0, hlow, h1⟩
  · rcases lt_or_gt_of_ne (hne 2) with h2 | h2
    · exact ⟨1, h1, h2⟩
    · rcases lt_or_gt_of_ne (hne 3) with h3 | h3
      · exact ⟨2, h2, h3⟩
      · rcases lt_or_gt_of_ne (hne 4) with h4 | h4
        · exact ⟨3, h3, h4⟩
        · exact ⟨4, h4, hhigh⟩

/-- Almost every parameter of a measurable subset of the shifted rotation interval lies in a
shifted open stage. -/
theorem ae_mem_openStage (c : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Icc c (c + Real.pi / 2)) :
    ∀ᵐ u ∂volume.restrict S, ∃ j : Fin 5,
      u - c ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ) := by
  refine ae_restrict_mem_of_countable_diff hS
    (((Set.finite_range gerverStageTimes).countable).image fun x ↦ x + c) ?_
  rintro u ⟨hu, hu'⟩
  by_contra hcon
  have hne : ∀ k : Fin 6, u - c ≠ gerverStageTimes k := by
    intro k hk
    exact hcon ⟨gerverStageTimes k, Set.mem_range_self k, by rw [← hk]; ring⟩
  have hmem : u - c ∈ Set.Ico (0 : ℝ) (Real.pi / 2) := by
    refine ⟨by linarith [(hSsub hu).1], ?_⟩
    have h5 : u - c ≠ gerverStageTimes 5 := hne 5
    rw [show gerverStageTimes 5 = Real.pi / 2 from rfl] at h5
    exact lt_of_le_of_ne (by linarith [(hSsub hu).2]) h5
  exact hu' (mem_openStage_of_mem_Ico hmem hne)

/-! ### Branch curves for the two inner contacts

The second contact `B = x + α v` is the first contact `A = x + α v + u` translated by `-u`, and
the fourth contact `D = x - β u` is the third contact `C = x - β u + v` translated by `-v`.  So
subtracting a frame vector from the transported phase curve of a stage produces a globally
differentiable branch curve for `B` and for `D`, whose speed against the frame is `1 - rhoA`
resp. `1 - rhoC`.  Both are nonnegative exactly where the inner contact is a genuine contact:
after the third stage time for `B` and before the second for `D`.
-/

/-- The second contact curve is the first one translated by `-u_t`. -/
theorem paperGerverContacts_one_eq_sub (t : ℝ) :
    paperGerverContacts t 1 = paperGerverContacts t 0 - normalVector (t : Real.Angle) := by
  change _ = paperGerverPath t + (paperGerverVelocityComponents t).1 •
    tangentVector (t : Real.Angle) + normalVector (t : Real.Angle) - normalVector _
  rw [add_sub_cancel_right]
  rfl

/-- The fourth contact curve is the third one translated by `-v_t`. -/
theorem paperGerverContacts_three_eq_sub (t : ℝ) :
    paperGerverContacts t 3 = paperGerverContacts t 2 - tangentVector (t : Real.Angle) := by
  change _ = paperGerverPath t - (paperGerverVelocityComponents t).2 •
    normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) - tangentVector _
  rw [add_sub_cancel_right]
  rfl

open GerverSofa.PartC.Stage2 in
/-- After the third stage time the first contact never outruns the rotating frame: its tangential
speed `rhoA` is at most the unit speed of `u`.  On the fourth stage this is the coarse bound
`d₁ ≤ 33/25` against `t > π/2 - θ > 4/5`; on the fifth the speed is the constant `1/2`. -/
private theorem rhoA_le_one_of_gerverStageTimes_three_lt {t : ℝ}
    (ht : gerverStageTimes 3 < t) : rhoA t ≤ 1 := by
  have h1 : gerverStageTimes 1 = GerverSofa.PartB.params.phi := gerverStageTimes_one
  have h2 : gerverStageTimes 2 = GerverSofa.PartB.params.theta := gerverStageTimes_two
  have h3 : gerverStageTimes 3 = GerverSofa.PartC.eta := gerverStageTimes_three
  have h4 : gerverStageTimes 4 = GerverSofa.PartC.tau := gerverStageTimes_four
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have h32 : gerverStageTimes 3 = Real.pi / 2 - gerverStageTimes 2 := rfl
  have hd1 := gerverDirectBox_d1_upper_bound GerverSofa.PartB.params_mem
  have hθ := gerverStageTimes_two_le_seven_div_ten
  have hpi := Real.pi_gt_three
  rw [rhoA]
  split_ifs with hphi htheta heta
  · exact absurd (h1 ▸ hphi) (by linarith)
  · exact absurd (h2 ▸ htheta) (by linarith)
  · exact absurd (h3 ▸ heta) (by linarith)
  · linarith
  · norm_num

open GerverSofa.PartC.Stage2 in
/-- Before the second stage time the third contact never outruns the rotating frame: its normal
speed `rhoC` is at most the unit speed of `v`.  On the first stage the speed is the constant
`1/2`; on the second this is the coarse bound `b₁ ≥ -53/100` against `t ≤ θ ≤ 7/10`. -/
private theorem rhoC_le_one_of_le_gerverStageTimes_two {t : ℝ}
    (ht : t ≤ gerverStageTimes 2) : rhoC t ≤ 1 := by
  have h2 : gerverStageTimes 2 = GerverSofa.PartB.params.theta := gerverStageTimes_two
  have hb1 := gerverDirectBox_b1_lower_bound GerverSofa.PartB.params_mem
  have hθ := gerverStageTimes_two_le_seven_div_ten
  rw [rhoC]
  split_ifs with hphi htheta
  · norm_num
  · linarith
  · exact absurd (h2 ▸ ht) (by linarith)
  · exact absurd (h2 ▸ ht) (by linarith)
  · exact absurd (h2 ▸ ht) (by linarith)

/-- On each of the last two stages the second contact curve agrees with a globally differentiable
branch curve whose derivative is `-(g t) • v_t` for a continuous factor `g` that is nonnegative
on the stage. -/
theorem exists_branch_paperGerverContacts_one {i : Fin 5} (hi : i = 3 ∨ i = 4) :
    ∃ (F : ℝ → Point) (g : ℝ → ℝ),
      (∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) ∧ Continuous g ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ), 0 ≤ g t) ∧
      (∀ t ∈ gerverStageIntervals i, paperGerverContacts t 1 = F t) := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, -, hmem, hrho⟩ := exists_phaseCurves_of_stage i
  obtain ⟨hA, -⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  have h3i : gerverStageTimes 3 ≤ gerverStageTimes i.castSucc :=
    gerverStageTimes_strictMono.monotone (by rcases hi with rfl | rfl <;> decide)
  refine ⟨fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PA s) - normalVector (s : Real.Angle),
    fun s ↦ 1 - rA s, fun s ↦ ?_, continuous_const.sub hcA, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · refine ((hA s).sub (hasDerivAt_normalVector s)).congr_deriv ?_
    module
  · have hrA := (hrho t ht).1
    linarith [rhoA_le_one_of_gerverStageTimes_three_lt (lt_of_le_of_lt h3i ht.1)]
  · rw [paperGerverContacts_one_eq_sub, (hmem t ht).1]

/-- On each of the first two stages the fourth contact curve agrees with a globally differentiable
branch curve whose derivative is `g t • u_t` for a continuous factor `g` that is nonnegative on
the stage. -/
theorem exists_branch_paperGerverContacts_three {i : Fin 5} (hi : i = 0 ∨ i = 1) :
    ∃ (F : ℝ → Point) (g : ℝ → ℝ),
      (∀ s, HasDerivAt F (g s • normalVector (s : Real.Angle)) s) ∧ Continuous g ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ), 0 ≤ g t) ∧
      (∀ t ∈ gerverStageIntervals i, paperGerverContacts t 3 = F t) := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, -, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage i
  obtain ⟨-, hC⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  have hi2 : gerverStageTimes i.succ ≤ gerverStageTimes 2 :=
    gerverStageTimes_strictMono.monotone (by rcases hi with rfl | rfl <;> decide)
  refine ⟨fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PC s) - tangentVector (s : Real.Angle),
    fun s ↦ 1 - rC s, fun s ↦ ?_, continuous_const.sub hcC, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · refine ((hC s).sub (hasDerivAt_tangentVector s)).congr_deriv ?_
    module
  · have hrC := (hrho t ht).2
    linarith [rhoC_le_one_of_le_gerverStageTimes_two (le_trans ht.2 hi2)]
  · rw [paperGerverContacts_three_eq_sub, (hmem t ht).2]

/-! ### The certified cap witness and its positive vertex curves -/

/-- The certified cap witness of support identification, together with the identification of its
positive vertex by the two contact curves on the whole closed parameter interval and the
vanishing of the surface atom at the included endpoint `0`.

Both included endpoint faces are singletons: at `0` the first contact is the anchor `(1, 0)`
and the cap lies in `0 ≤ q 1`, and at `π` the third contact has vanishing second coordinate,
so in each case the positive tangent endpoint cannot exceed the negative one. -/
private theorem exists_gerverCap_positiveVertex :
    ∃ K : CapSpace (Real.pi / 2),
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      surfaceAreaMeasure K.val {((0 : ℝ) : Real.Angle)} = 0 ∧
      (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
        (edgeVertices K.val ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0) ∧
      (∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
        (edgeVertices K.val ((s : ℝ) : Real.Angle)).1 =
          paperGerverContacts (s - Real.pi / 2) 2) := by
  have hpi := Real.pi_gt_three
  have hTpos : (0 : ℝ) < Real.pi / 2 := by linarith
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTmem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  obtain ⟨-, hpaper, -, -, hcapEq, ⟨K, hKset, hedges, hA0, -, hC0, hCT⟩, -⟩ :=
    gerver_capSupport_identification
  have hKupper : ∀ q ∈ (K.val : Set Point), 0 ≤ q 1 := by
    intro q hq
    rw [hKset] at hq
    exact hq.1
  -- the two included endpoint contacts lie on the lower fan boundary
  have hcontactA0y : paperGerverContacts 0 0 1 = 0 := by
    have h := fromPlane_paperGerverContacts 0 h0mem 0
    have h2 : paperGerverContacts 0 0 =
        GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.A 0) := by
      rw [← GerverSofa.PartF.Coordinates.toPlane_fromPlane (paperGerverContacts 0 0), h]
      rfl
    rw [h2, GerverSofa.PartC.Stage2.A_zero_eq_anchor]
    rfl
  have hcontactCTy : paperGerverContacts (Real.pi / 2) 2 1 = 0 := by
    have h := fromPlane_paperGerverContacts (Real.pi / 2) hTmem 2
    have h2 : paperGerverContacts (Real.pi / 2) 2 =
        GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.C (Real.pi / 2)) := by
      rw [← GerverSofa.PartF.Coordinates.toPlane_fromPlane
        (paperGerverContacts (Real.pi / 2) 2), h]
      rfl
    rw [h2]
    exact GerverSofa.PartC.Stage2.C_T_snd_zero
  -- hence both included endpoint faces are singletons and carry no atom
  have hatom0 : surfaceAreaMeasure K.val {((0 : ℝ) : Real.Angle)} = 0 := by
    refine surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le K.val _ ?_
    have hfst : (edgeVertices K.val ((0 : ℝ) : Real.Angle)).1 = paperGerverContacts 0 0 := by
      rw [Real.Angle.coe_zero]
      exact hA0.symm
    rw [inner_tangentVector_zero, inner_tangentVector_zero, hfst, hcontactA0y]
    exact hKupper _ (edgeVertices_snd_mem K.val _).1
  have hatompi : surfaceAreaMeasure K.val {((Real.pi : ℝ) : Real.Angle)} = 0 := by
    refine surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le K.val _ ?_
    rw [inner_tangentVector_pi, inner_tangentVector_pi, ← hCT, hcontactCTy]
    have h := hKupper _ (edgeVertices_fst_mem K.val ((Real.pi : ℝ) : Real.Angle)).1
    linarith
  refine ⟨K, by rw [hpaper, hcapEq]; exact hKset, hatom0, ?_, ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, Real.Angle.coe_zero]
      exact hA0.symm
    · rw [edgeVertices_eq_of_exposedEdge_singleton (hedges t ⟨h, ht.2⟩).1]
  · intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1, sub_self]
      exact hC0.symm
    rcases eq_or_lt_of_le hs.2 with h2 | h2
    · have hatom := (surfaceAreaMeasure_atom_length K.val ((Real.pi : ℝ) : Real.Angle)).2.2
      rw [hatompi] at hatom
      simp only [ENNReal.toReal_zero, zero_smul, add_zero] at hatom
      rw [h2, show Real.pi - Real.pi / 2 = Real.pi / 2 from by ring, hatom, ← hCT]
    · have htmem : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith, by linarith⟩
      have h := (hedges (s - Real.pi / 2) htmem).2
      rw [show s - Real.pi / 2 + Real.pi / 2 = s from by ring] at h
      rw [edgeVertices_eq_of_exposedEdge_singleton h]

/-! ### The stagewise density identities -/

/-- On a subinterval of a single stage, strictly below the switch `π/2`, the surface measure of
an angular image is the `rhoA`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage (K : ConvexBody Point)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (j : Fin 5) (a b : ℝ) (hja : gerverStageTimes j.castSucc ≤ a)
    (hjb : b ≤ gerverStageTimes j.succ) (hbT : b < Real.pi / 2)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt b a with hle | hab
  · have hempty : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      have hx' := hSsub hx
      rw [Set.mem_Ioc] at hx'
      linarith [hx'.1, hx'.2]
    rw [hempty]
    simp
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  have ha0 : 0 ≤ a := le_trans (gerverStageTimes_nonneg _) hja
  refine surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt K hab (by linarith)
    (fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PA s)) rA
    GerverSofa.PartC.Stage2.rhoA (fun s ↦ ?_) hcA ?_ ?_ ?_ S hS hSsub
  · have h := hasDerivAt_toPlane (hPA s)
    rw [toPlane_smul] at h
    exact h
  · intro s hs
    rw [hvertexA s ⟨le_trans ha0 hs.1, lt_of_le_of_lt hs.2 hbT⟩]
    exact (hmem s ⟨le_trans hja hs.1, le_trans hs.2 hjb⟩).1
  · intro s hs
    exact (hrho s ⟨lt_of_le_of_lt hja hs.1, le_trans hs.2 hjb⟩).1
  · intro s hs
    have hs0 : (0 : ℝ) ≤ s := by linarith [hs.1]
    have hsT : s ≤ Real.pi / 2 := by linarith [hs.2]
    exact GerverSofa.PartC.Stage2.rhoA_nonneg ⟨hs0, hsT⟩

/-- On a subinterval of a single shifted stage the surface measure of an angular image is the
translated `rhoC`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage (K : ConvexBody Point)
    (hvertexC : ∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
      (edgeVertices K ((s : ℝ) : Real.Angle)).1 = paperGerverContacts (s - Real.pi / 2) 2)
    (j : Fin 5) (a b : ℝ) (hja : Real.pi / 2 + gerverStageTimes j.castSucc ≤ a)
    (hjb : b ≤ Real.pi / 2 + gerverStageTimes j.succ)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt b a with hle | hab
  · have hempty : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      have hx' := hSsub hx
      rw [Set.mem_Ioc] at hx'
      linarith [hx'.1, hx'.2]
    rw [hempty]
    simp
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  have ha0 : Real.pi / 2 ≤ a := le_trans (by linarith [gerverStageTimes_nonneg j.castSucc]) hja
  have hbpi : b ≤ Real.pi := by
    have := gerverStageTimes_le_pi_div_two j.succ
    linarith
  refine surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt K hab (by linarith)
    (fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PC (s - Real.pi / 2)))
    (fun s ↦ rC (s - Real.pi / 2))
    (fun u ↦ GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2)) (fun s ↦ ?_)
    (hcC.comp (continuous_id.sub continuous_const)) ?_ ?_ ?_ S hS hSsub
  · have hinner : HasDerivAt (fun x : ℝ ↦ x - Real.pi / 2) 1 s :=
      (hasDerivAt_id s).sub_const _
    have h1 : HasDerivAt (fun x : ℝ ↦ PC (x - Real.pi / 2))
        (-(rC (s - Real.pi / 2)) • GerverSofa.u (s - Real.pi / 2)) s := by
      simpa [Function.comp_def] using (hPC (s - Real.pi / 2)).scomp s hinner
    have h2 := hasDerivAt_toPlane h1
    rw [toPlane_smul] at h2
    have hangle : tangentVector ((s : ℝ) : Real.Angle) =
        -normalVector (((s - Real.pi / 2 : ℝ)) : Real.Angle) := by
      have h := tangentVector_add_pi_div_two (s - Real.pi / 2)
      rw [show s - Real.pi / 2 + Real.pi / 2 = s from by ring] at h
      exact h
    rw [hangle, smul_neg, ← neg_smul]
    exact h2
  · intro s hs
    rw [hvertexC s ⟨le_trans ha0 hs.1, le_trans hs.2 hbpi⟩]
    exact (hmem (s - Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
  · intro s hs
    exact (hrho (s - Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
  · intro s hs
    have hs0 : (0 : ℝ) ≤ s - Real.pi / 2 := by linarith [hs.1]
    have hsT : s - Real.pi / 2 ≤ Real.pi / 2 := by linarith [hs.2, hbpi]
    exact GerverSofa.PartC.Stage2.rhoC_nonneg ⟨hs0, hsT⟩

/-! ### Exhausting the last stage of the first arc from inside -/

/-- The positive vertex jumps at `π/2`, so the last `rhoA` stage is reached by exhausting its
open interval by half-open subintervals. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_final_stage
    (K : ConvexBody Point)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo (gerverStageTimes 4) (Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have h4T := gerverStageTimes_four_lt_pi_div_two
  have hpos : 0 < Real.pi / 2 - gerverStageTimes 4 := by linarith
  have hbnlt : ∀ n : ℕ, Real.pi / 2 -
      (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) < Real.pi / 2 := by
    intro n
    have h : 0 < (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) := by positivity
    linarith
  refine measure_angleImage_eq_of_iUnion
    (J := fun n : ℕ ↦ Set.Ioc (gerverStageTimes 4)
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2)))
    ?_ (fun n ↦ measurableSet_Ioc) ?_ S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc_right ?_
    have hmn' : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      linarith
    have hd : (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) ≤
        (Real.pi / 2 - gerverStageTimes 4) / ((m : ℝ) + 2) := by
      gcongr
    linarith
  · intro n S' hS' hS'sub
    exact surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 4 _ _
      (le_refl _) (hbnlt n).le (hbnlt n) S' hS' hS'sub
  · intro x hx
    have hx' := hSsub hx
    obtain ⟨n, hn⟩ := exists_nat_gt ((Real.pi / 2 - gerverStageTimes 4) / (Real.pi / 2 - x))
    refine Set.mem_iUnion.2 ⟨n, ⟨hx'.1, ?_⟩⟩
    have h1 : 0 < Real.pi / 2 - x := by linarith [hx'.2]
    rw [div_lt_iff₀ h1] at hn
    have h4 : (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) < Real.pi / 2 - x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [h1]
    linarith

/-! ### Gluing two adjacent arcs -/

/-- Two adjacent windows inside `[0, π/2]` on which the `rhoA` identity holds may be merged. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union (K : ConvexBody Point)
    (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ Real.pi / 2)
    (hI : ∀ S, MeasurableSet S → S ⊆ Set.Icc x y →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S)
    (hJ : ∀ S, MeasurableSet S → S ⊆ Set.Ioc y z →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc x z) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  refine measure_angleImage_eq_of_union (c := -1) (d := Real.pi / 2) (by linarith)
    (I := Set.Icc x y) (J := Set.Ioc y z)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    measurableSet_Icc measurableSet_Ioc ?_ hI hJ S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Icc_union_Ioc_eq_Icc hxy hyz]
    exact hSsub

/-- Two adjacent windows inside `[π/2, π]` on which the `rhoC` identity holds may be merged. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union (K : ConvexBody Point)
    (x y z : ℝ) (hx : Real.pi / 2 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ Real.pi)
    (hI : ∀ S, MeasurableSet S → S ⊆ Set.Ioc x y →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity
          (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S)
    (hJ : ∀ S, MeasurableSet S → S ⊆ Set.Ioc y z →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity
          (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc x z) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  refine measure_angleImage_eq_of_union (c := Real.pi / 2) (d := Real.pi) (by linarith)
    (I := Set.Ioc x y) (J := Set.Ioc y z)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    measurableSet_Ioc measurableSet_Ioc ?_ hI hJ S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Ioc_union_Ioc_eq_Ioc hxy hyz]
    exact hSsub

/-! ### The density identity on each full arc -/

/-- The surface measure of the angular image of any measurable subset of `[0, π/2)` is the
`rhoA`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA (K : ConvexBody Point)
    (hatom0 : surfaceAreaMeasure K {((0 : ℝ) : Real.Angle)} = 0)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ico 0 (Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  have hT0 : gerverStageTimes 0 = 0 := rfl
  have hlt01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_lt_succ 0
  have hlt12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have hlt23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have hlt34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_lt_succ 3
  have h4T := gerverStageTimes_four_lt_pi_div_two
  have h1T : gerverStageTimes 1 < Real.pi / 2 := by linarith
  have h2T : gerverStageTimes 2 < Real.pi / 2 := by linarith
  have h3T : gerverStageTimes 3 < Real.pi / 2 := by linarith
  have h04 : gerverStageTimes 0 ≤ gerverStageTimes 4 := by linarith
  -- the left endpoint carries no atom
  have hzeroA : ∀ S, MeasurableSet S →
      S ⊆ Set.Icc (gerverStageTimes 0) (gerverStageTimes 0) →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
    intro S hS hSsub
    have h1 : surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = 0 := by
      refine measure_mono_null ?_ hatom0
      rintro u ⟨x, hx, rfl⟩
      have hx' := hSsub hx
      rw [Set.Icc_self, Set.mem_singleton_iff, hT0] at hx'
      rw [hx']
      exact rfl
    have h2 : volume.withDensity
        (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S = 0 := by
      refine measure_mono_null hSsub ?_
      rw [Set.Icc_self]
      exact (withDensity_absolutelyContinuous volume _) (measure_singleton _)
    rw [h1, h2]
  -- glue the left endpoint and the first four stages
  have hstep1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 0) (gerverStageTimes 1)
    hT0.ge le_rfl hlt01.le h1T.le hzeroA
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 0 _ _
      (le_refl _) (le_refl _) h1T)
  have hstep2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 1) (gerverStageTimes 2)
    hT0.ge hlt01.le hlt12.le h2T.le hstep1
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 1 _ _
      (le_refl _) (le_refl _) h2T)
  have hstep3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 2) (gerverStageTimes 3)
    hT0.ge (by linarith) hlt23.le h3T.le hstep2
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 2 _ _
      (le_refl _) (le_refl _) h3T)
  have hstep4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 3) (gerverStageTimes 4)
    hT0.ge (by linarith) hlt34.le h4T.le hstep3
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 3 _ _
      (le_refl _) (le_refl _) h4T)
  -- glue the exhausted last stage
  refine measure_angleImage_eq_of_union (c := -1) (d := Real.pi / 2) (by linarith)
    (I := Set.Icc (gerverStageTimes 0) (gerverStageTimes 4))
    (J := Set.Ioo (gerverStageTimes 4) (Real.pi / 2))
    (fun u hu ↦ ⟨by linarith [hu.1, hT0], by linarith [hu.2, h4T]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1, hT0, h04], by linarith [hu.2]⟩)
    measurableSet_Icc measurableSet_Ioo ?_ hstep4
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_final_stage K hvertexA) S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Icc_union_Ioo_eq_Ico h04 h4T, hT0]
    exact hSsub

/-- The surface measure of the angular image of any measurable subset of `(π/2, π]` is the
translated `rhoC`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC (K : ConvexBody Point)
    (hvertexC : ∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
      (edgeVertices K ((s : ℝ) : Real.Angle)).1 = paperGerverContacts (s - Real.pi / 2) 2)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Ioc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  have hT0 : gerverStageTimes 0 = 0 := rfl
  have hT5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have hlt01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_lt_succ 0
  have hlt12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have hlt23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have hlt34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_lt_succ 3
  have hlt45 : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_lt_succ 4
  have hc0 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 0
    (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) (le_refl _) (le_refl _)
  have hc1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 1
    (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) (le_refl _) (le_refl _)
  have hc2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 2
    (Real.pi / 2 + gerverStageTimes 2) (Real.pi / 2 + gerverStageTimes 3) (le_refl _) (le_refl _)
  have hc3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 3
    (Real.pi / 2 + gerverStageTimes 3) (Real.pi / 2 + gerverStageTimes 4) (le_refl _) (le_refl _)
  have hc4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 4
    (Real.pi / 2 + gerverStageTimes 4) (Real.pi / 2 + gerverStageTimes 5) (le_refl _) (le_refl _)
  have hstep1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 2]) hc0 hc1
  have hstep2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 2) (Real.pi / 2 + gerverStageTimes 3)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 3]) hstep1 hc2
  have hstep3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 3) (Real.pi / 2 + gerverStageTimes 4)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 4]) hstep2 hc3
  have hstep4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 4) (Real.pi / 2 + gerverStageTimes 5)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 5]) hstep3 hc4
  refine hstep4 S hS ?_
  rw [hT0, hT5, add_zero]
  exact hSsub

theorem gerver_surface_densities :
    ∃ K : RightAngleCapSpace,
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      ∃ r s : ℝ → ℝ≥0, HasCapDensities K r s ∧
        (∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          (r t : ℝ) ≤ M ∧ (s t : ℝ) ≤ M) ∧
        (∀ i : Fin 5, ∀ t ∈ Set.Ioo (gerverStageTimes i.castSucc) (gerverStageTimes i.succ),
          HasDerivAt (fun u ↦ paperGerverContacts u 0)
            ((r t : ℝ) • tangentVector (t : Real.Angle)) t ∧
          HasDerivAt (fun u ↦ paperGerverContacts u 2)
            (-(s t : ℝ) • normalVector (t : Real.Angle)) t) := by
  obtain ⟨K, hKcap, hatom0, hvertexA, hvertexC⟩ := exists_gerverCap_positiveVertex
  obtain ⟨M, hM⟩ := exists_bound_rhoA_rhoC
  refine ⟨K, hKcap, fun t ↦ Real.toNNReal (GerverSofa.PartC.Stage2.rhoA t),
    fun t ↦ Real.toNNReal (GerverSofa.PartC.Stage2.rhoC t),
    ⟨measurable_real_toNNReal.comp measurable_rhoA,
      measurable_real_toNNReal.comp measurable_rhoC, ?_, ?_⟩,
    ⟨max M 0, fun t ht ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · exact surfaceAreaMeasure_restrict_eq_map_withDensity measurableSet_Ico
      (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA K.val hatom0 hvertexA)
  · rw [show Set.Ioc (Real.pi / 2) Real.pi =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2) from by
        rw [show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]]
    exact surfaceAreaMeasure_restrict_eq_map_add_withDensity
      (surfaceAreaMeasure_angleImage_eq_withDensity_rhoC K.val hvertexC)
  · rw [Real.coe_toNNReal']
    exact max_le_max (hM t ht).1 le_rfl
  · rw [Real.coe_toNNReal']
    exact max_le_max (hM t ht).2 le_rfl
  · intro i t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨le_trans (gerverStageTimes_nonneg _) ht.1.le,
        le_trans ht.2.le (gerverStageTimes_le_pi_div_two _)⟩
    obtain ⟨hA, hC⟩ := hasDerivAt_paperGerverContacts_of_mem_stage i ht
    rw [Real.coe_toNNReal _ (GerverSofa.PartC.Stage2.rhoA_nonneg htIcc),
      Real.coe_toNNReal _ (GerverSofa.PartC.Stage2.rhoC_nonneg htIcc)]
    exact ⟨hA, hC⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Velocity And Cap Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem gerver_strict_velocity (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (paperGerverVelocityComponents t).1 < 0 ∧ 0 < (paperGerverVelocityComponents t).2 ∧
    inner ℝ (deriv paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
    0 < inner ℝ (deriv paperGerverPath t) (tangentVector (t : Real.Angle)) := by
  open GerverSofa.Romik in
  -- The certified direct parameter vector, its box enclosures and its equations.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, -, -, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := hthetaeq.trans selected_theta
  have hphi0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have ha2 : p.a2 = -(1 / 4 : ℝ) := a2_eq_neg_quarter_of_equations heqs
  have he1 : p.e1 = p.a1 := e1_eq_a1_of_equations heqs
  have he2 : p.e2 = -p.a2 := e2_eq_neg_a2_of_equations heqs
  have hbox : p ∈ GerverSofa.Romik.box := hmem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ha1lo, -, -, -, hb1lo, hb1hi, hb2lo, -, hc1lo, -, hc2lo, -, hd1lo, -, hd2lo, -,
      -, -, -, -, -, hphihi, -, hthetahi⟩ := hbox
  have ha1 : (6 : ℝ) / 5 ≤ p.a1 := le_trans (by norm_num) ha1lo
  have hb1u : p.b1 ≤ -(1 / 2 : ℝ) := le_trans hb1hi (by norm_num)
  have hb1l : -(53 / 100 : ℝ) ≤ p.b1 := le_trans (by norm_num) hb1lo
  have hb2 : (9 : ℝ) / 10 ≤ p.b2 := le_trans (by norm_num) hb2lo
  have hc1 : (3 : ℝ) / 5 ≤ p.c1 := le_trans (by norm_num) hc1lo
  have hc2 : (-1 : ℝ) ≤ p.c2 := le_trans (by norm_num) hc2lo
  have hd1 : (13 : ℝ) / 10 ≤ p.d1 := le_trans (by norm_num) hd1lo
  have hd2 : -(53 / 100 : ℝ) ≤ p.d2 := le_trans (by norm_num) hd2lo
  have hphiu : p.phi ≤ (1 : ℝ) / 20 := le_trans hphihi (by norm_num)
  have hthetau : p.theta ≤ (7 : ℝ) / 10 := le_trans hthetahi (by norm_num)
  have hpilo : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpihi : Real.pi < (63 : ℝ) / 20 := by linarith only [Real.pi_lt_d2]
  -- The two strict first-phase estimates, also used on the reflected fifth phase.
  have hkeyA : ∀ s : ℝ, 0 ≤ s → s ≤ (1 : ℝ) / 20 →
      (alphaBeta1 p s).1 ≤ -(2 * s) := by
    intro s hs0 hs20
    have hspi : s ≤ Real.pi := by linarith only [hs20, hpilo]
    have hsin0 : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs0 hspi
    have hsinlo : s - s ^ 3 / 6 ≤ Real.sin s := Real.sin_ge_sub_cube hs0
    have hcoslo : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
    have hmul : (12 / 5 : ℝ) * Real.sin s ≤ 2 * p.a1 * Real.sin s := by
      nlinarith only [ha1, hsin0]
    have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) := mul_nonneg hs0 (by linarith only [hs20])
    have hcube : 0 ≤ s ^ 2 * ((1 / 20 : ℝ) - s) :=
      mul_nonneg (sq_nonneg s) (by linarith only [hs20])
    dsimp [alphaBeta1]
    rw [ha2]
    linarith only [hmul, hsinlo, hcoslo, hquad, hcube, hs0]
  have hkeyB : ∀ s : ℝ, 0 ≤ s → s ≤ (1 : ℝ) / 20 →
      (343 : ℝ) / 250 ≤ (alphaBeta1 p s).2 := by
    intro s hs0 hs20
    have hspi : s ≤ Real.pi := by linarith only [hs20, hpilo]
    have hsinhi : Real.sin s ≤ s := Real.sin_le hs0
    have hcoslo : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
    have hcos0 : 0 ≤ Real.cos s :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hs0, hpilo], by linarith only [hs20, hpilo]⟩
    have hmul : (12 / 5 : ℝ) * Real.cos s ≤ 2 * p.a1 * Real.cos s := by
      nlinarith only [ha1, hcos0]
    have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) := mul_nonneg hs0 (by linarith only [hs20])
    dsimp [alphaBeta1]
    rw [ha2]
    linarith only [hmul, hsinhi, hcoslo, hquad, hs0, hs20]
  -- The fifth phase is the reflection of the first one through the angle `π/4`.
  have hrefl : ∀ s : ℝ, alphaBeta5 p (Real.pi / 2 - s) =
      (-(alphaBeta1 p s).2, -(alphaBeta1 p s).1) := by
    intro s
    dsimp [alphaBeta5, alphaBeta1]
    rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, he1, he2]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  -- The five closed stage intervals in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hval := paperGerverContactData_properties.2.2.2
  have hmain : (paperGerverVelocityComponents t).1 < 0 ∧
      0 < (paperGerverVelocityComponents t).2 := by
    rcases le_or_gt t p.phi with hs1 | hs1
    · -- Phase 1: `α ≤ -2t < 0` and `β ≥ 343/250 > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta1 p t := by
        rw [hval 0 t (by rw [hI0]; exact ⟨ht.1.le, hs1⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htu : t ≤ (1 : ℝ) / 20 := le_trans hs1 hphiu
      rw [hv]
      exact ⟨by linarith only [hkeyA t ht.1.le htu, ht.1],
        by linarith only [hkeyB t ht.1.le htu]⟩
    rcases le_or_gt t p.theta with hs2 | hs2
    · -- Phase 2: `α ≤ -t < 0` and `β ≥ 1813/2000 > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta2 p t := by
        rw [hval 1 t (by rw [hI1]; exact ⟨hs1.le, hs2⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htu : t ≤ (7 : ℝ) / 10 := le_trans hs2 hthetau
      have hbt : 0 ≤ (p.b1 + 53 / 100) * t := mul_nonneg (by linarith only [hb1l]) ht.1.le
      have hst : 0 ≤ ((7 : ℝ) / 10 - t) * t := mul_nonneg (by linarith only [htu]) ht.1.le
      rw [hv]
      dsimp [alphaBeta2]
      exact ⟨by linarith only [hb1u, ht.1], by linarith only [hb2, hbt, hst, htu]⟩
    rcases le_or_gt t (Real.pi / 2 - p.theta) with hs3 | hs3
    · -- Phase 3: `α ≤ -t < 0` and `β ≥ 8/5 - t > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta3 p t := by
        rw [hval 2 t (by rw [hI2]; exact ⟨hs2.le, hs3⟩)]
        simp [gerverBranchVelocityComponents, hp]
      rw [hv]
      dsimp [alphaBeta3]
      exact ⟨by linarith only [hc2, ht.1], by linarith only [hc1, ht.2, hpihi]⟩
    rcases le_or_gt t (Real.pi / 2 - p.phi) with hs4 | hs4
    · -- Phase 4: `-α > 69/100 > 0` and `β ≥ 8/5 - t > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta4 p t := by
        rw [hval 3 t (by rw [hI3]; exact ⟨hs3.le, hs4⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htlo : (4 : ℝ) / 5 < t := by linarith only [hs3, hthetau, hpilo]
      have hthi : t < (8 : ℝ) / 5 := by linarith only [ht.2, hpihi]
      have hcoef : (9 : ℝ) / 10 ≤ p.d1 - t / 4 := by linarith only [hd1, hthi]
      have hprod : (18 : ℝ) / 25 < t * (p.d1 - t / 4) := by nlinarith only [htlo, hcoef]
      rw [hv]
      dsimp [alphaBeta4]
      exact ⟨by linarith only [hprod, hd2], by linarith only [hd1, hthi]⟩
    · -- Phase 5: the reflected first-phase estimates at `s = π/2 - t ∈ (0, φ]`.
      have hv : paperGerverVelocityComponents t = alphaBeta5 p t := by
        rw [hval 4 t (by rw [hI4]; exact ⟨hs4.le, ht.2.le⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have hs0 : 0 < Real.pi / 2 - t := by linarith only [ht.2]
      have hsu : Real.pi / 2 - t ≤ (1 : ℝ) / 20 := by linarith only [hs4, hphiu]
      have hA := hkeyA (Real.pi / 2 - t) hs0.le hsu
      have hB := hkeyB (Real.pi / 2 - t) hs0.le hsu
      have h5 := hrefl (Real.pi / 2 - t)
      rw [show Real.pi / 2 - (Real.pi / 2 - t) = t by ring] at h5
      have hfst : (alphaBeta5 p t).1 = -(alphaBeta1 p (Real.pi / 2 - t)).2 := by rw [h5]
      have hsnd : (alphaBeta5 p t).2 = -(alphaBeta1 p (Real.pi / 2 - t)).1 := by rw [h5]
      rw [hv, hfst, hsnd]
      exact ⟨by linarith only [hB], by linarith only [hA, hs0]⟩
  exact ⟨hmain.1, hmain.2, hmain.1, hmain.2⟩

/-- The tangential velocity component is nonpositive on the whole closed rotation interval:
the strict inequality of `gerver_strict_velocity` holds on the open interval, and the
component is continuous, so the closed condition propagates to the two endpoints. -/
theorem paperGerverVelocityComponents_fst_nonpos {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : (paperGerverVelocityComponents t).1 ≤ 0 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcl : IsClosed {s : ℝ | (paperGerverVelocityComponents s).1 ≤ 0} :=
    isClosed_le (continuous_fst.comp paperGerverContactData_properties.1) continuous_const
  have h := closure_minimal
    (fun s hs => (gerver_strict_velocity s hs).1.le : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ _) hcl
  rw [closure_Ioo hpi.ne] at h
  exact h ht

/-- The normal velocity component is nonnegative on the whole closed rotation interval; see
`paperGerverVelocityComponents_fst_nonpos` for the argument. -/
theorem paperGerverVelocityComponents_snd_nonneg {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ (paperGerverVelocityComponents t).2 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcl : IsClosed {s : ℝ | 0 ≤ (paperGerverVelocityComponents s).2} :=
    isClosed_le continuous_const (continuous_snd.comp paperGerverContactData_properties.1)
  have h := closure_minimal
    (fun s hs => (gerver_strict_velocity s hs).2.1.le : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ _) hcl
  rw [closure_Ioo hpi.ne] at h
  exact h ht

theorem gerver_cap_area_lower_bound :
    2 * GerverSofa.PartB.params.a1 ≤ ClassicalResults.area gerverOuterCap ∧
    (12 : ℝ) / 5 ≤ 2 * GerverSofa.PartB.params.a1 ∧ (11 : ℝ) / 5 < 12 / 5 := by
  open GerverSofa.Romik in
  -- The certified direct parameter vector, its box enclosures and its equations.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  rw [hp]
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have h0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphieq, hthetaeq]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [hthetaeq]; exact hthetalt
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbox : p ∈ GerverSofa.Romik.box := hmem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk51lo, hk51hi, -, -,
      ha1lo, ha1hi, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -⟩ := hbox
  have ha1 : (6 : ℝ) / 5 ≤ p.a1 := le_trans (by norm_num) ha1lo
  have ha1' : p.a1 ≤ (61 : ℝ) / 50 := le_trans ha1hi (by norm_num)
  have hk51 : -(51 : ℝ) / 50 ≤ p.k51 := le_trans (by norm_num) hk51lo
  have hk51' : p.k51 ≤ -1 := le_trans hk51hi (by norm_num)
  have ha2 : p.a2 = -(1 / 4 : ℝ) := a2_eq_neg_quarter_of_equations heqs
  have he1 : p.e1 = p.a1 := e1_eq_a1_of_equations heqs
  have he2 : p.e2 = -p.a2 := e2_eq_neg_a2_of_equations heqs
  have hk52 : p.k52 = (1 / 4 : ℝ) := k52_eq_quarter_of_equations heqs
  -- The two path endpoints: `x(0) = 0` and `x(π/2) = (1 - a₁ + k₅₁, 0)`.
  obtain ⟨-, hzero, -⟩ := gerver_direct_path_regularity p hmem heqs
  have hpath0 : paperGerverPath 0 = 0 := by
    change GerverSofa.PartF.Coordinates.toPlane (path GerverSofa.PartB.params 0) = 0
    rw [hp, hzero]
    ext i
    fin_cases i <;> rfl
  have hpathT : path p (Real.pi / 2) = (1 - p.a1 + p.k51, 0) := by
    rw [path_eq_path5_of_mem_Icc heqs h1 h2 ⟨by linarith, le_rfl⟩]
    simp only [path5, addK, rot, Real.cos_pi_div_two, Real.sin_pi_div_two, he1, he2, ha2, hk52,
      Prod.mk.injEq]
    constructor <;> ring
  have hxT0 : paperGerverPath (Real.pi / 2) 0 = 1 - p.a1 + p.k51 := by
    change (path GerverSofa.PartB.params (Real.pi / 2)).1 = _
    rw [hp, hpathT]
  have hxT1 : paperGerverPath (Real.pi / 2) 1 = 0 := by
    change (path GerverSofa.PartB.params (Real.pi / 2)).2 = _
    rw [hp, hpathT]
  -- The velocity components at the two endpoints.
  have hvel := paperGerverContactData_properties.2.2.2
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have halpha0 : (paperGerverVelocityComponents 0).1 = 0 := by
    rw [hvel 0 0 (by rw [hI0]; exact ⟨le_rfl, h0.le⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta1, ha2]
    norm_num
  have hbeta0 : (paperGerverVelocityComponents 0).2 = 2 * p.a1 - 1 := by
    rw [hvel 0 0 (by rw [hI0]; exact ⟨le_rfl, h0.le⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta1, ha2]
  have halphaT : (paperGerverVelocityComponents (Real.pi / 2)).1 = 1 - 2 * p.a1 := by
    rw [hvel 4 (Real.pi / 2) (by rw [hI4]; exact ⟨by linarith, le_rfl⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta5, he1]
  have hbetaT : (paperGerverVelocityComponents (Real.pi / 2)).2 = 0 := by
    rw [hvel 4 (Real.pi / 2) (by rw [hI4]; exact ⟨by linarith, le_rfl⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta5, he2, ha2]
    norm_num
  -- The four displayed cap contacts, in coordinates.
  have hpteq : ∀ z w : Point, z 0 = w 0 → z 1 = w 1 → z = w := by
    intro z w hz hw
    ext i
    fin_cases i
    · exact hz
    · exact hw
  have hA0 : paperGerverContacts 0 0 = (!₂[1, 0] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, halpha0, hpath0]
  have hC0 : paperGerverContacts 0 2 = (!₂[1 - 2 * p.a1, 1] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, hbeta0, hpath0]
  have hAT : paperGerverContacts (Real.pi / 2) 0 = (!₂[p.a1 + p.k51, 1] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, halphaT, hxT0, hxT1]
    ring
  have hCT : paperGerverContacts (Real.pi / 2) 2 = (!₂[p.k51 - p.a1, 0] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, hbetaT, hxT0, hxT1]
    ring
  -- The cap is a convex body, so it is convex and of finite area.
  obtain ⟨-, -, -, -, -, ⟨K, hKset, -⟩, -⟩ := gerver_capSupport_identification
  have hconv : Convex ℝ gerverOuterCap := hKset ▸ K.val.convex'
  have hcomp : IsCompact gerverOuterCap := hKset ▸ K.val.isCompact'
  -- The inscribed trapezoid and its area.
  have hsub := EuclideanSpace.horizontalTrapezoid_subset_of_convex hconv
    (l₀ := p.k51 - p.a1) (r₀ := 1) (l₁ := 1 - 2 * p.a1) (r₁ := p.a1 + p.k51)
    (hCT ▸ gerver_outer_contact_C (Real.pi / 2) ⟨by positivity, le_rfl⟩)
    (hA0 ▸ gerver_outer_contact_A 0 ⟨le_rfl, by positivity⟩)
    (hC0 ▸ gerver_outer_contact_C 0 ⟨le_rfl, by positivity⟩)
    (hAT ▸ gerver_outer_contact_A (Real.pi / 2) ⟨by positivity, le_rfl⟩)
  have hvol := EuclideanSpace.volume_horizontalTrapezoid (l₀ := p.k51 - p.a1) (r₀ := 1)
    (l₁ := 1 - 2 * p.a1) (r₁ := p.a1 + p.k51) (by linarith) (by linarith)
  have hkey : ENNReal.ofReal (2 * p.a1) ≤ MeasureTheory.volume gerverOuterCap := by
    rw [show (2 * p.a1 : ℝ) =
      (1 - (p.k51 - p.a1) + (p.a1 + p.k51 - (1 - 2 * p.a1))) / 2 by ring, ← hvol]
    exact MeasureTheory.measure_mono hsub
  refine ⟨?_, by linarith, by norm_num⟩
  rw [ClassicalResults.area]
  exact (ENNReal.ofReal_le_iff_le_toReal hcomp.measure_lt_top.ne).1 hkey

end MovingSofa

end

end

end
