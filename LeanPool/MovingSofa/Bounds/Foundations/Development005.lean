/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development007
public import LeanPool.MovingSofa.Convex.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Bounds.MonotonicityIntervals`.
* `Bounds.WedgeEndpoints`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-! # Monotonicity intervals for the distinguished cap sides

`cap_tail_monotonicity_intervals` records that on the right interval
`(φ, π/2]` the inner corner has left the distinguished right half-plane, and
that inside that half-plane the inner quadrant is cut out by the single inner
wall `b(t)`; symmetrically on `[0, π/2 - φ)` for the left side.  Intersecting
with the fan gives the two wedge forms.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem capInnerCorner_right_projection_neg (K : SpecialCapSpace) :
    ∀ t ∈ Set.Ioc GerversSofa.φ (Real.pi / 2),
     inner ℝ (capInnerCorner K.val t - capInnerCorner K.val GerversSofa.φ)
       (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) < 0 := by
  have hpi := Real.pi_pos
  have hφ0 : (0 : ℝ) ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
  have hφ4 : GerversSofa.φ ≤ Real.pi / 4 :=
    le_trans GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.1
      GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.2.1
  -- the injectivity condition: a continuously differentiable corner with strict interior signs
  obtain ⟨-, hcd, hsign⟩ := K.2.1
  set D : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) with hDdef
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (D s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs => (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  have hsub : Set.Icc GerversSofa.φ (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Icc_subset_Icc hφ0 le_rfl
  have hanti : StrictAntiOn
      (fun s : ℝ ↦ inner ℝ (capInnerCorner K.val s)
        (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
      (Set.Icc GerversSofa.φ (Real.pi / 2)) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      ((hcont.mono hsub).inner continuousOn_const)
      (f' := fun s ↦ inner ℝ (D s) (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
      ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      have hsub' : Set.Ioo GerversSofa.φ (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        fun z hz => ⟨hφ0.trans hz.1.le, hz.2.le⟩
      simpa using
        ((hdw s (hsub' hs)).mono hsub').inner ℝ
          (hasDerivWithinAt_const s _
            (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨hα, hβ⟩ := hsign s ⟨hφ0.trans_lt hs1, hs2⟩
      rw [inner_normalVector_eq_frame_rotate (D s) s GerversSofa.φ]
      have hcos : 0 < Real.cos (s - GerversSofa.φ) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hsin : 0 < Real.sin (s - GerversSofa.φ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      nlinarith
  intro t ht
  have h := hanti ⟨le_rfl, le_trans hφ4 (by linarith)⟩ ⟨ht.1.le, ht.2⟩ ht.1
  rw [inner_sub_left]
  simpa using h

private theorem capInnerCorner_left_projection_neg (K : SpecialCapSpace) :
    ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2 - GerversSofa.φ),
     inner ℝ (capInnerCorner K.val t -
         capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
       (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) < 0 := by
  have hpi := Real.pi_pos
  have hφ0 : (0 : ℝ) ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
  have hφ4 : GerversSofa.φ ≤ Real.pi / 4 :=
    le_trans GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.1
      GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.2.1
  -- the injectivity condition: a continuously differentiable corner with strict interior signs
  obtain ⟨-, hcd, hsign⟩ := K.2.1
  set D : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) with hDdef
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (D s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs => (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2 - GerversSofa.φ) ⊆
      Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Icc_subset_Icc le_rfl (by linarith)
  have hmono : StrictMonoOn
      (fun s : ℝ ↦ inner ℝ (capInnerCorner K.val s)
        (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
      (Set.Icc (0 : ℝ) (Real.pi / 2 - GerversSofa.φ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      ((hcont.mono hsub).inner continuousOn_const)
      (f' := fun s ↦ inner ℝ (D s)
        (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
      ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      have hsub' : Set.Ioo (0 : ℝ) (Real.pi / 2 - GerversSofa.φ) ⊆
          Set.Icc (0 : ℝ) (Real.pi / 2) := fun z hz => ⟨hz.1.le, by linarith [hz.2]⟩
      simpa using
        ((hdw s (hsub' hs)).mono hsub').inner ℝ
          (hasDerivWithinAt_const s _
            (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨hα, hβ⟩ := hsign s ⟨hs1, by linarith⟩
      rw [inner_tangentVector_eq_frame_rotate (D s) s (Real.pi / 2 - GerversSofa.φ)]
      have hcos : 0 < Real.cos (s - (Real.pi / 2 - GerversSofa.φ)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hsin : Real.sin (s - (Real.pi / 2 - GerversSofa.φ)) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
      nlinarith
  intro t ht
  have h := hmono ⟨ht.1, ht.2.le⟩ ⟨by linarith, le_rfl⟩ ht.2
  rw [inner_sub_left]
  simpa using h

theorem cap_tail_monotonicity_intervals (K : SpecialCapSpace) :
    (∀ t ∈ Set.Ioc paperGerverConstants.2.1 (Real.pi / 2),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).1.upperHalfPlane ∧
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).1.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) paperGerverConstants.2.2,
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).2.upperHalfPlane ∧
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).2.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).2) ∧
    (∀ t ∈ Set.Ioc paperGerverConstants.2.1 (Real.pi / 2),
      t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ capWedge K.val t =
        ((distinguishedCapSides K.val).1.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val t).1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) paperGerverConstants.2.2,
      t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ capWedge K.val t =
        ((distinguishedCapSides K.val).2.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val t).2) := by
  have hpi := Real.pi_pos
  have hφ0 : (0 : ℝ) ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
  have hφ4 : GerversSofa.φ ≤ Real.pi / 4 :=
    le_trans GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.1
      GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.2.1
  -- frame coordinates of the inner corner path
  have hxu := inner_capInnerCorner_normalVector K.val
  have hxv := inner_capInnerCorner_tangentVector K.val
  -- membership descriptions relative to the moving corner
  have hHb : ∀ (t : ℝ) (p : Point), p ∈ (innerWallUpperHalfPlanes K.val t).1 ↔
      0 ≤ inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) := by
    intro t p
    rw [inner_sub_left, hxu]
    show (supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 ≤
      inner ℝ p (normalVector (t : Real.Angle))) ↔ _
    constructor <;> intro hp <;> linarith
  have hHd : ∀ (t : ℝ) (p : Point), p ∈ (innerWallUpperHalfPlanes K.val t).2 ↔
      0 ≤ inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) := by
    intro t p
    rw [inner_sub_left, hxv]
    show (supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) ↔ _
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
    constructor <;> intro hp <;> linarith
  have hQ : ∀ (t : ℝ) (p : Point), p ∈ innerQuadrant (K.val.val : Set Point) t ↔
      inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) < 0 ∧
        inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) < 0 := by
    intro t p
    rw [inner_sub_left, inner_sub_left, hxu, hxv]
    show (inner ℝ p (normalVector (t : Real.Angle)) <
        supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ↔ _
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hfan : capFan (Real.pi / 2) = {p : Point | 0 ≤ p 1} := by
    ext p
    have hval : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = p 1 := by
      simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    constructor
    · intro hp
      have := hp.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
      rw [hval] at this
      exact this
    · intro hp
      have hp' : (0 : ℝ) ≤ p 1 := hp
      exact ⟨by change 0 ≤ inner ℝ p _; rw [hval]; exact hp',
        by change 0 ≤ inner ℝ p _; rw [hval]; exact hp'⟩
  have hwedge : ∀ t : ℝ, capWedge K.val t =
      {p : Point | 0 ≤ p 1} ∩ innerQuadrant (K.val.val : Set Point) t := by
    intro t
    have hiq : (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerQuadrant =
        innerQuadrant (K.val.val : Set Point) t := by
      rw [(rotatingHallwayParts_formulas (K.val.val : Set Point)
        (t : Real.Angle)).2.2.2.2.2.2.2.2, innerQuadrant, ← Real.Angle.coe_add]
    show capFan (Real.pi / 2) ∩
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerQuadrant = _
    rw [hfan, hiq]
  -- monotone comparison of the corner path against the two distinguished frames
  have hkeyR := capInnerCorner_right_projection_neg K
  have hkeyL := capInnerCorner_left_projection_neg K
  -- the right-hand quadrant identity, at all quadrant times
  have partR : ∀ t ∈ Set.Ioc GerversSofa.φ (Real.pi / 2),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).1.upperHalfPlane ∧
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).1.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).1 := by
    intro t ht
    have hR := hkeyR t ht
    have hside : (distinguishedCapSides K.val).1.upperHalfPlane =
        (innerWallUpperHalfPlanes K.val GerversSofa.φ).1 := rfl
    have hcos : 0 ≤ Real.cos (t - GerversSofa.φ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsin : 0 ≤ Real.sin (t - GerversSofa.φ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
    rw [hside]
    constructor
    · intro hmem
      exact absurd ((hHb _ _).mp hmem) (not_le.mpr hR)
    refine Set.Subset.antisymm ?_ ?_
    · rintro p ⟨hA, hQp⟩
      refine ⟨hA, ?_⟩
      rw [hHb t p]
      exact not_le.mpr ((hQ t p).mp hQp).1
    · rintro p ⟨hA, hH⟩
      refine ⟨hA, ?_⟩
      rw [hQ t p]
      have ha : inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) < 0 :=
        not_le.mp fun h => hH ((hHb t p).mpr h)
      refine ⟨ha, ?_⟩
      by_contra hb
      rw [not_lt] at hb
      have hAmem : 0 ≤ inner ℝ (p - capInnerCorner K.val GerversSofa.φ)
          (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) := (hHb _ p).mp hA
      have hsplit : inner ℝ (p - capInnerCorner K.val GerversSofa.φ)
            (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) =
          inner ℝ (p - capInnerCorner K.val t)
              (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) +
            inner ℝ (capInnerCorner K.val t - capInnerCorner K.val GerversSofa.φ)
              (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) := by
        rw [← inner_add_left]
        congr 1
        abel
      have hle : inner ℝ (p - capInnerCorner K.val t)
          (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) ≤ 0 := by
        rw [inner_normalVector_eq_frame_rotate (p - capInnerCorner K.val t) t GerversSofa.φ]
        linarith [mul_nonneg hb hsin, mul_nonneg (neg_nonneg.mpr ha.le) hcos]
      linarith
  -- the left-hand quadrant identity, at all quadrant times
  have partL : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2 - GerversSofa.φ),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).2.upperHalfPlane ∧
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).2.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).2 := by
    intro t ht
    have hL := hkeyL t ht
    have hside : (distinguishedCapSides K.val).2.upperHalfPlane =
        (innerWallUpperHalfPlanes K.val (Real.pi / 2 - GerversSofa.φ)).2 := rfl
    have hcos : 0 ≤ Real.cos (t - (Real.pi / 2 - GerversSofa.φ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsin : Real.sin (t - (Real.pi / 2 - GerversSofa.φ)) ≤ 0 := by
      have hpos : 0 ≤ Real.sin (Real.pi / 2 - GerversSofa.φ - t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1])
      rw [show t - (Real.pi / 2 - GerversSofa.φ) =
        -(Real.pi / 2 - GerversSofa.φ - t) by ring, Real.sin_neg]
      linarith
    rw [hside]
    constructor
    · intro hmem
      exact absurd ((hHd _ _).mp hmem) (not_le.mpr hL)
    refine Set.Subset.antisymm ?_ ?_
    · rintro p ⟨hA, hQp⟩
      refine ⟨hA, ?_⟩
      rw [hHd t p]
      exact not_le.mpr ((hQ t p).mp hQp).2
    · rintro p ⟨hA, hH⟩
      refine ⟨hA, ?_⟩
      rw [hQ t p]
      have hb : inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) < 0 :=
        not_le.mp fun h => hH ((hHd t p).mpr h)
      refine ⟨?_, hb⟩
      by_contra ha
      rw [not_lt] at ha
      have hAmem : 0 ≤ inner ℝ
          (p - capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) := (hHd _ p).mp hA
      have hsplit : inner ℝ (p - capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
            (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) =
          inner ℝ (p - capInnerCorner K.val t)
              (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) +
            inner ℝ (capInnerCorner K.val t -
                capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
              (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) := by
        rw [← inner_add_left]
        congr 1
        abel
      have hle : inner ℝ (p - capInnerCorner K.val t)
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) ≤ 0 := by
        rw [inner_tangentVector_eq_frame_rotate (p - capInnerCorner K.val t) t
          (Real.pi / 2 - GerversSofa.φ)]
        linarith [mul_nonneg ha (neg_nonneg.mpr hsin),
          mul_nonneg (neg_nonneg.mpr hb.le) hcos]
      linarith
  -- the wedge identities are the quadrant identities intersected with the fan
  refine ⟨partR, partL, ?_, ?_⟩
  · intro t ht _
    rw [hwedge t, Set.inter_left_comm, (partR t ht).2]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto
  · intro t ht _
    rw [hwedge t, Set.inter_left_comm, (partL t ht).2]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto

/-- On any subinterval of `[0, π/2]` the inner corner of a special cap has strictly decreasing
horizontal coordinate: the injectivity condition makes its horizontal derivative negative. -/
theorem strictAntiOn_capInnerCorner_fst (K : SpecialCapSpace) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    StrictAntiOn (fun t ↦ capInnerCorner K.val t 0) (Set.Icc a b) := by
  obtain ⟨-, hcd, hsign⟩ := K.property.1
  set Dv : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2))
  have hIccsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  have hIoosub : Set.Ioo a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1.le, le_trans ht.2.le hb⟩
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (Dv s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs ↦ (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  have hinner0 : ∀ p : Point, inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) = p 0 := by
    intro p
    rw [inner_normalVector_real]
    simp
  have hmono0 : StrictAntiOn
      (fun t ↦ inner ℝ (capInnerCorner K.val t) (normalVector ((0 : ℝ) : Real.Angle)))
      (Set.Icc a b) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      ((hcont.mono hIccsub).inner continuousOn_const)
      (f' := fun s ↦ inner ℝ (Dv s) (normalVector ((0 : ℝ) : Real.Angle))) ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      simpa using ((hdw s (hIoosub hs)).mono hIoosub).inner ℝ
        (hasDerivWithinAt_const s _ (normalVector ((0 : ℝ) : Real.Angle)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hα, hβ⟩ := hsign s ⟨lt_of_le_of_lt ha hs.1, lt_of_lt_of_le hs.2 hb⟩
      rw [inner_normalVector_eq_frame_rotate (Dv s) s 0]
      have hcos : 0 < Real.cos (s - 0) := by
        rw [sub_zero]
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos, hs.1, ha],
          by linarith only [hs.2, hb]⟩
      have hsin : 0 < Real.sin (s - 0) := by
        rw [sub_zero]
        exact Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_lt ha hs.1)
          (by linarith only [hs.2, hb, Real.pi_pos])
      have h1 : inner ℝ (Dv s) (normalVector (s : Real.Angle)) * Real.cos (s - 0) < 0 :=
        mul_neg_of_neg_of_pos hα hcos
      have h2 : 0 < inner ℝ (Dv s) (tangentVector (s : Real.Angle)) * Real.sin (s - 0) :=
        mul_pos hβ hsin
      linarith only [h1, h2]
  intro u hu w hw huw
  simpa only [hinner0] using hmono0 hu hw huw

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
# Bounds / Wedge Endpoints
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem wedgeGaps_positive_lower_bound {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 ω) :
    (1 - Real.sin t) / Real.cos t ≤ (wedgeGaps K t).1 ∧
    0 < (1 - Real.sin t) / Real.cos t ∧
    (1 - Real.sin (ω - t)) / Real.cos (ω - t) ≤ (wedgeGaps K t).2 ∧
    0 < (1 - Real.sin (ω - t)) / Real.cos (ω - t) := by
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsint_lt : Real.sin t < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hcost]
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩
  have hsinδ_lt : Real.sin (ω - t) < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq (ω - t), sq_pos_of_pos hcosδ]
  have hbounds := K.supportValue_upper_bounds ht
  have hC := (edgeVertices_fst_mem K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)).2
  change inner ℝ (capVertices K ω).2.1
      (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp [normalVector, frame, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two] at hC
  change inner ℝ (capVertices K ω).2.1 (tangentVector (ω : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  have hgap₁ := wedgeGaps_fst_eq_supportValue K t
  have hgap₂ : (wedgeGaps K t).2 =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t) := by
    simp only [wedgeGaps, wedgeEndpoints, inner_sub_left,
      real_inner_smul_left, hC]
    rw [inner_tangentVector_self]
    ring
  rw [hgap₁, hgap₂]
  refine ⟨?_, div_pos (sub_pos.mpr hsint_lt) hcost, ?_,
    div_pos (sub_pos.mpr hsinδ_lt) hcosδ⟩
  · apply (div_le_iff₀ hcost).2
    rw [sub_mul, div_mul_cancel₀ _ hcost.ne']
    nlinarith [hbounds.1]
  · apply (div_le_iff₀ hcosδ).2
    rw [sub_mul, div_mul_cancel₀ _ hcosδ.ne']
    nlinarith [hbounds.2]

/-- Base points between the horizontal extrema of a right-angle cap lie in the cap. -/
private theorem smul_normalVector_zero_mem_of_rightAngleCap (K : RightAngleCapSpace) {x : ℝ}
    (hlo : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤ x)
    (hhi : x ≤ supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle)) :
    x • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
  obtain ⟨A, hA, hAeq⟩ := exists_mem_inner_eq_supportValue K.val ((0 : ℝ) : Real.Angle)
  obtain ⟨C, hC, hCeq⟩ := exists_mem_inner_eq_supportValue K.val ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_zero] at hAeq
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hCeq
  have hzero : inner ℝ (x • normalVector (0 : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_smul_normalVector_zero, Real.cos_pi_div_two, mul_zero]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨le_of_eq hzero.symm, le_of_eq hzero.symm⟩ ?_
  intro t ht
  have htI : 0 ≤ t ∧ t ≤ Real.pi := by
    rcases ht with h | h
    · exact ⟨h.1, by linarith only [h.2, Real.pi_pos]⟩
    · exact ⟨by linarith only [h.1, Real.pi_pos], by linarith only [h.2]⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1 htI.2
  rw [inner_smul_normalVector_zero]
  rcases le_or_gt 0 (Real.cos t) with hcos | hcos
  · have h := inner_le_supportValue K.val hA (t : Real.Angle)
    rw [inner_normalVector_real] at h
    have hy := (K.mem_horizontalStrip hA).1
    nlinarith only [h, hAeq, hhi, hcos, mul_nonneg hsin hy]
  · have h := inner_le_supportValue K.val hC (t : Real.Angle)
    rw [inner_normalVector_real] at h
    have hy := (K.mem_horizontalStrip hC).1
    nlinarith only [h, hCeq, hlo, hcos, mul_nonneg hsin hy]

/-- The bottom right cap vertex is the horizontal maximum on the base line. -/
private theorem capVertices_zero_snd_eq (K : RightAngleCapSpace) :
    (capVertices K 0).1.2 =
      supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) •
        normalVector (0 : Real.Angle) := by
  set R := supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) with hRdef
  have hS : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤ R := by
    obtain ⟨p, hp⟩ := K.val.nonempty
    have h0 := inner_le_supportValue K.val hp ((0 : ℝ) : Real.Angle)
    have hpi := inner_le_supportValue K.val hp ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_zero] at h0
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hpi
    rw [hRdef]
    linarith
  have hmem : R • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) :=
    smul_normalVector_zero_mem_of_rightAngleCap K hS le_rfl
  have hedge : R • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((0 : ℝ) : Real.Angle) := by
    refine ⟨hmem, ?_⟩
    change inner ℝ (R • normalVector (0 : Real.Angle))
      (normalVector ((0 : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, Real.cos_zero, mul_one]
  show (edgeVertices K.val ((0 : ℝ) : Real.Angle)).2 = _
  refine edgeVertices_snd_eq_of_tangent_isLeast K.val ((0 : ℝ) : Real.Angle) hedge ?_
  intro q hq
  have hq1 : 0 ≤ q 1 := (K.mem_horizontalStrip hq.1).1
  have hp1 : inner ℝ (R • normalVector (0 : Real.Angle))
      (tangentVector ((0 : ℝ) : Real.Angle)) = 0 := by
    rw [real_inner_smul_left, show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) from rfl,
      inner_normalVector_tangentVector, mul_zero]
  rw [hp1, inner_tangentVector_zero]
  exact hq1

/-- The bottom left cap vertex is the horizontal minimum on the base line. -/
private theorem capVertices_pi_div_two_fst_eq (K : RightAngleCapSpace) :
    (capVertices K (Real.pi / 2)).2.1 =
      (-supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) •
        normalVector (0 : Real.Angle) := by
  set S := supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) with hSdef
  have hR : -S ≤ supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) := by
    obtain ⟨p, hp⟩ := K.val.nonempty
    have h0 := inner_le_supportValue K.val hp ((0 : ℝ) : Real.Angle)
    have hpi := inner_le_supportValue K.val hp ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_zero] at h0
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hpi
    rw [hSdef]
    linarith
  have hmem : (-S) • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) :=
    smul_normalVector_zero_mem_of_rightAngleCap K le_rfl hR
  have hang : ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi : ℝ) : Real.Angle) := by
    congr 1
    ring
  have hedge : (-S) • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((Real.pi : ℝ) : Real.Angle) := by
    refine ⟨hmem, ?_⟩
    change inner ℝ ((-S) • normalVector (0 : Real.Angle))
      (normalVector ((Real.pi : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, Real.cos_pi]
    ring
  show (edgeVertices K.val ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 = _
  rw [hang]
  refine edgeVertices_fst_eq_of_tangent_isGreatest K.val ((Real.pi : ℝ) : Real.Angle) hedge ?_
  intro q hq
  have hq1 : 0 ≤ q 1 := (K.mem_horizontalStrip hq.1).1
  have hp1 : inner ℝ ((-S) • normalVector (0 : Real.Angle))
      (tangentVector ((Real.pi : ℝ) : Real.Angle)) = 0 := by
    rw [real_inner_smul_left, inner_tangentVector_pi]
    simp [normalVector, frame]
  rw [hp1, inner_tangentVector_pi]
  linarith

/-- Horizontal coordinates strictly inside the cap width give interior bottom-edge points. -/
private theorem smul_normalVector_zero_mem_bottomEdge (K : RightAngleCapSpace) {x : ℝ}
    (hlo : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) < x)
    (hhi : x < supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle)) :
    x • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K 0).1.2, (capVertices K (Real.pi / 2)).2.1} := by
  have hinj : ∀ a b : ℝ, a • normalVector (0 : Real.Angle) =
      b • normalVector (0 : Real.Angle) → a = b := by
    intro a b h
    have h' := congrArg (fun p : Point ↦ inner ℝ p (normalVector ((0 : ℝ) : Real.Angle))) h
    simpa only [inner_smul_normalVector_zero, Real.cos_zero, mul_one] using h'
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring, Real.cos_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi]
    ring
  refine ⟨⟨smul_normalVector_zero_mem_of_rightAngleCap K hlo.le hhi.le, ?_⟩, ?_⟩
  · change inner ℝ (x • normalVector (0 : Real.Angle))
      (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, hcos, mul_zero, K.property.2.2.2.2.2.1]
  · rintro (h | h)
    · rw [capVertices_zero_snd_eq K] at h
      exact absurd (hinj _ _ h) (ne_of_lt hhi)
    · rw [capVertices_pi_div_two_fst_eq K] at h
      exact absurd (hinj _ _ h) (ne_of_gt hlo)

theorem specialCap_wedgeEndpoints_in_bottomEdge (K : SpecialCapSpace) :
    (distinguishedCapSides K.val).1.fanPoint ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K.val 0).1.2, (capVertices K.val (Real.pi / 2)).2.1} ∧
    (distinguishedCapSides K.val).2.fanPoint ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K.val 0).1.2, (capVertices K.val (Real.pi / 2)).2.1} := by
  obtain ⟨hrIoo, hlIoo, hrl⟩ := paperGerverConstants_snd_mem_Ioo
  -- the certified parameter bound `0 < varphi ≤ 1/25` and its trigonometric consequences
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, q, hqbox, hqeq, -⟩ := gerver_parameter_identification
    exact (hall q hqbox hqeq).2.2.2.2.2.2.2.1
  have hcosr : (1249 : ℝ) / 1250 ≤ Real.cos paperGerverConstants.2.1 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := paperGerverConstants.2.1)
    nlinarith only [h, hphi, hrIoo.1]
  have hcpos : (0 : ℝ) < Real.cos paperGerverConstants.2.1 := by linarith
  have hsinr : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.1 :=
    (Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [hrIoo.2, Real.pi_pos])).le
  have hsinl : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.2 :=
    (Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [hlIoo.2, Real.pi_pos])).le
  have hcosl : (0 : ℝ) ≤ Real.cos paperGerverConstants.2.2 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hlIoo.1, Real.pi_pos], hlIoo.2⟩).le
  have hcosdiff : Real.pi / 2 - paperGerverConstants.2.2 = paperGerverConstants.2.1 := by
    linarith
  have hsinleq : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [show paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 by linarith,
      Real.sin_pi_div_two_sub]
  have hinvc : (1 : ℝ) / Real.cos paperGerverConstants.2.1 ≤ 1250 / 1249 := by
    rw [div_le_div_iff₀ hcpos (by norm_num)]
    linarith
  -- the cap is wide, by rectangle area monotonicity and the special-cap area threshold
  have hwidth : (11 : ℝ) / 5 ≤
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) := by
    have h := K.property.2.trans K.val.area_le_horizontalWidth
    rwa [supportValue_zero_eq_horizontalMax, supportValue_pi_eq_neg_horizontalMin,
      ← sub_eq_add_neg]
  -- support lower bounds at the two distinguished angles
  have hlowR : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinr hcpos.le).1
    rwa [← supportValue_zero_eq_horizontalMax] at h
  have hlowL : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinl hcosl).2
    rw [supportValue_pi_eq_neg_horizontalMin, ← hsinleq, mul_neg, ← neg_mul]
    exact h
  -- the two positive wedge gaps
  have hgap₁ := wedgeGaps_positive_lower_bound K.val paperGerverConstants.2.1 hrIoo
  have hgap₂ := wedgeGaps_positive_lower_bound K.val paperGerverConstants.2.2 hlIoo
  rw [wedgeGaps_fst_eq_supportValue] at hgap₁
  rw [wedgeGaps_snd_eq_supportValue,
    show ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) by
      congr 1; ring, hcosdiff] at hgap₂
  have hgap₁' : (1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1 ≤
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) -
        (supportValue (K.val.val : Set Point)
          ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 := hgap₁.1
  have hgap₂' : (1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1 ≤
      supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) -
        (supportValue (K.val.val : Set Point)
          ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 := hgap₂.2.2.1
  -- the reciprocal-cosine lower bounds for the two inner-wall coordinates
  have hRc : supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) /
        Real.cos paperGerverConstants.2.1 := by
    rw [le_div_iff₀ hcpos]
    linarith
  have hSc : supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) /
        Real.cos paperGerverConstants.2.1 := by
    rw [le_div_iff₀ hcpos]
    linarith
  have hRc' : supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) -
      1 / Real.cos paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1 := by
    rw [sub_div]
    linarith
  have hSc' : supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) -
      1 / Real.cos paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1 := by
    rw [sub_div]
    linarith
  -- the two fan points as multiples of the horizontal normal
  have htv : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (0 : Real.Angle) := by
    have h := tangentVector_add_pi_div_two 0
    rwa [zero_add, Real.Angle.coe_zero] at h
  constructor
  · show ((supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1) • normalVector (0 : Real.Angle) ∈ _
    refine smul_normalVector_zero_mem_bottomEdge K.val ?_ ?_
    · linarith
    · have hpos : 0 < (1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1 := hgap₁.2.1
      linarith
  · show ((supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos (Real.pi / 2 - paperGerverConstants.2.2)) •
        tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ _
    rw [hcosdiff, htv, smul_neg, ← neg_smul]
    refine smul_normalVector_zero_mem_bottomEdge K.val ?_ ?_
    · have hpos : 0 < (1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1 := hgap₂.2.2.2
      linarith
    · linarith

end MovingSofa

end

end

end
