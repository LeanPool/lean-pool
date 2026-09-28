/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development002
public import LeanPool.MovingSofa.Bounds.Foundations.Development004
public import LeanPool.MovingSofa.Cap.Foundations.Development004
public import LeanPool.MovingSofa.Cap.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001

public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Gerver.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Cap.Regularity`.
* `Cap.Tail.Contacts`.
* `Cap.Tail.Bodies`.
* `Cap.Tail.Extension`.
* `Cap.Tail.Separation`.
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
# Cap / Regularity
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace MovingSofa

private theorem continuous_nondegenerateCapData_right (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.1 := by
  have h := continuousOn_replace_right_endpoint (by positivity : (0 : ℝ) < Real.pi / 2)
    (fun t : ℝ ↦ (capVertices K t).1.1) ((capVertices K (Real.pi / 2)).1.2)
    (fun t ht ↦ (contact_oneSided_limits K.1 t).1)
    (fun t ht ↦ ?_) (contact_oneSided_limits K.1 (Real.pi / 2)).2.2.2.1
  · apply (continuousOn_iff_continuous_domRestrict.mp h).congr
    intro t
    dsimp [Set.domRestrict, nondegenerateCapData]
    split_ifs with heq
    · rw [heq]
    · rfl
  · have heq := (capDensities_contact_eq K hD).1 t ⟨ht.1.le, ht.2⟩ |>.1
    change (edgeVertices K.1 (t : Real.Angle)).1 =
      (edgeVertices K.1 (t : Real.Angle)).2 at heq
    simpa only [← heq, capVertices] using (contact_oneSided_limits K.1 t).2.2.2.1

private theorem continuous_nondegenerateCapData_left (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.2 := by
  let f : ℝ → Point := fun t ↦ (capVertices K t).2.1
  have hr (t : ℝ) : Tendsto f (𝓝[>] t) (𝓝 (f t)) := by
    apply (contact_oneSided_limits K.1 (t + Real.pi / 2)).1.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (tendsto_id.mono_left nhdsWithin_le_nhds).add_const _
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change t + Real.pi / 2 < u + Real.pi / 2
      simpa only [add_comm] using add_lt_add_right (Set.mem_Ioi.mp hu) (Real.pi / 2)
  have hl (t : ℝ) (ht : t ∈ Ioc 0 (Real.pi / 2)) :
      Tendsto f (𝓝[<] t) (𝓝 (f t)) := by
    have h := (contact_oneSided_limits K.1 (t + Real.pi / 2)).2.2.2.1
    have heq := (capDensities_contact_eq K hD).2 t ht |>.1
    change (edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 =
      (edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 at heq
    rw [← heq] at h
    apply h.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (tendsto_id.mono_left nhdsWithin_le_nhds).add_const _
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change u + Real.pi / 2 < t + Real.pi / 2
      simpa only [add_comm] using add_lt_add_right (Set.mem_Iio.mp hu) (Real.pi / 2)
  have h := continuousOn_replace_right_endpoint (by positivity : (0 : ℝ) < Real.pi / 2)
    f (f (Real.pi / 2)) (fun t _ ↦ hr t) (fun t ht ↦ hl t ⟨ht.1, ht.2.le⟩)
    (hl (Real.pi / 2) ⟨by positivity, le_rfl⟩)
  have hc : ContinuousOn f (Icc 0 (Real.pi / 2)) := h.congr fun t ht ↦ by
    by_cases heq : t = Real.pi / 2 <;> simp [heq]
  change Continuous ((Icc 0 (Real.pi / 2)).domRestrict f)
  exact continuousOn_iff_continuous_domRestrict.mp hc

private theorem continuous_nondegenerateCapData_arms (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).2.1 ∧
    Continuous (nondegenerateCapData K hD).2.2 := by
  have hy := (continuous_outerCorner K.1).comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hn := continuous_normalVector_real.comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hv := (continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_tangentVector t).continuousAt).comp
      (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  constructor
  · apply ((hy.sub (continuous_nondegenerateCapData_right K hD)).inner hv).congr
    intro t
    dsimp [nondegenerateCapData, tangentArmLengths]
    split_ifs <;> rfl
  · exact (hy.sub (continuous_nondegenerateCapData_left K hD)).inner hn

private theorem nondegenerateCap_hasDerivWithinAt (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) (t : Icc (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (capInnerCorner K)
      (-((nondegenerateCapData K hD).2.1 t - 1) • normalVector (t : Real.Angle) +
        ((nondegenerateCapData K hD).2.2 t - 1) • tangentVector (t : Real.Angle))
      (Icc 0 (Real.pi / 2)) (t : ℝ) ∧
    HasDerivWithinAt
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (-(nondegenerateCapData K hD).2.1 t • normalVector (t : Real.Angle) +
        (nondegenerateCapData K hD).2.2 t • tangentVector (t : Real.Angle))
      (Icc 0 (Real.pi / 2)) (t : ℝ) := by
  have hr (ht : (t : ℝ) < Real.pi / 2) :=
    (capCorners_oneSided_derivatives K).1 t ⟨t.property.1, ht⟩
  have hl (ht : 0 < (t : ℝ)) :=
    (capCorners_oneSided_derivatives K).2 t ⟨ht, t.property.2⟩
  have hfplus (ht : (t : ℝ) < Real.pi / 2) :
      (nondegenerateCapData K hD).2.1 t = (tangentArmLengths K t).1.1 := by
    simp only [nondegenerateCapData, ite_eq_right ht.ne]
  have hfminus (ht : 0 < (t : ℝ)) :
      (nondegenerateCapData K hD).2.1 t = (tangentArmLengths K t).1.2 := by
    dsimp [nondegenerateCapData]
    split_ifs with heq
    · rfl
    · exact ((capDensities_contact_eq K hD).1 t
        ⟨t.property.1, lt_of_le_of_ne t.property.2 heq⟩).2
  have hgminus (ht : 0 < (t : ℝ)) :
      (nondegenerateCapData K hD).2.2 t = (tangentArmLengths K t).2.2 :=
    ((capDensities_contact_eq K hD).2 t ⟨ht, t.property.2⟩).2
  constructor
  · apply hasDerivWithinAt_Icc_of_oneSided (by positivity) t.property
    · intro ht
      rw [hfplus ht]
      exact (hr ht).2
    · intro ht
      rw [hfminus ht, hgminus ht]
      exact (hl ht).2
  · apply hasDerivWithinAt_Icc_of_oneSided (by positivity) t.property
    · intro ht
      rw [hfplus ht]
      exact (hr ht).1
    · intro ht
      rw [hfminus ht, hgminus ht]
      exact (hl ht).1

theorem nondegenerateCap_continuity (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.1 ∧
    Continuous (nondegenerateCapData K hD).1.2 ∧
    Continuous (nondegenerateCapData K hD).2.1 ∧
    Continuous (nondegenerateCapData K hD).2.2 ∧
    ContDiffOn ℝ 1 (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) ∧
    ContDiffOn ℝ 1
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (Set.Icc 0 (Real.pi / 2)) ∧
    ∀ t : Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K)
        (-((nondegenerateCapData K hD).2.1 t - 1) • normalVector (t : Real.Angle) +
          ((nondegenerateCapData K hD).2.2 t - 1) • tangentVector (t : Real.Angle))
        (Set.Icc 0 (Real.pi / 2)) (t : ℝ) ∧
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
        (-(nondegenerateCapData K hD).2.1 t • normalVector (t : Real.Angle) +
          (nondegenerateCapData K hD).2.2 t • tangentVector (t : Real.Angle))
        (Set.Icc 0 (Real.pi / 2)) (t : ℝ) := by
  have hA := continuous_nondegenerateCapData_right K hD
  have hC := continuous_nondegenerateCapData_left K hD
  obtain ⟨hf, hg⟩ := continuous_nondegenerateCapData_arms K hD
  have hn := continuous_normalVector_real.comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hv := (continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_tangentVector t).continuousAt).comp
      (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  refine ⟨hA, hC, hf, hg, ?_, ?_, nondegenerateCap_hasDerivWithinAt K hD⟩
  · exact contDiffOn_one_of_continuous_derivative
      (uniqueDiffOn_Icc (by positivity)) _ _
      (((hf.sub continuous_const).neg.smul hn).add ((hg.sub continuous_const).smul hv))
      (fun t ↦ (nondegenerateCap_hasDerivWithinAt K hD t).1)
  · exact contDiffOn_one_of_continuous_derivative
      (uniqueDiffOn_Icc (by positivity)) _ _
      ((hf.neg.smul hn).add (hg.smul hv))
      (fun t ↦ (nondegenerateCap_hasDerivWithinAt K hD t).2)

/-- The corner coordinates of a right-angle cap in its moving frame. -/
theorem inner_capInnerCorner (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ∧
      inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
  constructor
  · have h := inner_supportingPlacement_normalVector (K.1 : Set Point) (t : Real.Angle) 0
    simpa [capInnerCorner, rotatingHallwayParts, hallwayParts] using h
  · have h := inner_supportingPlacement_tangentVector (K.1 : Set Point) (t : Real.Angle) 0
    rw [← Real.Angle.coe_add] at h
    simpa [capInnerCorner, rotatingHallwayParts, hallwayParts] using h

/-- The injectivity condition supplies the support derivatives with their strict signs. -/
theorem capSupport_hasDerivAt (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) :
    ∃ dh dj : ℝ → ℝ,
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) (dh t) t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) (dj t)
          (t + Real.pi / 2)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        dh t - supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) + 1 < 0) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        0 < dj t + supportValue (K.1 : Set Point) (t : Real.Angle) - 1) := by
  obtain ⟨-, hC1, hsign⟩ := hinj
  have hxn : ∀ t : ℝ, inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
      supportValue (K.1 : Set Point) (t : Real.Angle) - 1 := fun t => (inner_capInnerCorner K t).1
  have hxt : ∀ t : ℝ, inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
      supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    fun t => (inner_capInnerCorner K t).2
  have hdiff : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (capInnerCorner K) (deriv (capInnerCorner K) t) t := by
    intro t ht
    have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    exact (((hC1.differentiableOn one_ne_zero) t (Set.Ioo_subset_Icc_self ht)).differentiableAt
      hmem).hasDerivAt
  have hderivEq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t = deriv (capInnerCorner K) t :=
    fun t ht => derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hfunn : (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) =
      fun u : ℝ ↦ inner ℝ (capInnerCorner K u) (normalVector (u : Real.Angle)) + 1 := by
    funext u; rw [hxn u]; ring
  have hfunt :
      (fun u : ℝ ↦ supportValue (K.1 : Set Point) ((u + Real.pi / 2 : ℝ) : Real.Angle)) =
      fun u : ℝ ↦ inner ℝ (capInnerCorner K u) (tangentVector (u : Real.Angle)) + 1 := by
    funext u; rw [hxt u]; ring
  refine ⟨fun t ↦ inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) +
      inner ℝ (deriv (capInnerCorner K) t) (normalVector (t : Real.Angle)),
    fun t ↦ -inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) +
      inner ℝ (deriv (capInnerCorner K) t) (tangentVector (t : Real.Angle)), ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hfunn]
    exact ((hdiff t ht).inner ℝ (hasDerivAt_normalVector t)).add_const 1
  · intro t ht
    refine (hasDerivAt_comp_add_const_iff (f := fun u : ℝ ↦
      supportValue (K.1 : Set Point) (u : Real.Angle)) t (Real.pi / 2)).mp ?_
    rw [hfunt]
    have hd := ((hdiff t ht).inner ℝ (hasDerivAt_tangentVector t)).add_const 1
    rw [inner_neg_right] at hd
    exact hd
  · intro t ht
    have h1 := (hsign t ht).1
    rw [hderivEq t ht] at h1
    dsimp only
    rw [hxt t]
    linarith only [h1]
  · intro t ht
    have h2 := (hsign t ht).2
    rw [hderivEq t ht] at h2
    dsimp only
    rw [hxn t]
    linarith only [h2]
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
# Endpoint contacts for the canonical cap tails

The right and left canonical tails of a special cap are cut out of the cap by the upper
half-planes of its inner supporting walls. This file supplies the contact points that make the
tail support values meet their endpoint bounds.

The mathematical content is the frame-free lemma
`exists_mem_inner_eq_sub_one_of_deriv_signs`: let `s` be a nonempty compact convex planar set
lying above the horizontal axis with `h_s(pi/2) = 1`, whose support function `h` is
differentiable on the two quarter-turn families with the strict corner velocity signs
`h'(t) - h(t + pi/2) + 1 < 0` and `h'(t + pi/2) + h(t) - 1 > 0` for `t` in `(0, pi/2)`. Then
every interior cut line `{q | inner q (normalVector t) = h(t) - 1}` meets `s` in a point that
stays above the whole cut family on `[t, pi/2]`.

The proof selects the transverse maximum `p` of the first cut section and studies the
deficiency `g(t) = h(t) - inner p (normalVector t)`. Wherever `g(t) = 1`, the chord joining the
two frame contacts has nonpositive signed area (`planeCrossProduct_nonpos_of_isMaxOn`), which
forces `g` to decrease strictly at the cut angle; at a first return of `g` to level one the
same determinant is strictly positive, a contradiction.

The left tail follows from the same lemma applied to `reflectedBody (pi/2) K`, whose support
derivatives are the negated right-hand ones read backwards; see `exists_left_tail_contact`.

This argument replaces the step in the paper's proof of `lem:right-left-body` which infers that the
upper boundary avoids the niche; that inference fails for the stated class of caps (P46 in
`NOTES.md`).
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Lowering a right-angle cap point vertically to the base line keeps it inside the cap. -/
theorem basePoint_mem_of_rightAngleCap (K : RightAngleCapSpace) {q : Point}
    (hq : q ∈ (K.1 : Set Point)) : (!₂[q 0, 0] : Point) ∈ (K.1 : Set Point) := by
  have hq0 : (!₂[q 0, 0] : Point) 0 = q 0 := rfl
  have hq1 : (!₂[q 0, 0] : Point) 1 = 0 := rfl
  have hqy : 0 ≤ q 1 := by
    have h := K.inner_normalVector_pi_div_two_nonneg hq
    rwa [inner_normalVector_pi_div_two] at h
  have hzero : inner ℝ (!₂[q 0, 0] : Point)
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_normalVector_pi_div_two, hq1]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨le_of_eq hzero.symm, le_of_eq hzero.symm⟩ ?_
  intro t ht
  have htI : 0 ≤ t ∧ t ≤ Real.pi := by
    rcases ht with h | h
    · exact ⟨h.1, by linarith only [h.2, Real.pi_pos]⟩
    · exact ⟨by linarith only [h.1, Real.pi_pos], by linarith only [h.2]⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1 htI.2
  have hqt := inner_le_supportValue_of_isCompact K.1.isCompact hq (t : Real.Angle)
  rw [inner_normalVector_real] at hqt
  rw [inner_normalVector_real, hq0, hq1]
  nlinarith only [hqt, hsin, hqy]

/-- The two frame contacts at an interior angle, with their derivative coordinates. -/
theorem exists_frame_contacts {s : Set Point} (hcomp : IsCompact s) (hne : s.Nonempty)
    {t dh dj : ℝ}
    (hdh : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) dh t)
    (hdj : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) dj (t + Real.pi / 2)) :
    ∃ A ∈ s, ∃ C ∈ s,
      inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) ∧
      inner ℝ A (tangentVector (t : Real.Angle)) = dh ∧
      inner ℝ C (normalVector (t : Real.Angle)) = -dj ∧
      inner ℝ C (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  obtain ⟨A, hA, hA1, hA2⟩ := exists_contact_of_hasDerivAt hcomp hne hdh
  obtain ⟨C, hC, hC1, hC2⟩ := exists_contact_of_hasDerivAt hcomp hne hdj
  have hnv : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (t : Real.Angle) := by
    rw [Real.Angle.coe_add]
    exact normalVector_add_pi_div_two (t : Real.Angle)
  have htv : tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      -normalVector (t : Real.Angle) := tangentVector_add_pi_div_two t
  rw [hnv] at hC1
  rw [htv, inner_neg_right] at hC2
  exact ⟨A, hA, C, hC, hA1, hA2, by linarith, hC1⟩

/-- A transverse chord through a maximizing section point has nonpositive signed area. -/
theorem planeCrossProduct_nonpos_of_isMaxOn {s : Set Point} (hconv : Convex ℝ s)
    {r c₀ : ℝ} {p : Point}
    (hpline : inner ℝ p (normalVector (r : Real.Angle)) = c₀)
    (hmax : ∀ q ∈ s, inner ℝ q (normalVector (r : Real.Angle)) = c₀ →
      inner ℝ q (tangentVector (r : Real.Angle)) ≤ inner ℝ p (tangentVector (r : Real.Angle)))
    {A C : Point} (hA : A ∈ s) (hC : C ∈ s)
    (hApos : 0 < inner ℝ (A - p) (normalVector (r : Real.Angle)))
    (hCneg : inner ℝ (C - p) (normalVector (r : Real.Angle)) < 0) :
    planeCrossProduct (A - p) (C - p) ≤ 0 := by
  set u := normalVector (r : Real.Angle) with hu
  set v := tangentVector (r : Real.Angle) with hv
  set mu : ℝ := inner ℝ (A - p) u with hmu
  set la : ℝ := -inner ℝ (C - p) u with hla
  have hlapos : 0 < la := by simp only [hla]; linarith
  have hsum : 0 < la + mu := by linarith
  set w : ℝ := la / (la + mu) with hw
  have hw0 : 0 ≤ w := div_nonneg hlapos.le hsum.le
  have hw1 : 0 ≤ 1 - w := by
    rw [hw, sub_nonneg, div_le_one hsum]
    linarith
  set q : Point := w • A + (1 - w) • C with hq
  have hqs : q ∈ s := hconv hA hC hw0 hw1 (by ring)
  have hwmu : w * mu + (1 - w) * (-la) = 0 := by
    rw [hw]; field_simp; ring
  have hqu : inner ℝ q u = c₀ := by
    have h1 : inner ℝ q u - inner ℝ p u = w * mu + (1 - w) * (-la) := by
      simp only [hq, hmu, hla, inner_add_left, real_inner_smul_left, inner_sub_left]
      ring
    rw [hwmu] at h1
    rw [hpline] at h1
    linarith
  have hqv := hmax q hqs hqu
  have h2 : inner ℝ q v - inner ℝ p v =
      w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v := by
    simp only [hq, inner_add_left, real_inner_smul_left, inner_sub_left]
    ring
  have hnum : w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v ≤ 0 := by
    rw [← h2]; linarith
  have hcross : planeCrossProduct (A - p) (C - p) =
      mu * inner ℝ (C - p) v - inner ℝ (A - p) v * (-la) := by
    rw [planeCrossProduct_eq_inner_frame (A - p) (C - p) r, ← hu, ← hv, ← hmu]
    simp only [hla]
    ring
  rw [hcross]
  have hwid : (1 - w) * (la + mu) = mu := by rw [hw]; field_simp; ring
  have hwid2 : w * (la + mu) = la := by rw [hw]; field_simp
  have hexp : (w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v) * (la + mu) =
      la * inner ℝ (A - p) v + mu * inner ℝ (C - p) v := by
    calc (w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v) * (la + mu)
        = (w * (la + mu)) * inner ℝ (A - p) v +
          ((1 - w) * (la + mu)) * inner ℝ (C - p) v := by ring
      _ = la * inner ℝ (A - p) v + mu * inner ℝ (C - p) v := by rw [hwid, hwid2]
  have hmul := mul_nonpos_of_nonpos_of_nonneg hnum hsum.le
  rw [hexp] at hmul
  linarith

/-- The three chord signs at a first return time, in the frame coordinates at that time. -/
private theorem chord_signs {r t d al be : ℝ} (hr : 0 < r) (hrt : r < t)
    (ht : t < Real.pi / 2) (hd : 0 ≤ d) (hal : al < 0) (hbe : 0 < be)
    (hstrip : Real.sin t + Real.cos t * d ≤ 1) :
    0 < Real.cos (t - r) - Real.sin (t - r) * d ∧
      Real.cos (t - r) * (-be) - Real.sin (t - r) * (1 - al + d) < 0 ∧
      0 < 1 - al + d + be * d := by
  have hpi := Real.pi_pos
  have hδpos : 0 < t - r := by linarith only [hrt]
  have hδlt : t - r < Real.pi / 2 := by linarith only [hr, ht]
  have hsinδ : 0 < Real.sin (t - r) :=
    Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith only [hpi, hδlt])
  have hcosδ : 0 < Real.cos (t - r) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hpi, hδpos], hδlt⟩
  have hcost : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hpi, hr, hrt], ht⟩
  have hcosr : Real.cos (t - r) * Real.cos t + Real.sin (t - r) * Real.sin t = Real.cos r := by
    rw [← Real.cos_sub, show t - r - t = -r by ring, Real.cos_neg]
  have hcosrgt : Real.sin (t - r) < Real.cos r := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith only [hpi, hδpos])
      (by linarith only [hr]) (by linarith only [ht])
  refine ⟨?_, ?_, by nlinarith only [hal, hbe, hd]⟩
  · have hmul := mul_le_mul_of_nonneg_left hstrip hsinδ.le
    have hstep : Real.cos r - Real.sin (t - r) ≤
        Real.cos t * (Real.cos (t - r) - Real.sin (t - r) * d) := by
      nlinarith only [hmul, hcosr]
    by_contra hc
    push Not at hc
    nlinarith only [hstep, hc, hcost, hcosrgt]
  · nlinarith only [hcosδ, hsinδ, hbe, hal, hd]

/-- Contradiction sign lemma at the cut angle: a nonpositive determinant forces a negative slope. -/
private theorem neg_of_det_nonpos {d al be : ℝ} (hal : al < 0) (hbe : 0 < be)
    (hdet : 1 - al + d + be * d ≤ 0) : d < 0 := by
  by_contra h
  push Not at h
  nlinarith only [hal, hbe, hdet, h]

/-- Endpoint contact for the upper cut family of a strip body with strict corner velocities. -/
theorem exists_mem_inner_eq_sub_one_of_deriv_signs
    {s : Set Point} (hcomp : IsCompact s) (hconv : Convex ℝ s) (hne : s.Nonempty)
    (dh dj : ℝ → ℝ)
    (hdh : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) (dh t) t)
    (hdj : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) (dj t) (t + Real.pi / 2))
    (halpha : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      dh t - supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) + 1 < 0)
    (hbeta : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < dj t + supportValue s (t : Real.Angle) - 1)
    (htop : supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1)
    (hlow : ∀ q ∈ s, 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ s, inner ℝ p (normalVector (r : Real.Angle)) =
        supportValue s (r : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc r (Real.pi / 2),
        supportValue s (t : Real.Angle) - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
  -- the cut line at `r` meets the body, between the two frame contacts
  obtain ⟨A₀, hA₀, C₀, hC₀, hA₀n, hA₀t, hC₀n, hC₀t⟩ :=
    exists_frame_contacts hcomp hne (hdh r hr) (hdj r hr)
  have hC₀le : inner ℝ C₀ (normalVector (r : Real.Angle)) ≤
      supportValue s (r : Real.Angle) - 1 := by
    rw [hC₀n]; linarith only [hbeta r hr]
  have hA₀ge : supportValue s (r : Real.Angle) - 1 ≤
      inner ℝ A₀ (normalVector (r : Real.Angle)) := by rw [hA₀n]; linarith only []
  obtain ⟨p₀, hp₀, hp₀line⟩ :=
    exists_mem_inner_eq_of_convex hconv hA₀ hC₀ hC₀le hA₀ge
  -- the transverse maximizer on that cut section
  have hcontinner : Continuous (fun q : Point ↦ inner ℝ q (normalVector (r : Real.Angle))) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hScomp : IsCompact (s ∩ {q : Point |
      inner ℝ q (normalVector (r : Real.Angle)) = supportValue s (r : Real.Angle) - 1}) :=
    hcomp.inter_right (isClosed_eq hcontinner continuous_const)
  have hconttang : Continuous (fun q : Point ↦ inner ℝ q (tangentVector (r : Real.Angle))) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  obtain ⟨p, hpS, hpmax⟩ :=
    hScomp.exists_isMaxOn ⟨p₀, hp₀, hp₀line⟩ hconttang.continuousOn
  have hps : p ∈ s := hpS.1
  have hpline : inner ℝ p (normalVector (r : Real.Angle)) =
    supportValue s (r : Real.Angle) - 1 := hpS.2
  have hmaxq : ∀ q ∈ s, inner ℝ q (normalVector (r : Real.Angle)) =
      supportValue s (r : Real.Angle) - 1 →
      inner ℝ q (tangentVector (r : Real.Angle)) ≤
        inner ℝ p (tangentVector (r : Real.Angle)) := fun q hq hq2 => hpmax ⟨hq, hq2⟩
  -- the deficiency function
  set g : ℝ → ℝ := fun u ↦ supportValue s (u : Real.Angle) -
    inner ℝ p (normalVector (u : Real.Angle)) with hgdef
  have hgval : ∀ u : ℝ, g u = supportValue s (u : Real.Angle) -
      inner ℝ p (normalVector (u : Real.Angle)) := fun _ => rfl
  have hgr : g r = 1 := by rw [hgval, hpline]; ring
  have hgderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt g (dh t - inner ℝ p (tangentVector (t : Real.Angle))) t :=
    fun t ht => (hdh t ht).sub (hasDerivAt_inner_normalVector p t)
  have hgT : g (Real.pi / 2) ≤ 1 := by
    rw [hgval, htop]
    linarith only [hlow p hps]
  -- coordinates of the two contact chords relative to the maximizer
  have hcoords : ∀ t : ℝ, g t = 1 → ∀ A C : Point,
      inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) →
      inner ℝ A (tangentVector (t : Real.Angle)) = dh t →
      inner ℝ C (normalVector (t : Real.Angle)) = -dj t →
      inner ℝ C (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) →
      inner ℝ (A - p) (normalVector (t : Real.Angle)) = 1 ∧
      inner ℝ (A - p) (tangentVector (t : Real.Angle)) =
        dh t - inner ℝ p (tangentVector (t : Real.Angle)) ∧
      inner ℝ (C - p) (normalVector (t : Real.Angle)) =
        -dj t - (supportValue s (t : Real.Angle) - 1) ∧
      inner ℝ (C - p) (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) -
          inner ℝ p (tangentVector (t : Real.Angle)) := by
    intro t hgt A C e1 e2 e3 e4
    have hpu : inner ℝ p (normalVector (t : Real.Angle)) =
        supportValue s (t : Real.Angle) - 1 := by
      have h := hgval t
      rw [hgt] at h
      linarith only [h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [inner_sub_left, e1, hpu]; ring
    · simp only [inner_sub_left, e2]
    · simp only [inner_sub_left, e3, hpu]
    · simp only [inner_sub_left, e4]
  -- the deficiency decreases strictly at the cut angle
  have hdgr : dh r - inner ℝ p (tangentVector (r : Real.Angle)) < 0 := by
    obtain ⟨k1, k2, k3, k4⟩ := hcoords r hgr A₀ C₀ hA₀n hA₀t hC₀n hC₀t
    have hApos : 0 < inner ℝ (A₀ - p) (normalVector (r : Real.Angle)) := by
      rw [k1]; norm_num
    have hCneg : inner ℝ (C₀ - p) (normalVector (r : Real.Angle)) < 0 := by
      rw [k3]; linarith only [hbeta r hr]
    have hcr := planeCrossProduct_nonpos_of_isMaxOn hconv hpline hmaxq hA₀ hC₀ hApos hCneg
    rw [planeCrossProduct_eq_inner_frame (A₀ - p) (C₀ - p) r, k1, k2, k3, k4] at hcr
    exact neg_of_det_nonpos (halpha r hr) (hbeta r hr) (by linarith only [hcr])
  -- the deficiency never exceeds one on the cut range
  have hmain : ∀ t ∈ Set.Icc r (Real.pi / 2), g t ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁mem, ht₁gt⟩ := hcon
    have ht₁r : r < t₁ :=
      lt_of_le_of_ne ht₁mem.1 (by rintro rfl; rw [hgr] at ht₁gt; exact lt_irrefl 1 ht₁gt)
    have ht₁T : t₁ < Real.pi / 2 :=
      lt_of_le_of_ne ht₁mem.2 (by rintro rfl; exact absurd hgT (not_le.mpr ht₁gt))
    -- a time just to the right of the cut where the deficiency is below one
    have hev : ∀ᶠ y in nhdsWithin r (Set.Ioi r), slope g r y < 0 := by
      refine (((hasDerivAt_iff_tendsto_slope.mp (hgderiv r hr)).mono_left
        (nhdsWithin_mono r fun x hx => ne_of_gt hx)).eventually_lt_const hdgr)
    obtain ⟨r', hr'slope, hr'mem⟩ :=
      (hev.and (Filter.eventually_of_mem (Ioo_mem_nhdsGT ht₁r) fun y hy => hy)).exists
    have hrr' : r < r' := hr'mem.1
    have hr't₁ : r' < t₁ := hr'mem.2
    have hgr'lt : g r' < 1 := by
      rw [slope_def_field] at hr'slope
      have hnum : g r' - g r < 0 := by
        by_contra hcc
        push Not at hcc
        have h0 : 0 ≤ (g r' - g r) / (r' - r) := div_nonneg hcc (by linarith only [hrr'])
        linarith only [h0, hr'slope]
      linarith only [hnum, hgr]
    -- the first return to level one
    have hgcontOn : ContinuousOn g (Set.Icc r' t₁) := fun u hu =>
      ((hgderiv u ⟨by linarith only [hu.1, hrr', hr.1],
        by linarith only [hu.2, ht₁T]⟩).continuousAt).continuousWithinAt
    obtain ⟨t₂, ht₂mem', hgt₂, hleft⟩ :=
      exists_first_return hr't₁ hgcontOn hgr'lt ht₁gt.le
    have ht₂gt : r' < t₂ := ht₂mem'.1
    have ht₂mem : t₂ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [hr.1, hrr', ht₂gt], lt_of_le_of_lt ht₂mem'.2 ht₁T⟩
    have hdgt₂ : 0 ≤ dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle)) :=
      nonneg_of_first_return ht₂gt (hgderiv t₂ ht₂mem) hgt₂ hleft
    -- the transverse signs at the first return
    obtain ⟨A, hA, C, hC, e1, e2, e3, e4⟩ :=
      exists_frame_contacts hcomp hne (hdh t₂ ht₂mem) (hdj t₂ ht₂mem)
    obtain ⟨k1, k2, k3, k4⟩ := hcoords t₂ hgt₂ A C e1 e2 e3 e4
    have hframeR : normalVector (r : Real.Angle) =
        Real.cos (t₂ - r) • normalVector (t₂ : Real.Angle) -
          Real.sin (t₂ - r) • tangentVector (t₂ : Real.Angle) := by
      have hrew : ((r : ℝ) : Real.Angle) = ((t₂ + -(t₂ - r) : ℝ) : Real.Angle) := by
        congr 1; ring
      rw [hrew, normalVector_add_real t₂ (-(t₂ - r)), Real.cos_neg, Real.sin_neg]
      module
    have hframeT : normalVector ((Real.pi / 2 : ℝ) : Real.Angle) =
        Real.sin t₂ • normalVector (t₂ : Real.Angle) +
          Real.cos t₂ • tangentVector (t₂ : Real.Angle) := by
      have hrew : ((Real.pi / 2 : ℝ) : Real.Angle) =
          ((t₂ + (Real.pi / 2 - t₂) : ℝ) : Real.Angle) := by norm_num
      rw [hrew, normalVector_add_real t₂ (Real.pi / 2 - t₂), Real.cos_pi_div_two_sub,
        Real.sin_pi_div_two_sub]
    have hAT : inner ℝ (A - p) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.sin t₂ * 1 + Real.cos t₂ *
          (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeT, inner_add_right, real_inner_smul_right, real_inner_smul_right, k1, k2]
    have hstrip : Real.sin t₂ + Real.cos t₂ *
        (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) ≤ 1 := by
      have h1 := inner_le_supportValue_of_isCompact hcomp hA ((Real.pi / 2 : ℝ) : Real.Angle)
      rw [htop] at h1
      have h2 : inner ℝ (A - p) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
        rw [inner_sub_left]
        linarith only [h1, hlow p hps]
      rw [hAT] at h2
      linarith only [h2]
    obtain ⟨hs1, hs2, hs3⟩ := chord_signs hr.1 (by linarith only [hrr', ht₂gt])
      ht₂mem.2 hdgt₂ (halpha t₂ ht₂mem) (hbeta t₂ ht₂mem) hstrip
    have hAr : inner ℝ (A - p) (normalVector (r : Real.Angle)) =
        Real.cos (t₂ - r) * 1 - Real.sin (t₂ - r) *
          (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeR, inner_sub_right, real_inner_smul_right, real_inner_smul_right, k1, k2]
    have hCr : inner ℝ (C - p) (normalVector (r : Real.Angle)) =
        Real.cos (t₂ - r) * (-dj t₂ - (supportValue s (t₂ : Real.Angle) - 1)) -
          Real.sin (t₂ - r) * (supportValue s ((t₂ + Real.pi / 2 : ℝ) : Real.Angle) -
            inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeR, inner_sub_right, real_inner_smul_right, real_inner_smul_right, k3, k4]
    have hApos : 0 < inner ℝ (A - p) (normalVector (r : Real.Angle)) := by
      rw [hAr]; linarith only [hs1]
    have hCneg : inner ℝ (C - p) (normalVector (r : Real.Angle)) < 0 := by
      rw [hCr]; linarith only [hs2]
    have hcr := planeCrossProduct_nonpos_of_isMaxOn hconv hpline hmaxq hA hC hApos hCneg
    rw [planeCrossProduct_eq_inner_frame (A - p) (C - p) t₂, k1, k2, k3, k4] at hcr
    linarith only [hcr, hs3]
  refine ⟨p, hps, hpline, fun t ht => ?_⟩
  have hle := hmain t ht
  rw [hgval] at hle
  linarith only [hle]

/-- The lowered horizontal extremes of a right-angle cap lie under all right and left cuts. -/
theorem exists_cap_base_points (K : RightAngleCapSpace) :
    ∃ pR ∈ (K.1 : Set Point), ∃ pL ∈ (K.1 : Set Point),
      inner ℝ pR (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∧
      inner ℝ pL (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ pR (normalVector (t : Real.Angle))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ pL (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) := by
  have hheight : ∀ q ∈ (K.1 : Set Point), 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    intro q hq
    have hlo := K.inner_normalVector_pi_div_two_nonneg hq
    have hhi := inner_le_supportValue_of_isCompact K.1.isCompact hq
      ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.1] at hhi
    rw [inner_normalVector_pi_div_two] at hlo hhi
    exact ⟨hlo, hhi⟩
  obtain ⟨A, hA, hAeq⟩ := exists_mem_inner_eq_supportValue K.1 ((0 : ℝ) : Real.Angle)
  obtain ⟨C, hC, hCeq⟩ := exists_mem_inner_eq_supportValue K.1 ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero] at hAeq
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hCeq
  have hAmax : ∀ q ∈ (K.1 : Set Point), q 0 ≤ A 0 := by
    intro q hq
    have h := inner_le_supportValue_of_isCompact K.1.isCompact hq ((0 : ℝ) : Real.Angle)
    rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero] at h
    linarith only [h, hAeq]
  have hCmin : ∀ q ∈ (K.1 : Set Point), C 0 ≤ q 0 := by
    intro q hq
    have h := inner_le_supportValue_of_isCompact K.1.isCompact hq ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at h
    linarith only [h, hCeq]
  refine ⟨!₂[A 0, 0], basePoint_mem_of_rightAngleCap K hA, !₂[C 0, 0],
    basePoint_mem_of_rightAngleCap K hC, ?_, ?_, ?_, ?_⟩
  · rw [inner_normalVector_pi_div_two]; rfl
  · rw [inner_normalVector_pi_div_two]; rfl
  · intro t ht
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
    have hbound : supportValue (K.1 : Set Point) (t : Real.Angle) ≤ A 0 * Real.cos t + 1 := by
      refine csSup_le (K.1.nonempty.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      dsimp only
      rw [inner_normalVector_real]
      nlinarith only [hAmax q hq, (hheight q hq).2, hcos, hsin, hsin1]
    rw [inner_normalVector_real]
    show supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤ A 0 * Real.cos t + 0 * Real.sin t
    linarith only [hbound]
  · intro t ht
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    have hbound : supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
        -(C 0) * Real.sin t + 1 := by
      refine csSup_le (K.1.nonempty.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      dsimp only
      rw [inner_normalVector_real, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
      nlinarith only [hCmin q hq, (hheight q hq).2, hcos, hcos1, hsin]
    rw [inner_normalVector_real, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    show supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      C 0 * -Real.sin t + 0 * Real.cos t
    linarith only [hbound]

/-- The right cut line meets the cap, below the whole right cut family. -/
theorem exists_right_tail_contact (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ (K.1 : Set Point),
      inner ℝ p (normalVector (r : Real.Angle)) =
        supportValue (K.1 : Set Point) (r : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc r (Real.pi / 2),
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ p (normalVector (t : Real.Angle)) := by
  obtain ⟨dh, dj, h1, h2, h3, h4⟩ := capSupport_hasDerivAt K hinj
  exact exists_mem_inner_eq_sub_one_of_deriv_signs K.1.isCompact K.1.convex K.1.nonempty
    dh dj h1 h2 h3 h4 K.property.2.2.2.1
    (fun q hq => K.inner_normalVector_pi_div_two_nonneg hq) hr

/-- The left cut line meets the cap, below the whole left cut family. -/
theorem exists_left_tail_contact (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) {l : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ (K.1 : Set Point),
      inner ℝ p (normalVector ((l + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) l,
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  obtain ⟨dh, dj, h1, h2, h3, h4⟩ := capSupport_hasDerivAt K hinj
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have hsv : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point) (u : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi - u : ℝ) : Real.Angle) :=
    supportValue_reflectedBody_pi_div_two K.1
  have hfunS : (fun w : ℝ ↦ supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point)
      (w : Real.Angle)) =
      fun w : ℝ ↦ supportValue (K.1 : Set Point) ((Real.pi - w : ℝ) : Real.Angle) :=
    funext hsv
  have hrefl : ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Real.pi / 2 - u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun u hu => ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
  have hsvL : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point)
          ((u + Real.pi / 2 : ℝ) : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi / 2 - u : ℝ) : Real.Angle) := by
    intro u
    rw [hsv (u + Real.pi / 2),
      hcast _ _ (show Real.pi - (u + Real.pi / 2) = Real.pi / 2 - u by ring)]
  have hsvR : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point) (u : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi / 2 - u + Real.pi / 2 : ℝ) : Real.Angle) := by
    intro u
    rw [hsv u, hcast _ _ (show Real.pi - u = Real.pi / 2 - u + Real.pi / 2 by ring)]
  obtain ⟨q0, hq0s, hq0line, hq0bound⟩ :=
    exists_mem_inner_eq_sub_one_of_deriv_signs
      (reflectedBody (Real.pi / 2) K.1).isCompact (reflectedBody (Real.pi / 2) K.1).convex
      (reflectedBody (Real.pi / 2) K.1).nonempty
      (fun u ↦ -dj (Real.pi / 2 - u)) (fun u ↦ -dh (Real.pi / 2 - u))
      (by
        intro u hu
        have hF : HasDerivAt (fun w : ℝ ↦ supportValue (K.1 : Set Point) (w : Real.Angle))
            (dj (Real.pi / 2 - u)) (Real.pi - u) := by
          rw [show Real.pi - u = Real.pi / 2 - u + Real.pi / 2 by ring]
          exact h2 _ (hrefl u hu)
        rw [hfunS]
        exact HasDerivAt.comp_const_sub Real.pi u hF)
      (by
        intro u hu
        have hF : HasDerivAt (fun w : ℝ ↦ supportValue (K.1 : Set Point) (w : Real.Angle))
            (dh (Real.pi / 2 - u)) (Real.pi - (u + Real.pi / 2)) := by
          rw [show Real.pi - (u + Real.pi / 2) = Real.pi / 2 - u by ring]
          exact h1 _ (hrefl u hu)
        rw [hfunS]
        exact HasDerivAt.comp_const_sub Real.pi (u + Real.pi / 2) hF)
      (by
        intro u hu
        rw [hsvL u]
        linarith only [h4 _ (hrefl u hu)])
      (by
        intro u hu
        rw [hsvR u]
        linarith only [h3 _ (hrefl u hu)])
      (by
        rw [hsv (Real.pi / 2), hcast _ _ (show Real.pi - Real.pi / 2 = Real.pi / 2 by ring)]
        exact K.property.2.2.2.1)
      (by
        rintro q ⟨v, hv, rfl⟩
        rw [inner_capReflection_pi_div_two,
          hcast _ _ (show Real.pi - Real.pi / 2 = Real.pi / 2 by ring)]
        exact K.inner_normalVector_pi_div_two_nonneg hv)
      (show Real.pi / 2 - l ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from hrefl l hl)
  obtain ⟨p, hpK, rfl⟩ : ∃ p ∈ (K.1 : Set Point), capReflection (Real.pi / 2) p = q0 := hq0s
  refine ⟨p, hpK, ?_, ?_⟩
  · rw [inner_capReflection_pi_div_two,
      hcast _ _ (show Real.pi - (Real.pi / 2 - l) = l + Real.pi / 2 by ring)] at hq0line
    rw [hsv (Real.pi / 2 - l),
      hcast _ _ (show Real.pi - (Real.pi / 2 - l) = l + Real.pi / 2 by ring)] at hq0line
    exact hq0line
  · intro t ht
    have hw : Real.pi / 2 - t ∈ Set.Icc (Real.pi / 2 - l) (Real.pi / 2) :=
      ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
    have hb := hq0bound (Real.pi / 2 - t) hw
    rw [inner_capReflection_pi_div_two,
      hcast _ _ (show Real.pi - (Real.pi / 2 - t) = t + Real.pi / 2 by ring)] at hb
    rw [hsv (Real.pi / 2 - t),
      hcast _ _ (show Real.pi - (Real.pi / 2 - t) = t + Real.pi / 2 by ring)] at hb
    exact hb

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
# Cap / Tail / Bodies
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The distinguished inner wall, upper half-plane, fan point and corner on one side. -/
structure DistinguishedCapSide where
  /-- The distinguished inner supporting wall. -/
  wall : Set Point
  /-- The upper half-plane selected at the distinguished wall. -/
  upperHalfPlane : Set Point
  /-- The corresponding endpoint of the cap fan. -/
  fanPoint : Point
  /-- The inner hallway corner at the distinguished angle. -/
  corner : Point

/-- The right and left cap geometry at the two distinguished Gerver angles. -/
def distinguishedCapSides (K : RightAngleCapSpace) : DistinguishedCapSide × DistinguishedCapSide :=
  let r := paperGerverConstants.2.1
  let l := paperGerverConstants.2.2
  (⟨(rotatingHallwayParts (K.1 : Set Point) (r : Real.Angle)).b,
      (innerWallUpperHalfPlanes K r).1, (wedgeEndpoints K r).1, capInnerCorner K r⟩,
    ⟨(rotatingHallwayParts (K.1 : Set Point) (l : Real.Angle)).d,
      (innerWallUpperHalfPlanes K l).2, (wedgeEndpoints K l).2, capInnerCorner K l⟩)

/-- The right distinguished fan point is the right wedge endpoint at the right Gerver angle. -/
theorem distinguishedCapSides_fst_fanPoint (K : RightAngleCapSpace) :
    (distinguishedCapSides K).1.fanPoint = (wedgeEndpoints K paperGerverConstants.2.1).1 := rfl

/-- The right distinguished corner is the inner corner at the right Gerver angle. -/
theorem distinguishedCapSides_fst_corner (K : RightAngleCapSpace) :
    (distinguishedCapSides K).1.corner = capInnerCorner K paperGerverConstants.2.1 := rfl

/-- The left distinguished fan point is the left wedge endpoint at the left Gerver angle. -/
theorem distinguishedCapSides_snd_fanPoint (K : RightAngleCapSpace) :
    (distinguishedCapSides K).2.fanPoint = (wedgeEndpoints K paperGerverConstants.2.2).2 := rfl

/-- The left distinguished corner is the inner corner at the left Gerver angle. -/
theorem distinguishedCapSides_snd_corner (K : RightAngleCapSpace) :
    (distinguishedCapSides K).2.corner = capInnerCorner K paperGerverConstants.2.2 := rfl

/-- Canonical tails are convex bodies and satisfy all support and endpoint-line identities. -/
theorem canonicalTailSets_properties (K : SpecialCapSpace) :
    (canonicalTailSets K).1.Nonempty ∧ IsCompact (canonicalTailSets K).1 ∧ Convex ℝ
      (canonicalTailSets K).1 ∧ (canonicalTailSets K).1 ⊆ (K.1.1 : Set Point) ∧
    (canonicalTailSets K).2.Nonempty ∧ IsCompact (canonicalTailSets K).2 ∧ Convex ℝ
      (canonicalTailSets K).2 ∧ (canonicalTailSets K).2 ⊆ (K.1.1 : Set Point) ∧
    (∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      supportValue K.1.1 (t : Real.Angle) +
        supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) ≤ 1) ∧
    (∀ t ∈ ({paperGerverConstants.2.1, Real.pi / 2} : Set ℝ),
      supportValue K.1.1 (t : Real.Angle) +
        supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) = 1) ∧
    (supportingLineHalfPlane (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∧
    (supportingLineHalfPlane (canonicalTailSets K).1 ((Real.pi + paperGerverConstants.2.1 : ℝ) :
      Real.Angle)).1 =
      (distinguishedCapSides K.1).1.wall ∧
    (∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      supportValue K.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤ 1) ∧
    (∀ t ∈ ({0, paperGerverConstants.2.2} : Set ℝ),
      supportValue K.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1) ∧
    (supportingLineHalfPlane (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∧
    (supportingLineHalfPlane (canonicalTailSets K).2 ((3 * Real.pi / 2 + paperGerverConstants.2.2
      : ℝ) : Real.Angle)).1 =
      (distinguishedCapSides K.1).2.wall := by
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have htop : supportValue (K.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    K.1.property.2.2.2.1
  -- membership characterizations of the two tails
  have hBmem : ∀ p : Point, p ∈ (canonicalTailSets K).1 ↔
      (p ∈ (K.1.1 : Set Point) ∧ ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
        supportValue (K.1.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ p (normalVector (t : Real.Angle))) := by
    intro p
    simp [canonicalTailSets, innerWallUpperHalfPlanes, normalHalfPlane]
  have hDmem : ∀ p : Point, p ∈ (canonicalTailSets K).2 ↔
      (p ∈ (K.1.1 : Set Point) ∧ ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
        supportValue (K.1.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) := by
    intro p
    simp [canonicalTailSets, innerWallUpperHalfPlanes, normalHalfPlane]
  -- domain properties
  obtain ⟨pR, hpRK, pL, hpLK, hpRy, hpLy, hpRcut, hpLcut⟩ := exists_cap_base_points K.1
  have hpRB : pR ∈ (canonicalTailSets K).1 :=
    (hBmem pR).mpr ⟨hpRK, fun t ht => hpRcut t ⟨le_trans hr.1.le ht.1, ht.2⟩⟩
  have hpLD : pL ∈ (canonicalTailSets K).2 :=
    (hDmem pL).mpr ⟨hpLK, fun t ht => hpLcut t ⟨ht.1, le_trans ht.2 hl.2.le⟩⟩
  have hBne : (canonicalTailSets K).1.Nonempty := ⟨pR, hpRB⟩
  have hDne : (canonicalTailSets K).2.Nonempty := ⟨pL, hpLD⟩
  have hBsub : (canonicalTailSets K).1 ⊆ (K.1.1 : Set Point) := fun p hp => ((hBmem p).mp hp).1
  have hDsub : (canonicalTailSets K).2 ⊆ (K.1.1 : Set Point) := fun p hp => ((hDmem p).mp hp).1
  have hBcomp : IsCompact (canonicalTailSets K).1 :=
    K.1.1.isCompact.inter_right (isClosed_biInter fun t _ => isClosed_normalHalfPlane _ _ true)
  have hDcomp : IsCompact (canonicalTailSets K).2 :=
    K.1.1.isCompact.inter_right (isClosed_biInter fun t _ => isClosed_normalHalfPlane _ _ true)
  have hBconv : Convex ℝ (canonicalTailSets K).1 :=
    K.1.1.convex.inter (convex_iInter fun t => convex_iInter fun _ =>
      convex_normalHalfPlane _ _ true)
  have hDconv : Convex ℝ (canonicalTailSets K).2 :=
    K.1.1.convex.inter (convex_iInter fun t => convex_iInter fun _ =>
      convex_normalHalfPlane _ _ true)
  -- the two support inequalities
  have hBbound : ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) ≤
        1 - supportValue (K.1.1 : Set Point) (t : Real.Angle) := by
    intro t ht
    have h := supportValue_le_of_cut hBne (a := t) (b := Real.pi + t)
      (hcast _ _ (by ring)) (fun p hp => ((hBmem p).mp hp).2 t ht)
    linarith only [h]
  have hDbound : ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤
        1 - supportValue (K.1.1 : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) := by
    intro t ht
    have hc : ∀ p ∈ (canonicalTailSets K).2,
        supportValue (K.1.1 : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((Real.pi / 2 + t : ℝ) : Real.Angle)) := by
      intro p hp
      have h := ((hDmem p).mp hp).2 t ht
      rwa [hcast _ _ (show t + Real.pi / 2 = Real.pi / 2 + t by ring)] at h
    have h := supportValue_le_of_cut hDne (a := Real.pi / 2 + t) (b := 3 * Real.pi / 2 + t)
      (hcast _ _ (by ring)) hc
    linarith only [h]
  -- the four endpoint equalities
  have hBzero :
      supportValue (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm ?_ ?_
    · have h := hBbound (Real.pi / 2) ⟨hr.2.le, le_refl _⟩
      rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
      linarith only [h]
    · have h := le_supportValue_of_cut hBcomp (a := Real.pi / 2) (b := 3 * Real.pi / 2)
        (hcast _ _ (by ring)) hpRB hpRy
      linarith only [h]
  have hDzero :
      supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm ?_ ?_
    · have h := hDbound 0 ⟨le_refl _, hl.1.le⟩
      rw [hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring),
        hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring), htop] at h
      linarith only [h]
    · have h := le_supportValue_of_cut hDcomp (a := Real.pi / 2) (b := 3 * Real.pi / 2)
        (hcast _ _ (by ring)) hpLD hpLy
      linarith only [h]
  obtain ⟨pr, hprK, hprline, hprcut⟩ := exists_right_tail_contact K.1 K.property.1 hr
  obtain ⟨pl, hplK, hplline, hplcut⟩ := exists_left_tail_contact K.1 K.property.1 hl
  have hprB : pr ∈ (canonicalTailSets K).1 := (hBmem pr).mpr ⟨hprK, hprcut⟩
  have hplD : pl ∈ (canonicalTailSets K).2 := (hDmem pl).mpr ⟨hplK, hplcut⟩
  have hBeqR : supportValue (canonicalTailSets K).1
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    refine le_antisymm (hBbound _ ⟨le_refl _, hr.2.le⟩) ?_
    have h := le_supportValue_of_cut hBcomp (a := paperGerverConstants.2.1)
      (b := Real.pi + paperGerverConstants.2.1) (hcast _ _ (by ring)) hprB hprline
    linarith only [h]
  have hDeqL : supportValue (canonicalTailSets K).2
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    refine le_antisymm (hDbound _ ⟨hl.1.le, le_refl _⟩) ?_
    rw [hcast _ _ (show paperGerverConstants.2.2 + Real.pi / 2 =
      Real.pi / 2 + paperGerverConstants.2.2 by ring)] at hplline
    have h := le_supportValue_of_cut hDcomp (a := Real.pi / 2 + paperGerverConstants.2.2)
      (b := 3 * Real.pi / 2 + paperGerverConstants.2.2) (hcast _ _ (by ring)) hplD hplline
    linarith only [h]
  -- the distinguished walls
  have hwallR : (distinguishedCapSides K.1).1.wall =
      normalLine ((paperGerverConstants.2.1 : ℝ) : Real.Angle)
        (supportValue (K.1.1 : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) :=
    (rotatingHallwayParts_formulas (K.1.1 : Set Point)
      ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).2.2.2.2.1
  have hwallL : (distinguishedCapSides K.1).2.wall =
      normalLine
        (((paperGerverConstants.2.2 : ℝ) : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
        (supportValue (K.1.1 : Set Point)
          (((paperGerverConstants.2.2 : ℝ) : Real.Angle) +
            ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) :=
    (rotatingHallwayParts_formulas (K.1.1 : Set Point)
      ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).2.2.2.2.2.2.1
  have hangL :
      ((paperGerverConstants.2.2 : ℝ) : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
    exact hcast _ _ (by ring)
  refine ⟨hBne, hBcomp, hBconv, hBsub, hDne, hDcomp, hDconv, hDsub,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    linarith only [hBbound t ht]
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · linarith only [hBeqR]
    · rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), hBzero, htop]
      ring
  · show normalLine ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hBzero, normalLine_eq_of_cut (a := Real.pi / 2) (b := 3 * Real.pi / 2)
      (hcast _ _ (by ring)), neg_zero]
  · show normalLine ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).1
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)) = _
    rw [hBeqR, normalLine_eq_of_cut (a := paperGerverConstants.2.1)
      (b := Real.pi + paperGerverConstants.2.1) (hcast _ _ (by ring)), hwallR]
    congr 1
    ring
  · intro t ht
    linarith only [hDbound t ht]
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · rw [hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring),
        hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring), hDzero, htop]
      ring
    · linarith only [hDeqL]
  · show normalLine ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hDzero, normalLine_eq_of_cut (a := Real.pi / 2) (b := 3 * Real.pi / 2)
      (hcast _ _ (by ring)), neg_zero]
  · show normalLine ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).2
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) = _
    rw [hDeqL, normalLine_eq_of_cut (a := Real.pi / 2 + paperGerverConstants.2.2)
      (b := 3 * Real.pi / 2 + paperGerverConstants.2.2) (hcast _ _ (by ring)), hwallL, hangL]
    congr 1
    ring

/-- The inner corner's normal support coordinate is the cap's support value less one. -/
theorem inner_capInnerCorner_normalVector (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) (t : Real.Angle) - 1 := by
  have hform := (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1
  show inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
    (normalVector (t : Real.Angle)) = _
  rw [hform, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_normalVector_self, inner_tangentVector_normalVector_real]
  simp

/-- The inner corner's tangent support coordinate is the quarter-turned support value less one. -/
theorem inner_capInnerCorner_tangentVector (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
  have hform := (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1
  show inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
    (tangentVector (t : Real.Angle)) = _
  rw [hform, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_tangentVector_tangentVector, inner_normalVector_tangentVector,
    ← Real.Angle.coe_add]
  simp

/-- A point whose displacement from the inner corner has negative coordinates in the rotating
frame at time `t` lies in the open inward quadrant at that time. -/
theorem mem_innerQuadrant_of_frame_coordinates_neg (K : RightAngleCapSpace) (t : ℝ) (q : Point)
    (h1 : (q 0 - capInnerCorner K t 0) * Real.cos t +
      (q 1 - capInnerCorner K t 1) * Real.sin t < 0)
    (h2 : -((q 0 - capInnerCorner K t 0) * Real.sin t) +
      (q 1 - capInnerCorner K t 1) * Real.cos t < 0) :
    q ∈ innerQuadrant (K.val : Set Point) t := by
  have e1 : inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue (K.val : Set Point) (t : Real.Angle) - 1 := by
    rw [← inner_capInnerCorner_normalVector K t, inner_normalVector_real,
      inner_normalVector_real]
    linarith only [h1]
  have e2 : inner ℝ q (tangentVector (t : Real.Angle)) <
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    rw [← inner_capInnerCorner_tangentVector K t, inner_tangentVector_real,
      inner_tangentVector_real]
    linarith only [h2]
  refine ⟨e1, ?_⟩
  show inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
  rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
  exact e2

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
# Cap / Tail / Extension
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The canonical tail sets give an admissible cap-tail triple with exactly these carriers. -/
theorem exists_canonicalCapTail (K : SpecialCapSpace) :
    ∃ T : CapTailSpace, T.cap = K ∧
      (T.rightBody : Set Point) = (canonicalTailSets K).1 ∧
      (T.leftBody : Set Point) = (canonicalTailSets K).2 := by
  obtain ⟨hBne, hBcp, hBcv, hBsub, hDne, hDcp, hDcv, hDsub, hBbd, hBeq, -, -,
    hDbd, hDeq, -, -⟩ := canonicalTailSets_properties K
  exact ⟨{ cap := K
           rightBody := ⟨(canonicalTailSets K).1, hBcv, hBcp, hBne⟩
           leftBody := ⟨(canonicalTailSets K).2, hDcv, hDcp, hDne⟩
           right_subset := hBsub
           left_subset := hDsub
           right_bound := hBbd
           right_eq := hBeq
           left_bound := hDbd
           left_eq := hDeq }, rfl, rfl, rfl⟩

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
# Cap / Tail / Separation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A point above both distinguished inner walls of a special cap lies above mid-height. -/
private theorem lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes (K : SpecialCapSpace)
    {q : Point} (h₁ : q ∈ (distinguishedCapSides K.val).1.upperHalfPlane)
    (h₂ : q ∈ (distinguishedCapSides K.val).2.upperHalfPlane) :
    (horizontalMax K.val.val - horizontalMin K.val.val) / 2 < q 1 := by
  obtain ⟨hrIoo, hlIoo, hrl⟩ := paperGerverConstants_snd_mem_Ioo
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, p, hpbox, hpeq, -⟩ := gerver_parameter_identification
    exact (hall p hpbox hpeq).2.2.2.2.2.2.2.1
  have hcosr : (1249 : ℝ) / 1250 ≤ Real.cos paperGerverConstants.2.1 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := paperGerverConstants.2.1)
    nlinarith only [h, hphi, hrIoo.1]
  have hsinle : Real.sin paperGerverConstants.2.1 ≤ paperGerverConstants.2.1 :=
    Real.sin_le hrIoo.1.le
  have hcpos : (0 : ℝ) < Real.cos paperGerverConstants.2.1 := by linarith
  have hsinr : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.1 :=
    (Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [hrIoo.2, Real.pi_pos])).le
  have hsinl : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.2 :=
    (Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [hlIoo.2, Real.pi_pos])).le
  have hcosl : (0 : ℝ) ≤ Real.cos paperGerverConstants.2.2 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hlIoo.1, Real.pi_pos], hlIoo.2⟩).le
  have hleq : paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 := by linarith
  have hsinleq : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [hleq, Real.sin_pi_div_two_sub]
  have hcosleq : Real.cos paperGerverConstants.2.2 = Real.sin paperGerverConstants.2.1 := by
    rw [hleq, Real.cos_pi_div_two_sub]
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
  -- the two defining support inequalities of the closed tail half-planes
  have h₁' : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ q (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) := h₁
  have h₂' : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ q
        (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) := h₂
  rw [inner_normalVector_real] at h₁'
  rw [inner_normalVector_real, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two, hsinleq, hcosleq] at h₂'
  -- the strict product bound of the informal proof
  rw [← supportValue_zero_eq_horizontalMax, sub_eq_add_neg,
    ← supportValue_pi_eq_neg_horizontalMin]
  by_contra hcon
  rw [not_lt] at hcon
  have hcs : (1199 : ℝ) / 1250 ≤
      Real.cos paperGerverConstants.2.1 - Real.sin paperGerverConstants.2.1 := by linarith
  have hprod : (2 : ℝ) < (Real.cos paperGerverConstants.2.1 -
      Real.sin paperGerverConstants.2.1) *
      (supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) := by
    have h := mul_le_mul hcs hwidth (by norm_num) (by linarith)
    linarith
  have hmul : q 1 * Real.sin paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) / 2 *
        Real.sin paperGerverConstants.2.1 :=
    mul_le_mul_of_nonneg_right hcon hsinr
  nlinarith only [h₁', h₂', hlowR, hlowL, hmul, hprod]

theorem cap_and_niche_tail_separation (K : SpecialCapSpace) :
    ((K.val.val : Set Point) ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∩
        (distinguishedCapSides K.val).2.upperHalfPlane = ∅ ∧
    (capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∩
        (distinguishedCapSides K.val).2.upperHalfPlane = ∅ := by
  have hwidth : (11 : ℝ) / 5 ≤ horizontalMax K.val.val - horizontalMin K.val.val :=
    K.property.2.trans K.val.area_le_horizontalWidth
  constructor
  · refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨⟨hqK, h₁⟩, h₂⟩
    have hmid := lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes K h₁ h₂
    have hq := (K.val.mem_horizontalStrip hqK).2
    linarith
  · refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨⟨hqN, h₁⟩, h₂⟩
    have hmid := lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes K h₁ h₂
    have hq := (capNiche_subset_rectangle K.val hqN).2.2.2
    linarith

end MovingSofa

end

end

end
