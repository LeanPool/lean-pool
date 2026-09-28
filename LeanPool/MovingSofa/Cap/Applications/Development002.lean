/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development005
public import LeanPool.MovingSofa.Polygon.Applications.Development001

public import LeanPool.MovingSofa.Polygon.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Cap.BalancedExistence`.
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
# Cap / Balanced Existence
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

private def polygonSeedSet (Θ : AngleSet) : Set Point :=
  capFan Θ.angle ∩ ⋂ t ∈ angleDomain Θ,
    normalHalfPlane (t : Real.Angle) 1 false false

private theorem mem_polygonSeedSet_iff (Θ : AngleSet) (p : Point) :
    p ∈ polygonSeedSet Θ ↔
      p ∈ capFan Θ.angle ∧
        ∀ t ∈ angleDomain Θ, inner ℝ p (normalVector (t : Real.Angle)) ≤ 1 := by
  simp [polygonSeedSet, normalHalfPlane]

private theorem normalVector_mem_polygonSeedSet (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) : normalVector (t : Real.Angle) ∈ polygonSeedSet Θ := by
  apply (mem_polygonSeedSet_iff Θ _).mpr
  have htupper : t ∈ capUpperAngles Θ.angle := by
    rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  have ht0 : 0 ≤ t := by
    rcases htupper with ⟨h0, _⟩ | ⟨hT, _⟩
    · exact h0
    · linarith [Real.pi_pos]
  have htpi : t ≤ Real.pi := by
    rcases htupper with ⟨_, hω⟩ | ⟨_, hω⟩
    · linarith [Θ.angle_le, Real.pi_pos]
    · linarith [Θ.angle_le]
  have htω : -(Real.pi / 2) ≤ t - Θ.angle ∧ t - Θ.angle ≤ Real.pi / 2 := by
    rcases htupper with ⟨h0, hω⟩ | ⟨hT, hω⟩ <;>
      constructor <;> linarith [Θ.angle_le]
  constructor
  · constructor
    · change 0 ≤ inner ℝ (normalVector (t : Real.Angle))
        (normalVector (Θ.angle : Real.Angle))
      rw [inner_normalVector_normalVector]
      exact Real.cos_nonneg_of_mem_Icc htω
    · change 0 ≤ inner ℝ (normalVector (t : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [normalVector, frame, PiLp.inner_apply]
      exact Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  · intro s hs
    calc
      inner ℝ (normalVector (t : Real.Angle)) (normalVector (s : Real.Angle)) ≤
          ‖normalVector (t : Real.Angle)‖ * ‖normalVector (s : Real.Angle)‖ :=
        real_inner_le_norm _ _
      _ = 1 := by rw [norm_normalVector_real, norm_normalVector_real, mul_one]

private theorem zero_mem_polygonSeedSet (Θ : AngleSet) :
    (0 : Point) ∈ polygonSeedSet Θ := by
  rw [mem_polygonSeedSet_iff]
  simp [capFan, normalHalfPlane]

private theorem convex_polygonSeedSet (Θ : AngleSet) : Convex ℝ (polygonSeedSet Θ) := by
  rw [polygonSeedSet]
  apply Convex.inter
  · apply Convex.inter
    · exact convex_halfSpace_ge
        ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩ 0
    · exact convex_halfSpace_ge
        ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩ 0
  · apply convex_iInter
    intro t
    apply convex_iInter
    intro _
    exact convex_halfSpace_le
      ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩ 1

private theorem isClosed_polygonSeedSet (Θ : AngleSet) : IsClosed (polygonSeedSet Θ) := by
  rw [polygonSeedSet]
  apply IsClosed.inter
  · apply IsClosed.inter <;> exact isClosed_le continuous_const (by fun_prop)
  · apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro _
    exact isClosed_le (by fun_prop) continuous_const

private theorem isBounded_polygonSeedSet (Θ : AngleSet) :
    Bornology.IsBounded (polygonSeedSet Θ) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  let l := -1 / Real.sin t
  let r := 1 / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + 1, ?_⟩
  intro p hp
  obtain ⟨hfan, hupp⟩ := (mem_polygonSeedSet_iff Θ p).mp hp
  have htmem : t ∈ angleDomain Θ := Or.inl (Or.inl ht)
  have htmem' : t + Real.pi / 2 ∈ angleDomain Θ :=
    Or.inl (Or.inr ⟨t, ht, rfl⟩)
  have ha := hupp t htmem
  have hb := hupp (t + Real.pi / 2) htmem'
  have hy0 : 0 ≤ p 1 := by
    have := hfan.2
    simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using this
  have hy1 : p 1 ≤ 1 := by
    have htop := hupp (Real.pi / 2) (Or.inr (Or.inr rfl))
    simpa [normalVector, frame, PiLp.inner_apply] using htop
  simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add] at ha hb
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hs).mpr
    dsimp [l]
    nlinarith [mul_nonneg hc.le hy0]
  have hr : p 0 ≤ r := by
    apply (le_div_iff₀ hc).mpr
    dsimp [r]
    nlinarith [mul_nonneg hs.le hy0]
  have hx : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self r, abs_nonneg l, abs_nonneg r]
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hM).mpr hx
  have hy2 : (p 1) ^ 2 ≤ 1 := by nlinarith
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
  nlinarith [norm_nonneg p]

private def polygonSeedBody (Θ : AngleSet) : ConvexBody Point where
  carrier := polygonSeedSet Θ
  convex' := convex_polygonSeedSet Θ
  isCompact' := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_polygonSeedSet Θ, isBounded_polygonSeedSet Θ⟩
  nonempty' := ⟨0, zero_mem_polygonSeedSet Θ⟩

private theorem supportValue_polygonSeedBody_upper (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) :
    supportValue (polygonSeedBody Θ) (t : Real.Angle) = 1 := by
  apply le_antisymm
  · apply supportValue_le_of_subset_normalHalfPlane
    intro p hp
    exact ((mem_polygonSeedSet_iff Θ p).mp hp).2 t ht
  · have hmem := normalVector_mem_polygonSeedSet Θ ht
    have hle := inner_le_supportValue (polygonSeedBody Θ) hmem (t : Real.Angle)
    rwa [inner_normalVector_self] at hle

private theorem supportValue_polygonSeedBody_lower_angle (Θ : AngleSet) :
    supportValue (polygonSeedBody Θ) ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 0 := by
  apply le_antisymm
  · apply csSup_le ((polygonSeedBody Θ).nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hfan := ((mem_polygonSeedSet_iff Θ p).mp hp).1.1
    change 0 ≤ inner ℝ p (normalVector (Θ.angle : Real.Angle)) at hfan
    change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ 0
    rw [normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan
  · apply le_csSup ((polygonSeedBody Θ).isCompact.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
    exact ⟨0, zero_mem_polygonSeedSet Θ, by simp⟩

private theorem supportValue_polygonSeedBody_lower_vertical (Θ : AngleSet) :
    supportValue (polygonSeedBody Θ) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
  apply le_antisymm
  · apply csSup_le ((polygonSeedBody Θ).nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hfan := ((mem_polygonSeedSet_iff Θ p).mp hp).1.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hfan
    change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi by ring,
      normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan
  · apply le_csSup ((polygonSeedBody Θ).isCompact.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
    exact ⟨0, zero_mem_polygonSeedSet Θ, by simp⟩

private theorem polygonSeedBody_representation (Θ : AngleSet) :
    HasHalfPlaneRepresentation (polygonSeedBody Θ)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪
        capLowerNormals Θ.angle) := by
  let C : Set (Real.Angle × ℝ) :=
    (fun t : ℝ ↦ ((t : Real.Angle), 1)) '' angleDomain Θ ∪
      {(((Θ.angle + Real.pi : ℝ) : Real.Angle), 0),
        (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)}
  refine ⟨C, ?_, ?_⟩
  · rintro c (⟨t, ht, rfl⟩ | hc)
    · exact Or.inl ⟨t, ht, rfl⟩
    · rcases hc with rfl | hc
      · exact Or.inr (Or.inl rfl)
      · have hc' : c = ((((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)) := hc
        subst c
        exact Or.inr (Or.inr rfl)
  · ext p
    change p ∈ polygonSeedSet Θ ↔ _
    rw [mem_polygonSeedSet_iff]
    simp only [C, Set.mem_iInter, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, normalHalfPlane, Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro ⟨hfan, hupp⟩ c (⟨t, ht, rfl⟩ | hc)
      · exact hupp t ht
      · rcases hc with rfl | rfl
        · change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ 0
          rw [normalVector_add_pi, inner_neg_right]
          exact neg_nonpos.mpr hfan.1
        · change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
          rw [inner_normalVector_three_pi_div_two]
          have hy : 0 ≤ p 1 := by
            simpa [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hfan.2
          exact neg_nonpos.mpr hy
    · intro hp
      constructor
      · constructor
        · change 0 ≤ inner ℝ p (normalVector (Θ.angle : Real.Angle))
          have h := hp (((Θ.angle + Real.pi : ℝ) : Real.Angle), 0)
            (Or.inr (Or.inl rfl))
          change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ 0 at h
          rw [normalVector_add_pi, inner_neg_right] at h
          exact neg_nonpos.mp h
        · have h := hp (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)
            (Or.inr (Or.inr rfl))
          change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0 at h
          rw [inner_normalVector_three_pi_div_two] at h
          change p ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false
          simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using h
      · intro t ht
        exact hp ((t : Real.Angle), 1) (Or.inl ⟨t, ht, rfl⟩)

private def polygonSeedCap (Θ : AngleSet) : PolygonCapSpace Θ := by
  let K := polygonSeedBody Θ
  have hrepr := polygonSeedBody_representation Θ
  have hdomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
    rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  have hcaprepr : HasHalfPlaneRepresentation K
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
        capLowerNormals Θ.angle) := by
    obtain ⟨C, hC, hKC⟩ := hrepr
    refine ⟨C, ?_, hKC⟩
    intro c hc
    rcases hC c hc with ⟨t, ht, heq⟩ | ht
    · exact Or.inl ⟨t, hdomain ht, heq⟩
    · exact Or.inr ht
  have hcap : IsCap Θ.angle K := by
    refine ⟨Θ.angle_pos, Θ.angle_le, ?_, ?_, ?_, ?_, hcaprepr⟩
    · exact supportValue_polygonSeedBody_upper Θ (Or.inr (Or.inl rfl))
    · exact supportValue_polygonSeedBody_upper Θ (Or.inr (Or.inr rfl))
    · exact supportValue_polygonSeedBody_lower_angle Θ
    · exact supportValue_polygonSeedBody_lower_vertical Θ
  exact ⟨⟨K, hcap⟩, hrepr⟩

private theorem supportValue_polygonSeedCap_upper (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) :
    supportValue (polygonSeedCap Θ).val.val (t : Real.Angle) = 1 := by
  change supportValue (polygonSeedBody Θ) (t : Real.Angle) = 1
  exact supportValue_polygonSeedBody_upper Θ ht

private theorem polygonNiche_polygonSeedCap (Θ : AngleSet) :
    polygonNiche Θ (polygonSeedCap Θ).val = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hfan, hq⟩ := hp
  obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hq
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  have hy : 0 ≤ p 1 := by
    have := hfan.2
    simpa [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply] using this
  have h₁ := hq.1
  have h₂ := hq.2
  change inner ℝ p (normalVector (t : Real.Angle)) <
    supportValue (polygonSeedCap Θ).val.val (t : Real.Angle) - 1 at h₁
  change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
    supportValue (polygonSeedCap Θ).val.val
      ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h₂
  rw [supportValue_polygonSeedCap_upper Θ (Or.inl (Or.inl ht))] at h₁
  rw [supportValue_polygonSeedCap_upper Θ (Or.inl (Or.inr ⟨t, ht, rfl⟩))] at h₂
  simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add] at h₁ h₂
  have h₁' := mul_lt_mul_of_pos_left h₁ hs
  have h₂' := mul_lt_mul_of_pos_left h₂ hc
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem polygonSeedCap_area_nonneg (Θ : AngleSet) :
    0 ≤ polygonAreaFunctional Θ (polygonSeedCap Θ).val := by
  rw [(polygonArea_upperBound Θ).1, polygonNiche_polygonSeedCap]
  simp [ClassicalResults.area]

private theorem angleDomain_distance_midpoint (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) :
    Real.pi / 4 - Θ.angle / 2 ≤
        |t - (Real.pi / 4 + Θ.angle / 2)| ∧
      |t - (Real.pi / 4 + Θ.angle / 2)| ≤ Real.pi / 2 := by
  have htupper : t ∈ capUpperAngles Θ.angle := by
    rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  rcases htupper with ⟨ht0, htω⟩ | ⟨htT, htωT⟩
  · rw [abs_of_nonpos (by linarith [Θ.angle_le])]
    constructor <;> linarith [Θ.angle_le, Real.pi_pos]
  · rw [abs_of_nonneg (by linarith [Θ.angle_le])]
    constructor <;> linarith [Θ.angle_le]

private theorem stripParallelogram_top_mem_polygonSeedCap (Θ : AngleSet) :
    (stripParallelogram Θ.angle).2.2 ∈ ((polygonSeedCap Θ).val.val : Set Point) := by
  change (stripParallelogram Θ.angle).2.2 ∈ polygonSeedSet Θ
  apply (mem_polygonSeedSet_iff Θ _).mpr
  let β := Real.pi / 4 - Θ.angle / 2
  let m := Real.pi / 4 + Θ.angle / 2
  have hβ0 : 0 ≤ β := by dsimp [β]; linarith [Θ.angle_le]
  have hβlt : β < Real.pi / 2 := by
    dsimp [β]
    linarith [Θ.angle_pos, Real.pi_pos]
  have hcosβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hβlt⟩
  have htanβ : 0 ≤ Real.tan β :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hβ0 hβlt.le
  have hcosω : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
  have hsinω : 0 ≤ Real.sin Θ.angle := Real.sin_nonneg_of_nonneg_of_le_pi
    Θ.angle_pos.le (by linarith [Θ.angle_le])
  constructor
  · constructor
    · change 0 ≤ inner ℝ (!₂[Real.tan β, 1] : Point)
        (normalVector (Θ.angle : Real.Angle))
      simp [normalVector, frame, PiLp.inner_apply]
      positivity
    · change 0 ≤ inner ℝ (!₂[Real.tan β, 1] : Point)
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [normalVector, frame, PiLp.inner_apply]
  · intro t ht
    have hd := angleDomain_distance_midpoint Θ ht
    have hdpi : |t - m| ≤ Real.pi := by dsimp [m]; linarith [hd.2, Real.pi_pos]
    have hcosabs : Real.cos |t - m| ≤ Real.cos β :=
      Real.cos_le_cos_of_nonneg_of_le_pi hβ0 hdpi (by simpa [β, m] using hd.1)
    have hcos : Real.cos (t - m) ≤ Real.cos β := by
      simpa only [Real.cos_abs] using hcosabs
    change inner ℝ (!₂[Real.tan β, 1] : Point) (normalVector (t : Real.Angle)) ≤ 1
    simp only [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.inner_apply]
    have htrig : Real.sin β * Real.cos t + Real.cos β * Real.sin t =
        Real.cos (t - m) := by
      calc
        Real.sin β * Real.cos t + Real.cos β * Real.sin t =
            Real.sin (β + t) := by rw [Real.sin_add]
        _ = Real.cos (Real.pi / 2 - (β + t)) := by rw [Real.cos_pi_div_two_sub]
        _ = Real.cos (m - t) := by congr 1; dsimp [β, m]; ring
        _ = Real.cos (t - m) := by rw [← Real.cos_neg]; congr 1; ring
    apply le_of_mul_le_mul_left ?_ hcosβ
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcosβ.ne']
    change Real.sin β * Real.cos t + Real.cos β * Real.sin t ≤ Real.cos β
    rw [htrig]
    exact hcos

private def IsPolygonMaximizationCandidate (Θ : AngleSet) (K : PolygonCapSpace Θ) : Prop :=
  (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) ∧
    0 ≤ polygonAreaFunctional Θ K.val

private theorem exists_compact_polygonCap_bound (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (t : ℝ) (ht : t ∈ Set.Ioo 0 ω) :
    ∃ A : Set Point, IsCompact A ∧ ∀ (Θ : AngleSet), Θ.angle = ω →
      t ∈ Θ.directions → ∀ K : PolygonCapSpace Θ,
        IsPolygonMaximizationCandidate Θ K → (K.val.val : Set Point) ⊆ A := by
  obtain ⟨c, hc, hwidth⟩ := polygonCap_width_bound ω t hω hω' ht
  let o := (stripParallelogram ω).2.2
  let R := c + |o 0| + 2
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  intro Θ hΘ hdir K hK p hp
  subst ω
  have hw := hwidth Θ rfl hdir K hK.2
  have hp0 := inner_le_supportValue K.val.val hp (0 : Real.Angle)
  have hpπ := inner_le_supportValue K.val.val hp (Real.pi : Real.Angle)
  have ho0 := inner_le_supportValue K.val.val hK.1 (0 : Real.Angle)
  have hoπ := inner_le_supportValue K.val.val hK.1 (Real.pi : Real.Angle)
  simp [directionalWidth, supportValue, normalVector, frame, PiLp.inner_apply]
    at hw hp0 hpπ ho0 hoπ
  have hpx : |p 0| ≤ c + |o 0| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (o 0)]
    · linarith [le_abs_self (o 0)]
  have hpy := K.val.mem_horizontalStrip hp
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  rw [Metric.mem_closedBall]
  have hpx2 := (sq_le_sq₀ (abs_nonneg (p 0)) (by positivity : 0 ≤ c + |o 0|)).mpr hpx
  have hpy2 : (p 1) ^ 2 ≤ 1 := by nlinarith [hpy.1, hpy.2]
  have ha0 : 0 ≤ c + |o 0| := by positivity
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hpx2
  have hsquare : ‖p‖ ^ 2 ≤ R ^ 2 := by
    dsimp [R]
    nlinarith
  simpa [dist_eq_norm] using
    ((sq_le_sq₀ (norm_nonneg p) hR0).mp hsquare)

private theorem exists_compact_polygonCandidate_bound (Θ : AngleSet) :
    ∃ A : Set Point, IsCompact A ∧ ∀ K : PolygonCapSpace Θ,
      IsPolygonMaximizationCandidate Θ K → (K.val.val : Set Point) ⊆ A := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCap_bound Θ.angle
    Θ.angle_pos Θ.angle_le t (Θ.interior t ht)
  exact ⟨A, hA, fun K hK ↦ hbound Θ rfl ht K hK⟩

private theorem tendsto_supportValue_of_hausdorffBodies
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ supportValue (K i) (t : Real.Angle)) atTop
      (𝓝 (supportValue L (t : Real.Angle))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro i
  simpa only [Real.dist_eq, vectorSupport, supportValue] using
    (compactSet_support_continuity (K i) L (K i).nonempty
      (K i).isCompact L.nonempty L.isCompact).2.1
        (normalVector (t : Real.Angle)) (norm_normalVector_real t)

private theorem polygonCandidate_values_bddAbove (Θ : AngleSet) :
    BddAbove {r : ℝ | ∃ K : PolygonCapSpace Θ,
      IsPolygonMaximizationCandidate Θ K ∧ polygonAreaFunctional Θ K.val = r} := by
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCandidate_bound Θ
  refine ⟨ClassicalResults.area A, ?_⟩
  rintro r ⟨K, hK, rfl⟩
  rw [(polygonArea_upperBound Θ).1 K]
  calc
    ClassicalResults.area (K.val.val : Set Point) -
        ClassicalResults.area (polygonNiche Θ K.val) ≤
        ClassicalResults.area (K.val.val : Set Point) := by
      linarith [show 0 ≤ ClassicalResults.area (polygonNiche Θ K.val) from
        ENNReal.toReal_nonneg]
    _ ≤ ClassicalResults.area A := by
      exact ENNReal.toReal_mono hA.measure_ne_top (MeasureTheory.measure_mono (hbound K hK))

private theorem supportValue_limit_eq {K : ℕ → ConvexBody Point} {L : ConvexBody Point}
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (t c : ℝ)
    (hvalue : ∀ i, supportValue (K i) (t : Real.Angle) = c) :
    supportValue L (t : Real.Angle) = c := by
  apply tendsto_nhds_unique (tendsto_supportValue_of_hausdorffBodies K L hlim t)
  simpa only [hvalue] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c))

private theorem mem_hausdorffLimit {K : ℕ → ConvexBody Point} {L : ConvexBody Point}
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i : Set Point)
    (L : Set Point)) atTop (𝓝 0)) {p : Point} (hp : ∀ i, p ∈ (K i : Set Point)) :
    p ∈ (L : Set Point) := by
  have hle : (fun _ : ℕ ↦ Metric.infDist p (L : Set Point)) ≤ᶠ[atTop]
      (fun i ↦ Metric.hausdorffDist (K i : Set Point) (L : Set Point)) := by
    filter_upwards [] with i
    exact Metric.infDist_le_hausdorffDist_of_mem (hp i)
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K i).nonempty L.nonempty (K i).isCompact.isBounded L.isCompact.isBounded)
  have hz : Metric.infDist p (L : Set Point) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  exact (L.isClosed.mem_iff_infDist_zero L.nonempty).mpr
    (le_antisymm hz Metric.infDist_nonneg)

private theorem exists_polygonCap_of_hausdorffLimit (Θ : AngleSet)
    (K : ℕ → PolygonCapSpace Θ) (L : ConvexBody Point)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i).val.val (L : Set Point))
      atTop (𝓝 0)) :
    ∃ P : PolygonCapSpace Θ, (P.val.val : Set Point) = (L : Set Point) := by
  let N : Set Real.Angle :=
    ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  let U : Set Point := normalVector '' N
  have hU : ∀ u ∈ U, ‖u‖ = 1 := by
    rintro u ⟨a, ha, rfl⟩
    rcases ha with ⟨t, _, rfl⟩ | ha
    · exact norm_normalVector_real t
    · rcases ha with rfl | rfl
      · exact norm_normalVector_real (Θ.angle + Real.pi)
      · exact norm_normalVector_real (3 * Real.pi / 2)
  have hK (i : ℕ) : ((K i).val.val : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K i).val.val u} := by
    calc
      ((K i).val.val : Set Point) = ⋂ a ∈ N,
          normalHalfPlane a (supportValue (K i).val.val a) false false :=
        (K i).property.eq_iInter_supportValue
      _ = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport (K i).val.val u} := by
        ext p
        simp [U, normalHalfPlane, supportValue, vectorSupport]
  have hclosed := fixedNormalBody_closed U hU (fun i ↦ (K i).val.val) L hK hlim
  have hrepr : HasHalfPlaneRepresentation L N := by
    refine ⟨(fun t ↦ (t, supportValue L t)) '' N, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ht
    · calc
        (L : Set Point) = ⋂ u ∈ U,
            {x | inner ℝ x u ≤ vectorSupport L u} := hclosed
        _ = ⋂ t ∈ N, normalHalfPlane t (supportValue L t) false false := by
          ext p
          simp [U, normalHalfPlane, supportValue, vectorSupport]
        _ = ⋂ c ∈ (fun t ↦ (t, supportValue L t)) '' N,
            normalHalfPlane c.1 c.2 false false := by
          ext p
          simp
  have hω := supportValue_limit_eq hlim Θ.angle 1
    (fun i ↦ (K i).val.property.2.2.1)
  have hT := supportValue_limit_eq hlim (Real.pi / 2) 1
    (fun i ↦ (K i).val.property.2.2.2.1)
  have hωπ := supportValue_limit_eq hlim (Θ.angle + Real.pi) 0
    (fun i ↦ (K i).val.property.2.2.2.2.1)
  have h3T := supportValue_limit_eq hlim (3 * Real.pi / 2) 0
    (fun i ↦ (K i).val.property.2.2.2.2.2.1)
  have hdomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
    rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  have hcaprepr : HasHalfPlaneRepresentation L
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
        capLowerNormals Θ.angle) := by
    obtain ⟨C, hCN, hLC⟩ := hrepr
    refine ⟨C, ?_, hLC⟩
    intro c hc
    rcases hCN c hc with ⟨t, ht, heq⟩ | ht
    · exact Or.inl ⟨t, hdomain ht, heq⟩
    · exact Or.inr ht
  have hcap : IsCap Θ.angle L :=
    ⟨Θ.angle_pos, Θ.angle_le, hω, hT, hωπ, h3T, hcaprepr⟩
  exact ⟨⟨⟨L, hcap⟩, hrepr⟩, rfl⟩

private theorem exists_maximum_polygonCandidate (Θ : AngleSet) :
    ∃ K : PolygonCapSpace Θ, IsPolygonMaximizationCandidate Θ K ∧
      ∀ L : PolygonCapSpace Θ, IsPolygonMaximizationCandidate Θ L →
        polygonAreaFunctional Θ L.val ≤ polygonAreaFunctional Θ K.val := by
  let S : Set ℝ := {r | ∃ K : PolygonCapSpace Θ,
    IsPolygonMaximizationCandidate Θ K ∧ polygonAreaFunctional Θ K.val = r}
  have hS : S.Nonempty := by
    refine ⟨polygonAreaFunctional Θ (polygonSeedCap Θ).val, polygonSeedCap Θ, ?_, rfl⟩
    exact ⟨stripParallelogram_top_mem_polygonSeedCap Θ, polygonSeedCap_area_nonneg Θ⟩
  have hSbdd : BddAbove S := polygonCandidate_values_bddAbove Θ
  obtain ⟨u, _, hu, huS⟩ := exists_seq_tendsto_sSup hS hSbdd
  choose K hK hKu using huS
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCandidate_bound Θ
  obtain ⟨φ, L, hφ, hlim⟩ := convexBody_selection A hA (fun i ↦ (K i).val.val)
    (fun i ↦ hbound (K i) (hK i))
  obtain ⟨P, hPL⟩ := exists_polygonCap_of_hausdorffLimit Θ (fun i ↦ K (φ i)) L hlim
  have hlimP : Tendsto (fun i ↦ Metric.hausdorffDist ((K (φ i)).val.val : Set Point)
      (P.val.val : Set Point)) atTop (𝓝 0) := by
    simpa only [hPL] using hlim
  have hcont := (polygonArea_continuity Θ (fun i ↦ (K (φ i)).val) P.val hlimP).2
  have huφ : Tendsto (fun i ↦ u (φ i)) atTop (𝓝 (sSup S)) :=
    hu.comp hφ.tendsto_atTop
  have hfuncSup : polygonAreaFunctional Θ P.val = sSup S := by
    apply tendsto_nhds_unique hcont
    simpa only [hKu] using huφ
  have hPtop : (stripParallelogram Θ.angle).2.2 ∈ (P.val.val : Set Point) := by
    rw [hPL]
    exact mem_hausdorffLimit hlim (fun i ↦ (hK (φ i)).1)
  have hPnonneg : 0 ≤ polygonAreaFunctional Θ P.val := by
    apply ge_of_tendsto hcont
    exact Eventually.of_forall fun i ↦ (hK (φ i)).2
  refine ⟨P, ⟨hPtop, hPnonneg⟩, ?_⟩
  intro Q hQ
  rw [hfuncSup]
  exact le_csSup hSbdd ⟨Q, hQ, rfl⟩

private theorem innerQuadrant_translate (K : ConvexBody Point) (v : Point) (t : ℝ) :
    innerQuadrant (ConvexBody.translate K v : Set Point) t =
      (fun p ↦ p + v) '' innerQuadrant (K : Set Point) t := by
  have hsupp (a : Real.Angle) : supportValue (ConvexBody.translate K v) a =
      supportValue K a + inner ℝ v (normalVector a) := supportValue_image_add K v a
  ext q
  simp only [innerQuadrant, normalHalfPlane, Set.mem_inter_iff, Bool.false_eq_true,
    ↓reduceIte, Set.mem_image]
  rw [hsupp, hsupp]
  constructor
  · intro h
    change inner ℝ q (normalVector (t : Real.Angle)) <
        supportValue K (t : Real.Angle) + inner ℝ v (normalVector (t : Real.Angle)) - 1 ∧
      inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) +
          inner ℝ v (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) - 1 at h
    refine ⟨q - v, ?_, by simp⟩
    constructor
    · change inner ℝ (q - v) (normalVector (t : Real.Angle)) < _
      rw [inner_sub_left]
      linarith [h.1]
    · change inner ℝ (q - v) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [inner_sub_left]
      linarith [h.2]
  · rintro ⟨p, hp, rfl⟩
    change inner ℝ p (normalVector (t : Real.Angle)) < supportValue K (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hp
    constructor
    · change inner ℝ (p + v) (normalVector (t : Real.Angle)) < _
      rw [inner_add_left]
      linarith [hp.1]
    · change inner ℝ (p + v) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [inner_add_left]
      linarith [hp.2]

private theorem exists_candidate_translate_rightAngle (Θ : AngleSet)
    (hΘ : Θ.angle = Real.pi / 2) (K : PolygonCapSpace Θ)
    (hK : 0 ≤ polygonAreaFunctional Θ K.val) :
    ∃ P : PolygonCapSpace Θ, IsPolygonMaximizationCandidate Θ P ∧
      polygonAreaFunctional Θ P.val = polygonAreaFunctional Θ K.val := by
  obtain ⟨p, hp, hpeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image
        (fun q ↦ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
  have hp1 : p 1 = 1 := by
    change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Real.pi / 2 : ℝ) : Real.Angle) at hpeq
    rw [K.val.property.2.2.2.1] at hpeq
    simpa [normalVector, frame, PiLp.inner_apply] using hpeq
  let v : Point := !₂[-p 0, 0]
  let L := ConvexBody.translate K.val.val v
  have hv (a : Real.Angle) (ha : a = ((Real.pi / 2 : ℝ) : Real.Angle) ∨
      a = ((3 * Real.pi / 2 : ℝ) : Real.Angle)) :
      inner ℝ v (normalVector a) = 0 := by
    rcases ha with rfl | rfl <;>
      simp [v, normalVector, frame, PiLp.inner_apply,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.cos_add, Real.sin_add, -Real.Angle.coe_add]
  have hsupp (a : Real.Angle) : supportValue L a = supportValue K.val.val a +
      inner ℝ v (normalVector a) := supportValue_image_add K.val.val v a
  have hrepr := K.property.translate v
  have hcaprepr := K.val.property.2.2.2.2.2.2.translate v
  have htopω : supportValue K.val.val ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    simpa only [hΘ] using K.val.property.2.2.1
  have hbotω : supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have ha : (((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by rw [hΘ]; congr 1; ring
    simpa only [ha] using K.val.property.2.2.2.2.1
  have hcap : IsCap Θ.angle L := by
    refine ⟨Θ.angle_pos, Θ.angle_le, ?_, ?_, ?_, ?_, hcaprepr⟩
    · rw [hΘ, hsupp, htopω, hv _ (Or.inl rfl), add_zero]
    · rw [hsupp, K.val.property.2.2.2.1, hv _ (Or.inl rfl), add_zero]
    · have ha : (((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by rw [hΘ]; congr 1; ring
      rw [ha, hsupp, hbotω, hv _ (Or.inr rfl), add_zero]
    · rw [hsupp, K.val.property.2.2.2.2.2.1, hv _ (Or.inr rfl), add_zero]
  let P : PolygonCapSpace Θ := ⟨⟨L, hcap⟩, hrepr⟩
  have htop : (stripParallelogram Θ.angle).2.2 ∈ (P.val.val : Set Point) := by
    refine ⟨p, hp, ?_⟩
    ext i
    fin_cases i
    · simp [v, hΘ, stripParallelogram]
      rw [show Real.pi / 4 - Real.pi / 2 / 2 = 0 by ring, Real.tan_zero]
    · simp [v, hΘ, stripParallelogram, hp1]
  have hfan : capFan Θ.angle = (fun q ↦ q + v) '' capFan Θ.angle := by
    ext q
    rw [hΘ]
    simp only [capFan, normalHalfPlane, Set.mem_inter_iff, Bool.false_eq_true,
      ↓reduceIte, Set.mem_image]
    constructor
    · intro hq
      refine ⟨q - v, ?_, by simp⟩
      simpa [v, normalVector, frame, PiLp.inner_apply, inner_sub_left] using hq
    · rintro ⟨r, hr, rfl⟩
      simpa [v, normalVector, frame, PiLp.inner_apply, inner_add_left] using hr
  have hniche : polygonNiche Θ P.val =
      (fun q ↦ q + v) '' polygonNiche Θ K.val := by
    have hquad (t : ℝ) : innerQuadrant (P.val.val : Set Point) t =
        (fun q ↦ q + v) '' innerQuadrant (K.val.val : Set Point) t :=
      innerQuadrant_translate K.val.val v t
    have hunion : (⋃ t ∈ Θ.directions, innerQuadrant (P.val.val : Set Point) t) =
        (fun q ↦ q + v) '' ⋃ t ∈ Θ.directions,
          innerQuadrant (K.val.val : Set Point) t := by
      rw [Set.image_iUnion]
      congr 1
      funext t
      rw [Set.image_iUnion]
      congr 1
      funext ht
      exact hquad t
    unfold polygonNiche
    calc
      capFan Θ.angle ∩ ⋃ t ∈ Θ.directions, innerQuadrant (P.val.val : Set Point) t =
          (fun q ↦ q + v) '' capFan Θ.angle ∩
            (fun q ↦ q + v) '' ⋃ t ∈ Θ.directions,
              innerQuadrant (K.val.val : Set Point) t :=
        congrArg₂ (· ∩ ·) hfan hunion
      _ = (fun q ↦ q + v) '' (capFan Θ.angle ∩ ⋃ t ∈ Θ.directions,
          innerQuadrant (K.val.val : Set Point) t) :=
        (Set.image_inter (Equiv.addRight v).injective).symm
  have harea : polygonAreaFunctional Θ P.val = polygonAreaFunctional Θ K.val := by
    rw [(polygonArea_upperBound Θ).1 P, (polygonArea_upperBound Θ).1 K]
    change ClassicalResults.area ((fun q ↦ q + v) '' (K.val.val : Set Point)) -
        ClassicalResults.area (polygonNiche Θ P.val) = _
    rw [ClassicalResults.area_image_add, hniche, ClassicalResults.area_image_add]
  exact ⟨P, ⟨htop, harea.symm ▸ hK⟩, harea⟩

theorem exists_maximumPolygonCap (Θ : AngleSet) :
    ∃ K : PolygonCapSpace Θ, IsMaximumPolygonCap Θ K ∧ 0 ≤ polygonAreaFunctional Θ K.val := by
  obtain ⟨K, hK, hmax⟩ := exists_maximum_polygonCandidate Θ
  refine ⟨K, ⟨hK.1, ?_⟩, hK.2⟩
  intro L
  by_cases hL : 0 ≤ polygonAreaFunctional Θ L.val
  · rcases lt_or_eq_of_le Θ.angle_le with hΘ | hΘ
    · exact hmax L ⟨stripParallelogram_top_mem_of_angle_lt Θ hΘ L, hL⟩
    · obtain ⟨P, hP, heq⟩ := exists_candidate_translate_rightAngle Θ hΘ L hL
      rw [← heq]
      exact hmax P hP
  · exact (le_of_not_ge hL).trans hK.2

theorem maximumPolygonCap_niche_subset {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) : polygonNiche Θ K.val ⊆ (K.val.val : Set Point) := by
  exact polygonNiche_subset_of_balanced K (maximumPolygonCap_balanced K hK)

private theorem isCap_of_hausdorffLimit {ω : ℝ} (K : ℕ → CapSpace ω)
    (L : ConvexBody Point)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L : Set Point)) atTop (𝓝 0)) : IsCap ω L := by
  let N : Set Real.Angle :=
    ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪ capLowerNormals ω
  let U : Set Point := normalVector '' N
  have hU : ∀ u ∈ U, ‖u‖ = 1 := by
    rintro u ⟨a, _, rfl⟩
    induction a using Real.Angle.induction_on with
    | _ a => exact norm_normalVector_real a
  have hrepr (i : ℕ) : ((K i).val : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K i).val u} := by
    calc
      ((K i).val : Set Point) = ⋂ a ∈ N,
          normalHalfPlane a (supportValue (K i).val a) false false :=
        (K i).property.2.2.2.2.2.2.eq_iInter_supportValue
      _ = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport (K i).val u} := by
        ext p
        simp [U, normalHalfPlane, supportValue, vectorSupport]
  have hclosed := fixedNormalBody_closed U hU (fun i ↦ (K i).val) L hrepr hlim
  refine ⟨(K 0).property.1, (K 0).property.2.1,
    supportValue_limit_eq hlim ω 1 (fun i ↦ (K i).property.2.2.1),
    supportValue_limit_eq hlim (Real.pi / 2) 1 (fun i ↦ (K i).property.2.2.2.1),
    supportValue_limit_eq hlim (ω + Real.pi) 0 (fun i ↦ (K i).property.2.2.2.2.1),
    supportValue_limit_eq hlim (3 * Real.pi / 2) 0
      (fun i ↦ (K i).property.2.2.2.2.2.1), ?_⟩
  refine ⟨(fun t ↦ (t, supportValue L t)) '' N, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ht
  · calc
      (L : Set Point) = ⋂ u ∈ U,
          {x | inner ℝ x u ≤ vectorSupport L u} := hclosed
      _ = ⋂ c ∈ (fun t ↦ (t, supportValue L t)) '' N,
          normalHalfPlane c.1 c.2 false false := by
        ext p
        simp [U, normalHalfPlane, supportValue, vectorSupport]

theorem exists_balancedMaximumCap (ω : ℝ) (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2) :
    ∃ K : CapSpace ω, IsBalancedMaximumCap K := by
  let n : ℕ → ℕ := fun i ↦ 2 ^ (i + 1)
  have hn (i : ℕ) : 2 ≤ n i := by
    dsimp [n]
    have h : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
    rw [pow_succ]
    omega
  let Θ (i : ℕ) := uniformAngleSet ω hω hω' (n i) (hn i)
  have hmid (i : ℕ) : ω / 2 ∈ (Θ i).directions := by
    apply Finset.mem_image.mpr
    refine ⟨2 ^ i, Finset.mem_Ioo.mpr ⟨by positivity, ?_⟩, ?_⟩
    · change 2 ^ i < 2 ^ (i + 1)
      exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self i)
    · simp only [n, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      field_simp
      push_cast
      ring
  choose Q hQmax hQnonneg using fun i ↦ exists_maximumPolygonCap (Θ i)
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCap_bound ω hω hω' (ω / 2)
    ⟨by linarith, by linarith⟩
  obtain ⟨φ, L, hφ, hlim⟩ := convexBody_selection A hA (fun i ↦ (Q i).val.val)
    (fun i ↦ hbound (Θ i) rfl (hmid i) (Q i) ⟨(hQmax i).1, hQnonneg i⟩)
  let K : CapSpace ω := ⟨L, isCap_of_hausdorffLimit (fun i ↦ (Q (φ i)).val) L hlim⟩
  refine ⟨K, (fun i ↦ n (φ i)), (fun i ↦ hn (φ i)), ?_, ?_, ?_⟩
  · intro i j hij
    apply pow_lt_pow_right₀ (by norm_num)
    exact Nat.add_lt_add_right (hφ hij) 1
  · exact fun i ↦ ⟨φ i + 1, rfl⟩
  · exact ⟨(fun i ↦ Q (φ i)), (fun i ↦ hQmax (φ i)), hlim⟩

theorem balancedMaximumCap_niche_subset {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) : capNiche K ⊆ (K.val : Set Point) := by
  obtain ⟨n, hn, hmono, hdyadic, P, hmax, hlim⟩ := hK
  exact capNiche_subset_of_uniform_polygonNiche_subset K n hn hmono hdyadic P
    (fun i ↦ maximumPolygonCap_niche_subset (P i) (hmax i)) hlim

theorem balancedMaximumCap_maximizes_area {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) :
    ∀ L : CapSpace ω, capAreaFunctional L ≤ capAreaFunctional K := by
  obtain ⟨n, hn, hmono, hdyadic, P, hmax, hlim⟩ := hK
  let Θ (i : ℕ) := uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)
  have harealim := convexArea_hausdorff_continuity (fun i ↦ (P i).val.val) K.val hlim
  have hniche := maximizingPolygon_nicheArea_limit ω K.property.1 K.property.2.1
    n hn hmono hdyadic P hmax K hlim
  have hfunc : Tendsto (fun i ↦ polygonAreaFunctional (Θ i) (P i).val) atTop
      (𝓝 (capAreaFunctional K)) := by
    have hsub := harealim.sub hniche
    convert hsub using 1
    · funext i
      exact (polygonArea_upperBound (Θ i)).1 (P i)
    · rfl
  intro L
  apply ge_of_tendsto hfunc
  filter_upwards [] with i
  exact ((polygonArea_upperBound (Θ i)).2 L).trans
    (polygonAreaFunctional_le_maximum (Θ i) (P i) (hmax i) L)

end MovingSofa

end

end

end
