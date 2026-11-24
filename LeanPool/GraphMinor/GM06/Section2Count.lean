/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Section2Dual

/-!
# Graph Minors VI, Section 2: Proof of Theorem (2.4)

This file formalizes $\Delta$-minimizers, $\Delta^*$-maximizers, and the proof of (2.4) of
Robertson and Seymour, *Graph Minors. VI. Disjoint paths across a disc*, J. Combin. Theory
Ser. B **41** (1986), 115–138 (pages 118–119).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Function Topology GraphMinor.Surface

universe u

/-! ## 1. Counting $\Delta(x, y)$ when $x = y$ -/

theorem not_crossesOn_self_right {S : Type u} [TopologicalSpace S] {C : Set S} {a c x : S} :
    ¬ CrossesOn C a c x x :=
  fun h => h.2.2.2.2.2.1 rfl

theorem divisionCount_self_eq_one_of_mem {S : Type u} [TopologicalSpace S] {C : Set S}
    {Δ : Set (Set S)} {x : S} (hΔ : IsDivision Δ) (hx : x ∈ divisionUnion Δ) :
    divisionCount C Δ x x = 1 := by
  obtain ⟨δ₀, hδ₀, hxδ₀⟩ := hx
  unfold divisionCount
  have heq : {δ ∈ Δ | (δ ∩ {x, x}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v x x} = {δ₀} := by
    ext δ
    simp only [pair_eq_singleton, inter_singleton_nonempty, not_crossesOn_self_right,
      and_false, exists_false, or_false, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hδ, hxδ⟩
      by_contra hne
      exact (hΔ.2.2 hδ hδ₀ hne).ne_of_mem hxδ hxδ₀ rfl
    · rintro rfl
      exact ⟨hδ₀, hxδ₀⟩
  rw [heq, ncard_singleton]

theorem divisionCount_self_eq_zero_of_not_mem {S : Type u} [TopologicalSpace S] {C : Set S}
    {Δ : Set (Set S)} {x : S} (hx : x ∉ divisionUnion Δ) :
    divisionCount C Δ x x = 0 := by
  unfold divisionCount
  have heq : {δ ∈ Δ | (δ ∩ {x, x}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v x x} = ∅ := by
    ext δ
    simp only [pair_eq_singleton, inter_singleton_nonempty, not_crossesOn_self_right,
      and_false, exists_false, or_false, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hδ hxδ
    exact hx ⟨δ, hδ, hxδ⟩
  rw [heq, ncard_empty]

theorem theorem_2_4_self {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S))
    (x : S) (hV_fin : (divisionUnion Δ).Finite) (hV_sub : divisionUnion Δ ⊆ C)
    (hC : IsOArc C) (hΔ : IsDivision Δ) (hU : IsDualPointSet C (divisionUnion Δ) U)
    (hx : x ∈ divisionUnion Δ ∪ U) :
    ((x ∈ divisionUnion Δ ∧ x ∈ divisionUnion Δ →
        (divisionCount C Δ x x : ℤ) - (divisionCount C (dualDivision C U Δ) x x : ℤ) = 1) ∧
     (x ∈ U ∧ x ∈ U →
        (divisionCount C Δ x x : ℤ) - (divisionCount C (dualDivision C U Δ) x x : ℤ) = -1) ∧
     (¬ (x ∈ divisionUnion Δ ∧ x ∈ divisionUnion Δ) → ¬ (x ∈ U ∧ x ∈ U) →
        (divisionCount C Δ x x : ℤ) - (divisionCount C (dualDivision C U Δ) x x : ℤ) = 0)) := by
  have hU_sub : U ⊆ C \ divisionUnion Δ := isDualPointSet_subset_diff hU
  have hΔ_star_union : divisionUnion (dualDivision C U Δ) = U := divisionUnion_dualDivision C U Δ
  have hΔ_star_div : IsDivision (dualDivision C U Δ) := by
    obtain ⟨φ⟩ := hC
    have hinj := injective_oArcMap φ
    have hrange := range_oArcMap φ
    let U₀ := oArcMap φ ⁻¹' U
    let Δ₀ := (preimage (oArcMap φ)) '' Δ
    have hU_eq : oArcMap φ '' U₀ = U :=
      image_preimage_eq_of_subset (hU_sub.trans (sdiff_subset.trans hrange.symm.subset))
    have hΔ_eq : (image (oArcMap φ)) '' Δ₀ = Δ := by
      ext δ
      simp only [Δ₀, mem_image, exists_exists_and_eq_and]
      constructor
      · rintro ⟨δ', hδ', rfl⟩
        have hsub : δ' ⊆ range (oArcMap φ) := by
          rw [hrange]
          exact (subset_sUnion_of_mem hδ').trans hV_sub
        rwa [image_preimage_eq_of_subset hsub]
      · intro hδ
        have hsub : δ ⊆ range (oArcMap φ) := by
          rw [hrange]
          exact (subset_sUnion_of_mem hδ).trans hV_sub
        exact ⟨δ, hδ, image_preimage_eq_of_subset hsub⟩
    have hV₀_fin : (divisionUnion Δ₀).Finite := by
      refine Finite.of_finite_image ?_ hinj.injOn
      rw [← divisionUnion_oArcMap φ, hΔ_eq]
      exact hV_fin
    have hU₀ : IsDualPointSet (univ : Set Circle) (divisionUnion Δ₀) U₀ := by
      rw [← isDualPointSet_oArcMap_iff φ, ← divisionUnion_oArcMap φ, hΔ_eq, hU_eq]
      exact hU
    rw [← hU_eq, ← hΔ_eq, dualDivision_oArcMap, isDivision_oArcMap_iff]
    exact isDivision_dualDivision_univ hV₀_fin hU₀
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hxV, _⟩
    have hxU : x ∉ divisionUnion (dualDivision C U Δ) := by
      rw [hΔ_star_union]
      exact fun h => (hU_sub h).2 hxV
    rw [divisionCount_self_eq_one_of_mem hΔ hxV, divisionCount_self_eq_zero_of_not_mem hxU]
    norm_num
  · rintro ⟨hxU, _⟩
    have hxV : x ∉ divisionUnion Δ := (hU_sub hxU).2
    have hxU' : x ∈ divisionUnion (dualDivision C U Δ) := by rwa [hΔ_star_union]
    rw [divisionCount_self_eq_zero_of_not_mem hxV, divisionCount_self_eq_one_of_mem hΔ_star_div
      hxU']
    norm_num
  · intro hnotV hnotU
    rcases hx with hxV | hxU
    · exact (hnotV ⟨hxV, hxV⟩).elim
    · exact (hnotU ⟨hxU, hxU⟩).elim

/-! ## 2. Transfer of `divisionCount` along `oArcMap` -/

theorem divisionCount_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    (Δ : Set (Set Circle)) (x y : Circle) :
    divisionCount C ((image (oArcMap φ)) '' Δ) (oArcMap φ x) (oArcMap φ y) =
      divisionCount (univ : Set Circle) Δ x y := by
  have hinj := injective_oArcMap φ
  have himg_inj : Injective (image (oArcMap φ)) := image_injective.mpr hinj
  unfold divisionCount
  have heq : {δ ∈ (image (oArcMap φ)) '' Δ |
      (δ ∩ {oArcMap φ x, oArcMap φ y}).Nonempty ∨
        ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v (oArcMap φ x) (oArcMap φ y)} =
    (image (oArcMap φ)) '' {δ ∈ Δ |
      (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (univ : Set Circle) u v x y} := by
    ext s
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨⟨δ, hδ, rfl⟩, hcond⟩
      refine ⟨δ, ⟨hδ, ?_⟩, rfl⟩
      have hpair : ({oArcMap φ x, oArcMap φ y} : Set S) = oArcMap φ '' {x, y} := by simp
      rw [hpair, ← image_inter hinj, image_nonempty] at hcond
      simp only [mem_image, exists_exists_and_eq_and, crossesOn_oArcMap_iff] at hcond
      exact hcond
    · rintro ⟨δ, ⟨hδ, hcond⟩, rfl⟩
      refine ⟨⟨δ, hδ, rfl⟩, ?_⟩
      have hpair : ({oArcMap φ x, oArcMap φ y} : Set S) = oArcMap φ '' {x, y} := by simp
      rw [hpair, ← image_inter hinj, image_nonempty]
      simp only [mem_image, exists_exists_and_eq_and, crossesOn_oArcMap_iff]
      exact hcond
  rw [heq, ncard_image_of_injective _ himg_inj]

/-! ## 3. Active Members and $\Delta$-Minimizers on `Circle` -/

/-- A member $\delta \in \Delta$ is *active* for $(x, y)$ ($x \ne y$) on `Circle` if $x \notin
\delta$
and $\delta$ meets both half-open arcs $(x, y]$ (`0 < x.angleDiff v ≤ x.angleDiff y`) and $[y, x)$
(`x.angleDiff y ≤ x.angleDiff v`). -/
private def IsActiveFor (x y : Circle) (δ : Set Circle) : Prop :=
  x ∉ δ ∧
  (∃ v₁ ∈ δ, x.angleDiff v₁ ≤ x.angleDiff y) ∧
  (∃ v₂ ∈ δ, x.angleDiff y ≤ x.angleDiff v₂)

private lemma active_iff_counted_not_mem_x {x y : Circle} (hxy : x ≠ y) {δ : Set Circle} :
    ((δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (univ : Set Circle) u v x y) ∧ x ∉ δ ↔
      IsActiveFor x y δ := by
  have hxy_pos : 0 < x.angleDiff y := Circle.angleDiff_pos hxy
  constructor
  · rintro ⟨hcount, hxδ⟩
    refine ⟨hxδ, ?_⟩
    rcases hcount with ⟨z, hzδ, hzx | hzy⟩ | ⟨u, huδ, v, hvδ, hcross⟩
    · subst hzx
      exact (hxδ hzδ).elim
    · rw [mem_singleton_iff] at hzy
      subst hzy
      exact ⟨⟨z, hzδ, le_rfl⟩, ⟨z, hzδ, le_rfl⟩⟩
    · have hcross' := hcross.comm isOArc_univ_circle
      rw [crossesOn_univ_iff_angleDiff] at hcross'
      rcases hcross' with ⟨_, _, _, _, hyu, hyv, hiff⟩
      have hyu_ang : x.angleDiff y ≠ x.angleDiff u := (circleCoordFrom x).injective.ne hyu
      have hyv_ang : x.angleDiff y ≠ x.angleDiff v := (circleCoordFrom x).injective.ne hyv
      by_cases hu_lt : x.angleDiff u < x.angleDiff y
      · have hv_ge : x.angleDiff y ≤ x.angleDiff v := not_lt.mp (hiff.mp hu_lt)
        exact ⟨⟨u, huδ, hu_lt.le⟩, ⟨v, hvδ, hv_ge⟩⟩
      · have hv_lt : x.angleDiff v < x.angleDiff y := by tauto
        have hu_ge : x.angleDiff y ≤ x.angleDiff u := not_lt.mp hu_lt
        exact ⟨⟨v, hvδ, hv_lt.le⟩, ⟨u, huδ, hu_ge⟩⟩
  · rintro ⟨hxδ, ⟨v₁, hv₁δ, hle₁⟩, ⟨v₂, hv₂δ, hle₂⟩⟩
    refine ⟨?_, hxδ⟩
    by_cases hyδ : y ∈ δ
    · exact Or.inl ⟨y, hyδ, mem_insert_of_mem x (mem_singleton y)⟩
    · right
      have hv₁x : x ≠ v₁ := fun h => hxδ (h ▸ hv₁δ)
      have hv₂x : x ≠ v₂ := fun h => hxδ (h ▸ hv₂δ)
      have hv₁y : y ≠ v₁ := fun h => hyδ (h ▸ hv₁δ)
      have hv₂y : y ≠ v₂ := fun h => hyδ (h ▸ hv₂δ)
      have hlt₁ : x.angleDiff v₁ < x.angleDiff y :=
        lt_of_le_of_ne hle₁ ((circleCoordFrom x).injective.ne hv₁y.symm)
      have hlt₂ : x.angleDiff y < x.angleDiff v₂ :=
        lt_of_le_of_ne hle₂ ((circleCoordFrom x).injective.ne hv₂y)
      have hv₁v₂ : v₁ ≠ v₂ := fun h => by
        have : x.angleDiff v₁ = x.angleDiff v₂ := congrArg (Circle.angleDiff x) h
        linarith
      refine ⟨v₁, hv₁δ, v₂, hv₂δ, (CrossesOn.comm isOArc_univ_circle ?_)⟩
      rw [crossesOn_univ_iff_angleDiff]
      exact ⟨hxy, hv₁v₂, hv₁x, hv₂x, hv₁y, hv₂y, ⟨fun _ => not_lt_of_ge hlt₂.le, fun _ => hlt₁⟩⟩

private lemma divisionCount_eq_active_add_mem {Δ : Set (Set Circle)} (hΔ : IsDivision Δ)
    {x y : Circle} (hxy : x ≠ y) :
    (divisionCount (univ : Set Circle) Δ x y : ℤ) - ((divisionUnion Δ ∩ {x}).ncard : ℤ) =
      ({δ ∈ Δ | IsActiveFor x y δ}.ncard : ℤ) := by
  let S_all := {δ ∈ Δ | (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn
    (univ : Set Circle) u v x y}
  let S_act := {δ ∈ Δ | IsActiveFor x y δ}
  let S_x := {δ ∈ Δ | x ∈ δ}
  have hS_all_fin : S_all.Finite := hΔ.1.subset fun _ h => h.1
  have hS_act_fin : S_act.Finite := hΔ.1.subset fun _ h => h.1
  have hS_x_fin : S_x.Finite := hΔ.1.subset fun _ h => h.1
  have hdisj : Disjoint S_act S_x := by
    rw [disjoint_left]
    intro δ h1 h2
    exact h1.2.1 h2.2
  have hunion : S_all = S_act ∪ S_x := by
    ext δ
    simp only [S_all, S_act, S_x, mem_ofPred_eq, mem_union]
    by_cases hxδ : x ∈ δ
    · have hmem : (δ ∩ {x, y}).Nonempty := ⟨x, hxδ, mem_insert x {y}⟩
      have hnot : ¬ IsActiveFor x y δ := fun h => h.1 hxδ
      exact ⟨fun h => Or.inr ⟨h.1, hxδ⟩, fun h => ⟨h.elim (fun h1 => h1.1) (fun h2
        => h2.1), Or.inl hmem⟩⟩
    · have hiff := active_iff_counted_not_mem_x hxy (δ := δ)
      constructor
      · rintro ⟨hδ, hcond⟩
        exact Or.inl ⟨hδ, hiff.mp ⟨hcond, hxδ⟩⟩
      · rintro (⟨hδ, hact⟩ | ⟨_, hxδ'⟩)
        · exact ⟨hδ, (hiff.mpr hact).1⟩
        · exact (hxδ hxδ').elim
  have hcard_union : S_all.ncard = S_act.ncard + S_x.ncard := by
    rw [hunion]
    exact ncard_union_eq hdisj hS_act_fin hS_x_fin
  have hcard_x : S_x.ncard = (divisionUnion Δ ∩ {x}).ncard := by
    by_cases hxV : x ∈ divisionUnion Δ
    · obtain ⟨δ₀, hδ₀, hxδ₀⟩ := hxV
      have h1 : S_x = {δ₀} := by
        ext δ
        simp only [S_x, mem_ofPred_eq, mem_singleton_iff]
        refine ⟨fun ⟨hδ, hxδ⟩ => ?_, fun h => h ▸ ⟨hδ₀, hxδ₀⟩⟩
        by_contra hne
        exact (hΔ.2.2 hδ hδ₀ hne).ne_of_mem hxδ hxδ₀ rfl
      have h2 : divisionUnion Δ ∩ {x} = {x} := by
        ext z
        simp only [mem_inter_iff, mem_singleton_iff, and_iff_right_iff_imp]
        rintro rfl
        exact ⟨δ₀, hδ₀, hxδ₀⟩
      rw [h1, h2, ncard_singleton, ncard_singleton]
    · have h1 : S_x = ∅ := by
        ext δ
        simp only [S_x, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro hδ hxδ
        exact hxV ⟨δ, hδ, hxδ⟩
      have h2 : divisionUnion Δ ∩ {x} = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
        rintro h rfl
        exact hxV h
      rw [h1, h2, ncard_empty, ncard_empty]
  change (S_all.ncard : ℤ) - ((divisionUnion Δ ∩ {x}).ncard : ℤ) = (S_act.ncard : ℤ)
  rw [hcard_union, ← hcard_x]
  omega

/-! ## 4. Bijection between Active Members of $\Delta$ and Active Members of $\Delta^*$ -/

private lemma angleDiff_cases (x a b : Circle) :
    (x.angleDiff a ≤ x.angleDiff b ∧ a.angleDiff b = x.angleDiff b - x.angleDiff a) ∨
    (x.angleDiff b < x.angleDiff a ∧ a.angleDiff b = 2 * Real.pi + x.angleDiff b - x.angleDiff a)
      := by
  have h := angleDiff_eq_of_angleDiff (x := x) (a := a) (b := b)
  split_ifs at h with hle
  · exact Or.inl ⟨hle, h⟩
  · exact Or.inr ⟨not_le.mp hle, h⟩

private lemma prevSegment_angleDiff_bounds {V U : Set Circle}
    (hU : IsDualPointSet (univ : Set Circle) V U)
    {x v₁ u₁ : Circle} (hx : x ∈ V ∪ U) (hv₁V : v₁ ∈ V) (hv₁x : x ≠ v₁)
    (hu₁_eq : U ∩ prevSegment V v₁ = {u₁}) :
    u₁ ∈ U ∧ u₁ ≠ v₁ ∧
    x.angleDiff u₁ < x.angleDiff v₁ ∧
    (∀ w ∈ V, x.angleDiff u₁ ≤ x.angleDiff w → x.angleDiff v₁ ≤ x.angleDiff w) ∧
    (∀ u ∈ U, x.angleDiff u₁ < x.angleDiff u → x.angleDiff v₁ < x.angleDiff u) := by
  have hU_sub : U ⊆ (univ : Set Circle) \ V := isDualPointSet_subset_diff hU
  obtain ⟨hu₁U, hu₁v₁, hvw₁, hu'w₁⟩ := prevSegment_dual_properties hU hv₁V hu₁_eq
  have hxv₁_pos := Circle.angleDiff_pos hv₁x
  have hxv₁_lt_2pi := Circle.angleDiff_lt_two_pi x v₁
  have hu₁v₁_pos := Circle.angleDiff_pos hu₁v₁
  have hxu₁_lt_v₁ : x.angleDiff u₁ < x.angleDiff v₁ := by
    rcases eq_or_ne x u₁ with rfl | hxu₁_ne
    · have hx0 : x.angleDiff x = 0 := circleCoordFrom_self x
      linarith
    · have hxu₁_pos := Circle.angleDiff_pos hxu₁_ne
      have hxu₁_lt_2pi := Circle.angleDiff_lt_two_pi x u₁
      have hlt : u₁.angleDiff v₁ < x.angleDiff v₁ := by
        rcases hx with hxV | hxU
        · exact hvw₁ x ⟨hxV, hv₁x⟩
        · obtain ⟨w, _, h1, h2⟩ := hu'w₁ x ⟨hxU, hxu₁_ne⟩
          exact h1.trans h2
      rcases angleDiff_cases x u₁ v₁ with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
  have hno_V_1 : ∀ w ∈ V, x.angleDiff u₁ ≤ x.angleDiff w → x.angleDiff v₁ ≤ x.angleDiff w := by
    intro w hw hle
    rcases eq_or_ne w v₁ with rfl | hwv₁
    · exact le_rfl
    · have hlt := hvw₁ w ⟨hw, hwv₁⟩
      have hxw_ne : x ≠ w := by
        rintro rfl
        have hx0 : x.angleDiff x = 0 := circleCoordFrom_self x
        rcases eq_or_ne x u₁ with rfl | hxu₁
        · exact (hU_sub hu₁U).2 hw
        · have := Circle.angleDiff_pos hxu₁
          linarith
      have hxw_pos := Circle.angleDiff_pos hxw_ne
      have hxw_lt_2pi := Circle.angleDiff_lt_two_pi x w
      have hwv₁_pos := Circle.angleDiff_pos hwv₁
      rcases angleDiff_cases x w v₁ with ⟨_, heq_w⟩ | ⟨_, heq_w⟩ <;>
        rcases angleDiff_cases x u₁ v₁ with ⟨_, heq_u₁⟩ | ⟨_, heq_u₁⟩ <;>
        linarith
  have hno_U_1 : ∀ u ∈ U, x.angleDiff u₁ < x.angleDiff u → x.angleDiff v₁ < x.angleDiff u := by
    intro u huU hu₁_lt_u
    by_contra! hle
    have hu_ne_u₁ : u ≠ u₁ := fun h => by subst h; exact lt_irrefl _ hu₁_lt_u
    obtain ⟨w, _, hlt1, hlt2⟩ := hu'w₁ u ⟨huU, hu_ne_u₁⟩
    have hlt : u₁.angleDiff v₁ < u.angleDiff v₁ := hlt1.trans hlt2
    have hxu_ne : x ≠ u := fun h => by
      subst h
      have hx0 : x.angleDiff x = 0 := circleCoordFrom_self x
      have := Circle.angleDiff_nonneg x u₁
      linarith
    have hxu_pos := Circle.angleDiff_pos hxu_ne
    have hxu_lt_2pi := Circle.angleDiff_lt_two_pi x u
    have huv₁_ne : u ≠ v₁ := fun h => (hU_sub huU).2 (h ▸ hv₁V)
    have huv₁_pos := Circle.angleDiff_pos huv₁_ne
    rcases angleDiff_cases x u v₁ with ⟨_, heq_u⟩ | ⟨_, heq_u⟩ <;>
      rcases angleDiff_cases x u₁ v₁ with ⟨_, heq_u₁⟩ | ⟨_, heq_u₁⟩ <;>
      linarith
  exact ⟨hu₁U, hu₁v₁, hxu₁_lt_v₁, hno_V_1, hno_U_1⟩

private lemma nextSegment_angleDiff_bounds {V U : Set Circle}
    (hU : IsDualPointSet (univ : Set Circle) V U)
    {x v₂ u₂ : Circle} (hx : x ∈ V ∪ U) (hv₂V : v₂ ∈ V) (hv₂x : x ≠ v₂)
    (hx_not_V : x ∉ V) (hu₂_eq : U ∩ nextSegment V v₂ = {u₂}) :
    u₂ ∈ U ∧ u₂ ≠ v₂ ∧
    (x = u₂ ∨ x.angleDiff v₂ < x.angleDiff u₂) ∧
    (∀ w ∈ V, (x = u₂ ∨ x.angleDiff w ≤ x.angleDiff u₂) → x.angleDiff w ≤ x.angleDiff v₂) ∧
    (∀ u ∈ U, (x ≠ u₂ → x.angleDiff u < x.angleDiff u₂) → x.angleDiff u < x.angleDiff v₂) := by
  have hU_sub : U ⊆ (univ : Set Circle) \ V := isDualPointSet_subset_diff hU
  obtain ⟨hu₂U, hu₂v₂, hvw₂, hu'w₂⟩ := nextSegment_dual_properties hU hv₂V hu₂_eq
  have hxv₂_pos := Circle.angleDiff_pos hv₂x
  have hxv₂_lt_2pi := Circle.angleDiff_lt_two_pi x v₂
  have hsum_xv₂ := Circle.angleDiff_add_angleDiff hv₂x
  have hv₂u₂_pos := Circle.angleDiff_pos hu₂v₂.symm
  have hxv₂_lt_u₂ : x = u₂ ∨ x.angleDiff v₂ < x.angleDiff u₂ := by
    rcases eq_or_ne x u₂ with rfl | hxu₂_ne
    · exact Or.inl rfl
    · right
      have hxu₂_pos := Circle.angleDiff_pos hxu₂_ne
      have hxu₂_lt_2pi := Circle.angleDiff_lt_two_pi x u₂
      have hlt : v₂.angleDiff u₂ < v₂.angleDiff x := by
        rcases hx with hxV | hxU
        · exact (hx_not_V hxV).elim
        · obtain ⟨w, _, h1, h2⟩ := hu'w₂ x ⟨hxU, hxu₂_ne⟩
          exact h1.trans h2
      rcases angleDiff_cases x v₂ u₂ with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
  have hno_V_2 : ∀ w ∈ V,
      (x = u₂ ∨ x.angleDiff w ≤ x.angleDiff u₂) → x.angleDiff w ≤ x.angleDiff v₂ := by
    intro w hw hle
    rcases eq_or_ne w v₂ with rfl | hwv₂
    · exact le_rfl
    · have hlt := hvw₂ w ⟨hw, hwv₂⟩
      have hxw_ne : x ≠ w := fun h => hx_not_V (h ▸ hw)
      have hxw_pos := Circle.angleDiff_pos hxw_ne
      have hxw_lt_2pi := Circle.angleDiff_lt_two_pi x w
      have hv₂w_pos := Circle.angleDiff_pos hwv₂.symm
      rcases angleDiff_cases x v₂ w with ⟨_, heq_w⟩ | ⟨_, heq_w⟩
      · rcases hxv₂_lt_u₂ with rfl | hlt_u₂
        · linarith
        · have hle' : x.angleDiff w ≤ x.angleDiff u₂ := hle.resolve_left (fun h
          => by subst h; linarith)
          have hxu₂_lt_2pi := Circle.angleDiff_lt_two_pi x u₂
          rcases angleDiff_cases x v₂ u₂ with ⟨_, heq_u₂⟩ | ⟨_, heq_u₂⟩ <;>
            linarith
      · linarith
  have hno_U_2 : ∀ u ∈ U,
      (x ≠ u₂ → x.angleDiff u < x.angleDiff u₂) → x.angleDiff u < x.angleDiff v₂ := by
    intro u huU hu_lt_u₂
    by_contra! hge
    have hu_ne_u₂ : u ≠ u₂ := by
      rintro rfl
      rcases eq_or_ne x u with rfl | hxu
      · have hx0 : x.angleDiff x = 0 := circleCoordFrom_self x
        linarith
      · exact lt_irrefl _ (hu_lt_u₂ hxu)
    obtain ⟨w, _, hlt1, hlt2⟩ := hu'w₂ u ⟨huU, hu_ne_u₂⟩
    have hlt : v₂.angleDiff u₂ < v₂.angleDiff u := hlt1.trans hlt2
    have hxu_lt_2pi := Circle.angleDiff_lt_two_pi x u
    have hv₂u_ne : v₂ ≠ u := fun h => (hU_sub huU).2 (h ▸ hv₂V)
    have hv₂u_pos := Circle.angleDiff_pos hv₂u_ne
    rcases angleDiff_cases x v₂ u with ⟨_, heq_u⟩ | ⟨_, heq_u⟩
    · rcases hxv₂_lt_u₂ with rfl | hlt_u₂
      · linarith
      · have hlt' : x.angleDiff u < x.angleDiff u₂ := hu_lt_u₂ (fun h => by subst h; linarith)
        have hxu₂_lt_2pi := Circle.angleDiff_lt_two_pi x u₂
        rcases angleDiff_cases x v₂ u₂ with ⟨_, heq_u₂⟩ | ⟨_, heq_u₂⟩ <;>
          linarith
    · linarith
  exact ⟨hu₂U, hu₂v₂, hxv₂_lt_u₂, hno_V_2, hno_U_2⟩

/-- The dual endpoints of a primal active interval belong to the same region. -/
private lemma dualEquivRel_of_angle_bounds {Δ : Set (Set Circle)} {δ : Set Circle}
    (hΔ : IsDivision Δ) (hCF : IsCrossFree (univ : Set Circle) Δ)
    (hδ : δ ∈ Δ) {x v₁ v₂ u₁ u₂ : Circle} (hv₁δ : v₁ ∈ δ) (hv₂δ : v₂ ∈ δ)
    (hmin₁ : ∀ z ∈ δ, x.angleDiff v₁ ≤ x.angleDiff z)
    (hmax₂ : ∀ z ∈ δ, x.angleDiff z ≤ x.angleDiff v₂)
    (hxu₁_lt_v₁ : x.angleDiff u₁ < x.angleDiff v₁)
    (hle_v : x.angleDiff v₁ ≤ x.angleDiff v₂)
    (hxv₂_lt_u₂ : x = u₂ ∨ x.angleDiff v₂ < x.angleDiff u₂)
    (hno_V_1 : ∀ z ∈ divisionUnion Δ,
      x.angleDiff u₁ ≤ x.angleDiff z → x.angleDiff v₁ ≤ x.angleDiff z)
    (hno_V_2 : ∀ z ∈ divisionUnion Δ,
      (x = u₂ ∨ x.angleDiff z ≤ x.angleDiff u₂) → x.angleDiff z ≤ x.angleDiff v₂) :
    dualEquivRel (univ : Set Circle) Δ u₁ u₂ := by
  rcases eq_or_ne u₁ u₂ with rfl | hu₁u₂_ne
  · exact dualEquivRel_refl _ _ u₁
  rintro ⟨δ', hδ', z₁, hz₁, z₂, hz₂, hcross⟩
  have hz₁V : z₁ ∈ divisionUnion Δ := ⟨δ', hδ', hz₁⟩
  have hz₂V : z₂ ∈ divisionUnion Δ := ⟨δ', hδ', hz₂⟩
  have hcross' := hcross.comm isOArc_univ_circle
  rw [crossesOn_univ_iff_circleCoordFrom x] at hcross'
  rcases hcross' with ⟨_, hz₁z₂_ne, hu₁z₁, hu₁z₂, hu₂z₁, hu₂z₂, hiff⟩
  simp only [onOpenArc, circleCoordFrom] at hiff
  have hiff' :
      (x.angleDiff v₁ ≤ x.angleDiff z₁ ∧ x.angleDiff z₁ ≤ x.angleDiff v₂) ↔
      ¬ (x.angleDiff v₁ ≤ x.angleDiff z₂ ∧ x.angleDiff z₂ ≤ x.angleDiff v₂) := by
    rcases hxv₂_lt_u₂ with rfl | hlt_u₂
    · have hx0 : x.angleDiff x = 0 := circleCoordFrom_self x
      have hxu₁_pos : 0 < x.angleDiff u₁ := Circle.angleDiff_pos hu₁u₂_ne.symm
      have hmin_eq : min (x.angleDiff u₁) (x.angleDiff x) = 0 := by
        rw [hx0, min_eq_right hxu₁_pos.le]
      have hmax_eq : max (x.angleDiff u₁) (x.angleDiff x) = x.angleDiff u₁ := by
        rw [hx0, max_eq_left hxu₁_pos.le]
      rw [hmin_eq, hmax_eq] at hiff
      have hz₁_pos : 0 < x.angleDiff z₁ := Circle.angleDiff_pos hu₂z₁
      have hz₂_pos : 0 < x.angleDiff z₂ := Circle.angleDiff_pos hu₂z₂
      have hz₁_ne_u₁ : x.angleDiff z₁ ≠ x.angleDiff u₁ :=
        (circleCoordFrom x).injective.ne hu₁z₁.symm
      have hz₂_ne_u₁ : x.angleDiff z₂ ≠ x.angleDiff u₁ :=
        (circleCoordFrom x).injective.ne hu₁z₂.symm
      have h1_z₁ := hno_V_1 z₁ hz₁V
      have h2_z₁ := hno_V_2 z₁ hz₁V (Or.inl rfl)
      have h1_z₂ := hno_V_1 z₂ hz₂V
      have h2_z₂ := hno_V_2 z₂ hz₂V (Or.inl rfl)
      have hz₁_iff : (0 < x.angleDiff z₁ ∧ x.angleDiff z₁ < x.angleDiff u₁) ↔
          ¬ (x.angleDiff v₁ ≤ x.angleDiff z₁ ∧ x.angleDiff z₁ ≤ x.angleDiff v₂) := by
        constructor
        · rintro ⟨_, hlt⟩ ⟨hge, _⟩; linarith
        · intro hnot
          refine ⟨hz₁_pos, lt_of_le_of_ne ?_ hz₁_ne_u₁⟩
          by_contra! hgt
          exact hnot ⟨h1_z₁ hgt.le, h2_z₁⟩
      have hz₂_iff : (0 < x.angleDiff z₂ ∧ x.angleDiff z₂ < x.angleDiff u₁) ↔
          ¬ (x.angleDiff v₁ ≤ x.angleDiff z₂ ∧ x.angleDiff z₂ ≤ x.angleDiff v₂) := by
        constructor
        · rintro ⟨_, hlt⟩ ⟨hge, _⟩; linarith
        · intro hnot
          refine ⟨hz₂_pos, lt_of_le_of_ne ?_ hz₂_ne_u₁⟩
          by_contra! hgt
          exact hnot ⟨h1_z₂ hgt.le, h2_z₂⟩
      rw [hz₁_iff, hz₂_iff] at hiff
      exact ⟨fun h1 h2 => hiff.mpr (not_not.mpr h2) h1,
             fun hnot => by_contra fun hnotA => hiff.mp hnotA hnot⟩
    · have hlt_u₁_u₂ : x.angleDiff u₁ < x.angleDiff u₂ := by linarith
      have hmin_eq : min (x.angleDiff u₁) (x.angleDiff u₂) = x.angleDiff u₁ :=
        min_eq_left hlt_u₁_u₂.le
      have hmax_eq : max (x.angleDiff u₁) (x.angleDiff u₂) = x.angleDiff u₂ :=
        max_eq_right hlt_u₁_u₂.le
      rw [hmin_eq, hmax_eq] at hiff
      have h1_z₁ := hno_V_1 z₁ hz₁V
      have h2_z₁ := hno_V_2 z₁ hz₁V
      have h1_z₂ := hno_V_1 z₂ hz₂V
      have h2_z₂ := hno_V_2 z₂ hz₂V
      have hz₁_iff : (x.angleDiff u₁ < x.angleDiff z₁ ∧ x.angleDiff z₁ < x.angleDiff u₂) ↔
          (x.angleDiff v₁ ≤ x.angleDiff z₁ ∧ x.angleDiff z₁ ≤ x.angleDiff v₂) := by
        refine ⟨fun ⟨h1, h2⟩ => ⟨h1_z₁ h1.le, h2_z₁ (Or.inr h2.le)⟩, fun ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
          <;> linarith
      have hz₂_iff : (x.angleDiff u₁ < x.angleDiff z₂ ∧ x.angleDiff z₂ < x.angleDiff u₂) ↔
          (x.angleDiff v₁ ≤ x.angleDiff z₂ ∧ x.angleDiff z₂ ≤ x.angleDiff v₂) := by
        refine ⟨fun ⟨h1, h2⟩ => ⟨h1_z₂ h1.le, h2_z₂ (Or.inr h2.le)⟩, fun ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
          <;> linarith
      rwa [hz₁_iff, hz₂_iff] at hiff
  have hδ_ne_δ' : δ ≠ δ' := by
    rintro rfl
    exact hiff'.mp ⟨hmin₁ z₁ hz₁, hmax₂ z₁ hz₁⟩ ⟨hmin₁ z₂ hz₂, hmax₂ z₂ hz₂⟩
  have hdisj : Disjoint δ δ' := hΔ.2.2 hδ hδ' hδ_ne_δ'
  have hz₁_ne_v₁ : z₁ ≠ v₁ := (hdisj.ne_of_mem hv₁δ hz₁).symm
  have hz₁_ne_v₂ : z₁ ≠ v₂ := (hdisj.ne_of_mem hv₂δ hz₁).symm
  have hz₂_ne_v₁ : z₂ ≠ v₁ := (hdisj.ne_of_mem hv₁δ hz₂).symm
  have hz₂_ne_v₂ : z₂ ≠ v₂ := (hdisj.ne_of_mem hv₂δ hz₂).symm
  have hz₁_ne_v₁_ang : x.angleDiff z₁ ≠ x.angleDiff v₁ :=
    (circleCoordFrom x).injective.ne hz₁_ne_v₁
  have hz₁_ne_v₂_ang : x.angleDiff z₁ ≠ x.angleDiff v₂ :=
    (circleCoordFrom x).injective.ne hz₁_ne_v₂
  have hz₂_ne_v₁_ang : x.angleDiff z₂ ≠ x.angleDiff v₁ :=
    (circleCoordFrom x).injective.ne hz₂_ne_v₁
  have hz₂_ne_v₂_ang : x.angleDiff z₂ ≠ x.angleDiff v₂ :=
    (circleCoordFrom x).injective.ne hz₂_ne_v₂
  have hv₁_ne_v₂ : v₁ ≠ v₂ := by
    intro h
    subst h
    by_cases hb₁ : x.angleDiff v₁ ≤ x.angleDiff z₁ ∧ x.angleDiff z₁ ≤ x.angleDiff v₁
    · exact hz₁_ne_v₁_ang (le_antisymm hb₁.2 hb₁.1)
    · have hb₂ : x.angleDiff v₁ ≤ x.angleDiff z₂ ∧ x.angleDiff z₂ ≤ x.angleDiff v₁ :=
        not_not.mp (hiff'.not.mp hb₁)
      exact hz₂_ne_v₁_ang (le_antisymm hb₂.2 hb₂.1)
  have hv_cross : CrossesOn (univ : Set Circle) v₁ v₂ z₁ z₂ := by
    rw [crossesOn_univ_iff_circleCoordFrom x]
    refine ⟨hv₁_ne_v₂, hz₁z₂_ne, hz₁_ne_v₁.symm, hz₂_ne_v₁.symm,
      hz₁_ne_v₂.symm, hz₂_ne_v₂.symm, ?_⟩
    simp only [onOpenArc, circleCoordFrom]
    rw [min_eq_left hle_v, max_eq_right hle_v]
    have hz₁_open : (x.angleDiff v₁ < x.angleDiff z₁ ∧ x.angleDiff z₁ < x.angleDiff v₂) ↔
        (x.angleDiff v₁ ≤ x.angleDiff z₁ ∧ x.angleDiff z₁ ≤ x.angleDiff v₂) :=
      ⟨fun ⟨h1, h2⟩ => ⟨h1.le, h2.le⟩,
       fun ⟨h1, h2⟩ => ⟨lt_of_le_of_ne h1 hz₁_ne_v₁_ang.symm, lt_of_le_of_ne h2 hz₁_ne_v₂_ang⟩⟩
    have hz₂_open : (x.angleDiff v₁ < x.angleDiff z₂ ∧ x.angleDiff z₂ < x.angleDiff v₂) ↔
        (x.angleDiff v₁ ≤ x.angleDiff z₂ ∧ x.angleDiff z₂ ≤ x.angleDiff v₂) :=
      ⟨fun ⟨h1, h2⟩ => ⟨h1.le, h2.le⟩,
       fun ⟨h1, h2⟩ => ⟨lt_of_le_of_ne h1 hz₂_ne_v₁_ang.symm, lt_of_le_of_ne h2 hz₂_ne_v₂_ang⟩⟩
    rwa [hz₁_open, hz₂_open]
  exact hCF ⟨δ, hδ, δ', hδ', hδ_ne_δ', v₁, hv₁δ, v₂, hv₂δ, z₁, hz₁, z₂, hz₂, hv_cross⟩

private lemma dual_active_of_primal_active {U : Set Circle} {Δ : Set (Set Circle)}
    (hΔ : IsDivision Δ) (hV_fin : (divisionUnion Δ).Finite)
    (hU : IsDualPointSet (univ : Set Circle) (divisionUnion Δ) U)
    (hCF : IsCrossFree (univ : Set Circle) Δ)
    {x y : Circle} (hx : x ∈ divisionUnion Δ ∪ U) (hy : y ∈ divisionUnion Δ ∪ U)
    (hxy : x ≠ y) {δ : Set Circle} (hδ : δ ∈ Δ) (hact : IsActiveFor x y δ) :
    ∃ v₁ ∈ δ, ∃ v₂ ∈ δ,
      (∀ v ∈ δ, x.angleDiff v₁ ≤ x.angleDiff v ∧ x.angleDiff v ≤ x.angleDiff v₂) ∧
      x.angleDiff v₁ ≤ x.angleDiff y ∧ x.angleDiff y ≤ x.angleDiff v₂ ∧
      ∃ u₁ u₂ : Circle,
        U ∩ prevSegment (divisionUnion Δ) v₁ = {u₁} ∧
        U ∩ nextSegment (divisionUnion Δ) v₂ = {u₂} ∧
        ∃ δ_star ∈ dualDivision (univ : Set Circle) U Δ,
          u₁ ∈ δ_star ∧ u₂ ∈ δ_star ∧
          IsActiveFor y x δ_star ∧
          (∀ u ∈ δ_star, y.angleDiff u₂ ≤ y.angleDiff u ∧ y.angleDiff u ≤ y.angleDiff u₁) := by
  have hU_sub : U ⊆ (univ : Set Circle) \ divisionUnion Δ := isDualPointSet_subset_diff hU
  have hδ_fin : δ.Finite := hV_fin.subset (subset_sUnion_of_mem hδ)
  have hδ_ne : δ.Nonempty := hΔ.2.1 δ hδ
  obtain ⟨v₁, hv₁δ, hmin₁⟩ := exists_min_on_finite hδ_fin hδ_ne (Circle.angleDiff x)
  obtain ⟨v₂, hv₂δ, hmax₂⟩ := exists_max_on_finite hδ_fin hδ_ne (Circle.angleDiff x)
  rcases hact with ⟨hxδ, ⟨w₁, hw₁δ, hw₁le⟩, ⟨w₂, hw₂δ, hw₂ge⟩⟩
  have hv₁_le_y : x.angleDiff v₁ ≤ x.angleDiff y := (hmin₁ w₁ hw₁δ).trans hw₁le
  have hy_le_v₂ : x.angleDiff y ≤ x.angleDiff v₂ := hw₂ge.trans (hmax₂ w₂ hw₂δ)
  have hv₁V : v₁ ∈ divisionUnion Δ := ⟨δ, hδ, hv₁δ⟩
  have hv₂V : v₂ ∈ divisionUnion Δ := ⟨δ, hδ, hv₂δ⟩
  have hv₁x : x ≠ v₁ := fun h => hxδ (h ▸ hv₁δ)
  have hv₂x : x ≠ v₂ := fun h => hxδ (h ▸ hv₂δ)
  obtain ⟨u₁, hu₁_eq⟩ := exists_unique_mem_prevSegment_of_isDualPointSet hV_fin hU hv₁V
  obtain ⟨hu₁U, hu₁v₁, hxu₁_lt_v₁, hno_V_1, hno_U_1⟩ :=
    prevSegment_angleDiff_bounds hU hx hv₁V hv₁x hu₁_eq
  obtain ⟨u₂, hu₂_eq⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV_fin hU hv₂V
  have hxv₂_lt_u₂_all :
      u₂ ∈ U ∧ u₂ ≠ v₂ ∧
      (x = u₂ ∨ x.angleDiff v₂ < x.angleDiff u₂) ∧
      (∀ w ∈ divisionUnion Δ, (x = u₂ ∨ x.angleDiff w ≤ x.angleDiff u₂) → x.angleDiff w
        ≤ x.angleDiff v₂) ∧
      (∀ u ∈ U, (x ≠ u₂ → x.angleDiff u < x.angleDiff u₂) → x.angleDiff u < x.angleDiff v₂) := by
    by_cases hxV : x ∈ divisionUnion Δ
    · obtain ⟨hu₂U, hu₂v₂, hvw₂, hu'w₂⟩ := nextSegment_dual_properties hU hv₂V hu₂_eq
      have hxu₂_ne : x ≠ u₂ := fun h => (hU_sub hu₂U).2 (h ▸ hxV)
      have hxv₂_pos := Circle.angleDiff_pos hv₂x
      have hxv₂_lt_2pi := Circle.angleDiff_lt_two_pi x v₂
      have hsum_xv₂ := Circle.angleDiff_add_angleDiff hv₂x
      have hv₂u₂_pos := Circle.angleDiff_pos hu₂v₂.symm
      have hxu₂_pos := Circle.angleDiff_pos hxu₂_ne
      have hxu₂_lt_2pi := Circle.angleDiff_lt_two_pi x u₂
      have hlt_x := hvw₂ x ⟨hxV, hv₂x⟩
      have hlt_u₂ : x.angleDiff v₂ < x.angleDiff u₂ := by
        rcases angleDiff_cases x v₂ u₂ with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
      refine ⟨hu₂U, hu₂v₂, Or.inr hlt_u₂, ?_, ?_⟩
      · intro w hw hle
        rcases eq_or_ne w v₂ with rfl | hwv₂
        · exact le_rfl
        · have hlt := hvw₂ w ⟨hw, hwv₂⟩
          rcases eq_or_ne x w with rfl | hxw_ne
          · have hx0 : x.angleDiff x = 0 := circleCoordFrom_self x
            linarith
          · have hxw_pos := Circle.angleDiff_pos hxw_ne
            have hxw_lt_2pi := Circle.angleDiff_lt_two_pi x w
            have hv₂w_pos := Circle.angleDiff_pos hwv₂.symm
            have hle' := hle.resolve_left hxu₂_ne
            rcases angleDiff_cases x v₂ w with ⟨_, heq_w⟩ | ⟨_, heq_w⟩ <;>
              rcases angleDiff_cases x v₂ u₂ with ⟨_, heq_u₂⟩ | ⟨_, heq_u₂⟩ <;>
              linarith
      · intro u huU hu_lt_u₂
        by_contra! hge
        have hlt' := hu_lt_u₂ hxu₂_ne
        have hu_ne_u₂ : u ≠ u₂ := fun h => by subst h; linarith
        obtain ⟨w, _, hlt1, hlt2⟩ := hu'w₂ u ⟨huU, hu_ne_u₂⟩
        have hlt := hlt1.trans hlt2
        have hxu_lt_2pi := Circle.angleDiff_lt_two_pi x u
        have hv₂u_ne : v₂ ≠ u := fun h => (hU_sub huU).2 (h ▸ hv₂V)
        have hv₂u_pos := Circle.angleDiff_pos hv₂u_ne
        rcases angleDiff_cases x v₂ u with ⟨_, heq_u⟩ | ⟨_, heq_u⟩ <;>
          rcases angleDiff_cases x v₂ u₂ with ⟨_, heq_u₂⟩ | ⟨_, heq_u₂⟩ <;>
          linarith
    · exact nextSegment_angleDiff_bounds hU hx hv₂V hv₂x hxV hu₂_eq
  obtain ⟨hu₂U, hu₂v₂, hxv₂_lt_u₂, hno_V_2, hno_U_2⟩ := hxv₂_lt_u₂_all
  have hxy_pos := Circle.angleDiff_pos hxy
  have hxy_lt_2pi := Circle.angleDiff_lt_two_pi x y
  have hsum_xy := Circle.angleDiff_add_angleDiff hxy
  have hxv₁_pos := Circle.angleDiff_pos hv₁x
  have hxv₂_pos := Circle.angleDiff_pos hv₂x
  have hxv₁_lt_2pi := Circle.angleDiff_lt_two_pi x v₁
  have hxv₂_lt_2pi := Circle.angleDiff_lt_two_pi x v₂
  have hu₁u₂_rel : dualEquivRel (univ : Set Circle) Δ u₁ u₂ :=
    dualEquivRel_of_angle_bounds hΔ hCF hδ hv₁δ hv₂δ hmin₁ hmax₂ hxu₁_lt_v₁
      (hv₁_le_y.trans hy_le_v₂) hxv₂_lt_u₂ hno_V_1 hno_V_2
  -- Step 5: Every u ∈ δ_star lies outside (v₁, v₂)
  let δ_star := {u' ∈ U | dualEquivRel (univ : Set Circle) Δ u₁ u'}
  have hδ_star_mem : δ_star ∈ dualDivision (univ : Set Circle) U Δ := ⟨u₁, hu₁U, rfl⟩
  have hu₁_in : u₁ ∈ δ_star := ⟨hu₁U, dualEquivRel_refl _ _ u₁⟩
  have hu₂_in : u₂ ∈ δ_star := ⟨hu₂U, hu₁u₂_rel⟩
  have hδ_star_outside : ∀ u ∈ δ_star,
      x.angleDiff u ≤ x.angleDiff u₁ ∨ (x ≠ u₂ ∧ x.angleDiff u₂ ≤ x.angleDiff u) := by
    intro u ⟨huU, hrel⟩
    by_contra! hbetween
    rcases hbetween with ⟨hu₁_lt_u, hu_lt_u₂⟩
    have hu_gt_v₁ : x.angleDiff v₁ < x.angleDiff u := hno_U_1 u huU hu₁_lt_u
    have hu_lt_v₂ : x.angleDiff u < x.angleDiff v₂ := hno_U_2 u huU hu_lt_u₂
    have hv₁v₂_ne : v₁ ≠ v₂ := fun h => by subst h; linarith
    have hu₁u_ne : u₁ ≠ u := fun h => by subst h; linarith
    have hv₁u₁_ne : v₁ ≠ u₁ := hu₁v₁.symm
    have hv₁u_ne : v₁ ≠ u := fun h => (hU_sub huU).2 (h ▸ hv₁V)
    have hv₂u₁_ne : v₂ ≠ u₁ := fun h => (hU_sub hu₁U).2 (h ▸ hv₂V)
    have hv₂u_ne : v₂ ≠ u := fun h => (hU_sub huU).2 (h ▸ hv₂V)
    have hcross : CrossesOn (univ : Set Circle) v₁ v₂ u₁ u := by
      rw [crossesOn_univ_iff_circleCoordFrom x]
      refine ⟨hv₁v₂_ne, hu₁u_ne, hv₁u₁_ne, hv₁u_ne, hv₂u₁_ne, hv₂u_ne, ?_⟩
      simp only [onOpenArc, circleCoordFrom]
      have hle_v : x.angleDiff v₁ ≤ x.angleDiff v₂ := hv₁_le_y.trans hy_le_v₂
      rw [min_eq_left hle_v, max_eq_right hle_v]
      exact ⟨fun ⟨h1, _⟩ => (lt_irrefl _ (hxu₁_lt_v₁.trans h1)).elim,
             fun hnot => (hnot ⟨hu_gt_v₁, hu_lt_v₂⟩).elim⟩
    exact hrel ⟨δ, hδ, v₁, hv₁δ, v₂, hv₂δ, hcross⟩
  -- Step 6: Translate to y.angleDiff bounds!
  have hy_not_in : y ∉ δ_star := by
    intro hy_in
    rcases hy with hyV | hyU
    · exact (hU_sub hy_in.1).2 hyV
    · have hyv₁_ne : y ≠ v₁ := fun h => (hU_sub hyU).2 (h ▸ hv₁V)
      have hyv₂_ne : y ≠ v₂ := fun h => (hU_sub hyU).2 (h ▸ hv₂V)
      have hv₁_lt_y : x.angleDiff v₁ < x.angleDiff y :=
        lt_of_le_of_ne hv₁_le_y ((circleCoordFrom x).injective.ne hyv₁_ne.symm)
      have hy_lt_v₂ : x.angleDiff y < x.angleDiff v₂ :=
        lt_of_le_of_ne hy_le_v₂ ((circleCoordFrom x).injective.ne hyv₂_ne)
      rcases hδ_star_outside y hy_in with hle1 | ⟨hxu₂, hge2⟩
      · linarith
      · rcases hxv₂_lt_u₂ with rfl | hlt_u₂
        · exact hxu₂ rfl
        · linarith
  have hx0 : x.angleDiff x = 0 := circleCoordFrom_self x
  have hxu₁_nonneg := Circle.angleDiff_nonneg x u₁
  have hxu₁_lt_2pi := Circle.angleDiff_lt_two_pi x u₁
  have hxu₂_nonneg := Circle.angleDiff_nonneg x u₂
  have hxu₂_lt_2pi := Circle.angleDiff_lt_two_pi x u₂
  have hyu₁_val : y.angleDiff u₁ = x.angleDiff u₁ - x.angleDiff y + 2 * Real.pi := by
    rcases angleDiff_cases x y u₁ with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
  have hyu₂_val : (x = u₂ ∧ y.angleDiff u₂ = 2 * Real.pi - x.angleDiff y) ∨
      (x ≠ u₂ ∧ y.angleDiff u₂ = x.angleDiff u₂ - x.angleDiff y) := by
    rcases hxv₂_lt_u₂ with rfl | hlt_u₂
    · left
      refine ⟨rfl, ?_⟩
      rcases angleDiff_cases x y x with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
    · right
      refine ⟨fun h => by subst h; linarith, ?_⟩
      rcases angleDiff_cases x y u₂ with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
  have hy_bounds : ∀ u ∈ δ_star, y.angleDiff u₂ ≤ y.angleDiff u ∧ y.angleDiff u ≤ y.angleDiff u₁
    := by
    intro u hu
    have hxu_nonneg := Circle.angleDiff_nonneg x u
    have hxu_lt_2pi := Circle.angleDiff_lt_two_pi x u
    rcases hδ_star_outside u hu with hle1 | ⟨hxu₂, hge2⟩
    · have hyu_val : y.angleDiff u = x.angleDiff u - x.angleDiff y + 2 * Real.pi := by
        rcases angleDiff_cases x y u with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
      rcases hyu₂_val with ⟨_, heq₂⟩ | ⟨_, heq₂⟩ <;> refine ⟨?_, ?_⟩ <;> linarith
    · rcases hyu₂_val with ⟨rfl, _⟩ | ⟨_, heq₂⟩
      · exact (hxu₂ rfl).elim
      · rcases hxv₂_lt_u₂ with rfl | hlt_u₂
        · exact (hxu₂ rfl).elim
        · have hyu_val : y.angleDiff u = x.angleDiff u - x.angleDiff y := by
            rcases angleDiff_cases x y u with ⟨_, heq⟩ | ⟨_, heq⟩ <;> linarith
          refine ⟨?_, ?_⟩ <;> linarith
  have hyu₂_le_yx : y.angleDiff u₂ ≤ y.angleDiff x := by
    rcases hyu₂_val with ⟨_, heq₂⟩ | ⟨_, heq₂⟩ <;> linarith
  have hyx_le_yu₁ : y.angleDiff x ≤ y.angleDiff u₁ := by
    linarith
  refine ⟨v₁, hv₁δ, v₂, hv₂δ, fun v hv => ⟨hmin₁ v hv, hmax₂ v hv⟩,
    hv₁_le_y, hy_le_v₂, u₁, u₂, hu₁_eq, hu₂_eq,
    δ_star, hδ_star_mem, hu₁_in, hu₂_in,
    ⟨hy_not_in, ⟨u₂, hu₂_in, hyu₂_le_yx⟩, ⟨u₁, hu₁_in, hyx_le_yu₁⟩⟩,
    hy_bounds⟩

private lemma active_ncard_le_dual_active_ncard {U : Set Circle} {Δ : Set (Set Circle)}
    (hΔ : IsDivision Δ) (hV_fin : (divisionUnion Δ).Finite)
    (hU : IsDualPointSet (univ : Set Circle) (divisionUnion Δ) U)
    (hCF : IsCrossFree (univ : Set Circle) Δ)
    {x y : Circle} (hx : x ∈ divisionUnion Δ ∪ U) (hy : y ∈ divisionUnion Δ ∪ U)
    (hxy : x ≠ y) :
    {δ ∈ Δ | IsActiveFor x y δ}.ncard ≤
      {δ_star ∈ dualDivision (univ : Set Circle) U Δ | IsActiveFor y x δ_star}.ncard := by
  let V := divisionUnion Δ
  let Δ_star := dualDivision (univ : Set Circle) U Δ
  have hΔ_star_div : IsDivision Δ_star := isDivision_dualDivision_univ hV_fin hU
  have hS₂_fin : {δ_star ∈ Δ_star | IsActiveFor y x δ_star}.Finite :=
    hΔ_star_div.1.subset fun _ h => h.1
  have hex : ∀ δ : Set Circle,
      ∃ δ_star : Set Circle, δ ∈ {δ ∈ Δ | IsActiveFor x y δ} →
        δ_star ∈ {δ_star ∈ Δ_star | IsActiveFor y x δ_star} ∧
        ∃ v₁ ∈ δ, ∃ u₁ ∈ δ_star,
          U ∩ prevSegment V v₁ = {u₁} ∧
          ∀ u ∈ δ_star, y.angleDiff u ≤ y.angleDiff u₁ := by
    intro δ
    by_cases h : δ ∈ {δ ∈ Δ | IsActiveFor x y δ}
    · obtain ⟨v₁, hv₁δ, _, _, _, _, _, u₁, _, hu₁_eq, _, δ_star, hδ_star, hu₁_in, _, hact_star,
      hy_b⟩ :=
        dual_active_of_primal_active hΔ hV_fin hU hCF hx hy hxy h.1 h.2
      exact ⟨δ_star, fun _ => ⟨⟨hδ_star, hact_star⟩, v₁, hv₁δ, u₁, hu₁_in, hu₁_eq, fun u hu =>
        (hy_b u hu).2⟩⟩
    · exact ⟨∅, fun h' => (h h').elim⟩
  choose f hf using hex
  refine ncard_le_ncard_of_injOn f
    (fun δ hδ => (hf δ hδ).1) (fun δ₁ hδ₁ δ₂ hδ₂ heq => ?_) hS₂_fin
  obtain ⟨_, v₁, hv₁, u₁, hu₁, hu₁_eq, hmax₁⟩ := hf δ₁ hδ₁
  obtain ⟨_, v₁', hv₁', u₁', hu₁', hu₁'_eq, hmax₁'⟩ := hf δ₂ hδ₂
  rw [heq] at hu₁ hmax₁
  have hu_eq : u₁ = u₁' :=
    (circleCoordFrom y).injective (le_antisymm (hmax₁' u₁ hu₁) (hmax₁ u₁' hu₁'))
  rw [hu_eq] at hu₁_eq
  have hv₁V : v₁ ∈ V := ⟨δ₁, hδ₁.1, hv₁⟩
  have hv₁'V : v₁' ∈ V := ⟨δ₂, hδ₂.1, hv₁'⟩
  have hu₁'_in₁ : u₁' ∈ prevSegment V v₁ := by
    have : u₁' ∈ U ∩ prevSegment V v₁ := by rw [hu₁_eq]; exact mem_singleton u₁'
    exact this.2
  have hu₁'_in₂ : u₁' ∈ prevSegment V v₁' := by
    have : u₁' ∈ U ∩ prevSegment V v₁' := by rw [hu₁'_eq]; exact mem_singleton u₁'
    exact this.2
  have hu₁'_compl : u₁' ∈ Vᶜ := prevSegment_subset_compl hu₁'_in₁
  obtain ⟨_, _, huniq⟩ := exists_unique_prevSegment_of_mem_compl hV_fin ⟨v₁, hv₁V⟩ hu₁'_compl
  have hv_eq : v₁ = v₁' := (huniq v₁ ⟨hv₁V, hu₁'_in₁⟩).trans (huniq v₁' ⟨hv₁'V, hu₁'_in₂⟩).symm
  rw [hv_eq] at hv₁
  by_contra hne
  exact (hΔ.2.2 hδ₁.1 hδ₂.1 hne).ne_of_mem hv₁ hv₁' rfl

/-! ## 5. Proof of (2.4) -/

theorem theorem_2_4_univ (U : Set Circle) (Δ : Set (Set Circle)) (x y : Circle)
    (hΔ : IsDivision Δ) (hV_fin : (divisionUnion Δ).Finite)
    (hU : IsDualPointSet (univ : Set Circle) (divisionUnion Δ) U)
    (hCF : IsCrossFree (univ : Set Circle) Δ)
    (hx : x ∈ divisionUnion Δ ∪ U) (hy : y ∈ divisionUnion Δ ∪ U) :
    ((x ∈ divisionUnion Δ ∧ y ∈ divisionUnion Δ →
        (divisionCount (univ : Set Circle) Δ x y : ℤ) -
          (divisionCount (univ : Set Circle) (dualDivision (univ : Set Circle) U Δ) x y : ℤ) = 1) ∧
     (x ∈ U ∧ y ∈ U →
        (divisionCount (univ : Set Circle) Δ x y : ℤ) -
          (divisionCount (univ : Set Circle) (dualDivision (univ : Set Circle) U Δ) x y : ℤ) = -1) ∧
     (¬ (x ∈ divisionUnion Δ ∧ y ∈ divisionUnion Δ) → ¬ (x ∈ U ∧ y ∈ U) →
        (divisionCount (univ : Set Circle) Δ x y : ℤ) -
          (divisionCount (univ : Set Circle) (dualDivision (univ : Set Circle) U Δ) x y : ℤ) = 0))
            := by
  rcases eq_or_ne x y with rfl | hxy
  · exact theorem_2_4_self (univ : Set Circle) U Δ x hV_fin (subset_univ _)
      isOArc_univ_circle hΔ hU hx
  let V := divisionUnion Δ
  let Δ_star := dualDivision (univ : Set Circle) U Δ
  have hU_sub : U ⊆ (univ : Set Circle) \ V := isDualPointSet_subset_diff hU
  have hΔ_star_div : IsDivision Δ_star := isDivision_dualDivision_univ hV_fin hU
  have hΔ_star_union : divisionUnion Δ_star = U := divisionUnion_dualDivision _ U Δ
  have hU_fin : U.Finite := finite_of_isDualPointSet_univ hV_fin hU
  have hU_symm : IsDualPointSet (univ : Set Circle) U V := isDualPointSet_univ_symm hV_fin hU
  have hU_symm' : IsDualPointSet (univ : Set Circle) (divisionUnion Δ_star) V := by
    rwa [hΔ_star_union]
  have hCF_star : IsCrossFree (univ : Set Circle) Δ_star :=
    theorem_2_1_proof (univ : Set Circle) U Δ isOArc_univ_circle hΔ (subset_univ _) hU
  have hdd : dualDivision (univ : Set Circle) V Δ_star = Δ :=
    theorem_2_2_univ U Δ hΔ hV_fin hU hCF
  have hle₁ := active_ncard_le_dual_active_ncard hΔ hV_fin hU hCF hx hy hxy
  have hx' : x ∈ divisionUnion Δ_star ∪ V := by
    rw [hΔ_star_union, union_comm]
    exact hx
  have hy' : y ∈ divisionUnion Δ_star ∪ V := by
    rw [hΔ_star_union, union_comm]
    exact hy
  have hle₂ : {δ_star ∈ Δ_star | IsActiveFor y x δ_star}.ncard ≤
      {δ ∈ Δ | IsActiveFor x y δ}.ncard := by
    have h := active_ncard_le_dual_active_ncard hΔ_star_div (hΔ_star_union ▸ hU_fin)
      hU_symm' hCF_star hy' hx' hxy.symm
    rwa [hdd] at h
  have hact_eq : {δ ∈ Δ | IsActiveFor x y δ}.ncard =
      {δ_star ∈ Δ_star | IsActiveFor y x δ_star}.ncard := le_antisymm hle₁ hle₂
  have hcount_symm : divisionCount (univ : Set Circle) Δ_star x y =
      divisionCount (univ : Set Circle) Δ_star y x := by
    unfold divisionCount
    congr 1
    ext δ_star
    simp only [mem_ofPred_eq, pair_comm x y]
    refine and_congr_right fun _ => or_congr_right ?_
    exact exists_congr fun u => and_congr_right fun _ =>
      exists_congr fun v => and_congr_right fun _ =>
      ⟨CrossesOn.symm_right, CrossesOn.symm_right⟩
  have h1 := divisionCount_eq_active_add_mem hΔ hxy
  have h2 := divisionCount_eq_active_add_mem hΔ_star_div hxy.symm
  rw [hΔ_star_union, ← hcount_symm] at h2
  have hmain : (divisionCount (univ : Set Circle) Δ x y : ℤ) - ((divisionUnion Δ ∩ {x}).ncard : ℤ) =
      (divisionCount (univ : Set Circle) (dualDivision (univ : Set Circle) U Δ) x y : ℤ) -
        ((U ∩ {y}).ncard : ℤ) := by
    rw [h1, h2, hact_eq]
  have hxV_card : ∀ (h : x ∈ divisionUnion Δ), (divisionUnion Δ ∩ {x}).ncard = 1 := fun h => by
    have heq : divisionUnion Δ ∩ {x} = {x} := inter_eq_right.mpr (singleton_subset_iff.mpr h)
    rw [heq, ncard_singleton]
  have hxV_not_card : ∀ (h : x ∉ divisionUnion Δ), (divisionUnion Δ ∩ {x}).ncard = 0 := fun h => by
    have heq : divisionUnion Δ ∩ {x} = ∅ := by
      ext z; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro hz rfl; exact h hz
    rw [heq, ncard_empty]
  have hyU_card : ∀ (h : y ∈ U), (U ∩ {y}).ncard = 1 := fun h => by
    have heq : U ∩ {y} = {y} := inter_eq_right.mpr (singleton_subset_iff.mpr h)
    rw [heq, ncard_singleton]
  have hyU_not_card : ∀ (h : y ∉ U), (U ∩ {y}).ncard = 0 := fun h => by
    have heq : U ∩ {y} = ∅ := by
      ext z; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro hz rfl; exact h hz
    rw [heq, ncard_empty]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hxV, hyV⟩
    have hyU : y ∉ U := fun h => (hU_sub h).2 hyV
    rw [hxV_card hxV, hyU_not_card hyU] at hmain
    omega
  · rintro ⟨hxU, hyU⟩
    have hxV : x ∉ divisionUnion Δ := (hU_sub hxU).2
    rw [hxV_not_card hxV, hyU_card hyU] at hmain
    omega
  · intro hnotV hnotU
    rcases hx with hxV | hxU <;> rcases hy with hyV | hyU
    · exact (hnotV ⟨hxV, hyV⟩).elim
    · rw [hxV_card hxV, hyU_card hyU] at hmain
      omega
    · have hxV' : x ∉ divisionUnion Δ := (hU_sub hxU).2
      have hyU' : y ∉ U := fun h => (hU_sub h).2 hyV
      rw [hxV_not_card hxV', hyU_not_card hyU'] at hmain
      omega
    · exact (hnotU ⟨hxU, hyU⟩).elim

/-- **Graph Minors VI, (2.4)** (page 118):
"If $\Delta$ is cross-free and $x, y \in W$, then
$$\begin{aligned}
\Delta(x, y) - \Delta^*(x, y) &= 1 &&\text{if } x, y \in V \\
&= -1 &&\text{if } x, y \in U. \\
&= 0 &&\text{otherwise.}
\end{aligned}$$" -/
theorem theorem_2_4_proof : Statement24 := by
  intro S _ C U Δ x y hC hΔ hV_fin hV_sub hU hCF hx hy
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  have hrange := range_oArcMap φ
  let U₀ := oArcMap φ ⁻¹' U
  let Δ₀ := (preimage (oArcMap φ)) '' Δ
  have hU_sub : U ⊆ C \ divisionUnion Δ := isDualPointSet_subset_diff hU
  have hU_eq : oArcMap φ '' U₀ = U :=
    image_preimage_eq_of_subset (hU_sub.trans (sdiff_subset.trans hrange.symm.subset))
  have hΔ_eq : (image (oArcMap φ)) '' Δ₀ = Δ := by
    ext δ
    simp only [Δ₀, mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨δ', hδ', rfl⟩
      have hsub : δ' ⊆ range (oArcMap φ) := by
        rw [hrange]
        exact (subset_sUnion_of_mem hδ').trans hV_sub
      rwa [image_preimage_eq_of_subset hsub]
    · intro hδ
      have hsub : δ ⊆ range (oArcMap φ) := by
        rw [hrange]
        exact (subset_sUnion_of_mem hδ).trans hV_sub
      exact ⟨δ, hδ, image_preimage_eq_of_subset hsub⟩
  have hΔ₀ : IsDivision Δ₀ := by
    rw [← isDivision_oArcMap_iff φ, hΔ_eq]
    exact hΔ
  have hV₀_fin : (divisionUnion Δ₀).Finite := by
    refine Finite.of_finite_image ?_ hinj.injOn
    rw [← divisionUnion_oArcMap φ, hΔ_eq]
    exact hV_fin
  have hU₀ : IsDualPointSet (univ : Set Circle) (divisionUnion Δ₀) U₀ := by
    rw [← isDualPointSet_oArcMap_iff φ, ← divisionUnion_oArcMap φ, hΔ_eq, hU_eq]
    exact hU
  have hCF₀ : IsCrossFree (univ : Set Circle) Δ₀ := by
    rw [← isCrossFree_oArcMap_iff φ, hΔ_eq]
    exact hCF
  have hW_sub : divisionUnion Δ ∪ U ⊆ C := union_subset hV_sub (hU_sub.trans sdiff_subset)
  let x₀ := φ.symm ⟨x, hW_sub hx⟩
  let y₀ := φ.symm ⟨y, hW_sub hy⟩
  have hx₀_eq : oArcMap φ x₀ = x := by simp [oArcMap, x₀]
  have hy₀_eq : oArcMap φ y₀ = y := by simp [oArcMap, y₀]
  have hx₀_V : x₀ ∈ divisionUnion Δ₀ ↔ x ∈ divisionUnion Δ := by
    rw [← hinj.mem_set_image, ← divisionUnion_oArcMap φ, hΔ_eq, hx₀_eq]
  have hy₀_V : y₀ ∈ divisionUnion Δ₀ ↔ y ∈ divisionUnion Δ := by
    rw [← hinj.mem_set_image, ← divisionUnion_oArcMap φ, hΔ_eq, hy₀_eq]
  have hx₀_U : x₀ ∈ U₀ ↔ x ∈ U := by
    change oArcMap φ x₀ ∈ U ↔ x ∈ U
    rw [hx₀_eq]
  have hy₀_U : y₀ ∈ U₀ ↔ y ∈ U := by
    change oArcMap φ y₀ ∈ U ↔ y ∈ U
    rw [hy₀_eq]
  have hx₀ : x₀ ∈ divisionUnion Δ₀ ∪ U₀ := by
    rw [mem_union, hx₀_V, hx₀_U]
    exact hx
  have hy₀ : y₀ ∈ divisionUnion Δ₀ ∪ U₀ := by
    rw [mem_union, hy₀_V, hy₀_U]
    exact hy
  have hcount₁ : divisionCount C Δ x y = divisionCount (univ : Set Circle) Δ₀ x₀ y₀ := by
    rw [← hΔ_eq, ← hx₀_eq, ← hy₀_eq, divisionCount_oArcMap]
  have hcount₂ : divisionCount C (dualDivision C U Δ) x y =
      divisionCount (univ : Set Circle) (dualDivision (univ : Set Circle) U₀ Δ₀) x₀ y₀ := by
    rw [← hU_eq, ← hΔ_eq, dualDivision_oArcMap, ← hx₀_eq, ← hy₀_eq, divisionCount_oArcMap]
  rw [hcount₁, hcount₂, ← hx₀_V, ← hy₀_V, ← hx₀_U, ← hy₀_U]
  exact theorem_2_4_univ U₀ Δ₀ x₀ y₀ hΔ₀ hV₀_fin hU₀ hCF₀ hx₀ hy₀

end GraphMinor.GM06
