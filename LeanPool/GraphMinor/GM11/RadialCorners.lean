/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# The corners of the union of a drawing and its radial drawing

Let `H` be the union of a 2-cell drawing `Γ` with an edge and a radial drawing `Γ'` of `Γ`. This
file
looks at the rotation of `H` at a vertex.

At a vertex of `Γ`, no corner lies between two edges of `Γ`: this is `corner_has_spoke`, and it
comes
from the maximality of `Γ'`. The other results of this file are tools for `RadialFaces.lean`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A point of the unit interval other than `0`, with image in a given neighbourhood. -/
theorem exists_pos_mem {g : I → S} (hg : Continuous g) {N : Set S} (hN : IsOpen N)
    (h0 : g 0 ∈ N) : ∃ t, 0 < t ∧ g t ∈ N := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hN.preimage hg) 0 h0
  let t : I := ⟨min (δ / 2) 1, le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have ht : (0 : ℝ) < t := lt_min (half_pos hδ) one_pos
  refine ⟨t, ht, hball ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  show |(t : ℝ) - ((0 : I) : ℝ)| < δ
  rw [Icc.coe_zero, sub_zero, abs_of_pos ht]
  have : (t : ℝ) ≤ δ / 2 := min_le_left _ _
  linarith

/-- All the points of a path up to some positive time lie in a given neighbourhood. -/
theorem exists_pos_le {g : I → S} (hg : Continuous g) {N : Set S} (hN : IsOpen N)
    (h0 : g 0 ∈ N) {a : I} (ha : 0 < a) : ∃ u, 0 < u ∧ u ≤ a ∧ ∀ s, s ≤ u → g s ∈ N := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hN.preimage hg) 0 h0
  have ha' : (0 : ℝ) < a := ha
  let u : I := ⟨min (δ / 2) a, le_min (by positivity) ha'.le, (min_le_right _ _).trans a.2.2⟩
  have hu : (0 : ℝ) < u := lt_min (half_pos hδ) ha'
  refine ⟨u, hu, Subtype.coe_le_coe.mp (min_le_right _ _), fun s hs => hball ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  show |(s : ℝ) - ((0 : I) : ℝ)| < δ
  have hs' : (s : ℝ) ≤ u := hs
  have hu' : (u : ℝ) ≤ δ / 2 := min_le_left _ _
  rw [Icc.coe_zero, sub_zero, abs_of_nonneg s.2.1]
  linarith

/-- A piece of an injective path is a line. -/
theorem isLine_piece [T2Space S] {g : I → S} (hg : Continuous g) (hi : Function.Injective g)
    {a b : I} (hab : a < b) : IsLineWithEnds (g '' Icc a b) (g a) (g b) := by
  have hab' : (a : ℝ) < b := hab
  let m : I → I := fun t => ⟨(1 - (t : ℝ)) * a + t * b, by
    have := t.2.1
    have := t.2.2
    have := a.2.1
    have := b.2.1
    nlinarith, by
    have := t.2.1
    have := t.2.2
    have := a.2.2
    have := b.2.2
    nlinarith⟩
  have hm : Continuous m := Continuous.subtype_mk (by fun_prop) _
  have hmi : Function.Injective m := by
    intro s t h
    have h' : (1 - (s : ℝ)) * a + s * b = (1 - (t : ℝ)) * a + t * b := congrArg Subtype.val h
    have h₂ : ((s : ℝ) - t) * ((b : ℝ) - a) = 0 := by linarith
    have h₃ := (mul_eq_zero.mp h₂).resolve_right (by linarith)
    exact Subtype.ext (by linarith)
  have hm0 : m 0 = a := Subtype.ext (by simp [m])
  have hm1 : m 1 = b := Subtype.ext (by simp [m])
  have hr : g '' Icc a b = range (g ∘ m) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs₁ : (a : ℝ) ≤ s := hs.1
      have hs₂ : (s : ℝ) ≤ b := hs.2
      have hpos : (0 : ℝ) < (b : ℝ) - a := by linarith
      let t : I := ⟨((s : ℝ) - a) / ((b : ℝ) - a), div_nonneg (by linarith) hpos.le,
        (div_le_one hpos).mpr (by linarith)⟩
      refine ⟨t, ?_⟩
      have : m t = s := Subtype.ext (by
        change (1 - ((s : ℝ) - a) / ((b : ℝ) - a)) * a + ((s : ℝ) - a) / ((b : ℝ) - a) * b = s
        field_simp
        ring)
      simp [this]
    · rintro ⟨t, rfl⟩
      refine ⟨m t, ⟨?_, ?_⟩, rfl⟩
      · change (a : ℝ) ≤ (1 - (t : ℝ)) * a + t * b
        nlinarith [t.2.1]
      · change (1 - (t : ℝ)) * a + t * b ≤ b
        nlinarith [t.2.2]
  rw [hr]
  have := isLine_range (hg.comp hm) (hi.comp hmi)
  simpa [hm0, hm1] using this

variable {Γ Γ' : Drawing S} {e : Set S}

/-- Two different edges of a drawing meet only in vertices. -/
theorem closure_inter_subset_V {Γ : Drawing S} {e f : Set S} (he : e ∈ Γ.E) (hf : f ∈ Γ.E)
    (hef : e ≠ f) : closure e ∩ closure f ⊆ Γ.V := by
  rintro y ⟨h₁, h₂⟩
  by_contra hy
  exact hef (Γ.edge_eq_of_mem he hf ((Γ.closure_diff_V he).subset ⟨h₁, hy⟩)
    ((Γ.closure_diff_V hf).subset ⟨h₂, hy⟩))

/-- An edge with two different ends is a line with these ends. -/
theorem isLine_closure {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E) {x c : S} (hxc : x ≠ c)
    (hcap : closure e ∩ Γ.V = {x, c}) : IsLineWithEnds (closure e) x c := by
  rcases Γ.edge_cond e he with ⟨u, v, -, hc, hL⟩ | ⟨u, hc, -⟩
  · have hset : ({u, v} : Set S) = {x, c} := hc.symm.trans hcap
    have hx : x ∈ ({u, v} : Set S) := hset ▸ (Or.inl rfl)
    have hc' : c ∈ ({u, v} : Set S) := hset ▸ (Or.inr rfl)
    rcases hx with rfl | hx
    · rcases hc' with rfl | hc'
      · exact (hxc rfl).elim
      · obtain rfl : c = v := hc'
        exact hL
    · obtain rfl : x = v := hx
      rcases hc' with rfl | hc'
      · exact GraphMinor.GM11.IsLineWithEnds.symm hL
      · exact (hxc hc'.symm).elim
  · have hset : ({u} : Set S) = {x, c} := hc.symm.trans hcap
    have hx : x ∈ ({u} : Set S) := hset ▸ (Or.inl rfl)
    have hc' : c ∈ ({u} : Set S) := hset ▸ (Or.inr rfl)
    exact (hxc (hx.trans hc'.symm)).elim

/-- The edge `e`, as an injective path from the end `b`. The half-edge at `b` is its first half. -/
theorem exists_fullPar [T2Space S] {Γ : Drawing S} {γ : Set S → I → S}
  (hγ : EdgePar Γ γ) {e : Set S}
    (he : e ∈ Γ.E) (b : Bool) (hne : γ e 0 ≠ γ e 1) :
    ∃ g : I → S, Continuous g ∧ Function.Injective g ∧ g 0 = γ e (endOf b) ∧
      g 1 = γ e (endOf (!b)) ∧ range g = closure e ∧ ∀ t, spoke γ (e, b) t = g (halfT t) := by
  have hc := hγ.cont e he
  have hsplit : ∀ t : I, t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : I) 1 := by
    intro t
    by_cases h0 : t = 0
    · exact Or.inl h0
    by_cases h1 : t = 1
    · exact Or.inr (Or.inl h1)
    exact Or.inr (Or.inr ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr
      h1⟩)
  have hedge : ∀ t ∈ Ioo (0 : I) 1, γ e t ∈ e := fun t ht => (hγ.image e he).subset ⟨t, ht, rfl⟩
  have hinj : Function.Injective (γ e) := by
    intro s t h
    have hV0 : ∀ t ∈ Ioo (0 : I) 1, γ e t ≠ γ e 0 := fun t ht h' =>
      edge_notMem_V he (hedge t ht) (h' ▸ hγ.zero e he)
    have hV1 : ∀ t ∈ Ioo (0 : I) 1, γ e t ≠ γ e 1 := fun t ht h' =>
      edge_notMem_V he (hedge t ht) (h' ▸ hγ.one e he)
    rcases hsplit s with rfl | rfl | hs <;> rcases hsplit t with rfl | rfl | ht
    · rfl
    · exact (hne h).elim
    · exact (hV0 t ht h.symm).elim
    · exact (hne h.symm).elim
    · rfl
    · exact (hV1 t ht h.symm).elim
    · exact (hV0 s hs h).elim
    · exact (hV1 s hs h).elim
    · exact hγ.inj e he hs ht h
  have hrange : range (γ e) = closure e := by
    apply subset_antisymm
    · rintro _ ⟨t, rfl⟩
      rcases hsplit t with rfl | rfl | ht
      · exact end_mem_closure hγ he false
      · exact end_mem_closure hγ he true
      · exact subset_closure (hedge t ht)
    · refine closure_minimal ?_ (isCompact_range hc).isClosed
      exact (hγ.image e he).symm.subset.trans (image_subset_range _ _)
  cases b
  · exact ⟨γ e, hc, hinj, rfl, by simp [endOf], hrange, fun t => rfl⟩
  · refine ⟨fun t => γ e (σ t), hc.comp continuous_symm, hinj.comp symm_bijective.injective, ?_,
      ?_, ?_,
      fun t => rfl⟩
    · simp [endOf]
    · simp [endOf]
    · rw [← hrange]
      exact symm_bijective.surjective.range_comp _

/-- Two different edges of `Γ'` with the same ends `x`, `c` form an `O`-arc. -/
theorem isOArc_spokes [T2Space S] {e f : Set S} (he : e ∈ Γ'.E) (hf : f ∈ Γ'.E) (hef : e ≠ f)
    {x c : S} (hxc : x ≠ c) (hce : closure e ∩ Γ'.V = {x, c}) (hcf : closure f ∩ Γ'.V = {x, c}) :
    IsOArc (closure e ∪ closure f) := by
  refine isOArc_union (isLine_closure he hxc hce) (isLine_closure hf hxc hcf) fun y hy => ?_
  rw [← hce]
  exact ⟨hy.1, closure_inter_subset_V he hf hef hy⟩

private theorem corner_discs_inter [T2Space S] (hS : IsClosedSurface S)
    {C Q₁ Δ' : Set S} (hQ₁ : IsClosedDisc Q₁) (hΔ' : IsClosedDisc Δ')
    (hCb' : C ⊆ discBd Δ') (hCbQ : C ⊆ discBd Q₁)
    (hYfr : Disjoint (Q₁ \ C) (frontier Δ')) {x : S}
    (hxQ₁ : x ∈ Q₁) (hxC : x ∉ C) (hxΔ : x ∉ Δ') : Δ' ∩ Q₁ = C := by
  -- `Q₁ - C` is connected, so it misses `Δ'`.
  have hYconn : IsPreconnected (Q₁ \ C) := by
    refine (IsClosedDisc.isPreconnected_diff_frontier hS hQ₁).subset_closure ?_ ?_
    · rintro y ⟨hy', hn⟩
      rw [IsClosedDisc.frontier_eq_discBd hS hQ₁] at hn
      exact ⟨hy', fun h => hn (hCbQ h)⟩
    · exact sdiff_subset.trans (IsClosedDisc.subset_closure_diff_frontier hS hQ₁)
  have hYd : Disjoint (Q₁ \ C) Δ' := by
    rcases subset_or_disjoint_of_frontier hΔ'.isClosed hYconn hYfr with h | h
    · exact (hxΔ (h ⟨hxQ₁, hxC⟩)).elim
    · exact h
  have hinter : Δ' ∩ Q₁ = C := by
    apply subset_antisymm
    · rintro y ⟨h₁, h₂⟩
      by_contra hn
      exact disjoint_left.mp hYd ⟨h₂, hn⟩ h₁
    · exact fun y hy' => ⟨discBd_subset _ (hCb' hy'), discBd_subset _ (hCbQ hy')⟩
  exact hinter

omit [TopologicalSpace S] in
private theorem range_eq_image_halves (G : I → S) (u : I) :
    range G = G '' Icc 0 u ∪ G '' Icc u 1 := by
  apply subset_antisymm
  · rintro _ ⟨s, rfl⟩
    rcases le_total s u with h | h
    · exact Or.inl ⟨s, ⟨unitInterval.nonneg _, h⟩, rfl⟩
    · exact Or.inr ⟨s, ⟨h, unitInterval.le_one _⟩, rfl⟩
  · exact union_subset (image_subset_range _ _) (image_subset_range _ _)

/-- Two injective paths `G₁`, `G₂` from `x` to `c`, that start along the boundary of a closed disc
`Q`
and meet only at their ends, bound a closed disc in `r ∪ {x}`. Here `r` is an open disc not
containing
`x`, which contains the two paths without `x`, and also `Q` near `x` without the boundary of `Q`. -/
theorem exists_disc_of_corner [T2Space S] (hS : IsClosedSurface S) {Q W r ρ' : Set S}
    (hQ : IsClosedDisc Q) {x c : S} (hxQ : x ∈ discBd Q) (hW : IsOpen W) (hxW : x ∈ W)
    (hr : IsOpenDisc r) (hxr : x ∉ r) {G₁ G₂ : I → S} (hG₁ : Continuous G₁) (hG₂ : Continuous G₂)
    (hi₁ : Function.Injective G₁) (hi₂ : Function.Injective G₂) (h₁0 : G₁ 0 = x) (h₂0 : G₂ 0 = x)
    (h₁1 : G₁ 1 = c) (h₂1 : G₂ 1 = c) (hmeet : range G₁ ∩ range G₂ ⊆ {x, c})
    (hr₁ : ∀ s, s ≠ 0 → G₁ s ∈ r) (hr₂ : ∀ s, s ≠ 0 → G₂ s ∈ r)
    (hin : ∀ y ∈ W, y ∈ Q → y ∉ discBd Q → y ∈ ρ') (hρr : ρ' ⊆ r)
    (hρ₁ : Disjoint ρ' (range G₁)) (hρ₂ : Disjoint ρ' (range G₂)) {a₁ a₂ : I} (ha₁ : 0 < a₁)
    (ha₂ : 0 < a₂) (ha₁' : a₁ < 1) (ha₂' : a₂ < 1) (hb₁ : ∀ s, s ≤ a₁ → G₁ s ∈ discBd Q)
    (hb₂ : ∀ s, s ≤ a₂ → G₂ s ∈ discBd Q) :
    ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {x} ∧ discBd Δ = range G₁ ∪ range G₂ := by
  obtain ⟨W', hW', hxW', hcap⟩ := exists_cap hS hQ hxQ hW hxW
  obtain ⟨u₁, hu₁, hu₁a, hu₁W⟩ := exists_pos_le hG₁ hW' (h₁0 ▸ hxW') ha₁
  obtain ⟨u₂, hu₂, hu₂a, hu₂W⟩ := exists_pos_le hG₂ hW' (h₂0 ▸ hxW') ha₂
  have hu₁1 : u₁ < 1 := hu₁a.trans_lt ha₁'
  have hu₂1 : u₂ < 1 := hu₂a.trans_lt ha₂'
  let T₁ := G₁ '' Icc 0 u₁
  let T₂ := G₂ '' Icc 0 u₂
  let R₁ := G₁ '' Icc u₁ 1
  let R₂ := G₂ '' Icc u₂ 1
  have lT₁ : IsLineWithEnds T₁ x (G₁ u₁) := h₁0 ▸ isLine_piece hG₁ hi₁ hu₁
  have lT₂ : IsLineWithEnds T₂ x (G₂ u₂) := h₂0 ▸ isLine_piece hG₂ hi₂ hu₂
  have lR₁ : IsLineWithEnds R₁ (G₁ u₁) c := h₁1 ▸ isLine_piece hG₁ hi₁ hu₁1
  have lR₂ : IsLineWithEnds R₂ (G₂ u₂) c := h₂1 ▸ isLine_piece hG₂ hi₂ hu₂1
  have hxT₁ : x ∈ T₁ := ⟨0, ⟨le_rfl, hu₁.le⟩, h₁0⟩
  have hxT₂ : x ∈ T₂ := ⟨0, ⟨le_rfl, hu₂.le⟩, h₂0⟩
  have hcR₁ : c ∈ R₁ := ⟨1, ⟨hu₁1.le, le_rfl⟩, h₁1⟩
  have hcR₂ : c ∈ R₂ := ⟨1, ⟨hu₂1.le, le_rfl⟩, h₂1⟩
  have hxR₁ : x ∉ R₁ := by
    rintro ⟨s, hs, hsx⟩
    have : s = 0 := hi₁ (hsx.trans h₁0.symm)
    exact absurd (this ▸ hs.1) (not_le.mpr hu₁)
  have hxR₂ : x ∉ R₂ := by
    rintro ⟨s, hs, hsx⟩
    have : s = 0 := hi₂ (hsx.trans h₂0.symm)
    exact absurd (this ▸ hs.1) (not_le.mpr hu₂)
  have hcT₁ : c ∉ T₁ := by
    rintro ⟨s, hs, hsx⟩
    have : s = 1 := hi₁ (hsx.trans h₁1.symm)
    exact absurd (this ▸ hs.2) (not_le.mpr hu₁1)
  have hcT₂ : c ∉ T₂ := by
    rintro ⟨s, hs, hsx⟩
    have : s = 1 := hi₂ (hsx.trans h₂1.symm)
    exact absurd (this ▸ hs.2) (not_le.mpr hu₂1)
  have hT₁r : T₁ ⊆ range G₁ := image_subset_range _ _
  have hT₂r : T₂ ⊆ range G₂ := image_subset_range _ _
  have hR₁r : R₁ ⊆ range G₁ := image_subset_range _ _
  have hR₂r : R₂ ⊆ range G₂ := image_subset_range _ _
  have hTT : T₁ ∩ T₂ = {x} := by
    apply subset_antisymm
    · rintro y ⟨h₁, h₂⟩
      rcases hmeet ⟨hT₁r h₁, hT₂r h₂⟩ with h | h
      · exact h
      · exact (hcT₁ (h ▸ h₁)).elim
    · rintro y rfl
      exact ⟨hxT₁, hxT₂⟩
  have hRR : R₁ ∩ R₂ = {c} := by
    apply subset_antisymm
    · rintro y ⟨h₁, h₂⟩
      rcases hmeet ⟨hR₁r h₁, hR₂r h₂⟩ with h | h
      · exact (hxR₁ (h ▸ h₁)).elim
      · exact h
    · rintro y rfl
      exact ⟨hcR₁, hcR₂⟩
  have hT : IsLineWithEnds (T₁ ∪ T₂) (G₁ u₁) (G₂ u₂) := IsLineWithEnds.union lT₁ lT₂ hTT
  have hL : IsLineWithEnds (R₁ ∪ R₂) (G₁ u₁) (G₂ u₂) :=
    IsLineWithEnds.union (GraphMinor.GM11.IsLineWithEnds.symm lR₁)
      (GraphMinor.GM11.IsLineWithEnds.symm lR₂) hRR
  have hy₁T : G₁ u₁ ∈ T₁ := ⟨u₁, ⟨hu₁.le, le_rfl⟩, rfl⟩
  have hy₂T : G₂ u₂ ∈ T₂ := ⟨u₂, ⟨hu₂.le, le_rfl⟩, rfl⟩
  have hy₁R : G₁ u₁ ∈ R₁ := ⟨u₁, ⟨le_rfl, hu₁1.le⟩, rfl⟩
  have hy₂R : G₂ u₂ ∈ R₂ := ⟨u₂, ⟨le_rfl, hu₂1.le⟩, rfl⟩
  have hxy₁ : x ≠ G₁ u₁ := fun h => hxR₁ (h ▸ hy₁R)
  have hxy₂ : x ≠ G₂ u₂ := fun h => hxR₂ (h ▸ hy₂R)
  have hy : G₁ u₁ ≠ G₂ u₂ := by
    intro h
    rcases hmeet ⟨⟨u₁, rfl⟩, h ▸ ⟨u₂, rfl⟩⟩ with h' | h'
    · exact hxy₁ h'.symm
    · exact hcT₁ (h' ▸ hy₁T)
  have hTL : (T₁ ∪ T₂) ∩ (R₁ ∪ R₂) ⊆ {G₁ u₁, G₂ u₂} := by
    rintro y ⟨h₁ | h₁, h₂ | h₂⟩
    · obtain ⟨s, hs, rfl⟩ := h₁
      obtain ⟨s', hs', hss⟩ := h₂
      have : s' = s := hi₁ hss
      have e : s = u₁ := le_antisymm hs.2 (this ▸ hs'.1)
      exact Or.inl (by rw [e])
    · rcases hmeet ⟨hT₁r h₁, hR₂r h₂⟩ with h | h
      · exact (hxR₂ (h ▸ h₂)).elim
      · exact (hcT₁ (h ▸ h₁)).elim
    · rcases hmeet ⟨hR₁r h₂, hT₂r h₁⟩ with h | h
      · exact (hxR₁ (h ▸ h₂)).elim
      · exact (hcT₂ (h ▸ h₁)).elim
    · obtain ⟨s, hs, rfl⟩ := h₁
      obtain ⟨s', hs', hss⟩ := h₂
      have : s' = s := hi₂ hss
      have e : s = u₂ := le_antisymm hs.2 (this ▸ hs'.1)
      exact Or.inr (by rw [e]; rfl)
  have hTb : T₁ ∪ T₂ ⊆ discBd Q := by
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact hb₁ s (hs.2.trans hu₁a)
    · exact hb₂ s (hs.2.trans hu₂a)
  have hTW : T₁ ∪ T₂ ⊆ W' := by
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact hu₁W s hs.2
    · exact hu₂W s hs.2
  obtain ⟨C, Q₁, hC, hCW, hCQ, hCd, hQ₁, hQ₁W, hQ₁Q, hbQ₁, hQ₁b⟩ :=
    hcap _ _ (T₁ ∪ T₂) hy hT hTb hTW (Or.inl hxT₁) hxy₁ hxy₂
  have hCρ : C \ {G₁ u₁, G₂ u₂} ⊆ ρ' := fun y hy' =>
    hin y (hCW hy'.1) (hCQ hy'.1) (disjoint_left.mp hCd hy')
  have hQρ : ∀ y ∈ Q₁, y ∉ T₁ ∪ T₂ → y ∈ ρ' := fun y hy' hn =>
    hin y (hQ₁W hy') (hQ₁Q hy') fun hyb => hn (hQ₁b ⟨hy', hyb⟩)
  have hρU : ∀ y ∈ ρ', y ∉ range G₁ ∧ y ∉ range G₂ := fun y hy' =>
    ⟨disjoint_left.mp hρ₁ hy', disjoint_left.mp hρ₂ hy'⟩
  have hLU : ∀ y ∈ R₁ ∪ R₂, y ∉ ρ' := by
    rintro y (h | h) hy'
    · exact (hρU y hy').1 (hR₁r h)
    · exact (hρU y hy').2 (hR₂r h)
  have hLC : (R₁ ∪ R₂) ∩ C ⊆ {G₁ u₁, G₂ u₂} := by
    rintro y ⟨h₁, h₂⟩
    by_contra hn
    exact hLU y h₁ (hCρ ⟨h₂, hn⟩)
  have hJ : IsOArc ((R₁ ∪ R₂) ∪ C) := isOArc_union hL hC hLC
  have hend : G₁ u₁ ∈ C ∧ G₂ u₂ ∈ C := by
    obtain ⟨g, h0, h1⟩ := hC
    exact ⟨h0 ▸ (g 0).2, h1 ▸ (g 1).2⟩
  have hu₁r : G₁ u₁ ∈ r := hr₁ _ hu₁.ne'
  have hu₂r : G₂ u₂ ∈ r := hr₂ _ hu₂.ne'
  have hJr : (R₁ ∪ R₂) ∪ C ⊆ r := by
    rintro y ((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | h)
    · exact hr₁ s fun h => (hu₁.trans_le (h ▸ hs.1)).ne rfl
    · exact hr₂ s fun h => (hu₂.trans_le (h ▸ hs.1)).ne rfl
    · by_cases hye : y ∈ ({G₁ u₁, G₂ u₂} : Set S)
      · rcases hye with rfl | rfl
        · exact hu₁r
        · exact hu₂r
      · exact hρr (hCρ ⟨h, hye⟩)
  obtain ⟨Δ', hΔ'r, hΔ', hbΔ'⟩ := exists_disc_in_openDisc hr hJ hJr
  have hCb' : C ⊆ discBd Δ' := hbΔ' ▸ subset_union_right
  have hCbQ : C ⊆ discBd Q₁ := hbQ₁ ▸ subset_union_right
  have hxC : x ∉ C := fun h => by
    have hn : x ∉ ({G₁ u₁, G₂ u₂} : Set S) := fun h' => h'.elim hxy₁ hxy₂
    exact (hρU x (hCρ ⟨h, hn⟩)).1 ⟨0, h₁0⟩
  have hxQ₁ : x ∈ Q₁ := discBd_subset _ (hbQ₁ ▸ Or.inl (Or.inl hxT₁))
  have hYfr : Disjoint (Q₁ \ C) (frontier Δ') := by
    rw [IsClosedDisc.frontier_eq_discBd hS hΔ', hbΔ']
    refine disjoint_left.mpr ?_
    rintro y ⟨hy', hnC⟩ (hyL | hyC)
    · by_cases hyT : y ∈ T₁ ∪ T₂
      · exact (hTL ⟨hyT, hyL⟩).elim (fun e => hnC (e ▸ hend.1)) fun e => hnC (e ▸ hend.2)
      · exact hLU y hyL (hQρ y hy' hyT)
    · exact hnC hyC
  have hinter := corner_discs_inter hS hQ₁ hΔ' hCb' hCbQ hYfr hxQ₁ hxC
    (fun hxΔ => hxr (hΔ'r hxΔ))
  obtain ⟨hU, hUb⟩ := disc_union Δ' Q₁ C _ _ hΔ' hQ₁ hC hinter hCb' hCbQ
  have hcovG₁ : range G₁ = T₁ ∪ R₁ := range_eq_image_halves G₁ u₁
  have hcovG₂ : range G₂ = T₂ ∪ R₂ := range_eq_image_halves G₂ u₂
  have hnotρ : ∀ y, y ∈ range G₁ ∪ range G₂ → y ∉ ρ' := by
    rintro y (h | h) hy'
    · exact (hρU y hy').1 h
    · exact (hρU y hy').2 h
  refine ⟨Δ' ∪ Q₁, hU, ?_, ?_⟩
  · rintro y (h | h)
    · exact Or.inl (hΔ'r h)
    · by_cases hyT : y ∈ T₁ ∪ T₂
      · rcases hyT with ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩
        · by_cases hs : s = 0
          · exact Or.inr (by rw [hs, h₁0]; rfl)
          · exact Or.inl (hr₁ s hs)
        · by_cases hs : s = 0
          · exact Or.inr (by rw [hs, h₂0]; rfl)
          · exact Or.inl (hr₂ s hs)
      · exact Or.inl (hρr (hQρ y h hyT))
  · rw [hUb, hbΔ', hbQ₁]
    apply subset_antisymm
    · rintro y ⟨h, hn⟩
      have hyC : y ∈ C → y ∈ T₁ ∪ T₂ := fun hc' => by
        by_contra hyT
        exact hn ⟨hc', fun he => hyT (he.elim (fun e => e ▸ Or.inl hy₁T)
          fun e => e ▸ Or.inr hy₂T)⟩
      have hyU : y ∈ (T₁ ∪ T₂) ∪ (R₁ ∪ R₂) := by
        rcases h with (h | h) | (h | h)
        · exact Or.inr h
        · exact Or.inl (hyC h)
        · exact Or.inl h
        · exact Or.inl (hyC h)
      rcases hyU with (h | h) | (h | h)
      · exact Or.inl (hT₁r h)
      · exact Or.inr (hT₂r h)
      · exact Or.inl (hR₁r h)
      · exact Or.inr (hR₂r h)
    · intro y hy'
      refine ⟨?_, fun h => hnotρ y hy' (hCρ h)⟩
      rcases hy' with h | h
      · rw [hcovG₁] at h
        rcases h with h | h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inl (Or.inl (Or.inl h))
      · rw [hcovG₂] at h
        rcases h with h | h
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inl (Or.inl (Or.inr h))

variable [T2Space S] [ConnectedSpace S] (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
  (hS : IsClosedSurface S)

include hrad hS

omit [T2Space S] [ConnectedSpace S] in
/-- Two edges of `Γ'` with the same ends do not bound a closed disc in `r ∪ {x}`: this is condition
(iv), with `bd(Δ)` in place of the frontier. -/
theorem no_bigon {e f : Set S} (he : e ∈ Γ'.E) (hf : f ∈ Γ'.E) (hef : e ≠ f) {x c : S}
    (hx : x ∈ Γ.V) {r : Set S} (hr : r ∈ Γ.R) (hc : c ∈ r) (hcV : c ∈ Γ'.V)
    (hce : closure e ∩ Γ'.V = {x, c}) (hcf : closure f ∩ Γ'.V = {x, c}) {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hsub : Δ ⊆ r ∪ {x}) (hb : discBd Δ = closure e ∪ closure f) : False := by
  refine hrad.2.2.2.2.2.2 e he f hf hef x hx r hr c ⟨hc, hcV⟩ hce hcf ⟨Δ, hΔ, hsub, ?_⟩
  rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hΔ, hb]

omit [ConnectedSpace S] in
/-- The interior of the disc between a chord and a parallel edge of `Γ'` misses `H`. -/
theorem parallel_interior {r K Δ h : Set S} (hr : r ∈ Γ.R) {c x : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V)
    (hx : x ∈ Γ.V) (hh : h ∈ Γ'.E) (hcap : closure h ∩ Γ'.V = {x, c})
    (hKU : Disjoint (K \ {c, x}) Γ'.U) (hΔ : IsClosedDisc Δ) (hsub : Δ ⊆ r ∪ {x})
    (hb : discBd Δ = closure h ∪ K) : Disjoint (Δ \ discBd Δ) (radialUnion hrad).U := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hxc : x ≠ c := fun h' => region_subset hr (h' ▸ hc) (Γ.V_subset_U hx)
  have hxb : x ∈ discBd Δ := by
    rw [hb]
    have : x ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
    exact Or.inl this.1
  have hcb : c ∈ discBd Δ := by
    rw [hb]
    have : c ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
    exact Or.inl this.1
  have hV : ∀ y ∈ Δ, y ∈ Γ'.V → y = x ∨ y = c := by
    intro y hy hyV
    rcases hsub hy with h' | h'
    · exact Or.inr (hub_unique hrad hr hc hcV h' hyV)
    · exact Or.inl h'
  refine disjoint_left.mpr ?_
  rintro y ⟨hyΔ, hyb⟩ (hyU | hyU)
  · rcases hsub hyΔ with h' | h'
    · exact region_subset hr h' hyU
    · exact hyb (h'.symm ▸ hxb)
  by_cases hyV : y ∈ Γ'.V
  · rcases hV y hyΔ hyV with rfl | rfl
    · exact hyb hxb
    · exact hyb hcb
  rw [Γ'.U_eq] at hyU
  rcases hyU with h' | hyE
  · exact hyV h'
  obtain ⟨g, hg, hyg'⟩ := mem_iUnion₂.mp hyE
  have hyg : y ∈ g := (Γ'.closure_diff_V hg).subset ⟨hyg', hyV⟩
  have hgh : g ≠ h := by
    rintro rfl
    exact hyb (hb ▸ Or.inl hyg')
  -- The edge `g` misses the boundary of `Δ`, so it lies inside `Δ`.
  have hgb : Disjoint g (discBd Δ) := by
    refine disjoint_left.mpr fun z hz hzb => ?_
    have hzV : z ∉ Γ'.V := edge_notMem_V hg hz
    rw [hb] at hzb
    rcases hzb with hzh | hzK
    · exact hgh (Γ'.edge_eq_of_mem hg hh hz ((Γ'.closure_diff_V hh).subset ⟨hzh, hzV⟩))
    · have hmem : z ∈ K \ {c, x} := ⟨hzK, fun h' => hzV (h'.elim (fun e => e ▸ hcV)
        fun e => e ▸ radial_V hrad hx)⟩
      exact disjoint_left.mp hKU hmem (Γ'.closure_subset_U hg (subset_closure hz))
  have hgconn : IsPreconnected g := hg.2.2.1.isConnected.isPreconnected
  rw [← IsClosedDisc.frontier_eq_discBd hS hΔ] at hgb
  have hgΔ : g ⊆ Δ := by
    rcases subset_or_disjoint_of_frontier hΔ.isClosed hgconn hgb with h' | h'
    · exact h'
    · exact (disjoint_left.mp h' hyg hyΔ).elim
  have hclΔ : closure g ⊆ Δ := closure_minimal hgΔ hΔ.isClosed
  obtain ⟨v, hv, r', hr', w, hwr, hwV, hcg, hgr⟩ := spoke_ends hrad hS hg
  have hvcl : v ∈ closure g ∩ Γ'.V := by rw [hcg]; simp
  have hwcl : w ∈ closure g ∩ Γ'.V := by rw [hcg]; simp
  have hvx : v = x := by
    rcases hV v (hclΔ hvcl.1) hvcl.2 with h' | h'
    · exact h'
    · exact (notMem_V_of_mem_region hr hc (h' ▸ hv)).elim
  have hwc : w = c := by
    rcases hV w (hclΔ hwcl.1) hwcl.2 with h' | h'
    · exact (notMem_V_of_mem_region hr' hwr (h' ▸ hx)).elim
    · exact h'
  subst hvx hwc
  have hJ := isOArc_spokes hg hh hgh hxc hcg hcap
  have hJsub : closure g ∪ closure h ⊆ Δ :=
    union_subset hclΔ (subset_union_left.trans (hb ▸ discBd_subset Δ))
  obtain ⟨Δ₂, ⟨hsubΔ, hd, hb₂, -⟩, -⟩ := disc_oArc Δ _ hΔ hJsub hJ
  exact no_bigon hrad hS hg hh hgh hx hr hc hcV hcg hcap hd (hsubΔ.trans hsub) hb₂

/-- A half-edge of `H` at the vertex of a region. -/
theorem exists_half_at_hub (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ')
  (hE : Γ.E.Nonempty) {γ : Set S → I → S}
    (hγ : EdgePar (radialUnion hrad) γ) {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r)
    (hcV : c ∈ Γ'.V) : (halfEdges (radialUnion hrad) γ c).Nonempty := by
  obtain ⟨x, hx, hxr⟩ := exists_vertex_at_region hS hE hr
  obtain ⟨h, hh, hcap⟩ := exists_spoke_at hrad hmax hS hE hr hc hcV hx hxr
  have hhH : h ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr hh
  have hcl : c ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
  obtain ⟨b, hb⟩ := exists_end_eq hγ hhH (by rw [radialUnion_V]; exact hcV) hcl.1
  exact ⟨(h, b), hhH, hb⟩

/-- **No corner at a vertex of `Γ` lies between two edges of `Γ`.** Take a chord from the vertex of
the region into the corner. By maximality it has a parallel edge of `Γ'`, and the disc between them
shows that this edge is one of the two sides of the corner. -/
theorem corner_has_spoke (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ')
  (hE : Γ.E.Nonempty) {γ : Set S → I → S}
    (hγ : EdgePar (radialUnion hrad) γ) {x : S} (hx : x ∈ Γ.V)
    {next : halfEdges (radialUnion hrad) γ x → halfEdges (radialUnion hrad) γ x}
    {ρ P Q : halfEdges (radialUnion hrad) γ x → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ x → I}
    (hsec : IsSectors (radialUnion hrad) γ x next ρ P W Q τ) (k : halfEdges
      (radialUnion hrad) γ x) :
    k.1.1 ∈ Γ'.E ∨ (next k).1.1 ∈ Γ'.E := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpR : ρ k ∈ (radialUnion hrad).R := IsCorners.region (IsSectors.corners hsec) k
  obtain ⟨r, hr, hpr⟩ := exists_region_of_sub hrad hpR
  have hxH : x ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact radial_V hrad hx
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  have hcH : c ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hcV
  have hxU : x ∉ r := fun h => region_subset hr h (Γ.V_subset_U hx)
  have hcx : c ≠ x := fun h => hxU (h ▸ hc)
  have hcp := hub_mem_closure hrad hS hr hpR hpr hc hcV
  obtain ⟨g₁, hg₁, -, h₁0, h₁⟩ := exists_path_into_disc (IsSectors.disc hsec k)
    (IsSectors.bd hsec k)
    (IsSectors.isOpen hsec) (IsSectors.mem hsec)
  have hg₁p : ∀ t, 0 < t → g₁ t ∈ ρ k := fun t ht => by
    obtain ⟨a, b, d⟩ := h₁ t ht
    exact IsSectors.sub hsec k (IsSectors.inside hsec k ⟨⟨a, b⟩, d⟩)
  obtain ⟨g₂, hg₂, h₂0, h₂⟩ := exists_access hS _ hγ hcH (exists_half_at_hub hrad hS hmax hE hγ hr
    hc hcV)
    hpR hcp
  obtain ⟨y₀, hy₀⟩ := region_nonempty hpR
  have hppath : IsPathConnected (ρ k) :=
    isPathConnected_of_isOpen hS (region_isOpen hpR) (region_isPreconnected hpR) ⟨y₀, hy₀⟩
  obtain ⟨u, hu, hui, hu0, hu1, hup, O, hO, hxO, hOr⟩ :=
    exists_chord hppath hcx.symm (fun h => hxU (hpr h)) hg₁ hg₂ h₁0 h₂0 hg₁p h₂
  have hline : IsLineWithEnds (range u) c x := by
    have := isLine_range hu hui
    rw [hu0, hu1] at this
    exact GraphMinor.GM11.IsLineWithEnds.symm this
  have hsubp : range u \ {c, x} ⊆ ρ k := by
    rintro _ ⟨⟨t, rfl⟩, hn⟩
    exact hup t (fun h => hn (Or.inr (by rw [h, hu0]; rfl))) fun h => hn (Or.inl (by rw [h, hu1]))
  have hKU : Disjoint (range u \ {c, x}) Γ'.U :=
    disjoint_left.mpr fun z hz hzU => region_subset hpR (hsubp hz) (Or.inr hzU)
  obtain ⟨h, hh, hcap, Δ, hΔ, hΔr, hb'⟩ :=
    parallel_of_line hrad hmax hS hr hc hcV hx hline hcx (hsubp.trans hpr) hKU
  have hb : discBd Δ = closure h ∪ range u := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ, ← subBd_eq_frontier, hb']
  have hfree := parallel_interior hrad hS hr hc hcV hx hh hcap hKU hΔ hΔr hb
  have hhH : h ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr hh
  have hxh : x ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
  obtain ⟨b, hbx⟩ := exists_end_eq hγ hhH hxH hxh.1
  let i : halfEdges (radialUnion hrad) γ x := ⟨(h, b), hhH, hbx⟩
  by_cases hik : i = k
  · exact Or.inl (hik ▸ hh)
  by_cases hin : i = next k
  · exact Or.inr (hin ▸ hh)
  exfalso
  have hxb : x ∈ discBd Δ := hb ▸ Or.inl hxh.1
  have hWO : IsOpen (W ∩ O) := (IsSectors.isOpen hsec).inter hO
  obtain ⟨A, W₀, hW₀, hxW₀, hAc, hAΔ, hAb, hAX, hsubA, hclA⟩ :=
    exists_half_nbhd hΔ hWO.isClosed_compl hxb
      (fun h' => h' ⟨IsSectors.mem hsec, hxO⟩)
  have hAW : ∀ y ∈ A, y ∈ W ∩ O := fun y hy => by
    by_contra hn
    exact disjoint_left.mp hAX hy hn
  have hAU : ∀ y ∈ A, y ∉ (radialUnion hrad).U := fun y hy hyU =>
    disjoint_left.mp hfree ⟨hAΔ hy, disjoint_left.mp hAb hy⟩ hyU
  have hQd := IsSectors.disc hsec k
  have hAfr : Disjoint A (frontier (Q k)) := by
    rw [IsClosedDisc.frontier_eq_discBd hS hQd]
    exact disjoint_left.mpr fun y hy hyb =>
      hAU y hy (IsSectors.bdU hsec k ⟨(hAW y hy).1, hyb⟩)
  obtain ⟨t, ht, hutW⟩ := exists_pos_mem hu (hW₀.inter hO) (by rw [hu0]; exact ⟨hxW₀, hxO⟩)
  obtain ⟨s, hs⟩ := hOr t hutW.2
  have hs0 : 0 < s := by
    refine unitInterval.pos_iff_ne_zero.mpr ?_
    rintro rfl
    exact ht.ne' (hui (hs.symm.trans (h₁0.trans hu0.symm)))
  have hzcl : u t ∈ closure A := hclA ⟨hutW.1, hb ▸ Or.inr ⟨t, rfl⟩⟩
  obtain ⟨-, hzQ, hzb⟩ := h₁ s hs0
  rw [hs] at hzQ hzb
  have hzint : u t ∈ interior (Q k) := by
    have hnf : u t ∉ frontier (Q k) := by
      rwa [IsClosedDisc.frontier_eq_discBd hS hQd]
    by_contra hni
    exact hnf ⟨subset_closure hzQ, hni⟩
  have hAQ : A ⊆ Q k := by
    rcases subset_or_disjoint_of_frontier hQd.isClosed hAc hAfr with h' | h'
    · exact h'
    · obtain ⟨y, hyI, hyA⟩ := mem_closure_iff.mp hzcl _ isOpen_interior hzint
      exact (disjoint_left.mp h' hyA (interior_subset hyI)).elim
  have hclQ : closure A ⊆ Q k := closure_minimal hAQ hQd.isClosed
  obtain ⟨s', hs', hsW⟩ := exists_pos_mem (continuous_spoke hγ i.2.1)
    (hW₀.inter (IsSectors.isOpen hsec)) (by
      have e₀ : spoke γ i.1 0 = x := by
        rw [spoke_zero]
        exact hbx
      rw [e₀]
      exact ⟨hxW₀, IsSectors.mem hsec⟩)
  have hmem : spoke γ i.1 s' ∈ closure h := subset_closure (spoke_mem_edge hγ i.2.1 hs')
  exact IsSectors.off hsec k i hik hin s' hs' hsW.2
    (hclQ (hclA ⟨hsW.1, hb ▸ Or.inl hmem⟩))

omit [T2Space S] [ConnectedSpace S] in
/-- Facts on an edge `f` of `Γ'` with `f` in the closure of a region of `H` inside `r`. -/
theorem spoke_facts {f p r : Set S} (hf : f ∈ Γ'.E) (hr : r ∈ Γ.R) (hpr : p ⊆ r)
  (hfp : f ⊆ closure p) {c x : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) (hx : x ∈ Γ.V)
    (hxf : x ∈ closure f) :
    closure f ∩ Γ'.V = {x, c} ∧ f ⊆ r ∧ ∀ y ∈ closure f, y ≠ x → y ∈ r := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨v, hv, r', hr', w, hwr, hwV, hcap, hsubr⟩ := spoke_ends hrad hS hf
  obtain ⟨q, hq⟩ := hf.1
  obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp (hfp hq) r' (region_isOpen hr') (hsubr hq)
  obtain rfl : r' = r := region_eq_of_mem hr' hr hz' (hpr hz)
  obtain rfl : w = c := hub_unique hrad hr hc hcV hwr hwV
  have hxm : x ∈ ({v, w} : Set S) := hcap ▸ ⟨hxf, radial_V hrad hx⟩
  have hxv : x = v := by
    rcases hxm with h | h
    · exact h
    · exact (notMem_V_of_mem_region hr hwr (h ▸ hx)).elim
  subst hxv
  refine ⟨hcap, hsubr, fun y hy hyx => ?_⟩
  by_cases hyV : y ∈ Γ'.V
  · have : y ∈ ({x, w} : Set S) := hcap ▸ ⟨hy, hyV⟩
    rcases this with h | h
    · exact (hyx h).elim
    · exact h ▸ hwr
  · exact hsubr ((Γ'.closure_diff_V hf).subset ⟨hy, hyV⟩)

omit [T2Space S] [ConnectedSpace S] hS hrad in
/-- The map `next` of a rotation is onto. -/
theorem next_surjective {H : Drawing S} {γ : Set S → I → S} {x : S}
    {next : halfEdges H γ x → halfEdges H γ x} {ρ : halfEdges H γ x → Set S}
    (hc : IsCorners H γ x next ρ) : Function.Surjective next := by
  have : Finite (halfEdges H γ x) := (finite_halfEdges H γ x).to_subtype
  exact Finite.surjective_of_injective (IsCorners.inj hc)

end GraphMinor.GM11
