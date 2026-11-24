/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Arcs in a closed disc

* `disc_oArc : DiscOArcStatement`: an `O`-arc in a closed disc bounds a unique closed disc there.
* `disc_iArc : DiscIArcStatement`: a proper `I`-arc divides a closed disc into two closed discs.

The route is the one of the module docstring of `Surface/PlaneDisc.lean`. A closed disc `D` is
carried to the closed unit disc of `ℂ` by a chart (`IsChart`). There the closed disc inside an
`O`-arc is its closed domain, and the sides of a cross-cut are given by the theta lemma
`IsCut.closedInner_facts`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Coordinates on a closed disc, as a pair of maps. -/
structure IsChart (D : Set S) (h : S → ℂ) (g : ℂ → S) : Prop where
  hc : ContinuousOn h D
  gc : ContinuousOn g (closedBall 0 1)
  hm : MapsTo h D (closedBall 0 1)
  gm : MapsTo g (closedBall 0 1) D
  gh : LeftInvOn g h D
  hg : LeftInvOn h g (closedBall 0 1)
  bd : h '' discBd D = sphere 0 1

theorem IsClosedDisc.exists_isChart {D : Set S} (hD : IsClosedDisc D) :
    ∃ h g, IsChart D h g := by
  obtain ⟨h, g, h1, h2, h3, h4, h5, h6, h7⟩ := hD.exists_chart
  exact ⟨h, g, h1, h2, h3, h4, h5, h6, h7⟩

theorem discBd_subset (D : Set S) : discBd D ⊆ D := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

namespace IsChart

variable {D : Set S} {h : S → ℂ} {g : ℂ → S}

theorem image_subset (c : IsChart D h g) {X : Set S} (hX : X ⊆ D) : h '' X ⊆ closedBall 0 1 :=
  image_subset_iff.mpr fun _ hx => c.hm (hX hx)

theorem g_subset (c : IsChart D h g) {Z : Set ℂ} (hZ : Z ⊆ closedBall 0 1) : g '' Z ⊆ D :=
  image_subset_iff.mpr fun _ hx => c.gm (hZ hx)

theorem g_h (c : IsChart D h g) {X : Set S} (hX : X ⊆ D) : g '' (h '' X) = X :=
  (c.gh.mono hX).image_image

theorem h_g (c : IsChart D h g) {Z : Set ℂ} (hZ : Z ⊆ closedBall 0 1) : h '' (g '' Z) = Z :=
  (c.hg.mono hZ).image_image

theorem g_closedBall (c : IsChart D h g) : g '' closedBall 0 1 = D := by
  refine Subset.antisymm (c.g_subset Subset.rfl) fun x hx => ?_
  exact ⟨h x, c.hm hx, c.gh hx⟩

theorem g_sphere (c : IsChart D h g) : g '' sphere 0 1 = discBd D := by
  rw [← c.bd, c.g_h (discBd_subset D)]

theorem injOn (c : IsChart D h g) : InjOn g (closedBall 0 1) := c.hg.injOn

theorem g_inter (c : IsChart D h g) {Z W : Set ℂ} (hZ : Z ⊆ closedBall 0 1)
    (hW : W ⊆ closedBall 0 1) : g '' (Z ∩ W) = g '' Z ∩ g '' W := by
  refine Subset.antisymm (image_inter_subset _ _ _) ?_
  rintro _ ⟨⟨x, hx, rfl⟩, y, hy, he⟩
  obtain rfl := c.injOn (hW hy) (hZ hx) he
  exact ⟨y, ⟨hx, hy⟩, rfl⟩

theorem g_sdiff (c : IsChart D h g) {Z W : Set ℂ} (hZ : Z ⊆ closedBall 0 1)
    (hW : W ⊆ closedBall 0 1) : g '' (Z \ W) = g '' Z \ g '' W := by
  ext x
  constructor
  · rintro ⟨z, ⟨hz, hzW⟩, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, he⟩
    obtain rfl := c.injOn (hW hw) (hZ hz) he
    exact hzW hw
  · rintro ⟨⟨z, hz, rfl⟩, hn⟩
    exact ⟨z, ⟨hz, fun h' => hn ⟨z, h', rfl⟩⟩, rfl⟩

theorem disc_g (c : IsChart D h g) {Z : Set ℂ} (hZ : Z ⊆ closedBall 0 1) (hd : IsClosedDisc Z) :
    IsClosedDisc (g '' Z) ∧ discBd (g '' Z) = g '' discBd Z :=
  hd.image (c.gc.mono hZ) (c.hc.mono (c.g_subset hZ)) (c.hg.mono hZ)

theorem disc_h (c : IsChart D h g) {X : Set S} (hX : X ⊆ D) (hd : IsClosedDisc X) :
    IsClosedDisc (h '' X) ∧ discBd (h '' X) = h '' discBd X :=
  hd.image (c.hc.mono hX) (c.gc.mono (c.image_subset hX)) (c.gh.mono hX)

theorem oArc_h (c : IsChart D h g) {X : Set S} (hX : X ⊆ D) (hd : IsOArc X) :
    Nonempty (Circle ≃ₜ h '' X) :=
  hd.image (c.hc.mono hX) (c.gc.mono (c.image_subset hX)) (c.gh.mono hX)

theorem components_g (c : IsChart D h g) {Z : Set ℂ} (hZ : Z ⊆ closedBall 0 1) :
    componentsIn (g '' Z) = (fun C => g '' C) '' componentsIn Z :=
  componentsIn_image (c.gc.mono hZ) (c.hc.mono (c.g_subset hZ)) (c.hg.mono hZ)

end IsChart

/-- **An `O`-arc in a closed disc bounds a unique closed disc there.** The closed disc is the closed
domain of the arc in a chart. -/
theorem disc_oArc : DiscOArcStatement.{u} := by
  intro S _ D F hD hFD hF
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hGsub : h '' F ⊆ closedBall 0 1 := c.image_subset hFD
  have hG := c.oArc_h hFD hF
  have hFg : g '' (h '' F) = F := c.g_h hFD
  have hin := closedInner_subset_closedBall hG hGsub
  obtain ⟨d1, d2⟩ := isClosedDisc_closedInner hG
  obtain ⟨d3, d4⟩ := c.disc_g hin d1
  rw [d2, hFg] at d4
  have e1 : g '' closedInner (h '' F) \ F = g '' inner (h '' F) := by
    rw [← closedInner_sdiff hG, c.g_sdiff hin hGsub, hFg]
  have e2 : D \ F = g '' (closedBall 0 1 \ h '' F) := by
    rw [c.g_sdiff Subset.rfl hGsub, c.g_closedBall, hFg]
  obtain ⟨k1, k2, k3⟩ := components_closedBall_sdiff hG hGsub
  have hinner : inner (h '' F) ⊆ closedBall 0 1 := subset_union_left.trans hin
  refine ⟨g '' closedInner (h '' F), ⟨c.g_subset hin, d3, d4, ?_, ?_, ?_⟩, ?_⟩
  · rw [e1, e2, c.components_g sdiff_subset]
    exact mem_image_of_mem _ k1
  · rw [e1, ← c.g_sphere, Set.disjoint_iff_inter_eq_empty,
      ← c.g_inter hinner sphere_subset_closedBall, k2.inter_eq, image_empty]
  · intro C hC hd
    rw [e2, c.components_g sdiff_subset] at hC
    obtain ⟨C', hC', rfl⟩ := hC
    rw [e1]
    have hdis : Disjoint C' (sphere 0 1) := by
      rw [← c.g_sphere] at hd
      exact Set.disjoint_left.mpr fun z h1 h2 =>
        Set.disjoint_left.mp hd ⟨z, h1, rfl⟩ ⟨z, h2, rfl⟩
    simp only
    rw [k3 C' hC' hdis]
  · intro Δ' h1 h2 h3
    obtain ⟨a, b⟩ := c.disc_h h1 h2
    rw [h3] at b
    rw [← c.g_h h1, eq_closedInner_of_discBd hG a b]

/-- **A proper `I`-arc divides a closed disc into two closed discs.** In a chart the arc is a
cross-cut of the unit circle, and the two discs are the closed domains of the two sides. -/
theorem disc_iArc : DiscIArcStatement.{u} := by
  intro S _ D F s t hD hFD hst hL hmeet
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨f, hf0, hf1⟩ := hL
  have hinjh : InjOn h D := c.gh.injOn
  have hsF : s ∈ F ∩ discBd D := hmeet ▸ Or.inl rfl
  have htF : t ∈ F ∩ discBd D := hmeet ▸ Or.inr rfl
  let e : 𝕀 → ℂ := fun u => h (f u).1
  have he : IsArcMap e := by
    refine ⟨c.hc.comp_continuous (continuous_subtype_val.comp f.continuous) fun u => hFD (f u).2,
      fun u v huv => f.injective (Subtype.ext (hinjh (hFD (f u).2) (hFD (f v).2) huv))⟩
  have he0 : e 0 = h s := by
    simp only [e, hf0]
  have he1 : e 1 = h t := by
    simp only [e, hf1]
  have hne : e 0 ≠ e 1 := fun heq => zero_ne_one (he.2 heq)
  have hs0 : e 0 ∈ sphere (0 : ℂ) 1 := by
    rw [he0, ← c.bd]
    exact mem_image_of_mem h hsF.2
  have hs1 : e 1 ∈ sphere (0 : ℂ) 1 := by
    rw [he1, ← c.bd]
    exact mem_image_of_mem h htF.2
  have hin : ∀ u : 𝕀, u ≠ 0 → u ≠ 1 → e u ∈ inner (sphere (0 : ℂ) 1) := by
    intro u h0 h1
    rw [inner_sphere, mem_ball_zero_iff]
    refine lt_of_le_of_ne (mem_closedBall_zero_iff.mp (c.hm (hFD (f u).2))) fun hn => ?_
    have hz : e u ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hn
    rw [← c.bd] at hz
    obtain ⟨x, hx, hxe⟩ := hz
    have hxu : x = (f u).1 := hinjh (discBd_subset D hx) (hFD (f u).2) hxe
    have hmem : (f u).1 ∈ F ∩ discBd D := ⟨(f u).2, hxu ▸ hx⟩
    rw [hmeet] at hmem
    rcases hmem with h' | h'
    · exact h0 (f.injective (Subtype.ext (h'.trans hf0.symm)))
    · exact h1 (f.injective (Subtype.ext (h'.trans hf1.symm)))
  obtain ⟨φ₀⟩ := oArc_sphere
  have J₀ := isJordanParts φ₀
  obtain ⟨a, b, cut⟩ := exists_isCut φ₀ he hne hs0 hs1 hin
  have hFe : h '' F = range e := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f.symm ⟨x, hx⟩, by simp [e]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨(f u).1, (f u).2, rfl⟩
  have hFg : g '' range e = F := by
    rw [← hFe]
    exact c.g_h hFD
  have hends : g '' {e 0, e 1} = {s, t} := by
    rw [image_pair, he0, he1, c.gh (hFD hsF.1), c.gh (hFD htF.1)]
  obtain ⟨-, f2, f3, f4, -, -⟩ := cut.closedInner_facts J₀
  obtain ⟨u1, u2, u3, u4, u5⟩ := cut.components J₀
  rw [closedInner_sphere] at f2 f3 u1 u2
  have hA : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  have hrsub : range e ⊆ closedBall 0 1 := by
    rw [← hFe]
    exact c.image_subset hFD
  have hae : range a ⊆ closedBall 0 1 := fun z hz => hA (cut.union ▸ Or.inl hz)
  have hbe : range b ⊆ closedBall 0 1 := fun z hz => hA (cut.union ▸ Or.inr hz)
  have hpair : ({e 0, e 1} : Set ℂ) ⊆ closedBall 0 1 := by
    rintro z (rfl | rfl)
    · exact hA hs0
    · exact hA hs1
  obtain ⟨d1, d2⟩ := isClosedDisc_closedInner cut.oArc_side
  obtain ⟨d3, d4⟩ := isClosedDisc_closedInner cut.symm.oArc_side
  obtain ⟨g1, g2⟩ := c.disc_g f2 d1
  obtain ⟨g3, g4⟩ := c.disc_g f3 d3
  rw [d2] at g2
  rw [d4] at g4
  have hside : ∀ {d : 𝕀 → ℂ}, d 0 = e 0 → d 1 = e 1 →
      side d e = (range d \ {e 0, e 1}) ∪ range e := by
    intro d h0 h1
    ext z
    constructor
    · rintro (hz | hz)
      · by_cases hend : z ∈ ({e 0, e 1} : Set ℂ)
        · rcases hend with rfl | rfl
          · exact Or.inr ⟨0, rfl⟩
          · exact Or.inr ⟨1, rfl⟩
        · exact Or.inl ⟨hz, hend⟩
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inl hz.1
      · exact Or.inr hz
  have hsid₁ := hside cut.a_zero cut.a_one
  have hsid₂ := hside cut.b_zero cut.b_one
  have hinter : closedInner (side a e) ∩ closedInner (side b e) = range e := by
    refine Subset.antisymm f4 fun z hz => ⟨Or.inr (Or.inr hz), Or.inr (Or.inr hz)⟩
  refine ⟨g '' (range a \ {e 0, e 1}), g '' (range b \ {e 0, e 1}), _, _, ?_, ?_, g1, g3, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro hEq
    have := congrArg (fun X => h '' X) hEq
    rw [c.h_g (sdiff_subset.trans hae), c.h_g (sdiff_subset.trans hbe)] at this
    exact u5 this
  · rw [← c.g_sphere, ← hends, ← c.g_sdiff hA hpair, c.components_g (sdiff_subset.trans hA), u4,
      image_pair]
  · rw [← image_union, (cut.closedInner_facts J₀).1, closedInner_sphere, c.g_closedBall]
  · rw [← c.g_inter f2 f3, hinter, hFg]
  · rw [g2, hsid₁, image_union, hFg]
  · rw [g4, hsid₂, image_union, hFg]
  · have e3 : D \ F = g '' (closedBall 0 1 \ range e) := by
      rw [c.g_sdiff Subset.rfl hrsub, c.g_closedBall, hFg]
    rw [e3, c.components_g (sdiff_subset.trans Subset.rfl), u2, image_pair,
      c.g_sdiff f2 hrsub, c.g_sdiff f3 hrsub, hFg]

end GraphMinor.Surface
