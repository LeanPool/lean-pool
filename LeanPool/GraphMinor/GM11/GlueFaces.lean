/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.EdgeChart
public import LeanPool.GraphMinor.Surface.PushOff
import Mathlib.Analysis.Complex.Convex

/-!
# The union of two regions across an edge

`theorem_glue_regions`: let `e` be an edge of a drawing in a closed surface, with different regions
`p`
and `q` on its two sides, and suppose both are open discs. Then `p ∪ e ∪ q` is an open disc.

We let the union grow along `e`. Write `Z(s, t)` for `p ∪ q` with the piece of `e` between the
parameters
`s` and `t`. A chart around a point of `e` shows that `Z(s, t)` is an open disc for a short piece
(`zone_start`), and that a piece can be made longer (`zone_step`). In both steps, `exists_disc_off`
finds
a closed disc around a given `O`-arc. The union of a chain of open discs of this kind is an open
disc,
so the piece reaches the ends of `e`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Metric

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The closed unit disc of `ℂ` is a closed disc with the unit circle as boundary. -/
theorem closedBall_disc :
    IsClosedDisc (closedBall (0 : ℂ) 1) ∧ discBd (closedBall (0 : ℂ) 1) = sphere 0 1 := by
  have h := isClosedDisc_of_convex (convex_closedBall (0 : ℂ) 1)
    (by rw [interior_closedBall _ one_ne_zero]; exact ⟨0, by simp⟩) isBounded_closedBall
      isClosed_closedBall
  rw [frontier_closedBall _ one_ne_zero] at h
  exact h

/-- A closed disc grown by a closed disc. -/
theorem exists_absorb (hS : IsClosedSurface S) {A N C : Set S} (hA : IsOpenDisc A)
    (hN : IsClosedDisc N) {ℓ : I → S} (hℓ : Continuous ℓ) (h0 : ℓ 0 ∉ A) (h1 : ℓ 1 ∉ A)
    (hinj : InjOn ℓ (Ioo 0 1)) (hbd : discBd N ∩ A = ℓ '' Ioo 0 1)
    (hT : IsPreconnected (discInt N ∩ A)) (hTne : (discInt N ∩ A).Nonempty)
    (hC : IsCompact C) (hCA : C ⊆ A) (hCT : Disjoint C (discInt N)) (hCne : C.Nonempty) :
    ∃ ρ : Set S, IsClosedDisc (N ∪ ρ) ∧ ρ ⊆ A ∧ C ⊆ ρ ∧ discInt (N ∪ ρ) ⊆ ρ ∪ discInt N ∧
      ∀ x, x ∉ ρ → x ∈ discBd N → x ∈ discBd (N ∪ ρ) := by
  have hT2 : T2Space S := hS.2.1
  obtain ⟨ρ, L, s, t, hρ, hρA, hCρ, hL, hline, hLρ, hLN⟩ :=
    exists_disc_off hS hA hN hℓ h0 h1 hinj hbd hT hTne hC hCA hCT hCne
  have hLr : L ⊆ ρ := hL ▸ inter_subset_left
  obtain ⟨hW, hbW⟩ := disc_union N ρ L s t hN hρ hline (by rw [inter_comm]; exact hL) hLN hLρ
  have hkey : ∀ x, x ∉ ρ → x ∈ discBd N → x ∈ discBd (N ∪ ρ) := fun x hx hb => by
    rw [hbW]
    exact ⟨Or.inl hb, fun h => hx (hLr h.1)⟩
  refine ⟨ρ, hW, hρA, hCρ, ?_, hkey⟩
  rintro x ⟨hx | hx, hb⟩
  · by_cases hxρ : x ∈ ρ
    · exact Or.inl hxρ
    · exact Or.inr ⟨hx, fun h => hb (hkey x hxρ h)⟩
  · exact Or.inl hx

/-- An `O`-arc in a closed disc whose inside lies in `Y` bounds a closed disc in `Y`, if it lies in
`Y`. -/
theorem exists_bound_in {W F Y : Set S} (hW : IsClosedDisc W) (hF : IsOArc F) (hFW : F ⊆ W)
    (hsub : discInt W ⊆ Y) (hFY : F ⊆ Y) : ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
  obtain ⟨Δ, ⟨hΔW, hΔ, hb, -, hdis, -⟩, -⟩ := disc_oArc W F hW hFW hF
  refine ⟨Δ, ?_, hΔ, hb⟩
  intro x hx
  by_cases hxF : x ∈ F
  · exact hFY hxF
  · exact hsub ⟨hΔW hx, disjoint_left.mp hdis ⟨hx, hxF⟩⟩

/-- `open_disc` for a proper subset. -/
theorem isOpenDisc_of_bound (hS : IsClosedSurface S) [ConnectedSpace S] {Y : Set S} (hY : IsOpen Y)
    (hconn : IsConnected Y) (hne : Y ≠ univ)
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F) :
    IsOpenDisc Y := by
  rcases open_disc S Y hS inferInstance hconn hY H with h | h
  · exact absurd h.2 hne
  · exact h

/-- A chart of an edge, as in `exists_edge_chart`. -/
structure IsEdgeChart (H : Drawing S) (γ : I → S) (t₀ : I) (G : ℂ → S) (a b : I) : Prop where
  cont : ContinuousOn G (closedBall 0 1)
  inj : InjOn G (closedBall 0 1)
  left : a < t₀
  right : t₀ < b
  zero : G 0 = γ t₀
  mem_U : ∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0
  ball_eq : G '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} = γ '' Ioo a b
  closed_eq : G '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} = γ '' Icc a b
  ends : (G (-1) = γ a ∧ G 1 = γ b) ∨ (G (-1) = γ b ∧ G 1 = γ a)

namespace IsEdgeChart

variable {H : Drawing S} {γ : I → S} {t₀ a b : I} {G : ℂ → S}

/-- The closed disc of the chart. -/
noncomputable def disc (_ : IsEdgeChart H γ t₀ G a b) : Set S := G '' closedBall 0 1

section

variable [T2Space S] (c : IsEdgeChart H γ t₀ G a b)

include c

theorem isClosedDisc : IsClosedDisc c.disc := (isClosedDisc_image closedBall_disc.1 c.cont c.inj).1

theorem discBd_eq : discBd c.disc = G '' sphere 0 1 := by
  rw [disc, (isClosedDisc_image closedBall_disc.1 c.cont c.inj).2, closedBall_disc.2]

theorem discInt_eq : discInt c.disc = G '' ball 0 1 := by
  rw [discInt, discBd_eq c, disc]
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hn⟩
    refine ⟨z, ?_, rfl⟩
    have : ‖z‖ ≤ 1 := by simpa using hz
    have h' : ‖z‖ ≠ 1 := fun h => hn ⟨z, by simpa using h, rfl⟩
    simpa using lt_of_le_of_ne this h'
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, ball_subset_closedBall hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, he⟩
    have := c.inj (sphere_subset_closedBall hw) (ball_subset_closedBall hz) he
    rw [this] at hw
    have h₁ : ‖z‖ = 1 := by simpa using hw
    have h₂ : ‖z‖ < 1 := by simpa using hz
    linarith

omit [T2Space S] in
/-- The open lower half of the chart. -/
theorem mem_lower_of_mem {A : Set S} (hdis : Disjoint A H.U) {x : S} (hx : x ∈ A) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) (hxz : G z = x) : z.im ≠ 0 := fun h =>
  disjoint_left.mp hdis hx (hxz ▸ (c.mem_U z hz).mpr h)

end

/-- The lower half of the closed unit disc. -/
def lower : Set ℂ := {z | z ∈ closedBall (0 : ℂ) 1 ∧ z.im < 0}

/-- The upper half of the closed unit disc. -/
def upper : Set ℂ := {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < z.im}

/-- The reflection of a chart. -/
theorem conj (c : IsEdgeChart H γ t₀ G a b) :
    IsEdgeChart H γ t₀ (fun z => G ((starRingEnd ℂ) z)) a b := by
  have hnorm : ∀ z ∈ closedBall (0 : ℂ) 1, (starRingEnd ℂ) z ∈ closedBall (0 : ℂ) 1 := fun z hz
    => by
    simpa using hz
  have hset : ∀ X : Set ℂ, (∀ z, z ∈ X → z.im = 0) →
      (fun z => G ((starRingEnd ℂ) z)) '' X = G '' X := fun X hX =>
    image_congr fun z hz => by rw [Complex.conj_eq_iff_im.mpr (hX z hz)]
  refine ⟨c.cont.comp Complex.continuous_conj.continuousOn hnorm, ?_, c.left, c.right, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro y hy z hz h
    have := c.inj (hnorm y hy) (hnorm z hz) h
    simpa using congrArg (starRingEnd ℂ) this
  · simpa using c.zero
  · intro z hz
    rw [c.mem_U _ (hnorm z hz)]
    simp
  · rw [hset {z ∈ ball (0 : ℂ) 1 | z.im = 0} fun _ hz => hz.2]
    exact c.ball_eq
  · rw [hset {z ∈ closedBall (0 : ℂ) 1 | z.im = 0} fun _ hz => hz.2]
    exact c.closed_eq
  · simpa using c.ends

theorem conj_disc (c : IsEdgeChart H γ t₀ G a b) : c.conj.disc = c.disc := by
  change (fun z => G ((starRingEnd ℂ) z)) '' _ = G '' _
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, by simpa using hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(starRingEnd ℂ) z, by simpa using hz, by simp⟩

omit [TopologicalSpace S] in
theorem image_conj_lower : (fun z => G ((starRingEnd ℂ) z)) '' lower = G '' upper := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨by simpa using hz.1, by simpa using hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(starRingEnd ℂ) z, ⟨by simpa using hz.1, by simpa using hz.2⟩, by simp⟩

omit [TopologicalSpace S] in
theorem image_conj_upper : (fun z => G ((starRingEnd ℂ) z)) '' upper = G '' lower := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨by simpa using hz.1, by simpa using hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(starRingEnd ℂ) z, ⟨by simpa using hz.1, by simpa using hz.2⟩, by simp⟩

theorem convex_lower : Convex ℝ lower :=
  (convex_closedBall 0 1).inter (convex_halfSpace_im_lt 0)

theorem convex_upper : Convex ℝ upper :=
  (convex_closedBall 0 1).inter (convex_halfSpace_im_gt 0)

variable [T2Space S] (c : IsEdgeChart H γ t₀ G a b)

include c

omit [T2Space S] in
theorem lower_conn : IsPreconnected (G '' lower) :=
  (convex_lower.isPreconnected).image _ (c.cont.mono fun _ h => h.1)

omit [T2Space S] in
theorem upper_conn : IsPreconnected (G '' upper) :=
  (convex_upper.isPreconnected).image _ (c.cont.mono fun _ h => h.1)

omit [T2Space S] in
theorem lower_disjoint : Disjoint (G '' lower) H.U := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨z, hz, rfl⟩ hU
  exact hz.2.ne ((c.mem_U z hz.1).mp hU)

omit [T2Space S] in
theorem upper_disjoint : Disjoint (G '' upper) H.U := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨z, hz, rfl⟩ hU
  exact hz.2.ne' ((c.mem_U z hz.1).mp hU)

omit [TopologicalSpace S] [T2Space S] c in
theorem cases_of_closedBall {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    z ∈ lower ∨ z.im = 0 ∨ z ∈ upper := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hz, h⟩)

/-- **The two sides of the edge in the chart are the two regions.** -/
theorem sides (hS : IsClosedSurface S) {p q : Set S} (hp : p ∈ H.R) (hq : q ∈ H.R) (hpq : p ≠ q)
    (hep : γ t₀ ∈ closure p) (heq : γ t₀ ∈ closure q) :
    (G '' lower ⊆ p ∧ G '' upper ⊆ q) ∨ (G '' lower ⊆ q ∧ G '' upper ⊆ p) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hzl : (⟨0, -1 / 2⟩ : ℂ) ∈ lower := by
    refine ⟨?_, by norm_num⟩
    rw [mem_closedBall, dist_zero_right]
    have : ‖(⟨0, -1 / 2⟩ : ℂ)‖ = 1 / 2 := by
      rw [Complex.norm_def, Complex.normSq_mk]
      rw [show (0 : ℝ) * 0 + -1 / 2 * (-1 / 2) = (1 / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num)
    rw [this]
    norm_num
  have hzu : (⟨0, 1 / 2⟩ : ℂ) ∈ upper := by
    refine ⟨?_, by norm_num⟩
    rw [mem_closedBall, dist_zero_right]
    have : ‖(⟨0, 1 / 2⟩ : ℂ)‖ = 1 / 2 := by
      rw [Complex.norm_def, Complex.normSq_mk]
      rw [show (0 : ℝ) * 0 + 1 / 2 * (1 / 2) = (1 / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num)
    rw [this]
    norm_num
  have hxl : G ⟨0, -1 / 2⟩ ∉ H.U := disjoint_left.mp (lower_disjoint c) ⟨_, hzl, rfl⟩
  have hxu : G ⟨0, 1 / 2⟩ ∉ H.U := disjoint_left.mp (upper_disjoint c) ⟨_, hzu, rfl⟩
  obtain ⟨r₁, hr₁, hxr₁⟩ := exists_region_of_notMem hxl
  obtain ⟨r₂, hr₂, hxr₂⟩ := exists_region_of_notMem hxu
  have hl := subset_region hr₁ (lower_conn c) (lower_disjoint c) ⟨_, hzl, rfl⟩ hxr₁
  have hu := subset_region hr₂ (upper_conn c) (upper_disjoint c) ⟨_, hzu, rfl⟩ hxr₂
  have hop : IsOpen (G '' ball 0 1) := discInt_eq c ▸ c.isClosedDisc.isOpen_discInt hman
  have hmem : γ t₀ ∈ G '' ball 0 1 := ⟨0, by simp, c.zero⟩
  have hcase : ∀ {r : Set S}, r ∈ H.R → γ t₀ ∈ closure r → r = r₁ ∨ r = r₂ := by
    intro r hr hcl
    obtain ⟨x, hxb, hxr⟩ := mem_closure_iff.mp hcl _ hop hmem
    obtain ⟨z, hz, rfl⟩ := hxb
    have hzc := ball_subset_closedBall hz
    rcases cases_of_closedBall hzc with h | h | h
    · exact Or.inl (region_eq_of_mem hr hr₁ hxr (hl ⟨z, h, rfl⟩))
    · exact absurd ((c.mem_U z hzc).mpr h) (region_subset hr hxr)
    · exact Or.inr (region_eq_of_mem hr hr₂ hxr (hu ⟨z, h, rfl⟩))
  rcases hcase hp hep with rfl | rfl <;> rcases hcase hq heq with rfl | rfl
  · exact absurd rfl hpq
  · exact Or.inl ⟨hl, hu⟩
  · exact Or.inr ⟨hl, hu⟩
  · exact absurd rfl hpq

theorem isOpen_image_ball (hS : IsClosedSurface S) : IsOpen (G '' ball 0 1) :=
  discInt_eq c ▸ c.isClosedDisc.isOpen_discInt fun x => (hS.2.2 x).isManifoldPoint

/-- The data for `exists_disc_off`, for the lower half of the chart. -/
theorem lower_data {A : Set S} (hlo : G '' lower ⊆ A)
    (hrest : ∀ z ∈ closedBall (0 : ℂ) 1, 0 ≤ z.im → G z ∉ A) :
    ∃ ℓ : I → S, Continuous ℓ ∧ ℓ 0 ∉ A ∧ ℓ 1 ∉ A ∧ InjOn ℓ (Ioo 0 1) ∧
      discBd c.disc ∩ A = ℓ '' Ioo 0 1 ∧ IsPreconnected (discInt c.disc ∩ A) ∧
      (discInt c.disc ∩ A).Nonempty := by
  have harc := isTwoArcs_low_high
  have hmem : ∀ t, lowArc t ∈ sphere (0 : ℂ) 1 := fun t =>
    range_low_union_high ▸ Or.inl ⟨t, rfl⟩
  have hball : ∀ t, lowArc t ∈ closedBall (0 : ℂ) 1 := fun t => sphere_subset_closedBall (hmem t)
  have hneg : ∀ t ∈ Ioo (0 : I) 1, (lowArc t).im < 0 := by
    intro t ht
    have h₁ : (0 : ℝ) < t.1 := ht.1
    have h₂ : t.1 < 1 := ht.2
    have : 0 < capH (2 * t.1 - 1) := capH_pos (abs_lt.mpr ⟨by linarith, by linarith⟩)
    simpa [lowArc] using this
  have him : ∀ t, t ∉ Ioo (0 : I) 1 → (lowArc t).im = 0 := by
    intro t ht
    have : 1 ≤ |2 * t.1 - 1| := by
      by_contra hc
      push Not at hc
      obtain ⟨h₁, h₂⟩ := abs_lt.mp hc
      exact ht ⟨show (0 : ℝ) < t.1 by linarith, show t.1 < 1 by linarith⟩
    simp [lowArc, capH_eq_zero this]
  have hn0 : (0 : I) ∉ Ioo (0 : I) 1 := fun h => lt_irrefl _ h.1
  have hn1 : (1 : I) ∉ Ioo (0 : I) 1 := fun h => lt_irrefl _ h.2
  have hballeq : discInt c.disc ∩ A = G '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im < 0} := by
    rw [discInt_eq c]
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxA⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      by_contra hc
      exact hrest z (ball_subset_closedBall hz) (not_lt.mp hc) hxA
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1, rfl⟩, hlo ⟨z, ⟨ball_subset_closedBall hz.1, hz.2⟩, rfl⟩⟩
  refine ⟨G ∘ lowArc, c.cont.comp_continuous harc.arc_left.1 hball, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrest _ (hball 0) (him 0 hn0).ge
  · exact hrest _ (hball 1) (him 1 hn1).ge
  · intro s hs t ht h
    exact harc.arc_left.2 (c.inj (hball s) (hball t) h)
  · rw [discBd_eq c]
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxA⟩
      have hzim : z.im < 0 := by
        by_contra hc
        exact hrest z (sphere_subset_closedBall hz) (not_lt.mp hc) hxA
      rw [← range_low_union_high] at hz
      rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · refine ⟨t, ?_, rfl⟩
        by_contra hn
        rw [him t hn] at hzim
        exact lt_irrefl _ hzim
      · exfalso
        have : 0 ≤ capH (2 * t.1 - 1) := Real.sqrt_nonneg _
        have h₂ : (highArc t).im = capH (2 * t.1 - 1) := rfl
        linarith
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨_, hmem t, rfl⟩, hlo ⟨_, ⟨hball t, hneg t ht⟩, rfl⟩⟩
  · rw [hballeq]
    refine IsPreconnected.image ?_ _ (c.cont.mono fun _ h => ball_subset_closedBall h.1)
    exact ((convex_ball _ _).inter (convex_halfSpace_im_lt 0)).isPreconnected
  · rw [hballeq]
    refine ⟨_, (⟨0, -1 / 2⟩ : ℂ), ⟨?_, by norm_num⟩, rfl⟩
    rw [mem_ball, dist_zero_right]
    have : ‖(⟨0, -1 / 2⟩ : ℂ)‖ = 1 / 2 := by
      rw [Complex.norm_def, Complex.normSq_mk]
      rw [show (0 : ℝ) * 0 + -1 / 2 * (-1 / 2) = (1 / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num)
    rw [this]
    norm_num

end IsEdgeChart

theorem isPreconnected_of_isOpenDisc {r : Set S} (hr : IsOpenDisc r) : IsPreconnected r := by
  obtain ⟨-, ⟨φ⟩⟩ := hr
  have h : PreconnectedSpace OpenUnitDisc :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball _ _).isPreconnected
  have hr : range (fun x => (φ x).1) = r := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (φ y).2
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp⟩
  exact hr ▸ isPreconnected_range (continuous_subtype_val.comp φ.continuous)

/-- The two regions on the two sides of the edge `e`, with a parametrization of `e`. -/
structure GlueData (H : Drawing S) (e : Set S) (γ : I → S) (p q : Set S) : Prop where
  he : e ∈ H.E
  cont : Continuous γ
  zero : γ 0 ∈ H.V
  one : γ 1 ∈ H.V
  inj : InjOn γ (Ioo 0 1)
  image : γ '' Ioo 0 1 = e
  base : ∃ p₀ ∈ H.R, ∃ q₀ ∈ H.R, p₀ ≠ q₀ ∧ e ⊆ closure p₀ ∧ e ⊆ closure q₀ ∧ p₀ ⊆ p ∧ q₀ ⊆ q
  discp : IsOpenDisc p
  discq : IsOpenDisc q
  pq_dis : Disjoint p q
  notMem_p : ∀ t, γ t ∉ p
  notMem_q : ∀ t, γ t ∉ q

/-- `p ∪ q` with the piece of the edge between `s` and `t`. -/
def zone (p q : Set S) (γ : I → S) (s t : I) : Set S := p ∪ q ∪ γ '' Ioo s t

namespace GlueData

variable {H : Drawing S} {e : Set S} {γ : I → S} {p q : Set S} (d : GlueData H e γ p q)

include d

theorem swap : GlueData H e γ q p := by
  obtain ⟨p₀, hp, q₀, hq, hne, h₁, h₂, h₃, h₄⟩ := d.base
  exact ⟨d.he, d.cont, d.zero, d.one, d.inj, d.image, ⟨q₀, hq, p₀, hp, hne.symm, h₂, h₁, h₄, h₃⟩,
    d.discq, d.discp, d.pq_dis.symm, d.notMem_q, d.notMem_p⟩

omit d in
omit [TopologicalSpace S] in
theorem symm_lt_symm {x y : I} : unitInterval.symm x < unitInterval.symm y ↔ y < x := by
  rw [← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe, coe_symm_eq, coe_symm_eq]
  constructor <;> intro h <;> linarith

omit d in
omit [TopologicalSpace S] in
theorem symm_image_Ioo (x y : I) : unitInterval.symm '' Ioo x y = Ioo (unitInterval.symm y)
  (unitInterval.symm x) := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨symm_lt_symm.mpr hu.2, symm_lt_symm.mpr hu.1⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨unitInterval.symm t, ⟨?_, ?_⟩, symm_symm t⟩
    · rw [← symm_lt_symm, symm_symm]
      exact h₂
    · rw [← symm_lt_symm, symm_symm]
      exact h₁

/-- The same edge, traversed backwards. -/
theorem reverse : GlueData H e (γ ∘ unitInterval.symm) p q := by
  have hsym : unitInterval.symm '' Ioo (0 : I) 1 = Ioo 0 1 := by
    rw [symm_image_Ioo, symm_zero, symm_one]
  refine ⟨d.he, d.cont.comp continuous_symm, ?_, ?_, ?_, ?_, d.base, d.discp, d.discq, d.pq_dis,
    fun t => d.notMem_p _, fun t => d.notMem_q _⟩
  · simpa using d.one
  · simpa using d.zero
  · intro x hx y hy h
    have hx' : unitInterval.symm x ∈ Ioo (0 : I) 1 := hsym ▸ mem_image_of_mem _ hx
    have hy' : unitInterval.symm y ∈ Ioo (0 : I) 1 := hsym ▸ mem_image_of_mem _ hy
    exact symm_bijective.1 (d.inj hx' hy' h)
  · rw [image_comp, hsym]
    exact d.image

omit d in
omit [TopologicalSpace S] in
theorem zone_reverse (p q : Set S) (γ : I → S) (s t : I) :
    zone p q (γ ∘ unitInterval.symm) s t = zone p q γ (unitInterval.symm t) (unitInterval.symm s)
      := by
  simp only [zone]
  rw [image_comp, symm_image_Ioo]

theorem mem_e {t : I} (ht : t ∈ Ioo (0 : I) 1) : γ t ∈ e := d.image ▸ mem_image_of_mem γ ht

theorem mem_U (t : I) : γ t ∈ H.U := by
  by_cases ht : t ∈ Ioo (0 : I) 1
  · exact (d.he.2.1 (d.mem_e ht)).1
  · have : t = 0 ∨ t = 1 := by
      by_contra hc
      push Not at hc
      exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr hc.2⟩
    rcases this with rfl | rfl
    · exact H.V_subset_U d.zero
    · exact H.V_subset_U d.one

theorem clp : e ⊆ closure p := by
  obtain ⟨p₀, -, q₀, -, -, h₁, -, h₃, -⟩ := d.base
  exact h₁.trans (closure_mono h₃)

theorem clq : e ⊆ closure q := by
  obtain ⟨p₀, -, q₀, -, -, -, h₂, -, h₄⟩ := d.base
  exact h₂.trans (closure_mono h₄)

omit d in
omit [TopologicalSpace S] in
theorem Ioo_subset (s t : I) : Ioo s t ⊆ Ioo 0 1 := fun _ hx =>
  ⟨lt_of_le_of_lt (unitInterval.nonneg s) hx.1, lt_of_lt_of_le hx.2 (unitInterval.le_one t)⟩

theorem notMem_zone {s t x : I} (hx : x ∉ Ioo s t) : γ x ∉ zone p q γ s t := by
  rintro (h | ⟨y, hy, hyx⟩)
  · rcases h with h | h
    · exact d.notMem_p x h
    · exact d.notMem_q x h
  · have hy' := Ioo_subset _ _ hy
    by_cases hx' : x ∈ Ioo (0 : I) 1
    · exact hx (d.inj hy' hx' hyx ▸ hy)
    · have : x = 0 ∨ x = 1 := by
        by_contra hc
        push Not at hc
        exact hx' ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr hc.2⟩
      have hV : γ x ∈ H.V := by
        rcases this with rfl | rfl
        · exact d.zero
        · exact d.one
      exact (d.he.2.1 (d.mem_e hy')).2 (hyx ▸ hV)

theorem zone_ne_univ (s t : I) : zone p q γ s t ≠ univ := fun h =>
  d.notMem_zone (fun h' => not_lt.mpr (unitInterval.nonneg s) h'.1) (h ▸ mem_univ (γ 0))

theorem zone_isConnected {s t : I} (hst : s < t) : IsConnected (zone p q γ s t) := by
  obtain ⟨m, hm⟩ : (Ioo s t).Nonempty := by
    refine ⟨⟨(s.1 + t.1) / 2, ?_, ?_⟩, ?_, ?_⟩
    · have := s.2.1
      have := t.2.1
      linarith
    · have := s.2.2
      have := t.2.2
      linarith
    · exact show s.1 < (s.1 + t.1) / 2 by have : s.1 < t.1 := hst; linarith
    · exact show (s.1 + t.1) / 2 < t.1 by have : s.1 < t.1 := hst; linarith
  have hsub : ∀ {r : Set S}, IsOpenDisc r → e ⊆ closure r → IsPreconnected (r ∪ γ '' Ioo s t) := by
    intro r hr hcl
    have hrc : IsPreconnected r := isPreconnected_of_isOpenDisc hr
    refine hrc.subset_closure subset_union_left (union_subset subset_closure ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hcl (d.mem_e (Ioo_subset _ _ hx))
  have hne : γ m ∈ (p ∪ γ '' Ioo s t) ∩ (q ∪ γ '' Ioo s t) :=
    ⟨Or.inr (mem_image_of_mem γ hm), Or.inr (mem_image_of_mem γ hm)⟩
  have hu := (hsub d.discp d.clp).union' ⟨_, hne⟩ (hsub d.discq d.clq)
  have heq : (p ∪ γ '' Ioo s t) ∪ (q ∪ γ '' Ioo s t) = zone p q γ s t := by
    simp only [zone]
    ext x
    simp only [mem_union]
    tauto
  exact ⟨⟨γ m, Or.inr (mem_image_of_mem γ hm)⟩, heq ▸ hu⟩

omit d in
omit [TopologicalSpace S] in
theorem zone_mono (p q : Set S) (γ : I → S) (s : I) {t t' : I} (h : t ≤ t') :
    zone p q γ s t ⊆ zone p q γ s t' :=
  union_subset_union_right _ (image_mono fun _ hx => ⟨hx.1, hx.2.trans_le h⟩)

variable [T2Space S] [ConnectedSpace S] {G : ℂ → S} {t₀ a b : I}

/-- A short piece, when the lower half of the chart lies in `p`. -/
theorem zone_start_aux (hS : IsClosedSurface S) (c : IsEdgeChart H γ t₀ G a b)
    (hlo : G '' IsEdgeChart.lower ⊆ p) (hup : G '' IsEdgeChart.upper ⊆ q) :
    IsOpenDisc (zone p q γ a b) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hcase : ∀ {z}, z ∈ closedBall (0 : ℂ) 1 → z.im ≠ 0 → G z ∈ p ∨ G z ∈ q := by
    intro z hz him
    rcases IsEdgeChart.cases_of_closedBall hz with h | h | h
    · exact Or.inl (hlo ⟨z, h, rfl⟩)
    · exact absurd h him
    · exact Or.inr (hup ⟨z, h, rfl⟩)
  have hYeq : zone p q γ a b = p ∪ q ∪ G '' ball 0 1 := by
    simp only [zone]
    refine subset_antisymm (union_subset_union_right _ ?_) (union_subset subset_union_left ?_)
    · rw [← c.ball_eq]
      exact image_mono fun z hz => hz.1
    · rintro _ ⟨z, hz, rfl⟩
      by_cases him : z.im = 0
      · exact Or.inr (c.ball_eq ▸ mem_image_of_mem G ⟨hz, him⟩)
      · exact Or.inl (hcase (ball_subset_closedBall hz) him)
  have hop : IsOpen (zone p q γ a b) := by
    rw [hYeq]
    exact (d.discp.1.union d.discq.1).union (c.isOpen_image_ball hS)
  refine isOpenDisc_of_bound hS hop (d.zone_isConnected (c.left.trans c.right))
    (d.zone_ne_univ _ _) ?_
  intro F hFY hF
  have hbN : IsOpen (discInt c.disc) := c.isClosedDisc.isOpen_discInt hman
  have hKc : IsCompact (F \ discInt c.disc) := hF.isCompact.diff hbN
  have hint := c.discInt_eq
  have hKpq : F \ discInt c.disc ⊆ p ∪ q := by
    rintro x ⟨hxF, hxN⟩
    have := hFY hxF
    rw [hYeq] at this
    rcases this with h | h
    · exact h
    · exact absurd (hint ▸ h) hxN
  have hKp : IsCompact ((F \ discInt c.disc) ∩ p) := by
    have : (F \ discInt c.disc) ∩ p = (F \ discInt c.disc) \ q := by
      ext x
      constructor
      · rintro ⟨hx, hxp⟩
        exact ⟨hx, disjoint_left.mp d.pq_dis hxp⟩
      · rintro ⟨hx, hxq⟩
        exact ⟨hx, (hKpq hx).resolve_right hxq⟩
    rw [this]
    exact hKc.diff d.discq.1
  have hKq : IsCompact ((F \ discInt c.disc) ∩ q) := by
    have : (F \ discInt c.disc) ∩ q = (F \ discInt c.disc) \ p := by
      ext x
      constructor
      · rintro ⟨hx, hxp⟩
        exact ⟨hx, disjoint_right.mp d.pq_dis hxp⟩
      · rintro ⟨hx, hxq⟩
        exact ⟨hx, (hKpq hx).resolve_left hxq⟩
    rw [this]
    exact hKc.diff d.discp.1
  -- Two points of the boundary of the disc.
  have hI₁ : Complex.I ∈ sphere (0 : ℂ) 1 := by simp
  have hI₂ : -Complex.I ∈ sphere (0 : ℂ) 1 := by simp
  have hnotint : ∀ {z}, z ∈ sphere (0 : ℂ) 1 → G z ∉ discInt c.disc := by
    intro z hz hin
    have := hin.2
    rw [c.discBd_eq] at this
    exact this (mem_image_of_mem G hz)
  have hwp : G (-Complex.I) ∈ p := hlo ⟨_, ⟨sphere_subset_closedBall hI₂, by simp⟩, rfl⟩
  have hwq : G Complex.I ∈ q := hup ⟨_, ⟨sphere_subset_closedBall hI₁, by simp⟩, rfl⟩
  have hrp : ∀ z ∈ closedBall (0 : ℂ) 1, 0 ≤ z.im → G z ∉ p := by
    intro z hz him hzp
    rcases him.lt_or_eq with h | h
    · exact disjoint_left.mp d.pq_dis hzp (hup ⟨z, ⟨hz, h⟩, rfl⟩)
    · obtain ⟨y, -, hy⟩ : G z ∈ γ '' Icc a b := c.closed_eq ▸ mem_image_of_mem G ⟨hz, h.symm⟩
      exact d.notMem_p y (hy ▸ hzp)
  obtain ⟨ℓ, hℓ, h0, h1, hinj, hbd, hT, hTne⟩ := c.lower_data hlo hrp
  obtain ⟨ρ₁, hW₁, hρ₁, hCρ₁, hint₁, hbd₁⟩ := exists_absorb hS d.discp c.isClosedDisc hℓ h0 h1 hinj
    hbd
    hT hTne (C := insert (G (-Complex.I)) ((F \ discInt c.disc) ∩ p)) (hKp.insert _)
    (insert_subset hwp inter_subset_right)
    (disjoint_left.mpr (by
      rintro x (rfl | hx)
      · exact hnotint hI₂
      · exact hx.1.2)) (insert_nonempty _ _)
  have hρ₁q : ∀ {x}, x ∈ q → x ∉ ρ₁ := fun hx h => disjoint_left.mp d.pq_dis (hρ₁ h) hx
  have hbq : discBd (c.disc ∪ ρ₁) ∩ q = discBd c.disc ∩ q := by
    ext x
    constructor
    · rintro ⟨hx, hxq⟩
      refine ⟨?_, hxq⟩
      by_contra hn
      have hxN : x ∈ c.disc := by
        rcases discBd_subset _ hx with h | h
        · exact h
        · exact absurd h (hρ₁q hxq)
      have : x ∈ discInt (c.disc ∪ ρ₁) := discInt_mono hman c.isClosedDisc subset_union_left ⟨hxN,
        hn⟩
      exact this.2 hx
    · rintro ⟨hx, hxq⟩
      exact ⟨hbd₁ x (hρ₁q hxq) hx, hxq⟩
  have hiq : discInt (c.disc ∪ ρ₁) ∩ q = discInt c.disc ∩ q := by
    ext x
    constructor
    · rintro ⟨hx, hxq⟩
      exact ⟨(hint₁ hx).resolve_left (hρ₁q hxq), hxq⟩
    · rintro ⟨hx, hxq⟩
      exact ⟨discInt_mono hman c.isClosedDisc subset_union_left hx, hxq⟩
  have hrq : ∀ z ∈ closedBall (0 : ℂ) 1, 0 ≤ z.im → (fun z => G ((starRingEnd ℂ) z)) z ∉ q := by
    intro z hz him hzq
    rcases him.lt_or_eq with h | h
    · exact disjoint_left.mp d.pq_dis
        (hlo ⟨(starRingEnd ℂ) z, ⟨by simpa using hz, by simpa using h⟩, rfl⟩) hzq
    · have hz' : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr h.symm
      obtain ⟨y, -, hy⟩ : G z ∈ γ '' Icc a b := c.closed_eq ▸ mem_image_of_mem G ⟨hz, h.symm⟩
      refine d.notMem_q y ?_
      rw [hy]
      simpa only [hz'] using hzq
  obtain ⟨ℓ', hℓ', h0', h1', hinj', hbd', hT', hTne'⟩ :=
    c.conj.lower_data (A := q) (by rw [IsEdgeChart.image_conj_lower]; exact hup) hrq
  rw [c.conj_disc] at hbd' hT' hTne'
  rw [← hbq] at hbd'
  rw [← hiq] at hT' hTne'
  obtain ⟨ρ₂, hW₂, hρ₂, hCρ₂, hint₂, -⟩ := exists_absorb hS d.discq hW₁ hℓ' h0' h1' hinj' hbd'
    hT' hTne' (C := insert (G Complex.I) ((F \ discInt c.disc) ∩ q)) (hKq.insert _)
    (insert_subset hwq inter_subset_right)
    (disjoint_left.mpr (by
      rintro x hx hin
      have hxq : x ∈ q := by
        rcases hx with rfl | hx
        · exact hwq
        · exact hx.2
      have hin' : x ∈ discInt c.disc := (hiq.subset ⟨hin, hxq⟩).1
      rcases hx with rfl | hx
      · exact hnotint hI₁ hin'
      · exact hx.1.2 hin')) (insert_nonempty _ _)
  refine exists_bound_in hW₂ hF ?_ ?_ hFY
  · intro x hx
    by_cases hxN : x ∈ discInt c.disc
    · exact Or.inl (Or.inl hxN.1)
    · rcases hKpq ⟨hx, hxN⟩ with h | h
      · exact Or.inl (Or.inr (hCρ₁ (Or.inr ⟨⟨hx, hxN⟩, h⟩)))
      · exact Or.inr (hCρ₂ (Or.inr ⟨⟨hx, hxN⟩, h⟩))
  · intro x hx
    rw [hYeq]
    rcases hint₂ hx with h | h
    · exact Or.inl (Or.inr (hρ₂ h))
    · rcases hint₁ h with h' | h'
      · exact Or.inl (Or.inl (hρ₁ h'))
      · exact Or.inr (hint ▸ h')

omit [ConnectedSpace S] in
theorem sides (hS : IsClosedSurface S) (c : IsEdgeChart H γ t₀ G a b) (ht₀ : t₀ ∈ Ioo (0 : I) 1) :
    (G '' IsEdgeChart.lower ⊆ p ∧ G '' IsEdgeChart.upper ⊆ q) ∨
      (G '' IsEdgeChart.lower ⊆ q ∧ G '' IsEdgeChart.upper ⊆ p) := by
  obtain ⟨p₀, hp, q₀, hq, hne, h₁, h₂, h₃, h₄⟩ := d.base
  rcases c.sides hS hp hq hne (h₁ (d.mem_e ht₀)) (h₂ (d.mem_e ht₀)) with ⟨a₁, a₂⟩ | ⟨a₁, a₂⟩
  · exact Or.inl ⟨a₁.trans h₃, a₂.trans h₄⟩
  · exact Or.inr ⟨a₁.trans h₄, a₂.trans h₃⟩

/-- A short piece of the edge. -/
theorem zone_start (hS : IsClosedSurface S) (c : IsEdgeChart H γ t₀ G a b)
    (ht₀ : t₀ ∈ Ioo (0 : I) 1) : IsOpenDisc (zone p q γ a b) := by
  rcases d.sides hS c ht₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact d.zone_start_aux hS c h₁ h₂
  · have heq : zone p q γ a b = zone q p γ a b := by
      simp only [zone]
      rw [union_comm p q]
    rw [heq]
    exact d.swap.zone_start_aux hS c h₁ h₂

omit d [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
theorem real_of_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) (him : z.im = 0) : z = 1 ∨ z = -1 := by
  have h₁ : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have h₂ : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [h₂, Complex.norm_real, Real.norm_eq_abs] at h₁
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h₁ with h | h
  · left
    rw [h₂, h]
    simp
  · right
    rw [h₂, h]
    simp

omit d [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
/-- Real points of the open disc are limits of the lower half. -/
theorem mem_closure_lowerBall {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (him : z.im = 0) :
    z ∈ closure {w | w ∈ ball (0 : ℂ) 1 ∧ w.im < 0} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hn : ‖z‖ < 1 := by simpa using hz
  obtain ⟨δ, hδ, hδε, hδn⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < 1 - ‖z‖ :=
    ⟨min (ε / 2) ((1 - ‖z‖) / 2), by have : 0 < 1 - ‖z‖ := by linarith
                                     positivity,
      (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt (by linarith)⟩
  have hnI : ‖((δ : ℂ) * Complex.I)‖ = δ := by simp [abs_of_pos hδ]
  refine ⟨z - δ * Complex.I, ⟨?_, ?_⟩, ?_⟩
  · have := norm_sub_le z ((δ : ℂ) * Complex.I)
    rw [hnI] at this
    rw [mem_ball, dist_zero_right]
    linarith
  · simp [him, hδ]
  · rw [dist_eq_norm, sub_sub_cancel, hnI]
    exact hδε

omit [ConnectedSpace S] in
private theorem zone_chart_boundary (c : IsEdgeChart H γ t₀ G a b)
    {s : I} (hs : s < a)
    (hcase : ∀ {z}, z ∈ closedBall (0 : ℂ) 1 → z.im ≠ 0 → G z ∈ p ∪ q) :
    ∃ ℓ : I → S, Continuous ℓ ∧ ℓ 0 ∉ zone p q γ s t₀ ∧ ℓ 1 ∉ zone p q γ s t₀ ∧
      InjOn ℓ (Ioo 0 1) ∧ discBd c.disc ∩ zone p q γ s t₀ = ℓ '' Ioo 0 1 := by
  have hpqA : p ∪ q ⊆ zone p q γ s t₀ := subset_union_left
  have hbb : γ b ∉ zone p q γ s t₀ := d.notMem_zone fun h => lt_asymm h.2 c.right
  have haA : γ a ∈ zone p q γ s t₀ := Or.inr ⟨a, ⟨hs, c.left⟩, rfl⟩
  -- The loop along the boundary of the chart, from the far end of the chord.
  obtain ⟨e₀, he₀, hGe₀, hGe₁⟩ : ∃ e₀ : ℂ, (e₀ = 1 ∨ e₀ = -1) ∧ G e₀ = γ b ∧ G (-e₀) = γ a := by
    rcases c.ends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨1, Or.inl rfl, h₂, h₁⟩
    · exact ⟨-1, Or.inr rfl, h₁, by simpa using h₂⟩
  have he₀s : e₀ ∈ sphere (0 : ℂ) 1 := by
    rcases he₀ with rfl | rfl <;> simp
  have hsO : IsOArc (sphere (0 : ℂ) 1) := oArc_sphere
  obtain ⟨P, hPc, hP0, hP1, hPi, hPim, hPr⟩ := exists_oArc_par hsO he₀s
  have hPs : ∀ θ, P θ ∈ closedBall (0 : ℂ) 1 := fun θ => sphere_subset_closedBall (hPr ⟨θ, rfl⟩)
  have hpi := Real.pi_pos
  let ℓ : I → S := fun v => G (P (2 * Real.pi * v.1))
  have hℓ : Continuous ℓ := c.cont.comp_continuous (hPc.comp (by fun_prop)) fun v => hPs _
  have hPne : ∀ {θ}, θ ∈ Ioo 0 (2 * Real.pi) → P θ ≠ e₀ := by
    intro θ hθ he
    obtain ⟨k, hk⟩ := hPi θ 0 (he.trans hP0.symm)
    rw [zero_add] at hk
    have h₁ : (0 : ℝ) < k := by
      by_contra hc
      push Not at hc
      nlinarith [hθ.1]
    have h₂ : (k : ℝ) < 1 := by
      by_contra hc
      push Not at hc
      nlinarith [hθ.2]
    have h₃ : (0 : ℤ) < k := by exact_mod_cast h₁
    have h₄ : k < (1 : ℤ) := by exact_mod_cast h₂
    omega
  have hE : ∀ z ∈ sphere (0 : ℂ) 1, z ≠ e₀ → ∃ v ∈ Ioo (0 : I) 1, P (2 * Real.pi * v.1) = z := by
    intro z hz hne
    obtain ⟨θ, hθ, rfl⟩ : z ∈ P '' Ico 0 (2 * Real.pi) := hPim ▸ hz
    have hθ₀ : 0 < θ := lt_of_le_of_ne hθ.1 (by rintro rfl; exact hne hP0)
    have hv : θ / (2 * Real.pi) ∈ Ioo (0 : ℝ) 1 :=
      ⟨by positivity, (div_lt_one (by positivity)).mpr hθ.2⟩
    refine ⟨⟨_, hv.1.le, hv.2.le⟩, ⟨hv.1, hv.2⟩, ?_⟩
    simp only
    congr 1
    field_simp
  have hthet : ∀ v ∈ Ioo (0 : I) 1, 2 * Real.pi * v.1 ∈ Ioo 0 (2 * Real.pi) := by
    intro v hv
    have h₁ : (0 : ℝ) < v.1 := hv.1
    have h₂ : v.1 < 1 := hv.2
    constructor <;> nlinarith
  have hℓ0 : ℓ 0 ∉ zone p q γ s t₀ := by
    simp only [ℓ, Icc.coe_zero, mul_zero, hP0, hGe₀]
    exact hbb
  have hℓ1 : ℓ 1 ∉ zone p q γ s t₀ := by
    simp only [ℓ, Icc.coe_one, mul_one, hP1, hGe₀]
    exact hbb
  have hℓi : InjOn ℓ (Ioo 0 1) := by
    intro v hv w hw h
    have h₁ := c.inj (hPs _) (hPs _) h
    obtain ⟨k, hk⟩ := hPi _ _ h₁
    have hv₀ := hv.1
    have hv₁ := hv.2
    have hw₀ := hw.1
    have hw₁ := hw.2
    change (0 : ℝ) < v.1 at hv₀
    change v.1 < 1 at hv₁
    change (0 : ℝ) < w.1 at hw₀
    change w.1 < 1 at hw₁
    have h₂ : v.1 = w.1 + k := by
      have : 2 * Real.pi * v.1 = 2 * Real.pi * (w.1 + k) := by rw [hk]; ring
      exact mul_left_cancel₀ (by positivity) this
    have h₃ : (k : ℝ) < 1 := by linarith
    have h₄ : (-1 : ℝ) < k := by linarith
    have h₅ : k = 0 := by
      have a₁ : k < (1 : ℤ) := by exact_mod_cast h₃
      have a₂ : (-1 : ℤ) < k := by exact_mod_cast h₄
      omega
    rw [h₅] at h₂
    exact Subtype.ext (by simpa using h₂)
  have hbd : discBd c.disc ∩ zone p q γ s t₀ = ℓ '' Ioo 0 1 := by
    rw [c.discBd_eq]
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxA⟩
      have hne : z ≠ e₀ := by
        rintro rfl
        exact hbb (hGe₀ ▸ hxA)
      obtain ⟨v, hv, rfl⟩ := hE z hz hne
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have hzs : P (2 * Real.pi * v.1) ∈ sphere (0 : ℂ) 1 := hPr ⟨_, rfl⟩
      refine ⟨⟨_, hzs, rfl⟩, ?_⟩
      set z := P (2 * Real.pi * v.1) with hz
      by_cases him : z.im = 0
      · have hne := hPne (hthet v hv)
        rw [← hz] at hne
        have hz' : z = -e₀ := by
          rcases he₀ with rfl | rfl <;> rcases real_of_sphere hzs him with h | h
          · exact absurd h hne
          · exact h
          · simpa using h
          · exact absurd h hne
        change G z ∈ _
        rw [hz', hGe₁]
        exact haA
      · exact hpqA (hcase (sphere_subset_closedBall hzs) him)
  exact ⟨ℓ, hℓ, hℓ0, hℓ1, hℓi, hbd⟩

/-- **A piece of the edge can be made longer.** -/
theorem zone_step (hS : IsClosedSurface S) (c : IsEdgeChart H γ t₀ G a b)
    (ht₀ : t₀ ∈ Ioo (0 : I) 1) {s : I} (hs : s < a) (hA : IsOpenDisc (zone p q γ s t₀)) :
    IsOpenDisc (zone p q γ s b) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hsides : G '' IsEdgeChart.lower ⊆ p ∪ q ∧ G '' IsEdgeChart.upper ⊆ p ∪ q := by
    rcases d.sides hS c ht₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨h₁.trans subset_union_left, h₂.trans subset_union_right⟩
    · exact ⟨h₁.trans subset_union_right, h₂.trans subset_union_left⟩
  have hpqA : p ∪ q ⊆ zone p q γ s t₀ := subset_union_left
  have hcase : ∀ {z}, z ∈ closedBall (0 : ℂ) 1 → z.im ≠ 0 → G z ∈ p ∪ q := by
    intro z hz him
    rcases IsEdgeChart.cases_of_closedBall hz with h | h | h
    · exact hsides.1 ⟨z, h, rfl⟩
    · exact absurd h him
    · exact hsides.2 ⟨z, h, rfl⟩
  have hYeq : zone p q γ s b = zone p q γ s t₀ ∪ G '' ball 0 1 := by
    apply subset_antisymm
    · rintro x (h | ⟨y, hy, rfl⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hyt : y < t₀
        · exact Or.inl (Or.inr ⟨y, ⟨hy.1, hyt⟩, rfl⟩)
        · refine Or.inr ?_
          have : γ y ∈ γ '' Ioo a b := ⟨y, ⟨c.left.trans_le (not_lt.mp hyt), hy.2⟩, rfl⟩
          rw [← c.ball_eq] at this
          exact image_mono (Set.sep_subset _ _) this
    · refine union_subset (zone_mono _ _ _ _ (c.right.le)) ?_
      rintro _ ⟨z, hz, rfl⟩
      by_cases him : z.im = 0
      · have : G z ∈ γ '' Ioo a b := c.ball_eq ▸ mem_image_of_mem G ⟨hz, him⟩
        obtain ⟨y, hy, he⟩ := this
        exact Or.inr ⟨y, ⟨hs.trans hy.1, hy.2⟩, he⟩
      · exact Or.inl (hcase (ball_subset_closedBall hz) him)
  have hop : IsOpen (zone p q γ s b) := by
    rw [hYeq]
    exact hA.1.union (c.isOpen_image_ball hS)
  refine isOpenDisc_of_bound hS hop (d.zone_isConnected ((hs.trans c.left).trans c.right))
    (d.zone_ne_univ _ _) ?_
  intro F hFY hF
  have hbN : IsOpen (discInt c.disc) := c.isClosedDisc.isOpen_discInt hman
  have hint := c.discInt_eq
  obtain ⟨ℓ, hℓ, hℓ0, hℓ1, hℓi, hbd⟩ := d.zone_chart_boundary c hs hcase
  -- The inside of the chart in `A`.
  let Bl : Set ℂ := {z | z ∈ ball (0 : ℂ) 1 ∧ z.im < 0}
  let Bu : Set ℂ := {z | z ∈ ball (0 : ℂ) 1 ∧ 0 < z.im}
  have hTeq : discInt c.disc ∩ zone p q γ s t₀ = (G '' Bl ∪ γ '' Ioo a t₀) ∪
    (G '' Bu ∪ γ '' Ioo a t₀) := by
    rw [hint]
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxA⟩
      rcases lt_trichotomy z.im 0 with h | h | h
      · exact Or.inl (Or.inl ⟨z, ⟨hz, h⟩, rfl⟩)
      · obtain ⟨y, hy, he⟩ : G z ∈ γ '' Ioo a b := c.ball_eq ▸ mem_image_of_mem G ⟨hz, h⟩
        refine Or.inl (Or.inr ⟨y, ⟨hy.1, ?_⟩, he⟩)
        by_contra hn
        exact d.notMem_zone (fun h' => hn h'.2) (he ▸ hxA)
      · exact Or.inr (Or.inl ⟨z, ⟨hz, h⟩, rfl⟩)
    · rintro ((⟨z, hz, rfl⟩ | ⟨y, hy, rfl⟩) | (⟨z, hz, rfl⟩ | ⟨y, hy, rfl⟩))
      · exact ⟨⟨z, hz.1, rfl⟩, hpqA (hcase (ball_subset_closedBall hz.1) hz.2.ne)⟩
      · have : γ y ∈ γ '' Ioo a b := ⟨y, ⟨hy.1, hy.2.trans c.right⟩, rfl⟩
        rw [← c.ball_eq] at this
        exact ⟨image_mono (Set.sep_subset _ _) this, Or.inr ⟨y, ⟨hs.trans hy.1, hy.2⟩, rfl⟩⟩
      · exact ⟨⟨z, hz.1, rfl⟩, hpqA (hcase (ball_subset_closedBall hz.1) hz.2.ne')⟩
      · have : γ y ∈ γ '' Ioo a b := ⟨y, ⟨hy.1, hy.2.trans c.right⟩, rfl⟩
        rw [← c.ball_eq] at this
        exact ⟨image_mono (Set.sep_subset _ _) this, Or.inr ⟨y, ⟨hs.trans hy.1, hy.2⟩, rfl⟩⟩
  have hBlc : IsPreconnected (G '' Bl) :=
    (((convex_ball _ _).inter (convex_halfSpace_im_lt 0)).isPreconnected).image _
      (c.cont.mono fun _ h => ball_subset_closedBall h.1)
  have hBuc : IsPreconnected (G '' Bu) :=
    (((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected).image _
      (c.cont.mono fun _ h => ball_subset_closedBall h.1)
  have hclosure : ∀ X : Set ℂ, X ⊆ ball 0 1 → (∀ z ∈ ball (0 : ℂ) 1, z.im = 0 → z ∈ closure X) →
      γ '' Ioo a t₀ ⊆ closure (G '' X) := by
    intro X hX hcl x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem : γ y ∈ γ '' Ioo a b := ⟨y, ⟨hy.1, hy.2.trans c.right⟩, rfl⟩
    rw [← c.ball_eq] at hmem
    obtain ⟨z, ⟨hz, him⟩, he⟩ := hmem
    rw [← he]
    have hcont : ContinuousOn G (closure X) := c.cont.mono
      (closure_minimal (hX.trans ball_subset_closedBall) isClosed_closedBall)
    exact hcont.image_closure ⟨z, hcl z hz him, rfl⟩
  have hBlγ : IsPreconnected (G '' Bl ∪ γ '' Ioo a t₀) :=
    hBlc.subset_closure subset_union_left (union_subset subset_closure
      (hclosure _ (fun _ h => h.1) fun z hz him => mem_closure_lowerBall hz him))
  have hBuγ : IsPreconnected (G '' Bu ∪ γ '' Ioo a t₀) := by
    refine hBuc.subset_closure subset_union_left (union_subset subset_closure
      (hclosure _ (fun _ h => h.1) fun z hz him => ?_))
    have h₁ : (starRingEnd ℂ) z ∈ closure Bl := by
      apply mem_closure_lowerBall (by simpa using hz)
      simpa using him
    have h₂ : Continuous (starRingEnd ℂ : ℂ → ℂ) := Complex.continuous_conj
    have h₃ := image_closure_subset_closure_image h₂ (mem_image_of_mem _ h₁)
    have h₄ : (starRingEnd ℂ : ℂ → ℂ) '' Bl = Bu := by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨by simpa using hy.1, by simpa using hy.2⟩
      · intro hw
        exact ⟨(starRingEnd ℂ) w, ⟨by simpa using hw.1, by simpa using hw.2⟩, by simp⟩
    rw [h₄] at h₃
    simpa using h₃
  obtain ⟨m, hm⟩ : (Ioo a t₀).Nonempty := by
    refine ⟨⟨(a.1 + t₀.1) / 2, ?_, ?_⟩, ?_, ?_⟩
    · have := a.2.1
      have := t₀.2.1
      linarith
    · have := a.2.2
      have := t₀.2.2
      linarith
    · exact show a.1 < (a.1 + t₀.1) / 2 by have : a.1 < t₀.1 := c.left; linarith
    · exact show (a.1 + t₀.1) / 2 < t₀.1 by have : a.1 < t₀.1 := c.left; linarith
  have hT : IsPreconnected (discInt c.disc ∩ zone p q γ s t₀) := by
    rw [hTeq]
    exact hBlγ.union (γ m) (Or.inr (mem_image_of_mem γ hm)) (Or.inr (mem_image_of_mem γ hm)) hBuγ
  have hTne : (discInt c.disc ∩ zone p q γ s t₀).Nonempty := by
    rw [hTeq]
    exact ⟨γ m, Or.inl (Or.inr (mem_image_of_mem γ hm))⟩
  -- Now the closed disc around `F`.
  have hI₁ : Complex.I ∈ sphere (0 : ℂ) 1 := by simp
  have hwA : G Complex.I ∈ zone p q γ s t₀ :=
    hpqA (hsides.2 ⟨_, ⟨sphere_subset_closedBall hI₁, by simp⟩, rfl⟩)
  have hwb : G Complex.I ∉ discInt c.disc := by
    intro hin
    have := hin.2
    rw [c.discBd_eq] at this
    exact this (mem_image_of_mem G hI₁)
  have hFA : F \ discInt c.disc ⊆ zone p q γ s t₀ := by
    rintro x ⟨hxF, hxN⟩
    have := hFY hxF
    rw [hYeq] at this
    rcases this with h | h
    · exact h
    · exact absurd (hint ▸ h) hxN
  obtain ⟨ρ, hW, hρ, hCρ, hint', -⟩ := exists_absorb hS hA c.isClosedDisc hℓ hℓ0 hℓ1 hℓi hbd hT hTne
    (C := insert (G Complex.I) (F \ discInt c.disc)) ((hF.isCompact.diff hbN).insert _)
    (insert_subset hwA hFA)
    (disjoint_left.mpr (by
      rintro x (rfl | hx)
      · exact hwb
      · exact hx.2)) (insert_nonempty _ _)
  refine exists_bound_in hW hF ?_ ?_ hFY
  · intro x hx
    by_cases hxN : x ∈ discInt c.disc
    · exact Or.inl hxN.1
    · exact Or.inr (hCρ (Or.inr ⟨hx, hxN⟩))
  · intro x hx
    rw [hYeq]
    rcases hint' hx with h | h
    · exact Or.inl (hρ h)
    · exact Or.inr (hint ▸ h)

/-- A limit of pieces. -/
theorem zone_limit (hS : IsClosedSurface S) {s t : I} {T : Set I} (hst : s < t)
    (hT : ∀ x ∈ T, IsOpenDisc (zone p q γ s x)) (hle : ∀ x ∈ T, x ≤ t)
    (hsup : ∀ y < t, ∃ x ∈ T, y < x) : IsOpenDisc (zone p q γ s t) := by
  obtain ⟨y₀, -⟩ : ∃ y, y < t := ⟨s, hst⟩
  obtain ⟨x₀, hx₀, -⟩ := hsup s hst
  have hcov : zone p q γ s t ⊆ ⋃ x : T, zone p q γ s x.1 := by
    rintro y (h | ⟨u, hu, rfl⟩)
    · exact mem_iUnion.mpr ⟨⟨x₀, hx₀⟩, Or.inl h⟩
    · obtain ⟨x, hx, hux⟩ := hsup u hu.2
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Or.inr ⟨u, ⟨hu.1, hux⟩, rfl⟩⟩
  have hsubu : ⋃ x : T, zone p q γ s x.1 = zone p q γ s t :=
    subset_antisymm (iUnion_subset fun x => zone_mono _ _ _ _ (hle _ x.2)) hcov
  have hop : IsOpen (zone p q γ s t) := by
    rw [← hsubu]
    exact isOpen_iUnion fun x => (hT _ x.2).1
  refine isOpenDisc_of_bound hS hop (d.zone_isConnected hst) (d.zone_ne_univ _ _) ?_
  intro F hFY hF
  have : Nonempty T := ⟨⟨x₀, hx₀⟩⟩
  have hdir : Directed (· ⊆ ·) fun x : T => zone p q γ s x.1 := by
    intro x y
    rcases le_total x.1 y.1 with h | h
    · exact ⟨y, zone_mono _ _ _ _ h, Subset.rfl⟩
    · exact ⟨x, Subset.rfl, zone_mono _ _ _ _ h⟩
  obtain ⟨x, hx⟩ := hF.isCompact.elim_directed_cover _ (fun x => (hT _ x.2).1) (hFY.trans hcov) hdir
  obtain ⟨Δ, hΔ, hd, hb⟩ := exists_disc_in_openDisc (hT _ x.2) hF hx
  exact ⟨Δ, hΔ.trans (zone_mono _ _ _ _ (hle _ x.2)), hd, hb⟩

/-- **The piece reaches the end of the edge.** -/
theorem zone_right (hS : IsClosedSurface S) {s t : I} (hst : s < t)
    (hA : IsOpenDisc (zone p q γ s t)) : IsOpenDisc (zone p q γ s 1) := by
  let T : Set I := {x | s < x ∧ IsOpenDisc (zone p q γ s x)}
  have hne : (closure T).Nonempty := ⟨t, subset_closure ⟨hst, hA⟩⟩
  obtain ⟨m, hmc, hgr⟩ := isClosed_closure.isCompact.exists_isGreatest hne
  have hle : ∀ x ∈ T, x ≤ m := fun x hx => hgr (subset_closure hx)
  have htm : t ≤ m := hle t ⟨hst, hA⟩
  have hsm : s < m := hst.trans_le htm
  have hsup : ∀ y < m, ∃ x ∈ T, y < x := by
    intro y hy
    obtain ⟨x, hx₁, hx₂⟩ := mem_closure_iff.mp hmc _ isOpen_Ioi hy
    exact ⟨x, hx₂, hx₁⟩
  have hm : IsOpenDisc (zone p q γ s m) := d.zone_limit hS hsm (fun x (hx : x ∈ T) => hx.2) hle hsup
  by_cases hm1 : m = 1
  · exact hm1 ▸ hm
  have hm₀ : m ∈ Ioo (0 : I) 1 :=
    ⟨lt_of_le_of_lt (unitInterval.nonneg s) hsm, unitInterval.lt_one_iff_ne_one.mpr hm1⟩
  obtain ⟨G, a, b, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ :=
    exists_edge_chart hS H d.he d.cont d.zero d.one d.inj d.image hm₀ hsm hm₀.2
  have c : IsEdgeChart H γ m G a b := ⟨h₁, h₂, h₄, h₅, h₇, h₈, h₉, h₁₀, h₁₁⟩
  have hb : IsOpenDisc (zone p q γ s b) := d.zone_step hS c hm₀ h₃ hm
  exact absurd (hle b ⟨(h₃.trans h₄).trans h₅, hb⟩) (not_le.mpr h₅)

end GlueData

/-- **Two open discs across an edge.** Let `e` be an edge of a drawing `H` in a closed connected
surface.
Let `p₀ ≠ q₀` be regions of `H` with `e` in both closures. Let `p ⊇ p₀` and `q ⊇ q₀` be disjoint
open
discs that miss the closure of `e`. Then `p ∪ q ∪ e` is an open disc. -/
theorem glue_open_discs [ConnectedSpace S] (hS : IsClosedSurface S) {H : Drawing S} {e p q p₀ q₀ :
  Set S}
    (he : e ∈ H.E) (hp₀ : p₀ ∈ H.R) (hq₀ : q₀ ∈ H.R) (hne : p₀ ≠ q₀) (hcp : e ⊆ closure p₀)
    (hcq : e ⊆ closure q₀) (hsp : p₀ ⊆ p) (hsq : q₀ ⊆ q) (hdp : IsOpenDisc p) (hdq : IsOpenDisc q)
    (hpq : Disjoint p q) (hpe : Disjoint p (closure e)) (hqe : Disjoint q (closure e)) :
    IsOpenDisc (p ∪ q ∪ e) := by
  have hT2 : T2Space S := hS.2.1
  obtain ⟨γ, hγ, h0, h1, hinj, hγe⟩ := exists_edge_param H he
  have hcl : ∀ t, γ t ∈ closure e := by
    intro t
    have h₁ : range γ ⊆ closure (γ '' Ioo 0 1) := by
      have : (univ : Set I) ⊆ closure (Ioo (0 : I) 1) := by
        rw [closure_Ioo (zero_ne_one' I)]
        exact fun x _ => ⟨unitInterval.nonneg x, unitInterval.le_one x⟩
      rintro _ ⟨t, rfl⟩
      exact image_closure_subset_closure_image hγ ⟨t, this (mem_univ t), rfl⟩
    exact hγe ▸ h₁ ⟨t, rfl⟩
  have d : GlueData H e γ p q := ⟨he, hγ, h0, h1, hinj, hγe, ⟨p₀, hp₀, q₀, hq₀, hne, hcp, hcq, hsp,
    hsq⟩,
    hdp, hdq, hpq, fun t ht => disjoint_left.mp hpe ht (hcl t), fun t ht => disjoint_left.mp hqe ht
      (hcl t)⟩
  let t₀ : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : I) 1 := ⟨show (0 : ℝ) < 1 / 2 by norm_num, show
    (1 / 2 : ℝ) < 1 by norm_num⟩
  obtain ⟨G, a, b, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀, g₁₁⟩ :=
    exists_edge_chart hS H he hγ h0 h1 hinj hγe ht₀ ht₀.1 ht₀.2
  have c : IsEdgeChart H γ t₀ G a b := ⟨g₁, g₂, g₄, g₅, g₇, g₈, g₉, g₁₀, g₁₁⟩
  have hab : a < b := g₄.trans g₅
  have hstart := d.zone_start hS c ht₀
  have hright := d.zone_right hS hab hstart
  have hsym : unitInterval.symm 1 < unitInterval.symm a := by
    rw [GlueData.symm_lt_symm]
    exact g₄.trans ht₀.2
  have hr' : IsOpenDisc (zone p q (γ ∘ unitInterval.symm) (unitInterval.symm 1)
    (unitInterval.symm a)) := by
    rw [GlueData.zone_reverse, symm_symm, symm_symm]
    exact hright
  have hall := d.reverse.zone_right hS hsym hr'
  rw [GlueData.zone_reverse, symm_symm, symm_one] at hall
  have heq : zone p q γ 0 1 = p ∪ q ∪ e := by
    simp only [zone]
    rw [hγe]
  exact heq ▸ hall

/-- **The union of two regions across an edge.** Let `e` be an edge of a drawing in a closed
connected
surface. Let `p ≠ q` be regions with `e` in both closures, and suppose both are open discs. Then
`p ∪ q ∪ e` is an open disc. -/
theorem theorem_glue_regions [ConnectedSpace S] (hS : IsClosedSurface S) {H : Drawing S} {e p q :
  Set S}
    (he : e ∈ H.E) (hp : p ∈ H.R) (hq : q ∈ H.R) (hpq : p ≠ q) (hdp : IsOpenDisc p)
      (hdq : IsOpenDisc q)
    (hcp : e ⊆ closure p) (hcq : e ⊆ closure q) : IsOpenDisc (p ∪ q ∪ e) := by
  have hdis : ∀ r ∈ H.R, Disjoint r (closure e) := fun r hr =>
    disjoint_left.mpr fun x hx h => region_subset hr hx (H.closure_subset_U he h)
  exact glue_open_discs hS he hp hq hpq hcp hcq Subset.rfl Subset.rfl hdp hdq
    (disjoint_left.mpr fun x hx hx' => hpq (region_eq_of_mem hp hq hx hx')) (hdis p hp) (hdis q hq)

end GraphMinor.GM11
