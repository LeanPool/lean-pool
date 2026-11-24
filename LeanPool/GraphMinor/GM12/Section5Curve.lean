/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.GM07.Section11
import Mathlib.Topology.UnitInterval

/-!
# Moving a closed curve

Two tools for the proof of Graph Minors XII, (5.3) (page 256). The proof replaces the pieces of a
closed curve outside `Σ₂` by pieces on the boundary of `Σ₂`. `exists_replace` makes one such
replacement, inside a closed disc. There may be infinitely many pieces, but all but finitely many
lie in a thin collar of the boundary, and `exists_push` pushes these out of the collar at one
stroke.
This file also describes the arcs of the circle between points of a closed set (`IsGap`).
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The inverse of an injective continuous map from a compact space is continuous on the range. -/
theorem exists_continuousOn_inv {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] {a : X → Y} (hc : Continuous a) (hi : Function.Injective a) :
    ∃ r : Y → X, ContinuousOn r (range a) ∧ ∀ t, r (a t) = t := by
  classical
  have hemb : IsEmbedding a := (hc.isClosedEmbedding hi).isEmbedding
  refine ⟨Function.invFun a, ?_, Function.leftInverse_invFun hi⟩
  rw [continuousOn_iff_continuous_domRestrict]
  convert (hemb.toHomeomorph).symm.continuous using 1
  funext x
  obtain ⟨_, t, rfl⟩ := x
  have h : hemb.toHomeomorph t = ⟨a t, t, rfl⟩ := rfl
  change Function.invFun a (a t) = _
  rw [Function.leftInverse_invFun hi t, ← h, Homeomorph.symm_apply_apply]

omit [T2Space S] in
/-- Replace a piece `c ∘ a` of a closed curve by another path `γ` with the same ends in a closed
disc
that includes the piece. The new curve is homotopic to the old one, through the disc. -/
theorem exists_replace {c : C(Circle, S)} {a b : 𝕀 → Circle} (hab : IsTwoArcs a b)
    (hu : range a ∪ range b = univ) {γ : 𝕀 → S} (hγ : Continuous γ) (h0 : γ 0 = c (a 0))
    (h1 : γ 1 = c (a 1)) {Δ : Set S} (hΔ : IsClosedDisc Δ) (hc : ∀ t, c (a t) ∈ Δ)
    (hγΔ : ∀ t, γ t ∈ Δ) :
    ∃ c' : C(Circle, S), (∀ x ∈ range b, c' x = c x) ∧ (∀ t, c' (a t) = γ t) ∧
      ClosedCurvesHomotopicIn (range c ∪ Δ) c c' := by
  classical
  obtain ⟨h, g, ch⟩ := hΔ.exists_isChart
  obtain ⟨r, hr, hra⟩ := exists_continuousOn_inv hab.arc_left.1 hab.arc_left.2
  let mix : Circle × 𝕀 → ℂ := fun p =>
    ((1 - p.2.1 : ℝ) : ℂ) * h (c p.1) + ((p.2.1 : ℝ) : ℂ) * h (γ (r p.1))
  have hclosed_a : IsClosed (range a) := (isCompact_range hab.arc_left.1).isClosed
  have hclosed_b : IsClosed (range b) := (isCompact_range hab.arc_right.1).isClosed
  have hdiscA : ∀ x ∈ range a, c x ∈ Δ := by
    rintro _ ⟨t, rfl⟩
    exact hc t
  have hdiscγ : ∀ x ∈ range a, γ (r x) ∈ Δ := fun x _ => hγΔ _
  have hmixmem : ∀ p : Circle × 𝕀, p.1 ∈ range a → mix p ∈ closedBall (0 : ℂ) 1 := by
    intro p hp
    have h1' := (convex_closedBall (0 : ℂ) 1) (ch.hm (hdiscA _ hp)) (ch.hm (hdiscγ _ hp))
      (a := 1 - p.2.1) (b := p.2.1) (by linarith [p.2.2.2]) p.2.2.1 (by ring)
    simpa [mix, Complex.real_smul] using h1'
  have hmixc : ContinuousOn mix (range a ×ˢ univ) := by
    have ch1 : ContinuousOn (fun p : Circle × 𝕀 => h (c p.1)) (range a ×ˢ univ) :=
      ch.hc.comp (c.continuous.comp continuous_fst).continuousOn fun p hp => hdiscA _ hp.1
    have ch2 : ContinuousOn (fun p : Circle × 𝕀 => r p.1) (range a ×ˢ univ) :=
      hr.comp continuous_fst.continuousOn fun p hp => hp.1
    have ch3 : ContinuousOn (fun p : Circle × 𝕀 => h (γ (r p.1))) (range a ×ˢ univ) :=
      ch.hc.comp (hγ.comp_continuousOn ch2) fun p hp => hdiscγ _ hp.1
    have c1 : Continuous fun p : Circle × 𝕀 => ((1 - p.2.1 : ℝ) : ℂ) := by fun_prop
    have c2 : Continuous fun p : Circle × 𝕀 => ((p.2.1 : ℝ) : ℂ) := by fun_prop
    exact (c1.continuousOn.mul ch1).add (c2.continuousOn.mul ch3)
  let H : Circle × 𝕀 → S := fun p => if p.1 ∈ range a then g (mix p) else c p.1
  have hHa : ContinuousOn H (range a ×ˢ univ) :=
    (ch.gc.comp hmixc fun p hp => hmixmem p hp.1).congr fun p hp => ite_eq_left hp.1
  have hend : ∀ x ∈ range a, x ∈ range b → γ (r x) = c x := by
    rintro _ ⟨s, rfl⟩ ⟨t, ht⟩
    rw [hra]
    rcases hab.meet s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact h0
    · exact h1
  have hHb : ContinuousOn H (range b ×ˢ univ) := by
    have : ContinuousOn (fun p : Circle × 𝕀 => c p.1) (range b ×ˢ univ) :=
      (c.continuous.comp continuous_fst).continuousOn
    refine this.congr fun p hp => ?_
    by_cases hpa : p.1 ∈ range a
    · simp only [H, ite_eq_left hpa]
      have he := hend _ hpa hp.1
      simp only [mix, he]
      rw [← add_mul, ← Complex.ofReal_add, sub_add_cancel, Complex.ofReal_one, one_mul,
        ch.gh (hdiscA _ hpa)]
    · simp only [H, ite_eq_right hpa]
  have hcont : Continuous H := by
    have huniv : (range a ×ˢ univ) ∪ (range b ×ˢ univ) = (univ : Set (Circle × 𝕀)) := by
      rw [← union_prod, hu, univ_prod_univ]
    have := hHa.union_of_isClosed hHb (hclosed_a.prod isClosed_univ) (hclosed_b.prod isClosed_univ)
    rw [huniv] at this
    exact continuousOn_univ.mp this
  let c' : C(Circle, S) := ⟨fun x => H (x, 1), by fun_prop⟩
  have hH0 : ∀ x, H (x, 0) = c x := by
    intro x
    by_cases hx : x ∈ range a
    · simp only [H, ite_eq_left hx, mix]
      simp only [Set.Icc.coe_zero, sub_zero, Complex.ofReal_one, one_mul, Complex.ofReal_zero,
        zero_mul,
        add_zero]
      exact ch.gh (hdiscA _ hx)
    · simp only [H, ite_eq_right hx]
  have hH1a : ∀ x ∈ range a, H (x, 1) = γ (r x) := by
    intro x hx
    simp only [H, ite_eq_left hx, mix]
    simp only [Set.Icc.coe_one, sub_self, Complex.ofReal_zero, zero_mul, Complex.ofReal_one,
      one_mul,
      zero_add]
    exact ch.gh (hdiscγ _ hx)
  refine ⟨c', ?_, ?_, ⟨⟨H, hcont⟩, ?_, hH0, fun _ => rfl⟩⟩
  · intro x hx
    change H (x, 1) = c x
    by_cases hxa : x ∈ range a
    · rw [hH1a x hxa, hend x hxa hx]
    · simp only [H, ite_eq_right hxa]
  · intro t
    change H (a t, 1) = γ t
    rw [hH1a _ ⟨t, rfl⟩, hra]
  · rintro ⟨x, τ⟩
    change H (x, τ) ∈ range c ∪ Δ
    by_cases hx : x ∈ range a
    · simp only [H, ite_eq_left hx]
      exact .inr (ch.gm (hmixmem (x, τ) hx))
    · simp only [H, ite_eq_right hx]
      exact .inl ⟨x, rfl⟩

/-! ### A collar -/

/-- A map onto a collar of the boundary of `P₂` on the outside of `P₂`. -/
structure IsOuterCollar {Y : Type*} [TopologicalSpace Y] (P₂ : Set S) (b : Y × 𝕀 → S) : Prop where
  /-- The map is continuous. -/
  cont : Continuous b
  /-- The map is one to one. -/
  inj : Function.Injective b
  /-- Level zero lies in `P₂`. -/
  zero : ∀ y, b (y, 0) ∈ P₂
  /-- The other levels lie outside `P₂`. -/
  pos : ∀ y s, s ≠ 0 → b (y, s) ∉ P₂

/-- A closed curve in `P₂` together with the part of a collar below level `ε` is homotopic, in this
set, to a closed curve in `P₂`, by pushing each point of the collar down its fibre. -/
theorem exists_push {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [Nonempty Y] {P₂ : Set S}
    {b : Y × 𝕀 → S} (hb : IsOuterCollar P₂ b) (hP : IsClosed P₂) {ε : 𝕀} {c : C(Circle, S)}
    (hc : ∀ x, c x ∈ P₂ ∪ b '' {p | p.2 ≤ ε}) :
    ∃ c' : C(Circle, S), (∀ x, c x ∈ P₂ → c' x = c x) ∧ (∀ x p, c x = b p → c' x = b (p.1, 0)) ∧
      (∀ x, c' x ∈ P₂) ∧ ClosedCurvesHomotopicIn (P₂ ∪ b '' {p | p.2 ≤ ε}) c c' := by
  classical
  obtain ⟨r, hr, hrb⟩ := exists_continuousOn_inv hb.cont hb.inj
  have hRange : IsClosed (range b) := (isCompact_range hb.cont).isClosed
  let σ : 𝕀 → 𝕀 := unitInterval.symm
  let H : Circle × 𝕀 → S := fun q =>
    if c q.1 ∈ range b then b ((r (c q.1)).1, (r (c q.1)).2 * σ q.2) else c q.1
  have hP2 : ∀ z ∈ P₂, ∀ τ : 𝕀, ∀ hz : z ∈ range b, b ((r z).1, (r z).2 * σ τ) = z := by
    rintro _ hz τ ⟨p, rfl⟩
    rw [hrb]
    have h0 : p.2 = 0 := by
      by_contra hne
      exact hb.pos p.1 p.2 hne hz
    obtain ⟨y, s⟩ := p
    simp only at h0
    subst h0
    simp
  have hA : IsClosed (c ⁻¹' P₂) := hP.preimage c.continuous
  have hB : IsClosed (c ⁻¹' range b) := hRange.preimage c.continuous
  have h1 : ContinuousOn H ((c ⁻¹' P₂) ×ˢ univ) := by
    have : ContinuousOn (fun q : Circle × 𝕀 => c q.1) ((c ⁻¹' P₂) ×ˢ univ) :=
      (c.continuous.comp continuous_fst).continuousOn
    refine this.congr fun q hq => ?_
    by_cases hq' : c q.1 ∈ range b
    · simp only [H, ite_eq_left hq']
      exact hP2 _ hq.1 _ hq'
    · simp only [H, ite_eq_right hq']
  have h2 : ContinuousOn H ((c ⁻¹' range b) ×ˢ univ) := by
    have hrc : ContinuousOn (fun q : Circle × 𝕀 => r (c q.1)) ((c ⁻¹' range b) ×ˢ univ) :=
      hr.comp (c.continuous.comp continuous_fst).continuousOn fun q hq => hq.1
    have hσ : Continuous fun q : Circle × 𝕀 => σ q.2 := unitInterval.continuous_symm.comp
      continuous_snd
    have hmul : ContinuousOn (fun q : Circle × 𝕀 => (r (c q.1)).2 * σ q.2)
      ((c ⁻¹' range b) ×ˢ univ) :=
      (continuous_snd.comp_continuousOn hrc).mul hσ.continuousOn
    have hall : ContinuousOn (fun q : Circle × 𝕀 => b ((r (c q.1)).1, (r (c q.1)).2 * σ q.2))
        ((c ⁻¹' range b) ×ˢ univ) :=
      hb.cont.comp_continuousOn ((continuous_fst.comp_continuousOn hrc).prodMk hmul)
    exact hall.congr fun q hq => ite_eq_left hq.1
  have hcont : Continuous H := by
    have huniv : ((c ⁻¹' P₂) ×ˢ univ) ∪ ((c ⁻¹' range b) ×ˢ univ) = (univ : Set (Circle × 𝕀)) := by
      rw [← union_prod, ← preimage_union]
      refine (eq_univ_of_forall fun q => ?_)
      rcases hc q.1 with h | ⟨p, -, hp⟩
      · exact ⟨.inl h, mem_univ _⟩
      · exact ⟨.inr ⟨p, hp⟩, mem_univ _⟩
    have := h1.union_of_isClosed h2 (hA.prod isClosed_univ) (hB.prod isClosed_univ)
    rw [huniv] at this
    exact continuousOn_univ.mp this
  have hb0 : ∀ x p, c x = b p → ∀ τ, H (x, τ) = b (p.1, p.2 * σ τ) := by
    intro x p hxp τ
    simp only [H]
    rw [ite_eq_left ⟨p, hxp.symm⟩, hxp, hrb]
  let c' : C(Circle, S) := ⟨fun x => H (x, 1), by fun_prop⟩
  have hσ1 : σ 1 = 0 := unitInterval.symm_one
  have hσ0 : σ 0 = 1 := unitInterval.symm_zero
  have hP2' : ∀ x, c x ∈ P₂ → ∀ τ, H (x, τ) = c x := by
    intro x hx τ
    by_cases hq : c x ∈ range b
    · simp only [H, ite_eq_left hq]
      exact hP2 _ hx _ hq
    · simp only [H, ite_eq_right hq]
  have hc' : ∀ x p, c x = b p → c' x = b (p.1, 0) := by
    intro x p hxp
    change H (x, 1) = _
    rw [hb0 x p hxp, hσ1, mul_zero]
  refine ⟨c', fun x hx => hP2' x hx 1, hc', ?_, ⟨⟨H, hcont⟩, ?_, ?_, fun _ => rfl⟩⟩
  · intro x
    rcases hc x with h | ⟨p, -, hp⟩
    · change H (x, 1) ∈ P₂
      rw [hP2' x h]
      exact h
    · rw [hc' x p hp.symm]
      exact hb.zero _
  · rintro ⟨x, τ⟩
    change H (x, τ) ∈ _
    rcases hc x with h | ⟨p, hple, hp⟩
    · rw [hP2' x h]
      exact .inl h
    · rw [hb0 x p hp.symm]
      refine .inr ⟨(p.1, p.2 * σ τ), ?_, rfl⟩
      exact (unitInterval.mul_le_left).trans hple
  · intro x
    change H (x, 0) = c x
    rcases hc x with h | ⟨p, -, hp⟩
    · exact hP2' x h 0
    · rw [hb0 x p hp.symm, hσ0, mul_one]
      exact hp

/-! ### Gaps of a closed set of the circle -/

/-- `G` is the inside of an arc `a` of the circle with both ends in `A` and no other point in `A`;
`b` is the other arc. -/
structure IsGap (A : Set Circle) (G : Set Circle) (a b : 𝕀 → Circle) : Prop where
  /-- The two arcs. -/
  two : IsTwoArcs a b
  /-- They cover the circle. -/
  cover : range a ∪ range b = univ
  /-- The first end is in `A`. -/
  zero : a 0 ∈ A
  /-- The last end is in `A`. -/
  one : a 1 ∈ A
  /-- No other point is in `A`. -/
  off : ∀ r, r ≠ 0 → r ≠ 1 → a r ∉ A
  /-- `G` is the complement of the other arc. -/
  eq : G = (range b)ᶜ

variable {A G G' : Set Circle} {a b a' b' : 𝕀 → Circle}

theorem IsGap.isOpen (h : IsGap A G a b) : IsOpen G := by
  rw [h.eq]
  exact (isCompact_range h.two.arc_right.1).isClosed.isOpen_compl

theorem IsGap.mem_iff (h : IsGap A G a b) {r : 𝕀} : a r ∈ G ↔ r ≠ 0 ∧ r ≠ 1 := by
  rw [h.eq]
  constructor
  · intro hn
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hn ⟨0, h.two.zero⟩
    · rintro rfl
      exact hn ⟨1, h.two.one⟩
  · rintro ⟨h0, h1⟩ ⟨t, ht⟩
    rcases h.two.meet r t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact h0 rfl
    · exact h1 rfl

theorem IsGap.subset_range (h : IsGap A G a b) : G ⊆ range a := by
  intro x hx
  have : x ∈ range a ∪ range b := h.cover ▸ mem_univ x
  rcases this with hx' | hx'
  · exact hx'
  · rw [h.eq] at hx
    exact absurd hx' hx

theorem IsGap.disjoint (h : IsGap A G a b) : Disjoint G A := by
  refine Set.disjoint_left.mpr fun x hx hA => ?_
  obtain ⟨r, rfl⟩ := h.subset_range hx
  obtain ⟨h0, h1⟩ := h.mem_iff.mp hx
  exact h.off r h0 h1 hA

theorem IsGap.isPreconnected (h : IsGap A G a b) : IsPreconnected G := by
  have he : G = a '' {r | r ≠ 0 ∧ r ≠ 1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨r, rfl⟩ := h.subset_range hx
      exact ⟨r, h.mem_iff.mp hx, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact h.mem_iff.mpr hr
  have hc : IsPreconnected {r : 𝕀 | r ≠ 0 ∧ r ≠ 1} := by
    have : {r : 𝕀 | r ≠ 0 ∧ r ≠ 1} = Ioo 0 1 := by
      ext r
      exact ⟨fun hr => ⟨unitInterval.pos_iff_ne_zero.mpr hr.1, unitInterval.lt_one_iff_ne_one.mpr
        hr.2⟩,
        fun hr => ⟨hr.1.ne', hr.2.ne⟩⟩
    rw [this]
    exact isPreconnected_Ioo
  rw [he]
  exact hc.image _ h.two.arc_left.1.continuousOn

/-- Two gaps are equal or disjoint. -/
theorem IsGap.eq_or_disjoint (hA : IsClosed A) (h : IsGap A G a b) (h' : IsGap A G' a' b') :
    G = G' ∨ Disjoint G G' := by
  have key : ∀ {G₁ G₂ : Set Circle} {a₁ b₁ a₂ b₂ : 𝕀 → Circle}, IsGap A G₁ a₁ b₁ → IsGap A G₂ a₂ b₂
    →
      (G₁ ∩ G₂).Nonempty → G₂ ⊆ G₁ := by
    intro G₁ G₂ a₁ b₁ a₂ b₂ h₁ h₂ hne
    have hcl : IsClosed (range a₁ ∪ A) := (isCompact_range h₁.two.arc_left.1).isClosed.union hA
    have hcov : G₂ ⊆ G₁ ∪ (range a₁ ∪ A)ᶜ := by
      intro x hx
      by_cases hx₁ : x ∈ G₁
      · exact .inl hx₁
      · refine .inr ?_
        rintro (⟨r, rfl⟩ | hxA)
        · have hr : r = 0 ∨ r = 1 := by
            by_contra hn
            push Not at hn
            exact hx₁ (h₁.mem_iff.mpr hn)
          rcases hr with rfl | rfl
          · exact Set.disjoint_left.mp h₂.disjoint hx h₁.zero
          · exact Set.disjoint_left.mp h₂.disjoint hx h₁.one
        · exact Set.disjoint_left.mp h₂.disjoint hx hxA
    have hdis : Disjoint G₁ (range a₁ ∪ A)ᶜ :=
      Set.disjoint_left.mpr fun x hx hn => hn (.inl (h₁.subset_range hx))
    obtain ⟨x, hx₁, hx₂⟩ := hne
    exact h₂.isPreconnected.subset_left_of_subset_union h₁.isOpen hcl.isOpen_compl hdis hcov
      ⟨x, hx₂, hx₁⟩
  by_cases hne : (G ∩ G').Nonempty
  · exact .inl (Subset.antisymm (key h' h (by rwa [Set.inter_comm])) (key h h' hne))
  · exact .inr (Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne))

/-- Every point off a closed set with two points lies in a gap. -/
theorem exists_gap (hA : IsClosed A) {x y z : Circle} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hz : z ∉ A) : ∃ G a b, IsGap A G a b ∧ z ∈ G := by
  obtain ⟨a, b, hab, hu, h0, h1, hoff, hzr⟩ := exists_circle_chord hA hz hx hy hxy
  refine ⟨(range b)ᶜ, a, b, ⟨hab, hu, h0, h1, hoff, rfl⟩, ?_⟩
  rintro ⟨t, rfl⟩
  have hbA : b t ∈ range a := hzr
  obtain ⟨r, hr⟩ := hbA
  rcases hab.meet r t hr with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact hz (hab.zero ▸ h0)
  · exact hz (hab.one ▸ h1)

end GraphMinor.GM12
