/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.RuralExtend
public import LeanPool.GraphMinor.Surface.SphereDisc
public import LeanPool.GraphMinor.Surface.DiscArcs
public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.PlaneDisc
public import LeanPool.GraphMinor.Surface.Crossing

/-!
# Adding an ear to a disc in the plane

A line outside a closed disc `D` with its two ends on the boundary of `D` cuts off one closed disc
`L` from the complement of `D`, on the side away from infinity. The union of `D` and `L` is again a
closed disc. This is the step behind "the union of $\Delta_0$ with all lawns is a closed disc" of
Graph
Minors IX, page 67, and behind the discs `Δ(P)` defined there.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11
open scoped unitInterval

/-- The complement of a closed disc in the plane is connected. -/
theorem isPreconnected_compl_of_isClosedDisc {W : Set EuclideanPlane} (hW : IsClosedDisc W) :
    IsPreconnected Wᶜ := by
  classical
  have hF := hW.isOArc_discBd
  obtain ⟨A, B, ⟨hne, hc, -, -⟩, hA, hB⟩ := jordan_curve_theorem.{0}.1 _ hF
  have hcl : IsClosed W := hW.isCompact.isClosed
  have hint : interior W = W \ discBd W := by
    rw [interior_eq_discInt_plane hW]
    rfl
  have hF_cl : IsClosed (discBd W) := hF.isCompact.isClosed
  obtain ⟨x, hx⟩ : (interior W).Nonempty := by
    rw [hint]
    exact hW.nonempty_discInt
  have hxF : x ∈ univ \ discBd W := ⟨mem_univ _, (hint ▸ hx : x ∈ W \ discBd W).2⟩
  have hsame : connectedComponentIn (univ \ discBd W) x = interior W := by
    apply Subset.antisymm
    · refine isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_interior
        hcl.isOpen_compl ?_ ?_ ⟨x, mem_connectedComponentIn hxF, hx⟩
      · rw [disjoint_left]
        exact fun y hy hy' => hy' (interior_subset hy)
      · intro y hy
        have hyF := connectedComponentIn_subset _ _ hy
        by_cases hyW : y ∈ W
        · exact Or.inl (hint ▸ ⟨hyW, hyF.2⟩)
        · exact Or.inr hyW
    · refine IsPreconnected.subset_connectedComponentIn ?_ hx ?_
      · rw [interior_eq_discInt_plane hW]
        exact hW.isPreconnected_discInt
      · intro y hy
        exact ⟨mem_univ _, (hint ▸ hy : y ∈ W \ discBd W).2⟩
  have hmem : connectedComponentIn (univ \ discBd W) x ∈ componentsIn (univ \ discBd W) :=
    ⟨x, hxF, rfl⟩
  rw [hc, hsame] at hmem
  have hbdd : Bornology.IsBounded (interior W) := hW.isCompact.isBounded.subset interior_subset
  have hIA : interior W = A := by
    rcases hmem with h | h
    · exact h
    · exact (hB (h ▸ hbdd)).elim
  have hBmem : B ∈ componentsIn (univ \ discBd W) := by
    rw [hc]
    exact Or.inr rfl
  obtain ⟨y, hyF, rfl⟩ := hBmem
  have heq : Wᶜ = connectedComponentIn (univ \ discBd W) y := by
    apply Subset.antisymm
    · intro z hz
      have hzF : z ∈ univ \ discBd W := ⟨mem_univ _, fun h => hz (Surface.discBd_subset _ h)⟩
      have hzm : connectedComponentIn (univ \ discBd W) z ∈ componentsIn (univ \ discBd W) :=
        ⟨z, hzF, rfl⟩
      rw [hc] at hzm
      rcases hzm with h | h
      · exfalso
        have := mem_connectedComponentIn hzF
        rw [h, ← hIA] at this
        exact hz (interior_subset this)
      · rw [← h]
        exact mem_connectedComponentIn hzF
    · intro z hz hzW
      have hzF := connectedComponentIn_subset _ _ hz
      have hzi : z ∈ interior W := hint ▸ ⟨hzW, hzF.2⟩
      rw [hIA, ← hsame.trans hIA] at hzi
      apply hne
      rw [← hsame.trans hIA, connectedComponentIn_eq hzi, ← connectedComponentIn_eq hz]
  rw [heq]
  exact isPreconnected_connectedComponentIn

section Sphere

local notation "SHat" => OnePoint EuclideanPlane

private theorem coe_embedding : IsOpenEmbedding ((↑) : EuclideanPlane → SHat) :=
  OnePoint.isOpenEmbedding_coe

/-- A closed disc of the sphere that misses infinity comes from a closed disc of the plane. -/
private theorem exists_plane_disc {D₀ : Set SHat} (hD₀ : IsClosedDisc D₀)
  (hinf : OnePoint.infty ∉ D₀) :
    ∃ D : Set EuclideanPlane, (↑) '' D = D₀ ∧ IsClosedDisc D ∧
      discBd D₀ = (↑) '' discBd D := by
  classical
  let c : EuclideanPlane → SHat := (↑)
  have hc : IsOpenEmbedding c := coe_embedding
  let r : SHat → EuclideanPlane := invFun c
  have hrc : ∀ x, r (c x) = x := leftInverse_invFun hc.injective
  have hcr : ∀ p ∈ range c, c (r p) = p := by
    rintro _ ⟨x, rfl⟩
    rw [hrc]
  have hrcont : ContinuousOn r (range c) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous fun y : range c => r y.1
    have : (fun y : range c => r y.1) = hc.isEmbedding.toHomeomorph.symm := by
      funext y
      obtain ⟨_, x, rfl⟩ := y
      apply hc.isEmbedding.toHomeomorph.injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext (hcr _ ⟨x, rfl⟩)
    rw [this]
    exact Homeomorph.continuous _
  have hD₀c : D₀ ⊆ range c := by
    intro q hq
    induction q using OnePoint.rec with
    | infty => exact (hinf hq).elim
    | coe x => exact ⟨x, rfl⟩
  obtain ⟨hD, hb⟩ := hD₀.image (hrcont.mono hD₀c) hc.continuous.continuousOn
    (fun q hq => hcr q (hD₀c hq))
  have hback : c '' (r '' D₀) = D₀ := by
    rw [image_image]
    exact (image_congr fun q hq => hcr q (hD₀c hq)).trans (image_id' D₀)
  refine ⟨r '' D₀, hback, hD, ?_⟩
  rw [hb, image_image]
  exact ((image_congr fun q hq => hcr q (hD₀c (Surface.discBd_subset _ hq))).trans
    (image_id' _)).symm

/-- A closed disc of the plane gives a closed disc of the sphere. -/
private theorem sphere_disc_image {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    IsClosedDisc (((↑) : EuclideanPlane → SHat) '' D) ∧
      discBd (((↑) : EuclideanPlane → SHat) '' D) = (↑) '' discBd D := by
  classical
  let c : EuclideanPlane → SHat := (↑)
  have hc : IsOpenEmbedding c := coe_embedding
  let r : SHat → EuclideanPlane := invFun c
  have hrc : ∀ x, r (c x) = x := leftInverse_invFun hc.injective
  have hrcont : ContinuousOn r (c '' D) := by
    have h : ContinuousOn c D := hc.continuous.continuousOn
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous fun y : c '' D => r y.1
    have hmap : (fun y : c '' D => r y.1) = fun y => (hc.isEmbedding.toHomeomorph.symm
        ⟨y.1, image_subset_range c D y.2⟩ : EuclideanPlane) := by
      funext y
      obtain ⟨_, x, -, rfl⟩ := y
      rw [hrc]
      apply hc.injective
      have := hc.isEmbedding.toHomeomorph.apply_symm_apply
        ⟨c x, image_subset_range c D ⟨x, ‹_›, rfl⟩⟩
      exact (congrArg Subtype.val this).symm
    rw [hmap]
    exact (Homeomorph.continuous _).comp (by fun_prop)
  exact hD.image hc.continuous.continuousOn hrcont fun x _ => hrc x

/-- See `exists_ear_disc`. This form names the two open arcs of the boundary. -/
private theorem ear_finish {D c L J J' : Set EuclideanPlane} {p q : EuclideanPlane}
    (hD : IsClosedDisc D) (hpq : p ≠ q) (hJ : IsLineWithEnds (J ∪ {p, q}) p q)
    (hJ' : IsLineWithEnds (J' ∪ {p, q}) p q)
    (hJJ : Disjoint J J') (hu : J ∪ J' = discBd D \ {p, q}) (hp : p ∈ discBd D)
    (hq : q ∈ discBd D) (hc : IsLineWithEnds c p q) (hcJ : Disjoint c J) (hL : IsClosedDisc L)
    (hLb : discBd L = (J ∪ {p, q}) ∪ c) (hLD : L ∩ D = J ∪ {p, q}) :
    ∃ A A' L : Set EuclideanPlane, IsLineWithEnds A p q ∧ IsLineWithEnds A' p q ∧
      A ∪ A' = discBd D ∧ A ∩ A' = {p, q} ∧ IsClosedDisc L ∧ discBd L = A ∪ c ∧ L ∩ D = A ∧
      IsClosedDisc (D ∪ L) ∧ discBd (D ∪ L) = A' ∪ c := by
  have hAA : (J ∪ {p, q}) ∪ (J' ∪ {p, q}) = discBd D := by
    rw [union_union_union_comm, hu, union_self, sdiff_union_of_subset]
    rintro x (rfl | rfl)
    · exact hp
    · exact hq
  have hinter : (J ∪ {p, q}) ∩ (J' ∪ {p, q}) = {p, q} := by
    ext x
    constructor
    · rintro ⟨h | h, h' | h'⟩
      · exact (disjoint_left.mp hJJ h h').elim
      · exact h'
      · exact h
      · exact h
    · intro h
      exact ⟨Or.inr h, Or.inr h⟩
  have hsubD : J ∪ {p, q} ⊆ discBd D := hAA ▸ subset_union_left
  obtain ⟨h₁, h₂⟩ := disc_union.{0} D L (J ∪ {p, q}) p q hD hL hJ (by rw [inter_comm]; exact hLD)
    hsubD (hLb ▸ subset_union_left)
  refine ⟨J ∪ {p, q}, J' ∪ {p, q}, L, hJ, hJ', hAA, hinter, hL, hLb, hLD, h₁, ?_⟩
  rw [h₂, hLb]
  have hne : ∀ {y}, y ∈ J → y ≠ p ∧ y ≠ q := by
    intro y hy
    have : y ∈ discBd D \ {p, q} := hu ▸ Or.inl hy
    exact ⟨fun h => this.2 (Or.inl h), fun h => this.2 (Or.inr h)⟩
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    have hxJ : x ∉ J := fun h => hn ⟨Or.inl h, fun h' => by
      rcases h' with h' | h'
      · exact (hne h).1 h'
      · exact (hne h).2 h'⟩
    rcases hx with hx | hx | hx
    · rw [← hAA] at hx
      rcases hx with (h | h) | h
      · exact (hxJ h).elim
      · exact Or.inl (Or.inr h)
      · exact Or.inl h
    · rcases hx with h | h
      · exact (hxJ h).elim
      · exact Or.inl (Or.inr h)
    · exact Or.inr hx
  · intro hx
    refine ⟨?_, ?_⟩
    · rcases hx with hx | hx
      · exact Or.inl (hAA ▸ Or.inr hx)
      · exact Or.inr (Or.inr hx)
    · rintro ⟨h | h, hn⟩
      · rcases hx with (hx | hx) | hx
        · exact disjoint_left.mp hJJ h hx
        · exact hn hx
        · exact disjoint_left.mp hcJ hx h
      · exact hn h

/-- A line with distinct ends on the boundary of a closed disc `D`, and otherwise outside `D`, cuts
off a closed disc `L` from the complement of `D`. The two ends split the boundary of `D` into lines
`A` and `A'`. The disc `L` is bounded by `A` and the line, it meets `D` exactly in `A`, and `D ∪ L`
is a closed disc bounded by `A'` and the line. -/
theorem exists_ear_disc {D c : Set EuclideanPlane} {p q : EuclideanPlane} (hD : IsClosedDisc D)
    (hc : IsLineWithEnds c p q) (hpq : p ≠ q) (hp : p ∈ discBd D) (hq : q ∈ discBd D)
    (hcD : c ∩ D ⊆ {p, q}) :
    ∃ A A' L : Set EuclideanPlane, IsLineWithEnds A p q ∧ IsLineWithEnds A' p q ∧
      A ∪ A' = discBd D ∧ A ∩ A' = {p, q} ∧ IsClosedDisc L ∧ discBd L = A ∪ c ∧ L ∩ D = A ∧
      IsClosedDisc (D ∪ L) ∧ discBd (D ∪ L) = A' ∪ c := by
  classical
  let ι : EuclideanPlane → SHat := (↑)
  have hι : IsOpenEmbedding ι := coe_embedding
  have hιinj : Injective ι := hι.injective
  obtain ⟨hD₁, hD₁b⟩ := sphere_disc_image hD
  have hF₁ := hD₁.isOArc_discBd
  have hsub : ∀ {X : Set EuclideanPlane} {x : EuclideanPlane}, ι x ∈ ι '' X → x ∈ X := by
    rintro X x ⟨y, hy, hyx⟩
    rwa [← hιinj hyx]
  obtain ⟨E, hE, hEb, hcov, hmeet⟩ : ∃ E : Set SHat, IsClosedDisc E ∧ discBd E = ι '' discBd D ∧
      ι '' D ∪ E = univ ∧ ι '' D ∩ E = ι '' discBd D := by
    obtain ⟨Δ₁, Δ₂, -, h₁, h₂, hb₁, hb₂, hc, hm, -, hu⟩ :=
      sphere_disc.{0} SHat ⟨Homeomorph.refl _⟩ _ hF₁
    rcases hu _ hD₁ rfl with h | h
    · refine ⟨Δ₂, h₂, by rw [hb₂, hD₁b], by rw [h]; exact hc, by rw [h, hm, hD₁b]⟩
    · refine ⟨Δ₁, h₁, by rw [hb₁, hD₁b], by rw [h, union_comm]; exact hc,
        by rw [h, inter_comm, hm, hD₁b]⟩
  have hcHat : IsLineWithEnds (ι '' c) (ι p) (ι q) := hc.map_of_embedding hι.isEmbedding
  have hne : ι p ≠ ι q := fun h => hpq (hιinj h)
  have hcE : ι '' c ⊆ E := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxD : x ∈ D
    · have : x ∈ discBd D := by
        rcases hcD ⟨hx, hxD⟩ with rfl | rfl
        · exact hp
        · exact hq
      have h : ι x ∈ ι '' D ∩ E := hmeet ▸ mem_image_of_mem ι this
      exact h.2
    · have h : ι x ∈ ι '' D ∪ E := hcov ▸ mem_univ _
      rcases h with h | h
      · exact (hxD (hsub h)).elim
      · exact h
  have hcbd : ι '' c ∩ discBd E = {ι p, ι q} := by
    rw [hEb]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      rcases hcD ⟨hx, Surface.discBd_subset _ (hsub hy)⟩ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨mem_image_of_mem ι hc.left_mem, mem_image_of_mem ι hp⟩
      · exact ⟨mem_image_of_mem ι hc.right_mem, mem_image_of_mem ι hq⟩
  have hinf : OnePoint.infty ∈ E := by
    have h : (OnePoint.infty : SHat) ∈ ι '' D ∪ E := hcov ▸ mem_univ _
    rcases h with ⟨x, -, hx⟩ | h
    · exact (OnePoint.coe_ne_infty x hx).elim
    · exact h
  have hinfc : (OnePoint.infty : SHat) ∉ ι '' c := by
    rintro ⟨x, -, hx⟩
    exact OnePoint.coe_ne_infty x hx
  obtain ⟨φ⟩ := hD.isOArc_discBd
  obtain ⟨I₁, I₂, hI₁, hI₂, hd, hu, -, -, hl₁, hl₂⟩ := exists_open_arcs φ hp hq hpq
  have hne₁ : I₁.Nonempty := by
    obtain ⟨x, hx, hxn⟩ := hl₁.nonempty_sdiff
    rcases hx with h | h
    · exact ⟨x, h⟩
    · exact (hxn h).elim
  have hne₂ : I₂.Nonempty := by
    obtain ⟨x, hx, hxn⟩ := hl₂.nonempty_sdiff
    rcases hx with h | h
    · exact ⟨x, h⟩
    · exact (hxn (by rw [pair_comm]; exact h)).elim
  have hmem {y} (hy : y ∈ I₁ ∪ I₂) : y ≠ p ∧ y ≠ q := by
    have hy' : y ∈ discBd D \ {p, q} := hu ▸ hy
    exact ⟨fun h => hy'.2 (Or.inl h), fun h => hy'.2 (Or.inr h)⟩
  have hmem₁ {y} (hy : y ∈ I₁) := hmem (Or.inl hy)
  have hmem₂ {y} (hy : y ∈ I₂) := hmem (Or.inr hy)
  have hcl₁ : closure (ι '' I₁) ⊆ ι '' (I₁ ∪ {p, q}) :=
    closure_minimal (image_mono subset_union_left) (hl₁.isCompact.image hι.continuous).isClosed
  have hcl₂ : closure (ι '' I₂) ⊆ ι '' (I₂ ∪ {p, q}) :=
    closure_minimal (image_mono subset_union_left) (hl₂.isCompact.image hι.continuous).isClosed
  have hd₁ : Disjoint (closure (ι '' I₁)) (ι '' I₂) := by
    rw [disjoint_left]
    rintro _ h ⟨y, hy, rfl⟩
    rcases hsub (hcl₁ h) with h' | h'
    · exact disjoint_left.mp hd h' hy
    · rcases h' with h' | h'
      · exact (hmem₂ hy).1 h'
      · exact (hmem₂ hy).2 h'
  have hd₂ : Disjoint (ι '' I₁) (closure (ι '' I₂)) := by
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ h
    rcases hsub (hcl₂ h) with h' | h'
    · exact disjoint_left.mp hd hy h'
    · rcases h' with h' | h'
      · exact (hmem₁ hy).1 h'
      · exact (hmem₁ hy).2 h'
  have hX : discBd E \ {ι p, ι q} = ι '' I₁ ∪ ι '' I₂ := by
    rw [← image_union, hu, hEb]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      exact ⟨x, ⟨hx, fun h => hn (by
        rcases h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, fun h => hn ?_⟩
      rcases h with h | h
      · exact Or.inl (hιinj h)
      · exact Or.inr (hιinj h)
  have hcomp := componentsIn_union_eq_pair (hI₁.image ι hι.continuous.continuousOn)
    (hI₂.image ι hι.continuous.continuousOn) (hne₁.image ι) (hne₂.image ι) hd₁ hd₂
  -- The conclusion, given the side of the line away from infinity.
  have key : ∀ (J J' : Set EuclideanPlane) (Δa Δb : Set SHat), IsLineWithEnds (J ∪ {p, q}) p q →
      IsLineWithEnds (J' ∪ {p, q}) p q → Disjoint J J' → J ∪ J' = discBd D \ {p, q} →
      IsClosedDisc Δa → discBd Δa = ι '' J ∪ ι '' c → ι '' J' ⊆ Δb → Δa ∩ Δb = ι '' c → Δa ⊆ E →
      OnePoint.infty ∉ Δa →
      ∃ A A' L : Set EuclideanPlane, IsLineWithEnds A p q ∧ IsLineWithEnds A' p q ∧
        A ∪ A' = discBd D ∧ A ∩ A' = {p, q} ∧ IsClosedDisc L ∧ discBd L = A ∪ c ∧ L ∩ D = A ∧
        IsClosedDisc (D ∪ L) ∧ discBd (D ∪ L) = A' ∪ c := by
    intro J J' Δa Δb hJ hJ' hJJ hJu hΔa hΔab hJ'b hmt hsubE hinfa
    obtain ⟨L, hLeq, hL, hLb⟩ := exists_plane_disc hΔa hinfa
    have hJ_ne : ∀ {y}, y ∈ J → y ≠ p ∧ y ≠ q := by
      intro y hy
      have : y ∈ discBd D \ {p, q} := hJu ▸ Or.inl hy
      exact ⟨fun h => this.2 (Or.inl h), fun h => this.2 (Or.inr h)⟩
    have hJ'_ne : ∀ {y}, y ∈ J' → y ≠ p ∧ y ≠ q := by
      intro y hy
      have : y ∈ discBd D \ {p, q} := hJu ▸ Or.inr hy
      exact ⟨fun h => this.2 (Or.inl h), fun h => this.2 (Or.inr h)⟩
    have hcJ : Disjoint c J := by
      rw [disjoint_left]
      intro x hxc hxJ
      have hxD : x ∈ D := by
        have : x ∈ discBd D \ {p, q} := hJu ▸ Or.inl hxJ
        exact Surface.discBd_subset _ this.1
      rcases hcD ⟨hxc, hxD⟩ with h | h
      · exact (hJ_ne hxJ).1 h
      · exact (hJ_ne hxJ).2 h
    have hbL : discBd L = (J ∪ {p, q}) ∪ c := by
      apply hι.injective.image_injective
      rw [← hLb, hΔab, ← image_union]
      congr 1
      ext x
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · rcases h with rfl | rfl
          · exact Or.inr hc.left_mem
          · exact Or.inr hc.right_mem
        · exact Or.inr h
    have hLD : L ∩ D = J ∪ {p, q} := by
      ext x
      constructor
      · rintro ⟨hxL, hxD⟩
        have hxa : ι x ∈ Δa := hLeq ▸ mem_image_of_mem ι hxL
        have hb : ι x ∈ ι '' discBd D := hmeet ▸ ⟨mem_image_of_mem ι hxD, hsubE hxa⟩
        have hxF := hsub hb
        by_cases hxpq : x ∈ ({p, q} : Set EuclideanPlane)
        · exact Or.inr hxpq
        · have : x ∈ J ∪ J' := hJu ▸ ⟨hxF, hxpq⟩
          rcases this with h | h
          · exact Or.inl h
          · exfalso
            have hm : ι x ∈ ι '' c := hmt ▸ ⟨hxa, hJ'b (mem_image_of_mem ι h)⟩
            exact hxpq (hcD ⟨hsub hm, hxD⟩)
      · intro hx
        have hbx : x ∈ discBd L := hbL ▸ Or.inl hx
        refine ⟨Surface.discBd_subset _ hbx, ?_⟩
        rcases hx with h | h
        · have : x ∈ discBd D \ {p, q} := hJu ▸ Or.inl h
          exact Surface.discBd_subset _ this.1
        · rcases h with rfl | rfl
          · exact Surface.discBd_subset _ hp
          · exact Surface.discBd_subset _ hq
    exact ear_finish hD hpq hJ hJ' hJJ hJu hp hq hc hcJ hL hbL hLD
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hcm, h₁, h₂, hU, hI, hb₁, hb₂, -⟩ :=
    disc_iArc.{0} E _ _ _ hE hcE hne hcHat hcbd
  rw [hX, hcomp] at hcm
  have hsub₁ : Δ₁ ⊆ E := hU ▸ subset_union_left
  have hsub₂ : Δ₂ ⊆ E := hU ▸ subset_union_right
  have hA₁b : A₁ ⊆ Δ₁ := fun y hy => Surface.discBd_subset _ (hb₁ ▸ Or.inl hy)
  have hA₂b : A₂ ⊆ Δ₂ := fun y hy => Surface.discBd_subset _ (hb₂ ▸ Or.inl hy)
  have hl₂' := hl₂.symm
  have hmemA₁ : A₁ ∈ ({ι '' I₁, ι '' I₂} : Set (Set SHat)) := hcm ▸ Or.inl rfl
  have hmemA₂ : A₂ ∈ ({ι '' I₁, ι '' I₂} : Set (Set SHat)) := hcm ▸ Or.inr rfl
  have hinf' : OnePoint.infty ∈ Δ₁ ∪ Δ₂ := hU ▸ hinf
  have hu' : I₂ ∪ I₁ = discBd D \ {p, q} := by rw [union_comm]; exact hu
  rcases hinf' with hin | hin
  · have hn₂ : OnePoint.infty ∉ Δ₂ := fun h => hinfc (hI ▸ ⟨hin, h⟩)
    rcases hmemA₁ with h | h <;> rcases hmemA₂ with h' | h'
    · exact (hA (h.trans h'.symm)).elim
    · exact key I₂ I₁ Δ₂ Δ₁ hl₂' hl₁ hd.symm hu' h₂ (by rw [hb₂, h']) (h ▸ hA₁b)
        (by rw [inter_comm]; exact hI) hsub₂ hn₂
    · exact key I₁ I₂ Δ₂ Δ₁ hl₁ hl₂' hd hu h₂ (by rw [hb₂, h']) (h ▸ hA₁b)
        (by rw [inter_comm]; exact hI) hsub₂ hn₂
    · exact (hA (h.trans h'.symm)).elim
  · have hn₁ : OnePoint.infty ∉ Δ₁ := fun h => hinfc (hI ▸ ⟨h, hin⟩)
    rcases hmemA₁ with h | h <;> rcases hmemA₂ with h' | h'
    · exact (hA (h.trans h'.symm)).elim
    · exact key I₁ I₂ Δ₁ Δ₂ hl₁ hl₂' hd hu h₁ (by rw [hb₁, h]) (h' ▸ hA₂b) hI hsub₁ hn₁
    · exact key I₂ I₁ Δ₁ Δ₂ hl₂' hl₁ hd.symm hu' h₁ (by rw [hb₁, h]) (h' ▸ hA₂b) hI hsub₁ hn₁
    · exact (hA (h.trans h'.symm)).elim

end Sphere

end GraphMinor.GM09
