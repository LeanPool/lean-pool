/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Each region of a radial drawing contains one edge

Let `H` be the union of a 2-cell drawing `Γ` with an edge and a radial drawing `Γ'` of `Γ`. We show
that the closure of each region of `H` contains exactly one edge of `Γ`, and then deduce
`RegionFacts`,
which is the sentence of Graph Minors XI (Section 3, page 75) that every region of `Γ'` contains a
unique edge of `Γ`. The steps are these.

* At a vertex of `Γ`, no corner lies between two edges of `Γ'` (`corner_has_edge`). With
  `corner_has_spoke`, this says that exactly one side of each corner is an edge of `Γ'`.
* At the vertex of a region of `Γ`, different corners lie in different regions of `H`
  (`corner_regions_ne`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] {Γ Γ' : Drawing S}

/-- A parameter below `t / 2` is `s / 2` for some `s ≤ t`. -/
theorem exists_halfT_eq {s t : I} (h : s ≤ halfT t) : ∃ t', t' ≤ t ∧ halfT t' = s := by
  have h' : (s : ℝ) ≤ (t : ℝ) / 2 := h
  have ht := t.2.2
  refine ⟨⟨2 * s, by have := s.2.1; positivity, by linarith⟩, ?_, ?_⟩
  · change 2 * (s : ℝ) ≤ t
    linarith
  · exact Subtype.ext (by change 2 * (s : ℝ) / 2 = s; ring)

theorem halfT_pos {t : I} (h : 0 < t) : 0 < halfT t := by
  have h' : (0 : ℝ) < t := h
  change (0 : ℝ) < (t : ℝ) / 2
  positivity

theorem halfT_lt_one (t : I) : halfT t < 1 := by
  change (t : ℝ) / 2 < 1
  linarith [t.2.2]

/-- An edge of `H` with the two different ends `x`, `c`, as a path from the end of a half-edge. -/
theorem exists_edge_path [T2Space S] {H : Drawing S} {γ : Set S → I → S} (hγ : EdgePar H γ)
    {x c : S} (i : halfEdges H γ x) (hxc : x ≠ c) (hc : c ∈ H.V) (hcl : c ∈ closure i.1.1) :
    ∃ G : I → S, Continuous G ∧ Function.Injective G ∧ G 0 = x ∧ G 1 = c ∧
      range G = closure i.1.1 ∧ ∀ t, spoke γ i.1 t = G (halfT t) := by
  obtain ⟨⟨e, b⟩, he, hb⟩ := i
  dsimp only at he hb hcl ⊢
  obtain ⟨b', hb'⟩ := exists_end_eq hγ he hc hcl
  have hbb : b' = !b := by
    cases b <;> cases b' <;> first | rfl | exact (hxc (hb.symm.trans hb')).elim
  subst hbb
  have hne : γ e 0 ≠ γ e 1 := by
    intro h
    apply hxc
    cases b
    · simpa [endOf, ← hb, ← hb'] using h
    · simpa [endOf, ← hb, ← hb'] using h.symm
  obtain ⟨G, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_fullPar hγ he b hne
  exact ⟨G, h₁, h₂, h₃.trans hb, h₄.trans hb', h₅, h₆⟩

/-- Distinct sectors in a single region give a loop through their common vertex. If such a
loop bounds a disc with interior disjoint from the drawing, the two sectors cannot share a region.
The hypothesis supplies the disc for the particular drawing. -/
theorem corner_regions_ne_of_free_disc [T2Space S] (hS : IsClosedSurface S)
    {H : Drawing S} {c : S} (hc : c ∈ H.U) {γ : Set S → I → S}
    {next : halfEdges H γ c → halfEdges H γ c}
    {ρ P Q : halfEdges H γ c → Set S} {W : Set S} {τ : halfEdges H γ c → I}
    (hsec : IsSectors H γ c next ρ P W Q τ)
    {k k' : halfEdges H γ c} (hkk : k ≠ k')
    (hdisc : ∀ J : Set S, IsOArc J → c ∈ J → (∀ y ∈ J, y = c ∨ y ∈ ρ k) →
      ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = J ∧ Disjoint (Δ \ discBd Δ) H.U) :
    ρ k ≠ ρ k' := by
  intro hρ
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpR : ρ k ∈ H.R := IsCorners.region (IsSectors.corners hsec) k
  have hcp : c ∉ ρ k := fun h => region_subset hpR h hc
  have hppath : IsPathConnected (ρ k) :=
    isPathConnected_of_isOpen hS (region_isOpen hpR) (region_isPreconnected hpR)
      (region_nonempty hpR)
  obtain ⟨g₁, hg₁, hi₁, h₁0, h₁⟩ := exists_path_into_disc (IsSectors.disc hsec k)
    (IsSectors.bd hsec k) (IsSectors.isOpen hsec) (IsSectors.mem hsec)
  obtain ⟨g₂, hg₂, hi₂, h₂0, h₂⟩ := exists_path_into_disc (IsSectors.disc hsec k')
    (IsSectors.bd hsec k') (IsSectors.isOpen hsec) (IsSectors.mem hsec)
  have hg₁p : ∀ t, 0 < t → g₁ t ∈ ρ k := fun t ht => by
    obtain ⟨a, b, d⟩ := h₁ t ht
    exact IsSectors.sub hsec k (IsSectors.inside hsec k ⟨⟨a, b⟩, d⟩)
  have hg₂p : ∀ t, 0 < t → g₂ t ∈ ρ k := fun t ht => by
    obtain ⟨a, b, d⟩ := h₂ t ht
    rw [hρ]
    exact IsSectors.sub hsec k' (IsSectors.inside hsec k' ⟨⟨a, b⟩, d⟩)
  obtain ⟨e, he, hei, he0, he1, hep, O, hO, hcO, hOr⟩ :=
    exists_chord_to_point hppath hcp (hg₂p 1 one_pos) hg₁ h₁0 hg₁p
  -- The first time after `0` at which `e` meets `g₂`.
  have hsame : ∀ t, t ≠ 0 → e t ∈ O → e t ∉ range g₂ := by
    rintro t ht htO ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hOr t htO
    have hne : e t ≠ c := fun h => hcp (h ▸ hep t ht)
    have ha0 : 0 < a := unitInterval.pos_iff_ne_zero.mpr fun h => hne (by rw [← ha, h, h₁0])
    have hb0 : 0 < b := unitInterval.pos_iff_ne_zero.mpr fun h => hne (by rw [← hb, h, h₂0])
    have hmem : e t ∈ Q k ∩ Q k' := ⟨ha ▸ (h₁ a ha0).2.1, hb ▸ (h₂ b hb0).2.1⟩
    exact region_subset hpR (hep t ht) (IsSectors.inter hsec k k' hkk hmem)
  obtain ⟨δ, hδ, hδa, hδO⟩ := exists_pos_le he hO (he0 ▸ hcO) (a := 1) one_pos
  let Z : Set I := Icc δ 1 ∩ e ⁻¹' range g₂
  have hZc : IsCompact Z := isCompact_Icc.inter_right
    ((isCompact_range hg₂).isClosed.preimage he)
  have hZne : Z.Nonempty := ⟨1, ⟨hδa, le_rfl⟩, ⟨1, he1.symm⟩⟩
  obtain ⟨t₀, ⟨ht₀I, s₀, hs₀⟩, ht₀min⟩ := hZc.exists_isLeast hZne
  have ht₀ : 0 < t₀ := hδ.trans_le ht₀I.1
  have hne₀ : e t₀ ≠ c := fun h => ht₀.ne' (hei (h.trans he0.symm))
  have hs₀0 : 0 < s₀ := unitInterval.pos_iff_ne_zero.mpr fun h => hne₀ (by rw [← hs₀, h, h₂0])
  have hl₁ : IsLineWithEnds (e '' Icc 0 t₀) c (e t₀) := he0 ▸ isLine_piece he hei ht₀
  have hl₂ : IsLineWithEnds (g₂ '' Icc 0 s₀) c (e t₀) := by
    have := isLine_piece hg₂ hi₂ hs₀0
    rwa [h₂0, hs₀] at this
  have hmeet : e '' Icc 0 t₀ ∩ g₂ '' Icc 0 s₀ ⊆ {c, e t₀} := by
    rintro y ⟨⟨a, ha, rfl⟩, b, -, hb⟩
    by_cases ha0 : a = 0
    · exact Or.inl (by rw [ha0, he0])
    · refine Or.inr ?_
      have hle : t₀ ≤ a := by
        by_cases hδa' : δ ≤ a
        · exact ht₀min ⟨⟨hδa', unitInterval.le_one _⟩, ⟨b, hb⟩⟩
        · have hal : a ≤ δ := (not_le.mp hδa').le
          exact (hsame a ha0 (hδO a hal) ⟨b, hb⟩).elim
      have : a = t₀ := le_antisymm ha.2 hle
      change e a = e t₀
      rw [this]
  have hJ : IsOArc (e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀) := isOArc_union hl₁ hl₂ hmeet
  have hJp : ∀ y ∈ e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀, y = c ∨ y ∈ ρ k := by
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    · by_cases ha : a = 0
      · exact Or.inl (by rw [ha, he0])
      · exact Or.inr (hep a ha)
    · by_cases ha : a = 0
      · exact Or.inl (by rw [ha, h₂0])
      · exact Or.inr (hg₂p a (unitInterval.pos_iff_ne_zero.mpr ha))
  have hcJ : c ∈ e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀ :=
    Or.inl ⟨0, ⟨le_rfl, ht₀.le⟩, he0⟩
  obtain ⟨Δ, hΔ, hb, hfree⟩ := hdisc _ hJ hcJ hJp
  have hcb : c ∈ discBd Δ := hb.symm ▸ hcJ
  obtain ⟨A, W₀, hW₀, hcW₀, hAc, hAΔ, hAb, hAX, -, hclA⟩ :=
    exists_half_nbhd hΔ (IsSectors.isOpen hsec).isClosed_compl hcb
      (fun h' => h' (IsSectors.mem hsec))
  have hAW : ∀ y ∈ A, y ∈ W := fun y hy => by
    by_contra hn
    exact disjoint_left.mp hAX hy hn
  have hAU : ∀ y ∈ A, y ∉ H.U := fun y hy hyU =>
    disjoint_left.mp hfree ⟨hAΔ hy, disjoint_left.mp hAb hy⟩ hyU
  -- A connected set off `H` near `c`, with a point of a sector interior in its closure, lies in the
  -- closed disc of that sector.
  have hinQ : ∀ j, ∀ z, z ∈ closure A → z ∈ Q j → z ∉ discBd (Q j) → A ⊆ Q j := by
    intro j z hzA hzQ hzb
    have hQd := IsSectors.disc hsec j
    have hAfr : Disjoint A (frontier (Q j)) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hQd]
      exact disjoint_left.mpr fun y hy hyb => hAU y hy (IsSectors.bdU hsec j ⟨hAW y hy, hyb⟩)
    have hzint : z ∈ interior (Q j) := by
      have hnf : z ∉ frontier (Q j) := by
        rwa [IsClosedDisc.frontier_eq_discBd hS hQd]
      by_contra hni
      exact hnf ⟨subset_closure hzQ, hni⟩
    rcases subset_or_disjoint_of_frontier hQd.isClosed hAc hAfr with h' | h'
    · exact h'
    · obtain ⟨y, hyI, hyA⟩ := mem_closure_iff.mp hzA _ isOpen_interior hzint
      exact (disjoint_left.mp h' hyA (interior_subset hyI)).elim
  obtain ⟨t, ht, htt₀, htN⟩ := exists_pos_le he (hW₀.inter hO) (by rw [he0]; exact ⟨hcW₀, hcO⟩) ht₀
  obtain ⟨s, hs, hss₀, hsN⟩ := exists_pos_le hg₂ hW₀ (by rw [h₂0]; exact hcW₀) hs₀0
  have hzt : e t ∈ closure A := hclA ⟨(htN t le_rfl).1, hb ▸ Or.inl ⟨t, ⟨ht.le, htt₀⟩, rfl⟩⟩
  have hzs : g₂ s ∈ closure A := hclA ⟨hsN s le_rfl, hb ▸ Or.inr ⟨s, ⟨hs.le, hss₀⟩, rfl⟩⟩
  obtain ⟨a, ha⟩ := hOr t (htN t le_rfl).2
  have ha0 : 0 < a := unitInterval.pos_iff_ne_zero.mpr fun h =>
    ht.ne' (hei ((ha.symm.trans (by rw [h, h₁0])).trans he0.symm))
  have hA₁ : A ⊆ Q k := hinQ k _ hzt (ha ▸ (h₁ a ha0).2.1) (ha ▸ (h₁ a ha0).2.2)
  have hA₂ : A ⊆ Q k' := hinQ k' _ hzs (h₂ s hs).2.1 (h₂ s hs).2.2
  obtain ⟨y, -, hyA⟩ := mem_closure_iff.mp hzs _ isOpen_univ (mem_univ _)
  exact hAU y hyA (IsSectors.inter hsec k k' hkk ⟨hA₁ hyA, hA₂ hyA⟩)

variable [T2Space S] [ConnectedSpace S] (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
  (hS : IsClosedSurface S)

include hrad hS

omit [ConnectedSpace S] in
/-- **No corner at a vertex of `Γ` lies between two edges of `Γ'`.** Let `f`, `g` be such edges.
They
run from `x` to the vertex `c` of a region `r`. Then `exists_disc_of_corner` gives a closed disc in
`r ∪ {x}` with boundary `closure f ∪ closure g`, against condition (iv). -/
theorem corner_has_edge {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) {x : S}
    (hx : x ∈ Γ.V) {next : halfEdges (radialUnion hrad) γ x → halfEdges (radialUnion hrad) γ x}
    {ρ P Q : halfEdges (radialUnion hrad) γ x → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ x → I}
    (hsec : IsSectors (radialUnion hrad) γ x next ρ P W Q τ) (k : halfEdges (radialUnion hrad) γ x)
    (hk : k.1.1 ∈ Γ'.E) (hn : (next k).1.1 ∈ Γ'.E) : False := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcor := IsSectors.corners hsec
  have hpR : ρ k ∈ (radialUnion hrad).R := IsCorners.region hcor k
  obtain ⟨r, hr, hpr⟩ := exists_region_of_sub hrad hpR
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  have hxU : x ∉ r := fun h => region_subset hr h (Γ.V_subset_U hx)
  have hxc : x ≠ c := fun h => hxU (h ▸ hc)
  have hcH : c ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hcV
  obtain ⟨j, hj⟩ := next_surjective hcor k
  have hkcl : k.1.1 ⊆ closure (ρ k) := by
    have := IsCorners.right hcor j
    rwa [hj] at this
  have hncl : (next k).1.1 ⊆ closure (ρ k) := IsCorners.left hcor k
  have hxk : x ∈ closure k.1.1 := by
    have := end_mem_closure hγ k.2.1 k.1.2
    rwa [k.2.2] at this
  have hxn : x ∈ closure (next k).1.1 := by
    have := end_mem_closure hγ (next k).2.1 (next k).1.2
    rwa [(next k).2.2] at this
  obtain ⟨hcapk, -, hrk⟩ := spoke_facts hrad hS hk hr hpr hkcl hc hcV hx hxk
  obtain ⟨hcapn, -, hrn⟩ := spoke_facts hrad hS hn hr hpr hncl hc hcV hx hxn
  have hclk : c ∈ closure k.1.1 ∩ Γ'.V := by rw [hcapk]; simp
  have hcln : c ∈ closure (next k).1.1 ∩ Γ'.V := by rw [hcapn]; simp
  obtain ⟨G₁, hG₁, hi₁, h₁0, h₁1, hr₁, hs₁⟩ := exists_edge_path hγ k hxc hcH hclk.1
  obtain ⟨G₂, hG₂, hi₂, h₂0, h₂1, hr₂, hs₂⟩ := exists_edge_path hγ (next k) hxc hcH hcln.1
  have hne : k.1.1 ≠ (next k).1.1 := by
    intro he
    have hb : k.1.2 ≠ (next k).1.2 := fun h =>
      IsSectors.next_ne hsec k (Subtype.ext (Prod.ext he.symm h.symm))
    obtain ⟨b', hb'⟩ := exists_end_eq hγ k.2.1 hcH hclk.1
    have hk₂ := k.2.2
    have hn₂ := (next k).2.2
    rw [← he] at hn₂
    have : b' = k.1.2 ∨ b' = (next k).1.2 := by
      revert hb
      cases b' <;> cases k.1.2 <;> cases (next k).1.2 <;> simp
    rcases this with h | h
    · rw [h] at hb'
      exact hxc (hk₂.symm.trans hb')
    · rw [h] at hb'
      exact hxc (hn₂.symm.trans hb')
  have hmeet : range G₁ ∩ range G₂ ⊆ {x, c} := by
    rw [hr₁, hr₂, ← hcapk]
    exact fun y hy => ⟨hy.1, closure_inter_subset_V hk hn hne hy⟩
  have hU₁ : closure k.1.1 ⊆ (radialUnion hrad).U := fun y hy =>
    Or.inr (Γ'.closure_subset_U hk hy)
  have hU₂ : closure (next k).1.1 ⊆ (radialUnion hrad).U := fun y hy =>
    Or.inr (Γ'.closure_subset_U hn hy)
  have hsnz : ∀ {G : I → S}, G 0 = x → Function.Injective G → ∀ s, s ≠ 0 → G s ≠ x :=
    fun h0 hi s hs h => hs (hi (h.trans h0.symm))
  obtain ⟨Δ, hΔ, hsub, hb⟩ := exists_disc_of_corner hS (IsSectors.disc hsec k)
    (IsSectors.bd hsec k) (IsSectors.isOpen hsec) (IsSectors.mem hsec) (hrad.1.2 r hr) hxU hG₁ hG₂
    hi₁ hi₂ h₁0 h₂0 h₁1 h₂1 hmeet
    (fun s hs => hrk _ (hr₁ ▸ ⟨s, rfl⟩) (hsnz h₁0 hi₁ s hs))
    (fun s hs => hrn _ (hr₂ ▸ ⟨s, rfl⟩) (hsnz h₂0 hi₂ s hs))
    (ρ' := ρ k) (fun y hyW hyQ hyb => IsSectors.sub hsec k (IsSectors.inside hsec k ⟨⟨hyW, hyQ⟩,
      hyb⟩))
    hpr
    (disjoint_left.mpr fun y hy h => region_subset hpR hy (hU₁ (hr₁ ▸ h)))
    (disjoint_left.mpr fun y hy h => region_subset hpR hy (hU₂ (hr₂ ▸ h)))
    (halfT_pos (IsSectors.pos hsec k)) (halfT_pos (IsSectors.pos hsec (next k)))
    (halfT_lt_one _) (halfT_lt_one _)
    (fun s hs => by
      obtain ⟨t, ht, rfl⟩ := exists_halfT_eq hs
      rw [← hs₁]
      exact IsSectors.left hsec k t ht)
    (fun s hs => by
      obtain ⟨t, ht, rfl⟩ := exists_halfT_eq hs
      rw [← hs₂]
      exact IsSectors.right hsec k t ht)
  rw [hr₁, hr₂] at hb
  exact no_bigon hrad hS hk hn hne hx hr hc hcV hcapk hcapn hΔ hsub hb

omit [ConnectedSpace S] in
/-- **At the vertex of a region of `Γ`, different corners lie in different regions of `H`.** If two
corners lie in the same region of `H`, an `O`-arc `J` runs through `c` and these two corners, inside
a
region `r` of `Γ`. It bounds a closed disc in the open disc `r`. No edge of `Γ'` enters this disc,
because each one ends outside `r`. So the disc is on just one side of `J` at `c`, and it lies in one
sector at `c`. But `J` runs along both corners. -/
theorem corner_regions_ne {γ : Set S → I → S} {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r)
  (hcV : c ∈ Γ'.V)
    {next : halfEdges (radialUnion hrad) γ c → halfEdges (radialUnion hrad) γ c}
    {ρ P Q : halfEdges (radialUnion hrad) γ c → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ c → I}
    (hsec : IsSectors (radialUnion hrad) γ c next ρ P W Q τ)
    {k k' : halfEdges (radialUnion hrad) γ c} (hkk : k ≠ k') : ρ k ≠ ρ k' := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcor := IsSectors.corners hsec
  have hpR : ρ k ∈ (radialUnion hrad).R := IsCorners.region hcor k
  have hcH : c ∈ (radialUnion hrad).U := Or.inr (Γ'.V_subset_U hcV)
  have hdisH : Disjoint (ρ k) Γ.U := disjoint_left.mpr fun y hy h => region_subset hpR hy (Or.inl h)
  obtain ⟨y₀, hy₀r, hy₀⟩ := mem_closure_iff.mp (IsCorners.closure_v hcor k) r (region_isOpen hr) hc
  have hpr : ρ k ⊆ r := subset_region hr (region_isPreconnected hpR) hdisH hy₀ hy₀r
  refine corner_regions_ne_of_free_disc hS hcH hsec hkk ?_
  intro J hJ hcJ hJp
  have hJr : J ⊆ r := fun y hy => by
    rcases hJp y hy with h | h
    · exact h ▸ hc
    · exact hpr h
  obtain ⟨Δ, hΔr, hΔ, hb⟩ := exists_disc_in_openDisc (hrad.1.2 r hr) hJ hJr
  have hcb : c ∈ discBd Δ := hb.symm ▸ hcJ
  -- The interior of `Δ` misses `H`.
  have hfree : Disjoint (Δ \ discBd Δ) (radialUnion hrad).U := by
    refine disjoint_left.mpr ?_
    rintro y ⟨hyΔ, hyb⟩ (hyU | hyU)
    · exact region_subset hr (hΔr hyΔ) hyU
    by_cases hyV : y ∈ Γ'.V
    · exact hyb ((hub_unique hrad hr hc hcV (hΔr hyΔ) hyV) ▸ hcb)
    rw [Γ'.U_eq] at hyU
    rcases hyU with h' | hyE
    · exact hyV h'
    obtain ⟨g, hg, hyg'⟩ := mem_iUnion₂.mp hyE
    have hyg : y ∈ g := (Γ'.closure_diff_V hg).subset ⟨hyg', hyV⟩
    have hgb : Disjoint g (frontier Δ) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hΔ, hb]
      refine disjoint_left.mpr fun z hz hzJ => ?_
      rcases hJp z hzJ with h | h
      · exact edge_notMem_V hg hz (h ▸ hcV)
      · exact region_subset hpR h (Or.inr (Γ'.closure_subset_U hg (subset_closure hz)))
    have hgΔ : g ⊆ Δ := by
      rcases subset_or_disjoint_of_frontier hΔ.isClosed hg.2.2.1.isConnected.isPreconnected hgb with
        h' | h'
      · exact h'
      · exact (disjoint_left.mp h' hyg hyΔ).elim
    obtain ⟨v, hv, -, -, w, -, -, hcap, -⟩ := spoke_ends hrad hS hg
    have hvcl : v ∈ closure g ∩ Γ'.V := by rw [hcap]; simp
    exact region_subset hr (hΔr (closure_minimal hgΔ hΔ.isClosed hvcl.1)) (Γ.V_subset_U hv)
  exact ⟨Δ, hΔ, hb, hfree⟩

omit [ConnectedSpace S] [T2Space S] hS in
/-- No set is an edge of both `Γ` and `Γ'`. -/
theorem edge_not_both {e : Set S} (he : e ∈ Γ.E) (he' : e ∈ Γ'.E) : False := by
  obtain ⟨y, hy⟩ := he.1
  exact disjoint_left.mp (edge_disjoint hrad he) hy (Γ'.closure_subset_U he' (subset_closure hy))

omit [ConnectedSpace S] [T2Space S] hS in
/-- An edge of `H` is an edge of `Γ` or an edge of `Γ'`. -/
theorem edge_cases {γ : Set S → I → S} {x : S} (k : halfEdges (radialUnion hrad) γ x) :
    k.1.1 ∈ Γ.E ∨ k.1.1 ∈ Γ'.E := by
  have := k.2.1
  rwa [radialUnion_E] at this

/-- Exactly one side of a corner at a vertex of `Γ` is an edge of `Γ'`. -/
theorem corner_alternates (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ')
  (hE : Γ.E.Nonempty) {γ : Set S → I → S}
    (hγ : EdgePar (radialUnion hrad) γ) {x : S} (hx : x ∈ Γ.V)
    {next : halfEdges (radialUnion hrad) γ x → halfEdges (radialUnion hrad) γ x}
    {ρ P Q : halfEdges (radialUnion hrad) γ x → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ x → I}
    (hsec : IsSectors (radialUnion hrad) γ x next ρ P W Q τ)
    (k : halfEdges (radialUnion hrad) γ x) :
    (k.1.1 ∈ Γ'.E ∧ (next k).1.1 ∈ Γ.E) ∨ (k.1.1 ∈ Γ.E ∧ (next k).1.1 ∈ Γ'.E) := by
  rcases corner_has_spoke hrad hS hmax hE hγ hx hsec k with h | h
  · refine Or.inl ⟨h, (edge_cases hrad (next k)).resolve_right fun h' => ?_⟩
    exact corner_has_edge hrad hS hγ hx hsec k h h'
  · refine Or.inr ⟨(edge_cases hrad k).resolve_right fun h' => ?_, h⟩
    exact corner_has_edge hrad hS hγ hx hsec k h' h

/-- The half-edge `a` lies next to the half-edge `φ` in the rotation, with the corner between them
in
the region `p`. -/
def IsAdj {H : Drawing S} {γ : Set S → I → S} {x : S} (next : halfEdges H γ x → halfEdges H γ x)
    (ρ : halfEdges H γ x → Set S) (p : Set S) (φ a : halfEdges H γ x) : Prop :=
  (next φ = a ∧ ρ φ = p) ∨ (next a = φ ∧ ρ a = p)

/-- A half-edge of `Γ` in the closure of a region of `H` lies next to a half-edge of `Γ'`, with the
corner between them in that region. -/
theorem exists_adj (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') (hE : Γ.E.Nonempty) {γ : Set S
  → I → S}
    (hγ : EdgePar (radialUnion hrad) γ) {x : S} (hx : x ∈ Γ.V)
    {next : halfEdges (radialUnion hrad) γ x → halfEdges (radialUnion hrad) γ x}
    {ρ P Q : halfEdges (radialUnion hrad) γ x → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ x → I}
    (hsec : IsSectors (radialUnion hrad) γ x next ρ P W Q τ)
    (i : halfEdges (radialUnion hrad) γ x) (hi : i.1.1 ∈ Γ.E) {p : Set S}
    (hp : p ∈ (radialUnion hrad).R) (hip : i.1.1 ⊆ closure p) :
    ∃ φ, φ.1.1 ∈ Γ'.E ∧ φ.1.1 ⊆ closure p ∧ IsAdj next ρ p φ i := by
  have hcor := IsSectors.corners hsec
  have hsurj := next_surjective hcor
  have hsidecl : ∀ k, k.1.1 ⊆ closure (ρ k) := fun k => by
    obtain ⟨j, hj⟩ := hsurj k
    have := IsCorners.right hcor j
    rwa [hj] at this
  obtain ⟨j, hj⟩ := hsurj i
  rcases IsCorners.sides hcor j p hp (hj ▸ hip) with h | h
  · rcases corner_alternates hrad hS hmax hE hγ hx hsec j with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact ⟨j, h₁, h ▸ hsidecl j, Or.inl ⟨hj, h.symm⟩⟩
    · exact (edge_not_both hrad hi (hj ▸ h₂)).elim
  · rw [hj] at h
    rcases corner_alternates hrad hS hmax hE hγ hx hsec i with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact (edge_not_both hrad hi h₁).elim
    · exact ⟨next i, h₂, h ▸ IsCorners.left hcor i, Or.inr ⟨rfl, h.symm⟩⟩

omit hrad hS [T2Space S] [ConnectedSpace S] in
/-- If a half-edge has different regions on its two sides, then at most one half-edge lies next to
it
with its corner in a given region. -/
theorem adj_unique {H : Drawing S} {γ : Set S → I → S} {x : S}
    {next : halfEdges H γ x → halfEdges H γ x} {ρ : halfEdges H γ x → Set S}
    (hcor : IsCorners H γ x next ρ) {φ a₁ a₂ : halfEdges H γ x} {p A₁ A₂ : Set S}
    (hA₁ : A₁ ∈ H.R) (hA₂ : A₂ ∈ H.R) (hne : A₁ ≠ A₂) (h₁ : φ.1.1 ⊆ closure A₁)
    (h₂ : φ.1.1 ⊆ closure A₂) (ha₁ : IsAdj next ρ p φ a₁) (ha₂ : IsAdj next ρ p φ a₂) :
    a₁ = a₂ := by
  have key : ∀ j, next j = φ → ρ j ≠ ρ φ := by
    rintro j rfl h
    rcases IsCorners.sides hcor j A₁ hA₁ h₁ with e₁ | e₁ <;>
      rcases IsCorners.sides hcor j A₂ hA₂ h₂ with e₂ | e₂
    all_goals first
      | exact hne (e₁.trans e₂.symm)
      | exact hne (e₁.trans (h ▸ e₂.symm))
  rcases ha₁ with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ <;> rcases ha₂ with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
  · exact h₃.symm.trans h₅
  · exact (key a₂ h₅ (h₆.trans h₄.symm)).elim
  · exact (key a₁ h₃ (h₄.trans h₆.symm)).elim
  · exact IsCorners.inj hcor (h₃.trans h₅.symm)

omit hrad [ConnectedSpace S] in
/-- Only one region has a leaf of a drawing in its closure. -/
theorem region_eq_at_leaf {H : Drawing S} {γ : Set S → I → S} (hγ : EdgePar H γ) {v : S}
    (hv : v ∈ H.V) (k : halfEdges H γ v) (hk : ∀ l : halfEdges H γ v, l = k) {r₁ r₂ : Set S}
    (hr₁ : r₁ ∈ H.R) (hr₂ : r₂ ∈ H.R) (h₁ : v ∈ closure r₁) (h₂ : v ∈ closure r₂) : r₁ = r₂ := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨⟨e, b⟩, he, hb⟩ := k
  dsimp only at he hb
  have hve : v ∈ closure e := hb ▸ end_mem_closure hγ he b
  have hother : γ e (endOf (!b)) ≠ v := by
    intro h
    have := congrArg (fun x => x.1.2) (hk ⟨(e, !b), he, h⟩)
    simp at this
  have hleaf : ∀ f ∈ H.E, f ≠ e → v ∉ closure f := by
    intro f hf hfe hvf
    obtain ⟨c, hc⟩ := exists_end_eq hγ hf hv hvf
    exact hfe (congrArg (fun x => x.1.1) (hk ⟨(f, c), hf, hc⟩))
  have hu : γ e (endOf (!b)) ∈ closure e := end_mem_closure hγ he _
  have huV := end_mem_V hγ he (!b)
  set u := γ e (endOf (!b)) with hudef
  have hcase : closure e ∩ H.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
    rcases H.edge_cond e he with ⟨x, y, hxy, hcap, hL⟩ | ⟨x, hcap, -⟩
    · have hu' : u ∈ ({x, y} : Set S) := hcap ▸ ⟨hu, huV⟩
      have hv' : v ∈ ({x, y} : Set S) := hcap ▸ ⟨hve, hv⟩
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact absurd rfl hother
      · exact ⟨hcap, hL⟩
      · exact ⟨by rw [hcap, pair_comm], GraphMinor.GM11.IsLineWithEnds.symm hL⟩
      · exact absurd rfl hother
    · have hu' : u ∈ ({x} : Set S) := hcap ▸ ⟨hu, huV⟩
      have hv' : v ∈ ({x} : Set S) := hcap ▸ ⟨hve, hv⟩
      exact absurd ((mem_singleton_iff.mp hu').trans (mem_singleton_iff.mp hv').symm) hother
  obtain ⟨Z, hZ, hvZ, hsame⟩ :=
    exists_leaf_nbhd hS H he hother hcase.1 hcase.2 hleaf isOpen_univ (mem_univ _)
  obtain ⟨x, hxZ, hx⟩ := mem_closure_iff.mp h₁ Z hZ hvZ
  obtain ⟨y, hyZ, hy⟩ := mem_closure_iff.mp h₂ Z hZ hvZ
  obtain ⟨A, hA, hdis, hxA, hyA⟩ := hsame x hxZ (region_subset hr₁ hx) y hyZ (region_subset hr₂ hy)
  exact region_eq_of_mem hr₁ hr₂ (subset_region hr₁ hA hdis hxA hx hyA.1) hy

omit [T2Space S] [ConnectedSpace S] hS in
/-- A half-edge of `H` at a vertex of `Γ'` in a region `r` belongs to an edge of `Γ'`. -/
theorem hub_half_spoke {γ : Set S → I → S} {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r)
    (i : halfEdges (radialUnion hrad) γ c) (hγ : EdgePar (radialUnion hrad) γ) : i.1.1 ∈ Γ'.E := by
  refine (edge_cases hrad i).resolve_left fun h => ?_
  have hcl : c ∈ closure i.1.1 := by
    have := end_mem_closure hγ i.2.1 i.1.2
    rwa [i.2.2] at this
  exact region_subset hr hc (Γ.closure_subset_U h hcl)

/-- The sides at the vertex of a region: the edges of `Γ'` in the closure of a region `p` of `H` are
one or two, and if two, each of them has different regions on its two sides. -/
theorem hub_sides (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') (hE : Γ.E.Nonempty) {r p : Set
  S} (hr : r ∈ Γ.R)
    (hp : p ∈ (radialUnion hrad).R) (hpr : p ⊆ r) :
    ∃ f g : Set S, f ∈ Γ'.E ∧ g ∈ Γ'.E ∧ f ⊆ closure p ∧ g ⊆ closure p ∧
      (∀ s ∈ Γ'.E, s ⊆ closure p → s = f ∨ s = g) ∧
      (f = g ∨ ∀ s, (s = f ∨ s = g) → ∃ A₁ ∈ (radialUnion hrad).R, ∃ A₂ ∈ (radialUnion hrad).R,
        A₁ ≠ A₂ ∧ s ⊆ closure A₁ ∧ s ⊆ closure A₂) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  have hne : Nonempty S := ⟨c⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  have hcH : c ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hcV
  have hcp := hub_mem_closure hrad hS hr hp hpr hc hcV
  obtain ⟨k₀, hk₀⟩ := exists_half_at_hub hrad hS hmax hE hγ hr hc hcV
  let k : halfEdges (radialUnion hrad) γ c := ⟨k₀, hk₀⟩
  have hspoke : ∀ i : halfEdges (radialUnion hrad) γ c, i.1.1 ∈ Γ'.E := fun i =>
    hub_half_spoke hrad hr hc i hγ
  have hcl : ∀ i : halfEdges (radialUnion hrad) γ c, c ∈ closure i.1.1 := fun i => by
    have := end_mem_closure hγ i.2.1 i.1.2
    rwa [i.2.2] at this
  -- An edge of `Γ'` in the closure of `p` has a half-edge at `c`.
  have hathub : ∀ s ∈ Γ'.E, s ⊆ closure p → ∃ i : halfEdges (radialUnion hrad) γ c, i.1.1 = s := by
    intro s hs hsp
    obtain ⟨v, hv, r', hr', w, hwr, hwV, hcap, hsubr⟩ := spoke_ends hrad hS hs
    obtain ⟨q, hq⟩ := hs.1
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp (hsp hq) r' (region_isOpen hr') (hsubr hq)
    obtain rfl : r' = r := region_eq_of_mem hr' hr hz' (hpr hz)
    obtain rfl : w = c := hub_unique hrad hr hc hcV hwr hwV
    have hwcl : w ∈ closure s ∩ Γ'.V := by rw [hcap]; simp
    have hsH : s ∈ (radialUnion hrad).E := by
      rw [radialUnion_E]
      exact Or.inr hs
    obtain ⟨b, hb⟩ := exists_end_eq hγ hsH hcH hwcl.1
    exact ⟨⟨(s, b), hsH, hb⟩, rfl⟩
  by_cases h2 : 2 ≤ Nat.card (halfEdges (radialUnion hrad) γ c)
  · obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS _ hγ hcH h2
    have hcor := IsSectors.corners hsec
    obtain ⟨j, rfl⟩ := IsCorners.all hcor p hp hcp
    have hsurj := next_surjective hcor
    have hinj : ∀ {a b}, a ≠ b → ρ a ≠ ρ b := fun hab =>
      corner_regions_ne hrad hS hr hc hcV hsec hab
    have hsidecl : ∀ i, i.1.1 ⊆ closure (ρ i) := fun i => by
      obtain ⟨l, hl⟩ := hsurj i
      have := IsCorners.right hcor l
      rwa [hl] at this
    obtain ⟨l, hl⟩ := hsurj j
    refine ⟨j.1.1, (next j).1.1, hspoke j, hspoke _, hsidecl j, IsCorners.left hcor j, ?_,
      Or.inr ?_⟩
    · intro s hs hsp
      obtain ⟨i, rfl⟩ := hathub s hs hsp
      obtain ⟨m, rfl⟩ := hsurj i
      rcases IsCorners.sides hcor m (ρ j) (IsCorners.region hcor j) hsp with h | h
      · by_cases hmj : j = m
        · subst hmj
          exact Or.inr rfl
        · exact (hinj hmj h).elim
      · by_cases hmj : j = next m
        · rw [← hmj]
          exact Or.inl rfl
        · exact (hinj hmj h).elim
    · rintro s (rfl | rfl)
      · refine ⟨ρ l, IsCorners.region hcor l, ρ j, IsCorners.region hcor j, ?_, ?_, hsidecl j⟩
        · refine hinj fun h => IsSectors.next_ne hsec l (hl.trans h.symm)
        · have := IsCorners.left hcor l
          rwa [hl] at this
      · exact ⟨ρ j, IsCorners.region hcor j, ρ (next j), IsCorners.region hcor _,
          hinj (IsSectors.next_ne hsec j).symm, IsCorners.left hcor j, IsCorners.right hcor j⟩
  · have hsingle : ∀ l : halfEdges (radialUnion hrad) γ c, l = k := by
      intro l
      by_contra hl
      apply h2
      have hfin := finite_halfEdges (radialUnion hrad) γ c
      have hne' : l.1 ≠ k.1 := fun h => hl (Subtype.ext h)
      exact (one_lt_ncard hfin).mpr ⟨l.1, l.2, k.1, k.2, hne'⟩
    obtain ⟨A, hA, hkA⟩ := exists_region_incident hS k.2.1
    have hcA : c ∈ closure A := closure_minimal hkA isClosed_closure (hcl k)
    obtain rfl : A = p := region_eq_at_leaf hS hγ hcH k hsingle hA hp hcA hcp
    refine ⟨k.1.1, k.1.1, hspoke k, hspoke k, hkA, hkA, ?_, Or.inl rfl⟩
    intro s hs hsp
    obtain ⟨i, rfl⟩ := hathub s hs hsp
    exact Or.inl (by rw [hsingle i])

end GraphMinor.GM11
