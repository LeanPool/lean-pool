/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialTwoCell

/-!
# The corners at the vertex of a region

Let `Γ'` be a radial drawing of a 2-cell drawing `Γ`, let `r` be a region of `Γ`, and let `c` be the
vertex
of `Γ'` in `r`. Suppose that no edge of `Γ` is a loop. Each corner at `c` lies in a region `p` of `Γ
∪ Γ'`,
and we show that `p` is bounded by the two spokes of the corner and one edge of `Γ` (`corner_data`).
In a
sphere, the closure of `p` is a closed disc (`isClosedDisc_closure_corner`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] {Γ Γ' : Drawing S} [T2Space S] [ConnectedSpace S]
  (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S)
  (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ')

include hrad hS

omit [ConnectedSpace S] in
/-- A spoke in the closure of a region of `Γ ∪ Γ'` inside `r` has a half-edge at the vertex of `r`.
-/
theorem spoke_at_hub {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) {r p s : Set S}
  (hr : r ∈ Γ.R)
    {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) (_hp : p ∈ (radialUnion hrad).R) (hpr : p ⊆ r)
      (hs : s ∈ Γ'.E)
    (hsp : s ⊆ closure p) : ∃ k : halfEdges (radialUnion hrad) γ c, k.1.1 = s := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨v, hv, r', hr', w, hwr, hwV, hcap, hsub⟩ := spoke_ends hrad hS hs
  obtain ⟨y, hy⟩ := hs.1
  obtain ⟨z, hz, hzp⟩ := mem_closure_iff.mp (hsp hy) r' (region_isOpen hr') (hsub hy)
  obtain rfl : r' = r := region_eq_of_mem hr' hr hz (hpr hzp)
  have hwc : w = c := hub_unique hrad hr hc hcV hwr hwV
  subst hwc
  have hcs : w ∈ closure s := by
    have : w ∈ closure s ∩ Γ'.V := by rw [hcap]; simp
    exact this.1
  have hsH : s ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr hs
  have hcH : w ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hcV
  obtain ⟨b, hb⟩ := exists_end_eq hγ hsH hcH hcs
  exact ⟨⟨(s, b), hsH, hb⟩, rfl⟩

omit [T2Space S] [ConnectedSpace S] in
/-- A spoke at the vertex of a region joins it to a vertex of `Γ`. -/
theorem spoke_end {r s : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) (hs : s ∈ Γ'.E)
    (hcs : c ∈ closure s) : ∃ a ∈ Γ.V, closure s ∩ Γ'.V = {a, c} := by
  obtain ⟨v, hv, r', hr', w, hwr, hwV, hcap, hsub⟩ := spoke_ends hrad hS hs
  have hcv : c ≠ v := fun h => region_subset hr hc (Γ.V_subset_U (h ▸ hv))
  have hmem : c ∈ closure s ∩ Γ'.V := ⟨hcs, hcV⟩
  rw [hcap] at hmem
  rcases hmem with h | h
  · exact (hcv h).elim
  · have h' : c = w := h
    exact ⟨v, hv, by rw [hcap, h']⟩

omit [ConnectedSpace S] in
/-- A half-edge at the vertex of `r` whose spoke lies in the closure of a corner is a side of the
corner. -/
theorem corner_mem {γ : Set S → I → S} {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r)
  (hcV : c ∈ Γ'.V)
    {next : halfEdges (radialUnion hrad) γ c → halfEdges (radialUnion hrad) γ c}
    {ρ P Q : halfEdges (radialUnion hrad) γ c → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ c → I}
    (hsec : IsSectors (radialUnion hrad) γ c next ρ P W Q τ)
    {k k' : halfEdges (radialUnion hrad) γ c} (h : k'.1.1 ⊆ closure (ρ k)) : k' = k ∨ k' = next k
      := by
  have hcor := IsSectors.corners hsec
  obtain ⟨l, rfl⟩ := next_surjective hcor k'
  rcases IsCorners.sides hcor l (ρ k) (IsCorners.region hcor k) h with h₁ | h₁
  · by_contra hn
    push Not at hn
    by_cases hkl : k = l
    · exact hn.2 (hkl ▸ rfl)
    · exact corner_regions_ne hrad hS hr hc hcV hsec hkl h₁
  · by_contra hn
    push Not at hn
    exact corner_regions_ne hrad hS hr hc hcV hsec (Ne.symm hn.1) h₁

include hmax in
/-- **A corner at the vertex of `r`.** Its region is bounded by its two spokes and one edge of `Γ`.
-/
theorem corner_data (hE : Γ.E.Nonempty)
    (hloop : ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y})
    {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) {r : Set S} (hr : r ∈ Γ.R) {c : S}
      (hc : c ∈ r)
    (hcV : c ∈ Γ'.V)
    {next : halfEdges (radialUnion hrad) γ c → halfEdges (radialUnion hrad) γ c}
    {ρ P Q : halfEdges (radialUnion hrad) γ c → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ c → I}
    (hsec : IsSectors (radialUnion hrad) γ c next ρ P W Q τ)
    (hρr : ∀ k, ρ k ⊆ r) (k : halfEdges (radialUnion hrad) γ c) :
    ∃ e ∈ Γ.E, ∃ a b, a ≠ b ∧ a ∈ Γ.V ∧ b ∈ Γ.V ∧ closure e ∩ Γ.V = {a, b} ∧ e ⊆ closure (ρ k) ∧
      closure k.1.1 ∩ Γ'.V = {a, c} ∧ closure (next k).1.1 ∩ Γ'.V = {b, c} ∧
      frontier (ρ k) = closure k.1.1 ∪ closure (next k).1.1 ∪ closure e := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcor := IsSectors.corners hsec
  have hp : ρ k ∈ (radialUnion hrad).R := IsCorners.region hcor k
  have hspoke : ∀ i : halfEdges (radialUnion hrad) γ c, i.1.1 ∈ Γ'.E := fun i =>
    hub_half_spoke hrad hr hc i hγ
  have hhalf : ∀ i : halfEdges (radialUnion hrad) γ c, c ∈ closure i.1.1 := fun i => by
    have := end_mem_closure hγ i.2.1 i.1.2
    rwa [i.2.2] at this
  have hsurj := next_surjective hcor
  have hkcl : k.1.1 ⊆ closure (ρ k) := by
    obtain ⟨l, hl⟩ := hsurj k
    have := IsCorners.right hcor l
    rwa [hl] at this
  have hnkcl : (next k).1.1 ⊆ closure (ρ k) := IsCorners.left hcor k
  obtain ⟨a, ha, hcapa⟩ := spoke_end hrad hS hr hc hcV (hspoke k) (hhalf k)
  obtain ⟨b, hb, hcapb⟩ := spoke_end hrad hS hr hc hcV (hspoke (next k)) (hhalf (next k))
  obtain ⟨e, he, hep, hu, hv⟩ := face_edge hrad hS hmax hE hp
  obtain ⟨x, y, hxy, hcap⟩ := hloop e he
  have heH : e ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he
  have hsec' : ∀ x : Γ.V, ∃ next ρ P W Q τ, IsSectors (radialUnion hrad) γ x.1 next ρ P W Q τ :=
    fun x => exists_sectors hS _ hγ
      (by rw [radialUnion_V]; exact radial_V hrad x.2) (two_half_edges hrad hS hmax hE hγ x.2)
  -- Each end of `e` is an end of a side of the corner.
  have hend : ∀ z, z ∈ closure e ∩ Γ.V → z = a ∨ z = b := by
    rintro z ⟨hze, hzV⟩
    have hzH : z ∈ (radialUnion hrad).V := by
      rw [radialUnion_V]
      exact radial_V hrad hzV
    obtain ⟨bb, hbb⟩ := exists_end_eq hγ heH hzH hze
    obtain ⟨_, _, _, _, _, _, hs⟩ := hsec' ⟨z, hzV⟩
    obtain ⟨φ, hφ, hφp, -⟩ := exists_adj hrad hS hmax hE hγ hzV hs ⟨(e, bb), heH, hbb⟩ he hp hep
    obtain ⟨k', hk'⟩ := spoke_at_hub hrad hS hγ hr hc hcV hp (hρr k) hφ hφp
    have hzφ : z ∈ closure φ.1.1 := by
      have := end_mem_closure hγ φ.2.1 φ.1.2
      rwa [φ.2.2] at this
    have hzc : z ≠ c := fun h => region_subset hr hc (Γ.V_subset_U (h ▸ hzV))
    rw [← hk'] at hzφ
    rcases corner_mem hrad hS hr hc hcV hsec (hk' ▸ hφp) with rfl | rfl
    · have : z ∈ closure k'.1.1 ∩ Γ'.V := ⟨hzφ, radial_V hrad hzV⟩
      rw [hcapa] at this
      exact Or.inl (this.resolve_right hzc)
    · have : z ∈ closure (next k).1.1 ∩ Γ'.V := ⟨hzφ, radial_V hrad hzV⟩
      rw [hcapb] at this
      exact Or.inr (this.resolve_right hzc)
  have hxm : x ∈ closure e ∩ Γ.V := by rw [hcap]; simp
  have hym : y ∈ closure e ∩ Γ.V := by rw [hcap]; simp
  have hab : a ≠ b := by
    rintro rfl
    have h₁ := (hend x hxm).elim id id
    have h₂ := (hend y hym).elim id id
    exact hxy (h₁.trans h₂.symm)
  have hcape : closure e ∩ Γ.V = {a, b} := by
    rw [hcap]
    rcases hend x hxm with rfl | rfl <;> rcases hend y hym with rfl | rfl
    · exact (hxy rfl).elim
    · rfl
    · exact pair_comm _ _
    · exact (hxy rfl).elim
  refine ⟨e, he, a, b, hab, ha, hb, hcape, hep, hcapa, hcapb, ?_⟩
  have hclosed : IsClosed (closure k.1.1 ∪ closure (next k).1.1 ∪ closure e) :=
    (isClosed_closure.union isClosed_closure).union isClosed_closure
  rw [(region_isOpen hp).frontier_eq]
  apply subset_antisymm
  · rintro z ⟨hzcl, hzp⟩
    have hzU : z ∈ (radialUnion hrad).U := by
      by_contra hn
      obtain ⟨p', hp', hzp'⟩ := exists_region_of_notMem hn
      obtain ⟨w, hw', hw⟩ := mem_closure_iff.mp hzcl p' (region_isOpen hp') hzp'
      exact hzp (region_eq_of_mem hp' hp hw' hw ▸ hzp')
    by_cases hzV : z ∈ (radialUnion hrad).V
    · rw [radialUnion_V] at hzV
      by_cases hzΓ : z ∈ Γ.V
      · have hmem : z ∈ closure e ∩ Γ.V := ⟨hv z hzΓ hzcl, hzΓ⟩
        exact Or.inr hmem.1
      · obtain ⟨r', hr', hzr'⟩ := hrad.2.2.2.2.1 z ⟨hzV, hzΓ⟩
        obtain ⟨w, hw', hw⟩ := mem_closure_iff.mp hzcl r' (region_isOpen hr') hzr'
        obtain rfl : r' = r := region_eq_of_mem hr' hr hw' (hρr k hw)
        have hzc : z = c := hub_unique hrad hr hc hcV hzr' hzV
        exact Or.inl (Or.inl (hzc ▸ hhalf k))
    · rw [(radialUnion hrad).U_eq] at hzU
      rcases hzU with h | h
      · exact (hzV h).elim
      obtain ⟨g, hg, hzg'⟩ := mem_iUnion₂.mp h
      have hzg : z ∈ g := (radialUnion hrad).closure_diff_V hg ▸ ⟨hzg', hzV⟩
      have hgp : g ⊆ closure (ρ k) :=
        edge_subset_closure_of_incident hS hg hp ⟨z, hzg, hzcl⟩
      rw [radialUnion_E] at hg
      rcases hg with hg | hg
      · have := hu g hg hgp
        subst this
        exact Or.inr hzg'
      · obtain ⟨k', hk'⟩ := spoke_at_hub hrad hS hγ hr hc hcV hp (hρr k) hg hgp
        rcases corner_mem hrad hS hr hc hcV hsec (hk' ▸ hgp) with rfl | rfl
        · exact Or.inl (Or.inl (hk' ▸ hzg'))
        · exact Or.inl (Or.inr (hk' ▸ hzg'))
  · have hdis : ∀ {g : Set S}, g ∈ (radialUnion hrad).E → closure g ⊆ (radialUnion hrad).U :=
      fun hg => (radialUnion hrad).closure_subset_U hg
    have hk₁ : k.1.1 ∈ (radialUnion hrad).E := k.2.1
    have hk₂ : (next k).1.1 ∈ (radialUnion hrad).E := (next k).2.1
    rintro z ((h | h) | h)
    · exact ⟨closure_minimal hkcl isClosed_closure h, fun hz => region_subset hp hz (hdis hk₁ h)⟩
    · exact ⟨closure_minimal hnkcl isClosed_closure h, fun hz => region_subset hp hz (hdis hk₂ h)⟩
    · exact ⟨closure_minimal hep isClosed_closure h, fun hz => region_subset hp hz (hdis heH h)⟩

include hmax in
/-- **In a sphere, the closure of a corner is a closed disc.** -/
theorem isClosedDisc_closure_corner (hsph : IsSphere S) (hE : Γ.E.Nonempty)
    (hloop : ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y})
    {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) {r : Set S} (hr : r ∈ Γ.R) {c : S}
      (hc : c ∈ r)
    (hcV : c ∈ Γ'.V)
    {next : halfEdges (radialUnion hrad) γ c → halfEdges (radialUnion hrad) γ c}
    {ρ P Q : halfEdges (radialUnion hrad) γ c → Set S} {W : Set S}
    {τ : halfEdges (radialUnion hrad) γ c → I}
    (hsec : IsSectors (radialUnion hrad) γ c next ρ P W Q τ)
    (hρr : ∀ k, ρ k ⊆ r) (k : halfEdges (radialUnion hrad) γ c) :
    IsClosedDisc (closure (ρ k)) ∧ discInt (closure (ρ k)) = ρ k ∧
      discBd (closure (ρ k)) = frontier (ρ k) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcor := IsSectors.corners hsec
  have hp : ρ k ∈ (radialUnion hrad).R := IsCorners.region hcor k
  obtain ⟨e, he, a, b, hab, ha, hb, hcape, hep, hcapa, hcapb, hfr⟩ :=
    corner_data hrad hS hmax hE hloop hγ hr hc hcV hsec hρr k
  have hspoke : ∀ i : halfEdges (radialUnion hrad) γ c, i.1.1 ∈ Γ'.E := fun i =>
    hub_half_spoke hrad hr hc i hγ
  have hca : c ≠ a := fun h => region_subset hr hc (Γ.V_subset_U (h ▸ ha))
  have hcb : c ≠ b := fun h => region_subset hr hc (Γ.V_subset_U (h ▸ hb))
  have hL₁ : IsLineWithEnds (closure k.1.1) c a :=
    isLine_closure (hspoke k) hca (by rw [hcapa, pair_comm])
  have hL₂ : IsLineWithEnds (closure (next k).1.1) c b :=
    isLine_closure (hspoke (next k)) hcb (by rw [hcapb, pair_comm])
  have hL₃ : IsLineWithEnds (closure e) a b := isLine_closure he hab hcape
  have hne : k.1.1 ≠ (next k).1.1 := by
    intro h
    rw [← h, hcapa] at hcapb
    have : a ∈ ({b, c} : Set S) := hcapb ▸ mem_insert a {c}
    rcases this with h₁ | h₁
    · exact hab h₁
    · exact hca h₁.symm
  have h₁₂ : closure k.1.1 ∩ closure (next k).1.1 = {c} := by
    apply subset_antisymm
    · rintro z ⟨hz₁, hz₂⟩
      have hzV := closure_inter_subset_V (hspoke k) (hspoke (next k)) hne ⟨hz₁, hz₂⟩
      have m₁ : z ∈ closure k.1.1 ∩ Γ'.V := ⟨hz₁, hzV⟩
      have m₂ : z ∈ closure (next k).1.1 ∩ Γ'.V := ⟨hz₂, hzV⟩
      rw [hcapa] at m₁
      rw [hcapb] at m₂
      rcases m₁ with rfl | h
      · rcases m₂ with h | h
        · exact (hab h).elim
        · exact h
      · exact h
    · rintro z rfl
      have h₁ : z ∈ closure k.1.1 ∩ Γ'.V := by rw [hcapa]; simp
      have h₂ : z ∈ closure (next k).1.1 ∩ Γ'.V := by rw [hcapb]; simp
      exact ⟨h₁.1, h₂.1⟩
  have hL₄ : IsLineWithEnds (closure k.1.1 ∪ closure (next k).1.1) a b :=
    IsLineWithEnds.union hL₁ hL₂ h₁₂
  have hsp₃ : ∀ i : halfEdges (radialUnion hrad) γ c, closure i.1.1 ∩ closure e ⊆ Γ.V := by
    rintro i z ⟨hz₁, hz₂⟩
    have h₁ : Γ.U ∩ Γ'.U = Γ.V := radial_inter hrad
    exact h₁ ▸ (⟨Γ.closure_subset_U he hz₂, Γ'.closure_subset_U (hspoke i) hz₁⟩ : z ∈ Γ.U ∩ Γ'.U)
  have hcap₃ : (closure k.1.1 ∪ closure (next k).1.1) ∩ closure e ⊆ {a, b} := by
    rintro z ⟨hz | hz, hze⟩
    · have hzV := hsp₃ k ⟨hz, hze⟩
      exact (hcape ▸ (⟨hze, hzV⟩ : z ∈ closure e ∩ Γ.V))
    · have hzV := hsp₃ (next k) ⟨hz, hze⟩
      exact (hcape ▸ (⟨hze, hzV⟩ : z ∈ closure e ∩ Γ.V))
  have hF : IsOArc (frontier (ρ k)) := hfr ▸ isOArc_union hL₄ hL₃ hcap₃
  obtain ⟨Δ₁, Δ₂, -, h₁, h₂, hb₁, hb₂, -, -, hcomp, -⟩ := sphere_disc S hsph _ hF
  have hpo : IsOpen (ρ k) := region_isOpen hp
  have hpdis : ρ k ⊆ univ \ frontier (ρ k) := fun x hx => ⟨trivial, fun h => by
    rw [hpo.frontier_eq] at h
    exact h.2 hx⟩
  obtain ⟨x₀, hx₀⟩ := region_nonempty hp
  have hx₁ := hpdis hx₀
  have hcompx : connectedComponentIn (univ \ frontier (ρ k)) x₀ ∈
      componentsIn (univ \ frontier (ρ k)) := ⟨x₀, hx₁, rfl⟩
  have hsub : ρ k ⊆ connectedComponentIn (univ \ frontier (ρ k)) x₀ :=
    (region_isPreconnected hp).subset_connectedComponentIn hx₀ hpdis
  rw [hcomp] at hcompx
  -- The region is all of one side of the frontier.
  have key : ∀ Δ, IsClosedDisc Δ → discBd Δ = frontier (ρ k) → Δ \ frontier (ρ k) ∈ componentsIn
    (univ \ frontier (ρ k)) →
      ρ k ⊆ Δ \ frontier (ρ k) → IsClosedDisc (closure (ρ k)) ∧ discInt (closure (ρ k)) = ρ k ∧
      discBd (closure (ρ k)) = frontier (ρ k) := by
    intro Δ hΔ hbΔ hΔc hsubΔ
    have hconn : IsPreconnected (Δ \ frontier (ρ k)) := by
      rw [← hbΔ]
      exact hΔ.isPreconnected_discInt
    have hopenΔ : IsOpen (Δ \ frontier (ρ k)) := by
      have := hΔ.isOpen_discInt fun x => (hS.2.2 x).isManifoldPoint
      rwa [discInt, hbΔ] at this
    have heq : ρ k = Δ \ frontier (ρ k) := by
      apply subset_antisymm hsubΔ
      intro z hz
      by_contra hzp
      have hO : IsOpen (closure (ρ k))ᶜ := isClosed_closure.isOpen_compl
      have hzO : z ∈ (closure (ρ k))ᶜ := fun h => hz.2 ⟨h, by rw [hpo.interior_eq]; exact hzp⟩
      have hd : Disjoint (ρ k) (closure (ρ k))ᶜ := disjoint_left.mpr fun y hy h => h
        (subset_closure hy)
      have hcov : Δ \ frontier (ρ k) ⊆ ρ k ∪ (closure (ρ k))ᶜ := by
        intro y hy
        by_cases hyp : y ∈ ρ k
        · exact Or.inl hyp
        · exact Or.inr fun h => hy.2 ⟨h, by rw [hpo.interior_eq]; exact hyp⟩
      have := hconn.subset_left_of_subset_union hpo hO hd hcov ⟨x₀, hsubΔ hx₀, hx₀⟩ hz
      exact hzp this
    have hcl : closure (ρ k) = Δ := by
      apply subset_antisymm
      · exact closure_minimal (hsubΔ.trans sdiff_subset) hΔ.isClosed
      · have h₃ := hΔ.subset_closure_discInt
        rw [discInt, hbΔ, ← heq] at h₃
        exact h₃
    rw [hcl]
    exact ⟨hΔ, by rw [discInt, hbΔ]; exact heq.symm, hbΔ⟩
  rcases hcompx with h | h
  · rw [h] at hsub
    exact key Δ₁ h₁ hb₁ (by rw [hcomp]; simp) hsub
  · rw [show connectedComponentIn (univ \ frontier (ρ k)) x₀ = Δ₂ \ frontier (ρ k) from h] at hsub
    exact key Δ₂ h₂ hb₂ (by rw [hcomp]; simp) hsub

include hmax in
/-- The vertex of a region has at least two half-edges, if no edge of `Γ` is a loop. -/
theorem hub_two_halves (hE : Γ.E.Nonempty)
    (hloop : ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y})
    {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ) {r : Set S} (hr : r ∈ Γ.R) {c : S}
      (hc : c ∈ r)
    (hcV : c ∈ Γ'.V) : 2 ≤ Nat.card (halfEdges (radialUnion hrad) γ c) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨z, hzr, hzU⟩ := exists_notMem_U (Γ := radialUnion hrad) hS
    (region_isOpen hr) (region_nonempty hr)
  obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
  have hpr : p ⊆ r := by
    obtain ⟨r', hr', hpr'⟩ := exists_region_of_sub hrad hp
    obtain rfl := region_eq_of_mem hr' hr (hpr' hzp) hzr
    exact hpr'
  obtain ⟨e, he, hep, -, -⟩ := face_edge hrad hS hmax hE hp
  obtain ⟨x, y, hxy, hcap⟩ := hloop e he
  have heH : e ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he
  have hsec' : ∀ x : Γ.V, ∃ next ρ P W Q τ, IsSectors (radialUnion hrad) γ x.1 next ρ P W Q τ :=
    fun x => exists_sectors hS _ hγ
      (by rw [radialUnion_V]; exact radial_V hrad x.2) (two_half_edges hrad hS hmax hE hγ x.2)
  have hend : ∀ z, z ∈ closure e ∩ Γ.V → ∃ k : halfEdges (radialUnion hrad) γ c, z ∈ closure k.1.1
    := by
    rintro z ⟨hze, hzV⟩
    have hzH : z ∈ (radialUnion hrad).V := by
      rw [radialUnion_V]
      exact radial_V hrad hzV
    obtain ⟨bb, hbb⟩ := exists_end_eq hγ heH hzH hze
    obtain ⟨_, _, _, _, _, _, hs⟩ := hsec' ⟨z, hzV⟩
    obtain ⟨φ, hφ, hφp, -⟩ := exists_adj hrad hS hmax hE hγ hzV hs ⟨(e, bb), heH, hbb⟩ he hp hep
    obtain ⟨k', hk'⟩ := spoke_at_hub hrad hS hγ hr hc hcV hp hpr hφ hφp
    have hzφ : z ∈ closure φ.1.1 := by
      have := end_mem_closure hγ φ.2.1 φ.1.2
      rwa [φ.2.2] at this
    exact ⟨k', hk' ▸ hzφ⟩
  have hxm : x ∈ closure e ∩ Γ.V := by rw [hcap]; simp
  have hym : y ∈ closure e ∩ Γ.V := by rw [hcap]; simp
  obtain ⟨k₁, hk₁⟩ := hend x hxm
  obtain ⟨k₂, hk₂⟩ := hend y hym
  have hne : k₁ ≠ k₂ := by
    rintro rfl
    have hcs : c ∈ closure k₁.1.1 := by
      have := end_mem_closure hγ k₁.2.1 k₁.1.2
      rwa [k₁.2.2] at this
    obtain ⟨a, ha, hcapa⟩ := spoke_end hrad hS hr hc hcV (hub_half_spoke hrad hr hc k₁ hγ) hcs
    have hxc : x ≠ c := fun h => region_subset hr hc (Γ.V_subset_U (h ▸ hxm.2))
    have hyc : y ≠ c := fun h => region_subset hr hc (Γ.V_subset_U (h ▸ hym.2))
    have h₁ : x ∈ closure k₁.1.1 ∩ Γ'.V := ⟨hk₁, radial_V hrad hxm.2⟩
    have h₂ : y ∈ closure k₁.1.1 ∩ Γ'.V := ⟨hk₂, radial_V hrad hym.2⟩
    rw [hcapa] at h₁ h₂
    exact hxy ((h₁.resolve_right hxc).trans (h₂.resolve_right hyc).symm)
  have hfin : Finite (halfEdges (radialUnion hrad) γ c) := (finite_halfEdges _ _ _).to_subtype
  have hnt : Nontrivial (halfEdges (radialUnion hrad) γ c) := ⟨k₁, k₂, hne⟩
  exact Finite.one_lt_card

end GraphMinor.GM11
