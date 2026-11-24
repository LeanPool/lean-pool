/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialFaces
public import LeanPool.GraphMinor.GM11.Section6

/-!
# Each region of a radial drawing contains a unique edge

This file finishes the proof of the sentence of Graph Minors XI (Section 3, page 75), for a radial
drawing `Γ'` of a 2-cell drawing `Γ` with an edge: every region of `Γ'` contains a unique edge of
`Γ`.
More precisely, `regionFacts_of_radial` gives `RegionFacts Γ Γ'`, which also says that a vertex of
`Γ`
in the closure of a region of `Γ'` is an end of its edge.

Let `H` be the union of `Γ` and `Γ'`. First, the closure of each region of `H` contains exactly one
edge of `Γ` (`face_edge`). The reason is a count of half-edges. Each half-edge of `Γ` in the closure
of a region `p` of `H` lies next to an edge of `Γ'` in the rotation at its end, with the corner
between
them in `p`, and `p` has at most two such positions. Then each region of `Γ'` is the union of one
edge
of `Γ` with the regions of `H` whose closure contains that edge.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] {Γ Γ' : Drawing S} [T2Space S] [ConnectedSpace S]
  (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S)
  (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ')

include hrad hS

include hmax in
/-- A vertex of `Γ` has at least two half-edges in `H`: one of `Γ` and one of `Γ'`. -/
theorem two_half_edges (hE : Γ.E.Nonempty) {γ : Set S → I → S} (hγ : EdgePar (radialUnion hrad) γ)
    {x : S} (hx : x ∈ Γ.V) : 2 ≤ Nat.card (halfEdges (radialUnion hrad) γ x) := by
  obtain ⟨e₀, he₀, hxe₀⟩ := exists_edge_at hrad hS hE hx
  obtain ⟨r, hr, he₀r⟩ := exists_region_incident hS he₀
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  obtain ⟨h, hh, hcap⟩ := exists_spoke_at hrad hmax hS hE hr hc hcV hx
    (closure_minimal he₀r isClosed_closure hxe₀)
  have hxH : x ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact radial_V hrad hx
  have he₀H : e₀ ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he₀
  have hhH : h ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr hh
  have hxh : x ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
  obtain ⟨b₁, hb₁⟩ := exists_end_eq hγ he₀H hxH hxe₀
  obtain ⟨b₂, hb₂⟩ := exists_end_eq hγ hhH hxH hxh.1
  have hfin := finite_halfEdges (radialUnion hrad) γ x
  refine (one_lt_ncard hfin).mpr ⟨(e₀, b₁), ⟨he₀H, hb₁⟩, (h, b₂), ⟨hhH, hb₂⟩, fun he => ?_⟩
  have he' : e₀ = h := congrArg Prod.fst he
  exact edge_not_both hrad he₀ (he' ▸ hh)

omit [ConnectedSpace S] in
/-- An edge of `Γ'` has just one end in `V(Γ)`, and just one half-edge there. -/
theorem spoke_half_unique {s : Set S} (hs : s ∈ Γ'.E) {γ : Set S → I → S}
    (hγ : EdgePar (radialUnion hrad) γ) :
    ∃ x : Γ.V, ∃ φ : halfEdges (radialUnion hrad) γ x.1, φ.1.1 = s ∧
      ∀ (x' : Γ.V) (φ' : halfEdges (radialUnion hrad) γ x'.1), φ'.1.1 = s → x' = x ∧ φ'.1 = φ.1
        := by
  obtain ⟨v, hv, r, hr, w, hwr, hwV, hcap, -⟩ := spoke_ends hrad hS hs
  have hvcl : v ∈ closure s ∩ Γ'.V := by rw [hcap]; simp
  have hwcl : w ∈ closure s ∩ Γ'.V := by rw [hcap]; simp
  have hsH : s ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr hs
  have hvH : v ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hvcl.2
  have hwH : w ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hwV
  obtain ⟨b, hb⟩ := exists_end_eq hγ hsH hvH hvcl.1
  obtain ⟨b', hb'⟩ := exists_end_eq hγ hsH hwH hwcl.1
  have hvw : v ≠ w := fun h => notMem_V_of_mem_region hr hwr (h ▸ hv)
  have hbb : b' = !b := by
    cases b <;> cases b' <;> first | rfl | exact (hvw (hb.symm.trans hb')).elim
  refine ⟨⟨v, hv⟩, ⟨(s, b), hsH, hb⟩, rfl, ?_⟩
  rintro ⟨x', hx'⟩ ⟨⟨s', c⟩, hs', hc⟩ rfl
  dsimp only at hs' hc ⊢
  have hm : x' ∈ ({v, w} : Set S) := hcap ▸ ⟨hc ▸ end_mem_closure hγ hs' c, radial_V hrad hx'⟩
  have hx'v : x' = v := by
    rcases hm with h | h
    · exact h
    · exact (notMem_V_of_mem_region hr hwr (h ▸ hx')).elim
  subst hx'v
  refine ⟨rfl, ?_⟩
  have hcb : c = b := by
    subst hbb
    cases b <;> cases c <;> first | rfl | exact (hvw (hc.symm.trans hb')).elim
  rw [hcb]

include hmax in
/-- **The closure of each region of `H` contains exactly one edge of `Γ`.** It also contains no
vertex
of `Γ` other than the ends of that edge. -/
theorem face_edge (hE : Γ.E.Nonempty) {p : Set S} (hp : p ∈ (radialUnion hrad).R) :
    ∃ e ∈ Γ.E, e ⊆ closure p ∧ (∀ e' ∈ Γ.E, e' ⊆ closure p → e' = e) ∧
      ∀ v ∈ Γ.V, v ∈ closure p → v ∈ closure e := by
  classical
  obtain ⟨y₀, -⟩ := region_nonempty hp
  have hne : Nonempty S := ⟨y₀⟩
  obtain ⟨r, hr, hpr⟩ := exists_region_of_sub hrad hp
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  obtain ⟨f, g, hf, hg, hfp, hgp, hall, hsides⟩ := hub_sides hrad hS hmax hE hr hp hpr
  have hsec : ∀ x : Γ.V, ∃ next ρ P W Q τ, IsSectors (radialUnion hrad) γ x.1 next ρ P W Q τ :=
    fun x => exists_sectors hS _ hγ
      (by rw [radialUnion_V]; exact radial_V hrad x.2) (two_half_edges hrad hS hmax hE hγ x.2)
  choose next ρ P W Q τ hs using hsec
  have hcor : ∀ x, IsCorners (radialUnion hrad) γ x.1 (next x) (ρ x) := fun x =>
    IsSectors.corners (hs x)
  have hsurj : ∀ x, Function.Surjective (next x) := fun x => next_surjective (hcor x)
  have hsidecl : ∀ x i, i.1.1 ⊆ closure (ρ x i) := fun x i => by
    obtain ⟨l, hl⟩ := hsurj x i
    have := IsCorners.right (hcor x) l
    rwa [hl] at this
  -- The half-edges of `Γ` next to the edge `s` of `Γ'`, with the corner in `p`.
  let Cand : Set S → Set S × Bool → Prop := fun s a =>
    ∃ (x : Γ.V) (φ i : halfEdges (radialUnion hrad) γ x.1), φ.1.1 = s ∧ i.1 = a ∧
      IsAdj (next x) (ρ x) p φ i
  have hcand : ∀ e ∈ Γ.E, e ⊆ closure p → ∀ b, Cand f (e, b) ∨ Cand g (e, b) := by
    intro e he hep b
    have heH : e ∈ (radialUnion hrad).E := by
      rw [radialUnion_E]
      exact Or.inl he
    have hxU : γ e (endOf b) ∈ Γ.U := Γ.closure_subset_U he (end_mem_closure hγ heH b)
    have hxV' : γ e (endOf b) ∈ Γ'.V := by
      have := end_mem_V hγ heH b
      rwa [radialUnion_V] at this
    have hxV : γ e (endOf b) ∈ Γ.V :=
      radial_inter hrad ▸ ⟨hxU, Γ'.V_subset_U hxV'⟩
    let x : Γ.V := ⟨_, hxV⟩
    let i : halfEdges (radialUnion hrad) γ x.1 := ⟨(e, b), heH, rfl⟩
    obtain ⟨φ, hφ, hφp, hadj⟩ := exists_adj hrad hS hmax hE hγ hxV (hs x) i he hp hep
    rcases hall _ hφ hφp with h | h
    · exact Or.inl ⟨x, φ, i, h, rfl, hadj⟩
    · exact Or.inr ⟨x, φ, i, h, rfl, hadj⟩
  have hunique : ∀ s ∈ Γ'.E, s ⊆ closure p → (∃ A₁ ∈ (radialUnion hrad).R,
      ∃ A₂ ∈ (radialUnion hrad).R, A₁ ≠ A₂ ∧ s ⊆ closure A₁ ∧ s ⊆ closure A₂) →
      ∃ b, ∀ a, Cand s a → a = b := by
    rintro s hs' - ⟨A₁, hA₁, A₂, hA₂, hne', h₁, h₂⟩
    by_cases hex : ∃ a, Cand s a
    · obtain ⟨a, x, φ, i, hφ, hia, hadj⟩ := hex
      refine ⟨a, ?_⟩
      rintro a' ⟨x', φ', i', hφ', hia', hadj'⟩
      obtain ⟨x₀, φ₀, -, huniq⟩ := spoke_half_unique hrad hS hs' hγ
      obtain ⟨e₁, e₂⟩ := huniq x φ hφ
      obtain ⟨e₃, e₄⟩ := huniq x' φ' hφ'
      subst e₁
      subst e₃
      have hφφ : φ' = φ := Subtype.ext (e₄.trans e₂.symm)
      subst hφφ
      rw [← hia, ← hia']
      exact congrArg Subtype.val (adj_unique (hcor _) hA₁ hA₂ hne' (hφ ▸ h₁) (hφ ▸ h₂) hadj' hadj)
    · exact ⟨(∅, false), fun a ha => (hex ⟨a, ha⟩).elim⟩
  have htwo : ∀ s ∈ Γ'.E, ∃ b₁ b₂, ∀ a, Cand s a → a = b₁ ∨ a = b₂ := by
    intro s hs'
    obtain ⟨x, φ, hφ, huniq⟩ := spoke_half_unique hrad hS hs' hγ
    refine ⟨(next x φ).1, (Function.surjInv (hsurj x) φ).1, ?_⟩
    rintro a ⟨x', φ', i, hφ', hia, hadj⟩
    obtain ⟨e₁, e₂⟩ := huniq x' φ' hφ'
    subst e₁
    have hφφ : φ' = φ := Subtype.ext e₂
    subst hφφ
    rcases hadj with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl (by rw [← hia, h])
    · refine Or.inr ?_
      rw [← hia]
      have : i = Function.surjInv (hsurj x') φ' :=
        IsCorners.inj (hcor x') (h.trans (Function.surjInv_eq (hsurj x') φ').symm)
      rw [this]
  have hbound : ∃ b₁ b₂ : Set S × Bool, ∀ e ∈ Γ.E, e ⊆ closure p → ∀ b : Bool,
      (e, b) = b₁ ∨ (e, b) = b₂ := by
    rcases hsides with rfl | hsides
    · obtain ⟨b₁, b₂, h⟩ := htwo f hf
      exact ⟨b₁, b₂, fun e he hep b => (hcand e he hep b).elim (h _) (h _)⟩
    · obtain ⟨b₁, h₁⟩ := hunique f hf hfp (hsides f (Or.inl rfl))
      obtain ⟨b₂, h₂⟩ := hunique g hg hgp (hsides g (Or.inr rfl))
      exact ⟨b₁, b₂, fun e he hep b => (hcand e he hep b).elim (fun h => Or.inl (h₁ _ h))
        fun h => Or.inr (h₂ _ h)⟩
  obtain ⟨b₁, b₂, hb⟩ := hbound
  have huniq : ∀ e ∈ Γ.E, e ⊆ closure p → ∀ e' ∈ Γ.E, e' ⊆ closure p → e' = e := by
    intro e he hep e' he' hep'
    rcases hb e he hep false with h₁ | h₁ <;> rcases hb e he hep true with h₂ | h₂ <;>
      rcases hb e' he' hep' false with h₃ | h₃
    all_goals first
      | exact absurd (Prod.ext_iff.mp (h₁.trans h₂.symm)).2 (by simp)
      | exact congrArg Prod.fst (h₃.trans h₁.symm)
      | exact congrArg Prod.fst (h₃.trans h₂.symm)
  -- The edge next to `f` at its end in `V(Γ)`.
  obtain ⟨x, φ, hφ, -⟩ := spoke_half_unique hrad hS hf hγ
  have hφΓ' : φ.1.1 ∈ Γ'.E := hφ ▸ hf
  obtain ⟨j, hj⟩ := hsurj x φ
  have hexists : ∃ e ∈ Γ.E, e ⊆ closure p := by
    rcases IsCorners.sides (hcor x) j p hp (by rw [hj, hφ]; exact hfp) with h | h
    · rcases corner_alternates hrad hS hmax hE hγ x.2 (hs x) j with ⟨-, h₂⟩ | ⟨h₁, -⟩
      · exact (edge_not_both hrad (hj ▸ h₂) hφΓ').elim
      · exact ⟨_, h₁, h ▸ hsidecl x j⟩
    · rw [hj] at h
      rcases corner_alternates hrad hS hmax hE hγ x.2 (hs x) φ with ⟨-, h₂⟩ | ⟨h₁, -⟩
      · exact ⟨_, h₂, h ▸ IsCorners.left (hcor x) φ⟩
      · exact (edge_not_both hrad h₁ hφΓ').elim
  obtain ⟨e, he, hep⟩ := hexists
  refine ⟨e, he, hep, fun e' he' hep' => huniq e he hep e' he' hep', ?_⟩
  intro v hv hvp
  let z : Γ.V := ⟨v, hv⟩
  obtain ⟨k, rfl⟩ := IsCorners.all (hcor z) p hp hvp
  have hkcl : ∀ i : halfEdges (radialUnion hrad) γ z.1, v ∈ closure i.1.1 := fun i => by
    have := end_mem_closure hγ i.2.1 i.1.2
    rwa [i.2.2] at this
  rcases corner_alternates hrad hS hmax hE hγ hv (hs z) k with ⟨-, h₂⟩ | ⟨h₁, -⟩
  · have := huniq e he hep _ h₂ (IsCorners.left (hcor z) k)
    exact this ▸ hkcl (next z k)
  · have := huniq e he hep _ h₁ (hsidecl z k)
    exact this ▸ hkcl k

/-- The part of a region `s` of `Γ'` around the edge `e` of `Γ`: the edge, with the regions of `H`
in
`s` whose closure contains it. -/
def faceUnion (Γ Γ' : Drawing S) (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (s e : Set S) :
    Set S :=
  e ∪ ⋃ p ∈ {p ∈ (radialUnion hrad).R | p ⊆ s ∧ e ⊆ closure p}, p

omit [T2Space S] [ConnectedSpace S] in
/-- A region of `H` that meets a region `s` of `Γ'` lies in it. -/
theorem region_sub_of_mem {s p : Set S} (hs : s ∈ Γ'.R) (hp : p ∈ (radialUnion hrad).R) {y : S}
    (hy : y ∈ closure p) (hys : y ∈ s) : p ⊆ s := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨z, hzs, hzp⟩ := mem_closure_iff.mp hy s (region_isOpen hs) hys
  refine subset_region hs (region_isPreconnected hp) ?_ hzp hzs
  exact disjoint_left.mpr fun w hw h => region_subset hp hw (Or.inr h)

omit [T2Space S] [ConnectedSpace S] in
/-- An edge of `Γ` that meets the closure of a region `s` of `Γ'` lies in `s`. -/
theorem edge_sub_of_closure {s e : Set S} (hs : s ∈ Γ'.R) (he : e ∈ Γ.E) {y : S} (hye : y ∈ e)
    (hys : y ∈ closure s) : e ⊆ s := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hyU : y ∉ Γ'.U := disjoint_left.mp (edge_disjoint hrad he) hye
  obtain ⟨s', hs', hys'⟩ := exists_region_of_notMem hyU
  obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hys s' (region_isOpen hs') hys'
  obtain rfl : s' = s := region_eq_of_mem hs' hs hz' hz
  exact subset_region hs' he.2.2.1.isConnected.isPreconnected (edge_disjoint hrad he) hye hys'

omit [ConnectedSpace S] in
theorem isOpen_faceUnion {s e : Set S} (hs : s ∈ Γ'.R) (he : e ∈ Γ.E) (hes : e ⊆ s) :
    IsOpen (faceUnion Γ Γ' hrad s e) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have heH : e ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro y (hy | hy)
  · obtain ⟨W, A₁, A₂, hW, hyW, hWU, hsub, hc₁, hc₂, hd₁, hd₂, hcl₁, hcl₂⟩ :=
      exists_edge_sides hS (radialUnion hrad) heH hy
    refine Filter.mem_of_superset (hW.mem_nhds hyW) fun z hz => ?_
    by_cases hzU : z ∈ (radialUnion hrad).U
    · exact Or.inl (hWU ⟨hz, hzU⟩)
    refine Or.inr ?_
    -- Each side of `e` near `y` lies in a region of `H` in `s`.
    have hside : ∀ A : Set S, IsPreconnected A → Disjoint A (radialUnion hrad).U →
        e ∩ W ⊆ closure A → z ∈ A → z ∈ ⋃ p ∈ {p ∈ (radialUnion hrad).R | p ⊆ s ∧ e ⊆ closure p}, p
          := by
      intro A hA hd hcl hzA
      obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
      have hAp : A ⊆ p := subset_region hp hA hd hzA hzp
      have hyp : y ∈ closure p := closure_mono hAp (hcl ⟨hy, hyW⟩)
      have hpe := edge_subset_closure_of_incident hS heH hp ⟨y, hy, hyp⟩
      exact mem_iUnion₂.mpr ⟨p, ⟨hp, region_sub_of_mem hrad hS hs hp hyp (hes hy), hpe⟩, hzp⟩
    rcases hsub ⟨hz, hzU⟩ with h | h
    · exact hside A₁ hc₁ hd₁ hcl₁ h
    · exact hside A₂ hc₂ hd₂ hcl₂ h
  · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
    refine Filter.mem_of_superset ((region_isOpen hp.1).mem_nhds hyp) fun z hz => ?_
    exact Or.inr (mem_iUnion₂.mpr ⟨p, hp, hz⟩)

include hmax in
/-- A region of `Γ'` is the union of one edge of `Γ` and regions of `H`. -/
theorem region_eq_faceUnion (hE : Γ.E.Nonempty) {s e : Set S} (hs : s ∈ Γ'.R) (he : e ∈ Γ.E)
    (hes : e ⊆ s) : s ⊆ faceUnion Γ Γ' hrad s e := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  -- The rest of `s` is covered by the sets of the other edges in `s`.
  let Rest : Set S := ⋃ f ∈ {f ∈ Γ.E | f ⊆ s ∧ f ≠ e}, faceUnion Γ Γ' hrad s f
  have hRest : IsOpen Rest := isOpen_biUnion fun f hf => isOpen_faceUnion hrad hS hs hf.1 hf.2.1
  have hcover : s ⊆ faceUnion Γ Γ' hrad s e ∪ Rest := by
    have hedge : ∀ f ∈ Γ.E, f ⊆ s → ∀ y ∈ f, y ∈ faceUnion Γ Γ' hrad s e ∪ Rest := by
      intro f hf hfs y hy
      by_cases hfe : f = e
      · exact Or.inl (Or.inl (hfe ▸ hy))
      · exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfs, hfe⟩, Or.inl hy⟩)
    intro y hy
    have hyU' : y ∉ Γ'.U := region_subset hs hy
    by_cases hyU : y ∈ Γ.U
    · have hyV : y ∉ Γ.V := fun h => hyU' (Γ'.V_subset_U (radial_V hrad h))
      rw [Γ.U_eq] at hyU
      rcases hyU with h | hyE
      · exact (hyV h).elim
      obtain ⟨f, hf, hyf'⟩ := mem_iUnion₂.mp hyE
      have hyf : y ∈ f := (Γ.closure_diff_V hf).subset ⟨hyf', hyV⟩
      exact hedge f hf (edge_sub_of_closure hrad hS hs hf hyf (subset_closure hy)) y hyf
    · have hyH : y ∉ (radialUnion hrad).U := fun h => h.elim hyU hyU'
      obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem hyH
      have hps := region_sub_of_mem hrad hS hs hp (subset_closure hyp) hy
      obtain ⟨f, hf, hfp, -⟩ := face_edge hrad hS hmax hE hp
      obtain ⟨q, hq⟩ := hf.1
      have hfs : f ⊆ s := edge_sub_of_closure hrad hS hs hf hq (closure_mono hps (hfp hq))
      by_cases hfe : f = e
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨p, ⟨hp, hps, hfe ▸ hfp⟩, hyp⟩))
      · exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfs, hfe⟩, Or.inr (mem_iUnion₂.mpr
          ⟨p, ⟨hp, hps, hfp⟩, hyp⟩)⟩)
  have hdisj : Disjoint (faceUnion Γ Γ' hrad s e) Rest := by
    refine disjoint_left.mpr ?_
    intro y hy hy'
    obtain ⟨f, ⟨hf, -, hfe⟩, hyf⟩ := mem_iUnion₂.mp hy'
    have heH : e ⊆ (radialUnion hrad).U := fun z hz => Or.inl (Γ.closure_subset_U he
      (subset_closure hz))
    have hfH : f ⊆ (radialUnion hrad).U := fun z hz => Or.inl (Γ.closure_subset_U hf
      (subset_closure hz))
    rcases hy with hy | hy <;> rcases hyf with hyf | hyf
    · exact hfe (Γ.edge_eq_of_mem hf he hyf hy)
    · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hyf
      exact region_subset hp.1 hyp (heH hy)
    · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
      exact region_subset hp.1 hyp (hfH hyf)
    · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
      obtain ⟨p', hp', hyp'⟩ := mem_iUnion₂.mp hyf
      obtain rfl : p = p' := region_eq_of_mem hp.1 hp'.1 hyp hyp'
      obtain ⟨g, -, -, hg, -⟩ := face_edge hrad hS hmax hE hp.1
      exact hfe ((hg f hf hp'.2.2).trans (hg e he hp.2.2).symm)
  obtain ⟨y, hy⟩ := he.1
  exact (region_isPreconnected hs).subset_left_of_subset_union
    (isOpen_faceUnion hrad hS hs he hes) hRest hdisj hcover ⟨y, hes hy, Or.inl hy⟩

include hmax in
/-- **Every region of a radial drawing contains a unique edge.** Graph Minors XI, Section 3 (page
75):
"every region of $\Gamma'$ includes a unique edge of $\Gamma$", for a drawing `Γ` with an edge. -/
theorem regionFacts_of_radial (hE : Γ.E.Nonempty) :
    RegionFacts (PaintingOrDrawing.drawing Γ) Γ' := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨y, hyO⟩ := region_nonempty hs
    obtain ⟨z, hzs, hzU⟩ := exists_notMem_U (Γ := radialUnion hrad) hS
      (region_isOpen hs) ⟨y, hyO⟩
    obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
    have hps := region_sub_of_mem hrad hS hs hp (subset_closure hzp) hzs
    obtain ⟨e, he, hep, -⟩ := face_edge hrad hS hmax hE hp
    obtain ⟨q, hq⟩ := he.1
    exact ⟨e, he, edge_sub_of_closure hrad hS hs he hq (closure_mono hps (hep hq))⟩
  · intro s hs e he f hf hes hfs
    obtain ⟨y, hy⟩ := hf.1
    have hyU : y ∉ (radialUnion hrad).R.sUnion := by
      rintro ⟨p, hp, hyp⟩
      exact region_subset hp hyp (Or.inl (Γ.closure_subset_U hf (subset_closure hy)))
    rcases region_eq_faceUnion hrad hS hmax hE hs he hes (hfs hy) with h | h
    · exact Γ.edge_eq_of_mem he hf h hy
    · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp h
      exact (hyU ⟨p, hp.1, hyp⟩).elim
  · intro s hs e he hes v hv hvs
    have hfin := finite_R hS (radialUnion hrad)
    have hsub : s ⊆ e ∪ ⋃ p ∈ {p ∈ (radialUnion hrad).R | p ⊆ s ∧ e ⊆ closure p}, p :=
      region_eq_faceUnion hrad hS hmax hE hs he hes
    have hcl := closure_mono hsub hvs
    have hpfin : {p ∈ (radialUnion hrad).R | p ⊆ s ∧ e ⊆ closure p}.Finite :=
      hfin.subset fun _ h => h.1
    rw [closure_union, hpfin.closure_biUnion _] at hcl
    rcases hcl with h | h
    · exact h
    · obtain ⟨p, hp, hvp⟩ := mem_iUnion₂.mp h
      obtain ⟨e', -, -, hu, hv'⟩ := face_edge hrad hS hmax hE hp.1
      rw [hu e he hp.2.2]
      exact hv' v hv hvp

end GraphMinor.GM11
