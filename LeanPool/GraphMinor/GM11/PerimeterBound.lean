/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Theorem64
public import LeanPool.GraphMinor.GM11.Section810

/-!
# The perimeter of a region of a radial drawing

Graph Minors XI, proof of (6.5), page 92: "the perimeter of $r$ has length at least twice the number
of ends of $e$".
This is `two_mul_ends_le`. `perimeterLength_le_four` is the bound in the other direction, and it is
what the converse
of (6.5) needs.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ Γ' : Drawing S}

/-- The weight `n(h)` of an edge in the perimeter of `s`. -/
noncomputable def perimN (Γ' : Drawing S) (s h : Set S) : ℕ :=
  open Classical in if ∃ r' ∈ Γ'.R, r' ≠ s ∧ Γ'.EdgeRegionIncident h r' then 1 else 2

omit [T2Space S] [ConnectedSpace S] in
theorem one_le_perimN (s h : Set S) : 1 ≤ perimN Γ' s h := by
  unfold perimN
  split_ifs <;> simp

section Generic

omit [ConnectedSpace S] in
/-- A spoke is not a loop: its two ends are different. -/
theorem spoke_half_eq (hnl : ∀ h ∈ Γ'.E, ∃ x y, x ≠ y ∧ closure h ∩ Γ'.V = {x, y}) {γ : Set S → I
  → S}
    (hγ : EdgePar Γ' γ) {h : Set S} (hh : h ∈ Γ'.E) {v : S} {b b' : Bool}
    (h₁ : γ h (endOf b) = v) (h₂ : γ h (endOf b') = v) : b = b' := by
  by_contra hne
  obtain ⟨x, y, hxy, hcap⟩ := hnl h hh
  have hall : ∀ c, γ h (endOf c) = v := fun c => by
    cases b <;> cases b' <;> cases c <;> simp_all
  have hxc : x ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
  have hyc : y ∈ closure h ∩ Γ'.V := by rw [hcap]; simp
  obtain ⟨c₁, hc₁⟩ := exists_end_eq hγ hh hxc.2 hxc.1
  obtain ⟨c₂, hc₂⟩ := exists_end_eq hγ hh hyc.2 hyc.1
  exact hxy (by rw [← hc₁, ← hc₂, hall, hall])

/-- Around a vertex of `Γ'` on the closure of a region `s`, if an edge has that vertex as an end,
the perimeter of `s`
has weight at least 2. -/
theorem two_le_of_spoke (hS : IsClosedSurface S) (hnl : ∀ h ∈ Γ'.E, ∃ x y, x ≠ y ∧ closure h ∩ Γ'.V
  = {x, y})
    {s h₀ : Set S} (hs : s ∈ Γ'.R) {v : S} (hv' : v ∈ Γ'.V) (hvs : v ∈ closure s) (hh₀ : h₀ ∈ Γ'.E)
    (hvh₀ : v ∈ closure h₀) :
    ∃ T : Finset (Set S), (∀ h ∈ T, h ∈ Γ'.E ∧ h ⊆ closure s ∧ v ∈ closure h) ∧ 2
      ≤ ∑ h ∈ T, perimN Γ' s h := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ'
  obtain ⟨b, hb⟩ := exists_end_eq hγ hh₀ hv' hvh₀
  have hfin : Finite (halfEdges Γ' γ v) := (finite_halfEdges Γ' γ v).to_subtype
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ' γ v)
  · obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS Γ' hγ hv' h2
    have hcor := IsSectors.corners hsec
    obtain ⟨k, rfl⟩ := IsCorners.all hcor s hs hvs
    obtain ⟨k', rfl⟩ := next_surjective hcor k
    have hne : next k' ≠ next (next k') := (IsSectors.next_ne hsec _).symm
    have hne' : (next k').1.1 ≠ (next (next k')).1.1 := fun h => by
      have h₁ := (next k').2.2
      have h₂ := (next (next k')).2.2
      rw [← h] at h₂
      have hbb := spoke_half_eq hnl hγ (next k').2.1 h₁ h₂
      exact hne (Subtype.ext (Prod.ext h hbb))
    have hc₁ := IsCorners.right hcor k'
    have hc₂ := IsCorners.left hcor (next k')
    have hv₁ : v ∈ closure (next k').1.1 := by
      have := end_mem_closure hγ (next k').2.1 (next k').1.2
      rwa [(next k').2.2] at this
    have hv₂ : v ∈ closure (next (next k')).1.1 := by
      have := end_mem_closure hγ (next (next k')).2.1 (next (next k')).1.2
      rwa [(next (next k')).2.2] at this
    refine ⟨{(next k').1.1, (next (next k')).1.1}, fun h hh => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hh with rfl | hh
      · exact ⟨(next k').2.1, hc₁, hv₁⟩
      · obtain rfl := Finset.mem_singleton.mp hh
        exact ⟨(next (next k')).2.1, hc₂, hv₂⟩
    · rw [Finset.sum_pair hne']
      have := one_le_perimN (Γ' := Γ') (ρ (next k')) (next k').1.1
      have := one_le_perimN (Γ' := Γ') (ρ (next k')) (next (next k')).1.1
      omega
  · have hk : ∀ l : halfEdges Γ' γ v, l = ⟨(h₀, b), hh₀, hb⟩ := fun l => by
      have h1 : Nat.card (halfEdges Γ' γ v) ≤ 1 := by omega
      exact (Finite.card_le_one_iff_subsingleton.mp h1).elim _ _
    obtain ⟨Z, hZo, hvZ, hZ⟩ := exists_single_nbhd hS hγ _ hk
    have hone : ∀ r' ∈ Γ'.R, v ∈ closure r' → r' = s := fun r' hr' hvr' => by
      obtain ⟨y, hyZ, hyr'⟩ := mem_closure_iff.mp hvr' Z hZo hvZ
      obtain ⟨x, hxZ, hxs⟩ := mem_closure_iff.mp hvs Z hZo hvZ
      obtain ⟨A, hAc, hAd, hxA, hyA, -⟩ := hZ x hxZ (region_subset hs hxs) y hyZ
        (region_subset hr' hyr')
      exact region_eq_of_mem hr' hs hyr' (subset_region hs hAc hAd hxA hxs hyA)
    obtain ⟨r', hr', hh₀r'⟩ := exists_region_incident hS hh₀
    have hsub : closure h₀ ⊆ closure r' := closure_minimal hh₀r' isClosed_closure
    obtain rfl := hone r' hr' (hsub hvh₀)
    refine ⟨{h₀}, fun h hh => ?_, ?_⟩
    · obtain rfl := Finset.mem_singleton.mp hh
      exact ⟨hh₀, hh₀r', hvh₀⟩
    · rw [Finset.sum_singleton, perimN, ite_eq_right]
      rintro ⟨r₂, hr₂, hne, -, -, hinc⟩
      exact hne (hone r₂ hr₂ ((closure_minimal (edge_subset_closure_of_incident hS hh₀ hr₂ hinc)
        isClosed_closure) hvh₀))

/-- The perimeter of a region `s` has length at least twice the number of its vertices in a set `V₀`
of ends, if each
edge of `Γ'` has at most one end in `V₀`. -/
theorem two_mul_ncard_le_perimeter (hS : IsClosedSurface S)
    (hnl : ∀ h ∈ Γ'.E, ∃ x y, x ≠ y ∧ closure h ∩ Γ'.V = {x, y}) {V₀ s : Set S} (hf : V₀.Finite)
      (hV : V₀ ⊆ Γ'.V)
    (hs : s ∈ Γ'.R) (hu : ∀ h ∈ Γ'.E, ∀ v ∈ V₀, ∀ w ∈ V₀, v ∈ closure h → w ∈ closure h → v = w)
    (hspoke : ∀ v ∈ V₀ ∩ closure s, ∃ h ∈ Γ'.E, v ∈ closure h) :
    2 * (V₀ ∩ closure s).ncard ≤ perimeterLength Γ' s := by
  classical
  have hX : (V₀ ∩ closure s).Finite := hf.subset inter_subset_left
  have hex : ∀ v, v ∈ V₀ ∩ closure s → ∃ T : Finset (Set S), (∀ h ∈ T, h ∈ Γ'.E ∧ h ⊆ closure s
    ∧ v ∈ closure h) ∧
      2 ≤ ∑ h ∈ T, perimN Γ' s h := fun v hv => by
    obtain ⟨h₀, hh₀, hvh₀⟩ := hspoke v hv
    exact two_le_of_spoke hS hnl hs (hV hv.1) hv.2 hh₀ hvh₀
  choose! T hT hT2 using hex
  have hPf : (perimeter Γ' s).E.Finite := (perimeter Γ' s).finite_edges
  have hdis : ((hX.toFinset : Finset S) : Set S).PairwiseDisjoint T := fun a ha b hb hab => by
    rw [Function.onFun, Finset.disjoint_left]
    intro h h₁ h₂
    have ha' : a ∈ V₀ ∩ closure s := by simpa using ha
    have hb' : b ∈ V₀ ∩ closure s := by simpa using hb
    exact hab (hu h (hT a ha' h h₁).1 a ha'.1 b hb'.1 (hT a ha' h h₁).2.2 (hT b hb' h h₂).2.2)
  have hsub : hX.toFinset.biUnion T ⊆ hPf.toFinset := fun h hh => by
    obtain ⟨v, hv, hhv⟩ := Finset.mem_biUnion.mp hh
    have hv' : v ∈ V₀ ∩ closure s := by simpa using hv
    obtain ⟨h₁, h₂, -⟩ := hT v hv' h hhv
    exact hPf.mem_toFinset.mpr (mem_interSet_E_iff.mpr ⟨h₁, h₂⟩)
  have hlen : perimeterLength Γ' s = ∑ h ∈ hPf.toFinset, perimN Γ' s h := by
    rw [perimeterLength, finsum_mem_eq_finite_toFinset_sum _ hPf]
    rfl
  rw [hlen, ncard_eq_toFinset_card _ hX, Finset.card_eq_sum_ones, Finset.mul_sum]
  calc ∑ v ∈ hX.toFinset, 2 * 1 ≤ ∑ v ∈ hX.toFinset, ∑ h ∈ T v, perimN Γ' s h :=
        Finset.sum_le_sum fun v hv => by simpa using hT2 v (by simpa using hv)
    _ = ∑ h ∈ hX.toFinset.biUnion T, perimN Γ' s h := (Finset.sum_biUnion hdis).symm
    _ ≤ ∑ h ∈ hPf.toFinset, perimN Γ' s h := Finset.sum_le_sum_of_subset hsub

omit [T2Space S] [ConnectedSpace S] in
/-- An edge of a radial drawing has two different ends. -/
theorem two_ends_of_preRadial {Γ : PaintingOrDrawing S} (hrad : Γ.IsPreRadialDrawing Γ') :
    ∀ h ∈ Γ'.E, ∃ x y, x ≠ y ∧ closure h ∩ Γ'.V = {x, y} := fun h hh => by
  obtain ⟨v, hv, w, hw, hcap⟩ := hrad.2.2.2.2.1 h hh
  exact ⟨v, w, fun e => hw.2 (e ▸ hv), hcap⟩

omit [T2Space S] [ConnectedSpace S] in
/-- An edge of a radial drawing has one end in `V(Γ)`. -/
theorem end_unique_of_preRadial {Γ : PaintingOrDrawing S} (hrad : Γ.IsPreRadialDrawing Γ') :
    ∀ h ∈ Γ'.E, ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ∈ closure h → w ∈ closure h → v = w
      := fun h hh a ha b hb h₁ h₂ => by
  obtain ⟨v, -, w, hw, hcap⟩ := hrad.2.2.2.2.1 h hh
  have key : ∀ z ∈ Γ.V, z ∈ closure h → z = v := fun z hz hzh => by
    have : z ∈ closure h ∩ Γ'.V := ⟨hzh, hrad.2.1 hz⟩
    rw [hcap] at this
    rcases this with h' | h'
    · exact h'
    · exact absurd hz ((mem_singleton_iff.mp h') ▸ hw.2)
  rw [key a ha h₁, key b hb h₂]

end Generic

variable (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S)
  (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') (hE : Γ.E.Nonempty)

include hrad hS hmax hE

/-- **Graph Minors XI, proof of (6.5)** (page 92): "the perimeter of $r$ has length at least twice
the number of ends of $e$". -/
theorem two_mul_ends_le {s : Set S} (hs : s ∈ Γ'.R) : 2 * (Γ.V ∩ closure s).ncard
  ≤ perimeterLength Γ' s := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine two_mul_ncard_le_perimeter hS (two_ends_of_preRadial hrad.2) Γ.finite_V hrad.2.2.1 hs
    (end_unique_of_preRadial hrad.2) fun v hv => ?_
  obtain ⟨e₀, he₀, hve₀⟩ := exists_edge_at hrad hS hE hv.1
  obtain ⟨r, hr, he₀r⟩ := exists_region_incident hS he₀
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  obtain ⟨h₀, hh₀, hcap⟩ := exists_spoke_at hrad hmax hS hE hr hc hcV hv.1
    (closure_minimal he₀r isClosed_closure hve₀)
  have hvh₀ : v ∈ closure h₀ ∩ Γ'.V := by rw [hcap]; simp
  exact ⟨h₀, hh₀, hvh₀.1⟩

/-- The perimeter of a region of `Γ'` has length at most 4: its two faces in `Γ ∪ Γ'` have two sides
each in `Γ'`. -/
theorem perimeterLength_le_four {s : Set S} (hs : s ∈ Γ'.R) : perimeterLength Γ' s ≤ 4 := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hex, -, -⟩ := regionFacts_of_radial hrad hS hmax hE
  obtain ⟨e, he, hes⟩ := hex s hs
  obtain ⟨p, hp, q, hq, hpq, hep, heq, hseq⟩ := region_eq_two_faces hrad hS hmax hE hs he hes
  obtain ⟨r₁, hr₁, hpr⟩ := exists_region_of_sub hrad hp
  obtain ⟨r₂, hr₂, hqr⟩ := exists_region_of_sub hrad hq
  obtain ⟨f, g, hf, hg, hfp, hgp, hall, hsides⟩ := hub_sides hrad hS hmax hE hr₁ hp hpr
  obtain ⟨f', g', hf', hg', hfq, hgq, hall', hsides'⟩ := hub_sides hrad hS hmax hE hr₂ hq hqr
  have hPf : (perimeter Γ' s).E.Finite := (perimeter Γ' s).finite_edges
  have hlen : perimeterLength Γ' s = ∑ h ∈ hPf.toFinset, perimN Γ' s h := by
    rw [perimeterLength, finsum_mem_eq_finite_toFinset_sum _ hPf]
    rfl
  have hHE : ∀ {h}, h ∈ Γ'.E → h ∈ (radialUnion hrad).E := fun hh => by
    rw [radialUnion_E]
    exact Or.inr hh
  -- A region of `Γ ∪ Γ'` in `s` is one of the two faces.
  have hface : ∀ A ∈ (radialUnion hrad).R, (A ∩ s).Nonempty → A = p ∨ A = q := by
    rintro A hA ⟨y, hyA, hys⟩
    rw [hseq] at hys
    rcases hys with (hy | hy) | hy
    · exact Or.inl (region_eq_of_mem hA hp hyA hy)
    · exact Or.inr (region_eq_of_mem hA hq hyA hy)
    · have heE : e ∈ Γ.E := he
      exact absurd (Or.inl (Γ.closure_subset_U heE (subset_closure hy)) : y ∈ Γ.U ∪ Γ'.U)
        (region_subset hA hyA)
  -- The closure of `s`.
  have hclo : ∀ h ∈ Γ'.E, h ⊆ closure s → h ⊆ closure p ∨ h ⊆ closure q := fun h hh hhs => by
    obtain ⟨y, hy⟩ := hh.1
    have hyU : y ∉ Γ.U := fun hyU => by
      exact disjoint_left.mp (spoke_disjoint hrad hh) hy hyU
    have hy' := hhs hy
    rw [hseq, closure_union, closure_union] at hy'
    rcases hy' with (hy' | hy') | hy'
    · exact Or.inl (edge_subset_closure_of_incident hS (hHE hh) hp ⟨y, hy, hy'⟩)
    · exact Or.inr (edge_subset_closure_of_incident hS (hHE hh) hq ⟨y, hy, hy'⟩)
    · have heE : e ∈ Γ.E := he
      exact absurd (Γ.closure_subset_U heE hy') hyU
  have hsubs : closure p ⊆ closure s ∧ closure q ⊆ closure s := by
    constructor <;> refine closure_mono ?_ <;> rw [hseq]
    · exact fun x hx => Or.inl (Or.inl hx)
    · exact fun x hx => Or.inl (Or.inr hx)
  -- An edge on a third face is incident with another region.
  have hoth : ∀ h ∈ Γ'.E, ∀ A ∈ (radialUnion hrad).R, h ⊆ closure A → A ≠ p → A ≠ q → perimN Γ' s h
    ≤ 1 := by
    intro h hh A hA hhA hAp hAq
    obtain ⟨y, hy⟩ := region_nonempty hA
    have hyU : y ∉ Γ'.U := fun h' => region_subset hA hy (Or.inr h')
    obtain ⟨s', hs', hys'⟩ := exists_region_of_notMem hyU
    have hAs' : A ⊆ s' := subset_region hs' (region_isPreconnected hA)
      (disjoint_left.mpr fun x hx h' => region_subset hA hx (Or.inr h')) hy hys'
    have hne : s' ≠ s := fun h' => (hface A hA ⟨y, hy, h' ▸ hys'⟩).elim hAp hAq
    obtain ⟨z, hz⟩ := hh.1
    have hif : ∃ r' ∈ Γ'.R, r' ≠ s ∧ Γ'.EdgeRegionIncident h r' :=
      ⟨s', hs', hne, hh, hs', z, hz, closure_mono hAs' (hhA hz)⟩
    rw [perimN, ite_eq_left hif]
  let wp : ℕ := if f = g then 2 else 1
  let wq : ℕ := if f' = g' then 2 else 1
  let w : Set S → ℕ := fun h => (if h ⊆ closure p then wp else 0) + if h ⊆ closure q then wq else 0
  have hwp : 1 ≤ wp := by simp only [wp]; split_ifs <;> omega
  have hwq : 1 ≤ wq := by simp only [wq]; split_ifs <;> omega
  have hn2 : ∀ h, perimN Γ' s h ≤ 2 := fun h => by
    unfold perimN
    split_ifs <;> omega
  have hstep : ∀ {f g : Set S} {p' q' : Set S}, p' ∈ (radialUnion hrad).R →
      (f = g ∨ ∀ s', (s' = f ∨ s' = g) → ∃ A₁ ∈ (radialUnion hrad).R, ∃ A₂ ∈ (radialUnion hrad).R,
        A₁ ≠ A₂ ∧ s' ⊆ closure A₁ ∧ s' ⊆ closure A₂) → (p' = p ∧ q' = q ∨ p' = q ∧ q' = p) →
      ∀ h ∈ Γ'.E, (h = f ∨ h = g) → ¬ h ⊆ closure q' → f ≠ g → perimN Γ' s h ≤ 1 := by
    rintro f₁ g₁ p' q' - hsd hpp h hh hhfg hnq hne
    obtain ⟨A₁, hA₁, A₂, hA₂, hA, h₁, h₂⟩ := (hsd.resolve_left hne) h hhfg
    have hpick : ∃ A ∈ (radialUnion hrad).R, h ⊆ closure A ∧ A ≠ p' := by
      by_cases h' : A₁ = p'
      · exact ⟨A₂, hA₂, h₂, fun e => hA (h'.trans e.symm)⟩
      · exact ⟨A₁, hA₁, h₁, h'⟩
    obtain ⟨A, hAR, hhA, hAp⟩ := hpick
    have hAq : A ≠ q' := fun e => hnq (e ▸ hhA)
    rcases hpp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hoth h hh A hAR hhA hAp hAq
    · exact hoth h hh A hAR hhA hAq hAp
  have hbound : ∀ h ∈ hPf.toFinset, perimN Γ' s h ≤ w h := fun h hh => by
    have hh' : h ∈ Γ'.E ∧ h ⊆ closure s := mem_interSet_E_iff.mp (hPf.mem_toFinset.mp hh)
    by_cases hP : h ⊆ closure p <;> by_cases hQ : h ⊆ closure q
    · have := hn2 h
      simp only [w, ite_eq_left hP, ite_eq_left hQ]
      omega
    · simp only [w, ite_eq_left hP, ite_eq_right hQ, add_zero]
      by_cases hfg : f = g
      · have := hn2 h
        simp only [wp, ite_eq_left hfg]
        omega
      · exact (hstep hp hsides (Or.inl ⟨rfl, rfl⟩) h hh'.1 (hall h hh'.1 hP) hQ hfg).trans hwp
    · simp only [w, ite_eq_right hP, ite_eq_left hQ, zero_add]
      by_cases hfg : f' = g'
      · have := hn2 h
        simp only [wq, ite_eq_left hfg]
        omega
      · exact (hstep hq hsides' (Or.inr ⟨rfl, rfl⟩) h hh'.1 (hall' h hh'.1 hQ) hP hfg).trans hwq
    · exact ((hclo h hh'.1 hh'.2).elim hP hQ).elim
  have hsum : ∀ (f g c : Set S) (c' : ℕ), (∀ h ∈ hPf.toFinset, h ⊆ c → h = f ∨ h = g) →
      c' = (if f = g then 2 else 1) → ∑ h ∈ hPf.toFinset, (if h ⊆ c then c' else 0) ≤ 2 := by
    intro f g c c' hin hc'
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hsub : hPf.toFinset.filter (fun h => h ⊆ c) ⊆ {f, g} := fun h hh => by
      obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hh
      simpa using hin h h₁ h₂
    have hcard := Finset.card_le_card hsub
    by_cases hfg : f = g
    · subst hfg
      simp only [hc', ite_true, Finset.pair_eq_singleton, Finset.card_singleton] at hcard ⊢
      omega
    · have := Finset.card_pair hfg
      simp only [hc', ite_eq_right hfg]
      omega
  rw [hlen]
  calc ∑ h ∈ hPf.toFinset, perimN Γ' s h ≤ ∑ h ∈ hPf.toFinset, w h := Finset.sum_le_sum hbound
    _ = ∑ h ∈ hPf.toFinset, (if h ⊆ closure p then wp else 0) + ∑ h ∈ hPf.toFinset,
      (if h ⊆ closure q then wq else 0) :=
        Finset.sum_add_distrib
    _ ≤ 2 + 2 := add_le_add
        (hsum f g _ wp (fun h hh hc => hall h (mem_interSet_E_iff.mp (hPf.mem_toFinset.mp hh)).1
          hc) rfl)
        (hsum f' g' _ wq (fun h hh hc => hall' h (mem_interSet_E_iff.mp
          (hPf.mem_toFinset.mp hh)).1 hc) rfl)

end GraphMinor.GM11
