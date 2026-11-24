/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingFlat
public import LeanPool.GraphMinor.GM11.PerimeterBound

/-!
# The perimeter of a region of a radial drawing of a painting

`two_mul_ends_le_painting` and `perimeterLength_le_cell` show that a region of a radial drawing of a
painting has perimeter
of length twice the number of ends of the cell in it. Graph Minors XI, proof of (6.5), page 92, uses
the first, and the
converse of (6.5) uses the second.

For the second, let `D` be the drawing of the boundaries of the cells, and `G` the radial drawing of
`D` made from `Γ'` by
adding stars in the cells. The cell `e` in a region `s` of `Γ'` has as many boundary edges in `D` as
it has ends, and
each of these is a side of one face of `D ∪ G` in `s` outside `e`. Each such face has two sides in
`G`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- A circuit has at least as many vertices as edges. -/
theorem length_le_ncard_V {C : Drawing S} (hC : C.IsCircuit) : C.length ≤ C.V.ncard := by
  classical
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hCV, hCE⟩ := id hC
  have hlen : C.length = W.length := by
    rw [Drawing.length, hCE]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by
      ext x
      simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    rfl
  have htail : W.support.tail.length = W.length := by
    rw [List.length_tail, length_support]
    rfl
  have hsub : (W.support.tail.toFinset : Set S) ⊆ C.V := fun x hx => by
    rw [hCV]
    exact List.mem_of_mem_tail (by simpa using hx)
  have := ncard_le_ncard hsub C.finite_V
  rw [ncard_coe_finset, List.toFinset_card_of_nodup hnd, htail] at this
  rwa [hlen]

variable [ConnectedSpace S] {Γ : Painting S} {Γ' : Drawing S}

omit [ConnectedSpace S] in
/-- A boundary point of a cell off the vertices is in the closure of a region of the painting. -/
theorem exists_region_at_boundary (hS : IsClosedSurface S) (hrad : (PaintingOrDrawing.painting
  Γ).IsRadialDrawing Γ')
    (hR : Γ.R.Finite) {e : Set S} (he : e ∈ Γ.E) {y : S} (hy : y ∈ discBd (closure e))
      (hyV : y ∉ Γ.V) :
    ∃ r ∈ Γ.R, y ∈ closure r := by
  classical
  have hpre : PreRad (PaintingOrDrawing.painting Γ) Γ' := ⟨hrad.1, hrad.2.1⟩
  have hU : IsClosed Γ.U := cell_isClosed_U hpre
  have hd := Cell.isClosedDisc_closure he
  have hfe : Γ.E.Finite := Γ.finite_edges
  let W : Set S := (Γ.V ∪ ⋃ f ∈ Γ.E \ {e}, closure f)ᶜ
  have hW : IsOpen W := (Γ.finite_V.isClosed.union ((hfe.subset sdiff_subset).isClosed_biUnion
    fun _ _ => isClosed_closure)).isOpen_compl
  have hbW : y ∈ W := by
    rintro (h | h)
    · exact hyV h
    · obtain ⟨f, hf, hbf⟩ := mem_iUnion₂.mp h
      exact hyV (Cell.closure_inter_subset_V hS hU he hf.1 (Ne.symm hf.2) ⟨discBd_subset _ hy, hbf⟩)
  have hbf : y ∈ closure (closure e)ᶜ := by
    have : y ∈ frontier (closure e) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hd]
      exact hy
    exact (frontier_eq_closure_inter_closure.subset this).2
  have hcl : y ∈ closure (⋃ r ∈ Γ.R, r) := by
    refine mem_closure_iff.mpr fun O hO hyO => ?_
    obtain ⟨z, ⟨hzO, hzW⟩, hze⟩ := mem_closure_iff.mp hbf (O ∩ W) (hO.inter hW) ⟨hyO, hbW⟩
    refine ⟨z, hzO, ?_⟩
    have hzU : z ∉ Γ.U := fun hzU => by
      rcases Cell.mem_V_or_cell Γ hzU with h | ⟨f, hf, hzf⟩
      · exact hzW (Or.inl h)
      · by_cases hfe' : f = e
        · exact hze (subset_closure (hfe' ▸ hzf))
        · exact hzW (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe'⟩, subset_closure hzf⟩))
    exact mem_iUnion₂.mpr ⟨_, ⟨z, ⟨trivial, hzU⟩, rfl⟩, mem_connectedComponentIn ⟨trivial, hzU⟩⟩
  rw [hR.closure_biUnion] at hcl
  obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.mp hcl
  exact ⟨r, hr, hyr⟩

variable (hS : IsClosedSurface S) (hrad : (PaintingOrDrawing.painting Γ).IsRadialDrawing Γ')
  (hE : Γ.E.Nonempty)
  (hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty)

include hS hrad hE hv

/-- Each vertex of a painting with a cell at every point is an end of an edge of a radial drawing.
-/
theorem exists_spoke_painting {v : S} (hvV : v ∈ Γ.V) : ∃ h ∈ Γ'.E, v ∈ closure h := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨D, G, hDU, hDV, hDR, hGrad, hDE, hsub, -, hh₁, hh₂⟩ := exists_cell_drawings hS hrad hE hv
  have hGpre : PreRad (PaintingOrDrawing.drawing D) G := ⟨hGrad.1, hGrad.2.1⟩
  have hvD : v ∈ D.V := hDV ▸ hvV
  obtain ⟨a, ha, hva⟩ := exists_edge_at hGpre hS hDE hvD
  obtain ⟨y, hy⟩ := ha.1
  have hyU := (ha.2.1 hy)
  have hyV : y ∉ Γ.V := fun h => hyU.2 (hDV ▸ h)
  have hR : Γ.R.Finite := (finite_R hS D).subset (hDR ▸ subset_union_left)
  rw [hDU] at hyU
  obtain ⟨f, hf, hyf⟩ : ∃ f ∈ Γ.E, y ∈ discBd (closure f) := by
    rcases hyU.1 with h | h
    · exact absurd h hyV
    · obtain ⟨f, hf, h'⟩ := mem_iUnion₂.mp h
      exact ⟨f, hf, h'⟩
  obtain ⟨r, hr, hyr⟩ := exists_region_at_boundary (Γ' := Γ') hS hrad hR hf hyf hyV
  have hrD : r ∈ D.R := hDR ▸ Or.inl hr
  have har : a ⊆ closure r := edge_subset_closure_of_incident hS ha hrD ⟨y, hy, hyr⟩
  have hvr : v ∈ closure r := closure_minimal har isClosed_closure hva
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hGrad.2.1.2.2.1 r hrD
  obtain ⟨h, hh, hcap⟩ := exists_spoke_at hGpre hGrad.2.2 hS hDE hrD hc hcV hvD hvr
  obtain ⟨v', hv', r₁, hr₁, w, hw, hwV, hcap', hsubr⟩ := spoke_ends hGpre hS hh
  have hcc : c ∈ closure h ∩ G.V := by rw [hcap]; simp
  rw [hcap'] at hcc
  have hcw : c = w := by
    rcases hcc with h' | h'
    · exact absurd (h' ▸ hv') fun h'' => region_subset hrD hc (D.V_subset_U h'')
    · exact h'
  obtain rfl : r₁ = r := region_eq_of_mem hr₁ hrD (hcw ▸ hw) hc
  have hvh : v ∈ closure h ∩ G.V := by rw [hcap]; simp
  exact ⟨h, hh₁ h hh r₁ hr hsubr, hvh.1⟩

/-- **Graph Minors XI, proof of (6.5)** (page 92), for a painting: "the perimeter of $r$ has length
at least twice the number of ends of $e$". -/
theorem two_mul_ends_le_painting {s : Set S} (hs : s ∈ Γ'.R) : 2 * (Γ.V ∩ closure s).ncard
  ≤ perimeterLength Γ' s :=
  two_mul_ncard_le_perimeter hS (two_ends_of_preRadial hrad.2.1) Γ.finite_V hrad.2.1.2.1 hs
    (end_unique_of_preRadial hrad.2.1) fun _ hx => exists_spoke_painting hS hrad hE hv hx.1

omit hS hrad hE hv in
omit [T2Space S] [ConnectedSpace S] in
/-- The weight of an edge `h` in a region `s` of `Γ'` is at most its total weight in the regions of
`G` inside `s`.
If `h` has `s` on both sides, the two sides are one region of `G` on both sides, or two regions of
`G`. -/
theorem perimN_le_sum {G : Drawing S} (hGs : Γ'.IsSubdrawing G) (hS : IsClosedSurface S) {s h p₀ :
  Set S}
    {P : Finset (Set S)} (hP : ∀ p, p ∈ P ↔ p ∈ G.R ∧ p ⊆ s) (hh' : h ∈ Γ'.E) (hp₀ : p₀ ∈ P)
    (hh₀ : h ⊆ closure p₀) :
    open Classical in
    perimN Γ' s h ≤ ∑ p ∈ P, if h ⊆ closure p then perimN G p h else 0 := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hh : h ∈ G.E := hGs.2 hh'
  have hone : 1 ≤ perimN G p₀ h := one_le_perimN _ _
  have hle₀ : perimN G p₀ h ≤ ∑ p ∈ P, if h ⊆ closure p then perimN G p h else 0 := by
    have := Finset.single_le_sum (f := fun p => if h ⊆ closure p then perimN G p h else 0)
      (fun _ _ => Nat.zero_le _) hp₀
    simpa only [ite_eq_left hh₀] using this
  unfold perimN at hone hle₀ ⊢
  by_cases hG : ∃ r' ∈ G.R, r' ≠ p₀ ∧ G.EdgeRegionIncident h r'
  · obtain ⟨r', hr', hne, hinc⟩ := hG
    by_cases hΓ : ∃ r' ∈ Γ'.R, r' ≠ s ∧ Γ'.EdgeRegionIncident h r'
    · rw [ite_eq_left hΓ]
      exact hone.trans hle₀
    · rw [ite_eq_right hΓ]
      obtain ⟨x, hx⟩ := region_nonempty hr'
      have hxU : x ∉ Γ'.U := fun h' => region_subset hr' hx (hGs.U_subset h')
      obtain ⟨r'', hr'', hxr''⟩ := exists_region_of_notMem hxU
      have hsub : r' ⊆ r'' := subset_region hr'' (region_isPreconnected hr')
        (disjoint_left.mpr fun z hz h' => region_subset hr' hz (hGs.U_subset h')) hx hxr''
      have heq : r'' = s := by
        by_contra hn
        obtain ⟨y, hy, hyc⟩ := hinc.2.2
        exact hΓ ⟨r'', hr'', hn, hh', hr'', y, hy, closure_mono hsub hyc⟩
      have hr'P : r' ∈ P := (hP r').mpr ⟨hr', heq ▸ hsub⟩
      have hcl : h ⊆ closure r' := edge_subset_closure_of_incident hS hh hr' hinc.2.2
      have hsum := Finset.sum_le_sum_of_subset (f := fun p => if h ⊆ closure p then
        (if ∃ r' ∈ G.R, r' ≠ p ∧ G.EdgeRegionIncident h r' then 1 else 2) else 0)
        (show ({p₀, r'} : Finset (Set S)) ⊆ P from by
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hp₀
          · rw [Finset.mem_singleton.mp hq]
            exact hr'P)
      rw [Finset.sum_pair (Ne.symm hne)] at hsum
      simp only [ite_eq_left hh₀, ite_eq_left hcl] at hsum
      refine le_trans ?_ hsum
      split_ifs <;> omega
  · rw [ite_eq_right hG] at hle₀
    refine le_trans ?_ hle₀
    split_ifs <;> omega

/-- **The perimeter of a region of `Γ'`**: at most twice the number of ends of the cell in it. Each
region of `G` in `s`
has perimeter of length at most 4, and the centre of the cell gives weight 2 of that from the star.
So the region
has weight at most 2 on the edges of `Γ'`, and there are at most as many such regions as sides of
the cell. -/
theorem perimeterLength_le_painting {s e : Set S} (hs : s ∈ Γ'.R) (he : e ∈ Γ.E) (hes : e ⊆ s) :
    perimeterLength Γ' s ≤ 2 * (Γ.V ∩ closure e).ncard := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpre : PreRad (PaintingOrDrawing.painting Γ) Γ' := ⟨hrad.1, hrad.2.1⟩
  have hmax : RadMax (PaintingOrDrawing.painting Γ) Γ' := hrad.2.2
  obtain ⟨D, G, hDU, hDV, hDR, hGrad, hDE, hsub, hGU, -, -⟩ := exists_cell_drawings hS hrad hE hv
  have hGpre : PreRad (PaintingOrDrawing.drawing D) G := ⟨hGrad.1, hGrad.2.1⟩
  have hGmax : RadMax (PaintingOrDrawing.drawing D) G := hGrad.2.2
  obtain ⟨hex, -, -⟩ := regionFacts_of_radial hGpre hS hGmax hDE
  obtain ⟨-, huniq, -⟩ := regionFacts_of_painting hpre hmax hS hE
  have hUc : IsClosed Γ.U := cell_isClosed_U hpre
  have hRf : G.R.Finite := finite_R hS G
  let P : Finset (Set S) := hRf.toFinset.filter (· ⊆ s)
  have hP : ∀ p, p ∈ P ↔ p ∈ G.R ∧ p ⊆ s := fun p => by simp [P]
  have hEd : ∀ {f}, f ∈ Γ.E → Disjoint f Γ'.U := fun {f} hf => disjoint_left.mpr fun x hx hxU => by
    obtain ⟨-, hdis, hfU, -⟩ := (PaintingOrDrawing.painting Γ).edge_props hf
    have : x ∈ Γ.V := hrad.2.1.1.subset ⟨hfU hx, hxU⟩
    exact disjoint_left.mp hdis hx this
  -- An edge of `D` in `s` is on the boundary of `e`.
  have hbd : ∀ {a}, a ∈ D.E → a ⊆ s → a ⊆ discBd (closure e) := fun {a} ha has y hy => by
    have hyU : y ∈ D.U := ha.2.1 hy |>.1
    have hyV : y ∉ D.V := (ha.2.1 hy).2
    rw [hDU] at hyU
    rcases hyU with h | h
    · exact absurd (hDV ▸ h) hyV
    · obtain ⟨f, hf, hyf⟩ := mem_iUnion₂.mp h
      have hyc : y ∈ closure f := discBd_subset _ hyf
      have hyf' : y ∈ f := by
        rw [← Cell.closure_sdiff_V hS hUc hf]
        exact ⟨hyc, fun h' => hyV (hDV ▸ h')⟩
      have hfs : f ⊆ s := subset_region hs ((PaintingOrDrawing.painting Γ).edge_props hf).1
        (hEd hf) hyf' (has hy)
      rwa [huniq s hs e he f hf hes hfs]
  -- The perimeter edges of `s`.
  have hEf : (perimeter Γ' s).E.Finite := (perimeter Γ' s).finite_edges
  have hlen : perimeterLength Γ' s = ∑ h ∈ hEf.toFinset, perimN Γ' s h := by
    rw [perimeterLength, finsum_mem_eq_finite_toFinset_sum _ hEf]
    rfl
  -- Each perimeter edge of `s` is on the closure of a region of `G` in `s`.
  have hcover : ∀ h ∈ hEf.toFinset, ∃ p ∈ P, h ⊆ closure p := fun h hh => by
    obtain ⟨hhE, hhc⟩ := mem_interSet_E_iff.mp (hEf.mem_toFinset.mp hh)
    obtain ⟨y, hy⟩ := hhE.1
    have hyU : y ∉ Γ.U := fun h' =>
      edge_notMem_V hhE hy (hrad.2.1.2.1 (hrad.2.1.1.subset ⟨h', hhE.2.1 hy |>.1⟩))
    have hclo : y ∈ closure (⋃ p ∈ P, p) := by
      refine mem_closure_iff.mpr fun O hO hyO => ?_
      obtain ⟨z, ⟨hzO, hzU⟩, hzs⟩ := mem_closure_iff.mp (hhc hy) (O ∩ Γ.Uᶜ)
        (hO.inter hUc.isOpen_compl) ⟨hyO, hyU⟩
      have hzG : z ∉ G.U := fun h' => (hGU h').elim (region_subset hs hzs) hzU
      obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzG
      have hps : p ⊆ s := subset_region hs (region_isPreconnected hp)
        (disjoint_left.mpr fun x hx h' => region_subset hp hx (hsub.U_subset h')) hzp hzs
      exact ⟨z, hzO, mem_iUnion₂.mpr ⟨p, (hP p).mpr ⟨hp, hps⟩, hzp⟩⟩
    have hfin : ((P : Finset (Set S)) : Set (Set S)).Finite := P.finite_toSet
    rw [show (⋃ p ∈ P, p) = ⋃ p ∈ (P : Set (Set S)), p from rfl, hfin.closure_biUnion] at hclo
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hclo
    have hp' := (hP p).mp hp
    exact ⟨p, hp, edge_subset_closure_of_incident hS (hsub.2 hhE) hp'.1 ⟨y, hy, hyp⟩⟩
  -- The centre of `e` in `G`.
  have hcell : cellInt e ∈ D.R := hDR ▸ Or.inr ⟨e, he, rfl⟩
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hGrad.2.1.2.2.1 _ hcell
  have hcU : c ∉ Γ'.U := fun hc' => by
    have hcV' : c ∈ Γ.V := hrad.2.1.1.subset ⟨closure_subset_cell_U hpre he hc.1, hc'⟩
    exact hc.2 (Cell.closure_inter_V_subset hS he ⟨hc.1, hcV'⟩)
  -- The centre is on the closure of each region of `G` in `s`, and has an edge there.
  have hat : ∀ p ∈ P, c ∈ closure p ∧ ∃ f ∈ G.E, c ∈ closure f := fun p hp => by
    obtain ⟨hpR, hps⟩ := (hP p).mp hp
    obtain ⟨a, ha, hap⟩ := hex p hpR
    obtain ⟨y, hy⟩ := ha.1
    have hyb := hbd ha (hap.trans hps) hy
    have hyc : y ∈ closure (closure e \ discBd (closure e)) :=
      discBd_subset_closure (Cell.isClosedDisc_closure he) hyb
    obtain ⟨z, hzp, hzi⟩ := mem_closure_iff.mp hyc p (region_isOpen hpR) (hap hy)
    obtain ⟨p', hp', q', hq', -, -, -, hseq⟩ := region_eq_two_faces hGpre hS hGmax hDE hpR ha hap
    have key : ∀ t ∈ (radialUnion hGpre).R, t ⊆ p → z ∈ t → c ∈ closure p
      ∧ ∃ f ∈ G.E, c ∈ closure f := by
      intro t ht htp hzt
      obtain ⟨r, hr, htr⟩ := exists_region_of_sub hGpre ht
      obtain rfl : r = cellInt e := region_eq_of_mem hr hcell (htr hzt) hzi
      obtain ⟨f, -, hf, -, hft, -⟩ := hub_sides hGpre hS hGmax hDE hr ht htr
      obtain ⟨v, -, r₁, hr₁, w, hw, hwV, hcap, hfr₁⟩ := spoke_ends hGpre hS hf
      obtain ⟨x, hx⟩ := hf.1
      obtain ⟨u, hu₁, hu⟩ := mem_closure_iff.mp (closure_mono htr (hft hx)) r₁ (region_isOpen hr₁)
        (hfr₁ hx)
      obtain rfl : r₁ = cellInt e := region_eq_of_mem hr₁ hr hu₁ hu
      have hwc : w = c := hub_unique hGpre hr hc hcV hw hwV
      have hcf : c ∈ closure f ∩ G.V := by
        rw [hcap, hwc]
        simp
      exact ⟨closure_mono htp (closure_minimal hft isClosed_closure hcf.1), f, hf, hcf.1⟩
    have hzs : z ∈ p' ∪ q' ∪ a := hseq ▸ hzp
    rcases hzs with (h | h) | h
    · exact key p' hp' (fun x hx => hseq ▸ Or.inl (Or.inl hx)) h
    · exact key q' hq' (fun x hx => hseq ▸ Or.inl (Or.inr hx)) h
    · exact absurd (hbd ha (hap.trans hps) h) hzi.2
  -- Each region of `G` in `s` has weight at most 2 on the perimeter edges of `s`.
  have hweight : ∀ p ∈ P, ∑ h ∈ hEf.toFinset, (if h ⊆ closure p then perimN G p h else 0) ≤ 2
    := fun p hp => by
    obtain ⟨hpR, hps⟩ := (hP p).mp hp
    obtain ⟨hcp, f, hf, hcf⟩ := hat p hp
    obtain ⟨T, hT, hT2⟩ := two_le_of_spoke hS (two_ends_of_preRadial hGrad.2.1) hpR hcV hcp hf hcf
    have hEp : (perimeter G p).E.Finite := (perimeter G p).finite_edges
    have hlenp : perimeterLength G p = ∑ h ∈ hEp.toFinset, perimN G p h := by
      rw [perimeterLength, finsum_mem_eq_finite_toFinset_sum _ hEp]
      rfl
    have h4 := perimeterLength_le_four hGpre hS hGmax hDE hpR
    rw [← Finset.sum_filter]
    have hA : hEf.toFinset.filter (· ⊆ closure p) ⊆ hEp.toFinset := fun h hh => by
      obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hh
      exact hEp.mem_toFinset.mpr (mem_interSet_E_iff.mpr
        ⟨hsub.2 (mem_interSet_E_iff.mp (hEf.mem_toFinset.mp h₁)).1, h₂⟩)
    have hTs : T ⊆ hEp.toFinset := fun h hh =>
      hEp.mem_toFinset.mpr (mem_interSet_E_iff.mpr ⟨(hT h hh).1, (hT h hh).2.1⟩)
    have hdis : Disjoint (hEf.toFinset.filter (· ⊆ closure p)) T := Finset.disjoint_left.mpr fun h
      h₁ h₂ => by
      obtain ⟨h₃, -⟩ := Finset.mem_filter.mp h₁
      exact hcU (Γ'.closure_subset_U (mem_interSet_E_iff.mp (hEf.mem_toFinset.mp h₃)).1
        (hT h h₂).2.2)
    have hsum := Finset.sum_le_sum_of_subset (f := perimN G p) (Finset.union_subset hA hTs)
    rw [Finset.sum_union hdis] at hsum
    omega
  -- There are at most as many such regions as sides of `e`.
  have hcount : P.card ≤ (Γ.V ∩ closure e).ncard := by
    have hB := (Cell.isClosedDisc_closure he).isOArc_discBd
    have hBU : discBd (closure e) ⊆ D.U := by
      rw [hDU]
      exact fun x hx => Or.inr (mem_iUnion₂.mpr ⟨e, he, hx⟩)
    obtain ⟨C, hC, hCs, hCU⟩ := exists_circuit_of_oArc hB hBU
    have hCf : C.E.Finite := C.finite_edges
    have hle₁ : (Γ.V ∩ closure e).ncard ≥ C.V.ncard := by
      refine ncard_le_ncard (fun x hx => ⟨hDV ▸ hCs.1 hx, ?_⟩) (Γ.finite_V.subset inter_subset_left)
      exact discBd_subset _ (hCU ▸ C.V_subset_U hx)
    have hle₂ : C.length ≤ C.V.ncard := length_le_ncard_V hC
    choose! a ha hap using fun p (hp : p ∈ P) => hex p ((hP p).mp hp).1
    have hmem : ∀ p ∈ P, a p ∈ C.E := fun p hp => by
      obtain ⟨y, hy⟩ := (ha p hp).1
      have hyb := hbd (ha p hp) ((hap p hp).trans ((hP p).mp hp).2) hy
      have hyV : y ∉ C.V := fun h' => ((ha p hp).2.1 hy).2 (hCs.1 h')
      obtain ⟨a', ha', hya'⟩ := exists_mem_arcComponent (show y ∈ C.U \ C.V from ⟨hCU ▸ hyb, hyV⟩)
      have := arcComponent_eq (ha p hp) (hCs.2 ha') hy hya'
      rwa [this]
    have hinj : Set.InjOn a (P : Set (Set S)) := fun p hp q hq hpq => by
      obtain ⟨y, hy⟩ := (ha p hp).1
      exact region_eq_of_mem ((hP p).mp hp).1 ((hP q).mp hq).1 (hap p hp hy) (hap q hq (hpq ▸ hy))
    have := Finset.card_le_card_of_injOn a (s := P) (t := hCf.toFinset)
      (fun p hp => hCf.mem_toFinset.mpr (hmem p hp)) hinj
    have hlenC : C.length = hCf.toFinset.card := by
      rw [Drawing.length, ncard_eq_toFinset_card _ hCf]
    omega
  calc perimeterLength Γ' s = ∑ h ∈ hEf.toFinset, perimN Γ' s h := hlen
    _ ≤ ∑ h ∈ hEf.toFinset, ∑ p ∈ P, (if h ⊆ closure p then perimN G p h else 0)
      := Finset.sum_le_sum fun h hh => by
        obtain ⟨p₀, hp₀, hh₀⟩ := hcover h hh
        exact perimN_le_sum hsub hS hP (mem_interSet_E_iff.mp (hEf.mem_toFinset.mp hh)).1 hp₀ hh₀
    _ = ∑ p ∈ P, ∑ h ∈ hEf.toFinset, (if h ⊆ closure p then perimN G p h else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ P, 2 := Finset.sum_le_sum hweight
    _ = 2 * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * (Γ.V ∩ closure e).ncard := Nat.mul_le_mul_left 2 hcount

end GraphMinor.GM11
