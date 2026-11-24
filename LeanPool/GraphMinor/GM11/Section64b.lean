/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section64
public import LeanPool.GraphMinor.GM11.StarChart

/-!
# Claim (2) of (6.4) of Graph Minors XI, for drawings

Graph Minors XI, (6.4), pages 90–91. Let `(A, B)` be a separation of a 2-cell drawing `Γ` in a
surface that is not a
sphere. The paper shows that `Γ \ V(A ∩ B)` is 1-representative, "similar" to the case of paintings,
and then uses
(7.5). Here is the same proof with the steps written out.

`Q` is `U(Γ)` with a small piece of each edge removed near `V(A ∩ B)`. If each `O`-arc of `U(Γ) -
V(A ∩ B)` is
null-homotopic, then (7.5) gives a closed disc that contains `Q`. The outside of the disc lies in
the union of the
regions of `Γ` and small discs around the points of `V(A ∩ B)`. That union is flat by
`flat_iUnion_cover`: its pieces
are joined along edges of `Γ'` at `V(A ∩ B)`, whose circuits are null-homotopic since they are
short. This contradicts
`not_flat_compl_disc`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S]

theorem cl_symm_trans_symm {a b c : S} (f : Cl a b) (g : Cl b c) : (f.trans g).symm
  = g.symm.trans f.symm := by
  induction f using Path.Homotopic.Quotient.ind with | mk f => ?_
  induction g using Path.Homotopic.Quotient.ind with | mk g => ?_
  simp only [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm, Path.trans_symm]

/-- In a line, each point other than the first end is joined to the last end, off the first end. -/
theorem joinedIn_line {L : Set S} {x y p : S} (hL : IsLineWithEnds L x y) (hp : p ∈ L)
  (hpx : p ≠ x) :
    JoinedIn (L \ {x}) p y := by
  obtain ⟨f, h0, h1⟩ := hL
  have hne : (f.symm ⟨p, hp⟩ : I) ≠ 0 := fun h => hpx (by
    have := f.apply_symm_apply ⟨p, hp⟩
    rw [h] at this
    rw [← h0, this])
  set a : I := f.symm ⟨p, hp⟩ with ha
  have ha0 : 0 < a.1 := lt_of_le_of_ne a.2.1 fun h => hne (Subtype.ext h.symm)
  let m : I → I := fun t => ⟨a.1 + t.1 * (1 - a.1), by
    have := t.2.1
    have := a.2.2
    have := a.2.1
    nlinarith, by
    have := t.2.2
    have := a.2.2
    nlinarith⟩
  have hm : Continuous m := Continuous.subtype_mk (by fun_prop) _
  refine ⟨⟨⟨fun t => (f (m t)).1, by fun_prop⟩, ?_, ?_⟩, fun t => ⟨(f (m t)).2, ?_⟩⟩
  · have : m 0 = a := Subtype.ext (by simp [m])
    simp [this, ha]
  · have : m 1 = 1 := Subtype.ext (by simp [m])
    simp [this, h1]
  · intro h
    have h' : f (m t) = f 0 := Subtype.ext (by rw [h0]; exact h)
    have := congrArg Subtype.val (f.injective h')
    have ht := t.2.1
    have ht1 := a.2.2
    simp only [m] at this
    simp at this
    nlinarith

section Sep

variable {Γ : PaintingOrDrawing S} {A B : Hypergraph S (Set S)}

/-- `U(A)` is the union of `V(A)` and the closures of the edges of `A`. -/
theorem underlying_eq (hcl : ∀ e ∈ Γ.E, closure e \ Γ.V ⊆ e) (hA : A ≤ Γ.toHypergraph) :
    PaintingOrDrawing.underlying A = A.vertexSet ∪ ⋃ e ∈ A.edgeSet, closure e := by
  apply subset_antisymm
  · rintro x (hx | ⟨e, he, hxe⟩)
    · exact Or.inl hx
    · exact Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hxe⟩)
  · rintro x (hx | hx)
    · exact Or.inl hx
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    have heG : e ∈ Γ.E := Γ.toHypergraph_edgeSet ▸ hA.edgeSet_subset he
    by_cases hxV : x ∈ Γ.V
    · have hinc : Γ.toHypergraph.Inc e x := PaintingOrDrawing.toHypergraph_inc.mpr ⟨heG, hxV, hxe⟩
      have : x ∈ A.ends e := by
        rw [← hA.ends_eq e he]
        exact hinc
      exact Or.inl (A.vertex_mem_of_inc this)
    · exact Or.inr ⟨e, he, hcl e heG ⟨hxe, hxV⟩⟩

theorem isClosed_underlying [T2Space S] (hcl : ∀ e ∈ Γ.E, closure e \ Γ.V ⊆ e) (hA : A
  ≤ Γ.toHypergraph) :
    IsClosed (PaintingOrDrawing.underlying A) := by
  rw [underlying_eq hcl hA]
  exact A.vertexSet_finite.isClosed.union (A.edgeSet_finite.isClosed_biUnion fun _ _
    => isClosed_closure)

theorem U_subset_underlying (hmem : ∀ x ∈ Γ.U, x ∉ Γ.V → ∃ e ∈ Γ.E, x ∈ e)
  (hsep : Γ.toHypergraph.IsSeparation A B) :
    Γ.U ⊆ PaintingOrDrawing.underlying A ∪ PaintingOrDrawing.underlying B := by
  have hV : A.vertexSet ∪ B.vertexSet = Γ.V := (congrArg Hypergraph.vertexSet hsep.union_eq).trans
    Γ.toHypergraph_vertexSet
  have hE : A.edgeSet ∪ B.edgeSet = Γ.E := (congrArg Hypergraph.edgeSet hsep.union_eq).trans
    Γ.toHypergraph_edgeSet
  intro x hx
  by_cases hxV : x ∈ Γ.V
  · rw [← hV] at hxV
    exact hxV.imp Or.inl Or.inl
  obtain ⟨e, he, hxe⟩ := hmem x hx hxV
  rw [← hE] at he
  exact he.imp (fun h => Or.inr ⟨e, h, hxe⟩) fun h => Or.inr ⟨e, h, hxe⟩

theorem underlying_inter (hdis : ∀ e ∈ Γ.E, ∀ f ∈ Γ.E, ∀ x, x ∈ e → x ∈ f → e = f)
  (hEV : ∀ e ∈ Γ.E, ∀ x ∈ e, x ∉ Γ.V)
    (hsep : Γ.toHypergraph.IsSeparation A B) :
    PaintingOrDrawing.underlying A ∩ PaintingOrDrawing.underlying B ⊆ (A ∩ B).vertexSet := by
  have hAV : ∀ x ∈ A.vertexSet, x ∈ Γ.V := fun x hx => Γ.toHypergraph_vertexSet ▸
    hsep.left_le.vertexSet_subset hx
  have hBV : ∀ x ∈ B.vertexSet, x ∈ Γ.V := fun x hx => Γ.toHypergraph_vertexSet ▸
    hsep.right_le.vertexSet_subset hx
  have hAE : ∀ e ∈ A.edgeSet, e ∈ Γ.E := fun e he => Γ.toHypergraph_edgeSet ▸
    hsep.left_le.edgeSet_subset he
  have hBE : ∀ e ∈ B.edgeSet, e ∈ Γ.E := fun e he => Γ.toHypergraph_edgeSet ▸
    hsep.right_le.edgeSet_subset he
  rintro x ⟨hx | ⟨e, he, hxe⟩, hx' | ⟨f, hf, hxf⟩⟩
  · exact ⟨hx, hx'⟩
  · exact absurd (hAV x hx) (hEV f (hBE f hf) x hxf)
  · exact absurd (hBV x hx') (hEV e (hAE e he) x hxe)
  · have : e = f := hdis e (hAE e he) f (hBE f hf) x hxe hxf
    subst this
    have h₀ : (A ∩ B).edgeSet = ∅ := hsep.edgeSet_inter_eq
    exact absurd (show e ∈ (A ∩ B).edgeSet from ⟨he, hf⟩) (by rw [h₀]; exact notMem_empty e)

end Sep

section Main

variable [ConnectedSpace S] {Γ Γ' : Drawing S} {θ : ℕ}
  {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}

private theorem old_vertices_in_star_neighborhood
    {S : Type u}
    [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S}
    {Γ' : Drawing S}
    (hS : IsClosedSurface S)
    {G₀ : Drawing S}
    (hG₀ : G₀.IsSubdrawing Γ')
    {S₀ : Set S}
    (hS₀V : S₀ ⊆ Γ.V)
    (hpre : PreRad (PaintingOrDrawing.drawing Γ) Γ')
    (hV'V : Γ.V ⊆ Γ'.V) :
    let edges := {e | e ∈ G₀.E ∧ ∃ s ∈ S₀, s ∈ closure e}
    Γ.V ∩ (G₀.span (S₀ ∪ G₀.V \ Γ.V) edges).V ⊆ S₀ := by
  intro edges
  rintro x ⟨hxV, (hx | hx)⟩
  · rcases hx.1 with h | h
    · exact h
    · exact absurd hxV h.2
  · obtain ⟨e, ⟨⟨heE, s, hs, hse⟩, -⟩, hxe⟩ := mem_iUnion₂.mp hx
    obtain ⟨v, hv, r, hr, w, hw, hwV, hcap, -⟩ := spoke_ends hpre hS (hG₀.2 heE)
    have hw' : w ∉ Γ.V := fun h => region_subset hr hw (Γ.V_subset_U h)
    have hv' : ∀ z ∈ Γ.V, z ∈ closure e ∩ Γ'.V → z = v := fun z hz hzc => by
      rw [hcap] at hzc
      rcases hzc with rfl | rfl
      · rfl
      · exact absurd hz hw'
    rw [hv' x hxV ⟨hxe.1, hV'V hxV⟩, ← hv' s (hS₀V hs) ⟨hse, hV'V (hS₀V hs)⟩]
    exact hs

/-- The regions of `Γ`, and a small open set around each vertex of a small set `S₀ ⊆ V(Γ)`, form a
flat set, if short
circuits of `Γ'` are null-homotopic. This is the core of claim (2) of (6.4) (pages 90–91). -/
theorem exists_flat_regions_of_sub (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ') (hθ : 1 ≤ θ) {G₀ : Drawing S}
      (hG₀ : G₀.IsSubdrawing Γ')
    {R₀ : Set (Set S)} (hR₀ : R₀ ⊆ Γ.R) (hspoke : ∀ h ∈ Γ'.E, ∀ r ∈ R₀, h ⊆ r → h ∈ G₀.E)
    (hhubV : ∀ r ∈ R₀, ∀ c ∈ r, c ∈ Γ'.V → c ∈ G₀.V)
    (hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing G₀ → C.length < 2 * θ
      → IsNullHomotopicOArc C.U)
    {S₀ : Set S} (hS₀V : S₀ ⊆ Γ.V) (hS₀G : S₀ ⊆ G₀.V) (hS₀f : S₀.Finite) (hord : S₀.ncard < θ) :
    ∃ D : S → Set S, (∀ s ∈ S₀, IsOpen (D s)) ∧ (∀ s ∈ S₀, s ∈ D s) ∧
      Flat ((⋃ r ∈ R₀, r) ∪ ⋃ s ∈ S₀, D s) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpre : PreRad (PaintingOrDrawing.drawing Γ) Γ' := ⟨hrad.1, hrad.2.1⟩
  have hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ' := hrad.2.2
  have hV'V : Γ.V ⊆ Γ'.V := hrad.2.1.2.1
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hpre)
  obtain ⟨Sep, hSep, hdisj⟩ := hS₀f.t2_separation
  have hgood : ∀ s ∈ S₀, ∃ D : Set S, IsOpen D ∧ s ∈ D ∧ D ⊆ Sep s ∧ IsSimplyConnectedSet D ∧
      ∀ r ∈ Γ.R, ∀ y, y ∈ r → y ∈ D → y ∉ (radialUnion hpre).U → ∃ k : halfEdges
        (radialUnion hpre) γ s,
        k.1.1 ∈ Γ'.E ∧ ∃ t : I, 0 < t ∧ (∀ u, u ≤ t → spoke γ k.1 u ∈ D) ∧ spoke γ k.1 t ∈ r ∧
          JoinedIn (r ∩ D) y (spoke γ k.1 t) := fun s hs => by
    have hsV := hS₀V hs
    have hsH : s ∈ (radialUnion hpre).V := by
      rw [radialUnion_V]
      exact hV'V hsV
    have h2 := two_half_edges hpre hS hmax hE hγ hsV
    obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS (radialUnion hpre) hγ hsH h2
    obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_sectors hS hγ hsH h2
    obtain ⟨D, hDo, hsD, hDsub, hDs, hstar⟩ := exists_star_nbhd hΦ ((IsSectors.isOpen hsec).inter
      (hSep s).2)
      ⟨IsSectors.mem hsec, (hSep s).1⟩
    exact ⟨D, hDo, hsD, fun x hx => (hDsub hx).2, hDs, fun r hr y hy hyD hyU =>
      sector_join hpre hS hmax hE hγ hsV hsec hΦ hDo hsD (fun x hx =>
        (hDsub hx).1) hstar hr hy hyD hyU⟩
  choose! D hDo hsD hDsub hDs hDjoin using hgood
  -- The flat set `Z`: the edges of `Γ'` at `S₀`, and the vertices of `Γ'` in regions.
  let Es : Set (Set S) := {h | h ∈ G₀.E ∧ ∃ s ∈ S₀, s ∈ closure h}
  let N : Drawing S := G₀.span (S₀ ∪ (G₀.V \ Γ.V)) Es
  have hNs : N.IsSubdrawing G₀ := Drawing.span_isSubdrawing G₀ _ _
  have hcloZ : ∀ h, h ∈ G₀.E → ∀ s ∈ S₀, s ∈ closure h → closure h ⊆ N.U := fun h hh s hs hsh x hx
    =>
    Or.inr (mem_iUnion₂.mpr ⟨h, ⟨⟨hh, s, hs, hsh⟩, hh⟩, hx⟩)
  have hsZ : ∀ s ∈ S₀, s ∈ N.U := fun s hs => Or.inl (Or.inl ⟨Or.inl hs, hS₀G hs⟩)
  have hcZ : ∀ {r c}, r ∈ R₀ → c ∈ r → c ∈ Γ'.V → c ∈ N.U := fun hr hc hcV =>
    Or.inl (Or.inl ⟨Or.inr ⟨hhubV _ hr _ hc hcV, fun h => region_subset (hR₀ hr) hc
      (Γ.V_subset_U h)⟩,
      hhubV _ hr _ hc hcV⟩)
  have hNV : Γ.V ∩ N.V ⊆ S₀ := by
    exact old_vertices_in_star_neighborhood (S := S) (Γ := Γ) (Γ' := Γ') hS (G₀ := G₀) hG₀ (S₀ :=
      S₀) hS₀V hpre hV'V
  have hweight : IsWeighting Γ' (2 * θ) (PaintingOrDrawing.drawing Γ).V θ :=
    isWeighting_radial hθ hV'V (bipartite_of_preRadial hrad.2.1)
  have hZf : Flat N.U := by
    refine flat_univ_iff.mp (flat_of_null_oArcs (Γ := N) hS N.isClosed_U ?_
      (subset_univ _) fun F hFZ hF => ?_)
    · exact isGammaNice_of_frontier (Drawing.IsSubdrawing.refl N) subset_rfl
        (N.isClosed_U.frontier_eq.subset.trans sdiff_subset)
    · obtain ⟨C, hC, hCs, rfl⟩ := exists_circuit_of_oArc hF hFZ
      refine hnull C hC (hCs.trans hNs) (not_le.mp fun hl => ?_)
      exact absurd (hweight.le_ncard C hC ((hCs.trans hNs).trans hG₀) hl)
        (not_le.mpr ((ncard_le_ncard
          (fun x (hx : x ∈ (PaintingOrDrawing.drawing Γ).V ∩ C.V) =>
            hNV ⟨hx.1, hCs.1 hx.2⟩) hS₀f).trans_lt hord))
  -- The triangle at a point of `r ∩ D s`.
  have htri' : ∀ r ∈ R₀, ∀ c ∈ r, c ∈ Γ'.V → ∀ s ∈ S₀, ∀ y, y ∈ r → y ∈ D s →
      ∃ (f : Cl c y) (g : Cl y s), Arw r f ∧ Arw (D s) g ∧ Arw N.U (f.trans g) := by
    intro r hr c hc hcV s hs y hy hyD
    have hBo : IsOpen (r ∩ D s) := (region_isOpen (hR₀ hr)).inter (hDo s hs)
    have hco := hBo.connectedComponentIn (x := y)
    have hpc := isPathConnected_of_isOpen hS hco isPreconnected_connectedComponentIn
      ⟨y, mem_connectedComponentIn ⟨hy, hyD⟩⟩
    obtain ⟨y₀, hy₀, hy₀U⟩ := exists_notMem_U (Γ := radialUnion hpre) hS hco
      ⟨y, mem_connectedComponentIn ⟨hy, hyD⟩⟩
    have hy₀B := connectedComponentIn_subset _ _ hy₀
    have hj₀ : JoinedIn (r ∩ D s) y y₀ := (hpc.joinedIn y (mem_connectedComponentIn ⟨hy, hyD⟩) y₀
      hy₀).mono
      (connectedComponentIn_subset _ _)
    obtain ⟨k, hkE, t, ht, hle, htr, hj₁⟩ := hDjoin s hs r (hR₀ hr) y₀ hy₀B.1 hy₀B.2 hy₀U
    have hj := hj₀.trans hj₁
    set p := spoke γ k.1 t with hp
    let β : Cl y p := Cl.mk hj.somePath
    have hβ : Arw (r ∩ D s) β := ⟨hj.somePath, fun u => hj.somePath_mem u, rfl⟩
    have hkH : k.1.1 ∈ (radialUnion hpre).E := k.2.1
    have hsc : s ∈ closure k.1.1 := by
      have := end_mem_closure hγ hkH k.1.2
      rwa [k.2.2] at this
    obtain ⟨v, hv, r₁, hr₁, w, hw, hwV, hcap, hsub⟩ := spoke_ends hpre hS hkE
    have hsv : s = v := by
      have : s ∈ closure k.1.1 ∩ Γ'.V := ⟨hsc, hV'V (hS₀V hs)⟩
      rw [hcap] at this
      rcases this with h | h
      · exact h
      · exact absurd (hS₀V hs) (fun h' => region_subset hr₁ hw (Γ.V_subset_U (h ▸ h')))
    subst hsv
    have hpe : p ∈ k.1.1 := spoke_mem_edge hγ hkH ht
    obtain rfl : r₁ = r := region_eq_of_mem hr₁ (hR₀ hr) (hsub hpe) htr
    have hkG : k.1.1 ∈ G₀.E := hspoke _ hkE _ hr hsub
    obtain rfl : w = c := hub_unique hpre hr₁ hc hcV hw hwV
    have hsw : s ≠ w := fun h => region_subset hr₁ hc (Γ.V_subset_U (h ▸ hv))
    have hline : IsLineWithEnds (closure k.1.1) s w := by
      rcases Γ'.edge_cond k.1.1 hkE with ⟨a, b, hab, hc', hL⟩ | ⟨a, hc', -⟩
      · rw [hcap] at hc'
        rcases (Set.pair_eq_pair_iff.mp hc') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hL
        · exact IsLineWithEnds.symm hL
      · rw [hcap] at hc'
        have h₁ : s ∈ ({a} : Set S) := hc' ▸ mem_insert _ _
        have h₂ : w ∈ ({a} : Set S) := hc' ▸ mem_insert_of_mem _ rfl
        exact absurd (h₁.trans h₂.symm) hsw
    have hsub' : closure k.1.1 \ {s} ⊆ r₁ ∩ N.U := by
      rintro z ⟨hz, hzs⟩
      refine ⟨?_, hcloZ _ hkG s hs hsc hz⟩
      by_cases hzV : z ∈ Γ'.V
      · have : z ∈ closure k.1.1 ∩ Γ'.V := ⟨hz, hzV⟩
        rw [hcap] at this
        rcases this with h | h
        · exact absurd h hzs
        · exact (mem_singleton_iff.mp h) ▸ hw
      · exact hsub ((Γ'.closure_diff_V hkE).subset ⟨hz, hzV⟩)
    have hps : p ≠ s := fun h => edge_notMem_V hkE hpe (h ▸ hV'V hv)
    have hja := (joinedIn_line hline (subset_closure hpe) hps).symm.mono hsub'
    let a : Cl w p := Cl.mk hja.somePath
    have ha : Arw (r₁ ∩ N.U) a := ⟨hja.somePath, fun u => hja.somePath_mem u, rfl⟩
    have hspc := continuous_spoke hγ hkH
    have hspoke' : ∀ u : I, spoke γ k.1 u ∈ closure k.1.1 := fun u => by
      rcases eq_or_lt_of_le (unitInterval.nonneg u) with h0 | h0
      · have h0' : u = 0 := Subtype.ext h0.symm
        rw [h0', spoke_zero]
        exact end_mem_closure hγ hkH _
      · exact subset_closure (spoke_mem_edge hγ hkH h0)
    let q : Path p s := ⟨⟨fun u => spoke γ k.1 (σ u * t), hspc.comp (by fun_prop)⟩, by simp [hp], by
      simp only [unitInterval.symm_one, zero_mul, spoke_zero]
      exact k.2.2⟩
    have hq : Arw (D s ∩ N.U) (Cl.mk q) := ⟨q, fun u => ⟨hle _ unitInterval.mul_le_right,
      hcloZ _ hkG s hs hsc (hspoke' _)⟩, rfl⟩
    refine ⟨a.trans β.symm, β.trans (Cl.mk q), (ha.mono inter_subset_left).trans
      (hβ.symm.mono inter_subset_left),
      (hβ.mono inter_subset_right).trans (hq.mono inter_subset_left), ?_⟩
    have : (a.trans β.symm).trans (β.trans (Cl.mk q)) = a.trans (Cl.mk q) := by
      rw [cl_assoc, cl_symm_trans_left]
    rw [this]
    exact (ha.mono inter_subset_right).trans (hq.mono inter_subset_right)
  -- The pieces.
  have hhub : ∀ r ∈ R₀, ∃ c, c ∈ r ∧ c ∈ Γ'.V := fun r hr => (hrad.2.1.2.2.1 r (hR₀ hr)).exists
  choose! hub hubr hubV using hhub
  let ι := {r // r ∈ R₀} ⊕ {s // s ∈ S₀}
  let O : ι → Set S := Sum.elim (fun r => r.1) fun s => D s.1
  let b : ι → S := Sum.elim (fun r => hub r.1) fun s => s.1
  have hOd : ∀ r ∈ R₀, IsSimplyConnectedSet r := fun r hr => IsOpenDisc.isSimplyConnectedSet
    (hrad.1.2 r (hR₀ hr))
  have hfl : Flat (⋃ i, O i) := by
    refine flat_iUnion_cover hZf O b ?_ ?_ ?_ ?_ ?_
    · rintro (r | s)
      · exact region_isOpen (hR₀ r.2)
      · exact hDo s.1 s.2
    · rintro (r | s)
      · exact hubr r.1 r.2
      · exact hsD s.1 s.2
    · rintro (r | s)
      · exact (hOd r.1 r.2).1
      · exact (hDs s.1 s.2).1
    · rintro (r | s)
      · exact IsSimplyConnectedSet.flat (hOd r.1 r.2)
      · exact IsSimplyConnectedSet.flat (hDs s.1 s.2)
    · rintro (r | s) (r' | s') y hy hy'
      · obtain rfl : r = r' := Subtype.ext (region_eq_of_mem (hR₀ r.2) (hR₀ r'.2) hy hy')
        have hj := (hOd r.1 r.2).1.joinedIn _ (hubr r.1 r.2) y hy
        refine ⟨Cl.mk hj.somePath, (Cl.mk hj.somePath).symm, ⟨_, hj.somePath_mem, rfl⟩,
          Arw.symm ⟨_, hj.somePath_mem, rfl⟩, ?_⟩
        have h : Arw N.U ((Cl.mk hj.somePath).trans (Cl.mk hj.somePath).symm) := by
          rw [cl_trans_symm]
          exact arw_refl (hcZ r.2 (hubr r.1 r.2) (hubV r.1 r.2))
        exact h
      · exact htri' r.1 r.2 _ (hubr r.1 r.2) (hubV r.1 r.2) s'.1 s'.2 y hy hy'
      · obtain ⟨f, g, hf, hg, hw⟩ := htri' r'.1 r'.2 _ (hubr r'.1 r'.2)
          (hubV r'.1 r'.2) s.1 s.2 y hy' hy
        refine ⟨g.symm, f.symm, hg.symm, hf.symm, ?_⟩
        have h : Arw N.U (g.symm.trans f.symm) := by
          rw [← cl_symm_trans_symm]
          exact hw.symm
        exact h
      · obtain rfl : s = s' := Subtype.ext (by
          by_contra hne
          exact disjoint_left.mp (hdisj s.2 s'.2 hne) (hDsub _ s.2 hy) (hDsub _ s'.2 hy'))
        have hj := (hDs s.1 s.2).1.joinedIn _ (hsD s.1 s.2) y hy
        refine ⟨Cl.mk hj.somePath, (Cl.mk hj.somePath).symm, ⟨_, hj.somePath_mem, rfl⟩,
          Arw.symm ⟨_, hj.somePath_mem, rfl⟩, ?_⟩
        have h : Arw N.U ((Cl.mk hj.somePath).trans (Cl.mk hj.somePath).symm) := by
          rw [cl_trans_symm]
          exact arw_refl (hsZ s.1 s.2)
        exact h
  refine ⟨D, hDo, hsD, ?_⟩
  have hK : (⋃ r ∈ R₀, r) ∪ (⋃ s ∈ S₀, D s) = ⋃ i, O i := by
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨r, hr, hx⟩ | ⟨s, hs, hx⟩)
      · exact ⟨Sum.inl ⟨r, hr⟩, hx⟩
      · exact ⟨Sum.inr ⟨s, hs⟩, hx⟩
    · rintro ⟨r | s, hx⟩
      · exact Or.inl ⟨r.1, r.2, hx⟩
      · exact Or.inr ⟨s.1, s.2, hx⟩
  rw [hK]
  exact hfl

/-- `exists_flat_regions_of_sub` for all regions of `Γ` and all edges of `Γ'`. -/
theorem exists_flat_regions (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ') (hθ : 1 ≤ θ)
    (hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ
      → IsNullHomotopicOArc C.U)
    {S₀ : Set S} (hS₀V : S₀ ⊆ Γ.V) (hS₀f : S₀.Finite) (hord : S₀.ncard < θ) :
    ∃ D : S → Set S, (∀ s ∈ S₀, IsOpen (D s)) ∧ (∀ s ∈ S₀, s ∈ D s) ∧
      Flat ((⋃ r ∈ Γ.R, r) ∪ ⋃ s ∈ S₀, D s) :=
  exists_flat_regions_of_sub hS hE hrad hθ (Drawing.IsSubdrawing.refl Γ') Subset.rfl (fun _ h _ _ _
    => h)
    (fun _ _ _ _ h => h) hnull hS₀V (hS₀V.trans hrad.2.1.2.1) hS₀f hord

/-- **Claim (2) of (6.4)** (pages 90–91), for a drawing. -/
theorem exists_oArc_of_null (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (hE : Γ.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ') (hθ : 1 ≤ θ)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ T ins) {A B : Hypergraph S (Set S)}
    (hsep : Γ.toHypergraph.IsSeparation A B) (hord : separationOrder A B < θ)
    (hA : ∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A → IsOArc F → IsNullHomotopicOArc F) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A ∧
      ¬ IsNullHomotopicOArc F := by
  by_contra hno
  push Not at hno
  have ht2 : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ
    → IsNullHomotopicOArc C.U :=
    fun C hC hCs hl => null_of_short hd hC hCs hl
  have hS₀V : (A ∩ B).vertexSet ⊆ Γ.V := fun x hx => hsep.left_le.vertexSet_subset hx.1
  obtain ⟨D, hDo, hsD, hfl⟩ := exists_flat_regions hS hE hrad hθ hnull hS₀V
    (A ∩ B).vertexSet_finite hord
  set S₀ : Set S := (A ∩ B).vertexSet with hS₀
  -- The closed set `Q`.
  obtain ⟨γ₀, hγ₀⟩ := exists_edgePar Γ
  obtain ⟨Q, hQc, hQn, hQU, hQc'⟩ := exists_cut_edges hγ₀ hS₀V hDo hsD
  have hcl : ∀ e ∈ (PaintingOrDrawing.drawing Γ).E, closure e \ (PaintingOrDrawing.drawing Γ).V ⊆ e
    := fun e he =>
    (Γ.closure_diff_V he).subset
  have hAc := isClosed_underlying (Γ := PaintingOrDrawing.drawing Γ) hcl hsep.left_le
  have hBc := isClosed_underlying (Γ := PaintingOrDrawing.drawing Γ) hcl hsep.right_le
  have hcov := U_subset_underlying (Γ := PaintingOrDrawing.drawing Γ)
    (fun x hx hxV => Γ.exists_edge_of_mem hx hxV) hsep
  have hint := underlying_inter (Γ := PaintingOrDrawing.drawing Γ)
    (fun e he f hf x hxe hxf => Γ.edge_eq_of_mem he hf hxe hxf) (fun e he x hx
      => edge_notMem_V he hx) hsep
  have hu : Q ≠ univ := fun h => by
    obtain ⟨z, -, hz⟩ := exists_notMem_U (Γ := Γ) hS isOpen_univ univ_nonempty
    exact hz (hQU (h ▸ mem_univ z)).1
  obtain ⟨Δ, hΔ, -, hQΔ⟩ := theorem_7_5_proof hS hQc hQn hu finite_empty
    (disjoint_empty _) fun F hFQ hF => by
    rw [sdiff_empty]
    have hFA : F ⊆ PaintingOrDrawing.underlying A ∪ PaintingOrDrawing.underlying B := fun x hx =>
      hcov (hQU (hFQ hx)).1
    by_cases hFa : F ⊆ PaintingOrDrawing.underlying A
    · exact hA F hFa hF
    · refine hno F hF fun x hx => ?_
      have hFB : F ⊆ PaintingOrDrawing.underlying B := by
        obtain ⟨a, ha, haA⟩ := not_subset.mp hFa
        by_contra hFb
        obtain ⟨c, hc, hcB⟩ := not_subset.mp hFb
        obtain ⟨z, hzF, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hF.isPreconnected _ _ hAc hBc hFA
          ⟨c, hc, (hFA hc).resolve_right hcB⟩ ⟨a, ha, (hFA ha).resolve_left haA⟩
        exact (hQU (hFQ hzF)).2 (hint ⟨hz₁, hz₂⟩)
      refine ⟨hFB hx, fun hxA => ?_⟩
      exact (hQU (hFQ hx)).2 (hint ⟨hxA, hFB hx⟩)
  refine not_flat_compl_disc hS hns hΔ (fun x hx => ?_) hfl
  have hxQ : x ∉ Q := fun h => hx (hQΔ h)
  by_cases hxU : x ∈ Γ.U
  · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (hQc' ⟨hxU, hxQ⟩)
    exact Or.inr (mem_iUnion₂.mpr ⟨s, hs, hxs⟩)
  · obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
    exact Or.inl (mem_iUnion₂.mpr ⟨r, hr, hxr⟩)

end Main

end GraphMinor.GM11
