/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingFlat
public import LeanPool.GraphMinor.GM11.Theorem63
public import LeanPool.GraphMinor.GM11.Section5c
public import LeanPool.GraphMinor.GM11.GlueDiscs

/-!
# Theorem (6.1) of Graph Minors XI

Graph Minors XI, (6.1), page 87: the pretangle induced from a slope is a respectful pretangle, and
the slope is derived
from it.

The first and third parts follow the paper. For respectfulness we take another route. In a sphere,
each `O`-arc bounds two discs that are each other's outside, so the first tangle axiom picks one of
them. In any other
surface, a `Γ`-normal `O`-arc `F` with `|F ∩ V(Γ)| < θ` lies in the flat set of
`exists_flat_regions`, so it is
null-homotopic and bounds a disc `Δ`. Claims (1) and (2) of (6.4) then decide that `(Γ ∩ Δ, Γ ∩
closure (Σ - Δ)) ∈ 𝒯`.
So we do not need the step of the paper that perturbs `F` onto a circuit of `Γ'`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

section Sep

variable {Γ : PaintingOrDrawing S}

omit [T2Space S] in
/-- For a closed set `X`, `Γ ∩ X` is a subhypergraph of `Γ`. -/
theorem inter_le {X : Set S} (hX : IsClosed X) :
    Γ.inter X ≤ Γ.toHypergraph where
  vertexSet_subset := fun _ h => Γ.toHypergraph_vertexSet ▸ h.1
  edgeSet_subset := fun _ h => Γ.toHypergraph_edgeSet ▸ h.1
  ends_eq := fun e he => by
    ext v
    exact ⟨fun h => ⟨h, he.2, hX.closure_subset_iff.mpr he.2
      (PaintingOrDrawing.toHypergraph_inc.mp h).2.2⟩, fun h => h.1⟩

omit [T2Space S] in
/-- A closed set whose frontier is `Γ`-normal gives a separation of `Γ`. -/
theorem isSeparation_inter {Δ : Set S} (hΔ : IsClosed Δ) (hn : frontier Δ ∩ Γ.U ⊆ Γ.V) :
    Γ.toHypergraph.IsSeparation (Γ.inter Δ)
      (Γ.interOutside Δ) := by
  have hcov : ∀ x, x ∈ Δ ∨ x ∈ closure (univ \ Δ) := fun x => by
    by_cases hx : x ∈ Δ
    · exact Or.inl hx
    · exact Or.inr (subset_closure ⟨mem_univ x, hx⟩)
  have hedge : ∀ e ∈ Γ.E, e ⊆ Δ ∨ e ⊆ closure (univ \ Δ) := fun e he => by
    by_cases heΔ : e ⊆ Δ
    · exact Or.inl heΔ
    · right
      obtain ⟨x, hx, hxΔ⟩ := not_subset.mp heΔ
      have hsu : e ⊆ interior Δ ∪ Δᶜ := fun y hy => by
        by_cases hyi : y ∈ Δ
        · refine Or.inl ?_
          by_contra hn'
          have hyf : y ∈ frontier Δ := ⟨subset_closure hyi, hn'⟩
          exact disjoint_left.mp (Γ.edge_props he).2.1 hy (hn ⟨hyf, (Γ.edge_props he).2.2.1 hy⟩)
        · exact Or.inr hyi
      have hec : IsPreconnected e := (Γ.edge_props he).1
      have := hec.subset_right_of_subset_union isOpen_interior hΔ.isOpen_compl
        (disjoint_left.mpr fun x h₁ h₂ => h₂ (interior_subset h₁)) hsu ⟨x, hx, hxΔ⟩
      exact fun y hy => subset_closure ⟨mem_univ y, this hy⟩
  refine ⟨inter_le hΔ, inter_le isClosed_closure, ?_, ?_⟩
  · apply Hypergraph.ext
    · change (Γ.V ∩ Δ) ∪ (Γ.V ∩ closure (univ \ Δ)) = Γ.toHypergraph.vertexSet
      rw [Γ.toHypergraph_vertexSet]
      ext x
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        exact (hcov x).imp (fun h' => ⟨h, h'⟩) fun h' => ⟨h, h'⟩
    · change {e | e ∈ Γ.E ∧ e ⊆ Δ} ∪ {e | e ∈ Γ.E ∧ e ⊆ closure (univ \ Δ)} = Γ.toHypergraph.edgeSet
      rw [Γ.toHypergraph_edgeSet]
      ext e
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        exact (hedge e h).imp (fun h' => ⟨h, h'⟩) fun h' => ⟨h, h'⟩
    · funext e v
      apply propext
      change (Γ.toHypergraph.Inc e v ∧ e ⊆ Δ ∧ v ∈ Δ) ∨
        (Γ.toHypergraph.Inc e v ∧ e ⊆ closure (univ \ Δ) ∧ v ∈ closure
          (univ \ Δ)) ↔ Γ.toHypergraph.Inc e v
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        have hi := PaintingOrDrawing.toHypergraph_inc.mp h
        rcases hedge e hi.1 with h' | h'
        · exact Or.inl ⟨h, h', hΔ.closure_subset_iff.mpr h' hi.2.2⟩
        · exact Or.inr ⟨h, h', isClosed_closure.closure_subset_iff.mpr h' hi.2.2⟩
  · refine eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨⟨he₁, h₁⟩, ⟨-, h₂⟩⟩ := he
    obtain ⟨y, hy⟩ := (Γ.edge_props he₁).2.2.2
    have hyf : y ∈ frontier Δ := by
      rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
      exact ⟨subset_closure (h₁ hy), h₂ hy⟩
    exact disjoint_left.mp (Γ.edge_props he₁).2.1 hy (hn ⟨hyf, (Γ.edge_props he₁).2.2.1 hy⟩)

omit [T2Space S] in
/-- The vertices common to the two sides lie on the frontier. -/
theorem inter_outside_subset {Δ : Set S} {x : S}
    (hx : x ∈ (Γ.inter Δ ∩ Γ.interOutside Δ).vertexSet) :
    x ∈ frontier Δ ∩ Γ.V := by
  obtain ⟨⟨hxV, hxΔ⟩, -, hxc⟩ := hx
  refine ⟨?_, hxV⟩
  rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
  exact ⟨subset_closure hxΔ, hxc⟩

end Sep

variable [ConnectedSpace S] {Γ : PaintingOrDrawing S} {Γ' : Drawing S} {θ : ℕ} {ins : Drawing S
  → Set S}

/-- `RegionFacts` for a painting or drawing. -/
theorem regionFacts_any (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) (hrad : Γ.IsRadialDrawing Γ') :
    RegionFacts Γ Γ' := by
  cases Γ with
  | painting Γ => exact regionFacts_of_painting ⟨hrad.1, hrad.2.1⟩ hrad.2.2 hS hE
  | drawing Γ => exact regionFacts_of_radial ⟨hrad.1, hrad.2.1⟩ hS hrad.2.2 hE

/-- **Graph Minors XI, (6.1)** (page 87), the first part: the set induced from a slope is a
pretangle. -/
theorem isPretangle_induced (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hrad : Γ.IsRadialDrawing Γ') (hθ : 1 ≤ θ) (hsl : IsSlope Γ' (2 * θ) ins) :
    IsPretangle Γ.toHypergraph θ (inducedPretangle Γ Γ' θ ins) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hf : RegionFacts Γ Γ' := regionFacts_any hS hE hrad
  have hw : IsWeighting Γ' (2 * θ) Γ.V θ := isWeighting_radial hθ hrad.2.1.2.1
    (bipartite_of_preRadial hrad.2.1)
  refine ⟨hθ, fun A B h => h.1, fun A B h => h.2.1, fun A B hsep hord => ?_,
    fun A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU => ?_⟩
  · rcases (small_or_small hS hf hsl hw hsep hord).1 with h | h
    · exact Or.inl ⟨hsep, hord, h⟩
    · exact Or.inr ⟨hsep.symm, by rwa [GM10.separationOrder_comm], h⟩
  · refine theorem_5_5_proof hS hsl hw h₁.2.2 h₂.2.2 h₃.2.2 ?_
    ext s
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hs
      obtain ⟨e, he, hes⟩ := hf.1 s hs
      have he' : e ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := by
        rw [hU]
        exact Γ.toHypergraph_edgeSet ▸ he
      rcases he' with (h | h) | h
      · exact Or.inl (Or.inl ⟨hs, e, h, hes⟩)
      · exact Or.inl (Or.inr ⟨hs, e, h, hes⟩)
      · exact Or.inr ⟨hs, e, h, hes⟩

/-- **Graph Minors XI, (6.1)** (page 87), the last part: "`ins` is the slope derived from `𝒯`". -/
theorem isDerivedSlope_induced (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hrad : Γ.IsRadialDrawing Γ') (hsl : IsSlope Γ' (2 * θ) ins) :
    IsDerivedSlope Γ Γ' θ (inducedPretangle Γ Γ' θ ins) ins := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hf : RegionFacts Γ Γ' := regionFacts_any hS hE hrad
  intro C hC hCs hl
  have hd := hsl.isClosedDisc C hC hCs hl
  have hb := hsl.subBd_eq C hC hCs hl
  refine ⟨hd, hb, ?_⟩
  have hfr : frontier (ins C) = C.U := by rw [← subBd_eq_frontier, hb]
  have hcl := (IsClosedDisc.isCompact hd).isClosed
  have hsep := isSeparation_inter (Γ := Γ) hcl (by
    rw [hfr]
    rintro x ⟨hx, hxU⟩
    exact hrad.2.1.1.subset ⟨hxU, hCs.U_subset hx⟩)
  have hord : separationOrder (Γ.inter (ins C))
      (Γ.interOutside (ins C)) < θ := by
    have h₁ := two_mul_ncard_le_length Γ.V (bipartite_of_preRadial hrad.2.1) hC hCs
    have h₂ : (Γ.V ∩ C.V).Finite := C.finite_V.subset inter_subset_right
    have h₃ := ncard_le_ncard (s := (Γ.inter (ins C) ∩
      Γ.interOutside (ins C)).vertexSet) (fun x hx => by
        have := inter_outside_vertex hrad.2.1.2.1 hCs hfr hx
        exact ⟨this.2, this.1⟩) h₂
    rw [separationOrder]
    omega
  refine ⟨hsep, hord, ?_⟩
  have hZ : PaintingOrDrawing.regionsIncludingEdge Γ' (Γ.inter (ins C)) =
      insideRegions Γ' (ins C) := by
    ext s
    constructor
    · rintro ⟨hs, e, he, hes⟩
      obtain ⟨y, hy⟩ := (Γ.edge_props he.1).2.2.2
      refine ⟨hs, (region_subset_or_disjoint hsl hC hCs hl hs).resolve_right fun h => ?_⟩
      exact disjoint_left.mp h (hes hy) (he.2 hy)
    · rintro ⟨hs, hsi⟩
      obtain ⟨e, he, hes⟩ := hf.1 s hs
      exact ⟨hs, e, ⟨he, hes.trans hsi⟩, hes⟩
  have hN := boundaryDrawing_inside hS hsl hC hCs hl
  rw [hZ]
  refine ⟨?_, ?_⟩
  · rw [hN]
    have h₁ := two_mul_ncard_le_length Γ.V (bipartite_of_preRadial hrad.2.1) hC hCs
    change (Γ.V ∩ C.V).ncard < θ
    omega
  · rintro r ⟨-, hr⟩
    rw [hN]
    exact ⟨C, hC, Drawing.IsSubdrawing.refl C, hl, hr⟩

/-- **Graph Minors XI, (6.1)** (page 87), the middle part: the pretangle induced from a slope is
respectful. -/
theorem isRespectful_induced (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hrad : Γ.IsRadialDrawing Γ') (hθ : 1 ≤ θ) (hsl : IsSlope Γ' (2 * θ) ins) :
    Γ.IsRespectful θ (inducedPretangle Γ Γ' θ ins) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hf : RegionFacts Γ Γ' := regionFacts_any hS hE hrad
  have hVf : Γ.V.Finite := Γ.toHypergraph_vertexSet ▸ Γ.toHypergraph.vertexSet_finite
  have hT := isPretangle_induced hS hE hrad hθ hsl
  have hd := isDerivedSlope_induced hS hE hrad hsl
  refine ⟨inferInstance, fun F hF hN hk => ?_⟩
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  -- A closed disc bounded by `F` gives a separation of small order.
  have hsepΔ : ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F →
      Γ.toHypergraph.IsSeparation (Γ.inter Δ)
        (Γ.interOutside Δ) ∧
      separationOrder (Γ.inter Δ) (Γ.interOutside Δ) < θ := by
    intro Δ hΔ hb
    have hfr : frontier Δ = F := by rw [IsClosedDisc.frontier_eq_discBd hS hΔ, hb]
    refine ⟨isSeparation_inter (IsClosedDisc.isCompact hΔ).isClosed (by rw [hfr]; exact hN), ?_⟩
    refine (ncard_le_ncard (fun x hx => ?_) (hVf.subset inter_subset_right)).trans_lt hk
    rw [← hfr]
    exact inter_outside_subset hx
  have hbd : ∀ Δ : Set S, IsClosedDisc Δ → subBd Δ = discBd Δ := fun Δ hΔ => by
    rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hΔ]
  by_cases hsph : IsSphere S
  · obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, -⟩ := sphere_disc S hsph F hF
    have hout : ∀ {Δ Δ' : Set S}, IsClosedDisc Δ → IsClosedDisc Δ' → discBd Δ' = F → Δ ∪ Δ' = univ
      → Δ ∩ Δ' = F →
        closure (univ \ Δ) = Δ' := fun {Δ Δ'} h h' hb' hu hi => by
      apply Subset.antisymm
      · refine closure_minimal (fun x hx => ?_) (IsClosedDisc.isCompact h').isClosed
        exact ((hu.ge (mem_univ x)).resolve_left hx.2)
      · refine (IsClosedDisc.subset_closure_discInt h').trans (closure_mono fun x hx => ?_)
        refine ⟨mem_univ x, fun hxΔ => hx.2 ?_⟩
        rw [hb', ← hi]
        exact ⟨hxΔ, hx.1⟩
    have h₁₂ := hout hΔ₁ hΔ₂ hb₂ hcup hcap
    have h₂₁ := hout hΔ₂ hΔ₁ hb₁ (by rw [union_comm, hcup]) (by rw [inter_comm, hcap])
    obtain ⟨hsep, hord⟩ := hsepΔ Δ₁ hΔ₁ hb₁
    rcases hT.axiom1 hsep hord with h | h
    · exact ⟨Δ₁, hΔ₁, (hbd _ hΔ₁).trans hb₁, h⟩
    · refine ⟨Δ₂, hΔ₂, (hbd _ hΔ₂).trans hb₂, ?_⟩
      have e₁ : Γ.interOutside Δ₁ = Γ.inter Δ₂ := by
        rw [PaintingOrDrawing.interOutside, h₁₂]
      have e₂ : Γ.interOutside Δ₂ = Γ.inter Δ₁ := by
        rw [PaintingOrDrawing.interOutside, h₂₁]
      rw [e₂]
      rwa [e₁] at h
  · have hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ
      → IsNullHomotopicOArc C.U :=
      fun C hC hCs hl => null_of_short hd hC hCs hl
    obtain ⟨D, -, hsD, hfl⟩ := exists_flat_of_not_sphere hS hsph hE hrad hθ hnull (S₀
      := F ∩ Γ.V) inter_subset_right
      (hVf.subset inter_subset_right) hk
    have hFK : F ⊆ (⋃ r ∈ Γ.R, r) ∪ ⋃ s ∈ F ∩ Γ.V, D s := fun x hx => by
      by_cases hxU : x ∈ Γ.U
      · have hxV : x ∈ F ∩ Γ.V := ⟨hx, hN ⟨hx, hxU⟩⟩
        exact Or.inr (mem_iUnion₂.mpr ⟨x, hxV, hsD x hxV⟩)
      · obtain ⟨r, hr, hxr⟩ := exists_mem_region hxU
        exact Or.inl (mem_iUnion₂.mpr ⟨r, hr, hxr⟩)
    have hFn := null_of_flat hfl hF hFK
    have hbdS : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx => hx (hS.2.2 x)
    obtain ⟨Δ, -, hΔ, hb⟩ := (epstein S univ F (IsClosedSurface.isSurface hS) inferInstance hF
      (subset_univ _)
      hbdS).1 hFn
    obtain ⟨hsep, hord⟩ := hsepΔ Δ hΔ hb
    refine ⟨Δ, hΔ, (hbd _ hΔ).trans hb, ?_⟩
    refine (hT.axiom1 hsep hord).resolve_right fun hBA => ?_
    have hUA : PaintingOrDrawing.underlying (Γ.inter Δ) ⊆ Δ := by
      rintro x (hx | hx)
      · exact hx.2
      · obtain ⟨e, he, hxe⟩ := hx
        exact he.2 hxe
    obtain ⟨F', hF', hsub, hnn⟩ := exists_oArc_of_null_any hS hsph hE hrad hθ hd hsep hord fun G hG
      hGo =>
      isNullHomotopicOArcIn_of_subset_disc hGo (subset_univ _) hΔ (hG.trans hUA)
    obtain ⟨k', C, hC, hcov⟩ := circuits_of_small hS hf hrad.2.1.1 hsep.symm hBA.2.2
    exact hnn (no_oArc_of_circuits hS hsph hθ hrad hd hBA.2.1 hC hcov hF' fun x hx => (hsub hx).1)

/-- **Graph Minors XI, (6.1)** (page 87). -/
theorem theorem_6_1_proof (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hrad : Γ.IsRadialDrawing Γ') (hθ : 1 ≤ θ) (hsl : IsSlope Γ' (2 * θ) ins) :
    IsPretangle Γ.toHypergraph θ (inducedPretangle Γ Γ' θ ins) ∧
      Γ.IsRespectful θ (inducedPretangle Γ Γ' θ ins) ∧
      IsDerivedSlope Γ Γ' θ (inducedPretangle Γ Γ' θ ins) ins :=
  ⟨isPretangle_induced hS hE hrad hθ hsl, isRespectful_induced hS hE hrad hθ hsl,
    isDerivedSlope_induced hS hE hrad hsl⟩

end GraphMinor.GM11
