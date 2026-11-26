/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section5c

/-!
# Graph Minors XI, Section 8: the regions in `ins(W)`

`theorem_8_2` is statement (8.2): three closed walks of length `< 2θ` do not cover `Σ` by their sets
`ins(W)`. The proof is the paper's. The set `Z` of regions in `ins(W)` is small with respect to the
weighting `(V(Γ), 2θ)`, and (5.5) applies. The paper derives "small" from (4.5). We use (5.2) and
(4.4)
instead: if the complement of `Z` were small, then the region outside `ins(W)` would be captured.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A list has at most as many distinct entries as its length. -/
theorem ncard_mem_list_le {α : Type*} (l : List α) : {x | x ∈ l}.ncard ≤ l.length := by
  classical
  have h : {x | x ∈ l} = (l.toFinset : Set α) := by
    ext x
    simp
  rw [h, ncard_coe_finset]
  exact List.toFinset_card_le l

/-- A circuit has as many vertices as edges. -/
theorem IsCircuit.length_le_ncard_V {C : Drawing S} (hC : C.IsCircuit) :
    C.length ≤ C.V.ncard := by
  classical
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := hC
  have hl : C.length = W.edges.length := by
    rw [Drawing.length, hE]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by
      ext x
      simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
  have hsub : (W.support.tail.toFinset : Set S) ⊆ C.V := by
    intro x hx
    rw [hV]
    exact List.mem_of_mem_tail (by simpa using hx)
  have hle := ncard_le_ncard hsub C.finite_V
  rw [ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_tail,
    length_support] at hle
  rw [hl]
  simpa [GraphWalk.length] using hle

variable [T2Space S] {Γ : Drawing S} {k : ℕ} {ins : Drawing S → Set S}

omit [T2Space S] in
/-- `(V(Γ), 2θ)` is a weighting of `Γ`. -/
theorem isWeighting_vertices (hk : 1 ≤ k) : IsWeighting Γ k Γ.V k where
  subset := subset_rfl
  one_le := hk
  le_ncard C hC hCs hl := by
    have heq : Γ.V ∩ C.V = C.V := inter_eq_right.mpr hCs.1
    rw [heq]
    exact hl.trans (IsCircuit.length_le_ncard_V hC)

variable [ConnectedSpace S] (hS : IsClosedSurface S)
  (hs : IsSlope Γ k ins)
include hS hs

/-- The regions in `ins(W)` form a small set, for a closed walk `W` of length `< 2θ` (Graph Minors
XI,
proof of (8.2), page 96). -/
theorem small_of_walk {u : S} (W : GraphWalk Γ.toGraph u u) (hW : W.length < k) :
    IsSmall Γ ins k Γ.V k (insideRegions Γ (insWalk ins Γ W)) := by
  have hk := hs.two_le
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hw : IsWeighting Γ k Γ.V k := isWeighting_vertices (by omega)
  set D := walkDrawing Γ W with hD
  set X := insWalk ins Γ W with hX
  set Z := insideRegions Γ X with hZ
  have hDs : D.IsSubdrawing Γ := walkDrawing_isSubdrawing Γ W
  have hconfD : IsConfined k D := by
    intro C _ hCs
    have hle : C.length ≤ W.edges.length := by
      refine (ncard_le_ncard ?_ (W.edges.finite_toSet)).trans (ncard_mem_list_le W.edges)
      intro e he
      have h := hCs.2 he
      rw [hD, walkDrawing_E] at h
      exact h
    exact lt_of_le_of_lt hle hW
  have hXeq : X = D.U ∪ ⋃ C ∈ {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}, ins C := rfl
  have hfinC : {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}.Finite := by
    refine Set.Finite.of_finite_image (f := fun C : Drawing S => (C.V, C.E)) ?_ ?_
    · refine (D.finite_V.finite_subsets.prod D.finite_edges.finite_subsets).subset ?_
      rintro _ ⟨C, ⟨-, hs'⟩, rfl⟩
      exact ⟨hs'.1, hs'.2⟩
    · intro C _ C' _ h
      exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hXcl : IsClosed X := by
    rw [hXeq]
    refine D.isClosed_U.union (hfinC.isClosed_biUnion fun C hC => ?_)
    exact (hs.isClosedDisc C hC.1 (hC.2.trans hDs) (hconfD C hC.1 hC.2)).isClosed
  -- A point in the closures of a region in `X` and a region not in `X` lies on `U(W)`.
  have hpt : ∀ r ∈ Z, ∀ s ∈ Γ.R, s ∉ Z → ∀ p, p ∈ closure r → p ∈ closure s → p ∈ D.U := by
    intro r hr s hsR hsn p hpr hps
    have hpX : p ∈ X := hXcl.closure_subset_iff.mpr hr.2 hpr
    rw [hXeq] at hpX
    rcases hpX with h | h
    · exact h
    · obtain ⟨C, ⟨hC, hCs⟩, hpC⟩ := mem_iUnion₂.mp h
      have hl := hconfD C hC hCs
      by_contra hpU
      have hpCU : p ∉ C.U := fun h' => hpU (hCs.U_subset h')
      have hin := region_subset_ins_of_closure hs hC (hCs.trans hDs) hl hsR hps hpC hpCU
      exact hsn ⟨hsR, fun x hx => Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hin hx⟩)⟩
  have hN : (boundaryDrawing Γ Z).IsSubdrawing D := by
    constructor
    · intro v hv
      obtain ⟨⟨r, hr, hir⟩, s, ⟨hsR, hsn⟩, his⟩ := (mem_boundaryDrawing_V hS).mp hv
      have hvU := hpt r hr s hsR hsn v hir.2.2 his.2.2
      by_contra hvD
      obtain ⟨g, hg, hvg⟩ := D.exists_edge_of_mem hvU hvD
      exact ((hDs.2 hg).2.1 hvg).2 hir.1
    · intro e he
      obtain ⟨⟨r, hr, hir⟩, s, ⟨hsR, hsn⟩, -, -, p, hpe, hps⟩ := mem_boundaryDrawing_E.mp he
      have her := edge_subset_closure_of_incident hS hir.1 hr.1 hir.2.2
      have hpU := hpt r hr s hsR hsn p (her hpe) hps
      have hpV : p ∉ D.V := fun h => (hir.1.2.1 hpe).2 (hDs.1 h)
      obtain ⟨g, hg, hpg⟩ := D.exists_edge_of_mem hpU hpV
      rw [Γ.edge_eq_of_mem hir.1 (hDs.2 hg) hpe hpg]
      exact hg
  have hlt : (Γ.V ∩ (boundaryDrawing Γ Z).V).ncard < k := by
    have h₁ : (Γ.V ∩ (boundaryDrawing Γ Z).V).ncard ≤ D.V.ncard :=
      ncard_le_ncard (fun x hx => hN.1 hx.2) D.finite_V
    have h₂ : D.V.ncard ≤ max 1 W.length := by
      rw [hD, walkDrawing_V]
      cases hW' : W with
      | nil h =>
        have : {x | x ∈ (GraphWalk.nil h).support} = ({u} : Set S) := by
          ext x
          simp
        rw [this, ncard_singleton]
        exact le_max_left _ _
      | @cons a y b e hl r =>
        have heq : {x | x ∈ (GraphWalk.cons hl r).support} = {x | x ∈ r.support} := by
          ext x
          constructor
          · intro hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact r.end_mem_support
            · exact hx
          · exact fun hx => List.mem_cons_of_mem _ hx
        rw [heq]
        refine (ncard_mem_list_le r.support).trans ?_
        rw [length_support]
        simp [GraphWalk.length]
    have h₃ : max 1 W.length < k := max_lt (by omega) hW
    omega
  have hZR : Z ⊆ Γ.R := fun r h => h.1
  refine (theorem_5_2_proof hS hs hw hZR hlt).1.resolve_right fun hsm => ?_
  -- Outside `ins(W)` there is a region of `Γ`, which then would be captured.
  have hr₀ := theorem_4_4_proof hS hs hDs hconfD
  obtain ⟨y, hy, hyU⟩ := exists_notMem_U (Γ := Γ) hS (region_isOpen hr₀) (region_nonempty hr₀)
  obtain ⟨s, hsR, hys⟩ := exists_region_of_notMem hyU
  have hsZ : s ∉ Z := fun h => hy.2 (h.2 hys)
  obtain ⟨C, hC, hCs, -, hin⟩ := hsm.2 s ⟨hsR, hsZ⟩
  rw [boundaryDrawing_compl hZR] at hCs
  refine hy.2 ?_
  have hmem : y ∈ ins C := hin hys
  exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs.trans hN⟩, hmem⟩)

/-- **(8.2)** of Graph Minors XI (page 96):
"(8.2) *Let $W_1, W_2, W_3$ be closed walks of $\Gamma$, each of length $<2\theta$. Then there is a
region $r$ of $\Gamma$ with $r \notin \mathrm{ins}(W_1) \cup \mathrm{ins}(W_2) \cup
\mathrm{ins}(W_3)$.*"
(Here $r \notin \dots$ in the paper means $r \not\subseteq \dots$; we prove that $r$ lies in none of
the three, which is what the paper's proof gives.) -/
theorem theorem_8_2_proof {u₁ u₂ u₃ : S} (W₁ : GraphWalk Γ.toGraph u₁ u₁)
    (W₂ : GraphWalk Γ.toGraph u₂ u₂) (W₃ : GraphWalk Γ.toGraph u₃ u₃) (h₁ : W₁.length < k)
    (h₂ : W₂.length < k) (h₃ : W₃.length < k) :
    ∃ r ∈ Γ.R, ¬ r ⊆ insWalk ins Γ W₁ ∧ ¬ r ⊆ insWalk ins Γ W₂ ∧ ¬ r ⊆ insWalk ins Γ W₃ := by
  have hk := hs.two_le
  have hw : IsWeighting Γ k Γ.V k := isWeighting_vertices (by omega)
  have hne := theorem_5_5_proof hS hs hw (small_of_walk hS hs W₁ h₁)
    (small_of_walk hS hs W₂ h₂) (small_of_walk hS hs W₃ h₃)
  by_contra hno
  push Not at hno
  refine hne (subset_antisymm ?_ fun r hr => ?_)
  · refine union_subset (union_subset ?_ ?_) ?_ <;> exact fun r h => h.1
  · by_cases a₁ : r ⊆ insWalk ins Γ W₁
    · exact Or.inl (Or.inl ⟨hr, a₁⟩)
    · by_cases a₂ : r ⊆ insWalk ins Γ W₂
      · exact Or.inl (Or.inr ⟨hr, a₂⟩)
      · exact Or.inr ⟨hr, hno r hr a₁ a₂⟩

end GraphMinor.GM11
