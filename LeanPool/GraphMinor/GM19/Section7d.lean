/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section7c
public import LeanPool.GraphMinor.GM11.Section91
public import LeanPool.GraphMinor.GM11.Section810
public import LeanPool.GraphMinor.GM14.Section5

/-!
# Closed walks of the radial drawing, and restraints

Graph Minors XIX, Section 7, defines the metric of a tangle by closed walks of `Γ*`. Graph Minors XI
works
with restraints. This file connects the two. A closed walk of length `< 2 rep(𝒯)` gives a restraint,
by
(8.5) of XI, and each restraint comes from a closed walk, by (8.3) of XI. The paper uses the ties of
(9.2)
of XI at this point, and (8.3) makes that detour unnecessary.

The results used later are `ClosedWalkIns.ins_eq_insWalk`, `TangleDatum.exists_walk_of_restraint`,
`TangleDatum.dist_le`, `TangleDatum.exists_of_dist_lt`, and the facts about atoms at the end.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

/-- Along a walk of a graph with two sides, the number of steps is even if and only if the two ends
are on
the same side. -/
theorem even_length_iff {α β : Type*} {G : Graph α β} (X : Set α)
    (hb : ∀ e x y, G.IsLink e x y → (x ∈ X ↔ y ∉ X)) {u v : α} (W : GraphWalk G u v) :
    Even W.length ↔ (u ∈ X ↔ v ∈ X) := by
  induction W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges]
  | @cons a y b e hl r ih =>
    have h₁ := hb e a y hl
    have hlen : (GraphWalk.cons hl r).length = r.length + 1 := rfl
    rw [hlen, Nat.even_add_one, ih]
    tauto

section Radial

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}

omit [T2Space Shat] in
/-- If an edge of `Γ*` meets a region of `Γ`, then the vertex of `Γ*` in that region is an end of
the
edge. -/
theorem RadialDrawing.center_mem_closure (hS : IsSurface S) (rad : RadialDrawing cap Γ) {e ρ : Set
  Shat}
    {w : Shat} (he : e ∈ rad.G.E) (hρ : ρ ∈ Γ.hatRegions cap) (hm : (e ∩ ρ).Nonempty) (hw : w ∈ ρ)
    (hwG : w ∈ rad.G.V) : w ∈ closure e := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨hG1, hG2, hG3, hG4, hG5, -⟩ := id rad.isPreRadial
  obtain ⟨v, hv, w', ⟨hw'G, hw'n⟩, hcap⟩ := hG5 e he
  obtain ⟨r', hr', hw'r⟩ := hG4 w' ⟨hw'G, hw'n⟩
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap Γ
  have hρD := hSk.hatRegion_mem_R hS hρ
  have hrD := hSk.hatRegion_mem_R hS hr'
  have hdis : ∀ y ∈ e, y ∉ Γ.hatU cap := by
    intro y hy hyU
    have hyG : y ∈ rad.G.U := by
      rw [rad.G.U_eq]
      exact Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hy⟩)
    have : y ∈ Γ.hatU cap ∩ rad.G.U := ⟨hyU, hyG⟩
    rw [hG1] at this
    exact (he.2.1 hy).2 (hG2 this)
  have hpre : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have hin : ∀ {r : Set Shat}, r ∈ Γ.hatRegions cap → (e ∩ r).Nonempty → e ⊆ r := by
    rintro r ⟨x, hx, rfl⟩ ⟨y, hye, hyr⟩
    rw [connectedComponentIn_eq hyr]
    exact hpre.subset_connectedComponentIn hye hdis
  have hw'cl : w' ∈ closure e := by
    have : w' ∈ closure e ∩ rad.G.V := by rw [hcap]; exact Or.inr rfl
    exact this.1
  obtain ⟨y, hyO, hye⟩ := mem_closure_iff.mp hw'cl r' (region_isOpen hrD) hw'r
  have h₁ := hin hr' ⟨y, hye, hyO⟩
  have h₂ := hin hρ hm
  have hreq : r' = ρ := region_eq_of_mem hrD hρD (h₁ hye) (h₂ hye)
  subst hreq
  rw [(hG3 r' hr').unique ⟨hw, hwG⟩ ⟨hw'r, hw'G⟩]
  exact hw'cl

/-- A region of `Γ*` that meets a region `ρ` of `Γ` has the vertex of `Γ*` in `ρ` on its closure. -/
theorem RadialDrawing.center_mem_closure_region (hS : IsSurface S) (rad : RadialDrawing cap Γ)
    {s ρ : Set Shat} {w : Shat} (hs : s ∈ rad.G.R) (hρ : ρ ∈ Γ.hatRegions cap)
    (hm : (s ∩ ρ).Nonempty) (hw : w ∈ ρ) (hwG : w ∈ rad.G.V) : w ∈ closure s := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap Γ
  have hρD := hSk.hatRegion_mem_R hS hρ
  by_contra hn
  let Z : Set (Set Shat) := {r | r ∈ rad.G.R ∧ w ∈ closure r}
  obtain ⟨r₁, hr₁, -, hwr₁⟩ := exists_region_outside (Γ := rad.G) hT (T := ∅) isClosed_empty
    ⟨∅, empty_subset _, sUnion_empty.symm⟩ (b := w) (by simp)
  obtain ⟨y, hyρ, hyr⟩ := mem_closure_iff.mp hwr₁ ρ (region_isOpen hρD) hw
  obtain ⟨e, he, hm'⟩ := exists_boundary_edge hT (region_isOpen hρD) (region_isPreconnected hρD)
    (Z := Z) ⟨hr₁, hwr₁⟩ (fun _ h ↦ h.1) ⟨hs, fun h ↦ hn h.2⟩ ⟨y, hyr, hyρ⟩ hm
  obtain ⟨-, r, hr, hinc⟩ := mem_boundaryDrawing_E.mp he
  have hsub := edge_subset_closure_of_incident hT hinc.1 hinc.2.1 hinc.2.2
  have hc := center_mem_closure hS rad hinc.1 hρ hm' hw hwG
  exact hr.2 ⟨hr.1, closure_minimal hsub isClosed_closure hc⟩

/-- Each point of the closure of a region `ρ` of `Γ` is on the closure of a region of `Γ*` that
meets
`ρ`. -/
theorem RadialDrawing.exists_region_at (hS : IsSurface S) (rad : RadialDrawing cap Γ) {ρ : Set Shat}
    (hρ : ρ ∈ Γ.hatRegions cap) {q : Shat} (hq : q ∈ closure ρ) :
    ∃ s ∈ rad.G.R, (s ∩ ρ).Nonempty ∧ q ∈ closure s := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap Γ
  have hρD := hSk.hatRegion_mem_R hS hρ
  have hRfin := finite_R hT rad.G
  have hcov : ρ ⊆ closure (⋃ s ∈ {s | s ∈ rad.G.R ∧ (s ∩ ρ).Nonempty}, s) := by
    intro x hx
    refine mem_closure_iff.mpr fun O hO hxO ↦ ?_
    obtain ⟨y, ⟨hyO, hyρ⟩, hyU⟩ := exists_notMem_U (Γ := rad.G) hT
      (hO.inter (region_isOpen hρD)) ⟨x, hxO, hx⟩
    obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyU
    exact ⟨y, hyO, mem_iUnion₂.mpr ⟨s, ⟨hs, y, hys, hyρ⟩, hys⟩⟩
  have hq' := closure_minimal hcov isClosed_closure hq
  have hfin : {s | s ∈ rad.G.R ∧ (s ∩ ρ).Nonempty}.Finite := hRfin.subset fun _ h ↦ h.1
  rw [hfin.closure_biUnion] at hq'
  obtain ⟨s, ⟨hs, hm⟩, hqs⟩ := mem_iUnion₂.mp hq'
  exact ⟨s, hs, hm, hqs⟩

end Radial

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

omit [T2Space S] in
/-- The inside of a short circuit is unique. -/
theorem eq_ins_of_isInsOf (D : TangleDatum cap χ) {F : Drawing Shat} {Δ : Set Shat}
    (h : IsInsOf D.rad D.ord D.𝒯 F Δ) : Δ = D.ins F := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hs := D.ins_spec h.1 h.2.1
  by_contra hne
  have hcov := cover_of_discBd_eq hT h.2.2.1 hs.2.2.1 (h.2.2.2.1.trans hs.2.2.2.1.symm) hne
  exact D.not_cover h hs hs (by rw [Set.union_assoc, Set.union_self, hcov])

omit [T2Space S] in
/-- `ins(W)` of Graph Minors XIX is `ins(W)` of Graph Minors XI. -/
theorem ins_eq_insWalk (D : TangleDatum cap χ) (T : ClosedWalkIns D.rad D.ord D.𝒯) :
    T.ins = insWalk D.ins D.rad.G T.walk := by
  have hlen : T.walk.length < 2 * D.rep := by
    rw [T.walk_len]
    have := T.halfLen_lt
    change T.halfLen < D.rep at this
    omega
  rw [T.ins_eq, T.sub_eq, insWalk, insOf]
  congr 1
  apply Subset.antisymm
  · refine iUnion_subset fun F ↦ iUnion_subset fun hF ↦ iUnion_subset fun Δ ↦ iUnion_subset fun h ↦
    ?_
    rw [D.eq_ins_of_isInsOf h]
    exact subset_biUnion_of_mem (u := D.ins) (show F ∈ _ from ⟨h.1.2, hF⟩)
  · refine iUnion₂_subset fun C hC ↦ ?_
    have hl := isConfined_walk T.walk hlen C hC.1 hC.2
    have hi := D.ins_spec (F := C) ⟨hC.2.trans (walkDrawing_isSubdrawing _ _), hC.1⟩ hl
    exact subset_iUnion_of_subset C (subset_iUnion_of_subset hC.2
      (subset_iUnion_of_subset _ (subset_iUnion_of_subset hi subset_rfl)))

/-- A closed walk of `Γ*` of length `< 2 rep(𝒯)` is one of the walks of the metric. -/
theorem exists_closedWalkIns (D : TangleDatum cap χ) {u : Shat}
    (W : GraphWalk D.rad.G.toGraph u u) (hlt : W.length < 2 * D.rep) :
    ∃ T : ClosedWalkIns D.rad D.ord D.𝒯, T.ins = insWalk D.ins D.rad.G W ∧ 2 * T.halfLen = W.length
      := by
  obtain ⟨n, hn⟩ : Even W.length := by
    obtain ⟨Sk, hSk⟩ := exists_isSkHat χ.isSurface cap D.P.Γ
    exact (even_length_iff Sk.V (D.rad.bipartite hSk.hV) W).mpr Iff.rfl
  let T : ClosedWalkIns D.rad D.ord D.𝒯 :=
    { base := u
      walk := W
      sub := walkDrawing D.rad.G W
      halfLen := n
      ins := _
      sub_eq := rfl
      walk_len := by omega
      halfLen_lt := by change n < D.rep; omega
      ins_eq := rfl }
  exact ⟨T, D.ins_eq_insWalk T, by change 2 * n = _; omega⟩

omit [T2Space S] in
/-- A bound for the metric from one closed walk. -/
theorem dist_le (D : TangleDatum cap χ) {a b : Set Shat} (T : ClosedWalkIns D.rad D.ord D.𝒯)
    (ha : (a ∩ T.ins).Nonempty) (hb : (b ∩ T.ins).Nonempty) : D.dist a b ≤ T.halfLen := by
  classical
  unfold dist tangleMetric
  split_ifs with h₁ h₂
  · exact Nat.zero_le _
  · exact Nat.sInf_le ⟨T, ha, hb, rfl⟩
  · exact absurd ⟨T, ha, hb⟩ h₂

omit [T2Space S] in
/-- Two different atoms at distance `< rep(𝒯)` lie in a closed walk that attains the distance. -/
theorem exists_of_dist_lt (D : TangleDatum cap χ) {a b : Set Shat} (hne : a ≠ b)
    (hlt : D.dist a b < D.rep) :
    ∃ T : ClosedWalkIns D.rad D.ord D.𝒯, (a ∩ T.ins).Nonempty ∧ (b ∩ T.ins).Nonempty ∧
      T.halfLen = D.dist a b := by
  classical
  unfold dist tangleMetric at *
  rw [ite_eq_right hne] at *
  split_ifs at * with h₂
  · obtain ⟨T, h₁, h₂', h₃⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ W : ClosedWalkIns D.rad D.ord D.𝒯,
      (a ∩ W.ins).Nonempty ∧ (b ∩ W.ins).Nonempty ∧ W.halfLen = k}) (by
        obtain ⟨T, h₁, h₂'⟩ := h₂
        exact ⟨_, T, h₁, h₂', rfl⟩)
    exact ⟨T, h₁, h₂', h₃⟩
  · exact absurd hlt (lt_irrefl _)

end TangleDatum

end GraphMinor.GM19
