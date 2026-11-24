/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionBranchConnected
import LeanPool.GraphMinor.Minor.Basic

/-!
# Recovering the original graph from its subdivision

XII (4.5), page 252, uses that the source clique is a minor of
its subdivided graph. Contract the later edges of every chain
inside its right-end branch, and keep the first edge to represent
the original one. The branch membership of its two ends gives
the incidence and loop conditions of the minor model.
-/

public section

namespace GraphMinor.GM12

open Set Graph

/-- Contracting every chain except its first edge gives the
original graph. This proves the minor-model assertion for the
subdivision in XII (4.5), page 252, including possible original loops. -/
theorem isMinorModel_subdivision {m n : ℕ} (H : Graph (Fin m) (Fin n))
    (κ : Fin n × Bool → Fin m) (hlink : ∀ e, H.IsLink e (κ (e, false)) (κ (e, true)))
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e) :
    IsMinorModel H (subdivisionGraph κ k) (subdivisionBranch κ k) (subdivisionFirstEdge k hk) := by
  let l : Fin n → SubdivisionVertex m n k := fun e =>
    subdivisionVertexAt κ k e (⟨0, hk e⟩ : Fin (k e)).castSucc
  let r : Fin n → SubdivisionVertex m n k := fun e =>
    subdivisionVertexAt κ k e (⟨0, hk e⟩ : Fin (k e)).succ
  have hfirst : ∀ e, (subdivisionGraph κ k).IsLink (subdivisionFirstEdge k hk e) (l e) (r e) :=
    fun e => subdivisionGraph_isLink κ k e ⟨0, hk e⟩
  have hleft : ∀ e v, l e ∈ subdivisionBranch κ k v ↔ κ (e, false) = v :=
    fun e v => mem_subdivisionBranch_vertexAt_zero κ k v e
  have hright : ∀ e v, r e ∈ subdivisionBranch κ k v ↔ κ (e, true) = v :=
    fun e v => mem_subdivisionBranch_vertexAt_pos κ k v e _ (by change 0 < 0 + 1; decide)
  have hEall : H.edgeSet = univ := by
    ext e
    exact ⟨fun _ => mem_univ e, fun _ => (hlink e).edge_mem⟩
  refine {
    vertex_nonempty := fun v _ => subdivisionBranch_nonempty κ k v
    vertex_subset := fun _ _ _ _ => mem_univ _
    edge_mem := fun _ _ => mem_univ _
    vertex_disjoint := fun _ _ _ _ hne => subdivisionBranch_disjoint κ k hne
    edge_injOn := (subdivisionFirstEdge_injective k hk).injOn
    inc_iff := ?_
    isLoopAt_iff := ?_
    connected := ?_ }
  · intro v _ e _
    constructor
    · intro hev
      rcases hev.eq_or_eq_of_isLink (hlink e) with hve | hve
      · exact ⟨l e, (hleft e v).mpr hve.symm, (hfirst e).inc_left⟩
      · exact ⟨r e, (hright e v).mpr hve.symm, (hfirst e).inc_right⟩
    · rintro ⟨z, hz, hez⟩
      rcases hez.eq_or_eq_of_isLink (hfirst e) with hzl | hzr
      · have hkv := (hleft e v).mp (hzl ▸ hz)
        exact hkv ▸ (hlink e).inc_left
      · have hkv := (hright e v).mp (hzr ▸ hz)
        exact hkv ▸ (hlink e).inc_right
  · intro v _ e _
    constructor
    · intro hloop z hez
      have hlv : κ (e, false) = v :=
        (H.eq_or_eq_of_isLink_of_isLink (hlink e) hloop).elim id id
      have hrv : κ (e, true) = v :=
        (H.eq_or_eq_of_isLink_of_isLink (hlink e).symm hloop).elim id id
      rcases hez.eq_or_eq_of_isLink (hfirst e) with hzl | hzr
      · exact hzl ▸ (hleft e v).mpr hlv
      · exact hzr ▸ (hright e v).mpr hrv
    · intro hall
      have hlv := (hleft e v).mp (hall (l e) (hfirst e).inc_left)
      have hrv := (hright e v).mp (hall (r e) (hfirst e).inc_right)
      change H.IsLink e v v
      simpa only [hlv, hrv] using hlink e
  · intro v _
    rw [hEall, image_univ]
    exact subdivisionBranch_connected_subgraph κ k hk v

/-- A finite graph is isomorphic to a minor of any subdivision
of its edges into nonempty chains, as used in XII (4.5), page 252. -/
theorem isIsoMinor_subdivision {m n : ℕ} (H : Graph (Fin m) (Fin n))
    (κ : Fin n × Bool → Fin m) (hlink : ∀ e, H.IsLink e (κ (e, false)) (κ (e, true)))
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e) : IsIsoMinor H (subdivisionGraph κ k) :=
  isIsoMinor_of_isMinorModel H (subdivisionGraph κ k) (toFinite _) (toFinite _)
    (toFinite _) (toFinite _) (subdivisionBranch κ k) (subdivisionFirstEdge k hk)
    (isMinorModel_subdivision H κ hlink k hk)

end GraphMinor.GM12
