/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section10
import LeanPool.GraphMinor.GM17.Section5Proved
import LeanPool.GraphMinor.GM17.Section6Proved
import LeanPool.GraphMinor.GM17.Section7Proved
import LeanPool.GraphMinor.GM17.Section8Proved
import LeanPool.GraphMinor.GM17.Section9Proved
import LeanPool.GraphMinor.GM17.Section9bProved

public import LeanPool.GraphMinor.GM17.Section9b
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode

import LeanPool.GraphMinor.Surface.Cuffs

import LeanPool.GraphMinor.GM17.IndentMain

import LeanPool.GraphMinor.GM17.RegionBoundary

/-!
# Graph Minors XVII: proved deductions of Section10

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section10`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Helper Lemmas on Walks and Subhypergraphs -/

private lemma walk_skeleton_mono {α : Type u} {β : Type v}
    {H₁ H₂ : Hypergraph α β} (h : H₁ ≤ H₂) {u v : α}
    (W : H₁.skeleton.Walk u v) :
    ∃ W' : H₂.skeleton.Walk u v, W'.support = W.support :=
  ⟨W.map (SimpleGraph.Hom.ofLE (skeleton_le_of_le h)), by simp⟩

private lemma walk_support_subset_vertexSet {α : Type u} {β : Type v}
    {H : Hypergraph α β} {u v : α} (hu : u ∈ H.vertexSet)
    (W : H.skeleton.Walk u v) :
    {z | z ∈ W.support} ⊆ H.vertexSet :=
  fun _ hz => Hypergraph.skeleton_walk_support_subset_vertexSet W hu _ hz

/-- Existence of `CuffStandardLinkages` from (9.8) (`theorem_9_8_proof`). -/
theorem exists_cuffStandardLinkages
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k) :
    Nonempty (CuffStandardLinkages π Θ k (π.warpAt Θ) E) := by
  have hk_pos : 0 < k := by have := E.two_le; omega
  have hex : ∀ i : Fin k,
      ∃ L : Fin (π.warpAt Θ) →
          PathFromTo (π.cellGraph (E.cell i)).skeleton
            (π.borderSet (E.node i)) (π.borderSet (E.node (cyclicSucc hk_pos i))),
        π.IsStandardLinkage (E.cell i) (E.node i) (E.node (cyclicSucc hk_pos i))
          (π.warpAt Θ) L := by
    intro i
    have hc_mem : E.cell i ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i
    have htilde := E.cell_tilde i
    have hn₁ : E.node i ∈ tilde (E.cell i) := htilde ▸ mem_insert _ _
    have hn₂ : E.node (cyclicSucc hk_pos i) ∈ tilde (E.cell i) :=
      htilde ▸ mem_insert_of_mem _ (mem_singleton _)
    have hne : E.node i ≠ E.node (cyclicSucc hk_pos i) :=
      E.injective_node.ne (cyclicSucc_ne_self E.two_le i).symm
    exact (theorem_9_8_proof h𝒯 π htrue hred hwarp hθ E.cuff_mem hc_mem.1 hc_mem.2
      hn₁ hn₂ hne).2.2.2.2
  choose L hstd using hex
  exact ⟨⟨L, hstd⟩⟩

section Circumnavigation

variable {α : Type u} {β : Type v} {G : Hypergraph α β}
variable {π : Portrayal G} {Θ : Set π.S} {k q : ℕ} {E : π.Γ.CuffEnumeration Θ k}
variable (SL : CuffStandardLinkages π Θ k q E)

theorem CuffStandardLinkages.mem_support_tail_subset_cellGraph
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) {u z : α} (hu : u ∈ π.borderSet (E.node i))
    (hz_tail : z ∈ (SL.stepWalk i u).support.tail) :
    z ∈ (π.cellGraph (E.cell i)).vertexSet := by
  obtain ⟨a, ha, _, _, hwalk_sup, _, _⟩ := SL.step_spec_of_mem hcard i hu
  have hz_sup : z ∈ (SL.L i a).walk.support :=
    hwalk_sup ▸ List.mem_of_mem_tail hz_tail
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases E.cuff_mem with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbd_i : (E.cell i ∩ bd π.S).Nonempty :=
    (E.cell_inter_cuff_nonempty i).mono (inter_subset_inter_right _ hΘ_bd)
  exact walk_support_subset_vertexSet
    (π.p3_subset (E.cell i) (E.cell_mem i) hbd_i (E.node i)
      (E.cell_tilde i ▸ mem_insert _ _) (ha ▸ (SL.L i a).first_mem))
    (SL.L i a).walk hz_sup

/-- Key structural property of the tail of a step walk: any vertex $z$ in
`(SL.stepWalk i u).support.tail` that also lies in `π.otherVertices (E.cell i)` (or in
`π.borderSet (E.node i) ∪ π.borderSet (E.node (cyclicSucc hk i))`) equals `SL.stepVertex i u`
and belongs to `π.borderPlus (E.node (cyclicSucc hk i)) \ π.borderPlus (E.node i)`. -/
theorem CuffStandardLinkages.mem_tail_stepWalk_inter_other
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) {u z : α} (hu : u ∈ π.borderSet (E.node i))
    (hz_tail : z ∈ (SL.stepWalk i u).support.tail)
    (hz_other : z ∈ π.otherVertices (E.cell i) ∨
      z ∈ π.borderSet (E.node i) ∪
        π.borderSet (E.node (cyclicSucc (by have := E.two_le; omega) i))) :
    z = SL.stepVertex i u ∧
    z ∉ π.borderPlus (E.node i) ∧
    z ∈ π.borderPlus (E.node (cyclicSucc (by have := E.two_le; omega) i)) := by
  obtain ⟨a, ha, hstep, _, hwalk_sup, hisPath, hstep_mem⟩ := SL.step_spec_of_mem hcard i hu
  have hsup_cons : (SL.stepWalk i u).support = u :: (SL.stepWalk i u).support.tail :=
    ((SL.stepWalk i u).cons_tail_support).symm
  have hnodup : (u :: (SL.stepWalk i u).support.tail).Nodup :=
    hsup_cons ▸ hisPath.support_nodup
  have hz_ne_u : z ≠ u := fun hEq => (List.nodup_cons.mp hnodup).1 (hEq ▸ hz_tail)
  have hz_sup : z ∈ (SL.L i a).walk.support :=
    hwalk_sup ▸ List.mem_of_mem_tail hz_tail
  have hz_not_bs₁ : z ∉ π.borderSet (E.node i) := by
    intro hz_bs₁
    have hEq := SL.mem_support_inter_borderSet_left hcard i a hz_sup hz_bs₁
    exact hz_ne_u (hEq.trans ha)
  have hz_not_bp₁ : z ∉ π.borderPlus (E.node i) := by
    rintro (hz_bs₁ | ⟨_, rfl⟩)
    · exact hz_not_bs₁ hz_bs₁
    · exact ((SL.isStandard i).2.1 a).1 hz_sup
  have hz_bs_union : z ∈ π.borderSet (E.node i) ∪
      π.borderSet (E.node (cyclicSucc (by have := E.two_le; omega) i)) := by
    rcases hz_other with hvo | hbu
    · have hΘ_bd : Θ ⊆ bd π.S := by
        rcases E.cuff_mem with ⟨x₀, _, rfl⟩
        exact connectedComponentIn_subset (bd π.S) x₀
      have hbd_i : (E.cell i ∩ bd π.S).Nonempty :=
        (E.cell_inter_cuff_nonempty i).mono (inter_subset_inter_right _ hΘ_bd)
      have hzc : z ∈ (π.cellGraph (E.cell i)).vertexSet :=
        SL.mem_support_tail_subset_cellGraph hcard i hu hz_tail
      obtain ⟨m, hm_t, hzm_bp⟩ := π.p6_borderPlus (E.cell_mem i) hbd_i hzc hvo
      rw [E.cell_tilde i] at hm_t
      rcases hm_t with rfl | rfl
      · exact (hz_not_bp₁ hzm_bp).elim
      · rcases hzm_bp with h | ⟨_, rfl⟩
        · exact Or.inr h
        · exact (((SL.isStandard i).2.1 a).2 hz_sup).elim
    · exact hbu
  have hz_bs₂ : z ∈ π.borderSet (E.node (cyclicSucc (by have := E.two_le; omega) i)) :=
    hz_bs_union.resolve_left hz_not_bs₁
  have hz_eq_last : z = (SL.L i a).last :=
    SL.mem_support_inter_borderSet_right hcard i a hz_sup hz_bs₂
  exact ⟨hz_eq_last.trans hstep.symm, hz_not_bp₁, Or.inl hz_bs₂⟩

/-- For any two distinct pairs $(i_1, u_1) \ne (i_2, u_2)$ with $u_1 \in \beta(E.\text{node } i_1)$
and $u_2 \in \beta(E.\text{node } i_2)$, the tails `(SL.stepWalk i₁ u₁).support.tail` and
`(SL.stepWalk i₂ u₂).support.tail` are disjoint. -/
theorem CuffStandardLinkages.disjoint_support_tail_stepWalk
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    {i₁ i₂ : Fin k} {u₁ u₂ : α}
    (hu₁ : u₁ ∈ π.borderSet (E.node i₁))
    (hu₂ : u₂ ∈ π.borderSet (E.node i₂))
    (hne : i₁ ≠ i₂ ∨ u₁ ≠ u₂) :
    List.Disjoint (SL.stepWalk i₁ u₁).support.tail (SL.stepWalk i₂ u₂).support.tail := by
  intro z hz₁ hz₂
  by_cases hi : i₁ = i₂
  · subst hi
    have hu_ne : u₁ ≠ u₂ := hne.resolve_left (not_not.mpr rfl)
    obtain ⟨a₁, ha₁, _, _, hsup₁, _, _⟩ := SL.step_spec_of_mem hcard i₁ hu₁
    obtain ⟨a₂, ha₂, _, _, hsup₂, _, _⟩ := SL.step_spec_of_mem hcard i₁ hu₂
    have ha_ne : a₁ ≠ a₂ := by
      rintro rfl
      exact hu_ne (ha₁.symm.trans ha₂)
    exact Set.disjoint_left.mp ((SL.isStandard i₁).1 ha_ne)
      (hsup₁ ▸ List.mem_of_mem_tail hz₁)
      (hsup₂ ▸ List.mem_of_mem_tail hz₂)
  · have hcell_ne : E.cell i₁ ≠ E.cell i₂ := E.injective_cell.ne hi
    have hzc₁ : z ∈ (π.cellGraph (E.cell i₁)).vertexSet :=
      SL.mem_support_tail_subset_cellGraph hcard i₁ hu₁ hz₁
    have hzc₂ : z ∈ (π.cellGraph (E.cell i₂)).vertexSet :=
      SL.mem_support_tail_subset_cellGraph hcard i₂ hu₂ hz₂
    have hvo₁ : z ∈ π.otherVertices (E.cell i₁) := ⟨E.cell i₂, E.cell_mem i₂, hcell_ne.symm, hzc₂⟩
    have hvo₂ : z ∈ π.otherVertices (E.cell i₂) := ⟨E.cell i₁, E.cell_mem i₁, hcell_ne, hzc₁⟩
    obtain ⟨_, hnot₁, hmem₁⟩ := SL.mem_tail_stepWalk_inter_other hcard i₁ hu₁ hz₁ (Or.inl hvo₁)
    obtain ⟨_, hnot₂, hmem₂⟩ := SL.mem_tail_stepWalk_inter_other hcard i₂ hu₂ hz₂ (Or.inl hvo₂)
    exact hi (unique_entry_index π E ⟨hnot₁, hmem₁⟩ ⟨hnot₂, hmem₂⟩)

/-- For every $v \in \beta(E.\text{node } i_0)$ and $m \le k$, `(SL.circWalk i₀ v m).support.tail`
is duplicate-free. -/
theorem CuffStandardLinkages.nodup_support_tail_circWalk
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) {v : α} (hv : v ∈ π.borderSet (E.node i₀))
    {m : ℕ} (hm : m ≤ k) :
    (SL.circWalk i₀ v m).support.tail.Nodup := by
  induction m with
  | zero =>
    change ([] : List α).Nodup
    exact List.nodup_nil
  | succ m ih =>
    rw [SL.support_tail_circWalk_succ]
    refine List.nodup_append.mpr ⟨ih (by omega), ?_, ?_⟩
    · have hisPath := (SL.step_spec_of_mem hcard (stepIdx E.two_le i₀ m)
        (SL.traceVertex_mem_borderSet hcard i₀ hv m)).choose_spec.2.2.2.2.1
      have hcons := (SL.stepWalk (stepIdx E.two_le i₀ m) (SL.traceVertex i₀ v m)).cons_tail_support
      exact (List.nodup_cons.mp (hcons ▸ hisPath.support_nodup)).2
    · intro z₁ hz₁ z₂ hz₂ hEq
      subst hEq
      rw [SL.mem_support_tail_circWalk_iff] at hz₁
      rcases hz₁ with ⟨r, hr, hzr⟩
      exact SL.disjoint_support_tail_stepWalk hcard
        (SL.traceVertex_mem_borderSet hcard i₀ hv r)
        (SL.traceVertex_mem_borderSet hcard i₀ hv m)
        (Or.inl (stepIdx_ne_of_lt E.two_le i₀ hr hm)) hzr hz₂

/-- For distinct $v_1, v_2 \in \beta(E.\text{node } i_0)$, `(SL.circWalk i₀ v₁ k).support.tail`
and `(SL.circWalk i₀ v₂ k).support.tail` are disjoint. -/
theorem CuffStandardLinkages.disjoint_support_tail_circWalk
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) {v₁ v₂ : α}
    (hv₁ : v₁ ∈ π.borderSet (E.node i₀))
    (hv₂ : v₂ ∈ π.borderSet (E.node i₀))
    (hne : v₁ ≠ v₂) :
    List.Disjoint (SL.circWalk i₀ v₁ k).support.tail (SL.circWalk i₀ v₂ k).support.tail := by
  intro z hz₁ hz₂
  rw [SL.mem_support_tail_circWalk_iff] at hz₁ hz₂
  rcases hz₁ with ⟨r₁, hr₁, hzr₁⟩
  rcases hz₂ with ⟨r₂, hr₂, hzr₂⟩
  have hne_step : stepIdx E.two_le i₀ r₁ ≠ stepIdx E.two_le i₀ r₂ ∨
      SL.traceVertex i₀ v₁ r₁ ≠ SL.traceVertex i₀ v₂ r₂ := by
    rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
    · exact Or.inl (stepIdx_ne_of_lt E.two_le i₀ hlt hr₂)
    · exact Or.inr (fun hEq => hne (SL.traceVertex_injOn hcard i₀ r₁ hv₁ hv₂ hEq))
    · exact Or.inl (stepIdx_ne_of_lt E.two_le i₀ hgt hr₁).symm
  exact SL.disjoint_support_tail_stepWalk hcard
    (SL.traceVertex_mem_borderSet hcard i₀ hv₁ r₁)
    (SL.traceVertex_mem_borderSet hcard i₀ hv₂ r₂)
    hne_step hzr₁ hzr₂

theorem CuffStandardLinkages.support_tail_circWalk_ne_nil
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hz : 3 ≤ z) (hθ : z + max 3 (2 * p + 2) < θ)
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) {v : α} (hv : v ∈ π.borderSet (E.node i₀)) :
    (SL.circWalk i₀ v k).support.tail ≠ [] := by
  intro hnil
  have hstep_nil : ∀ r < k,
      (SL.stepWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r)).support.tail = [] := by
    intro r hr
    by_contra hne
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
    have hz_all : z ∈ (SL.circWalk i₀ v k).support.tail :=
      (SL.mem_support_tail_circWalk_iff i₀ v k z).mpr ⟨r, hr, hz⟩
    rw [hnil] at hz_all
    exact List.not_mem_nil hz_all
  have htrace_eq : ∀ r ≤ k, SL.traceVertex i₀ v r = v := by
    intro r hr
    induction r with
    | zero => rfl
    | succ r ih =>
      have h_eq := start_eq_end_of_support_tail_eq_nil
        (SL.stepWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r))
        (hstep_nil r (by omega))
      exact h_eq.symm.trans (ih (by omega))
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases E.cuff_mem with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hv_G : v ∈ G.vertexSet :=
    π.borderSet_subset (E.node i₀) ⟨(E.node_mem i₀).1, hΘ_bd (E.node_mem i₀).2⟩ hv
  have hX_sub : ({v} : Set α) ⊆ G.vertexSet := singleton_subset_iff.mpr hv_G
  have hX_card : 3 * ({v} : Set α).ncard ≤ z := by
    rw [ncard_singleton]; omega
  refine theorem_6_6_proof h𝒯 π hT hwarp hred hθ E.cuff_mem hX_sub hX_card ?_
  intro n hn
  have hn_range : n ∈ Set.range E.node := by rwa [E.range_node]
  rcases hn_range with ⟨j, rfl⟩
  obtain ⟨r, hr_lt, hr_eq⟩ := stepIdx_surjective E.two_le i₀ j
  refine ⟨v, mem_singleton v, Or.inl ?_⟩
  have hmem := SL.traceVertex_mem_borderSet hcard i₀ hv r
  rw [htrace_eq r (by omega), hr_eq] at hmem
  exact hmem

theorem CuffStandardLinkages.mem_support_tail_circWalk_inter_borderSet_iff
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k)
    (hne_nil : ∀ w ∈ π.borderSet (E.node i₀), (SL.circWalk i₀ w k).support.tail ≠ [])
    {v u : α} (hv : v ∈ π.borderSet (E.node i₀)) (hu : u ∈ π.borderSet (E.node i₀)) :
    u ∈ (SL.circWalk i₀ v k).support.tail ↔ u = SL.traceVertex i₀ v k := by
  constructor
  · intro hu_tail
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases E.cuff_mem with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    have hn₀_bd : E.node i₀ ∈ π.Γ.N ∩ bd π.S := ⟨(E.node_mem i₀).1, hΘ_bd (E.node_mem i₀).2⟩
    have hfin : (π.borderSet (E.node i₀)).Finite := π.borderSet_finite hn₀_bd
    let f : α → α := fun w => SL.traceVertex i₀ w k
    have hf_sub : f '' π.borderSet (E.node i₀) ⊆ π.borderSet (E.node i₀) := by
      rintro _ ⟨w, hw, rfl⟩
      have hmem := SL.traceVertex_mem_borderSet hcard i₀ hw k
      rwa [stepIdx_self] at hmem
    have hf_card : (f '' π.borderSet (E.node i₀)).ncard = (π.borderSet (E.node i₀)).ncard :=
      (SL.traceVertex_injOn hcard i₀ k).ncard_image
    have hf_eq : f '' π.borderSet (E.node i₀) = π.borderSet (E.node i₀) :=
      eq_of_subset_of_ncard_le hf_sub hf_card.ge hfin
    obtain ⟨v', hv', hv'_eq⟩ : ∃ v' ∈ π.borderSet (E.node i₀), SL.traceVertex i₀ v' k = u := by
      rw [← hf_eq] at hu
      exact hu
    have hu_tail' : u ∈ (SL.circWalk i₀ v' k).support.tail := by
      rw [← hv'_eq]
      exact end_mem_support_tail_of_support_tail_ne_nil _ (hne_nil v' hv')
    have hvv' : v = v' := by
      by_contra hne
      exact SL.disjoint_support_tail_circWalk hcard i₀ hv hv' hne hu_tail hu_tail'
    rw [hvv', hv'_eq]
  · rintro rfl
    exact end_mem_support_tail_of_support_tail_ne_nil _ (hne_nil v hv)

/-- **Graph Minors XVII, (10.1)** (page 188):
"With notation as before, if $v_k \ne v$ then $L(v, n_0)$ is a path, and if $v_k = v$ then
$L(v, n_0)$ is a circuit; and for distinct $v, v' \in \beta(n_0)$, $L(v, n_0)$ and $L(v', n_0)$
are edge-disjoint, and if some vertex $u$ belongs to both of them then both are paths and $u$ is
an initial vertex of one and a terminal vertex of the other." -/
theorem theorem_10_1_proof
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hz : 3 ≤ z) (hθ : z + max 3 (2 * p + 2) < θ)
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) :
    (∀ v ∈ π.borderSet (E.node i₀),
      {z | z ∈ (SL.circWalk i₀ v k).support} = SL.circumnavigationVertices i₀ v ∧
      (SL.circWalk i₀ v k).support.tail ≠ [] ∧
      (SL.circWalk i₀ v k).support.tail.Nodup ∧
      (SL.traceVertex i₀ v k ≠ v → (SL.circWalk i₀ v k).IsPath) ∧
      (SL.traceVertex i₀ v k = v →
        {z | z ∈ (SL.circWalk i₀ v k).support.tail} = SL.circumnavigationVertices i₀ v)) ∧
    (∀ v ∈ π.borderSet (E.node i₀), ∀ v' ∈ π.borderSet (E.node i₀), v ≠ v' →
      List.Disjoint (SL.circWalk i₀ v k).support.tail (SL.circWalk i₀ v' k).support.tail ∧
      ∀ u ∈ SL.circumnavigationVertices i₀ v ∩ SL.circumnavigationVertices i₀ v',
        (SL.circWalk i₀ v k).IsPath ∧ (SL.circWalk i₀ v' k).IsPath ∧
        SL.traceVertex i₀ v k ≠ v ∧ SL.traceVertex i₀ v' k ≠ v' ∧
        ((u = v ∧ u = SL.traceVertex i₀ v' k) ∨ (u = v' ∧ u = SL.traceVertex i₀ v k))) := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hne_nil : ∀ w ∈ π.borderSet (E.node i₀), (SL.circWalk i₀ w k).support.tail ≠ [] :=
    fun w hw => SL.support_tail_circWalk_ne_nil
      h𝒯 hT hwarp hred hz hθ hcard i₀ hw
  have hisPath_of_ne : ∀ v ∈ π.borderSet (E.node i₀),
      SL.traceVertex i₀ v k ≠ v → (SL.circWalk i₀ v k).IsPath := by
    intro v hv hne
    rw [SimpleGraph.Walk.isPath_def, ← (SL.circWalk i₀ v k).cons_tail_support]
    refine List.nodup_cons.mpr ⟨?_, SL.nodup_support_tail_circWalk hcard i₀ hv le_rfl⟩
    rw [SL.mem_support_tail_circWalk_inter_borderSet_iff hcard i₀ hne_nil hv hv]
    exact hne.symm
  refine ⟨fun v hv => ⟨SL.support_circWalk_eq_circumnavigationVertices i₀ v,
    hne_nil v hv, SL.nodup_support_tail_circWalk hcard i₀ hv le_rfl,
    hisPath_of_ne v hv, ?_⟩, ?_⟩
  · intro hEq
    rw [← SL.support_circWalk_eq_circumnavigationVertices i₀ v]
    ext z
    simp only [mem_ofPred_eq]
    have hcons := (SL.circWalk i₀ v k).cons_tail_support
    conv_rhs => rw [← hcons, List.mem_cons]
    refine ⟨fun hz => Or.inr hz, ?_⟩
    rintro (rfl | hz)
    · rw [SL.mem_support_tail_circWalk_inter_borderSet_iff hcard i₀ hne_nil hv hv]
      exact hEq.symm
    · exact hz
  · intro v hv v' hv' hne
    have hdisj := SL.disjoint_support_tail_circWalk hcard i₀ hv hv' hne
    refine ⟨hdisj, ?_⟩
    rintro u ⟨hu_v, hu_v'⟩
    rw [← SL.support_circWalk_eq_circumnavigationVertices i₀ v] at hu_v
    rw [← SL.support_circWalk_eq_circumnavigationVertices i₀ v'] at hu_v'
    change u ∈ (SL.circWalk i₀ v k).support at hu_v
    change u ∈ (SL.circWalk i₀ v' k).support at hu_v'
    rw [← (SL.circWalk i₀ v k).cons_tail_support, List.mem_cons] at hu_v
    rw [← (SL.circWalk i₀ v' k).cons_tail_support, List.mem_cons] at hu_v'
    rcases hu_v with rfl | hu_tail_v <;> rcases hu_v' with hEq | hu_tail_v'
    · exact (hne hEq).elim
    · have hv_eq : u = SL.traceVertex i₀ v' k :=
        (SL.mem_support_tail_circWalk_inter_borderSet_iff hcard i₀ hne_nil hv' hv).mp hu_tail_v'
      have hne_v' : SL.traceVertex i₀ v' k ≠ v' := by
        rw [← hv_eq]; exact hne
      have hne_v : SL.traceVertex i₀ u k ≠ u := by
        intro hEq
        exact hne (SL.traceVertex_injOn hcard i₀ k hv hv' (hEq.trans hv_eq))
      exact ⟨hisPath_of_ne u hv hne_v, hisPath_of_ne v' hv' hne_v',
        hne_v, hne_v', Or.inl ⟨rfl, hv_eq⟩⟩
    · subst hEq
      have hv'_eq : u = SL.traceVertex i₀ v k :=
        (SL.mem_support_tail_circWalk_inter_borderSet_iff hcard i₀ hne_nil hv hv').mp hu_tail_v
      have hne_v : SL.traceVertex i₀ v k ≠ v := by
        rw [← hv'_eq]; exact hne.symm
      have hne_v' : SL.traceVertex i₀ u k ≠ u := by
        intro hEq
        exact hne (SL.traceVertex_injOn hcard i₀ k hv hv' (hv'_eq.symm.trans hEq.symm))
      exact ⟨hisPath_of_ne v hv hne_v, hisPath_of_ne u hv' hne_v',
        hne_v, hne_v', Or.inr ⟨rfl, hv'_eq⟩⟩
    · exact (hdisj hu_tail_v hu_tail_v').elim

/-! ## 4. Non-Containment of $L(v, n_0)$ and $\gamma(N(\Gamma) \cap \Theta)$: (10.2) and (10.3)
(Pages 188–189) -/

private theorem restriction_preserves_cuff_warp
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {p : ℕ}
    (π : Portrayal G)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    {Θ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hp : π.warpAt Θ = p)
    (c' : Set π.S)
    (hc' : c' ∈ π.Γ.C)
    (hsep : G.IsSeparation A B)
    (hnot_simp : ¬(π.restrictQuotient A B hsep c' hc').IsSimpler π) :
    (π.restrictQuotient A B hsep c' hc').warpAt Θ = p := by
  let π' := π.restrictQuotient A B hsep c' hc'
  have hEq := Portrayal.warpAt_eq_of_warpAt_le_of_not_isSimpler (π' := π') (π := π)
    (Homeomorph.refl π.S)
    (fun Φ hΦ => by
      have hle := π.restrictQuotient_warpAt_le A B hsep c' hc' hΦ
      have himg : (Homeomorph.refl π.S : π.S → π.S) '' Φ = Φ := image_id Φ
      change π'.warpAt Φ ≤ π.warpAt ((Homeomorph.refl π.S : π.S → π.S) '' Φ)
      rw [himg]; exact hle)
    hnot_simp Θ hΘ
  have himg : (Homeomorph.refl π.S : π.S → π.S) '' Θ = Θ := image_id Θ
  change π'.warpAt Θ = π.warpAt ((Homeomorph.refl π.S : π.S → π.S) '' Θ) at hEq
  rw [himg, hp] at hEq
  exact hEq

private theorem lift_quotient_border_linkage
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {p : ℕ}
    (π : Portrayal G)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    (c' : Set π.S)
    (hc' : c' ∈ π.Γ.C)
    (hsep : G.IsSeparation A B)
    (c : Set π.S)
    (hc : c ∈ (π.restrictQuotient A B hsep c' hc').Γ.C)
    (hbd : (c ∩ bd π.S).Nonempty)
    (m₁ : π.S)
    (hm₁_t : m₁ ∈ tilde c)
    (m₂ : π.S)
    (P : Fin p → PathFromTo ((π.restrictQuotient A B hsep c' hc').cellGraph c).skeleton
      ((π.restrictQuotient A B hsep c' hc').borderPlus m₁) ((π.restrictQuotient A B hsep c'
      hc').borderPlus m₂))
    (hbp₁ : (π.restrictQuotient A B hsep c' hc').borderPlus m₁ = π.borderPlus m₁ \ A.vertexSet)
    (hbp₂ : (π.restrictQuotient A B hsep c' hc').borderPlus m₂ = π.borderPlus m₂ \ A.vertexSet) :
    ∀ (i : Fin p), ∃ Q : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
      Q.first = (P i).first ∧ Q.last = (P i).last ∧ Q.walk.support = (P i).walk.support ∧ {z | z ∈
      Q.walk.support} ⊆ (π.cellGraph c).vertexSet \ A.vertexSet := by
  let π' := π.restrictQuotient A B hsep c' hc'
  intro i
  have hfirst_bp : (P i).first ∈ π.borderPlus m₁ \ A.vertexSet :=
    (Set.ext_iff.mp hbp₁ (P i).first).mp (P i).first_mem
  have hlast_bp : (P i).last ∈ π.borderPlus m₂ \ A.vertexSet :=
    (Set.ext_iff.mp hbp₂ (P i).last).mp (P i).last_mem
  have hfirst_c : (P i).first ∈ (π.cellGraph c).vertexSet \ A.vertexSet :=
    ⟨π.borderPlus_subset_cellGraph hc hbd hm₁_t hfirst_bp.1, hfirst_bp.2⟩
  obtain ⟨W₀, hsupp₀, hsub₀⟩ :=
    π.restrictQuotient_walk_lift A B hsep c' hc' hc hfirst_c (P i).walk
  have hle_Bc : π.cellGraph c ∩ B ≤ π.cellGraph c :=
    inter_le_left (π.cellGraph_le c hc) hsep.right_le
  obtain ⟨W', hsupp'⟩ := walk_skeleton_mono hle_Bc W₀
  have hsupp : W'.support = (P i).walk.support := hsupp'.trans hsupp₀
  have hisPath : W'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsupp]
    exact SimpleGraph.Walk.IsPath.support_nodup (P i).isPath
  refine ⟨⟨(P i).first, (P i).last, W', hisPath, hfirst_bp.1, hlast_bp.1⟩,
    rfl, rfl, hsupp, fun z hz => hsub₀ (by rwa [← hsupp'])⟩

private theorem linkage_with_added_path_is_disjoint
    {α : Type*} {G : SimpleGraph α} {A B : Set α} {p : ℕ}
    (Q : Fin p → PathFromTo G A B) (extra : PathFromTo G A B)
    (hQ : Pairwise fun i j => Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support})
    (hextra : ∀ i, Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ extra.walk.support}) :
    let paths (i : Fin (p + 1)) := if hi : i.1 < p then Q ⟨i.1, hi⟩ else extra
    Pairwise fun i j =>
      Disjoint {z | z ∈ (paths i).walk.support} {z | z ∈ (paths j).walk.support} := by
  intro paths i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  change z ∈ (if hi : i.1 < p then Q ⟨i.1, hi⟩ else extra).walk.support at hzi
  change z ∈ (if hj : j.1 < p then Q ⟨j.1, hj⟩ else extra).walk.support at hzj
  by_cases hi : i.1 < p <;> by_cases hj : j.1 < p
  · rw [dite_eq_left hi] at hzi
    rw [dite_eq_left hj] at hzj
    have hij' : (⟨i.1, hi⟩ : Fin p) ≠ ⟨j.1, hj⟩ :=
      fun h => hij (Fin.ext (Fin.mk.inj_iff.mp h))
    exact Set.disjoint_left.mp (hQ hij') hzi hzj
  · rw [dite_eq_left hi] at hzi
    rw [dite_eq_right hj] at hzj
    exact Set.disjoint_left.mp (hextra ⟨i.1, hi⟩) hzi hzj
  · rw [dite_eq_right hi] at hzi
    rw [dite_eq_left hj] at hzj
    exact Set.disjoint_left.mp (hextra ⟨j.1, hj⟩) hzj hzi
  · have hi' : i.1 = p := Nat.le_antisymm (Nat.le_of_lt_succ i.isLt) (Nat.le_of_not_gt hi)
    have hj' : j.1 = p := Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) (Nat.le_of_not_gt hj)
    exact hij (Fin.ext (hi'.trans hj'.symm))

/-- Vertex-support form of **Graph Minors XVII, (6.5)** (page 175): the proof of `theorem_6_5_proof`
shows
that in case (ii), there is no walk $W$ of $\alpha(c)^*$ between $\beta(n_1)$ and $\beta(n_2)$ whose
vertex support lies in $V(A)$ (since the $p$ paths in $\alpha'(c) = (\alpha(c) \cap B)/Z$ lift to
$p$ disjoint paths in $\alpha(c)^*$ with vertex support in $V(\alpha(c)) \setminus V(A)$). -/
theorem theorem_6_5_walk_subset
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ q p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ q) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * q + 2) < θ)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hord : separationOrder A B ≤ z)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hp : π.warpAt Θ = p) :
    (∃ n ∈ π.Γ.N ∩ Θ, (π.borderSet n).ncard = p ∧ Disjoint (π.borderSet n) A.vertexSet) ∨
    (∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ ∃ n₁ n₂ : π.S, n₁ ≠ n₂ ∧ tilde c = {n₁, n₂} ∧
      n₁ ∈ π.domγ ∧ n₂ ∈ π.domγ ∧
      π.nodeVertex n₁ ∉ A.vertexSet ∧ π.nodeVertex n₂ ∉ A.vertexSet ∧
      (∀ u ∈ π.borderSet n₁, ∀ v ∈ π.borderSet n₂,
       ∀ W : (π.cellGraph c).skeleton.Walk u v, ¬ ({z | z ∈ W.support} ⊆ A.vertexSet)) ∧
      (π.borderSet n₁ \ A.vertexSet).ncard = p - 1 ∧
      (π.borderSet n₂ \ A.vertexSet).ncard = p - 1 ∧ 2 ≤ p) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x
  have hp_pos : 1 ≤ p := by
    rw [← hp]
    exact theorem_5_1_proof π hT (hred.isZeroRedundant h𝒯) hΘ
  obtain ⟨c', hc', hc'Θ, _⟩ := π.exists_cell_cellWarp_eq_warpAt hΘ hΘ_arc
  set Z := A.vertexSet ∩ B.vertexSet
  have hsep := h𝒯.isSeparation hAB
  have hZ_sub : Z ⊆ G.vertexSet := inter_subset_left.trans hsep.left_le.1
  have hZ_le : (A.vertexSet ∩ B.vertexSet).ncard ≤ z := hord
  let π' := π.restrictQuotient A B hsep c' hc'
  have hT' : π'.IsCentral (quotientTangle G 𝒯 Z) :=
    π.restrictQuotient_isCentral h𝒯 hT hwarp hAB (by omega) c' hc'
  have hnot_simp : ¬ π'.IsSimpler π := hred.2 Z hZ_sub hZ_le π' hT'
  have hwarpAt_eq : π'.warpAt Θ = p := by
    exact restriction_preserves_cuff_warp (α := α) (β := β) (G := G) (p := p) π (A := A) (B := B)
      (Θ := Θ) hΘ hp c' hc' hsep hnot_simp
  by_cases hcase1 : ∃ n ∈ π.Γ.N ∩ Θ, p ≤ (π.borderSet n \ A.vertexSet).ncard
  · refine Or.inl ?_
    rcases hcase1 with ⟨n, hn, hle⟩
    have hn_bd : n ∈ π.Γ.N ∩ bd π.S := ⟨hn.1, hΘ_bd hn.2⟩
    have hle_p : (π.borderSet n).ncard ≤ p := hp ▸ π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn
    have hsub_le : (π.borderSet n \ A.vertexSet).ncard ≤ (π.borderSet n).ncard :=
      ncard_le_ncard sdiff_subset (π.borderSet_finite hn_bd)
    have hcard_eq : (π.borderSet n).ncard = p := by omega
    have h_eq : π.borderSet n \ A.vertexSet = π.borderSet n :=
      eq_of_subset_of_ncard_le sdiff_subset (by omega) (π.borderSet_finite hn_bd)
    refine ⟨n, hn, hcard_eq, Set.disjoint_left.mpr fun v hvn hvA => ?_⟩
    have hvn' : v ∈ π.borderSet n \ A.vertexSet := by rwa [h_eq]
    exact hvn'.2 hvA
  · refine Or.inr ?_
    have hcase1' : ∀ n ∈ π.Γ.N ∩ Θ, (π.borderSet n \ A.vertexSet).ncard < p :=
      fun n hn => Nat.lt_of_not_ge fun hge => hcase1 ⟨n, hn, hge⟩
    obtain ⟨c : Set π.S, hc, hcΘ, hcw'⟩ := π'.exists_cell_cellWarp_eq_warpAt hΘ hΘ_arc
    rw [hwarpAt_eq] at hcw'
    have hbd : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
    have htilde_Θ : tilde c ⊆ π.Γ.N ∩ Θ := (π.Γ.border_cell_subset_cuff hc hΘ hcΘ).2.2.2.1
    obtain ⟨n₁, n₂, hne, htilde, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc hbd
    have hnot_le : ¬ π'.CellWarpLE c (p - 1) := by
      intro hle; have := (π'.cellWarp_le_iff hc hbd).mpr hle; omega
    have hm_exists : ∃ m₁ ∈ tilde c, ∃ m₂ ∈ tilde c, m₁ ≠ m₂ ∧
        ¬ ((π'.borderSet m₁).ncard ≤ p - 1 ∧ (π'.borderSet m₂).ncard ≤ p - 1 ∧
          ((π'.borderPlus m₁).ncard = p - 1 + 1 → (π'.borderPlus m₂).ncard = p - 1 + 1 →
            Portrayal.LinkagePairs (π'.cellGraph c).skeleton (π'.borderPlus m₁) (π'.borderPlus m₂)
              (p - 1 + 1) (π'.nodeVertex m₁) (π'.nodeVertex m₂))) := by
      by_contra h_all; apply hnot_le
      intro m₁ hm₁ m₂ hm₂ hm_ne; by_contra h_neg
      exact h_all ⟨m₁, hm₁, m₂, hm₂, hm_ne, h_neg⟩
    obtain ⟨m₁ : π.S, hm₁_t, m₂ : π.S, hm₂_t, hm_ne, hm_cond⟩ := hm_exists
    have hsub_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
    rw [hsub_eq] at hm_cond
    have hm₁_Θ : m₁ ∈ π.Γ.N ∩ Θ := htilde_Θ hm₁_t
    have hm₂_Θ : m₂ ∈ π.Γ.N ∩ Θ := htilde_Θ hm₂_t
    have hm₁_bd : m₁ ∈ π.Γ.N ∩ bd π.S := ⟨hm₁_Θ.1, hΘ_bd hm₁_Θ.2⟩
    have hm₂_bd : m₂ ∈ π.Γ.N ∩ bd π.S := ⟨hm₂_Θ.1, hΘ_bd hm₂_Θ.2⟩
    have hm₁_lt : (π'.borderSet m₁).ncard ≤ p - 1 := by
      have := hcase1' m₁ hm₁_Θ; change (π.borderSet m₁ \ A.vertexSet).ncard ≤ p - 1; omega
    have hm₂_lt : (π'.borderSet m₂).ncard ≤ p - 1 := by
      have := hcase1' m₂ hm₂_Θ; change (π.borderSet m₂ \ A.vertexSet).ncard ≤ p - 1; omega
    have hm_not_link : ¬ ((π'.borderPlus m₁).ncard = p → (π'.borderPlus m₂).ncard = p →
        Portrayal.LinkagePairs (π'.cellGraph c).skeleton (π'.borderPlus m₁) (π'.borderPlus m₂)
          p (π'.nodeVertex m₁) (π'.nodeVertex m₂)) :=
      fun h => hm_cond ⟨hm₁_lt, hm₂_lt, h⟩
    have hm_link_ex : (π'.borderPlus m₁).ncard = p ∧ (π'.borderPlus m₂).ncard = p ∧
        ∃ (P : Fin p → PathFromTo (π'.cellGraph c).skeleton
            (π'.borderPlus m₁) (π'.borderPlus m₂)),
          (Pairwise fun i j =>
            Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P j).walk.support}) ∧
          ∀ i : Fin p,
            (P i).first = π'.nodeVertex m₁ → (P i).last ≠ π'.nodeVertex m₂ := by
      by_contra h_neg; apply hm_not_link
      intro h1 h2 P hP_disj; by_contra h_no_i; apply h_neg
      refine ⟨h1, h2, P, hP_disj, fun i hfirst hlast => h_no_i ⟨i, hfirst, hlast⟩⟩
    obtain ⟨hbp₁_eq, hbp₂_eq, P, hP_disj, hP_not_pair⟩ := hm_link_ex
    have hm₁_dom' : m₁ ∈ π'.domγ := by
      by_contra hnot; rw [π'.ncard_borderPlus_of_notMem_domγ hnot] at hbp₁_eq; omega
    have hm₂_dom' : m₂ ∈ π'.domγ := by
      by_contra hnot; rw [π'.ncard_borderPlus_of_notMem_domγ hnot] at hbp₂_eq; omega
    have hm₁_card : (π.borderSet m₁ \ A.vertexSet).ncard = p - 1 := by
      have := π'.ncard_borderPlus_of_mem_domγ hm₁_dom' hm₁_bd.2
      change (π'.borderPlus m₁).ncard = (π.borderSet m₁ \ A.vertexSet).ncard + 1 at this; omega
    have hm₂_card : (π.borderSet m₂ \ A.vertexSet).ncard = p - 1 := by
      have := π'.ncard_borderPlus_of_mem_domγ hm₂_dom' hm₂_bd.2
      change (π'.borderPlus m₂).ncard = (π.borderSet m₂ \ A.vertexSet).ncard + 1 at this; omega
    have hp_ge2 : 2 ≤ p := by
      by_contra hlt
      have hp1 : p = 1 := by omega
      subst hp1
      have hbp₁_sing : π'.borderPlus m₁ = {π'.nodeVertex m₁} := by
        have hempty : π'.borderSet m₁ = ∅ :=
          (ncard_eq_zero ((π.borderSet_finite hm₁_bd).subset sdiff_subset)).mp hm₁_card
        rw [π'.borderPlus_eq_insert hm₁_dom', hempty, insert_empty_eq]
      have hbp₂_sing : π'.borderPlus m₂ = {π'.nodeVertex m₂} := by
        have hempty : π'.borderSet m₂ = ∅ :=
          (ncard_eq_zero ((π.borderSet_finite hm₂_bd).subset sdiff_subset)).mp hm₂_card
        rw [π'.borderPlus_eq_insert hm₂_dom', hempty, insert_empty_eq]
      have hfirst0 : (P ⟨0, Nat.zero_lt_one⟩).first = π'.nodeVertex m₁ :=
        mem_singleton_iff.mp (hbp₁_sing ▸ (P ⟨0, Nat.zero_lt_one⟩).first_mem)
      have hlast0 : (P ⟨0, Nat.zero_lt_one⟩).last = π'.nodeVertex m₂ :=
        mem_singleton_iff.mp (hbp₂_sing ▸ (P ⟨0, Nat.zero_lt_one⟩).last_mem)
      exact hP_not_pair ⟨0, Nat.zero_lt_one⟩ hfirst0 hlast0
    have htilde_m : tilde c = {m₁, m₂} := by
      have h1 : m₁ ∈ ({n₁, n₂} : Set π.S) := htilde ▸ hm₁_t
      have h2 : m₂ ∈ ({n₁, n₂} : Set π.S) := htilde ▸ hm₂_t
      refine htilde.trans ?_
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact (hm_ne rfl).elim
      · rfl
      · exact Set.pair_comm _ _
      · exact (hm_ne rfl).elim
    refine ⟨c, hc, hcΘ, m₁, m₂, hm_ne, htilde_m, hm₁_dom'.1, hm₂_dom'.1, hm₁_dom'.2, hm₂_dom'.2,
      ?_, hm₁_card, hm₂_card, hp_ge2⟩
    intro u₀ hu₀ v₀ hv₀ W_c hW_sub
    let W_cp := W_c.toPath.1
    have hW_cp_path : W_cp.IsPath := W_c.toPath.2
    have hW_cp_supp_A : {z | z ∈ W_cp.support} ⊆ A.vertexSet :=
      fun z hz => hW_sub (SimpleGraph.Walk.support_toPath_subset_support W_c hz)
    let Q_extra : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂) :=
      ⟨u₀, v₀, W_cp, hW_cp_path, Or.inl hu₀, Or.inl hv₀⟩
    have hbp₁ := π.restrictQuotient_borderPlus A B hsep c' hc' m₁
    have hbp₂ := π.restrictQuotient_borderPlus A B hsep c' hc' m₂
    have hlift : ∀ i : Fin p,
        ∃ Q : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
          Q.first = (P i).first ∧ Q.last = (P i).last ∧
          Q.walk.support = (P i).walk.support ∧
          {z | z ∈ Q.walk.support} ⊆ (π.cellGraph c).vertexSet \ A.vertexSet := by
      exact lift_quotient_border_linkage (α := α) (β := β) (G := G) (p := p) π (A := A) (B := B)
        c' hc' hsep c hc hbd m₁ hm₁_t m₂ P hbp₁ hbp₂
    choose Q hQ_first hQ_last hQ_supp hQ_sub using hlift
    let Q_all : Fin (p + 1) →
        PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂) :=
      fun i => if h : i.1 < p then Q ⟨i.1, h⟩ else Q_extra
    have hQ_all_disj : Pairwise fun i j =>
        Disjoint {z | z ∈ (Q_all i).walk.support} {z | z ∈ (Q_all j).walk.support} := by
      apply linkage_with_added_path_is_disjoint Q Q_extra
      · intro i j hij
        simpa only [hQ_supp i, hQ_supp j] using hP_disj hij
      · intro i
        exact Set.disjoint_left.mpr fun z hz hz' => (hQ_sub i hz).2 (hW_cp_supp_A hz')
    have hfirst_inj : Function.Injective (fun i : Fin (p + 1) => (Q_all i).first) := by
      intro i j hEq
      dsimp only at hEq
      by_contra hij
      have hmem : (Q_all i).first ∈ {z | z ∈ (Q_all j).walk.support} := by
        change (Q_all i).first ∈ (Q_all j).walk.support
        rw [hEq]; exact SimpleGraph.Walk.start_mem_support _
      exact Set.disjoint_left.mp (hQ_all_disj hij)
        (SimpleGraph.Walk.start_mem_support _) hmem
    have hlast_inj : Function.Injective (fun i : Fin (p + 1) => (Q_all i).last) := by
      intro i j hEq
      dsimp only at hEq
      by_contra hij
      have hmem : (Q_all i).last ∈ {z | z ∈ (Q_all j).walk.support} := by
        change (Q_all i).last ∈ (Q_all j).walk.support
        rw [hEq]; exact SimpleGraph.Walk.end_mem_support _
      exact Set.disjoint_left.mp (hQ_all_disj hij)
        (SimpleGraph.Walk.end_mem_support _) hmem
    have hbp₁_ge : p + 1 ≤ (π.borderPlus m₁).ncard := by
      have hsub_r : Set.range (fun i : Fin (p + 1) => (Q_all i).first) ⊆ π.borderPlus m₁ := by
        rintro _ ⟨i, rfl⟩; exact (Q_all i).first_mem
      have hcard_r : (Set.range (fun i : Fin (p + 1) => (Q_all i).first)).ncard = p + 1 := by
        rw [ncard_range_of_injective hfirst_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact hcard_r ▸ ncard_le_ncard hsub_r (π.borderPlus_finite hm₁_bd)
    have hbp₂_ge : p + 1 ≤ (π.borderPlus m₂).ncard := by
      have hsub_r : Set.range (fun i : Fin (p + 1) => (Q_all i).last) ⊆ π.borderPlus m₂ := by
        rintro _ ⟨i, rfl⟩; exact (Q_all i).last_mem
      have hcard_r : (Set.range (fun i : Fin (p + 1) => (Q_all i).last)).ncard = p + 1 := by
        rw [ncard_range_of_injective hlast_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact hcard_r ▸ ncard_le_ncard hsub_r (π.borderPlus_finite hm₂_bd)
    have hcw_le_p : π.cellWarp c ≤ p := hp ▸ π.cellWarp_le_warpAt hc hcΘ
    have hspec_c := (π.cellWarp_le_iff hc hbd).mp hcw_le_p m₁ hm₁_t m₂ hm₂_t hm_ne
    have hbp₁_le : (π.borderPlus m₁).ncard ≤ p + 1 :=
      (π.ncard_borderPlus_le hm₁_bd).trans (Nat.add_le_add_right hspec_c.1 1)
    have hbp₂_le : (π.borderPlus m₂).ncard ≤ p + 1 :=
      (π.ncard_borderPlus_le hm₂_bd).trans (Nat.add_le_add_right hspec_c.2.1 1)
    obtain ⟨i, hfirst_i, hlast_i⟩ :=
      hspec_c.2.2 (by omega) (by omega) Q_all hQ_all_disj
    dsimp only [Q_all] at hfirst_i hlast_i
    split_ifs at hfirst_i hlast_i with hi
    · exact hP_not_pair ⟨i.1, hi⟩
        ((hQ_first ⟨i.1, hi⟩).symm.trans hfirst_i)
        ((hQ_last ⟨i.1, hi⟩).symm.trans hlast_i)
    · have hu₀_A : u₀ ∈ A.vertexSet := hW_cp_supp_A W_cp.start_mem_support
      exact hm₁_dom'.2 (hfirst_i ▸ hu₀_A)

/-- **Graph Minors XVII, (10.2)** (page 188):
"There is no $(A, B) \in \mathcal{T}$ of order $\le z$ with $V(L(v, n_0)) \subseteq V(A)$."

Note on hypergraph edges: the paper's proof applies [1, Theorem (2.8)] to deduce $L(v, n_0)
\subseteq A$
and hence that each $P_i$ is a path of $(A \cap \alpha(c_i))^*$. In a hypergraph $G$, an edge
$e \in E(\alpha(c_i))$ witnessing an adjacency of $P_i$ may also be incident with a third vertex
outside
$V(A)$, so $e$ may belong to $E(B)$ even when $B$ is minimal. Using `theorem_6_5_walk_subset` (which
is the vertex-support statement proved by the proof of (6.5) on page 176), the contradiction holds
directly from $V(P_i) \subseteq V(L(v, n_0)) \subseteq V(A)$ without assuming edges have size $\le
2$. -/
theorem theorem_10_2_proof
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hT : π.IsCentral 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (_hz : 2 * p + 3 ≤ z) (hθ : z + 2 * p + 2 < θ)
    (hq : π.warpAt Θ = q)
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) {v : α} (hv : v ∈ π.borderSet (E.node i₀))
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hord : separationOrder A B ≤ z) :
    ¬ (SL.circumnavigationVertices i₀ v ⊆ A.vertexSet) := by
  intro hsub
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hk_pos : 0 < k := by have := E.two_le; omega
  have hq_pos : 1 ≤ π.warpAt Θ :=
    theorem_5_1_proof π hT (hred.isZeroRedundant h𝒯) E.cuff_mem
  have hp_pos : 1 ≤ p :=
    (hq_pos.trans (π.warpAt_le_warp E.cuff_mem)).trans hwarp
  have hθ_max : z + max 3 (2 * p + 2) < θ := by omega
  rcases theorem_6_5_walk_subset
      h𝒯 π hT hwarp hred hθ_max hAB hord E.cuff_mem hq with
    ⟨n, hn, _, hdisj⟩ |
    ⟨c, hc, hcΘ, n₁, n₂, hne, htilde, _, _, _, _, hno_walk, _, _, _⟩
  · have hn_range : n ∈ Set.range E.node := by rwa [E.range_node]
    rcases hn_range with ⟨j, rfl⟩
    obtain ⟨r, hr_lt, hr_eq⟩ := stepIdx_surjective E.two_le i₀ j
    have hmem_bs : SL.traceVertex i₀ v r ∈ π.borderSet (E.node j) := by
      rw [← hr_eq]
      exact SL.traceVertex_mem_borderSet hcard i₀ hv r
    have hmem_A : SL.traceVertex i₀ v r ∈ A.vertexSet :=
      hsub (SL.traceVertex_mem_circumnavigationVertices i₀ v hr_lt)
    exact Set.disjoint_left.mp hdisj hmem_bs hmem_A
  · have hc_range : c ∈ Set.range E.cell := by
      rw [E.range_cell]; exact ⟨hc, hcΘ⟩
    rcases hc_range with ⟨j, rfl⟩
    obtain ⟨r, hr_lt, rfl⟩ := stepIdx_surjective E.two_le i₀ j
    set idx := stepIdx E.two_le i₀ r
    let u₀ := SL.traceVertex i₀ v r
    let v₀ := SL.stepVertex idx u₀
    have hu₀_bs : u₀ ∈ π.borderSet (E.node idx) :=
      SL.traceVertex_mem_borderSet hcard i₀ hv r
    have hv₀_bs : v₀ ∈ π.borderSet (E.node (cyclicSucc hk_pos idx)) :=
      (SL.step_spec_of_mem hcard idx hu₀_bs).choose_spec.2.2.2.2.2
    let W : (π.cellGraph (E.cell idx)).skeleton.Walk u₀ v₀ := SL.stepCellWalk idx u₀
    have hW_sub : {z | z ∈ W.support} ⊆ A.vertexSet :=
      (SL.support_stepCellWalk_subset_circumnavigationVertices i₀ v hr_lt).trans hsub
    have htilde_j : tilde (E.cell idx) = {E.node idx, E.node (cyclicSucc hk_pos idx)} :=
      E.cell_tilde idx
    have hn₁_mem : n₁ ∈ ({E.node idx, E.node (cyclicSucc hk_pos idx)} : Set π.S) := by
      rw [← htilde_j, htilde]; exact mem_insert _ _
    have hn₂_mem : n₂ ∈ ({E.node idx, E.node (cyclicSucc hk_pos idx)} : Set π.S) := by
      rw [← htilde_j, htilde]; exact mem_insert_of_mem _ (mem_singleton _)
    rcases hn₁_mem with rfl | rfl <;> rcases hn₂_mem with rfl | rfl
    · exact hne rfl
    · exact hno_walk u₀ hu₀_bs v₀ hv₀_bs W hW_sub
    · refine hno_walk v₀ hv₀_bs u₀ hu₀_bs W.reverse ?_
      intro z hz
      change z ∈ W.reverse.support at hz
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
      exact hW_sub hz
    · exact hne rfl

theorem CuffStandardLinkages.circumnavigationVertices_subset_cellsUnion
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) {v : α} (hv : v ∈ π.borderSet (E.node i₀)) :
    SL.circumnavigationVertices i₀ v ⊆
      (π.cellsUnion {c ∈ π.Γ.C | (c ∩ Θ).Nonempty}).vertexSet := by
  classical
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases E.cuff_mem with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  intro z hz
  unfold CuffStandardLinkages.circumnavigationVertices at hz
  rw [mem_iUnion₂] at hz
  rcases hz with ⟨r, _, hzr⟩
  set idx : Fin k := stepIdx E.two_le i₀ r
  have hc_mem : E.cell idx ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
    rw [← E.range_cell]; exact mem_range_self idx
  have hbd_idx : (E.cell idx ∩ bd π.S).Nonempty :=
    hc_mem.2.mono (inter_subset_inter_right _ hΘ_bd)
  have hcur_bs : SL.traceVertex i₀ v r ∈ π.borderSet (E.node idx) :=
    SL.traceVertex_mem_borderSet hcard i₀ hv r
  have hcur_c : SL.traceVertex i₀ v r ∈ (π.cellGraph (E.cell idx)).vertexSet :=
    π.p3_subset (E.cell idx) hc_mem.1 hbd_idx (E.node idx)
      (E.cell_tilde idx ▸ mem_insert _ _) hcur_bs
  refine mem_iUnion₂.mpr ⟨E.cell idx, ⟨hc_mem, hc_mem.1⟩, ?_⟩
  change z ∈ (if h : ∃ j : Fin q, (SL.L idx j).first = SL.traceVertex i₀ v r then
      {z | z ∈ (SL.L idx (Classical.choose h)).walk.support}
    else {SL.traceVertex i₀ v r}) at hzr
  by_cases h : ∃ j : Fin q, (SL.L idx j).first = SL.traceVertex i₀ v r
  · rw [dite_eq_left h] at hzr
    have hfirst_c : (SL.L idx (Classical.choose h)).first ∈
        (π.cellGraph (E.cell idx)).vertexSet := by
      rw [Classical.choose_spec h]; exact hcur_c
    exact walk_support_subset_vertexSet hfirst_c (SL.L idx (Classical.choose h)).walk hzr
  · rw [dite_eq_right h] at hzr
    rw [mem_singleton_iff.mp hzr]
    exact hcur_c

end Circumnavigation

/-- **Graph Minors XVII, (10.3)** (page 189):
"For each cuff $\Theta$, there is no $(A, B) \in \mathcal{T}$ of order $\le z$ with
$\gamma(N(\Gamma) \cap \Theta) \subseteq V(A)$." -/
theorem theorem_10_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hT : π.IsCentral 𝒯) (htrue : π.IsTrue 𝒯)
    (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hz : 2 * p + 3 ≤ z) (hθ : z + 2 * p + 2 < θ)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hord : separationOrder A B ≤ z) :
    ¬ (π.gammaImage (π.Γ.N ∩ Θ) ⊆ A.vertexSet) := by
  intro hγ_sub
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hq_pos : 1 ≤ π.warpAt Θ :=
    theorem_5_1_proof π hT (hred.isZeroRedundant h𝒯) hΘ
  let I₁ : Set (Set π.S) := {c ∈ π.Γ.C | (c ∩ Θ).Nonempty}
  let I₂ : Set (Set π.S) := π.Γ.C \ I₁
  have hcov : I₁ ∪ I₂ = π.Γ.C := by
    ext c
    simp only [I₁, I₂, mem_union, mem_sdiff, mem_ofPred_eq]
    tauto
  have hdisj : Disjoint I₁ I₂ := disjoint_sdiff_self_right
  let A₁ := π.cellsUnion I₁
  let A₂ := π.cellsUnion I₂
  have hsepA₁₂ : G.IsSeparation A₁ A₂ := π.isSeparation_cellsUnion hcov hdisj
  have hA₁₂_sub_γ : (A₁ ∩ A₂).vertexSet ⊆ π.gammaImage (π.Γ.N ∩ Θ) := by
    intro v hv
    rw [(theorem_2_1_proof π hcov hdisj).2] at hv
    rcases hv with hγ | hbs
    · rw [mem_iUnion₂] at hγ
      rcases hγ with ⟨c₁, hc₁, hγ⟩
      rw [mem_iUnion₂] at hγ
      rcases hγ with ⟨c₂, _, hγ₁, _⟩
      have htilde₁ : tilde c₁ ⊆ π.Γ.N ∩ Θ :=
        (π.Γ.border_cell_subset_cuff hc₁.1 hΘ hc₁.2).2.2.2.1
      exact π.gammaImage_mono htilde₁ hγ₁
    · rw [mem_iUnion₂] at hbs
      rcases hbs with ⟨n, ⟨c₁, hc₁, _, c₂, hc₂, hc₂_bd, hnc₁, hnc₂⟩, _⟩
      exfalso
      have hnΘ : n ∈ Θ := ((π.Γ.border_cell_subset_cuff hc₁.1 hΘ hc₁.2).2.2.2.1 hnc₁).2
      rcases hc₂_bd with ⟨x, hxc₂, hxbd⟩
      let Θ' := connectedComponentIn (bd π.S) x
      have hΘ' : Θ' ∈ cuffs π.S := ⟨x, hxbd, rfl⟩
      have hc₂Θ' : (c₂ ∩ Θ').Nonempty := ⟨x, hxc₂, mem_connectedComponentIn hxbd⟩
      have hnΘ' : n ∈ Θ' := ((π.Γ.border_cell_subset_cuff hc₂.1 hΘ' hc₂Θ').2.2.2.1 hnc₂).2
      rcases hΘ with ⟨x₀, _, rfl⟩
      have hΘ_eq : connectedComponentIn (bd π.S) x₀ = Θ' :=
        (connectedComponentIn_eq hnΘ).trans (connectedComponentIn_eq hnΘ').symm
      exact hc₂.2 ⟨hc₂.1, hΘ_eq.symm ▸ hc₂Θ'⟩
  have hA₁₂_sub_A : (A₁ ∩ A₂).vertexSet ⊆ A.vertexSet := hA₁₂_sub_γ.trans hγ_sub
  have hsepAB : G.IsSeparation A B := h𝒯.isSeparation hAB
  let B₁ := B ∩ A₁
  let B₂ := B ∩ A₂
  have hB₁_le : B₁ ≤ G := inter_le hsepAB.right_le hsepA₁₂.left_le
  have hB₂_le : B₂ ≤ G := inter_le hsepAB.right_le hsepA₁₂.right_le
  have hB_union_V : B₁.vertexSet ∪ B₂.vertexSet = B.vertexSet := by
    ext x
    simp only [B₁, B₂, inter_vertexSet, mem_union, mem_inter_iff]
    refine ⟨fun h => h.elim And.left And.left, fun hxB => ?_⟩
    have hxG : x ∈ A₁.vertexSet ∪ A₂.vertexSet :=
      hsepA₁₂.vertexSet_union.symm ▸ hsepAB.right_le.vertexSet_subset hxB
    rcases hxG with hx₁ | hx₂
    · exact Or.inl ⟨hxB, hx₁⟩
    · exact Or.inr ⟨hxB, hx₂⟩
  have hB_union_E : B₁.edgeSet ∪ B₂.edgeSet = B.edgeSet := by
    ext e
    simp only [B₁, B₂, inter_edgeSet, mem_union, mem_inter_iff]
    refine ⟨fun h => h.elim And.left And.left, fun heB => ?_⟩
    have heG : e ∈ A₁.edgeSet ∪ A₂.edgeSet :=
      hsepA₁₂.edgeSet_union.symm ▸ hsepAB.right_le.edgeSet_subset heB
    rcases heG with he₁ | he₂
    · exact Or.inl ⟨heB, he₁⟩
    · exact Or.inr ⟨heB, he₂⟩
  have hB_inter_E : B₁.edgeSet ∩ B₂.edgeSet = ∅ := by
    ext e
    simp only [B₁, B₂, inter_edgeSet, mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, he₁⟩, ⟨_, he₂⟩⟩
    exact hsepA₁₂.notMem_edgeSet_right he₁ he₂
  have hsep1 : G.IsSeparation (A ∪ B₁) B₂ := by
    rw [isSeparation_iff_of_le (union_le hsepAB.left_le hB₁_le) hB₂_le]
    refine ⟨?_, ?_, ?_⟩
    · rw [union_vertexSet, Set.union_assoc, hB_union_V, hsepAB.vertexSet_union]
    · rw [union_edgeSet, Set.union_assoc, hB_union_E, hsepAB.edgeSet_union]
    · ext e
      simp only [union_edgeSet, mem_inter_iff, mem_union, mem_empty_iff_false, iff_false, not_and]
      rintro (heA | heB₁) heB₂
      · exact hsepAB.notMem_edgeSet_right heA heB₂.1
      · exact Set.notMem_empty e (hB_inter_E ▸ ⟨heB₁, heB₂⟩)
  have hsep2 : G.IsSeparation (A ∪ B₂) B₁ := by
    rw [isSeparation_iff_of_le (union_le hsepAB.left_le hB₂_le) hB₁_le]
    refine ⟨?_, ?_, ?_⟩
    · rw [union_vertexSet, Set.union_assoc, Set.union_comm B₂.vertexSet, hB_union_V,
        hsepAB.vertexSet_union]
    · rw [union_edgeSet, Set.union_assoc, Set.union_comm B₂.edgeSet, hB_union_E,
        hsepAB.edgeSet_union]
    · ext e
      simp only [union_edgeSet, mem_inter_iff, mem_union, mem_empty_iff_false, iff_false, not_and]
      rintro (heA | heB₂) heB₁
      · exact hsepAB.notMem_edgeSet_right heA heB₁.1
      · exact Set.notMem_empty e (hB_inter_E ▸ ⟨heB₁, heB₂⟩)
  have hsub_inter1 : ((A ∪ B₁) ∩ B₂).vertexSet ⊆ (A ∩ B).vertexSet := by
    rintro x ⟨hxA | ⟨hxB, hxA₁⟩, hxB, hxA₂⟩
    · exact ⟨hxA, hxB⟩
    · exact ⟨hA₁₂_sub_A ⟨hxA₁, hxA₂⟩, hxB⟩
  have hsub_inter2 : ((A ∪ B₂) ∩ B₁).vertexSet ⊆ (A ∩ B).vertexSet := by
    rintro x ⟨hxA | ⟨hxB, hxA₂⟩, hxB, hxA₁⟩
    · exact ⟨hxA, hxB⟩
    · exact ⟨hA₁₂_sub_A ⟨hxA₁, hxA₂⟩, hxB⟩
  have hord1 : separationOrder (A ∪ B₁) B₂ ≤ z :=
    (ncard_le_ncard hsub_inter1 (A ∩ B).vertexSet_finite).trans hord
  have hord2 : separationOrder (A ∪ B₂) B₁ ≤ z :=
    (ncard_le_ncard hsub_inter2 (A ∩ B).vertexSet_finite).trans hord
  have hnot_both : ¬ ((B₂, A ∪ B₁) ∈ 𝒯 ∧ (B₁, A ∪ B₂) ∈ 𝒯) := by
    rintro ⟨hm1, hm2⟩
    apply h𝒯.axiom2 hAB hm1 hm2
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (union_le (union_le hsepAB.left_le hB₂_le) hB₁_le) le_rfl
    · rw [union_vertexSet, union_vertexSet, Set.union_assoc, Set.union_comm B₂.vertexSet,
        hB_union_V, hsepAB.vertexSet_union]
    · rw [union_edgeSet, union_edgeSet, Set.union_assoc, Set.union_comm B₂.edgeSet,
        hB_union_E, hsepAB.edgeSet_union]
  have hm1_or_m2 : (A ∪ B₁, B₂) ∈ 𝒯 ∨ (A ∪ B₂, B₁) ∈ 𝒯 := by
    rcases h𝒯.axiom1 hsep1 (by omega) with h1 | h1
    · exact Or.inl h1
    · rcases h𝒯.axiom1 hsep2 (by omega) with h2 | h2
      · exact Or.inr h2
      · exact (hnot_both ⟨h1, h2⟩).elim
  rcases hm1_or_m2 with hm1 | hm2
  · obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hred_2p3 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono hz
    obtain ⟨SL⟩ := exists_cuffStandardLinkages h𝒯 π htrue hred_2p3 hwarp
      (by omega) E
    have hcard : ∀ r : Fin (π.Γ.N ∩ Θ).ncard, (π.borderSet (E.node r)).ncard = π.warpAt Θ :=
      fun r => theorem_9_4_proof h𝒯 π htrue hred_2p3 hwarp (by omega) hΘ (E.node_mem r)
    let i₀ : Fin (π.Γ.N ∩ Θ).ncard := ⟨0, by linarith [E.two_le]⟩
    have hn₀_bd : E.node i₀ ∈ π.Γ.N ∩ bd π.S := ⟨(E.node_mem i₀).1, hΘ_bd (E.node_mem i₀).2⟩
    have hne_bs : (π.borderSet (E.node i₀)).Nonempty :=
      (ncard_pos (π.borderSet_finite hn₀_bd)).mp (by rw [hcard i₀]; exact hq_pos)
    rcases hne_bs with ⟨v, hv⟩
    have hsub_A₁ : SL.circumnavigationVertices i₀ v ⊆ (A ∪ B₁).vertexSet := by
      refine (SL.circumnavigationVertices_subset_cellsUnion hcard i₀ hv).trans ?_
      intro x hxA₁
      have hxG : x ∈ A.vertexSet ∪ B.vertexSet :=
        hsepAB.vertexSet_union.symm ▸ hsepA₁₂.left_le.vertexSet_subset hxA₁
      rcases hxG with hxA | hxB
      · exact Or.inl hxA
      · exact Or.inr ⟨hxB, hxA₁⟩
    exact theorem_10_2_proof SL h𝒯 hT hwarp hred hz hθ rfl hcard i₀ hv hm1 hord1 hsub_A₁
  · have hsmall : IsSmallWrt 𝒯 (A ∪ B₂) := ⟨B₁, hm2⟩
    have hatt_sub : attachments G (A ∪ B₂) ⊆ (A ∩ B).vertexSet :=
      (attachments_subset_inter_of_isSeparation hsep2).trans hsub_inter2
    have hatt_lt : (attachments G (A ∪ B₂)).ncard < θ - 2 * p := by
      have hle : (attachments G (A ∪ B₂)).ncard ≤ z :=
        (ncard_le_ncard hatt_sub (A ∩ B).vertexSet_finite).trans hord
      omega
    refine theorem_4_3_proof h𝒯 π hT hwarp ⟨A ∪ B₂, hsmall, hatt_lt, ?_⟩
    intro n hn_dom
    by_cases hnΘ : n ∈ Θ
    · have hxA : π.nodeVertex n ∈ A.vertexSet :=
        hγ_sub ⟨n, ⟨⟨π.domγ_subset hn_dom, hnΘ⟩, hn_dom⟩, rfl⟩
      exact Or.inl hxA
    · have hred_2p3 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono hz
      obtain ⟨c, hc, hnc⟩ :=
        (theorem_8_2_proof
          h𝒯 π htrue hred_2p3 hwarp (by omega)).2.2 n (π.domγ_subset hn_dom)
      have hvc : π.nodeVertex n ∈ (π.cellGraph c).vertexSet := π.p2 c hc n ⟨hnc, hn_dom⟩
      have hc_not_I₁ : c ∉ I₁ := by
        rintro ⟨_, hcΘ⟩
        exact hnΘ ((π.Γ.border_cell_subset_cuff hc hΘ hcΘ).2.2.2.1 hnc).2
      have hc_I₂ : c ∈ I₂ := ⟨hc, hc_not_I₁⟩
      have hxA₂ : π.nodeVertex n ∈ A₂.vertexSet :=
        mem_iUnion₂.mpr ⟨c, ⟨hc_I₂, hc⟩, hvc⟩
      have hxG : π.nodeVertex n ∈ A.vertexSet ∪ B.vertexSet :=
        hsepAB.vertexSet_union.symm ▸ π.nodeVertex_mem n hn_dom
      rcases hxG with hxA | hxB
      · exact Or.inl hxA
      · exact Or.inr ⟨hxB, hxA₂⟩

end GraphMinor.GM17
