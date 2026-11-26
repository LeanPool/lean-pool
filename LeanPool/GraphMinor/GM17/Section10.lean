/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section9b
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode

import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Graph Minors XVII, Section 10: Circumnavigating a Vortex

This file formalizes Section 10 (pages 188–189) of N. Robertson and P. D. Seymour,
*Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210:
- Standard linkages around a cuff (`exists_cuffStandardLinkages`) and the circumnavigation walks
  $L(v, n_0)$ (`CuffStandardLinkages.circWalk`, `CuffStandardLinkages.circumnavigationVertices`).
- **Graph Minors XVII, (10.1)** (`theorem_10_1`, page 188): structural properties of $L(v, n_0)$
  (paths vs. circuits, disjointness of tails, and shared endpoints).
- **Graph Minors XVII, (10.2)** (`theorem_10_2`, page 188): no separation $(A, B) \in \mathcal{T}$
  of order $\le z$ satisfies $V(L(v, n_0)) \subseteq V(A)$.
- **Graph Minors XVII, (10.3)** (`theorem_10_3`, page 189): for each cuff $\Theta$, no separation
  $(A, B) \in \mathcal{T}$ of order $\le z$ satisfies $\gamma(N(\Gamma) \cap \Theta) \subseteq
  V(A)$.
The portrayal deductions that use painting results are proved in `Section10Proved`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Helper Lemmas on Walks and Subhypergraphs -/

theorem skeleton_le_of_le {α : Type u} {β : Type v}
    {H₁ H₂ : Hypergraph α β} (h : H₁ ≤ H₂) :
    H₁.skeleton ≤ H₂.skeleton := by
  intro u v ⟨hne, e, heu, hev⟩
  have heH₁ : e ∈ H₁.edgeSet := H₁.edge_mem_of_inc heu
  have hends := h.ends_eq e heH₁
  have heu' : H₂.Inc e u := by change u ∈ H₂.ends e; rw [hends]; exact heu
  have hev' : H₂.Inc e v := by change v ∈ H₂.ends e; rw [hends]; exact hev
  exact ⟨hne, e, heu', hev'⟩

theorem end_mem_support_tail_of_support_tail_ne_nil {α : Type u} {G : SimpleGraph α} {u w : α}
    (W : G.Walk u w) (h : W.support.tail ≠ []) : w ∈ W.support.tail := by
  cases W with
  | nil => simp at h
  | cons _ W' => exact W'.end_mem_support

theorem start_eq_end_of_support_tail_eq_nil {α : Type u} {G : SimpleGraph α} {u w : α}
    (W : G.Walk u w) (h : W.support.tail = []) : u = w := by
  cases W with
  | nil => rfl
  | cons _ W' =>
    exfalso
    exact SimpleGraph.Walk.support_ne_nil W' h

/-! ## 2. Entry Uniqueness on a Cuff (Dual of Claim (1) of (6.6)) -/

/-- Dual of `lemma_6_6_claim_1`: for each $x \in V(G)$, there is at most one index $i \in \text{Fin
} k$
such that $x \notin \beta(n_i+)$ and $x \in \beta(n_{i+1}+)$. -/
theorem unique_entry_index {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {x : α} {i₁ i₂ : Fin k}
    (hi₁ : x ∉ π.borderPlus (E.node i₁) ∧
      x ∈ π.borderPlus (E.node (cyclicSucc (by have := E.two_le; omega) i₁)))
    (hi₂ : x ∉ π.borderPlus (E.node i₂) ∧
      x ∈ π.borderPlus (E.node (cyclicSucc (by have := E.two_le; omega) i₂))) :
    i₁ = i₂ := by
  by_contra hne
  have hk : 2 ≤ k := E.two_le
  have hk_pos : 0 < k := by omega
  have v12 : i₁.1 ≠ i₂.1 := fun h => hne (Fin.ext h)
  have b1 := i₁.2
  have b2 := i₂.2
  have hcyc : cyclicDist (cyclicSucc hk_pos i₁) i₂ + cyclicDist i₂ (cyclicSucc hk_pos i₂) +
      cyclicDist (cyclicSucc hk_pos i₂) i₁ ≤ k := by
    have hnext1 : (cyclicSucc hk_pos i₁).1 = if i₁.1 + 1 < k then i₁.1 + 1 else 0 := by
      change (i₁.1 + 1) % k = _
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · have : i₁.1 + 1 = k := by omega
        rw [this, Nat.mod_self]
    have hnext2 : (cyclicSucc hk_pos i₂).1 = if i₂.1 + 1 < k then i₂.1 + 1 else 0 := by
      change (i₂.1 + 1) % k = _
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · have : i₂.1 + 1 = k := by omega
        rw [this, Nat.mod_self]
    simp only [cyclicDist_eq_ite, hnext1, hnext2]
    split_ifs <;> omega
  have hp7 := π.p7_of_cyclicDist E hcyc hi₁.2 hi₂.2
  rcases hp7 with h2 | h1
  · exact hi₂.1 h2
  · exact hi₁.1 h1

/-! ## 3. Standard Linkages and Circumnavigation Walks $L(v, n_0)$ (Page 188) -/

section Circumnavigation

variable {α : Type u} {β : Type v} {G : Hypergraph α β}
variable {π : Portrayal G} {Θ : Set π.S} {k q : ℕ} {E : π.Γ.CuffEnumeration Θ k}
variable (SL : CuffStandardLinkages π Θ k q E)

theorem Painting.CuffEnumeration.cell_mem (E : π.Γ.CuffEnumeration Θ k) (i : Fin k) :
    E.cell i ∈ π.Γ.C := by
  have h : E.cell i ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
    rw [← E.range_cell]; exact mem_range_self i
  exact h.1

theorem Painting.CuffEnumeration.cell_inter_cuff_nonempty
    (E : π.Γ.CuffEnumeration Θ k) (i : Fin k) :
    (E.cell i ∩ Θ).Nonempty := by
  have h : E.cell i ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
    rw [← E.range_cell]; exact mem_range_self i
  exact h.2

theorem Painting.CuffEnumeration.node_mem (E : π.Γ.CuffEnumeration Θ k) (i : Fin k) :
    E.node i ∈ π.Γ.N ∩ Θ := by
  rw [← E.range_node]; exact mem_range_self i

open Classical in
/-- Next vertex along the standard linkage at step $i : \text{Fin } k$. -/
noncomputable def CuffStandardLinkages.stepVertex (i : Fin k) (u : α) : α :=
  if h : ∃ j : Fin q, (SL.L i j).first = u then
    (SL.L i (Classical.choose h)).last
  else u

open Classical in
/-- The walk in $(\pi.\text{cellGraph } (E.\text{cell } i)).\text{skeleton}$ from $u$ to
`SL.stepVertex i u`. -/
noncomputable def CuffStandardLinkages.stepCellWalk (i : Fin k) (u : α) :
    (π.cellGraph (E.cell i)).skeleton.Walk u (SL.stepVertex i u) :=
  if h : ∃ j : Fin q, (SL.L i j).first = u then
    ((SL.L i (Classical.choose h)).walk).copy (Classical.choose_spec h)
      (by dsimp [CuffStandardLinkages.stepVertex]; rw [dite_eq_left h])
  else
    SimpleGraph.Walk.nil.copy rfl
      (by dsimp [CuffStandardLinkages.stepVertex]; rw [dite_eq_right h])

/-- The walk in $G.\text{skeleton}$ from $u$ to `SL.stepVertex i u`. -/
noncomputable def CuffStandardLinkages.stepWalk (i : Fin k) (u : α) :
    G.skeleton.Walk u (SL.stepVertex i u) :=
  (SL.stepCellWalk i u).map
    (SimpleGraph.Hom.ofLE (skeleton_le_of_le (π.cellGraph_le (E.cell i) (E.cell_mem i))))

@[simp]
theorem CuffStandardLinkages.support_stepWalk (i : Fin k) (u : α) :
    (SL.stepWalk i u).support = (SL.stepCellWalk i u).support := by
  simp [CuffStandardLinkages.stepWalk]

/-- Cyclic index `(i₀.1 + m) % k` used at step `m` of `traceVertex`. -/
def stepIdx {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k) (m : ℕ) : Fin k :=
  ⟨(i₀.1 + m) % k, Nat.mod_lt _ (by omega)⟩

@[simp]
theorem stepIdx_zero {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k) :
    stepIdx hk i₀ 0 = i₀ := by
  ext; simp [stepIdx, Nat.mod_eq_of_lt i₀.2]

@[simp]
theorem stepIdx_self {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k) :
    stepIdx hk i₀ k = i₀ := by
  ext; simp [stepIdx, Nat.add_mod_right, Nat.mod_eq_of_lt i₀.2]

theorem stepIdx_succ {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k) (m : ℕ) :
    stepIdx hk i₀ (m + 1) = cyclicSucc (by omega) (stepIdx hk i₀ m) := by
  ext
  change (i₀.1 + (m + 1)) % k = ((i₀.1 + m) % k + 1) % k
  rw [← Nat.add_assoc, Nat.mod_add_mod]

theorem stepIdx_ne_of_lt {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k) {m₁ m₂ : ℕ}
    (hm₁ : m₁ < m₂) (hm₂ : m₂ < k) :
    stepIdx hk i₀ m₁ ≠ stepIdx hk i₀ m₂ := by
  intro hEq
  have hval : (i₀.1 + m₁) % k = (i₀.1 + m₂) % k := congrArg Fin.val hEq
  have hi₀ := i₀.2
  by_cases h1 : i₀.1 + m₁ < k <;> by_cases h2 : i₀.1 + m₂ < k
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval; omega
  · have h2' : i₀.1 + m₂ = (i₀.1 + m₂ - k) + 1 * k := by omega
    rw [Nat.mod_eq_of_lt h1, h2', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hval
    omega
  · omega
  · have h1' : i₀.1 + m₁ = (i₀.1 + m₁ - k) + 1 * k := by omega
    have h2' : i₀.1 + m₂ = (i₀.1 + m₂ - k) + 1 * k := by omega
    rw [h1', h2', Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hval
    omega

theorem stepIdx_surjective {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k) (j : Fin k) :
    ∃ r < k, stepIdx hk i₀ r = j := by
  by_cases hle : i₀.1 ≤ j.1
  · refine ⟨j.1 - i₀.1, by omega, ?_⟩
    ext
    change (i₀.1 + (j.1 - i₀.1)) % k = j.1
    rw [Nat.add_sub_of_le hle, Nat.mod_eq_of_lt j.2]
  · refine ⟨j.1 + k - i₀.1, by omega, ?_⟩
    ext
    change (i₀.1 + (j.1 + k - i₀.1)) % k = j.1
    have hEq : i₀.1 + (j.1 + k - i₀.1) = j.1 + k := by omega
    rw [hEq, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]

theorem CuffStandardLinkages.traceVertex_succ (i₀ : Fin k) (v : α) (m : ℕ) :
    SL.traceVertex i₀ v (m + 1) = SL.stepVertex (stepIdx E.two_le i₀ m) (SL.traceVertex i₀ v m) :=
  rfl

/-- Inductively defined walk $P_1 \cup \dots \cup P_m$ ($0 \le m \le k$) in $G^*$ from $v$ to
`SL.traceVertex i₀ v m`, giving $L(v, n_0)$ when $m = k$
(Graph Minors XVII, Section 10, page 188). -/
noncomputable def CuffStandardLinkages.circWalk
    (SL : CuffStandardLinkages π Θ k q E) (i₀ : Fin k) (v : α) :
    (m : ℕ) → G.skeleton.Walk v (SL.traceVertex i₀ v m)
  | 0 => .nil
  | m + 1 =>
    (SL.circWalk i₀ v m).append
      (SL.stepWalk (stepIdx E.two_le i₀ m) (SL.traceVertex i₀ v m))

theorem CuffStandardLinkages.support_tail_circWalk_succ (i₀ : Fin k) (v : α) (m : ℕ) :
    (SL.circWalk i₀ v (m + 1)).support.tail =
      (SL.circWalk i₀ v m).support.tail ++
        (SL.stepWalk (stepIdx E.two_le i₀ m) (SL.traceVertex i₀ v m)).support.tail := by
  change ((SL.circWalk i₀ v m).append
    (SL.stepWalk (stepIdx E.two_le i₀ m) (SL.traceVertex i₀ v m))).support.tail = _
  rw [SimpleGraph.Walk.support_append]
  have hcons := (SL.circWalk i₀ v m).cons_tail_support
  conv_lhs => rw [← hcons, List.cons_append, List.tail_cons]

theorem CuffStandardLinkages.mem_support_tail_circWalk_iff (i₀ : Fin k) (v : α) (m : ℕ) (z : α) :
    z ∈ (SL.circWalk i₀ v m).support.tail ↔
      ∃ r < m, z ∈ (SL.stepWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r)).support.tail := by
  induction m with
  | zero =>
    change z ∈ ([] : List α) ↔ _
    simp
  | succ m ih =>
    rw [SL.support_tail_circWalk_succ, List.mem_append, ih]
    constructor
    · rintro (⟨r, hr, hz⟩ | hz)
      · exact ⟨r, Nat.lt_succ_of_lt hr, hz⟩
      · exact ⟨m, Nat.lt_succ_self m, hz⟩
    · rintro ⟨r, hr, hz⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
      · exact Or.inl ⟨r, hlt, hz⟩
      · exact Or.inr hz

theorem CuffStandardLinkages.last_inj (i : Fin k) {a b : Fin q}
    (hEq : (SL.L i a).last = (SL.L i b).last) : a = b := by
  by_contra hne
  have ha : (SL.L i a).last ∈ (SL.L i a).walk.support :=
    (SL.L i a).walk.end_mem_support
  have hb : (SL.L i a).last ∈ (SL.L i b).walk.support := by
    rw [hEq]
    exact (SL.L i b).walk.end_mem_support
  exact Set.disjoint_left.mp ((SL.isStandard i).1 hne) ha hb

theorem CuffStandardLinkages.exists_first_eq
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) {u : α} (hu : u ∈ π.borderSet (E.node i)) :
    ∃ a : Fin q, (SL.L i a).first = u := by
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases E.cuff_mem with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hn_bd : E.node i ∈ π.Γ.N ∩ bd π.S := ⟨(E.node_mem i).1, hΘ_bd (E.node_mem i).2⟩
  have hfin : (π.borderSet (E.node i)).Finite := π.borderSet_finite hn_bd
  exact exists_first_eq_of_ncard_le hfin (hcard i).le (SL.L i) (SL.isStandard i).1 hu

theorem CuffStandardLinkages.exists_last_eq
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) {w : α}
    (hw : w ∈ π.borderSet (E.node (cyclicSucc (by have := E.two_le; omega) i))) :
    ∃ a : Fin q, (SL.L i a).last = w := by
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases E.cuff_mem with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  let j := cyclicSucc (by have := E.two_le; omega) i
  have hj_bd : E.node j ∈ π.Γ.N ∩ bd π.S := ⟨(E.node_mem j).1, hΘ_bd (E.node_mem j).2⟩
  have hfin : (π.borderSet (E.node j)).Finite := π.borderSet_finite hj_bd
  exact exists_last_eq_of_ncard_le hfin (hcard j).le (SL.L i) (SL.isStandard i).1 hw

theorem CuffStandardLinkages.step_spec_of_mem
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) {u : α} (hu : u ∈ π.borderSet (E.node i)) :
    ∃ a : Fin q,
      (SL.L i a).first = u ∧
      SL.stepVertex i u = (SL.L i a).last ∧
      (SL.stepCellWalk i u).support = (SL.L i a).walk.support ∧
      (SL.stepWalk i u).support = (SL.L i a).walk.support ∧
      (SL.stepWalk i u).IsPath ∧
      SL.stepVertex i u ∈ π.borderSet (E.node (cyclicSucc (by have := E.two_le; omega) i)) := by
  have hex := SL.exists_first_eq hcard i hu
  let a := Classical.choose hex
  have ha : (SL.L i a).first = u := Classical.choose_spec hex
  have hstep : SL.stepVertex i u = (SL.L i a).last := dite_eq_left hex
  have hcell_sup : (SL.stepCellWalk i u).support = (SL.L i a).walk.support := by
    unfold CuffStandardLinkages.stepCellWalk
    rw [dite_eq_left hex, SimpleGraph.Walk.support_copy]
  have hwalk_sup : (SL.stepWalk i u).support = (SL.L i a).walk.support :=
    (SL.support_stepWalk i u).trans hcell_sup
  have hisPath : (SL.stepWalk i u).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hwalk_sup]
    exact (SL.L i a).isPath.support_nodup
  refine ⟨a, ha, hstep, hcell_sup, hwalk_sup, hisPath, ?_⟩
  rw [hstep]
  exact (SL.L i a).last_mem

theorem CuffStandardLinkages.stepVertex_injOn
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) :
    InjOn (SL.stepVertex i) (π.borderSet (E.node i)) := by
  intro u₁ hu₁ u₂ hu₂ hEq
  obtain ⟨a₁, ha₁, hstep₁, _, _, _, _⟩ := SL.step_spec_of_mem hcard i hu₁
  obtain ⟨a₂, ha₂, hstep₂, _, _, _, _⟩ := SL.step_spec_of_mem hcard i hu₂
  have ha_eq : a₁ = a₂ := SL.last_inj i (hstep₁.symm.trans (hEq.trans hstep₂))
  rw [← ha₁, ← ha₂, ha_eq]

theorem CuffStandardLinkages.traceVertex_mem_borderSet
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) {v : α} (hv : v ∈ π.borderSet (E.node i₀)) (m : ℕ) :
    SL.traceVertex i₀ v m ∈ π.borderSet (E.node (stepIdx E.two_le i₀ m)) := by
  induction m with
  | zero =>
    rw [stepIdx_zero]
    exact hv
  | succ m ih =>
    rw [SL.traceVertex_succ, stepIdx_succ]
    exact (SL.step_spec_of_mem hcard (stepIdx E.two_le i₀ m) ih).choose_spec.2.2.2.2.2

theorem CuffStandardLinkages.traceVertex_injOn
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) (m : ℕ) :
    InjOn (fun v => SL.traceVertex i₀ v m) (π.borderSet (E.node i₀)) := by
  induction m with
  | zero => exact fun _ _ _ _ h => h
  | succ m ih =>
    intro v₁ hv₁ v₂ hv₂ hEq
    apply ih hv₁ hv₂
    exact SL.stepVertex_injOn hcard (stepIdx E.two_le i₀ m)
      (SL.traceVertex_mem_borderSet hcard i₀ hv₁ m)
      (SL.traceVertex_mem_borderSet hcard i₀ hv₂ m) hEq

theorem CuffStandardLinkages.mem_support_inter_borderSet_left
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) (a : Fin q) {z : α}
    (hz_sup : z ∈ (SL.L i a).walk.support)
    (hz_bs : z ∈ π.borderSet (E.node i)) :
    z = (SL.L i a).first := by
  obtain ⟨b, hb⟩ := SL.exists_first_eq hcard i hz_bs
  have hab : a = b := by
    by_contra hne
    exact Set.disjoint_left.mp ((SL.isStandard i).1 hne) hz_sup
      (hb ▸ (SL.L i b).walk.start_mem_support)
  rw [hab, hb]

theorem CuffStandardLinkages.mem_support_inter_borderSet_right
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i : Fin k) (a : Fin q) {z : α}
    (hz_sup : z ∈ (SL.L i a).walk.support)
    (hz_bs : z ∈ π.borderSet (E.node (cyclicSucc (by have := E.two_le; omega) i))) :
    z = (SL.L i a).last := by
  obtain ⟨b, hb⟩ := SL.exists_last_eq hcard i hz_bs
  have hab : a = b := by
    by_contra hne
    exact Set.disjoint_left.mp ((SL.isStandard i).1 hne) hz_sup
      (hb ▸ (SL.L i b).walk.end_mem_support)
  rw [hab, hb]

/-- The vertex set of `SL.circWalk i₀ v k` equals `SL.circumnavigationVertices i₀ v`. -/
theorem CuffStandardLinkages.support_circWalk_eq_circumnavigationVertices
    (i₀ : Fin k) (v : α) :
    {z | z ∈ (SL.circWalk i₀ v k).support} = SL.circumnavigationVertices i₀ v := by
  classical
  have hstep_set : ∀ r : ℕ,
      {z | z ∈ (SL.stepWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r)).support} =
      (let idx : Fin k := ⟨(i₀.1 + r) % k, Nat.mod_lt _ (by have := E.two_le; omega)⟩
       let cur := SL.traceVertex i₀ v r
       if h : ∃ j : Fin q, (SL.L idx j).first = cur then
         {z | z ∈ (SL.L idx (Classical.choose h)).walk.support}
       else {cur}) := by
    intro r
    rw [SL.support_stepWalk]
    dsimp only [CuffStandardLinkages.stepCellWalk, stepIdx]
    by_cases h : ∃ j : Fin q,
        (SL.L ⟨(i₀.1 + r) % k, Nat.mod_lt _ (by have := E.two_le; omega)⟩ j).first =
          SL.traceVertex i₀ v r
    · rw [dite_eq_left h, dite_eq_left h, SimpleGraph.Walk.support_copy]
    · rw [dite_eq_right h, dite_eq_right h, SimpleGraph.Walk.support_copy]
      ext z
      simp
  have hind : ∀ m : ℕ, 1 ≤ m →
      {z | z ∈ (SL.circWalk i₀ v m).support} =
        ⋃ r ∈ Finset.range m,
          {z | z ∈ (SL.stepWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r)).support} := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases m with _ | m
      · ext z
        change z ∈ (SimpleGraph.Walk.nil.append (SL.stepWalk (stepIdx E.two_le i₀ 0) v)).support ↔
          z ∈ ⋃ r ∈ Finset.range 1,
            {z | z ∈ (SL.stepWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r)).support}
        rw [SimpleGraph.Walk.nil_append, Finset.range_one]
        simp only [Finset.mem_singleton, iUnion_iUnion_eq_left, mem_ofPred_eq]
        rfl
      · rw [Finset.range_add_one]
        ext z
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union, mem_ofPred_eq]
        change z ∈ ((SL.circWalk i₀ v (m + 1)).append
          (SL.stepWalk (stepIdx E.two_le i₀ (m + 1)) (SL.traceVertex i₀ v (m + 1)))).support ↔ _
        rw [SimpleGraph.Walk.mem_support_append_iff, or_comm]
        exact or_congr Iff.rfl (Set.ext_iff.mp (ih (by omega)) z)
  rw [hind k (by linarith [E.two_le])]
  unfold CuffStandardLinkages.circumnavigationVertices
  refine iUnion₂_congr fun r _ => hstep_set r

theorem CuffStandardLinkages.support_stepCellWalk_subset_circumnavigationVertices
    (i₀ : Fin k) (v : α) {r : ℕ} (hr : r < k) :
    {z | z ∈ (SL.stepCellWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r)).support} ⊆
      SL.circumnavigationVertices i₀ v := by
  intro z hz
  change z ∈ (SL.stepCellWalk (stepIdx E.two_le i₀ r) (SL.traceVertex i₀ v r)).support at hz
  unfold CuffStandardLinkages.circumnavigationVertices
  refine mem_iUnion₂.mpr ⟨r, Finset.mem_range.mpr hr, ?_⟩
  dsimp only [CuffStandardLinkages.stepCellWalk, stepIdx] at hz ⊢
  by_cases h : ∃ j : Fin q,
      (SL.L ⟨(i₀.1 + r) % k, Nat.mod_lt _ (by have := E.two_le; omega)⟩ j).first =
        SL.traceVertex i₀ v r
  · rw [dite_eq_left h, SimpleGraph.Walk.support_copy] at hz
    rw [dite_eq_left h]
    exact hz
  · rw [dite_eq_right h, SimpleGraph.Walk.support_copy] at hz
    rw [dite_eq_right h]
    simpa using hz

theorem CuffStandardLinkages.traceVertex_mem_circumnavigationVertices
    (i₀ : Fin k) (v : α) {r : ℕ} (hr : r < k) :
    SL.traceVertex i₀ v r ∈ SL.circumnavigationVertices i₀ v :=
  SL.support_stepCellWalk_subset_circumnavigationVertices i₀ v hr
    (SimpleGraph.Walk.start_mem_support _)

end Circumnavigation

end GraphMinor.GM17
