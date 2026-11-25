/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM09.DiscDrawing
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2b
import LeanPool.GraphMinor.GM09.Section2c
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a

/-!
# Graph Minors IX, Section 2 (Part 5): Proof of (2.4)

This file formalizes Theorem (2.4) from Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 45–46):
every 3-connected society `(G, Ω)` with no cross or tripod is rural.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-! ## Subpaths Indexed by Support Positions and Cyclic Permutations from Nodup Lists -/

theorem nodup_getElem_inj {L : List α} (hnd : L.Nodup) {i j : ℕ}
    (hi : i < L.length) (hj : j < L.length) (h : L[i] = L[j]) : i = j := by
  induction L generalizing i j with
  | nil => exact (Nat.not_lt_zero i hi).elim
  | cons a L' ih =>
    obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
        exact (ha (h ▸ List.getElem_mem hj)).elim
    | succ i' =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      cases j with
      | zero =>
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
        exact (ha (h.symm ▸ List.getElem_mem hi)).elim
      | succ j' =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
        simp only [List.getElem_cons_succ] at h
        exact congrArg (· + 1) (ih hnd' hi hj h)

theorem walkSubgraph_cons_tail_le {G : Graph α β} {u w v : α} {e : β}
    (hlink : G.IsLink e u w) (W' : GraphWalk G w v) :
    walkSubgraph W' ≤ walkSubgraph (.cons hlink W') := by
  rw [(Compatible.of_le_le (walkSubgraph_le W') (walkSubgraph_le (.cons hlink W'))).le_iff]
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · rw [vertexSet_walkSubgraph] at hx ⊢
    exact List.mem_cons_of_mem u hx
  · rw [edgeSet_walkSubgraph] at hf ⊢
    exact List.mem_cons_of_mem e hf

theorem support_getElem_zero {G : Graph α β} {u v : α} (W : GraphWalk G u v)
    (h0 : 0 < W.support.length) : W.support[0]'h0 = u := by
  cases W <;> rfl

/-- For any simple walk `W : GraphWalk G u v` and indices `i ≤ j < W.support.length`, there is a
subpath `Q ≤ walkSubgraph W` from `W.support[i]` to `W.support[j]` whose vertex set consists of
`W.support[k]` for `i ≤ k ≤ j`. -/
theorem exists_subpath_of_support_indices {G : Graph α β} {u v : α}
    {W : GraphWalk G u v} (hW : W.IsSimple) {i j : ℕ}
    (hij : i ≤ j) (hj : j < W.support.length) :
    ∃ Q : Graph α β, Q ≤ walkSubgraph W ∧
      IsGraphPathWithEnds G Q (W.support[i]'(Nat.lt_of_le_of_lt hij hj)) (W.support[j]'hj) ∧
      V(Q) = {x | ∃ (k : ℕ) (hk : k < W.support.length), i ≤ k ∧ k ≤ j ∧ W.support[k]'hk = x} := by
  induction W generalizing i j with
  | @nil u hu =>
    simp only [GraphWalk.support_nil, List.length_singleton] at hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0 hj0
    refine ⟨walkSubgraph (.nil hu), le_rfl,
      isGraphPathWithEnds_walkSubgraph (by simp [GraphWalk.IsSimple]), ?_⟩
    ext x
    simp only [vertexSet_walkSubgraph, GraphWalk.support_nil, List.mem_singleton, mem_ofPred_eq,
      List.length_singleton]
    constructor
    · rintro rfl
      exact ⟨0, by omega, le_rfl, le_rfl, rfl⟩
    · rintro ⟨k, hk, _, _, rfl⟩
      have hk0 : k = 0 := by omega
      subst hk0
      rfl
  | @cons u w v e hlink W' ih =>
    have hnd : (u :: W'.support).Nodup := hW
    obtain ⟨hu_not, hW'⟩ := List.nodup_cons.mp hnd
    have htail_le : walkSubgraph W' ≤ walkSubgraph (.cons hlink W') :=
      walkSubgraph_cons_tail_le hlink W'
    cases i with
    | zero =>
      cases j with
      | zero =>
        let W₀ : GraphWalk G u u := .nil hlink.left_mem
        have hW₀_le : walkSubgraph W₀ ≤ walkSubgraph (.cons hlink W') := by
          rw [(Compatible.of_le_le (walkSubgraph_le W₀) (walkSubgraph_le (.cons hlink W'))).le_iff]
          refine ⟨fun x hx => ?_, fun f hf => ?_⟩
          · rw [vertexSet_walkSubgraph] at hx ⊢
            simp only [W₀, GraphWalk.support_nil, List.mem_singleton] at hx
            subst hx
            exact List.mem_cons_self
          · rw [edgeSet_walkSubgraph] at hf
            simp [W₀] at hf
        refine ⟨walkSubgraph W₀, hW₀_le,
          isGraphPathWithEnds_walkSubgraph (by simp [W₀, GraphWalk.IsSimple]), ?_⟩
        ext x
        simp only [vertexSet_walkSubgraph, W₀, GraphWalk.support_nil, List.mem_singleton,
          mem_ofPred_eq, GraphWalk.support_cons, List.length_cons]
        constructor
        · rintro rfl
          exact ⟨0, by omega, le_rfl, le_rfl, rfl⟩
        · rintro ⟨k, _, _, hk0, rfl⟩
          have hk_eq : k = 0 := by omega
          subst hk_eq
          rfl
      | succ j' =>
        have hj' : j' < W'.support.length := by
          simp only [GraphWalk.support_cons, List.length_cons] at hj
          omega
        obtain ⟨Q', hQ'_le, hQ'_path, hVQ'⟩ := ih hW' (Nat.zero_le j') hj'
        have hw_mem : w ∈ W'.support := W'.start_mem_support
        have huw_ne : u ≠ w := fun h => hu_not (h ▸ hw_mem)
        let W₁ : GraphWalk G u w := .cons hlink (.nil hlink.right_mem)
        have hW₁_simple : W₁.IsSimple := by simp [W₁, GraphWalk.IsSimple, huw_ne]
        let Q₁ := walkSubgraph W₁
        have hQ₁_le : Q₁ ≤ walkSubgraph (.cons hlink W') := by
          rw [(Compatible.of_le_le (walkSubgraph_le W₁) (walkSubgraph_le (.cons hlink W'))).le_iff]
          refine ⟨fun x hx => ?_, fun f hf => ?_⟩
          · rw [vertexSet_walkSubgraph] at hx ⊢
            simp only [W₁, GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem u hw_mem
          · rw [edgeSet_walkSubgraph] at hf ⊢
            simp only [W₁, GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton] at hf
            subst hf
            exact List.mem_cons_self
        have hQ₁_path : IsGraphPathWithEnds G Q₁ u w := isGraphPathWithEnds_walkSubgraph hW₁_simple
        have hw_eq0 : W'.support[0]'(Nat.zero_lt_of_lt hj') = w :=
          support_getElem_zero W' (Nat.zero_lt_of_lt hj')
        have hQ'_path' : IsGraphPathWithEnds G Q' w (W'.support[j']'hj') := by
          simpa [hw_eq0] using hQ'_path
        have hinter : V(Q₁) ∩ V(Q') = {w} := by
          ext x
          simp only [Q₁, vertexSet_walkSubgraph, W₁, GraphWalk.support_cons, GraphWalk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false, mem_inter_iff, mem_ofPred_eq,
            mem_singleton_iff]
          constructor
          · rintro ⟨rfl | rfl, hxQ'⟩
            · have hxW' : x ∈ W'.support := by
                have := hQ'_le.vertexSet_mono hxQ'
                rwa [vertexSet_walkSubgraph] at this
              exact (hu_not hxW').elim
            · rfl
          · rintro rfl
            exact ⟨Or.inr rfl, hQ'_path'.left_mem⟩
        refine ⟨subgraphUnion G Q₁ Q',
          (subgraphUnion_le_iff (hQ₁_le.trans (walkSubgraph_le _))
            ((hQ'_le.trans htail_le).trans (walkSubgraph_le _)) (walkSubgraph_le _)).mpr
            ⟨hQ₁_le, hQ'_le.trans htail_le⟩,
          hQ₁_path.subgraphUnion hQ'_path' hinter, ?_⟩
        ext x
        rw [vertexSet_subgraphUnion, hVQ']
        simp only [Q₁, vertexSet_walkSubgraph, W₁, GraphWalk.support_cons, GraphWalk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false, mem_union, mem_ofPred_eq, List.length_cons]
        constructor
        · rintro ((rfl | rfl) | ⟨k', hk', _, hk'j', rfl⟩)
          · exact ⟨0, by omega, le_rfl, by omega, rfl⟩
          · refine ⟨1, by omega, by omega, by omega, ?_⟩
            simpa using hw_eq0
          · exact ⟨k' + 1, by omega, by omega, by omega, rfl⟩
        · rintro ⟨k, hk, _, hkj, rfl⟩
          cases k with
          | zero => exact Or.inl (Or.inl rfl)
          | succ k' =>
            exact Or.inr ⟨k', by omega, Nat.zero_le k', by omega, rfl⟩
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        have hi'j' : i' ≤ j' := by omega
        have hj' : j' < W'.support.length := by
          simp only [GraphWalk.support_cons, List.length_cons] at hj
          omega
        obtain ⟨Q', hQ'_le, hQ'_path, hVQ'⟩ := ih hW' hi'j' hj'
        refine ⟨Q', hQ'_le.trans htail_le, hQ'_path, ?_⟩
        ext x
        rw [hVQ']
        simp only [GraphWalk.support_cons, List.length_cons, mem_ofPred_eq]
        constructor
        · rintro ⟨k', hk', hi'k', hk'j', rfl⟩
          exact ⟨k' + 1, by omega, by omega, by omega, rfl⟩
        · rintro ⟨k, hk, hik, hkj, rfl⟩
          cases k with
          | zero => omega
          | succ k' =>
            exact ⟨k', by omega, by omega, by omega, rfl⟩

namespace CyclicPerm

/-- For `x ∈ L`, the unique index `i < L.length` such that `L[i] = x`. -/
noncomputable def indexOfMem (L : List α) {x : α} (hx : x ∈ L) : ℕ :=
  Classical.choose (List.mem_iff_getElem.mp hx)

theorem indexOfMem_lt (L : List α) {x : α} (hx : x ∈ L) :
    indexOfMem L hx < L.length :=
  (Classical.choose_spec (List.mem_iff_getElem.mp hx)).1

theorem getElem_indexOfMem (L : List α) {x : α} (hx : x ∈ L) :
    L[indexOfMem L hx]'(indexOfMem_lt L hx) = x :=
  (Classical.choose_spec (List.mem_iff_getElem.mp hx)).2

theorem indexOfMem_getElem {L : List α} (hnd : L.Nodup) {i : ℕ} (hi : i < L.length) :
    indexOfMem L (List.getElem_mem hi) = i :=
  nodup_getElem_inj hnd (indexOfMem_lt L _) hi (getElem_indexOfMem L _)

/-- Underlying map of `ofNodupList`. -/
noncomputable def ofNodupListFun (L : List α) (hne : L ≠ []) (x : α) : α := by
  classical
  exact if hx : x ∈ L then
    L[(indexOfMem L hx + 1) % L.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hne))
  else x

theorem ofNodupListFun_of_mem (L : List α) (hne : L ≠ []) {x : α} (hx : x ∈ L) :
    ofNodupListFun L hne x =
      L[(indexOfMem L hx + 1) % L.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hne)) := by
  classical
  simp [ofNodupListFun, hx]

theorem ofNodupListFun_getElem (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i : ℕ} (hi : i < L.length) :
    ofNodupListFun L hne (L[i]'hi) =
      L[(i + 1) % L.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hne)) := by
  rw [ofNodupListFun_of_mem L hne (List.getElem_mem hi)]
  congr 1
  rw [indexOfMem_getElem hnd hi]

theorem ofNodupListFun_iterate_getElem (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    (m : ℕ) {i : ℕ} (hi : i < L.length) :
    ((ofNodupListFun L hne)^[m]) (L[i]'hi) =
      L[(i + m) % L.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hne)) := by
  induction m with
  | zero =>
    simp only [Function.iterate_zero_apply, Nat.add_zero]
    congr 1
    exact (Nat.mod_eq_of_lt hi).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih,
      ofNodupListFun_getElem L hnd hne (Nat.mod_lt _ (List.length_pos_of_ne_nil hne))]
    congr 1
    rw [Nat.mod_add_mod, Nat.add_assoc]

/-- The cyclic permutation defined by a non-empty duplicate-free list `L`. -/
noncomputable def ofNodupList (L : List α) (hnd : L.Nodup) (hne : L ≠ []) : CyclicPerm α where
  bar := {x | x ∈ L}
  toFun := ofNodupListFun L hne
  finite_bar := by
    classical
    exact L.toFinset.finite_toSet.subset fun x hx => List.mem_toFinset.mpr hx
  bijOn := by
    have hpos : 0 < L.length := List.length_pos_of_ne_nil hne
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
    · simp only [mem_ofPred_eq] at hx ⊢
      rw [ofNodupListFun_of_mem L hne hx]
      exact List.getElem_mem _
    · simp only [mem_ofPred_eq] at hx hy
      rw [← getElem_indexOfMem L hx, ← getElem_indexOfMem L hy] at hxy ⊢
      rw [ofNodupListFun_getElem L hnd hne (indexOfMem_lt L hx),
        ofNodupListFun_getElem L hnd hne (indexOfMem_lt L hy)] at hxy
      have hmod := nodup_getElem_inj hnd (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hxy
      have hi := indexOfMem_lt L hx
      have hj := indexOfMem_lt L hy
      have hij : indexOfMem L hx = indexOfMem L hy := by
        by_cases h1 : indexOfMem L hx + 1 = L.length <;>
          by_cases h2 : indexOfMem L hy + 1 = L.length
        · omega
        · have hm1 : (indexOfMem L hx + 1) % L.length = 0 := by rw [h1, Nat.mod_self]
          have hm2 : (indexOfMem L hy + 1) % L.length = indexOfMem L hy + 1 :=
            Nat.mod_eq_of_lt (by omega)
          omega
        · have hm1 : (indexOfMem L hx + 1) % L.length = indexOfMem L hx + 1 :=
            Nat.mod_eq_of_lt (by omega)
          have hm2 : (indexOfMem L hy + 1) % L.length = 0 := by rw [h2, Nat.mod_self]
          omega
        · have hm1 : (indexOfMem L hx + 1) % L.length = indexOfMem L hx + 1 :=
            Nat.mod_eq_of_lt (by omega)
          have hm2 : (indexOfMem L hy + 1) % L.length = indexOfMem L hy + 1 :=
            Nat.mod_eq_of_lt (by omega)
          omega
      congr 1
    · simp only [mem_ofPred_eq] at hy
      have hj : indexOfMem L hy < L.length := indexOfMem_lt L hy
      let i := (indexOfMem L hy + L.length - 1) % L.length
      have hi : i < L.length := Nat.mod_lt _ hpos
      refine ⟨L[i]'hi, List.getElem_mem hi, ?_⟩
      rw [ofNodupListFun_getElem L hnd hne hi, ← getElem_indexOfMem L hy]
      congr 1
      dsimp [i]
      rw [Nat.mod_add_mod]
      have hsum : indexOfMem L hy + L.length - 1 + 1 = indexOfMem L hy + L.length := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  single_orbit := by
    intro x hx y hy
    simp only [mem_ofPred_eq] at hx hy
    have hi : indexOfMem L hx < L.length := indexOfMem_lt L hx
    have hj : indexOfMem L hy < L.length := indexOfMem_lt L hy
    let k := indexOfMem L hy + L.length - indexOfMem L hx
    refine ⟨k, ?_⟩
    have hx_eq : L[indexOfMem L hx]'hi = x := getElem_indexOfMem L hx
    have hy_eq : L[indexOfMem L hy]'hj = y := getElem_indexOfMem L hy
    calc ((ofNodupListFun L hne)^[k]) x
      _ = ((ofNodupListFun L hne)^[k]) (L[indexOfMem L hx]'hi) := by rw [hx_eq]
      _ = L[(indexOfMem L hx + k) % L.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hne)) :=
        ofNodupListFun_iterate_getElem L hnd hne k hi
      _ = L[indexOfMem L hy]'hj := by
        congr 1
        have hsum : indexOfMem L hx + k = indexOfMem L hy + L.length := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      _ = y := hy_eq

@[simp]
theorem ofNodupList_bar (L : List α) (hnd : L.Nodup) (hne : L ≠ []) :
    (ofNodupList L hnd hne).bar = {x | x ∈ L} := rfl

theorem ofNodupList_toFun_getElem (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i : ℕ} (hi : i < L.length) :
    (ofNodupList L hnd hne).toFun (L[i]'hi) =
      L[(i + 1) % L.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hne)) :=
  ofNodupListFun_getElem L hnd hne hi

theorem ofNodupList_iterate_getElem (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    (m : ℕ) {i : ℕ} (hi : i < L.length) :
    ((ofNodupList L hnd hne).toFun^[m]) (L[i]'hi) =
      L[(i + m) % L.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hne)) :=
  ofNodupListFun_iterate_getElem L hnd hne m hi

/-- In `ofNodupList L hnd hne`, if `i < j < k < L.length`, then `L[j]` lies in the open interval
`interval (L[i]) (L[k])`. -/
theorem ofNodupList_mem_interval_of_lt (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < L.length) :
    (L[j]'(Nat.lt_trans hjk hk)) ∈
      (ofNodupList L hnd hne).interval (L[i]'(Nat.lt_trans (Nat.lt_trans hij hjk) hk)) (L[k]'hk)
        := by
  have hi : i < L.length := Nat.lt_trans (Nat.lt_trans hij hjk) hk
  have hj : j < L.length := Nat.lt_trans hjk hk
  have hpos : 0 < L.length := List.length_pos_of_ne_nil hne
  have hne_ik : L[i]'hi ≠ L[k]'hk := fun h => by have := nodup_getElem_inj hnd hi hk h; omega
  have hne_ji : L[j]'hj ≠ L[i]'hi := fun h => by have := nodup_getElem_inj hnd hj hi h; omega
  have hne_jk : L[j]'hj ≠ L[k]'hk := fun h => by have := nodup_getElem_inj hnd hj hk h; omega
  rw [(ofNodupList L hnd hne).mem_interval_iff_firstHitIn
    (List.getElem_mem hi) (List.getElem_mem hk) (List.getElem_mem hj) hne_ik hne_ji hne_jk]
  refine ⟨j - i, by omega, ?_, by simp, fun d hd1 hdj hd_in => ?_⟩
  · rw [ofNodupList_iterate_getElem L hnd hne (j - i) hi]
    congr 1
    have hsum : i + (j - i) = j := by omega
    rw [hsum, Nat.mod_eq_of_lt hj]
  · rw [ofNodupList_iterate_getElem L hnd hne d hi] at hd_in
    have hmod_eq : (i + d) % L.length = i + d := Nat.mod_eq_of_lt (by omega)
    simp only [mem_insert_iff, mem_singleton_iff] at hd_in
    rcases hd_in with h | h | h
    · have := nodup_getElem_inj hnd (Nat.mod_lt _ hpos) hi h; omega
    · have := nodup_getElem_inj hnd (Nat.mod_lt _ hpos) hj h; omega
    · have := nodup_getElem_inj hnd (Nat.mod_lt _ hpos) hk h; omega

/-- In `ofNodupList L hnd hne`, for `i < k < L.length` and `j < L.length` with `j < i ∨ k < j`,
`L[j]` lies in the open interval `interval (L[k]) (L[i])`. -/
theorem ofNodupList_mem_interval_swap_of_lt_or_gt (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i j k : ℕ} (hik : i < k) (hk : k < L.length) (hj : j < L.length)
    (hj_out : j < i ∨ k < j) :
    (L[j]'hj) ∈ (ofNodupList L hnd hne).interval (L[k]'hk) (L[i]'(Nat.lt_trans hik hk)) := by
  rcases hj_out with hji | hkj
  · have h_in := ofNodupList_mem_interval_of_lt L hnd hne hji hik hk
    exact (ofNodupList L hnd hne).mem_interval_rotate_right h_in
  · have h_in := ofNodupList_mem_interval_of_lt L hnd hne hik hkj hj
    exact (ofNodupList L hnd hne).mem_interval_rotate_left h_in

/-- Exact interval characterization in `ofNodupList L hnd hne` for `i < k < L.length`. -/
theorem ofNodupList_mem_interval_iff (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i j k : ℕ} (hik : i < k) (hk : k < L.length) (hj : j < L.length) :
    (L[j]'hj) ∈ (ofNodupList L hnd hne).interval (L[i]'(Nat.lt_trans hik hk)) (L[k]'hk) ↔
      i < j ∧ j < k := by
  have hi : i < L.length := Nat.lt_trans hik hk
  constructor
  · intro h_in
    have hne_ji : j ≠ i := fun h => by
      subst h
      exact (ofNodupList L hnd hne).not_mem_interval_left (L[j]'hj) (L[k]'hk) h_in
    have hne_jk : j ≠ k := fun h => by
      subst h
      exact (ofNodupList L hnd hne).not_mem_interval_right (L[i]'hi) (L[j]'hj) h_in
    by_contra hnot
    have hj_out : j < i ∨ k < j := by omega
    have h_swap := ofNodupList_mem_interval_swap_of_lt_or_gt L hnd hne hik hk hj hj_out
    exact disjoint_left.mp ((ofNodupList L hnd hne).disjoint_interval_swap (L[i]'hi) (L[k]'hk))
      h_in h_swap
  · rintro ⟨hij, hjk⟩
    exact ofNodupList_mem_interval_of_lt L hnd hne hij hjk hk

/-- Exact reverse-interval characterization in `ofNodupList L hnd hne` for `i < k < L.length`. -/
theorem ofNodupList_mem_interval_swap_iff (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i j k : ℕ} (hik : i < k) (hk : k < L.length) (hj : j < L.length) :
    (L[j]'hj) ∈ (ofNodupList L hnd hne).interval (L[k]'hk) (L[i]'(Nat.lt_trans hik hk)) ↔
      j < i ∨ k < j := by
  have hi : i < L.length := Nat.lt_trans hik hk
  constructor
  · intro h_in
    have hne_ji : j ≠ i := fun h => by
      subst h
      exact (ofNodupList L hnd hne).not_mem_interval_right (L[k]'hk) (L[j]'hj) h_in
    have hne_jk : j ≠ k := fun h => by
      subst h
      exact (ofNodupList L hnd hne).not_mem_interval_left (L[j]'hj) (L[i]'hi) h_in
    by_contra hnot
    have hj_mid : i < j ∧ j < k := by omega
    have h_mid := ofNodupList_mem_interval_of_lt L hnd hne hj_mid.1 hj_mid.2 hk
    exact disjoint_left.mp ((ofNodupList L hnd hne).disjoint_interval_swap (L[i]'hi) (L[k]'hk))
      h_mid h_in
  · intro hj_out
    exact ofNodupList_mem_interval_swap_of_lt_or_gt L hnd hne hik hk hj hj_out

/-- Crossing characterization in `ofNodupList L hnd hne` for ordered endpoint pairs `i₁ < j₁` and
`i₂ < j₂`. -/
theorem ofNodupList_crosses_iff (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i₁ j₁ i₂ j₂ : ℕ} (h1 : i₁ < j₁) (hj₁ : j₁ < L.length)
    (h2 : i₂ < j₂) (hj₂ : j₂ < L.length) :
    (ofNodupList L hnd hne).Crosses
      (L[i₁]'(Nat.lt_trans h1 hj₁)) (L[j₁]'hj₁)
      (L[i₂]'(Nat.lt_trans h2 hj₂)) (L[j₂]'hj₂) ↔
      (i₁ < i₂ ∧ i₂ < j₁ ∧ j₁ < j₂) ∨ (i₂ < i₁ ∧ i₁ < j₂ ∧ j₂ < j₁) := by
  have hi₂ : i₂ < L.length := Nat.lt_trans h2 hj₂
  rw [(ofNodupList L hnd hne).crosses_iff_interval,
    ofNodupList_mem_interval_iff L hnd hne h1 hj₁ hi₂,
    ofNodupList_mem_interval_swap_iff L hnd hne h1 hj₁ hj₂,
    ofNodupList_mem_interval_iff L hnd hne h1 hj₁ hj₂,
    ofNodupList_mem_interval_swap_iff L hnd hne h1 hj₁ hi₂]
  omega

/-- Any non-empty prefix `L₁` of `L = L₁ ++ L₂` is clockwise in `ofNodupList (L₁ ++ L₂) hnd hne`. -/
theorem ofNodupList_isClockwiseSeq_prefix {L₁ L₂ : List α}
    (hnd : (L₁ ++ L₂).Nodup) (hne₁ : L₁ ≠ []) :
    (ofNodupList (L₁ ++ L₂) hnd (List.append_ne_nil_of_left_ne_nil hne₁ L₂)).IsClockwiseSeq L₁ := by
  have hne : L₁ ++ L₂ ≠ [] := List.append_ne_nil_of_left_ne_nil hne₁ L₂
  have hpos₁ : 0 < L₁.length := List.length_pos_of_ne_nil hne₁
  have hpos : 0 < (L₁ ++ L₂).length := List.length_pos_of_ne_nil hne
  have hle : L₁.length ≤ (L₁ ++ L₂).length := by simp
  obtain ⟨hnd₁, _, _⟩ := List.nodup_append.mp hnd
  refine ⟨hnd₁, fun v hv => List.mem_append_left L₂ hv, fun i hi => ?_⟩
  have hiL : i < (L₁ ++ L₂).length := Nat.lt_of_lt_of_le hi hle
  have hget_i : L₁[i]'hi = (L₁ ++ L₂)[i]'hiL := (List.getElem_append_left hi).symm
  by_cases hi_last : i + 1 < L₁.length
  · have hi1L : i + 1 < (L₁ ++ L₂).length := Nat.lt_of_lt_of_le hi_last hle
    have hmod₁ : (i + 1) % L₁.length = i + 1 := Nat.mod_eq_of_lt hi_last
    refine ⟨1, le_rfl, ?_, List.getElem_mem _, fun j hj1 hjlt => by omega⟩
    rw [hget_i, Function.iterate_one, ofNodupList_toFun_getElem (L₁ ++ L₂) hnd hne hiL]
    trans (L₁ ++ L₂)[i + 1]'hi1L
    · congr 1
      exact Nat.mod_eq_of_lt hi1L
    · trans L₁[i + 1]'hi_last
      · exact List.getElem_append_left hi_last
      · congr 1
        exact hmod₁.symm
  · have hi_eq : i + 1 = L₁.length := by omega
    have hmod₁ : (i + 1) % L₁.length = 0 := by rw [hi_eq, Nat.mod_self]
    let m := (L₁ ++ L₂).length - i
    have hm1 : 1 ≤ m := by omega
    refine ⟨m, hm1, ?_, List.getElem_mem _, fun j hj1 hjlt hj_in => ?_⟩
    · rw [hget_i, ofNodupList_iterate_getElem (L₁ ++ L₂) hnd hne m hiL]
      have hsum : (i + m) % (L₁ ++ L₂).length = 0 := by
        have : i + m = (L₁ ++ L₂).length := by omega
        rw [this, Nat.mod_self]
      trans (L₁ ++ L₂)[0]'hpos
      · congr 1
      · trans L₁[0]'hpos₁
        · exact List.getElem_append_left hpos₁
        · congr 1
          exact hmod₁.symm
    · rw [hget_i, ofNodupList_iterate_getElem (L₁ ++ L₂) hnd hne j hiL] at hj_in
      simp only [mem_ofPred_eq] at hj_in
      obtain ⟨k, hk, hk_eq⟩ := List.mem_iff_getElem.mp hj_in
      have hkL : k < (L₁ ++ L₂).length := Nat.lt_of_lt_of_le hk hle
      have hk_eqL : (L₁ ++ L₂)[k]'hkL = (L₁ ++ L₂)[(i + j) % (L₁ ++ L₂).length]'(Nat.mod_lt _ hpos)
        := by
        trans L₁[k]'hk
        · exact List.getElem_append_left hk
        · exact hk_eq
      have hidx := nodup_getElem_inj hnd hkL (Nat.mod_lt _ hpos) hk_eqL
      have hmod_ij : (i + j) % (L₁ ++ L₂).length = i + j := Nat.mod_eq_of_lt (by omega)
      omega

/-! ## Listing `Ω.interval s t` and Splitting `Ω` Along a Path `P` -/

theorem exists_hitStep (Ω : CyclicPerm α) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) :
    ∃ k : ℕ, 1 ≤ k ∧ (Ω.toFun^[k]) s = t ∧ ∀ j : ℕ, 1 ≤ j → j < k → (Ω.toFun^[j]) s ≠ t := by
  have hne : (Ω.bar ∩ ({t} : Set α)).Nonempty := ⟨t, ht, mem_singleton t⟩
  obtain ⟨y, k, hk1, hky, hy_in, hmin⟩ := Ω.exists_firstHitIn hs hne
  rw [mem_singleton_iff] at hy_in
  subst hy_in
  exact ⟨k, hk1, hky, fun j hj1 hjk hj_eq => hmin j hj1 hjk (mem_singleton_iff.mpr hj_eq)⟩

/-- The positive step count `k ≥ 1` at which `Ω` first hits `t` starting from `s`. -/
noncomputable def hitStep (Ω : CyclicPerm α) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) : ℕ :=
  Classical.choose (exists_hitStep Ω hs ht)

theorem hitStep_ge_one (Ω : CyclicPerm α) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) :
    1 ≤ Ω.hitStep hs ht :=
  (Classical.choose_spec (exists_hitStep Ω hs ht)).1

theorem iterate_hitStep (Ω : CyclicPerm α) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) :
    (Ω.toFun^[Ω.hitStep hs ht]) s = t :=
  (Classical.choose_spec (exists_hitStep Ω hs ht)).2.1

theorem iterate_ne_of_lt_hitStep (Ω : CyclicPerm α) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j < Ω.hitStep hs ht) :
    (Ω.toFun^[j]) s ≠ t :=
  (Classical.choose_spec (exists_hitStep Ω hs ht)).2.2 j hj1 hjk

theorem iterate_ne_self_of_lt_hitStep (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t)
    {d : ℕ} (hd1 : 1 ≤ d) (hdk : d < Ω.hitStep hs ht) :
    (Ω.toFun^[d]) s ≠ s := by
  intro heq
  have hmul : ∀ q : ℕ, (Ω.toFun^[d * q]) s = s := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, heq]
  have hrem : (Ω.toFun^[(Ω.hitStep hs ht) % d]) s = t := by
    trans (Ω.toFun^[Ω.hitStep hs ht]) s
    · conv_rhs => rw [← Nat.div_add_mod (Ω.hitStep hs ht) d, add_comm]
      rw [Function.iterate_add_apply, hmul]
    · exact Ω.iterate_hitStep hs ht
  have hmod_lt : (Ω.hitStep hs ht) % d < d := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos ((Ω.hitStep hs ht) % d) with h0 | hpos
  · rw [h0, Function.iterate_zero_apply] at hrem
    exact hst hrem
  · exact Ω.iterate_ne_of_lt_hitStep hs ht hpos (by omega) hrem

theorem iterate_inj_le_hitStep (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t)
    {i j : ℕ} (hi : i ≤ Ω.hitStep hs ht) (hj : j ≤ Ω.hitStep hs ht)
    (heq : (Ω.toFun^[i]) s = (Ω.toFun^[j]) s) : i = j := by
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exfalso
    have hiter : (Ω.toFun^[i]) ((Ω.toFun^[j - i]) s) = (Ω.toFun^[i]) s := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hlt), heq]
    have hsub_eq : (Ω.toFun^[j - i]) s = s :=
      Ω.injOn_iterate i (Ω.iterate_mem (j - i) hs) hs hiter
    by_cases hji_eq : j - i = Ω.hitStep hs ht
    · rw [hji_eq, Ω.iterate_hitStep hs ht] at hsub_eq
      exact hst hsub_eq.symm
    · exact Ω.iterate_ne_self_of_lt_hitStep hs ht hst (by omega) (by omega) hsub_eq
  · rfl
  · exfalso
    have hiter : (Ω.toFun^[j]) ((Ω.toFun^[i - j]) s) = (Ω.toFun^[j]) s := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hgt), ← heq]
    have hsub_eq : (Ω.toFun^[i - j]) s = s :=
      Ω.injOn_iterate j (Ω.iterate_mem (i - j) hs) hs hiter
    by_cases hij_eq : i - j = Ω.hitStep hs ht
    · rw [hij_eq, Ω.iterate_hitStep hs ht] at hsub_eq
      exact hst hsub_eq.symm
    · exact Ω.iterate_ne_self_of_lt_hitStep hs ht hst (by omega) (by omega) hsub_eq

/-- For `0 ≤ j₁ < j₂ < j₃ ≤ hitStep Ω hs ht`, `(Ω.toFun^[j₂]) s` lies in the open interval
`Ω.interval ((Ω.toFun^[j₁]) s) ((Ω.toFun^[j₃]) s)`. -/
theorem iterate_mem_interval_of_lt_hitStep (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t)
    {j₁ j₂ j₃ : ℕ} (h12 : j₁ < j₂) (h23 : j₂ < j₃) (h3 : j₃ ≤ Ω.hitStep hs ht) :
    ((Ω.toFun^[j₂]) s) ∈ Ω.interval ((Ω.toFun^[j₁]) s) ((Ω.toFun^[j₃]) s) := by
  have h1 : j₁ ≤ Ω.hitStep hs ht := by omega
  have h2 : j₂ ≤ Ω.hitStep hs ht := by omega
  have hne13 : (Ω.toFun^[j₁]) s ≠ (Ω.toFun^[j₃]) s := fun h => by
    have := Ω.iterate_inj_le_hitStep hs ht hst h1 h3 h; omega
  have hne21 : (Ω.toFun^[j₂]) s ≠ (Ω.toFun^[j₁]) s := fun h => by
    have := Ω.iterate_inj_le_hitStep hs ht hst h2 h1 h; omega
  have hne23 : (Ω.toFun^[j₂]) s ≠ (Ω.toFun^[j₃]) s := fun h => by
    have := Ω.iterate_inj_le_hitStep hs ht hst h2 h3 h; omega
  rw [Ω.mem_interval_iff_firstHitIn
    (Ω.iterate_mem j₁ hs) (Ω.iterate_mem j₃ hs) (Ω.iterate_mem j₂ hs) hne13 hne21 hne23]
  refine ⟨j₂ - j₁, by omega, ?_, by simp, fun d hd1 hdj hd_in => ?_⟩
  · rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
  · rw [← Function.iterate_add_apply] at hd_in
    have hdj_le : d + j₁ ≤ Ω.hitStep hs ht := by omega
    simp only [mem_insert_iff, mem_singleton_iff] at hd_in
    rcases hd_in with h | h | h
    · have := Ω.iterate_inj_le_hitStep hs ht hst hdj_le h1 h; omega
    · have := Ω.iterate_inj_le_hitStep hs ht hst hdj_le h2 h; omega
    · have := Ω.iterate_inj_le_hitStep hs ht hst hdj_le h3 h; omega

/-- The list of elements of `Ω.interval s t` in clockwise order from `s` to `t`. -/
noncomputable def intervalList (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) : List α :=
  (List.range (Ω.hitStep hs ht - 1)).map (fun i => (Ω.toFun^[i + 1]) s)

@[simp]
theorem length_intervalList (Ω : CyclicPerm α) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) :
    (Ω.intervalList hs ht).length = Ω.hitStep hs ht - 1 := by
  simp [intervalList]

theorem getElem_intervalList (Ω : CyclicPerm α) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar)
    {i : ℕ} (hi : i < (Ω.intervalList hs ht).length) :
    (Ω.intervalList hs ht)[i]'hi = (Ω.toFun^[i + 1]) s := by
  simp [intervalList]

theorem nodup_intervalList (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t) :
    (Ω.intervalList hs ht).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  rw [getElem_intervalList, getElem_intervalList] at heq
  rw [length_intervalList] at hi hj
  have := Ω.iterate_inj_le_hitStep hs ht hst (by omega) (by omega) heq
  omega

theorem mem_intervalList_iff (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t) (x : α) :
    x ∈ Ω.intervalList hs ht ↔ x ∈ Ω.interval s t := by
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [getElem_intervalList]
    rw [length_intervalList] at hi
    have hmem := Ω.iterate_mem_interval_of_lt_hitStep hs ht hst
      (Nat.zero_lt_succ i) (by omega) (le_rfl)
    simpa [Ω.iterate_hitStep hs ht] using hmem
  · intro hx
    have hx_bar : x ∈ Ω.bar := hx.1.1
    have hxs : x ≠ s := fun h => hx.1.2 (by simp [h])
    have hxt : x ≠ t := fun h => hx.1.2 (by simp [h])
    have hhit : Ω.FirstHitIn {s, x, t} s x :=
      (Ω.mem_interval_iff_firstHitIn hs ht hx_bar hst hxs hxt).mp hx
    rcases hhit with ⟨j, hj1, rfl, _, hmin⟩
    have hjk : j < Ω.hitStep hs ht := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
      · rw [← heq, Ω.iterate_hitStep hs ht] at hxt
        exact hxt rfl
      · exact hmin (Ω.hitStep hs ht) (Ω.hitStep_ge_one hs ht) hgt
          (by simp [Ω.iterate_hitStep hs ht])
    rw [List.mem_iff_getElem]
    refine ⟨j - 1, ?_, ?_⟩
    · rw [length_intervalList]; omega
    · rw [getElem_intervalList, Nat.sub_add_cancel hj1]

/-- For `a < b < (Ω.intervalList hs ht).length`, `{t, L_W[a]}` crosses `{s, L_W[b]}` in `Ω`. -/
theorem crosses_t_s_intervalList_of_lt (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t)
    {a b : ℕ} (hab : a < b) (hb : b < (Ω.intervalList hs ht).length) :
    Ω.Crosses t ((Ω.intervalList hs ht)[a]'(Nat.lt_trans hab hb))
      s ((Ω.intervalList hs ht)[b]'hb) := by
  have ha : a < (Ω.intervalList hs ht).length := Nat.lt_trans hab hb
  rw [getElem_intervalList, getElem_intervalList]
  rw [length_intervalList] at ha hb
  have ha_in_sb : (Ω.toFun^[a + 1]) s ∈ Ω.interval s ((Ω.toFun^[b + 1]) s) :=
    Ω.iterate_mem_interval_of_lt_hitStep hs ht hst (j₁ := 0) (j₂ := a + 1) (j₃ := b + 1)
      (Nat.zero_lt_succ a) (by omega) (by omega)
  have hb_in_st : (Ω.toFun^[b + 1]) s ∈ Ω.interval s t := by
    have h := Ω.iterate_mem_interval_of_lt_hitStep hs ht hst
      (j₁ := 0) (j₂ := b + 1) (j₃ := Ω.hitStep hs ht) (Nat.zero_lt_succ b) (by omega) (le_rfl)
    rwa [Function.iterate_zero_apply, Ω.iterate_hitStep hs ht] at h
  exact (Ω.crosses_iff_interval.mpr (Or.inr ⟨ha_in_sb, Ω.mem_interval_rotate_left hb_in_st⟩)).symm

/-- For `a < b < c < (Ω.intervalList hs ht).length`, `{t, L_W[b]}` crosses `{L_W[a], L_W[c]}` in
`Ω`. -/
theorem crosses_t_intervalList_of_lt (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t)
    {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : c < (Ω.intervalList hs ht).length) :
    Ω.Crosses t ((Ω.intervalList hs ht)[b]'(Nat.lt_trans hbc hc))
      ((Ω.intervalList hs ht)[a]'(Nat.lt_trans (Nat.lt_trans hab hbc) hc))
      ((Ω.intervalList hs ht)[c]'hc) := by
  have ha : a < (Ω.intervalList hs ht).length := Nat.lt_trans (Nat.lt_trans hab hbc) hc
  have hb : b < (Ω.intervalList hs ht).length := Nat.lt_trans hbc hc
  rw [getElem_intervalList, getElem_intervalList, getElem_intervalList]
  rw [length_intervalList] at ha hb hc
  have hb_in_ac : (Ω.toFun^[b + 1]) s ∈ Ω.interval ((Ω.toFun^[a + 1]) s) ((Ω.toFun^[c + 1]) s) :=
    Ω.iterate_mem_interval_of_lt_hitStep hs ht hst (j₁ := a + 1) (j₂ := b + 1) (j₃ := c + 1)
      (by omega) (by omega) (by omega)
  have hc_in_at : (Ω.toFun^[c + 1]) s ∈ Ω.interval ((Ω.toFun^[a + 1]) s) t := by
    have h := Ω.iterate_mem_interval_of_lt_hitStep hs ht hst
      (j₁ := a + 1) (j₂ := c + 1) (j₃ := Ω.hitStep hs ht) (by omega) (by omega) (le_rfl)
    rwa [Ω.iterate_hitStep hs ht] at h
  exact (Ω.crosses_iff_interval.mpr (Or.inr ⟨hb_in_ac, Ω.mem_interval_rotate_left hc_in_at⟩)).symm

/-- For `a < b < c < d < (Ω.intervalList hs ht).length`, `{L_W[a], L_W[c]}` crosses
`{L_W[b], L_W[d]}` in `Ω`. -/
theorem crosses_intervalList_of_lt (Ω : CyclicPerm α) {s t : α}
    (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t)
    {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hd : d < (Ω.intervalList hs ht).length) :
    Ω.Crosses
      ((Ω.intervalList hs ht)[a]'(by omega))
      ((Ω.intervalList hs ht)[c]'(by omega))
      ((Ω.intervalList hs ht)[b]'(by omega))
      ((Ω.intervalList hs ht)[d]'hd) := by
  have hd' : d < Ω.hitStep hs ht - 1 := by rwa [length_intervalList] at hd
  rw [getElem_intervalList, getElem_intervalList, getElem_intervalList, getElem_intervalList]
  have hb_in_ac : (Ω.toFun^[b + 1]) s ∈ Ω.interval ((Ω.toFun^[a + 1]) s) ((Ω.toFun^[c + 1]) s) :=
    Ω.iterate_mem_interval_of_lt_hitStep hs ht hst (by omega) (by omega) (by omega)
  have hc_in_ad : (Ω.toFun^[c + 1]) s ∈ Ω.interval ((Ω.toFun^[a + 1]) s) ((Ω.toFun^[d + 1]) s) :=
    Ω.iterate_mem_interval_of_lt_hitStep hs ht hst (by omega) (by omega) (by omega)
  have hd_in_ca : (Ω.toFun^[d + 1]) s ∈ Ω.interval ((Ω.toFun^[c + 1]) s) ((Ω.toFun^[a + 1]) s) :=
    Ω.mem_interval_rotate_left hc_in_ad
  exact Ω.crosses_iff_interval.mpr (Or.inl ⟨hb_in_ac, hd_in_ca⟩)

end CyclicPerm

/-! ## Splitting `G \ V(P)` into `H₁` and `H₂` Along an Induced Path `P` -/

/-- For a subgraph `P` of `G` and a vertex set `W`, `splitSide G P W` is the union of those
components of `G \ V(P)` of which some vertex belongs to `W`
(Graph Minors IX, (2.4), page 45: "For $i = 1, 2$, let $H_i$ be the union of those components of
$G \setminus V(P)$ of which some vertex is in $W_i$"). -/
def splitSide (G P : Graph α β) (W : Set α) : Graph α β :=
  (deleteVertices G V(P)).induce
    {v ∈ V(deleteVertices G V(P)) | (W ∩ V(reachableComponent (deleteVertices G V(P)) v)).Nonempty}

@[simp]
theorem vertexSet_splitSide (G P : Graph α β) (W : Set α) :
    V(splitSide G P W) =
      {v ∈ V(deleteVertices G V(P)) | (W ∩ V(reachableComponent (deleteVertices G V(P))
        v)).Nonempty} :=
  rfl

theorem splitSide_le_deleteVertices (G P : Graph α β) (W : Set α) :
    splitSide G P W ≤ deleteVertices G V(P) :=
  (deleteVertices G V(P)).induce_le fun _ hv => hv.1

theorem splitSide_le (G P : Graph α β) (W : Set α) :
    splitSide G P W ≤ G :=
  (splitSide_le_deleteVertices G P W).trans (deleteVertices_le G V(P))

theorem disjoint_vertexSet_splitSide_P (G P : Graph α β) (W : Set α) :
    Disjoint V(splitSide G P W) V(P) := by
  rw [disjoint_left]
  intro v hv hvP
  exact hv.1.2 hvP

theorem mem_vertexSet_splitSide_of_mem_W {G P : Graph α β} {W : Set α} {w : α}
    (hwG : w ∈ V(G)) (hwP : w ∉ V(P)) (hwW : w ∈ W) :
    w ∈ V(splitSide G P W) := by
  have hw_del : w ∈ V(deleteVertices G V(P)) := ⟨hwG, hwP⟩
  exact ⟨hw_del, ⟨w, hwW, self_mem_reachableComponent hw_del⟩⟩

theorem isClosedSubgraph_splitSide_deleteVertices (G P : Graph α β) (W : Set α) :
    splitSide G P W ≤c deleteVertices G V(P) := by
  refine IsClosedSubgraph.mk' (splitSide_le_deleteVertices G P W) fun e x hinc hx => ?_
  obtain ⟨y, hxy⟩ := hinc
  have hx_del : x ∈ V(deleteVertices G V(P)) := hx.1
  have hy_del : y ∈ V(deleteVertices G V(P)) := hxy.right_mem
  have hcomp_eq : reachableComponent (deleteVertices G V(P)) x =
      reachableComponent (deleteVertices G V(P)) y := by
    refine isGraphComponent_eq_of_mem_inter
      (isGraphComponent_reachableComponent hx_del)
      (isGraphComponent_reachableComponent hy_del)
      ⟨y, ?_, self_mem_reachableComponent hy_del⟩
    exact (mem_graphComponent_iff_of_isLink
      (isGraphComponent_reachableComponent hx_del) hxy).mp (self_mem_reachableComponent hx_del)
  have hy_in : y ∈ V(splitSide G P W) := ⟨hy_del, hcomp_eq ▸ hx.2⟩
  exact ⟨x, y, hxy, hx, hy_in⟩

theorem mem_splitSide_iff_of_deleteVertices_isLink {G P : Graph α β} {W : Set α}
    {e : β} {x y : α} (hxy : (deleteVertices G V(P)).IsLink e x y) :
    x ∈ V(splitSide G P W) ↔ y ∈ V(splitSide G P W) :=
  (isClosedSubgraph_splitSide_deleteVertices G P W).mem_iff_of_isLink hxy

/-- Every vertex `v ∈ V(splitSide G P W)` has a walk in `splitSide G P W` to some vertex `w ∈ W`. -/
theorem exists_walk_in_splitSide_to_W {G P : Graph α β} {W : Set α} {v : α}
    (hv : v ∈ V(splitSide G P W)) :
    ∃ w ∈ W ∩ V(splitSide G P W), Nonempty (GraphWalk (splitSide G P W) v w) := by
  rcases hv with ⟨hv_del, w, hwW, hw_reach⟩
  have hcomp_v := isGraphComponent_reachableComponent hv_del
  have hle_split : reachableComponent (deleteVertices G V(P)) v ≤ splitSide G P W := by
    have hsubV : V(reachableComponent (deleteVertices G V(P)) v) ⊆ V(splitSide G P W) := by
      intro u hu
      have hu_del : u ∈ V(deleteVertices G V(P)) := (reachableComponent_le _ _).vertexSet_mono hu
      have hcomp_eq : reachableComponent (deleteVertices G V(P)) u =
          reachableComponent (deleteVertices G V(P)) v :=
        isGraphComponent_eq_of_mem_inter (isGraphComponent_reachableComponent hu_del) hcomp_v
          ⟨u, self_mem_reachableComponent hu_del, hu⟩
      exact ⟨hu_del, hcomp_eq.symm ▸ ⟨w, hwW, hw_reach⟩⟩
    rw [(Compatible.of_le_le (reachableComponent_le _ _) (splitSide_le_deleteVertices G P
      W)).le_iff]
    refine ⟨hsubV, fun e he => ?_⟩
    obtain ⟨x, y, hxy⟩ := (reachableComponent (deleteVertices G V(P))
      v).exists_isLink_of_mem_edgeSet he
    exact ⟨x, y, hxy.mono (reachableComponent_le _ _), hsubV hxy.left_mem, hsubV hxy.right_mem⟩
  obtain ⟨W_vw⟩ := hcomp_v.2.1.2 v (self_mem_reachableComponent hv_del) w hw_reach
  obtain ⟨W_vw', _, _⟩ := exists_walk_up_of_le hle_split W_vw
  exact ⟨w, ⟨hwW, hle_split.vertexSet_mono hw_reach⟩, ⟨W_vw'⟩⟩

/-- **Graph Minors IX, (2.4)** (page 45):
"Put $W_1 = \Omega(s, t)$ and $W_2 = \Omega(t, s)$. For $i = 1, 2$, let $H_i$ be the union of those
components of $G \setminus V(P)$ of which some vertex is in $W_i$. Then
$H_1 \cup H_2 = G \setminus V(P)$ since $Z$ catches $G \setminus V(P)$." -/
theorem lemma_2_4_H1_union_H2 (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P))) :
    subgraphUnion (deleteVertices S.G V(P))
      (splitSide S.G P (S.Ω.interval s t))
      (splitSide S.G P (S.Ω.interval t s)) = deleteVertices S.G V(P) := by
  let K := deleteVertices S.G V(P)
  let H₁ := splitSide S.G P (S.Ω.interval s t)
  let H₂ := splitSide S.G P (S.Ω.interval t s)
  have h₁ : H₁ ≤ K := splitSide_le_deleteVertices S.G P (S.Ω.interval s t)
  have h₂ : H₂ ≤ K := splitSide_le_deleteVertices S.G P (S.Ω.interval t s)
  have hV_eq : V(H₁) ∪ V(H₂) = V(K) := by
    refine Subset.antisymm (union_subset h₁.vertexSet_mono h₂.vertexSet_mono) fun v hv => ?_
    obtain ⟨z, hzZ, hzv⟩ := hcatch.2 (reachableComponent K v) (isGraphComponent_reachableComponent
      hv)
    rw [ ← S.Ω.interval_union_interval_swap hs ht hst] at hzZ
    rcases hzZ with hz1 | hz2
    · exact Or.inl ⟨hv, ⟨z, hz1, hzv⟩⟩
    · exact Or.inr ⟨hv, ⟨z, hz2, hzv⟩⟩
  refine (Compatible.of_le_le (subgraphUnion_le h₁ h₂) le_rfl).ext ?_ ?_
  · rw [vertexSet_subgraphUnion, hV_eq]
  · rw [edgeSet_subgraphUnion h₁ h₂]
    refine Subset.antisymm (union_subset h₁.edgeSet_mono h₂.edgeSet_mono) fun e he => ?_
    obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet he
    have hx_in : x ∈ V(H₁) ∪ V(H₂) := hV_eq.symm ▸ hxy.left_mem
    rcases hx_in with hx₁ | hx₂
    · have hy₁ : y ∈ V(H₁) := (mem_splitSide_iff_of_deleteVertices_isLink hxy).mp hx₁
      exact Or.inl ⟨x, y, hxy, hx₁, hy₁⟩
    · have hy₂ : y ∈ V(H₂) := (mem_splitSide_iff_of_deleteVertices_isLink hxy).mp hx₂
      exact Or.inr ⟨x, y, hxy, hx₂, hy₂⟩

/-- **Graph Minors IX, (2.4)** (page 45):
"Moreover, $H_1 \cap H_2$ is null, since $(G, \Omega)$ has no cross." -/
theorem lemma_2_4_H1_disjoint_H2 (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂) :
    Disjoint V(splitSide S.G P (S.Ω.interval s t)) V(splitSide S.G P (S.Ω.interval t s)) ∧
      Disjoint E(splitSide S.G P (S.Ω.interval s t)) E(splitSide S.G P (S.Ω.interval t s)) := by
  have hdisjV :
      Disjoint V(splitSide S.G P (S.Ω.interval s t)) V(splitSide S.G P (S.Ω.interval t s)) := by
    rw [disjoint_left]
    intro v hv₁ hv₂
    rcases hv₁ with ⟨hv_del, w₁, hw₁_int, hw₁_reach⟩
    rcases hv₂ with ⟨_, w₂, hw₂_int, hw₂_reach⟩
    have hcomp := isGraphComponent_reachableComponent hv_del
    obtain ⟨W_12⟩ := hcomp.2.1.2 w₁ hw₁_reach w₂ hw₂_reach
    obtain ⟨W_K, hs_K, _⟩ := exists_walk_up_of_le (reachableComponent_le _ _) W_12
    obtain ⟨W_G, hs_G, _⟩ := exists_walk_up_of_le (deleteVertices_le S.G V(P)) W_K
    obtain ⟨Q, hQ, hVQ, _⟩ := exists_isGraphPathWithEnds_of_walk W_G
    have hdisj_PQ : Disjoint V(P) V(Q) := by
      rw [disjoint_right]
      intro u huQ huP
      have hu_supp : u ∈ W_12.support := by
        have := hVQ huQ
        rwa [mem_ofPred_eq, hs_G, hs_K] at this
      have hu_del : u ∈ V(deleteVertices S.G V(P)) :=
        (reachableComponent_le _ _).vertexSet_mono (W_12.mem_vertexSet_of_mem_support hu_supp)
      exact hu_del.2 huP
    have hcross_ends : S.Ω.Crosses s t w₁ w₂ :=
      S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hw₁_int, hw₂_int⟩)
    have hw₁_ne_w₂ : w₁ ≠ w₂ := hcross_ends.ne_ends.2
    exact hnocross ⟨P, Q, hdisj_PQ, s, t, w₁, w₂,
      ⟨hP, hst, hs, ht⟩, ⟨hQ, hw₁_ne_w₂, hw₁_int.1.1, hw₂_int.1.1⟩, hcross_ends⟩
  refine ⟨hdisjV, disjoint_left.mpr fun e he₁ he₂ => ?_⟩
  obtain ⟨x, _, hxy₁⟩ := (splitSide S.G P (S.Ω.interval s t)).exists_isLink_of_mem_edgeSet he₁
  have hxy₂ := ((splitSide_le S.G P (S.Ω.interval t s)).isLink_iff he₂).mpr
    (hxy₁.mono (splitSide_le S.G P (S.Ω.interval s t)))
  exact disjoint_left.mp hdisjV hxy₁.left_mem hxy₂.left_mem

/-- No edge of `S.G` has one endpoint in `V(H₁)` and the other in `V(H₂)` when `(G, Ω)` has no
cross. -/
theorem no_link_between_splitSides (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    {e : β} {x y : α} (hxy : S.G.IsLink e x y)
    (hx : x ∈ V(splitSide S.G P (S.Ω.interval s t)))
    (hy : y ∈ V(splitSide S.G P (S.Ω.interval t s))) : False := by
  have hxy_del : (deleteVertices S.G V(P)).IsLink e x y :=
    (deleteVertices_isLink S.G V(P)).mpr ⟨hxy, hx.1.2, hy.1.2⟩
  have hy₁ : y ∈ V(splitSide S.G P (S.Ω.interval s t)) :=
    (mem_splitSide_iff_of_deleteVertices_isLink hxy_del).mp hx
  exact disjoint_left.mp (lemma_2_4_H1_disjoint_H2 S hs ht hst hP hnocross).1 hy₁ hy

/-! ## Construction of `(G₁, Ω₁)` and Basic Structural Properties -/

/-- Canonical simple walk of `P` from `t` to `s` for a path `P` in `G` with ends `s, t`. -/
noncomputable def pathWalkTS {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) : GraphWalk P t s :=
  Classical.choose hP.symm.2

theorem isSimple_pathWalkTS {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) : (pathWalkTS hP).IsSimple :=
  (Classical.choose_spec hP.symm.2).1

theorem vertexSet_eq_support_pathWalkTS {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) :
    V(P) = {x | x ∈ (pathWalkTS hP).support} :=
  (Classical.choose_spec hP.symm.2).2.1

theorem edgeSet_eq_edges_pathWalkTS {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) :
    E(P) = {e | e ∈ (pathWalkTS hP).edges} :=
  (Classical.choose_spec hP.symm.2).2.2

theorem walkSubgraph_pathWalkTS {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) :
    walkSubgraph (pathWalkTS hP) = P := by
  refine (Compatible.of_le_le (walkSubgraph_le (pathWalkTS hP)) le_rfl).ext ?_ ?_
  · rw [vertexSet_walkSubgraph, vertexSet_eq_support_pathWalkTS]
  · rw [edgeSet_walkSubgraph, edgeSet_eq_edges_pathWalkTS]

theorem support_getElem_last {G : Graph α β} {u v : α} (W : GraphWalk G u v) :
    W.support[W.support.length - 1]'(by cases W <;> simp) = v := by
  induction W with
  | nil _ => rfl
  | @cons u w v e hlink W' ih =>
    have hpos : 0 < W'.support.length := by cases W' <;> simp
    have hidx : (u :: W'.support).length - 1 = (W'.support.length - 1) + 1 := by
      simp only [List.length_cons]
      omega
    trans (u :: W'.support)[(W'.support.length - 1) + 1]'(by simp; omega)
    · congr 1
    · simpa using ih

/-- The concatenated clockwise list `(pathWalkTS hP).support ++ S.Ω.intervalList hs ht`
defining `Ω₁`. -/
noncomputable def splitList (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t) : List α :=
  (pathWalkTS hP).support ++ S.Ω.intervalList hs ht

theorem splitList_ne_nil (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t) :
    splitList S hs ht hP ≠ [] := by
  apply List.append_ne_nil_of_left_ne_nil
  cases pathWalkTS hP <;> simp

theorem nodup_splitList (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar) :
    (splitList S hs ht hP).Nodup := by
  rw [splitList, List.nodup_append]
  refine ⟨isSimple_pathWalkTS hP, S.Ω.nodup_intervalList hs ht hst, fun x hx y hy hxy => ?_⟩
  subst hxy
  have hxP : x ∈ V(P) := by rw [vertexSet_eq_support_pathWalkTS hP]; exact hx
  have hxW : x ∈ S.Ω.interval s t := (S.Ω.mem_intervalList_iff hs ht hst x).mp hy
  exact disjoint_left.mp hP_bar ⟨hxP, hxW.1.2⟩ hxW.1.1

/-- The cyclic permutation `Ω₁` on `W₁ ∪ V(P)` from `(2.4)` (page 45). -/
noncomputable def splitCyclicPerm (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar) : CyclicPerm α :=
  CyclicPerm.ofNodupList (splitList S hs ht hP)
    (nodup_splitList S hs ht hst hP hP_bar) (splitList_ne_nil S hs ht hP)

@[simp]
theorem splitCyclicPerm_bar (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar) :
    (splitCyclicPerm S hs ht hst hP hP_bar).bar = S.Ω.interval s t ∪ V(P) := by
  ext x
  simp only [splitCyclicPerm, CyclicPerm.ofNodupList_bar, splitList, List.mem_append,
    S.Ω.mem_intervalList_iff hs ht hst, vertexSet_eq_support_pathWalkTS hP, mem_union,
    mem_ofPred_eq, or_comm]

theorem splitCyclicPerm_isClockwiseSeq_pathWalkTS (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar) :
    (splitCyclicPerm S hs ht hst hP hP_bar).IsClockwiseSeq (pathWalkTS hP).support :=
  CyclicPerm.ofNodupList_isClockwiseSeq_prefix
    (nodup_splitList S hs ht hst hP hP_bar)
    (by cases pathWalkTS hP <;> simp)

/-- The graph `G₁ = (G \ E(P)) \ V(H₂)` from `(2.4)` (page 45). -/
def splitGraph (S : Society α β) (P : Graph α β) (s t : α) : Graph α β :=
  deleteVertices (S.G.restrict (E(S.G) \ E(P))) V(splitSide S.G P (S.Ω.interval t s))

theorem splitGraph_le (S : Society α β) (P : Graph α β) (s t : α) :
    splitGraph S P s t ≤ S.G :=
  (deleteVertices_le _ _).trans restrict_le

@[simp]
theorem vertexSet_splitGraph (S : Society α β) (P : Graph α β) (s t : α) :
    V(splitGraph S P s t) = V(S.G) \ V(splitSide S.G P (S.Ω.interval t s)) :=
  rfl

theorem splitGraph_isLink_iff (S : Society α β) (P : Graph α β) (s t : α) {e : β} {x y : α} :
    (splitGraph S P s t).IsLink e x y ↔
      S.G.IsLink e x y ∧ e ∉ E(P) ∧
      x ∉ V(splitSide S.G P (S.Ω.interval t s)) ∧
      y ∉ V(splitSide S.G P (S.Ω.interval t s)) := by
  unfold splitGraph
  rw [deleteVertices_isLink, restrict_isLink, mem_sdiff]
  refine ⟨fun ⟨⟨⟨_, heP⟩, hxy⟩, hx, hy⟩ => ⟨hxy, heP, hx, hy⟩,
    fun ⟨hxy, heP, hx, hy⟩ => ⟨⟨⟨hxy.edge_mem, heP⟩, hxy⟩, hx, hy⟩⟩

theorem edgeSet_splitGraph_subset (S : Society α β) (P : Graph α β) (s t : α) :
    E(splitGraph S P s t) ⊆ E(S.G) \ E(P) := by
  intro e he
  obtain ⟨x, y, hxy⟩ := (splitGraph S P s t).exists_isLink_of_mem_edgeSet he
  rw [splitGraph_isLink_iff] at hxy
  exact ⟨hxy.1.edge_mem, hxy.2.1⟩

/-- The society `(G₁, Ω₁)` from `(2.4)` (page 45). -/
noncomputable def splitSociety (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂) : Society α β where
  G := splitGraph S P s t
  Ω := splitCyclicPerm S hs ht hst hP hP_bar
  bar_subset := by
    rw [splitCyclicPerm_bar, vertexSet_splitGraph]
    rintro x (hxW₁ | hxP)
    · refine ⟨S.bar_subset hxW₁.1.1, fun hxH₂ => ?_⟩
      have hxH₁ : x ∈ V(splitSide S.G P (S.Ω.interval s t)) :=
        mem_vertexSet_splitSide_of_mem_W (S.bar_subset hxW₁.1.1)
          (fun hxP => disjoint_left.mp hP_bar ⟨hxP, hxW₁.1.2⟩ hxW₁.1.1) hxW₁
      exact disjoint_left.mp (lemma_2_4_H1_disjoint_H2 S hs ht hst hP hnocross).1 hxH₁ hxH₂
    · exact ⟨hP.1.vertexSet_mono hxP, fun hxH₂ => hxH₂.1.2 hxP⟩
  finite_V := S.finite_V.subset (splitGraph_le S P s t).vertexSet_mono
  finite_E := S.finite_E.subset (splitGraph_le S P s t).edgeSet_mono

theorem vertexSet_splitGraph_eq_union (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂) :
    V(splitGraph S P s t) = V(P) ∪ V(splitSide S.G P (S.Ω.interval s t)) := by
  have hunion := congrArg Graph.vertexSet (lemma_2_4_H1_union_H2 S hs ht hst hcatch)
  change V(splitSide S.G P (S.Ω.interval s t)) ∪ V(splitSide S.G P (S.Ω.interval t s)) =
    V(S.G) \ V(P) at hunion
  have hdisj := (lemma_2_4_H1_disjoint_H2 S hs ht hst hP hnocross).1
  ext x
  simp only [vertexSet_splitGraph, mem_sdiff, mem_union]
  constructor
  · rintro ⟨hxG, hx_not_H₂⟩
    by_cases hxP : x ∈ V(P)
    · exact Or.inl hxP
    · have hx_in : x ∈ V(splitSide S.G P (S.Ω.interval s t)) ∪
          V(splitSide S.G P (S.Ω.interval t s)) := by
        rw [hunion]
        exact ⟨hxG, hxP⟩
      exact Or.inr (hx_in.resolve_right hx_not_H₂)
  · rintro (hxP | hxH₁)
    · exact ⟨hP.1.vertexSet_mono hxP, fun hxH₂ => hxH₂.1.2 hxP⟩
    · exact ⟨hxH₁.1.1, disjoint_left.mp hdisj hxH₁⟩

theorem deleteVertices_splitGraph_eq_splitSide (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂) :
    deleteVertices (splitGraph S P s t) V(P) = splitSide S.G P (S.Ω.interval s t) := by
  have hle1 : deleteVertices (splitGraph S P s t) V(P) ≤ S.G :=
    (deleteVertices_le _ _).trans (splitGraph_le S P s t)
  have hle2 : splitSide S.G P (S.Ω.interval s t) ≤ S.G :=
    splitSide_le S.G P (S.Ω.interval s t)
  have hV_eq : V(deleteVertices (splitGraph S P s t) V(P)) =
      V(splitSide S.G P (S.Ω.interval s t)) := by
    change V(splitGraph S P s t) \ V(P) = V(splitSide S.G P (S.Ω.interval s t))
    rw [vertexSet_splitGraph_eq_union S hs ht hst hP hcatch hnocross]
    ext x
    simp only [mem_sdiff, mem_union]
    exact ⟨fun ⟨hx, hx_not_P⟩ => hx.resolve_left hx_not_P,
      fun hxH₁ => ⟨Or.inr hxH₁, hxH₁.1.2⟩⟩
  have hdisj := (lemma_2_4_H1_disjoint_H2 S hs ht hst hP hnocross).1
  refine (Compatible.of_le_le hle1 hle2).ext hV_eq ?_
  ext e
  constructor
  · intro he
    obtain ⟨x, y, hxy⟩ := (deleteVertices (splitGraph S P s t) V(P)).exists_isLink_of_mem_edgeSet he
    have hxH₁ : x ∈ V(splitSide S.G P (S.Ω.interval s t)) := hV_eq ▸ hxy.left_mem
    have hyH₁ : y ∈ V(splitSide S.G P (S.Ω.interval s t)) := hV_eq ▸ hxy.right_mem
    rw [deleteVertices_isLink, splitGraph_isLink_iff] at hxy
    have hxy_del : (deleteVertices S.G V(P)).IsLink e x y :=
      (deleteVertices_isLink S.G V(P)).mpr ⟨hxy.1.1, hxy.2.1, hxy.2.2⟩
    exact ⟨x, y, hxy_del, hxH₁, hyH₁⟩
  · intro he
    obtain ⟨x, y, hxy⟩ := (splitSide S.G P (S.Ω.interval s t)).exists_isLink_of_mem_edgeSet he
    have hxH₁ : x ∈ V(splitSide S.G P (S.Ω.interval s t)) := hxy.left_mem
    have hyH₁ : y ∈ V(splitSide S.G P (S.Ω.interval s t)) := hxy.right_mem
    have hxyG : S.G.IsLink e x y := hxy.mono hle2
    have he_not_P : e ∉ E(P) := by
      intro heP
      obtain ⟨u, v, huvP⟩ := P.exists_isLink_of_mem_edgeSet heP
      rcases hxyG.left_eq_or_eq (huvP.mono hP.1) with rfl | rfl
      · exact hxH₁.1.2 huvP.left_mem
      · exact hxH₁.1.2 huvP.right_mem
    have hxy_split : (splitGraph S P s t).IsLink e x y :=
      (splitGraph_isLink_iff S P s t).mpr
        ⟨hxyG, he_not_P, disjoint_left.mp hdisj hxH₁, disjoint_left.mp hdisj hyH₁⟩
    exact ((deleteVertices_isLink (splitGraph S P s t) V(P)).mpr
      ⟨hxy_split, hxH₁.1.2, hyH₁.1.2⟩).edge_mem

/-- **Graph Minors IX, (2.4)** (page 45):
"$(G_1, \Omega_1)$, $(G_2, \Omega_2)$ are 3-connected societies, both with fewer edges than $(G,
\Omega)$."
(Part 1: `|E(G₁)| < |E(G)|`.) -/
theorem lemma_2_4_edgeSet_ncard_lt (S : Society α β) {P : Graph α β} {s t : α}
    (hst : s ≠ t) (hP : IsGraphPathWithEnds S.G P s t) :
    E(splitGraph S P s t).ncard < E(S.G).ncard := by
  obtain ⟨e₀, he₀P⟩ := nonempty_edgeSet_of_isGraphPathWithEnds_ne hP hst
  have he₀G : e₀ ∈ E(S.G) := hP.1.edgeSet_mono he₀P
  have he₀_not : e₀ ∉ E(splitGraph S P s t) :=
    fun h => (edgeSet_splitGraph_subset S P s t h).2 he₀P
  exact ncard_lt_ncard
    ⟨(splitGraph_le S P s t).edgeSet_mono, fun h => he₀_not (h he₀G)⟩ S.finite_E

/-- **Graph Minors IX, (2.4)** (page 45):
"Then $(G_1, \Omega_1)$, $(G_2, \Omega_2)$ are 3-connected societies, both with fewer edges than
$(G, \Omega)$." (Part 2: `(G₁, Ω₁)` is 3-connected.) -/
theorem lemma_2_4_isKConnected_three (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (_hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hconn : S.IsKConnected 3) :
    (splitSociety S hs ht hst hP hP_bar hnocross).IsKConnected 3 := by
  rintro k hk3 A₁ A₂ ⟨⟨hsep, hbar_A₂⟩, hcard_lt, hVA₂_ne⟩
  let G₁ := splitGraph S P s t
  let H₂ := splitSide S.G P (S.Ω.interval t s)
  have hA₁G : A₁ ≤ S.G := hsep.1.trans (splitGraph_le S P s t)
  have hA₂G : A₂ ≤ S.G := hsep.2.1.trans (splitGraph_le S P s t)
  have hbar₁ : S.Ω.interval s t ∪ V(P) ⊆ V(A₂) := by
    rw [← splitCyclicPerm_bar S hs ht hst hP hP_bar]
    exact hbar_A₂
  have hVP_A₂ : V(P) ⊆ V(A₂) := subset_union_right.trans hbar₁
  have hW₁_A₂ : S.Ω.interval s t ⊆ V(A₂) := subset_union_left.trans hbar₁
  have hdisj_A₁_H₂ : Disjoint V(A₁) V(H₂) := by
    rw [disjoint_left]
    intro x hxA₁ hxH₂
    exact (hsep.1.vertexSet_mono hxA₁).2 hxH₂
  let A₂' : Graph α β := (S.G.induce (V(A₂) ∪ V(H₂))).restrict (E(S.G) \ E(A₁))
  have hVA₂_H₂_sub : V(A₂) ∪ V(H₂) ⊆ V(S.G) :=
    union_subset hA₂G.vertexSet_mono (splitSide_le S.G P (S.Ω.interval t s)).vertexSet_mono
  have hA₂'G : A₂' ≤ S.G := restrict_le.trans (S.G.induce_le hVA₂_H₂_sub)
  have hVA₂' : V(A₂') = V(A₂) ∪ V(H₂) := rfl
  have hsep_S : IsGraphSeparation S.G A₁ A₂' := by
    refine ⟨hA₁G, hA₂'G, ?_, ?_, ?_⟩
    · change V(A₁) ∪ (V(A₂) ∪ V(H₂)) = V(S.G)
      rw [← union_assoc, hsep.2.2.1]
      change (V(S.G) \ V(H₂)) ∪ V(H₂) = V(S.G)
      rw [sdiff_union_self,
        union_eq_self_of_subset_right (splitSide_le S.G P (S.Ω.interval t s)).vertexSet_mono]
    · refine Subset.antisymm (union_subset hA₁G.edgeSet_mono hA₂'G.edgeSet_mono) fun e heG => ?_
      by_cases heA₁ : e ∈ E(A₁)
      · exact Or.inl heA₁
      · right
        obtain ⟨x, y, hxyG⟩ := S.G.exists_isLink_of_mem_edgeSet heG
        have hxy_in : x ∈ V(A₂) ∪ V(H₂) ∧ y ∈ V(A₂) ∪ V(H₂) := by
          by_cases heP : e ∈ E(P)
          · obtain ⟨u, v, huvP⟩ := P.exists_isLink_of_mem_edgeSet heP
            have hxP : x ∈ V(P) := by
              rcases hxyG.left_eq_or_eq (huvP.mono hP.1) with rfl | rfl
              · exact huvP.left_mem
              · exact huvP.right_mem
            have hyP : y ∈ V(P) := by
              rcases hxyG.symm.left_eq_or_eq (huvP.mono hP.1) with rfl | rfl
              · exact huvP.left_mem
              · exact huvP.right_mem
            exact ⟨Or.inl (hVP_A₂ hxP), Or.inl (hVP_A₂ hyP)⟩
          · by_cases hxH₂ : x ∈ V(H₂)
            · refine ⟨Or.inr hxH₂, ?_⟩
              by_cases hyP : y ∈ V(P)
              · exact Or.inl (hVP_A₂ hyP)
              · have hxy_del : (deleteVertices S.G V(P)).IsLink e x y :=
                  (deleteVertices_isLink S.G V(P)).mpr ⟨hxyG, hxH₂.1.2, hyP⟩
                exact Or.inr ((mem_splitSide_iff_of_deleteVertices_isLink hxy_del).mp hxH₂)
            · by_cases hyH₂ : y ∈ V(H₂)
              · refine ⟨?_, Or.inr hyH₂⟩
                by_cases hxP : x ∈ V(P)
                · exact Or.inl (hVP_A₂ hxP)
                · have hyx_del : (deleteVertices S.G V(P)).IsLink e y x :=
                    (deleteVertices_isLink S.G V(P)).mpr ⟨hxyG.symm, hyH₂.1.2, hxP⟩
                  exact Or.inr ((mem_splitSide_iff_of_deleteVertices_isLink hyx_del).mp hyH₂)
              · have hxy_G₁ : G₁.IsLink e x y :=
                  (splitGraph_isLink_iff S P s t).mpr ⟨hxyG, heP, hxH₂, hyH₂⟩
                have he_A₁₂ : e ∈ E(A₁) ∪ E(A₂) := hsep.2.2.2.1 ▸ hxy_G₁.edge_mem
                have heA₂ : e ∈ E(A₂) := he_A₁₂.resolve_left heA₁
                have hxy_A₂ : A₂.IsLink e x y := (hsep.2.1.isLink_iff heA₂).mpr hxy_G₁
                exact ⟨Or.inl hxy_A₂.left_mem, Or.inl hxy_A₂.right_mem⟩
        exact ⟨⟨x, y, hxyG, hxy_in.1, hxy_in.2⟩, heG, heA₁⟩
    · rw [disjoint_left]
      intro e heA₁ heA₂'
      exact heA₂'.2.2 heA₁
  have hbar_A₂' : S.Ω.bar ⊆ V(A₂') := by
    intro z hz
    rw [hVA₂']
    by_cases hzs : z = s
    · subst hzs; exact Or.inl (hVP_A₂ hP.left_mem)
    · by_cases hzt : z = t
      · subst hzt; exact Or.inl (hVP_A₂ hP.right_mem)
      · rcases S.Ω.mem_interval_or_interval_swap hs ht hz hst hzs hzt with hz1 | hz2
        · exact Or.inl (hW₁_A₂ hz1)
        · right
          exact mem_vertexSet_splitSide_of_mem_W (S.bar_subset hz)
            (fun hzP => disjoint_left.mp hP_bar ⟨hzP, by simp [hzs, hzt]⟩ hz) hz2
  have hinter_eq : V(A₁) ∩ V(A₂') = V(A₁) ∩ V(A₂) := by
    rw [hVA₂', inter_union_distrib_left, disjoint_iff_inter_eq_empty.mp hdisj_A₁_H₂, union_empty]
  have hVA₂'_ne : V(A₂') ≠ V(S.G) := by
    intro heq
    apply hVA₂_ne
    refine Subset.antisymm hsep.2.1.vertexSet_mono fun x hxG₁ => ?_
    have hx_in : x ∈ V(A₂) ∪ V(H₂) := by
      rw [← hVA₂', heq]
      exact hxG₁.1
    exact hx_in.resolve_right hxG₁.2
  exact hconn k hk3 A₁ A₂' ⟨⟨hsep_S, hbar_A₂'⟩, hinter_eq ▸ hcard_lt, hVA₂'_ne⟩

/-! ## Shrinking Crosses and Indexing `splitList` -/

/-- If `{a₁, b₁}` crosses `{a₂, b₂}` in `Ω` and `z ∈ Ω.bar \ {a₁, b₁, a₂, b₂}`, then either
`{a₁, z}` crosses `{a₂, b₂}` or `{z, b₁}` crosses `{a₂, b₂}`. -/
theorem CyclicPerm.crosses_split_at (Ω : CyclicPerm α) {a₁ b₁ a₂ b₂ z : α}
    (hcross : Ω.Crosses a₁ b₁ a₂ b₂) (hz_bar : z ∈ Ω.bar)
    (hza₁ : z ≠ a₁) (hzb₁ : z ≠ b₁) (hza₂ : z ≠ a₂) (hzb₂ : z ≠ b₂) :
    Ω.Crosses a₁ z a₂ b₂ ∨ Ω.Crosses z b₁ a₂ b₂ := by
  have hsplit : ∀ {u v : α}, Ω.Crosses u v a₂ b₂ → z ∈ Ω.interval u v →
      Ω.Crosses u z a₂ b₂ ∨ Ω.Crosses z v a₂ b₂ := by
    intro u v hc hz_uv
    have hv_zu : v ∈ Ω.interval z u := Ω.mem_interval_rotate_left hz_uv
    have hu_vz : u ∈ Ω.interval v z := Ω.mem_interval_rotate_right hz_uv
    have hsub_zu : Ω.interval v u ⊆ Ω.interval z u := Ω.interval_subset_interval_right hv_zu
    have hsub_vz : Ω.interval v u ⊆ Ω.interval v z := Ω.interval_subset_interval_left hu_vz
    have hunion := Ω.interval_eq_union_of_mem hz_uv
    rw [Ω.crosses_iff_interval] at hc
    rcases hc with ⟨hx_uv, hy_vu⟩ | ⟨hy_uv, hx_vu⟩
    · rw [hunion] at hx_uv
      rcases hx_uv with (hx_uz | hxz) | hx_zv
      · exact Or.inl (Ω.crosses_iff_interval.mpr (Or.inl ⟨hx_uz, hsub_zu hy_vu⟩))
      · rw [mem_singleton_iff] at hxz
        exact (hza₂ hxz.symm).elim
      · exact Or.inr (Ω.crosses_iff_interval.mpr (Or.inl ⟨hx_zv, hsub_vz hy_vu⟩))
    · rw [hunion] at hy_uv
      rcases hy_uv with (hy_uz | hyz) | hy_zv
      · exact Or.inl (Ω.crosses_iff_interval.mpr (Or.inr ⟨hy_uz, hsub_zu hx_vu⟩))
      · rw [mem_singleton_iff] at hyz
        exact (hzb₂ hyz.symm).elim
      · exact Or.inr (Ω.crosses_iff_interval.mpr (Or.inr ⟨hy_zv, hsub_vz hx_vu⟩))
  have ha₁_bar : a₁ ∈ Ω.bar := by
    rcases Ω.crosses_iff_interval.mp hcross with ⟨h, _⟩ | ⟨h, _⟩ <;>
      exact (Ω.isClockwise3_iff.mp h.2).2.2.2.1
  have hb₁_bar : b₁ ∈ Ω.bar := by
    rcases Ω.crosses_iff_interval.mp hcross with ⟨h, _⟩ | ⟨h, _⟩ <;>
      exact (Ω.isClockwise3_iff.mp h.2).2.2.2.2.2.1
  rcases Ω.mem_interval_or_interval_swap ha₁_bar hb₁_bar hz_bar hcross.ne_ends.1 hza₁ hzb₁ with
    hz_ab | hz_ba
  · exact hsplit hcross hz_ab
  · rcases hsplit hcross.swap_left hz_ba with h1 | h2
    · exact Or.inr h1.swap_left
    · exact Or.inl h2.swap_left

/-- Any path `Q₁` in `S'.G` from `a₁` to `b₁` whose ends cross `{a₂, b₂}` (with `a₂, b₂ ∉ V(Q₁)`)
contains a subpath `Q₁' ≤ Q₁` with ends `a₁', b₁' ∈ S'.Ω.bar` that still cross `{a₂, b₂}` and has
`V(Q₁') ∩ S'.Ω.bar = {a₁', b₁'}`. -/
theorem Society.exists_subpath_crosses_disjoint_bar (S' : Society α β)
    {Q₁ : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (hQ₁ : IsGraphPathWithEnds S'.G Q₁ a₁ b₁)
    (ha₂_not : a₂ ∉ V(Q₁)) (hb₂_not : b₂ ∉ V(Q₁))
    (hcross : S'.Ω.Crosses a₁ b₁ a₂ b₂) :
    ∃ Q₁' : Graph α β, ∃ a₁' b₁' : α,
      Q₁' ≤ Q₁ ∧
      IsGraphPathWithEnds S'.G Q₁' a₁' b₁' ∧
      V(Q₁') ∩ S'.Ω.bar = {a₁', b₁'} ∧
      S'.Ω.Crosses a₁' b₁' a₂ b₂ := by
  classical
  have hind : ∀ (n : ℕ) {P : Graph α β} {u v : α},
      P ≤ Q₁ → IsGraphPathWithEnds S'.G P u v → V(P).ncard = n →
      S'.Ω.Crosses u v a₂ b₂ →
      ∃ Q₁' : Graph α β, ∃ a₁' b₁' : α,
        Q₁' ≤ P ∧
        IsGraphPathWithEnds S'.G Q₁' a₁' b₁' ∧
        V(Q₁') ∩ S'.Ω.bar = {a₁', b₁'} ∧
        S'.Ω.Crosses a₁' b₁' a₂ b₂ := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro P u v hPQ₁ hP hcard hc
      by_cases hhit : ∃ z ∈ V(P) ∩ S'.Ω.bar, z ≠ u ∧ z ≠ v
      · obtain ⟨z, ⟨hzP, hz_bar⟩, hzu, hzv⟩ := hhit
        have hza₂ : z ≠ a₂ := fun h => ha₂_not (h ▸ hPQ₁.vertexSet_mono hzP)
        have hzb₂ : z ≠ b₂ := fun h => hb₂_not (h ▸ hPQ₁.vertexSet_mono hzP)
        obtain ⟨P₁, P₂, hP₁P, hP₂P, hpath₁, hpath₂, _, hinter, _⟩ := hP.exists_split_at hzP
        have hv_not_P₁ : v ∉ V(P₁) := by
          intro hv₁
          have : v ∈ V(P₁) ∩ V(P₂) := ⟨hv₁, hpath₂.right_mem⟩
          rw [hinter, mem_singleton_iff] at this
          exact hzv this.symm
        have hu_not_P₂ : u ∉ V(P₂) := by
          intro hu₂
          have : u ∈ V(P₁) ∩ V(P₂) := ⟨hpath₁.left_mem, hu₂⟩
          rw [hinter, mem_singleton_iff] at this
          exact hzu this.symm
        have hlt₁ : V(P₁).ncard < n := by
          rw [← hcard]
          exact ncard_lt_ncard ⟨hP₁P.vertexSet_mono, fun h => hv_not_P₁ (h hP.right_mem)⟩
            hP.vertexSet_finite
        have hlt₂ : V(P₂).ncard < n := by
          rw [← hcard]
          exact ncard_lt_ncard ⟨hP₂P.vertexSet_mono, fun h => hu_not_P₂ (h hP.left_mem)⟩
            hP.vertexSet_finite
        rcases S'.Ω.crosses_split_at hc hz_bar hzu hzv hza₂ hzb₂ with hc₁ | hc₂
        · obtain ⟨Q', a', b', hQ'P₁, hQ', hQ'_bar, hc'⟩ :=
            ih V(P₁).ncard hlt₁ (hP₁P.trans hPQ₁) (hpath₁.mono hP.le) rfl hc₁
          exact ⟨Q', a', b', hQ'P₁.trans hP₁P, hQ', hQ'_bar, hc'⟩
        · obtain ⟨Q', a', b', hQ'P₂, hQ', hQ'_bar, hc'⟩ :=
            ih V(P₂).ncard hlt₂ (hP₂P.trans hPQ₁) (hpath₂.mono hP.le) rfl hc₂
          exact ⟨Q', a', b', hQ'P₂.trans hP₂P, hQ', hQ'_bar, hc'⟩
      · have hu_bar : u ∈ S'.Ω.bar := by
          rcases S'.Ω.crosses_iff_interval.mp hc with ⟨h, _⟩ | ⟨h, _⟩ <;>
            exact (S'.Ω.isClockwise3_iff.mp h.2).2.2.2.1
        have hv_bar : v ∈ S'.Ω.bar := by
          rcases S'.Ω.crosses_iff_interval.mp hc with ⟨h, _⟩ | ⟨h, _⟩ <;>
            exact (S'.Ω.isClockwise3_iff.mp h.2).2.2.2.2.2.1
        refine ⟨P, u, v, le_rfl, hP, ?_, hc⟩
        ext z
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨hzP, hz_bar⟩
          by_contra! hne
          exact hhit ⟨z, ⟨hzP, hz_bar⟩, hne.1, hne.2⟩
        · rintro (rfl | rfl)
          · exact ⟨hP.left_mem, hu_bar⟩
          · exact ⟨hP.right_mem, hv_bar⟩
  exact hind V(Q₁).ncard le_rfl hQ₁ rfl hcross

/-- If a society `S'` has a cross, then it has a reduced cross `(P₁, P₂)` where neither `P₁` nor
`P₂` has any internal vertex in `S'.Ω.bar`. -/
theorem Society.exists_reduced_cross_of_isCross (S' : Society α β) {Q₁ Q₂ : Graph α β}
    (hcross : S'.IsCross Q₁ Q₂) :
    ∃ P₁ P₂ : Graph α β, ∃ s₁ t₁ s₂ t₂ : α,
      Disjoint V(P₁) V(P₂) ∧
      IsGraphPathWithEnds S'.G P₁ s₁ t₁ ∧
      IsGraphPathWithEnds S'.G P₂ s₂ t₂ ∧
      V(P₁) ∩ S'.Ω.bar = {s₁, t₁} ∧
      V(P₂) ∩ S'.Ω.bar = {s₂, t₂} ∧
      S'.Ω.Crosses s₁ t₁ s₂ t₂ := by
  rcases hcross with ⟨hdisj, a₁, b₁, a₂, b₂, hQ₁, hQ₂, hc⟩
  have ha₂_not : a₂ ∉ V(Q₁) := fun h => disjoint_left.mp hdisj h hQ₂.1.left_mem
  have hb₂_not : b₂ ∉ V(Q₁) := fun h => disjoint_left.mp hdisj h hQ₂.1.right_mem
  obtain ⟨P₁, s₁, t₁, hP₁Q₁, hP₁, hP₁_bar, hc₁⟩ :=
    S'.exists_subpath_crosses_disjoint_bar hQ₁.1 ha₂_not hb₂_not hc
  have hdisj₁ : Disjoint V(P₁) V(Q₂) := hdisj.mono_left hP₁Q₁.vertexSet_mono
  have hs₁_not : s₁ ∉ V(Q₂) := fun h => disjoint_left.mp hdisj₁ hP₁.left_mem h
  have ht₁_not : t₁ ∉ V(Q₂) := fun h => disjoint_left.mp hdisj₁ hP₁.right_mem h
  obtain ⟨P₂, s₂, t₂, hP₂Q₂, hP₂, hP₂_bar, hc₂⟩ :=
    S'.exists_subpath_crosses_disjoint_bar hQ₂.1 hs₁_not ht₁_not hc₁.symm
  exact ⟨P₁, P₂, s₁, t₁, s₂, t₂, hdisj₁.mono_right hP₂Q₂.vertexSet_mono,
    hP₁, hP₂, hP₁_bar, hP₂_bar, hc₂.symm⟩

/-- In a society `S' = (G', ofNodupList L hnd hne)`, any cross yields a reduced cross with
ordered indices `0 ≤ i₁ < i₂ < j₁ < j₂ < L.length`. -/
theorem exists_ordered_reduced_cross_of_ofNodupList {G' : Graph α β} {L : List α}
    (hnd : L.Nodup) (hne : L ≠ [])
    {S' : Society α β} (hG' : S'.G = G') (hΩ' : S'.Ω = CyclicPerm.ofNodupList L hnd hne)
    {Q₁ Q₂ : Graph α β} (hcross : S'.IsCross Q₁ Q₂) :
    ∃ P₁ P₂ : Graph α β, ∃ i₁ j₁ i₂ j₂ : ℕ,
      ∃ (hi₁ : i₁ < L.length) (hj₁ : j₁ < L.length)
        (hi₂ : i₂ < L.length) (hj₂ : j₂ < L.length),
        i₁ < i₂ ∧ i₂ < j₁ ∧ j₁ < j₂ ∧
        Disjoint V(P₁) V(P₂) ∧
        IsGraphPathWithEnds G' P₁ (L[i₁]'hi₁) (L[j₁]'hj₁) ∧
        IsGraphPathWithEnds G' P₂ (L[i₂]'hi₂) (L[j₂]'hj₂) ∧
        V(P₁) ∩ {x | x ∈ L} = {L[i₁]'hi₁, L[j₁]'hj₁} ∧
        V(P₂) ∩ {x | x ∈ L} = {L[i₂]'hi₂, L[j₂]'hj₂} := by
  obtain ⟨P₁, P₂, s₁, t₁, s₂, t₂, hdisj, hP₁, hP₂, hP₁_bar, hP₂_bar, hc⟩ :=
    S'.exists_reduced_cross_of_isCross hcross
  rw [hG'] at hP₁ hP₂
  have hbar_eq : S'.Ω.bar = {x | x ∈ L} := by rw [hΩ', CyclicPerm.ofNodupList_bar]
  rw [hbar_eq] at hP₁_bar hP₂_bar
  have hs₁L : s₁ ∈ L := by
    have : s₁ ∈ V(P₁) ∩ {x | x ∈ L} := by rw [hP₁_bar]; simp
    exact this.2
  have ht₁L : t₁ ∈ L := by
    have : t₁ ∈ V(P₁) ∩ {x | x ∈ L} := by rw [hP₁_bar]; simp
    exact this.2
  have hs₂L : s₂ ∈ L := by
    have : s₂ ∈ V(P₂) ∩ {x | x ∈ L} := by rw [hP₂_bar]; simp
    exact this.2
  have ht₂L : t₂ ∈ L := by
    have : t₂ ∈ V(P₂) ∩ {x | x ∈ L} := by rw [hP₂_bar]; simp
    exact this.2
  obtain ⟨a₁, ha₁, rfl⟩ := List.mem_iff_getElem.mp hs₁L
  obtain ⟨b₁, hb₁, rfl⟩ := List.mem_iff_getElem.mp ht₁L
  obtain ⟨a₂, ha₂, rfl⟩ := List.mem_iff_getElem.mp hs₂L
  obtain ⟨b₂, hb₂, rfl⟩ := List.mem_iff_getElem.mp ht₂L
  have hab₁_ne : a₁ ≠ b₁ := fun h => by subst h; exact hc.ne_ends.1 rfl
  have hab₂_ne : a₂ ≠ b₂ := fun h => by subst h; exact hc.ne_ends.2 rfl
  -- First orient `P₁` so `i₁ < j₁`, and `P₂` so `i₂ < j₂`.
  have horient₁ : ∃ i₁ j₁ : ℕ, ∃ (hi₁ : i₁ < L.length) (hj₁ : j₁ < L.length),
      i₁ < j₁ ∧
      IsGraphPathWithEnds G' P₁ (L[i₁]'hi₁) (L[j₁]'hj₁) ∧
      V(P₁) ∩ {x | x ∈ L} = {L[i₁]'hi₁, L[j₁]'hj₁} ∧
      S'.Ω.Crosses (L[i₁]'hi₁) (L[j₁]'hj₁) (L[a₂]'ha₂) (L[b₂]'hb₂) := by
    rcases lt_or_gt_of_ne hab₁_ne with hlt | hgt
    · exact ⟨a₁, b₁, ha₁, hb₁, hlt, hP₁, hP₁_bar, hc⟩
    · exact ⟨b₁, a₁, hb₁, ha₁, hgt, hP₁.symm, by rw [pair_comm]; exact hP₁_bar, hc.swap_left⟩
  obtain ⟨i₁, j₁, hi₁, hj₁, hij₁, hP₁', hP₁_bar', hc'⟩ := horient₁
  have horient₂ : ∃ i₂ j₂ : ℕ, ∃ (hi₂ : i₂ < L.length) (hj₂ : j₂ < L.length),
      i₂ < j₂ ∧
      IsGraphPathWithEnds G' P₂ (L[i₂]'hi₂) (L[j₂]'hj₂) ∧
      V(P₂) ∩ {x | x ∈ L} = {L[i₂]'hi₂, L[j₂]'hj₂} ∧
      S'.Ω.Crosses (L[i₁]'hi₁) (L[j₁]'hj₁) (L[i₂]'hi₂) (L[j₂]'hj₂) := by
    rcases lt_or_gt_of_ne hab₂_ne with hlt | hgt
    · exact ⟨a₂, b₂, ha₂, hb₂, hlt, hP₂, hP₂_bar, hc'⟩
    · exact ⟨b₂, a₂, hb₂, ha₂, hgt, hP₂.symm, by rw [pair_comm]; exact hP₂_bar, hc'.swap_right⟩
  obtain ⟨i₂, j₂, hi₂, hj₂, hij₂, hP₂', hP₂_bar', hc''⟩ := horient₂
  rw [hΩ', CyclicPerm.ofNodupList_crosses_iff L hnd hne hij₁ hj₁ hij₂ hj₂] at hc''
  rcases hc'' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨P₁, P₂, i₁, j₁, i₂, j₂, hi₁, hj₁, hi₂, hj₂,
      h1, h2, h3, hdisj, hP₁', hP₂', hP₁_bar', hP₂_bar'⟩
  · exact ⟨P₂, P₁, i₂, j₂, i₁, j₁, hi₂, hj₂, hi₁, hj₁,
      h1, h2, h3, hdisj.symm, hP₂', hP₁', hP₂_bar', hP₁_bar'⟩

theorem two_le_length_support_pathWalkTS {G P : Graph α β} {s t : α}
    (hst : s ≠ t) (hP : IsGraphPathWithEnds G P s t) :
    2 ≤ (pathWalkTS hP).support.length := by
  rcases hW : pathWalkTS hP with _ | ⟨hlink, W'⟩
  · exact (hst.symm (by rfl)).elim
  · cases W' <;> simp

theorem length_splitList (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t) :
    (splitList S hs ht hP).length =
      (pathWalkTS hP).support.length + (S.Ω.intervalList hs ht).length := by
  simp [splitList]

theorem getElem_splitList_of_lt (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t)
    {i : ℕ} (hi : i < (pathWalkTS hP).support.length) :
    (splitList S hs ht hP)[i]'(by rw [length_splitList]; omega) =
      (pathWalkTS hP).support[i]'hi := by
  simp [splitList, List.getElem_append_left hi]

theorem getElem_splitList_of_le (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t)
    {i : ℕ} (hmi : (pathWalkTS hP).support.length ≤ i)
    (hi : i < (splitList S hs ht hP).length) :
    (splitList S hs ht hP)[i]'hi =
      (S.Ω.intervalList hs ht)[i - (pathWalkTS hP).support.length]'(by
        rw [length_splitList] at hi; omega) := by
  simp [splitList, List.getElem_append_right hmi]

theorem getElem_splitList_zero (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t) :
    (splitList S hs ht hP)[0]'(by
      rw [length_splitList]
      have : 0 < (pathWalkTS hP).support.length := by cases pathWalkTS hP <;> simp
      omega) = t := by
  have hpos : 0 < (pathWalkTS hP).support.length := by cases pathWalkTS hP <;> simp
  rw [getElem_splitList_of_lt S hs ht hP hpos, support_getElem_zero]

theorem getElem_splitList_pred (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t) :
    (splitList S hs ht hP)[(pathWalkTS hP).support.length - 1]'(by
      rw [length_splitList]
      have : 0 < (pathWalkTS hP).support.length := by cases pathWalkTS hP <;> simp
      omega) = s := by
  have hpos : 0 < (pathWalkTS hP).support.length := by cases pathWalkTS hP <;> simp
  have hlt : (pathWalkTS hP).support.length - 1 < (pathWalkTS hP).support.length := by omega
  rw [getElem_splitList_of_lt S hs ht hP hlt, support_getElem_last]

theorem getElem_splitList_mem_P_iff (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {i : ℕ} (hi : i < (splitList S hs ht hP).length) :
    (splitList S hs ht hP)[i]'hi ∈ V(P) ↔ i < (pathWalkTS hP).support.length := by
  constructor
  · intro hxP
    rw [vertexSet_eq_support_pathWalkTS hP, mem_ofPred_eq, List.mem_iff_getElem] at hxP
    obtain ⟨k, hk, heq⟩ := hxP
    have hkl : k < (splitList S hs ht hP).length := by rw [length_splitList]; omega
    have heq' : (splitList S hs ht hP)[k]'hkl = (splitList S hs ht hP)[i]'hi := by
      rw [getElem_splitList_of_lt S hs ht hP hk, heq]
    have hik := nodup_getElem_inj (nodup_splitList S hs ht hst hP hP_bar) hkl hi heq'
    omega
  · intro hlt
    rw [getElem_splitList_of_lt S hs ht hP hlt, vertexSet_eq_support_pathWalkTS hP]
    exact List.getElem_mem hlt

theorem getElem_splitList_mem_W1_iff (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {i : ℕ} (hi : i < (splitList S hs ht hP).length) :
    (splitList S hs ht hP)[i]'hi ∈ S.Ω.interval s t ↔
      (pathWalkTS hP).support.length ≤ i := by
  constructor
  · intro hxW
    have hxL := (S.Ω.mem_intervalList_iff hs ht hst _).mpr hxW
    obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hxL
    have hkl : (pathWalkTS hP).support.length + k < (splitList S hs ht hP).length := by
      rw [length_splitList]; omega
    have heq' : (splitList S hs ht hP)[(pathWalkTS hP).support.length + k]'hkl =
        (splitList S hs ht hP)[i]'hi := by
      rw [getElem_splitList_of_le S hs ht hP (by omega) hkl]
      simpa using heq
    have hik := nodup_getElem_inj (nodup_splitList S hs ht hst hP hP_bar) hkl hi heq'
    omega
  · intro hmi
    rw [getElem_splitList_of_le S hs ht hP hmi hi]
    exact (S.Ω.mem_intervalList_iff hs ht hst _).mp (List.getElem_mem _)

theorem exists_subpath_P_of_splitList_indices (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar)
    (hP : IsGraphPathWithEnds S.G P s t)
    {i j : ℕ} (hij : i ≤ j) (hj : j < (pathWalkTS hP).support.length) :
    ∃ Q ≤ P,
      IsGraphPathWithEnds S.G Q
        ((splitList S hs ht hP)[i]'(by rw [length_splitList]; omega))
        ((splitList S hs ht hP)[j]'(by rw [length_splitList]; omega)) ∧
      V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
        i ≤ k ∧ k ≤ j ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)} := by
  obtain ⟨Q, hQW, hQ, hVQ⟩ :=
    exists_subpath_of_support_indices (isSimple_pathWalkTS hP) hij hj
  rw [walkSubgraph_pathWalkTS hP] at hQW
  refine ⟨Q, hQW, ?_, ?_⟩
  · rw [getElem_splitList_of_lt S hs ht hP (by omega), getElem_splitList_of_lt S hs ht hP hj]
    exact hQ.mono hP.le
  · ext x
    rw [hVQ]
    simp only [mem_ofPred_eq]
    refine ⟨fun ⟨k, hk, hik, hkj, hxk⟩ => ⟨k, hk, hik, hkj, ?_⟩,
      fun ⟨k, hk, hik, hkj, hxk⟩ => ⟨k, hk, hik, hkj, ?_⟩⟩
    · rw [getElem_splitList_of_lt S hs ht hP hk, hxk]
    · rw [← getElem_splitList_of_lt S hs ht hP hk, hxk]

/-- Because `P` is an induced subgraph of `S.G` and `splitGraph` deletes `E(P)`, no edge of
`splitGraph S P s t` has both endpoints in `V(P)`. -/
theorem not_isLink_splitGraph_of_mem_P (S : Society α β) {P : Graph α β} (s t : α)
    (hP_ind : P ≤i S.G) {e : β} {x y : α}
    (hlink : (splitGraph S P s t).IsLink e x y) (hx : x ∈ V(P)) (hy : y ∈ V(P)) :
    False := by
  rw [splitGraph_isLink_iff] at hlink
  exact hlink.2.1 (hP_ind.isLink_of_mem_mem hlink.1 hx hy).edge_mem

/-- Every path `Q` in `splitGraph S P s t` between distinct vertices `u ≠ v` contains a vertex
in `V(splitSide S.G P (S.Ω.interval s t))` (outside `V(P)`). -/
theorem exists_vertex_in_splitSide_of_path_in_splitGraph (S : Society α β) {P : Graph α β}
    {s t : α} (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t) (hP_ind : P ≤i S.G)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    {Q : Graph α β} {u v : α} (hQ : IsGraphPathWithEnds (splitGraph S P s t) Q u v)
    (huv : u ≠ v) :
    ∃ x ∈ V(Q), x ∈ V(splitSide S.G P (S.Ω.interval s t)) := by
  by_contra! hsub
  have hVQ_P : V(Q) ⊆ V(P) := by
    intro x hxQ
    have hxG₁ : x ∈ V(splitGraph S P s t) := hQ.1.vertexSet_mono hxQ
    rw [vertexSet_splitGraph_eq_union S hs ht hst hP hcatch hnocross] at hxG₁
    exact hxG₁.resolve_right (hsub x hxQ)
  obtain ⟨W, _, _, _⟩ := hQ.2
  cases W with
  | nil _ => exact huv rfl
  | @cons u w v e hlink W' =>
    have huP : u ∈ V(P) := hVQ_P hlink.left_mem
    have hwP : w ∈ V(P) := hVQ_P hlink.right_mem
    exact not_isLink_splitGraph_of_mem_P S s t hP_ind (hlink.mono hQ.1) huP hwP

/-- Given a set `X` containing a vertex `u₀ ∈ V(splitSide S.G P (S.Ω.interval s t))`, there is
an `X → W₁` path `P₃` in `splitSide S.G P (S.Ω.interval s t)` ending at `(splitList S hs ht hP)[k]`
with `m ≤ k`, disjoint from `V(P)` and meeting `S.Ω.bar` and `splitList` only at `L[k]`. -/
theorem exists_fromToPath_in_splitSide (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    {X : Set α} {u₀ : α} (hu₀X : u₀ ∈ X)
    (hu₀H₁ : u₀ ∈ V(splitSide S.G P (S.Ω.interval s t))) :
    ∃ u ∈ X, ∃ k : ℕ, ∃ hk : k < (splitList S hs ht hP).length,
      ∃ P₃ ≤ splitSide S.G P (S.Ω.interval s t),
        (pathWalkTS hP).support.length ≤ k ∧
        Disjoint V(P₃) V(P) ∧
        IsFromToPathWithEnds (splitGraph S P s t) P₃ X (S.Ω.interval s t) u
          ((splitList S hs ht hP)[k]'hk) ∧
        V(P₃) ∩ {x | x ∈ splitList S hs ht hP} = {(splitList S hs ht hP)[k]'hk} ∧
        V(P₃) ∩ S.Ω.bar = {(splitList S hs ht hP)[k]'hk} := by
  let H₁ := splitSide S.G P (S.Ω.interval s t)
  obtain ⟨w₀, ⟨hw₀W₁, _⟩, ⟨W⟩⟩ := exists_walk_in_splitSide_to_W hu₀H₁
  obtain ⟨u, huX, w, hwW₁, P₃, hP₃W, _, hP₃_ft⟩ :=
    exists_isFromToPathWithEnds_of_walk W hu₀X hw₀W₁
  have hP₃H₁ : P₃ ≤ H₁ := hP₃W.trans (walkSubgraph_le W)
  have hdisj_P : Disjoint V(P₃) V(P) := by
    rw [disjoint_left]
    intro x hxP₃
    exact (hP₃H₁.vertexSet_mono hxP₃).1.2
  have hH₁_le_G₁ : H₁ ≤ splitGraph S P s t := by
    have hdisj_H₁_H₂ := (lemma_2_4_H1_disjoint_H2 S hs ht hst hP hnocross).1
    refine (Compatible.of_le_le (splitSide_le S.G P (S.Ω.interval s t))
      (splitGraph_le S P s t)).le_iff.mpr ⟨?_, ?_⟩
    · intro x hxH₁
      exact ⟨hxH₁.1.1, disjoint_left.mp hdisj_H₁_H₂ hxH₁⟩
    · intro e heH₁
      obtain ⟨x, y, hxy⟩ := H₁.exists_isLink_of_mem_edgeSet heH₁
      have hxH₁ := hxy.left_mem
      have hyH₁ := hxy.right_mem
      have hxyG : S.G.IsLink e x y := hxy.mono (splitSide_le S.G P (S.Ω.interval s t))
      have he_not_P : e ∉ E(P) := by
        intro heP
        obtain ⟨a, b, habP⟩ := P.exists_isLink_of_mem_edgeSet heP
        have habG : S.G.IsLink e a b := habP.mono hP.1
        rcases hxyG.eq_and_eq_or_eq_and_eq habG with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxH₁.1.2 habP.left_mem
        · exact hxH₁.1.2 habP.right_mem
      have hxyG₁ : (splitGraph S P s t).IsLink e x y := by
        rw [splitGraph_isLink_iff]
        exact ⟨hxyG, he_not_P, disjoint_left.mp hdisj_H₁_H₂ hxH₁,
          disjoint_left.mp hdisj_H₁_H₂ hyH₁⟩
      exact hxyG₁.edge_mem
  have hwL : w ∈ S.Ω.intervalList hs ht := (S.Ω.mem_intervalList_iff hs ht hst w).mpr hwW₁
  obtain ⟨idx, hidx, hwk⟩ := List.mem_iff_getElem.mp hwL
  let k := (pathWalkTS hP).support.length + idx
  have hk : k < (splitList S hs ht hP).length := by
    rw [length_splitList]; omega
  have hmk : (pathWalkTS hP).support.length ≤ k := by omega
  have hLk : (splitList S hs ht hP)[k]'hk = w := by
    rw [getElem_splitList_of_le S hs ht hP hmk hk]
    simpa [k] using hwk
  have hP₃_G₁ : IsFromToPathWithEnds (splitGraph S P s t) P₃ X (S.Ω.interval s t) u w :=
    ⟨hP₃_ft.1.mono hH₁_le_G₁, hP₃_ft.2⟩
  have hP₃_L : V(P₃) ∩ {x | x ∈ splitList S hs ht hP} = {w} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hxP₃, hxL⟩
      rw [splitList, List.mem_append, S.Ω.mem_intervalList_iff hs ht hst] at hxL
      rcases hxL with hxP | hxW₁
      · have hxP' : x ∈ V(P) := by rw [vertexSet_eq_support_pathWalkTS hP]; exact hxP
        exact (disjoint_left.mp hdisj_P hxP₃ hxP').elim
      · have hx_in : x ∈ V(P₃) ∩ S.Ω.interval s t := ⟨hxP₃, hxW₁⟩
        rwa [hP₃_ft.2.2, mem_singleton_iff] at hx_in
    · rintro rfl
      exact ⟨hP₃_ft.1.right_mem, List.mem_append_right _ hwL⟩
  have hP₃_bar : V(P₃) ∩ S.Ω.bar = {w} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxP₃, hx_bar⟩
      have hxH₁ : x ∈ V(H₁) := hP₃H₁.vertexSet_mono hxP₃
      have hxs : x ≠ s := fun h => hxH₁.1.2 (h ▸ hP.left_mem)
      have hxt : x ≠ t := fun h => hxH₁.1.2 (h ▸ hP.right_mem)
      rcases S.Ω.mem_interval_or_interval_swap hs ht hx_bar hst hxs hxt with hxW₁ | hxW₂
      · have hx_in : x ∈ V(P₃) ∩ S.Ω.interval s t := ⟨hxP₃, hxW₁⟩
        rwa [hP₃_ft.2.2, mem_singleton_iff] at hx_in
      · have hxH₂ : x ∈ V(splitSide S.G P (S.Ω.interval t s)) :=
          mem_vertexSet_splitSide_of_mem_W (S.bar_subset hx_bar) hxH₁.1.2 hxW₂
        exact (disjoint_left.mp (lemma_2_4_H1_disjoint_H2 S hs ht hst hP hnocross).1
          hxH₁ hxH₂).elim
    · rintro rfl
      exact ⟨hP₃_ft.1.right_mem, hwW₁.1.1⟩
  refine ⟨u, huX, k, hk, P₃, hP₃H₁, hmk, hdisj_P, ?_, ?_, ?_⟩
  · rwa [hLk]
  · rwa [hLk]
  · rwa [hLk]

theorem subpath_P_subset_splitList (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hP : IsGraphPathWithEnds S.G P s t)
    {a b : ℕ}
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a ≤ k ∧ k ≤ b ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)}) :
    V(Q) ⊆ {x | x ∈ splitList S hs ht hP} := by
  intro x hx
  rw [hVQ, mem_ofPred_eq] at hx
  obtain ⟨k, hk, _, _, rfl⟩ := hx
  exact List.getElem_mem _

theorem mem_subpath_P_iff (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {a b : ℕ} (hb : b < (pathWalkTS hP).support.length)
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a ≤ k ∧ k ≤ b ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)})
    {idx : ℕ} (hidx : idx < (splitList S hs ht hP).length) :
    (splitList S hs ht hP)[idx]'hidx ∈ V(Q) ↔ a ≤ idx ∧ idx ≤ b := by
  rw [hVQ, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, hak, hkb, heq⟩
    have hkl : k < (splitList S hs ht hP).length := by rw [length_splitList]; omega
    have hik := nodup_getElem_inj (nodup_splitList S hs ht hst hP hP_bar) hidx hkl heq
    omega
  · rintro ⟨ha, hb'⟩
    exact ⟨idx, by omega, ha, hb', rfl⟩

theorem disjoint_subpath_P_of_inter_pair (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {a b i j : ℕ} (hb : b < (pathWalkTS hP).support.length)
    (hi : i < (splitList S hs ht hP).length) (hj : j < (splitList S hs ht hP).length)
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a ≤ k ∧ k ≤ b ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)})
    {A : Set α}
    (hA : A ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i]'hi, (splitList S hs ht hP)[j]'hj})
    (hni : ¬ (a ≤ i ∧ i ≤ b)) (hnj : ¬ (a ≤ j ∧ j ≤ b)) :
    Disjoint A V(Q) := by
  rw [disjoint_left]
  intro x hxA hxQ
  have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
    subpath_P_subset_splitList S hs ht hP hVQ hxQ
  have hx_pair : x ∈ A ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxA, hxL⟩
  rw [hA, mem_insert_iff, mem_singleton_iff] at hx_pair
  rcases hx_pair with rfl | rfl
  · exact hni ((mem_subpath_P_iff S hs ht hst hP hP_bar hb hVQ hi).mp hxQ)
  · exact hnj ((mem_subpath_P_iff S hs ht hst hP hP_bar hb hVQ hj).mp hxQ)

theorem inter_subpath_P_eq_left_of_inter_pair (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {a b i j : ℕ} (hb : b < (pathWalkTS hP).support.length)
    (hi : i < (splitList S hs ht hP).length) (hj : j < (splitList S hs ht hP).length)
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a ≤ k ∧ k ≤ b ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)})
    {A : Set α}
    (hA : A ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i]'hi, (splitList S hs ht hP)[j]'hj})
    (hi_in : a ≤ i ∧ i ≤ b) (hnj : ¬ (a ≤ j ∧ j ≤ b)) :
    V(Q) ∩ A = {(splitList S hs ht hP)[i]'hi} := by
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxQ, hxA⟩
    have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
      subpath_P_subset_splitList S hs ht hP hVQ hxQ
    have hx_pair : x ∈ A ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxA, hxL⟩
    rw [hA, mem_insert_iff, mem_singleton_iff] at hx_pair
    rcases hx_pair with rfl | rfl
    · rfl
    · exact (hnj ((mem_subpath_P_iff S hs ht hst hP hP_bar hb hVQ hj).mp hxQ)).elim
  · rintro rfl
    have hiA : (splitList S hs ht hP)[i]'hi ∈ A ∩ {y | y ∈ splitList S hs ht hP} := by
      rw [hA]; simp
    exact ⟨(mem_subpath_P_iff S hs ht hst hP hP_bar hb hVQ hi).mpr hi_in, hiA.1⟩

theorem disjoint_subpath_P_subpath_P (S : Society α β) {P Q₁ Q₂ : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {a₁ b₁ a₂ b₂ : ℕ}
    (hb₂ : b₂ < (pathWalkTS hP).support.length) (hlt : b₁ < a₂)
    (hVQ₁ : V(Q₁) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a₁ ≤ k ∧ k ≤ b₁ ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)})
    (hVQ₂ : V(Q₂) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a₂ ≤ k ∧ k ≤ b₂ ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)}) :
    Disjoint V(Q₁) V(Q₂) := by
  rw [disjoint_left]
  intro x hx₁ hx₂
  rw [hVQ₁, mem_ofPred_eq] at hx₁
  obtain ⟨k, hk, _, hkb₁, rfl⟩ := hx₁
  have hkl : k < (splitList S hs ht hP).length := by rw [length_splitList]; omega
  have hk₂ := (mem_subpath_P_iff S hs ht hst hP hP_bar hb₂ hVQ₂ hkl).mp hx₂
  omega

/-- Case `r ≥ 2` of `(2.4)` (`lemma_2_4_no_cross`): no reduced cross `(P₁, P₂)` in `(G₁, Ω₁)`
with indices `0 ≤ i₁ < i₂ < j₁ < j₂ < L.length` can have `m ≤ j₁` (at least two endpoints
in `W₁`). -/
theorem no_reduced_cross_of_two_in_W1 (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    {P₁ P₂ : Graph α β} {i₁ j₁ i₂ j₂ : ℕ}
    (hi₁ : i₁ < (splitList S hs ht hP).length)
    (hj₁ : j₁ < (splitList S hs ht hP).length)
    (hi₂ : i₂ < (splitList S hs ht hP).length)
    (hj₂ : j₂ < (splitList S hs ht hP).length)
    (h12 : i₁ < i₂) (h21 : i₂ < j₁) (h12' : j₁ < j₂)
    (hdisj : Disjoint V(P₁) V(P₂))
    (hP₁ : IsGraphPathWithEnds (splitGraph S P s t) P₁
      ((splitList S hs ht hP)[i₁]'hi₁) ((splitList S hs ht hP)[j₁]'hj₁))
    (hP₂ : IsGraphPathWithEnds (splitGraph S P s t) P₂
      ((splitList S hs ht hP)[i₂]'hi₂) ((splitList S hs ht hP)[j₂]'hj₂))
    (hP₁_L : V(P₁) ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i₁]'hi₁, (splitList S hs ht hP)[j₁]'hj₁})
    (hP₂_L : V(P₂) ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i₂]'hi₂, (splitList S hs ht hP)[j₂]'hj₂})
    (hmj₁ : (pathWalkTS hP).support.length ≤ j₁) :
    False := by
  let m := (pathWalkTS hP).support.length
  have hm2 : 2 ≤ m := two_le_length_support_pathWalkTS hst hP
  have hP₁G : IsGraphPathWithEnds S.G P₁
      ((splitList S hs ht hP)[i₁]'hi₁) ((splitList S hs ht hP)[j₁]'hj₁) :=
    hP₁.mono (splitGraph_le S P s t)
  have hP₂G : IsGraphPathWithEnds S.G P₂
      ((splitList S hs ht hP)[i₂]'hi₂) ((splitList S hs ht hP)[j₂]'hj₂) :=
    hP₂.mono (splitGraph_le S P s t)
  by_cases hmi₁ : m ≤ i₁
  · -- Subcase 1a: all 4 endpoints in `W₁`.
    have hc : S.Ω.Crosses
        ((splitList S hs ht hP)[i₁]'hi₁) ((splitList S hs ht hP)[j₁]'hj₁)
        ((splitList S hs ht hP)[i₂]'hi₂) ((splitList S hs ht hP)[j₂]'hj₂) := by
      rw [getElem_splitList_of_le S hs ht hP hmi₁ hi₁,
        getElem_splitList_of_le S hs ht hP hmj₁ hj₁,
        getElem_splitList_of_le S hs ht hP (by omega) hi₂,
        getElem_splitList_of_le S hs ht hP (by omega) hj₂]
      exact S.Ω.crosses_intervalList_of_lt hs ht hst (by omega) (by omega) (by omega)
        (by rw [length_splitList] at hj₂; omega)
    have hbar₁ : (splitList S hs ht hP)[i₁]'hi₁ ∈ S.Ω.bar :=
      ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hi₁).mpr hmi₁).1.1
    have hbar₁' : (splitList S hs ht hP)[j₁]'hj₁ ∈ S.Ω.bar :=
      ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hj₁).mpr hmj₁).1.1
    have hbar₂ : (splitList S hs ht hP)[i₂]'hi₂ ∈ S.Ω.bar :=
      ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hi₂).mpr (by omega)).1.1
    have hbar₂' : (splitList S hs ht hP)[j₂]'hj₂ ∈ S.Ω.bar :=
      ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hj₂).mpr (by omega)).1.1
    exact hnocross ⟨P₁, P₂, hdisj, _, _, _, _,
      ⟨hP₁G, hc.ne_ends.1, hbar₁, hbar₁'⟩, ⟨hP₂G, hc.ne_ends.2, hbar₂, hbar₂'⟩, hc⟩
  · have hmi₁' : i₁ < m := Nat.lt_of_not_ge hmi₁
    obtain ⟨Q₀, _, hQ₀, hVQ₀⟩ :=
      exists_subpath_P_of_splitList_indices S hs ht hP (Nat.zero_le i₁) hmi₁'
    have hQ₀_P₁ : V(Q₀) ∩ V(P₁) = {(splitList S hs ht hP)[i₁]'hi₁} :=
      inter_subpath_P_eq_left_of_inter_pair S hs ht hst hP hP_bar hmi₁' hi₁ hj₁ hVQ₀ hP₁_L
        ⟨Nat.zero_le i₁, le_rfl⟩ (by omega)
    have hR₁_path : IsGraphPathWithEnds S.G (subgraphUnion S.G Q₀ P₁) t
        ((splitList S hs ht hP)[j₁]'hj₁) := by
      have h := hQ₀.subgraphUnion hP₁G hQ₀_P₁
      rwa [getElem_splitList_zero S hs ht hP] at h
    have hdisj_P₂_Q₀ : Disjoint V(P₂) V(Q₀) :=
      disjoint_subpath_P_of_inter_pair S hs ht hst hP hP_bar hmi₁' hi₂ hj₂ hVQ₀ hP₂_L
        (by omega) (by omega)
    have hbar₁' : (splitList S hs ht hP)[j₁]'hj₁ ∈ S.Ω.bar :=
      ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hj₁).mpr hmj₁).1.1
    have hbar₂' : (splitList S hs ht hP)[j₂]'hj₂ ∈ S.Ω.bar :=
      ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hj₂).mpr (by omega)).1.1
    by_cases hmi₂ : m ≤ i₂
    · -- Subcase 1b: `i₁ < m ≤ i₂ < j₁ < j₂`.
      have hdisj_R₁_P₂ : Disjoint V(subgraphUnion S.G Q₀ P₁) V(P₂) := by
        rw [vertexSet_subgraphUnion]
        exact Disjoint.union_left hdisj_P₂_Q₀.symm hdisj
      have hc : S.Ω.Crosses t ((splitList S hs ht hP)[j₁]'hj₁)
          ((splitList S hs ht hP)[i₂]'hi₂) ((splitList S hs ht hP)[j₂]'hj₂) := by
        rw [getElem_splitList_of_le S hs ht hP hmj₁ hj₁,
          getElem_splitList_of_le S hs ht hP hmi₂ hi₂,
          getElem_splitList_of_le S hs ht hP (by omega) hj₂]
        exact S.Ω.crosses_t_intervalList_of_lt hs ht hst (by omega) (by omega)
          (by rw [length_splitList] at hj₂; omega)
      have hbar₂ : (splitList S hs ht hP)[i₂]'hi₂ ∈ S.Ω.bar :=
        ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hi₂).mpr hmi₂).1.1
      exact hnocross ⟨subgraphUnion S.G Q₀ P₁, P₂, hdisj_R₁_P₂, _, _, _, _,
        ⟨hR₁_path, hc.ne_ends.1, ht, hbar₁'⟩, ⟨hP₂G, hc.ne_ends.2, hbar₂, hbar₂'⟩, hc⟩
    · -- Subcase 1c: `i₁ < i₂ < m ≤ j₁ < j₂`.
      have hmi₂' : i₂ < m := Nat.lt_of_not_ge hmi₂
      have hm_pred : m - 1 < m := by omega
      obtain ⟨Q₁, _, hQ₁, hVQ₁⟩ :=
        exists_subpath_P_of_splitList_indices S hs ht hP (by omega : i₂ ≤ m - 1) hm_pred
      have hQ₁_P₂ : V(Q₁) ∩ V(P₂) = {(splitList S hs ht hP)[i₂]'hi₂} :=
        inter_subpath_P_eq_left_of_inter_pair S hs ht hst hP hP_bar hm_pred hi₂ hj₂ hVQ₁ hP₂_L
          ⟨le_rfl, by omega⟩ (by omega)
      have hR₂_path : IsGraphPathWithEnds S.G (subgraphUnion S.G Q₁ P₂) s
          ((splitList S hs ht hP)[j₂]'hj₂) := by
        have h := (hQ₁.symm).subgraphUnion hP₂G hQ₁_P₂
        rwa [getElem_splitList_pred S hs ht hP] at h
      have hdisj_P₁_Q₁ : Disjoint V(P₁) V(Q₁) :=
        disjoint_subpath_P_of_inter_pair S hs ht hst hP hP_bar hm_pred hi₁ hj₁ hVQ₁ hP₁_L
          (by omega) (by omega)
      have hdisj_Q₀_Q₁ : Disjoint V(Q₀) V(Q₁) :=
        disjoint_subpath_P_subpath_P S hs ht hst hP hP_bar hm_pred h12 hVQ₀ hVQ₁
      have hdisj_R₁_R₂ : Disjoint V(subgraphUnion S.G Q₀ P₁) V(subgraphUnion S.G Q₁ P₂) := by
        rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion]
        exact Disjoint.union_left (Disjoint.union_right hdisj_Q₀_Q₁ hdisj_P₂_Q₀.symm)
          (Disjoint.union_right hdisj_P₁_Q₁ hdisj)
      have hc : S.Ω.Crosses t ((splitList S hs ht hP)[j₁]'hj₁)
          s ((splitList S hs ht hP)[j₂]'hj₂) := by
        rw [getElem_splitList_of_le S hs ht hP hmj₁ hj₁,
          getElem_splitList_of_le S hs ht hP (by omega) hj₂]
        exact S.Ω.crosses_t_s_intervalList_of_lt hs ht hst (by omega)
          (by rw [length_splitList] at hj₂; omega)
      exact hnocross ⟨subgraphUnion S.G Q₀ P₁, subgraphUnion S.G Q₁ P₂, hdisj_R₁_R₂, _, _, _, _,
        ⟨hR₁_path, hc.ne_ends.1, ht, hbar₁'⟩, ⟨hR₂_path, hc.ne_ends.2, hs, hbar₂'⟩, hc⟩

theorem inter_left_of_split {P P_a P_b : Graph α β} {A : Set α} {a b u : α}
    (hPa : P_a ≤ P) (hinter : V(P_a) ∩ V(P_b) = {u})
    (ha : a ∈ V(P_a)) (hb : b ∈ V(P_b)) (hub : u ≠ b)
    (hPA : V(P) ∩ A = {a, b}) :
    V(P_a) ∩ A = {a} := by
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxPa, hxA⟩
    have hx_in : x ∈ V(P) ∩ A := ⟨hPa.vertexSet_mono hxPa, hxA⟩
    rw [hPA, mem_insert_iff, mem_singleton_iff] at hx_in
    rcases hx_in with hxa | hxb
    · exact hxa
    · subst hxb
      have hb_in : x ∈ V(P_a) ∩ V(P_b) := ⟨hxPa, hb⟩
      rw [hinter, mem_singleton_iff] at hb_in
      exact (hub hb_in.symm).elim
  · rintro rfl
    have ha_in : x ∈ V(P) ∩ A := by rw [hPA]; simp
    exact ⟨ha, ha_in.2⟩

theorem inter_right_of_split {P P_a P_b : Graph α β} {A : Set α} {a b u : α}
    (hPb : P_b ≤ P) (hinter : V(P_a) ∩ V(P_b) = {u})
    (ha : a ∈ V(P_a)) (hb : b ∈ V(P_b)) (hua : u ≠ a)
    (hPA : V(P) ∩ A = {a, b}) :
    V(P_b) ∩ A = {b} := by
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxPb, hxA⟩
    have hx_in : x ∈ V(P) ∩ A := ⟨hPb.vertexSet_mono hxPb, hxA⟩
    rw [hPA, mem_insert_iff, mem_singleton_iff] at hx_in
    rcases hx_in with hxa | hxb
    · subst hxa
      have ha_in : x ∈ V(P_a) ∩ V(P_b) := ⟨ha, hxPb⟩
      rw [hinter, mem_singleton_iff] at ha_in
      exact (hua ha_in.symm).elim
    · exact hxb
  · rintro rfl
    have hb_in : x ∈ V(P) ∩ A := by rw [hPA]; simp
    exact ⟨hb, hb_in.2⟩

/-- Three pairwise vertex-disjoint `X → Y` paths `R₁, R₂, R₃` in `G` from distinct `s₁, s₂, s₃ ∈ X`
to `t₁, t₂, t₃ ∈ Y` witness `RedirectsTo G X Y {s₁, s₂, s₃} {t₁, t₂, t₃}`. -/
theorem redirectsTo_of_three_disjoint_paths {α : Type u} {β : Type v}
    {G R₁ R₂ R₃ : Graph α β} {X Y : Set α}
    {s₁ s₂ s₃ t₁ t₂ t₃ : α}
    (hs₁ : s₁ ∈ X) (hs₂ : s₂ ∈ X) (hs₃ : s₃ ∈ X)
    (ht₁ : t₁ ∈ Y) (ht₂ : t₂ ∈ Y) (ht₃ : t₃ ∈ Y)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃)
    (hR₁ : IsFromToPathWithEnds G R₁ X Y s₁ t₁)
    (hR₂ : IsFromToPathWithEnds G R₂ X Y s₂ t₂)
    (hR₃ : IsFromToPathWithEnds G R₃ X Y s₃ t₃)
    (hd12 : Disjoint V(R₁) V(R₂))
    (hd13 : Disjoint V(R₁) V(R₃))
    (hd23 : Disjoint V(R₂) V(R₃)) :
    RedirectsTo G X Y {s₁, s₂, s₃} {t₁, t₂, t₃} := by
  classical
  have ht12 : t₁ ≠ t₂ := fun h => disjoint_left.mp hd12 hR₁.1.right_mem (h ▸ hR₂.1.right_mem)
  have ht13 : t₁ ≠ t₃ := fun h => disjoint_left.mp hd13 hR₁.1.right_mem (h ▸ hR₃.1.right_mem)
  have ht23 : t₂ ≠ t₃ := fun h => disjoint_left.mp hd23 hR₂.1.right_mem (h ▸ hR₃.1.right_mem)
  have hX'_sub : ({s₁, s₂, s₃} : Set α) ⊆ X := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hY'_sub : ({t₁, t₂, t₃} : Set α) ⊆ Y := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hcard_s : ({s₁, s₂, s₃} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hs12, hs13]) ((finite_singleton s₃).insert s₂),
      ncard_insert_of_notMem (by simp [hs23]) (finite_singleton s₃), ncard_singleton]
  have hcard_t : ({t₁, t₂, t₃} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [ht12, ht13]) ((finite_singleton t₃).insert t₂),
      ncard_insert_of_notMem (by simp [ht23]) (finite_singleton t₃), ncard_singleton]
  refine ⟨hX'_sub, hY'_sub, hcard_s.trans hcard_t.symm, ?_⟩
  let P_fam : Fin ({s₁, s₂, s₃} : Set α).ncard → Graph α β :=
    fun i => if i.1 = 0 then R₁ else if i.1 = 1 then R₂ else R₃
  refine ⟨P_fam, ?_, ?_⟩
  · intro i j hij
    have hi : i.1 < 3 := hcard_s ▸ i.2
    have hj : j.1 < 3 := hcard_s ▸ j.2
    have hij' : i.1 ≠ j.1 := Fin.val_ne_of_ne hij
    rcases ( by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 ) with hi0 | hi1 | hi2 <;>
      rcases ( by omega : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 ) with hj0 | hj1 | hj2 <;>
      try omega
    · simp [P_fam, hi0, hj1, hd12]
    · simp [P_fam, hi0, hj2, hd13]
    · simp [P_fam, hi1, hj0, hd12.symm]
    · simp [P_fam, hi1, hj2, hd23]
    · simp [P_fam, hi2, hj0, hd13.symm]
    · simp [P_fam, hi2, hj1, hd23.symm]
  · intro i
    have hi : i.1 < 3 := hcard_s ▸ i.2
    rcases ( by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 ) with hi0 | hi1 | hi2
    · exact ⟨s₁, by simp, t₁, by simp, by simp [P_fam, hi0, hR₁]⟩
    · exact ⟨s₂, by simp, t₂, by simp, by simp [P_fam, hi1, hR₂]⟩
    · exact ⟨s₃, by simp, t₃, by simp, by simp [P_fam, hi2, hR₃]⟩

theorem disjoint_subpath_P_of_inter_singleton (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {a b i : ℕ} (hb : b < (pathWalkTS hP).support.length)
    (hi : i < (splitList S hs ht hP).length)
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a ≤ k ∧ k ≤ b ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)})
    {A : Set α}
    (hA : A ∩ {x | x ∈ splitList S hs ht hP} = {(splitList S hs ht hP)[i]'hi})
    (hni : ¬ (a ≤ i ∧ i ≤ b)) :
    Disjoint A V(Q) := by
  rw [disjoint_left]
  intro x hxA hxQ
  have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
    subpath_P_subset_splitList S hs ht hP hVQ hxQ
  have hx_in : x ∈ A ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxA, hxL⟩
  rw [hA, mem_singleton_iff] at hx_in
  subst hx_in
  exact hni ((mem_subpath_P_iff S hs ht hst hP hP_bar hb hVQ hi).mp hxQ)

theorem inter_subpath_P_eq_of_inter_singleton (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {a b i : ℕ} (hb : b < (pathWalkTS hP).support.length)
    (hi : i < (splitList S hs ht hP).length)
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a ≤ k ∧ k ≤ b ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)})
    {A : Set α}
    (hA : A ∩ {x | x ∈ splitList S hs ht hP} = {(splitList S hs ht hP)[i]'hi})
    (hi_in : a ≤ i ∧ i ≤ b) :
    V(Q) ∩ A = {(splitList S hs ht hP)[i]'hi} := by
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxQ, hxA⟩
    have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
      subpath_P_subset_splitList S hs ht hP hVQ hxQ
    have hx_in : x ∈ A ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxA, hxL⟩
    rwa [hA, mem_singleton_iff] at hx_in
  · rintro rfl
    have hiA : (splitList S hs ht hP)[i]'hi ∈ A ∩ {y | y ∈ splitList S hs ht hP} := by
      rw [hA]; simp
    exact ⟨(mem_subpath_P_iff S hs ht hst hP hP_bar hb hVQ hi).mpr hi_in, hiA.1⟩

theorem inter_subpath_P_subpath_P_eq_singleton (S : Society α β) {P Q₁ Q₂ : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hc : c < (pathWalkTS hP).support.length)
    (hVQ₁ : V(Q₁) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      a ≤ k ∧ k ≤ b ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)})
    (hVQ₂ : V(Q₂) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      b ≤ k ∧ k ≤ c ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)}) :
    V(Q₁) ∩ V(Q₂) =
      {(splitList S hs ht hP)[b]'(by rw [length_splitList]; omega)} := by
  have hbL : b < (splitList S hs ht hP).length := by rw [length_splitList]; omega
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx₁, hx₂⟩
    rw [hVQ₁, mem_ofPred_eq] at hx₁
    obtain ⟨k, hk, hak, hkb, rfl⟩ := hx₁
    have hkL : k < (splitList S hs ht hP).length := by rw [length_splitList]; omega
    have hk₂ := (mem_subpath_P_iff S hs ht hst hP hP_bar hc hVQ₂ hkL).mp hx₂
    have hkeq : k = b := by omega
    subst hkeq
    rfl
  · rintro rfl
    exact ⟨(mem_subpath_P_iff S hs ht hst hP hP_bar (by omega) hVQ₁ hbL).mpr ⟨hab, le_rfl⟩,
      (mem_subpath_P_iff S hs ht hst hP hP_bar hc hVQ₂ hbL).mpr ⟨le_rfl, hbc⟩⟩

theorem subpath_P_inter_bar_eq_t (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {i : ℕ} (hi : i < (pathWalkTS hP).support.length - 1)
    (hQ_le : Q ≤ P)
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      0 ≤ k ∧ k ≤ i ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)}) :
    V(Q) ∩ S.Ω.bar = {t} := by
  have hm2 : 2 ≤ (pathWalkTS hP).support.length := two_le_length_support_pathWalkTS hst hP
  have hi' : i < (pathWalkTS hP).support.length := by omega
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxQ, hx_bar⟩
    have hxP : x ∈ V(P) := hQ_le.vertexSet_mono hxQ
    by_cases hxt : x = t
    · exact hxt
    · by_cases hxs : x = s
      · subst hxs
        have hs_eq := (getElem_splitList_pred S hs ht hP).symm
        have hpredL : (pathWalkTS hP).support.length - 1 < (splitList S hs ht hP).length := by
          rw [length_splitList]; omega
        rw [hs_eq] at hxQ
        have hmem := (mem_subpath_P_iff S hs ht hst hP hP_bar hi' hVQ hpredL).mp hxQ
        omega
      · exact (disjoint_left.mp hP_bar ⟨hxP, by simp [hxs, hxt]⟩ hx_bar).elim
  · rintro rfl
    have h0L : 0 < (splitList S hs ht hP).length := by rw [length_splitList]; omega
    have htQ : x ∈ V(Q) := by
      rw [← getElem_splitList_zero S hs ht hP]
      exact (mem_subpath_P_iff S hs ht hst hP hP_bar hi' hVQ h0L).mpr ⟨le_rfl, Nat.zero_le i⟩
    exact ⟨htQ, ht⟩

theorem subpath_P_inter_bar_eq_s (S : Society α β) {P Q : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {j : ℕ} (hj0 : 0 < j) (hj : j ≤ (pathWalkTS hP).support.length - 1)
    (hQ_le : Q ≤ P)
    (hVQ : V(Q) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      j ≤ k ∧ k ≤ (pathWalkTS hP).support.length - 1 ∧
      x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)}) :
    V(Q) ∩ S.Ω.bar = {s} := by
  have hm2 : 2 ≤ (pathWalkTS hP).support.length := two_le_length_support_pathWalkTS hst hP
  have hpred : (pathWalkTS hP).support.length - 1 < (pathWalkTS hP).support.length := by omega
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxQ, hx_bar⟩
    have hxP : x ∈ V(P) := hQ_le.vertexSet_mono hxQ
    by_cases hxs : x = s
    · exact hxs
    · by_cases hxt : x = t
      · subst hxt
        have ht_eq := (getElem_splitList_zero S hs ht hP).symm
        have h0L : 0 < (splitList S hs ht hP).length := by rw [length_splitList]; omega
        rw [ht_eq] at hxQ
        have hmem := (mem_subpath_P_iff S hs ht hst hP hP_bar hpred hVQ h0L).mp hxQ
        omega
      · exact (disjoint_left.mp hP_bar ⟨hxP, by simp [hxs, hxt]⟩ hx_bar).elim
  · rintro rfl
    have hpredL : (pathWalkTS hP).support.length - 1 < (splitList S hs ht hP).length := by
      rw [length_splitList]; omega
    have hsQ : x ∈ V(Q) := by
      rw [← getElem_splitList_pred S hs ht hP]
      exact (mem_subpath_P_iff S hs ht hst hP hP_bar hpred hVQ hpredL).mpr ⟨hj, le_rfl⟩
    exact ⟨hsQ, hs⟩

theorem vertexSet_splitGraph_inter_bar_subset_splitList (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t) :
    V(splitGraph S P s t) ∩ S.Ω.bar ⊆ {x | x ∈ splitList S hs ht hP} := by
  rintro x ⟨hxG₁, hx_bar⟩
  rw [vertexSet_splitGraph, mem_sdiff] at hxG₁
  rw [mem_ofPred_eq, splitList, List.mem_append, S.Ω.mem_intervalList_iff hs ht hst]
  by_cases hxP : x ∈ V(P)
  · left
    rwa [vertexSet_eq_support_pathWalkTS hP, mem_ofPred_eq] at hxP
  · have hxs : x ≠ s := fun h => hxP (h ▸ hP.left_mem)
    have hxt : x ≠ t := fun h => hxP (h ▸ hP.right_mem)
    rcases S.Ω.mem_interval_or_interval_swap hs ht hx_bar hst hxs hxt with hxW₁ | hxW₂
    · exact Or.inr hxW₁
    · exact (hxG₁.2 (mem_vertexSet_splitSide_of_mem_W hxG₁.1 hxP hxW₂)).elim

private theorem no_reduced_cross_of_disjoint_spur (S : Society α β)
    {P P₁ P₂ P₃ P₁_a P₁_b : Graph α β} {s t u : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    {i₁ j₁ i₂ j₂ k : ℕ} :
    let m := (pathWalkTS hP).support.length
    let L := splitList S hs ht hP
    (hi₁ : i₁ < L.length) → (hj₁ : j₁ < L.length) →
    (hi₂ : i₂ < L.length) → (hj₂ : j₂ < L.length) → (hk : k < L.length) →
    i₁ < i₂ → i₂ < j₁ → j₁ < m → m ≤ j₂ → m ≤ k →
    (hP₁ : P₁ ≤ splitGraph S P s t) →
    IsGraphPathWithEnds (splitGraph S P s t) P₂ (L[i₂]'hi₂) (L[j₂]'hj₂) →
    IsGraphPathWithEnds P₁ P₁_a (L[i₁]'hi₁) u →
    IsGraphPathWithEnds P₁ P₁_b u (L[j₁]'hj₁) →
    P₁_a ≤ P₁ → P₁_b ≤ P₁ →
    IsGraphPathWithEnds (splitGraph S P s t) P₃ u (L[k]'hk) →
    V(P₃) ∩ V(P₁) = {u} →
    V(P₂) ∩ {x | x ∈ L} = {L[i₂]'hi₂, L[j₂]'hj₂} →
    V(P₃) ∩ {x | x ∈ L} = {L[k]'hk} →
    V(P₁_a) ∩ {x | x ∈ L} = {L[i₁]'hi₁} →
    V(P₁_b) ∩ {x | x ∈ L} = {L[j₁]'hj₁} →
    Disjoint V(P₁) V(P₂) → Disjoint V(P₃) V(P₂) → False := by
  intro m L hi₁ hj₁ hi₂ hj₂ hk h12 h21 hj₁m hmj₂ hmk hP₁ hP₂ hP₁a_path hP₁b_path
    hP₁a_le hP₁b_le hP₃_path hP₃_inter hP₂_L hP₃_L hP₁a_L hP₁b_L hdisj hdisj_P₃_P₂
  have hkj₂_ne : k ≠ j₂ := by
    intro h
    subst h
    exact disjoint_left.mp hdisj_P₃_P₂ hP₃_path.right_mem hP₂.right_mem
  have hP₁a_P₃ : V(P₁_a) ∩ V(P₃) = {u} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxPa, hxP₃⟩ => ?_, fun h => h ▸ ⟨hP₁a_path.right_mem, hP₃_path.left_mem⟩⟩
    have hx_in : x ∈ V(P₃) ∩ V(P₁) := ⟨hxP₃, hP₁a_le.vertexSet_mono hxPa⟩
    rwa [hP₃_inter, mem_singleton_iff] at hx_in
  have hP₁b_P₃ : V(P₁_b) ∩ V(P₃) = {u} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxPb, hxP₃⟩ => ?_, fun h => h ▸ ⟨hP₁b_path.left_mem, hP₃_path.left_mem⟩⟩
    have hx_in : x ∈ V(P₃) ∩ V(P₁) := ⟨hxP₃, hP₁b_le.vertexSet_mono hxPb⟩
    rwa [hP₃_inter, mem_singleton_iff] at hx_in
  rcases lt_or_gt_of_ne hkj₂_ne with hkj₂ | hj₂k
  · let P₁' := subgraphUnion (splitGraph S P s t) P₁_a P₃
    have hP₁'_path : IsGraphPathWithEnds (splitGraph S P s t) P₁' (L[i₁]'hi₁) (L[k]'hk) :=
      (hP₁a_path.mono hP₁).subgraphUnion hP₃_path hP₁a_P₃
    have hdisj' : Disjoint V(P₁') V(P₂) := by
      rw [vertexSet_subgraphUnion]
      exact Disjoint.union_left (hdisj.mono_left hP₁a_le.vertexSet_mono) hdisj_P₃_P₂
    have hP₁'_L : V(P₁') ∩ {x | x ∈ L} = {L[i₁]'hi₁, L[k]'hk} := by
      rw [vertexSet_subgraphUnion, union_inter_distrib_right, hP₁a_L, hP₃_L]
      ext x
      simp [L, or_comm]
    exact no_reduced_cross_of_two_in_W1 S hs ht hst hP hP_bar hnocross
      hi₁ hk hi₂ hj₂ h12 (by omega) hkj₂ hdisj' hP₁'_path hP₂ hP₁'_L hP₂_L hmk
  · let P₁'' := subgraphUnion (splitGraph S P s t) P₁_b P₃
    have hP₁''_path : IsGraphPathWithEnds (splitGraph S P s t) P₁'' (L[j₁]'hj₁) (L[k]'hk) :=
      (hP₁b_path.mono hP₁).symm.subgraphUnion hP₃_path hP₁b_P₃
    have hdisj'' : Disjoint V(P₂) V(P₁'') := by
      rw [vertexSet_subgraphUnion]
      exact Disjoint.union_right (hdisj.symm.mono_right hP₁b_le.vertexSet_mono) hdisj_P₃_P₂.symm
    have hP₁''_L : V(P₁'') ∩ {x | x ∈ L} = {L[j₁]'hj₁, L[k]'hk} := by
      rw [vertexSet_subgraphUnion, union_inter_distrib_right, hP₁b_L, hP₃_L]
      ext x
      simp [L, or_comm]
    exact no_reduced_cross_of_two_in_W1 S hs ht hst hP hP_bar hnocross
      hi₂ hj₂ hj₁ hk h21 (by omega) hj₂k hdisj'' hP₂ hP₁''_path hP₂_L hP₁''_L hmj₂

private theorem theta_paths_of_split_cross (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t) (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {P₁ P₂ P₁_a P₁_b P₂' P₃' Q_i₁_i₂ Q_i₂_j₁ : Graph α β} {u v : α}
    {i₁ j₁ i₂ j₂ : ℕ}
    (hi₁ : i₁ < (splitList S hs ht hP).length) (hj₁ : j₁ < (splitList S hs ht hP).length)
    (hi₂ : i₂ < (splitList S hs ht hP).length) (hj₂ : j₂ < (splitList S hs ht hP).length)
    (h12 : i₁ < i₂) (h21 : i₂ < j₁)
    (hj₁m : j₁ < (pathWalkTS hP).support.length)
    (hmj₂ : (pathWalkTS hP).support.length ≤ j₂)
    (hdisj : Disjoint V(P₁) V(P₂))
    (hinter_P₁ : V(P₁_a) ∩ V(P₁_b) = {u})
    (hP₁a_le : P₁_a ≤ P₁) (hP₁b_le : P₁_b ≤ P₁) (hP₂'_le : P₂' ≤ P₂)
    (hQ12_le : Q_i₁_i₂ ≤ P) (hQ21_le : Q_i₂_j₁ ≤ P)
    (hdisj_P₃'_P : Disjoint V(P₃') V(P))
    (hP₃'_ft : IsFromToPathWithEnds S.G P₃' V(P₁) V(P₂) u v) :
    let L := splitList S hs ht hP
    (V(P₁_a) ∩ {x | x ∈ L} = {L[i₁]'hi₁}) →
    (V(P₁_b) ∩ {x | x ∈ L} = {L[j₁]'hj₁}) →
    (V(P₂) ∩ {x | x ∈ L} = {L[i₂]'hi₂, L[j₂]'hj₂}) →
    IsGraphPathWithEnds S.G P₁_a (L[i₁]'hi₁) u →
    IsGraphPathWithEnds S.G P₁_b u (L[j₁]'hj₁) →
    IsGraphPathWithEnds S.G P₂' (L[i₂]'hi₂) v →
    IsGraphPathWithEnds S.G Q_i₁_i₂ (L[i₁]'hi₁) (L[i₂]'hi₂) →
    IsGraphPathWithEnds S.G Q_i₂_j₁ (L[i₂]'hi₂) (L[j₁]'hj₁) →
    (V(Q_i₁_i₂) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      i₁ ≤ k ∧ k ≤ i₂ ∧ x = L[k]'(by dsimp [L]; rw [length_splitList]; omega)}) →
    (V(Q_i₂_j₁) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      i₂ ≤ k ∧ k ≤ j₁ ∧ x = L[k]'(by dsimp [L]; rw [length_splitList]; omega)}) →
    let T₁ := subgraphUnion S.G P₁_a Q_i₁_i₂
    let T₂ := subgraphUnion S.G P₁_b Q_i₂_j₁
    let T₃ := subgraphUnion S.G P₃' P₂'
    IsGraphPathWithEnds S.G T₁ u (L[i₂]'hi₂) ∧
    IsGraphPathWithEnds S.G T₂ u (L[i₂]'hi₂) ∧
    IsGraphPathWithEnds S.G T₃ u (L[i₂]'hi₂) ∧
    V(T₁) ∩ V(T₂) = {u, L[i₂]'hi₂} ∧ V(T₁) ∩ V(T₃) = {u, L[i₂]'hi₂} ∧
    V(T₂) ∩ V(T₃) = {u, L[i₂]'hi₂} := by
  intro L hP₁a_L hP₁b_L hP₂_L hP₁a_path hP₁b_path hP₂'_path hQ12_path hQ21_path
    hVQ12 hVQ21 T₁ T₂ T₃
  have hP₁a_Q12 : V(P₁_a) ∩ V(Q_i₁_i₂) = {L[i₁]'hi₁} := by
    rw [inter_comm]
    exact inter_subpath_P_eq_of_inter_singleton S hs ht hst hP hP_bar (by omega) hi₁ hVQ12
      hP₁a_L ⟨le_rfl, by omega⟩
  have hP₁b_Q21 : V(P₁_b) ∩ V(Q_i₂_j₁) = {L[j₁]'hj₁} := by
    rw [inter_comm]
    exact inter_subpath_P_eq_of_inter_singleton S hs ht hst hP hP_bar hj₁m hj₁ hVQ21
      hP₁b_L ⟨by omega, le_rfl⟩
  have hP₃'_P₂' : V(P₃') ∩ V(P₂') = {v} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxP₃', hxP₂'⟩ => ?_, fun h => h ▸ ⟨hP₃'_ft.1.right_mem, hP₂'_path.right_mem⟩⟩
    have hx_in : x ∈ V(P₃') ∩ V(P₂) := ⟨hxP₃', hP₂'_le.vertexSet_mono hxP₂'⟩
    rwa [hP₃'_ft.2.2, mem_singleton_iff] at hx_in
  have hT₁_path : IsGraphPathWithEnds S.G T₁ u (L[i₂]'hi₂) :=
    hP₁a_path.symm.subgraphUnion hQ12_path hP₁a_Q12
  have hT₂_path : IsGraphPathWithEnds S.G T₂ u (L[i₂]'hi₂) :=
    hP₁b_path.subgraphUnion hQ21_path.symm hP₁b_Q21
  have hT₃_path : IsGraphPathWithEnds S.G T₃ u (L[i₂]'hi₂) :=
    hP₃'_ft.1.subgraphUnion hP₂'_path.symm hP₃'_P₂'
  -- Disjointness facts for the components of `T₁, T₂, T₃`.
  have hdisj_P₁a_Q21 : Disjoint V(P₁_a) V(Q_i₂_j₁) :=
    disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar hj₁m hi₁ hVQ21 hP₁a_L (by omega)
  have hdisj_P₁b_Q12 : Disjoint V(P₁_b) V(Q_i₁_i₂) :=
    disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar (by omega) hj₁ hVQ12 hP₁b_L
      (by omega)
  have hQ12_Q21 : V(Q_i₁_i₂) ∩ V(Q_i₂_j₁) = {L[i₂]'hi₂} :=
    inter_subpath_P_subpath_P_eq_singleton S hs ht hst hP hP_bar (by omega) (by omega) hj₁m
      hVQ12 hVQ21
  have hP₁a_P₃' : V(P₁_a) ∩ V(P₃') = {u} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxPa, hxP₃'⟩ => ?_, fun h => h ▸ ⟨hP₁a_path.right_mem, hP₃'_ft.1.left_mem⟩⟩
    have hx_in : x ∈ V(P₃') ∩ V(P₁) := ⟨hxP₃', hP₁a_le.vertexSet_mono hxPa⟩
    rwa [hP₃'_ft.2.1, mem_singleton_iff] at hx_in
  have hP₁b_P₃' : V(P₁_b) ∩ V(P₃') = {u} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxPb, hxP₃'⟩ => ?_, fun h => h ▸ ⟨hP₁b_path.left_mem, hP₃'_ft.1.left_mem⟩⟩
    have hx_in : x ∈ V(P₃') ∩ V(P₁) := ⟨hxP₃', hP₁b_le.vertexSet_mono hxPb⟩
    rwa [hP₃'_ft.2.1, mem_singleton_iff] at hx_in
  have hQ12_P₂' : V(Q_i₁_i₂) ∩ V(P₂') = {L[i₂]'hi₂} := by
    have hQ12_P₂ : V(Q_i₁_i₂) ∩ V(P₂) = {L[i₂]'hi₂} :=
      inter_subpath_P_eq_left_of_inter_pair S hs ht hst hP hP_bar (by omega) hi₂ hj₂ hVQ12 hP₂_L
        ⟨by omega, le_rfl⟩ (by omega)
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxQ, hxP₂'⟩ => ?_, fun h => h ▸ ⟨hQ12_path.right_mem, hP₂'_path.left_mem⟩⟩
    have hx_in : x ∈ V(Q_i₁_i₂) ∩ V(P₂) := ⟨hxQ, hP₂'_le.vertexSet_mono hxP₂'⟩
    rwa [hQ12_P₂, mem_singleton_iff] at hx_in
  have hQ21_P₂' : V(Q_i₂_j₁) ∩ V(P₂') = {L[i₂]'hi₂} := by
    have hQ21_P₂ : V(Q_i₂_j₁) ∩ V(P₂) = {L[i₂]'hi₂} :=
      inter_subpath_P_eq_left_of_inter_pair S hs ht hst hP hP_bar hj₁m hi₂ hj₂ hVQ21 hP₂_L
        ⟨le_rfl, by omega⟩ (by omega)
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxQ, hxP₂'⟩ => ?_, fun h => h ▸ ⟨hQ21_path.left_mem, hP₂'_path.left_mem⟩⟩
    have hx_in : x ∈ V(Q_i₂_j₁) ∩ V(P₂) := ⟨hxQ, hP₂'_le.vertexSet_mono hxP₂'⟩
    rwa [hQ21_P₂, mem_singleton_iff] at hx_in
  have hinter_T12 : V(T₁) ∩ V(T₂) = {u, L[i₂]'hi₂} := by
    simp only [T₁, T₂, vertexSet_subgraphUnion, union_inter_distrib_right,
      inter_union_distrib_left, hinter_P₁, Set.disjoint_iff_inter_eq_empty.mp hdisj_P₁a_Q21,
      Set.disjoint_iff_inter_eq_empty.mp hdisj_P₁b_Q12.symm, hQ12_Q21, union_empty, empty_union]
    rfl
  have hinter_T13 : V(T₁) ∩ V(T₃) = {u, L[i₂]'hi₂} := by
    have hPaP₂ : Disjoint V(P₁_a) V(P₂') := hdisj.mono
      hP₁a_le.vertexSet_mono hP₂'_le.vertexSet_mono
    have hQP₃ : Disjoint V(Q_i₁_i₂) V(P₃') := hdisj_P₃'_P.symm.mono_left hQ12_le.vertexSet_mono
    simp only [T₁, T₃, vertexSet_subgraphUnion, union_inter_distrib_right,
      inter_union_distrib_left, hP₁a_P₃', Set.disjoint_iff_inter_eq_empty.mp hPaP₂,
      Set.disjoint_iff_inter_eq_empty.mp hQP₃, hQ12_P₂', union_empty, empty_union]
    rfl
  have hinter_T23 : V(T₂) ∩ V(T₃) = {u, L[i₂]'hi₂} := by
    have hPbP₂ : Disjoint V(P₁_b) V(P₂') := hdisj.mono
      hP₁b_le.vertexSet_mono hP₂'_le.vertexSet_mono
    have hQP₃ : Disjoint V(Q_i₂_j₁) V(P₃') := hdisj_P₃'_P.symm.mono_left hQ21_le.vertexSet_mono
    simp only [T₂, T₃, vertexSet_subgraphUnion, union_inter_distrib_right,
      inter_union_distrib_left, hP₁b_P₃', Set.disjoint_iff_inter_eq_empty.mp hPbP₂,
      Set.disjoint_iff_inter_eq_empty.mp hQP₃, hQ21_P₂', union_empty, empty_union]
    rfl
  exact ⟨hT₁_path, hT₂_path, hT₃_path, hinter_T12, hinter_T13, hinter_T23⟩

/-- Case `r = 1` of `(2.4)` (`lemma_2_4_no_cross`): no reduced cross `(P₁, P₂)` in `(G₁, Ω₁)`
with indices `0 ≤ i₁ < i₂ < j₁ < j₂ < L.length` can have `j₁ < m ≤ j₂`. -/
theorem no_reduced_cross_of_one_in_W1 (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t) (hP_ind : P ≤i S.G)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃)
    {P₁ P₂ : Graph α β} {i₁ j₁ i₂ j₂ : ℕ}
    (hi₁ : i₁ < (splitList S hs ht hP).length)
    (hj₁ : j₁ < (splitList S hs ht hP).length)
    (hi₂ : i₂ < (splitList S hs ht hP).length)
    (hj₂ : j₂ < (splitList S hs ht hP).length)
    (h12 : i₁ < i₂) (h21 : i₂ < j₁)
    (hdisj : Disjoint V(P₁) V(P₂))
    (hP₁ : IsGraphPathWithEnds (splitGraph S P s t) P₁
      ((splitList S hs ht hP)[i₁]'hi₁) ((splitList S hs ht hP)[j₁]'hj₁))
    (hP₂ : IsGraphPathWithEnds (splitGraph S P s t) P₂
      ((splitList S hs ht hP)[i₂]'hi₂) ((splitList S hs ht hP)[j₂]'hj₂))
    (hP₁_L : V(P₁) ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i₁]'hi₁, (splitList S hs ht hP)[j₁]'hj₁})
    (hP₂_L : V(P₂) ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i₂]'hi₂, (splitList S hs ht hP)[j₂]'hj₂})
    (hj₁m : j₁ < (pathWalkTS hP).support.length)
    (hmj₂ : (pathWalkTS hP).support.length ≤ j₂) :
    False := by
  let m := (pathWalkTS hP).support.length
  let L := splitList S hs ht hP
  have hnd := nodup_splitList S hs ht hst hP hP_bar
  have hij₁_ne : L[i₁]'hi₁ ≠ L[j₁]'hj₁ := fun h => by
    have := nodup_getElem_inj hnd hi₁ hj₁ h; omega
  obtain ⟨u₀, hu₀P₁, hu₀H₁⟩ :=
    exists_vertex_in_splitSide_of_path_in_splitGraph S hs ht hst hP hP_ind hcatch hnocross
      hP₁ hij₁_ne
  obtain ⟨u, huP₁, k, hk, P₃, hP₃H₁, hmk, hdisj_P₃_P, hP₃_ft, hP₃_L, _⟩ :=
    exists_fromToPath_in_splitSide S hs ht hst hP hnocross hu₀P₁ hu₀H₁
  have hu_not_P : u ∉ V(P) := disjoint_left.mp hdisj_P₃_P hP₃_ft.1.left_mem
  have hi₁P : L[i₁]'hi₁ ∈ V(P) :=
    (getElem_splitList_mem_P_iff S hs ht hst hP hP_bar hi₁).mpr (by omega)
  have hj₁P : L[j₁]'hj₁ ∈ V(P) :=
    (getElem_splitList_mem_P_iff S hs ht hst hP hP_bar hj₁).mpr hj₁m
  have hi₂P : L[i₂]'hi₂ ∈ V(P) :=
    (getElem_splitList_mem_P_iff S hs ht hst hP hP_bar hi₂).mpr (by omega)
  have hu_ne_i₁ : u ≠ L[i₁]'hi₁ := fun h => hu_not_P (h ▸ hi₁P)
  have hu_ne_j₁ : u ≠ L[j₁]'hj₁ := fun h => hu_not_P (h ▸ hj₁P)
  obtain ⟨P₁_a, P₁_b, hP₁a_le, hP₁b_le, hP₁a_path, hP₁b_path, hunion_P₁, hinter_P₁, _⟩ :=
    hP₁.exists_split_at huP₁
  have hP₁a_V : V(P₁_a) ∪ V(P₁_b) = V(P₁) := by
    rw [← vertexSet_subgraphUnion P₁ P₁_a P₁_b, hunion_P₁]
  have hP₁a_L : V(P₁_a) ∩ {x | x ∈ L} = {L[i₁]'hi₁} :=
    inter_left_of_split hP₁a_le hinter_P₁ hP₁a_path.left_mem hP₁b_path.right_mem hu_ne_j₁ hP₁_L
  have hP₁b_L : V(P₁_b) ∩ {x | x ∈ L} = {L[j₁]'hj₁} :=
    inter_right_of_split hP₁b_le hinter_P₁ hP₁a_path.left_mem hP₁b_path.right_mem hu_ne_i₁ hP₁_L
  by_cases hdisj_P₃_P₂ : Disjoint V(P₃) V(P₂)
  · exact no_reduced_cross_of_disjoint_spur S hs ht hst hP hP_bar hnocross
      hi₁ hj₁ hi₂ hj₂ hk h12 h21 hj₁m hmj₂ hmk hP₁.le hP₂ hP₁a_path hP₁b_path
      hP₁a_le hP₁b_le hP₃_ft.1 hP₃_ft.2.1 hP₂_L hP₃_L hP₁a_L hP₁b_L hdisj hdisj_P₃_P₂
  · -- Subcase 2b: `P₃` meets `P₂`; construct a tripod in `(G, Ω)`.
    rw [not_disjoint_iff] at hdisj_P₃_P₂
    obtain ⟨z₀, hz₀P₃, hz₀P₂⟩ := hdisj_P₃_P₂
    obtain ⟨P₃_a, _, hP₃a_le, _, hP₃a_path, _, _, _, _⟩ := hP₃_ft.1.exists_split_at hz₀P₃
    obtain ⟨u', hu'P₁, v, hvP₂, P₃', hP₃'_le_a, hP₃'_ft⟩ :=
      (hP₃a_path.mono (hP₃_ft.1.le.trans (splitGraph_le S P s t))).exists_isFromToPathWithEnds
        huP₁ hz₀P₂
    have hP₃'_le : P₃' ≤ P₃ := hP₃'_le_a.trans hP₃a_le
    have hu'_eq : u = u' := by
      have : u' ∈ V(P₃) ∩ V(P₁) := ⟨hP₃'_le.vertexSet_mono hP₃'_ft.1.left_mem, hu'P₁⟩
      rw [hP₃_ft.2.1, mem_singleton_iff] at this
      exact this.symm
    subst hu'_eq
    have hdisj_P₃'_P : Disjoint V(P₃') V(P) :=
      hdisj_P₃_P.mono_left hP₃'_le.vertexSet_mono
    have hv_not_P : v ∉ V(P) := disjoint_left.mp hdisj_P₃'_P hP₃'_ft.1.right_mem
    have hv_ne_i₂ : v ≠ L[i₂]'hi₂ := fun h => hv_not_P (h ▸ hi₂P)
    have hP₁G : IsGraphPathWithEnds S.G P₁ (L[i₁]'hi₁) (L[j₁]'hj₁) :=
      hP₁.mono (splitGraph_le S P s t)
    have hP₂G : IsGraphPathWithEnds S.G P₂ (L[i₂]'hi₂) (L[j₂]'hj₂) :=
      hP₂.mono (splitGraph_le S P s t)
    obtain ⟨P₂', P₂'', hP₂'_le, hP₂''_le, hP₂'_path, hP₂''_path, hunion_P₂, hinter_P₂, _⟩ :=
      hP₂G.exists_split_at hvP₂
    have hP₂_V : V(P₂') ∪ V(P₂'') = V(P₂) := by
      rw [← vertexSet_subgraphUnion P₂ P₂' P₂'', hunion_P₂]
    have hP₂''_L : V(P₂'') ∩ {x | x ∈ L} = {L[j₂]'hj₂} :=
      inter_right_of_split hP₂''_le hinter_P₂ hP₂'_path.left_mem hP₂''_path.right_mem hv_ne_i₂ hP₂_L
    -- Four subpaths of `P` along `[0, i₁]`, `[i₁, i₂]`, `[i₂, j₁]`, `[j₁, m - 1]`.
    have hm2 : 2 ≤ m := two_le_length_support_pathWalkTS hst hP
    have hm_pred : m - 1 < m := by omega
    obtain ⟨Q_0_i₁, hQ0_le, hQ0_path, hVQ0⟩ :=
      exists_subpath_P_of_splitList_indices S hs ht hP (Nat.zero_le i₁) (by omega)
    obtain ⟨Q_i₁_i₂, hQ12_le, hQ12_path, hVQ12⟩ :=
      exists_subpath_P_of_splitList_indices S hs ht hP (by omega : i₁ ≤ i₂) (by omega)
    obtain ⟨Q_i₂_j₁, hQ21_le, hQ21_path, hVQ21⟩ :=
      exists_subpath_P_of_splitList_indices S hs ht hP (by omega : i₂ ≤ j₁) hj₁m
    obtain ⟨Q_j₁_m, hQjm_le, hQjm_path, hVQjm⟩ :=
      exists_subpath_P_of_splitList_indices S hs ht hP (by omega : j₁ ≤ m - 1) hm_pred
    -- Build the three theta paths `T₁, T₂, T₃` between `u` and `L[i₂]`.
    let T₁ := subgraphUnion S.G P₁_a Q_i₁_i₂
    let T₂ := subgraphUnion S.G P₁_b Q_i₂_j₁
    let T₃ := subgraphUnion S.G P₃' P₂'
    obtain ⟨hT₁_path, hT₂_path, hT₃_path, hinter_T12, hinter_T13, hinter_T23⟩ :=
      theta_paths_of_split_cross S hs ht hst hP hP_bar hi₁ hj₁ hi₂ hj₂ h12 h21 hj₁m hmj₂
        hdisj hinter_P₁ hP₁a_le hP₁b_le hP₂'_le hQ12_le hQ21_le hdisj_P₃'_P hP₃'_ft
        hP₁a_L hP₁b_L hP₂_L (hP₁a_path.mono hP₁G.le) (hP₁b_path.mono hP₁G.le)
        (hP₂'_path.mono hP₂G.le) hQ12_path hQ21_path hVQ12 hVQ21
    have hu_ne_i₂ : u ≠ L[i₂]'hi₂ := fun h => hu_not_P (h ▸ hi₂P)
    -- Internal vertices `L[i₁] ∈ V(T₁) \ {u, L[i₂]}`, `L[j₁] ∈ V(T₂) \ {u, L[i₂]}`,
    -- `v ∈ V(T₃) \ {u, L[i₂]}`.
    have hs₁_int : L[i₁]'hi₁ ∈ V(T₁) \ {u, L[i₂]'hi₂} := by
      refine ⟨Or.inl hP₁a_path.left_mem, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hu_ne_i₁.symm, fun h => by have := nodup_getElem_inj hnd hi₁ hi₂ h; omega⟩
    have hs₂_int : L[j₁]'hj₁ ∈ V(T₂) \ {u, L[i₂]'hi₂} := by
      refine ⟨Or.inl hP₁b_path.right_mem, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hu_ne_j₁.symm, fun h => by have := nodup_getElem_inj hnd hj₁ hi₂ h; omega⟩
    have hs₃_int : v ∈ V(T₃) \ {u, L[i₂]'hi₂} := by
      refine ⟨Or.inl hP₃'_ft.1.right_mem, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun h => disjoint_left.mp hdisj huP₁ (h ▸ hvP₂), hv_ne_i₂⟩
    -- Three legs `Q_0_i₁` (`L[i₁] → t`), `Q_j₁_m` (`L[j₁] → s`), `P₂''` (`v → L[j₂]`).
    let X_T := V(T₁) ∪ V(T₂) ∪ V(T₃)
    have hR₁_path : IsGraphPathWithEnds S.G Q_0_i₁ (L[i₁]'hi₁) t := by
      have h := hQ0_path.symm
      rwa [getElem_splitList_zero S hs ht hP] at h
    have hR₂_path : IsGraphPathWithEnds S.G Q_j₁_m (L[j₁]'hj₁) s := by
      have h := hQjm_path
      rwa [getElem_splitList_pred S hs ht hP] at h
    have hR₃_path : IsGraphPathWithEnds S.G P₂'' v (L[j₂]'hj₂) :=
      hP₂''_path.mono hP₂G.le
    have hQ0_bar : V(Q_0_i₁) ∩ S.Ω.bar = {t} :=
      subpath_P_inter_bar_eq_t S hs ht hst hP hP_bar (by omega) hQ0_le hVQ0
    have hQjm_bar : V(Q_j₁_m) ∩ S.Ω.bar = {s} :=
      subpath_P_inter_bar_eq_s S hs ht hst hP hP_bar (by omega) (by omega) hQjm_le hVQjm
    have hj₂_bar : L[j₂]'hj₂ ∈ S.Ω.bar :=
      ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hj₂).mpr hmj₂).1.1
    have hP₂''_bar : V(P₂'') ∩ S.Ω.bar = {L[j₂]'hj₂} := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hxP₂'', hx_bar⟩ => ?_, fun h => h ▸ ⟨hP₂''_path.right_mem, hj₂_bar⟩⟩
      have hxG₁ : x ∈ V(splitGraph S P s t) :=
        hP₂.le.vertexSet_mono (hP₂''_le.vertexSet_mono hxP₂'')
      have hxL : x ∈ {y | y ∈ L} :=
        vertexSet_splitGraph_inter_bar_subset_splitList S hs ht hst hP ⟨hxG₁, hx_bar⟩
      have hx_in : x ∈ V(P₂'') ∩ {y | y ∈ L} := ⟨hxP₂'', hxL⟩
      rwa [hP₂''_L, mem_singleton_iff] at hx_in
    -- Intersections of `Q_0_i₁`, `Q_j₁_m`, `P₂''` with `X_T`.
    have hQ0_P₁a : V(Q_0_i₁) ∩ V(P₁_a) = {L[i₁]'hi₁} :=
      inter_subpath_P_eq_of_inter_singleton S hs ht hst hP hP_bar (by omega) hi₁ hVQ0
        hP₁a_L ⟨Nat.zero_le i₁, le_rfl⟩
    have hQ0_Q12 : V(Q_0_i₁) ∩ V(Q_i₁_i₂) = {L[i₁]'hi₁} :=
      inter_subpath_P_subpath_P_eq_singleton S hs ht hst hP hP_bar (Nat.zero_le i₁)
        (by omega) (by omega) hVQ0 hVQ12
    have hdisj_Q0_P₁b : Disjoint V(P₁_b) V(Q_0_i₁) :=
      disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar (by omega) hj₁ hVQ0 hP₁b_L
        (by omega)
    have hdisj_Q0_Q21 : Disjoint V(Q_0_i₁) V(Q_i₂_j₁) :=
      disjoint_subpath_P_subpath_P S hs ht hst hP hP_bar hj₁m h12 hVQ0 hVQ21
    have hdisj_Q0_P₂ : Disjoint V(P₂) V(Q_0_i₁) :=
      disjoint_subpath_P_of_inter_pair S hs ht hst hP hP_bar (by omega) hi₂ hj₂ hVQ0 hP₂_L
        (by omega) (by omega)
    have hQ0_XT : V(Q_0_i₁) ∩ X_T = {L[i₁]'hi₁} := by
      have hQ0P₃ : Disjoint V(Q_0_i₁) V(P₃') := hdisj_P₃'_P.symm.mono_left hQ0_le.vertexSet_mono
      have hQ0P₂ : Disjoint V(Q_0_i₁) V(P₂') := hdisj_Q0_P₂.symm.mono_right hP₂'_le.vertexSet_mono
      simp [X_T, T₁, T₂, T₃, vertexSet_subgraphUnion, inter_union_distrib_left, hQ0_P₁a, hQ0_Q12,
        Set.disjoint_iff_inter_eq_empty.mp hdisj_Q0_P₁b.symm,
        Set.disjoint_iff_inter_eq_empty.mp hdisj_Q0_Q21,
        Set.disjoint_iff_inter_eq_empty.mp hQ0P₃, Set.disjoint_iff_inter_eq_empty.mp hQ0P₂]
    have hdisj_Qjm_P₁a : Disjoint V(P₁_a) V(Q_j₁_m) :=
      disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar hm_pred hi₁ hVQjm hP₁a_L
        (by omega)
    have hdisj_Qjm_Q12 : Disjoint V(Q_i₁_i₂) V(Q_j₁_m) :=
      disjoint_subpath_P_subpath_P S hs ht hst hP hP_bar hm_pred h21 hVQ12 hVQjm
    have hQjm_P₁b : V(Q_j₁_m) ∩ V(P₁_b) = {L[j₁]'hj₁} :=
      inter_subpath_P_eq_of_inter_singleton S hs ht hst hP hP_bar hm_pred hj₁ hVQjm hP₁b_L
        ⟨le_rfl, by omega⟩
    have hQ21_Qjm : V(Q_i₂_j₁) ∩ V(Q_j₁_m) = {L[j₁]'hj₁} :=
      inter_subpath_P_subpath_P_eq_singleton S hs ht hst hP hP_bar (by omega) (by omega) hm_pred
        hVQ21 hVQjm
    have hdisj_Qjm_P₂ : Disjoint V(P₂) V(Q_j₁_m) :=
      disjoint_subpath_P_of_inter_pair S hs ht hst hP hP_bar hm_pred hi₂ hj₂ hVQjm hP₂_L
        (by omega) (by omega)
    have hQjm_XT : V(Q_j₁_m) ∩ X_T = {L[j₁]'hj₁} := by
      have hQjmP₃ : Disjoint V(Q_j₁_m) V(P₃') := hdisj_P₃'_P.symm.mono_left hQjm_le.vertexSet_mono
      have hQjmP₂ : Disjoint V(Q_j₁_m) V(P₂') := hdisj_Qjm_P₂.symm.mono_right hP₂'_le.vertexSet_mono
      simp [X_T, T₁, T₂, T₃, vertexSet_subgraphUnion, inter_union_distrib_left, hQjm_P₁b,
        (inter_comm V(Q_j₁_m) V(Q_i₂_j₁)).trans hQ21_Qjm,
        Set.disjoint_iff_inter_eq_empty.mp hdisj_Qjm_P₁a.symm,
        Set.disjoint_iff_inter_eq_empty.mp hdisj_Qjm_Q12.symm,
        Set.disjoint_iff_inter_eq_empty.mp hQjmP₃, Set.disjoint_iff_inter_eq_empty.mp hQjmP₂]
    have hdisj_P₂''_Q12 : Disjoint V(P₂'') V(Q_i₁_i₂) :=
      disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar (by omega) hj₂ hVQ12 hP₂''_L
        (by omega)
    have hdisj_P₂''_Q21 : Disjoint V(P₂'') V(Q_i₂_j₁) :=
      disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar hj₁m hj₂ hVQ21 hP₂''_L
        (by omega)
    have hP₂''_XT : V(P₂'') ∩ X_T = {v} := by
      have hPa : Disjoint V(P₂'') V(P₁_a) := hdisj.symm.mono
        hP₂''_le.vertexSet_mono hP₁a_le.vertexSet_mono
      have hPb : Disjoint V(P₂'') V(P₁_b) := hdisj.symm.mono
        hP₂''_le.vertexSet_mono hP₁b_le.vertexSet_mono
      have hP₃ : V(P₂'') ∩ V(P₃') = {v} := by
        apply subset_antisymm
        · rintro x ⟨hx, hx'⟩
          exact hP₃'_ft.2.2.subset ⟨hx', hP₂''_le.vertexSet_mono hx⟩
        · rintro _ rfl
          exact ⟨hP₂''_path.left_mem, hP₃'_ft.1.right_mem⟩
      simp [X_T, T₁, T₂, T₃, vertexSet_subgraphUnion, inter_union_distrib_left, hP₃,
        (inter_comm V(P₂'') V(P₂')).trans hinter_P₂,
        Set.disjoint_iff_inter_eq_empty.mp hPa, Set.disjoint_iff_inter_eq_empty.mp hPb,
        Set.disjoint_iff_inter_eq_empty.mp hdisj_P₂''_Q12,
        Set.disjoint_iff_inter_eq_empty.mp hdisj_P₂''_Q21]
    have hd_R12 : Disjoint V(Q_0_i₁) V(Q_j₁_m) :=
      disjoint_subpath_P_subpath_P S hs ht hst hP hP_bar hm_pred (by omega) hVQ0 hVQjm
    have hd_R13 : Disjoint V(Q_0_i₁) V(P₂'') :=
      hdisj_Q0_P₂.symm.mono_right hP₂''_le.vertexSet_mono
    have hd_R23 : Disjoint V(Q_j₁_m) V(P₂'') :=
      hdisj_Qjm_P₂.symm.mono_right hP₂''_le.vertexSet_mono
    have hs12_ne : L[i₁]'hi₁ ≠ L[j₁]'hj₁ := hij₁_ne
    have hs13_ne : L[i₁]'hi₁ ≠ v := fun h => hv_not_P (h ▸ hi₁P)
    have hs23_ne : L[j₁]'hj₁ ≠ v := fun h => hv_not_P (h ▸ hj₁P)
    have hred : RedirectsTo S.G X_T S.Ω.bar {L[i₁]'hi₁, L[j₁]'hj₁, v} {t, s, L[j₂]'hj₂} :=
      redirectsTo_of_three_disjoint_paths
        (Or.inl (Or.inl hs₁_int.1)) (Or.inl (Or.inr hs₂_int.1)) (Or.inr hs₃_int.1)
        ht hs hj₂_bar hs12_ne hs13_ne hs23_ne
        ⟨hR₁_path, hQ0_XT, hQ0_bar⟩ ⟨hR₂_path, hQjm_XT, hQjm_bar⟩ ⟨hR₃_path, hP₂''_XT, hP₂''_bar⟩
        hd_R12 hd_R13 hd_R23
    exact hnotripod ⟨T₁, T₂, T₃, u, L[i₂]'hi₂, hu_ne_i₂, hT₁_path, hT₂_path, hT₃_path,
      hinter_T12, hinter_T13, hinter_T23,
      L[i₁]'hi₁, hs₁_int, L[j₁]'hj₁, hs₂_int, v, hs₃_int,
      t, ht, s, hs, L[j₂]'hj₂, hj₂_bar, hred⟩

/-- Case `r = 0` of `(2.4)` (`lemma_2_4_no_cross`): no reduced cross `(P₁, P₂)` in `(G₁, Ω₁)`
with indices `0 ≤ i₁ < i₂ < j₁ < j₂ < L.length` can have `j₂ < m`. -/
theorem no_reduced_cross_of_zero_in_W1 (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t) (hP_ind : P ≤i S.G)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃)
    {P₁ P₂ : Graph α β} {i₁ j₁ i₂ j₂ : ℕ}
    (hi₁ : i₁ < (splitList S hs ht hP).length)
    (hj₁ : j₁ < (splitList S hs ht hP).length)
    (hi₂ : i₂ < (splitList S hs ht hP).length)
    (hj₂ : j₂ < (splitList S hs ht hP).length)
    (h12 : i₁ < i₂) (h21 : i₂ < j₁) (h12' : j₁ < j₂)
    (hdisj : Disjoint V(P₁) V(P₂))
    (hP₁ : IsGraphPathWithEnds (splitGraph S P s t) P₁
      ((splitList S hs ht hP)[i₁]'hi₁) ((splitList S hs ht hP)[j₁]'hj₁))
    (hP₂ : IsGraphPathWithEnds (splitGraph S P s t) P₂
      ((splitList S hs ht hP)[i₂]'hi₂) ((splitList S hs ht hP)[j₂]'hj₂))
    (hP₁_L : V(P₁) ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i₁]'hi₁, (splitList S hs ht hP)[j₁]'hj₁})
    (hP₂_L : V(P₂) ∩ {x | x ∈ splitList S hs ht hP} =
      {(splitList S hs ht hP)[i₂]'hi₂, (splitList S hs ht hP)[j₂]'hj₂})
    (hj₂m : j₂ < (pathWalkTS hP).support.length) :
    False := by
  let L := splitList S hs ht hP
  have hnd := nodup_splitList S hs ht hst hP hP_bar
  have hij₁_ne : L[i₁]'hi₁ ≠ L[j₁]'hj₁ := fun h => by
    have := nodup_getElem_inj hnd hi₁ hj₁ h; omega
  obtain ⟨u₀, hu₀P₁, hu₀H₁⟩ :=
    exists_vertex_in_splitSide_of_path_in_splitGraph S hs ht hst hP hP_ind hcatch hnocross
      hP₁ hij₁_ne
  obtain ⟨u, hu_union, k, hk, P₃, _, hmk, hdisj_P₃_P, hP₃_ft, hP₃_L, _⟩ :=
    exists_fromToPath_in_splitSide S hs ht hst hP hnocross
      (X := V(P₁) ∪ V(P₂)) (Or.inl hu₀P₁) hu₀H₁
  have hu_not_P : u ∉ V(P) := disjoint_left.mp hdisj_P₃_P hP₃_ft.1.left_mem
  rcases hu_union with huP₁ | huP₂
  · -- `u ∈ V(P₁)`: replace `L[i₁]` by `L[k]` (using `P₁_b ∪ P₃`) and contradict
    -- `no_reduced_cross_of_one_in_W1`.
    have hi₁P : L[i₁]'hi₁ ∈ V(P) :=
      (getElem_splitList_mem_P_iff S hs ht hst hP hP_bar hi₁).mpr (by omega)
    have hu_ne_i₁ : u ≠ L[i₁]'hi₁ := fun h => hu_not_P (h ▸ hi₁P)
    obtain ⟨P₁_a, P₁_b, _, hP₁b_le, hP₁a_path, hP₁b_path, _, hinter_P₁, _⟩ :=
      hP₁.exists_split_at huP₁
    have hP₁b_L : V(P₁_b) ∩ {x | x ∈ L} = {L[j₁]'hj₁} :=
      inter_right_of_split hP₁b_le hinter_P₁ hP₁a_path.left_mem hP₁b_path.right_mem hu_ne_i₁ hP₁_L
    have hP₁b_P₃ : V(P₁_b) ∩ V(P₃) = {u} := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hxPb, hxP₃⟩ => ?_, fun h => h ▸ ⟨hP₁b_path.left_mem, hP₃_ft.1.left_mem⟩⟩
      have hx_in : x ∈ V(P₃) ∩ (V(P₁) ∪ V(P₂)) := ⟨hxP₃, Or.inl (hP₁b_le.vertexSet_mono hxPb)⟩
      rwa [hP₃_ft.2.1, mem_singleton_iff] at hx_in
    have hdisj_P₃_P₂ : Disjoint V(P₃) V(P₂) := by
      rw [disjoint_left]
      intro x hxP₃ hxP₂
      have hx_in : x ∈ V(P₃) ∩ (V(P₁) ∪ V(P₂)) := ⟨hxP₃, Or.inr hxP₂⟩
      rw [hP₃_ft.2.1, mem_singleton_iff] at hx_in
      subst hx_in
      exact disjoint_left.mp hdisj huP₁ hxP₂
    let P₁' := subgraphUnion (splitGraph S P s t) P₁_b P₃
    have hP₁'_path : IsGraphPathWithEnds (splitGraph S P s t) P₁' (L[j₁]'hj₁) (L[k]'hk) :=
      (hP₁b_path.mono hP₁.le).symm.subgraphUnion hP₃_ft.1 hP₁b_P₃
    have hdisj' : Disjoint V(P₂) V(P₁') := by
      rw [vertexSet_subgraphUnion]
      exact Disjoint.union_right (hdisj.symm.mono_right hP₁b_le.vertexSet_mono) hdisj_P₃_P₂.symm
    have hP₁'_L : V(P₁') ∩ {x | x ∈ L} = {L[j₁]'hj₁, L[k]'hk} := by
      rw [vertexSet_subgraphUnion, union_inter_distrib_right, hP₁b_L, hP₃_L]
      ext x
      simp [L, or_comm]
    exact no_reduced_cross_of_one_in_W1 S hs ht hst hP hP_ind hP_bar hcatch hnocross hnotripod
      hi₂ hj₂ hj₁ hk h21 h12' hdisj' hP₂ hP₁'_path hP₂_L hP₁'_L hj₂m hmk
  · -- `u ∈ V(P₂)`: replace `L[j₂]` by `L[k]` and contradict `no_reduced_cross_of_one_in_W1`.
    have hj₂P : L[j₂]'hj₂ ∈ V(P) :=
      (getElem_splitList_mem_P_iff S hs ht hst hP hP_bar hj₂).mpr hj₂m
    have hu_ne_j₂ : u ≠ L[j₂]'hj₂ := fun h => hu_not_P (h ▸ hj₂P)
    obtain ⟨P₂_a, P₂_b, hP₂a_le, _, hP₂a_path, hP₂b_path, _, hinter_P₂, _⟩ :=
      hP₂.exists_split_at huP₂
    have hP₂a_L : V(P₂_a) ∩ {x | x ∈ L} = {L[i₂]'hi₂} :=
      inter_left_of_split hP₂a_le hinter_P₂ hP₂a_path.left_mem hP₂b_path.right_mem hu_ne_j₂ hP₂_L
    have hP₂a_P₃ : V(P₂_a) ∩ V(P₃) = {u} := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hxPa, hxP₃⟩ => ?_, fun h => h ▸ ⟨hP₂a_path.right_mem, hP₃_ft.1.left_mem⟩⟩
      have hx_in : x ∈ V(P₃) ∩ (V(P₁) ∪ V(P₂)) := ⟨hxP₃, Or.inr (hP₂a_le.vertexSet_mono hxPa)⟩
      rwa [hP₃_ft.2.1, mem_singleton_iff] at hx_in
    have hdisj_P₁_P₃ : Disjoint V(P₁) V(P₃) := by
      rw [disjoint_left]
      intro x hxP₁ hxP₃
      have hx_in : x ∈ V(P₃) ∩ (V(P₁) ∪ V(P₂)) := ⟨hxP₃, Or.inl hxP₁⟩
      rw [hP₃_ft.2.1, mem_singleton_iff] at hx_in
      subst hx_in
      exact disjoint_left.mp hdisj hxP₁ huP₂
    let P₂' := subgraphUnion (splitGraph S P s t) P₂_a P₃
    have hP₂'_path : IsGraphPathWithEnds (splitGraph S P s t) P₂' (L[i₂]'hi₂) (L[k]'hk) :=
      (hP₂a_path.mono hP₂.le).subgraphUnion hP₃_ft.1 hP₂a_P₃
    have hdisj' : Disjoint V(P₁) V(P₂') := by
      rw [vertexSet_subgraphUnion]
      exact Disjoint.union_right (hdisj.mono_right hP₂a_le.vertexSet_mono) hdisj_P₁_P₃
    have hP₂'_L : V(P₂') ∩ {x | x ∈ L} = {L[i₂]'hi₂, L[k]'hk} := by
      rw [vertexSet_subgraphUnion, union_inter_distrib_right, hP₂a_L, hP₃_L]
      ext x
      simp [L, or_comm]
    exact no_reduced_cross_of_one_in_W1 S hs ht hst hP hP_ind hP_bar hcatch hnocross hnotripod
      hi₁ hj₁ hi₂ hk h12 h21 hdisj' hP₁ hP₂'_path hP₁_L hP₂'_L (by omega) hmk

/-- **Graph Minors IX, (2.4)** (page 46):
"We claim also that $(G_1, \Omega_1)$ has no cross." -/
theorem lemma_2_4_no_cross (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t) (hP_ind : P ≤i S.G)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃) :
    ¬ ∃ Q₁ Q₂ : Graph α β, (splitSociety S hs ht hst hP hP_bar hnocross).IsCross Q₁ Q₂ := by
  rintro ⟨Q₁, Q₂, hcross⟩
  obtain ⟨P₁, P₂, i₁, j₁, i₂, j₂, hi₁, hj₁, hi₂, hj₂,
      h12, h21, h12', hdisj, hP₁, hP₂, hP₁_L, hP₂_L⟩ :=
    exists_ordered_reduced_cross_of_ofNodupList
      (nodup_splitList S hs ht hst hP hP_bar) (splitList_ne_nil S hs ht hP)
      rfl rfl hcross
  let m := (pathWalkTS hP).support.length
  by_cases hmj₁ : m ≤ j₁
  · exact no_reduced_cross_of_two_in_W1 S hs ht hst hP hP_bar hnocross
      hi₁ hj₁ hi₂ hj₂ h12 h21 h12' hdisj hP₁ hP₂ hP₁_L hP₂_L hmj₁
  · by_cases hmj₂ : m ≤ j₂
    · exact no_reduced_cross_of_one_in_W1 S hs ht hst hP hP_ind hP_bar hcatch hnocross hnotripod
        hi₁ hj₁ hi₂ hj₂ h12 h21 hdisj hP₁ hP₂ hP₁_L hP₂_L (Nat.lt_of_not_ge hmj₁) hmj₂
    · exact no_reduced_cross_of_zero_in_W1 S hs ht hst hP hP_ind hP_bar hcatch hnocross hnotripod
        hi₁ hj₁ hi₂ hj₂ h12 h21 h12' hdisj hP₁ hP₂ hP₁_L hP₂_L (Nat.lt_of_not_ge hmj₂)

/-! ## Showing `(G₁, Ω₁)` Has No Tripod (`lemma_2_4_no_tripod`) -/

/-- Every walk `W` in `G` from `a ∈ V(A₁)` to `b ∈ V(A₂)` across a separation `(A₁, A₂)` of `G`
contains a vertex of `V(A₁) ∩ V(A₂)`. -/
theorem exists_mem_inter_of_isGraphSeparation_of_walk {G A₁ A₂ : Graph α β}
    (hsep : IsGraphSeparation G A₁ A₂) {a b : α} (W : GraphWalk G a b)
    (ha : a ∈ V(A₁)) (hb : b ∈ V(A₂)) :
    ∃ v ∈ W.support, v ∈ V(A₁) ∩ V(A₂) := by
  induction W with
  | @nil a _ => exact ⟨a, by simp, ha, hb⟩
  | @cons a w b e hlink W' ih =>
    have he : e ∈ E(A₁) ∪ E(A₂) := hsep.2.2.2.1 ▸ hlink.edge_mem
    rcases he with he₁ | he₂
    · have hw : w ∈ V(A₁) := ((hsep.1.isLink_iff he₁).mpr hlink).right_mem
      obtain ⟨v, hvW', hv⟩ := ih hw hb
      exact ⟨v, List.mem_cons_of_mem a hvW', hv⟩
    · have ha₂ : a ∈ V(A₂) := ((hsep.2.1.isLink_iff he₂).mpr hlink).left_mem
      exact ⟨a, by simp, ha, ha₂⟩

theorem exists_mem_inter_of_isGraphSeparation_of_path {G A₁ A₂ Q : Graph α β}
    (hsep : IsGraphSeparation G A₁ A₂) {a b : α} (hQ : IsGraphPathWithEnds G Q a b)
    (ha : a ∈ V(A₁)) (hb : b ∈ V(A₂)) :
    ∃ v ∈ V(Q), v ∈ V(A₁) ∩ V(A₂) := by
  obtain ⟨W, _, hV, _⟩ := hQ.2
  obtain ⟨W', hsupp, _⟩ := exists_walk_up_of_le hQ.1 W
  obtain ⟨v, hvW', hv⟩ := exists_mem_inter_of_isGraphSeparation_of_walk hsep W' ha hb
  refine ⟨v, ?_, hv⟩
  rw [hV, mem_ofPred_eq, ← hsupp]
  exact hvW'

/-- Given a separation `(A₁, A₂)` of `G` with `X ⊆ V(A₁)`, `Y ⊆ V(A₂)`, `V(A₂).Finite`, and
`(V(A₁) ∩ V(A₂)).ncard ≤ 3`, and three pairwise disjoint `X → Y` paths `Q₁, Q₂, Q₃` in `G` from
`s₁, s₂, s₃ ∈ X` to `t₁, t₂, t₃ ∈ Y`, every vertex of `V(A₁) ∩ V(A₂)` lies in
`V(Q₁) ∪ V(Q₂) ∪ V(Q₃)`, and every vertex of `X ∩ Y` lies in `{t₁, t₂, t₃}`. -/
theorem sep_subset_and_inter_subset_of_three_legs {α : Type u} {β : Type v}
    {G A₁ A₂ Q₁ Q₂ Q₃ : Graph α β} {X Y : Set α} {s₁ s₂ s₃ t₁ t₂ t₃ : α}
    (hsep : IsGraphSeparation G A₁ A₂) (hfin : V(A₂).Finite)
    (hX_A₁ : X ⊆ V(A₁)) (hY_A₂ : Y ⊆ V(A₂))
    (hcard_le : (V(A₁) ∩ V(A₂)).ncard ≤ 3)
    (hQ₁ : IsFromToPathWithEnds G Q₁ X Y s₁ t₁)
    (hQ₂ : IsFromToPathWithEnds G Q₂ X Y s₂ t₂)
    (hQ₃ : IsFromToPathWithEnds G Q₃ X Y s₃ t₃)
    (hd12 : Disjoint V(Q₁) V(Q₂))
    (hd13 : Disjoint V(Q₁) V(Q₃))
    (hd23 : Disjoint V(Q₂) V(Q₃)) :
    V(A₁) ∩ V(A₂) ⊆ V(Q₁) ∪ V(Q₂) ∪ V(Q₃) ∧
    X ∩ Y ⊆ {t₁, t₂, t₃} := by
  obtain ⟨v₁, hv₁Q, hv₁S⟩ := exists_mem_inter_of_isGraphSeparation_of_path hsep hQ₁.1
    (hX_A₁ hQ₁.left_mem_X) (hY_A₂ hQ₁.right_mem_Y)
  obtain ⟨v₂, hv₂Q, hv₂S⟩ := exists_mem_inter_of_isGraphSeparation_of_path hsep hQ₂.1
    (hX_A₁ hQ₂.left_mem_X) (hY_A₂ hQ₂.right_mem_Y)
  obtain ⟨v₃, hv₃Q, hv₃S⟩ := exists_mem_inter_of_isGraphSeparation_of_path hsep hQ₃.1
    (hX_A₁ hQ₃.left_mem_X) (hY_A₂ hQ₃.right_mem_Y)
  have hv12 : v₁ ≠ v₂ := fun h => disjoint_left.mp hd12 hv₁Q (h ▸ hv₂Q)
  have hv13 : v₁ ≠ v₃ := fun h => disjoint_left.mp hd13 hv₁Q (h ▸ hv₃Q)
  have hv23 : v₂ ≠ v₃ := fun h => disjoint_left.mp hd23 hv₂Q (h ▸ hv₃Q)
  have hsub : ({v₁, v₂, v₃} : Set α) ⊆ V(A₁) ∩ V(A₂) := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hcard3 : ({v₁, v₂, v₃} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hv12, hv13]) ((finite_singleton v₃).insert v₂),
      ncard_insert_of_notMem (by simp [hv23]) (finite_singleton v₃), ncard_singleton]
  have hfin_inter : (V(A₁) ∩ V(A₂)).Finite := hfin.subset inter_subset_right
  have heq : ({v₁, v₂, v₃} : Set α) = V(A₁) ∩ V(A₂) :=
    eq_of_subset_of_ncard_le hsub (by omega) hfin_inter
  have hS_sub : V(A₁) ∩ V(A₂) ⊆ V(Q₁) ∪ V(Q₂) ∪ V(Q₃) := by
    rw [← heq]
    rintro x (rfl | rfl | rfl)
    · exact Or.inl (Or.inl hv₁Q)
    · exact Or.inl (Or.inr hv₂Q)
    · exact Or.inr hv₃Q
  refine ⟨hS_sub, fun x ⟨hxX, hxY⟩ => ?_⟩
  have hxS : x ∈ V(A₁) ∩ V(A₂) := ⟨hX_A₁ hxX, hY_A₂ hxY⟩
  rcases hS_sub hxS with (hx₁ | hx₂) | hx₃
  · have hx_t₁ : x ∈ V(Q₁) ∩ Y := ⟨hx₁, hxY⟩
    rw [hQ₁.2.2, mem_singleton_iff] at hx_t₁
    simp [hx_t₁]
  · have hx_t₂ : x ∈ V(Q₂) ∩ Y := ⟨hx₂, hxY⟩
    rw [hQ₂.2.2, mem_singleton_iff] at hx_t₂
    simp [hx_t₂]
  · have hx_t₃ : x ∈ V(Q₃) ∩ Y := ⟨hx₃, hxY⟩
    rw [hQ₃.2.2, mem_singleton_iff] at hx_t₃
    simp [hx_t₃]

/-- Replacing one leg `Q₁` at a vertex `z ∈ V(Q₁)` by a path `P_W'` from `z` to `w₁ ∈ Y` that meets
`V(Q₁) ∪ V(Q₂) ∪ V(Q₃)` only at `z`, meets `Y` only at `w₁`, and meets `X` only within `{z}`
produces a new `X → Y` leg `Q₁'` from `s₁` to `w₁` disjoint from `Q₂` and `Q₃`. -/
theorem replace_leg_by_path {G Q₁ Q₂ Q₃ P_W' : Graph α β} {X Y : Set α}
    {s₁ t₁ z w₁ : α}
    (hQ₁ : IsFromToPathWithEnds G Q₁ X Y s₁ t₁)
    (hd12 : Disjoint V(Q₁) V(Q₂)) (hd13 : Disjoint V(Q₁) V(Q₃))
    (hzQ₁ : z ∈ V(Q₁))
    (hPW'_path : IsGraphPathWithEnds G P_W' z w₁)
    (hPW'_Q : V(P_W') ∩ (V(Q₁) ∪ V(Q₂) ∪ V(Q₃)) = {z})
    (hPW'_X : V(P_W') ∩ X ⊆ {z})
    (hPW'_Y : V(P_W') ∩ Y = {w₁}) :
    IsFromToPathWithEnds G (subgraphUnion G (Classical.choose (hQ₁.1.exists_split_at hzQ₁)) P_W')
      X Y s₁ w₁ ∧
    Disjoint V(subgraphUnion G (Classical.choose (hQ₁.1.exists_split_at hzQ₁)) P_W') V(Q₂) ∧
    Disjoint V(subgraphUnion G (Classical.choose (hQ₁.1.exists_split_at hzQ₁)) P_W') V(Q₃) := by
  let Q₁_a := Classical.choose (hQ₁.1.exists_split_at hzQ₁)
  obtain ⟨Q₁_b, hQ₁a_le, hQ₁b_le, hQ₁a_path, hQ₁b_path, _, hinter_Q₁, _⟩ :=
    Classical.choose_spec (hQ₁.1.exists_split_at hzQ₁)
  have hQ₁a_PW' : V(Q₁_a) ∩ V(P_W') = {z} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxQa, hxPW'⟩ => ?_, fun h => h ▸ ⟨hQ₁a_path.right_mem, hPW'_path.left_mem⟩⟩
    have hx_in : x ∈ V(P_W') ∩ (V(Q₁) ∪ V(Q₂) ∪ V(Q₃)) :=
      ⟨hxPW', Or.inl (Or.inl (hQ₁a_le.vertexSet_mono hxQa))⟩
    rwa [hPW'_Q, mem_singleton_iff] at hx_in
  have hQ₁'_path : IsGraphPathWithEnds G (subgraphUnion G Q₁_a P_W') s₁ w₁ :=
    (hQ₁a_path.mono hQ₁.1.le).subgraphUnion hPW'_path hQ₁a_PW'
  have hQ₁'_X : V(subgraphUnion G Q₁_a P_W') ∩ X = {s₁} := by
    ext x
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hxQa | hxPW', hxX⟩
      · have hx_in : x ∈ V(Q₁) ∩ X := ⟨hQ₁a_le.vertexSet_mono hxQa, hxX⟩
        rwa [hQ₁.2.1, mem_singleton_iff] at hx_in
      · have hxz : x = z := mem_singleton_iff.mp (hPW'_X ⟨hxPW', hxX⟩)
        subst hxz
        have hx_in : x ∈ V(Q₁) ∩ X := ⟨hzQ₁, hxX⟩
        rwa [hQ₁.2.1, mem_singleton_iff] at hx_in
    · rintro rfl
      exact ⟨Or.inl hQ₁a_path.left_mem, hQ₁.left_mem_X⟩
  have hQ₁'_Y : V(subgraphUnion G Q₁_a P_W') ∩ Y = {w₁} := by
    ext x
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hxQa | hxPW', hxY⟩
      · have hxt₁ : x = t₁ := by
          have hx_in : x ∈ V(Q₁) ∩ Y := ⟨hQ₁a_le.vertexSet_mono hxQa, hxY⟩
          rwa [hQ₁.2.2, mem_singleton_iff] at hx_in
        subst hxt₁
        have hxz : x = z := by
          have hx_in : x ∈ V(Q₁_a) ∩ V(Q₁_b) := ⟨hxQa, hQ₁b_path.right_mem⟩
          rwa [hinter_Q₁, mem_singleton_iff] at hx_in
        subst hxz
        have hx_in : x ∈ V(P_W') ∩ Y := ⟨hPW'_path.left_mem, hxY⟩
        rwa [hPW'_Y, mem_singleton_iff] at hx_in
      · have hx_in : x ∈ V(P_W') ∩ Y := ⟨hxPW', hxY⟩
        rwa [hPW'_Y, mem_singleton_iff] at hx_in
    · rintro rfl
      have hw₁Y : x ∈ V(P_W') ∩ Y := by rw [hPW'_Y]; simp
      exact ⟨Or.inr hPW'_path.right_mem, hw₁Y.2⟩
  have hdisj_PW'_Q₂ : Disjoint V(P_W') V(Q₂) := by
    rw [disjoint_left]
    intro x hxPW' hxQ₂
    have hx_in : x ∈ V(P_W') ∩ (V(Q₁) ∪ V(Q₂) ∪ V(Q₃)) := ⟨hxPW', Or.inl (Or.inr hxQ₂)⟩
    rw [hPW'_Q, mem_singleton_iff] at hx_in
    subst hx_in
    exact disjoint_left.mp hd12 hzQ₁ hxQ₂
  have hdisj_PW'_Q₃ : Disjoint V(P_W') V(Q₃) := by
    rw [disjoint_left]
    intro x hxPW' hxQ₃
    have hx_in : x ∈ V(P_W') ∩ (V(Q₁) ∪ V(Q₂) ∪ V(Q₃)) := ⟨hxPW', Or.inr hxQ₃⟩
    rw [hPW'_Q, mem_singleton_iff] at hx_in
    subst hx_in
    exact disjoint_left.mp hd13 hzQ₁ hxQ₃
  refine ⟨⟨hQ₁'_path, hQ₁'_X, hQ₁'_Y⟩, ?_, ?_⟩
  · rw [vertexSet_subgraphUnion]
    exact Disjoint.union_left (hd12.mono_left hQ₁a_le.vertexSet_mono) hdisj_PW'_Q₂
  · rw [vertexSet_subgraphUnion]
    exact Disjoint.union_left (hd13.mono_left hQ₁a_le.vertexSet_mono) hdisj_PW'_Q₃

theorem leg_in_W1_isFromToPathWithEnds (S : Society α β) {P Q : Graph α β} {s t s_q : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {X : Set α} {k : ℕ} (hk : k < (splitList S hs ht hP).length)
    (hmk : (pathWalkTS hP).support.length ≤ k)
    (hQ : IsFromToPathWithEnds (splitGraph S P s t) Q X
      {x | x ∈ splitList S hs ht hP} s_q ((splitList S hs ht hP)[k]'hk)) :
    (splitList S hs ht hP)[k]'hk ∈ S.Ω.bar ∧
    IsFromToPathWithEnds S.G Q X S.Ω.bar s_q ((splitList S hs ht hP)[k]'hk) := by
  have hk_bar : (splitList S hs ht hP)[k]'hk ∈ S.Ω.bar :=
    ((getElem_splitList_mem_W1_iff S hs ht hst hP hP_bar hk).mpr hmk).1.1
  refine ⟨hk_bar, hQ.1.mono (splitGraph_le S P s t), hQ.2.1, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  refine ⟨fun ⟨hxQ, hx_bar⟩ => ?_, fun h => h ▸ ⟨hQ.1.right_mem, hk_bar⟩⟩
  have hxG₁ : x ∈ V(splitGraph S P s t) := hQ.1.le.vertexSet_mono hxQ
  have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
    vertexSet_splitGraph_inter_bar_subset_splitList S hs ht hst hP ⟨hxG₁, hx_bar⟩
  have hx_in : x ∈ V(Q) ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxQ, hxL⟩
  rwa [hQ.2.2, mem_singleton_iff] at hx_in

theorem extend_leg_left_to_t (S : Society α β) {P Q_a : Graph α β} {s t s_a : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {X : Set α} {k_a k_b k_c : ℕ}
    (hka : k_a < (splitList S hs ht hP).length)
    (hkb : k_b < (splitList S hs ht hP).length)
    (hkc : k_c < (splitList S hs ht hP).length)
    (hab : k_a < k_b) (hac : k_a < k_c)
    (hka_pred : k_a < (pathWalkTS hP).support.length - 1)
    (hQa : IsFromToPathWithEnds (splitGraph S P s t) Q_a X
      {x | x ∈ splitList S hs ht hP} s_a ((splitList S hs ht hP)[k_a]'hka))
    (hX_L : X ∩ {x | x ∈ splitList S hs ht hP} ⊆
      {(splitList S hs ht hP)[k_a]'hka, (splitList S hs ht hP)[k_b]'hkb,
       (splitList S hs ht hP)[k_c]'hkc})
    {Q_0_ka : Graph α β} (hQ0_le : Q_0_ka ≤ P)
    (hQ0_path : IsGraphPathWithEnds S.G Q_0_ka
      ((splitList S hs ht hP)[0]'(by
        rw [length_splitList]
        have := two_le_length_support_pathWalkTS hst hP; omega))
      ((splitList S hs ht hP)[k_a]'hka))
    (hVQ0 : V(Q_0_ka) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      0 ≤ k ∧ k ≤ k_a ∧ x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)}) :
    IsFromToPathWithEnds S.G (subgraphUnion S.G Q_a Q_0_ka) X S.Ω.bar s_a t := by
  have hm2 : 2 ≤ (pathWalkTS hP).support.length := two_le_length_support_pathWalkTS hst hP
  have hka_m : k_a < (pathWalkTS hP).support.length := by omega
  have hQa_Q0 : V(Q_a) ∩ V(Q_0_ka) = {(splitList S hs ht hP)[k_a]'hka} := by
    rw [inter_comm]
    exact inter_subpath_P_eq_of_inter_singleton S hs ht hst hP hP_bar hka_m hka hVQ0
      hQa.2.2 ⟨Nat.zero_le k_a, le_rfl⟩
  have hRa_path : IsGraphPathWithEnds S.G (subgraphUnion S.G Q_a Q_0_ka) s_a t := by
    have h := (hQa.1.mono (splitGraph_le S P s t)).subgraphUnion hQ0_path.symm hQa_Q0
    rwa [getElem_splitList_zero S hs ht hP] at h
  have hQ0_bar : V(Q_0_ka) ∩ S.Ω.bar = {t} :=
    subpath_P_inter_bar_eq_t S hs ht hst hP hP_bar hka_pred hQ0_le hVQ0
  have hRa_X : V(subgraphUnion S.G Q_a Q_0_ka) ∩ X = {s_a} := by
    ext x
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hxQa | hxQ0, hxX⟩
      · have hx_in : x ∈ V(Q_a) ∩ X := ⟨hxQa, hxX⟩
        rwa [hQa.2.1, mem_singleton_iff] at hx_in
      · have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
          subpath_P_subset_splitList S hs ht hP hVQ0 hxQ0
        have hx_three := hX_L ⟨hxX, hxL⟩
        simp only [mem_insert_iff, mem_singleton_iff] at hx_three
        rcases hx_three with rfl | rfl | rfl
        · have hx_in : (splitList S hs ht hP)[k_a]'hka ∈ V(Q_a) ∩ X := ⟨hQa.1.right_mem, hxX⟩
          rwa [hQa.2.1, mem_singleton_iff] at hx_in
        · have hmem := (mem_subpath_P_iff S hs ht hst hP hP_bar hka_m hVQ0 hkb).mp hxQ0
          omega
        · have hmem := (mem_subpath_P_iff S hs ht hst hP hP_bar hka_m hVQ0 hkc).mp hxQ0
          omega
    · rintro rfl
      exact ⟨Or.inl hQa.1.left_mem, hQa.left_mem_X⟩
  have hRa_bar : V(subgraphUnion S.G Q_a Q_0_ka) ∩ S.Ω.bar = {t} := by
    ext x
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hxQa | hxQ0, hx_bar⟩
      · have hxG₁ : x ∈ V(splitGraph S P s t) := hQa.1.le.vertexSet_mono hxQa
        have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
          vertexSet_splitGraph_inter_bar_subset_splitList S hs ht hst hP ⟨hxG₁, hx_bar⟩
        have hx_in : x ∈ V(Q_a) ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxQa, hxL⟩
        rw [hQa.2.2, mem_singleton_iff] at hx_in
        subst hx_in
        have hxQ0' : (splitList S hs ht hP)[k_a]'hka ∈ V(Q_0_ka) ∩ S.Ω.bar :=
          ⟨hQ0_path.right_mem, hx_bar⟩
        rwa [hQ0_bar, mem_singleton_iff] at hxQ0'
      · have hx_in : x ∈ V(Q_0_ka) ∩ S.Ω.bar := ⟨hxQ0, hx_bar⟩
        rwa [hQ0_bar, mem_singleton_iff] at hx_in
    · rintro rfl
      have ht_in : x ∈ V(Q_0_ka) ∩ S.Ω.bar := by rw [hQ0_bar]; simp
      exact ⟨Or.inr ht_in.1, ht_in.2⟩
  exact ⟨hRa_path, hRa_X, hRa_bar⟩

theorem extend_leg_right_to_s (S : Society α β) {P Q_b : Graph α β} {s t s_b : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {X : Set α} {k_a k_b k_c : ℕ}
    (hka : k_a < (splitList S hs ht hP).length)
    (hkb : k_b < (splitList S hs ht hP).length)
    (hkc : k_c < (splitList S hs ht hP).length)
    (hab : k_a < k_b)
    (hkb_pred : k_b ≤ (pathWalkTS hP).support.length - 1)
    (hQb : IsFromToPathWithEnds (splitGraph S P s t) Q_b X
      {x | x ∈ splitList S hs ht hP} s_b ((splitList S hs ht hP)[k_b]'hkb))
    (hX_L : X ∩ {x | x ∈ splitList S hs ht hP} ⊆
      {(splitList S hs ht hP)[k_a]'hka, (splitList S hs ht hP)[k_b]'hkb,
       (splitList S hs ht hP)[k_c]'hkc})
    (hmkc : (pathWalkTS hP).support.length ≤ k_c)
    {Q_kb_m : Graph α β} (hQbm_le : Q_kb_m ≤ P)
    (hQbm_path : IsGraphPathWithEnds S.G Q_kb_m
      ((splitList S hs ht hP)[k_b]'hkb)
      ((splitList S hs ht hP)[(pathWalkTS hP).support.length - 1]'(by
        rw [length_splitList]
        have := two_le_length_support_pathWalkTS hst hP; omega)))
    (hVQbm : V(Q_kb_m) = {x | ∃ k : ℕ, ∃ hk : k < (pathWalkTS hP).support.length,
      k_b ≤ k ∧ k ≤ (pathWalkTS hP).support.length - 1 ∧
      x = (splitList S hs ht hP)[k]'(by rw [length_splitList]; omega)}) :
    IsFromToPathWithEnds S.G (subgraphUnion S.G Q_b Q_kb_m) X S.Ω.bar s_b s := by
  have hm2 : 2 ≤ (pathWalkTS hP).support.length := two_le_length_support_pathWalkTS hst hP
  have hpred : (pathWalkTS hP).support.length - 1 < (pathWalkTS hP).support.length := by omega
  have hQb_Qbm : V(Q_b) ∩ V(Q_kb_m) = {(splitList S hs ht hP)[k_b]'hkb} := by
    rw [inter_comm]
    exact inter_subpath_P_eq_of_inter_singleton S hs ht hst hP hP_bar hpred hkb hVQbm
      hQb.2.2 ⟨le_rfl, hkb_pred⟩
  have hRb_path : IsGraphPathWithEnds S.G (subgraphUnion S.G Q_b Q_kb_m) s_b s := by
    have h := (hQb.1.mono (splitGraph_le S P s t)).subgraphUnion hQbm_path hQb_Qbm
    rwa [getElem_splitList_pred S hs ht hP] at h
  have hQbm_bar : V(Q_kb_m) ∩ S.Ω.bar = {s} :=
    subpath_P_inter_bar_eq_s S hs ht hst hP hP_bar (by omega) hkb_pred hQbm_le hVQbm
  have hRb_X : V(subgraphUnion S.G Q_b Q_kb_m) ∩ X = {s_b} := by
    ext x
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hxQb | hxQbm, hxX⟩
      · have hx_in : x ∈ V(Q_b) ∩ X := ⟨hxQb, hxX⟩
        rwa [hQb.2.1, mem_singleton_iff] at hx_in
      · have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
          subpath_P_subset_splitList S hs ht hP hVQbm hxQbm
        have hx_three := hX_L ⟨hxX, hxL⟩
        simp only [mem_insert_iff, mem_singleton_iff] at hx_three
        rcases hx_three with rfl | rfl | rfl
        · have hmem := (mem_subpath_P_iff S hs ht hst hP hP_bar hpred hVQbm hka).mp hxQbm
          omega
        · have hx_in : (splitList S hs ht hP)[k_b]'hkb ∈ V(Q_b) ∩ X := ⟨hQb.1.right_mem, hxX⟩
          rwa [hQb.2.1, mem_singleton_iff] at hx_in
        · have hmem := (mem_subpath_P_iff S hs ht hst hP hP_bar hpred hVQbm hkc).mp hxQbm
          omega
    · rintro rfl
      exact ⟨Or.inl hQb.1.left_mem, hQb.left_mem_X⟩
  have hRb_bar : V(subgraphUnion S.G Q_b Q_kb_m) ∩ S.Ω.bar = {s} := by
    ext x
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hxQb | hxQbm, hx_bar⟩
      · have hxG₁ : x ∈ V(splitGraph S P s t) := hQb.1.le.vertexSet_mono hxQb
        have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
          vertexSet_splitGraph_inter_bar_subset_splitList S hs ht hst hP ⟨hxG₁, hx_bar⟩
        have hx_in : x ∈ V(Q_b) ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxQb, hxL⟩
        rw [hQb.2.2, mem_singleton_iff] at hx_in
        subst hx_in
        have hxQbm' : (splitList S hs ht hP)[k_b]'hkb ∈ V(Q_kb_m) ∩ S.Ω.bar :=
          ⟨hQbm_path.left_mem, hx_bar⟩
        rwa [hQbm_bar, mem_singleton_iff] at hxQbm'
      · have hx_in : x ∈ V(Q_kb_m) ∩ S.Ω.bar := ⟨hxQbm, hx_bar⟩
        rwa [hQbm_bar, mem_singleton_iff] at hx_in
    · rintro rfl
      have hs_in : x ∈ V(Q_kb_m) ∩ S.Ω.bar := by rw [hQbm_bar]; simp
      exact ⟨Or.inr hs_in.1, hs_in.2⟩
  exact ⟨hRb_path, hRb_X, hRb_bar⟩

theorem redirectsTo_bar_of_sorted_legs (S : Society α β) {P Q_a Q_b Q_c : Graph α β}
    {s t s_a s_b s_c : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {X : Set α} (hsa : s_a ∈ X) (hsb : s_b ∈ X) (hsc : s_c ∈ X)
    (hsab : s_a ≠ s_b) (hsac : s_a ≠ s_c) (hsbc : s_b ≠ s_c)
    {k_a k_b k_c : ℕ}
    (hka : k_a < (splitList S hs ht hP).length)
    (hkb : k_b < (splitList S hs ht hP).length)
    (hkc : k_c < (splitList S hs ht hP).length)
    (hab : k_a < k_b)
    (hmkc : (pathWalkTS hP).support.length ≤ k_c)
    (hQa : IsFromToPathWithEnds (splitGraph S P s t) Q_a X
      {x | x ∈ splitList S hs ht hP} s_a ((splitList S hs ht hP)[k_a]'hka))
    (hQb : IsFromToPathWithEnds (splitGraph S P s t) Q_b X
      {x | x ∈ splitList S hs ht hP} s_b ((splitList S hs ht hP)[k_b]'hkb))
    (hQc : IsFromToPathWithEnds (splitGraph S P s t) Q_c X
      {x | x ∈ splitList S hs ht hP} s_c ((splitList S hs ht hP)[k_c]'hkc))
    (hd_ab : Disjoint V(Q_a) V(Q_b))
    (hd_ac : Disjoint V(Q_a) V(Q_c))
    (hd_bc : Disjoint V(Q_b) V(Q_c))
    (hX_L : X ∩ {x | x ∈ splitList S hs ht hP} ⊆
      {(splitList S hs ht hP)[k_a]'hka, (splitList S hs ht hP)[k_b]'hkb,
       (splitList S hs ht hP)[k_c]'hkc}) :
    ∃ t₁' ∈ S.Ω.bar, ∃ t₂' ∈ S.Ω.bar, ∃ t₃' ∈ S.Ω.bar,
      RedirectsTo S.G X S.Ω.bar {s_a, s_b, s_c} {t₁', t₂', t₃'} := by
  let m := (pathWalkTS hP).support.length
  have hm2 : 2 ≤ m := two_le_length_support_pathWalkTS hst hP
  obtain ⟨hkc_bar, hRc⟩ :=
    leg_in_W1_isFromToPathWithEnds S hs ht hst hP hP_bar hkc hmkc hQc
  by_cases hka_pred : k_a < m - 1
  · have hka_m : k_a < m := by omega
    obtain ⟨Q_0_ka, hQ0_le, hQ0_path, hVQ0⟩ :=
      exists_subpath_P_of_splitList_indices S hs ht hP (Nat.zero_le k_a) hka_m
    have hRa := extend_leg_left_to_t S hs ht hst hP hP_bar hka hkb hkc hab (by omega)
      hka_pred hQa hX_L hQ0_le hQ0_path hVQ0
    have hd_Qb_Q0 : Disjoint V(Q_b) V(Q_0_ka) :=
      disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar hka_m hkb hVQ0 hQb.2.2 (by omega)
    have hd_Qc_Q0 : Disjoint V(Q_c) V(Q_0_ka) :=
      disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar hka_m hkc hVQ0 hQc.2.2 (by omega)
    have hd_Ra_Qc : Disjoint V(subgraphUnion S.G Q_a Q_0_ka) V(Q_c) := by
      rw [vertexSet_subgraphUnion]
      exact Disjoint.union_left hd_ac hd_Qc_Q0.symm
    by_cases hmkb : m ≤ k_b
    · obtain ⟨hkb_bar, hRb⟩ :=
        leg_in_W1_isFromToPathWithEnds S hs ht hst hP hP_bar hkb hmkb hQb
      have hd_Ra_Qb : Disjoint V(subgraphUnion S.G Q_a Q_0_ka) V(Q_b) := by
        rw [vertexSet_subgraphUnion]
        exact Disjoint.union_left hd_ab hd_Qb_Q0.symm
      exact ⟨t, ht, _, hkb_bar, _, hkc_bar,
        redirectsTo_of_three_disjoint_paths hsa hsb hsc ht hkb_bar hkc_bar
          hsab hsac hsbc hRa hRb hRc hd_Ra_Qb hd_Ra_Qc hd_bc⟩
    · have hkb_pred : k_b ≤ m - 1 := by omega
      have hpred : m - 1 < m := by omega
      obtain ⟨Q_kb_m, hQbm_le, hQbm_path, hVQbm⟩ :=
        exists_subpath_P_of_splitList_indices S hs ht hP hkb_pred hpred
      have hRb := extend_leg_right_to_s S hs ht hst hP hP_bar hka hkb hkc hab hkb_pred
        hQb hX_L hmkc hQbm_le hQbm_path hVQbm
      have hd_Qa_Qbm : Disjoint V(Q_a) V(Q_kb_m) :=
        disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar hpred hka hVQbm hQa.2.2
          (by omega)
      have hd_Qc_Qbm : Disjoint V(Q_c) V(Q_kb_m) :=
        disjoint_subpath_P_of_inter_singleton S hs ht hst hP hP_bar hpred hkc hVQbm hQc.2.2
          (by omega)
      have hd_Q0_Qbm : Disjoint V(Q_0_ka) V(Q_kb_m) :=
        disjoint_subpath_P_subpath_P S hs ht hst hP hP_bar hpred hab hVQ0 hVQbm
      have hd_Ra_Rb :
          Disjoint V(subgraphUnion S.G Q_a Q_0_ka) V(subgraphUnion S.G Q_b Q_kb_m) := by
        rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion]
        exact Disjoint.union_left (Disjoint.union_right hd_ab hd_Qa_Qbm)
          (Disjoint.union_right hd_Qb_Q0.symm hd_Q0_Qbm)
      have hd_Rb_Qc : Disjoint V(subgraphUnion S.G Q_b Q_kb_m) V(Q_c) := by
        rw [vertexSet_subgraphUnion]
        exact Disjoint.union_left hd_bc hd_Qc_Qbm.symm
      exact ⟨t, ht, s, hs, _, hkc_bar,
        redirectsTo_of_three_disjoint_paths hsa hsb hsc ht hs hkc_bar
          hsab hsac hsbc hRa hRb hRc hd_Ra_Rb hd_Ra_Qc hd_Rb_Qc⟩
  · -- `m - 1 ≤ k_a < k_b < k_c`, so `m ≤ k_b` and either `k_a = m - 1` (`L[k_a] = s`) or `m ≤ k_a`.
    have hmkb : m ≤ k_b := by omega
    obtain ⟨hkb_bar, hRb⟩ :=
      leg_in_W1_isFromToPathWithEnds S hs ht hst hP hP_bar hkb hmkb hQb
    have hka_bar_and_Ra :
        (splitList S hs ht hP)[k_a]'hka ∈ S.Ω.bar ∧
        IsFromToPathWithEnds S.G Q_a X S.Ω.bar s_a ((splitList S hs ht hP)[k_a]'hka) := by
      by_cases hmka : m ≤ k_a
      · exact leg_in_W1_isFromToPathWithEnds S hs ht hst hP hP_bar hka hmka hQa
      · have hka_eq : k_a = m - 1 := by omega
        have hLka_s : (splitList S hs ht hP)[k_a]'hka = s := by
          subst hka_eq
          exact getElem_splitList_pred S hs ht hP
        have hka_bar : (splitList S hs ht hP)[k_a]'hka ∈ S.Ω.bar := by
          rw [hLka_s]
          exact hs
        refine ⟨hka_bar, hQa.1.mono (splitGraph_le S P s t), hQa.2.1, ?_⟩
        ext x
        simp only [mem_inter_iff, mem_singleton_iff]
        refine ⟨fun ⟨hxQa, hx_bar⟩ => ?_, fun h => h ▸ ⟨hQa.1.right_mem, hka_bar⟩⟩
        have hxG₁ : x ∈ V(splitGraph S P s t) := hQa.1.le.vertexSet_mono hxQa
        have hxL : x ∈ {y | y ∈ splitList S hs ht hP} :=
          vertexSet_splitGraph_inter_bar_subset_splitList S hs ht hst hP ⟨hxG₁, hx_bar⟩
        have hx_in : x ∈ V(Q_a) ∩ {y | y ∈ splitList S hs ht hP} := ⟨hxQa, hxL⟩
        rwa [hQa.2.2, mem_singleton_iff] at hx_in
    exact ⟨_, hka_bar_and_Ra.1, _, hkb_bar, _, hkc_bar,
      redirectsTo_of_three_disjoint_paths hsa hsb hsc hka_bar_and_Ra.1 hkb_bar hkc_bar
        hsab hsac hsbc hka_bar_and_Ra.2 hRb hRc hd_ab hd_ac hd_bc⟩

theorem redirectsTo_bar_of_one_leg_in_W1 (S : Society α β) {P Q_a Q_b Q_c : Graph α β}
    {s t s_a s_b s_c : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {X : Set α} (hsa : s_a ∈ X) (hsb : s_b ∈ X) (hsc : s_c ∈ X)
    (hsab : s_a ≠ s_b) (hsac : s_a ≠ s_c) (hsbc : s_b ≠ s_c)
    {k_a k_b k_c : ℕ}
    (hka : k_a < (splitList S hs ht hP).length)
    (hkb : k_b < (splitList S hs ht hP).length)
    (hkc : k_c < (splitList S hs ht hP).length)
    (hmkc : (pathWalkTS hP).support.length ≤ k_c)
    (hQa : IsFromToPathWithEnds (splitGraph S P s t) Q_a X
      {x | x ∈ splitList S hs ht hP} s_a ((splitList S hs ht hP)[k_a]'hka))
    (hQb : IsFromToPathWithEnds (splitGraph S P s t) Q_b X
      {x | x ∈ splitList S hs ht hP} s_b ((splitList S hs ht hP)[k_b]'hkb))
    (hQc : IsFromToPathWithEnds (splitGraph S P s t) Q_c X
      {x | x ∈ splitList S hs ht hP} s_c ((splitList S hs ht hP)[k_c]'hkc))
    (hd_ab : Disjoint V(Q_a) V(Q_b))
    (hd_ac : Disjoint V(Q_a) V(Q_c))
    (hd_bc : Disjoint V(Q_b) V(Q_c))
    (hX_L : X ∩ {x | x ∈ splitList S hs ht hP} ⊆
      {(splitList S hs ht hP)[k_a]'hka, (splitList S hs ht hP)[k_b]'hkb,
       (splitList S hs ht hP)[k_c]'hkc}) :
    ∃ t₁' ∈ S.Ω.bar, ∃ t₂' ∈ S.Ω.bar, ∃ t₃' ∈ S.Ω.bar,
      RedirectsTo S.G X S.Ω.bar {s_a, s_b, s_c} {t₁', t₂', t₃'} := by
  have hkab_ne : k_a ≠ k_b := by
    intro h
    subst h
    exact disjoint_left.mp hd_ab hQa.1.right_mem hQb.1.right_mem
  rcases lt_or_gt_of_ne hkab_ne with hab | hba
  · exact redirectsTo_bar_of_sorted_legs S hs ht hst hP hP_bar hsa hsb hsc hsab hsac hsbc
      hka hkb hkc hab hmkc hQa hQb hQc hd_ab hd_ac hd_bc hX_L
  · have hX_L' : X ∩ {x | x ∈ splitList S hs ht hP} ⊆
        {(splitList S hs ht hP)[k_b]'hkb, (splitList S hs ht hP)[k_a]'hka,
         (splitList S hs ht hP)[k_c]'hkc} := by
      intro x hx
      rcases hX_L hx with rfl | rfl | rfl <;> simp
    obtain ⟨t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩ :=
      redirectsTo_bar_of_sorted_legs S hs ht hst hP hP_bar hsb hsa hsc hsab.symm hsbc hsac
        hkb hka hkc hba hmkc hQb hQa hQc hd_ab.symm hd_bc hd_ac hX_L'
    have hset_eq : ({s_b, s_a, s_c} : Set α) = {s_a, s_b, s_c} := by
      ext x; simp [or_left_comm]
    rw [hset_eq] at hred
    exact ⟨t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩

/-- **Graph Minors IX, (2.4)** (page 46):
"Suppose that $\{P_1, P_2, P_3\}$ is a tripod in $(G_1, \Omega_1)$... Thus $(G_1, \Omega_1)$ has no
tripod." -/
theorem lemma_2_4_no_tripod (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t) (hP_ind : P ≤i S.G)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    (hcatch : Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)))
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃) :
    ¬ ∃ T₁ T₂ T₃ : Graph α β,
      (splitSociety S hs ht hst hP hP_bar hnocross).IsTripod T₁ T₂ T₃ := by
  classical
  let S₁ := splitSociety S hs ht hst hP hP_bar hnocross
  let L := splitList S hs ht hP
  rintro ⟨T₁, T₂, T₃, htripod⟩
  have hnocross₁ : ¬ ∃ Q₁ Q₂ : Graph α β, S₁.IsCross Q₁ Q₂ :=
    lemma_2_4_no_cross S hs ht hst hP hP_ind hP_bar hcatch hnocross hnotripod
  obtain ⟨A₁, A₂, hsep_int, hT_le_A₁⟩ :=
    (theorem_2_3_proof S₁ htripod).resolve_left hnocross₁
  rcases htripod with ⟨u, v, huv, hT₁, hT₂, hT₃, hinter_12, hinter_13, hinter_23,
    s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁₀, _, t₂₀, _, t₃₀, _, hred₃⟩
  let X : Set α := V(T₁) ∪ V(T₂) ∪ V(T₃)
  have hX_A₁ : X ⊆ V(A₁) := by
    have hV := hT_le_A₁.vertexSet_mono
    rwa [vertexSet_subgraphUnion, vertexSet_subgraphUnion] at hV
  have hs12 : s₁ ≠ s₂ := by
    intro h
    have : s₁ ∈ V(T₁) ∩ V(T₂) := ⟨hs₁.1, h ▸ hs₂.1⟩
    rw [hinter_12] at this
    exact hs₁.2 this
  have hs13 : s₁ ≠ s₃ := by
    intro h
    have : s₁ ∈ V(T₁) ∩ V(T₃) := ⟨hs₁.1, h ▸ hs₃.1⟩
    rw [hinter_13] at this
    exact hs₁.2 this
  have hs23 : s₂ ≠ s₃ := by
    intro h
    have : s₂ ∈ V(T₂) ∩ V(T₃) := ⟨hs₂.1, h ▸ hs₃.1⟩
    rw [hinter_23] at this
    exact hs₂.2 this
  have hcard_s : ({s₁, s₂, s₃} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hs12, hs13]) ((finite_singleton s₃).insert s₂),
      ncard_insert_of_notMem (by simp [hs23]) (finite_singleton s₃), ncard_singleton]
  have hX'_fin : ({s₁, s₂, s₃} : Set α).Finite :=
    ((finite_singleton s₃).insert s₂).insert s₁
  have hY'_fin : ({t₁₀, t₂₀, t₃₀} : Set α).Finite :=
    ((finite_singleton t₃₀).insert t₂₀).insert t₁₀
  obtain ⟨Q_fam, x_fn, y_fn, hdisjQ, hQ_fam, hx_range, _⟩ :=
    exists_indexed_of_redirectsTo hX'_fin hY'_fin hred₃ hcard_s
  obtain ⟨hx_inj, _, _, _, _⟩ := redirectsTo_of_disjoint_fromToPaths hdisjQ hQ_fam
  obtain ⟨i₁, hi₁⟩ : s₁ ∈ range x_fn := hx_range ▸ by simp
  obtain ⟨i₂, hi₂⟩ : s₂ ∈ range x_fn := hx_range ▸ by simp
  obtain ⟨i₃, hi₃⟩ : s₃ ∈ range x_fn := hx_range ▸ by simp
  have hi12 : i₁ ≠ i₂ := fun h => hs12 (hi₁ ▸ hi₂ ▸ congrArg x_fn h)
  have hi13 : i₁ ≠ i₃ := fun h => hs13 (hi₁ ▸ hi₃ ▸ congrArg x_fn h)
  have hi23 : i₂ ≠ i₃ := fun h => hs23 (hi₂ ▸ hi₃ ▸ congrArg x_fn h)
  let Q₁ := Q_fam i₁
  let Q₂ := Q_fam i₂
  let Q₃ := Q_fam i₃
  have hbar₁_eq : S₁.Ω.bar = {x | x ∈ L} := by
    change (splitCyclicPerm S hs ht hst hP hP_bar).bar = {x | x ∈ L}
    rw [splitCyclicPerm, CyclicPerm.ofNodupList_bar]
  have hQ₁ : IsFromToPathWithEnds (splitGraph S P s t) Q₁ X {x | x ∈ L} s₁ (y_fn i₁) := by
    have h := hi₁ ▸ hQ_fam i₁
    rwa [hbar₁_eq] at h
  have hQ₂ : IsFromToPathWithEnds (splitGraph S P s t) Q₂ X {x | x ∈ L} s₂ (y_fn i₂) := by
    have h := hi₂ ▸ hQ_fam i₂
    rwa [hbar₁_eq] at h
  have hQ₃ : IsFromToPathWithEnds (splitGraph S P s t) Q₃ X {x | x ∈ L} s₃ (y_fn i₃) := by
    have h := hi₃ ▸ hQ_fam i₃
    rwa [hbar₁_eq] at h
  have hd12 : Disjoint V(Q₁) V(Q₂) := hdisjQ hi12
  have hd13 : Disjoint V(Q₁) V(Q₃) := hdisjQ hi13
  have hd23 : Disjoint V(Q₂) V(Q₃) := hdisjQ hi23
  obtain ⟨k₁, hk₁, hy₁⟩ := List.mem_iff_getElem.mp hQ₁.right_mem_Y
  obtain ⟨k₂, hk₂, hy₂⟩ := List.mem_iff_getElem.mp hQ₂.right_mem_Y
  obtain ⟨k₃, hk₃, hy₃⟩ := List.mem_iff_getElem.mp hQ₃.right_mem_Y
  have hQ₁' : IsFromToPathWithEnds (splitGraph S P s t) Q₁ X {x | x ∈ L} s₁ (L[k₁]'hk₁) :=
    hy₁ ▸ hQ₁
  have hQ₂' : IsFromToPathWithEnds (splitGraph S P s t) Q₂ X {x | x ∈ L} s₂ (L[k₂]'hk₂) :=
    hy₂ ▸ hQ₂
  have hQ₃' : IsFromToPathWithEnds (splitGraph S P s t) Q₃ X {x | x ∈ L} s₃ (L[k₃]'hk₃) :=
    hy₃ ▸ hQ₃
  -- Use the internal 3-separation `(A₁, A₂)` to find a path `P_W'` in `H₁` from `V(Q₁) ∪ V(Q₂) ∪
  -- V(Q₃)` to `W₁`.
  have hsep_G₁ : IsGraphSeparation (splitGraph S P s t) A₁ A₂ := hsep_int.1.1.1
  have hL_A₂ : {x | x ∈ L} ⊆ V(A₂) := hbar₁_eq ▸ hsep_int.1.1.2
  have hfin_A₂ : V(A₂).Finite := S₁.finite_V.subset hsep_G₁.2.1.vertexSet_mono
  have hS_and_XL := sep_subset_and_inter_subset_of_three_legs hsep_G₁ hfin_A₂ hX_A₁ hL_A₂
    hsep_int.1.2.1 hQ₁' hQ₂' hQ₃' hd12 hd13 hd23
  have hex_u₀ : ∃ u₀ ∈ V(splitGraph S P s t), u₀ ∉ V(A₂) := by
    by_contra! hsub
    have heq : V(A₂) = V(S₁.G) := Subset.antisymm hsep_G₁.2.1.vertexSet_mono hsub
    exact hsep_int.1.2.2 heq
  obtain ⟨u₀, hu₀G₁, hu₀_not_A₂⟩ := hex_u₀
  have hu₀A₁ : u₀ ∈ V(A₁) := by
    have hu₀_union : u₀ ∈ V(A₁) ∪ V(A₂) := hsep_G₁.2.2.1 ▸ hu₀G₁
    exact hu₀_union.resolve_right hu₀_not_A₂
  have hu₀H₁ : u₀ ∈ V(splitSide S.G P (S.Ω.interval s t)) := by
    rw [vertexSet_splitGraph_eq_union S hs ht hst hP hcatch hnocross] at hu₀G₁
    refine hu₀G₁.resolve_left fun hu₀P => hu₀_not_A₂ (hL_A₂ ?_)
    change u₀ ∈ splitList S hs ht hP
    rw [splitList, List.mem_append]
    left
    rwa [vertexSet_eq_support_pathWalkTS hP, mem_ofPred_eq] at hu₀P
  obtain ⟨v_A, hv_A, k, hk, P_W, _, hmk, _, hPW_ft, hPW_L, _⟩ :=
    exists_fromToPath_in_splitSide S hs ht hst hP hnocross hu₀A₁ hu₀H₁
  have hv_A_S : v_A ∈ V(A₁) ∩ V(A₂) := by
    obtain ⟨v', hv'PW, hv'S⟩ := exists_mem_inter_of_isGraphSeparation_of_path hsep_G₁ hPW_ft.1
      hv_A (hL_A₂ (List.getElem_mem hk))
    have hv'_in : v' ∈ V(P_W) ∩ V(A₁) := ⟨hv'PW, hv'S.1⟩
    rw [hPW_ft.2.1, mem_singleton_iff] at hv'_in
    exact hv'_in ▸ hv'S
  have hv_A_Q : v_A ∈ V(Q₁) ∪ V(Q₂) ∪ V(Q₃) := hS_and_XL.1 hv_A_S
  obtain ⟨z, hzQ, w₁', hw₁'L, P_W', hPW'_le, hPW'_ft⟩ :=
    hPW_ft.1.exists_isFromToPathWithEnds (X := V(Q₁) ∪ V(Q₂) ∪ V(Q₃)) (Y := {x | x ∈ L})
      hv_A_Q (List.getElem_mem hk)
  have hw₁'_eq : w₁' = L[k]'hk := by
    have : w₁' ∈ V(P_W) ∩ {x | x ∈ L} := ⟨hPW'_le.vertexSet_mono hPW'_ft.1.right_mem, hw₁'L⟩
    rwa [hPW_L, mem_singleton_iff] at this
  subst hw₁'_eq
  have hPW'_X : V(P_W') ∩ X ⊆ {z} := by
    rintro x ⟨hxPW', hxX⟩
    have hx_vA : x ∈ V(P_W) ∩ V(A₁) := ⟨hPW'_le.vertexSet_mono hxPW', hX_A₁ hxX⟩
    rw [hPW_ft.2.1, mem_singleton_iff] at hx_vA
    subst hx_vA
    have hv_in : x ∈ V(P_W') ∩ (V(Q₁) ∪ V(Q₂) ∪ V(Q₃)) := ⟨hxPW', hv_A_Q⟩
    rwa [hPW'_ft.2.1, mem_singleton_iff] at hv_in
  have hs₁X : s₁ ∈ X := Or.inl (Or.inl hs₁.1)
  have hs₂X : s₂ ∈ X := Or.inl (Or.inr hs₂.1)
  have hs₃X : s₃ ∈ X := Or.inr hs₃.1
  have hT₁G : IsGraphPathWithEnds S.G T₁ u v := hT₁.mono (splitGraph_le S P s t)
  have hT₂G : IsGraphPathWithEnds S.G T₂ u v := hT₂.mono (splitGraph_le S P s t)
  have hT₃G : IsGraphPathWithEnds S.G T₃ u v := hT₃.mono (splitGraph_le S P s t)
  rcases hzQ with (hzQ₁ | hzQ₂) | hzQ₃
  · obtain ⟨hQ₁_new, hd_12_new, hd_13_new⟩ :=
      replace_leg_by_path hQ₁' hd12 hd13 hzQ₁ hPW'_ft.1 hPW'_ft.2.1 hPW'_X hPW'_ft.2.2
    have ⟨_, hX_L_new⟩ := sep_subset_and_inter_subset_of_three_legs hsep_G₁ hfin_A₂ hX_A₁ hL_A₂
      hsep_int.1.2.1 hQ₂' hQ₃' hQ₁_new hd23 hd_12_new.symm hd_13_new.symm
    obtain ⟨t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩ :=
      redirectsTo_bar_of_one_leg_in_W1 S hs ht hst hP hP_bar hs₂X hs₃X hs₁X
        hs23 hs12.symm hs13.symm hk₂ hk₃ hk hmk hQ₂' hQ₃' hQ₁_new
        hd23 hd_12_new.symm hd_13_new.symm hX_L_new
    have hset_eq : ({s₂, s₃, s₁} : Set α) = {s₁, s₂, s₃} := by
      ext x; simp [or_comm, or_left_comm]
    rw [hset_eq] at hred
    exact hnotripod ⟨T₁, T₂, T₃, u, v, huv, hT₁G, hT₂G, hT₃G,
      hinter_12, hinter_13, hinter_23, s₁, hs₁, s₂, hs₂, s₃, hs₃,
      t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩
  · have hPW'_Q2 : V(P_W') ∩ (V(Q₂) ∪ V(Q₁) ∪ V(Q₃)) = {z} := by
      rw [union_comm V(Q₂) V(Q₁)]
      exact hPW'_ft.2.1
    obtain ⟨hQ₂_new, hd_21_new, hd_23_new⟩ :=
      replace_leg_by_path hQ₂' hd12.symm hd23 hzQ₂ hPW'_ft.1 hPW'_Q2 hPW'_X hPW'_ft.2.2
    have ⟨_, hX_L_new⟩ := sep_subset_and_inter_subset_of_three_legs hsep_G₁ hfin_A₂ hX_A₁ hL_A₂
      hsep_int.1.2.1 hQ₁' hQ₃' hQ₂_new hd13 hd_21_new.symm hd_23_new.symm
    obtain ⟨t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩ :=
      redirectsTo_bar_of_one_leg_in_W1 S hs ht hst hP hP_bar hs₁X hs₃X hs₂X
        hs13 hs12 hs23.symm hk₁ hk₃ hk hmk hQ₁' hQ₃' hQ₂_new
        hd13 hd_21_new.symm hd_23_new.symm hX_L_new
    have hset_eq : ({s₁, s₃, s₂} : Set α) = {s₁, s₂, s₃} := by
      ext x; simp [or_comm]
    rw [hset_eq] at hred
    exact hnotripod ⟨T₁, T₂, T₃, u, v, huv, hT₁G, hT₂G, hT₃G,
      hinter_12, hinter_13, hinter_23, s₁, hs₁, s₂, hs₂, s₃, hs₃,
      t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩
  · have hPW'_Q3 : V(P_W') ∩ (V(Q₃) ∪ V(Q₁) ∪ V(Q₂)) = {z} := by
      have hunion_eq : V(Q₃) ∪ V(Q₁) ∪ V(Q₂) = V(Q₁) ∪ V(Q₂) ∪ V(Q₃) := by
        ext x; simp [mem_union, or_comm, or_left_comm, or_assoc]
      rw [hunion_eq]
      exact hPW'_ft.2.1
    obtain ⟨hQ₃_new, hd_31_new, hd_32_new⟩ :=
      replace_leg_by_path hQ₃' hd13.symm hd23.symm hzQ₃ hPW'_ft.1 hPW'_Q3 hPW'_X hPW'_ft.2.2
    have ⟨_, hX_L_new⟩ := sep_subset_and_inter_subset_of_three_legs hsep_G₁ hfin_A₂ hX_A₁ hL_A₂
      hsep_int.1.2.1 hQ₁' hQ₂' hQ₃_new hd12 hd_31_new.symm hd_32_new.symm
    obtain ⟨t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩ :=
      redirectsTo_bar_of_one_leg_in_W1 S hs ht hst hP hP_bar hs₁X hs₂X hs₃X
        hs12 hs13 hs23 hk₁ hk₂ hk hmk hQ₁' hQ₂' hQ₃_new
        hd12 hd_31_new.symm hd_32_new.symm hX_L_new
    exact hnotripod ⟨T₁, T₂, T₃, u, v, huv, hT₁G, hT₂G, hT₃G,
      hinter_12, hinter_13, hinter_23, s₁, hs₁, s₂, hs₂, s₃, hs₃,
      t₁', ht₁', t₂', ht₂', t₃', ht₃', hred⟩

/-! ## Applying `(2.1)` and the Induction on `|E(G)|` for `(2.4)` -/

/-- In a society `S` whose graph `S.G` is connected and has `2 ≤ S.Ω.bar.ncard`, there exist
distinct `s, t ∈ S.Ω.bar` and an `(s, t)`-path `Q₀` in `S.G` avoiding `S.Ω.bar \ {s, t}`. -/
theorem exists_path_avoiding_bar_diff (S : Society α β)
    (hconn_G : IsGraphConnected S.G) (hbar2 : 2 ≤ S.Ω.bar.ncard) :
    ∃ s ∈ S.Ω.bar, ∃ t ∈ S.Ω.bar, s ≠ t ∧
      ∃ Q₀ : Graph α β, IsGraphPathWithEnds S.G Q₀ s t ∧ Avoids Q₀ (S.Ω.bar \ {s, t}) := by
  obtain ⟨s, hs⟩ := nonempty_of_ncard_ne_zero (by omega : S.Ω.bar.ncard ≠ 0)
  obtain ⟨t₀, ht₀, hst₀⟩ := exists_ne_of_one_lt_ncard (by omega : 1 < S.Ω.bar.ncard) s
  have hst₀' : s ≠ t₀ := hst₀.symm
  obtain ⟨W₀⟩ := hconn_G.2 s (S.bar_subset hs) t₀ (S.bar_subset ht₀)
  obtain ⟨W, hW_simple, _, _⟩ := exists_isSimple_subwalk W₀
  cases W with
  | nil _ => exact (hst₀' rfl).elim
  | @cons s w t₀ e hlink W' =>
    have hnd : (s :: W'.support).Nodup := hW_simple
    obtain ⟨hs_not_W', hW'_simple⟩ := List.nodup_cons.mp hnd
    have ht₀_bar_diff : t₀ ∈ S.Ω.bar \ {s} := ⟨ht₀, fun h => hst₀ (mem_singleton_iff.mp h)⟩
    obtain ⟨w', hw'w, t, ht_diff, Q', _, hVQ'_sub, hQ'_ft⟩ :=
      exists_isFromToPathWithEnds_of_walk W' (X := {w}) (Y := S.Ω.bar \ {s}) rfl ht₀_bar_diff
    rw [mem_singleton_iff] at hw'w
    subst hw'w
    have hs_not_Q' : s ∉ V(Q') := fun hsQ' => hs_not_W' (hVQ'_sub hsQ')
    let W_sw : GraphWalk S.G s w' := .cons hlink (.nil hlink.right_mem)
    have hsw_ne : s ≠ w' := fun h => hs_not_W' (h ▸ W'.start_mem_support)
    have hW_sw_simple : W_sw.IsSimple := by simp [GraphWalk.IsSimple, W_sw, hsw_ne]
    have hP_sw : IsGraphPathWithEnds S.G (walkSubgraph W_sw) s w' :=
      isGraphPathWithEnds_walkSubgraph hW_sw_simple
    have hsw_Q' : V(walkSubgraph W_sw) ∩ V(Q') = {w'} := by
      ext x
      simp only [vertexSet_walkSubgraph, W_sw, GraphWalk.support_cons, GraphWalk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, mem_inter_iff, mem_ofPred_eq,
        mem_singleton_iff]
      refine ⟨fun ⟨hx_sw, hxQ'⟩ => hx_sw.resolve_left fun hxs => hs_not_Q' (hxs ▸ hxQ'), ?_⟩
      rintro rfl
      exact ⟨Or.inr rfl, hQ'_ft.1.left_mem⟩
    let Q₀ := subgraphUnion S.G (walkSubgraph W_sw) Q'
    have hQ₀_path : IsGraphPathWithEnds S.G Q₀ s t :=
      hP_sw.subgraphUnion hQ'_ft.1 hsw_Q'
    refine ⟨s, hs, t, ht_diff.1, Ne.symm ht_diff.2, Q₀, hQ₀_path, ?_⟩
    rw [Avoids, disjoint_left]
    rintro x ⟨hx_bar, hx_ne⟩ hxQ₀
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx_ne
    rw [vertexSet_subgraphUnion] at hxQ₀
    rcases hxQ₀ with hx_sw | hxQ'
    · simp only [vertexSet_walkSubgraph, W_sw, GraphWalk.support_cons, GraphWalk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, mem_ofPred_eq] at hx_sw
      rcases hx_sw with rfl | rfl
      · exact hx_ne.1 rfl
      · have hw_in : x ∈ V(Q') ∩ (S.Ω.bar \ {s}) := ⟨hQ'_ft.1.left_mem, hx_bar, hx_ne.1⟩
        rw [hQ'_ft.2.2, mem_singleton_iff] at hw_in
        exact hx_ne.2 hw_in
    · have hx_in : x ∈ V(Q') ∩ (S.Ω.bar \ {s}) := ⟨hxQ', hx_bar, hx_ne.1⟩
      rw [hQ'_ft.2.2, mem_singleton_iff] at hx_in
      exact hx_ne.2 hx_in

private theorem induced_catches_path_from_path (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hG_loopless : ∀ x : α, ¬ S.G.Adj x x)
    (hG_simple : ∀ e₁ e₂ x y, S.G.IsLink e₁ x y → S.G.IsLink e₂ x y → e₁ = e₂)
    {s t : α} (hst : s ≠ t) {Q₀ : Graph α β}
    (hQ₀ : IsGraphPathWithEnds S.G Q₀ s t) (hQ₀_av : Avoids Q₀ (S.Ω.bar \ {s, t})) :
    ∃ P : Graph α β,
      IsGraphPathWithEnds S.G P s t ∧ P ≤i S.G ∧
      Disjoint (V(P) \ {s, t}) S.Ω.bar ∧
      Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)) := by
  classical
  let Z := S.Ω.bar \ {s, t}
  have hZ_sub : Z ⊆ V(S.G) := sdiff_subset.trans S.bar_subset
  let Good (H : Graph α β) : Prop :=
    H ≤ S.G ∧ Catches Z H ∧ ∃ Q : Graph α β, IsGraphPathWithEnds S.G Q s t ∧ Avoids Q V(H)
  have hGood₀ : Good (S.G.induce Z) := by
    refine ⟨S.G.induce_le hZ_sub, ⟨subset_rfl, fun C hC => ?_⟩, Q₀, hQ₀, hQ₀_av⟩
    obtain ⟨v, hvC⟩ := hC.2.1.1
    exact ⟨v, hC.1.vertexSet_mono hvC, hvC⟩
  have hex_max : ∀ (n : ℕ) {H : Graph α β}, Good H →
      (V(S.G).ncard + E(S.G).ncard) - (V(H).ncard + E(H).ncard) = n →
      ∃ H_m : Graph α β, Good H_m ∧
        ∀ H' : Graph α β, H_m ≤ H' → H' ≤ S.G → Catches Z H' →
          (∃ Q : Graph α β, IsGraphPathWithEnds S.G Q s t ∧ Avoids Q V(H')) → H' = H_m := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro H hGood hmeas
      by_cases hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ S.G → Catches Z H' →
          (∃ Q : Graph α β, IsGraphPathWithEnds S.G Q s t ∧ Avoids Q V(H')) → H' = H
      · exact ⟨H, hGood, hmax⟩
      · push Not at hmax
        obtain ⟨H', hHH', hH'G, hZ', hQ', hne⟩ := hmax
        have hV_le : V(H).ncard ≤ V(H').ncard :=
          ncard_le_ncard hHH'.vertexSet_mono (S.finite_V.subset hH'G.vertexSet_mono)
        have hE_le : E(H).ncard ≤ E(H').ncard :=
          ncard_le_ncard hHH'.edgeSet_mono (S.finite_E.subset hH'G.edgeSet_mono)
        have hV_top : V(H').ncard ≤ V(S.G).ncard :=
          ncard_le_ncard hH'G.vertexSet_mono S.finite_V
        have hE_top : E(H').ncard ≤ E(S.G).ncard :=
          ncard_le_ncard hH'G.edgeSet_mono S.finite_E
        have hlt_sum : V(H).ncard + E(H).ncard < V(H').ncard + E(H').ncard := by
          by_cases hV_eq : V(H) = V(H')
          · have hE_ne : E(H) ≠ E(H') := fun hE_eq =>
              hne ((Compatible.of_le_le le_rfl hHH').ext hV_eq.symm hE_eq.symm)
            have hE_lt : E(H).ncard < E(H').ncard :=
              ncard_lt_ncard ⟨hHH'.edgeSet_mono, fun h => hE_ne (Subset.antisymm hHH'.edgeSet_mono
                h)⟩
                (S.finite_E.subset hH'G.edgeSet_mono)
            omega
          · have hV_lt : V(H).ncard < V(H').ncard :=
              ncard_lt_ncard ⟨hHH'.vertexSet_mono, fun h => hV_eq (Subset.antisymm
                hHH'.vertexSet_mono h)⟩
                (S.finite_V.subset hH'G.vertexSet_mono)
            omega
        exact ih ((V(S.G).ncard + E(S.G).ncard) - (V(H').ncard + E(H').ncard))
          (by omega) ⟨hH'G, hZ', hQ'⟩ rfl
  obtain ⟨H, ⟨hHG, hZH, P, hP, hP_av⟩, hmax⟩ := hex_max _ hGood₀ rfl
  have hPK : IsGraphPathWithEnds (deleteVertices S.G V(H)) P s t :=
    hP.in_deleteVertices hP_av
  rcases theorem_2_1_proof hG_loopless hG_simple hst hHG hZH hmax hPK with hP_eq | hsep2
  · have hP_ind : P ≤i S.G := by
      rw [hP_eq]
      exact ⟨deleteVertices_le S.G V(H), fun e x y hxy hx hy =>
        (deleteVertices_isLink S.G V(H)).mpr ⟨hxy, hx.2, hy.2⟩⟩
    have hVP : V(P) = V(S.G) \ V(H) := by rw [hP_eq]; rfl
    have hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar := by
      rw [disjoint_left]
      rintro x ⟨hxP, hx_st⟩ hx_bar
      have hxZ : x ∈ Z := ⟨hx_bar, hx_st⟩
      exact disjoint_left.mp hP_av (hZH.1 hxZ) hxP
    have hH_le_delP : H ≤ deleteVertices S.G V(P) :=
      le_deleteVertices hHG (by rw [hVP]; exact disjoint_sdiff_right)
    have hV_delP : V(deleteVertices S.G V(P)) = V(H) := by
      ext x
      simp only [vertexSet_deleteVertices, hVP, mem_sdiff]
      exact ⟨fun ⟨hxG, hx_not⟩ => by_contra fun hxH => hx_not ⟨hxG, hxH⟩,
        fun hxH => ⟨hHG.vertexSet_mono hxH, fun ⟨_, hx_not⟩ => hx_not hxH⟩⟩
    have hcatch_delP : Catches Z (deleteVertices S.G V(P)) := by
      refine ⟨hV_delP.symm ▸ hZH.1, fun C hC => ?_⟩
      obtain ⟨v, hvC⟩ := hC.2.1.1
      have hv_delP : v ∈ V(deleteVertices S.G V(P)) := hC.1.vertexSet_mono hvC
      have hvH : v ∈ V(H) := hV_delP ▸ hv_delP
      obtain ⟨z, hzZ, hzv⟩ := hZH.2 (reachableComponent H v) (isGraphComponent_reachableComponent
        hvH)
      have hC_eq : C = reachableComponent (deleteVertices S.G V(P)) v :=
        isGraphComponent_eq_reachableComponent hC hvC
      refine ⟨z, hzZ, ?_⟩
      rw [hC_eq, vertexSet_reachableComponent]
      rw [vertexSet_reachableComponent] at hzv
      rcases hzv with ⟨hzH, ⟨W⟩⟩
      obtain ⟨W', _, _⟩ := exists_walk_up_of_le hH_le_delP W
      exact ⟨hH_le_delP.vertexSet_mono hzH, ⟨W'⟩⟩
    exact ⟨P, hP, hP_ind, hP_bar, hcatch_delP⟩
  · obtain ⟨G₁, G₂, hsep, hst_G₁, hcard2, _, _, hHG₁, hVG₁_ne⟩ := hsep2
    have hbar_G₁ : S.Ω.bar ⊆ V(G₁) := by
      intro x hx_bar
      by_cases hx_st : x ∈ ({s, t} : Set α)
      · exact hst_G₁ hx_st
      · exact hHG₁.vertexSet_mono (hZH.1 ⟨hx_bar, hx_st⟩)
    have hsep_S : S.IsKSeparation 2 G₂ G₁ :=
      ⟨⟨IsGraphSeparation.symm hsep, hbar_G₁⟩, by rw [inter_comm, hcard2], hVG₁_ne⟩
    exact (hconn 2 (by omega) G₂ G₁ hsep_S).elim

/-- **Graph Minors IX, (2.4)** (page 45):
"We may choose distinct $s, t \in \bar{\Omega}$ such that there is a path between $s$ and $t$
avoiding $Z$, where $Z = \bar{\Omega} - \{s, t\}$. We apply (2.1), and deduce that there is a path
$P$ joining $s$ and $t$ such that $P$ is an induced subgraph of $G$ and $Z$ catches
$G \setminus V(P)$. In particular, no internal vertex of $P$ is in $\bar{\Omega}$." -/
theorem exists_induced_catches_path_of_three_connected (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hconn_G : IsGraphConnected S.G)
    (hG_loopless : ∀ x : α, ¬ S.G.Adj x x)
    (hG_simple : ∀ e₁ e₂ x y, S.G.IsLink e₁ x y → S.G.IsLink e₂ x y → e₁ = e₂)
    (hbar3 : 3 ≤ S.Ω.bar.ncard) :
    ∃ s ∈ S.Ω.bar, ∃ t ∈ S.Ω.bar, s ≠ t ∧
      ∃ P : Graph α β,
        IsGraphPathWithEnds S.G P s t ∧
        P ≤i S.G ∧
        Disjoint (V(P) \ {s, t}) S.Ω.bar ∧
        Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)) := by
  classical
  obtain ⟨s, hs, t, ht, hst, Q₀, hQ₀, hQ₀_av⟩ :=
    exists_path_avoiding_bar_diff S hconn_G (by omega)
  exact ⟨s, hs, t, ht, hst, induced_catches_path_from_path S hconn hG_loopless hG_simple
    hst hQ₀ hQ₀_av⟩

/-! ## Module 1: Walk Uniqueness on a Path, Simple Reduction, and 3-Connected Base Lemmas -/

/-- Any simple walk `W₂` from `u` to `v` in a graph `P` whose vertices and edges are those of a
simple walk `W₁ : GraphWalk P u v` has the same support as `W₁`. -/
theorem support_eq_of_isSimple_of_subset {P : Graph α β} {u v : α}
    (W₁ W₂ : GraphWalk P u v) (h₁ : W₁.IsSimple) (h₂ : W₂.IsSimple)
    (hE : ∀ e ∈ W₂.edges, e ∈ W₁.edges) :
    W₂.support = W₁.support := by
  induction W₁ with
  | @nil u hu =>
    have hlen : W₂.length = 0 := h₂.length_eq_zero
    cases W₂ with
    | nil _ => rfl
    | cons _ _ => simp at hlen
  | @cons u w v e hlink₁ W₁' ih =>
    have hnd₁ : (u :: W₁'.support).Nodup := h₁
    obtain ⟨hu_not₁, h₁'⟩ := List.nodup_cons.mp hnd₁
    cases W₂ with
    | nil _ =>
      exact (hu_not₁ W₁'.end_mem_support).elim
    | @cons u w' v f hlink₂ W₂' =>
      have hnd₂ : (u :: W₂'.support).Nodup := h₂
      obtain ⟨hu_not₂, h₂'⟩ := List.nodup_cons.mp hnd₂
      have hf_in : f ∈ e :: W₁'.edges := hE f (by simp)
      have hf_eq : f = e := by
        rcases List.mem_cons.mp hf_in with rfl | hf'
        · rfl
        · exfalso
          exact hu_not₁ (W₁'.left_mem_support_of_mem_edges hf' hlink₂)
      have hw'_eq : w' = w := by
        have hlink₂' : P.IsLink e u w' := hf_eq ▸ hlink₂
        rcases hlink₂'.eq_and_eq_or_eq_and_eq hlink₁ with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · rfl
        · exact (hu_not₁ W₁'.start_mem_support).elim
      subst hw'_eq
      have hE' : ∀ g ∈ W₂'.edges, g ∈ W₁'.edges := by
        intro g hg
        have hg_in : g ∈ e :: W₁'.edges := hE g (by simp [hg])
        rcases List.mem_cons.mp hg_in with rfl | hg'
        · exfalso
          exact hu_not₂ (W₂'.left_mem_support_of_mem_edges hg hlink₁)
        · exact hg'
      simp [ih W₂' h₁' h₂' hE']

theorem support_pathWalkTS_symm {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) :
    (pathWalkTS hP.symm).support = (pathWalkTS hP).support.reverse := by
  have h₁ : (pathWalkTS hP).reverse.IsSimple := (isSimple_pathWalkTS hP).reverse
  have h₂ : (pathWalkTS hP.symm).IsSimple := isSimple_pathWalkTS hP.symm
  have hE : ∀ e ∈ (pathWalkTS hP.symm).edges, e ∈ (pathWalkTS hP).reverse.edges := by
    intro e he
    rw [GraphWalk.edges_reverse, List.mem_reverse]
    have heP : e ∈ E(P) := by rw [edgeSet_eq_edges_pathWalkTS hP.symm]; exact he
    rwa [edgeSet_eq_edges_pathWalkTS hP] at heP
  rw [← GraphWalk.support_reverse]
  exact support_eq_of_isSimple_of_subset (pathWalkTS hP).reverse (pathWalkTS hP.symm) h₁ h₂ hE

/-- Every edge of a walk `W` links consecutive vertices `W.support[k]` and `W.support[k+1]`. -/
theorem exists_consecutive_of_mem_edges {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) {e : β} (he : e ∈ W.edges) :
    ∃ (k : ℕ) (hk : k + 1 < W.support.length),
      G.IsLink e (W.support[k]'(Nat.lt_trans (Nat.lt_succ_self k) hk)) (W.support[k + 1]'hk) := by
  induction W with
  | nil _ => simp at he
  | @cons u w v f hlink W' ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · refine ⟨0, by cases W' <;> simp, ?_⟩
      have h1 : (u :: W'.support)[1]'(by cases W' <;> simp) = w := by
        cases W' <;> rfl
      simpa [h1] using hlink
    · obtain ⟨k, hk, hlink_k⟩ := ih he'
      refine ⟨k + 1, by simp; omega, ?_⟩
      simpa using hlink_k

/-- If two vertices are adjacent in `P` (`IsGraphPathWithEnds G P s t`), they are consecutive
vertices along `(pathWalkTS hP).support`. -/
theorem exists_support_index_of_adj_pathWalkTS {G P : Graph α β} {s t x y : α}
    (hP : IsGraphPathWithEnds G P s t) (hadj : P.Adj x y) :
    ∃ (k : ℕ) (hk : k + 1 < (pathWalkTS hP).support.length),
      ({x, y} : Set α) =
        {(pathWalkTS hP).support[k]'(Nat.lt_trans (Nat.lt_succ_self k) hk),
         (pathWalkTS hP).support[k + 1]'hk} := by
  obtain ⟨e, hxy⟩ := hadj
  have he : e ∈ (pathWalkTS hP).edges := by
    have heP : e ∈ E(P) := hxy.edge_mem
    rwa [edgeSet_eq_edges_pathWalkTS hP] at heP
  obtain ⟨k, hk, hlink_k⟩ := exists_consecutive_of_mem_edges (pathWalkTS hP) he
  refine ⟨k, hk, ?_⟩
  rcases hxy.eq_and_eq_or_eq_and_eq hlink_k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact pair_comm _ _

/-- In a 3-connected society `S` with `E(S.G) = ∅`, every vertex of `S.G` is in `S.Ω.bar`. -/
theorem vertexSet_eq_bar_of_edgeSet_eq_empty (S : Society α β)
    (hconn : S.IsKConnected 3) (hE : E(S.G) = ∅) :
    V(S.G) = S.Ω.bar := by
  refine Subset.antisymm (fun v hvG => ?_) S.bar_subset
  by_contra hv_not_bar
  let G₁ := (S.G.induce {v}).restrict ∅
  let G₂ := deleteVertices S.G {v}
  have hG₁_le : G₁ ≤ S.G := restrict_le.trans (S.G.induce_le (singleton_subset_iff.mpr hvG))
  have hG₂_le : G₂ ≤ S.G := deleteVertices_le S.G {v}
  have hV_union : V(G₁) ∪ V(G₂) = V(S.G) := by
    ext x
    simp only [G₁, G₂, vertexSet_restrict, vertexSet_induce, vertexSet_deleteVertices,
      mem_union, mem_singleton_iff, mem_sdiff]
    exact ⟨fun h => h.elim (fun hxv => hxv ▸ hvG) And.left,
      fun hxG => by_cases (fun hxv : x = v => Or.inl hxv) (fun hxv => Or.inr ⟨hxG, hxv⟩)⟩
  have hE_union : E(G₁) ∪ E(G₂) = E(S.G) := by
    refine Subset.antisymm (union_subset hG₁_le.edgeSet_mono hG₂_le.edgeSet_mono) ?_
    rw [hE]
    exact empty_subset _
  have hE_disj : Disjoint E(G₁) E(G₂) := by
    have : E(G₁) = ∅ := by simp [G₁]
    rw [this]
    exact disjoint_bot_left
  have hbar_G₂ : S.Ω.bar ⊆ V(G₂) := by
    intro x hx_bar
    exact ⟨S.bar_subset hx_bar, fun hxv => hv_not_bar (mem_singleton_iff.mp hxv ▸ hx_bar)⟩
  have hinter_empty : V(G₁) ∩ V(G₂) = ∅ := by
    ext x
    simp [G₁, G₂]
  have hcard0 : (V(G₁) ∩ V(G₂)).ncard ≤ 0 := by
    rw [hinter_empty, ncard_empty]
  have hVG₂_ne : V(G₂) ≠ V(S.G) := by
    intro heq
    have hvG₂ : v ∈ V(G₂) := heq.symm ▸ hvG
    exact hvG₂.2 (mem_singleton v)
  have hsep : S.IsKSeparation 0 G₁ G₂ :=
    ⟨⟨⟨hG₁_le, hG₂_le, hV_union, hE_union, hE_disj⟩, hbar_G₂⟩, hcard0, hVG₂_ne⟩
  exact hconn 0 (by omega) G₁ G₂ hsep

/-- In a 3-connected loopless society `S` with `E(S.G).Nonempty`, there exist distinct
`s, t ∈ S.Ω.bar` and an `(s, t)`-path `Q₀` in `S.G` avoiding `S.Ω.bar \ {s, t}`. -/
theorem exists_path_avoiding_bar_diff_of_three_connected (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hG_loopless : ∀ x : α, ¬ S.G.Adj x x)
    (hE : E(S.G).Nonempty) :
    ∃ s ∈ S.Ω.bar, ∃ t ∈ S.Ω.bar, s ≠ t ∧
      ∃ Q₀ : Graph α β, IsGraphPathWithEnds S.G Q₀ s t ∧ Avoids Q₀ (S.Ω.bar \ {s, t}) := by
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨u, v, huv_link⟩ := S.G.exists_isLink_of_mem_edgeSet he₀
  have huv_ne : u ≠ v := fun h => hG_loopless u ⟨e₀, h ▸ huv_link⟩
  let C₀ := reachableComponent S.G u
  have huC₀ : u ∈ V(C₀) := self_mem_reachableComponent huv_link.left_mem
  have hvC₀ : v ∈ V(C₀) := by
    rw [vertexSet_reachableComponent]
    exact ⟨huv_link.right_mem, ⟨.cons huv_link (.nil huv_link.right_mem)⟩⟩
  have hex_walk : ∃ s ∈ S.Ω.bar, ∃ t₀ ∈ S.Ω.bar, s ≠ t₀ ∧ Nonempty (GraphWalk S.G s t₀) := by
    by_cases hsub_bar : V(C₀) ⊆ S.Ω.bar
    · exact ⟨u, hsub_bar huC₀, v, hsub_bar hvC₀, huv_ne,
        ⟨.cons huv_link (.nil huv_link.right_mem)⟩⟩
    · obtain ⟨w₀, hw₀C₀, hw₀_not_bar⟩ := not_subset.mp hsub_bar
      have hcard2 : 2 ≤ (V(C₀) ∩ S.Ω.bar).ncard := by
        by_contra hlt2
        let G₁ := C₀
        let G₂ := (S.G.induce ((V(S.G) \ V(C₀)) ∪ S.Ω.bar)).restrict (E(S.G) \ E(C₀))
        have hC₀_comp : IsGraphComponent C₀ S.G :=
          isGraphComponent_reachableComponent huv_link.left_mem
        have hG₁_le : G₁ ≤ S.G := hC₀_comp.1
        have hG₂_le : G₂ ≤ S.G :=
          restrict_le.trans (S.G.induce_le (union_subset sdiff_subset S.bar_subset))
        have hV_union : V(G₁) ∪ V(G₂) = V(S.G) := by
          ext x
          simp only [G₁, G₂, vertexSet_restrict, vertexSet_induce, mem_union, mem_sdiff]
          exact ⟨fun h => h.elim (fun hx => hG₁_le.vertexSet_mono hx)
              (fun h2 => h2.elim And.left (fun hx => S.bar_subset hx)),
            fun hxG => by_cases (fun hxC : x ∈ V(C₀) => Or.inl hxC)
              (fun hxC => Or.inr (Or.inl ⟨hxG, hxC⟩))⟩
        have hE_G₂ : E(G₂) = E(S.G) \ E(C₀) := by
          unfold G₂
          rw [edgeSet_restrict, inter_eq_right]
          rintro e ⟨heG, he_not_C₀⟩
          obtain ⟨x, y, hxy⟩ := S.G.exists_isLink_of_mem_edgeSet heG
          have hx_not_C₀ : x ∉ V(C₀) := by
            intro hxC₀
            have hC₀_closed : C₀ ≤c S.G := isClosedSubgraph_of_isGraphComponent hC₀_comp
            have hyC₀ : y ∈ V(C₀) := (mem_graphComponent_iff_of_isLink hC₀_comp hxy).mp hxC₀
            have hxy_C₀ : C₀.IsLink e x y :=
              hC₀_closed.isInducedSubgraph.isLink_of_mem_mem hxy hxC₀ hyC₀
            exact he_not_C₀ hxy_C₀.edge_mem
          have hy_not_C₀ : y ∉ V(C₀) := fun hyC₀ =>
            hx_not_C₀ ((mem_graphComponent_iff_of_isLink hC₀_comp hxy).mpr hyC₀)
          exact ⟨x, y, hxy, Or.inl ⟨hxy.left_mem, hx_not_C₀⟩, Or.inl ⟨hxy.right_mem, hy_not_C₀⟩⟩
        have hE_union : E(G₁) ∪ E(G₂) = E(S.G) := by
          rw [hE_G₂]
          ext e
          simp only [mem_union, mem_sdiff]
          exact ⟨fun h => h.elim (fun he => hG₁_le.edgeSet_mono he) And.left,
            fun he => by_cases (fun he1 : e ∈ E(G₁) => Or.inl he1) (fun he1 => Or.inr ⟨he, he1⟩)⟩
        have hE_disj : Disjoint E(G₁) E(G₂) := by
          rw [hE_G₂]
          exact disjoint_sdiff_right
        have hbar_G₂ : S.Ω.bar ⊆ V(G₂) := fun x hx => Or.inr hx
        have hinter_eq : V(G₁) ∩ V(G₂) = V(C₀) ∩ S.Ω.bar := by
          ext x
          simp only [G₁, G₂, vertexSet_restrict, vertexSet_induce, mem_inter_iff, mem_union,
            mem_sdiff]
          exact ⟨fun ⟨hxC, h⟩ => ⟨hxC, h.resolve_left fun ⟨_, hx_not⟩ => hx_not hxC⟩,
            fun ⟨hxC, hx_bar⟩ => ⟨hxC, Or.inr hx_bar⟩⟩
        have hVG₂_ne : V(G₂) ≠ V(S.G) := by
          intro heq
          have hw₀G₂ : w₀ ∈ V(G₂) := heq.symm ▸ hG₁_le.vertexSet_mono hw₀C₀
          rcases hw₀G₂ with ⟨_, hw₀_not⟩ | hw₀_bar
          · exact hw₀_not hw₀C₀
          · exact hw₀_not_bar hw₀_bar
        have hsep : S.IsKSeparation 1 G₁ G₂ :=
          ⟨⟨⟨hG₁_le, hG₂_le, hV_union, hE_union, hE_disj⟩, hbar_G₂⟩,
            by rw [hinter_eq]; omega, hVG₂_ne⟩
        exact hconn 1 (by omega) G₁ G₂ hsep
      obtain ⟨s, hs_in⟩ := nonempty_of_ncard_ne_zero (by omega : (V(C₀) ∩ S.Ω.bar).ncard ≠ 0)
      obtain ⟨t₀, ht₀_in, hst₀⟩ := exists_ne_of_one_lt_ncard (by omega : 1 <
        (V(C₀) ∩ S.Ω.bar).ncard) s
      obtain ⟨W_C₀⟩ := (isGraphConnected_reachableComponent huv_link.left_mem).2 s hs_in.1 t₀
        ht₀_in.1
      obtain ⟨W₀, _, _⟩ := exists_walk_up_of_le (reachableComponent_le S.G u) W_C₀
      exact ⟨s, hs_in.2, t₀, ht₀_in.2, hst₀.symm, ⟨W₀⟩⟩
  obtain ⟨s, hs, t₀, ht₀, hst₀', ⟨W₀⟩⟩ := hex_walk
  have hst₀ : t₀ ≠ s := hst₀'.symm
  obtain ⟨W, hW_simple, _, _⟩ := exists_isSimple_subwalk W₀
  cases W with
  | nil _ => exact (hst₀' rfl).elim
  | @cons s w t₀ e hlink W' =>
    have hnd : (s :: W'.support).Nodup := hW_simple
    obtain ⟨hs_not_W', _⟩ := List.nodup_cons.mp hnd
    have ht₀_bar_diff : t₀ ∈ S.Ω.bar \ {s} := ⟨ht₀, fun h => hst₀ (mem_singleton_iff.mp h)⟩
    obtain ⟨w', hw'w, t, ht_diff, Q', _, hVQ'_sub, hQ'_ft⟩ :=
      exists_isFromToPathWithEnds_of_walk W' (X := {w}) (Y := S.Ω.bar \ {s}) rfl ht₀_bar_diff
    rw [mem_singleton_iff] at hw'w
    subst hw'w
    have hs_not_Q' : s ∉ V(Q') := fun hsQ' => hs_not_W' (hVQ'_sub hsQ')
    let W_sw : GraphWalk S.G s w' := .cons hlink (.nil hlink.right_mem)
    have hsw_ne : s ≠ w' := fun h => hs_not_W' (h ▸ W'.start_mem_support)
    have hW_sw_simple : W_sw.IsSimple := by simp [GraphWalk.IsSimple, W_sw, hsw_ne]
    have hP_sw : IsGraphPathWithEnds S.G (walkSubgraph W_sw) s w' :=
      isGraphPathWithEnds_walkSubgraph hW_sw_simple
    have hsw_Q' : V(walkSubgraph W_sw) ∩ V(Q') = {w'} := by
      ext x
      simp only [vertexSet_walkSubgraph, W_sw, GraphWalk.support_cons, GraphWalk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, mem_inter_iff, mem_ofPred_eq,
        mem_singleton_iff]
      refine ⟨fun ⟨hx_sw, hxQ'⟩ => hx_sw.resolve_left fun hxs => hs_not_Q' (hxs ▸ hxQ'), ?_⟩
      rintro rfl
      exact ⟨Or.inr rfl, hQ'_ft.1.left_mem⟩
    let Q₀ := subgraphUnion S.G (walkSubgraph W_sw) Q'
    have hQ₀_path : IsGraphPathWithEnds S.G Q₀ s t :=
      hP_sw.subgraphUnion hQ'_ft.1 hsw_Q'
    refine ⟨s, hs, t, ht_diff.1, Ne.symm ht_diff.2, Q₀, hQ₀_path, ?_⟩
    rw [Avoids, disjoint_left]
    rintro x ⟨hx_bar, hx_ne⟩ hxQ₀
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx_ne
    rw [vertexSet_subgraphUnion] at hxQ₀
    rcases hxQ₀ with hx_sw | hxQ'
    · simp only [vertexSet_walkSubgraph, W_sw, GraphWalk.support_cons, GraphWalk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, mem_ofPred_eq] at hx_sw
      rcases hx_sw with rfl | rfl
      · exact hx_ne.1 rfl
      · have hw_in : x ∈ V(Q') ∩ (S.Ω.bar \ {s}) := ⟨hQ'_ft.1.left_mem, hx_bar, hx_ne.1⟩
        rw [hQ'_ft.2.2, mem_singleton_iff] at hw_in
        exact hx_ne.2 hw_in
    · have hx_in : x ∈ V(Q') ∩ (S.Ω.bar \ {s}) := ⟨hxQ', hx_bar, hx_ne.1⟩
      rw [hQ'_ft.2.2, mem_singleton_iff] at hx_in
      exact hx_ne.2 hx_in

theorem exists_induced_catches_path_of_three_connected_nonempty (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hG_loopless : ∀ x : α, ¬ S.G.Adj x x)
    (hG_simple : ∀ e₁ e₂ x y, S.G.IsLink e₁ x y → S.G.IsLink e₂ x y → e₁ = e₂)
    (hE : E(S.G).Nonempty) :
    ∃ s ∈ S.Ω.bar, ∃ t ∈ S.Ω.bar, s ≠ t ∧
      ∃ P : Graph α β,
        IsGraphPathWithEnds S.G P s t ∧
        P ≤i S.G ∧
        Disjoint (V(P) \ {s, t}) S.Ω.bar ∧
        Catches (S.Ω.bar \ {s, t}) (deleteVertices S.G V(P)) := by
  classical
  obtain ⟨s, hs, t, ht, hst, Q₀, hQ₀, hQ₀_av⟩ :=
    exists_path_avoiding_bar_diff_of_three_connected S hconn hG_loopless hE
  exact ⟨s, hs, t, ht, hst, induced_catches_path_from_path S hconn hG_loopless hG_simple
    hst hQ₀ hQ₀_av⟩

theorem RedirectsTo.mono {G H : Graph α β} (hle : H ≤ G) {X Y X' Y' : Set α}
    (h : RedirectsTo H X Y X' Y') : RedirectsTo G X Y X' Y' := by
  rcases h with ⟨hX', hY', hcard, P, hdisj, hP⟩
  exact ⟨hX', hY', hcard, P, hdisj, fun i =>
    let ⟨x, hx, y, hy, hft⟩ := hP i
    ⟨x, hx, y, hy, hft.1.mono hle, hft.2⟩⟩

theorem isCross_mono_of_le {S₀ S : Society α β} (hle : S₀.G ≤ S.G) (hΩ : S₀.Ω = S.Ω)
    {Q₁ Q₂ : Graph α β} (h : S₀.IsCross Q₁ Q₂) : S.IsCross Q₁ Q₂ := by
  rcases h with ⟨hdisj, s₁, t₁, s₂, t₂, ⟨hP₁, hne₁, hs₁, ht₁⟩, ⟨hP₂, hne₂, hs₂, ht₂⟩, hcross⟩
  rw [hΩ] at hs₁ ht₁ hs₂ ht₂ hcross
  exact ⟨hdisj, s₁, t₁, s₂, t₂, ⟨hP₁.mono hle, hne₁, hs₁, ht₁⟩,
    ⟨hP₂.mono hle, hne₂, hs₂, ht₂⟩, hcross⟩

theorem isTripod_mono_of_le {S₀ S : Society α β} (hle : S₀.G ≤ S.G) (hΩ : S₀.Ω = S.Ω)
    {T₁ T₂ T₃ : Graph α β} (h : S₀.IsTripod T₁ T₂ T₃) : S.IsTripod T₁ T₂ T₃ := by
  rcases h with ⟨u, v, huv, h₁, h₂, h₃, hi12, hi13, hi23,
    s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, ht₁, t₂, ht₂, t₃, ht₃, hred⟩
  rw [hΩ] at ht₁ ht₂ ht₃ hred
  exact ⟨u, v, huv, h₁.mono hle, h₂.mono hle, h₃.mono hle, hi12, hi13, hi23,
    s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, ht₁, t₂, ht₂, t₃, ht₃, hred.mono hle⟩

/-- Deleting a loop or a parallel duplicate edge `e₀` preserves `IsKConnected k`. -/
theorem isKConnected_restrict_sdiff_singleton (S : Society α β) (k : ℕ)
    (hconn : S.IsKConnected k) {e₀ : β} {u v : α}
    (he₀_link : S.G.IsLink e₀ u v)
    (hred : u = v ∨ ∃ e₁ : β, e₁ ≠ e₀ ∧ S.G.IsLink e₁ u v) :
    (Society.mk (S.G.restrict (E(S.G) \ {e₀})) S.Ω S.finite_V
      (S.finite_E.subset restrict_le.edgeSet_mono) S.bar_subset).IsKConnected k := by
  let S' : Society α β := ⟨S.G.restrict (E(S.G) \ {e₀}), S.Ω, S.finite_V,
    S.finite_E.subset restrict_le.edgeSet_mono, S.bar_subset⟩
  have hE_S' : E(S'.G) = E(S.G) \ {e₀} := by
    change E(S.G.restrict (E(S.G) \ {e₀})) = _
    rw [edgeSet_restrict, inter_eq_right]
    exact sdiff_subset
  intro k' hk' G₁ G₂ hsep
  rcases hsep with ⟨⟨⟨hG₁_le, hG₂_le, hV_union, hE_union, hE_disj⟩, hbar_G₂⟩, hcard, hVG₂_ne⟩
  have hG₁_G : G₁ ≤ S.G := hG₁_le.trans restrict_le
  have hG₂_G : G₂ ≤ S.G := hG₂_le.trans restrict_le
  have he₀_not_S' : e₀ ∉ E(S'.G) := by
    rw [hE_S']
    exact fun h => h.2 (mem_singleton e₀)
  have he₀_not_G₁ : e₀ ∉ E(G₁) := fun h => he₀_not_S' (hG₁_le.edgeSet_mono h)
  have he₀_not_G₂ : e₀ ∉ E(G₂) := fun h => he₀_not_S' (hG₂_le.edgeSet_mono h)
  have huv_side : (u ∈ V(G₁) ∧ v ∈ V(G₁)) ∨ (u ∈ V(G₂) ∧ v ∈ V(G₂)) := by
    rcases hred with rfl | ⟨e₁, he₁_ne, he₁_link⟩
    · have hu_in : u ∈ V(G₁) ∪ V(G₂) := by rw [hV_union]; exact he₀_link.left_mem
      rcases hu_in with hu₁ | hu₂
      · exact Or.inl ⟨hu₁, hu₁⟩
      · exact Or.inr ⟨hu₂, hu₂⟩
    · have he₁_S' : e₁ ∈ E(S'.G) := by
        rw [hE_S']
        exact ⟨he₁_link.edge_mem, fun h => he₁_ne (mem_singleton_iff.mp h)⟩
      have he₁_link' : S'.G.IsLink e₁ u v := (restrict_le.isLink_iff he₁_S').mpr he₁_link
      have he₁_union : e₁ ∈ E(G₁) ∪ E(G₂) := hE_union.symm ▸ he₁_S'
      rcases he₁_union with he₁_1 | he₁_2
      · have hl1 : G₁.IsLink e₁ u v := (hG₁_le.isLink_iff he₁_1).mpr he₁_link'
        exact Or.inl ⟨hl1.left_mem, hl1.right_mem⟩
      · have hl2 : G₂.IsLink e₁ u v := (hG₂_le.isLink_iff he₁_2).mpr he₁_link'
        exact Or.inr ⟨hl2.left_mem, hl2.right_mem⟩
  rcases huv_side with ⟨hu₁, hv₁⟩ | ⟨hu₂, hv₂⟩
  · let G₁' := (S.G.induce V(G₁)).restrict (insert e₀ E(G₁))
    have hG₁'_le : G₁' ≤ S.G := restrict_le.trans (S.G.induce_le hG₁_G.vertexSet_mono)
    have hE_G₁' : E(G₁') = insert e₀ E(G₁) := by
      unfold G₁'
      rw [edgeSet_restrict, inter_eq_right]
      rintro e (rfl | he₁)
      · exact ⟨u, v, he₀_link, hu₁, hv₁⟩
      · obtain ⟨x, y, hxy⟩ := G₁.exists_isLink_of_mem_edgeSet he₁
        exact ⟨x, y, hxy.mono hG₁_G, hxy.left_mem, hxy.right_mem⟩
    have hE_union' : E(G₁') ∪ E(G₂) = E(S.G) := by
      rw [hE_G₁', insert_union, hE_union, hE_S', insert_sdiff_singleton,
        insert_eq_of_mem he₀_link.edge_mem]
    have hE_disj' : Disjoint E(G₁') E(G₂) := by
      rw [hE_G₁', disjoint_insert_left]
      exact ⟨he₀_not_G₂, hE_disj⟩
    have hsep' : S.IsKSeparation k' G₁' G₂ :=
      ⟨⟨⟨hG₁'_le, hG₂_G, hV_union, hE_union', hE_disj'⟩, hbar_G₂⟩, hcard, hVG₂_ne⟩
    exact hconn k' hk' G₁' G₂ hsep'
  · let G₂' := (S.G.induce V(G₂)).restrict (insert e₀ E(G₂))
    have hG₂'_le : G₂' ≤ S.G := restrict_le.trans (S.G.induce_le hG₂_G.vertexSet_mono)
    have hE_G₂' : E(G₂') = insert e₀ E(G₂) := by
      unfold G₂'
      rw [edgeSet_restrict, inter_eq_right]
      rintro e (rfl | he₂)
      · exact ⟨u, v, he₀_link, hu₂, hv₂⟩
      · obtain ⟨x, y, hxy⟩ := G₂.exists_isLink_of_mem_edgeSet he₂
        exact ⟨x, y, hxy.mono hG₂_G, hxy.left_mem, hxy.right_mem⟩
    have hE_union' : E(G₁) ∪ E(G₂') = E(S.G) := by
      rw [hE_G₂', union_insert, hE_union, hE_S', insert_sdiff_singleton,
        insert_eq_of_mem he₀_link.edge_mem]
    have hE_disj' : Disjoint E(G₁) E(G₂') := by
      rw [hE_G₂', disjoint_insert_right]
      exact ⟨he₀_not_G₁, hE_disj⟩
    have hsep' : S.IsKSeparation k' G₁ G₂' :=
      ⟨⟨⟨hG₁_G, hG₂'_le, hV_union, hE_union', hE_disj'⟩, hbar_G₂⟩, hcard, hVG₂_ne⟩
    exact hconn k' hk' G₁ G₂' hsep'

/-- Every 3-connected society `S` with no cross or tripod admits a simple spanning reduction `S₀`
preserving 3-connectivity, no-cross, no-tripod, and non-loop adjacency. -/
theorem exists_simple_reduction (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃) :
    ∃ S₀ : Society α β,
      S₀.G ≤ S.G ∧
      V(S₀.G) = V(S.G) ∧
      S₀.Ω = S.Ω ∧
      S₀.IsKConnected 3 ∧
      (¬ ∃ Q₁ Q₂ : Graph α β, S₀.IsCross Q₁ Q₂) ∧
      (¬ ∃ T₁ T₂ T₃ : Graph α β, S₀.IsTripod T₁ T₂ T₃) ∧
      (∀ x : α, ¬ S₀.G.Adj x x) ∧
      (∀ e₁ e₂ x y, S₀.G.IsLink e₁ x y → S₀.G.IsLink e₂ x y → e₁ = e₂) ∧
      (∀ e x y, S.G.IsLink e x y → x = y ∨ S₀.G.Adj x y) := by
  suffices h : ∀ (n : ℕ) (S' : Society α β), E(S'.G).ncard = n →
      S'.IsKConnected 3 →
      (¬ ∃ Q₁ Q₂ : Graph α β, S'.IsCross Q₁ Q₂) →
      (¬ ∃ T₁ T₂ T₃ : Graph α β, S'.IsTripod T₁ T₂ T₃) →
      ∃ S₀ : Society α β,
        S₀.G ≤ S'.G ∧
        V(S₀.G) = V(S'.G) ∧
        S₀.Ω = S'.Ω ∧
        S₀.IsKConnected 3 ∧
        (¬ ∃ Q₁ Q₂ : Graph α β, S₀.IsCross Q₁ Q₂) ∧
        (¬ ∃ T₁ T₂ T₃ : Graph α β, S₀.IsTripod T₁ T₂ T₃) ∧
        (∀ x : α, ¬ S₀.G.Adj x x) ∧
        (∀ e₁ e₂ x y, S₀.G.IsLink e₁ x y → S₀.G.IsLink e₂ x y → e₁ = e₂) ∧
        (∀ e x y, S'.G.IsLink e x y → x = y ∨ S₀.G.Adj x y) from
    h E(S.G).ncard S rfl hconn hnocross hnotripod
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro S' hn hconn' hnocross' hnotripod'
    by_cases hG_loopless : ∀ x : α, ¬ S'.G.Adj x x
    · by_cases hG_simple : ∀ e₁ e₂ x y, S'.G.IsLink e₁ x y → S'.G.IsLink e₂ x y → e₁ = e₂
      · exact ⟨S', le_rfl, rfl, rfl, hconn', hnocross', hnotripod', hG_loopless, hG_simple,
          fun e x y hxy => Or.inr ⟨e, hxy⟩⟩
      · push Not at hG_simple
        obtain ⟨e₀, e₁, u, v, he₀, he₁, hne⟩ := hG_simple
        let S₁ : Society α β := ⟨S'.G.restrict (E(S'.G) \ {e₀}), S'.Ω, S'.finite_V,
          S'.finite_E.subset restrict_le.edgeSet_mono, S'.bar_subset⟩
        have hE_S₁ : E(S₁.G) = E(S'.G) \ {e₀} := by
          change E(S'.G.restrict (E(S'.G) \ {e₀})) = _
          rw [edgeSet_restrict, inter_eq_right]
          exact sdiff_subset
        have hlt : E(S₁.G).ncard < n := by
          rw [← hn, hE_S₁]
          exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h he₀.edge_mem).2 (mem_singleton e₀)⟩
            S'.finite_E
        have hconn₁ : S₁.IsKConnected 3 :=
          isKConnected_restrict_sdiff_singleton S' 3 hconn' he₀ (Or.inr ⟨e₁, hne.symm, he₁⟩)
        have hnocross₁ : ¬ ∃ Q₁ Q₂ : Graph α β, S₁.IsCross Q₁ Q₂ :=
          fun ⟨Q₁, Q₂, hc⟩ => hnocross' ⟨Q₁, Q₂, isCross_mono_of_le (S₀ := S₁) (S
            := S') restrict_le rfl hc⟩
        have hnotripod₁ : ¬ ∃ T₁ T₂ T₃ : Graph α β, S₁.IsTripod T₁ T₂ T₃ :=
          fun ⟨T₁, T₂, T₃, ht⟩ => hnotripod' ⟨T₁, T₂, T₃, isTripod_mono_of_le (S₀ := S₁) (S
            := S') restrict_le rfl ht⟩
        obtain ⟨S₀, hle₀, hV₀, hΩ₀, hc₀, hnc₀, hnt₀, hloop₀, hsimp₀, hadj₀⟩ :=
          ih _ hlt S₁ rfl hconn₁ hnocross₁ hnotripod₁
        refine ⟨S₀, hle₀.trans restrict_le, hV₀, hΩ₀, hc₀, hnc₀, hnt₀, hloop₀, hsimp₀, ?_⟩
        intro e x y hxy
        by_cases hee₀ : e = e₀
        · subst hee₀
          have he₁_S₁ : S₁.G.IsLink e₁ u v := by
            refine (restrict_le.isLink_iff ?_).mpr he₁
            rw [hE_S₁]
            exact ⟨he₁.edge_mem, fun h => hne.symm (mem_singleton_iff.mp h)⟩
          rcases hxy.eq_and_eq_or_eq_and_eq he₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hadj₀ e₁ x y he₁_S₁
          · exact hadj₀ e₁ x y he₁_S₁.symm
        · have he_S₁ : S₁.G.IsLink e x y := by
            refine (restrict_le.isLink_iff ?_).mpr hxy
            rw [hE_S₁]
            exact ⟨hxy.edge_mem, hee₀⟩
          exact hadj₀ e x y he_S₁
    · push Not at hG_loopless
      obtain ⟨u, e₀, he₀⟩ := hG_loopless
      let S₁ : Society α β := ⟨S'.G.restrict (E(S'.G) \ {e₀}), S'.Ω, S'.finite_V,
        S'.finite_E.subset restrict_le.edgeSet_mono, S'.bar_subset⟩
      have hE_S₁ : E(S₁.G) = E(S'.G) \ {e₀} := by
        change E(S'.G.restrict (E(S'.G) \ {e₀})) = _
        rw [edgeSet_restrict, inter_eq_right]
        exact sdiff_subset
      have hlt : E(S₁.G).ncard < n := by
        rw [← hn, hE_S₁]
        exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h he₀.edge_mem).2 (mem_singleton e₀)⟩
          S'.finite_E
      have hconn₁ : S₁.IsKConnected 3 :=
        isKConnected_restrict_sdiff_singleton S' 3 hconn' he₀ (Or.inl rfl)
      have hnocross₁ : ¬ ∃ Q₁ Q₂ : Graph α β, S₁.IsCross Q₁ Q₂ :=
        fun ⟨Q₁, Q₂, hc⟩ => hnocross' ⟨Q₁, Q₂, isCross_mono_of_le (S₀ := S₁) (S
          := S') restrict_le rfl hc⟩
      have hnotripod₁ : ¬ ∃ T₁ T₂ T₃ : Graph α β, S₁.IsTripod T₁ T₂ T₃ :=
        fun ⟨T₁, T₂, T₃, ht⟩ => hnotripod' ⟨T₁, T₂, T₃, isTripod_mono_of_le (S₀ := S₁) (S
          := S') restrict_le rfl ht⟩
      obtain ⟨S₀, hle₀, hV₀, hΩ₀, hc₀, hnc₀, hnt₀, hloop₀, hsimp₀, hadj₀⟩ :=
        ih _ hlt S₁ rfl hconn₁ hnocross₁ hnotripod₁
      refine ⟨S₀, hle₀.trans restrict_le, hV₀, hΩ₀, hc₀, hnc₀, hnt₀, hloop₀, hsimp₀, ?_⟩
      intro e x y hxy
      by_cases hee₀ : e = e₀
      · subst hee₀
        rcases hxy.eq_and_eq_or_eq_and_eq he₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inl rfl
      · have he_S₁ : S₁.G.IsLink e x y := by
          refine (restrict_le.isLink_iff ?_).mpr hxy
          rw [hE_S₁]
          exact ⟨hxy.edge_mem, hee₀⟩
        exact hadj₀ e x y he_S₁



theorem iterate_toFun_eq_getElem_of_next {Ω : CyclicPerm α} {L : List α}
    (hL_next : ∀ (i : ℕ) (hi : i < L.length),
      Ω.toFun (L[i]'hi) = L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))
    {i₀ : ℕ} (hi₀ : i₀ < L.length) (d : ℕ) :
    (Ω.toFun^[d]) (L[i₀]'hi₀) =
      L[(i₀ + d) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi₀)) := by
  have hpos : 0 < L.length := Nat.zero_lt_of_lt hi₀
  induction d with
  | zero =>
    simp only [Function.iterate_zero_apply, Nat.add_zero]
    congr 1
    exact (Nat.mod_eq_of_lt hi₀).symm
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih, hL_next _ (Nat.mod_lt _ hpos)]
    congr 1
    rw [Nat.mod_add_mod, Nat.add_assoc]

noncomputable section

open Classical in
/-- Shift an angle assignment `θ` on `L` by adding `2π` to vertices appearing before `i₀`,
so that angles become strictly increasing along the `Ω`-orbit starting at `L[i₀]`. -/
def shiftedAngle (L : List α) (θ : α → ℝ) (i₀ : ℕ) (v : α) : ℝ :=
  if hv : v ∈ L then
    if CyclicPerm.indexOfMem L hv < i₀ then θ v + 2 * Real.pi else θ v
  else 0

open Classical in
theorem circle_exp_shiftedAngle (L : List α) (θ : α → ℝ) (i₀ : ℕ)
    {v : α} (hv : v ∈ L) :
    Circle.exp (shiftedAngle L θ i₀ v) = Circle.exp (θ v) := by
  simp only [shiftedAngle, hv, ↓reduceDIte]
  split_ifs
  · rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
  · rfl

open Classical in
theorem shiftedAngle_getElem_self {L : List α} (hnd : L.Nodup) (θ : α → ℝ)
    {i₀ : ℕ} (hi₀ : i₀ < L.length) :
    shiftedAngle L θ i₀ (L[i₀]'hi₀) = θ (L[i₀]'hi₀) := by
  have hmem : L[i₀]'hi₀ ∈ L := List.getElem_mem hi₀
  simp only [shiftedAngle, hmem, ↓reduceDIte, CyclicPerm.indexOfMem_getElem hnd hi₀,
    Nat.lt_irrefl, ↓reduceIte]

private theorem mod_eq_sub_of_le_of_lt {n k : ℕ} (h1 : n ≤ k) (h2 : k < 2 * n) :
    k % n = k - n := by
  have heq : k = n + (k - n) := by omega
  conv_lhs => rw [heq]
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

open Classical in
theorem shiftedAngle_iterate_strictMono {Ω : CyclicPerm α} {L : List α}
    (hnd : L.Nodup)
    (hL_next : ∀ (i : ℕ) (hi : i < L.length),
      Ω.toFun (L[i]'hi) = L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))
    {θ : α → ℝ}
    (hθ_mono : ∀ i j (hi : i < L.length) (hj : j < L.length),
      i < j → θ (L[i]'hi) < θ (L[j]'hj))
    (hθ_span : ∀ i (hi : i < L.length),
      θ (L[i]'hi) < θ (L[0]'(Nat.zero_lt_of_lt hi)) + 2 * Real.pi)
    {i₀ : ℕ} (hi₀ : i₀ < L.length) {d₁ d₂ : ℕ}
    (hd₁₂ : d₁ < d₂) (hd₂ : d₂ < L.length) :
    shiftedAngle L θ i₀ ((Ω.toFun^[d₁]) (L[i₀]'hi₀)) <
      shiftedAngle L θ i₀ ((Ω.toFun^[d₂]) (L[i₀]'hi₀)) := by
  have hpos : 0 < L.length := Nat.zero_lt_of_lt hi₀
  rw [iterate_toFun_eq_getElem_of_next hL_next hi₀ d₁,
    iterate_toFun_eq_getElem_of_next hL_next hi₀ d₂]
  have hm₁ : (i₀ + d₁) % L.length < L.length := Nat.mod_lt _ hpos
  have hm₂ : (i₀ + d₂) % L.length < L.length := Nat.mod_lt _ hpos
  have hmem₁ : L[(i₀ + d₁) % L.length]'hm₁ ∈ L := List.getElem_mem hm₁
  have hmem₂ : L[(i₀ + d₂) % L.length]'hm₂ ∈ L := List.getElem_mem hm₂
  simp only [shiftedAngle, hmem₁, hmem₂, ↓reduceDIte,
    CyclicPerm.indexOfMem_getElem hnd hm₁, CyclicPerm.indexOfMem_getElem hnd hm₂]
  by_cases h1 : i₀ + d₁ < L.length <;> by_cases h2 : i₀ + d₂ < L.length
  · have hmod₁ : (i₀ + d₁) % L.length = i₀ + d₁ := Nat.mod_eq_of_lt h1
    have hmod₂ : (i₀ + d₂) % L.length = i₀ + d₂ := Nat.mod_eq_of_lt h2
    have hn₁ : ¬ (i₀ + d₁) % L.length < i₀ := by omega
    have hn₂ : ¬ (i₀ + d₂) % L.length < i₀ := by omega
    simp only [hn₁, hn₂, ↓reduceIte]
    exact hθ_mono _ _ hm₁ hm₂ (by omega)
  · have hmod₁ : (i₀ + d₁) % L.length = i₀ + d₁ := Nat.mod_eq_of_lt h1
    have hmod₂ : (i₀ + d₂) % L.length = i₀ + d₂ - L.length :=
      mod_eq_sub_of_le_of_lt (by omega) (by omega)
    have hn₁ : ¬ (i₀ + d₁) % L.length < i₀ := by omega
    have hp₂ : (i₀ + d₂) % L.length < i₀ := by omega
    simp only [hn₁, hp₂, ↓reduceIte]
    have h_sp := hθ_span ((i₀ + d₁) % L.length) hm₁
    by_cases h0 : (i₀ + d₂) % L.length = 0
    · have h_eq : θ (L[0]'hpos) = θ (L[(i₀ + d₂) % L.length]'hm₂) := by congr 2; exact h0.symm
      linarith
    · have h_gt0 : 0 < (i₀ + d₂) % L.length := Nat.pos_of_ne_zero h0
      have h_m0 := hθ_mono 0 ((i₀ + d₂) % L.length) hpos hm₂ h_gt0
      linarith
  · omega
  · have hmod₁ : (i₀ + d₁) % L.length = i₀ + d₁ - L.length :=
      mod_eq_sub_of_le_of_lt (by omega) (by omega)
    have hmod₂ : (i₀ + d₂) % L.length = i₀ + d₂ - L.length :=
      mod_eq_sub_of_le_of_lt (by omega) (by omega)
    have hp₁ : (i₀ + d₁) % L.length < i₀ := by omega
    have hp₂ : (i₀ + d₂) % L.length < i₀ := by omega
    simp only [hp₁, hp₂, ↓reduceIte]
    have h_lt := hθ_mono _ _ hm₁ hm₂ (by omega)
    linarith

open Classical in
theorem shiftedAngle_iterate_lt_span {Ω : CyclicPerm α} {L : List α}
    (hnd : L.Nodup)
    (hL_next : ∀ (i : ℕ) (hi : i < L.length),
      Ω.toFun (L[i]'hi) = L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))
    {θ : α → ℝ}
    (hθ_mono : ∀ i j (hi : i < L.length) (hj : j < L.length),
      i < j → θ (L[i]'hi) < θ (L[j]'hj))
    (hθ_span : ∀ i (hi : i < L.length),
      θ (L[i]'hi) < θ (L[0]'(Nat.zero_lt_of_lt hi)) + 2 * Real.pi)
    {i₀ : ℕ} (hi₀ : i₀ < L.length) {d : ℕ} (hd : d < L.length) :
    shiftedAngle L θ i₀ ((Ω.toFun^[d]) (L[i₀]'hi₀)) <
      shiftedAngle L θ i₀ (L[i₀]'hi₀) + 2 * Real.pi := by
  have hpos : 0 < L.length := Nat.zero_lt_of_lt hi₀
  rw [shiftedAngle_getElem_self hnd θ hi₀, iterate_toFun_eq_getElem_of_next hL_next hi₀ d]
  have hm : (i₀ + d) % L.length < L.length := Nat.mod_lt _ hpos
  have hmem : L[(i₀ + d) % L.length]'hm ∈ L := List.getElem_mem hm
  simp only [shiftedAngle, hmem, ↓reduceDIte, CyclicPerm.indexOfMem_getElem hnd hm]
  by_cases h1 : i₀ + d < L.length
  · have hmod : (i₀ + d) % L.length = i₀ + d := Nat.mod_eq_of_lt h1
    have hn : ¬ (i₀ + d) % L.length < i₀ := by omega
    simp only [hn, ↓reduceIte]
    have h_sp := hθ_span ((i₀ + d) % L.length) hm
    by_cases hi0 : i₀ = 0
    · have h_eq : θ (L[0]'hpos) = θ (L[i₀]'hi₀) := by congr 2; exact hi0.symm
      linarith
    · have h_gt0 := hθ_mono 0 i₀ hpos hi₀ (Nat.pos_of_ne_zero hi0)
      linarith
  · have hmod : (i₀ + d) % L.length = i₀ + d - L.length :=
      mod_eq_sub_of_le_of_lt (by omega) (by omega)
    have hp : (i₀ + d) % L.length < i₀ := by omega
    simp only [hp, ↓reduceIte]
    have h_lt := hθ_mono _ i₀ hm hi₀ (by omega)
    linarith

/-- A nodup list `L` enumerating `Ω.bar` in `Ω.toFun`-orbit order. -/
def CyclicPerm.IsOrbitList (Ω : CyclicPerm α) (L : List α) : Prop :=
  L.Nodup ∧ L ≠ [] ∧ {v | v ∈ L} = Ω.bar ∧
    ∀ (i : ℕ) (hi : i < L.length),
      Ω.toFun (L[i]'hi) = L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))

theorem CyclicPerm.isOrbitList_ofNodupList (L : List α) (hnd : L.Nodup) (hne : L ≠ []) :
    (CyclicPerm.ofNodupList L hnd hne).IsOrbitList L :=
  ⟨hnd, hne, rfl, fun _ hi => CyclicPerm.ofNodupList_toFun_getElem L hnd hne hi⟩

theorem isOrbitList_splitList (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar) :
    (splitCyclicPerm S hs ht hst hP hP_bar).IsOrbitList (splitList S hs ht hP) :=
  CyclicPerm.isOrbitList_ofNodupList _ _ _

theorem CyclicPerm.exists_isOrbitList_starting_at (Ω : CyclicPerm α) {w₀ : α} (hw₀ : w₀ ∈ Ω.bar) :
    ∃ L : List α, Ω.IsOrbitList L ∧ ∀ h : 0 < L.length, L[0]'h = w₀ := by
  let K := Ω.hitStep hw₀ hw₀
  have hK1 : 1 ≤ K := Ω.hitStep_ge_one hw₀ hw₀
  have hK_eq : (Ω.toFun^[K]) w₀ = w₀ := Ω.iterate_hitStep hw₀ hw₀
  have hK_min : ∀ j : ℕ, 1 ≤ j → j < K → (Ω.toFun^[j]) w₀ ≠ w₀ :=
    fun j hj1 hjK => Ω.iterate_ne_of_lt_hitStep hw₀ hw₀ hj1 hjK
  let L : List α := (List.range K).map (fun i => (Ω.toFun^[i]) w₀)
  have hlen : L.length = K := by simp [L]
  have hget : ∀ (i : ℕ) (hi : i < L.length), L[i]'hi = (Ω.toFun^[i]) w₀ := by
    intro i _; simp [L]
  have hnd : L.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    rw [hget i hi, hget j hj] at heq
    rw [hlen] at hi hj
    have hiter : (Ω.toFun^[i]) ((Ω.toFun^[j - i]) w₀) = (Ω.toFun^[i]) w₀ := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hij), heq]
    have hsub := Ω.injOn_iterate i (Ω.iterate_mem (j - i) hw₀) hw₀ hiter
    exact (hK_min (j - i) (by omega) (by omega) hsub).elim
  have hne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hbar : {v | v ∈ L} = Ω.bar := by
    ext v
    simp only [mem_ofPred_eq, List.mem_iff_getElem, hlen]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hget i (by omega)]
      exact Ω.iterate_mem i hw₀
    · intro hv
      obtain ⟨m, rfl⟩ := Ω.single_orbit w₀ hw₀ v hv
      have hmul : ∀ q : ℕ, (Ω.toFun^[K * q]) w₀ = w₀ := by
        intro q
        induction q with
        | zero => rfl
        | succ q ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hK_eq]
      refine ⟨m % K, Nat.mod_lt _ (by omega), ?_⟩
      rw [hget (m % K) (by rw [hlen]; exact Nat.mod_lt _ (by omega))]
      conv_rhs => rw [← Nat.div_add_mod m K, add_comm]
      rw [Function.iterate_add_apply, hmul]
  have hnext : ∀ (i : ℕ) (hi : i < L.length),
      Ω.toFun (L[i]'hi) = L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) := by
    intro i hi
    have hiK : i < K := hlen ▸ hi
    rw [hget i hi, hget ((i + 1) % L.length) (Nat.mod_lt _ (Nat.zero_lt_of_lt hi)),
      ← Function.iterate_succ_apply' Ω.toFun i w₀, hlen]
    by_cases h1 : i + 1 < K
    · rw [Nat.mod_eq_of_lt h1]
    · have hi_eq : i + 1 = K := by omega
      rw [hi_eq, Nat.mod_self, Function.iterate_zero_apply]
      change (Ω.toFun^[i + 1]) w₀ = w₀
      rw [hi_eq, hK_eq]
  exact ⟨L, ⟨hnd, hne, hbar, hnext⟩, fun h => hget 0 h⟩

theorem CyclicPerm.exists_isOrbitList_of_mem (Ω : CyclicPerm α) {w₀ : α} (hw₀ : w₀ ∈ Ω.bar) :
    ∃ L : List α, Ω.IsOrbitList L :=
  (Ω.exists_isOrbitList_starting_at hw₀).imp fun _ h => h.1

/-- An angle assignment `θ : α → ℝ` is valid on `L` if it is strictly increasing along `L`
and spans strictly less than `2π`. -/
def IsValidAngle (L : List α) (θ : α → ℝ) : Prop :=
  (∀ i j (hi : i < L.length) (hj : j < L.length), i < j → θ (L[i]'hi) < θ (L[j]'hj)) ∧
  (∀ i (hi : i < L.length), θ (L[i]'hi) < θ (L[0]'(Nat.zero_lt_of_lt hi)) + 2 * Real.pi)

theorem injOn_circle_exp_of_isValidAngle {Ω : CyclicPerm α} {L : List α}
    (hL : Ω.IsOrbitList L) {θ : α → ℝ} (hθ : IsValidAngle L θ) :
    InjOn (fun v => (Circle.exp (θ v) : ℂ)) Ω.bar := by
  intro u hu v hv heq
  rw [← hL.2.2.1, mem_ofPred_eq, List.mem_iff_getElem] at hu hv
  obtain ⟨i, hi, rfl⟩ := hu
  obtain ⟨j, hj, rfl⟩ := hv
  have hexp : Circle.exp (θ (L[i]'hi)) = Circle.exp (θ (L[j]'hj)) := Subtype.ext heq
  have hpos : 0 < L.length := Nat.zero_lt_of_lt hi
  have hge0 : ∀ k (hk : k < L.length), θ (L[0]'hpos) ≤ θ (L[k]'hk) := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hpos_k
    · exact le_rfl
    · exact (hθ.1 0 k hpos hk hpos_k).le
  have hθ_eq : θ (L[i]'hi) = θ (L[j]'hj) := by
    apply circle_exp_inj_of_abs_sub_lt _ hexp
    exact abs_lt.mpr ⟨by linarith [hge0 i hi, hθ.2 j hj], by linarith [hge0 j hj, hθ.2 i hi]⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · linarith [hθ.1 i j hi hj hij]
  · rfl
  · linarith [hθ.1 j i hj hi hji]

theorem hitStep_add_hitStep_le_length {Ω : CyclicPerm α} {L : List α}
    (hL : Ω.IsOrbitList L) {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t) :
    Ω.hitStep hs ht + Ω.hitStep ht hs ≤ L.length := by
  have hsL : s ∈ L := by rwa [← hL.2.2.1] at hs
  let i₀ := CyclicPerm.indexOfMem L hsL
  have hi₀ : i₀ < L.length := CyclicPerm.indexOfMem_lt L hsL
  have hpos : 0 < L.length := Nat.zero_lt_of_lt hi₀
  have hLi₀ : L[i₀]'hi₀ = s := CyclicPerm.getElem_indexOfMem L hsL
  have hiter_len : (Ω.toFun^[L.length]) s = s := by
    rw [← hLi₀, iterate_toFun_eq_getElem_of_next hL.2.2.2 hi₀ L.length]
    congr 1
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi₀]
  have hk₁_lt : Ω.hitStep hs ht < L.length := by
    by_contra hge
    rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
    · have : t = s := by rw [← Ω.iterate_hitStep hs ht, ← heq, hiter_len]
      exact hst this.symm
    · exact Ω.iterate_ne_self_of_lt_hitStep hs ht hst hpos hgt hiter_len
  by_contra hgt
  have hrem_pos : 1 ≤ L.length - Ω.hitStep hs ht := by omega
  have hrem_lt : L.length - Ω.hitStep hs ht < Ω.hitStep ht hs := by omega
  have hrem_eq : (Ω.toFun^[L.length - Ω.hitStep hs ht]) t = s := by
    calc (Ω.toFun^[L.length - Ω.hitStep hs ht]) t
      _ = (Ω.toFun^[L.length - Ω.hitStep hs ht]) ((Ω.toFun^[Ω.hitStep hs ht]) s) := by
        rw [Ω.iterate_hitStep hs ht]
      _ = s := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega), hiter_len]
  exact Ω.iterate_ne_of_lt_hitStep ht hs hrem_pos hrem_lt hrem_eq

open Classical in
/-- Angle assignment on `splitList S hs ht hP` for the upper half-disc society `S₁`. -/
def upperSplitAngle {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) (v : α) : ℝ :=
  let L_P := (pathWalkTS hP).support
  let m := L_P.length
  if hv : v ∈ L_P then
    2 * Real.pi - Real.arccos (pathX m (CyclicPerm.indexOfMem L_P hv))
  else
    2 * Real.pi + Real.pi * (θ' v - θ' s) / (θ' t - θ' s)

open Classical in
/-- Angle assignment on `splitList S ht hs hP.symm` for the lower half-disc society `S₂`. -/
def lowerSplitAngle {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) (v : α) : ℝ :=
  let L_P := (pathWalkTS hP).support
  let m := L_P.length
  if hv : v ∈ L_P then
    Real.arccos (pathX m (CyclicPerm.indexOfMem L_P hv))
  else
    Real.pi + Real.pi * (θ' v - θ' t) / (θ' s + 2 * Real.pi - θ' t)

open Classical in
theorem upperSplitAngle_of_mem_P {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) {k : ℕ}
    (hk : k < (pathWalkTS hP).support.length) :
    upperSplitAngle hP θ' ((pathWalkTS hP).support[k]'hk) =
      2 * Real.pi - Real.arccos (pathX (pathWalkTS hP).support.length k) := by
  have hmem : (pathWalkTS hP).support[k]'hk ∈ (pathWalkTS hP).support := List.getElem_mem hk
  simp only [upperSplitAngle, hmem, ↓reduceDIte,
    CyclicPerm.indexOfMem_getElem (isSimple_pathWalkTS hP) hk]

open Classical in
theorem upperSplitAngle_of_not_mem_P {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) {v : α}
    (hv : v ∉ V(P)) :
    upperSplitAngle hP θ' v =
      2 * Real.pi + Real.pi * (θ' v - θ' s) / (θ' t - θ' s) := by
  have hv_not : v ∉ (pathWalkTS hP).support := fun h =>
    hv (by rw [vertexSet_eq_support_pathWalkTS hP]; exact h)
  simp [upperSplitAngle, hv_not]

open Classical in
theorem lowerSplitAngle_of_mem_P {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) {k : ℕ}
    (hk : k < (pathWalkTS hP).support.length) :
    lowerSplitAngle hP θ' ((pathWalkTS hP).support[k]'hk) =
      Real.arccos (pathX (pathWalkTS hP).support.length k) := by
  have hmem : (pathWalkTS hP).support[k]'hk ∈ (pathWalkTS hP).support := List.getElem_mem hk
  simp only [lowerSplitAngle, hmem, ↓reduceDIte,
    CyclicPerm.indexOfMem_getElem (isSimple_pathWalkTS hP) hk]

open Classical in
theorem lowerSplitAngle_of_not_mem_P {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) {v : α}
    (hv : v ∉ V(P)) :
    lowerSplitAngle hP θ' v =
      Real.pi + Real.pi * (θ' v - θ' t) / (θ' s + 2 * Real.pi - θ' t) := by
  have hv_not : v ∉ (pathWalkTS hP).support := fun h =>
    hv (by rw [vertexSet_eq_support_pathWalkTS hP]; exact h)
  simp [lowerSplitAngle, hv_not]

theorem arccos_pathX_strictAnti {m : ℕ} (hm : 2 ≤ m) {i j : ℕ} (hij : i < j) (hj : j < m) :
    Real.arccos (pathX m j) < Real.arccos (pathX m i) :=
  Real.strictAntiOn_arccos (pathX_mem_Icc hm (Nat.lt_trans hij hj)) (pathX_mem_Icc hm hj)
    (pathX_strictMono hm hij)

theorem isValidAngle_upperSplitAngle (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {θ' : α → ℝ}
    (h_st : θ' s < θ' t)
    (h_W1_bounds : ∀ a (ha : a < (S.Ω.intervalList hs ht).length),
      θ' s < θ' ((S.Ω.intervalList hs ht)[a]'ha) ∧
      θ' ((S.Ω.intervalList hs ht)[a]'ha) < θ' t)
    (h_W1_mono : ∀ a₁ a₂ (ha₁ : a₁ < (S.Ω.intervalList hs ht).length)
      (ha₂ : a₂ < (S.Ω.intervalList hs ht).length),
      a₁ < a₂ → θ' ((S.Ω.intervalList hs ht)[a₁]'ha₁) < θ' ((S.Ω.intervalList hs ht)[a₂]'ha₂)) :
    IsValidAngle (splitList S hs ht hP) (upperSplitAngle hP θ') := by
  let L₁ := splitList S hs ht hP
  let m := (pathWalkTS hP).support.length
  have hm : 2 ≤ m := two_le_length_support_pathWalkTS hst hP
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff : 0 < θ' t - θ' s := by linarith
  have h_val_lt : ∀ i (hi : i < m),
      upperSplitAngle hP θ' (L₁[i]'(by rw [length_splitList]; omega)) =
        2 * Real.pi - Real.arccos (pathX m i) := by
    intro i hi
    rw [getElem_splitList_of_lt S hs ht hP hi, upperSplitAngle_of_mem_P hP θ' hi]
  have h_val_ge : ∀ i (hmi : m ≤ i) (hi : i < L₁.length),
      upperSplitAngle hP θ' (L₁[i]'hi) =
        2 * Real.pi + Real.pi *
          (θ' ((S.Ω.intervalList hs ht)[i - m]'(by rw [length_splitList] at hi; omega)) - θ' s) /
          (θ' t - θ' s) := by
    intro i hmi hi
    have hnotP : L₁[i]'hi ∉ V(P) := by
      rw [getElem_splitList_mem_P_iff S hs ht hst hP hP_bar hi]
      omega
    rw [upperSplitAngle_of_not_mem_P hP θ' hnotP, getElem_splitList_of_le S hs ht hP hmi hi]
  have h_0_val : upperSplitAngle hP θ' (L₁[0]'(by rw [length_splitList]; omega)) = Real.pi := by
    rw [h_val_lt 0 (by omega), pathX_zero, Real.arccos_neg_one]
    ring
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · by_cases him : i < m <;> by_cases hjm : j < m
    · rw [h_val_lt i him, h_val_lt j hjm]
      linarith [arccos_pathX_strictAnti hm hij hjm]
    · rw [h_val_lt i him, h_val_ge j (by omega) hj]
      have harc : 0 ≤ Real.arccos (pathX m i) := Real.arccos_nonneg _
      have hb := (h_W1_bounds (j - m) (by rw [length_splitList] at hj; omega)).1
      have hj' : j - m < (S.Ω.intervalList hs ht).length := by
        rw [length_splitList] at hj
        omega
      have hpos : 0 < Real.pi * (θ' ((S.Ω.intervalList hs ht)[j - m]'hj') - θ' s) /
          (θ' t - θ' s) :=
        div_pos (mul_pos hpi (by linarith)) hdiff
      linarith
    · omega
    · rw [h_val_ge i (by omega) hi, h_val_ge j (by omega) hj]
      have hmono := h_W1_mono (i - m) (j - m)
        (by rw [length_splitList] at hi; omega) (by rw [length_splitList] at hj; omega) (by omega)
      have hlt_div :
          Real.pi * (θ' ((S.Ω.intervalList hs ht)[i - m]'(by rw [length_splitList] at hi; omega)) -
            θ' s) / (θ' t - θ' s) <
          Real.pi * (θ' ((S.Ω.intervalList hs ht)[j - m]'(by rw [length_splitList] at hj; omega)) -
            θ' s) / (θ' t - θ' s) :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (by linarith) hpi) hdiff
      linarith
  · rw [h_0_val]
    by_cases him : i < m
    · rw [h_val_lt i him]
      have harc : 0 ≤ Real.arccos (pathX m i) := Real.arccos_nonneg _
      linarith
    · rw [h_val_ge i (by omega) hi]
      have hb := (h_W1_bounds (i - m) (by rw [length_splitList] at hi; omega)).2
      have hlt_pi :
          Real.pi * (θ' ((S.Ω.intervalList hs ht)[i - m]'(by rw [length_splitList] at hi; omega)) -
            θ' s) / (θ' t - θ' s) < Real.pi := by
        rw [div_lt_iff₀ hdiff]
        nlinarith
      linarith

theorem isValidAngle_lowerSplitAngle (S : Society α β) {P : Graph α β} {s t : α}
    (hs : s ∈ S.Ω.bar) (ht : t ∈ S.Ω.bar) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds S.G P s t)
    (hP_bar : Disjoint (V(P) \ {s, t}) S.Ω.bar)
    {θ' : α → ℝ}
    (h_span : θ' t < θ' s + 2 * Real.pi)
    (h_W2_bounds : ∀ b (hb : b < (S.Ω.intervalList ht hs).length),
      θ' t < θ' ((S.Ω.intervalList ht hs)[b]'hb) ∧
      θ' ((S.Ω.intervalList ht hs)[b]'hb) < θ' s + 2 * Real.pi)
    (h_W2_mono : ∀ b₁ b₂ (hb₁ : b₁ < (S.Ω.intervalList ht hs).length)
      (hb₂ : b₂ < (S.Ω.intervalList ht hs).length),
      b₁ < b₂ → θ' ((S.Ω.intervalList ht hs)[b₁]'hb₁) < θ' ((S.Ω.intervalList ht hs)[b₂]'hb₂)) :
    IsValidAngle (splitList S ht hs hP.symm) (lowerSplitAngle hP θ') := by
  let L₂ := splitList S ht hs hP.symm
  let m := (pathWalkTS hP).support.length
  have hm : 2 ≤ m := two_le_length_support_pathWalkTS hst hP
  have hlen_symm : (pathWalkTS hP.symm).support.length = m := by
    rw [support_pathWalkTS_symm hP, List.length_reverse]
  have hP_bar₂ : Disjoint (V(P) \ {t, s}) S.Ω.bar := by rw [pair_comm]; exact hP_bar
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff : 0 < θ' s + 2 * Real.pi - θ' t := by linarith
  have h_val_lt : ∀ i (hi : i < m),
      lowerSplitAngle hP θ' (L₂[i]'(by rw [length_splitList, hlen_symm]; omega)) =
        Real.arccos (pathX m (m - 1 - i)) := by
    intro i hi
    have hi_symm : i < (pathWalkTS hP.symm).support.length := hlen_symm ▸ hi
    have h_elem : L₂[i]'(by rw [length_splitList, hlen_symm]; omega) =
        (pathWalkTS hP).support[m - 1 - i]'(by omega) := by
      rw [getElem_splitList_of_lt S ht hs hP.symm hi_symm]
      simp only [support_pathWalkTS_symm hP, List.getElem_reverse]
      rfl
    rw [h_elem, lowerSplitAngle_of_mem_P hP θ' (by omega)]
  have h_val_ge : ∀ i (hmi : m ≤ i) (hi : i < L₂.length),
      lowerSplitAngle hP θ' (L₂[i]'hi) =
        Real.pi + Real.pi *
          (θ' ((S.Ω.intervalList ht hs)[i - m]'(by rw [length_splitList, hlen_symm] at hi; omega))
            - θ' t) /
          (θ' s + 2 * Real.pi - θ' t) := by
    intro i hmi hi
    have hmi_symm : (pathWalkTS hP.symm).support.length ≤ i := hlen_symm ▸ hmi
    have hnotP : L₂[i]'hi ∉ V(P) := by
      rw [getElem_splitList_mem_P_iff S ht hs hst.symm hP.symm hP_bar₂ hi, hlen_symm]
      omega
    rw [lowerSplitAngle_of_not_mem_P hP θ' hnotP, getElem_splitList_of_le S ht hs hP.symm hmi_symm
      hi]
    congr 6
    rw [hlen_symm]
  have h_0_val : lowerSplitAngle hP θ' (L₂[0]'(by rw [length_splitList, hlen_symm]; omega)) = 0
    := by
    rw [h_val_lt 0 (by omega), Nat.sub_zero, pathX_pred hm, Real.arccos_one]
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · by_cases him : i < m <;> by_cases hjm : j < m
    · rw [h_val_lt i him, h_val_lt j hjm]
      exact arccos_pathX_strictAnti hm (by omega) (by omega)
    · rw [h_val_lt i him, h_val_ge j (by omega) hj]
      have harc : Real.arccos (pathX m (m - 1 - i)) ≤ Real.pi := Real.arccos_le_pi _
      have hb := (h_W2_bounds (j - m) (by rw [length_splitList, hlen_symm] at hj; omega)).1
      have hj' : j - m < (S.Ω.intervalList ht hs).length := by
        rw [length_splitList, hlen_symm] at hj
        omega
      have hpos : 0 < Real.pi * (θ' ((S.Ω.intervalList ht hs)[j - m]'hj') - θ' t) /
          (θ' s + 2 * Real.pi - θ' t) :=
        div_pos (mul_pos hpi (by linarith)) hdiff
      linarith
    · omega
    · rw [h_val_ge i (by omega) hi, h_val_ge j (by omega) hj]
      have hmono := h_W2_mono (i - m) (j - m)
        (by rw [length_splitList, hlen_symm] at hi; omega)
        (by rw [length_splitList, hlen_symm] at hj; omega) (by omega)
      have hi' : i - m < (S.Ω.intervalList ht hs).length := by
        rw [length_splitList, hlen_symm] at hi
        omega
      have hj' : j - m < (S.Ω.intervalList ht hs).length := by
        rw [length_splitList, hlen_symm] at hj
        omega
      have hlt_div :
          Real.pi * (θ' ((S.Ω.intervalList ht hs)[i - m]'hi') - θ' t) /
            (θ' s + 2 * Real.pi - θ' t) <
          Real.pi * (θ' ((S.Ω.intervalList ht hs)[j - m]'hj') - θ' t) /
            (θ' s + 2 * Real.pi - θ' t) :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (by linarith) hpi) hdiff
      linarith
  · rw [h_0_val]
    by_cases him : i < m
    · rw [h_val_lt i him]
      have harc : Real.arccos (pathX m (m - 1 - i)) ≤ Real.pi := Real.arccos_le_pi _
      linarith
    · rw [h_val_ge i (by omega) hi]
      have hb := (h_W2_bounds (i - m) (by rw [length_splitList, hlen_symm] at hi; omega)).2
      have hi' : i - m < (S.Ω.intervalList ht hs).length := by
        rw [length_splitList, hlen_symm] at hi
        omega
      have hlt_pi : Real.pi * (θ' ((S.Ω.intervalList ht hs)[i - m]'hi') - θ' t) /
          (θ' s + 2 * Real.pi - θ' t) < Real.pi := by
        rw [div_lt_iff₀ hdiff]
        nlinarith
      linarith

open Classical in
theorem shiftedAngle_intervalList_props {Ω : CyclicPerm α} {L : List α}
    (hL : Ω.IsOrbitList L) {θ : α → ℝ} (hθ : IsValidAngle L θ)
    {s t : α} (hs : s ∈ Ω.bar) (ht : t ∈ Ω.bar) (hst : s ≠ t) :
    let hsL : s ∈ L := by rwa [← hL.2.2.1] at hs
    let i₀ := CyclicPerm.indexOfMem L hsL
    let θ' := shiftedAngle L θ i₀
    θ' s < θ' t ∧
    θ' t < θ' s + 2 * Real.pi ∧
    (∀ a (ha : a < (Ω.intervalList hs ht).length),
      θ' s < θ' ((Ω.intervalList hs ht)[a]'ha) ∧
      θ' ((Ω.intervalList hs ht)[a]'ha) < θ' t) ∧
    (∀ a₁ a₂ (ha₁ : a₁ < (Ω.intervalList hs ht).length)
      (ha₂ : a₂ < (Ω.intervalList hs ht).length),
      a₁ < a₂ → θ' ((Ω.intervalList hs ht)[a₁]'ha₁) < θ' ((Ω.intervalList hs ht)[a₂]'ha₂)) ∧
    (∀ b (hb : b < (Ω.intervalList ht hs).length),
      θ' t < θ' ((Ω.intervalList ht hs)[b]'hb) ∧
      θ' ((Ω.intervalList ht hs)[b]'hb) < θ' s + 2 * Real.pi) ∧
    (∀ b₁ b₂ (hb₁ : b₁ < (Ω.intervalList ht hs).length)
      (hb₂ : b₂ < (Ω.intervalList ht hs).length),
      b₁ < b₂ → θ' ((Ω.intervalList ht hs)[b₁]'hb₁) < θ' ((Ω.intervalList ht hs)[b₂]'hb₂)) := by
  intro hsL i₀ θ'
  have hi₀ : i₀ < L.length := CyclicPerm.indexOfMem_lt L hsL
  have hLi₀ : L[i₀]'hi₀ = s := CyclicPerm.getElem_indexOfMem L hsL
  have hsum_le : Ω.hitStep hs ht + Ω.hitStep ht hs ≤ L.length :=
    hitStep_add_hitStep_le_length hL hs ht hst
  have hk₁_ge : 1 ≤ Ω.hitStep hs ht := Ω.hitStep_ge_one hs ht
  have hk₂_ge : 1 ≤ Ω.hitStep ht hs := Ω.hitStep_ge_one ht hs
  have h_mono : ∀ {d₁ d₂ : ℕ}, d₁ < d₂ → d₂ < L.length →
      θ' ((Ω.toFun^[d₁]) s) < θ' ((Ω.toFun^[d₂]) s) := by
    intro d₁ d₂ hd₁₂ hd₂
    rw [← hLi₀]
    exact shiftedAngle_iterate_strictMono hL.1 hL.2.2.2 hθ.1 hθ.2 hi₀ hd₁₂ hd₂
  have h_span : ∀ {d : ℕ}, d < L.length → θ' ((Ω.toFun^[d]) s) < θ' s + 2 * Real.pi := by
    intro d hd
    conv_lhs => rw [← hLi₀]
    conv_rhs => rw [← hLi₀]
    exact shiftedAngle_iterate_lt_span hL.1 hL.2.2.2 hθ.1 hθ.2 hi₀ hd
  have ht_iter : (Ω.toFun^[Ω.hitStep hs ht]) s = t := Ω.iterate_hitStep hs ht
  have hW1_iter : ∀ a (ha : a < (Ω.intervalList hs ht).length),
      (Ω.intervalList hs ht)[a]'ha = (Ω.toFun^[a + 1]) s :=
    fun a ha => Ω.getElem_intervalList hs ht ha
  have hW2_iter : ∀ b (hb : b < (Ω.intervalList ht hs).length),
      (Ω.intervalList ht hs)[b]'hb = (Ω.toFun^[b + 1 + Ω.hitStep hs ht]) s := by
    intro b hb
    rw [Ω.getElem_intervalList ht hs hb,
      Function.iterate_add_apply Ω.toFun (b + 1) (Ω.hitStep hs ht) s, ht_iter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Function.iterate_zero_apply Ω.toFun s, ← ht_iter]
    exact h_mono (by omega) (by omega)
  · rw [← ht_iter]
    exact h_span (by omega)
  · intro a ha
    have ha_len : a < Ω.hitStep hs ht - 1 := by rwa [Ω.length_intervalList] at ha
    rw [hW1_iter a ha]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← Function.iterate_zero_apply Ω.toFun s]
      exact h_mono (by omega) (by omega)
    · rw [← ht_iter]
      exact h_mono (by omega) (by omega)
  · intro a₁ a₂ ha₁ ha₂ ha₁₂
    have ha₂_len : a₂ < Ω.hitStep hs ht - 1 := by rwa [Ω.length_intervalList] at ha₂
    rw [hW1_iter a₁ ha₁, hW1_iter a₂ ha₂]
    exact h_mono (by omega) (by omega)
  · intro b hb
    have hb_len : b < Ω.hitStep ht hs - 1 := by rwa [Ω.length_intervalList] at hb
    rw [hW2_iter b hb]
    refine ⟨?_, h_span (by omega)⟩
    conv_lhs => rw [← ht_iter]
    exact h_mono (by omega) (by omega)
  · intro b₁ b₂ hb₁ hb₂ hb₁₂
    have hb₂_len : b₂ < Ω.hitStep ht hs - 1 := by rwa [Ω.length_intervalList] at hb₂
    rw [hW2_iter b₁ hb₁, hW2_iter b₂ hb₂]
    exact h_mono (by omega) (by omega)

/-- `S₀` is a simple spanning reduction of `S`. -/
def IsSimpleReduction (S₀ S : Society α β) : Prop :=
  S₀.G ≤ S.G ∧
  V(S₀.G) = V(S.G) ∧
  S₀.Ω = S.Ω ∧
  S₀.IsKConnected 3 ∧
  (¬ ∃ Q₁ Q₂ : Graph α β, S₀.IsCross Q₁ Q₂) ∧
  (¬ ∃ T₁ T₂ T₃ : Graph α β, S₀.IsTripod T₁ T₂ T₃) ∧
  (∀ x : α, ¬ S₀.G.Adj x x) ∧
  (∀ e₁ e₂ x y, S₀.G.IsLink e₁ x y → S₀.G.IsLink e₂ x y → e₁ = e₂) ∧
  (∀ e x y, S.G.IsLink e x y → x = y ∨ S₀.G.Adj x y)

theorem exists_isSimpleReduction (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃) :
    ∃ S₀ : Society α β, IsSimpleReduction S₀ S :=
  exists_simple_reduction S hconn hnocross hnotripod

theorem exists_split_simple_reductions {S₀ S : Society α β}
    (hred : IsSimpleReduction S₀ S)
    {s t : α} (hs : s ∈ S₀.Ω.bar) (ht : t ∈ S₀.Ω.bar) (hst : s ≠ t)
    {P : Graph α β} (hP : IsGraphPathWithEnds S₀.G P s t) (hP_ind : P ≤i S₀.G)
    (hP_bar : Disjoint (V(P) \ {s, t}) S₀.Ω.bar)
    (hcatch : Catches (S₀.Ω.bar \ {s, t}) (deleteVertices S₀.G V(P))) :
    let hP_bar₂ : Disjoint (V(P) \ {t, s}) S₀.Ω.bar := by rw [pair_comm]; exact hP_bar
    let S₀₁ := splitSociety S₀ hs ht hst hP hP_bar hred.2.2.2.2.1
    let S₀₂ := splitSociety S₀ ht hs hst.symm hP.symm hP_bar₂ hred.2.2.2.2.1
    ∃ (E_base E_P : Set β) (S₁ S₂ : Society α β),
      IsSimpleReduction S₀₁ S₁ ∧
      IsSimpleReduction S₀₂ S₂ ∧
      S₁.G ≤ S.G.restrict E_base ∧
      S₂.G ≤ S.G.restrict E_base ∧
      V(S₁.G) ∪ V(S₂.G) = V(S.G.restrict E_base) ∧
      V(S₁.G) ∩ V(S₂.G) = V(P) ∧
      E(S₁.G) ∪ E(S₂.G) = E(S.G.restrict E_base) ∧
      Disjoint E(S₁.G) E(S₂.G) ∧
      E_base ∪ E_P = E(S.G) ∧
      Disjoint E_base E_P ∧
      (∀ e ∈ E_P, ∃ u v : α, S.G.IsLink e u v ∧ P.Adj u v) := by
  intro hP_bar₂ S₀₁ S₀₂
  have hcatch₂ : Catches (S₀.Ω.bar \ {t, s}) (deleteVertices S₀.G V(P)) := by
    rw [pair_comm]; exact hcatch
  rcases hred with ⟨hG₀_le, hV₀_eq, hΩ₀_eq, hconn₀, hnc₀, hnt₀, hloop₀, hsimp₀, hadj₀⟩
  let H₁ := splitSide S₀.G P (S₀.Ω.interval s t)
  let H₂ := splitSide S₀.G P (S₀.Ω.interval t s)
  have hV_S₀₁ : V(S₀₁.G) = V(P) ∪ V(H₁) :=
    vertexSet_splitGraph_eq_union S₀ hs ht hst hP hcatch hnc₀
  have hV_S₀₂ : V(S₀₂.G) = V(P) ∪ V(H₂) :=
    vertexSet_splitGraph_eq_union S₀ ht hs hst.symm hP.symm hcatch₂ hnc₀
  have hdisj_H : Disjoint V(H₁) V(H₂) := (lemma_2_4_H1_disjoint_H2 S₀ hs ht hst hP hnc₀).1
  have hdisj_P_H₁ : Disjoint V(P) V(H₁) := (disjoint_vertexSet_splitSide_P S₀.G P _).symm
  have hdisj_P_H₂ : Disjoint V(P) V(H₂) := (disjoint_vertexSet_splitSide_P S₀.G P _).symm
  have hV_union₀ : V(S₀₁.G) ∪ V(S₀₂.G) = V(S.G) := by
    rw [hV_S₀₁, hV_S₀₂, ← hV₀_eq, ← union_union_distrib_left]
    have hunion_H := congrArg Graph.vertexSet (lemma_2_4_H1_union_H2 S₀ hs ht hst hcatch)
    change V(H₁) ∪ V(H₂) = V(S₀.G) \ V(P) at hunion_H
    rw [hunion_H]
    exact union_sdiff_cancel hP.1.vertexSet_mono
  have hV_inter₀ : V(S₀₁.G) ∩ V(S₀₂.G) = V(P) := by
    rw [hV_S₀₁, hV_S₀₂, ← union_inter_distrib_left,
      Set.disjoint_iff_inter_eq_empty.mp hdisj_H, union_empty]
  let E_P : Set β := {e ∈ E(S.G) | ∃ u ∈ V(P), ∃ v ∈ V(P), u ≠ v ∧ S.G.IsLink e u v}
  let E₁ : Set β := {e ∈ E(S.G) \ E_P | ∃ u ∈ V(S₀₁.G), ∃ v ∈ V(S₀₁.G), S.G.IsLink e u v}
  let E₂ : Set β := {e ∈ E(S.G) \ (E_P ∪ E₁) | ∃ u ∈ V(S₀₂.G), ∃ v ∈ V(S₀₂.G), S.G.IsLink e u v}
  let E_base : Set β := E₁ ∪ E₂
  have hE₁_sub : E₁ ⊆ E(S.G) := fun _ he => he.1.1
  have hE₂_sub : E₂ ⊆ E(S.G) := fun _ he => he.1.1
  have hEP_sub : E_P ⊆ E(S.G) := fun _ he => he.1
  let G₁ := (S.G.induce V(S₀₁.G)).restrict E₁
  let G₂ := (S.G.induce V(S₀₂.G)).restrict E₂
  have hV_G₁ : V(G₁) = V(S₀₁.G) := rfl
  have hV_G₂ : V(G₂) = V(S₀₂.G) := rfl
  have hE_G₁ : E(G₁) = E₁ := by
    change E((S.G.induce V(S₀₁.G)).restrict E₁) = E₁
    rw [edgeSet_restrict, inter_eq_right]
    rintro e ⟨_, u, hu, v, hv, huv⟩
    exact ⟨u, v, huv, hu, hv⟩
  have hE_G₂ : E(G₂) = E₂ := by
    change E((S.G.induce V(S₀₂.G)).restrict E₂) = E₂
    rw [edgeSet_restrict, inter_eq_right]
    rintro e ⟨_, u, hu, v, hv, huv⟩
    exact ⟨u, v, huv, hu, hv⟩
  have hS₀₁_le_G₁ : S₀₁.G ≤ G₁ := by
    refine ⟨le_rfl, fun {e x y} hlink => ?_⟩
    have hlink₀ : S₀.G.IsLink e x y := hlink.mono (splitGraph_le S₀ P s t)
    have hlinkG : S.G.IsLink e x y := hlink₀.mono hG₀_le
    have hx₁ : x ∈ V(S₀₁.G) := hlink.left_mem
    have hy₁ : y ∈ V(S₀₁.G) := hlink.right_mem
    have hnot_EP : e ∉ E_P := by
      rintro ⟨_, u, huP, v, hvP, _, huv⟩
      rcases hlinkG.eq_and_eq_or_eq_and_eq huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact not_isLink_splitGraph_of_mem_P S₀ s t hP_ind hlink huP hvP
      · exact not_isLink_splitGraph_of_mem_P S₀ s t hP_ind hlink hvP huP
    have he₁ : e ∈ E₁ := ⟨⟨hlinkG.edge_mem, hnot_EP⟩, x, hx₁, y, hy₁, hlinkG⟩
    exact ⟨he₁, hlinkG, hx₁, hy₁⟩
  have hS₀₂_le_G₂ : S₀₂.G ≤ G₂ := by
    refine ⟨le_rfl, fun {e x y} hlink => ?_⟩
    have hlink₀ : S₀.G.IsLink e x y := hlink.mono (splitGraph_le S₀ P t s)
    have hlinkG : S.G.IsLink e x y := hlink₀.mono hG₀_le
    have hx₂ : x ∈ V(S₀₂.G) := hlink.left_mem
    have hy₂ : y ∈ V(S₀₂.G) := hlink.right_mem
    have hnot_both_P : ¬ (x ∈ V(P) ∧ y ∈ V(P)) := fun ⟨hxP, hyP⟩ =>
      not_isLink_splitGraph_of_mem_P S₀ t s hP_ind hlink hxP hyP
    have hnot_EP : e ∉ E_P := by
      rintro ⟨_, u, huP, v, hvP, _, huv⟩
      rcases hlinkG.eq_and_eq_or_eq_and_eq huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnot_both_P ⟨huP, hvP⟩
      · exact hnot_both_P ⟨hvP, huP⟩
    have hnot_E₁ : e ∉ E₁ := by
      rintro ⟨_, u, hu₁, v, hv₁, huv⟩
      rcases hlinkG.eq_and_eq_or_eq_and_eq huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hxP : x ∈ V(P) := hV_inter₀ ▸ ⟨hu₁, hx₂⟩
        have hyP : y ∈ V(P) := hV_inter₀ ▸ ⟨hv₁, hy₂⟩
        exact hnot_both_P ⟨hxP, hyP⟩
      · have hxP : x ∈ V(P) := hV_inter₀ ▸ ⟨hv₁, hx₂⟩
        have hyP : y ∈ V(P) := hV_inter₀ ▸ ⟨hu₁, hy₂⟩
        exact hnot_both_P ⟨hxP, hyP⟩
    have he₂ : e ∈ E₂ := ⟨⟨hlinkG.edge_mem, fun h => h.elim hnot_EP hnot_E₁⟩, x, hx₂, y, hy₂,
      hlinkG⟩
    exact ⟨he₂, hlinkG, hx₂, hy₂⟩
  have hG₁_le_S : G₁ ≤ S.G :=
    restrict_le.trans (S.G.induce_le (hV₀_eq ▸ (splitGraph_le S₀ P s t).vertexSet_mono))
  have hG₂_le_S : G₂ ≤ S.G :=
    restrict_le.trans (S.G.induce_le (hV₀_eq ▸ (splitGraph_le S₀ P t s).vertexSet_mono))
  let S₁ : Society α β := ⟨G₁, S₀₁.Ω, S.finite_V.subset hG₁_le_S.vertexSet_mono,
    S.finite_E.subset hG₁_le_S.edgeSet_mono, S₀₁.bar_subset⟩
  let S₂ : Society α β := ⟨G₂, S₀₂.Ω, S.finite_V.subset hG₂_le_S.vertexSet_mono,
    S.finite_E.subset hG₂_le_S.edgeSet_mono, S₀₂.bar_subset⟩
  have hred₁ : IsSimpleReduction S₀₁ S₁ := by
    refine ⟨hS₀₁_le_G₁, rfl, rfl,
      lemma_2_4_isKConnected_three S₀ hs ht hst hP hP_bar hcatch hnc₀ hconn₀,
      lemma_2_4_no_cross S₀ hs ht hst hP hP_ind hP_bar hcatch hnc₀ hnt₀,
      lemma_2_4_no_tripod S₀ hs ht hst hP hP_ind hP_bar hcatch hnc₀ hnt₀,
      fun x hx => hloop₀ x (hx.mono (splitGraph_le S₀ P s t)),
      fun e₁ e₂ x y h1 h2 =>
        hsimp₀ e₁ e₂ x y (h1.mono (splitGraph_le S₀ P s t)) (h2.mono (splitGraph_le S₀ P s t)),
      fun e x y hlink => ?_⟩
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      have hlinkG : S.G.IsLink e x y := hlink.2.1
      have hx₁ : x ∈ V(S₀₁.G) := hlink.2.2.1
      have hy₁ : y ∈ V(S₀₁.G) := hlink.2.2.2
      have he_not_EP : e ∉ E_P := hlink.1.1.2
      obtain ⟨e₀, he₀⟩ := (hadj₀ e x y hlinkG).resolve_left hxy
      have he₀_not_P : e₀ ∉ E(P) := by
        intro he₀P
        obtain ⟨u, v, huvP⟩ := P.exists_isLink_of_mem_edgeSet he₀P
        rcases he₀.eq_and_eq_or_eq_and_eq (huvP.mono hP.1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he_not_EP ⟨hlinkG.edge_mem, x, huvP.left_mem, y, huvP.right_mem, hxy, hlinkG⟩
        · exact he_not_EP ⟨hlinkG.edge_mem, x, huvP.right_mem, y, huvP.left_mem, hxy, hlinkG⟩
      exact ⟨e₀, (splitGraph_isLink_iff S₀ P s t).mpr ⟨he₀, he₀_not_P, hx₁.2, hy₁.2⟩⟩
  have hred₂ : IsSimpleReduction S₀₂ S₂ := by
    refine ⟨hS₀₂_le_G₂, rfl, rfl,
      lemma_2_4_isKConnected_three S₀ ht hs hst.symm hP.symm hP_bar₂ hcatch₂ hnc₀ hconn₀,
      lemma_2_4_no_cross S₀ ht hs hst.symm hP.symm hP_ind hP_bar₂ hcatch₂ hnc₀ hnt₀,
      lemma_2_4_no_tripod S₀ ht hs hst.symm hP.symm hP_ind hP_bar₂ hcatch₂ hnc₀ hnt₀,
      fun x hx => hloop₀ x (hx.mono (splitGraph_le S₀ P t s)),
      fun e₁ e₂ x y h1 h2 =>
        hsimp₀ e₁ e₂ x y (h1.mono (splitGraph_le S₀ P t s)) (h2.mono (splitGraph_le S₀ P t s)),
      fun e x y hlink => ?_⟩
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      have hlinkG : S.G.IsLink e x y := hlink.2.1
      have hx₂ : x ∈ V(S₀₂.G) := hlink.2.2.1
      have hy₂ : y ∈ V(S₀₂.G) := hlink.2.2.2
      have he_not_EP : e ∉ E_P := fun h => hlink.1.1.2 (Or.inl h)
      obtain ⟨e₀, he₀⟩ := (hadj₀ e x y hlinkG).resolve_left hxy
      have he₀_not_P : e₀ ∉ E(P) := by
        intro he₀P
        obtain ⟨u, v, huvP⟩ := P.exists_isLink_of_mem_edgeSet he₀P
        rcases he₀.eq_and_eq_or_eq_and_eq (huvP.mono hP.1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he_not_EP ⟨hlinkG.edge_mem, x, huvP.left_mem, y, huvP.right_mem, hxy, hlinkG⟩
        · exact he_not_EP ⟨hlinkG.edge_mem, x, huvP.right_mem, y, huvP.left_mem, hxy, hlinkG⟩
      exact ⟨e₀, (splitGraph_isLink_iff S₀ P t s).mpr ⟨he₀, he₀_not_P, hx₂.2, hy₂.2⟩⟩
  have hE_union_all : E_base ∪ E_P = E(S.G) := by
    refine Subset.antisymm (union_subset (union_subset hE₁_sub hE₂_sub) hEP_sub) fun e he => ?_
    by_cases heP : e ∈ E_P
    · exact Or.inr heP
    · left
      by_cases he₁ : e ∈ E₁
      · exact Or.inl he₁
      · right
        obtain ⟨x, y, hxy⟩ := S.G.exists_isLink_of_mem_edgeSet he
        refine ⟨⟨he, fun h => h.elim heP he₁⟩, x, ?_, y, ?_, hxy⟩
        · have hx_in : x ∈ V(S₀₁.G) ∪ V(S₀₂.G) := hV_union₀.symm ▸ hxy.left_mem
          rcases hx_in with hx₁ | hx₂
          · by_cases hy₁ : y ∈ V(S₀₁.G)
            · exact (he₁ ⟨⟨he, heP⟩, x, hx₁, y, hy₁, hxy⟩).elim
            · have hy_in : y ∈ V(S₀₁.G) ∪ V(S₀₂.G) := hV_union₀.symm ▸ hxy.right_mem
              have hy₂ : y ∈ V(S₀₂.G) := hy_in.resolve_left hy₁
              have hyH₂ : y ∈ V(H₂) := (hV_S₀₂ ▸ hy₂).resolve_left fun hyP => hy₁
                (hV_S₀₁ ▸ Or.inl hyP)
              rcases hV_S₀₁ ▸ hx₁ with hxP | hxH₁
              · exact hV_S₀₂ ▸ Or.inl hxP
              · have hne : x ≠ y := fun h => disjoint_left.mp hdisj_H hxH₁ (h ▸ hyH₂)
                obtain ⟨e₀, he₀⟩ := (hadj₀ e x y hxy).resolve_left hne
                exact (no_link_between_splitSides S₀ hs ht hst hP hnc₀ he₀ hxH₁ hyH₂).elim
          · exact hx₂
        · have hy_in : y ∈ V(S₀₁.G) ∪ V(S₀₂.G) := hV_union₀.symm ▸ hxy.right_mem
          rcases hy_in with hy₁ | hy₂
          · by_cases hx₁ : x ∈ V(S₀₁.G)
            · exact (he₁ ⟨⟨he, heP⟩, x, hx₁, y, hy₁, hxy⟩).elim
            · have hx_in : x ∈ V(S₀₁.G) ∪ V(S₀₂.G) := hV_union₀.symm ▸ hxy.left_mem
              have hx₂ : x ∈ V(S₀₂.G) := hx_in.resolve_left hx₁
              have hxH₂ : x ∈ V(H₂) := (hV_S₀₂ ▸ hx₂).resolve_left fun hxP => hx₁
                (hV_S₀₁ ▸ Or.inl hxP)
              rcases hV_S₀₁ ▸ hy₁ with hyP | hyH₁
              · exact hV_S₀₂ ▸ Or.inl hyP
              · have hne : x ≠ y := fun h => disjoint_left.mp hdisj_H (h ▸ hyH₁) hxH₂
                obtain ⟨e₀, he₀⟩ := (hadj₀ e x y hxy).resolve_left hne
                exact (no_link_between_splitSides S₀ hs ht hst hP hnc₀ he₀.symm hyH₁ hxH₂).elim
          · exact hy₂
  refine ⟨E_base, E_P, S₁, S₂, hred₁, hred₂, ?_, ?_, ?_, hV_inter₀, ?_, ?_, hE_union_all, ?_, ?_⟩
  · exact ⟨by rw [vertexSet_restrict]; exact hG₁_le_S.vertexSet_mono,
      fun {_ _ _} hl => ⟨Or.inl hl.1, hl.2.1⟩⟩
  · exact ⟨by rw [vertexSet_restrict]; exact hG₂_le_S.vertexSet_mono,
      fun {_ _ _} hl => ⟨Or.inr hl.1, hl.2.1⟩⟩
  · rw [vertexSet_restrict]
    exact hV_union₀
  · change E(G₁) ∪ E(G₂) = E(S.G.restrict (E₁ ∪ E₂))
    rw [hE_G₁, hE_G₂, edgeSet_restrict, inter_eq_right.mpr (union_subset hE₁_sub hE₂_sub)]
  · change Disjoint E(G₁) E(G₂)
    rw [hE_G₁, hE_G₂, disjoint_left]
    exact fun _ he₁ he₂ => he₂.1.2 (Or.inr he₁)
  · rw [disjoint_left]
    rintro e (he₁ | he₂) heP
    · exact he₁.1.2 heP
    · exact he₂.1.2 (Or.inl heP)
  · rintro e ⟨_, u, huP, v, hvP, huv_ne, huv_link⟩
    obtain ⟨e₀, he₀⟩ := (hadj₀ e u v huv_link).resolve_left huv_ne
    exact ⟨u, v, huv_link, e₀, hP_ind.isLink_of_mem_mem he₀ huP hvP⟩

theorem upperDiscMap_exp_upperSplitAngle_of_mem_P {G P : Graph α β} {s t : α}
    (hst : s ≠ t) (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) {k : ℕ}
    (hk : k < (pathWalkTS hP).support.length) :
    upperDiscMap (pathWalkTS hP).support.length
      (Circle.exp (upperSplitAngle hP θ' ((pathWalkTS hP).support[k]'hk)) : ℂ) =
      (pathX (pathWalkTS hP).support.length k : ℂ) := by
  let m := (pathWalkTS hP).support.length
  have hm : 2 ≤ m := two_le_length_support_pathWalkTS hst hP
  rw [upperSplitAngle_of_mem_P hP θ' hk, circle_exp_two_pi_sub_arccos (pathX_mem_Icc hm hk)]
  exact upperDiscMap_pathX m hk

theorem lowerDiscMap_exp_lowerSplitAngle_of_mem_P {G P : Graph α β} {s t : α}
    (hst : s ≠ t) (hP : IsGraphPathWithEnds G P s t) (θ' : α → ℝ) {k : ℕ}
    (hk : k < (pathWalkTS hP).support.length) :
    lowerDiscMap (pathWalkTS hP).support.length
      (Circle.exp (lowerSplitAngle hP θ' ((pathWalkTS hP).support[k]'hk)) : ℂ) =
      (pathX (pathWalkTS hP).support.length k : ℂ) := by
  let m := (pathWalkTS hP).support.length
  have hm : 2 ≤ m := two_le_length_support_pathWalkTS hst hP
  rw [lowerSplitAngle_of_mem_P hP θ' hk, circle_exp_arccos (pathX_mem_Icc hm hk)]
  exact lowerDiscMap_pathX m hk

theorem upperDiscMap_exp_upperSplitAngle_of_not_mem_P {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) {θ' : α → ℝ} {v : α}
    (hv_not_P : v ∉ V(P)) (h1 : θ' s < θ' v) (h2 : θ' v < θ' t) :
    upperDiscMap (pathWalkTS hP).support.length
      (Circle.exp (upperSplitAngle hP θ' v) : ℂ) =
      (Circle.exp (2 * Real.pi + Real.pi * (θ' v - θ' s) / (θ' t - θ' s)) : ℂ) := by
  rw [upperSplitAngle_of_not_mem_P hP θ' hv_not_P]
  let u := Real.pi * (θ' v - θ' s) / (θ' t - θ' s)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff : 0 < θ' t - θ' s := by linarith
  have hu0 : 0 < u := div_pos (mul_pos hpi (by linarith)) hdiff
  have hu_pi : u < Real.pi := by
    dsimp [u]
    rw [div_lt_iff₀ hdiff]
    nlinarith
  have hexp_eq : Circle.exp (2 * Real.pi + u) = Circle.exp u := by
    rw [Circle.exp_add, Circle.exp_two_pi, one_mul]
  have him : 0 ≤ ((Circle.exp (2 * Real.pi + u) : ℂ)).im := by
    rw [hexp_eq]
    simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    exact (Real.sin_pos_of_pos_of_lt_pi hu0 hu_pi).le
  exact upperDiscMap_eq_self_of_mem_sphere (Circle.exp _).2 him

theorem lowerDiscMap_exp_lowerSplitAngle_of_not_mem_P {G P : Graph α β} {s t : α}
    (hP : IsGraphPathWithEnds G P s t) {θ' : α → ℝ} {v : α}
    (hv_not_P : v ∉ V(P)) (h1 : θ' t < θ' v) (h2 : θ' v < θ' s + 2 * Real.pi) :
    lowerDiscMap (pathWalkTS hP).support.length
      (Circle.exp (lowerSplitAngle hP θ' v) : ℂ) =
      (Circle.exp (Real.pi + Real.pi * (θ' v - θ' t) / (θ' s + 2 * Real.pi - θ' t)) : ℂ) := by
  rw [lowerSplitAngle_of_not_mem_P hP θ' hv_not_P]
  let u := Real.pi * (θ' v - θ' t) / (θ' s + 2 * Real.pi - θ' t)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff : 0 < θ' s + 2 * Real.pi - θ' t := by linarith
  have hu0 : 0 < u := div_pos (mul_pos hpi (by linarith)) hdiff
  have hu_pi : u < Real.pi := by
    dsimp [u]
    rw [div_lt_iff₀ hdiff]
    nlinarith
  have him : ((Circle.exp (Real.pi + u) : ℂ)).im ≤ 0 := by
    simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    rw [add_comm Real.pi u, Real.sin_add_pi]
    linarith [Real.sin_pos_of_pos_of_lt_pi hu0 hu_pi]
  exact lowerDiscMap_eq_self_of_mem_sphere (Circle.exp _).2 him

open Classical in
private theorem glue_drawings_along_path {S S₀ S₁ S₂ : Society α β} {s t : α}
    {P : Graph α β} (hP₀ : IsGraphPathWithEnds S₀.G P s t) (hm : 2 ≤ (pathWalkTS
      hP₀).support.length)
    {E_base E_P : Set β}
    (hS₁_le_base : S₁.G ≤ S.G.restrict E_base) (hS₂_le_base : S₂.G ≤ S.G.restrict E_base)
    (hV_union_base : V(S₁.G) ∪ V(S₂.G) = V(S.G.restrict E_base))
    (hV_inter_P : V(S₁.G) ∩ V(S₂.G) = V(P))
    (hE_union_base : E(S₁.G) ∪ E(S₂.G) = E(S.G.restrict E_base))
    (hE_disj_base : Disjoint E(S₁.G) E(S₂.G)) (hE_union_all : E_base ∪ E_P = E(S.G))
    (hE_disj_all : Disjoint E_base E_P)
    (hEP_adj : ∀ e ∈ E_P, ∃ u v : α, S.G.IsLink e u v ∧ P.Adj u v)
    {ν₁ ν₂ : α → ℂ} {Γ₁ : GraphDrawing S₁.G ℂ} {Γ₂ : GraphDrawing S₂.G ℂ}
    (hν₁_inj : InjOn ν₁ V(S₁.G)) (hν₂_inj : InjOn ν₂ V(S₂.G))
    (hU₁_ball : Γ₁.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1)
    (hU₂_ball : Γ₂.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1)
    (hν₁_eq : ∀ v : V(S₁.G), (Γ₁.iso.vertexEquiv v).1 = ν₁ v.1)
    (hν₂_eq : ∀ v : V(S₂.G), (Γ₂.iso.vertexEquiv v).1 = ν₂ v.1) :
    let L_P := (pathWalkTS hP₀).support
    let m := L_P.length
    (∀ k (hk : k < m), upperDiscMap m (ν₁ (L_P[k]'hk)) = (pathX m k : ℂ)) →
    (∀ v ∈ V(P), upperDiscMap m (ν₁ v) = lowerDiscMap m (ν₂ v)) →
    ∃ (ν_mid : α → ℂ) (Γ_mid : GraphDrawing S.G ℂ),
      (∀ v ∈ V(S₁.G), ν_mid v = upperDiscMap m (ν₁ v)) ∧
      (∀ v ∈ V(S₂.G), ν_mid v = lowerDiscMap m (ν₂ v)) ∧
      InjOn ν_mid V(S.G) ∧ Γ_mid.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1 ∧
      Γ_mid.drawing.U ⊆ (upperDiscMap m '' Γ₁.drawing.U ∪ lowerDiscMap m '' Γ₂.drawing.U) ∪
        {w : ℂ | ∃ j k : ℕ, k + 1 < m ∧ w ∈ lensArc m k (1 / (4 * ((j : ℝ) + 2)))} ∧
      ∀ v : V(S.G), (Γ_mid.iso.vertexEquiv v).1 = ν_mid v.1 := by
  intro L_P m hP_val₁ hP_agree
  obtain ⟨Γ₁', hU₁', hV₁', hν₁'_eq⟩ :=
    GraphDrawing.transport Γ₁
      ((isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset Γ₁.drawing.isClosed_U hU₁_ball)
      hν₁_eq (continuous_upperDiscMap m) (injOn_upperDiscMap hm |>.mono hU₁_ball)
  obtain ⟨Γ₂', hU₂', hV₂', hν₂'_eq⟩ :=
    GraphDrawing.transport Γ₂
      ((isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset Γ₂.drawing.isClosed_U hU₂_ball)
      hν₂_eq (continuous_lowerDiscMap m) (injOn_lowerDiscMap hm |>.mono hU₂_ball)
  let ν_mid (v : α) : ℂ :=
    if v ∈ V(S₁.G) then upperDiscMap m (ν₁ v) else lowerDiscMap m (ν₂ v)
  have hν_mid_1 : ∀ v ∈ V(S₁.G), ν_mid v = upperDiscMap m (ν₁ v) :=
    fun v hv => by simp [ν_mid, hv]
  have hν_mid_2 : ∀ v ∈ V(S₂.G), ν_mid v = lowerDiscMap m (ν₂ v) := by
    intro v hv₂
    dsimp [ν_mid]
    split_ifs with hv₁
    · exact hP_agree v (hV_inter_P ▸ ⟨hv₁, hv₂⟩)
    · rfl
  have hν₁_in_ball : ∀ v ∈ V(S₁.G), ν₁ v ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro v hv
    have : ν₁ v ∈ Γ₁.drawing.V := by
      rw [← hν₁_eq ⟨v, hv⟩]; exact (Γ₁.iso.vertexEquiv ⟨v, hv⟩).2
    exact hU₁_ball (Γ₁.drawing.V_subset_U this)
  have hν₂_in_ball : ∀ v ∈ V(S₂.G), ν₂ v ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro v hv
    have : ν₂ v ∈ Γ₂.drawing.V := by
      rw [← hν₂_eq ⟨v, hv⟩]; exact (Γ₂.iso.vertexEquiv ⟨v, hv⟩).2
    exact hU₂_ball (Γ₂.drawing.V_subset_U this)
  have hU_inter_P :
      (upperDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∩
        (lowerDiscMap m '' Metric.closedBall (0 : ℂ) 1) ⊆
        ν_mid '' V(P) := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := upperDiscMap_inter_lowerDiscMap hm hw
    have hkP : L_P[k]'hk ∈ V(P) := by
      rw [vertexSet_eq_support_pathWalkTS hP₀]; exact List.getElem_mem hk
    have hk₁ : L_P[k]'hk ∈ V(S₁.G) := by
      have : V(P) ⊆ V(S₁.G) := hV_inter_P ▸ inter_subset_left
      exact this hkP
    refine ⟨L_P[k]'hk, hkP, ?_⟩
    rw [hν_mid_1 _ hk₁, hP_val₁ k hk]
  have hν_mid_inj : InjOn ν_mid V(S.G) := by
    have hV_S_eq : V(S.G) = V(S₁.G) ∪ V(S₂.G) := by
      have := hV_union_base.symm
      rwa [vertexSet_restrict] at this
    intro u hu v hv heq
    rw [hV_S_eq] at hu hv
    rcases hu with hu₁ | hu₂ <;> rcases hv with hv₁ | hv₂
    · rw [hν_mid_1 u hu₁, hν_mid_1 v hv₁] at heq
      exact hν₁_inj hu₁ hv₁ (injOn_upperDiscMap hm (hν₁_in_ball u hu₁) (hν₁_in_ball v hv₁) heq)
    · have hw_in : ν_mid u ∈
          (upperDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∩
            (lowerDiscMap m '' Metric.closedBall (0 : ℂ) 1) := by
        refine ⟨?_, ?_⟩
        · rw [hν_mid_1 u hu₁]; exact ⟨ν₁ u, hν₁_in_ball u hu₁, rfl⟩
        · rw [heq, hν_mid_2 v hv₂]; exact ⟨ν₂ v, hν₂_in_ball v hv₂, rfl⟩
      obtain ⟨p, hpP, hp_eq⟩ := hU_inter_P hw_in
      have hp₁ : p ∈ V(S₁.G) := (hV_inter_P ▸ inter_subset_left) hpP
      have hp₂ : p ∈ V(S₂.G) := (hV_inter_P ▸ inter_subset_right) hpP
      have hup : u = p := by
        have heq1 : upperDiscMap m (ν₁ p) = upperDiscMap m (ν₁ u) := by
          rw [← hν_mid_1 p hp₁, ← hν_mid_1 u hu₁, hp_eq]
        exact (hν₁_inj hp₁ hu₁
          (injOn_upperDiscMap hm (hν₁_in_ball p hp₁) (hν₁_in_ball u hu₁) heq1)).symm
      have hvp : v = p := by
        have heq2 : lowerDiscMap m (ν₂ p) = lowerDiscMap m (ν₂ v) := by
          rw [← hν_mid_2 p hp₂, ← hν_mid_2 v hv₂, hp_eq, heq]
        exact (hν₂_inj hp₂ hv₂
          (injOn_lowerDiscMap hm (hν₂_in_ball p hp₂) (hν₂_in_ball v hv₂) heq2)).symm
      exact hup.trans hvp.symm
    · have hw_in : ν_mid v ∈
          (upperDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∩
            (lowerDiscMap m '' Metric.closedBall (0 : ℂ) 1) := by
        refine ⟨?_, ?_⟩
        · rw [hν_mid_1 v hv₁]; exact ⟨ν₁ v, hν₁_in_ball v hv₁, rfl⟩
        · rw [← heq, hν_mid_2 u hu₂]; exact ⟨ν₂ u, hν₂_in_ball u hu₂, rfl⟩
      obtain ⟨p, hpP, hp_eq⟩ := hU_inter_P hw_in
      have hp₁ : p ∈ V(S₁.G) := (hV_inter_P ▸ inter_subset_left) hpP
      have hp₂ : p ∈ V(S₂.G) := (hV_inter_P ▸ inter_subset_right) hpP
      have hvp : v = p := by
        have heq1 : upperDiscMap m (ν₁ p) = upperDiscMap m (ν₁ v) := by
          rw [← hν_mid_1 p hp₁, ← hν_mid_1 v hv₁, hp_eq]
        exact (hν₁_inj hp₁ hv₁
          (injOn_upperDiscMap hm (hν₁_in_ball p hp₁) (hν₁_in_ball v hv₁) heq1)).symm
      have hup : u = p := by
        have heq2 : lowerDiscMap m (ν₂ p) = lowerDiscMap m (ν₂ u) := by
          rw [← hν_mid_2 p hp₂, ← hν_mid_2 u hu₂, hp_eq, ← heq]
        exact (hν₂_inj hp₂ hu₂
          (injOn_lowerDiscMap hm (hν₂_in_ball p hp₂) (hν₂_in_ball u hu₂) heq2)).symm
      exact hup.trans hvp.symm
    · rw [hν_mid_2 u hu₂, hν_mid_2 v hv₂] at heq
      exact hν₂_inj hu₂ hv₂ (injOn_lowerDiscMap hm (hν₂_in_ball u hu₂) (hν₂_in_ball v hv₂) heq)
  have hmeet_base : Γ₁'.drawing.U ∩ Γ₂'.drawing.U ⊆ ν_mid '' (V(S₁.G) ∩ V(S₂.G)) := by
    rw [hU₁', hU₂', hV_inter_P]
    exact (inter_subset_inter (image_mono hU₁_ball) (image_mono hU₂_ball)).trans hU_inter_P
  obtain ⟨Γ_base, hU_base, hν_base⟩ :=
    GraphDrawing.glue hS₁_le_base hS₂_le_base hV_union_base hE_union_base hE_disj_base
      (by rw [vertexSet_restrict]; exact hν_mid_inj) Γ₁' Γ₂'
      (fun v => (hν₁'_eq v).trans (hν_mid_1 v.1 v.2).symm)
      (fun v => (hν₂'_eq v).trans (hν_mid_2 v.1 v.2).symm)
      hmeet_base
  have hU_base_sub : Γ_base.drawing.U ⊆
      (upperDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∪
      (lowerDiscMap m '' Metric.closedBall (0 : ℂ) 1) := by
    rw [hU_base, hU₁', hU₂']
    exact union_subset_union (image_mono hU₁_ball) (image_mono hU₂_ball)
  have hEP_links : ∀ e ∈ E_P, ∃ u v : α, S.G.IsLink e u v ∧
      ∃ k : ℕ, k + 1 < m ∧ ν_mid u = (pathX m k : ℂ) ∧ ν_mid v = (pathX m (k + 1) : ℂ) := by
    intro e heP
    obtain ⟨u, v, huv_link, huv_adj⟩ := hEP_adj e heP
    obtain ⟨k, hk, hpair⟩ := exists_support_index_of_adj_pathWalkTS hP₀ huv_adj
    have hk0 : k < m := Nat.lt_trans (Nat.lt_succ_self k) hk
    have hkP0 : L_P[k]'hk0 ∈ V(P) := by
      rw [vertexSet_eq_support_pathWalkTS hP₀]; exact List.getElem_mem hk0
    have hkP1 : L_P[k + 1]'hk ∈ V(P) := by
      rw [vertexSet_eq_support_pathWalkTS hP₀]; exact List.getElem_mem hk
    have hk1_0 : L_P[k]'hk0 ∈ V(S₁.G) := (hV_inter_P ▸ inter_subset_left) hkP0
    have hk1_1 : L_P[k + 1]'hk ∈ V(S₁.G) := (hV_inter_P ▸ inter_subset_left) hkP1
    have hval0 : ν_mid (L_P[k]'hk0) = (pathX m k : ℂ) := by
      rw [hν_mid_1 _ hk1_0, hP_val₁ k hk0]
    have hval1 : ν_mid (L_P[k + 1]'hk) = (pathX m (k + 1) : ℂ) := by
      rw [hν_mid_1 _ hk1_1, hP_val₁ (k + 1) hk]
    have hu_in : u ∈ ({L_P[k]'hk0, L_P[k + 1]'hk} : Set α) := hpair ▸ by simp
    have hv_in : v ∈ ({L_P[k]'hk0, L_P[k + 1]'hk} : Set α) := hpair ▸ by simp
    have hLP0_in : L_P[k]'hk0 ∈ ({u, v} : Set α) := by
      rw [hpair]; exact Or.inl rfl
    have hLP1_in : L_P[k + 1]'hk ∈ ({u, v} : Set α) := by
      rw [hpair]; exact Or.inr (mem_singleton _)
    have hne_LP : L_P[k]'hk0 ≠ L_P[k + 1]'hk := fun heq => by
      have := (List.Nodup.getElem_inj_iff (isSimple_pathWalkTS hP₀)).mp heq
      omega
    rcases hu_in with rfl | rfl <;> rcases hv_in with rfl | rfl
    · exfalso
      rcases hLP1_in with h1 | h1
      · exact hne_LP h1.symm
      · exact hne_LP (mem_singleton_iff.mp h1).symm
    · exact ⟨_, _, huv_link, k, hk, hval0, hval1⟩
    · exact ⟨_, _, huv_link.symm, k, hk, hval0, hval1⟩
    · exfalso
      rcases hLP0_in with h0 | h0
      · exact hne_LP h0
      · exact hne_LP (mem_singleton_iff.mp h0)
  obtain ⟨Γ_mid, hU_mid_sub₁, hU_mid_sub₂, hν_mid_eq⟩ :=
    exists_drawing_gluing_lensArcs hm S.finite_E hE_union_all hE_disj_all
      hν_mid_inj hEP_links Γ_base hU_base_sub hν_base
  have hU_mid_ball : Γ_mid.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1 := by
    refine hU_mid_sub₂.trans (union_subset ?_ ?_)
    · refine hU_base_sub.trans (union_subset ?_ ?_)
      · rintro w ⟨z, hz, rfl⟩; exact upperDiscMap_mem_closedBall hm hz
      · rintro w ⟨z, hz, rfl⟩; exact lowerDiscMap_mem_closedBall hm hz
    · rintro w ⟨j, k, hk, hw⟩
      have hc0 : (0 : ℝ) < 1 / (4 * ((j : ℝ) + 2)) := by positivity
      have hc1 : 1 / (4 * ((j : ℝ) + 2)) < (1 : ℝ) / 2 := by
        have : (2 : ℝ) < 4 * ((j : ℝ) + 2) := by linarith
        exact one_div_lt_one_div_of_lt (by norm_num) this
      exact lensArc_subset_closedBall hm hk hc0 hc1 hw
  have hcover := hU_mid_sub₂
  rw [hU_base, hU₁', hU₂'] at hcover
  exact ⟨ν_mid, Γ_mid, hν_mid_1, hν_mid_2, hν_mid_inj, hU_mid_ball, hcover, hν_mid_eq⟩

private theorem glued_drawing_meets_sphere {S S₀ S₁ S₂ : Society α β} {s t : α}
    (hΩ : S₀.Ω = S.Ω) (hs₀ : s ∈ S₀.Ω.bar) (ht₀ : t ∈ S₀.Ω.bar) (hst : s ≠ t)
    {P : Graph α β} (hP₀ : IsGraphPathWithEnds S₀.G P s t)
    {ν₁ ν₂ ν_mid : α → ℂ} {Γ₁ : GraphDrawing S₁.G ℂ} {Γ₂ : GraphDrawing S₂.G ℂ}
    {Γ_mid : GraphDrawing S.G ℂ}
    (hU₁_ball : Γ₁.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1)
    (hU₂_ball : Γ₂.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1)
    (hU₁_sph : Γ₁.drawing.U ∩ Metric.sphere (0 : ℂ) 1 = ν₁ '' S₁.Ω.bar)
    (hU₂_sph : Γ₂.drawing.U ∩ Metric.sphere (0 : ℂ) 1 = ν₂ '' S₂.Ω.bar)
    (hbar₁_eq : S₁.Ω.bar = S₀.Ω.interval s t ∪ V(P))
    (hbar₂_eq : S₂.Ω.bar = S₀.Ω.interval t s ∪ V(P))
    (hν_mid_eq : ∀ v : V(S.G), (Γ_mid.iso.vertexEquiv v).1 = ν_mid v.1)
    (hν_mid_s : ν_mid s = 1) (hν_mid_t : ν_mid t = -1)
    (hθ₁ : ∀ v ∈ S₀.Ω.interval s t, ν_mid v ∈ Metric.sphere (0 : ℂ) 1)
    (hθ₂ : ∀ v ∈ S₀.Ω.interval t s, ν_mid v ∈ Metric.sphere (0 : ℂ) 1) :
    let L_P := (pathWalkTS hP₀).support
    let m := L_P.length
    2 ≤ m →
    (∀ v ∈ V(S₁.G), ν_mid v = upperDiscMap m (ν₁ v)) →
    (∀ v ∈ V(S₂.G), ν_mid v = lowerDiscMap m (ν₂ v)) →
    (∀ k (hk : k < m), upperDiscMap m (ν₁ (L_P[k]'hk)) = (pathX m k : ℂ)) →
    (∀ k (hk : k < m), lowerDiscMap m (ν₂ (L_P[k]'hk)) = (pathX m k : ℂ)) →
    Γ_mid.drawing.U ⊆ (upperDiscMap m '' Γ₁.drawing.U ∪ lowerDiscMap m '' Γ₂.drawing.U) ∪
      {w : ℂ | ∃ j k : ℕ, k + 1 < m ∧ w ∈ lensArc m k (1 / (4 * ((j : ℝ) + 2)))} →
    Γ_mid.drawing.U ∩ Metric.sphere (0 : ℂ) 1 = ν_mid '' S.Ω.bar := by
  intro L_P m hm hν_mid_1 hν_mid_2 hP_val₁ hP_val₂ hU_mid_cover
  refine Subset.antisymm ?_ ?_
  · rintro w ⟨hwU, hwS⟩
    rcases hU_mid_cover hwU with hw_base | ⟨j, k, hk, hw_lens⟩
    · rcases hw_base with hw₁' | hw₂'
      · obtain ⟨z, hzU₁, rfl⟩ := hw₁'
        have hz_sph : z ∈ Metric.sphere (0 : ℂ) 1 :=
          ((upperDiscMap_mem_sphere_iff hm (hU₁_ball hzU₁)).mp hwS).1
        have hz_bar₁ : z ∈ ν₁ '' S₁.Ω.bar := hU₁_sph ▸ ⟨hzU₁, hz_sph⟩
        obtain ⟨v, hv_bar₁, rfl⟩ := hz_bar₁
        have hv₁ : v ∈ V(S₁.G) := S₁.bar_subset hv_bar₁
        rw [← hν_mid_1 v hv₁] at hwS ⊢
        rcases hbar₁_eq ▸ hv_bar₁ with hvW1 | hvP
        · exact ⟨v, hΩ ▸ hvW1.1.1, rfl⟩
        · have hv_LP : v ∈ L_P := by
            change v ∈ {x | x ∈ (pathWalkTS hP₀).support}
            rwa [← vertexSet_eq_support_pathWalkTS hP₀]
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv_LP
          rw [hν_mid_1 _ hv₁, hP_val₁ k hk] at hwS
          have hnorm1 : |pathX m k| = 1 := by
            simpa [Complex.norm_real] using hwS
          have hxk_Icc := pathX_mem_Icc hm hk
          have hk_end : k = 0 ∨ k = m - 1 := by
            rcases eq_or_eq_neg_of_abs_eq hnorm1 with h1 | h1
            · right
              by_contra hne
              have : pathX m k < pathX m (m - 1) := pathX_strictMono hm (by omega)
              rw [pathX_pred hm] at this
              linarith
            · left
              by_contra hne
              have : pathX m 0 < pathX m k := pathX_strictMono hm (by omega)
              rw [pathX_zero] at this
              linarith
          rcases hk_end with rfl | rfl
          · have ht_LP : L_P[0]'hk = t := support_getElem_zero (pathWalkTS hP₀) hk
            rw [ht_LP]
            exact ⟨t, hΩ ▸ ht₀, rfl⟩
          · have hs_LP : L_P[m - 1]'hk = s := support_getElem_last (pathWalkTS hP₀)
            rw [hs_LP]
            exact ⟨s, hΩ ▸ hs₀, rfl⟩
      · obtain ⟨z, hzU₂, rfl⟩ := hw₂'
        have hz_sph : z ∈ Metric.sphere (0 : ℂ) 1 :=
          ((lowerDiscMap_mem_sphere_iff hm (hU₂_ball hzU₂)).mp hwS).1
        have hz_bar₂ : z ∈ ν₂ '' S₂.Ω.bar := hU₂_sph ▸ ⟨hzU₂, hz_sph⟩
        obtain ⟨v, hv_bar₂, rfl⟩ := hz_bar₂
        have hv₂ : v ∈ V(S₂.G) := S₂.bar_subset hv_bar₂
        rw [← hν_mid_2 v hv₂] at hwS ⊢
        rcases hbar₂_eq ▸ hv_bar₂ with hvW2 | hvP
        · exact ⟨v, hΩ ▸ hvW2.1.1, rfl⟩
        · have hv_LP : v ∈ L_P := by
            change v ∈ {x | x ∈ (pathWalkTS hP₀).support}
            rwa [← vertexSet_eq_support_pathWalkTS hP₀]
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv_LP
          rw [hν_mid_2 _ hv₂, hP_val₂ k hk] at hwS
          have hnorm1 : |pathX m k| = 1 := by
            simpa [Complex.norm_real] using hwS
          have hk_end : k = 0 ∨ k = m - 1 := by
            rcases eq_or_eq_neg_of_abs_eq hnorm1 with h1 | h1
            · right
              by_contra hne
              have : pathX m k < pathX m (m - 1) := pathX_strictMono hm (by omega)
              rw [pathX_pred hm] at this
              linarith
            · left
              by_contra hne
              have : pathX m 0 < pathX m k := pathX_strictMono hm (by omega)
              rw [pathX_zero] at this
              linarith
          rcases hk_end with rfl | rfl
          · have ht_LP : L_P[0]'hk = t := support_getElem_zero (pathWalkTS hP₀) hk
            rw [ht_LP]
            exact ⟨t, hΩ ▸ ht₀, rfl⟩
          · have hs_LP : L_P[m - 1]'hk = s := support_getElem_last (pathWalkTS hP₀)
            rw [hs_LP]
            exact ⟨s, hΩ ▸ hs₀, rfl⟩
    · have hc0 : (0 : ℝ) < 1 / (4 * ((j : ℝ) + 2)) := by positivity
      have hc1 : 1 / (4 * ((j : ℝ) + 2)) < (1 : ℝ) / 2 := by
        have : (2 : ℝ) < 4 * ((j : ℝ) + 2) := by linarith
        exact one_div_lt_one_div_of_lt (by norm_num) this
      rcases lensArc_inter_sphere hm hk hc0 hc1 ⟨hw_lens, hwS⟩ with rfl | rfl
      · rw [pathX_zero]; exact ⟨t, hΩ ▸ ht₀, by simpa using hν_mid_t⟩
      · rw [pathX_pred hm]; exact ⟨s, hΩ ▸ hs₀, by simpa using hν_mid_s⟩
  · rintro w ⟨v, hv_bar, rfl⟩
    have hvG : v ∈ V(S.G) := S.bar_subset hv_bar
    have hvU : ν_mid v ∈ Γ_mid.drawing.U := by
      rw [← hν_mid_eq ⟨v, hvG⟩]
      exact Γ_mid.drawing.V_subset_U (Γ_mid.iso.vertexEquiv ⟨v, hvG⟩).2
    refine ⟨hvU, ?_⟩
    have hv_bar₀ : v ∈ S₀.Ω.bar := hΩ.symm ▸ hv_bar
    by_cases hvs : v = s
    · subst hvs; rw [hν_mid_s]; simp
    · by_cases hvt : v = t
      · subst hvt; rw [hν_mid_t]; simp
      · rcases S₀.Ω.mem_interval_or_interval_swap hs₀ ht₀ hv_bar₀ hst hvs hvt with hv1 | hv2
        · exact hθ₁ v hv1
        · exact hθ₂ v hv2

open Classical in
theorem exists_disc_drawing_of_isSimpleReduction :
    ∀ (n : ℕ) (S₀ S : Society α β),
      IsSimpleReduction S₀ S →
      E(S₀.G).ncard = n →
      ∀ (L : List α), S.Ω.IsOrbitList L →
      ∀ (θ : α → ℝ), IsValidAngle L θ →
      ∃ (ν : α → ℂ) (Γ : GraphDrawing S.G ℂ),
        InjOn ν V(S.G) ∧
        (∀ v ∈ S.Ω.bar, ν v = (Circle.exp (θ v) : ℂ)) ∧
        Γ.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1 ∧
        Γ.drawing.U ∩ Metric.sphere (0 : ℂ) 1 = ν '' S.Ω.bar ∧
        ∀ v : V(S.G), (Γ.iso.vertexEquiv v).1 = ν v.1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro S₀ S hred hn L hL θ hθ
    by_cases hE₀ : E(S₀.G).Nonempty
    · obtain ⟨s, hs₀, t, ht₀, hst, P, hP₀, hP_ind₀, hP_bar₀, hcatch₀⟩ :=
        exists_induced_catches_path_of_three_connected_nonempty S₀
          hred.2.2.2.1 hred.2.2.2.2.2.2.1 hred.2.2.2.2.2.2.2.1 hE₀
      have hP_bar₂₀ : Disjoint (V(P) \ {t, s}) S₀.Ω.bar := by rw [pair_comm]; exact hP_bar₀
      let S₀₁ := splitSociety S₀ hs₀ ht₀ hst hP₀ hP_bar₀ hred.2.2.2.2.1
      let S₀₂ := splitSociety S₀ ht₀ hs₀ hst.symm hP₀.symm hP_bar₂₀ hred.2.2.2.2.1
      obtain ⟨E_base, E_P, S₁, S₂, hred₁, hred₂, hS₁_le_base, hS₂_le_base,
          hV_union_base, hV_inter_P, hE_union_base, hE_disj_base,
          hE_union_all, hE_disj_all, hEP_adj⟩ :=
        exists_split_simple_reductions hred hs₀ ht₀ hst hP₀ hP_ind₀ hP_bar₀ hcatch₀
      have hlt₁ : E(S₀₁.G).ncard < n := by
        rw [← hn]
        exact lemma_2_4_edgeSet_ncard_lt S₀ hst hP₀
      have hlt₂ : E(S₀₂.G).ncard < n := by
        rw [← hn]
        exact lemma_2_4_edgeSet_ncard_lt S₀ hst.symm hP₀.symm
      have hL₀ : S₀.Ω.IsOrbitList L := hred.2.2.1 ▸ hL
      have hsL : s ∈ L := by rwa [← hL₀.2.2.1] at hs₀
      let i₀ := CyclicPerm.indexOfMem L hsL
      let θ' := shiftedAngle L θ i₀
      obtain ⟨h_st, h_span, h_W1_bounds, h_W1_mono, h_W2_bounds, h_W2_mono⟩ :=
        shiftedAngle_intervalList_props hL₀ hθ hs₀ ht₀ hst
      let L₁ := splitList S₀ hs₀ ht₀ hP₀
      let L₂ := splitList S₀ ht₀ hs₀ hP₀.symm
      let θ₁ := upperSplitAngle hP₀ θ'
      let θ₂ := lowerSplitAngle hP₀ θ'
      have hL₁ : S₁.Ω.IsOrbitList L₁ := hred₁.2.2.1 ▸ isOrbitList_splitList S₀ hs₀ ht₀ hst hP₀
        hP_bar₀
      have hL₂ : S₂.Ω.IsOrbitList L₂ :=
        hred₂.2.2.1 ▸ isOrbitList_splitList S₀ ht₀ hs₀ hst.symm hP₀.symm hP_bar₂₀
      have hθ₁ : IsValidAngle L₁ θ₁ :=
        isValidAngle_upperSplitAngle S₀ hs₀ ht₀ hst hP₀ hP_bar₀ h_st h_W1_bounds h_W1_mono
      have hθ₂ : IsValidAngle L₂ θ₂ :=
        isValidAngle_lowerSplitAngle S₀ hs₀ ht₀ hst hP₀ hP_bar₀ h_span h_W2_bounds h_W2_mono
      obtain ⟨ν₁, Γ₁, hν₁_inj, hν₁_bar, hU₁_ball, hU₁_sph, hν₁_eq⟩ :=
        ih _ hlt₁ S₀₁ S₁ hred₁ rfl L₁ hL₁ θ₁ hθ₁
      obtain ⟨ν₂, Γ₂, hν₂_inj, hν₂_bar, hU₂_ball, hU₂_sph, hν₂_eq⟩ :=
        ih _ hlt₂ S₀₂ S₂ hred₂ rfl L₂ hL₂ θ₂ hθ₂
      let L_P := (pathWalkTS hP₀).support
      let m := L_P.length
      have hm : 2 ≤ m := two_le_length_support_pathWalkTS hst hP₀
      have hbar₁_eq : S₁.Ω.bar = S₀.Ω.interval s t ∪ V(P) := by
        rw [← hred₁.2.2.1]; exact splitCyclicPerm_bar S₀ hs₀ ht₀ hst hP₀ hP_bar₀
      have hbar₂_eq : S₂.Ω.bar = S₀.Ω.interval t s ∪ V(P) := by
        rw [← hred₂.2.2.1]; exact splitCyclicPerm_bar S₀ ht₀ hs₀ hst.symm hP₀.symm hP_bar₂₀
      have hP_val₁ : ∀ k (hk : k < m),
          upperDiscMap m (ν₁ (L_P[k]'hk)) = (pathX m k : ℂ) := by
        intro k hk
        have hvP : L_P[k]'hk ∈ V(P) := by
          rw [vertexSet_eq_support_pathWalkTS hP₀]; exact List.getElem_mem hk
        rw [hν₁_bar _ (hbar₁_eq ▸ Or.inr hvP)]
        exact upperDiscMap_exp_upperSplitAngle_of_mem_P hst hP₀ θ' hk
      have hP_val₂ : ∀ k (hk : k < m),
          lowerDiscMap m (ν₂ (L_P[k]'hk)) = (pathX m k : ℂ) := by
        intro k hk
        have hvP : L_P[k]'hk ∈ V(P) := by
          rw [vertexSet_eq_support_pathWalkTS hP₀]; exact List.getElem_mem hk
        rw [hν₂_bar _ (hbar₂_eq ▸ Or.inr hvP)]
        exact lowerDiscMap_exp_lowerSplitAngle_of_mem_P hst hP₀ θ' hk
      have hP_agree : ∀ v ∈ V(P), upperDiscMap m (ν₁ v) = lowerDiscMap m (ν₂ v) := by
        intro v hvP
        have hv_LP : v ∈ L_P := by
          change v ∈ {x | x ∈ (pathWalkTS hP₀).support}
          rwa [← vertexSet_eq_support_pathWalkTS hP₀]
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv_LP
        rw [hP_val₁ k hk, hP_val₂ k hk]
      obtain ⟨ν_mid, Γ_mid, hν_mid_1, hν_mid_2, hν_mid_inj, hU_mid_ball,
          hU_mid_cover, hν_mid_eq⟩ :=
        glue_drawings_along_path hP₀ hm hS₁_le_base hS₂_le_base hV_union_base hV_inter_P
          hE_union_base hE_disj_base hE_union_all hE_disj_all hEP_adj
          hν₁_inj hν₂_inj hU₁_ball hU₂_ball hν₁_eq hν₂_eq hP_val₁ hP_agree
      have hν_mid_s : ν_mid s = 1 := by
        have hpos : 0 < m := by omega
        have hs_LP : L_P[m - 1]'(by omega) = s := support_getElem_last (pathWalkTS hP₀)
        have hsP : s ∈ V(P) := hP₀.left_mem
        have hs₁ : s ∈ V(S₁.G) := (hV_inter_P ▸ inter_subset_left) hsP
        rw [hν_mid_1 s hs₁]
        change upperDiscMap m (ν₁ s) = 1
        rw [← hs_LP, hP_val₁ (m - 1) (by omega), pathX_pred hm]
        simp
      have hν_mid_t : ν_mid t = -1 := by
        have hpos : 0 < m := by omega
        have ht_LP : L_P[0]'hpos = t := support_getElem_zero (pathWalkTS hP₀) hpos
        have htP : t ∈ V(P) := hP₀.right_mem
        have ht₁ : t ∈ V(S₁.G) := (hV_inter_P ▸ inter_subset_left) htP
        rw [hν_mid_1 t ht₁]
        change upperDiscMap m (ν₁ t) = -1
        rw [← ht_LP, hP_val₁ 0 hpos, pathX_zero]
        simp
      have hν_mid_W1 : ∀ v ∈ S₀.Ω.interval s t,
          ν_mid v = (Circle.exp (2 * Real.pi + Real.pi * (θ' v - θ' s) / (θ' t - θ' s)) : ℂ) := by
        intro v hvW1
        have hv_bar₁ : v ∈ S₁.Ω.bar := hbar₁_eq ▸ Or.inl hvW1
        have hv₁ : v ∈ V(S₁.G) := S₁.bar_subset hv_bar₁
        have hv_not_P : v ∉ V(P) := fun hvP =>
          disjoint_left.mp hP_bar₀ ⟨hvP, hvW1.1.2⟩ hvW1.1.1
        have hv_LW1 : v ∈ S₀.Ω.intervalList hs₀ ht₀ :=
          (S₀.Ω.mem_intervalList_iff hs₀ ht₀ hst v).mpr hvW1
        obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hv_LW1
        obtain ⟨hb1, hb2⟩ := h_W1_bounds a ha
        rw [hν_mid_1 _ hv₁, hν₁_bar _ hv_bar₁]
        exact upperDiscMap_exp_upperSplitAngle_of_not_mem_P hP₀ hv_not_P hb1 hb2
      have hν_mid_W2 : ∀ v ∈ S₀.Ω.interval t s,
          ν_mid v = (Circle.exp (Real.pi + Real.pi * (θ' v - θ' t) / (θ' s + 2 * Real.pi - θ' t)) :
            ℂ) := by
        intro v hvW2
        have hv_bar₂ : v ∈ S₂.Ω.bar := hbar₂_eq ▸ Or.inl hvW2
        have hv₂ : v ∈ V(S₂.G) := S₂.bar_subset hv_bar₂
        have hv_not_P : v ∉ V(P) := fun hvP =>
          disjoint_left.mp hP_bar₂₀ ⟨hvP, hvW2.1.2⟩ hvW2.1.1
        have hv_LW2 : v ∈ S₀.Ω.intervalList ht₀ hs₀ :=
          (S₀.Ω.mem_intervalList_iff ht₀ hs₀ hst.symm v).mpr hvW2
        obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hv_LW2
        obtain ⟨hb1, hb2⟩ := h_W2_bounds b hb
        rw [hν_mid_2 _ hv₂, hν₂_bar _ hv_bar₂]
        exact lowerDiscMap_exp_lowerSplitAngle_of_not_mem_P hP₀ hv_not_P hb1 hb2
      have hU_mid_sph := glued_drawing_meets_sphere hred.2.2.1 hs₀ ht₀ hst hP₀
        hU₁_ball hU₂_ball hU₁_sph hU₂_sph hbar₁_eq hbar₂_eq hν_mid_eq hν_mid_s hν_mid_t
        (fun v hv => (hν_mid_W1 v hv).symm ▸ (Circle.exp _).2)
        (fun v hv => (hν_mid_W2 v hv).symm ▸ (Circle.exp _).2)
        hm hν_mid_1 hν_mid_2 hP_val₁ hP_val₂ hU_mid_cover
      let Φ := discAngleMap (θ' s) (θ' t)
      have hΦ_inj : Function.Injective Φ := injective_discAngleMap h_st h_span
      obtain ⟨Γ, hU_Γ, _, hν_Γ⟩ :=
        GraphDrawing.transport Γ_mid
          ((isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset Γ_mid.drawing.isClosed_U hU_mid_ball)
          hν_mid_eq (continuous_discAngleMap (θ' s) (θ' t)) hΦ_inj.injOn
      let ν (v : α) : ℂ := Φ (ν_mid v)
      refine ⟨ν, Γ, hΦ_inj.injOn.comp hν_mid_inj (mapsTo_univ _ _), ?_, ?_, ?_, hν_Γ⟩
      · intro v hv_bar
        have hvL : v ∈ L := by rwa [← hL.2.2.1] at hv_bar
        have hexp_θ' : (Circle.exp (θ' v) : ℂ) = (Circle.exp (θ v) : ℂ) :=
          congrArg Subtype.val (circle_exp_shiftedAngle L θ i₀ hvL)
        rw [← hexp_θ']
        have hv_bar₀ : v ∈ S₀.Ω.bar := hred.2.2.1.symm ▸ hv_bar
        by_cases hvs : v = s
        · subst hvs
          change discAngleMap (θ' v) (θ' t) (ν_mid v) = (Circle.exp (θ' v) : ℂ)
          rw [hν_mid_s, discAngleMap_one]
        · by_cases hvt : v = t
          · subst hvt
            change discAngleMap (θ' s) (θ' v) (ν_mid v) = (Circle.exp (θ' v) : ℂ)
            rw [hν_mid_t, discAngleMap_neg_one]
          · rcases S₀.Ω.mem_interval_or_interval_swap hs₀ ht₀ hv_bar₀ hst hvs hvt with hv1 | hv2
            · have hv_LW1 : v ∈ S₀.Ω.intervalList hs₀ ht₀ :=
                (S₀.Ω.mem_intervalList_iff hs₀ ht₀ hst v).mpr hv1
              obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hv_LW1
              obtain ⟨hb1, hb2⟩ := h_W1_bounds a ha
              change discAngleMap (θ' s) (θ' t) (ν_mid _) = _
              rw [hν_mid_W1 _ hv1]
              exact discAngleMap_upper_exp hb1 hb2
            · have hv_LW2 : v ∈ S₀.Ω.intervalList ht₀ hs₀ :=
                (S₀.Ω.mem_intervalList_iff ht₀ hs₀ hst.symm v).mpr hv2
              obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hv_LW2
              obtain ⟨hb1, hb2⟩ := h_W2_bounds b hb
              change discAngleMap (θ' s) (θ' t) (ν_mid _) = _
              rw [hν_mid_W2 _ hv2]
              exact discAngleMap_lower_exp hb1 hb2
      · rw [hU_Γ]
        rintro w ⟨z, hz, rfl⟩
        exact (discAngleMap_mem_closedBall_iff (θ' s) (θ' t) z).mpr (hU_mid_ball hz)
      · rw [hU_Γ]
        ext w
        simp only [mem_inter_iff, mem_image]
        constructor
        · rintro ⟨⟨z, hzU, rfl⟩, hwS⟩
          have hzS : z ∈ Metric.sphere (0 : ℂ) 1 :=
            (discAngleMap_mem_sphere_iff (θ' s) (θ' t) z).mp hwS
          have hz_in : z ∈ ν_mid '' S.Ω.bar := hU_mid_sph ▸ ⟨hzU, hzS⟩
          obtain ⟨v, hv_bar, rfl⟩ := hz_in
          exact ⟨v, hv_bar, rfl⟩
        · rintro ⟨v, hv_bar, rfl⟩
          have hz_in : ν_mid v ∈ Γ_mid.drawing.U ∩ Metric.sphere (0 : ℂ) 1 :=
            hU_mid_sph.symm ▸ ⟨v, hv_bar, rfl⟩
          exact ⟨⟨ν_mid v, hz_in.1, rfl⟩,
            (discAngleMap_mem_sphere_iff (θ' s) (θ' t) (ν_mid v)).mpr hz_in.2⟩
    · have hE₀_empty : E(S₀.G) = ∅ := Set.not_nonempty_iff_eq_empty.mp hE₀
      have hV_eq : V(S.G) = S.Ω.bar := by
        rw [← hred.2.1, ← hred.2.2.1]
        exact vertexSet_eq_bar_of_edgeSet_eq_empty S₀ hred.2.2.2.1 hE₀_empty
      have hloops : ∀ e x y, S.G.IsLink e x y → x = y := by
        intro e x y hlink
        rcases hred.2.2.2.2.2.2.2.2 e x y hlink with rfl | ⟨f, hf⟩
        · rfl
        · have hfE : f ∈ E(S₀.G) := hf.edge_mem
          rw [hE₀_empty] at hfE
          exact hfE.elim
      let ν (v : α) : ℂ := (Circle.exp (θ v) : ℂ)
      have hν_inj : InjOn ν V(S.G) := hV_eq ▸ injOn_circle_exp_of_isValidAngle hL hθ
      have hν_sph : ∀ v ∈ V(S.G), ν v ∈ Metric.sphere (0 : ℂ) 1 := fun v _ => (Circle.exp _).2
      obtain ⟨Γ, hU_ball, hU_sph, hν_eq⟩ :=
        exists_drawing_of_loops_only S.finite_V S.finite_E hloops hν_inj hν_sph
      exact ⟨ν, Γ, hν_inj, fun _ _ => rfl, hU_ball, hV_eq ▸ hU_sph, hν_eq⟩

theorem CyclicPerm.isOrbitList_mem_interval_of_lt {Ω : CyclicPerm α} {L : List α}
    (hL : Ω.IsOrbitList L) {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < L.length) :
    (L[j]'(Nat.lt_trans hjk hk)) ∈
      Ω.interval (L[i]'(Nat.lt_trans (Nat.lt_trans hij hjk) hk)) (L[k]'hk) := by
  have hi : i < L.length := Nat.lt_trans (Nat.lt_trans hij hjk) hk
  have hj : j < L.length := Nat.lt_trans hjk hk
  have hi_bar : L[i]'hi ∈ Ω.bar := hL.2.2.1 ▸ List.getElem_mem hi
  have hj_bar : L[j]'hj ∈ Ω.bar := hL.2.2.1 ▸ List.getElem_mem hj
  have hk_bar : L[k]'hk ∈ Ω.bar := hL.2.2.1 ▸ List.getElem_mem hk
  have hne_ik : L[i]'hi ≠ L[k]'hk := fun h => by
    have := (List.Nodup.getElem_inj_iff hL.1).mp h; omega
  have hne_ji : L[j]'hj ≠ L[i]'hi := fun h => by
    have := (List.Nodup.getElem_inj_iff hL.1).mp h; omega
  have hne_jk : L[j]'hj ≠ L[k]'hk := fun h => by
    have := (List.Nodup.getElem_inj_iff hL.1).mp h; omega
  rw [Ω.mem_interval_iff_firstHitIn hi_bar hk_bar hj_bar hne_ik hne_ji hne_jk]
  refine ⟨j - i, by omega, ?_, by simp, ?_⟩
  · rw [iterate_toFun_eq_getElem_of_next hL.2.2.2 hi (j - i)]
    congr 1; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro m hm1 hmj hmem
    have hm_lt : i + m < L.length := by omega
    have h_eq : (Ω.toFun^[m]) (L[i]'hi) = L[i + m]'hm_lt := by
      rw [iterate_toFun_eq_getElem_of_next hL.2.2.2 hi m]
      congr 1; exact Nat.mod_eq_of_lt hm_lt
    rw [h_eq] at hmem
    rcases hmem with h1 | h2 | h3
    · have := (List.Nodup.getElem_inj_iff hL.1).mp h1; omega
    · have := (List.Nodup.getElem_inj_iff hL.1).mp h2; omega
    · have := (List.Nodup.getElem_inj_iff hL.1).mp (mem_singleton_iff.mp h3); omega

/-- An orbit list has valid angles, spaced evenly around the circle. -/
theorem CyclicPerm.IsOrbitList.exists_isValidAngle {Ω : CyclicPerm α} {L : List α}
    (hL : Ω.IsOrbitList L) : ∃ θ : α → ℝ, IsValidAngle L θ := by
  classical
  have hpos : 0 < L.length := List.length_pos_of_ne_nil hL.2.1
  have hpos_real : (0 : ℝ) < (L.length : ℝ) := Nat.cast_pos.mpr hpos
  let θ (v : α) : ℝ :=
    if hv : v ∈ L then 2 * Real.pi * (CyclicPerm.indexOfMem L hv : ℝ) / (L.length : ℝ) else 0
  have hθ_get : ∀ i (hi : i < L.length),
      θ (L[i]'hi) = 2 * Real.pi * (i : ℝ) / (L.length : ℝ) := by
    intro i hi
    have hmem : L[i]'hi ∈ L := List.getElem_mem hi
    simp only [θ, hmem, ↓reduceDIte]
    rw [CyclicPerm.indexOfMem_getElem hL.1 hi]
  have hθ : IsValidAngle L θ := by
    refine ⟨?_, ?_⟩
    · intro i j hi hj hij
      rw [hθ_get i hi, hθ_get j hj]
      have hij_real : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
      gcongr
    · intro i hi
      have h0_eq : θ (L[0]'(Nat.zero_lt_of_lt hi)) = 0 := by
        rw [hθ_get 0 (Nat.zero_lt_of_lt hi)]
        simp
      rw [h0_eq, hθ_get i hi, zero_add]
      have hi_real : (i : ℝ) < (L.length : ℝ) := Nat.cast_lt.mpr hi
      calc
        2 * Real.pi * (i : ℝ) / (L.length : ℝ) < 2 * Real.pi * (L.length : ℝ) / (L.length : ℝ) := by
          gcongr
        _ = 2 * Real.pi := mul_div_cancel_right₀ _ (ne_of_gt hpos_real)
  exact ⟨θ, hθ⟩

/-- If angles increase along an orbit list of `Ω` and span less than one turn, then a clockwise
triple of `Ω` has increasing angles within one turn. -/
theorem exists_angles_of_isClockwise3 {Ω : CyclicPerm α} {L : List α}
    (hL : Ω.IsOrbitList L) {θ : α → ℝ} (hθ : IsValidAngle L θ) {X : Type*} {f : ℝ → X}
    (hf : ∀ t, f (t + 2 * Real.pi) = f t) {T : α → Set X} (hT : ∀ v ∈ Ω.bar, f (θ v) ∈ T v)
    {v₁ v₂ v₃ : α} (hcw : Ω.IsClockwise3 v₁ v₂ v₃) :
    ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
      f t₁ ∈ T v₁ ∧ f t₂ ∈ T v₂ ∧ f t₃ ∈ T v₃ := by
  obtain ⟨h12, h13, h23, hv₁, hv₂, hv₃, _⟩ := Ω.isClockwise3_iff.mp hcw
  have hv₁L : v₁ ∈ L := by rwa [← hL.2.2.1] at hv₁
  have hv₂L : v₂ ∈ L := by rwa [← hL.2.2.1] at hv₂
  have hv₃L : v₃ ∈ L := by rwa [← hL.2.2.1] at hv₃
  obtain ⟨i₁, hi₁, rfl⟩ := List.mem_iff_getElem.mp hv₁L
  obtain ⟨i₂, hi₂, rfl⟩ := List.mem_iff_getElem.mp hv₂L
  obtain ⟨i₃, hi₃, rfl⟩ := List.mem_iff_getElem.mp hv₃L
  have hne12 : i₁ ≠ i₂ := fun h => h12 (by subst h; rfl)
  have hne13 : i₁ ≠ i₃ := fun h => h13 (by subst h; rfl)
  have hne23 : i₂ ≠ i₃ := fun h => h23 (by subst h; rfl)
  have h_in' : L[i₂]'hi₂ ∈ Ω.interval (L[i₁]'hi₁) (L[i₃]'hi₃) :=
    ⟨⟨hv₂, by simp [h12.symm, h23]⟩, hcw⟩
  have hnot_132 : ¬ (i₁ < i₃ ∧ i₃ < i₂) := by
    rintro ⟨h_a, h_b⟩
    have h_in := Ω.isOrbitList_mem_interval_of_lt hL h_a h_b hi₂
    exact disjoint_left.mp (Ω.disjoint_interval_swap (L[i₁]'hi₁) (L[i₂]'hi₂))
      h_in (Ω.mem_interval_rotate_left h_in')
  have hnot_321 : ¬ (i₃ < i₂ ∧ i₂ < i₁) := by
    rintro ⟨h_a, h_b⟩
    have h_in := Ω.isOrbitList_mem_interval_of_lt hL h_a h_b hi₁
    exact disjoint_left.mp (Ω.disjoint_interval_swap (L[i₃]'hi₃) (L[i₁]'hi₁))
      h_in h_in'
  have hnot_213 : ¬ (i₂ < i₁ ∧ i₁ < i₃) := by
    rintro ⟨h_a, h_b⟩
    have h_in := Ω.isOrbitList_mem_interval_of_lt hL h_a h_b hi₃
    exact disjoint_left.mp (Ω.disjoint_interval_swap (L[i₂]'hi₂) (L[i₃]'hi₃))
      h_in (Ω.mem_interval_rotate_right h_in')
  have hcases : (i₁ < i₂ ∧ i₂ < i₃) ∨ (i₂ < i₃ ∧ i₃ < i₁) ∨ (i₃ < i₁ ∧ i₁ < i₂) := by
    omega
  have hθ_ge : ∀ i (hi : i < L.length), θ (L[0]'(by omega)) ≤ θ (L[i]'hi) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact le_rfl
    · exact le_of_lt (hθ.1 0 i (by omega) hi hpos)
  have hφ_mem : ∀ i (hi : i < L.length), f (θ (L[i]'hi)) ∈ T (L[i]'hi) := fun i hi =>
    hT _ (by rw [← hL.2.2.1]; exact List.getElem_mem hi)
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨θ (L[i₁]'hi₁), θ (L[i₂]'hi₂), θ (L[i₃]'hi₃),
      hθ.1 i₁ i₂ hi₁ hi₂ ha, hθ.1 i₂ i₃ hi₂ hi₃ hb, ?_,
      hφ_mem i₁ hi₁, hφ_mem i₂ hi₂, hφ_mem i₃ hi₃⟩
    linarith [hθ_ge i₁ hi₁, hθ.2 i₃ hi₃]
  · refine ⟨θ (L[i₁]'hi₁), θ (L[i₂]'hi₂) + 2 * Real.pi, θ (L[i₃]'hi₃) + 2 * Real.pi,
      by linarith [hθ.2 i₁ hi₁, hθ_ge i₂ hi₂],
      by linarith [hθ.1 i₂ i₃ hi₂ hi₃ ha],
      by linarith [hθ.1 i₃ i₁ hi₃ hi₁ hb],
      hφ_mem i₁ hi₁, ?_, ?_⟩
    · rw [hf]; exact hφ_mem i₂ hi₂
    · rw [hf]; exact hφ_mem i₃ hi₃
  · refine ⟨θ (L[i₁]'hi₁), θ (L[i₂]'hi₂), θ (L[i₃]'hi₃) + 2 * Real.pi,
      hθ.1 i₁ i₂ hi₁ hi₂ hb,
      by linarith [hθ.2 i₂ hi₂, hθ_ge i₃ hi₃],
      by linarith [hθ.1 i₃ i₁ hi₃ hi₁ ha],
      hφ_mem i₁ hi₁, hφ_mem i₂ hi₂, ?_⟩
    rw [hf]; exact hφ_mem i₃ hi₃

/-- Transport a complex unit-disc drawing `(ν, Γ)` with valid boundary angles to `ClosedUnitDisc`,
proving `S.IsRuralSociety`. -/
theorem isRuralSociety_of_complex_disc_drawing (S : Society α β)
    {L : List α} (hL : S.Ω.IsOrbitList L) {θ : α → ℝ} (hθ : IsValidAngle L θ)
    {ν : α → ℂ} {Γ : GraphDrawing S.G ℂ}
    (hν_inj : InjOn ν V(S.G))
    (hν_bar : ∀ v ∈ S.Ω.bar, ν v = (Circle.exp (θ v) : ℂ))
    (hU_ball : Γ.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1)
    (hU_sph : Γ.drawing.U ∩ Metric.sphere (0 : ℂ) 1 = ν '' S.Ω.bar)
    (hν_eq : ∀ v : V(S.G), (Γ.iso.vertexEquiv v).1 = ν v.1) :
    S.IsRuralSociety := by
  let Ω₀ : CyclicPerm α := {
    bar := ∅
    toFun := id
    finite_bar := finite_empty
    bijOn := bijOn_empty id
    single_orbit := fun _ hx => hx.elim
  }
  refine ⟨Ω₀, empty_subset _, rfl, ?_⟩
  obtain ⟨Γ_E, hU_E, _, hν_E⟩ :=
    GraphDrawing.transport Γ
      ((isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset Γ.drawing.isClosed_U hU_ball)
      hν_eq complexPlane.continuous complexPlane.injective.injOn
  have hdisc : IsClosedDisc ClosedUnitDisc := ⟨Homeomorph.refl ClosedUnitDisc⟩
  have hvertex_eq : ∀ v (hv : v ∈ V(S.G)),
      graphDrawingVertexSet Γ_E v = {complexPlane (ν v)} := by
    intro v hv
    ext x
    simp only [graphDrawingVertexSet, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun ⟨hv', hx⟩ => hx.symm.trans (hν_E ⟨v, hv'⟩),
      fun hx => ⟨hv, (hν_E ⟨v, hv⟩).trans hx.symm⟩⟩
  have hbd_iff : ∀ v ∈ V(S.G),
      (graphDrawingVertexSet Γ_E v ⊆ subBd ClosedUnitDisc ↔ v ∈ S.Ω.bar) := by
    intro v hv
    rw [hvertex_eq v hv, singleton_subset_iff, subBd_closedUnitDisc_eq_unitCircle,
      UnitCircle, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map,
      ← mem_sphere_zero_iff_norm]
    have hvU : ν v ∈ Γ.drawing.U := by
      rw [← hν_eq ⟨v, hv⟩]
      exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hv⟩).2
    constructor
    · intro hvS
      have h_in : ν v ∈ ν '' S.Ω.bar := hU_sph ▸ ⟨hvU, hvS⟩
      obtain ⟨w, hw_bar, hw_eq⟩ := h_in
      have heq : w = v := hν_inj (S.bar_subset hw_bar) hv hw_eq
      exact heq ▸ hw_bar
    · intro hv_bar
      have h_in : ν v ∈ Γ.drawing.U ∩ Metric.sphere (0 : ℂ) 1 :=
        hU_sph.symm ▸ ⟨v, hv_bar, rfl⟩
      exact h_in.2
  refine ⟨Γ_E, ClosedUnitDisc, ∅, hdisc, empty_subset _, ?_, hbd_iff, ?_,
    ⟨circleHomeomorphSubBdClosedUnitDisc, isClockwiseDiscHomeo_closedUnitDisc, ?_⟩, Or.inl ⟨rfl,
      rfl⟩⟩
  · rw [interior_empty, sdiff_empty, hU_E]
    rintro x ⟨z, hz, rfl⟩
    have hz_ball := hU_ball hz
    rw [mem_closedBall_zero_iff] at hz_ball
    change complexPlane z ∈ Metric.closedBall (0 : EuclideanPlane) 1
    rwa [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
  · intro v hv
    rw [hvertex_eq v hv, singleton_subset_iff]
    simp [subBd, Ω₀]
  · refine ⟨fun v hv_bar => (hbd_iff v (S.bar_subset hv_bar)).mpr hv_bar, ?_⟩
    intro v₁ v₂ v₃ hcw
    refine exists_angles_of_isClockwise3 hL hθ (T := graphDrawingVertexSet Γ_E)
      (f := fun t => (circleHomeomorphSubBdClosedUnitDisc (Circle.exp t)).1)
      (fun t => by simp only [circle_exp_add_two_pi]) (fun v h_bar => ?_) hcw
    rw [hvertex_eq _ (S.bar_subset h_bar), mem_singleton_iff, hν_bar _ h_bar]
    rfl

open Classical in
/-- **Graph Minors IX, (2.4)** (pages 45–46):
"Let $(G, \Omega)$ be a 3-connected society with no cross or tripod. Then $(G, \Omega)$ is rural."
-/
theorem theorem_2_4_proof (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃) :
    S.IsRuralSociety := by
  obtain ⟨S₀, hred⟩ := exists_isSimpleReduction S hconn hnocross hnotripod
  rcases S.Ω.bar.eq_empty_or_nonempty with hbar_empty | ⟨w₀, hw₀⟩
  · have hbar₀_empty : S₀.Ω.bar = ∅ := by rw [hred.2.2.1, hbar_empty]
    have hV₀_empty : V(S₀.G) = ∅ := by
      by_contra hne
      obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hne
      let G₁ := S₀.G.induce ∅
      let G₂ := S₀.G
      have hsep : IsGraphSeparation S₀.G G₁ G₂ := by
        refine ⟨S₀.G.induce_le (empty_subset _), le_rfl, ?_, ?_, ?_⟩
        · simp [G₁, G₂]
        · have hE₁ : E(G₁) = ∅ := by
            ext e
            simp only [G₁, edgeSet_induce, mem_ofPred_eq, mem_empty_iff_false, iff_false]
            rintro ⟨x, _, _, hx, _⟩
            exact hx
          rw [hE₁, empty_union]
        · have hE₁ : E(G₁) = ∅ := by
            ext e
            simp only [G₁, edgeSet_induce, mem_ofPred_eq, mem_empty_iff_false, iff_false]
            rintro ⟨x, _, _, hx, _⟩
            exact hx
          rw [hE₁]
          exact disjoint_bot_left
      have hsep_S : S₀.IsKSeparation 0 G₂ G₁ := by
        refine ⟨⟨IsGraphSeparation.symm hsep, ?_⟩, ?_, ?_⟩
        · rw [hbar₀_empty]; exact empty_subset _
        · simp [G₁, G₂]
        · intro heq
          have hv₁ : v ∈ V(G₁) := heq.symm ▸ hv
          exact hv₁
      exact hred.2.2.2.1 0 (by omega) G₂ G₁ hsep_S
    have hV_empty : V(S.G) = ∅ := hred.2.1.symm.trans hV₀_empty
    have hE_empty : E(S.G) = ∅ := by
      ext e
      simp only [mem_empty_iff_false, iff_false]
      intro he
      obtain ⟨u, _, hlink⟩ := exists_isLink_of_mem_edgeSet he
      have hu : u ∈ V(S.G) := hlink.left_mem
      rw [hV_empty] at hu
      exact hu
    let Ω₀ : CyclicPerm α := {
      bar := ∅
      toFun := id
      finite_bar := finite_empty
      bijOn := bijOn_empty id
      single_orbit := fun _ hx => hx.elim
    }
    refine ⟨Ω₀, empty_subset _, rfl, ?_⟩
    have hinj₀ : InjOn (fun _ : α => (0 : EuclideanPlane)) V(S.G) := by
      rw [hV_empty]; exact injOn_empty _
    obtain ⟨Γ, hU_eq, _⟩ := GraphDrawing.of_edgeless S.finite_V hE_empty hinj₀
    have hU_empty : Γ.drawing.U = ∅ := by rw [hU_eq, hV_empty, image_empty]
    have hdisc : IsClosedDisc ClosedUnitDisc := ⟨Homeomorph.refl ClosedUnitDisc⟩
    refine ⟨Γ, ClosedUnitDisc, ∅, hdisc, empty_subset _, ?_, ?_, ?_,
      ⟨circleHomeomorphSubBdClosedUnitDisc, isClockwiseDiscHomeo_closedUnitDisc, ?_⟩, Or.inl ⟨rfl,
        rfl⟩⟩
    · rw [hU_empty]; exact empty_subset _
    · intro v hv; rw [hV_empty] at hv; exact hv.elim
    · intro v hv; rw [hV_empty] at hv; exact hv.elim
    · refine ⟨fun v hv => (hbar_empty ▸ hv).elim, fun v₁ _ _ hcw => ?_⟩
      have hv₁ : v₁ ∈ S.Ω.bar := (S.Ω.isClockwise3_iff.mp hcw).2.2.2.1
      rw [hbar_empty] at hv₁
      exact hv₁.elim
  · obtain ⟨L, hL⟩ := S.Ω.exists_isOrbitList_of_mem hw₀
    obtain ⟨θ, hθ⟩ := hL.exists_isValidAngle
    obtain ⟨ν, Γ, hν_inj, hν_bar, hU_ball, hU_sph, hν_eq⟩ :=
      exists_disc_drawing_of_isSimpleReduction E(S₀.G).ncard S₀ S hred rfl L hL θ hθ
    exact isRuralSociety_of_complex_disc_drawing S hL hθ hν_inj hν_bar hU_ball hU_sph hν_eq

/-- Dot-notation alias for `theorem_2_4_proof`. -/
theorem Society.theorem_2_4_proof (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃) :
    S.IsRuralSociety :=
  GraphMinor.GM09.theorem_2_4_proof S hconn hnocross hnotripod

end

end GraphMinor.GM09
