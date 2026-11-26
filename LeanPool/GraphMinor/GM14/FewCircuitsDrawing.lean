/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.FewCircuits
public import LeanPool.GraphMinor.GM09.RuralExtend
public import LeanPool.GraphMinor.GM09.Section2e
public import LeanPool.GraphMinor.GM09.DiscDrawing
public import LeanPool.GraphMinor.GM09.Section6b

/-!
# Drawing a graph with at most one circuit

"every graph with at most one circuit can be drawn in the plane with all its vertices incident with
the infinite region" (Graph Minors XIV, proof of (8.4), page 42). We put all the vertices on the
boundary of a disc, and add them in the order given by `isGraphCircuit_self_or_exists_leaf`. A
new vertex goes next to the end of its edge, so the edge fits along the boundary.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-- The order of a list, read by positions. -/
theorem isClockwise3_ofNodupList_iff (L : List α) (hnd : L.Nodup) (hne : L ≠ [])
    {i j k : ℕ} (hi : i < L.length) (hj : j < L.length) (hk : k < L.length)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (CyclicPerm.ofNodupList L hnd hne).IsClockwise3 L[i] L[j] L[k] ↔
      (i < k ∧ i < j ∧ j < k) ∨ (k < i ∧ (j < k ∨ i < j)) := by
  have hmem : L[j] ∈ (CyclicPerm.ofNodupList L hnd hne).interval L[i] L[k] ↔
      (CyclicPerm.ofNodupList L hnd hne).IsClockwise3 L[i] L[j] L[k] := by
    refine ⟨fun h => h.2, fun h => ⟨⟨List.getElem_mem hj, ?_⟩, h⟩⟩
    rintro (h' | h')
    · exact hij (nodup_getElem_inj hnd hj hi h').symm
    · exact hjk (nodup_getElem_inj hnd hj hk h')
  rw [← hmem]
  rcases lt_or_gt_of_ne hik with h | h
  · rw [CyclicPerm.ofNodupList_mem_interval_iff L hnd hne h hk hj]
    omega
  · rw [CyclicPerm.ofNodupList_mem_interval_swap_iff L hnd hne h hi hj]
    omega

/-- Inserting a new element in a list keeps the order of the other elements. -/
theorem isClockwise3_of_insert (L₁ L₂ : List α) (r : α) (hnd : (L₁ ++ r :: L₂).Nodup)
    (hne : L₁ ++ r :: L₂ ≠ []) (hnd' : (L₁ ++ L₂).Nodup) (hne' : L₁ ++ L₂ ≠ []) :
    ∀ v₁ v₂ v₃ : α, (CyclicPerm.ofNodupList _ hnd hne).IsClockwise3 v₁ v₂ v₃ → v₁ ≠ r → v₂ ≠ r →
      v₃ ≠ r → (CyclicPerm.ofNodupList _ hnd' hne').IsClockwise3 v₁ v₂ v₃ := by
  intro v₁ v₂ v₃ h h₁ h₂ h₃
  set A := L₁ ++ L₂ with hA
  set B := L₁ ++ r :: L₂ with hB
  let f : ℕ → ℕ := fun j => if j < L₁.length then j else j + 1
  have hlen : B.length = A.length + 1 := by simp [hA, hB]; omega
  have hf : ∀ j (hj : j < A.length), ∃ h' : f j < B.length, B[f j] = A[j] := by
    intro j hj
    have hlt : f j < B.length := by
      simp only [f]
      split_ifs <;> omega
    refine ⟨hlt, ?_⟩
    by_cases hjL : j < L₁.length
    · simp only [f, hjL, ite_true, hA, hB]
      rw [List.getElem_append_left hjL, List.getElem_append_left hjL]
    · have hfj : f j = j + 1 := by simp [f, hjL]
      simp only [hfj, hA, hB]
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have : j + 1 - L₁.length = (j - L₁.length) + 1 := by omega
      simp only [this, List.getElem_cons_succ]
  have hm := (CyclicPerm.ofNodupList _ hnd hne).isClockwise3_iff.mp h
  have hidx : ∀ v, v ∈ B → v ≠ r → ∃ (j : ℕ) (hj : j < A.length), A[j] = v := by
    intro v hv hvr
    have hvA : v ∈ A := by
      simp only [hB, List.mem_append, List.mem_cons] at hv
      simp only [hA, List.mem_append]
      tauto
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvA
    exact ⟨j, hj, rfl⟩
  obtain ⟨i, hi, rfl⟩ := hidx v₁ hm.2.2.2.1 h₁
  obtain ⟨j, hj, rfl⟩ := hidx v₂ hm.2.2.2.2.1 h₂
  obtain ⟨k, hk, rfl⟩ := hidx v₃ hm.2.2.2.2.2.1 h₃
  have hij : i ≠ j := fun h' => hm.1 (by subst h'; rfl)
  have hik : i ≠ k := fun h' => hm.2.1 (by subst h'; rfl)
  have hjk : j ≠ k := fun h' => hm.2.2.1 (by subst h'; rfl)
  obtain ⟨hi', hfi⟩ := hf i hi
  obtain ⟨hj', hfj⟩ := hf j hj
  obtain ⟨hk', hfk⟩ := hf k hk
  have hmono : ∀ {a b : ℕ}, a < b → f a < f b := by
    intro a b hab
    simp only [f]
    split_ifs <;> omega
  have hinj : ∀ {a b : ℕ}, a ≠ b → f a ≠ f b := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h' | h'
    · exact (hmono h').ne
    · exact (hmono h').ne'
  rw [← hfi, ← hfj, ← hfk, isClockwise3_ofNodupList_iff B hnd hne hi' hj' hk' (hinj hij) (hinj hik)
    (hinj hjk)] at h
  rw [isClockwise3_ofNodupList_iff A hnd' hne' hi hj hk hij hik hjk]
  have hmono' : ∀ {a b : ℕ}, f a < f b → a < b := by
    intro a b hab
    by_contra hn
    rcases eq_or_lt_of_le (not_lt.mp hn) with h' | h'
    · subst h'
      exact lt_irrefl _ hab
    · exact lt_asymm hab (hmono h')
  rcases h with ⟨a, b, c⟩ | ⟨a, b | b⟩
  · exact Or.inl ⟨hmono' a, hmono' b, hmono' c⟩
  · exact Or.inr ⟨hmono' a, Or.inl (hmono' b)⟩
  · exact Or.inr ⟨hmono' a, Or.inr (hmono' b)⟩

/-- Consecutive elements of a list have nothing between them. -/
theorem interval_succ_eq_empty (L : List α) (hnd : L.Nodup) (hne : L ≠ []) {i : ℕ}
    (hi : i + 1 < L.length) :
    (CyclicPerm.ofNodupList L hnd hne).interval L[i] L[i + 1] = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have hxL : x ∈ L := hx.1.1
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hxL
  have := (CyclicPerm.ofNodupList_mem_interval_iff L hnd hne (Nat.lt_succ_self i) hi hj).mp hx
  omega

/-- The last and first elements of a list have nothing between them. -/
theorem interval_last_eq_empty (L : List α) (hnd : L.Nodup) (hne : L ≠ []) (h1 : 0 < L.length)
    (h2 : 1 < L.length) :
    (CyclicPerm.ofNodupList L hnd hne).interval (L[L.length - 1]'(by omega)) L[0] = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have hxL : x ∈ L := hx.1.1
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hxL
  have := (CyclicPerm.ofNodupList_mem_interval_swap_iff L hnd hne (i := 0) (k := L.length - 1)
    (by omega) (by omega) hj).mp hx
  omega

/-- `K` has a rural drawing with all its vertices on the boundary of the disc, in the order of the
list `L`. -/
def BoundaryRural (K : Graph α β) (L : List α) : Prop :=
  {x | x ∈ L} = V(K) ∧ ∃ (hnd : L.Nodup) (hne : L ≠ []) (N : Neighborhood α β),
    N.G = K ∧ N.Ω = CyclicPerm.ofNodupList L hnd hne ∧ N.Ω₀.bar = ∅ ∧ N.IsRural

/-- A single vertex. -/
theorem boundaryRural_singleton {K : Graph α β} {v : α} (hV : V(K) = {v}) (hE : E(K) = ∅) :
    BoundaryRural K [v] := by
  have hnd : [v].Nodup := List.nodup_singleton v
  have hne : [v] ≠ [] := by simp
  have hbar : {x | x ∈ [v]} = V(K) := by rw [hV]; ext x; simp
  let S : Society α β :=
    { G := K
      Ω := CyclicPerm.ofNodupList [v] hnd hne
      finite_V := hV ▸ finite_singleton v
      finite_E := hE ▸ finite_empty
      bar_subset := by rw [CyclicPerm.ofNodupList_bar, hbar] }
  have hVS : V(S.G) = {v} := hV
  let ν : α → ℂ := fun _ => 1
  have hinj : InjOn ν V(S.G) := by
    rw [hVS]
    exact injOn_singleton _ _
  obtain ⟨Γ, hU, hν⟩ := GraphDrawing.of_edgeless S.finite_V hE hinj
  have hθ : IsValidAngle [v] (fun _ => (0 : ℝ)) := by
    refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
    · simp only [List.length_singleton] at hi hj
      omega
    · have := Real.pi_pos
      linarith
  have hbarS : S.Ω.bar = {v} := by
    change {x | x ∈ [v]} = {v}
    ext x
    simp
  have hL : S.Ω.IsOrbitList [v] := CyclicPerm.isOrbitList_ofNodupList _ hnd hne
  have hball : Γ.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [hU]
    rintro _ ⟨x, -, rfl⟩
    simp [ν]
  have hsph : Γ.drawing.U ∩ Metric.sphere (0 : ℂ) 1 = ν '' S.Ω.bar := by
    rw [hU, hbarS, hVS]
    ext x
    simp [ν]
  have hr := isRuralSociety_of_complex_disc_drawing S hL hθ hinj
    (fun w _ => by simp [ν]) hball hsph hν
  obtain ⟨Ω₀, h₀, hΩ₀, hr⟩ := hr
  exact ⟨hbar, hnd, hne, _, rfl, rfl, hΩ₀, hr⟩

/-- Adding a vertex with no edges. -/
theorem BoundaryRural.add_vertex {K K' : Graph α β} {L₁ L₂ : List α} {r : α}
    (h : BoundaryRural K' (L₁ ++ L₂)) (hVf : V(K).Finite) (hEf : E(K).Finite) (hle : K' ≤ K)
    (hr : r ∉ V(K')) (hV : V(K) = insert r V(K')) (hE : E(K) = E(K')) :
    BoundaryRural K (L₁ ++ r :: L₂) := by
  obtain ⟨hL, hnd, hne, N, hG, hΩ, hΩ₀, hrural⟩ := h
  subst hG
  have hrL : r ∉ L₁ ++ L₂ := fun h' => hr (hL ▸ h')
  have hnd' : (L₁ ++ r :: L₂).Nodup := by
    have hp : (L₁ ++ r :: L₂).Perm (r :: (L₁ ++ L₂)) := List.perm_middle
    exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hrL, hnd⟩)
  have hne' : L₁ ++ r :: L₂ ≠ [] := by simp
  have hL' : {x | x ∈ L₁ ++ r :: L₂} = V(K) := by
    rw [hV, ← hL]
    ext x
    simp only [mem_ofPred_eq, List.mem_append, List.mem_cons, mem_insert_iff]
    tauto
  let N' : Neighborhood α β :=
    { G := K
      Ω := CyclicPerm.ofNodupList _ hnd' hne'
      Ω₀ := N.Ω₀
      finite_V := hVf
      finite_E := hEf
      bar_subset := by rw [CyclicPerm.ofNodupList_bar, hL']
      bar₀_subset := hle.vertexSet_mono.trans' N.bar₀_subset |> fun h => h }
  refine ⟨hL', hnd', hne', N', rfl, rfl, hΩ₀, ?_⟩
  refine hrural.add_boundary_vertex rfl hle hr hV hE ?_ ?_ ?_
  · change r ∈ {x | x ∈ L₁ ++ r :: L₂}
    simp
  · rw [hΩ]
    change {x | x ∈ L₁ ++ L₂} = {x | x ∈ L₁ ++ r :: L₂} \ {r}
    ext x
    simp only [mem_ofPred_eq, List.mem_append, List.mem_cons, mem_sdiff, mem_singleton_iff]
    constructor
    · intro hx
      refine ⟨by tauto, ?_⟩
      rintro rfl
      exact hrL (by simpa using hx)
    · tauto
  · rw [hΩ]
    exact isClockwise3_of_insert L₁ L₂ r hnd' hne' hnd hne

/-- Adding an edge along the boundary. -/
theorem BoundaryRural.add_edge {K K' : Graph α β} {L : List α} {e : β} {u w : α}
    (h : BoundaryRural K' L) (hVf : V(K).Finite) (hEf : E(K).Finite) (hle : K' ≤ K)
    (hV : V(K) = V(K')) (hE : E(K) = insert e E(K')) (he : e ∉ E(K'))
    (hl : K.IsLink e u w) (huw : u ≠ w)
    (hgap : ∀ (hnd : L.Nodup) (hne : L ≠ []),
      (CyclicPerm.ofNodupList L hnd hne).interval u w = ∅) :
    BoundaryRural K L := by
  obtain ⟨hL, hnd, hne, N, hG, hΩ, hΩ₀, hrural⟩ := h
  subst hG
  have hL' : {x | x ∈ L} = V(K) := hV ▸ hL
  let N' : Neighborhood α β :=
    { G := K
      Ω := N.Ω
      Ω₀ := N.Ω₀
      finite_V := hVf
      finite_E := hEf
      bar_subset := hle.vertexSet_mono.trans' N.bar_subset |> fun h => h
      bar₀_subset := hle.vertexSet_mono.trans' N.bar₀_subset |> fun h => h }
  have hbar : N.Ω.bar = V(N.G) := by rw [hΩ, ← hL]; rfl
  refine ⟨hL', hnd, hne, N', rfl, hΩ, hΩ₀, ?_⟩
  refine hrural.add_boundary_edge rfl rfl hle hV hE he hl ?_ ?_ huw ?_
  · rw [hbar, ← hV]
    exact hl.left_mem
  · rw [hbar, ← hV]
    exact hl.right_mem
  · rw [hΩ]
    exact hgap hnd hne

/-- Adding a loop. -/
theorem BoundaryRural.add_loop {K K' : Graph α β} {L : List α} {e : β} {u : α}
    (h : BoundaryRural K' L) (hVf : V(K).Finite) (hEf : E(K).Finite) (hle : K' ≤ K)
    (hV : V(K) = V(K')) (hE : E(K) = insert e E(K')) (he : e ∉ E(K'))
    (hl : K.IsLink e u u) : BoundaryRural K L := by
  obtain ⟨hL, hnd, hne, N, hG, hΩ, hΩ₀, hrural⟩ := h
  subst hG
  have hL' : {x | x ∈ L} = V(K) := hV ▸ hL
  let N' : Neighborhood α β :=
    { G := K
      Ω := N.Ω
      Ω₀ := N.Ω₀
      finite_V := hVf
      finite_E := hEf
      bar_subset := hle.vertexSet_mono.trans' N.bar_subset |> fun h => h
      bar₀_subset := hle.vertexSet_mono.trans' N.bar₀_subset |> fun h => h }
  refine ⟨hL', hnd, hne, N', rfl, hΩ, hΩ₀, ?_⟩
  refine hrural.add_loop rfl rfl hle hV hE he hl (hV ▸ hl.left_mem) ?_
  rw [hΩ₀]
  exact fun h => h

/-- Two subgraphs of `G`, compared by their vertices and edges. -/
theorem le_of_subset_of_subset {G A B : Graph α β} (hA : A ≤ G) (hB : B ≤ G)
    (hV : V(A) ⊆ V(B)) (hE : E(A) ⊆ E(B)) : A ≤ B := by
  rw [(Compatible.of_le_le hA hB).le_iff]
  exact ⟨hV, hE⟩

/-- A path, in its own order. -/
theorem boundaryRural_path {K : Graph α β} {x y : α} (W : GraphWalk K x y) (hW : W.IsSimple) :
    BoundaryRural (walkSubgraph W) W.support := by
  induction W with
  | nil hv =>
    refine boundaryRural_singleton ?_ ?_
    · rw [vertexSet_walkSubgraph]
      ext a
      simp [GraphWalk.support]
    · rw [edgeSet_walkSubgraph]
      ext a
      simp [GraphWalk.edges]
  | @cons x z y f hl rest ih =>
    have hs : (x :: rest.support).Nodup := hW
    obtain ⟨hx, hrest⟩ := List.nodup_cons.mp hs
    have hih := ih hrest
    have hle₀ := walkSubgraph_le rest
    let W₂ : GraphWalk K x y := GraphWalk.cons hl rest
    have hV₂ : V(walkSubgraph W₂) = insert x V(walkSubgraph rest) := by
      rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph]
      ext a
      simp [W₂, GraphWalk.support]
    have hE₂ : E(walkSubgraph W₂) = insert f E(walkSubgraph rest) := by
      rw [edgeSet_walkSubgraph, edgeSet_walkSubgraph]
      ext a
      simp [W₂, GraphWalk.edges]
    have hxV : x ∉ V(walkSubgraph rest) := by
      rw [vertexSet_walkSubgraph]
      exact hx
    have hxK : x ∈ V(K) := hl.left_mem
    let K₁ := addVertexTo K (walkSubgraph rest) x
    have hK₁K : K₁ ≤ K := addVertexTo_le hle₀ hxK
    have hK₁₂ : K₁ ≤ walkSubgraph W₂ := by
      refine le_of_subset_of_subset hK₁K (walkSubgraph_le W₂) ?_ ?_
      · rw [vertexSet_addVertexTo, hV₂]
      · rw [edgeSet_addVertexTo hle₀, hE₂]
        exact subset_insert _ _
    have hfin : V(walkSubgraph W₂).Finite := by
      rw [vertexSet_walkSubgraph]
      exact List.finite_toSet _
    have hfinE : E(walkSubgraph W₂).Finite := by
      rw [edgeSet_walkSubgraph]
      exact List.finite_toSet _
    have h₁ : BoundaryRural K₁ ([] ++ x :: rest.support) := by
      refine BoundaryRural.add_vertex (L₁ := []) (L₂ := rest.support) hih
        (hfin.subset hK₁₂.vertexSet_mono) (hfinE.subset hK₁₂.edgeSet_mono)
        (le_addVertexTo hle₀) hxV vertexSet_addVertexTo (edgeSet_addVertexTo hle₀)
    have hxz : x ≠ z := fun h => hx (h ▸ rest.start_mem_support)
    have hfE : f ∉ E(K₁) := by
      rw [edgeSet_addVertexTo hle₀, edgeSet_walkSubgraph]
      intro hf
      have hf' : f ∈ E(walkSubgraph rest) := by rw [edgeSet_walkSubgraph]; exact hf
      obtain ⟨p, q, hpq⟩ := (walkSubgraph rest).exists_isLink_of_mem_edgeSet hf'
      have hpq' := hpq.mono hle₀
      rcases hpq'.eq_and_eq_or_eq_and_eq hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hxV hpq.left_mem
      · exact hxV hpq.right_mem
    have hlink : (walkSubgraph W₂).IsLink f x z :=
      (walkSubgraph_isLink W₂).mpr ⟨by simp [W₂, GraphWalk.edges], hl⟩
    refine BoundaryRural.add_edge h₁ hfin hfinE hK₁₂ ?_ ?_ hfE hlink hxz ?_
    · rw [vertexSet_addVertexTo, hV₂]
    · rw [edgeSet_addVertexTo hle₀, hE₂]
    · intro hnd hne
      have hlen : 1 < ([] ++ x :: rest.support).length := by
        have : 0 < rest.support.length := List.length_pos_of_mem rest.start_mem_support
        simp only [List.nil_append, List.length_cons]
        omega
      have := interval_succ_eq_empty _ hnd hne (i := 0) hlen
      simpa [support_getElem_zero] using this

/-- A circuit, in its own order. -/
theorem exists_boundaryRural_of_isCircuit {K : Graph α β} (hC : IsGraphCircuit K K) :
    ∃ L, BoundaryRural K L := by
  obtain ⟨-, u, W, ⟨hnd, hed⟩, hpos, hVK, hEK⟩ := hC
  cases W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
  | @cons u x _ f hl W' =>
    have hs : W'.support.Nodup := by simpa [GraphWalk.support] using hnd
    have hf : f ∉ W'.edges := (List.nodup_cons.mp (by simpa [GraphWalk.edges] using hed)).1
    refine ⟨W'.support, ?_⟩
    have hP := boundaryRural_path W' hs
    have hle := walkSubgraph_le W'
    have huW : u ∈ W'.support := W'.end_mem_support
    have hV' : V(K) = V(walkSubgraph W') := by
      rw [vertexSet_walkSubgraph, hVK]
      ext a
      simp only [mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact huW
        · exact h
      · exact Or.inr
    have hE' : E(K) = insert f E(walkSubgraph W') := by
      rw [edgeSet_walkSubgraph, hEK]
      ext a
      simp [GraphWalk.edges]
    have hf' : f ∉ E(walkSubgraph W') := by
      rw [edgeSet_walkSubgraph]
      exact hf
    have hVf : V(K).Finite := by rw [hVK]; exact List.finite_toSet _
    have hEf : E(K).Finite := by rw [hEK]; exact List.finite_toSet _
    by_cases hxu : x = u
    · subst hxu
      exact hP.add_loop hVf hEf hle hV' hE' hf' hl
    · refine hP.add_edge hVf hEf hle hV' hE' hf' hl (Ne.symm hxu) ?_
      intro hnd' hne'
      have hlen : 1 < W'.support.length := by
        by_contra hn
        have h1 : W'.support.length = 1 := by
          have : 0 < W'.support.length := List.length_pos_of_mem huW
          omega
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
        have hx' : x ∈ W'.support := W'.start_mem_support
        rw [ha] at hx' huW
        simp only [List.mem_singleton] at hx' huW
        exact hxu (hx'.trans huW.symm)
      have := interval_last_eq_empty _ hnd' hne' (by omega) hlen
      simpa [support_getElem_zero, support_getElem_last] using this

/-- The circuits of a subgraph are circuits of the graph. -/
theorem ncard_circuits_le_of_le {K K' : Graph α β} (hV : V(K).Finite) (hE : E(K).Finite)
    (hle : K' ≤ K) (hc : {C | IsGraphCircuit K C}.ncard ≤ 1) :
    {C | IsGraphCircuit K' C}.ncard ≤ 1 := by
  have hfin : {C | IsGraphCircuit K C}.Finite :=
    (finite_subgraphs hV hE).subset fun _ h => h.1
  have hsub : {C | IsGraphCircuit K' C} ⊆ {C | IsGraphCircuit K C} := fun C hC =>
    (⟨hC.1.trans hle, hC.2⟩ : IsGraphCircuit K C)
  exact (ncard_le_ncard hsub hfin).trans hc

/-- A finite graph with a vertex and at most one circuit has a rural drawing with all its vertices
on the boundary. -/
theorem exists_boundaryRural {K : Graph α β} (hV : V(K).Finite) (hE : E(K).Finite)
    (hc : {C | IsGraphCircuit K C}.ncard ≤ 1) (hne : V(K).Nonempty) :
    ∃ L, BoundaryRural K L := by
  classical
  induction hn : V(K).ncard using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    have hdel : ∀ r ∈ V(K), V(deleteVertices K {r}).Nonempty →
        ∃ L, BoundaryRural (deleteVertices K {r}) L := by
      intro r hr hne'
      have hle := deleteVertices_le K {r}
      refine ih _ ?_ (hV.subset hle.vertexSet_mono) (hE.subset hle.edgeSet_mono)
        (ncard_circuits_le_of_le hV hE hle hc) hne' rfl
      rw [← hn, vertexSet_deleteVertices]
      exact ncard_sdiff_singleton_lt_of_mem hr hV
    rcases isGraphCircuit_self_or_exists_leaf hV hE hc hne with hC | ⟨r, hr, hiso | ⟨e, u, hur, hl,
      huniq⟩⟩
    · exact exists_boundaryRural_of_isCircuit hC
    · have hle := deleteVertices_le K {r}
      have hEe : E(K) = E(deleteVertices K {r}) := by
        refine subset_antisymm (fun f hf => ?_) hle.edgeSet_mono
        obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet hf
        have hx : x ≠ r := by rintro rfl; exact hiso f y hxy
        have hy : y ≠ r := by rintro rfl; exact hiso f x hxy.symm
        exact ((deleteVertices_isLink K {r}).mpr ⟨hxy, hx, hy⟩).edge_mem
      by_cases hne' : V(deleteVertices K {r}).Nonempty
      · obtain ⟨L, hL⟩ := hdel r hr hne'
        refine ⟨r :: L, ?_⟩
        refine BoundaryRural.add_vertex (L₁ := []) (L₂ := L) hL hV hE hle (fun h => h.2 rfl) ?_ hEe
        rw [vertexSet_deleteVertices, insert_sdiff_singleton, insert_eq_of_mem hr]
      · have hVr : V(K) = {r} := by
          refine subset_antisymm (fun x hx => ?_) (singleton_subset_iff.mpr hr)
          by_contra hxr
          exact hne' ⟨x, hx, hxr⟩
        have hE0 : E(K) = ∅ := by
          refine eq_empty_of_forall_notMem fun f hf => ?_
          obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet hf
          have hx : x = r := by
            have := hxy.left_mem
            rwa [hVr] at this
          exact hiso f y (hx ▸ hxy)
        exact ⟨[r], boundaryRural_singleton hVr hE0⟩
    · have hle := deleteVertices_le K {r}
      have huV : u ∈ V(deleteVertices K {r}) := ⟨hl.right_mem, hur⟩
      obtain ⟨L, hL⟩ := hdel r hr ⟨u, huV⟩
      have huL : u ∈ L := by
        have : u ∈ {x | x ∈ L} := hL.1 ▸ huV
        exact this
      obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem huL
      let K₀ := addVertexTo K (deleteVertices K {r}) r
      have hK₀ : K₀ ≤ K := addVertexTo_le hle hr
      have hEdel : E(K₀) = E(deleteVertices K {r}) := edgeSet_addVertexTo hle
      have h₀ : BoundaryRural K₀ (L₁ ++ u :: r :: L₂) := by
        have := BoundaryRural.add_vertex (K := K₀) (L₁ := L₁ ++ [u]) (L₂ := L₂) (r := r)
          (by simpa using hL) (hV.subset hK₀.vertexSet_mono) (hE.subset hK₀.edgeSet_mono)
          (le_addVertexTo hle) (fun h => h.2 rfl) vertexSet_addVertexTo hEdel
        simpa using this
      have hVeq : V(K) = V(K₀) := by
        rw [vertexSet_addVertexTo, vertexSet_deleteVertices, insert_sdiff_singleton,
          insert_eq_of_mem hr]
      have heK₀ : e ∉ E(K₀) := by
        rw [hEdel]
        intro he
        obtain ⟨x, y, hxy⟩ := (deleteVertices K {r}).exists_isLink_of_mem_edgeSet he
        obtain ⟨-, hx, hy⟩ := (deleteVertices_isLink K {r}).mp hxy
        rcases hxy.mono hle |>.eq_and_eq_or_eq_and_eq hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact hx rfl
        · exact hy rfl
      have hEins : E(K) = insert e E(K₀) := by
        rw [hEdel]
        refine subset_antisymm (fun f hf => ?_) (insert_subset hl.edge_mem hle.edgeSet_mono)
        obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet hf
        by_cases hx : x = r
        · subst hx
          exact Or.inl (huniq f y hxy)
        by_cases hy : y = r
        · subst hy
          exact Or.inl (huniq f x hxy.symm)
        exact Or.inr ((deleteVertices_isLink K {r}).mpr ⟨hxy, hx, hy⟩).edge_mem
      refine ⟨_, h₀.add_edge hV hE hK₀ hVeq hEins heK₀ hl.symm hur ?_⟩
      intro hnd hne₀
      have hlen : L₁.length + 1 < (L₁ ++ u :: r :: L₂).length := by simp
      have := interval_succ_eq_empty _ hnd hne₀ hlen
      simpa using this

/-- **Graph Minors XIV, proof of (8.4), page 42.** "every graph with at most one circuit can be
drawn in the plane with all its vertices
incident with the infinite region" Here the vertices lie
on the boundary of a closed disc that contains the drawing. -/
theorem exists_boundary_drawing {K : Graph α β} (hV : V(K).Finite) (hE : E(K).Finite)
    (hc : {C | IsGraphCircuit K C}.ncard ≤ 1) :
    ∃ (Γ : GraphDrawing K EuclideanPlane) (Δ : Set EuclideanPlane), IsClosedDisc Δ ∧
      Γ.drawing.U ⊆ Δ ∧ Γ.drawing.V ⊆ subBd Δ := by
  by_cases hne : V(K).Nonempty
  · obtain ⟨L, hL, hnd, hne', N, rfl, hΩ, -, Γ, Δ, Δ₀, hΔ, -, hU, hbd, -⟩ :=
      exists_boundaryRural hV hE hc hne
    refine ⟨Γ, Δ, hΔ, fun x hx => (hU hx).1, ?_⟩
    intro x hx
    let v := Γ.iso.vertexEquiv.symm ⟨x, hx⟩
    have hv : v.1 ∈ N.Ω.bar := by
      rw [hΩ]
      change v.1 ∈ {x | x ∈ L}
      rw [hL]
      exact v.2
    have hsub := (hbd v.1 v.2).mpr hv
    apply hsub
    refine ⟨v.2, ?_⟩
    simp [v]
  · have hVe : V(K) = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hEe : E(K) = ∅ := by
      refine eq_empty_of_forall_notMem fun f hf => ?_
      obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet hf
      exact hne ⟨x, hxy.left_mem⟩
    obtain ⟨Γ, hU, hν⟩ := GraphDrawing.of_edgeless (S := EuclideanPlane) hV hEe
      (ν := fun _ => 0) (by rw [hVe]; exact injOn_empty _)
    refine ⟨Γ, ClosedUnitDisc, ⟨Homeomorph.refl ClosedUnitDisc⟩, ?_, ?_⟩
    · rw [hU, hVe]
      simp
    · have : Γ.drawing.V ⊆ Γ.drawing.U := Γ.drawing.V_subset_U
      rw [hU, hVe, image_empty] at this
      exact this.trans (empty_subset _)

end GraphMinor.GM14
