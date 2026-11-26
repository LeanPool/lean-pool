/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Hypergraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Menger's theorem for finite simple graphs

This file proves Menger's theorem for finite simple graphs
(`GraphMinor.Menger.exists_disjointPaths`). The induction follows F. Göring,
[*A proof of Menger's theorem by contraction*](https://doi.org/10.7151/dmgt.1161),
Discuss. Math. Graph Theory 22 (2002), 111–112. It tries contracting an edge and uses deletion
when the contraction admits a separator below the size bound.
-/

public section

namespace GraphMinor.Menger

open SimpleGraph

variable {V : Type*}

/-- `S` is an `A`-`B` separator in `K`: every path in `K` from `A` to `B` meets `S`. -/
private def IsSeparator (K : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ P : PathFromTo K A B, ∃ x ∈ P.walk.support, x ∈ S

private lemma IsSeparator.exists_mem_support_of_walk {K : SimpleGraph V} {A B S : Set V}
    (hS : IsSeparator K A B S) {u v : V} (hu : u ∈ A) (hv : v ∈ B) (w : K.Walk u v) :
    ∃ x ∈ w.support, x ∈ S := by
  classical
  obtain ⟨x, hx, hxS⟩ := hS ⟨u, v, w.bypass, w.bypass_isPath, hu, hv⟩
  exact ⟨x, w.support_bypass_subset_support hx, hxS⟩

private lemma hasDisjointPaths_of_edgeSet_eq_empty [Finite V] (K : SimpleGraph V) (A B : Set V)
    (hE : K.edgeSet = ∅) (k : ℕ) (h : ∀ S : Set V, IsSeparator K A B S → k ≤ S.ncard) :
    HasDisjointPaths K A B k := by
  have hsep : IsSeparator K A B (A ∩ B) := by
    intro P
    rcases P with ⟨u, v, w, _, hu, hv⟩
    cases w with
    | nil =>
      exact ⟨u, Walk.start_mem_support _, hu, hv⟩
    | cons hadj _ =>
      have he : s(u, _) ∈ K.edgeSet := K.mem_edgeSet.mpr hadj
      rw [hE] at he
      exact False.elim he
  have hk : k ≤ (A ∩ B).ncard := h (A ∩ B) hsep
  let _ : Fintype ↥(A ∩ B) := Fintype.ofFinite ↥(A ∩ B)
  have hcard : k ≤ Fintype.card ↥(A ∩ B) := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  let e := (Fintype.equivFin ↥(A ∩ B)).symm
  let v : Fin k → ↥(A ∩ B) := fun i ↦ e (Fin.castLE hcard i)
  refine ⟨fun i ↦ ⟨(v i).1, (v i).1, .nil, .nil, (v i).2.1, (v i).2.2⟩, ?_⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  simp only [Set.mem_ofPred_eq, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hzi hzj
  apply hij
  have hv_eq : v i = v j := Subtype.ext (hzi.symm.trans hzj)
  exact (Fin.castLE_injective hcard) (e.injective hv_eq)

/-- The graph obtained from `K` by contracting the edge `x y` into `x` and isolating `y`. -/
private def contractEdge (K : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ≠ y ∧ v ≠ y ∧
    (K.Adj u v ∨ (u = x ∧ K.Adj y v) ∨ (v = x ∧ K.Adj u y))
  symm := ⟨fun _ _ ⟨huv, huy, hvy, h⟩ ↦ ⟨huv.symm, hvy, huy,
    h.elim (fun h ↦ Or.inl h.symm)
      (fun h ↦ h.elim (fun ⟨rfl, h⟩ ↦ Or.inr (Or.inr ⟨rfl, h.symm⟩))
        (fun ⟨rfl, h⟩ ↦ Or.inr (Or.inl ⟨rfl, h.symm⟩)))⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- The image of a vertex set `A` when contracting `y` into `x`. -/
private def contractSet (x y : V) (A : Set V) : Set V :=
  {u | u ≠ y ∧ (u ∈ A ∨ (u = x ∧ y ∈ A))}

private lemma not_mem_support_of_contractEdge {K : SimpleGraph V} {x y u v : V}
    (w : (contractEdge K x y).Walk u v) (hu : u ≠ y) : y ∉ w.support := by
  induction w with
  | nil =>
    simp [hu.symm]
  | cons hadj rest ih =>
    rw [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hu.symm, ih hadj.2.2.1⟩

private lemma ncard_edgeSet_contractEdge_lt [Finite V] {K : SimpleGraph V} {x y : V}
    (hxy : K.Adj x y) : (contractEdge K x y).edgeSet.ncard < K.edgeSet.ncard := by
  classical
  let f : V → V := fun u ↦ if u = y then x else u
  have hsub : (contractEdge K x y).edgeSet ⊆ Sym2.map f '' (K.edgeSet \ {s(x, y)}) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet] at he
      rcases he with ⟨huv, huy, hvy, h⟩
      rcases h with huv' | ⟨rfl, hyv⟩ | ⟨rfl, huy'⟩
      · refine ⟨s(u, v), ⟨K.mem_edgeSet.mpr huv', ?_⟩, ?_⟩
        · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          rintro (⟨_, rfl⟩ | ⟨rfl, _⟩) <;> contradiction
        · simp [f, huy, hvy]
      · refine ⟨s(y, v), ⟨K.mem_edgeSet.mpr hyv, ?_⟩, ?_⟩
        · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          rintro (⟨rfl, rfl⟩ | ⟨_, rfl⟩)
          · exact hxy.ne rfl
          · exact huv rfl
        · simp [f, hvy]
      · refine ⟨s(u, y), ⟨K.mem_edgeSet.mpr huy', ?_⟩, ?_⟩
        · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          rintro (⟨rfl, _⟩ | ⟨rfl, rfl⟩)
          · exact huv rfl
          · exact hxy.ne rfl
        · simp [f, huy]
  have h1 : (contractEdge K x y).edgeSet.ncard ≤
      (Sym2.map f '' (K.edgeSet \ {s(x, y)})).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (Sym2.map f '' (K.edgeSet \ {s(x, y)})).ncard ≤ (K.edgeSet \ {s(x, y)}).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have h3 : (K.edgeSet \ {s(x, y)}).ncard + 1 = K.edgeSet.ncard :=
    Set.ncard_sdiff_singleton_add_one (K.mem_edgeSet.mpr hxy) (Set.toFinite _)
  omega

private lemma exists_liftWalk {K : SimpleGraph V} {x y : V} (hxy : K.Adj x y) {u v : V}
    (w : (contractEdge K x y).Walk u v) :
    ∃ w' : K.Walk u v, ∀ z ∈ w'.support, z ∈ w.support ∨ (z = y ∧ x ∈ w.support) := by
  induction w with
  | nil =>
    exact ⟨.nil, fun z hz ↦ Or.inl hz⟩
  | @cons u u' v hadj rest ih =>
    obtain ⟨w', hw'⟩ := ih
    rcases hadj.2.2.2 with huu' | ⟨rfl, hyu'⟩ | ⟨rfl, huy⟩
    · refine ⟨.cons huu' w', fun z hz ↦ ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl (Walk.start_mem_support _)
      · rcases hw' z hz with hz' | ⟨rfl, hx⟩
        · exact Or.inl (List.mem_cons_of_mem _ hz')
        · exact Or.inr ⟨rfl, List.mem_cons_of_mem _ hx⟩
    · refine ⟨.cons hxy (.cons hyu' w'), fun z hz ↦ ?_⟩
      rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact Or.inl (Walk.start_mem_support _)
      · exact Or.inr ⟨rfl, Walk.start_mem_support _⟩
      · rcases hw' z hz with hz' | ⟨rfl, _⟩
        · exact Or.inl (List.mem_cons_of_mem _ hz')
        · exact Or.inr ⟨rfl, Walk.start_mem_support _⟩
    · refine ⟨.cons huy (.cons hxy.symm w'), fun z hz ↦ ?_⟩
      rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hz
      have hxin : u' ∈ (Walk.cons hadj rest).support :=
        List.mem_cons_of_mem _ (Walk.start_mem_support _)
      rcases hz with rfl | rfl | hz
      · exact Or.inl (Walk.start_mem_support _)
      · exact Or.inr ⟨rfl, hxin⟩
      · rcases hw' z hz with hz' | ⟨rfl, _⟩
        · exact Or.inl (List.mem_cons_of_mem _ hz')
        · exact Or.inr ⟨rfl, hxin⟩

private lemma exists_liftStart {K : SimpleGraph V} {x y : V} (hxy : K.Adj x y) {A : Set V}
    {u : V} (hu : u ∈ contractSet x y A) :
    ∃ u₀ ∈ A, ∃ w : K.Walk u₀ u, ∀ z ∈ w.support, z = u ∨ (z = y ∧ u = x) := by
  rcases hu.2 with huA | ⟨rfl, hyA⟩
  · refine ⟨u, huA, .nil, fun z hz ↦ ?_⟩
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    exact Or.inl hz
  · refine ⟨y, hyA, hxy.symm.toWalk, fun z hz ↦ ?_⟩
    simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl

private lemma exists_liftEnd {K : SimpleGraph V} {x y : V} (hxy : K.Adj x y) {B : Set V}
    {v : V} (hv : v ∈ contractSet x y B) :
    ∃ v₀ ∈ B, ∃ w : K.Walk v v₀, ∀ z ∈ w.support, z = v ∨ (z = y ∧ v = x) := by
  rcases hv.2 with hvB | ⟨rfl, hyB⟩
  · refine ⟨v, hvB, .nil, fun z hz ↦ ?_⟩
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    exact Or.inl hz
  · refine ⟨y, hyB, hxy.toWalk, fun z hz ↦ ?_⟩
    simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, rfl⟩

private lemma hasDisjointPaths_of_contractEdge {K : SimpleGraph V} {x y : V} (hxy : K.Adj x y)
    {A B : Set V} {k : ℕ}
    (h : HasDisjointPaths (contractEdge K x y) (contractSet x y A) (contractSet x y B) k) :
    HasDisjointPaths K A B k := by
  classical
  obtain ⟨P, hP⟩ := h
  have hlift : ∀ i : Fin k, ∃ Q : PathFromTo K A B,
      ∀ z ∈ Q.walk.support, z ∈ (P i).walk.support ∨ (z = y ∧ x ∈ (P i).walk.support) := by
    intro i
    obtain ⟨u₀, hu₀, w₁, hw₁⟩ := exists_liftStart hxy (P i).first_mem
    obtain ⟨w₂, hw₂⟩ := exists_liftWalk hxy (P i).walk
    obtain ⟨v₀, hv₀, w₃, hw₃⟩ := exists_liftEnd hxy (P i).last_mem
    let w := (w₁.append w₂).append w₃
    refine ⟨⟨u₀, v₀, w.bypass, w.bypass_isPath, hu₀, hv₀⟩, fun z hz ↦ ?_⟩
    have hzw := w.support_bypass_subset_support hz
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hzw
    rcases hzw with (hz₁ | hz₂) | hz₃
    · rcases hw₁ z hz₁ with rfl | ⟨rfl, hux⟩
      · exact Or.inl (Walk.start_mem_support _)
      · exact Or.inr ⟨rfl, Eq.mp (congrArg (· ∈ (P i).walk.support) hux) (Walk.start_mem_support _)⟩
    · exact hw₂ z hz₂
    · rcases hw₃ z hz₃ with rfl | ⟨rfl, hvx⟩
      · exact Or.inl (Walk.end_mem_support _)
      · exact Or.inr ⟨rfl, Eq.mp (congrArg (· ∈ (P i).walk.support) hvx) (Walk.end_mem_support _)⟩
  choose Q hQ using hlift
  refine ⟨Q, fun i j hij ↦ Set.disjoint_left.mpr fun z hzi hzj ↦ ?_⟩
  have hyi : y ∉ (P i).walk.support :=
    not_mem_support_of_contractEdge (P i).walk (P i).first_mem.1
  have hyj : y ∉ (P j).walk.support :=
    not_mem_support_of_contractEdge (P j).walk (P j).first_mem.1
  rcases hQ i z hzi with hzi' | ⟨rfl, hxi⟩ <;> rcases hQ j z hzj with hzj' | ⟨hzy, hxj⟩
  · exact Set.disjoint_left.mp (hP hij) hzi' hzj'
  · exact hyi (hzy ▸ hzi')
  · exact hyj hzj'
  · exact Set.disjoint_left.mp (hP hij) hxi hxj

private lemma exists_contractWalk {K : SimpleGraph V} {x y : V} (hxy : K.Adj x y)
    [DecidableEq V] {u v : V} (w : K.Walk u v) :
    let f : V → V := fun z ↦ if z = y then x else z
    ∃ w' : (contractEdge K x y).Walk (f u) (f v),
      ∀ z' ∈ w'.support, ∃ z ∈ w.support, f z = z' := by
  intro f
  induction w with
  | nil =>
    refine ⟨.nil, fun z' hz' ↦ ?_⟩
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz'
    exact ⟨_, Walk.start_mem_support _, hz'.symm⟩
  | @cons u u' v hadj rest ih =>
    obtain ⟨w', hw'⟩ := ih
    by_cases hfu : f u = f u'
    · refine ⟨w'.copy hfu.symm rfl, fun z' hz' ↦ ?_⟩
      rw [Walk.support_copy] at hz'
      obtain ⟨z, hz, rfl⟩ := hw' z' hz'
      exact ⟨z, List.mem_cons_of_mem _ hz, rfl⟩
    · have hadj' : (contractEdge K x y).Adj (f u) (f u') := by
        refine ⟨hfu, ?_, ?_, ?_⟩
        · dsimp [f]; split_ifs with h <;> [exact hxy.ne; exact h]
        · dsimp [f]; split_ifs with h <;> [exact hxy.ne; exact h]
        · by_cases hu : u = y <;> by_cases hu' : u' = y
          · exact False.elim (hfu (by simp [f, hu, hu']))
          · subst hu
            exact Or.inr (Or.inl ⟨by simp [f], by simpa [f, hu'] using hadj⟩)
          · subst hu'
            exact Or.inr (Or.inr ⟨by simp [f], by simpa [f, hu] using hadj⟩)
          · exact Or.inl (by simpa [f, hu, hu'] using hadj)
      refine ⟨.cons hadj' w', fun z' hz' ↦ ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hz'
      rcases hz' with rfl | hz'
      · exact ⟨u, Walk.start_mem_support _, rfl⟩
      · obtain ⟨z, hz, rfl⟩ := hw' z' hz'
        exact ⟨z, List.mem_cons_of_mem _ hz, rfl⟩

private lemma exists_separator_of_not_contractEdge [Finite V] {K : SimpleGraph V} {x y : V}
    (hxy : K.Adj x y) {A B : Set V} {k : ℕ}
    (h : ∀ S : Set V, IsSeparator K A B S → k ≤ S.ncard)
    (hnot : ¬ ∀ S' : Set V,
      IsSeparator (contractEdge K x y) (contractSet x y A) (contractSet x y B) S' → k ≤ S'.ncard) :
    ∃ S : Set V, x ∈ S ∧ y ∈ S ∧ IsSeparator K A B S ∧ S.ncard = k := by
  classical
  push Not at hnot
  obtain ⟨S₀, hS₀_sep, hS₀_lt⟩ := hnot
  let S' : Set V := S₀ \ {y}
  have hS'_sep : IsSeparator (contractEdge K x y) (contractSet x y A) (contractSet x y B) S' := by
    intro P
    obtain ⟨z, hz, hzS₀⟩ := hS₀_sep P
    have hzy : z ≠ y := fun h ↦
      not_mem_support_of_contractEdge P.walk P.first_mem.1 (h ▸ hz)
    exact ⟨z, hz, hzS₀, hzy⟩
  have hS'_lt : S'.ncard < k :=
    lt_of_le_of_lt (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)) hS₀_lt
  let f : V → V := fun z ↦ if z = y then x else z
  have hf_mem : ∀ P : PathFromTo K A B, ∃ z ∈ P.walk.support, f z ∈ S' := by
    intro P
    have hu : f P.first ∈ contractSet x y A := by
      refine ⟨?_, ?_⟩
      · dsimp [f]; split_ifs with h <;> [exact hxy.ne; exact h]
      · dsimp [f]
        split_ifs with h
        · subst h; exact Or.inr ⟨rfl, P.first_mem⟩
        · exact Or.inl P.first_mem
    have hv : f P.last ∈ contractSet x y B := by
      refine ⟨?_, ?_⟩
      · dsimp [f]; split_ifs with h <;> [exact hxy.ne; exact h]
      · dsimp [f]
        split_ifs with h
        · subst h; exact Or.inr ⟨rfl, P.last_mem⟩
        · exact Or.inl P.last_mem
    obtain ⟨w', hw'⟩ := exists_contractWalk hxy P.walk
    obtain ⟨z', hz', hz'S'⟩ := hS'_sep.exists_mem_support_of_walk hu hv w'
    obtain ⟨z, hz, rfl⟩ := hw' z' hz'
    exact ⟨z, hz, hz'S'⟩
  have hxS' : x ∈ S' := by
    by_contra hx
    have hsep' : IsSeparator K A B S' := by
      intro P
      obtain ⟨z, hz, hfz⟩ := hf_mem P
      have hzy : z ≠ y := by
        intro hzy
        have : f z = x := by simp [f, hzy]
        exact hx (this ▸ hfz)
      have : f z = z := by simp [f, hzy]
      exact ⟨z, hz, this ▸ hfz⟩
    have := h S' hsep'
    omega
  let S : Set V := insert y S'
  have hS_sep : IsSeparator K A B S := by
    intro P
    obtain ⟨z, hz, hfz⟩ := hf_mem P
    by_cases hzy : z = y
    · exact ⟨z, hz, Or.inl hzy⟩
    · have : f z = z := by simp [f, hzy]
      exact ⟨z, hz, Or.inr (this ▸ hfz)⟩
  have hkS : k ≤ S.ncard := h S hS_sep
  have hSy : y ∉ S' := fun hy ↦ hy.2 rfl
  have hS_card_eq : S.ncard = S'.ncard + 1 := Set.ncard_insert_of_notMem hSy (Set.toFinite _)
  exact ⟨S, Or.inr hxS', Or.inl rfl, hS_sep, by omega⟩

private lemma exists_prefix_walk {K : SimpleGraph V} {S : Set V} {u v : V}
    (w : K.Walk u v) (hw : ∃ z ∈ w.support, z ∈ S) :
    ∃ z ∈ S, ∃ q : K.Walk u z,
      (∀ a ∈ q.support, a ∈ w.support) ∧ (∀ a ∈ q.support, a ∈ S → a = z) := by
  induction w with
  | nil =>
    obtain ⟨z, hz, hzS⟩ := hw
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    subst hz
    refine ⟨z, hzS, .nil, fun a ha ↦ ha, fun a ha _ ↦ ?_⟩
    simpa [Walk.support_nil] using ha
  | @cons u u' v hadj rest ih =>
    by_cases huS : u ∈ S
    · refine ⟨u, huS, .nil, fun a ha ↦ ?_, fun a ha _ ↦ ?_⟩
      · simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha
        exact Walk.start_mem_support _
      · simpa [Walk.support_nil] using ha
    · have hrest : ∃ z ∈ rest.support, z ∈ S := by
        obtain ⟨z, hz, hzS⟩ := hw
        rw [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact absurd hzS huS
        · exact ⟨z, hz, hzS⟩
      obtain ⟨z, hzS, q, hq_sub, hq_only⟩ := ih hrest
      refine ⟨z, hzS, .cons hadj q, ?_, ?_⟩
      · intro a ha
        rw [Walk.support_cons, List.mem_cons] at ha ⊢
        exact ha.imp_right (hq_sub a)
      · intro a ha haS
        rw [Walk.support_cons, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact absurd haS huS
        · exact hq_only a ha haS

private lemma not_mem_edges_of_only_end_in_S {K : SimpleGraph V} {S : Set V} {x y : V}
    (hxy : K.Adj x y) (hxS : x ∈ S) (hyS : y ∈ S) {u z : V} (q : K.Walk u z)
    (hq : ∀ a ∈ q.support, a ∈ S → a = z) : s(x, y) ∉ q.edges := by
  intro he
  have hx_mem : x ∈ q.support := q.fst_mem_support_of_mem_edges he
  have hy_mem : y ∈ q.support := q.snd_mem_support_of_mem_edges he
  have hxz : x = z := hq x hx_mem hxS
  have hyz : y = z := hq y hy_mem hyS
  exact hxy.ne (hxz.trans hyz.symm)

private lemma isSeparator_of_deleteEdges_left {K : SimpleGraph V} {x y : V} (hxy : K.Adj x y)
    {A B S T : Set V} (hxS : x ∈ S) (hyS : y ∈ S) (hS : IsSeparator K A B S)
    (hT : IsSeparator (K.deleteEdges {s(x, y)}) A S T) : IsSeparator K A B T := by
  intro P
  obtain ⟨z, hzS, q, hq_sub, hq_only⟩ := exists_prefix_walk P.walk (hS P)
  have hne : s(x, y) ∉ q.edges := not_mem_edges_of_only_end_in_S hxy hxS hyS q hq_only
  let q' := q.toDeleteEdge s(x, y) hne
  obtain ⟨t, ht, htT⟩ := hT.exists_mem_support_of_walk P.first_mem hzS q'
  rw [Walk.support_transfer] at ht
  exact ⟨t, hq_sub t ht, htT⟩

private lemma isSeparator_of_deleteEdges_right {K : SimpleGraph V} {x y : V} (hxy : K.Adj x y)
    {A B S T : Set V} (hxS : x ∈ S) (hyS : y ∈ S) (hS : IsSeparator K A B S)
    (hT : IsSeparator (K.deleteEdges {s(x, y)}) S B T) : IsSeparator K A B T := by
  intro P
  have hrev_S : ∃ z ∈ P.walk.reverse.support, z ∈ S := by
    obtain ⟨z, hz, hzS⟩ := hS P
    exact ⟨z, Walk.support_reverse P.walk ▸ List.mem_reverse.mpr hz, hzS⟩
  obtain ⟨z, hzS, q, hq_sub, hq_only⟩ := exists_prefix_walk P.walk.reverse hrev_S
  have hne : s(x, y) ∉ q.reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse]
    exact not_mem_edges_of_only_end_in_S hxy hxS hyS q hq_only
  let q' := q.reverse.toDeleteEdge s(x, y) hne
  obtain ⟨t, ht, htT⟩ := hT.exists_mem_support_of_walk hzS P.last_mem q'
  rw [Walk.support_transfer, Walk.support_reverse, List.mem_reverse] at ht
  have ht_rev := hq_sub t ht
  rw [Walk.support_reverse, List.mem_reverse] at ht_rev
  exact ⟨t, ht_rev, htT⟩

private lemma hasDisjointPaths_trans_of_separator [Finite V] {K : SimpleGraph V}
    {A B S : Set V} {k : ℕ} (hS_sep : IsSeparator K A B S) (hS_card : S.ncard = k)
    (hAS : HasDisjointPaths K A S k) (hSB : HasDisjointPaths K S B k) :
    HasDisjointPaths K A B k := by
  classical
  obtain ⟨P, hP⟩ := hAS
  obtain ⟨Q₀, hQ₀⟩ := hSB
  have hcard_S : Nat.card ↥S = k := by rw [Nat.card_coe_set_eq, hS_card]
  let p : Fin k → ↥S := fun i ↦ ⟨(P i).last, (P i).last_mem⟩
  have hp_inj : Function.Injective p := by
    intro i j hij
    by_contra hne
    have hlast : (P i).last = (P j).last := congrArg Subtype.val hij
    have h1 : (P i).last ∈ (P i).walk.support := Walk.end_mem_support _
    have h2 : (P i).last ∈ (P j).walk.support := by
      rw [hlast]
      exact Walk.end_mem_support _
    exact Set.disjoint_left.mp (hP hne) h1 h2
  have hp_bij : Function.Bijective p :=
    (Nat.bijective_iff_injective_and_card p).mpr ⟨hp_inj, by rw [Nat.card_fin, hcard_S]⟩
  let q₀ : Fin k → ↥S := fun j ↦ ⟨(Q₀ j).first, (Q₀ j).first_mem⟩
  have hq₀_inj : Function.Injective q₀ := by
    intro i j hij
    by_contra hne
    have hfirst : (Q₀ i).first = (Q₀ j).first := congrArg Subtype.val hij
    have h1 : (Q₀ i).first ∈ (Q₀ i).walk.support := Walk.start_mem_support _
    have h2 : (Q₀ i).first ∈ (Q₀ j).walk.support := by
      rw [hfirst]
      exact Walk.start_mem_support _
    exact Set.disjoint_left.mp (hQ₀ hne) h1 h2
  have hq₀_bij : Function.Bijective q₀ :=
    (Nat.bijective_iff_injective_and_card q₀).mpr ⟨hq₀_inj, by rw [Nat.card_fin, hcard_S]⟩
  let σ : Fin k ≃ Fin k := (Equiv.ofBijective p hp_bij).trans (Equiv.ofBijective q₀ hq₀_bij).symm
  let Q : Fin k → PathFromTo K S B := fun i ↦ Q₀ (σ i)
  have hQ : Pairwise fun i j ↦
      Disjoint {x | x ∈ (Q i).walk.support} {x | x ∈ (Q j).walk.support} :=
    fun i j hij ↦ hQ₀ (σ.injective.ne hij)
  have hPQ_eq : ∀ i : Fin k, (Q i).first = (P i).last := by
    intro i
    have h1 : q₀ (σ i) = p i :=
      (Equiv.ofBijective q₀ hq₀_bij).apply_symm_apply (p i)
    exact congrArg Subtype.val h1
  have hP_only : ∀ (i : Fin k) {z : V}, z ∈ (P i).walk.support → z ∈ S → z = (P i).last := by
    intro i z hz hzS
    obtain ⟨j, hj⟩ := hp_bij.surjective ⟨z, hzS⟩
    have hzj : z = (P j).last := (congrArg Subtype.val hj).symm
    have h_eq : i = j := by
      by_contra hne
      have h2 : z ∈ (P j).walk.support := by
        rw [hzj]
        exact Walk.end_mem_support _
      exact Set.disjoint_left.mp (hP hne) hz h2
    subst h_eq
    exact hzj
  have hQ_only : ∀ (i : Fin k) {z : V}, z ∈ (Q i).walk.support → z ∈ S → z = (P i).last := by
    intro i z hz hzS
    obtain ⟨j, hj⟩ := hp_bij.surjective ⟨z, hzS⟩
    have hzj : z = (P j).last := (congrArg Subtype.val hj).symm
    have h_eq : i = j := by
      by_contra hne
      have h2 : z ∈ (Q j).walk.support := by
        rw [hzj, ← hPQ_eq j]
        exact Walk.start_mem_support _
      exact Set.disjoint_left.mp (hQ hne) hz h2
    subst h_eq
    exact hzj
  have h_inter_in_S : ∀ (i j : Fin k) {z : V},
      z ∈ (P i).walk.support → z ∈ (Q j).walk.support → z ∈ S := by
    intro i j z hzP hzQ
    by_contra hzS
    have hneP : (P i).last ≠ z := fun h ↦ hzS (h ▸ (P i).last_mem)
    have hneQ : (Q j).first ≠ z := fun h ↦ hzS (h ▸ (Q j).first_mem)
    have hzQ_rev : z ∈ (Q j).walk.reverse.support :=
      Walk.support_reverse (Q j).walk ▸ List.mem_reverse.mpr hzQ
    let w₁ := (P i).walk.takeUntil z hzP
    let w₂ := ((Q j).walk.reverse.takeUntil z hzQ_rev).reverse
    have hw₁_not : (P i).last ∉ w₁.support :=
      Walk.endpoint_notMem_support_takeUntil (P i).isPath hzP hneP
    have hw₂_not : (Q j).first ∉ w₂.support := by
      rw [Walk.support_reverse, List.mem_reverse]
      exact Walk.endpoint_notMem_support_takeUntil (Q j).isPath.reverse hzQ_rev hneQ
    obtain ⟨s, hs, hsS⟩ :=
      hS_sep.exists_mem_support_of_walk (P i).first_mem (Q j).last_mem (w₁.append w₂)
    rw [Walk.mem_support_append_iff] at hs
    rcases hs with hs₁ | hs₂
    · have hs_eq : s = (P i).last :=
        hP_only i (Walk.support_takeUntil_subset_support _ _ hs₁) hsS
      exact hw₁_not (hs_eq ▸ hs₁)
    · rw [Walk.support_reverse, List.mem_reverse] at hs₂
      have hs_in_Q : s ∈ (Q j).walk.support := by
        have := Walk.support_takeUntil_subset_support _ _ hs₂
        rwa [Walk.support_reverse, List.mem_reverse] at this
      have hs_eq : s = (Q j).first := (hQ_only j hs_in_Q hsS).trans (hPQ_eq j).symm
      rw [Walk.support_reverse, List.mem_reverse] at hw₂_not
      exact hw₂_not (hs_eq ▸ hs₂)
  let R : Fin k → PathFromTo K A B := fun i ↦
    let w := (P i).walk.append ((Q i).walk.copy (hPQ_eq i) rfl)
    ⟨(P i).first, (Q i).last, w.bypass, w.bypass_isPath, (P i).first_mem, (Q i).last_mem⟩
  refine ⟨R, fun i j hij ↦ Set.disjoint_left.mpr fun z hzi hzj ↦ ?_⟩
  have hzi' := Walk.support_bypass_subset_support _ hzi
  have hzj' := Walk.support_bypass_subset_support _ hzj
  rw [Walk.mem_support_append_iff, Walk.support_copy] at hzi' hzj'
  rcases hzi' with hziP | hziQ <;> rcases hzj' with hzjP | hzjQ
  · exact Set.disjoint_left.mp (hP hij) hziP hzjP
  · have hzS := h_inter_in_S i j hziP hzjQ
    have h1 := hP_only i hziP hzS
    have h2 := hQ_only j hzjQ hzS
    exact hp_inj.ne hij (Subtype.ext (h1.symm.trans h2))
  · have hzS := h_inter_in_S j i hzjP hziQ
    have h1 := hQ_only i hziQ hzS
    have h2 := hP_only j hzjP hzS
    exact hp_inj.ne hij (Subtype.ext (h1.symm.trans h2))
  · exact Set.disjoint_left.mp (hQ hij) hziQ hzjQ

private lemma hasDisjointPaths_mono {K K' : SimpleGraph V} (hle : K ≤ K') {A B : Set V} {k : ℕ}
    (h : HasDisjointPaths K A B k) : HasDisjointPaths K' A B k := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun i ↦ ⟨(P i).first, (P i).last, (P i).walk.mapLe hle, (P i).isPath.mapLe _,
    (P i).first_mem, (P i).last_mem⟩, fun i j hij ↦ ?_⟩
  simpa using hP hij

private lemma exists_disjointPaths_aux [Finite V] :
    ∀ (n : ℕ) (K : SimpleGraph V) (A B : Set V), K.edgeSet.ncard = n →
      ∀ (k : ℕ), (∀ S : Set V, IsSeparator K A B S → k ≤ S.ncard) →
        HasDisjointPaths K A B k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K A B hn k h
    rcases K.edgeSet.eq_empty_or_nonempty with hE | ⟨e, he⟩
    · exact hasDisjointPaths_of_edgeSet_eq_empty K A B hE k h
    · induction e using Sym2.ind with
      | _ x y =>
        have hxy : K.Adj x y := K.mem_edgeSet.mp he
        let K_con := contractEdge K x y
        let A' := contractSet x y A
        let B' := contractSet x y B
        by_cases hcon : ∀ S' : Set V, IsSeparator K_con A' B' S' → k ≤ S'.ncard
        · have hlt : K_con.edgeSet.ncard < n := hn ▸ ncard_edgeSet_contractEdge_lt hxy
          exact hasDisjointPaths_of_contractEdge hxy (ih _ hlt K_con A' B' rfl k hcon)
        · obtain ⟨S, hxS, hyS, hS_sep, hS_card⟩ :=
            exists_separator_of_not_contractEdge hxy h hcon
          let K_del := K.deleteEdges {s(x, y)}
          have hdel_lt : K_del.edgeSet.ncard < n := by
            have h1 : (K.edgeSet \ {s(x, y)}).ncard + 1 = K.edgeSet.ncard :=
              Set.ncard_sdiff_singleton_add_one he (Set.toFinite _)
            rw [edgeSet_deleteEdges]
            omega
          have hAS_sep : ∀ T : Set V, IsSeparator K_del A S T → k ≤ T.ncard :=
            fun T hT ↦ h T (isSeparator_of_deleteEdges_left hxy hxS hyS hS_sep hT)
          have hSB_sep : ∀ T : Set V, IsSeparator K_del S B T → k ≤ T.ncard :=
            fun T hT ↦ h T (isSeparator_of_deleteEdges_right hxy hxS hyS hS_sep hT)
          have hAS : HasDisjointPaths K A S k :=
            hasDisjointPaths_mono (K.deleteEdges_le _) (ih _ hdel_lt K_del A S rfl k hAS_sep)
          have hSB : HasDisjointPaths K S B k :=
            hasDisjointPaths_mono (K.deleteEdges_le _) (ih _ hdel_lt K_del S B rfl k hSB_sep)
          exact hasDisjointPaths_trans_of_separator hS_sep hS_card hAS hSB

/-- Menger's theorem for finite simple graphs: if every set of vertices meeting every path from
`A` to `B` has at least `k` vertices, there are `k` disjoint paths from `A` to `B`. -/
theorem exists_disjointPaths {V : Type*} (K : SimpleGraph V)
    (A B : Set V) (hfin : Finite V) (k : ℕ) (h : ∀ S : Set V, (∀ P : PathFromTo K A B,
      ∃ x ∈ P.walk.support, x ∈ S) → k ≤ S.ncard) : HasDisjointPaths K A B k :=
  exists_disjointPaths_aux K.edgeSet.ncard K A B rfl k h

end GraphMinor.Menger
