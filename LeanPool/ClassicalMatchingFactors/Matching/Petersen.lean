/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
/-!

Imported from [jtraverso/petersen-matching](https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean), registered as PALOMAR-2026-10-16-000004. The original proof is retained; module paths and imports are adapted for this collection.

# Petersen's theorem on perfect matchings in cubic graphs

For a finite simple graph that is 3-regular (`IsRegularOfDegree 3`) and has no bridge (no edge
of the graph is a bridge, `IsBridge`):

* `PetersenTheorem.exists_isPerfectMatching`: **Petersen (1891).** The graph has a perfect
  matching.
* `PetersenTheorem.exists_isPerfectMatching_mem`: moreover, every edge lies in some perfect
  matching.

Both follow from Tutte's theorem (Mathlib's `SimpleGraph.tutte`) by counting the edges leaving the
odd components.
-/

@[expose] public section

open SimpleGraph

namespace PetersenTheorem

variable {V : Type*}

section Counting

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of darts leaving a vertex set `C`. -/
def outDarts (C : Finset V) : ℕ := ∑ x ∈ C, (G.neighborFinset x \ C).card

/-- Number of darts inside a vertex set `C`. -/
def innDarts (C : Finset V) : ℕ := ∑ x ∈ C, (G.neighborFinset x ∩ C).card

lemma even_innDarts (C : Finset V) : Even (innDarts G C) := by
  classical
  let H : SimpleGraph V :=
    { Adj := fun x y => G.Adj x y ∧ x ∈ C ∧ y ∈ C
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  have hdeg : ∀ x, H.degree x = if x ∈ C then (G.neighborFinset x ∩ C).card else 0 := by
    intro x
    rw [← card_neighborFinset_eq_degree]
    split_ifs with hx
    · congr 1
      ext y
      simp [H, hx]
    · rw [Finset.card_eq_zero]
      ext y
      simp [H, hx]
  have hsum := H.sum_degrees_eq_twice_card_edges
  simp only [hdeg] at hsum
  rw [Finset.sum_ite_mem, Finset.univ_inter] at hsum
  unfold innDarts
  rw [hsum]
  exact even_two_mul _

lemma outDarts_add_innDarts (h3 : G.IsRegularOfDegree 3) (C : Finset V) :
    outDarts G C + innDarts G C = 3 * C.card := by
  unfold outDarts innDarts
  rw [← Finset.sum_add_distrib, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_sdiff_add_card_inter, card_neighborFinset_eq_degree, h3 x]
  rfl

lemma outDarts_ne_one (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (C : Finset V) :
    outDarts G C ≠ 1 := by
  intro h1
  have hcard : (C.sigma fun x => G.neighborFinset x \ C).card = 1 := by
    rw [Finset.card_sigma]; exact h1
  obtain ⟨⟨x, y⟩, hD⟩ := Finset.card_eq_one.mp hcard
  have hxy : (⟨x, y⟩ : Σ _ : V, V) ∈ C.sigma fun x => G.neighborFinset x \ C := by
    rw [hD]; exact Finset.mem_singleton_self _
  simp only [Finset.mem_sigma, Finset.mem_sdiff, mem_neighborFinset] at hxy
  obtain ⟨hx, hadj, hy⟩ := hxy
  apply hb s(x, y) hadj
  rw [isBridge_iff]
  rintro ⟨p⟩
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (C : Set V) hx hy
  have hdadj := d.adj
  rw [deleteEdges_adj] at hdadj
  have hmem : (⟨d.fst, d.snd⟩ : Σ _ : V, V) ∈ C.sigma fun x => G.neighborFinset x \ C := by
    simp only [Finset.mem_sigma, Finset.mem_sdiff, mem_neighborFinset]
    exact ⟨hd1, hdadj.1, hd2⟩
  rw [hD, Finset.mem_singleton] at hmem
  simp only [Sigma.mk.injEq, heq_eq_eq] at hmem
  apply hdadj.2
  rw [hmem.1, hmem.2]
  rfl

lemma three_le_outDarts (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (C : Finset V) (hC : Odd C.card) : 3 ≤ outDarts G C := by
  have h1 := outDarts_add_innDarts G h3 C
  have h2 := even_innDarts G C
  have h4 := outDarts_ne_one G hb C
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := hC
  omega

lemma three_mul_card_le {ι : Type*} (h3 : G.IsRegularOfDegree 3)
    (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (O : Finset ι) (f : ι → Finset V) (T : Finset V)
    (hdisj : (O : Set ι).PairwiseDisjoint f) (hT : ∀ i ∈ O, Disjoint (f i) T)
    (hclosed : ∀ i ∈ O, ∀ x ∈ f i, ∀ y, G.Adj x y → y ∉ T → y ∈ f i)
    (hodd : ∀ i ∈ O, Odd (f i).card) :
    3 * O.card ≤ ∑ y ∈ T, (G.neighborFinset y \ T).card := by
  have step1 : 3 * O.card ≤ ∑ i ∈ O, ∑ x ∈ f i, (G.neighborFinset x ∩ T).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i hi => ?_
    refine (three_le_outDarts G h3 hb _ (hodd i hi)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x hx => ?_
    congr 1
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_inter, mem_neighborFinset]
    constructor
    · rintro ⟨hxy, hy⟩
      refine ⟨hxy, ?_⟩
      by_contra hyT
      exact hy (hclosed i hi x hx y hxy hyT)
    · rintro ⟨hxy, hy⟩
      exact ⟨hxy, fun hyi => Finset.disjoint_left.mp (hT i hi) hyi hy⟩
  rw [← Finset.sum_biUnion hdisj] at step1
  refine step1.trans ?_
  set U := O.biUnion f with hU
  have hUT : Disjoint U T := by
    rw [hU, Finset.disjoint_biUnion_left]; exact hT
  have e1 : ∀ x, (G.neighborFinset x ∩ T).card = ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
    intro x
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext y; simp [mem_neighborFinset, and_comm]
  simp only [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun y hy => ?_
  rw [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter] at hx
  simp only [Finset.mem_sdiff, mem_neighborFinset]
  exact ⟨hx.2.symm, fun hxT => Finset.disjoint_left.mp hUT hx.1 hxT⟩

end Counting

lemma three_mul_oddComponents_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    {W : Type*} [Finite W] (H : SimpleGraph W) (S : Set W) (e : W ↪ V) (T : Finset V)
    (hdisjT : ∀ w, w ∉ S → e w ∉ T)
    (hclosed : ∀ w, w ∉ S → ∀ y, G.Adj (e w) y → y ∉ T → ∃ w', e w' = y ∧ H.Adj w w' ∧ w' ∉ S) :
    3 * ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤
      ∑ y ∈ T, (G.neighborFinset y \ T).card := by
  classical
  have := Fintype.ofFinite W
  set K := ((⊤ : H.Subgraph).deleteVerts S).coe with hK
  have hfin : K.oddComponents.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  let f : K.ConnectedComponent → Finset V := fun c =>
    (c.supp.toFinset.map (Function.Embedding.subtype _)).map e
  have hmem : ∀ c y, y ∈ f c ↔ ∃ w, ∃ hw : w ∈ ((⊤ : H.Subgraph).deleteVerts S).verts,
      K.connectedComponentMk ⟨w, hw⟩ = c ∧ e w = y := by
    intro c y
    simp [f, ConnectedComponent.mem_supp_iff]
  apply three_mul_card_le G h3 hb hfin.toFinset f T
  · intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨w, hw, rfl, rfl⟩ := (hmem _ _).mp hy
    obtain ⟨w', hw', rfl, he⟩ := (hmem _ _).mp hy'
    obtain rfl := e.injective he
    exact hcc' rfl
  · intro c _
    rw [Finset.disjoint_left]
    intro y hy
    obtain ⟨w, hw, rfl, rfl⟩ := (hmem _ _).mp hy
    exact hdisjT w (by simpa using hw)
  · intro c _ x hx y hadj hyT
    obtain ⟨w, hw, rfl, rfl⟩ := (hmem _ _).mp hx
    have hwS : w ∉ S := by simpa using hw
    obtain ⟨w', rfl, hadj', hw'S⟩ := hclosed w hwS y hadj hyT
    have hw' : w' ∈ ((⊤ : H.Subgraph).deleteVerts S).verts := by simpa using hw'S
    rw [hmem]
    refine ⟨w', hw', ?_, rfl⟩
    have hKadj : K.Adj ⟨w, hw⟩ ⟨w', hw'⟩ := by
      simp [hK, hwS, hw'S, hadj']
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hKadj).symm
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    simp only [f, Finset.card_map]
    rw [← Set.ncard_eq_toFinset_card']
    exact hc


lemma sum_card_neighborFinset_sdiff_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) (T : Finset V) :
    ∑ y ∈ T, (G.neighborFinset y \ T).card ≤ 3 * T.card := by
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun y _ => (Finset.card_le_card Finset.sdiff_subset).trans ?_
  rw [card_neighborFinset_eq_degree, h3 y]


/-- **Petersen's theorem (1891).** A finite bridgeless cubic graph has a perfect matching. -/
theorem exists_isPerfectMatching [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  rw [tutte]
  intro S hS
  rw [IsTutteViolator] at hS
  have h := three_mul_oddComponents_le G h3 hb G S (Function.Embedding.refl V) S.toFinset
    (fun w hw => by simpa using hw)
    (fun w hw y hadj hy => ⟨y, rfl, hadj, by simpa using hy⟩)
  have h' := sum_card_neighborFinset_sdiff_le G h3 S.toFinset
  rw [← Set.ncard_eq_toFinset_card'] at h'
  omega

/-- In a finite bridgeless cubic graph every edge lies in some perfect matching. -/
theorem exists_isPerfectMatching_mem [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∀ e ∈ G.edgeSet, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∈ M.edgeSet := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := he
  have hne : u ≠ v := huv.ne
  let W : Set V := ({u, v} : Set V)ᶜ
  let G' : SimpleGraph W := G.induce W
  obtain ⟨M', hM'⟩ : ∃ M : G'.Subgraph, M.IsPerfectMatching := by
    rw [tutte]
    intro S hS
    rw [IsTutteViolator] at hS
    have hWuv : ∀ w : W, (w : V) ≠ u ∧ (w : V) ≠ v := by
      intro w
      have h : (w : V) ∉ ({u, v} : Set V) := w.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
      exact h
    let T : Finset V := S.toFinset.map (Function.Embedding.subtype _) ∪ {u, v}
    have hdisjT : ∀ w, w ∉ S → (Function.Embedding.subtype _ w : V) ∉ T := by
      intro w hw hwT
      rcases Finset.mem_union.mp hwT with h | h
      · obtain ⟨w', hw', hww'⟩ := Finset.mem_map.mp h
        obtain rfl := Subtype.val_injective hww'
        exact hw (Set.mem_toFinset.mp hw')
      · have := hWuv w
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact this.1 h
        · exact this.2 h
    have hclosed : ∀ w, w ∉ S → ∀ y, G.Adj (Function.Embedding.subtype _ w) y → y ∉ T →
        ∃ w', Function.Embedding.subtype _ w' = y ∧ G'.Adj w w' ∧ w' ∉ S := by
      intro w hw y hadj hy
      have hyu : y ≠ u := by
        rintro rfl; exact hy (Finset.mem_union_right _ (by simp))
      have hyv : y ≠ v := by
        rintro rfl; exact hy (Finset.mem_union_right _ (by simp))
      have hyW : y ∈ W := by simp [W, hyu, hyv]
      refine ⟨⟨y, hyW⟩, rfl, hadj, fun hS' => hy ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ (Set.mem_toFinset.mpr hS'))
    have h := three_mul_oddComponents_le G h3 hb G' S (Function.Embedding.subtype _) T
      hdisjT hclosed
    have hle3 : ∀ y, (G.neighborFinset y \ T).card ≤ 3 := fun y =>
      (Finset.card_le_card Finset.sdiff_subset).trans (by rw [card_neighborFinset_eq_degree, h3 y])
    have hle2 : ∀ a b, G.Adj a b → b ∈ T → (G.neighborFinset a \ T).card ≤ 2 := by
      intro a b hab hbT
      have hsub : G.neighborFinset a \ T ⊆ (G.neighborFinset a).erase b := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        exact Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ hbT), hx.1⟩
      refine (Finset.card_le_card hsub).trans ?_
      rw [Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hab),
        card_neighborFinset_eq_degree, h3 a]
    have hdisj : Disjoint (S.toFinset.map (Function.Embedding.subtype _)) ({u, v} : Finset V) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hx
      have := hWuv w
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with h | h
      · exact this.1 h
      · exact this.2 h
    have key : ∀ g : V → ℕ, (∀ y, g y ≤ 3) → g u ≤ 2 → g v ≤ 2 →
        ∑ y ∈ T, g y ≤ 3 * S.ncard + 4 := by
      intro g hg hgu hgv
      simp only [T]
      rw [Finset.sum_union hdisj, Finset.sum_pair hne]
      have h1 : ∑ x ∈ S.toFinset.map (Function.Embedding.subtype _), g x ≤ S.ncard * 3 := by
        rw [Set.ncard_eq_toFinset_card', ← Finset.card_map (Function.Embedding.subtype _)]
        have h := Finset.sum_le_card_nsmul (S.toFinset.map (Function.Embedding.subtype _)) g 3
          (fun y _ => hg y)
        rw [smul_eq_mul] at h
        exact h
      omega
    have hsum : ∑ y ∈ T, (G.neighborFinset y \ T).card ≤ 3 * S.ncard + 4 :=
      key _ hle3 (hle2 u v huv (Finset.mem_union_right _ (by simp)))
        (hle2 v u huv.symm (Finset.mem_union_right _ (by simp)))
    -- parity
    have hpar := odd_ncard_oddComponents (G := ((⊤ : G'.Subgraph).deleteVerts S).coe)
    have hdiff : Nat.card ↥((⊤ : G'.Subgraph).deleteVerts S).verts + S.ncard = W.ncard := by
      rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top,
        Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ S), Set.ncard_univ,
        Nat.card_coe_set_eq]
    have hW : 2 + W.ncard = Nat.card V := by
      rw [← Set.ncard_pair hne]; exact Set.ncard_add_ncard_compl _
    have hV : Even (Nat.card V) := by
      have hs := G.sum_degrees_eq_twice_card_edges
      simp only [h3.degree_eq, Finset.sum_const, smul_eq_mul, Finset.card_univ] at hs
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr (by omega)
    rw [Nat.odd_iff, Nat.odd_iff] at hpar
    rw [Nat.even_iff] at hV
    omega
  rw [Subgraph.isPerfectMatching_iff] at hM'
  let M : G.Subgraph :=
    { verts := Set.univ
      Adj := fun a b => s(a, b) = s(u, v) ∨
        ∃ (ha : a ∈ W) (hb : b ∈ W), M'.Adj ⟨a, ha⟩ ⟨b, hb⟩
      adj_sub := by
        rintro a b (h | ⟨ha, hb, h⟩)
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact huv
          · exact huv.symm
        · exact M'.adj_sub h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨by
        rintro a b (h | ⟨ha, hb, h⟩)
        · left; rw [Sym2.eq_swap]; exact h
        · exact Or.inr ⟨hb, ha, h.symm⟩⟩ }
  have hWuv : ∀ a, a ∈ W ↔ a ≠ u ∧ a ≠ v := by
    intro a; simp [W, not_or]
  refine ⟨M, ?_, Or.inl rfl⟩
  rw [Subgraph.isPerfectMatching_iff]
  intro a
  by_cases hau : a = u
  · subst hau
    refine ⟨v, Or.inl rfl, ?_⟩
    rintro b (h | ⟨ha, -, -⟩)
    · exact Sym2.congr_right.mp h
    · exact absurd rfl ((hWuv a).mp ha).1
  by_cases hav : a = v
  · subst hav
    refine ⟨u, Or.inl Sym2.eq_swap, ?_⟩
    rintro b (h | ⟨ha, -, -⟩)
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1.symm hne
      · exact h2
    · exact absurd rfl ((hWuv a).mp ha).2
  have ha : a ∈ W := (hWuv a).mpr ⟨hau, hav⟩
  obtain ⟨w, hw, huniq⟩ := hM' ⟨a, ha⟩
  refine ⟨w, Or.inr ⟨ha, w.2, hw⟩, ?_⟩
  rintro b (h | ⟨_, hb, h⟩)
  · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hau
    · exact absurd h1 hav
  · exact congrArg Subtype.val (huniq ⟨b, hb⟩ h)

end PetersenTheorem
