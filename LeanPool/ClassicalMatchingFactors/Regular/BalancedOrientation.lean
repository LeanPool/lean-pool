/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalMatchingFactors.Regular.EulerTrail

/-!

Imported from [jtraverso/euler-petersen](https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean), registered as PALOMAR-2026-10-16-000016. The original proof is retained; module paths and imports are adapted for this collection.

# Orientaciones eulerianas

Todo grafo finito cuyos vértices tienen grado par admite una orientación *balanceada*: cada
vértice tiene tantos arcos salientes como entrantes.

La prueba reutiliza la maquinaria del teorema de Euler (`exists_closed_trail_avoiding`): se
descomponen las aristas en trails cerrados disjuntos, agregando uno a la vez, y cada trail
cerrado, recorrido en su sentido, aporta lo mismo a los grados de entrada y de salida.

Representamos una orientación por un conjunto de dardos `Ds : Finset G.Dart` que contiene
exactamente un dardo por arista.
-/

@[expose] public section

namespace SimpleGraph

open Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- En un paseo de `u` a `w`, los dardos que salen de `v` y los que entran a `v` difieren sólo
en los extremos. -/
lemma Walk.countP_darts_fst_add {u w : V} (p : G.Walk u w) (v : V) :
    p.darts.countP (fun d => d.fst = v) + (if w = v then 1 else 0) =
      p.darts.countP (fun d => d.snd = v) + (if u = v then 1 else 0) := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rename_i a b c
    simp only [darts_cons, List.countP_cons]
    have := ih
    by_cases hav : a = v <;> by_cases hbv : b = v <;> simp_all <;> omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- En un paseo cerrado salen de cada vértice tantos dardos como entran. -/
lemma Walk.countP_darts_fst_eq {u : V} (p : G.Walk u u) (v : V) :
    p.darts.countP (fun d => d.fst = v) = p.darts.countP (fun d => d.snd = v) := by
  have := p.countP_darts_fst_add v
  omega

/-- `Ds` contiene a lo más un dardo por arista. -/
def EdgeInj (Ds : Finset G.Dart) : Prop :=
  ∀ d ∈ Ds, ∀ d' ∈ Ds, d.edge = d'.edge → d = d'

/-- `Ds` es balanceado: en cada vértice salen tantos dardos como entran. -/
def Balanced (Ds : Finset G.Dart) : Prop :=
  ∀ v, (Ds.filter fun d => d.fst = v).card = (Ds.filter fun d => d.snd = v).card

lemma card_filter_toFinset_of_nodup {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (p : α → Prop) [DecidablePred p] : (l.toFinset.filter p).card = l.countP p := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext a
  simp

omit [Fintype V] [DecidableRel G.Adj] in
/-- Las aristas de un conjunto de dardos con a lo más un dardo por arista, contadas en `v`. -/
lemma card_image_edge_filter {Ds : Finset G.Dart} (hinj : EdgeInj Ds) (v : V) :
    ((Ds.image Dart.edge).filter (v ∈ ·)).card =
      (Ds.filter fun d => d.fst = v).card + (Ds.filter fun d => d.snd = v).card := by
  have h1 : (Ds.image Dart.edge).filter (v ∈ ·) =
      (Ds.filter fun d => v ∈ d.edge).image Dart.edge := by
    ext e
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hv⟩; exact ⟨a, ⟨ha, hv⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hv⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, hv⟩
  rw [h1, card_image_of_injOn fun d hd d' hd' h =>
    hinj d (mem_filter.mp hd).1 d' (mem_filter.mp hd').1 h]
  have h2 : (Ds.filter fun d => v ∈ d.edge) =
      (Ds.filter fun d => d.fst = v) ∪ (Ds.filter fun d => d.snd = v) := by
    ext d
    simp only [mem_filter, mem_union, Dart.edge, Sym2.mem_iff]
    constructor
    · rintro ⟨hd, h | h⟩
      · exact Or.inl ⟨hd, h.symm⟩
      · exact Or.inr ⟨hd, h.symm⟩
    · rintro (⟨hd, h⟩ | ⟨hd, h⟩)
      · exact ⟨hd, Or.inl h.symm⟩
      · exact ⟨hd, Or.inr h.symm⟩
  rw [h2, card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro d h1 h2
  rw [mem_filter] at h1 h2
  exact d.adj.ne (h1.2.trans h2.2.symm)

/-- Paso: si `Ds` no cubre todas las aristas, se agrega un trail cerrado. -/
lemma exists_larger_balanced (heven : ∀ v, Even (G.degree v)) {Ds : Finset G.Dart}
    (hinj : EdgeInj Ds) (hbal : Balanced Ds) {x y₀ : V} (hxy : G.Adj x y₀)
    (hnot : ∀ d ∈ Ds, d.edge ≠ s(x, y₀)) :
    ∃ Ds' : Finset G.Dart, EdgeInj Ds' ∧ Balanced Ds' ∧ Ds ⊆ Ds' ∧ Ds.card < Ds'.card := by
  set S := (Ds.image Dart.edge).toList
  have hSnd : S.Nodup := nodup_toList _
  have hSsub : ∀ e ∈ S, e ∈ G.edgeSet := by
    intro e he
    rw [mem_toList, mem_image] at he
    obtain ⟨d, -, rfl⟩ := he
    exact d.edge_mem
  have hpar : ∀ y, Even (S.countP fun e => y ∈ e) ↔ Even (G.degree y) := by
    intro y
    refine iff_of_true ?_ (heven y)
    rw [← card_filter_toFinset_of_nodup hSnd, toList_toFinset, card_image_edge_filter hinj,
      hbal y]
    exact ⟨_, rfl⟩
  have hnotS : s(x, y₀) ∉ S := by
    rw [mem_toList, mem_image]
    rintro ⟨d, hd, he⟩
    exact hnot d hd he
  obtain ⟨c, hc, hcpos, hcdisj⟩ := exists_closed_trail_avoiding hSnd hSsub hpar hxy hnotS
  have hdnd : c.darts.Nodup := List.Nodup.of_map Dart.edge hc.edges_nodup
  have hdisj : Disjoint Ds c.darts.toFinset := by
    rw [Finset.disjoint_left]
    intro d hd hdc
    have : d.edge ∈ c.edges := by
      rw [edges_eq_map_darts]; exact List.mem_map_of_mem (List.mem_toFinset.mp hdc)
    exact hcdisj _ this (by rw [mem_toList]; exact mem_image_of_mem _ hd)
  refine ⟨Ds ∪ c.darts.toFinset, ?_, ?_, subset_union_left, ?_⟩
  · intro d hd d' hd' he
    rcases mem_union.mp hd with hd | hd <;> rcases mem_union.mp hd' with hd' | hd'
    · exact hinj d hd d' hd' he
    · exfalso
      have : d'.edge ∈ c.edges := by
        rw [edges_eq_map_darts]; exact List.mem_map_of_mem (List.mem_toFinset.mp hd')
      exact hcdisj _ this (by rw [mem_toList, ← he]; exact mem_image_of_mem _ hd)
    · exfalso
      have : d.edge ∈ c.edges := by
        rw [edges_eq_map_darts]; exact List.mem_map_of_mem (List.mem_toFinset.mp hd)
      exact hcdisj _ this (by rw [mem_toList, he]; exact mem_image_of_mem _ hd')
    · exact List.inj_on_of_nodup_map (by rw [← edges_eq_map_darts]; exact hc.edges_nodup)
        (List.mem_toFinset.mp hd) (List.mem_toFinset.mp hd') he
  · intro v
    rw [filter_union, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj),
      card_union_of_disjoint (disjoint_filter_filter hdisj), hbal v,
      card_filter_toFinset_of_nodup hdnd, card_filter_toFinset_of_nodup hdnd,
      c.countP_darts_fst_eq v]
  · rw [card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hdnd, length_darts]
    omega

omit [DecidableEq V] in
/-- Un conjunto de dardos con a lo más un dardo por arista tiene a lo más `|E|` elementos. -/
lemma card_le_of_edgeInj {Ds : Finset G.Dart} (hinj : EdgeInj Ds) :
    Ds.card ≤ G.edgeFinset.card := by
  classical
  rw [← card_image_of_injOn fun d hd d' hd' h => hinj d hd d' hd' h]
  refine card_le_card fun e he => ?_
  obtain ⟨d, -, rfl⟩ := mem_image.mp he
  rw [mem_edgeFinset]
  exact d.edge_mem

/-- **Orientación euleriana.** Si todos los grados son pares, existe un conjunto de dardos con
exactamente un dardo por arista, balanceado en cada vértice. -/
theorem exists_balanced_orientation (heven : ∀ v, Even (G.degree v)) :
    ∃ Ds : Finset G.Dart, EdgeInj Ds ∧ Balanced Ds ∧
      ∀ e ∈ G.edgeSet, ∃ d ∈ Ds, d.edge = e := by
  suffices key : ∀ n, ∀ Ds : Finset G.Dart, EdgeInj Ds → Balanced Ds →
      G.edgeFinset.card - Ds.card = n → ∃ Ds' : Finset G.Dart, EdgeInj Ds' ∧ Balanced Ds' ∧
        ∀ e ∈ G.edgeSet, ∃ d ∈ Ds', d.edge = e by
    exact key _ ∅ (by simp [EdgeInj]) (by simp [Balanced]) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Ds hinj hbal hn
  by_cases hcov : ∀ e ∈ G.edgeSet, ∃ d ∈ Ds, d.edge = e
  · exact ⟨Ds, hinj, hbal, hcov⟩
  push Not at hcov
  obtain ⟨e, he, hnot⟩ := hcov
  induction e using Sym2.ind with
  | _ x y₀ =>
  obtain ⟨Ds', hinj', hbal', -, hlt⟩ := exists_larger_balanced heven hinj hbal he hnot
  have h1 := card_le_of_edgeInj hinj'
  exact ih _ (by omega) Ds' hinj' hbal' rfl

end SimpleGraph
