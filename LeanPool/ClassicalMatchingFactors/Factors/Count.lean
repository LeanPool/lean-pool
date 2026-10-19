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
public import LeanPool.ClassicalMatchingFactors.Factors.Defs
public import LeanPool.ClassicalMatchingFactors.Factors.Suff

/-!

Imported from [jtraverso/tutte-f-factor](https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean), registered as PALOMAR-2026-10-18-000005. The original proof is retained; module paths and imports are adapted for this collection.

# Counting the odd components of the gadget minus a normalised Tutte violator
-/

@[expose] public section

open Finset SimpleGraph

namespace FFactor

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}

open Classical in
/-- Filters along equivalent predicates (with arbitrary decidability instances) have the same
cardinality. -/
theorem card_filter_congr' {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (h : ∀ a, p a ↔ q a) : #{a | p a} = #{a | q a} := by
  apply card_bij (fun a _ => a) <;> simp [h]

open Classical in
/-- Cardinality of a filter over a sum type. -/
theorem card_filter_sum_type {α β : Type*} [Fintype α] [Fintype β] (P : α ⊕ β → Prop)
    [DecidablePred P] :
    #{x | P x} = #{a | P (.inl a)} + #{b | P (.inr b)} := by
  simp only [card_filter, Fintype.sum_sum_type]

omit [DecidableEq V] in
open Classical in
/-- Cardinality of a filter over the vertices of `gadget - U`. -/
theorem card_filter_verts (P : GV G f → Prop) [DecidablePred P]
    [DecidablePred (fun x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts => P x.1)] :
    #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts | P x.1} = #{a | a ∉ U ∧ P a} := by
  apply card_bij (fun x _ => x.1)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨(mem_del_verts _).mp x.2, hx⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    exact ⟨⟨a, (mem_del_verts _).mpr ha.1⟩, by simpa using ha.2, rfl⟩

open Classical in
theorem card_inner_fiber (r : V) :
    #{p : Σ v : V, Fin (G.degree v - f v) | p.1 = r} = G.degree r - f r := by
  have : #(univ : Finset (Fin (G.degree r - f r))) =
      #{p : Σ v : V, Fin (G.degree v - f v) | p.1 = r} := by
    apply card_bij (fun (i : Fin (G.degree r - f r)) _ =>
      (⟨r, i⟩ : Σ v : V, Fin (G.degree v - f v)))
    · intro i _; simp
    · intro i _ j _ h; exact eq_of_heq (Sigma.mk.inj h).2
    · rintro ⟨r', j⟩ h
      simp only [mem_filter, mem_univ, true_and] at h
      subst h
      exact ⟨j, mem_univ _, rfl⟩
  rw [← this, card_univ, Fintype.card_fin]

open Classical in
theorem card_dart_snd_fst (r : V) (T : Finset V) :
    #{d : G.Dart | d.fst ∈ T ∧ d.snd = r} = #{t ∈ T | G.Adj r t} := by
  apply card_bij (fun d _ => d.fst)
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    exact ⟨hd.1, hd.2 ▸ d.adj.symm⟩
  · intro d _ d' _ h
    simp only [mem_filter, mem_univ, true_and] at *
    exact Dart.ext _ _ (Prod.ext h (by simp_all))
  · intro t ht
    simp only [mem_filter] at ht
    exact ⟨⟨(t, r), ht.2.symm⟩, by simp [ht.1], rfl⟩

open Classical in
theorem card_home_fiber {r : V} (hr : r ∉ Tset G f U) :
    #{a : GV G f | home G f U a = r} =
      G.degree r + #{t ∈ Tset G f U | G.Adj r t} + (G.degree r - f r) := by
  rw [card_filter_sum_type]
  have e1 : #{b : Σ v : V, Fin (G.degree v - f v) | home G f U (.inr b) = r} =
      G.degree r - f r := by
    rw [← card_inner_fiber r]; congr 1
  have e2 : #{d : G.Dart | home G f U (.inl d) = r} =
      G.degree r + #{t ∈ Tset G f U | G.Adj r t} := by
    rw [← card_dart_snd_fst r (Tset G f U), ← G.dart_fst_fiber_card_eq_degree r,
      ← card_union_of_disjoint]
    · congr 1
      ext d
      simp only [mem_filter, mem_univ, true_and, mem_union]
      rw [home_inl]
      split_ifs with h
      · constructor
        · intro h'; exact Or.inr ⟨h, h'⟩
        · rintro (h' | h')
          · exact absurd (h' ▸ h) hr
          · exact h'.2
      · constructor
        · intro h'; exact Or.inl h'
        · rintro (h' | h')
          · exact h'
          · exact absurd h'.1 h
    · rw [Finset.disjoint_left]
      intro d h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      exact hr (h1 ▸ h2.1)
  rw [e1, e2]

open Classical in
theorem notMem_U_of_home {hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x} {a : GV G f}
    (ha : home G f U a ∉ Sset G f U ∪ Tset G f U) : a ∉ U := by
  have hT := notMem_T_of_notMem_union ha
  have hS := notMem_S_of_notMem_union ha
  rcases a with d | ⟨r, i⟩
  · rw [home_inl] at hT hS
    by_cases h : d.fst ∈ Tset G f U
    · exact F2 hmin h rfl
    · rw [ite_eq_right h] at hT hS
      exact F3 hmin hT hS rfl
  · exact F1 hmin hT i

open Classical in
theorem odd_fiber_iff (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    (hf : ∀ v, f v ≤ G.degree v) (c : (Gr G f U).ConnectedComponent) :
    Odd #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts | lab G f U x.1 = .inl c} ↔
    Odd (∑ w ∈ univ.filter (fun w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) =>
        (G.induce ((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ Tset G f U | G.Adj w t})) := by
  rw [card_filter_verts (U := U) (fun a => lab G f U a = .inl c)]
  obtain ⟨Cs, hCs⟩ : ∃ Cs : Finset V, Cs = (univ.filter
      (fun w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) =>
      (Gr G f U).connectedComponentMk w = c)).map (Function.Embedding.subtype _) := ⟨_, rfl⟩
  have hmem : ∀ r, r ∈ Cs ↔ ∃ h : r ∉ Sset G f U ∪ Tset G f U,
      (Gr G f U).connectedComponentMk ⟨r, h⟩ = c := by
    intro r
    simp only [hCs, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
    · rintro ⟨h, hc⟩; exact ⟨⟨r, h⟩, hc, rfl⟩
  have hset : ∀ a, (a ∉ U ∧ lab G f U a = .inl c) ↔ home G f U a ∈ Cs := by
    intro a
    rw [hmem]
    constructor
    · rintro ⟨haU, hlab⟩
      by_cases hh : home G f U a ∈ Sset G f U ∪ Tset G f U
      · exfalso
        rcases a with d | p
        · rw [lab_inl_of_mem hh] at hlab; simp at hlab
        · rw [lab_inr_of_mem hh] at hlab; simp at hlab
      · rw [lab_of_notMem hh] at hlab
        exact ⟨hh, Sum.inl_injective hlab⟩
    · rintro ⟨hh, hc⟩
      refine ⟨notMem_U_of_home (hmin := hmin) hh, ?_⟩
      rw [lab_of_notMem hh, hc]
  rw [card_filter_congr' _ _ hset, card_eq_sum_card_fiberwise (f := home G f U) (t := Cs)
    (fun a ha => by simpa using ha)]
  have hterm : ∀ r ∈ Cs, #{a ∈ ({a | home G f U a ∈ Cs} : Finset (GV G f)) | home G f U a = r} =
      G.degree r + #{t ∈ Tset G f U | G.Adj r t} + (G.degree r - f r) := by
    intro r hr
    obtain ⟨h, -⟩ := (hmem r).mp hr
    rw [← card_home_fiber (notMem_T_of_notMem_union h), filter_filter]
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h'; exact ⟨h' ▸ hr, h'⟩
  rw [sum_congr rfl hterm]
  have hsum : ∑ r ∈ Cs, (G.degree r + #{t ∈ Tset G f U | G.Adj r t} + (G.degree r - f r)) =
      ∑ w ∈ univ.filter (fun w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) =>
        (Gr G f U).connectedComponentMk w = c),
      (G.degree w + #{t ∈ Tset G f U | G.Adj w t} + (G.degree w - f w)) := by
    rw [hCs, sum_map]; rfl
  rw [hsum]
  have hsplit : ∀ w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ),
      G.degree w + #{t ∈ Tset G f U | G.Adj w t} + (G.degree w - f w) =
      (f w + #{t ∈ Tset G f U | G.Adj w t}) + 2 * (G.degree w - f w) := by
    intro w; have := hf w; omega
  rw [sum_congr rfl (fun w _ => hsplit w), sum_add_distrib, ← mul_sum]
  have key : ∀ A B : ℕ, Odd (A + 2 * B) ↔ Odd A := fun A B => by
    simp only [Nat.odd_iff]; omega
  exact key _ _

open Classical in
theorem card_fiber_TT (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {d : G.Dart}
    (hd : (.inl d : GV G f) ∉ U) (h1 : d.fst ∈ Tset G f U) (h2 : d.snd ∈ Tset G f U) :
    #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts |
      lab G f U x.1 = .inr (.inl d.edge)} = 2 := by
  have hmemd : home G f U (.inl d) ∈ Sset G f U ∪ Tset G f U := by
    simp [h1, h2]
  have hds : (.inl d.symm : GV G f) ∉ U := F2 hmin h2 (d := d.symm) rfl
  have hmemds : home G f U (.inl d.symm) ∈ Sset G f U ∪ Tset G f U := by
    simp [h1, h2]
  rw [card_filter_verts (U := U) (fun a => lab G f U a = .inr (.inl d.edge))]
  rw [card_filter_congr' _ (fun a => a ∈ ({.inl d, .inl d.symm} : Finset (GV G f)))]
  · rw [filter_univ_mem, card_pair]
    intro h
    exact d.symm_ne (Sum.inl_injective h).symm
  · intro a
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨haU, hlab⟩
      rcases a with d' | q
      · by_cases hh : home G f U (.inl d') ∈ Sset G f U ∪ Tset G f U
        · rw [lab_inl_of_mem hh] at hlab
          simp only [Sum.inr.injEq, Sum.inl.injEq] at hlab
          rcases (dart_edge_eq_iff _ _).mp hlab with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (by rw [h])
        · rw [lab_of_notMem hh] at hlab; simp at hlab
      · by_cases hh : home G f U (.inr q) ∈ Sset G f U ∪ Tset G f U
        · rw [lab_inr_of_mem hh] at hlab; simp at hlab
        · rw [lab_of_notMem hh] at hlab; simp at hlab
    · rintro (rfl | rfl)
      · exact ⟨hd, lab_inl_of_mem hmemd⟩
      · exact ⟨hds, by rw [lab_inl_of_mem hmemds, Dart.edge_symm]⟩

open Classical in
theorem ncard_odd_le (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    (hf : ∀ v, f v ≤ G.degree v) :
    (del (gadget G f) U).oddComponents.ncard ≤ oddCount G f (Sset G f U) (Tset G f U) +
      #{d : G.Dart | d.fst ∈ Tset G f U ∧ d.snd ∈ Sset G f U} +
      #{p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ Sset G f U} := by
  let φ : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts →
      (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f) := fun x => lab G f U x.1
  rw [oddComponents_ncard_eq_of_label (del (gadget G f) U) φ
    (fun x y h => lab_eq_of_adj _ _ ((mem_del_verts _).mp x.2) ((mem_del_verts _).mp y.2)
      ((del_adj _).mp h))
    (fun x y h => reach_of_lab_eq hmin x.1 y.1 ((mem_del_verts _).mp x.2)
      ((mem_del_verts _).mp y.2) h)]
  let A := (univ.filter (fun c : (Gr G f U).ConnectedComponent =>
    Odd #{x | φ x = .inl c})).image
    (fun c => (.inl c : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))
  let B := (univ.filter (fun d : G.Dart => d.fst ∈ Tset G f U ∧ d.snd ∈ Sset G f U)).image
    (fun d => (.inr (.inl d.edge) : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))
  let C := (univ.filter (fun p : Σ v : V, Fin (G.degree v - f v) => p.1 ∈ Sset G f U)).image
    (fun p => (.inr (.inr (.inr p)) : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))
  have hsub : ({l ∈ univ.image φ | Odd #{x | φ x = l}} :
      Finset ((Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f))) ⊆ A ∪ B ∪ C := by
    intro l hl
    simp only [mem_filter, mem_image, mem_univ, true_and] at hl
    obtain ⟨⟨x, rfl⟩, hodd⟩ := hl
    obtain ⟨a, ha⟩ := x
    have haU : a ∉ U := (mem_del_verts _).mp ha
    simp only [mem_union]
    by_cases hh : home G f U a ∈ Sset G f U ∪ Tset G f U
    · rcases a with d | p
      · have hS := fst_notMem_S_of_notMem haU
        have hT : d.fst ∈ Tset G f U := by
          by_contra hT
          rw [home_inl, ite_eq_right hT] at hh
          rcases mem_union.mp hh with h | h
          · exact hS h
          · exact hT h
        have hsnd : d.snd ∈ Sset G f U ∪ Tset G f U := by rwa [home_inl, ite_eq_left hT] at hh
        have hφ : φ ⟨.inl d, ha⟩ = .inr (.inl d.edge) := lab_inl_of_mem hh
        by_cases hsS : d.snd ∈ Sset G f U
        · left; right
          rw [hφ]
          exact mem_image.mpr ⟨d, by simp [hT, hsS], rfl⟩
        · exfalso
          have hsT : d.snd ∈ Tset G f U := by
            rcases mem_union.mp hsnd with h | h
            · exact absurd h hsS
            · exact h
          rw [hφ] at hodd
          have := card_fiber_TT hmin haU hT hsT
          rw [this] at hodd
          exact (Nat.not_odd_iff_even.mpr even_two) hodd
      · right
        have hφ : φ ⟨.inr p, ha⟩ = .inr (.inr (.inr p)) := lab_inr_of_mem hh
        rw [hφ]
        have hpT : p.1 ∉ Tset G f U := by
          obtain ⟨v, i⟩ := p
          exact notMem_T_of_inner_notMem haU
        have hpS : p.1 ∈ Sset G f U := by
          rcases mem_union.mp hh with h | h
          · exact h
          · exact absurd h hpT
        exact mem_image.mpr ⟨p, by simp [hpS], rfl⟩
    · left; left
      have hφ : φ ⟨a, ha⟩ = .inl ((Gr G f U).connectedComponentMk ⟨home G f U a, hh⟩) :=
        lab_of_notMem hh
      rw [hφ] at hodd ⊢
      exact mem_image.mpr ⟨_, by simpa using hodd, rfl⟩
  have hA : #A ≤ oddCount G f (Sset G f U) (Tset G f U) := by
    refine card_image_le.trans (le_of_eq ?_)
    rw [oddCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_filter_congr' _ _ (fun c => odd_fiber_iff hmin hf c)
  have key : ∀ s : Finset ((Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)),
      (∀ l ∈ s, l ∈ ({l ∈ univ.image φ | Odd #{x | φ x = l}} :
        Finset ((Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f)))) →
      #s ≤ #(A ∪ B ∪ C) := fun s hs => card_le_card (fun l hl => hsub (hs l hl))
  refine le_trans (key _ (fun l hl => by
    simp only [mem_filter, mem_image] at hl ⊢
    exact ⟨hl.1, by convert hl.2 using 2; ext; simp⟩)) ?_
  have h2 := card_union_le (A ∪ B) C
  have h3 := card_union_le A B
  have h4 : #B ≤ #{d : G.Dart | d.fst ∈ Tset G f U ∧ d.snd ∈ Sset G f U} := card_image_le
  have h5 : #C ≤ #{p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ Sset G f U} := card_image_le
  omega

open Classical in
theorem card_dart_fst_mem (s0 : Finset V) :
    #{d : G.Dart | d.fst ∈ s0} = ∑ v ∈ s0, G.degree v := by
  rw [card_eq_sum_card_fiberwise (s := {d : G.Dart | d.fst ∈ s0}) (f := fun d : G.Dart => d.fst)
    (t := s0) (fun d hd => (mem_filter.mp hd).2)]
  refine sum_congr rfl (fun v hv => ?_)
  rw [← G.dart_fst_fiber_card_eq_degree v, filter_filter]
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv, h⟩

open Classical in
theorem card_inner_mem (s0 : Finset V) :
    #{p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ s0} = ∑ v ∈ s0, (G.degree v - f v) := by
  rw [card_eq_sum_card_fiberwise (s := {p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ s0})
    (f := fun p : Σ v : V, Fin (G.degree v - f v) => p.1) (t := s0)
    (fun p hp => (mem_filter.mp hp).2)]
  refine sum_congr rfl (fun v hv => ?_)
  rw [← card_inner_fiber (f := f) v, filter_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv, h⟩

open Classical in
theorem card_dart_fst_snd_mem (T S : Finset V) :
    #{d : G.Dart | d.fst ∈ T ∧ d.snd ∈ S} = ∑ t ∈ T, #{u | G.Adj t u ∧ u ∈ S} := by
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := T)
    (fun d hd => (mem_filter.mp hd).2.1)]
  refine sum_congr rfl (fun t ht => ?_)
  apply card_bij (fun d _ => d.snd)
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    exact ⟨hd.2 ▸ d.adj, hd.1.2⟩
  · intro d hd d' hd' h
    simp only [mem_filter, mem_univ, true_and] at hd hd'
    exact Dart.ext _ _ (Prod.ext (hd.2.trans hd'.2.symm) h)
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    exact ⟨⟨(t, u), hu.1⟩, by simp [ht, hu.2], rfl⟩

omit [DecidableEq V] in
open Classical in
theorem card_adj_eq_degree (v : V) : #{u | G.Adj v u} = G.degree v := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext u
  simp

open Classical in
theorem card_adj_split (t : V) (S : Finset V) :
    #{u | G.Adj t u ∧ u ∈ S} + #{u | G.Adj t u ∧ u ∉ S} = G.degree t := by
  rw [← card_adj_eq_degree, ← card_filter_add_card_filter_not (s := {u | G.Adj t u})
    (fun u => u ∈ S), filter_filter, filter_filter]

omit [DecidableEq V] in
open Classical in
theorem card_le_ncard_U :
    ∑ v ∈ Sset G f U, G.degree v + ∑ v ∈ Tset G f U, (G.degree v - f v) ≤ U.ncard := by
  let F : Finset (GV G f) := (univ.filter (fun d : G.Dart => d.fst ∈ Sset G f U)).disjSum
    (univ.filter (fun p : Σ v : V, Fin (G.degree v - f v) => p.1 ∈ Tset G f U))
  have hF : (F : Set (GV G f)) ⊆ U := by
    rintro (d | p) h
    · have h' := inl_mem_disjSum.mp (mem_coe.mp h)
      exact F4 (mem_filter.mp h').2 rfl
    · have h' := inr_mem_disjSum.mp (mem_coe.mp h)
      obtain ⟨v, i⟩ := p
      exact F5 (mem_filter.mp h').2 i
  have := Set.ncard_le_ncard hF (Set.toFinite U)
  rw [Set.ncard_coe_finset, card_disjSum, card_dart_fst_mem, card_inner_mem] at this
  exact this

omit [DecidableEq V] in
open Classical in
theorem not_isTutteViolator_iff_le {U' : Set (GV G f)} :
    (gadget G f).IsTutteViolator U' ↔ U'.ncard < (del (gadget G f) U').oddComponents.ncard :=
  Iff.rfl

open Classical in
variable (G f) in
/-- Sufficiency in Tutte's f-factor theorem (classical formulation). -/
theorem exists_factor_of_condition
    (h : ∀ S T : Finset V, Disjoint S T → (oddCount G f S T : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ)) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, #{u | H.Adj v u} = f v := by
  have hf : ∀ v, f v ≤ G.degree v := by
    intro v
    have h1 := h ∅ {v} (disjoint_empty_left _)
    have h2 := card_adj_split (G := G) v ∅
    simp only [sum_empty, sum_singleton, zero_sub] at h1
    have h3 : (#{u | G.Adj v u ∧ u ∈ (∅ : Finset V)}) = 0 := by simp
    have h4 : (0 : ℤ) ≤ oddCount G f ∅ {v} := Nat.cast_nonneg _
    omega
  by_cases hM : ∃ M : (gadget G f).Subgraph, M.IsPerfectMatching
  · obtain ⟨M, hM⟩ := hM
    exact exists_factor_of_matching hf M hM
  exfalso
  have hviol : ∃ U, (gadget G f).IsTutteViolator U := by
    by_contra hno
    push Not at hno
    exact hM (tutte.mpr hno)
  obtain ⟨U, hU, hmin⟩ := exists_min_violator _ hviol
  have hodd := ncard_odd_le hmin hf
  have hUc := card_le_ncard_U (U := U)
  have hU' := (not_isTutteViolator_iff_le).mp hU
  have hyp := h (Sset G f U) (Tset G f U) disjoint_Sset_Tset
  rw [card_dart_fst_snd_mem, card_inner_mem] at hodd
  have hsplit : ∀ t, (#{u | G.Adj t u ∧ u ∈ Sset G f U} : ℤ) +
      (#{u | G.Adj t u ∧ u ∉ Sset G f U} : ℤ) = G.degree t := by
    intro t; exact_mod_cast card_adj_split t (Sset G f U)
  have hsub : ∀ s : Finset V, ((∑ v ∈ s, (G.degree v - f v) : ℕ) : ℤ) =
      ∑ v ∈ s, ((G.degree v : ℤ) - f v) := by
    intro s
    rw [Nat.cast_sum]
    exact sum_congr rfl (fun v _ => Nat.cast_sub (hf v))
  have hodd' : ((del (gadget G f) U).oddComponents.ncard : ℤ) ≤
      oddCount G f (Sset G f U) (Tset G f U) +
      ∑ t ∈ Tset G f U, (#{u | G.Adj t u ∧ u ∈ Sset G f U} : ℤ) +
      ∑ v ∈ Sset G f U, ((G.degree v : ℤ) - f v) := by
    rw [← hsub]; exact_mod_cast hodd
  have hUc' : ∑ v ∈ Sset G f U, (G.degree v : ℤ) + ∑ v ∈ Tset G f U, ((G.degree v : ℤ) - f v) ≤
      U.ncard := by
    rw [← hsub]; exact_mod_cast hUc
  have hU'' : (U.ncard : ℤ) < (del (gadget G f) U).oddComponents.ncard := by exact_mod_cast hU'
  have hT : ∑ t ∈ Tset G f U, (#{u | G.Adj t u ∧ u ∈ Sset G f U} : ℤ) +
      ∑ t ∈ Tset G f U, (#{u | G.Adj t u ∧ u ∉ Sset G f U} : ℤ) =
      ∑ t ∈ Tset G f U, (G.degree t : ℤ) := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun t _ => hsplit t)
  simp only [sum_sub_distrib] at hodd' hUc'
  linarith

end FFactor
