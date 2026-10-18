/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!

Imported from [jtraverso/euler-petersen](https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean), registered as PALOMAR-2026-10-16-000016. The original proof is retained; module paths and imports are adapted for this collection.

# Teorema de Euler (caracterización de grafos eulerianos)

Un grafo simple finito y conexo admite un circuito euleriano (un camino cerrado que recorre
cada arista exactamente una vez) si y sólo si todos sus vértices tienen grado par.

Mathlib ya contiene la dirección necesaria (`SimpleGraph.Walk.IsEulerian.even_degree_iff`);
aquí probamos la suficiencia (listada como TODO en `Mathlib/Combinatorics/SimpleGraph/Trails.lean`).

## Estrategia (argumento del trail maximal)

Sea `p : G.Walk u v` un trail (camino sin aristas repetidas).
* Si `u ≠ v`, el número de aristas de `p` incidentes en `v` es impar, mientras que `deg v` es par;
  luego hay una arista en `v` no usada y `p` se extiende.
* Si `u = v` y `p` no es euleriano, por conexidad algún vértice `x` de `p` tiene una arista no
  usada; rotando `p` para que empiece en `x`, se extiende.
Como la longitud de un trail está acotada por `|E|`, algún trail no se puede extender, y por lo
anterior ese trail es un circuito euleriano.
-/

@[expose] public section

namespace SimpleGraph

open Walk

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Si el número de aristas de un trail incidentes en `x` no tiene la paridad de `deg x`,
hay una arista en `x` que el trail no usa. -/
lemma exists_adj_not_mem_edges_of_not_even {u v x : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hx : Even (G.degree x)) (hodd : ¬ Even (p.edges.countP fun e => x ∈ e)) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by
  by_contra! h
  apply hodd
  have hinc : G.incidenceFinset x = hp.edgesFinset.filter (x ∈ ·) := by
    ext e
    simp only [mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq, Finset.mem_filter,
      Finset.mem_mk, Multiset.mem_coe]
    constructor
    · rintro ⟨he, hxe⟩
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
      exact ⟨h y he, hxe⟩
    · rintro ⟨hm, hxe⟩
      exact ⟨p.edges_subset_edgeSet hm, hxe⟩
  have hcard : p.edges.countP (fun e => x ∈ e) = G.degree x := by
    rw [← card_incidenceFinset_eq_degree, hinc, ← Multiset.coe_countP,
      Multiset.countP_eq_card_filter]
    rfl
  rwa [hcard]

omit [Fintype V] [DecidableRel G.Adj] in
/-- En un grafo conexo, si un trail no es euleriano, algún vértice del trail tiene
una arista que el trail no usa. -/
lemma exists_mem_support_adj_not_mem_edges (hconn : G.Connected) {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) (hne : ¬ p.IsEulerian) :
    ∃ x ∈ p.support, ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by
  by_contra! h
  apply hne
  -- Todo vértice alcanzable desde el soporte está en el soporte.
  have hclosed : ∀ a b (q : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hab q ih =>
      intro ha
      exact ih (p.snd_mem_support_of_mem_edges (h _ ha _ hab))
  have hall : ∀ w, w ∈ p.support := fun w =>
    hclosed u w (hconn.preconnected u w).some p.start_mem_support
  refine hp.isEulerian_of_forall_mem fun e he => ?_
  induction e using Sym2.ind with
  | _ a b => exact h a (hall a) b he

/-- Lema de extensión: todo trail, o bien da lugar a un circuito euleriano, o bien se extiende
a un trail estrictamente más largo. -/
lemma exists_isEulerian_or_longer_trail (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    (∃ w, ∃ q : G.Walk w w, q.IsEulerian) ∨
      ∃ a b, ∃ q : G.Walk a b, q.IsTrail ∧ p.length < q.length := by
  by_cases huv : u = v
  · subst huv
    by_cases he : p.IsEulerian
    · exact Or.inl ⟨u, p, he⟩
    right
    obtain ⟨x, hx, y, hxy, hnot⟩ := exists_mem_support_adj_not_mem_edges hconn hp he
    refine ⟨y, x, cons hxy.symm (p.rotate x hx).reverse, ?_, ?_⟩
    · rw [isTrail_cons]
      refine ⟨((isTrail_rotate hx).mpr hp).reverse, ?_⟩
      rw [edges_reverse, List.mem_reverse, (rotate_edges p x hx).mem_iff, Sym2.eq_swap]
      exact hnot
    · rw [length_cons, length_reverse, ← length_edges, ← length_edges,
        (rotate_edges p x hx).perm.length_eq]
      omega
  · right
    have hodd : ¬ Even (p.edges.countP fun e => v ∈ e) := by
      rw [hp.even_countP_edges_iff v]
      simp [huv]
    obtain ⟨y, hvy, hnot⟩ := exists_adj_not_mem_edges_of_not_even hp (heven v) hodd
    refine ⟨y, u, cons hvy.symm p.reverse, ?_, ?_⟩
    · rw [isTrail_cons]
      refine ⟨hp.reverse, ?_⟩
      rw [edges_reverse, List.mem_reverse, Sym2.eq_swap]
      exact hnot
    · simp

/-- **Euler (suficiencia).** Un grafo finito conexo con todos sus grados pares admite un
circuito euleriano. -/
theorem exists_isEulerian_of_forall_even_degree (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) : ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by
  by_contra hno
  have key : ∀ k : ℕ, ∃ a b, ∃ q : G.Walk a b, q.IsTrail ∧ k ≤ q.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := hconn.nonempty
      exact ⟨v, v, nil, by simp, le_rfl⟩
    | succ k ih =>
      obtain ⟨a, b, q, hq, hk⟩ := ih
      rcases exists_isEulerian_or_longer_trail hconn heven q hq with h | ⟨a', b', q', hq', hlt⟩
      · exact absurd h hno
      · exact ⟨a', b', q', hq', by omega⟩
  obtain ⟨a, b, q, hq, hk⟩ := key (G.edgeFinset.card + 1)
  have := hq.length_le_card_edgeFinset
  omega

/-- **Teorema de Euler.** Un grafo finito conexo admite un circuito euleriano si y sólo si
todos sus vértices tienen grado par. -/
theorem exists_isEulerian_iff_forall_even_degree (hconn : G.Connected) :
    (∃ u, ∃ p : G.Walk u u, p.IsEulerian) ↔ ∀ v, Even (G.degree v) := by
  constructor
  · rintro ⟨u, p, hp⟩ v
    exact hp.even_degree_iff.mpr fun h => absurd rfl h
  · exact exists_isEulerian_of_forall_even_degree hconn

end SimpleGraph
