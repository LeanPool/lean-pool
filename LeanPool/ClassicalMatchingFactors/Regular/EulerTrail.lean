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

Imported from [jtraverso/euler-petersen](https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean), registered as PALOMAR-2026-10-16-000016. The parity proof is retained, with shared circuit helpers and compatibility results consolidated here to avoid parallel circuit-existence proofs.

# Circuitos y caminos eulerianos

Un grafo finito conexo admite un trail euleriano (camino que recorre cada arista exactamente una
vez, no necesariamente cerrado) si y sólo si tiene 0 ó 2 vértices de grado impar. Más
precisamente, si los vértices de grado impar son exactamente `a` y `b` (`a ≠ b`), hay un trail
euleriano de `a` a `b`; si no hay vértices de grado impar, hay un circuito euleriano por
cualquier vértice.

Mathlib contiene la dirección necesaria (`SimpleGraph.Walk.IsEulerian.card_odd_degree`); aquí
probamos la suficiencia (el TODO de `Mathlib/Combinatorics/SimpleGraph/Trails.lean`).

## Estrategia

Fijamos `a, b` con la condición de paridad
`Even (deg x) ↔ (a ≠ b → x ≠ a ∧ x ≠ b)` (la misma que satisface un trail de `a` a `b`).
Tomamos un trail `p : a → b` de longitud máxima. Si no es euleriano, por conexidad hay un vértice
`x` de `p` con una arista libre. Las aristas de `p` tienen, en cada vértice, la misma paridad que
el grado, así que en el grafo de aristas no usadas todos los grados son pares; de ahí sale un
trail cerrado `c` en `x`, de longitud positiva, disjunto de `p`. Insertando `c` en `p` en `x`
se obtiene un trail `a → b` más largo: contradicción.
-/

@[expose] public section

namespace SimpleGraph

open Walk

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Si una lista sin repeticiones de aristas contiene todas las aristas en `x`, el número de
sus aristas incidentes en `x` es `deg x`. -/
lemma countP_eq_degree_of_forall_adj_mem {L : List (Sym2 V)} (hL : L.Nodup)
    (hsub : ∀ e ∈ L, e ∈ G.edgeSet) {x : V} (h : ∀ y, G.Adj x y → s(x, y) ∈ L) :
    L.countP (fun e => x ∈ e) = G.degree x := by
  have hinc : G.incidenceFinset x = (⟨(L : Multiset (Sym2 V)), hL⟩ : Finset _).filter (x ∈ ·) := by
    ext e
    simp only [mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq, Finset.mem_filter]
    constructor
    · rintro ⟨he, hxe⟩
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
      exact ⟨h y he, hxe⟩
    · rintro ⟨hm, hxe⟩
      exact ⟨hsub _ hm, hxe⟩
  rw [← card_incidenceFinset_eq_degree, hinc, ← Multiset.coe_countP,
    Multiset.countP_eq_card_filter]
  rfl

/-- Si una lista sin repeticiones de aristas no tiene `deg x` aristas en `x`, falta alguna
arista en `x`. -/
lemma exists_adj_not_mem_of_countP_ne {L : List (Sym2 V)} (hL : L.Nodup)
    (hsub : ∀ e ∈ L, e ∈ G.edgeSet) {x : V} (h : L.countP (fun e => x ∈ e) ≠ G.degree x) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ L := by
  by_contra! h'
  exact h (countP_eq_degree_of_forall_adj_mem hL hsub h')

/-- Si el número de aristas de un trail incidentes en `x` no tiene la paridad de `deg x`,
hay una arista en `x` que el trail no usa. -/
lemma exists_adj_not_mem_edges_of_not_even {u v x : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hx : Even (G.degree x)) (hodd : ¬ Even (p.edges.countP fun e => x ∈ e)) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by
  apply exists_adj_not_mem_of_countP_ne hp.edges_nodup (fun e he => p.edges_subset_edgeSet he)
  intro hcount
  apply hodd
  rwa [hcount]

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

/-- Sea `S` una lista de aristas que en cada vértice tiene la paridad del grado. Si `x` tiene
una arista fuera de `S`, existe un trail cerrado en `x`, de longitud positiva, que no usa
aristas de `S`. -/
lemma exists_closed_trail_avoiding {S : List (Sym2 V)} (hS : S.Nodup)
    (hSsub : ∀ e ∈ S, e ∈ G.edgeSet)
    (hpar : ∀ y, Even (S.countP fun e => y ∈ e) ↔ Even (G.degree y))
    {x y₀ : V} (hxy : G.Adj x y₀) (hnot : s(x, y₀) ∉ S) :
    ∃ c : G.Walk x x, c.IsTrail ∧ 0 < c.length ∧ ∀ e ∈ c.edges, e ∉ S := by
  by_contra hno
  have key : ∀ k : ℕ, ∃ v, ∃ q : G.Walk x v,
      q.IsTrail ∧ 0 < q.length ∧ (∀ e ∈ q.edges, e ∉ S) ∧ k ≤ q.length := by
    intro k
    induction k with
    | zero => exact ⟨y₀, cons hxy nil, by simp, by simp, by simpa using hnot, by simp⟩
    | succ k ih =>
      obtain ⟨v, q, hq, hpos, hdisj, hk⟩ := ih
      by_cases hv : v = x
      · subst hv
        exact absurd ⟨q, hq, hpos, hdisj⟩ hno
      have hqodd : ¬ Even (q.edges.countP fun e => v ∈ e) := by
        rw [hq.even_countP_edges_iff]
        simp [Ne.symm hv]
      have hnd : (S ++ q.edges).Nodup :=
        List.nodup_append.mpr ⟨hS, hq.edges_nodup, fun a ha b hb hab => hdisj b hb (hab ▸ ha)⟩
      have hsub : ∀ e ∈ S ++ q.edges, e ∈ G.edgeSet := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hSsub e he
        · exact q.edges_subset_edgeSet he
      have hne : (S ++ q.edges).countP (fun e => v ∈ e) ≠ G.degree v := by
        intro heq
        have := hpar v
        rw [← heq, List.countP_append, Nat.even_add] at this
        tauto
      obtain ⟨w, hvw, hw⟩ := exists_adj_not_mem_of_countP_ne hnd hsub hne
      rw [List.mem_append, not_or] at hw
      refine ⟨w, (cons hvw.symm q.reverse).reverse, ?_, ?_, ?_, ?_⟩
      · refine ((isTrail_cons _ _).mpr ⟨hq.reverse, ?_⟩).reverse
        rw [edges_reverse, List.mem_reverse, Sym2.eq_swap]
        exact hw.2
      · simp
      · intro e he
        simp only [edges_reverse, edges_cons, List.reverse_cons, List.reverse_reverse,
          List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hdisj e he
        · rw [Sym2.eq_swap]
          exact hw.1
      · simp
        omega
  obtain ⟨v, q, hq, -, -, hk⟩ := key (G.edgeFinset.card + 1)
  have := hq.length_le_card_edgeFinset
  omega

/-- **Euler (suficiencia, versión con extremos).** Si `G` es conexo y los vértices de grado
impar son exactamente `a` y `b` (o no hay ninguno, cuando `a = b`), existe un trail euleriano
de `a` a `b`. -/
theorem exists_isEulerian_of_parity (hconn : G.Connected) {a b : V}
    (h : ∀ x, Even (G.degree x) ↔ (a ≠ b → x ≠ a ∧ x ≠ b)) :
    ∃ p : G.Walk a b, p.IsEulerian := by
  by_contra hno
  -- Todo trail `a → b` se extiende a uno más largo.
  have ext : ∀ p : G.Walk a b, p.IsTrail → ∃ q : G.Walk a b, q.IsTrail ∧ p.length < q.length := by
    intro p hp
    obtain ⟨x, hx, y, hxy, hnot⟩ :=
      exists_mem_support_adj_not_mem_edges hconn hp fun he => hno ⟨p, he⟩
    have hpar : ∀ z, Even (p.edges.countP fun e => z ∈ e) ↔ Even (G.degree z) := fun z => by
      rw [hp.even_countP_edges_iff, h]
    obtain ⟨c, hc, hcpos, hcdisj⟩ := exists_closed_trail_avoiding hp.edges_nodup
      (fun e he => p.edges_subset_edgeSet he) hpar hxy hnot
    have hedges : p.edges = (p.takeUntil x hx).edges ++ (p.dropUntil x hx).edges := by
      rw [← edges_append, p.take_spec hx]
    have hlen : p.length = (p.takeUntil x hx).length + (p.dropUntil x hx).length := by
      rw [← length_append, p.take_spec hx]
    refine ⟨(p.takeUntil x hx).append (c.append (p.dropUntil x hx)), ?_, ?_⟩
    · have hperm : List.Perm ((p.takeUntil x hx).edges ++ (c.edges ++ (p.dropUntil x hx).edges))
          (c.edges ++ p.edges) := by
        rw [hedges, ← List.append_assoc, ← List.append_assoc]
        exact List.perm_append_comm.append_right _
      rw [isTrail_def, edges_append, edges_append, hperm.nodup_iff]
      exact List.nodup_append.mpr
        ⟨hc.edges_nodup, hp.edges_nodup, fun e he e' he' hee => hcdisj e he (hee ▸ he')⟩
    · rw [length_append, length_append]
      omega
  -- Existe algún trail `a → b`.
  have h0 : ∃ p : G.Walk a b, p.IsTrail := by
    obtain ⟨q⟩ := hconn.preconnected a b
    exact ⟨q.bypass, q.bypass_isPath.isTrail⟩
  have key : ∀ k : ℕ, ∃ q : G.Walk a b, q.IsTrail ∧ k ≤ q.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨p, hp⟩ := h0
      exact ⟨p, hp, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨q, hq, hk⟩ := ih
      obtain ⟨q', hq', hlt⟩ := ext q hq
      exact ⟨q', hq', by omega⟩
  obtain ⟨q, hq, hk⟩ := key (G.edgeFinset.card + 1)
  have := hq.length_le_card_edgeFinset
  omega

/-- En un grafo conexo con todos los grados pares hay un circuito euleriano que pasa por
cualquier vértice prefijado. -/
theorem exists_isEulerian_circuit_at (hconn : G.Connected) (heven : ∀ v, Even (G.degree v))
    (a : V) : ∃ p : G.Walk a a, p.IsEulerian :=
  exists_isEulerian_of_parity hconn fun x => iff_of_true (heven x) fun h => absurd rfl h

/-- **Euler (suficiencia).** Un grafo finito conexo con todos sus grados pares admite un
circuito euleriano. -/
theorem exists_isEulerian_of_forall_even_degree (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) : ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by
  obtain ⟨u⟩ := hconn.nonempty
  obtain ⟨p, hp⟩ := exists_isEulerian_circuit_at hconn heven u
  exact ⟨u, p, hp⟩

/-- **Teorema de Euler.** Un grafo finito conexo admite un circuito euleriano si y sólo si
todos sus vértices tienen grado par. -/
theorem exists_isEulerian_iff_forall_even_degree (hconn : G.Connected) :
    (∃ u, ∃ p : G.Walk u u, p.IsEulerian) ↔ ∀ v, Even (G.degree v) := by
  constructor
  · rintro ⟨u, p, hp⟩ v
    exact hp.even_degree_iff.mpr fun h => absurd rfl h
  · exact exists_isEulerian_of_forall_even_degree hconn

/-- Compatibility form of circuit existence, with the original trail-extension conclusion. -/
lemma exists_isEulerian_or_longer_trail (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) {u v : V} (p : G.Walk u v) (_hp : p.IsTrail) :
    (∃ w, ∃ q : G.Walk w w, q.IsEulerian) ∨
      ∃ a b, ∃ q : G.Walk a b, q.IsTrail ∧ p.length < q.length := by
  exact Or.inl (exists_isEulerian_of_forall_even_degree hconn heven)

/-- **Teorema de Euler (trails).** Un grafo finito conexo admite un trail euleriano si y sólo
si tiene 0 ó 2 vértices de grado impar. -/
theorem exists_isEulerian_walk_iff (hconn : G.Connected) :
    (∃ u v, ∃ p : G.Walk u v, p.IsEulerian) ↔
      Fintype.card {v | Odd (G.degree v)} = 0 ∨ Fintype.card {v | Odd (G.degree v)} = 2 := by
  constructor
  · rintro ⟨u, v, p, hp⟩
    exact hp.card_odd_degree
  · intro hcard
    rw [← Set.toFinset_card, Set.toFinset_ofPred] at hcard
    rcases hcard with h0 | h2
    · obtain ⟨a⟩ := hconn.nonempty
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact ⟨a, a, exists_isEulerian_circuit_at hconn
        (fun x => Nat.not_odd_iff_even.mp (h0 (Finset.mem_univ x))) a⟩
    · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2
      refine ⟨a, b, exists_isEulerian_of_parity hconn fun x => ?_⟩
      have hx := Finset.ext_iff.mp hs x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rw [← Nat.not_odd_iff_even, hx]
      simp [hab, not_or]

/-- Versión con extremos explícitos: si los únicos vértices de grado impar son `a ≠ b`, hay un
trail euleriano de `a` a `b`. -/
theorem exists_isEulerian_of_odd_iff (hconn : G.Connected) {a b : V} (hab : a ≠ b)
    (hodd : ∀ x, Odd (G.degree x) ↔ x = a ∨ x = b) : ∃ p : G.Walk a b, p.IsEulerian :=
  exists_isEulerian_of_parity hconn fun x => by
    rw [← Nat.not_odd_iff_even, hodd]
    simp [hab, not_or]

end SimpleGraph
