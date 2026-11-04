/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import LeanPool.CircuitComplexity.Digraph.Defs
public import Mathlib.Tactic

/-!
# The Gallai–Hasse–Roy–Vitaver theorem

An orientation of a simple graph `G` is a relation `o` such that every edge `uv` of `G` is
oriented in at least one direction (`o u v ∨ o v u`) and every arc is an edge of `G`. A directed
path with `m` vertices is an injective map `f : Fin m → V` with an arc from `f i` to `f (i + 1)`
for all consecutive indices.

* `GallaiRoy.colorable_of_orientation`: **Gallai (1968), Hasse (1965), Roy (1967),
  Vitaver (1962).** If some orientation of `G` has no directed path with more than `k` vertices,
  then `G` is `k`-colourable.
* `GallaiRoy.exists_orientation_of_colorable`: conversely, a `k`-colourable graph has an
  orientation without directed paths on more than `k` vertices. Together: the
  chromatic number is the minimum, over orientations, of the number of vertices of a longest
  directed path.
-/

@[expose] public section

open SimpleGraph

namespace GallaiRoy

variable {V : Type*}

/-- `o` is an orientation of `G`: every edge is oriented in at least one direction and every arc
is an edge. -/
def IsOrientation (G : SimpleGraph V) (o : V → V → Prop) : Prop :=
  (∀ u v, G.Adj u v → o u v ∨ o v u) ∧ ∀ u v, o u v → G.Adj u v

/-- `f` is a directed path of `o` with `m` vertices. -/
def IsDirectedPath (o : V → V → Prop) {m : ℕ} (f : Fin m → V) : Prop :=
  Function.Injective f ∧ ∀ (i : ℕ) (h : i + 1 < m), o (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩)

/-- The relation-based path predicate agrees with Lean Pool's digraph simple-path API. -/
theorem isDirectedPath_iff_isSimplePath (D : Digraph V) {m : ℕ} (f : Fin m → V) :
    IsDirectedPath D.Adj f ↔ D.IsSimplePath f := by
  constructor
  · rintro ⟨hinj, hstep⟩
    exact ⟨fun i hi => hstep i.val hi, hinj⟩
  · rintro ⟨hstep, hinj⟩
    exact ⟨hinj, fun i hi => hstep ⟨i, by omega⟩ hi⟩

private lemma transGen_of_mem_isChain {D : V → V → Prop} :
    ∀ {a : V} {l : List V}, List.IsChain D (a :: l) → ∀ w ∈ l, Relation.TransGen D a w
  | a, [], _, w, hw => by simp at hw
  | a, b :: l, h, w, hw => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact .single h.1
    · exact .head h.1 (transGen_of_mem_isChain h.2 w hw)

private lemma nodup_of_isChain {D : V → V → Prop} (hD : ∀ x, ¬ Relation.TransGen D x x) :
    ∀ {l : List V}, List.IsChain D l → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    refine List.nodup_cons.2 ⟨fun ha => hD a (transGen_of_mem_isChain h a ha), ?_⟩
    exact nodup_of_isChain hD h.tail

private lemma isDirectedPath_of_isChain {D o : V → V → Prop} (hDo : ∀ a b, D a b → o a b)
    (hD : ∀ x, ¬ Relation.TransGen D x x) {l : List V} (h : List.IsChain D l) :
    IsDirectedPath o l.get := by
  refine ⟨List.nodup_iff_injective_get.1 (nodup_of_isChain hD h), fun i hi => ?_⟩
  exact hDo _ _ (List.isChain_iff_getElem.1 h i hi)

private lemma exists_longer_of_transGen {D : V → V → Prop} {a b : V} (hab : Relation.TransGen D a b)
    {l : List V} (hl : List.IsChain D (b :: l)) :
    ∃ l', List.IsChain D (a :: l') ∧ l.length < l'.length := by
  induction hab using Relation.TransGen.head_induction_on generalizing l with
  | single h => exact ⟨b :: l, List.isChain_cons_cons.2 ⟨h, hl⟩, by simp⟩
  | head h _ ih =>
    obtain ⟨l', hl', hlen⟩ := ih hl
    exact ⟨_ :: l', List.isChain_cons_cons.2 ⟨h, hl'⟩, by simp; omega⟩

private lemma transGen_sup_edge {D : V → V → Prop} {u v a b : V}
    (h : Relation.TransGen (fun x y => D x y ∨ (x = u ∧ y = v)) a b) :
    Relation.TransGen D a b ∨ (Relation.ReflTransGen D a u ∧ Relation.ReflTransGen D v b) := by
  induction h with
  | single h =>
    rcases h with h | ⟨rfl, rfl⟩
    · exact .inl (.single h)
    · exact .inr ⟨.refl, .refl⟩
  | tail _ h ih =>
    rcases h with h | ⟨rfl, rfl⟩
    · rcases ih with ih | ⟨h1, h2⟩
      · exact .inl (ih.tail h)
      · exact .inr ⟨h1, h2.tail h⟩
    · rcases ih with ih | ⟨h1, _⟩
      · exact .inr ⟨ih.to_reflTransGen, .refl⟩
      · exact .inr ⟨h1, .refl⟩

/-- **Gallai–Hasse–Roy–Vitaver.** If an orientation of a finite graph has no directed path on more
than `k` vertices, the graph is `k`-colourable. -/
theorem colorable_of_orientation [Finite V] (G : SimpleGraph V) (o : V → V → Prop)
    (ho : IsOrientation G o) (k : ℕ)
    (hk : ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k) : G.Colorable k := by
  classical
  -- a maximal acyclic sub-relation of `o`
  obtain ⟨D, ⟨hDo, hDac⟩, hmax⟩ := (Set.toFinite
    {D : V → V → Prop | (∀ a b, D a b → o a b) ∧ ∀ x, ¬ Relation.TransGen D x x}).exists_maximal
    ⟨fun _ _ => False, fun _ _ h => h.elim, fun x h => by
      cases h with | single h => exact h | tail _ h => exact h⟩
  have hbound : ∀ {v : V} {l : List V}, List.IsChain D (v :: l) → l.length + 1 ≤ k := by
    intro v l hl
    simpa using hk _ _ (isDirectedPath_of_isChain hDo hDac hl)
  let P : V → ℕ → Prop := fun v m => ∃ l : List V, List.IsChain D (v :: l) ∧ l.length = m
  let h : V → ℕ := fun v => Nat.findGreatest (P v) k
  have hP0 : ∀ v, P v 0 := fun v => ⟨[], by simp, rfl⟩
  have hspec : ∀ v, P v (h v) := fun v => Nat.findGreatest_spec (Nat.zero_le _) (hP0 v)
  have hlt : ∀ v, h v < k := by
    intro v
    obtain ⟨l, hl, hlen⟩ := hspec v
    have := hbound hl
    omega
  have hmono : ∀ {a b : V}, Relation.TransGen D a b → h b < h a := by
    intro a b hab
    obtain ⟨l, hl, hlen⟩ := hspec b
    obtain ⟨l', hl', hlen'⟩ := exists_longer_of_transGen hab hl
    have : l'.length ≤ h a :=
      Nat.le_findGreatest (by have := hbound hl'; omega) ⟨l', hl', rfl⟩
    omega
  have key : ∀ {u v : V}, o u v → u ≠ v → h u ≠ h v := by
    intro u v huv hne
    by_cases hD : D u v
    · exact (hmono (.single hD)).ne'
    · have hvu : Relation.ReflTransGen D v u := by
        by_contra hvu
        have hmem : (fun x y => D x y ∨ (x = u ∧ y = v)) ∈
            {D : V → V → Prop | (∀ a b, D a b → o a b) ∧ ∀ x, ¬ Relation.TransGen D x x} := by
          refine ⟨fun a b hab => ?_, fun x hx => ?_⟩
          · rcases hab with hab | ⟨rfl, rfl⟩
            · exact hDo a b hab
            · exact huv
          · rcases transGen_sup_edge hx with hx | ⟨h1, h2⟩
            · exact hDac x hx
            · exact hvu (h2.trans h1)
        have := hmax hmem (fun a b hab => Or.inl hab)
        exact hD (this u v (Or.inr ⟨rfl, rfl⟩))
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hvu with h1 | h1
      · exact absurd h1 hne
      · exact (hmono h1).ne
  refine ⟨Coloring.mk (fun v => ⟨h v, hlt v⟩) fun {u v} huv => ?_⟩
  intro heq
  have heq' : h u = h v := congrArg Fin.val heq
  rcases ho.1 u v huv with h1 | h1
  · exact key h1 huv.ne heq'
  · exact key h1 huv.ne.symm heq'.symm

/-- Conversely, a `k`-colourable graph has an orientation without directed paths on more than `k`
vertices (orient every edge towards the larger colour). -/
theorem exists_orientation_of_colorable (G : SimpleGraph V) (k : ℕ) (h : G.Colorable k) :
    ∃ o : V → V → Prop, IsOrientation G o ∧
      ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k := by
  obtain ⟨c⟩ := h
  refine ⟨fun u v => G.Adj u v ∧ c u < c v, ⟨fun u v huv => ?_, fun u v h => h.1⟩, ?_⟩
  · rcases lt_or_gt_of_ne (c.valid huv) with h | h
    · exact .inl ⟨huv, h⟩
    · exact .inr ⟨huv.symm, h⟩
  · intro m f hf
    cases m with
    | zero => exact Nat.zero_le _
    | succ n =>
    have hmono : StrictMono (fun i : Fin (n + 1) => c (f i)) := by
      refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      have := hf.2 i.1 (by omega)
      exact this.2
    simpa using Fintype.card_le_of_injective _ hmono.injective

end GallaiRoy
