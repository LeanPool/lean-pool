/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.BigOperators.Group.List.Basic

-- [TABLET NODE: P3221T2ConnectedPathIntegration]

/-!
# P3221T2ConnectedPathIntegration

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3221T2ConnectedPathIntegration {α : Type*}
    (G : SimpleGraph α) (x₀ : α)
    (hconn : ∀ x, Nonempty (G.Walk x₀ x))
    (D : α → α → ℤ)
    (hanti : ∀ a b, G.Adj a b → D b a = -D a b)
    (hclosed : ∀ x (p : G.Walk x x),
      (p.darts.map (fun d => D d.fst d.snd)).sum = 0) :
    ∃ g : α → ℤ, g x₀ = 0 ∧
      (∀ a b, G.Adj a b → g b - g a = D a b) ∧
      ∀ g' : α → ℤ,
        (∀ a b, G.Adj a b → g' b - g' a = D a b) →
        ∃ c : ℤ, ∀ x, g' x - g x = c := by
-- BODY
  classical
  let I {u v : α} (p : G.Walk u v) : ℤ :=
    (p.darts.map (fun d => D d.fst d.snd)).sum
  have iappend {u v w : α} (p : G.Walk u v) (q : G.Walk v w) :
      I (p.append q) = I p + I q := by
    simp [I, SimpleGraph.Walk.darts_append]
  have ireverse {u v : α} (p : G.Walk u v) : I p.reverse = -I p := by
    have hneg (l : List G.Dart) :
        (l.map (fun d => D d.snd d.fst)).sum =
          -(l.map (fun d => D d.fst d.snd)).sum := by
      induction l with
      | nil => simp
      | cons d l ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [hanti d.fst d.snd d.adj, ih]
          omega
    simpa [I, SimpleGraph.Walk.darts_reverse, List.map_map,
      Function.comp_def, SimpleGraph.Dart.symm] using hneg p.darts
  let P (x : α) : G.Walk x₀ x := Classical.choice (hconn x)
  let g (x : α) : ℤ := I (P x)
  have ipath (x : α) (q : G.Walk x₀ x) : I q = g x := by
    have hz := hclosed x₀ (q.append (P x).reverse)
    change I (q.append (P x).reverse) = 0 at hz
    rw [iappend, ireverse] at hz
    dsimp [g]
    omega
  have hgzero : g x₀ = 0 := by
    have hz := ipath x₀ SimpleGraph.Walk.nil
    simpa [I] using hz.symm
  have hgedge : ∀ a b, G.Adj a b → g b - g a = D a b := by
    intro a b hab
    have hp := ipath b ((P a).append hab.toWalk)
    rw [iappend] at hp
    have he : I hab.toWalk = D a b := by simp [I]
    rw [he] at hp
    change g a + D a b = g b at hp
    omega
  refine ⟨g, hgzero, hgedge, ?_⟩
  intro g' hg'
  have telescope {u v : α} (p : G.Walk u v) : g' v - g' u = I p := by
    induction p with
    | nil => simp [I]
    | @cons u v w hab p ih =>
        have he := hg' u v hab
        have hi : I (SimpleGraph.Walk.cons hab p) = D u v + I p := by
          simp [I]
        rw [hi]
        omega
  refine ⟨g' x₀, ?_⟩
  intro x
  have ht := telescope (P x)
  change g' x - g' x₀ = g x at ht
  omega

end ApollonianSuperharmonic

end
