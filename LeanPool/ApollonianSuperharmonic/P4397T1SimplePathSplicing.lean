/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Pairwise


-- [TABLET NODE: P4397T1SimplePathSplicing]

/-!
# P4397T1SimplePathSplicing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4397T1SimplePathSplicing {α : Type*}
    (g k : List α) (a b : α)
    (hg : g.Nodup) (hk : k.Nodup) (hgl : 2 ≤ g.length) (hkl : 2 ≤ k.length)
    (hga : g.head? = some a) (hgb : g.getLast? = some b)
    (hkb : k.head? = some b) (hka : k.getLast? = some a)
    (hmeet : ∀ z, z ∈ g → z ∈ k → z = a ∨ z = b)
    (hedge : ∀ u v, (u, v) ∈ g.zip g.tail →
      (u, v) ∉ k.zip k.tail ∧ (v, u) ∉ k.zip k.tail) :
    let p := g.dropLast ++ k.dropLast
    p.Nodup ∧ 3 ≤ p.length ∧
      ∃ x y, p.head? = some x ∧ p.getLast? = some y ∧
        (p.zip p.tail) ++ [(y, x)] = (g.zip g.tail) ++ (k.zip k.tail) ∧
        (∀ z ∈ p, z ∈ g ∨ z ∈ k) := by
-- BODY
  have form (l : List α) (u v : α) (hlen : 2 ≤ l.length)
      (hh : l.head? = some u) (hl : l.getLast? = some v) :
      ∃ m : List α, l = (u :: m) ++ [v] := by
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hh
    have ht : t ≠ [] := by intro he; simp [he] at hlen
    have htl : t.getLast? = some v := by
      cases t with
      | nil => exact (ht rfl).elim
      | cons c cs => simpa using hl
    obtain ⟨m, hm⟩ := List.getLast?_eq_some_iff.mp htl
    exact ⟨m, by simp [hm]⟩
  obtain ⟨m, rfl⟩ := form g a b hgl hga hgb
  obtain ⟨n, rfl⟩ := form k b a hkl hkb hka
  dsimp only
  simp only [List.dropLast_concat]
  have hnd : ((a :: m) ++ (b :: n)).Nodup := by
    apply (List.nodup_append.mp hg).1.append (List.nodup_append.mp hk).1
    apply List.disjoint_left.mpr
    intro z hz hz'
    rcases hmeet z (by simp only [List.mem_append]; exact Or.inl hz)
      (by simp only [List.mem_append]; exact Or.inl hz') with hza | hzb
    · exact (List.nodup_append.mp hk).2.2 z hz' a (by simp) hza
    · exact (List.nodup_append.mp hg).2.2 z hz b (by simp) hzb
  have hlen : 3 ≤ ((a :: m) ++ (b :: n)).length := by
    cases m with
    | nil =>
      cases n with
      | nil => exact ((hedge a b (by simp)).2 (by simp)).elim
      | cons c cs => simp
    | cons c cs => simp; omega
  let y := (b :: n).getLast (by simp)
  have hy : (b :: n).getLast? = some y := by
    exact List.getLast?_eq_some_getLast (by simp)
  have hpLast : ((a :: m) ++ (b :: n)).getLast? = some y := by
    simp only [List.getLast?_append, hy, Option.some_or]
  have close_edges (l : List α) (v u : α) (hl : l.getLast? = some v) :
      l.zip (l.tail ++ [u]) = l.zip l.tail ++ [(v, u)] := by
    induction l with
    | nil => simp at hl
    | cons c l ih =>
      cases l with
      | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hl
               subst v
               rfl
      | cons d ds =>
        have hlast : (d :: ds).getLast? = some v := by simpa using hl
        simpa only [List.tail_cons, List.cons_append, List.zip_cons_cons] using
          congrArg (List.cons (c, d)) (ih hlast)
  have trim_zip (l : List α) (u v : α) :
      ((u :: l) ++ [v]).zip (((u :: l) ++ [v]).tail) =
        (u :: l).zip (l ++ [v]) := by
    simpa only [List.tail_append, List.tail_cons, List.isEmpty_cons, Bool.false_eq_true,
      ↓reduceIte,
      List.append_nil, List.zip_nil_right] using
      (List.zip_append (l₁ := u :: l) (r₁ := [v]) (l₂ := l ++ [v]) (r₂ := [])
        (by simp))
  refine ⟨hnd, hlen, a, y, by simp, hpLast, ?_, ?_⟩
  · rw [← close_edges _ y a hpLast, trim_zip m a b, trim_zip n b a]
    have ht : (((a :: m) ++ (b :: n)).tail ++ [a]) =
        (m ++ [b]) ++ (n ++ [a]) := by simp [List.append_assoc]
    rw [ht]
    exact List.zip_append (by simp)
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact Or.inl (by simp only [List.mem_append]; exact Or.inl hz)
    · exact Or.inr (by simp only [List.mem_append]; exact Or.inl hz)

end ApollonianSuperharmonic

end
