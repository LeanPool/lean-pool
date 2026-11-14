/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.NodupPathEdgeIndices

public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: P3161T2PathExhaustion]

/-!
# P3161T2PathExhaustion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3161T2PathExhaustion
    {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
    {x y : GaussianInt} (hpath : SimpleGridPathBetween V E x y)
    (walk : List GaussianInt)
    (hhead : walk.head? = some x) (hlast : walk.getLast? = some y)
    (hedges : ∀ a b : GaussianInt, ∀ l r : List GaussianInt,
      walk = l ++ a :: b :: r → {a, b} ∈ E) :
    ∀ z ∈ V, z ∈ walk := by
-- BODY
  classical
  rcases hpath with ⟨p, hp, hlen, hx, hy, hV, _, hE⟩
  have hindex (a b : GaussianInt) (hab : {a, b} ∈ E) :=
    NodupPathEdgeIndices p hp a b ((hE {a, b}).mp hab)
  have hix : p.idxOf x = 0 := by
    cases p with
    | nil => simp at hlen
    | cons a r =>
      simp only [List.head?_cons, Option.some.injEq] at hx
      simp [hx]
  have hpform : p.dropLast ++ [y] = p :=
    List.dropLast_append_getLast? y (by simp [hy])
  have hyabsent : y ∉ p.dropLast := by
    have hnd := hp
    rw [← hpform, List.nodup_append] at hnd
    intro h
    exact hnd.2.2 y h y (by simp) rfl
  have hiy : p.idxOf y = p.length - 1 := by
    rw [← hpform, List.idxOf_append]
    simp [hyabsent]
  intro z hz
  have hzmem : z ∈ p := by simpa [hV] using hz
  have hiz : p.idxOf z < p.length := List.idxOf_lt_length_of_mem hzmem
  by_cases hzx : z = x
  · subst z
    exact List.mem_of_mem_head? (by simp [hhead])
  have hizpos : 0 < p.idxOf z := by
    have hne : p.idxOf z ≠ p.idxOf x := by
      intro h
      exact hzx ((List.idxOf_inj hzmem).mp h)
    omega
  by_contra hzw
  have propagate : ∀ (w : List GaussianInt),
      (∀ a b : GaussianInt, ∀ l r : List GaussianInt,
        w = l ++ a :: b :: r → {a, b} ∈ E) →
      z ∉ w →
      (∀ a ∈ w.head?, p.idxOf a < p.idxOf z) →
      ∀ b ∈ w.getLast?, p.idxOf b < p.idxOf z := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      intro hw hznot ha
      cases w with
      | nil => simpa using ha
      | cons b w =>
        have hab := hindex a b (hw a b [] w rfl)
        have hia : p.idxOf a < p.idxOf z := ha a (by simp)
        have hbz : p.idxOf b ≠ p.idxOf z := by
          intro h
          have hb : b = z := ((List.idxOf_inj hzmem).mp h.symm).symm
          exact hznot (by simp [hb])
        have hib : p.idxOf b < p.idxOf z := by omega
        have hw' : ∀ c d : GaussianInt, ∀ l r : List GaussianInt,
            b :: w = l ++ c :: d :: r → {c, d} ∈ E := by
          intro c d l r h
          exact hw c d (a :: l) r (by simp [h, List.cons_append])
        have hznot' : z ∉ b :: w := by
          intro h
          exact hznot (List.mem_cons_of_mem a h)
        simpa using ih hw' hznot' (by simpa using hib)
  have hylt := propagate walk hedges hzw (by simpa [hhead, hix] using hizpos)
  have : p.idxOf y < p.idxOf z := hylt y (by simp [hlast])
  omega

end ApollonianSuperharmonic

end
