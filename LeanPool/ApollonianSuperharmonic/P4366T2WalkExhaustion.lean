/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3161T2PathExhaustion

-- [TABLET NODE: P4366T2WalkExhaustion]

/-!
# P4366T2WalkExhaustion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4366T2WalkExhaustion
    {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
    {x y : GaussianInt} (hpath : SimpleGridPathBetween V E x y)
    (walk : List GaussianInt)
    (hhead : walk.head? = some x) (hlast : walk.getLast? = some y)
    (hedges : ∀ a b : GaussianInt, ∀ l r : List GaussianInt,
      walk = l ++ a :: b :: r → {a, b} ∈ E) :
    (∀ z ∈ V, z ∈ walk) ∧
    ∀ e ∈ E, ∃ a b : GaussianInt, ∃ l r : List GaussianInt,
      walk = l ++ a :: b :: r ∧ e = {a, b} := by
-- BODY
  classical
  refine ⟨P3161T2PathExhaustion hpath walk hhead hlast hedges, ?_⟩
  rcases hpath with ⟨p, hp, hlen, hx, hy, hV, hsteps, hE⟩
  have hindex : ∀ a b, {a, b} ∈ E →
      p.idxOf a + 1 = p.idxOf b ∨ p.idxOf b + 1 = p.idxOf a := by
    intro a b hab
    rcases (hE {a, b}).mp hab with ⟨c, d, l, r, heq, hedge⟩
    have hnd := hp
    rw [heq, List.nodup_append] at hnd
    have hc : c ∉ l := by
      intro hc
      exact hnd.2.2 c hc c (by simp) rfl
    have hd : d ∉ l := by
      intro hd
      exact hnd.2.2 d hd d (by simp) rfl
    have hcd : c ≠ d := by
      have hcnot := (List.nodup_cons.mp hnd.2.1).1
      intro h
      exact hcnot (by simp [h])
    have hic : p.idxOf c = l.length := by
      simp [heq, List.idxOf_append, hc]
    have hid : p.idxOf d = l.length + 1 := by
      simp [heq, List.idxOf_append, hd, hcd, Nat.add_comm]
    have ha : a = c ∨ a = d := by
      have : a ∈ ({c, d} : Finset GaussianInt) := by rw [← hedge]; simp
      simpa using this
    have hb : b = c ∨ b = d := by
      have : b ∈ ({c, d} : Finset GaussianInt) := by rw [← hedge]; simp
      simpa using this
    have habne : a ≠ b := by
      intro h
      have hcmem : c ∈ ({a, b} : Finset GaussianInt) := by rw [hedge]; simp
      have hdmem : d ∈ ({a, b} : Finset GaussianInt) := by rw [hedge]; simp
      simp [h] at hcmem hdmem
      exact hcd (hcmem.trans hdmem.symm)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (habne rfl)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · exact False.elim (habne rfl)
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
  intro e he
  obtain ⟨c, d, l, r, hpEq, heEq⟩ := (hE e).mp he
  have hnd := hp
  rw [hpEq, List.nodup_append] at hnd
  have hcnot : c ∉ l := by
    intro hc
    exact hnd.2.2 c hc c (by simp) rfl
  have hdnot : d ∉ l := by
    intro hd
    exact hnd.2.2 d hd d (by simp) rfl
  have hcd : c ≠ d := by
    intro h
    exact (List.nodup_cons.mp hnd.2.1).1 (by simp [h])
  have hic : p.idxOf c = l.length := by
    simp [hpEq, List.idxOf_append, hcnot]
  have hid : p.idxOf d = l.length + 1 := by
    simp [hpEq, List.idxOf_append, hdnot, hcd, Nat.add_comm]
  have hcmem : c ∈ p := by simp [hpEq]
  have hdmem : d ∈ p := by simp [hpEq]
  by_contra hmissing
  have hnoedge : ∀ a b, ∀ pre post : List GaussianInt,
      walk = pre ++ a :: b :: post → ({a, b} : Finset GaussianInt) ≠ e := by
    intro a b pre post hw he'
    exact hmissing ⟨a, b, pre, post, hw, he'.symm⟩
  have propagate : ∀ (w : List GaussianInt),
      (∀ a b, ∀ pre post : List GaussianInt,
        w = pre ++ a :: b :: post → {a, b} ∈ E ∧ ({a, b} : Finset GaussianInt) ≠ e) →
      (∀ a ∈ w.head?, p.idxOf a ≤ l.length) →
      ∀ b ∈ w.getLast?, p.idxOf b ≤ l.length := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      intro hw ha
      cases w with
      | nil => simpa using ha
      | cons b w =>
        have hab := hw a b [] w rfl
        have hiab := hindex a b hab.1
        have hia : p.idxOf a ≤ l.length := ha a (by simp)
        have hib : p.idxOf b ≤ l.length := by
          by_contra hgt
          have hac : p.idxOf a = p.idxOf c := by omega
          have hbd : p.idxOf b = p.idxOf d := by omega
          have hac' : a = c := ((List.idxOf_inj hcmem).mp hac.symm).symm
          have hbd' : b = d := ((List.idxOf_inj hdmem).mp hbd.symm).symm
          exact hab.2 (by simpa [hac', hbd'] using heEq.symm)
        have hw' : ∀ c' d', ∀ pre post : List GaussianInt,
            b :: w = pre ++ c' :: d' :: post →
              {c', d'} ∈ E ∧ ({c', d'} : Finset GaussianInt) ≠ e := by
          intro c' d' pre post hw'
          exact hw c' d' (a :: pre) post (by simp [hw', List.cons_append])
        simpa using ih hw' (by simpa using hib)
  have hylt := propagate walk
    (fun a b pre post hw => ⟨hedges a b pre post hw, hnoedge a b pre post hw⟩)
    (by simp [hhead, hix]) y (by simp [hlast])
  have hlength : p.length = l.length + 2 + r.length := by simp [hpEq]; omega
  omega

end ApollonianSuperharmonic

end
