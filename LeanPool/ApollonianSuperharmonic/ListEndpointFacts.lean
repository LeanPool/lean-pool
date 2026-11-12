/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt


/-!
# ListEndpointFacts

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace ListEndpointFacts

/-- Shared internalNeighbors identity for ListEndpointFacts. -/
theorem internalNeighbors :
    (by
      classical
      exact
        ∀ (l : List GaussianInt), ∀ (x : GaussianInt), ∀ (h : GaussianInt), ∀ (t : GaussianInt),
            l.Nodup → l.head? = some h → l.getLast? = some t → x ∈ l → x ≠ h → x ≠ t → ∃ pre y z
            post, l = pre ++ y :: x :: z :: post ) := by
  classical
  intro l
  induction l with
  | nil => intro x h t hn hh ht hx; simp at hx
  | cons a tail ih =>
    intro x h t hn hh ht hx hxh hxt
    have hah : a = h := by simpa using hh
    subst h
    rcases List.mem_cons.mp hx with hxa | hx
    · exact (hxh hxa).elim
    · cases tail with
      | nil => simp at hx
      | cons b rest =>
        by_cases hxb : x = b
        · subst x
          have hrest : rest ≠ [] := by
            intro he
            subst rest
            have hb : b = t := by simpa using ht
            exact hxt hb
          cases rest with
          | nil => exact (hrest rfl).elim
          | cons c u =>
            refine ⟨[], a, c, u, ?_⟩
            simp
        · obtain ⟨pre, y, z, post, heq⟩ :=
            ih x b t hn.tail (by rfl) (by simpa using ht) hx hxb hxt
          refine ⟨a :: pre, y, z, post, ?_⟩
          simp [heq]

/-- A specified head belongs to its list. -/
theorem headMembership {α : Type*} (l : List α) (a : α)
    (hhead : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at hhead
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst x
    simp

/-- Zipping lists with specified heads separates the first pair. -/
theorem zipHeadShape {α β : Type*} (left : List α) (right : List β)
    (a : α) (b : β) (hleft : left.head? = some a)
    (hright : right.head? = some b) :
    left.zip right = [(a, b)] ++ left.tail.zip right.tail := by
  cases left with
  | nil => simp at hleft
  | cons x xs =>
    cases right with
    | nil => simp at hright
    | cons y ys =>
      simp only [List.head?_cons, Option.some.injEq] at hleft hright
      subst x
      subst y
      rfl

/-- Replacing a list's last entry by a list starting there preserves its head. -/
theorem headDropLastAppend {α : Type*} (left right : List α) (a b : α)
    (hhead : left.head? = some a) (hlast : left.getLast? = some b)
    (hright : right.head? = some b) : (left.dropLast ++ right).head? = some a := by
  cases left with
  | nil => simp at hhead
  | cons x xs => cases xs <;> simp_all

/-- Appending a nonempty final list preserves its last entry. -/
theorem lastDropLastAppend {α : Type*} (left right : List α) (a : α)
    (hlast : right.getLast? = some a) : (left.dropLast ++ right).getLast? = some a := by
  cases right with
  | nil => simp at hlast
  | cons x xs => simpa using hlast

/-- A nodup list's indexed entry does not occur in its preceding prefix. -/
theorem getNotTake {α : Type*} (l : List α) (hn : l.Nodup) (m : Nat)
    (hm : m < l.length) : l.get ⟨m, hm⟩ ∉ l.take m := by
  intro hmem
  rcases List.mem_take_iff_getElem.mp hmem with ⟨i, hi, heq⟩
  have hi' : i < m := by omega
  have hiList : i < l.length := lt_trans hi' hm
  have heq' : l[i] = l[m] := by simpa using heq
  have hidx := hn.getElem_inj_iff.mp heq'
  omega

end ListEndpointFacts
end ApollonianSuperharmonic

end
