/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/LargestOrdinalSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.LevelOrdinalHeight

/-!
# Largest Ordinal Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- A full formula asserting that the distinguished parameter is a largest ordinal in the
model. -/
noncomputable def largestOrdinalSentence : SentenceForm :=
  .conj ordinalSentence (.all (.imp ordinalSentence (.disj (.member 0 1) (.equal 0 1))))

theorem largestOrdinalSentence_bound : largestOrdinalSentence.bound = 1 := by rfl

theorem largestOrdinalSentence_spec (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ A) :
    largestOrdinalSentence.Sat (A : Set ZFSet) e ↔
      (e 0).IsOrdinal ∧ ∀ x ∈ A, x.IsOrdinal → x ∈ e 0 ∨ x = e 0 := by
  simp only [largestOrdinalSentence,SentenceForm.Sat,SentenceForm.sat_all,
    SentenceForm.sat_imp,SentenceForm.sat_disj,cons_zero,cons_succ]
  rw [ordinalSentence_spec A hA e he]
  apply and_congr_right; intro _
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  rw [ordinalSentence_spec A hA (cons x e) hx]
  rfl

theorem largestOrdinalSentence_unique (A : ZFSet.{u}) (hA : Transitive A)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ A)
    (hmax : ∀ b : Ordinal.{u}, b.toZFSet ∈ A → b ≤ a)
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ A) :
    largestOrdinalSentence.Sat (A : Set ZFSet) e ↔ e 0 = a.toZFSet := by
  rw [largestOrdinalSentence_spec A hA e he]
  constructor
  · rintro ⟨ho,hm⟩
    have heq := ho.toZFSet_rank_eq
    have hle := hmax (e 0).rank (by rwa [heq])
    have hge : a ≤ (e 0).rank := by
      rcases hm a.toZFSet ha (ZFSet.isOrdinal_toZFSet a) with h|h
      · rw [← heq,Ordinal.toZFSet_mem_toZFSet_iff] at h
        exact h.le
      · have := congrArg ZFSet.rank h
        simpa only [Ordinal.rank_toZFSet] using this.le
    exact heq.symm.trans (congrArg Ordinal.toZFSet (le_antisymm hle hge))
  · intro heq
    refine ⟨heq ▸ ZFSet.isOrdinal_toZFSet a,?_⟩
    intro x hx ho
    have hle : x.rank ≤ a := hmax x.rank (by rwa [ho.toZFSet_rank_eq])
    rcases lt_or_eq_of_le hle with h|h
    · left
      rw [heq,← ho.toZFSet_rank_eq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr h
    · right
      rw [← ho.toZFSet_rank_eq,h,heq]

theorem largestOrdinalSentence_level (R : ZFSet.{u}) (o : Ordinal.{u})
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ level R (o + 1)) :
    largestOrdinalSentence.Sat (level R (o+1) : Set ZFSet) e ↔
      e 0 = (ordinalHeight (seed R) + o).toZFSet := by
  have hm := largest_ordinal_level_succ R o
  exact largestOrdinalSentence_unique _ (level_transitive R _) _ hm.1
    (fun b hb => (hm.2 b).mp hb) e he

/-- Existentially bind a largest ordinal before evaluating the formula body. -/
noncomputable def bindLargestOrdinal (p : SentenceForm) : SentenceForm :=
  .ex (.conj largestOrdinalSentence p)

theorem bindLargestOrdinal_bound (p : SentenceForm) :
    (bindLargestOrdinal p).bound = p.bound - 1 := by
  change max largestOrdinalSentence.bound p.bound - 1 = p.bound - 1
  rw [largestOrdinalSentence_bound]
  omega

theorem bindLargestOrdinal_level (p : SentenceForm) (R : ZFSet.{u}) (o : Ordinal.{u})
    (e : ℕ → ZFSet.{u}) :
    (bindLargestOrdinal p).Sat (level R (o+1) : Set ZFSet) e ↔
      p.Sat (level R (o+1) : Set ZFSet) (cons (ordinalHeight (seed R) + o).toZFSet e) := by
  change (∃ a ∈ level R (o+1), largestOrdinalSentence.Sat _ (cons a e) ∧ p.Sat _ (cons a e)) ↔ _
  constructor
  · rintro ⟨a,ha,hm,hp⟩
    have heq := (largestOrdinalSentence_level R o (cons a e) ha).mp hm
    change a = _ at heq
    simpa only [heq] using hp
  · intro hp
    have hm := largest_ordinal_level_succ R o
    exact ⟨_,hm.1,(largestOrdinalSentence_level R o _ hm.1).mpr rfl,hp⟩

end TuringRigidity.RelativeConstructible

end OAI
