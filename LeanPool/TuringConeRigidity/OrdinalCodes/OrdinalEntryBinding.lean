/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalEntryBinding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalPaddingSyntax

/-!
# Ordinal Entry Binding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

def codeBindEntries : ℕ → SentenceForm → SentenceForm
  | 0, p => p
  | n+1, p => .ex (codeBindEntries n p)

theorem codeBindEntries_bound (n : ℕ) (p : SentenceForm) :
    (codeBindEntries n p).bound = p.bound - n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [codeBindEntries,SentenceForm.bound,ih,Nat.sub_sub]

theorem code_prepend_congr (w v : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u})
    (h : ∀ i, i < n → w i = v i) : prependValues w n e = prependValues v n e := by
  funext i
  by_cases hi : i < n
  · rw [prependValues_lt w n e i hi,prependValues_lt v n e i hi,h i hi]
  · have heq : i = n+(i-n) := by omega
    rw [heq,prependValues_tail,prependValues_tail]

theorem codeBindEntries_sat (M : ZFSet.{u}) (n : ℕ) (p : SentenceForm)
    (e : ℕ → ZFSet.{u}) :
    (codeBindEntries n p).Sat (M : Set ZFSet) e ↔
      ∃ w : ℕ → ZFSet.{u}, (∀ i, i < n → w i ∈ M) ∧
        p.Sat (M : Set ZFSet) (prependValues w n e) := by
  induction n generalizing e with
  | zero => exact ⟨fun h => ⟨e,by intro i hi; omega,h⟩,fun ⟨_,_,h⟩ => h⟩
  | succ n ih =>
    change (∃ x ∈ M, (codeBindEntries n p).Sat _ (cons x e)) ↔ _
    constructor
    · rintro ⟨x,hx,hp⟩
      obtain ⟨w,hw,hp⟩ := (ih (cons x e)).mp hp
      let v : ℕ → ZFSet.{u} := fun i => if i < n then w i else x
      have hn : v n = x := by simp [v]
      refine ⟨v,?_,?_⟩
      · intro i hi
        dsimp [v]
        split
        · exact hw i ‹i < n›
        · exact hx
      · change p.Sat _ (prependValues v n (cons (v n) e))
        rw [hn,code_prepend_congr v w n (cons x e) (by intro i hi; simp [v,hi])]
        exact hp
    · rintro ⟨w,hw,hp⟩
      exact ⟨w n,hw n (by omega),(ih _).mpr ⟨w,fun i hi => hw i (by omega),hp⟩⟩

def entryCodeSlots (n : ℕ) : ℕ → ℕ
  | 0 => n+1
  | i+1 => if i < n then i else n+1

noncomputable def paddedEntrySentence (n : ℕ) (k : Fin n) : SentenceForm :=
  codeBindEntries n (.conj (.equal n k.val)
    ((paddedCodeSentence n).rename (entryCodeSlots n)))

theorem paddedEntrySentence_bound (n : ℕ) (k : Fin n) :
    (paddedEntrySentence n k).bound ≤ 2 := by
  have hp := code_rename_bound (paddedCodeSentence n) (entryCodeSlots n) (n+2) (by
    intro i _; cases i <;> simp only [entryCodeSlots] <;> (try split) <;> omega)
  rw [paddedEntrySentence,codeBindEntries_bound]
  change max (max n k.val + 1) _ - n ≤ 2
  have hk := k.isLt
  omega

theorem entryCodeSlots_env (n : ℕ) (e w : ℕ → ZFSet.{u}) :
    ∀ i, i < (paddedCodeSentence n).bound →
      prependValues w n e (entryCodeSlots n i) = cons (e 1) w i := by
  intro i hi
  have hb := paddedCodeSentence_bound n
  cases i with
  | zero => exact prependValues_tail w n e 1
  | succ i =>
    simp only [entryCodeSlots,ite_eq_left (show i < n by omega),cons_succ]
    exact prependValues_lt w n e i (by omega)

theorem paddedEntrySentence_semantics (M : ZFSet.{u}) (n : ℕ) (k : Fin n)
    (e : ℕ → ZFSet.{u}) :
    (paddedEntrySentence n k).Sat (M : Set ZFSet) e ↔
      ∃ w : ℕ → ZFSet.{u}, (∀ i, i < n → w i ∈ M) ∧ e 0 = w k.val ∧
        (paddedCodeSentence n).Sat (M : Set ZFSet) (cons (e 1) w) := by
  rw [paddedEntrySentence,codeBindEntries_sat]
  apply exists_congr; intro w
  apply and_congr_right; intro _
  change (prependValues w n e n = prependValues w n e k.val ∧ _) ↔ _
  rw [show prependValues w n e n = e 0 from prependValues_tail w n e 0,prependValues_lt w n e
    k.val k.isLt,
    SentenceForm.sat_rename]
  exact and_congr Iff.rfl ((paddedCodeSentence n).finite_support _ _ _ (entryCodeSlots_env n e w))

end TuringRigidity.OrdinalCoding

end OAI
