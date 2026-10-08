/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Presentation
public import Mathlib.Computability.Reduce

/-!
# Computability

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

/-- A total computable enumeration of all words on `n` generators. -/
def wordOfNat (n : ℕ) (k : ℕ) : Word n :=
  (Encodable.decode k : Option (Word n)).getD []

theorem wordOfNat_computable (n : ℕ) :
    Computable (wordOfNat n) :=
  Computable.option_getD
    (@Computable.decode (Word n) _)
    (Computable.const ([] : Word n))

@[simp]
theorem wordOfNat_encode (w : Word n) :
    wordOfNat n (Encodable.encode w) = w := by
  simp [wordOfNat]

/-- Undecidability transfers forward along a computable many-one reduction. -/
theorem not_computablePred_of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop}
    (hp : ¬ ComputablePred p) (hred : p ≤₀ q) :
    ¬ ComputablePred q := by
  intro hq
  exact hp (ComputablePred.computable_of_manyOneReducible hred hq)

/--
Turn a uniform word-indexed presentation construction into a natural-number
indexed Adian--Rabin family.
-/
theorem isAdianRabinFamily_of_wordProblem_reduction
    {n m n' m' : ℕ}
    (P : FP n m) (R : Word n → FP n' m')
    (hP : ¬ ComputablePred P.wordProblem)
    (hR : Computable₂ fun w i => (R w).relator i)
    (hiff : ∀ w, (R w).presentsTrivial ↔ P.wordProblem w) :
    FP.IsAdianRabinFamily (fun j => R (wordOfNat n j)) := by
  constructor
  · unfold FP.Effective
    exact hR.comp
      ((wordOfNat_computable n).comp Computable.fst)
      Computable.snd
  · apply not_computablePred_of_manyOneReducible hP
    refine ⟨Encodable.encode, Computable.encode, ?_⟩
    intro w
    simpa only [wordOfNat_encode] using (hiff w).symm

end Undecidability
