/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host
public import LeanPool.SmallUndecidableGroups.Host.Abelianization
public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Condition
public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Embedding

public import LeanPool.SmallUndecidableGroups.Computability

/-! Gordon's Lemma 2.1 and its specialization to the three-nine host. -/

@[expose] public section

namespace Undecidability.Gordon

/-- Gordon's transformed presentation is trivial exactly when the input word
is trivial in the host group. -/
theorem presentsTrivial_transform_iff
    (P : FP n m) (data : TorsionData P) (w : Word n) :
    (transform P data w).presentsTrivial ↔ P.wordProblem w := by
  constructor
  · intro htrivial
    by_contra hw
    exact transform_not_trivial_of_not_wordProblem P data w hw htrivial
  · exact presentsTrivial_transform_of_wordProblem P data w

/-- The effective family obtained by enumerating the input words and transforming their
presentations. -/
def family (P : FP n m) (data : TorsionData P) : ℕ → FP 2 (m + 1) :=
  fun j ↦ transform P data (wordOfNat n j)

theorem family_isAdianRabin
    (P : FP n m) (data : TorsionData P)
    (hP : ¬ ComputablePred P.wordProblem) :
    FP.IsAdianRabinFamily (family P data) :=
  isAdianRabinFamily_of_wordProblem_reduction
    P (transform P data) hP (transform_computable P data)
      (presentsTrivial_transform_iff P data)

/-- Gordon's Lemma 2.1: condition (2.1) and an unsolvable host word problem
give a two-generator Adian--Rabin family with one more relator. -/
theorem lemma_2_1
    (P : FP n m) (condition : Condition21 P)
    (hP : ¬ ComputablePred P.wordProblem) :
    ∃ A : ℕ → FP 2 (m + 1), FP.IsAdianRabinFamily A :=
  ⟨family P condition.toTorsionData,
    family_isAdianRabin P condition.toTorsionData hP⟩

end Undecidability.Gordon

namespace Undecidability.Host

/-- Gordon's printed condition (2.1) for the host, using the generator `D`,
whose abelianized image is trivial (and therefore has order one). -/
def gordonCondition21 (datum : Thue.StandingDatum) :
    Gordon.Condition21 (presentationOf datum) where
  p := 1
  selected :=
    ⟨fun _ ↦ (0 : Fin 3), fun _ _ _ ↦ Subsingleton.elim _ _⟩
  q := fun _ ↦ 1
  q_pos := by intro i; omega
  gcd_q := by simp
  exactOrder := by
    intro i
    change orderOf (Abelianization.of
      (PresentedGroup.of (0 : Fin 3) : (presentationOf datum).Group)) = 1
    rw [d_eq_one_in_abelianization datum]
    simp

end Undecidability.Host
