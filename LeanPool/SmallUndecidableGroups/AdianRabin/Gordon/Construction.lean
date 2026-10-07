/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.RightBasis
public import LeanPool.SmallUndecidableGroups.Presentation
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group

/-!
# Gordon's one-extra-relator construction

This file formalizes the presentation-theoretic part of Lemma 2.1 of
Gordon (2022).  The torsion hypothesis is recorded in the minimal form used
in Gordon's proof: the selected abelianized generators have distinct orders,
their orders have gcd one, and `degree` extends those orders injectively to
all generators.  (Gordon obtains this form by choosing a minimal witness to
condition (2.1).)
-/

@[expose] public section

namespace Undecidability.Gordon

/-- Proof-ready, minimal-witness form of condition (2.1) in Gordon's paper.

`selected` lists the generators used in (2.1), `q` gives their exact orders
in the abelianization, and `degree` is the injective exponent assignment used
in relations (iii)--(iv). -/
structure TorsionData (P : FP n m) where
  /-- The number of generators selected for the torsion condition. -/
  p : ℕ
  /-- The distinct generator indices selected for the torsion condition. -/
  selected : Fin p ↪ Fin n
  /-- The prescribed orders of the selected generators in the abelianization. -/
  q : Fin p → ℕ
  gcd_q : Finset.univ.gcd q = 1
  exactOrder : ∀ i,
    orderOf (Abelianization.of
      (PresentedGroup.of (selected i) : P.Group)) = q i
  /-- The distinct positive exponents assigned to the original generators. -/
  degree : Fin n → ℕ
  degree_pos : ∀ i, 0 < degree i
  degree_injective : Function.Injective degree
  degree_selected : ∀ i, degree (selected i) = q i

variable {n m : ℕ} {P : FP n m}

/-- The word representing the generator `a` in this presentation. -/
def aWord : Word 2 := Word.generator 0
/-- The word representing the generator `b` in this presentation. -/
def bWord : Word 2 := Word.generator 1

/-- Eliminate `alpha` using `a * alpha * a⁻¹ = b²`. -/
def alphaWord : Word 2 :=
  Word.product [Word.inverse aWord, Word.pow bWord 2, aWord]

/-- Eliminate `beta` using
`alpha * a * alpha⁻¹ = b * beta * b⁻¹`. -/
def betaWord : Word 2 :=
  Word.product
    [Word.inverse bWord, alphaWord, aWord, Word.inverse alphaWord, bWord]

/-- Gordon's right-hand word `beta⁻ʳ * b * betaʳ`. -/
def rightConjugateWord (r : ℕ) : Word 2 :=
  Word.product
    [Word.inverse (Word.pow betaWord r), bWord, Word.pow betaWord r]

/-- The paper's commutator convention: `[u,v] = u*v*u⁻¹*v⁻¹`.

The project's older constructions use the opposite convention, so this is
kept explicit. -/
def paperCommutator (u v : Word n) : Word n :=
  Word.product [u, v, Word.inverse u, Word.inverse v]

/-- An old generator after eliminating `alpha`, `beta`, and the old
generators from Gordon's presentation. -/
def encodedGenerator (data : TorsionData P) (i : Fin n) : Word 2 :=
  Word.product
    [Word.pow aWord (data.degree i), rightConjugateWord (i.1 + 1),
      Word.inverse (Word.pow alphaWord (data.degree i))]

/-- Substitute the encoded two-generator words for a word in the old
generators. -/
def encodeWord (data : TorsionData P) (w : Word n) : Word 2 :=
  Word.substitute (encodedGenerator data) w

@[simp]
theorem eval_encodeWord {H : Type*} [Group H]
    (data : TorsionData P) (x : Fin 2 → H) (w : Word n) :
    Word.eval x (encodeWord data w) =
      Word.eval (fun i ↦ Word.eval x (encodedGenerator data i)) w :=
  Word.eval_substitute x (encodedGenerator data) w

/-- The single relation left after all Tietze eliminations. -/
def additionalRelator (data : TorsionData P) (w : Word n) : Word 2 :=
  Word.relation
    (paperCommutator (encodeWord data w) (Word.pow alphaWord 2))
    (rightConjugateWord (n + 1))

/-- Gordon's two-generator, one-extra-relator presentation. -/
def transform (P : FP n m) (data : TorsionData P)
    (w : Word n) : FP 2 (m + 1) where
  relator := Fin.append
    (fun i ↦ encodeWord data (P.relator i))
    (fun _ ↦ additionalRelator data w)

@[simp]
theorem transform_old (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : Fin m) :
    (transform P data w).relator (Fin.castAdd 1 i) =
      encodeWord data (P.relator i) := by
  simp [transform]

@[simp]
theorem transform_additional (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : Fin 1) :
    (transform P data w).relator (Fin.natAdd m i) =
      additionalRelator data w := by
  simp [transform]

private theorem inverse_primrec : Primrec (@Word.inverse 2) := by
  have hletterInverse : Primrec fun x : SignedGenerator 2 ↦
      (x.1, !x.2) :=
    Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
  apply Primrec.of_eq
    (Primrec.list_map Primrec.list_reverse
      (hletterInverse.comp Primrec.snd).to₂)
  intro w
  rfl

theorem encodeWord_primrec (P : FP n m) (data : TorsionData P) :
    Primrec (fun w : Word n ↦ encodeWord data w) := by
  have hgenerator : Primrec (encodedGenerator data) :=
    Primrec.fin_app.comp
      (Primrec.const (α := Fin n) (encodedGenerator data)) Primrec.id
  have hletter : Primrec fun x : SignedGenerator n ↦
      bif x.2 then encodedGenerator data x.1
      else Word.inverse (encodedGenerator data x.1) :=
    Primrec.cond Primrec.snd
      (hgenerator.comp Primrec.fst)
      (inverse_primrec.comp (hgenerator.comp Primrec.fst))
  apply Primrec.of_eq
    (Primrec.list_flatMap Primrec.id (hletter.comp Primrec.snd).to₂)
  intro w
  simp only [encodeWord, Word.substitute]
  congr 1
  funext x
  cases x.2 <;> rfl

private theorem relation_primrec {f : Word n → Word 2}
    (hf : Primrec f) (rhs : Word 2) :
    Primrec fun w ↦ Word.relation (f w) rhs := by
  apply Primrec.of_eq
    (Primrec.list_append.comp hf
      (Primrec.const (Word.inverse rhs)))
  intro w
  rfl

private theorem paperCommutator_primrec (v : Word 2) :
    Primrec fun u : Word 2 ↦ paperCommutator u v := by
  apply Primrec.of_eq
    (Primrec.list_append.comp Primrec.id
      (Primrec.list_append.comp (Primrec.const v)
        (Primrec.list_append.comp inverse_primrec
          (Primrec.const (Word.inverse v)))))
  intro u
  simp [paperCommutator, Word.product]

/-- The word-indexed Gordon transformation is uniform and computable. -/
theorem transform_computable (P : FP n m) (data : TorsionData P) :
    Computable₂ fun w i ↦ (transform P data w).relator i := by
  have hcomm : Primrec fun w : Word n ↦
      paperCommutator (encodeWord data w) (Word.pow alphaWord 2) :=
    (paperCommutator_primrec (Word.pow alphaWord 2)).comp
      (encodeWord_primrec P data)
  have hadditional : Primrec fun w : Word n ↦ additionalRelator data w :=
    relation_primrec hcomm (rightConjugateWord (n + 1))
  apply Primrec₂.to_comp
  apply (Primrec.fin_curry).mp
  apply (Primrec.fin_curry).mpr
  apply Primrec₂.swap
  apply (Primrec.fin_curry₁).mpr
  intro i
  change Fin (m + 1) at i
  cases i using Fin.addCases with
  | left j =>
      simpa using
        (Primrec.const (α := Word n) (encodeWord data (P.relator j)))
  | right j =>
      refine Fin.cases ?_ (fun j' ↦ Fin.elim0 j') j
      apply Primrec.of_eq hadditional
      intro w
      rw [transform_additional]

private theorem additional_relator_eq_one
    (P : FP n m) (data : TorsionData P) (w : Word n) :
    Word.eval
        (PresentedGroup.of : Fin 2 → (transform P data w).Group)
        (additionalRelator data w) = 1 := by
  change (transform P data w).evalWord (additionalRelator data w) = 1
  rw [FP.evalWord_eq_mk]
  apply PresentedGroup.one_of_mem
  exact ⟨Fin.natAdd m (0 : Fin 1), by simp⟩

private theorem exists_oldHom
    (P : FP n m) (data : TorsionData P) (w : Word n) :
    ∃ f : P.Group →* (transform P data w).Group,
      ∀ i : Fin n,
        f (PresentedGroup.of i) =
          Word.eval PresentedGroup.of (encodedGenerator data i) := by
  let y : Fin n → (transform P data w).Group :=
    fun i ↦ Word.eval PresentedGroup.of (encodedGenerator data i)
  have hrel : ∀ i, Word.eval y (P.relator i) = 1 := by
    intro i
    have hold : Word.eval
        (PresentedGroup.of : Fin 2 → (transform P data w).Group)
        (encodeWord data (P.relator i)) = 1 := by
      change (transform P data w).evalWord
        (encodeWord data (P.relator i)) = 1
      rw [FP.evalWord_eq_mk]
      apply PresentedGroup.one_of_mem
      exact ⟨Fin.castAdd 1 i, by simp⟩
    change Word.eval y (P.relator i) = 1
    rw [← eval_encodeWord]
    exact hold
  refine ⟨P.homOfRelators y hrel, ?_⟩
  intro i
  exact P.homOfRelators_of y hrel i

private theorem gcd_sq_eq_one (data : TorsionData P) :
    Finset.univ.gcd (fun i ↦ data.q i ^ 2) = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro l hl hldiv
  have hallSq : ∀ i ∈ (Finset.univ : Finset (Fin data.p)),
      l ∣ data.q i ^ 2 :=
    Finset.dvd_gcd_iff.mp hldiv
  have hall : ∀ i ∈ (Finset.univ : Finset (Fin data.p)),
      l ∣ data.q i := by
    intro i hi
    exact hl.dvd_of_dvd_pow (hallSq i hi)
  have hlgcd : l ∣ Finset.univ.gcd data.q :=
    Finset.dvd_gcd hall
  rw [data.gcd_q] at hlgcd
  exact hl.not_dvd_one hlgcd

/-- If the input word is trivial, Gordon's transformed presentation is
trivial.  This is the elementary half of Lemma 2.1. -/
theorem presentsTrivial_transform_of_wordProblem
    (P : FP n m) (data : TorsionData P) (w : Word n)
    (hw : P.wordProblem w) :
    (transform P data w).presentsTrivial := by
  let x : Fin 2 → (transform P data w).Group := PresentedGroup.of
  let a := x 0
  let b := x 1
  let alpha := Word.eval x alphaWord
  let beta := Word.eval x betaWord
  obtain ⟨f, hf⟩ := exists_oldHom P data w
  have hwP : P.evalWord w = 1 :=
    (P.wordProblem_iff_evalWord_eq_one w).mp hw
  have hwT : Word.eval x (encodeWord data w) = 1 := by
    rw [eval_encodeWord]
    calc
      Word.eval (fun i ↦ Word.eval x (encodedGenerator data i)) w =
          Word.eval (fun i ↦ f (PresentedGroup.of i)) w := by
            congr 2
            funext i
            exact (hf i).symm
      _ = f (P.evalWord w) := by
            symm
            exact Word.map_eval f _ w
      _ = 1 := by rw [hwP, map_one]
  have hfinal := additional_relator_eq_one P data w
  change Word.eval x
    (Word.relation
      (paperCommutator (encodeWord data w) (Word.pow alphaWord 2))
      (rightConjugateWord (n + 1))) = 1 at hfinal
  rw [Word.eval_relation_eq_one_iff] at hfinal
  have hbConj :
      (beta ^ (n + 1))⁻¹ * b * beta ^ (n + 1) = 1 := by
    simpa [paperCommutator, Word.product, rightConjugateWord,
      bWord, hwT, alpha, beta, b, x, mul_assoc] using hfinal.symm
  have hb : b = 1 := by
    calc
      b = beta ^ (n + 1) *
          ((beta ^ (n + 1))⁻¹ * b * beta ^ (n + 1)) *
            (beta ^ (n + 1))⁻¹ := by group
      _ = 1 := by rw [hbConj]; simp
  have halpha : alpha = 1 := by
    simp [alpha, alphaWord, aWord, bWord, b, x, hb]
  have hbeta : beta = a := by
    simp [beta, betaWord, aWord, bWord, alphaWord,
      a, b, x, hb]
  have hencoded (i : Fin n) :
      Word.eval x (encodedGenerator data i) = a ^ data.degree i := by
    simp [encodedGenerator, rightConjugateWord, aWord, bWord,
      alphaWord, betaWord, a, b, x, hb]
  have hcyclicFG (r : FreeGroup (Fin 2)) :
      ∃ k : ℤ,
        PresentedGroup.mk (transform P data w).relSet r = a ^ k := by
    induction r using FreeGroup.induction_on with
    | one => exact ⟨0, by simp⟩
    | of i =>
        fin_cases i
        · exact ⟨1, by simp [a, x, PresentedGroup.of]⟩
        · exact ⟨0, by simpa [b, x, PresentedGroup.of] using hb⟩
    | inv_of i _ =>
        fin_cases i
        · exact ⟨-1, by simp [a, x, PresentedGroup.of]⟩
        · exact ⟨0, by
            simpa [b, x, PresentedGroup.of] using congrArg Inv.inv hb⟩
    | mul r s hr hs =>
        obtain ⟨k, hk⟩ := hr
        obtain ⟨l, hl⟩ := hs
        exact ⟨k + l, by simp [hk, hl, zpow_add]⟩
  have hcyclic : IsCyclic (transform P data w).Group := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨a, eq_top_iff.mpr ?_⟩
    intro g _
    obtain ⟨r, rfl⟩ := PresentedGroup.mk_surjective
      (transform P data w).relSet g
    obtain ⟨k, hk⟩ := hcyclicFG r
    exact ⟨k, hk.symm⟩
  let : IsCyclic (transform P data w).Group := hcyclic
  let : CommGroup (transform P data w).Group := IsCyclic.commGroup
  have haSq (i : Fin data.p) : a ^ (data.q i ^ 2) = 1 := by
    have hab :
        (Abelianization.of
          (PresentedGroup.of (data.selected i) : P.Group)) ^ data.q i = 1 := by
      rw [← data.exactOrder i]
      exact pow_orderOf_eq_one _
    have hmapped := congrArg (Abelianization.lift f) hab
    have hfi : f (PresentedGroup.of (data.selected i)) ^ data.q i = 1 := by
      simpa using hmapped
    rw [hf, hencoded, data.degree_selected] at hfi
    calc
      a ^ data.q i ^ 2 = (a ^ data.q i) ^ data.q i := by
        rw [pow_two, pow_mul]
      _ = 1 := hfi
  have horderDvd :
      orderOf a ∣ Finset.univ.gcd (fun i : Fin data.p ↦ data.q i ^ 2) := by
    apply Finset.dvd_gcd
    intro i _
    exact orderOf_dvd_of_pow_eq_one (haSq i)
  have horder : orderOf a = 1 := by
    rw [gcd_sq_eq_one data] at horderDvd
    exact Nat.dvd_one.mp horderDvd
  have ha : a = 1 := orderOf_eq_one_iff.mp horder
  have hx : ∀ i : Fin 2, x i = 1 := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
  exact (transform P data w).presentsTrivial_of_generator_eq_one hx

end Undecidability.Gordon
