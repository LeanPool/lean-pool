/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.StandingDatum
public import Mathlib.Data.Fin.VecNotation

/-!
# Presentation

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability
namespace Host

/-- Words on the compressed host generators `d, s, z`. -/
abbrev HostWord := Word 3

/-- Names of the nine generators just before Tietze compression. -/
inductive OldGen
  | d | e | s1 | s2 | c | t | k | y | z

/-- Words on the nine-generator alphabet before the ordered Tietze eliminations. -/
abbrev OldWord := List (OldGen × Bool)

namespace OldWord

/-- The positive one-letter word for an original generator. -/
def generator (g : OldGen) : OldWord :=
  [(g, true)]

/-- Reverse a word and invert each of its letters. -/
def inverse (w : OldWord) : OldWord :=
  FreeGroup.invRev w

/-- Concatenate two words on the original generator alphabet. -/
def mul (u v : OldWord) : OldWord :=
  u ++ v

/-- Concatenate the supplied list of original-alphabet words. -/
def product (ws : List OldWord) : OldWord :=
  ws.flatten

/-- Concatenate the indicated number of copies of an original-alphabet word. -/
def pow (w : OldWord) (n : ℕ) : OldWord :=
  (List.replicate n w).flatten

/-- Substitute a host word for each old generator, respecting signs. -/
def evaluate (sigma : OldGen → HostWord) (w : OldWord) : HostWord :=
  Word.substitute sigma w

/-- Read a positive `{s₁,s₂}`-word in the old alphabet. -/
def positive (w : List (Fin 2)) : OldWord :=
  w.flatMap fun i => generator (if i = 0 then .s1 else .s2)

/-- The relator word obtained from an equality of two original-alphabet words. -/
def relation (lhs rhs : OldWord) : OldWord :=
  mul lhs (inverse rhs)

/-- The paper's convention `[u,v] = u⁻¹v⁻¹uv`. -/
def commutator (u v : OldWord) : OldWord :=
  product [inverse u, inverse v, u, v]

@[simp]
theorem evaluate_generator (sigma : OldGen → HostWord) (g : OldGen) :
    evaluate sigma (generator g) = sigma g := by
  simp [evaluate, generator, Word.substitute]

@[simp]
theorem evaluate_mul (sigma : OldGen → HostWord) (u v : OldWord) :
    evaluate sigma (mul u v) =
      Word.mul (evaluate sigma u) (evaluate sigma v) := by
  simp [evaluate, mul]

@[simp]
theorem evaluate_inverse (sigma : OldGen → HostWord) (w : OldWord) :
    evaluate sigma (inverse w) = Word.inverse (evaluate sigma w) :=
  Word.substitute_invRev sigma w

@[simp]
theorem evaluate_product (sigma : OldGen → HostWord) (ws : List OldWord) :
    evaluate sigma (product ws) =
      Word.product (ws.map (evaluate sigma)) :=
  Word.substitute_flatten sigma ws

@[simp]
theorem evaluate_pow (sigma : OldGen → HostWord) (w : OldWord) (n : ℕ) :
    evaluate sigma (pow w n) = Word.pow (evaluate sigma w) n := by
  simpa only [evaluate, pow, Word.pow, Word.product, List.map_replicate] using
    Word.substitute_flatten sigma (List.replicate n w)

@[simp]
theorem evaluate_relation (sigma : OldGen → HostWord) (lhs rhs : OldWord) :
    evaluate sigma (relation lhs rhs) =
      Word.relation (evaluate sigma lhs) (evaluate sigma rhs) := by
  simp [relation, Word.relation]

@[simp]
theorem evaluate_commutator (sigma : OldGen → HostWord) (u v : OldWord) :
    evaluate sigma (commutator u v) =
      Word.commutator (evaluate sigma u) (evaluate sigma v) := by
  simp [commutator, Word.commutator, Word.product, Word.mul]

@[simp]
theorem evaluate_positive (sigma : OldGen → HostWord) (w : List (Fin 2)) :
    evaluate sigma (positive w) =
      Word.substitutePositive (sigma .s1) (sigma .s2) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change evaluate sigma
          (mul (generator (if i = 0 then .s1 else .s2)) (positive w)) = _
      rw [evaluate_mul, evaluate_generator, ih]
      fin_cases i <;> rfl

end OldWord

open OldGen

/-- The one-letter original-alphabet word `d`. -/
abbrev od : OldWord := OldWord.generator d
/-- The one-letter original-alphabet word `e`. -/
abbrev oe : OldWord := OldWord.generator e
/-- The one-letter original-alphabet word `s₁`. -/
abbrev os1 : OldWord := OldWord.generator s1
/-- The one-letter original-alphabet word `c`. -/
abbrev oc : OldWord := OldWord.generator c
/-- The one-letter original-alphabet word `t`. -/
abbrev ot : OldWord := OldWord.generator t
/-- The one-letter original-alphabet word `k`. -/
abbrev ok : OldWord := OldWord.generator k
/-- The one-letter original-alphabet word `y`. -/
abbrev oy : OldWord := OldWord.generator y

/-- The `i`th Borisov simulation relation retained during the compression
of Proposition 2.3 of the paper. -/
def oldSimulationRelator
    (F E : Fin 3 → List (Fin 2)) (i : Fin 3) : OldWord :=
  let exponent := i.val + 1
  OldWord.relation
    (OldWord.product
      [OldWord.inverse oc, OldWord.pow od exponent, OldWord.positive (F i),
       OldWord.pow oe exponent, oc])
    (OldWord.product
      [OldWord.pow od exponent, OldWord.positive (E i), OldWord.pow oe exponent])

/-- The nine surviving relators, before applying the ordered substitution `tau`. -/
def oldSurvivingRelator
    (F E : Fin 3 → List (Fin 2)) (P : List (Fin 2)) : Fin 9 → OldWord :=
  ![
    OldWord.relation
      (OldWord.product [OldWord.inverse os1, OldWord.pow od 4, os1]) od,
    OldWord.relation
      (OldWord.product [OldWord.inverse os1, oe, os1]) (OldWord.pow oe 4),
    OldWord.commutator os1 oc,
    oldSimulationRelator F E 0,
    oldSimulationRelator F E 1,
    oldSimulationRelator F E 2,
    OldWord.commutator od ot,
    OldWord.commutator
      (OldWord.product
        [OldWord.inverse (OldWord.positive P), ot, OldWord.positive P])
      ok,
    OldWord.relation
      (OldWord.product [OldWord.inverse oy, oe, oy]) od
  ]

/-- Retained generators in order: `D`, `S`, `Z`. -/
def dWord : HostWord := Word.generator 0
/-- The retained host generator `s`. -/
def sWord : HostWord := Word.generator 1
/-- The retained host generator `z`. -/
def zWord : HostWord := Word.generator 2

/-- The substitution word `z⁻¹ * d * z` for `t`. -/
def tWord : HostWord :=
  Word.product [Word.inverse zWord, dWord, zWord]

/-- The substitution word `z⁻¹ * t * z` for `c`. -/
def cWord : HostWord :=
  Word.product [Word.inverse zWord, tWord, zWord]

/-- The substitution word `z⁻¹ * c * z` for `y`. -/
def yWord : HostWord :=
  Word.product [Word.inverse zWord, cWord, zWord]

/-- The substitution word `y⁻¹ * d⁻¹ * y` for `e`. -/
def eWord : HostWord :=
  Word.product [Word.inverse yWord, Word.inverse dWord, yWord]

/-- The substitution word `y⁻¹ * t * y` for `k`. -/
def kWord : HostWord :=
  Word.product [Word.inverse yWord, tWord, yWord]

/-- The substitution word `y⁻¹ * s⁻¹ * y` for the eliminated second stable generator. -/
def s2Word : HostWord :=
  Word.product [Word.inverse yWord, Word.inverse sWord, yWord]

/-- The ordered substitution `tau` used in the six Tietze eliminations. -/
def tau : OldGen → HostWord
  | .d => dWord
  | .e => eWord
  | .s1 => sWord
  | .s2 => s2Word
  | .c => cWord
  | .t => tWord
  | .k => kWord
  | .y => yWord
  | .z => zWord

/-- `rhoᵢ` is the image under `tau` of the `i`th relator in `oldSurvivingRelator`. -/
def rho
    (F E : Fin 3 → List (Fin 2)) (P : List (Fin 2))
    (i : Fin 9) : HostWord :=
  OldWord.evaluate tau (oldSurvivingRelator F E P i)

/-- An explicit three-generator, nine-relator presentation of the group
in Proposition 2.3 of the paper. -/
def presentation
    (F E : Fin 3 → List (Fin 2)) (P : List (Fin 2)) : FP 3 9 where
  relator := rho F E P

/-- The three-generator nine-relator host presentation attached to the proved Thue datum. -/
def presentationOf (datum : Thue.StandingDatum) : FP 3 9 :=
  presentation datum.F datum.E datum.P

/-- Evaluate a positive Thue word after `tau`. -/
def positiveWord (Q : List (Fin 2)) : HostWord :=
  Word.substitutePositive sWord s2Word Q

/-- The compressed image of Borisov's test word `[Q⁻¹tQ,k]`. -/
def testWord (Q : List (Fin 2)) : HostWord :=
  let q := positiveWord Q
  Word.commutator (Word.product [Word.inverse q, tWord, q]) kWord

/-- The syntactic map from a Thue input to the host test word is computable. -/
theorem testWord_computable : Computable testWord := by
  have hpositive : Primrec positiveWord := by
    apply Primrec.of_eq
      (Primrec.list_flatMap Primrec.id
        ((Primrec.dom_finite
          (fun i : Fin 2 => if i = 0 then sWord else s2Word)).comp
            Primrec.snd).to₂)
    intro Q
    rfl
  have hletterInverse : Primrec fun x : SignedGenerator 3 =>
      (x.1, !x.2) :=
    Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
  have hinverse : Primrec (@Word.inverse 3) := by
    apply Primrec.of_eq
      (Primrec.list_map Primrec.list_reverse
        (hletterInverse.comp Primrec.snd).to₂)
    intro w
    rfl
  have hconjugate : Primrec fun Q =>
      Word.product [Word.inverse (positiveWord Q), tWord, positiveWord Q] := by
    apply Primrec.of_eq
      (Primrec.list_append.comp (hinverse.comp hpositive)
        (Primrec.list_append.comp (Primrec.const tWord) hpositive))
    intro Q
    simp [Word.product]
  have hcommutator : Primrec fun u : HostWord =>
      Word.commutator u kWord := by
    apply Primrec.of_eq
      (Primrec.list_append.comp hinverse
        (Primrec.list_append.comp (Primrec.const (Word.inverse kWord))
          (Primrec.list_append.comp Primrec.id (Primrec.const kWord))))
    intro u
    rfl
  exact (hcommutator.comp hconjugate).to_comp

end Host
end Undecidability
