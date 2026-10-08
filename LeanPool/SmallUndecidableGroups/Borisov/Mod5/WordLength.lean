/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Mod5.BaseWords

/-!
# Normal-form length in the mod-five Borisov quotient

The base-coordinate trace constructed in
`GroupUndecidability.Borisov.Mod5.BaseWords` is a reduced free-product word:
its syllables are nontrivial and alternate between the two cyclic factors.
Consequently its displayed length is the canonical free-product normal-form
length.
-/

@[expose] public section

namespace Undecidability

open Monoid

namespace CoprodIWordLength

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
  [DecidableEq ι] [∀ i, DecidableEq (M i)]

/-- The one-letter indexed free-product word. -/
def singletonWord {i : ι} (m : M i) (hm : m ≠ 1) :
    CoprodI.Word M :=
  CoprodI.Word.cons m CoprodI.Word.empty
    (by simp [CoprodI.Word.fstIdx, CoprodI.Word.empty]) hm

omit [DecidableEq ι] [(i : ι) → DecidableEq (M i)] in
@[simp] private theorem singletonWord_prod {i : ι} (m : M i)
    (hm : m ≠ 1) :
    (singletonWord m hm : CoprodI.Word M).prod = CoprodI.of m := by
  change CoprodI.of m * 1 = CoprodI.of m
  exact mul_one _

/-- The two-letter indexed free-product word with distinct factor labels. -/
def twoWord {i j : ι} (hij : i ≠ j) (d : M i) (e : M j)
    (hd : d ≠ 1) (he : e ≠ 1) : CoprodI.Word M :=
  CoprodI.Word.cons d (singletonWord e he) (by
    simpa [singletonWord, CoprodI.Word.fstIdx, CoprodI.Word.empty] using hij.symm) hd

omit [DecidableEq ι] [(i : ι) → DecidableEq (M i)] in
@[simp] private theorem twoWord_prod {i j : ι} (hij : i ≠ j)
    (d : M i) (e : M j) (hd : d ≠ 1) (he : e ≠ 1) :
    (twoWord hij d e hd he : CoprodI.Word M).prod =
      CoprodI.of d * CoprodI.of e := by
  simp [twoWord, CoprodI.Word.prod_cons]

/-- A product of two letters from distinct free factors has canonical
free-product normal-form length at most two. -/
theorem normalForm_length_mul_of_of_le_two {i j : ι} (hij : i ≠ j)
    (d : M i) (e : M j) :
    (CoprodI.Word.equiv (CoprodI.of d * CoprodI.of e)).toList.length ≤ 2 := by
  by_cases hd : d = 1
  · subst d
    by_cases he : e = 1
    · subst e
      simp [CoprodI.Word.equiv, CoprodI.Word.empty]
    · have hword :
          CoprodI.Word.equiv (CoprodI.of (1 : M i) * CoprodI.of e) =
            singletonWord e he := by
        apply CoprodI.Word.equiv.symm.injective
        change _ = (singletonWord e he).prod
        simp
      rw [hword]
      change 1 ≤ 2
      decide
  · by_cases he : e = 1
    · subst e
      have hword :
          CoprodI.Word.equiv (CoprodI.of d * CoprodI.of (1 : M j)) =
            singletonWord d hd := by
        apply CoprodI.Word.equiv.symm.injective
        change _ = (singletonWord d hd).prod
        simp
      rw [hword]
      change 1 ≤ 2
      decide
    · have hword :
          CoprodI.Word.equiv (CoprodI.of d * CoprodI.of e) =
            twoWord hij d e hd he := by
        apply CoprodI.Word.equiv.symm.injective
        change _ = (twoWord hij d e hd he).prod
        simp
      rw [hword]
      change 2 ≤ 2
      exact le_rfl

end CoprodIWordLength

namespace BorisovModFiveWordLength

open BorisovModFiveBaseWords
open BorisovModFiveQuotient

noncomputable section

private theorem twistLetter_chain (n : ℕ) {letters : List BaseLetter}
    (hletters : letters.IsChain fun x y ↦ x.1 ≠ y.1) :
    (letters.map (twistLetter n)).IsChain fun x y ↦ x.1 ≠ y.1 := by
  rw [List.isChain_map]
  exact hletters.imp fun x y hxy ↦ by simpa using hxy

private theorem c5_rulePower_ne_one (i : Fin 3) :
    BorisovModFiveQuotient.c5Generator ^ (i.val + 1) ≠ 1 := by
  fin_cases i <;> decide

private theorem rulePair_ne_one (rules : Fin 3 → List (Fin 2)) (i : Fin 3) :
    ∀ x ∈ rulePair rules i, x.2 ≠ 1 := by
  intro x hx
  simp only [rulePair, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact c5_rulePower_ne_one i
  · exact twistLetter_ne_one (rules i).length
      ⟨1, BorisovModFiveQuotient.c5Generator ^ (i.val + 1)⟩
      (c5_rulePower_ne_one i)

/-- No base syllable in the displayed trace is the identity of its factor. -/
theorem baseLetters_ne_one (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    ∀ x ∈ baseLetters rules letters, x.2 ≠ 1 := by
  induction letters with
  | nil => simp [baseLetters]
  | cons q rest ih =>
      cases q with
      | inl beta =>
          simp only [baseLetters, List.mem_map]
          rintro x ⟨y, hy, rfl⟩
          exact twistLetter_ne_one 1 y (ih y hy)
      | inr i =>
          intro x hx
          rw [baseLetters, List.mem_append] at hx
          rcases hx with hx | hx
          · exact rulePair_ne_one rules i x hx
          · rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
            exact twistLetter_ne_one (rules i).length y (ih y hy)

private theorem baseLetters_head_fst (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    ∀ x ∈ (baseLetters rules letters).head?, x.1 = 0 := by
  induction letters with
  | nil => simp [baseLetters]
  | cons q rest ih =>
      cases q with
      | inl beta =>
          rw [baseLetters, List.head?_map]
          intro x hx
          rcases Option.mem_map.1 hx with ⟨y, hy, rfl⟩
          simpa using ih y hy
      | inr i => simp [baseLetters, rulePair]

/-- The base trace alternates between the two free factors. -/
theorem baseLetters_chain_ne (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    (baseLetters rules letters).IsChain fun x y ↦ x.1 ≠ y.1 := by
  induction letters with
  | nil => simp [baseLetters]
  | cons q rest ih =>
      cases q with
      | inl beta =>
          simpa [baseLetters] using twistLetter_chain 1 ih
      | inr i =>
          rw [baseLetters]
          apply List.IsChain.append
          · simp [rulePair]
          · exact twistLetter_chain (rules i).length ih
          · intro x hx y hy
            have hxeq :
                (⟨1, (invertC5 ^ (rules i).length)
                  (BorisovModFiveQuotient.c5Generator ^ (i.val + 1))⟩ :
                    BaseLetter) = x := by
              simpa [rulePair] using hx
            have hx1 : x.1 = 1 := by
              rw [← hxeq]
            rw [List.head?_map] at hy
            rcases Option.mem_map.1 hy with ⟨z, hz, rfl⟩
            have hz0 : z.1 = 0 := baseLetters_head_fst rules rest z hz
            simp only [twistLetter_fst, hx1, hz0]
            decide

/-- The displayed base trace, packaged as a reduced free-product word. -/
def baseWord (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) : CoprodI.Word Factor5 where
  toList := baseLetters rules letters
  ne_one := baseLetters_ne_one rules letters
  chain_ne := baseLetters_chain_ne rules letters

@[simp] theorem baseWord_prod (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    (baseWord rules letters).prod = letterProd (baseLetters rules letters) := rfl

/-- The canonical normal form of the base-coordinate product is exactly the
reduced trace constructed above. -/
theorem normalForm_letterProd (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    CoprodI.Word.equiv (letterProd (baseLetters rules letters)) =
      baseWord rules letters := by
  apply CoprodI.Word.equiv.symm.injective
  rw [Equiv.symm_apply_apply]
  change letterProd (baseLetters rules letters) =
    (baseWord rules letters).prod
  exact (baseWord_prod rules letters).symm

/-- Every displayed rule letter contributes exactly two syllables to the
canonical free-product normal form, while stable letters contribute none. -/
theorem normalForm_letterProd_length (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    (CoprodI.Word.equiv
      (letterProd (baseLetters rules letters))).toList.length =
        2 * basisRuleCount letters := by
  rw [normalForm_letterProd]
  exact baseLetters_length rules letters

/-- The concrete two-factor version used for mod-five coefficient words. -/
theorem normalForm_length_factor_zero_one_le_two (d e : C5) :
    (CoprodI.Word.equiv
      (CoprodI.of (M := Factor5) (i := (0 : Fin 2)) d *
        CoprodI.of (M := Factor5) (i := (1 : Fin 2)) e)).toList.length ≤ 2 :=
  CoprodIWordLength.normalForm_length_mul_of_of_le_two
    (M := Factor5) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) d e

end

end BorisovModFiveWordLength
end Undecidability
