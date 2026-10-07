/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Construction
public import LeanPool.SmallUndecidableGroups.GroupTheory.CoprodILemmas
public import Mathlib.Tactic.Group

/-!
# Gordon 2022: the right-hand free basis

The right-hand amalgamating words in Gordon's Lemma 2.1 are words in the
free group on `b, beta`.  This file proves that they freely generate.  The
proof maps that free group to the coproduct `Z * Z` and assigns an explicit
reduced normal form to every reduced word in nonzero powers of the proposed
basis elements.
-/

@[expose] public section

namespace Undecidability.Gordon

open Monoid

/-- The right free factor used to construct the amalgam. -/
abbrev RightFactor := FreeGroup (Fin 2)

/-- The free generator `b` of the right-hand factor. -/
def rightB : RightFactor := FreeGroup.of (0 : Fin 2)
/-- The free generator `beta` of the right-hand factor. -/
def rightBeta : RightFactor := FreeGroup.of (1 : Fin 2)

/-- Gordon's right-hand conjugate `beta^(-r) * b * beta^r`. -/
def rightU (r : ℕ) : RightFactor :=
  (rightBeta ^ r)⁻¹ * rightB * rightBeta ^ r

/-- The right-hand amalgamating elements in Gordon's construction. -/
def rightBasis {n : ℕ} : BasisIndex n → RightFactor
  | .conjugateA => rightB ^ 2
  | .conjugateAlpha => rightB * rightBeta * rightB⁻¹
  | .old i => rightU (i.1 + 1)
  | .commutator => rightU (n + 1)

/-- The homomorphism freely extending Gordon’s right-hand amalgamating basis. -/
def rightBasisMap (n : ℕ) : FreeGroup (BasisIndex n) →* RightFactor :=
  FreeGroup.lift rightBasis

namespace RightNormalForm

open Monoid.CoprodI

/-- The infinite cyclic group, written multiplicatively. -/
abbrev ZMul := Multiplicative ℤ
/-- An indexed family of infinite cyclic groups. -/
abbrev CyclicFamily (d : ℕ) : Fin d → Type := fun _ => ZMul
/-- The free product of the indicated number of infinite cyclic groups. -/
abbrev CyclicCoprod (d : ℕ) := Monoid.CoprodI (CyclicFamily d)
/-- The cyclic factor assigned to each proposed basis element. -/
abbrev BasisFamily (n : ℕ) : BasisIndex n → Type := fun _ => ZMul
/-- The free product with one cyclic factor for each proposed basis element. -/
abbrev BasisCoprod (n : ℕ) := Monoid.CoprodI (BasisFamily n)
/-- The indexed free product realizing the right-hand free group. -/
abbrev R := CyclicCoprod 2

/-- The generator `b` in Gordon’s right normal form construction. -/
def b : R := CoprodI.of (i := (0 : Fin 2)) (Multiplicative.ofAdd 1)
/-- The generator `beta` in Gordon’s right normal form construction. -/
def beta : R := CoprodI.of (i := (1 : Fin 2)) (Multiplicative.ofAdd 1)

/-- The conjugate `beta⁻ʳ * b * betaʳ` in the right-hand normal-form model. -/
def u (r : ℕ) : R := (beta ^ r)⁻¹ * b * beta ^ r

/-- The right-hand proposed basis, represented in the indexed free product. -/
def elt {n : ℕ} : BasisIndex n → R
  | .conjugateA => b ^ 2
  | .conjugateAlpha => b * beta * b⁻¹
  | .old i => u (i.1 + 1)
  | .commutator => u (n + 1)

/-- The free factor containing both endpoints of the normal-form block. -/
def side {n : ℕ} : BasisIndex n → Fin 2
  | .conjugateA => 0
  | .conjugateAlpha => 0
  | .old _ => 1
  | .commutator => 1

/-- Concatenate nonempty reduced words whose adjacent factor labels differ. -/
def app {i j k l : Fin 2}
    (x : CoprodI.NeWord (CyclicFamily 2) i j) (h : j ≠ k)
    (y : CoprodI.NeWord (CyclicFamily 2) k l) :=
  CoprodI.NeWord.append x h y

/-- The reduced block representing a power of the first basis element. -/
def blockA (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 0 0 :=
  CoprodI.NeWord.singletonZ 0 (2 * k) (by omega)

/-- The reduced block representing a power of the conjugated cyclic basis element. -/
def blockAlpha (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 0 0 :=
  app (CoprodI.NeWord.singletonZ 0 1 (by omega)) (by decide)
    (app (CoprodI.NeWord.singletonZ 1 k hk) (by decide)
      (CoprodI.NeWord.singletonZ 0 (-1) (by omega)))

/-- The positive exponent `i + 1` assigned to an original generator. -/
def oldExponent (i : Fin n) : ℤ := i.1 + 1

theorem oldExponent_pos (i : Fin n) : 0 < oldExponent i := by
  simp [oldExponent]

/-- The exponent `n + 1` reserved for the distinguished commutator. -/
def commutatorExponent (n : ℕ) : ℤ := n + 1

theorem commutatorExponent_pos (n : ℕ) : 0 < commutatorExponent n := by
  simp [commutatorExponent]

/-- The reduced block conjugating a nonzero power by the indicated cyclic power. -/
def blockU (r : ℤ) (hr : 0 < r) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  app (CoprodI.NeWord.singletonZ 1 (-r) (neg_ne_zero.mpr (ne_of_gt hr))) (by decide)
    (app (CoprodI.NeWord.singletonZ 0 k hk) (by decide)
      (CoprodI.NeWord.singletonZ 1 r (ne_of_gt hr)))

/-- The reduced block representing a power of the encoded original generator. -/
def blockOld (i : Fin n) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  blockU (oldExponent i) (oldExponent_pos i) k hk

/-- The reduced block representing a power of the distinguished commutator element. -/
def blockCommutator (n : ℕ) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  blockU (commutatorExponent n) (commutatorExponent_pos n) k hk

/-- The reduced block associated with a basis element and a nonzero exponent. -/
def block (i : BasisIndex n) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) (side i) (side i) := by
  cases i with
  | conjugateA => exact blockA k hk
  | conjugateAlpha => exact blockAlpha k hk
  | old i => exact blockOld i k hk
  | commutator => exact blockCommutator n k hk

private theorem conjugate_zpow_right {G : Type*} [Group G]
    (a x : G) (k : ℤ) : (a * x * a⁻¹) ^ k = a * x ^ k * a⁻¹ := by
  simp

private theorem conjugate_zpow_left {G : Type*} [Group G]
    (a x : G) (k : ℤ) : (a⁻¹ * x * a) ^ k = a⁻¹ * x ^ k * a := by
  simpa using conjugate_zpow_right a⁻¹ x k

private theorem blockA_prod (k : ℤ) (hk : k ≠ 0) :
    (blockA k hk).prod = elt (.conjugateA : BasisIndex n) ^ k := by
  simp only [blockA, CoprodI.NeWord.singletonZ, CoprodI.NeWord.prod_singleton]
  rw [CoprodI.of_int_eq_zpow]
  simp only [Fin.isValue, elt, b]
  rw [zpow_mul]
  rfl

private theorem blockAlpha_prod (k : ℤ) (hk : k ≠ 0) :
    (blockAlpha k hk).prod = elt (.conjugateAlpha : BasisIndex n) ^ k := by
  change (blockAlpha k hk).prod = (b * beta * b⁻¹) ^ k
  rw [conjugate_zpow_right]
  simp only [blockAlpha, app, CoprodI.NeWord.singletonZ, CoprodI.NeWord.append_prod,
    CoprodI.NeWord.prod_singleton]
  rw [CoprodI.of_int_eq_zpow (1 : Fin 2) k]
  simp [b, beta]
  group

private theorem blockU_prod (r : ℤ) (hr : 0 < r) (k : ℤ) (hk : k ≠ 0) :
    (blockU r hr k hk).prod = ((beta ^ r)⁻¹ * b * beta ^ r) ^ k := by
  rw [conjugate_zpow_left]
  simp only [blockU, app, CoprodI.NeWord.singletonZ, CoprodI.NeWord.append_prod,
    CoprodI.NeWord.prod_singleton]
  rw [CoprodI.of_int_eq_zpow (0 : Fin 2) k,
    CoprodI.of_int_eq_zpow (1 : Fin 2) (-r),
    CoprodI.of_int_eq_zpow (1 : Fin 2) r]
  simp [b, beta]
  group

private theorem blockOld_prod (i : Fin n) (k : ℤ) (hk : k ≠ 0) :
    (blockOld i k hk).prod = elt (.old i) ^ k := by
  rw [blockOld, blockU_prod]
  change ((beta ^ oldExponent i)⁻¹ * b * beta ^ oldExponent i) ^ k =
    ((beta ^ (i.1 + 1))⁻¹ * b * beta ^ (i.1 + 1)) ^ k
  rw [show oldExponent i = ((i.1 + 1 : ℕ) : ℤ) by simp [oldExponent], zpow_natCast]

private theorem blockCommutator_prod (n : ℕ) (k : ℤ) (hk : k ≠ 0) :
    (blockCommutator n k hk).prod =
      elt (.commutator : BasisIndex n) ^ k := by
  rw [blockCommutator, blockU_prod]
  change ((beta ^ commutatorExponent n)⁻¹ * b * beta ^ commutatorExponent n) ^ k =
    ((beta ^ (n + 1))⁻¹ * b * beta ^ (n + 1)) ^ k
  rw [show commutatorExponent n = ((n + 1 : ℕ) : ℤ) by
    simp [commutatorExponent], zpow_natCast]

@[simp] theorem block_prod (i : BasisIndex n) (k : ℤ) (hk : k ≠ 0) :
    (block i k hk).prod = elt i ^ k := by
  cases i with
  | conjugateA => exact blockA_prod k hk
  | conjugateAlpha => exact blockAlpha_prod k hk
  | old i => exact blockOld_prod i k hk
  | commutator => exact blockCommutator_prod n k hk

/-- The value prescribed for the first letter of a basis-power block. -/
def headValue : BasisIndex n → ZMul → ZMul
  | .conjugateA, x => Multiplicative.ofAdd (2 * x.toAdd)
  | .conjugateAlpha, _ => Multiplicative.ofAdd 1
  | .old i, _ => Multiplicative.ofAdd (-oldExponent i)
  | .commutator, _ => Multiplicative.ofAdd (-commutatorExponent n)

/-- The value prescribed for the last letter of a basis-power block. -/
def lastValue : BasisIndex n → ZMul → ZMul
  | .conjugateA, x => Multiplicative.ofAdd (2 * x.toAdd)
  | .conjugateAlpha, _ => Multiplicative.ofAdd (-1)
  | .old i, _ => Multiplicative.ofAdd (oldExponent i)
  | .commutator, _ => Multiplicative.ofAdd (commutatorExponent n)

@[simp] theorem block_head (i : BasisIndex n) (k : ℤ) (hk : k ≠ 0) :
    (block i k hk).head = headValue i (Multiplicative.ofAdd k) := by
  cases i <;> rfl

@[simp] theorem block_last (i : BasisIndex n) (k : ℤ) (hk : k ≠ 0) :
    (block i k hk).last = lastValue i (Multiplicative.ofAdd k) := by
  cases i <;> rfl

theorem side_eq_zero_iff (i : BasisIndex n) :
    side i = 0 ↔ i = .conjugateA ∨ i = .conjugateAlpha := by
  cases i <;> simp [side]

theorem block_append_or_small (i : BasisIndex n) (k : ℤ) (hk : k ≠ 0) :
    i = .conjugateA ∨ CoprodI.NeWord.IsAppend (block i k hk) := by
  cases i with
  | conjugateA => exact Or.inl rfl
  | conjugateAlpha => exact Or.inr trivial
  | old => exact Or.inr trivial
  | commutator => exact Or.inr trivial

/-- The initial letter satisfies the boundary condition for the specified basis element. -/
def GoodHead : BasisIndex n → ZMul → Prop
  | .conjugateA, x => x.toAdd ≠ 1
  | .conjugateAlpha, x => x = Multiplicative.ofAdd 1
  | .old i, x => x = Multiplicative.ofAdd (-oldExponent i)
  | .commutator, x => x = Multiplicative.ofAdd (-commutatorExponent n)

/-- The final letter satisfies the boundary condition for the specified basis element. -/
def GoodLast : BasisIndex n → ZMul → Prop
  | .conjugateA, x => x.toAdd ≠ -1
  | .conjugateAlpha, x => x = Multiplicative.ofAdd (-1)
  | .old i, x => x = Multiplicative.ofAdd (oldExponent i)
  | .commutator, x => x = Multiplicative.ofAdd (commutatorExponent n)

@[simp] theorem goodHead_headValue (i : BasisIndex n) (x : ZMul) :
    GoodHead i (headValue i x) := by
  cases i <;> simp [GoodHead, headValue]
  omega

@[simp] theorem goodLast_lastValue (i : BasisIndex n) (x : ZMul) :
    GoodLast i (lastValue i x) := by
  cases i <;> simp [GoodLast, lastValue]
  omega

theorem boundary_ne_one (i j : BasisIndex n) (hij : i ≠ j)
    (hside : side i = side j) (x y : ZMul)
    (hx : GoodLast i x) (hy : GoodHead j y) : x * y ≠ 1 := by
  change x.toAdd + y.toAdd ≠ 0
  cases i <;> cases j <;>
    simp_all [side, GoodHead, GoodLast, oldExponent, commutatorExponent,
      Fin.ext_iff] <;> omega

/-- The homomorphism sending an integer exponent to a power of the corresponding basis element. -/
def cyclicMap (i : BasisIndex n) : ZMul →* R :=
  zpowersHom R (elt i)

/-- The homomorphism induced by the power maps for the proposed cyclic factors. -/
def lift (n : ℕ) : BasisCoprod n →* R :=
  CoprodI.lift cyclicMap

/-- A reduced representative of a mapped word, together with its evaluation and boundary properties.
-/
structure Image {n : ℕ} {i j : BasisIndex n}
    (w : CoprodI.NeWord (BasisFamily n) i j) where
  /-- The reduced-word representative carrying the stated evaluation and boundary properties. -/
  word : CoprodI.NeWord (CyclicFamily 2) (side i) (side j)
  head_good : GoodHead i word.head
  last_good : GoodLast j word.last
  prod_eq : word.prod = lift n w.prod
  append_or_zero :
    (i = .conjugateA ∧ j = .conjugateA) ∨
      CoprodI.NeWord.IsAppend word

/-- Construct the reduced image of an arbitrary nonempty source normal form. -/
noncomputable def image {n : ℕ} {i j : BasisIndex n}
    (w : CoprodI.NeWord (BasisFamily n) i j) : Image w := by
  induction w with
  | @singleton i x hx =>
      let k : ℤ := x.toAdd
      have hk : k ≠ 0 := by simpa [k] using hx
      let v := block i k hk
      refine ⟨v, ?_, ?_, ?_, ?_⟩
      · simp [v, k]
      · simp [v, k]
      · rw [block_prod]
        simp [lift, cyclicMap, k]
      · exact (block_append_or_small i k hk).imp (fun hi => ⟨hi, hi⟩) id
  | @append i j k l w1 hjk w2 ih1 ih2 =>
      by_cases hs : side j = side k
      · let word2 : CoprodI.NeWord (CyclicFamily 2) (side j) (side l) :=
          hs.symm ▸ ih2.word
        have word2_head_good : GoodHead k word2.head := by
          rw [show word2.head = ih2.word.head from
            CoprodI.NeWord.cast_start_head (G := ZMul) hs.symm ih2.word]
          exact ih2.head_good
        have word2_last_good : GoodLast l word2.last := by
          rw [show word2.last = ih2.word.last from
            CoprodI.NeWord.cast_start_last hs.symm ih2.word]
          exact ih2.last_good
        have word2_prod : word2.prod = lift n w2.prod := by
          rw [show word2.prod = ih2.word.prod from
            CoprodI.NeWord.cast_start_prod hs.symm ih2.word]
          exact ih2.prod_eq
        have hboundary : ih1.word.last * word2.head ≠ 1 :=
          boundary_ne_one j k hjk hs _ _ ih1.last_good word2_head_good
        let v := CoprodI.NeWord.merge ih1.word word2 hboundary
        refine ⟨v, ?_, ?_, ?_, ?_⟩
        · rcases ih1.append_or_zero with hzero | happ
          · rcases hzero with ⟨rfl, rfl⟩
            have hkAlpha : k = .conjugateAlpha := by
              rcases (side_eq_zero_iff k).mp (by simpa [side] using hs.symm) with
                hkA | hkAlpha
              · exact (hjk hkA.symm).elim
              · exact hkAlpha
            subst k
            cases hword : ih1.word with
            | singleton x hx =>
                have hb : x * word2.head ≠ 1 := by
                  simpa [hword] using hboundary
                rw [show v.head = x * word2.head by
                  simp only [v, hword]
                  exact CoprodI.NeWord.merge_head_singleton x hx word2 hb]
                simp only [GoodHead]
                have hy : word2.head = Multiplicative.ofAdd 1 :=
                  word2_head_good
                rw [hy]
                intro heq
                simp only [side, Fin.isValue, toAdd_mul, toAdd_ofAdd, add_eq_right,
                  toAdd_eq_zero] at heq
                exact hx heq
            | append front hne tail =>
                have happend : CoprodI.NeWord.IsAppend ih1.word := by
                  rw [hword]
                  trivial
                rw [show v.head = ih1.word.head from
                  CoprodI.NeWord.merge_head_of_isAppend_left _ _ _ happend]
                exact ih1.head_good
          · rw [show v.head = ih1.word.head from
                CoprodI.NeWord.merge_head_of_isAppend_left _ _ _ happ]
            exact ih1.head_good
        · rcases ih2.append_or_zero with hzero | happ
          · rcases hzero with ⟨rfl, rfl⟩
            have hjAlpha : j = .conjugateAlpha := by
              rcases (side_eq_zero_iff j).mp (by simpa [side] using hs) with
                hjA | hjAlpha
              · exact (hjk hjA).elim
              · exact hjAlpha
            subst j
            cases hword : word2 with
            | singleton y hy =>
                have hb : ih1.word.last * y ≠ 1 := by
                  simpa [hword] using hboundary
                rw [show v.last = ih1.word.last * y by
                  simp only [v, hword]
                  exact CoprodI.NeWord.merge_last_singleton ih1.word y hy hb]
                simp only [GoodLast]
                have hx : ih1.word.last = Multiplicative.ofAdd (-1) :=
                  ih1.last_good
                rw [hx]
                intro heq
                simp only [side, Fin.isValue, Int.reduceNeg, ofAdd_neg, toAdd_mul, toAdd_inv,
                  toAdd_ofAdd, add_eq_left, toAdd_eq_zero] at heq
                exact hy heq
            | append front hne tail =>
                have happend : CoprodI.NeWord.IsAppend word2 := by
                  rw [hword]
                  trivial
                rw [show v.last = word2.last from
                  CoprodI.NeWord.merge_last_of_isAppend_right _ _ _ happend]
                exact word2_last_good
          · have word2_append : CoprodI.NeWord.IsAppend word2 :=
              (CoprodI.NeWord.cast_start_isAppend hs.symm ih2.word).2 happ
            rw [show v.last = word2.last from
              CoprodI.NeWord.merge_last_of_isAppend_right _ _ _ word2_append]
            exact word2_last_good
        · rw [CoprodI.NeWord.merge_prod, ih1.prod_eq, word2_prod]
          simp [lift]
        · rcases ih1.append_or_zero with hzero | happ
          · rcases hzero with ⟨_, hj0⟩
            have hkAlpha : k = .conjugateAlpha := by
              rcases (side_eq_zero_iff k).mp (by simpa [side, hj0] using hs.symm) with
                hkA | hkAlpha
              · exact (hjk (hj0.trans hkA.symm)).elim
              · exact hkAlpha
            subst k
            have ih2_append : CoprodI.NeWord.IsAppend ih2.word :=
              ih2.append_or_zero.resolve_left (by simp)
            have word2_append : CoprodI.NeWord.IsAppend word2 :=
              (CoprodI.NeWord.cast_start_isAppend hs.symm ih2.word).2 ih2_append
            exact Or.inr
              (CoprodI.NeWord.merge_isAppend_of_right _ _ _ word2_append)
          · exact Or.inr
              (CoprodI.NeWord.merge_isAppend_of_left _ _ _ happ)
      · let v := CoprodI.NeWord.append ih1.word hs ih2.word
        refine ⟨v, ?_, ?_, ?_, Or.inr trivial⟩
        · simpa [v] using ih1.head_good
        · simpa [v] using ih2.last_good
        · rw [CoprodI.NeWord.append_prod, ih1.prod_eq, ih2.prod_eq]
          simp [lift]

theorem lift_injective (n : ℕ) : Function.Injective (lift n) := by
  apply CoprodI.lift_injective_of_neWord_nontrivial cyclicMap
  intro i j w
  change lift n w.prod ≠ 1
  rw [← (image w).prod_eq]
  exact CoprodI.NeWord.prod_ne_one _

/-- The homomorphism freely extending the displayed group-valued basis. -/
def freeMap (n : ℕ) : FreeGroup (BasisIndex n) →* R :=
  FreeGroup.lift elt

theorem freeMap_eq (n : ℕ) : freeMap n =
    (lift n).comp (CoprodI.intOfFree (BasisIndex n)) := by
  apply FreeGroup.ext_hom
  intro i
  simp [freeMap, lift, cyclicMap, CoprodI.intOfFree]

theorem freeMap_injective (n : ℕ) : Function.Injective (freeMap n) := by
  rw [freeMap_eq n]
  exact (lift_injective n).comp (CoprodI.intOfFree_injective (BasisIndex n))

theorem rightBasisMap_comp (n : ℕ) :
    (CoprodI.intOfFree (Fin 2)).comp (rightBasisMap n) = freeMap n := by
  apply FreeGroup.ext_hom
  intro i
  cases i <;>
    simp [CoprodI.intOfFree, rightBasisMap, rightBasis,
      rightU, rightB, rightBeta, freeMap, elt, u, b, beta]

end RightNormalForm

/-- Gordon's right-hand amalgamating words freely generate. -/
theorem rightBasisMap_injective (n : ℕ) :
    Function.Injective (rightBasisMap n) := by
  intro x y h
  apply RightNormalForm.freeMap_injective n
  rw [← RightNormalForm.rightBasisMap_comp n]
  exact congrArg (CoprodI.intOfFree (Fin 2)) h

end Undecidability.Gordon
