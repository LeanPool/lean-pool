/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.Construction
public import LeanPool.SmallUndecidableGroups.GroupTheory.CoprodILemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum

/-!
# RightNormalForm

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability.MillerTancer

open Monoid

/-- The right free factor used to construct the amalgam. -/
abbrev RightFactor := FreeGroup (Fin 2)

/-- The right-factor free generator `beta`. -/
def rightBeta : RightFactor := FreeGroup.of (0 : Fin 2)
/-- The right-factor free generator `gamma`. -/
def rightGamma : RightFactor := FreeGroup.of (1 : Fin 2)

/-- The five right-hand amalgamating generators of the Miller–Tancer construction. -/
def rightBasis : Fin 5 → RightFactor
  | 0 => rightBeta
  | 1 => rightGamma⁻¹ * rightBeta⁻¹ * rightGamma * rightBeta * rightGamma
  | 2 => (rightGamma ^ 2)⁻¹ * rightBeta⁻¹ * rightGamma * rightBeta * rightGamma ^ 2
  | 3 => (rightGamma ^ 3)⁻¹ * rightBeta * rightGamma ^ 3
  | 4 => (rightGamma ^ 4)⁻¹ * rightBeta * rightGamma ^ 4

/-- The homomorphism freely extending the five right-hand amalgamating generators. -/
def rightBasisMap : FreeGroup (Fin 5) →* RightFactor :=
  FreeGroup.lift rightBasis

/-- The infinite cyclic group, written multiplicatively. -/
abbrev ZMul := Multiplicative ℤ
/-- An indexed family of infinite cyclic groups. -/
abbrev CyclicFamily (d : ℕ) : Fin d → Type := fun _ => ZMul
/-- The free product of the indicated number of infinite cyclic groups. -/
abbrev CyclicCoprod (d : ℕ) := Monoid.CoprodI (CyclicFamily d)

namespace RightNormalForm

open Monoid.CoprodI

/-- The indexed free product realizing the right-hand free group. -/
abbrev R := CyclicCoprod 2

/-- The generator `b` in Miller–Tancer’s right normal form construction. -/
def b : R := CoprodI.of (i := (0 : Fin 2)) (Multiplicative.ofAdd 1)
/-- The generator of the second cyclic factor, representing `gamma`. -/
def g : R := CoprodI.of (i := (1 : Fin 2)) (Multiplicative.ofAdd 1)

/-- The five right-hand basis elements in the cyclic-factor normal-form model. -/
def elt : Fin 5 → R
  | 0 => b
  | 1 => g⁻¹ * b⁻¹ * g * b * g
  | 2 => (g ^ 2)⁻¹ * b⁻¹ * g * b * g ^ 2
  | 3 => (g ^ 3)⁻¹ * b * g ^ 3
  | 4 => (g ^ 4)⁻¹ * b * g ^ 4

/-- The cyclic factor containing the two endpoints of each basis-power block. -/
def side : Fin 5 → Fin 2
  | 0 => 0
  | _ => 1

/-- Concatenate nonempty reduced words whose adjacent factor labels differ. -/
def app {i j k l : Fin 2}
    (u : CoprodI.NeWord (CyclicFamily 2) i j) (h : j ≠ k)
    (v : CoprodI.NeWord (CyclicFamily 2) k l) :=
  CoprodI.NeWord.append u h v

/-- The singleton reduced block representing a nonzero power of the first basis element. -/
def block₀ (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 0 0 :=
  NeWord.singletonZ 0 k hk

/-- The reduced block for a power of a conjugated twisted basis element. -/
def blockTwisted (r : ℕ) (hr : 0 < r) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  app (NeWord.singletonZ 1 (-r) (by omega)) (by decide)
    (app (NeWord.singletonZ 0 (-1) (by omega)) (by decide)
      (app (NeWord.singletonZ 1 k hk) (by decide)
        (app (NeWord.singletonZ 0 1 (by omega)) (by decide)
          (NeWord.singletonZ 1 r (by omega)))))

/-- The reduced block for a nonzero power of the second basis element. -/
def block₁ (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  blockTwisted 1 (by omega) k hk

/-- The reduced block for a nonzero power of the third basis element. -/
def block₂ (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  blockTwisted 2 (by omega) k hk

/-- The reduced block for a conjugate of a nonzero cyclic power. -/
def blockConjugate (r : ℕ) (hr : 0 < r) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  app (NeWord.singletonZ 1 (-r) (by omega)) (by decide)
    (app (NeWord.singletonZ 0 k hk) (by decide)
      (NeWord.singletonZ 1 r (by omega)))

/-- The reduced block for a nonzero power of the fourth basis element. -/
def block₃ (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  blockConjugate 3 (by omega) k hk

/-- The reduced block for a nonzero power of the fifth basis element. -/
def block₄ (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (CyclicFamily 2) 1 1 :=
  blockConjugate 4 (by omega) k hk

/-- The reduced block associated with a basis element and a nonzero exponent. -/
def block : (i : Fin 5) → (k : ℤ) → (hk : k ≠ 0) →
    CoprodI.NeWord (CyclicFamily 2) (side i) (side i)
  | 0, k, hk => block₀ k hk
  | 1, k, hk => block₁ k hk
  | 2, k, hk => block₂ k hk
  | 3, k, hk => block₃ k hk
  | 4, k, hk => block₄ k hk

private theorem conjugate_zpow {G : Type*} [Group G]
    (a x : G) (k : ℤ) : (a⁻¹ * x * a) ^ k = a⁻¹ * x ^ k * a := by
  simpa using (conj_zpow (a := a⁻¹) (b := x) (i := k))

private theorem block₀_prod (k : ℤ) (hk : k ≠ 0) :
    (block₀ k hk).prod = b ^ k := by
  change CoprodI.of (i := (0 : Fin 2)) (Multiplicative.ofAdd k) = b ^ k
  exact CoprodI.of_int_eq_zpow 0 k

private theorem blockTwisted_prod (r : ℕ) (hr : 0 < r)
    (k : ℤ) (hk : k ≠ 0) :
    (blockTwisted r hr k hk).prod =
      ((g ^ r)⁻¹ * b⁻¹ * g * b * g ^ r) ^ k := by
  rw [show ((g ^ r)⁻¹ * b⁻¹ * g * b * g ^ r : R) =
      (g ^ r)⁻¹ * (b⁻¹ * g * b) * g ^ r by group]
  rw [conjugate_zpow, conjugate_zpow]
  simp only [blockTwisted, app, NeWord.singletonZ, CoprodI.NeWord.append_prod,
    CoprodI.NeWord.prod_singleton]
  rw [CoprodI.of_int_eq_zpow (1 : Fin 2) k]
  rw [CoprodI.of_int_eq_zpow (1 : Fin 2) (-r),
    CoprodI.of_int_eq_zpow (0 : Fin 2) (-1),
    CoprodI.of_int_eq_zpow (0 : Fin 2) 1,
    CoprodI.of_int_eq_zpow (1 : Fin 2) r]
  simp [b, g]
  group

private theorem block₁_prod (k : ℤ) (hk : k ≠ 0) :
    (block₁ k hk).prod = elt 1 ^ k := by
  simpa [block₁, elt] using blockTwisted_prod 1 (by omega) k hk

private theorem block₂_prod (k : ℤ) (hk : k ≠ 0) :
    (block₂ k hk).prod = elt 2 ^ k := by
  simpa [block₂, elt] using blockTwisted_prod 2 (by omega) k hk

private theorem blockConjugate_prod (r : ℕ) (hr : 0 < r)
    (k : ℤ) (hk : k ≠ 0) :
    (blockConjugate r hr k hk).prod = ((g ^ r)⁻¹ * b * g ^ r) ^ k := by
  rw [conjugate_zpow]
  simp only [blockConjugate, app, NeWord.singletonZ, CoprodI.NeWord.append_prod,
    CoprodI.NeWord.prod_singleton]
  rw [CoprodI.of_int_eq_zpow (0 : Fin 2) k]
  rw [CoprodI.of_int_eq_zpow (1 : Fin 2) (-r),
    CoprodI.of_int_eq_zpow (1 : Fin 2) r]
  simp [b, g]
  group

private theorem block₃_prod (k : ℤ) (hk : k ≠ 0) :
    (block₃ k hk).prod = elt 3 ^ k := by
  simpa [block₃, elt] using blockConjugate_prod 3 (by omega) k hk

private theorem block₄_prod (k : ℤ) (hk : k ≠ 0) :
    (block₄ k hk).prod = elt 4 ^ k := by
  simpa [block₄, elt] using blockConjugate_prod 4 (by omega) k hk

@[simp]
theorem block_prod (i : Fin 5) (k : ℤ) (hk : k ≠ 0) :
    (block i k hk).prod = elt i ^ k := by
  refine Fin.cases (block₀_prod k hk) (fun i₁ => ?_) i
  refine Fin.cases (block₁_prod k hk) (fun i₂ => ?_) i₁
  refine Fin.cases (block₂_prod k hk) (fun i₃ => ?_) i₂
  refine Fin.cases (block₃_prod k hk) (fun i₄ => ?_) i₃
  refine Fin.cases (block₄_prod k hk) (fun i₅ => ?_) i₄
  exact Fin.elim0 i₅

/-- The value prescribed for the first letter of a basis-power block. -/
def headValue : Fin 5 → ZMul → ZMul
  | 0, x => x
  | 1, _ => Multiplicative.ofAdd (-1)
  | 2, _ => Multiplicative.ofAdd (-2)
  | 3, _ => Multiplicative.ofAdd (-3)
  | 4, _ => Multiplicative.ofAdd (-4)

/-- The value prescribed for the last letter of a basis-power block. -/
def lastValue : Fin 5 → ZMul → ZMul
  | 0, x => x
  | 1, _ => Multiplicative.ofAdd 1
  | 2, _ => Multiplicative.ofAdd 2
  | 3, _ => Multiplicative.ofAdd 3
  | 4, _ => Multiplicative.ofAdd 4

@[simp]
theorem block_head (i : Fin 5) (k : ℤ) (hk : k ≠ 0) :
    (block i k hk).head = headValue i (Multiplicative.ofAdd k) := by
  fin_cases i <;> rfl

@[simp]
theorem block_last (i : Fin 5) (k : ℤ) (hk : k ≠ 0) :
    (block i k hk).last = lastValue i (Multiplicative.ofAdd k) := by
  fin_cases i <;> rfl

theorem side_eq_zero_iff (i : Fin 5) : side i = 0 ↔ i = 0 := by
  fin_cases i <;> simp [side]

theorem block_append_or_zero (i : Fin 5) (k : ℤ) (hk : k ≠ 0) :
    i = 0 ∨ NeWord.IsAppend (block i k hk) := by
  fin_cases i
  · exact Or.inl rfl
  all_goals exact Or.inr trivial

theorem boundary_ne_one (i j : Fin 5) (hij : i ≠ j)
    (hside : side i = side j) (x y : ZMul) :
    lastValue i x * headValue j y ≠ 1 := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals try norm_num [side] at hside
  all_goals
    intro h
    have hh := congrArg Multiplicative.toAdd h
    norm_num [headValue, lastValue] at hh

/-- The homomorphism sending an integer exponent to a power of the corresponding basis element. -/
def cyclicMap (i : Fin 5) : ZMul →* R :=
  zpowersHom R (elt i)

/-- The homomorphism induced by the five cyclic basis power maps. -/
def lift : CyclicCoprod 5 →* R :=
  CoprodI.lift cyclicMap

/-- A reduced representative of a mapped word, together with its evaluation and boundary properties.
-/
structure Image {i j : Fin 5}
    (w : CoprodI.NeWord (CyclicFamily 5) i j) where
  /-- The reduced-word representative carrying the stated evaluation and boundary properties. -/
  word : CoprodI.NeWord (CyclicFamily 2) (side i) (side j)
  head_eq : word.head = headValue i w.head
  last_eq : word.last = lastValue j w.last
  prod_eq : word.prod = lift w.prod
  append_or_zero : (i = 0 ∧ j = 0) ∨ NeWord.IsAppend word

/-- Construct the reduced image of an arbitrary source normal-form word. -/
noncomputable def image {i j : Fin 5}
    (w : CoprodI.NeWord (CyclicFamily 5) i j) : Image w := by
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
      · exact (block_append_or_zero i k hk).imp (fun hi => ⟨hi, hi⟩) id
  | @append i j k l w₁ hjk w₂ ih₁ ih₂ =>
      by_cases hs : side j = side k
      · let word₂ : CoprodI.NeWord (CyclicFamily 2) (side j) (side l) :=
          hs.symm ▸ ih₂.word
        have hj0 : j ≠ 0 := by
          intro hj
          subst j
          have hk0 : k = 0 := (side_eq_zero_iff k).mp (by simpa [side] using hs.symm)
          exact hjk hk0.symm
        have hk0 : k ≠ 0 := by
          intro hk
          subst k
          have hjzero : j = 0 := (side_eq_zero_iff j).mp hs
          exact hjk hjzero
        have ih₁_append : NeWord.IsAppend ih₁.word :=
          ih₁.append_or_zero.resolve_left (fun h => hj0 h.2)
        have ih₂_append : NeWord.IsAppend ih₂.word :=
          ih₂.append_or_zero.resolve_left (fun h => hk0 h.1)
        have word₂_append : NeWord.IsAppend word₂ :=
          (NeWord.cast_start_isAppend hs.symm ih₂.word).2 ih₂_append
        have word₂_head : word₂.head = headValue k w₂.head := by
          rw [show word₂.head = ih₂.word.head from
            NeWord.cast_start_head (G := ZMul) hs.symm ih₂.word]
          exact ih₂.head_eq
        have word₂_last : word₂.last = lastValue l w₂.last := by
          rw [show word₂.last = ih₂.word.last from
            NeWord.cast_start_last hs.symm ih₂.word]
          exact ih₂.last_eq
        have word₂_prod : word₂.prod = lift w₂.prod := by
          rw [show word₂.prod = ih₂.word.prod from
            NeWord.cast_start_prod hs.symm ih₂.word]
          exact ih₂.prod_eq
        have hboundary : ih₁.word.last * word₂.head ≠ 1 := by
          rw [ih₁.last_eq, word₂_head]
          exact boundary_ne_one j k hjk hs w₁.last w₂.head
        let v := NeWord.merge ih₁.word word₂ hboundary
        refine ⟨v, ?_, ?_, ?_, ?_⟩
        · rw [show v.head = ih₁.word.head from
            NeWord.merge_head_of_isAppend_left _ _ _ ih₁_append]
          exact ih₁.head_eq
        · rw [show v.last = word₂.last from
            NeWord.merge_last_of_isAppend_right _ _ _ word₂_append]
          exact word₂_last
        · rw [NeWord.merge_prod, ih₁.prod_eq, word₂_prod]
          simp [lift]
        · exact Or.inr (NeWord.merge_isAppend_of_left _ _ _ ih₁_append)
      · let v := CoprodI.NeWord.append ih₁.word hs ih₂.word
        refine ⟨v, ?_, ?_, ?_, Or.inr trivial⟩
        · simpa [v] using ih₁.head_eq
        · simpa [v] using ih₂.last_eq
        · rw [CoprodI.NeWord.append_prod, ih₁.prod_eq, ih₂.prod_eq]
          simp [lift]

theorem lift_injective : Function.Injective lift := by
  apply CoprodI.lift_injective_of_neWord_nontrivial cyclicMap
  intro i j w
  change lift w.prod ≠ 1
  rw [← (image w).prod_eq]
  exact CoprodI.NeWord.prod_ne_one _

end RightNormalForm

namespace RightNormalForm

/-- The homomorphism freely extending the displayed group-valued basis. -/
def freeMap : FreeGroup (Fin 5) →* R :=
  FreeGroup.lift elt

theorem freeMap_eq : freeMap = lift.comp (CoprodI.intOfFree (Fin 5)) := by
  apply FreeGroup.ext_hom
  intro i
  simp [freeMap, lift, cyclicMap, CoprodI.intOfFree]

theorem freeMap_injective : Function.Injective freeMap := by
  rw [freeMap_eq]
  exact lift_injective.comp (CoprodI.intOfFree_injective (Fin 5))

theorem original_rightBasisMap_comp :
    (CoprodI.intOfFree (Fin 2)).comp rightBasisMap = freeMap := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp [CoprodI.intOfFree, rightBasisMap, rightBasis, freeMap, elt, b, g,
      rightBeta, rightGamma]

theorem original_rightBasisMap_injective : Function.Injective rightBasisMap := by
  intro x y h
  apply freeMap_injective
  rw [← original_rightBasisMap_comp]
  exact congrArg (CoprodI.intOfFree (Fin 2)) h

end RightNormalForm

end Undecidability.MillerTancer
