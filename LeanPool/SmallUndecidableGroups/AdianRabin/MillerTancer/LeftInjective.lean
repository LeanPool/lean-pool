/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.LeftNormalForm
public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.LeftSplit
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.SplitIfs

/-! The left separated-conjugates map is injective when `w ≠ 1`. -/

@[expose] public section

namespace Undecidability.MillerTancer.LeftInjective

open Monoid
open LeftNormalForm

attribute [local implicit_reducible] OuterFactor

variable {G : Type} [Group G]

/-- The element obtained by multiplying the original normal generator by `beta`. -/
def q (z : G) : LeftProduct G := old z * beta

theorem q_ne_one (z : G) : q z ≠ 1 :=
  old_mul_beta_ne_one z

/-- The repeated suffix of a positive-power normal-form block. -/
def posRest (z : G) : (n : ℕ) →
    CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.alpha
  | 0 =>
      .append (baseSingleton (q z) (q_ne_one z)) (by decide)
        (alphaSingleton 4 (by norm_num))
  | n + 1 =>
      .append (baseSingleton (q z) (q_ne_one z)) (by decide)
        (.append (alphaSingleton 2 (by norm_num)) (by decide) (posRest z n))

/-- The full reduced normal-form block for a positive power. -/
def posBlock (z : G) (n : ℕ) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-2) (by norm_num)) (by decide) (posRest z n)

/-- The repeated suffix of a negative-power normal-form block. -/
def negRest (z : G) : (n : ℕ) →
    CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.base
  | 0 =>
      baseSingleton (q z)⁻¹ (inv_ne_one.mpr (q_ne_one z))
  | n + 1 =>
      .append (negRest z n) (by decide)
        (.append (alphaSingleton (-2) (by norm_num)) (by decide)
          (baseSingleton (q z)⁻¹ (inv_ne_one.mpr (q_ne_one z))))

/-- The initial segment of a negative-power normal-form block. -/
def negInit (z : G) (n : ℕ) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.base :=
  .append (alphaSingleton (-4) (by norm_num)) (by decide) (negRest z n)

/-- The full reduced normal-form block for a negative power. -/
def negBlock (z : G) (n : ℕ) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (negInit z n) (by decide) (alphaSingleton 2 (by norm_num))

private theorem posBlock_prod (z : G) (n : ℕ) :
    (posBlock z n).prod = outerLeftBasis (1 : G) z 4 ^ (n + 1) := by
  induction n with
  | zero =>
      simp only [posBlock, posRest, CoprodI.NeWord.append_prod,
        alphaSingleton_prod, baseSingleton_prod, outerLeftBasis, q]
      group
  | succ n ih =>
      calc
        (posBlock z (n + 1)).prod =
            outerLeftBasis (1 : G) z 4 * (posBlock z n).prod := by
          simp only [posBlock, posRest, CoprodI.NeWord.append_prod,
            alphaSingleton_prod, baseSingleton_prod, outerLeftBasis, q]
          group
        _ = outerLeftBasis (1 : G) z 4 *
            outerLeftBasis (1 : G) z 4 ^ (n + 1) := by rw [ih]
        _ = outerLeftBasis (1 : G) z 4 ^ (n + 1 + 1) :=
          (pow_succ' _ (n + 1)).symm

private theorem negBlock_prod_inv (z : G) (n : ℕ) :
    (negBlock z n).prod = (outerLeftBasis (1 : G) z 4)⁻¹ ^ (n + 1) := by
  induction n with
  | zero =>
      simp only [negBlock, negInit, negRest, CoprodI.NeWord.append_prod,
        alphaSingleton_prod, baseSingleton_prod, outerLeftBasis, q, baseOf_inv]
      group
  | succ n ih =>
      calc
        (negBlock z (n + 1)).prod =
            (negBlock z n).prod * (outerLeftBasis (1 : G) z 4)⁻¹ := by
          simp only [negBlock, negInit, negRest, CoprodI.NeWord.append_prod,
            alphaSingleton_prod, baseSingleton_prod, outerLeftBasis, q,
            baseOf_inv]
          group
        _ = (outerLeftBasis (1 : G) z 4)⁻¹ ^ (n + 1) *
            (outerLeftBasis (1 : G) z 4)⁻¹ := by rw [ih]
        _ = (outerLeftBasis (1 : G) z 4)⁻¹ ^ (n + 1 + 1) :=
          (pow_succ _ (n + 1)).symm

/-- The reduced word representing a nonzero power of the fourth left basis element. -/
def leftPowerWord4 (z : G) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact (hk rfl).elim
      | succ n => exact posBlock z n
  | negSucc n => exact negBlock z n

theorem leftPowerWord4_ofNat (z : G) (n : ℕ) :
    leftPowerWord4 z (Int.ofNat (n + 1))
      (Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n)) = posBlock z n := rfl

@[simp] theorem leftPowerWord4_negSucc (z : G) (n : ℕ) :
    leftPowerWord4 z (Int.negSucc n) (by omega) = negBlock z n := rfl

theorem leftPowerWord4_prod (w z : G) (k : ℤ) (hk : k ≠ 0) :
    (leftPowerWord4 z k hk).prod = outerLeftBasis w z 4 ^ k := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact (hk rfl).elim
      | succ n =>
          rw [leftPowerWord4_ofNat]
          simpa only [Int.ofNat_eq_natCast, zpow_natCast, outerLeftBasis]
            using posBlock_prod z n
  | negSucc n =>
      rw [leftPowerWord4_negSucc]
      simpa only [zpow_negSucc, inv_pow, outerLeftBasis] using negBlock_prod_inv z n

/-- The indicated integer power of the generator of the `alpha` cyclic factor. -/
def alphaVal (k : ℤ) : FreeGroup Unit := (FreeGroup.of ()) ^ k

theorem posRest_last (z : G) (n : ℕ) :
    (posRest z n).last = alphaVal 4 := by
  induction n with
  | zero => simp [posRest, alphaVal, alphaSingleton]
  | succ n ih => simpa [posRest] using ih

/-! The delicate part lives on generators `1,2,3,4`.  Generator `0` is
split off later as a separate cyclic free factor. -/

/-- The indices of the four nontrivial left basis blocks. -/
inductive SmallIndex
  | one
  | two
  | three
  | four
  deriving DecidableEq

/-- The four nontrivial basis elements used in the left injectivity argument. -/
def smallBasis (w z : G) : SmallIndex → MillerLeft G
  | .one => outerLeftBasis w z 1
  | .two => outerLeftBasis w z 2
  | .three => outerLeftBasis w z 3
  | .four => outerLeftBasis w z 4

/-- The reduced word realizing a nonzero power of a nontrivial left basis element. -/
def smallWord (w z : G) (hw : w ≠ 1) (i : SmallIndex) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  match i with
  | .one => leftPowerWord1 (G := G) k hk
  | .two => leftPowerWord2 (G := G) k hk
  | .three => leftPowerWord3 w hw k hk
  | .four => leftPowerWord4 z k hk

@[simp] theorem smallWord_prod (w z : G) (hw : w ≠ 1)
    (i : SmallIndex) (k : ℤ) (hk : k ≠ 0) :
    (smallWord w z hw i k hk).prod = smallBasis w z i ^ k := by
  cases i with
  | one => exact leftPowerWord1_prod w z k hk
  | two => exact leftPowerWord2_prod w z k hk
  | three => exact leftPowerWord3_prod w z hw k hk
  | four => exact leftPowerWord4_prod w z k hk

/-- The initial cyclic exponent of a nontrivial left basis block. -/
def smallHeadExp : SmallIndex → ℤ → ℤ
  | .one, _ => -1
  | .two, _ => -2
  | .three, _ => -3
  | .four, k => if 0 < k then -2 else -4

/-- The final cyclic exponent of a nontrivial left basis block. -/
def smallLastExp : SmallIndex → ℤ → ℤ
  | .one, _ => 1
  | .two, _ => 2
  | .three, _ => 3
  | .four, k => if 0 < k then 4 else 2

theorem smallWord_head (w z : G) (hw : w ≠ 1)
    (i : SmallIndex) (k : ℤ) (hk : k ≠ 0) :
    (smallWord w z hw i k hk).head = alphaVal (smallHeadExp i k) := by
  cases i with
  | one => simp [smallWord, leftPowerWord1, smallHeadExp, alphaVal, alphaSingleton]
  | two => simp [smallWord, leftPowerWord2, smallHeadExp, alphaVal, alphaSingleton]
  | three => simp [smallWord, leftPowerWord3, smallHeadExp, alphaVal, alphaSingleton]
  | four =>
      cases k with
      | ofNat n =>
          cases n with
          | zero => exact (hk rfl).elim
          | succ n =>
              rw [show smallWord w z hw .four (Int.ofNat (n + 1)) hk =
                posBlock z n by rfl]
              simp [posBlock, smallHeadExp, alphaVal, alphaSingleton]
      | negSucc n =>
          rw [show smallWord w z hw .four (Int.negSucc n) hk = negBlock z n by rfl]
          simp [negBlock, negInit, smallHeadExp, alphaVal, alphaSingleton]

theorem smallWord_last (w z : G) (hw : w ≠ 1)
    (i : SmallIndex) (k : ℤ) (hk : k ≠ 0) :
    (smallWord w z hw i k hk).last = alphaVal (smallLastExp i k) := by
  cases i with
  | one => simp [smallWord, leftPowerWord1, smallLastExp, alphaVal, alphaSingleton]
  | two => simp [smallWord, leftPowerWord2, smallLastExp, alphaVal, alphaSingleton]
  | three => simp [smallWord, leftPowerWord3, smallLastExp, alphaVal, alphaSingleton]
  | four =>
      cases k with
      | ofNat n =>
          cases n with
          | zero => exact (hk rfl).elim
          | succ n =>
              rw [show smallWord w z hw .four (Int.ofNat (n + 1)) hk =
                posBlock z n by rfl]
              rw [show smallLastExp .four (Int.ofNat (n + 1)) = 4 by
                simp [smallLastExp]]
              change (posRest z n).last = alphaVal 4
              exact posRest_last z n
      | negSucc n =>
          rw [show smallWord w z hw .four (Int.negSucc n) hk = negBlock z n by rfl]
          simp [negBlock, smallLastExp, alphaVal, alphaSingleton]

/-- The reduced tail exposing the base letter in a power of the second left basis element. -/
def tailTwo (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.alpha :=
  .append (baseSingleton beta⁻¹ (inv_ne_one.mpr beta_ne_one)) (by decide)
    (.append (alphaSingleton k hk) (by decide)
      (.append (baseSingleton beta beta_ne_one) (by decide)
        (alphaSingleton 2 (by norm_num))))

/-- A reduced prefix decomposition exposing a prescribed base-group letter. -/
structure Prefix (word : CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha)
    (x : LeftProduct G) where
  /-- The reduced tail beginning with the prescribed base-group letter. -/
  tail : CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.alpha
  tail_head : tail.head = x
  prod_eq : word.prod = outerAlpha ^ (-2 : ℤ) * tail.prod

/-- The prefix decomposition of a nonzero power of the second left basis element. -/
def prefixTwo (k : ℤ) (hk : k ≠ 0) :
    Prefix (leftPowerWord2 (G := G) k hk) beta⁻¹ where
  tail := tailTwo k hk
  tail_head := by rfl
  prod_eq := by
    simp [leftPowerWord2, tailTwo]

/-- The prefix decomposition of a positive power of the fourth left basis element. -/
def prefixFourPos (z : G) (n : ℕ) : Prefix (posBlock z n) (q z) where
  tail := posRest z n
  tail_head := by
    cases n <;> rfl
  prod_eq := by
    simp [posBlock]

theorem tailTwo_last (k : ℤ) (hk : k ≠ 0) :
    (tailTwo (G := G) k hk).last = alphaVal 2 := rfl

/-- A reduced word has an append constructor rather than a singleton constructor. -/
def IsAppend {i j : OuterIndex} :
    CoprodI.NeWord (OuterFactor G) i j → Prop
  | .singleton _ _ => False
  | .append _ _ _ => True

theorem tailTwo_isAppend (k : ℤ) (hk : k ≠ 0) :
    IsAppend (tailTwo (G := G) k hk) := by
  trivial

theorem posRest_isAppend (z : G) (n : ℕ) :
    IsAppend (posRest z n) := by
  cases n <;> trivial

theorem merge_head_of_isAppend_left {i j k : OuterIndex}
    (u : CoprodI.NeWord (OuterFactor G) i j)
    (v : CoprodI.NeWord (OuterFactor G) j k)
    (h : u.last * v.head ≠ 1) (hu : IsAppend u) :
    (CoprodI.NeWord.merge u v h).head = u.head := by
  cases u with
  | singleton => contradiction
  | append => rfl

theorem smallWord_isAppend (w z : G) (hw : w ≠ 1)
    (i : SmallIndex) (k : ℤ) (hk : k ≠ 0) :
    IsAppend (smallWord w z hw i k hk) := by
  cases i with
  | one => trivial
  | two => trivial
  | three => trivial
  | four =>
      cases k with
      | ofNat n =>
          cases n with
          | zero => exact (hk rfl).elim
          | succ n => trivial
      | negSucc n => trivial

private theorem alphaVal_mul_ne_one (r s : ℤ) (h : r + s ≠ 0) :
    alphaVal r * alphaVal s ≠ (1 : FreeGroup Unit) := by
  unfold alphaVal
  rw [← zpow_add]
  exact FreeGroup.unitGenerator_zpow_ne_one (r + s) h

/-- The two signed boundary configurations requiring a separate cancellation argument. -/
def Exceptional (i : SmallIndex) (r : ℤ) (j : SmallIndex) (s : ℤ) : Prop :=
  (i = .two ∧ j = .four ∧ 0 < s) ∨
    (i = .four ∧ r < 0 ∧ j = .two)

private theorem boundary_sum_ne_zero (i j : SmallIndex) (r s : ℤ)
    (hr : r ≠ 0) (hs : s ≠ 0) (hij : i ≠ j)
    (hex : ¬ Exceptional i r j s) :
    smallLastExp i r + smallHeadExp j s ≠ 0 := by
  cases i <;> cases j <;>
    simp [Exceptional, smallLastExp, smallHeadExp] at hij hex ⊢ <;>
    split_ifs at * <;> omega

theorem boundary_ne_one (w z : G) (hw : w ≠ 1)
    (i j : SmallIndex) (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hij : i ≠ j) (hex : ¬ Exceptional i r j s)
    (v : CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha)
    (hv : v.head = alphaVal (smallHeadExp j s)) :
    (smallWord w z hw i r hr).last * v.head ≠ 1 := by
  rw [smallWord_last, hv]
  exact alphaVal_mul_ne_one _ _ (boundary_sum_ne_zero i j r s hr hs hij hex)

/-- The product of the indicated powers of the four nontrivial left basis elements. -/
def evalSmall (w z : G) : List (SmallIndex × ℤ) → MillerLeft G
  | [] => 1
  | p :: l => smallBasis w z p.1 ^ p.2 * evalSmall w z l

/-- A reduced representative of a mapped word, together with its evaluation and boundary properties.
-/
structure Image (w z : G) (hw : w ≠ 1) (p : SmallIndex × ℤ)
    (rest : List (SmallIndex × ℤ)) where
  /-- The reduced-word representative carrying the stated evaluation and boundary properties. -/
  word : CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha
  prod_eq : word.prod = evalSmall w z (p :: rest)
  head_eq : word.head = alphaVal (smallHeadExp p.1 p.2)
  /-- The prefix decomposition when the leading basis index is the second one. -/
  prefixTwo : p.1 = .two → Prefix word beta⁻¹
  /-- The prefix decomposition for a positive leading power of the fourth basis element. -/
  prefixFourPositive : p.1 = .four → 0 < p.2 → Prefix word (q z)

/-- The reduced image of a one-block input word. -/
def singletonImage (w z : G) (hw : w ≠ 1) (i : SmallIndex) (k : ℤ)
    (hk : k ≠ 0) : Image w z hw (i, k) [] := by
  let u := smallWord w z hw i k hk
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · simp [u, evalSmall]
  · exact smallWord_head w z hw i k hk
  · intro hi
    change i = .two at hi
    subst i
    exact prefixTwo k hk
  · intro hi hkpos
    change i = .four at hi
    change 0 < k at hkpos
    subst i
    cases k with
    | ofNat n =>
        cases n with
        | zero => exact (hk rfl).elim
        | succ n =>
            change Prefix (posBlock z n) (q z)
            exact prefixFourPos z n
    | negSucc n => omega

/-- The reduced image formed when two adjacent input blocks are merged. -/
noncomputable def mergedImage (w z : G) (hw : w ≠ 1)
    (i j : SmallIndex) (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (rest : List (SmallIndex × ℤ))
    (tail : Image w z hw (j, s) rest) (hij : i ≠ j)
    (hex : ¬ Exceptional i r j s) : Image w z hw (i, r) ((j, s) :: rest) := by
  let u := smallWord w z hw i r hr
  have hu : IsAppend u := smallWord_isAppend w z hw i r hr
  have hb : u.last * tail.word.head ≠ 1 :=
    boundary_ne_one w z hw i j r s hr hs hij hex tail.word tail.head_eq
  let word := CoprodI.NeWord.merge u tail.word hb
  refine ⟨word, ?_, ?_, ?_, ?_⟩
  · rw [show word.prod = u.prod * tail.word.prod from
        CoprodI.NeWord.merge_prod u tail.word hb]
    rw [show u.prod = smallBasis w z i ^ r from smallWord_prod w z hw i r hr]
    rw [tail.prod_eq]
    rfl
  · rw [show word.head = u.head from merge_head_of_isAppend_left u tail.word hb hu]
    exact smallWord_head w z hw i r hr
  · intro hi
    change i = .two at hi
    subst i
    let bp := prefixTwo (G := G) r hr
    have hlast : bp.tail.last = u.last := by
      rw [show bp.tail.last = alphaVal 2 from tailTwo_last r hr]
      rw [smallWord_last]
      rfl
    have hbt : bp.tail.last * tail.word.head ≠ 1 := by
      rw [hlast]
      exact hb
    let t := CoprodI.NeWord.merge bp.tail tail.word hbt
    refine ⟨t, ?_, ?_⟩
    · rw [show t.head = bp.tail.head from
          merge_head_of_isAppend_left bp.tail tail.word hbt (tailTwo_isAppend r hr)]
      exact bp.tail_head
    · have huprod : u.prod = outerAlpha ^ (-2 : ℤ) * bp.tail.prod := by
        change (leftPowerWord2 (G := G) r hr).prod = _
        exact bp.prod_eq
      rw [show word.prod = u.prod * tail.word.prod from
        CoprodI.NeWord.merge_prod u tail.word hb]
      rw [huprod]
      rw [show t.prod = bp.tail.prod * tail.word.prod from
        CoprodI.NeWord.merge_prod bp.tail tail.word hbt]
      group
  · intro hi hpos
    change i = .four at hi
    change 0 < r at hpos
    subst i
    cases r with
    | ofNat n =>
        cases n with
        | zero => exact (hr rfl).elim
        | succ n =>
            let bp := prefixFourPos z n
            have hlast : bp.tail.last = u.last := by
              rw [show bp.tail.last = alphaVal 4 from posRest_last z n]
              rw [smallWord_last]
              simp [smallLastExp]
            have hbt : bp.tail.last * tail.word.head ≠ 1 := by
              rw [hlast]
              exact hb
            let t := CoprodI.NeWord.merge bp.tail tail.word hbt
            refine ⟨t, ?_, ?_⟩
            · rw [show t.head = bp.tail.head from
                  merge_head_of_isAppend_left bp.tail tail.word hbt
                    (posRest_isAppend z n)]
              exact bp.tail_head
            · have huprod : u.prod = outerAlpha ^ (-2 : ℤ) * bp.tail.prod := by
                change (posBlock z n).prod = _
                exact bp.prod_eq
              rw [show word.prod = u.prod * tail.word.prod from
                CoprodI.NeWord.merge_prod u tail.word hb]
              rw [huprod]
              rw [show t.prod = bp.tail.prod * tail.word.prod from
                CoprodI.NeWord.merge_prod bp.tail tail.word hbt]
              group
    | negSucc n => omega

/-- The reduced tail for the exceptional second-to-fourth block boundary. -/
def special24Tail (z : G) (r : ℤ) (hr : r ≠ 0)
    (v : CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.alpha)
    (hv : v.head = q z) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.alpha :=
  .append (baseSingleton beta⁻¹ (inv_ne_one.mpr beta_ne_one)) (by decide)
    (.append (alphaSingleton r hr) (by decide)
      (v.mulHead beta (by
        rw [hv]
        exact beta_mul_old_mul_beta_ne_one z)))

/-- The reduced word for the exceptional second-to-fourth block boundary. -/
def special24Word (z : G) (r : ℤ) (hr : r ≠ 0)
    (v : CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.alpha)
    (hv : v.head = q z) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-2) (by norm_num)) (by decide)
    (special24Tail z r hr v hv)

theorem special24Word_prod (z : G) (r : ℤ) (hr : r ≠ 0)
    (right : CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha)
    (pf : Prefix right (q z)) :
    (special24Word z r hr pf.tail pf.tail_head).prod =
      (leftPowerWord2 (G := G) r hr).prod * right.prod := by
  rw [pf.prod_eq]
  simp only [special24Word, special24Tail, CoprodI.NeWord.append_prod,
    CoprodI.NeWord.mulHead_prod, alphaSingleton_prod, baseSingleton_prod]
  simp only [leftPowerWord2, CoprodI.NeWord.append_prod, alphaSingleton_prod,
    baseSingleton_prod]
  simp only [baseOf]
  group

/-- The image construction for an exceptional second-to-fourth block boundary. -/
def special24Image (w z : G) (hw : w ≠ 1) (r s : ℤ)
    (hr : r ≠ 0) (_hs : s ≠ 0) (hpos : 0 < s)
    (rest : List (SmallIndex × ℤ))
    (tail : Image w z hw (.four, s) rest) :
    Image w z hw (.two, r) ((.four, s) :: rest) := by
  let pf := tail.prefixFourPositive rfl hpos
  let word := special24Word z r hr pf.tail pf.tail_head
  refine ⟨word, ?_, ?_, ?_, ?_⟩
  · rw [show word.prod = (leftPowerWord2 (G := G) r hr).prod * tail.word.prod from
        special24Word_prod z r hr tail.word pf]
    rw [leftPowerWord2_prod w z r hr, tail.prod_eq]
    rfl
  · rfl
  · intro _
    refine ⟨special24Tail z r hr pf.tail pf.tail_head, rfl, ?_⟩
    simp only [word, special24Word, CoprodI.NeWord.append_prod,
      alphaSingleton_prod]
  · intro h
    simp at h

theorem negInit_isAppend (z : G) (n : ℕ) : IsAppend (negInit z n) := by
  trivial

theorem negInit_head (z : G) (n : ℕ) :
    (negInit z n).head = alphaVal (-4) := rfl

theorem negInit_last (z : G) (n : ℕ) :
    (negInit z n).last = (q z)⁻¹ := by
  cases n <;> rfl

/-- The image construction for an exceptional fourth-to-second block boundary. -/
noncomputable def special42Image (w z : G) (hw : w ≠ 1) (n : ℕ)
    (s : ℤ) (_hs : s ≠ 0) (rest : List (SmallIndex × ℤ))
    (tail : Image w z hw (.two, s) rest) :
    Image w z hw (.four, Int.negSucc n) ((.two, s) :: rest) := by
  let pf := tail.prefixTwo rfl
  have hbt : (negInit z n).last * pf.tail.head ≠ 1 := by
    rw [negInit_last, pf.tail_head]
    exact inv_old_mul_beta_inv_mul_beta_inv_ne_one z
  let word := CoprodI.NeWord.merge (negInit z n) pf.tail hbt
  refine ⟨word, ?_, ?_, ?_, ?_⟩
  · have hprod : word.prod =
        (negBlock z n).prod * tail.word.prod := by
      rw [show word.prod = (negInit z n).prod * pf.tail.prod from
        CoprodI.NeWord.merge_prod (negInit z n) pf.tail hbt]
      rw [pf.prod_eq]
      simp only [negBlock, CoprodI.NeWord.append_prod, alphaSingleton_prod]
      group
    rw [hprod]
    have hbprod : (negBlock z n).prod =
      smallBasis w z .four ^ Int.negSucc n := by
      simpa only [smallWord, leftPowerWord4_negSucc] using
        smallWord_prod w z hw .four (Int.negSucc n) (by omega)
    rw [hbprod, tail.prod_eq]
    rfl
  · rw [show word.head = (negInit z n).head from
        merge_head_of_isAppend_left (negInit z n) pf.tail hbt
          (negInit_isAppend z n)]
    rw [negInit_head]
    simp [smallHeadExp]
  · intro h
    simp at h
  · intro _ hpos
    omega

/-- The reduced image of a list of nontrivial left basis powers. -/
noncomputable def imageList (w z : G) (hw : w ≠ 1)
    (p : SmallIndex × ℤ) (rest : List (SmallIndex × ℤ))
    (hp : p.2 ≠ 0) (hrest : ∀ q ∈ rest, q.2 ≠ 0)
    (hchain : (p :: rest).IsChain (fun a b ↦ a.1 ≠ b.1)) :
    Image w z hw p rest := by
  induction rest generalizing p with
  | nil =>
      exact singletonImage w z hw p.1 p.2 hp
  | cons q rest ih =>
      rcases p with ⟨i, r⟩
      rcases q with ⟨j, s⟩
      have hs : s ≠ 0 := hrest (j, s) (by simp)
      have hrest' : ∀ q ∈ rest, q.2 ≠ 0 := by
        intro q hq
        exact hrest q (by simp [hq])
      rw [List.isChain_cons_cons] at hchain
      let tail := ih (j, s) hs hrest' hchain.2
      have hij : i ≠ j := hchain.1
      by_cases hi2 : i = .two
      · subst i
        by_cases hj4 : j = .four
        · subst j
          by_cases hpos : 0 < s
          · exact special24Image w z hw r s hp hs hpos rest tail
          · exact mergedImage w z hw .two .four r s hp hs rest tail hij (by
              simp [Exceptional, hpos])
        · exact mergedImage w z hw .two j r s hp hs rest tail hij (by
            simp [Exceptional, hj4])
      · by_cases hi4 : i = .four
        · subst i
          by_cases hj2 : j = .two
          · subst j
            by_cases hneg : r < 0
            · cases r with
              | ofNat n =>
                  exact (Int.not_lt_of_ge (Int.natCast_nonneg n) hneg).elim
              | negSucc n => exact special42Image w z hw n s hs rest tail
            · exact mergedImage w z hw .four .two r s hp hs rest tail hij (by
                simp [Exceptional, hneg])
          · exact mergedImage w z hw .four j r s hp hs rest tail hij (by
              simp [Exceptional, hj2])
        · exact mergedImage w z hw i j r s hp hs rest tail hij (by
            simp [Exceptional, hi2, hi4])

private theorem evalSmall_eq_map_prod (w z : G) (l : List (SmallIndex × ℤ)) :
    evalSmall w z l = (l.map fun p ↦ smallBasis w z p.1 ^ p.2).prod := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [evalSmall, ih]

/-- The infinite cyclic free group assigned to each of the four basis indices. -/
abbrev SmallCyclic (_ : SmallIndex) := FreeGroup Unit

theorem exists_small_image (w z : G) (hw : w ≠ 1)
    (x : FreeGroup SmallIndex) (hx : x ≠ 1) :
    ∃ u : CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha,
      u.prod = FreeGroup.lift (smallBasis w z) x := by
  classical
  let y : CoprodI SmallCyclic := (@freeGroupEquivCoprodI SmallIndex).toMonoidHom x
  have hy : y ≠ 1 := by
    intro hy1
    apply hx
    exact (@freeGroupEquivCoprodI SmallIndex).injective (by simpa [y] using hy1)
  let sw : CoprodI.Word SmallCyclic := CoprodI.Word.equiv y
  have hsw : sw ≠ CoprodI.Word.empty := by
    intro he
    apply hy
    calc
      y = (CoprodI.Word.equiv (M := SmallCyclic)).symm sw :=
        ((CoprodI.Word.equiv (M := SmallCyclic)).symm_apply_apply y).symm
      _ = (CoprodI.Word.equiv (M := SmallCyclic)).symm CoprodI.Word.empty :=
        congrArg _ he
      _ = 1 := rfl
  obtain ⟨i, j, src, hsrc⟩ := CoprodI.NeWord.of_word sw hsw
  let encode : (Σ _ : SmallIndex, FreeGroup Unit) → SmallIndex × ℤ :=
    fun s ↦ (s.1, FreeGroup.freeGroupUnitEquivInt s.2)
  let l := src.toList.map encode
  have hlne : l ≠ [] := by
    simpa [l] using src.toList_ne_nil
  have hlexp : ∀ p ∈ l, p.2 ≠ 0 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨s, hs, rfl⟩
    intro heq
    have hsone : s.2 = 1 :=
      FreeGroup.freeGroupUnitEquivInt.injective (by
        simpa [encode, FreeGroup.freeGroupUnitEquivInt] using heq)
    exact src.toWord.ne_one s hs hsone
  have hlchain : l.IsChain (fun p q ↦ p.1 ≠ q.1) := by
    change (src.toList.map encode).IsChain (fun p q ↦ p.1 ≠ q.1)
    rw [List.isChain_map]
    exact src.toWord.chain_ne.imp (by
      intro p q hpq
      simpa [encode] using hpq)
  obtain ⟨p, rest, hl⟩ := List.exists_cons_of_ne_nil hlne
  have hp : p.2 ≠ 0 := hlexp p (by rw [hl]; simp)
  have hrest : ∀ q ∈ rest, q.2 ≠ 0 := by
    intro q hq
    exact hlexp q (by rw [hl]; simp [hq])
  have hchain : (p :: rest).IsChain (fun a b ↦ a.1 ≠ b.1) := by
    rw [← hl]
    exact hlchain
  let im := imageList w z hw p rest hp hrest hchain
  let cyclicLift : CoprodI SmallCyclic →* MillerLeft G :=
    CoprodI.lift fun i ↦ FreeGroup.lift fun _ ↦ smallBasis w z i
  have heval : cyclicLift src.prod = evalSmall w z l := by
    rw [evalSmall_eq_map_prod]
    simp only [cyclicLift, CoprodI.NeWord.prod, CoprodI.Word.prod, map_list_prod,
      List.map_map, l, encode]
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [Function.comp_apply, CoprodI.lift_of]
    have hreconstruct :
        FreeGroup.of () ^ FreeGroup.freeGroupUnitEquivInt s.2 = s.2 :=
      FreeGroup.freeGroupUnitEquivInt.symm_apply_apply s.2
    calc
      FreeGroup.lift (fun _ ↦ smallBasis w z s.1) s.2 =
          FreeGroup.lift (fun _ ↦ smallBasis w z s.1)
            (FreeGroup.of () ^ FreeGroup.freeGroupUnitEquivInt s.2) := by
              rw [hreconstruct]
      _ = smallBasis w z s.1 ^ FreeGroup.freeGroupUnitEquivInt s.2 := by
        rw [map_zpow, FreeGroup.lift_apply_of]
  have hsrcprod : src.prod = y := by
    change src.toWord.prod = y
    rw [hsrc]
    exact (CoprodI.Word.equiv (M := SmallCyclic)).symm_apply_apply y
  have hlift : FreeGroup.lift (smallBasis w z) =
      cyclicLift.comp (@freeGroupEquivCoprodI SmallIndex).toMonoidHom := by
    apply FreeGroup.ext_hom
    intro i
    simp [cyclicLift]
  refine ⟨im.word, ?_⟩
  calc
    im.word.prod = evalSmall w z (p :: rest) := im.prod_eq
    _ = evalSmall w z l := by rw [hl]
    _ = cyclicLift src.prod := heval.symm
    _ = cyclicLift y := congrArg cyclicLift hsrcprod
    _ = FreeGroup.lift (smallBasis w z) x := by
      rw [hlift]
      rfl

/-- Convert a four-element finite index to the named basis index. -/
def smallOfFin : Fin 4 → SmallIndex
  | 0 => .one
  | 1 => .two
  | 2 => .three
  | 3 => .four

/-- Convert a named basis index to its four-element finite index. -/
def finOfSmall : SmallIndex → Fin 4
  | .one => 0
  | .two => 1
  | .three => 2
  | .four => 3

/-- The free-group homomorphism renaming the four finite indices to named basis indices. -/
def toSmall : FreeGroup (Fin 4) →* FreeGroup SmallIndex :=
  FreeGroup.lift fun i ↦ FreeGroup.of (smallOfFin i)

/-- The inverse free-group homomorphism renaming the named indices to finite indices. -/
def fromSmall : FreeGroup SmallIndex →* FreeGroup (Fin 4) :=
  FreeGroup.lift fun i ↦ FreeGroup.of (finOfSmall i)

theorem toSmall_injective : Function.Injective toSmall := by
  apply Function.LeftInverse.injective (g := fromSmall)
  intro x
  have hcomp : fromSmall.comp toSmall = MonoidHom.id (FreeGroup (Fin 4)) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [fromSmall, toSmall, smallOfFin, finOfSmall]
  exact DFunLike.congr_fun hcomp x

theorem smallLift_comp_toSmall (w z : G) :
    (FreeGroup.lift (smallBasis w z)).comp toSmall =
      LeftSplit.tailMap w z := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp [toSmall, smallOfFin, smallBasis, LeftSplit.tailMap,
      LeftSplit.tailBasis, outerLeftBasis]

theorem exists_fin_tail_image (w z : G) (hw : w ≠ 1)
    (x : FreeGroup (Fin 4)) (hx : x ≠ 1) :
    ∃ u : CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha,
      u.prod = LeftSplit.tailMap w z x := by
  have hy : toSmall x ≠ 1 := by
    intro hy1
    apply hx
    apply toSmall_injective
    simpa using hy1
  obtain ⟨u, hu⟩ := exists_small_image w z hw (toSmall x) hy
  refine ⟨u, ?_⟩
  rw [hu]
  exact DFunLike.congr_fun (smallLift_comp_toSmall w z) x

/-- A reduced representative of the image of a nonidentity four-generator free word. -/
noncomputable def tailImageFin (w z : G) (hw : w ≠ 1)
    (x : FreeGroup (Fin 4)) (hx : x ≠ 1) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  Classical.choose (exists_fin_tail_image w z hw x hx)

theorem tailImageFin_prod (w z : G) (hw : w ≠ 1)
    (x : FreeGroup (Fin 4)) (hx : x ≠ 1) :
    (tailImageFin w z hw x hx).prod = LeftSplit.tailMap w z x :=
  Classical.choose_spec (exists_fin_tail_image w z hw x hx)

/-- The complete left free-basis lemma used in the amalgamated-product proof. -/
theorem outerLeftBasis_lift_injective (w z : G) (hw : w ≠ 1) :
    Function.Injective (FreeGroup.lift (outerLeftBasis w z)) :=
  LeftSplit.outerLeftBasis_injective_of_tailImage w z
    (tailImageFin w z hw) (tailImageFin_prod w z hw)

end Undecidability.MillerTancer.LeftInjective
