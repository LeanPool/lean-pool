/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Construction
public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.LeftNormalForm
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum

/-!
The left free-basis calculation in Gordon's Lemma 2.1.

We split `G * F(a, alpha)` into the free product of `G`, `<a>`, and
`<alpha>`.  The exponent assignment is kept abstract: positivity makes each
displayed block nonempty, while injectivity is exactly what rules out the
only possible boundary cancellation between two old-generator blocks.
-/

@[expose] public section

namespace Undecidability.Gordon.LeftNormalForm

open Monoid
open Undecidability.MillerTancer.LeftNormalForm

variable {d : ℕ} {G : Type} [Group G]

/-- The left group with its cyclic generators separated into individual free factors. -/
abbrev SplitLeft (G : Type) [Group G] := LeftProduct G

/-- The generator `a` in Gordon’s left normal form construction. -/
def a : SplitLeft G := alpha
/-- The second cyclic generator, used as the auxiliary letter `alpha`. -/
def auxiliaryAlpha : SplitLeft G := beta

/-- The assigned natural-number exponent, regarded as an integer. -/
def degreeInt (degree : Fin d → ℕ) (i : Fin d) : ℤ := degree i

/-- The encoded original generator between the indicated powers of the two cyclic generators. -/
def oldElement (degree : Fin d → ℕ) (x : Fin d → G) (i : Fin d) :
    SplitLeft G :=
  a ^ (-degreeInt degree i) * old (x i) *
    auxiliaryAlpha ^ degreeInt degree i

/-- The proposed amalgamating basis, realized in the separated left factors. -/
def splitBasis (degree : Fin d → ℕ) (x : Fin d → G) (w : G) :
    BasisIndex d → SplitLeft G
  | .conjugateA => a * auxiliaryAlpha * a⁻¹
  | .conjugateAlpha => auxiliaryAlpha * a * auxiliaryAlpha⁻¹
  | .old i => oldElement degree x i
  | .commutator =>
      old w * auxiliaryAlpha ^ 2 * (old w)⁻¹ *
        (auxiliaryAlpha ^ 2)⁻¹

/-- The one-letter reduced word representing a nonzero power in a cyclic factor. -/
def cyclicSingleton (i : LeftIndex) (k : ℤ) (hk : k ≠ 0)
    (hi : i = .alpha ∨ i = .beta) :
    CoprodI.NeWord (LeftFactor G) i i := by
  cases i with
  | old => simp at hi
  | alpha =>
      exact .singleton ((FreeGroup.of () : FreeGroup Unit) ^ k)
        (FreeGroup.unitGenerator_zpow_ne_one k hk)
  | beta =>
      exact .singleton ((FreeGroup.of () : FreeGroup Unit) ^ k)
        (FreeGroup.unitGenerator_zpow_ne_one k hk)

/-- The one-letter reduced word in the `alpha` factor. -/
def alphaSingleton (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (LeftFactor G) .alpha .alpha :=
  cyclicSingleton .alpha k hk (Or.inl rfl)

/-- The one-letter reduced word in the `beta` factor. -/
def betaSingleton (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (LeftFactor G) .beta .beta :=
  cyclicSingleton .beta k hk (Or.inr rfl)

/-- The one-letter reduced word representing a nonidentity element of the original group. -/
def oldSingleton (g : G) (hg : g ≠ 1) :
    CoprodI.NeWord (LeftFactor G) .old .old :=
  .singleton g hg

@[simp] theorem alphaSingleton_prod (k : ℤ) (hk : k ≠ 0) :
    (alphaSingleton (G := G) k hk).prod = a ^ k := by
  change CoprodI.of (i := LeftIndex.alpha) ((FreeGroup.of ()) ^ k) =
    (CoprodI.of (i := LeftIndex.alpha) (FreeGroup.of ()) : SplitLeft G) ^ k
  exact map_zpow _ _ _

@[simp] theorem betaSingleton_prod (k : ℤ) (hk : k ≠ 0) :
    (betaSingleton (G := G) k hk).prod = auxiliaryAlpha ^ k := by
  change CoprodI.of (i := LeftIndex.beta) ((FreeGroup.of ()) ^ k) =
    (CoprodI.of (i := LeftIndex.beta) (FreeGroup.of ()) : SplitLeft G) ^ k
  exact map_zpow _ _ _

@[simp] theorem old_one : old (1 : G) = (1 : SplitLeft G) :=
  map_one
    (CoprodI.of (M := LeftFactor G) (i := LeftIndex.old) :
      G →* SplitLeft G)

/-- The reduced word representing a nonzero power of the first conjugated cyclic generator. -/
def conjugatePowerA (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (LeftFactor G) .alpha .alpha :=
  .append (alphaSingleton 1 (by norm_num)) (by decide)
    (.append (betaSingleton k hk) (by decide)
      (alphaSingleton (-1) (by norm_num)))

/-- The reduced word representing a nonzero power of the second conjugated cyclic generator. -/
def conjugatePowerAlpha (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (LeftFactor G) .beta .beta :=
  .append (betaSingleton 1 (by norm_num)) (by decide)
    (.append (alphaSingleton k hk) (by decide)
      (betaSingleton (-1) (by norm_num)))

@[simp] theorem conjugatePowerA_prod (k : ℤ) (hk : k ≠ 0) :
    (conjugatePowerA (G := G) k hk).prod =
      (a * auxiliaryAlpha * a⁻¹) ^ k := by
  simp [conjugatePowerA]
  group

@[simp] theorem conjugatePowerAlpha_prod (k : ℤ) (hk : k ≠ 0) :
    (conjugatePowerAlpha (G := G) k hk).prod =
      (auxiliaryAlpha * a * auxiliaryAlpha⁻¹) ^ k := by
  simp [conjugatePowerAlpha]
  group

theorem degreeInt_ne_zero (degree : Fin d → ℕ)
    (hdegree : ∀ i, 0 < degree i) (i : Fin d) :
    degreeInt degree i ≠ 0 := by
  unfold degreeInt
  exact_mod_cast (Nat.ne_of_gt (hdegree i))

/-- The reduced block representing a power of an encoded original generator. -/
noncomputable def oldBlock (degree : Fin d → ℕ)
    (hdegree : ∀ i, 0 < degree i) (x : Fin d → G) (i : Fin d) :
    CoprodI.NeWord (LeftFactor G) .alpha .beta := by
  let e := degreeInt degree i
  have he : e ≠ 0 := degreeInt_ne_zero degree hdegree i
  by_cases hx : x i = 1
  · exact .append (alphaSingleton (-e) (neg_ne_zero.mpr he)) (by decide)
      (betaSingleton e he)
  · exact .append (alphaSingleton (-e) (neg_ne_zero.mpr he)) (by decide)
      (.append (oldSingleton (x i) hx) (by decide)
        (betaSingleton e he))

@[simp] theorem oldBlock_prod (degree : Fin d → ℕ)
    (hdegree : ∀ i, 0 < degree i) (x : Fin d → G) (i : Fin d) :
    (oldBlock degree hdegree x i).prod = oldElement degree x i := by
  classical
  have oldSingleton_prod_local (g : G) (hg : g ≠ 1) :
      (oldSingleton g hg).prod = old g := rfl
  by_cases hx : x i = 1
  · simp [oldBlock, hx, oldElement]
  · simp [oldBlock, hx, oldElement, oldSingleton_prod_local]
    group

@[simp] theorem oldBlock_head (degree : Fin d → ℕ)
    (hdegree : ∀ i, 0 < degree i) (x : Fin d → G) (i : Fin d) :
    (oldBlock degree hdegree x i).head =
      (FreeGroup.of () : FreeGroup Unit) ^ (-degreeInt degree i) := by
  classical
  by_cases hx : x i = 1 <;>
    simp [oldBlock, hx, alphaSingleton, cyclicSingleton] <;> rfl

@[simp] theorem oldBlock_last (degree : Fin d → ℕ)
    (hdegree : ∀ i, 0 < degree i) (x : Fin d → G) (i : Fin d) :
    (oldBlock degree hdegree x i).last =
      (FreeGroup.of () : FreeGroup Unit) ^ degreeInt degree i := by
  classical
  by_cases hx : x i = 1 <;>
    simp [oldBlock, hx, betaSingleton, cyclicSingleton] <;> rfl

/-- The reduced block representing the distinguished commutator. -/
def commutatorBlock (w : G) (hw : w ≠ 1) :
    CoprodI.NeWord (LeftFactor G) .old .beta :=
  .append (oldSingleton w hw) (by decide)
    (.append (betaSingleton 2 (by norm_num)) (by decide)
      (.append (oldSingleton w⁻¹ (inv_ne_one.mpr hw)) (by decide)
        (betaSingleton (-2) (by norm_num))))

@[simp] theorem commutatorBlock_prod (w : G) (hw : w ≠ 1) :
    (commutatorBlock w hw).prod =
      old w * auxiliaryAlpha ^ 2 * (old w)⁻¹ *
        (auxiliaryAlpha ^ 2)⁻¹ := by
  have oldSingleton_prod_local (g : G) (hg : g ≠ 1) :
      (oldSingleton g hg).prod = old g := rfl
  simp [commutatorBlock, oldSingleton_prod_local]
  group

/-- A nonempty reduced word packaged with its two endpoint factor labels. -/
structure PackedWord (G : Type) [Group G] where
  /-- The label of the factor containing the first letter. -/
  first : LeftIndex
  /-- The label of the factor containing the last letter. -/
  last : LeftIndex
  /-- The reduced-word representative carrying the stated evaluation and boundary properties. -/
  word : CoprodI.NeWord (LeftFactor G) first last

/-- The first letter, paired with its factor label. -/
def PackedWord.headLetter (u : PackedWord G) : Σ i, LeftFactor G i :=
  ⟨u.first, u.word.head⟩

/-- The last letter, paired with its factor label. -/
def PackedWord.lastLetter (u : PackedWord G) : Σ i, LeftFactor G i :=
  ⟨u.last, u.word.last⟩

/-- A positive power of a cyclically reduced word, packaged with its endpoints. -/
def positivePacked {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (n : ℕ) :
    PackedWord G :=
  ⟨i, j, positivePowerWord u hij n⟩

/-- The inverse of a positive power, with the endpoint labels exchanged. -/
def negativePacked {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (n : ℕ) :
    PackedWord G :=
  ⟨j, i, (positivePowerWord u hij n).inv⟩

/-- A nonzero integer power of a cyclically reduced word, with its endpoint labels. -/
def cyclicPowerPacked {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) : PackedWord G := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact (hk rfl).elim
      | succ n => exact positivePacked u hij n
  | negSucc n => exact negativePacked u hij n

@[simp] theorem positivePowerWord_head {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (n : ℕ) :
    (positivePowerWord u hij n).head = u.head := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [positivePowerWord] using ih

@[simp] theorem positivePowerWord_last {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (n : ℕ) :
    (positivePowerWord u hij n).last = u.last := by
  induction n with
  | zero => rfl
  | succ => rfl

theorem cyclicPowerPacked_prod {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) :
    (cyclicPowerPacked u hij k hk).word.prod = u.prod ^ k := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact (hk rfl).elim
      | succ n =>
          change (positivePowerWord u hij n).prod =
            u.prod ^ (Int.ofNat (n + 1))
          simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
            positivePowerWord_prod u hij n
  | negSucc n =>
      change (positivePowerWord u hij n).inv.prod = u.prod ^ Int.negSucc n
      simp [positivePowerWord_prod, zpow_negSucc]

theorem cyclicPowerPacked_head_pos {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) (hpos : 0 < k) :
    (cyclicPowerPacked u hij k hk).headLetter = ⟨i, u.head⟩ := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simp at hpos
      | succ n =>
          change (positivePacked u hij n).headLetter = ⟨i, u.head⟩
          simp [positivePacked, PackedWord.headLetter]
  | negSucc n => simp at hpos

theorem cyclicPowerPacked_last_pos {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) (hpos : 0 < k) :
    (cyclicPowerPacked u hij k hk).lastLetter = ⟨j, u.last⟩ := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simp at hpos
      | succ n =>
          change (positivePacked u hij n).lastLetter = ⟨j, u.last⟩
          simp [positivePacked, PackedWord.lastLetter]
  | negSucc n => simp at hpos

theorem cyclicPowerPacked_head_neg {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) (hneg : k < 0) :
    (cyclicPowerPacked u hij k hk).headLetter = ⟨j, u.last⁻¹⟩ := by
  cases k with
  | ofNat n => exact (Int.not_lt_of_ge (Int.natCast_nonneg n) hneg).elim
  | negSucc n =>
      change (negativePacked u hij n).headLetter = ⟨j, u.last⁻¹⟩
      simp [negativePacked, PackedWord.headLetter]

theorem cyclicPowerPacked_last_neg {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) (hneg : k < 0) :
    (cyclicPowerPacked u hij k hk).lastLetter = ⟨i, u.head⁻¹⟩ := by
  cases k with
  | ofNat n => exact (Int.not_lt_of_ge (Int.natCast_nonneg n) hneg).elim
  | negSucc n =>
      change (negativePacked u hij n).lastLetter = ⟨i, u.head⁻¹⟩
      simp [negativePacked, PackedWord.lastLetter]

/-- The reduced block representing a nonzero power of a proposed basis element. -/
noncomputable def powerPacked (degree : Fin d → ℕ)
    (hdegree : ∀ i, 0 < degree i) (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (i : BasisIndex d) (k : ℤ) (hk : k ≠ 0) : PackedWord G := by
  cases i with
  | conjugateA => exact ⟨.alpha, .alpha, conjugatePowerA k hk⟩
  | conjugateAlpha =>
      exact ⟨.beta, .beta, conjugatePowerAlpha k hk⟩
  | old i =>
      exact cyclicPowerPacked (oldBlock degree hdegree x i) (by decide) k hk
  | commutator =>
      exact cyclicPowerPacked (commutatorBlock w hw) (by decide) k hk

@[simp] theorem powerPacked_old
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (x : Fin d → G) (w : G) (hw : w ≠ 1) (i : Fin d)
    (k : ℤ) (hk : k ≠ 0) :
    powerPacked degree hdegree x w hw (.old i) k hk =
      cyclicPowerPacked (oldBlock degree hdegree x i) (by decide) k hk := rfl

@[simp] theorem powerPacked_commutator
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (x : Fin d → G) (w : G) (hw : w ≠ 1) (k : ℤ) (hk : k ≠ 0) :
    powerPacked degree hdegree x w hw .commutator k hk =
      cyclicPowerPacked (commutatorBlock w hw) (by decide) k hk := rfl

/-- An integer power in the `alpha` factor, paired with its factor label. -/
def alphaLetter (k : ℤ) : Σ i, LeftFactor G i :=
  ⟨.alpha, (FreeGroup.of () : FreeGroup Unit) ^ k⟩

/-- An integer power in the `beta` factor, paired with its factor label. -/
def betaLetter (k : ℤ) : Σ i, LeftFactor G i :=
  ⟨.beta, (FreeGroup.of () : FreeGroup Unit) ^ k⟩

/-- An original-group element paired with its factor label. -/
def oldLetter (g : G) : Σ i, LeftFactor G i := ⟨.old, g⟩

/-- The possible endpoint letters, recorded independently of the original group. -/
inductive LetterCode
  | oldW
  | oldWInv
  | alpha (k : ℤ)
  | beta (k : ℤ)

/-- The group-valued endpoint letter represented by a letter code. -/
def codeLetter (w : G) : LetterCode → Σ i, LeftFactor G i
  | .oldW => oldLetter w
  | .oldWInv => oldLetter w⁻¹
  | .alpha k => alphaLetter k
  | .beta k => betaLetter k

/-- The code of the initial letter expected for a basis power. -/
def expectedHeadCode (degree : Fin d → ℕ)
    (i : BasisIndex d) (k : ℤ) : LetterCode :=
  match i with
  | .conjugateA => .alpha 1
  | .conjugateAlpha => .beta 1
  | .old i =>
      if 0 < k then .alpha (-degreeInt degree i)
      else .beta (-degreeInt degree i)
  | .commutator => if 0 < k then .oldW else .beta 2

/-- The code of the final letter expected for a basis power. -/
def expectedLastCode (degree : Fin d → ℕ)
    (i : BasisIndex d) (k : ℤ) : LetterCode :=
  match i with
  | .conjugateA => .alpha (-1)
  | .conjugateAlpha => .beta (-1)
  | .old i =>
      if 0 < k then .beta (degreeInt degree i)
      else .alpha (degreeInt degree i)
  | .commutator => if 0 < k then .beta (-2) else .oldWInv

/-- The group-valued initial letter expected for a basis power. -/
def expectedHead (degree : Fin d → ℕ) (w : G)
    (i : BasisIndex d) (k : ℤ) : Σ i, LeftFactor G i :=
  codeLetter w (expectedHeadCode degree i k)

/-- The group-valued final letter expected for a basis power. -/
def expectedLast (degree : Fin d → ℕ) (w : G)
    (i : BasisIndex d) (k : ℤ) : Σ i, LeftFactor G i :=
  codeLetter w (expectedLastCode degree i k)

attribute [simp] codeLetter expectedHeadCode expectedLastCode

private theorem not_pos_of_neg {k : ℤ} (hk : k < 0) : ¬ 0 < k := by omega

@[simp] theorem powerPacked_headLetter
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (i : BasisIndex d) (k : ℤ) (hk : k ≠ 0) :
    (powerPacked degree hdegree x w hw i k hk).headLetter =
      expectedHead degree w i k := by
  cases i with
  | conjugateA =>
      simp [powerPacked, PackedWord.headLetter, conjugatePowerA, alphaSingleton,
        cyclicSingleton, expectedHead, alphaLetter]
  | conjugateAlpha =>
      simp [powerPacked, PackedWord.headLetter, conjugatePowerAlpha, betaSingleton,
        cyclicSingleton, expectedHead, betaLetter]
  | old i =>
      rcases lt_or_gt_of_ne hk with hneg | hpos
      · rw [powerPacked_old,
          cyclicPowerPacked_head_neg
            (oldBlock degree hdegree x i) (by decide) k hk hneg]
        simp [expectedHead, not_pos_of_neg hneg, oldBlock_last,
          betaLetter]
        rfl
      · rw [powerPacked_old,
          cyclicPowerPacked_head_pos
            (oldBlock degree hdegree x i) (by decide) k hk hpos]
        simp [expectedHead, hpos, oldBlock_head, alphaLetter]
  | commutator =>
      rcases lt_or_gt_of_ne hk with hneg | hpos
      · rw [powerPacked_commutator,
          cyclicPowerPacked_head_neg
            (commutatorBlock w hw) (by decide) k hk hneg]
        simp [expectedHead, not_pos_of_neg hneg, betaLetter,
          commutatorBlock, betaSingleton, cyclicSingleton]
        congr 1
      · rw [powerPacked_commutator,
          cyclicPowerPacked_head_pos
            (commutatorBlock w hw) (by decide) k hk hpos]
        simp [expectedHead, hpos, oldLetter, commutatorBlock, oldSingleton]

@[simp] theorem powerPacked_lastLetter
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (i : BasisIndex d) (k : ℤ) (hk : k ≠ 0) :
    (powerPacked degree hdegree x w hw i k hk).lastLetter =
      expectedLast degree w i k := by
  cases i with
  | conjugateA =>
      simp [powerPacked, PackedWord.lastLetter, conjugatePowerA, alphaSingleton,
        cyclicSingleton, expectedLast, alphaLetter]
  | conjugateAlpha =>
      simp [powerPacked, PackedWord.lastLetter, conjugatePowerAlpha, betaSingleton,
        cyclicSingleton, expectedLast, betaLetter]
  | old i =>
      rcases lt_or_gt_of_ne hk with hneg | hpos
      · rw [powerPacked_old,
          cyclicPowerPacked_last_neg
            (oldBlock degree hdegree x i) (by decide) k hk hneg]
        simp only [oldBlock_head, zpow_neg, expectedLast, codeLetter, expectedLastCode,
          not_pos_of_neg hneg, ↓reduceIte, alphaLetter]
        congr 1
        exact inv_inv _
      · rw [powerPacked_old,
          cyclicPowerPacked_last_pos
            (oldBlock degree hdegree x i) (by decide) k hk hpos]
        simp [expectedLast, hpos, oldBlock_last, betaLetter]
  | commutator =>
      rcases lt_or_gt_of_ne hk with hneg | hpos
      · rw [powerPacked_commutator,
          cyclicPowerPacked_last_neg
            (commutatorBlock w hw) (by decide) k hk hneg]
        simp [expectedLast, not_pos_of_neg hneg, oldLetter,
          commutatorBlock, oldSingleton]
        rfl
      · rw [powerPacked_commutator,
          cyclicPowerPacked_last_pos
            (commutatorBlock w hw) (by decide) k hk hpos]
        simp [expectedLast, hpos, betaLetter, commutatorBlock,
          betaSingleton, cyclicSingleton]

@[simp] theorem powerPacked_prod
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (i : BasisIndex d) (k : ℤ) (hk : k ≠ 0) :
    (powerPacked degree hdegree x w hw i k hk).word.prod =
      splitBasis degree x w i ^ k := by
  cases i with
  | conjugateA =>
      simpa only [powerPacked, splitBasis] using
        (conjugatePowerA_prod (G := G) k hk)
  | conjugateAlpha =>
      simpa only [powerPacked, splitBasis] using
        (conjugatePowerAlpha_prod (G := G) k hk)
  | old i =>
      simpa [splitBasis] using
        cyclicPowerPacked_prod
          (oldBlock degree hdegree x i) (by decide) k hk
  | commutator =>
      simpa only [powerPacked_commutator, splitBasis,
        commutatorBlock_prod] using
        cyclicPowerPacked_prod (commutatorBlock w hw) (by decide) k hk

/-- Two adjacent letters do not multiply to the identity when their factor labels agree. -/
def Noncancelling (p q : Σ i, LeftFactor G i) : Prop :=
  ∀ h : p.1 = q.1,
    p.2 * cast (congrArg (LeftFactor G) h.symm) q.2 ≠ 1

theorem noncancelling_of_index_ne (p q : Σ i, LeftFactor G i)
    (h : p.1 ≠ q.1) : Noncancelling p q := by
  intro heq
  exact (h heq).elim

theorem alphaLetter_noncancelling (r s : ℤ) (h : r + s ≠ 0) :
    Noncancelling (alphaLetter (G := G) r) (alphaLetter s) := by
  intro _
  change (FreeGroup.of () : FreeGroup Unit) ^ r * FreeGroup.of () ^ s ≠ 1
  rw [← zpow_add]
  exact FreeGroup.unitGenerator_zpow_ne_one (r + s) h

theorem betaLetter_noncancelling (r s : ℤ) (h : r + s ≠ 0) :
    Noncancelling (betaLetter (G := G) r) (betaLetter s) := by
  intro _
  change (FreeGroup.of () : FreeGroup Unit) ^ r * FreeGroup.of () ^ s ≠ 1
  rw [← zpow_add]
  exact FreeGroup.unitGenerator_zpow_ne_one (r + s) h

/-- The endpoint codes ensure that the corresponding adjacent letters do not cancel. -/
def CodeNoncancelling : LetterCode → LetterCode → Prop
  | .alpha r, .alpha s => r + s ≠ 0
  | .beta r, .beta s => r + s ≠ 0
  | .oldW, .oldW => False
  | .oldW, .oldWInv => False
  | .oldWInv, .oldW => False
  | .oldWInv, .oldWInv => False
  | _, _ => True

theorem code_noncancelling (w : G) (p q : LetterCode)
    (h : CodeNoncancelling p q) :
    Noncancelling (codeLetter w p) (codeLetter w q) := by
  cases p <;> cases q
  · contradiction
  · contradiction
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, alphaLetter])
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, betaLetter])
  · contradiction
  · contradiction
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, alphaLetter])
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, betaLetter])
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, alphaLetter])
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, alphaLetter])
  · exact alphaLetter_noncancelling _ _ h
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, alphaLetter, betaLetter])
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, betaLetter])
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, oldLetter, betaLetter])
  · exact noncancelling_of_index_ne _ _ (by
      simp [codeLetter, alphaLetter, betaLetter])
  · exact betaLetter_noncancelling _ _ h

private theorem degreeInt_injective (degree : Fin d → ℕ)
    (hinjective : Function.Injective degree) :
    Function.Injective (degreeInt degree) := by
  intro i j h
  apply hinjective
  have h' : (degree i : ℤ) = degree j := by
    simpa [degreeInt] using h
  exact_mod_cast h'

private theorem expected_code_noncancelling
    (degree : Fin d → ℕ) (hinjective : Function.Injective degree)
    (i j : BasisIndex d) (r s : ℤ) (hij : i ≠ j) :
    CodeNoncancelling
      (expectedLastCode degree i r) (expectedHeadCode degree j s) := by
  have hdegreeInt : Function.Injective (degreeInt degree) :=
    degreeInt_injective degree hinjective
  by_cases hrp : 0 < r <;> by_cases hsp : 0 < s
  all_goals
    cases i <;> cases j <;>
      simp [CodeNoncancelling, expectedLastCode, expectedHeadCode,
        hrp, hsp, degreeInt] at hij ⊢
  all_goals try omega
  all_goals
    have hne := hdegreeInt.ne hij
    simp [degreeInt] at hne
    omega

theorem expected_noncancelling
    (degree : Fin d → ℕ) (hinjective : Function.Injective degree)
    (w : G) (i j : BasisIndex d) (r s : ℤ) (hij : i ≠ j) :
    Noncancelling
      (expectedLast degree w i r) (expectedHead degree w j s) :=
  code_noncancelling w _ _
    (expected_code_noncancelling degree hinjective i j r s hij)

/-- A reduced word has an append constructor rather than a singleton constructor. -/
def IsAppend {i j : LeftIndex} :
    CoprodI.NeWord (LeftFactor G) i j → Prop
  | .singleton _ _ => False
  | .append _ _ _ => True

theorem positivePowerWord_isAppend {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (n : ℕ)
    (hu : IsAppend u) : IsAppend (positivePowerWord u hij n) := by
  cases n with
  | zero => exact hu
  | succ => trivial

theorem inv_isAppend {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hu : IsAppend u) :
    IsAppend u.inv := by
  cases u with
  | singleton => contradiction
  | append => trivial

theorem cyclicPowerPacked_isAppend {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) (hu : IsAppend u) :
    IsAppend (cyclicPowerPacked u hij k hk).word := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact (hk rfl).elim
      | succ n => exact positivePowerWord_isAppend u hij n hu
  | negSucc n => exact inv_isAppend _ (positivePowerWord_isAppend u hij n hu)

theorem oldBlock_isAppend (degree : Fin d → ℕ)
    (hdegree : ∀ i, 0 < degree i) (x : Fin d → G) (i : Fin d) :
    IsAppend (oldBlock degree hdegree x i) := by
  classical
  by_cases hx : x i = 1 <;> simp [oldBlock, hx, IsAppend]

theorem powerPacked_isAppend
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (i : BasisIndex d) (k : ℤ) (hk : k ≠ 0) :
    IsAppend (powerPacked degree hdegree x w hw i k hk).word := by
  cases i with
  | conjugateA => trivial
  | conjugateAlpha => trivial
  | old i =>
      exact cyclicPowerPacked_isAppend _ _ k hk
        (oldBlock_isAppend degree hdegree x i)
  | commutator =>
      exact cyclicPowerPacked_isAppend _ _ k hk (by trivial)

theorem exists_joinPacked (u v : PackedWord G)
    (hu : IsAppend u.word)
    (h : Noncancelling u.lastLetter v.headLetter) :
    ∃ q : PackedWord G,
      q.word.prod = u.word.prod * v.word.prod ∧
      q.headLetter = u.headLetter := by
  rcases u with ⟨uf, ul, uw⟩
  rcases v with ⟨vf, vl, vw⟩
  by_cases e : ul = vf
  · subst vf
    let q : PackedWord G :=
      ⟨uf, vl, CoprodI.NeWord.merge uw vw (h rfl)⟩
    refine ⟨q, CoprodI.NeWord.merge_prod uw vw (h rfl), ?_⟩
    change (⟨uf, (CoprodI.NeWord.merge uw vw (h rfl)).head⟩ :
        Σ i, LeftFactor G i) = ⟨uf, uw.head⟩
    cases uw with
    | singleton => contradiction
    | append => rfl
  · let q : PackedWord G := ⟨uf, vl, CoprodI.NeWord.append uw e vw⟩
    refine ⟨q, ?_, rfl⟩
    change (CoprodI.NeWord.append uw e vw).prod = uw.prod * vw.prod
    exact CoprodI.NeWord.append_prod

/-- The reduced concatenation of two packaged words whose boundary does not cancel. -/
noncomputable def joinPacked (u v : PackedWord G)
    (hu : IsAppend u.word)
    (h : Noncancelling u.lastLetter v.headLetter) : PackedWord G :=
  Classical.choose (exists_joinPacked u v hu h)

theorem joinPacked_prod (u v : PackedWord G)
    (hu : IsAppend u.word)
    (h : Noncancelling u.lastLetter v.headLetter) :
    (joinPacked u v hu h).word.prod = u.word.prod * v.word.prod :=
  (Classical.choose_spec (exists_joinPacked u v hu h)).1

@[simp] theorem joinPacked_headLetter (u v : PackedWord G)
    (hu : IsAppend u.word)
    (h : Noncancelling u.lastLetter v.headLetter) :
    (joinPacked u v hu h).headLetter = u.headLetter :=
  (Classical.choose_spec (exists_joinPacked u v hu h)).2

/-- The product of the indicated powers of the proposed basis elements. -/
def evalBasis (degree : Fin d → ℕ) (x : Fin d → G) (w : G) :
    List (BasisIndex d × ℤ) → SplitLeft G
  | [] => 1
  | p :: rest =>
      splitBasis degree x w p.1 ^ p.2 * evalBasis degree x w rest

/-- A reduced representative of a mapped word, together with its evaluation and boundary properties.
-/
structure Image (degree : Fin d → ℕ) (x : Fin d → G)
    (w : G) (p : BasisIndex d × ℤ)
    (rest : List (BasisIndex d × ℤ)) where
  /-- The reduced word together with its endpoint labels. -/
  packed : PackedWord G
  prod_eq : packed.word.prod = evalBasis degree x w (p :: rest)
  head_eq : packed.headLetter = expectedHead degree w p.1 p.2

/-- The reduced image of a one-block input word. -/
noncomputable def singletonImage
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (i : BasisIndex d) (k : ℤ) (hk : k ≠ 0) :
    Image degree x w (i, k) [] := by
  let u := powerPacked degree hdegree x w hw i k hk
  refine ⟨u, ?_, powerPacked_headLetter degree hdegree x w hw i k hk⟩
  simp [u, evalBasis]

/-- The reduced image formed when two adjacent input blocks are merged. -/
noncomputable def mergedImage
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (hinjective : Function.Injective degree)
    (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (i j : BasisIndex d) (r s : ℤ) (hr : r ≠ 0) (_hs : s ≠ 0)
    (rest : List (BasisIndex d × ℤ))
    (tail : Image degree x w (j, s) rest) (hij : i ≠ j) :
    Image degree x w (i, r) ((j, s) :: rest) := by
  let u := powerPacked degree hdegree x w hw i r hr
  have hu : IsAppend u.word :=
    powerPacked_isAppend degree hdegree x w hw i r hr
  have hb : Noncancelling u.lastLetter tail.packed.headLetter := by
    rw [show u.lastLetter = expectedLast degree w i r from
      powerPacked_lastLetter degree hdegree x w hw i r hr]
    rw [tail.head_eq]
    exact expected_noncancelling degree hinjective w i j r s hij
  let word := joinPacked u tail.packed hu hb
  refine ⟨word, ?_, ?_⟩
  · rw [show word.word.prod = u.word.prod * tail.packed.word.prod from
      joinPacked_prod u tail.packed hu hb]
    rw [powerPacked_prod, tail.prod_eq]
    rfl
  · rw [show word.headLetter = u.headLetter from
      joinPacked_headLetter u tail.packed hu hb]
    exact powerPacked_headLetter degree hdegree x w hw i r hr

/-- The reduced image of a nonempty list of basis powers with noncancelling boundaries. -/
noncomputable def imageList
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (hinjective : Function.Injective degree)
    (x : Fin d → G) (w : G) (hw : w ≠ 1)
    (p : BasisIndex d × ℤ) (rest : List (BasisIndex d × ℤ))
    (hp : p.2 ≠ 0) (hrest : ∀ q ∈ rest, q.2 ≠ 0)
    (hchain : (p :: rest).IsChain (fun a b ↦ a.1 ≠ b.1)) :
    Image degree x w p rest := by
  induction rest generalizing p with
  | nil => exact singletonImage degree hdegree x w hw p.1 p.2 hp
  | cons q rest ih =>
      rcases p with ⟨i, r⟩
      rcases q with ⟨j, s⟩
      have hs : s ≠ 0 := hrest (j, s) (by simp)
      have hrest' : ∀ q ∈ rest, q.2 ≠ 0 := by
        intro q hq
        exact hrest q (by simp [hq])
      rw [List.isChain_cons_cons] at hchain
      let tail := ih (j, s) hs hrest' hchain.2
      exact mergedImage degree hdegree hinjective x w hw
        i j r s hp hs rest tail hchain.1

private theorem neWord_prod_ne_one {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) : u.prod ≠ 1 := by
  classical
  intro hu
  have heq : u.toWord =
      (CoprodI.Word.empty : CoprodI.Word (LeftFactor G)) := by
    apply (CoprodI.Word.equiv (M := LeftFactor G)).symm.injective
    change u.prod = 1
    exact hu
  have hlist := congrArg CoprodI.Word.toList heq
  exact u.toList_ne_nil (by
    simpa [CoprodI.NeWord.toWord] using hlist)

private theorem evalBasis_eq_map_prod
    (degree : Fin d → ℕ) (x : Fin d → G) (w : G)
    (l : List (BasisIndex d × ℤ)) :
    evalBasis degree x w l =
      (l.map fun p ↦ splitBasis degree x w p.1 ^ p.2).prod := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [evalBasis, ih]

/-- Gordon's left-hand words freely generate whenever the degree assignment
is positive and injective and the parameter word is nontrivial. -/
theorem splitBasis_lift_injective
    (degree : Fin d → ℕ) (hdegree : ∀ i, 0 < degree i)
    (hinjective : Function.Injective degree)
    (x : Fin d → G) (w : G) (hw : w ≠ 1) :
    Function.Injective (FreeGroup.lift (splitBasis degree x w)) := by
  apply FreeGroup.lift_injective_of_reduced_zpow_products
    (splitBasis degree x w)
  intro l hlne hlexp hlchain
  cases l with
  | nil => contradiction
  | cons p rest =>
      have hp : p.2 ≠ 0 := hlexp p (by simp)
      have hrest : ∀ q ∈ rest, q.2 ≠ 0 := by
        intro q hq
        exact hlexp q (by simp [hq])
      let im := imageList degree hdegree hinjective x w hw
        p rest hp hrest hlchain
      rw [← evalBasis_eq_map_prod]
      rw [← im.prod_eq]
      exact neWord_prod_ne_one im.packed.word

end Undecidability.Gordon.LeftNormalForm
