/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Periodic.Basic
public import LeanPool.DeciSigma1.Holes.Tail.ClosedFactors
import Mathlib.Order.SuccPred.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.GroupWithZero.Nat

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Levels of periodic covers

The bound on rejected tails measures how far a rejected tail is from being periodic, at a
sequence of levels with growing period bounds. At level `l` a rejected tail has a *periodic
cover* if all but `uncoveredBound l` of its positions lie in at most `pieceCountBase + 1`
factors of period at most `periodBound l` (`CoordinateCover`). The *level cover property* adds
that its longest suffix with such a period is shorter than `terminalLengthBound l`
(`LevelCoverProperty`). The functions of a level are packaged in `LevelBounds` together with the
inequalities between consecutive levels that the proof uses; `levelBounds` defines them
explicitly by the recursion `levelStep`.

Both properties are monotone in the level (`coordinateCover_mono`, `levelCoverProperty_succ`).
Among the `levelCount k = 3 (2k + 1)` levels there is therefore a level at which neither
property changes for any coordinate (`exists_stable_level`). A word with the level cover property
at level `m` has suffix chains of at most `chainLengthBound m + N` members
(`levelCoverProperty_chainBound`): the members are counted by their suffix starts, at most
`N - 1` before the first rejected cut, the uncovered positions, the terminal suffix and two
periods for each factor of the cover. From a long enough window on, the chains of such a word
have at most `pieceCountBase + N` steps, independently of the level
(`Holes.Tail.WindowChains`); the initial window `startWindow (m + 2)` of the level two above is
that long (`chainWindow_le_startWindow`), so the recursion `levelStep` gives every target the
same chain budget at every level.

## Main declarations

- `LevelBounds`, `levelBounds`, `levelCount`: the functions of the levels and their explicit
  values.
- `PeriodicFactor`, `PeriodicCover`, `longestPeriodicSuffixLength`: periodic covers of a rejected
  tail and its longest periodic suffix.
- `CoordinateCover`, `LevelCoverProperty`: the two level properties of a coordinate.
- `levelCoverProperty_succ`, `exists_stable_level`: monotonicity and a stable level.
- `levelCoverProperty_chainBound`: the level cover property bounds suffix chains.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words

variable {α S : Type} {k : ℕ}

/-! ## The level bounds -/

/-- The functions of the levels and the inequalities between them that the bound on rejected
tails uses, for `k` coordinates and `N` states; the size `σ` of the alphabet does not enter them.
At level `l`, `periodBound l` bounds the periods of the cover, `uncoveredBound l` the uncovered
positions, `terminalLengthBound l` the periodic suffix and `chainLengthBound l` the suffix
chains; `fixedChainBudget l` bounds all suffix chains of the targets and `startWindow l` is the
initial window. From the initial window on, the chains of the targets have at most
`pieceCountBase + N` steps, whatever the level (`chainWindow_le_startWindow`), and
`escapeLengthBound l` and `comparisonWindow l` are the values of `suffixLengthBound` and
`suffixLengthEnvelope` for this budget, with the suffix dictionary of `k` targets. -/
structure LevelBounds (σ k N : ℕ) where
  /-- Uniform bound on designated periodic pieces. -/
  pieceCountBase : ℕ
  /-- Period bound at each level. -/
  periodBound : ℕ → ℕ
  /-- Suffix-chain bound at each level. -/
  chainLengthBound : ℕ → ℕ
  /-- Terminal periodic-suffix bound at each level. -/
  terminalLengthBound : ℕ → ℕ
  /-- Bound on uncovered positions at each level. -/
  uncoveredBound : ℕ → ℕ
  /-- Length needed to escape the preceding level. -/
  escapeLengthBound : ℕ → ℕ
  /-- Suffix window needed to compare states at each level. -/
  comparisonWindow : ℕ → ℕ
  /-- Initial suffix window at each level. -/
  startWindow : ℕ → ℕ
  /-- Level-independent suffix-chain budget. -/
  fixedChainBudget : ℕ → ℕ
  pieceCountBase_eq : pieceCountBase = 4 + 2 * (k - 1) * (N - 1)
  periodBound_mono : Monotone periodBound
  terminalLengthBound_mono : Monotone terminalLengthBound
  uncoveredBound_mono : Monotone uncoveredBound
  escapeLengthBound_mono : Monotone escapeLengthBound
  stateCount_le_fixedChainBudget : ∀ l, N ≤ fixedChainBudget l
  fixedChainBudget_ge_chainLength : ∀ l, chainLengthBound l + N ≤ fixedChainBudget (l + 2)
  chainLengthBound_ge_cover : ∀ l, (pieceCountBase + 1) * (2 * periodBound l) + uncoveredBound l +
      terminalLengthBound l ≤ chainLengthBound l
  startWindow_gt : ∀ l, (N + 1) * periodBound l < startWindow (l + 1)
  chainWindow_le_startWindow : ∀ l, (pieceCountBase + 2) * (chainLengthBound l + 1) ≤
      startWindow (l + 2)
  escapeLengthBound_eq : ∀ l, escapeLengthBound l =
      suffixLengthBound k N (List.replicate k (pieceCountBase + N)) (startWindow l)
  comparisonWindow_eq : ∀ l, comparisonWindow l =
      suffixLengthEnvelope k N (List.replicate k (pieceCountBase + N)) (startWindow l)
  factorLengthBound_le_periodBound : ∀ l, factorLengthBound k N (comparisonWindow l) ≤ periodBound l
  periodBound_lt_escapeLengthBound : 1 ≤ N → ∀ l, periodBound l < escapeLengthBound l
  uncoveredBound_ge_candidateBound : ∀ l, (pieceCountBase + 2) * (3 * escapeLengthBound l + 3) ≤
      uncoveredBound l
  terminalLengthBound_gt_cover : ∀ l, N * periodBound (l + 1) + uncoveredBound l +
      (pieceCountBase + 1) * (2 * periodBound (l + 1)) < terminalLengthBound (l + 1)
  terminalLengthBound_ge_periodBudget : ∀ l, 1 + fixedChainBudget (l + 1) *
      (periodBound l * N.factorial) + 2 * (periodBound l * N.factorial) + N * periodBound l ≤
          terminalLengthBound l

/-- The number `3 (2k + 1)` of levels. -/
def levelCount (k : ℕ) : ℕ := 3 * (2 * k + 1)

/-! ## The explicit level functions -/

/-- The values of a level that the next level uses. -/
structure LevelState where
  /-- Period bound passed to the next level. -/
  periodBound : ℕ
  /-- Current suffix-chain bound. -/
  chainLengthBound : ℕ
  /-- Suffix-chain bound from the preceding level. -/
  previousChainLengthBound : ℕ
  /-- Bound on terminal periodic suffixes. -/
  terminalLengthBound : ℕ
  /-- Bound on positions outside the periodic cover. -/
  uncoveredBound : ℕ

/-- The initial window of the level after `st`, for `Q + 1` factors in a cover: larger than
`N + 1` periods of the level of `st`, and at least `(Q + 2) (X + 1)` for the chain length bound
`X` two levels below. From this window on, the suffix chains of the words with the level cover
property two levels below have at most `Q + N` steps. -/
def levelStartWindow (N Q : ℕ) (st : LevelState) : ℕ :=
  (N + 1) * st.periodBound + (Q + 2) * (st.previousChainLengthBound + 1)

/-- One step of the recursion of the level functions, for `Q + 1` factors in a cover. The
targets have the chain budget `Q + N` from the initial window `levelStartWindow N Q st`. -/
def levelStep (k N Q : ℕ) (st : LevelState) : LevelState :=
  let bs := levelStartWindow N Q st
  let Tp := suffixLengthBound k N (List.replicate k (Q + N)) bs
  let Bw := suffixLengthEnvelope k N (List.replicate k (Q + N)) bs
  let e := max (factorLengthBound k N Bw) st.periodBound
  let Tt := (Q + 2) * (3 * Tp + 3)
  let h := e * N.factorial
  let Y := (1 + (st.chainLengthBound + N) * h) + 2 * h + N * e + (Q + 3) * (3 * e) +
      st.uncoveredBound + st.terminalLengthBound
  { periodBound := e, chainLengthBound := (Q + 2) * (1 + 2 * e) + Tt + Y + N,
    previousChainLengthBound := st.chainLengthBound, terminalLengthBound := Y,
    uncoveredBound := Tt }

/-- The values before the first level: period bound `1` and all other values `0`. -/
def initialLevelState : LevelState :=
  { periodBound := 1, chainLengthBound := 0, previousChainLengthBound := 0,
    terminalLengthBound := 0, uncoveredBound := 0 }

/-- The number `4 + 2 (k - 1) (N - 1)`, which is `pieceCountBase` for the explicit level
functions. -/
def levelMultiplicity (k N : ℕ) : ℕ := 4 + 2 * (k - 1) * (N - 1)

/-- The state before level `l` (the values of level `l - 1`). -/
def levelState (k N l : ℕ) :
    LevelState := (levelStep k N (levelMultiplicity k N))^[l] initialLevelState

section Explicit

variable {N : ℕ}

theorem levelState_succ (l : ℕ) :
    levelState k N (l + 1) = levelStep k N (levelMultiplicity k N) (levelState k N l) :=
  Function.iterate_succ_apply' _ _ _

theorem levelState_periodBound_pos (l : ℕ) : 1 ≤ (levelState k N l).periodBound := by
  induction l with
  | zero => simp [levelState, initialLevelState]
  | succ l ih => rw [levelState_succ]; simp only [levelStep]; omega

theorem levelStep_chainLengthBound_ge (Q : ℕ) (st : LevelState) (he : 1 ≤ st.periodBound) :
    st.chainLengthBound ≤ (levelStep k N Q st).chainLengthBound := by
  simp only [levelStep]
  set e := max (factorLengthBound k N (suffixLengthEnvelope k N (List.replicate k (Q + N))
    (levelStartWindow N Q st))) st.periodBound
  have h1 : 1 ≤ e := le_trans he (le_max_right _ _)
  have h2 : 1 ≤ e * N.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.factorial_ne_zero N))
  have h3 := Nat.le_mul_of_pos_right (st.chainLengthBound + N) h2
  omega

theorem levelState_previousChainLengthBound_le (l : ℕ) :
    (levelState k N l).previousChainLengthBound ≤ (levelState k N l).chainLengthBound := by
  cases l with
  | zero => simp [levelState, initialLevelState]
  | succ l =>
    rw [levelState_succ]
    exact levelStep_chainLengthBound_ge _ _ (levelState_periodBound_pos l)

theorem lt_factorLengthBound (m N b : ℕ) (hN : 1 ≤ N) : b < factorLengthBound m N b := by
  unfold factorLengthBound suffixNodeBound
  have h1 : 1 ≤ N * (m * (b * (b + 1) / 2) + 1) := Nat.mul_pos hN (Nat.succ_pos _)
  have h2 := Nat.mul_le_mul_left (b + 1) h1
  omega

theorem factorLengthBound_suffixLengthEnvelope_lt (m N : ℕ) :
    ∀ (Ss : List ℕ) (b : ℕ), factorLengthBound m N (suffixLengthEnvelope m N Ss b) <
        suffixLengthBound m N Ss b
  | [], b => by simp
  | S :: Ss, b => by
    rw [suffixLengthBound_cons, suffixLengthEnvelope_cons]
    have :=
        factorLengthBound_suffixLengthEnvelope_lt m N Ss
            ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
      suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b))
    omega

/-- The initial window of level `l`. -/
def levelWindow (k N l : ℕ) : ℕ := levelStartWindow N (levelMultiplicity k N) (levelState k N l)

/-- The escape length of level `l`: `suffixLengthBound` for `k` targets with the chain budget
`levelMultiplicity k N + N`, from the initial window of the level. -/
def levelEscapeLength (k N l : ℕ) : ℕ :=
  suffixLengthBound k N (List.replicate k (levelMultiplicity k N + N)) (levelWindow k N l)

theorem levelWindow_le_succ (l : ℕ) : levelWindow k N l ≤ levelWindow k N (l + 1) := by
  unfold levelWindow levelStartWindow
  rw [levelState_succ l]
  simp only [levelStep]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_right _ _))
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (levelState_previousChainLengthBound_le l) 1))

theorem levelEscapeLength_le_succ (l : ℕ) :
    levelEscapeLength k N l ≤ levelEscapeLength k N (l + 1) :=
  suffixLengthBound_mono k N _ (levelWindow_le_succ l)

theorem levelState_succ_uncoveredBound (l : ℕ) : (levelState k N (l + 1)).uncoveredBound =
    (levelMultiplicity k N + 2) * (3 * levelEscapeLength k N l + 3) := by
  rw [levelState_succ]; rfl

end Explicit

/-- The explicit level functions, defined by `levelStep`. They are only used through the bounds
they satisfy and are not meant to be evaluated. -/
def levelBounds (σ k N : ℕ) : LevelBounds σ k N where
  pieceCountBase := levelMultiplicity k N
  periodBound l := (levelState k N (l + 1)).periodBound
  chainLengthBound l := (levelState k N (l + 1)).chainLengthBound
  terminalLengthBound l := (levelState k N (l + 1)).terminalLengthBound
  uncoveredBound l := (levelState k N (l + 1)).uncoveredBound
  escapeLengthBound l := levelEscapeLength k N l
  comparisonWindow l :=
      suffixLengthEnvelope k N (List.replicate k (levelMultiplicity k N + N)) (levelWindow k N l)
  startWindow l := levelWindow k N l
  fixedChainBudget l := (levelState k N l).previousChainLengthBound + N
  pieceCountBase_eq := rfl
  periodBound_mono := by
    apply monotone_nat_of_le_succ
    intro l
    change (levelState k N (l + 1)).periodBound ≤ (levelState k N (l + 1 + 1)).periodBound
    rw [levelState_succ (l + 1)]; simp only [levelStep]; exact le_max_right _ _
  terminalLengthBound_mono := by
    apply monotone_nat_of_le_succ
    intro l
    change (levelState k N (l + 1)).terminalLengthBound ≤
        (levelState k N (l + 1 + 1)).terminalLengthBound
    rw [levelState_succ (l + 1)]; simp only [levelStep]; omega
  uncoveredBound_mono := monotone_nat_of_le_succ fun l => by
    change (levelState k N (l + 1)).uncoveredBound ≤ (levelState k N (l + 1 + 1)).uncoveredBound
    rw [levelState_succ_uncoveredBound, levelState_succ_uncoveredBound]
    have := levelEscapeLength_le_succ (k := k) (N := N) l
    exact Nat.mul_le_mul_left _ (by omega)
  escapeLengthBound_mono := monotone_nat_of_le_succ levelEscapeLength_le_succ
  stateCount_le_fixedChainBudget l := Nat.le_add_left _ _
  fixedChainBudget_ge_chainLength l := by
    show (levelState k N (l + 1)).chainLengthBound + N ≤
        (levelState k N (l + 2)).previousChainLengthBound + N
    rw [show l + 2 = (l + 1) + 1 by rfl, levelState_succ (l + 1)]
    simp [levelStep]
  chainLengthBound_ge_cover l := by
    show (levelMultiplicity k N + 1) * (2 * (levelState k N (l + 1)).periodBound) +
        (levelState k N (l + 1)).uncoveredBound +
      (levelState k N (l + 1)).terminalLengthBound ≤ (levelState k N (l + 1)).chainLengthBound
    rw [levelState_succ l]
    simp only [levelStep]
    set e :=
        max (factorLengthBound k N (suffixLengthEnvelope k N
          (List.replicate k (levelMultiplicity k N + N))
          (levelStartWindow N (levelMultiplicity k N) (levelState k N l))))
          (levelState k N l).periodBound
    have : (levelMultiplicity k N + 1) * (2 * e) ≤ (levelMultiplicity k N + 2) * (1 + 2 * e) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  startWindow_gt l := by
    show (N + 1) * (levelState k N (l + 1)).periodBound < levelWindow k N (l + 1)
    unfold levelWindow levelStartWindow
    have : 0 < (levelMultiplicity k N + 2) *
        ((levelState k N (l + 1)).previousChainLengthBound + 1) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  chainWindow_le_startWindow l := by
    show (levelMultiplicity k N + 2) * ((levelState k N (l + 1)).chainLengthBound + 1) ≤
      levelWindow k N (l + 2)
    unfold levelWindow levelStartWindow
    rw [levelState_succ (l + 1)]
    exact Nat.le_add_left _ _
  escapeLengthBound_eq l := rfl
  comparisonWindow_eq l := rfl
  factorLengthBound_le_periodBound l := by
    show _ ≤ (levelState k N (l + 1)).periodBound
    rw [levelState_succ l]; simp only [levelStep]; exact le_max_left _ _
  periodBound_lt_escapeLengthBound hN l := by
    show (levelState k N (l + 1)).periodBound < levelEscapeLength k N l
    rw [levelState_succ l]
    simp only [levelStep, levelEscapeLength, levelWindow]
    apply max_lt (factorLengthBound_suffixLengthEnvelope_lt k N _ _)
    set Ss := List.replicate k (levelMultiplicity k N + N)
    set bs := levelStartWindow N (levelMultiplicity k N) (levelState k N l)
    have h1 := factorLengthBound_suffixLengthEnvelope_lt k N Ss bs
    have h2 := le_suffixLengthEnvelope k N Ss bs
    have h3 := lt_factorLengthBound k N (suffixLengthEnvelope k N Ss bs) hN
    have h4 : (levelState k N l).periodBound ≤ bs := by
      have : (levelState k N l).periodBound ≤ (N + 1) * (levelState k N l).periodBound :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact this.trans (Nat.le_add_right _ _)
    omega
  uncoveredBound_ge_candidateBound l := (levelState_succ_uncoveredBound l).ge
  terminalLengthBound_gt_cover l := by
    show N * (levelState k N (l + 1 + 1)).periodBound +
        (levelState k N (l + 1)).uncoveredBound +
      (levelMultiplicity k N + 1) * (2 * (levelState k N (l + 1 + 1)).periodBound) <
          (levelState k N (l + 1 + 1)).terminalLengthBound
    rw [levelState_succ (l + 1)]
    simp only [levelStep]
    set e :=
        max (factorLengthBound k N (suffixLengthEnvelope k N
          (List.replicate k (levelMultiplicity k N + N))
          (levelStartWindow N (levelMultiplicity k N) (levelState k N (l + 1)))))
          (levelState k N (l + 1)).periodBound
    have : (levelMultiplicity k N + 1) * (2 * e) ≤ (levelMultiplicity k N + 3) * (3 * e) :=
        Nat.mul_le_mul (by omega) (by omega)
    omega
  terminalLengthBound_ge_periodBudget l := by
    show 1 + ((levelState k N (l + 1)).previousChainLengthBound + N) *
        ((levelState k N (l + 1)).periodBound * N.factorial) +
      2 * ((levelState k N (l + 1)).periodBound * N.factorial) + N *
          (levelState k N (l + 1)).periodBound ≤
      (levelState k N (l + 1)).terminalLengthBound
    rw [levelState_succ l]
    simp only [levelStep]
    omega

/-! ## Periodic factors, covers and terminal suffixes -/

/-- A periodic factor: the positions `[start, stop)` with period `period`. -/
structure PeriodicFactor where
  /-- First position of the factor. -/
  start : ℕ
  /-- Position immediately after the factor. -/
  stop : ℕ
  /-- Period assigned to the factor. -/
  period : ℕ
  deriving DecidableEq

/-- A valid factor of `w` with period in `[1, E]`. -/
def PeriodicFactor.Valid (w : List α) (E : ℕ) (f : PeriodicFactor) : Prop :=
  0 < f.period ∧ f.period ≤ E ∧ f.stop ≤ w.length ∧ PeriodicOn w f.period f.start f.stop

/-- Position `x` lies in one of the factors. -/
def Covers (fs : List PeriodicFactor) (x : ℕ) : Prop := ∃ f ∈ fs, f.start ≤ x ∧ x < f.stop

instance (fs : List PeriodicFactor) (x : ℕ) : Decidable (Covers fs x) :=
  inferInstanceAs (Decidable (∃ f ∈ fs, _))

/-- The positions of `[J, n)` in no factor. -/
def uncoveredPositions (fs : List PeriodicFactor) (J n : ℕ) : Finset ℕ :=
  (Finset.Ico J n).filter (fun x => ¬ Covers fs x)

/-- All positions of `[J, |w|)` except at most `T` lie in at most `P` factors of `w`, possibly
overlapping, with periods in `[1, E]`. -/
def PeriodicCover (w : List α) (J P E T : ℕ) : Prop :=
  ∃ fs : List PeriodicFactor, fs.length ≤ P ∧ (∀ f ∈ fs, f.Valid w E) ∧
      (uncoveredPositions fs J w.length).card ≤ T

theorem PeriodicCover.mono {w : List α} {J P E T P' E' T' : ℕ} (h : PeriodicCover w J P E T)
    (hP : P ≤ P')
    (hE : E ≤ E') (hT : T ≤ T') : PeriodicCover w J P' E' T' := by
  obtain ⟨fs, h1, h2, h3⟩ := h
  exact ⟨fs, h1.trans hP, fun f hf => let ⟨a, b, c, d⟩ := h2 f hf; ⟨a, b.trans hE, c, d⟩,
    h3.trans hT⟩

theorem covers_cons {f : PeriodicFactor} {fs : List PeriodicFactor} {x : ℕ} :
    Covers (f :: fs) x ↔ (f.start ≤ x ∧ x < f.stop) ∨ Covers fs x := by
  simp [Covers]

/-- A cover of `x` extends to a word `x'` that agrees with `x` below `|x| ≤ |x'|`, by one more
factor of `x'` that runs from at most `|x|` to the end of `x'`. -/
theorem PeriodicCover.cons_of_agree {x x' : List α} {J P E T : ℕ} (h : PeriodicCover x J P E T)
    {sf : PeriodicFactor} (hsf : sf.Valid x' E) (hs : sf.start ≤ x.length)
    (hstop : sf.stop = x'.length) (hlen : x.length ≤ x'.length)
    (hagree : ∀ q < x.length, x'[q]? = x[q]?) : PeriodicCover x' J (P + 1) E T := by
  obtain ⟨fs, hfl, hfv, hunc⟩ := h
  refine ⟨sf :: fs, by simp [hfl], fun f hf => ?_, (Finset.card_le_card fun q hq => ?_).trans hunc⟩
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact hsf
    · obtain ⟨hp, hpE, hfe, hper⟩ := hfv f hf
      exact ⟨hp, hpE, hfe.trans hlen, hper.transfer fun q hq => hagree q (by omega)⟩
  · simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    have hqs : q < sf.start := by
      by_contra h; exact hq.2 (covers_cons.mpr (.inl ⟨by omega, by omega⟩))
    exact ⟨⟨hq.1.1, by omega⟩, fun hc => hq.2 (covers_cons.mpr (.inr hc))⟩

/-- The covered positions of `X` number at most the sum of the factor intersections. -/
theorem card_filter_covers_le (X : Finset ℕ) :
    ∀ fs : List PeriodicFactor, (X.filter (Covers fs)).card ≤
      (fs.map (fun f => (X.filter (fun x => f.start ≤ x ∧ x < f.stop)).card)).sum
  | [] => by simp [Covers]
  | f :: fs => by
    have : X.filter (Covers (f :: fs)) =
        X.filter (fun x => f.start ≤ x ∧ x < f.stop) ∪ X.filter (Covers fs) := by
      rw [← Finset.filter_or]; congr 1; funext x; exact propext covers_cons
    rw [this, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (card_filter_covers_le X fs) _)

theorem periodicOn_full_iff {w : List α} {p s : ℕ} (hs : s ≤ w.length) :
    PeriodicOn w p s w.length ↔ (w.drop s).HasPeriod p := by
  rw [periodicOn_iff_hasPeriod hs le_rfl, List.take_of_length_le (by simp)]

/-- The suffix from cut `s` has some period in `[1, E]`. -/
def HasTerminalPeriod (E : ℕ) (w : List α) (s : ℕ) : Prop :=
  ∃ p ∈ Finset.Icc 1 E, (w.drop s).HasPeriod p

instance [DecidableEq α] (E : ℕ) (w : List α) : DecidablePred (HasTerminalPeriod E w) :=
  fun _ => inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- The length of the longest suffix of `w` with some period in `[1, E]`. -/
def longestPeriodicSuffixLength [DecidableEq α] (E : ℕ) (w : List α) : ℕ :=
  ((Finset.range (w.length + 1)).filter (HasTerminalPeriod E w)).sup (fun s => w.length - s)

theorem le_longestPeriodicSuffixLength [DecidableEq α] {w : List α} {E p s : ℕ} (hp : 0 < p)
    (hpE : p ≤ E)
    (hs : s ≤ w.length) (h : PeriodicOn w p s w.length) : w.length - s ≤
        longestPeriodicSuffixLength E w := by
  unfold longestPeriodicSuffixLength
  apply Finset.le_sup (f := fun s => w.length - s)
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, p, Finset.mem_Icc.mpr ⟨hp, hpE⟩, (periodicOn_full_iff hs).mp h⟩

theorem exists_of_le_longestPeriodicSuffixLength [DecidableEq α] {w : List α} {E Y : ℕ} (hY : 0 < Y)
    (h : Y ≤ longestPeriodicSuffixLength E w) : ∃ s p, 0 < p ∧ p ≤ E ∧ s ≤ w.length ∧
        PeriodicOn w p s w.length ∧
      Y ≤ w.length - s := by
  unfold longestPeriodicSuffixLength at h
  rw [Finset.le_sup_iff (by simpa using hY)] at h
  obtain ⟨s, hs, hY'⟩ := h
  rw [Finset.mem_filter, Finset.mem_range] at hs
  obtain ⟨hs, p, hp, hper⟩ := hs
  rw [Finset.mem_Icc] at hp
  exact ⟨s, p, by omega, hp.2, by omega, (periodicOn_full_iff (by omega)).mpr hper, hY'⟩

/-! ## The two level properties -/

section LevelProperties

variable {σ N : ℕ}

/-- The rejected tail of coordinate `i` has a periodic cover at level `l`. -/
def CoordinateCover (C : LevelBounds σ k N) (l : ℕ) (M : StructuralReader α S k)
    (W : Fin k → List α)
    (i : Fin k) : Prop :=
  PeriodicCover (W i) (M.firstRejection W i) (C.pieceCountBase + 1) (C.periodBound l)
      (C.uncoveredBound l)

/-- The rejected tail of coordinate `i` has a periodic cover at level `l`, and the longest
suffix of `W i` with period at most `periodBound l` is shorter than `terminalLengthBound l`. -/
def LevelCoverProperty [DecidableEq α] (C : LevelBounds σ k N) (l : ℕ) (M : StructuralReader α S k)
    (W : Fin k → List α) (i : Fin k) : Prop :=
  CoordinateCover C l M W i ∧ longestPeriodicSuffixLength (C.periodBound l) (W i) <
      C.terminalLengthBound l

/-- A periodic cover at level `l` is one at every higher level. -/
theorem coordinateCover_mono (C : LevelBounds σ k N) {l l' : ℕ} (hl : l ≤ l')
    {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : CoordinateCover C l M W i) : CoordinateCover C l' M W i :=
  PeriodicCover.mono h le_rfl (C.periodBound_mono hl) (C.uncoveredBound_mono hl)

end LevelProperties

/-! ## First rejection along repeated text -/

section FirstRejection

variable {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k}

/-- A state repeated at cuts `a' < a ≤ J` and followed by the same text up to the first rejected
cut `J` would give an earlier rejected cut, which is impossible. -/
theorem no_early_repeat (h : M.Eligible W i) {a' a : ℕ} (ha : a' < a)
    (haJ : a ≤ M.firstRejection W i)
    (htext : ∀ t, t < M.firstRejection W i - a → (W i)[a' + t]? = (W i)[a + t]?)
    (hq : M.runPrefix W i a' = M.runPrefix W i a) : False := by
  obtain ⟨hJl, hJr, hJb⟩ := StructuralReader.firstRejection_spec h
  set J := M.firstRejection W i
  have htake : ((W i).drop a').take (J - a) = ((W i).drop a).take (J - a) := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < J - a
    · rw [List.getElem?_take_of_lt ht, List.getElem?_take_of_lt ht, List.getElem?_drop,
        List.getElem?_drop]
      exact htext t ht
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have h1 : M.runPrefix W i (a' + (J - a)) = M.runPrefix W i J := by
    rw [Table.runPrefix_add, hq, htake, ← Table.runPrefix_add, show a + (J - a) = J by omega]
  have h2 := hJb (a' + (J - a)) (by omega)
  rw [h1, hJr] at h2
  exact absurd h2 (by decide)

/-- An interval of period `p` that starts at `s ≤ J` and reaches the first rejected cut `J`
satisfies `J - s < N · p`. -/
theorem firstRejection_sub_lt_word [Fintype S] (h : M.Eligible W i) {p s e : ℕ} (hp : 0 < p)
    (hper : PeriodicOn (W i) p s e) (hsJ : s ≤ M.firstRejection W i)
        (hJe : M.firstRejection W i ≤ e) :
    M.firstRejection W i - s < Fintype.card S * p := by
  classical
  by_contra hge
  push Not at hge
  obtain ⟨hJl, hJr, hJb⟩ := StructuralReader.firstRejection_spec h
  have hcut : ∀ j : Fin (Fintype.card S), s + j * p < M.firstRejection W i := by
    intro j
    have : (j : ℕ) * p < Fintype.card S * p := Nat.mul_lt_mul_of_pos_right j.isLt hp
    omega
  let f : Fin (Fintype.card S) → {q : S // M.rejected q = false} :=
    fun j => ⟨M.runPrefix W i (s + j * p), hJb _ (hcut j)⟩
  have hcard : Fintype.card {q : S // M.rejected q = false} <
      Fintype.card (Fin (Fintype.card S)) := by
    rw [Fintype.card_fin]
    exact Fintype.card_subtype_lt (p := fun q => M.rejected q = false)
        (x := M.runPrefix W i (M.firstRejection W i))
      (by rw [hJr]; decide)
  obtain ⟨j₁, j₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hq : M.runPrefix W i (s + j₁ * p) = M.runPrefix W i (s + j₂ * p) := congrArg Subtype.val heq
  have key : ∀ a b : Fin (Fintype.card S), (a : ℕ) < b →
      M.runPrefix W i (s + a * p) = M.runPrefix W i (s + b * p) → False := by
    intro a b hab hq'
    have hm : (a : ℕ) * p < b * p := Nat.mul_lt_mul_of_pos_right hab hp
    have hsplit : ((b : ℕ) - a) * p + a * p = b * p := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hab.le]
    apply no_early_repeat h (a' := s + a * p) (a := s + b * p) (by omega) (hcut b).le _ hq'
    intro t ht
    have := hper.eq_of_le_add (p := s + a * p + t) (by omega) ((b : ℕ) - a) (by omega)
    rw [this]; congr 1; omega
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact key j₁ j₂ hlt hq
  · exact key j₂ j₁ hlt hq.symm

end FirstRejection

/-- If an interval `[s, e)` has period `p` and contains an interval `[a, b)` of length at least
`p + g` with period `g`, then the whole interval `[s, e)` has period `g`. -/
theorem periodicOn_of_window {w : List α} {p g s e a b : ℕ} (hp : PeriodicOn w p s e)
    (hg : PeriodicOn w g a b)
    (hsa : s ≤ a) (hbe : b ≤ e) (hlen : a + p + g ≤ b) (hp0 : 0 < p) : PeriodicOn w g s e := by
  intro x hx hxe
  set y := a + (x + p * a - a) % p with hy
  have hya : a ≤ y := Nat.le_add_right _ _
  have hyp : y < a + p := by have := Nat.mod_lt (x + p * a - a) hp0; omega
  have hmod : y % p = x % p := by
    have h1 : a ≤ p * a := Nat.le_mul_of_pos_left a hp0
    have e1 : y ≡ a + (x + p * a - a) [MOD p] := Nat.ModEq.add_left a (Nat.mod_modEq _ _)
    have e2 : a + (x + p * a - a) = x + p * a := by omega
    rw [e2] at e1
    have e3 : x + p * a ≡ x [MOD p] := by
      unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]
    exact e1.trans e3
  have hmod' : (y + g) % p = (x + g) % p := by rw [Nat.add_mod, hmod, ← Nat.add_mod]
  rw [hp.eq_of_mod hx (by omega) (by omega) (by omega) hmod.symm, hg y hya (by omega),
    hp.eq_of_mod (by omega) (by omega) (by omega) (by omega) hmod']

/-! ## Monotonicity of the level cover property -/

section Monotonicity

variable {σ : ℕ} [DecidableEq α] [Fintype S]

/-- The level cover property at level `l` implies the one at level `l + 1`. -/
theorem levelCoverProperty_succ (C : LevelBounds σ k (Fintype.card S)) {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) {l : ℕ}
        (hK : LevelCoverProperty C l M W i) :
    LevelCoverProperty C (l + 1) M W i := by
  refine ⟨coordinateCover_mono C (Nat.le_succ l) hK.1, ?_⟩
  by_contra hge
  push Not at hge
  have hYK := C.terminalLengthBound_gt_cover l
  have hY1 : 0 < C.terminalLengthBound (l + 1) := by omega
  obtain ⟨s, p, hp, hpE, hs, hper, hYs⟩ := exists_of_le_longestPeriodicSuffixLength hY1 hge
  have hYm : C.terminalLengthBound l ≤ C.terminalLengthBound (l + 1) :=
      C.terminalLengthBound_mono (by omega)
  have hKt := hK.2
  by_cases hpl : p ≤ C.periodBound l
  · have := le_longestPeriodicSuffixLength hp hpl hs hper
    omega
  push Not at hpl
  obtain ⟨fs, hfl, hfv, hunc⟩ := hK.1
  have hJn : M.firstRejection W i ≤ (W i).length := StructuralReader.firstRejection_le h
  have hNp : Fintype.card S * p ≤ Fintype.card S * C.periodBound (l + 1) :=
      Nat.mul_le_mul_left _ hpE
  have hX : C.terminalLengthBound (l + 1) ≤ (W i).length - max s (M.firstRejection W i) +
      Fintype.card S * C.periodBound (l + 1) := by
    by_cases hsJ : M.firstRejection W i ≤ s
    · have : max s (M.firstRejection W i) = s := max_eq_left hsJ
      omega
    · have := firstRejection_sub_lt_word h hp hper (by omega) hJn
      have : max s (M.firstRejection W i) = M.firstRejection W i := max_eq_right (by omega)
      omega
  have hex : ∃ f ∈ fs, p + f.period ≤ f.stop - max (max s (M.firstRejection W i)) f.start := by
    by_contra hno
    push Not at hno
    set X := Finset.Ico (max s (M.firstRejection W i)) (W i).length with hXdef
    have hsplit := Finset.card_filter_add_card_filter_not (s := X) (p := Covers fs)
    have h1 : (X.filter (fun x => ¬ Covers fs x)).card ≤ C.uncoveredBound l := by
      refine le_trans (Finset.card_le_card ?_) hunc
      intro x hx
      simp only [X, uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
      exact ⟨⟨by omega, hx.1.2⟩, hx.2⟩
    have h2 : (X.filter (Covers fs)).card ≤ fs.length * (p + C.periodBound l) := by
      refine (card_filter_covers_le X fs).trans ?_
      have := List.sum_le_length_nsmul
        (fs.map (fun f => (X.filter (fun x => f.start ≤ x ∧ x < f.stop)).card))
            (p + C.periodBound l) (by
        intro y hy
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
        have hfv' := hfv f hf
        have hnf := hno f hf
        calc (X.filter (fun x => f.start ≤ x ∧ x < f.stop)).card
            ≤ (Finset.Ico (max (max s (M.firstRejection W i)) f.start) f.stop).card :=
              Finset.card_le_card (fun x hx => by
                simp only [X, Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
          _ = f.stop - max (max s (M.firstRejection W i)) f.start := Nat.card_Ico _ _
          _ ≤ p + C.periodBound l := by have := hfv'.2.1; omega)
      simpa using this
    have h3 : fs.length * (p + C.periodBound l) ≤ (C.pieceCountBase + 1) *
        (2 * C.periodBound (l + 1)) :=
      Nat.mul_le_mul hfl
          (by have : C.periodBound l ≤ C.periodBound (l + 1) := C.periodBound_mono (by omega);
              omega)
    have h4 : X.card = (W i).length - max s (M.firstRejection W i) := Nat.card_Ico _ _
    omega
  obtain ⟨f, hf, hfm⟩ := hex
  obtain ⟨hfp, hfE, hfe, hfper⟩ := hfv f hf
  have h1 : PeriodicOn (W i) p (max (max s (M.firstRejection W i)) f.start) f.stop :=
    hper.mono (by omega) hfe
  have h2 : PeriodicOn (W i) f.period (max (max s (M.firstRejection W i)) f.start) f.stop :=
    hfper.mono (le_max_right _ _) le_rfl
  have hgle : p.gcd f.period ≤ f.period := Nat.gcd_le_right _ hfp
  have hgpos : 0 < p.gcd f.period := Nat.gcd_pos_of_pos_left _ hp
  have hg := period_extend_gcd (by omega) hfe h1 h2 (by omega)
  have hwin := periodicOn_of_window hper hg (by omega) hfe (by omega) hp
  have := le_longestPeriodicSuffixLength hgpos (hgle.trans hfE) hs hwin
  omega

end Monotonicity

/-! ## The stable level -/

/-- Finite avoidance: if for each `u ∈ U` at most `c` elements of `R` fail `p u`, and
`|U| · c < |R|`, some element of `R` satisfies `p u` for every `u ∈ U`. -/
theorem exists_forall_of_card_filter_not_le {ι κ : Type*} {R : Finset κ} {U : Finset ι}
    (p : ι → κ → Prop) [∀ u, DecidablePred (p u)] {c : ℕ}
    (hbad : ∀ u ∈ U, (R.filter fun r => ¬ p u r).card ≤ c) (hlt : U.card * c < R.card) :
    ∃ r ∈ R, ∀ u ∈ U, p u r := by
  classical
  have hU : (U.biUnion fun u => R.filter fun r => ¬ p u r).card < R.card :=
    (Finset.card_biUnion_le_card_mul _ _ _ hbad).trans_lt hlt
  obtain ⟨r, hr, hrn⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
  exact ⟨r, hr, fun u hu => by_contra fun h =>
    hrn (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨hr, h⟩⟩)⟩

/-- For finitely many monotone predicates on levels, one of the triples `{3j, 3j+1, 3j+2}` with
`j ≤ |ι|` sees no change of any of them. -/
theorem exists_const_triple {ι : Type} [Fintype ι] (P : ι → ℕ → Prop)
    (hmono : ∀ x l, P x l → P x (l + 1)) :
    ∃ j, j ≤ Fintype.card ι ∧ ∀ x, (P x (3 * j) ↔ P x (3 * j + 2)) := by
  classical
  have hmono' : ∀ x l l', l ≤ l' → P x l → P x l' := by
    intro x l l' hl
    induction l', hl using Nat.le_induction with
    | base => exact id
    | succ l' _ ih => exact fun h => hmono x _ (ih h)
  have key : ∀ x j, ¬ (P x (3 * j) ↔ P x (3 * j + 2)) → ¬ P x (3 * j) ∧ P x (3 * j + 2) := by
    intro x j hj
    by_cases h0 : P x (3 * j)
    · exact absurd ⟨fun _ => hmono' x _ _ (by omega) h0, fun _ => h0⟩ hj
    · refine ⟨h0, ?_⟩
      by_contra h2
      exact hj ⟨fun h => absurd h h0, fun h => absurd h h2⟩
  -- each predicate changes in at most one triple
  obtain ⟨j, hj, hjP⟩ := exists_forall_of_card_filter_not_le
    (R := Finset.range (Fintype.card ι + 1)) (U := Finset.univ)
    (fun x j => P x (3 * j) ↔ P x (3 * j + 2)) (c := 1) (fun x _ => by
      rw [Finset.card_le_one]
      intro j hj j' hj'
      simp only [Finset.mem_filter] at hj hj'
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact (key x j' hj'.2).1 (hmono' x _ _ (by omega) (key x j hj.2).2)
      · exact (key x j hj.2).1 (hmono' x _ _ (by omega) (key x j' hj'.2).2)) (by simp)
  exact ⟨j, by simp at hj; omega, fun x => hjP x (Finset.mem_univ x)⟩

section Stable

variable {σ : ℕ} [DecidableEq α] [Fintype S]

/-- Some level `2 ≤ l ≤ levelCount k` has, for every coordinate, the same periodic cover
property at levels `l - 1` and `l`, and the same level cover property at levels `l - 2` and
`l - 1`. -/
theorem exists_stable_level (C : LevelBounds σ k (Fintype.card S)) (M : StructuralReader α S k)
    (W : Fin k → List α) (hE : ∀ i, M.Eligible W i) :
    ∃ l, 2 ≤ l ∧ l ≤ levelCount k ∧
        ∀ i, (CoordinateCover C (l - 1) M W i ↔ CoordinateCover C l M W i) ∧
      (LevelCoverProperty C (l - 2) M W i ↔ LevelCoverProperty C (l - 1) M W i) := by
  let P : Fin k ⊕ Fin k → ℕ → Prop := fun x l => match x with
    | .inl i => CoordinateCover C l M W i
    | .inr i => LevelCoverProperty C l M W i
  have hmono : ∀ x l, P x l → P x (l + 1) := by
    intro x l hx
    cases x with
    | inl i => exact coordinateCover_mono C (Nat.le_succ l) hx
    | inr i => exact levelCoverProperty_succ C (hE i) hx
  obtain ⟨j, hj, hjP⟩ := exists_const_triple P hmono
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by simp; ring
  rw [hcard] at hj
  refine ⟨3 * j + 2, by omega, by unfold levelCount; omega, fun i => ⟨?_, ?_⟩⟩
  · have h := hjP (.inl i)
    simp only [P] at h
    rw [show 3 * j + 2 - 1 = 3 * j + 1 by omega]
    exact ⟨fun h1 => coordinateCover_mono C (Nat.le_succ _) h1,
      fun h2 => coordinateCover_mono C (Nat.le_succ _) (h.mpr h2)⟩
  · have h := hjP (.inr i)
    simp only [P] at h
    rw [show 3 * j + 2 - 2 = 3 * j by omega, show 3 * j + 2 - 1 = 3 * j + 1 by omega]
    exact ⟨fun h1 => levelCoverProperty_succ C (hE i) h1,
      fun h2 => h.mpr (levelCoverProperty_succ C (hE i) h2)⟩

end Stable

/-! ## Suffix chains of words with the level cover property -/

/-- Counting by states: if the elements of `A`, ordered by an injective key, carry pairwise
distinct states other than `d`, then `A` has at most `N - 1` elements. -/
theorem card_le_card_sub_one_of_injOn {κ S : Type*} [Fintype S] (A : Finset κ)
    (key : κ → ℕ) (hkey : Set.InjOn key A) (f : κ → S) (d : S)
    (hinj : ∀ x ∈ A, ∀ y ∈ A, key x < key y → f x ≠ f y) (hd : ∀ x ∈ A, f x ≠ d) :
    A.card ≤ Fintype.card S - 1 := by
  classical
  have h := Finset.card_le_card_of_injOn f (t := Finset.univ.erase d)
    (fun x hx => Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hd x hx, Finset.mem_univ _⟩))
    (fun x hx y hy he => by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne fun h => hne (hkey hx hy h) with h | h
      · exact hinj x hx y hy h he
      · exact hinj y hy x hx h he.symm)
  rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h

section Chains

variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- A word with the level cover property at level `m` has suffix chains of at most
`chainLengthBound m + N` members. The members are counted by their suffix starts: at most
`N - 1` at or before the first rejected cut, one empty suffix, the uncovered positions of the
rejected tail, fewer than `terminalLengthBound m` in the periodic suffix, and at most twice the
period for each factor of the cover. -/
theorem levelCoverProperty_chainBound (C : LevelBounds σ k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} {m : ℕ} (h : M.Eligible W i)
        (hK : LevelCoverProperty C m M W i) :
    ChainBound (W i) (C.chainLengthBound m + Fintype.card S) := by
  classical
  intro bs hbs
  by_cases h2 : bs.length ≤ 1
  · omega
  push Not at h2
  have hle := hbs.le_length (by omega)
  obtain ⟨fs, hfl, hfv, hunc⟩ := hK.1
  have hLY : longestPeriodicSuffixLength (C.periodBound m) (W i) < C.terminalLengthBound m := hK.2
  have hJn : M.firstRejection W i ≤ (W i).length := StructuralReader.firstRejection_le h
  set A : Finset ℕ := bs.toFinset.image (fun b => (W i).length - b) with hA
  have hcardA : A.card = bs.length := by
    rw [hA, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hbs.nodup]
    intro b hb b' hb' he
    rw [Finset.mem_coe, List.mem_toFinset] at hb hb'
    have := hle b hb; have := hle b' hb'
    simp only at he; omega
  have hAle : ∀ x ∈ A, x ≤ (W i).length := by
    intro x hx; obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx; omega
  have hcmp : ∀ x ∈ A, ∀ y ∈ A, x < y → (W i).drop y <+: (W i).drop x := by
    intro x hx y hy hxy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hy
    rw [List.mem_toFinset] at hb hb'
    have hbb : b' < b := by have := hle b hb; have := hle b' hb'; omega
    exact hbs.prefix_of_lt hb' hb hbb
  have hper : ∀ x ∈ A, ∀ y ∈ A, x < y → PeriodicOn (W i) (y - x) x (W i).length := by
    intro x hx y hy hxy
    have hpre := (prefix_drop_iff (hAle x hx)).mp (hcmp x hx y hy hxy)
    intro p hp1 hp2
    have := hpre.2 (p - x) (by simp; omega)
    rw [List.getElem?_drop, show x + (p - x) = p by omega] at this
    rw [this]; congr 1; omega
  -- the five kinds of start
  set n := (W i).length with hn
  set L := longestPeriodicSuffixLength (C.periodBound m) (W i) with hL
  set J := M.firstRejection W i with hJ
  let Af : PeriodicFactor → Finset ℕ :=
      fun f => A.filter (fun x => f.start ≤ x ∧ x < f.stop ∧ x + L < n)
  have hsub : A ⊆ A.filter (fun x => x ≤ J) ∪ A.filter (fun x => x = n) ∪
      A.filter (fun x => J ≤ x ∧ x < n ∧ ¬ Covers fs x) ∪
      A.filter (fun x => n ≤ x + L ∧ x < n) ∪ fs.toFinset.biUnion Af := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset, Af]
    by_cases h1 : x ≤ J
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hx, h1⟩)))
    by_cases h2 : x = n
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hx, h2⟩)))
    have hxn : x < n := lt_of_le_of_ne (hAle x hx) h2
    by_cases h3 : Covers fs x
    · obtain ⟨f, hf, hfs, hfe⟩ := h3
      by_cases h4 : n ≤ x + L
      · exact Or.inl (Or.inr ⟨hx, h4, hxn⟩)
      · exact Or.inr ⟨f, hf, hx, hfs, hfe, by omega⟩
    · exact Or.inl (Or.inl (Or.inr ⟨hx, by omega, hxn, h3⟩))
  -- starts before the first rejected cut carry distinct live states
  have hH : (A.filter (fun x => x ≤ J)).card ≤ Fintype.card S - 1 := by
    apply card_le_card_sub_one_of_injOn _ id (Set.injOn_id _) (M.runPrefix W i) M.dead
    · intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      exact StructuralReader.runPrefix_ne_of_le_firstRejection h hxy hy.2 (hcmp x hx.1 y hy.1 hxy)
    · intro x _; exact h.runPrefix_ne x
  have hE : (A.filter (fun x => x = n)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    omega
  have hU : (A.filter (fun x => J ≤ x ∧ x < n ∧ ¬ Covers fs x)).card ≤ C.uncoveredBound m := by
    refine le_trans (Finset.card_le_card ?_) hunc
    intro x hx
    simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    exact ⟨⟨hx.2.1, hx.2.2.1⟩, hx.2.2.2⟩
  have hT : (A.filter (fun x => n ≤ x + L ∧ x < n)).card ≤ L := by
    calc _ ≤ (Finset.Ico (n - L) n).card := Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
      _ ≤ L := by rw [Nat.card_Ico]; omega
  -- each factor contributes at most twice the period bound of the level
  have hAf : ∀ f ∈ fs, (Af f).card ≤ 2 * C.periodBound m := by
    intro f hf
    obtain ⟨hfp, hfE, hfe, hfper⟩ := hfv f hf
    by_cases hshort : f.stop < f.start + 2 * f.period
    · calc (Af f).card ≤ (Finset.Ico f.start f.stop).card := Finset.card_le_card (fun x hx => by
              simp only [Af, Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
        _ ≤ 2 * C.periodBound m := by rw [Nat.card_Ico]; omega
    push Not at hshort
    obtain ⟨d, P, hPl, hPs, hPe, hdvd⟩ : ∃ d, ∃ P : Piece W d, P.coordinate = i ∧ P.start ≤
        f.start ∧ f.stop ≤ P.stop ∧
        d ∣ f.period := by
      obtain ⟨P, h1, h2, h3, h4⟩ := long_factor_in_piece W i hfp hfe hshort hfper
      exact ⟨_, P, h1, h2, h3, h4⟩
    have hdpos : 0 < d := P.period_pos
    have hdle : d ≤ f.period := Nat.le_of_dvd hfp hdvd
    have hPper : PeriodicOn (W i) d P.start P.stop := by have := P.periodicOn; rwa [hPl] at this
    have hPle : P.stop ≤ n := by have := P.stop_le_length; rwa [hPl] at this
    by_cases hterm : P.stop = n
    · have hTl := le_longestPeriodicSuffixLength hdpos (hdle.trans hfE) (by omega) (hterm ▸ hPper)
      have hempty : Af f = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        simp only [Af, Finset.mem_filter] at hx
        omega
      rw [hempty]; simp
    have hbrk : (W i)[P.stop]? ≠ (W i)[P.stop - d]? := by
      have hmaxR := P.right_maximal
      rw [hPl] at hmaxR
      rcases hmaxR with h' | h'
      · exact absurd h' hterm
      · exact h'
    have hone : (A.filter (fun x => P.start ≤ x ∧ x + d ≤ P.stop)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_filter] at hx hy
      by_contra hne
      have main : ∀ x y, x ∈ A → P.start ≤ x → y ∈ A → y + d ≤ P.stop → x < y → False := by
        intro x y hxA hxs hyA hyd hxy
        have hδ := hper x hxA y hyA hxy
        have hδ' : PeriodicOn (W P.coordinate) (y - x) x P.stop := by
          rw [hPl]; exact hδ.mono le_rfl hPle
        have hdδ := P.dvd_of_periodicOn hxs hδ' (by omega)
        obtain ⟨c, hc⟩ := hdδ
        apply hbrk
        have e1 := hδ (P.stop - (y - x)) (by omega) (by omega)
        rw [show P.stop - (y - x) + (y - x) = P.stop by omega] at e1
        rw [← e1]
        apply hPper.eq_of_mod (by omega) (by omega) (by omega) (by omega)
        rw [hc, Nat.sub_mul_mod (by rw [← hc]; omega)]
        have := Nat.sub_mul_mod (x := P.stop) (k := 1) (n := d) (by omega)
        rw [Nat.mul_one] at this
        rw [this]
      rcases Nat.lt_or_gt_of_ne hne with hxy | hxy
      · exact main x y hx.1 hx.2.1 hy.1 hy.2.2 hxy
      · exact main y x hy.1 hy.2.1 hx.1 hx.2.2 hxy
    have hrest : (A.filter (fun x => P.stop < x + d ∧ x < P.stop)).card ≤ d - 1 := by
      calc _ ≤ (Finset.Ico (P.stop + 1 - d) P.stop).card := Finset.card_le_card (fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
        _ ≤ d - 1 := by rw [Nat.card_Ico]; omega
    calc (Af f).card ≤ (A.filter (fun x => P.start ≤ x ∧ x + d ≤ P.stop) ∪
          A.filter (fun x => P.stop < x + d ∧ x < P.stop)).card :=
          Finset.card_le_card (fun x hx => by
            simp only [Af, Finset.mem_filter, Finset.mem_union] at hx ⊢
            by_cases hxd : x + d ≤ P.stop
            · exact Or.inl ⟨hx.1, by omega, hxd⟩
            · exact Or.inr ⟨hx.1, by omega, by omega⟩)
      _ ≤ 1 + (d - 1) := (Finset.card_union_le _ _).trans (Nat.add_le_add hone hrest)
      _ ≤ 2 * C.periodBound m := by omega
  have hB : (fs.toFinset.biUnion Af).card ≤ (C.pieceCountBase + 1) * (2 * C.periodBound m) := by
    calc (fs.toFinset.biUnion Af).card ≤ ∑ f ∈ fs.toFinset, (Af f).card := Finset.card_biUnion_le
      _ ≤ fs.toFinset.card • (2 * C.periodBound m) :=
          Finset.sum_le_card_nsmul _ _ _ (fun f hf => hAf f (List.mem_toFinset.mp hf))
      _ ≤ (C.pieceCountBase + 1) * (2 * C.periodBound m) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul ((List.toFinset_card_le fs).trans hfl) le_rfl
  have hXK := C.chainLengthBound_ge_cover m
  have htot := (Finset.card_le_card hsub).trans <| (Finset.card_union_le _ _).trans <|
    Nat.add_le_add_right ((Finset.card_union_le _ _).trans <| Nat.add_le_add_right
      ((Finset.card_union_le _ _).trans <| Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _
  omega

end Chains

end DeciSigma1.Holes.Tail
