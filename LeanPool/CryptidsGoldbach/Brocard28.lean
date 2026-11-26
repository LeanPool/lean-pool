/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Veljjanoski
-/

-- Modified for Lean Pool.

module

public import LeanPool.CryptidsGoldbach.Goldbach21
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Brocard28

The 28-state Turing machine `brocard_28` halts on the blank tape if and only if Brocard's
problem `n! + 1 = m ^ 2` has a solution with `n > 7`, i.e. beyond the three known solutions
`n = 4, 5, 7`.

## Provenance and Attribution

The machine and the proofs are by Daniel Veljjanoski, with Claude (Anthropic) as assistant
(November 2026). Earlier machines for the same problem are Charlie Reams's 61-state machine
with a Lean proof (`calr3/tinycryptids`, November 2026) and a 43-state table without a
machine-checked proof by Tandi, Gonzalez-Hendrix and Brown (<https://arxiv.org/abs/2605.20215>);
Gasarch's SIGACT News Open Problems Column (September 2026, Open Problem 6.2) asks to improve
the 43-state count and reports Jonathan Brown's conjecture that about 30 states may suffice.

## Machine Layout

The tape holds, left to right, a block `N` of `n` ones, a separator, and a block `B` of ones,
all in unary. Between rounds `B` holds `n! / 8` ones (`3` at `n = 4`). A round multiplies `B`
by `n + 1` and grows `N` by one cell, then tests whether `(n + 1)! / 8` is a triangular number
`1 + 2 + ⋯ + k`; this holds if and only if `(n + 1)! + 1` is a perfect square (`m = 2k + 1`).

* Multiply (states `2`–`11`): `LN0`/`LN1` walk left and write a `1` left of `N`; `EN` walks a
  hole through `N`, and for every cell `R0`/`R1`/`L0`/`L1`/`EC` copy the template `B` once,
  cell by cell, to the right end; `X` merges. `B` becomes `(n + 1) B + 1` ones.
* Test (states `1`, `12`–`19`): a hole walks right through `B` (`TLs`/`TLx` create it, `TE`
  moves it); a block `S` right of `B` holds the current chunk size with a hole walking left
  (`TR0`/`TR1`, `SB`); each wrap of `S` adds a cell to `S` for free (the blank beyond `S`
  acts as the hole), and `SC` then checks whether `B` is exhausted: if so, success.
* Fail (states `20`–`22`): `ER`/`ER2`/`ER3` erase `S`, and `ER3` erases the last cell of `B`
  on the way back, which cancels the extra cell left by the merge.
* Gate (states `23`–`27`): on success `M0`–`M3` walk left over `B` counting its ones modulo
  `4`. At the separator, residue `0` halts (`M0` reading `0` is undefined); residues `2` and `3`
  return via `Bs`, which fills the hole of `B`, and `ER` erases `S`. Since `32 ∣ n!` for
  `n ≥ 8`, a success with `n ≥ 8` has residue `0`, while the known solutions have
  `5! / 8 = 15 ≡ 3` and `7! / 8 = 630 ≡ 2 (mod 4)` and are suppressed. Residue `1` never
  occurs at a success, so `M1` reading `0` is free for the start.
* Start: the machine starts in `GO` (state `0`) on the blank tape. `GO` and the two cells the
  loop never reads (`TLx` and `M1` reading `0`) steer the loop's own states to write
  `1111 0 111` in `46` steps, ending in `LN1` on the blank left of `N`: the configuration
  every round passes through.
-/

@[expose] public section

namespace ConjectureMachines.Brocard28

open Turing
open StateTransition
open Goldbach21.Tape (mkL_cons mk'_cons)
open Goldbach21 (nSteps nSteps_zero nSteps_succ nSteps_reaches nSteps_add nSteps_bind_eq
  step_nSteps step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)

local notation "mkL" => Goldbach21.Tape.mkL

/-- The blank half of the binary tape. -/
abbrev B0 : ListBlank (Fin 2) := Goldbach21.B0

theorem B0_cons_zero : B0.cons 0 = B0 := Goldbach21.B0_cons_zero

theorem mkRight_blank (L : ListBlank (Fin 2)) : Tape.mk' L B0 = ⟨0, L, B0⟩ := rfl

/-- Prepend `k` ones to a half tape. -/
def ones (k : ℕ) (L : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (List.replicate k 1) L

theorem ones_succ' (k : ℕ) (L : ListBlank (Fin 2)) : ones (k + 1) L = ones k (L.cons 1) := by
  rw [ones, List.replicate_succ', ListBlank.append_assoc]
  rfl

theorem ones_add (j k : ℕ) (L : ListBlank (Fin 2)) : ones (j + k) L = ones j (ones k L) := by
  rw [ones, List.replicate_add, ListBlank.append_assoc]
  rfl

/-- The 28-state, two-symbol transition table from the upstream `brocard_28` artifact. -/
def brocard28 : Machine 28 2 := Machine.ofRows [
  [some (1, .left, 10), some (1, .right, 3)],
  [some (0, .left, 10), some (0, .right, 13)],
  [some (0, .left, 3), some (1, .left, 2)],
  [some (1, .right, 4), some (1, .left, 3)],
  [some (0, .right, 11), some (0, .right, 5)],
  [some (0, .right, 10), some (1, .right, 5)],
  [some (0, .right, 7), some (1, .right, 6)],
  [some (1, .left, 8), some (1, .right, 7)],
  [some (0, .left, 9), some (1, .left, 8)],
  [some (1, .right, 10), some (1, .left, 9)],
  [some (0, .left, 2), some (0, .right, 6)],
  [some (1, .right, 12), some (1, .right, 11)],
  [some (0, .right, 1), some (1, .left, 12)],
  [some (0, .right, 14), some (1, .right, 13)],
  [some (1, .left, 15), some (1, .right, 14)],
  [some (0, .left, 16), some (0, .left, 17)],
  [some (0, .left, 23), some (1, .right, 13)],
  [some (0, .left, 18), some (1, .left, 17)],
  [some (1, .right, 19), some (1, .left, 18)],
  [some (0, .right, 20), some (0, .right, 13)],
  [some (0, .right, 21), some (0, .right, 20)],
  [some (0, .left, 22), some (0, .right, 21)],
  [some (0, .left, 22), some (0, .left, 2)],
  [none, some (1, .left, 24)],
  [some (1, .right, 0), some (1, .left, 25)],
  [some (0, .right, 27), some (1, .left, 26)],
  [some (0, .right, 27), some (1, .left, 23)],
  [some (1, .right, 20), some (1, .right, 27)]
]

theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

theorem stepR {q q' : Fin 28} {a b : Fin 2}
    (h : brocard28.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step brocard28 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

theorem stepL {q q' : Fin 28} {a b : Fin 2}
    (h : brocard28.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step brocard28 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table

States in file order:
`0` = GO, `1` = TLx, `2` = LN0, `3` = LN1, `4` = EN, `5` = S1, `6` = R0, `7` = R1, `8` = L0,
`9` = L1, `10` = EC, `11` = X, `12` = TLs, `13` = TR0, `14` = TR1, `15` = SB, `16` = SC,
`17` = TL0, `18` = TL1, `19` = TE, `20` = ER, `21` = ER2, `22` = ER3, `23` = M0, `24` = M1,
`25` = M2, `26` = M3, `27` = Bs.
-/

theorem sGO_0 (L R) : step brocard28 ⟨0, ⟨0, L, R⟩⟩ = some ⟨10, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sGO_1 (L R) : step brocard28 ⟨0, ⟨1, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTLx_0 (L R) : step brocard28 ⟨1, ⟨0, L, R⟩⟩ = some ⟨10, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sTLx_1 (L R) : step brocard28 ⟨1, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sLN0_0 (L R) : step brocard28 ⟨2, ⟨0, L, R⟩⟩ = some ⟨3, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sLN0_1 (L R) : step brocard28 ⟨2, ⟨1, L, R⟩⟩ = some ⟨2, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sLN1_0 (L R) : step brocard28 ⟨3, ⟨0, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sLN1_1 (L R) : step brocard28 ⟨3, ⟨1, L, R⟩⟩ = some ⟨3, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sEN_0 (L R) : step brocard28 ⟨4, ⟨0, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sEN_1 (L R) : step brocard28 ⟨4, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sS1_0 (L R) : step brocard28 ⟨5, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sS1_1 (L R) : step brocard28 ⟨5, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sR0_0 (L R) : step brocard28 ⟨6, ⟨0, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sR0_1 (L R) : step brocard28 ⟨6, ⟨1, L, R⟩⟩ = some ⟨6, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sR1_0 (L R) : step brocard28 ⟨7, ⟨0, L, R⟩⟩ = some ⟨8, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sR1_1 (L R) : step brocard28 ⟨7, ⟨1, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sL0_0 (L R) : step brocard28 ⟨8, ⟨0, L, R⟩⟩ = some ⟨9, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sL0_1 (L R) : step brocard28 ⟨8, ⟨1, L, R⟩⟩ = some ⟨8, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sL1_0 (L R) : step brocard28 ⟨9, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sL1_1 (L R) : step brocard28 ⟨9, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sEC_0 (L R) : step brocard28 ⟨10, ⟨0, L, R⟩⟩ = some ⟨2, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sEC_1 (L R) : step brocard28 ⟨10, ⟨1, L, R⟩⟩ = some ⟨6, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sX_0 (L R) : step brocard28 ⟨11, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sX_1 (L R) : step brocard28 ⟨11, ⟨1, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTLs_0 (L R) : step brocard28 ⟨12, ⟨0, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTLs_1 (L R) : step brocard28 ⟨12, ⟨1, L, R⟩⟩ = some ⟨12, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTR0_0 (L R) : step brocard28 ⟨13, ⟨0, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTR0_1 (L R) : step brocard28 ⟨13, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTR1_0 (L R) : step brocard28 ⟨14, ⟨0, L, R⟩⟩ = some ⟨15, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTR1_1 (L R) : step brocard28 ⟨14, ⟨1, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sSB_0 (L R) : step brocard28 ⟨15, ⟨0, L, R⟩⟩ = some ⟨16, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sSB_1 (L R) : step brocard28 ⟨15, ⟨1, L, R⟩⟩ = some ⟨17, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sSC_0 (L R) : step brocard28 ⟨16, ⟨0, L, R⟩⟩ = some ⟨23, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sSC_1 (L R) : step brocard28 ⟨16, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTL0_0 (L R) : step brocard28 ⟨17, ⟨0, L, R⟩⟩ = some ⟨18, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sTL0_1 (L R) : step brocard28 ⟨17, ⟨1, L, R⟩⟩ = some ⟨17, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTL1_0 (L R) : step brocard28 ⟨18, ⟨0, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTL1_1 (L R) : step brocard28 ⟨18, ⟨1, L, R⟩⟩ = some ⟨18, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTE_0 (L R) : step brocard28 ⟨19, ⟨0, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTE_1 (L R) : step brocard28 ⟨19, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER_0 (L R) : step brocard28 ⟨20, ⟨0, L, R⟩⟩ = some ⟨21, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER_1 (L R) : step brocard28 ⟨20, ⟨1, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER2_0 (L R) : step brocard28 ⟨21, ⟨0, L, R⟩⟩ = some ⟨22, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sER2_1 (L R) : step brocard28 ⟨21, ⟨1, L, R⟩⟩ = some ⟨21, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER3_0 (L R) : step brocard28 ⟨22, ⟨0, L, R⟩⟩ = some ⟨22, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sER3_1 (L R) : step brocard28 ⟨22, ⟨1, L, R⟩⟩ = some ⟨2, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sM0_0 (L R : ListBlank (Fin 2)) : step brocard28 ⟨23, ⟨0, L, R⟩⟩ = none := rfl
theorem sM0_1 (L R) : step brocard28 ⟨23, ⟨1, L, R⟩⟩ = some ⟨24, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sM1_0 (L R) : step brocard28 ⟨24, ⟨0, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sM1_1 (L R) : step brocard28 ⟨24, ⟨1, L, R⟩⟩ = some ⟨25, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sM2_0 (L R) : step brocard28 ⟨25, ⟨0, L, R⟩⟩ = some ⟨27, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sM2_1 (L R) : step brocard28 ⟨25, ⟨1, L, R⟩⟩ = some ⟨26, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sM3_0 (L R) : step brocard28 ⟨26, ⟨0, L, R⟩⟩ = some ⟨27, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sM3_1 (L R) : step brocard28 ⟨26, ⟨1, L, R⟩⟩ = some ⟨23, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sBs_0 (L R) : step brocard28 ⟨27, ⟨0, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sBs_1 (L R) : step brocard28 ⟨27, ⟨1, L, R⟩⟩ = some ⟨27, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R

/-! ## Sweeps over Ones -/

theorem sweepR {q : Fin 28}
    (h : ∀ L R, step brocard28 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard28 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ :=
  Goldbach21.nSteps_mk'_right_scan_of_step h k L R

theorem sweepL {q : Fin 28}
    (h : ∀ L R, step brocard28 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard28 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ :=
  Goldbach21.nSteps_mkL_left_scan_of_step h k L R

/-! ## Tape Encoding and Configurations -/

/-- The cells left of `B`: the separator, then the `n` cells of `N`. -/
def NL (n : ℕ) : ListBlank (Fin 2) := (ones n B0).cons 0

/-- Start of a round: `LN0` on the last of the `v + 1` cells of `B`, `N` has `n` cells. -/
def roundCfg (n v : ℕ) : Cfg 28 2 := ⟨2, Tape.mk' (ones v (NL n)) (B0.cons 1)⟩

/-- Start of a test: `TLx` on the first of the `M` cells of `B`. -/
def testCfg (n M : ℕ) : Cfg 28 2 := ⟨1, Tape.mk' (NL n) (ones M B0)⟩

/-- Inside the copy loop: `R0` right of the cursor hole; `u` template cells are done and `v`
remain, `M` has `m` cells, and `N`'s hole has `a` cells to its left and `b` to its right. -/
def copyCfg (a b u v m : ℕ) : Cfg 28 2 :=
  ⟨6, Tape.mk' ((ones u ((ones b ((ones a B0).cons 0)).cons 0)).cons 0)
    (ones v ((ones m B0).cons 0))⟩

/-- `EN` on the first of the `b` remaining cells of `N`, `a` cells to its left; the template
has `V` cells and `M` has `m`. -/
def enCfg (a b V m : ℕ) : Cfg 28 2 :=
  ⟨4, Tape.mk' (ones a B0) (ones b ((ones V ((ones m B0).cons 0)).cons 0))⟩

/-- Inside the test: `TR0` on the separator right of `B`; the hole of `B` has `a` cells to its
left and `r` to its right; `S` has `p` cells, a hole, and `q` cells (`q = 0` and the blank
beyond `S` as the hole for a solid `S` of `p` cells). -/
def advCfg (n a r p q : ℕ) : Cfg 28 2 :=
  ⟨13, Tape.mk' (ones r ((ones a (NL n)).cons 0)) ((ones p ((ones q B0).cons 0)).cons 0)⟩

theorem ones_zero (L : ListBlank (Fin 2)) : ones 0 L = L := rfl

theorem ones_zero_B0 : ones 0 B0 = B0 := rfl

theorem advCfg_solid (n a r p : ℕ) :
    advCfg n a r p 0 = ⟨13, Tape.mk' (ones r ((ones a (NL n)).cons 0)) ((ones p B0).cons 0)⟩ := by
  simp only [advCfg, ones_zero_B0, B0_cons_zero]

/-! ## Multiply (States `2`–`11`) -/

/-- One copy step: the cursor moves one cell right and `M` gains a cell. -/
theorem copy_step (a b u v m : ℕ) :
    ∃ s, nSteps brocard28 s (copyCfg a b u (v + 1) m) = some (copyCfg a b (u + 1) v (m + 1)) := by
  set W := (ones b ((ones a B0).cons 0)).cons 0 with hW
  set Y := ones u W with hY
  have h₁ := sweepR sR0_1 (v + 1) (Y.cons 0) ((ones m B0).cons 0)
  have h₂ : step brocard28 ⟨6, Tape.mk' (ones (v + 1) (Y.cons 0)) ((ones m B0).cons 0)⟩ =
      some ⟨7, Tape.mk' ((ones (v + 1) (Y.cons 0)).cons 0) (ones m B0)⟩ := by
    rw [mk'_cons, sR0_0]
  have h₃ := sweepR sR1_1 m ((ones (v + 1) (Y.cons 0)).cons 0) B0
  have h₄ : step brocard28 ⟨7, Tape.mk' (ones m ((ones (v + 1) (Y.cons 0)).cons 0)) B0⟩ =
      some ⟨8, mkL (ones m ((ones (v + 1) (Y.cons 0)).cons 0)) (B0.cons 1)⟩ := by
    rw [mkRight_blank, sR1_0]
  have h₅ := sweepL sL0_1 m ((ones (v + 1) (Y.cons 0)).cons 0) (B0.cons 1)
  have h₆ : step brocard28 ⟨8, mkL ((ones (v + 1) (Y.cons 0)).cons 0) (ones m (B0.cons 1))⟩ =
      some ⟨9, mkL (ones (v + 1) (Y.cons 0)) ((ones (m + 1) B0).cons 0)⟩ := by
    rw [mkL_cons, sL0_0, ones_succ' m]
  have h₇ := sweepL sL1_1 (v + 1) (Y.cons 0) ((ones (m + 1) B0).cons 0)
  have h₈ : nSteps brocard28 2 ⟨9, mkL (Y.cons 0) (ones (v + 1) ((ones (m + 1) B0).cons 0))⟩ =
      some (copyCfg a b (u + 1) v (m + 1)) := by
    change nSteps brocard28 2 ⟨9, mkL (Y.cons 0) ((ones v ((ones (m + 1) B0).cons 0)).cons 1)⟩ =
      some ⟨6, Tape.mk' ((Y.cons 1).cons 0) (ones v ((ones (m + 1) B0).cons 0))⟩
    simp only [mkL_cons, nSteps_succ, sL1_0, mk'_cons, nSteps_zero, Option.bind_some, sEC_1]
  exact ⟨_, nSteps_bind_eq h₁ (step_nSteps h₂ (nSteps_bind_eq h₃ (step_nSteps h₄
    (nSteps_bind_eq h₅ (step_nSteps h₆ (nSteps_bind_eq h₇ h₈))))))⟩

/-- The last copy step: the cursor leaves the template, `LN0`/`LN1` return to the hole of `N`
and fill it, and `EN` reads the next cell of `N`. -/
theorem copy_done (a b u m : ℕ) :
    ∃ s, nSteps brocard28 s (copyCfg a b u 0 m) = some (enCfg (a + 1) b (u + 1) (m + 1)) := by
  set W := (ones b ((ones a B0).cons 0)).cons 0 with hW
  set Y := ones u W with hY
  have h₂ : step brocard28 (copyCfg a b u 0 m) =
      some ⟨7, Tape.mk' ((Y.cons 0).cons 0) (ones m B0)⟩ := by
    change step brocard28 ⟨6, Tape.mk' (Y.cons 0) ((ones m B0).cons 0)⟩ = _
    rw [mk'_cons, sR0_0]
  have h₃ := sweepR sR1_1 m ((Y.cons 0).cons 0) B0
  have h₄ : step brocard28 ⟨7, Tape.mk' (ones m ((Y.cons 0).cons 0)) B0⟩ =
      some ⟨8, mkL (ones m ((Y.cons 0).cons 0)) (B0.cons 1)⟩ := by
    rw [mkRight_blank, sR1_0]
  have h₅ := sweepL sL0_1 m ((Y.cons 0).cons 0) (B0.cons 1)
  have h₆ : nSteps brocard28 3 ⟨8, mkL ((Y.cons 0).cons 0) (ones m (B0.cons 1))⟩ =
      some ⟨2, mkL (Y.cons 1) ((ones (m + 1) B0).cons 0)⟩ := by
    rw [ones_succ' m]
    simp only [mkL_cons, nSteps_succ, sL0_0, nSteps_zero, Option.bind_some, sL1_0, mk'_cons,
      sEC_0]
  have h₇ := sweepL sLN0_1 (u + 1) W ((ones (m + 1) B0).cons 0)
  have h₈ : step brocard28 ⟨2, mkL W (ones (u + 1) ((ones (m + 1) B0).cons 0))⟩ =
      some ⟨3, mkL (ones b ((ones a B0).cons 0))
        ((ones (u + 1) ((ones (m + 1) B0).cons 0)).cons 0)⟩ := by
    rw [hW, mkL_cons, sLN0_0]
  have h₉ := sweepL sLN1_1 b ((ones a B0).cons 0)
    ((ones (u + 1) ((ones (m + 1) B0).cons 0)).cons 0)
  have h₁₀ : step brocard28 ⟨3, mkL ((ones a B0).cons 0)
      (ones b ((ones (u + 1) ((ones (m + 1) B0).cons 0)).cons 0))⟩ =
      some (enCfg (a + 1) b (u + 1) (m + 1)) := by
    rw [mkL_cons, sLN1_0]
    rfl
  have hY1 : Y.cons 1 = ones (u + 1) W := rfl
  rw [hY1] at h₆
  exact ⟨_, step_nSteps h₂ (nSteps_bind_eq h₃ (step_nSteps h₄ (nSteps_bind_eq h₅
    (nSteps_bind_eq h₆ (nSteps_bind_eq h₇ (step_nSteps h₈ (nSteps_bind_eq h₉
    (step_one h₁₀))))))))⟩

/-- A whole copy of the template. -/
theorem copy_loop (a b u : ℕ) : ∀ v m, ∃ s, nSteps brocard28 s (copyCfg a b u v m) =
    some (enCfg (a + 1) b (u + v + 1) (m + v + 1)) := by
  intro v
  induction v generalizing u with
  | zero => intro m; simpa using copy_done a b u m
  | succ v ih =>
    intro m
    obtain ⟨s₁, hs₁⟩ := copy_step a b u v m
    obtain ⟨s₂, hs₂⟩ := ih (u + 1) (m + 1)
    refine ⟨s₁ + s₂, ?_⟩
    rw [show u + (v + 1) + 1 = u + 1 + v + 1 by omega,
      show m + (v + 1) + 1 = m + 1 + v + 1 by omega]
    exact nSteps_bind_eq hs₁ hs₂

/-- `EN` finds a cell of `N`: it becomes the hole, `S1` runs to `B`, and `EC` makes the cursor. -/
theorem en_step (a c w m : ℕ) :
    ∃ s, nSteps brocard28 s (enCfg a (c + 1) (w + 1) m) = some (copyCfg a c 0 w m) := by
  have h₁ : step brocard28 (enCfg a (c + 1) (w + 1) m) =
      some ⟨5, Tape.mk' ((ones a B0).cons 0)
        (ones c ((ones (w + 1) ((ones m B0).cons 0)).cons 0))⟩ := by
    change step brocard28 ⟨4, Tape.mk' (ones a B0)
      ((ones c ((ones (w + 1) ((ones m B0).cons 0)).cons 0)).cons 1)⟩ = _
    rw [mk'_cons, sEN_1]
  have h₂ := sweepR sS1_1 c ((ones a B0).cons 0) ((ones (w + 1) ((ones m B0).cons 0)).cons 0)
  have h₃ : nSteps brocard28 2 ⟨5, Tape.mk' (ones c ((ones a B0).cons 0))
      ((ones (w + 1) ((ones m B0).cons 0)).cons 0)⟩ = some (copyCfg a c 0 w m) := by
    change nSteps brocard28 2 ⟨5, Tape.mk' (ones c ((ones a B0).cons 0))
      (((ones w ((ones m B0).cons 0)).cons 1).cons 0)⟩ =
      some ⟨6, Tape.mk' (((ones c ((ones a B0).cons 0)).cons 0).cons 0)
        (ones w ((ones m B0).cons 0))⟩
    simp only [mk'_cons, nSteps_succ, sS1_0, nSteps_zero, Option.bind_some, sEC_1]
  exact ⟨_, step_nSteps h₁ (nSteps_bind_eq h₂ h₃)⟩

/-- The hole of `N` walks through the `b` remaining cells, one copy of the template each. -/
theorem en_loop (w : ℕ) : ∀ a b m, ∃ s, nSteps brocard28 s (enCfg a b (w + 1) m) =
    some (enCfg (a + b) 0 (w + 1) (m + b * (w + 1))) := by
  intro a b
  induction b generalizing a with
  | zero => intro m; exact ⟨0, by simp [enCfg]⟩
  | succ c ih =>
    intro m
    obtain ⟨s₁, hs₁⟩ := en_step a c w m
    obtain ⟨s₂, hs₂⟩ := copy_loop a c 0 w m
    obtain ⟨s₃, hs₃⟩ := ih (a + 1) (m + w + 1)
    refine ⟨s₁ + s₂ + s₃, ?_⟩
    rw [show a + (c + 1) = a + 1 + c by omega,
      show m + (c + 1) * (w + 1) = m + w + 1 + c * (w + 1) by ring]
    simp only [Nat.zero_add] at hs₂
    exact nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃

/-- `N` exhausted: `X` merges the template and `M`, `TLs` returns to the start of `B`. -/
theorem en_exit (a V m : ℕ) :
    ∃ s, nSteps brocard28 s (enCfg a 0 V (m + 1)) = some (testCfg a (V + m + 2)) := by
  have h₁ : step brocard28 (enCfg a 0 V (m + 1)) =
      some ⟨11, Tape.mk' ((ones a B0).cons 0) (ones V ((ones (m + 1) B0).cons 0))⟩ := by
    change step brocard28 ⟨4, Tape.mk' (ones a B0)
      ((ones V ((ones (m + 1) B0).cons 0)).cons 0)⟩ = _
    rw [mk'_cons, sEN_0]
  have h₂ := sweepR sX_1 V ((ones a B0).cons 0) ((ones (m + 1) B0).cons 0)
  have h₃ : step brocard28 ⟨11, Tape.mk' (ones V ((ones a B0).cons 0))
      ((ones (m + 1) B0).cons 0)⟩ = some ⟨12, mkL (ones (V + 2) (NL a)) (ones m B0)⟩ := by
    rw [mk'_cons, sX_0]
    change some (⟨12, Tape.mk' ((ones V (NL a)).cons 1) ((ones m B0).cons 1)⟩ : Cfg 28 2) =
      some (⟨12, mkL (((ones V (NL a)).cons 1).cons 1) (ones m B0)⟩ : Cfg 28 2)
    rw [mk'_cons, mkL_cons]
  have h₄ := sweepL sTLs_1 (V + 2) (NL a) (ones m B0)
  have h₅ : step brocard28 ⟨12, mkL (NL a) (ones (V + 2) (ones m B0))⟩ =
      some (testCfg a (V + m + 2)) := by
    rw [NL, mkL_cons, sTLs_0, ← ones_add]
    rw [show V + 2 + m = V + m + 2 by omega]
    rfl
  exact ⟨_, step_nSteps h₁ (nSteps_bind_eq h₂ (step_nSteps h₃ (nSteps_bind_eq h₄
    (step_one h₅))))⟩

/-- `LN1` on the blank left of `N` writes the new cell of `N`, and `EN` reads `N`'s first
cell. -/
theorem ln_exit (n v : ℕ) :
    step brocard28 ⟨3, mkL B0 (ones n ((ones (v + 1) B0).cons 0))⟩ =
      some (enCfg 1 n (v + 1) 0) := by
  rw [mkL_B0, sLN1_0]
  change _ = some (⟨4, Tape.mk' (B0.cons 1)
    (ones n ((ones (v + 1) ((ones 0 B0).cons 0)).cons 0))⟩ : Cfg 28 2)
  rw [ones_zero_B0, B0_cons_zero]

/-- The start of a round: `LN0`/`LN1` write a cell left of `N` and `EN` reads its first cell. -/
theorem round_start (n v : ℕ) :
    ∃ s, nSteps brocard28 s (roundCfg n v) = some (enCfg 1 n (v + 1) 0) := by
  have h₁ : roundCfg n v = ⟨2, mkL (ones (v + 1) (NL n)) B0⟩ := by
    change (⟨2, Tape.mk' (ones v (NL n)) (B0.cons 1)⟩ : Cfg 28 2) =
      ⟨2, mkL ((ones v (NL n)).cons 1) B0⟩
    rw [mk'_cons, mkL_cons]
  have h₂ := sweepL sLN0_1 (v + 1) (NL n) B0
  have h₃ : step brocard28 ⟨2, mkL (NL n) (ones (v + 1) B0)⟩ =
      some ⟨3, mkL (ones n B0) ((ones (v + 1) B0).cons 0)⟩ := by
    rw [NL, mkL_cons, sLN0_0]
  have h₄ := sweepL sLN1_1 n B0 ((ones (v + 1) B0).cons 0)
  rw [h₁]
  exact ⟨_, nSteps_bind_eq h₂ (step_nSteps h₃ (nSteps_bind_eq h₄ (step_one (ln_exit n v))))⟩

/-- From `EN` on the first cell of `N`: `B` with `v + 1` cells becomes `(n + 1) (v + 1) + 1`
cells and the test starts. -/
theorem multiply_en (n v : ℕ) (hn : 1 ≤ n) :
    ∃ s, nSteps brocard28 s (enCfg 1 n (v + 1) 0) =
      some (testCfg (n + 1) ((n + 1) * (v + 1) + 1)) := by
  obtain ⟨s₂, hs₂⟩ := en_loop v 1 n 0
  obtain ⟨m, hm⟩ : ∃ m, 0 + n * (v + 1) = m + 1 := ⟨n * (v + 1) - 1, by
    have : 1 ≤ n * (v + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega⟩
  rw [hm] at hs₂
  obtain ⟨s₃, hs₃⟩ := en_exit (1 + n) (v + 1) m
  refine ⟨s₂ + s₃, ?_⟩
  have e : (n + 1) * (v + 1) + 1 = v + 1 + m + 2 := by
    have : (n + 1) * (v + 1) = v + 1 + n * (v + 1) := by ring
    omega
  rw [show n + 1 = 1 + n by omega] at e ⊢
  rw [e]
  exact nSteps_bind_eq hs₂ hs₃

/-- A whole round: `B` with `v + 1` cells becomes `(n + 1) (v + 1) + 1` cells and `N` grows. -/
theorem multiply (n v : ℕ) (hn : 1 ≤ n) :
    ∃ s, 1 ≤ s ∧ nSteps brocard28 s (roundCfg n v) =
      some (testCfg (n + 1) ((n + 1) * (v + 1) + 1)) := by
  obtain ⟨s₁, hs₁⟩ := round_start n v
  obtain ⟨s₂, hs₂⟩ := multiply_en n v hn
  refine ⟨s₁ + s₂, ?_, nSteps_bind_eq hs₁ hs₂⟩
  have : 1 ≤ s₁ := by
    rcases Nat.eq_zero_or_pos s₁ with rfl | h
    · simp [roundCfg, enCfg] at hs₁
    · exact h
  omega

/-! ## Test and Fail (States `1`, `12`–`22`) -/

/-- `k` zeros followed by `L`. -/
def zeros (k : ℕ) (L : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (List.replicate k 0) L

theorem zeros_succ' (k : ℕ) (L : ListBlank (Fin 2)) : zeros (k + 1) L = zeros k (L.cons 0) := by
  rw [zeros, List.replicate_succ', ListBlank.append_assoc]
  rfl

theorem zeros_B0 (k : ℕ) : zeros k B0 = B0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zeros_succ', B0_cons_zero, ih]

/-- A state that erases ones while moving right. -/
theorem sweepR_erase {q : Fin 28}
    (h : ∀ L R, step brocard28 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 0) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard28 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (zeros k L) R⟩ :=
  Goldbach21.nSteps_mk'_right_scan_of_step h k L R

/-- A state that moves left over zeros. -/
theorem sweepL_zeros {q : Fin 28}
    (h : ∀ L R, step brocard28 ⟨q, ⟨0, L, R⟩⟩ = some ⟨q, mkL L (R.cons 0)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard28 k ⟨q, mkL (zeros k L) R⟩ = some ⟨q, mkL L (zeros k R)⟩ :=
  Goldbach21.nSteps_mkL_left_scan_of_step h k L R

/-- `TR0` right after the hole of `B`, with `r` cells of `B` still to pass. -/
def tCfg (n a r p q : ℕ) : Cfg 28 2 :=
  ⟨13, Tape.mk' ((ones a (NL n)).cons 0) (ones r ((ones p ((ones q B0).cons 0)).cons 0))⟩

theorem t_to_adv (n a r p q : ℕ) :
    nSteps brocard28 r (tCfg n a r p q) = some (advCfg n a r p q) :=
  sweepR sTR0_1 r _ _

/-- The test starts: `TLx` erases the first cell of `B`. -/
theorem test_start (n r : ℕ) :
    ∃ s, nSteps brocard28 s (testCfg n (r + 1)) = some (advCfg n 0 r 0 0) := by
  have h₁ : step brocard28 (testCfg n (r + 1)) = some (tCfg n 0 r 0 0) := by
    change step brocard28 ⟨1, Tape.mk' (NL n) ((ones r B0).cons 1)⟩ =
      some ⟨13, Tape.mk' ((NL n).cons 0) (ones r ((ones 0 ((ones 0 B0).cons 0)).cons 0))⟩
    rw [mk'_cons, sTLx_1, ones_zero_B0, B0_cons_zero, ones_zero_B0,
      B0_cons_zero]
  exact ⟨_, step_nSteps h₁ (t_to_adv n 0 r 0 0)⟩

/-- One unit: the hole of `S` moves one cell left and the hole of `B` one cell right. -/
theorem adv_step (n a r p q : ℕ) :
    ∃ s, nSteps brocard28 s (advCfg n a (r + 1) (p + 1) q) = some (tCfg n (a + 1) r p (q + 1)) := by
  set H := (ones a (NL n)).cons 0 with hH
  set Lr := ones (r + 1) H with hLr
  have h₁ : step brocard28 (advCfg n a (r + 1) (p + 1) q) =
      some ⟨14, Tape.mk' (Lr.cons 0) (ones (p + 1) ((ones q B0).cons 0))⟩ := by
    change step brocard28 ⟨13, Tape.mk' Lr ((ones (p + 1) ((ones q B0).cons 0)).cons 0)⟩ = _
    rw [mk'_cons, sTR0_0]
  have h₂ := sweepR sTR1_1 (p + 1) (Lr.cons 0) ((ones q B0).cons 0)
  have h₃ : nSteps brocard28 2 ⟨14, Tape.mk' (ones (p + 1) (Lr.cons 0)) ((ones q B0).cons 0)⟩ =
      some ⟨17, mkL (ones p (Lr.cons 0)) ((ones (q + 1) B0).cons 0)⟩ := by
    change nSteps brocard28 2 ⟨14, Tape.mk' ((ones p (Lr.cons 0)).cons 1) ((ones q B0).cons 0)⟩ =
      some ⟨17, mkL (ones p (Lr.cons 0)) (((ones q B0).cons 1).cons 0)⟩
    simp only [mk'_cons, nSteps_succ, sTR1_0, mkL_cons, nSteps_zero, Option.bind_some, sSB_1]
  have h₄ := sweepL sTL0_1 p (Lr.cons 0) ((ones (q + 1) B0).cons 0)
  have h₅ : step brocard28 ⟨17, mkL (Lr.cons 0) (ones p ((ones (q + 1) B0).cons 0))⟩ =
      some ⟨18, mkL Lr ((ones p ((ones (q + 1) B0).cons 0)).cons 0)⟩ := by
    rw [mkL_cons, sTL0_0]
  have h₆ := sweepL sTL1_1 (r + 1) H ((ones p ((ones (q + 1) B0).cons 0)).cons 0)
  have h₇ : nSteps brocard28 2
      ⟨18, mkL H (ones (r + 1) ((ones p ((ones (q + 1) B0).cons 0)).cons 0))⟩ =
      some (tCfg n (a + 1) r p (q + 1)) := by
    change nSteps brocard28 2 ⟨18, mkL ((ones a (NL n)).cons 0)
      ((ones r ((ones p ((ones (q + 1) B0).cons 0)).cons 0)).cons 1)⟩ =
      some ⟨13, Tape.mk' (((ones a (NL n)).cons 1).cons 0)
        (ones r ((ones p ((ones (q + 1) B0).cons 0)).cons 0))⟩
    simp only [mkL_cons, nSteps_succ, sTL1_0, mk'_cons, nSteps_zero, Option.bind_some, sTE_1]
  exact ⟨_, step_nSteps h₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ (nSteps_bind_eq h₄
    (step_nSteps h₅ (nSteps_bind_eq h₆ h₇)))))⟩

/-- `p` units in a row, while `B` has enough cells. -/
theorem adv_many (n : ℕ) : ∀ p a r p' q, ∃ s, nSteps brocard28 s (advCfg n a (r + p) (p + p') q) =
    some (advCfg n (a + p) r p' (q + p)) := by
  intro p
  induction p with
  | zero => intro a r p' q; exact ⟨0, by simp⟩
  | succ p ih =>
    intro a r p' q
    obtain ⟨s₁, hs₁⟩ := adv_step n a (r + p) (p + p') q
    have h₂ := t_to_adv n (a + 1) (r + p) (p + p') (q + 1)
    obtain ⟨s₃, hs₃⟩ := ih (a + 1) r p' (q + 1)
    refine ⟨s₁ + (r + p) + s₃, ?_⟩
    rw [show r + (p + 1) = r + p + 1 by omega, show p + 1 + p' = p + p' + 1 by omega,
      show a + (p + 1) = a + 1 + p by omega, show q + (p + 1) = q + 1 + p by omega]
    exact nSteps_bind_eq (nSteps_bind_eq hs₁ h₂) hs₃

/-- The wrap: the hole of `S` is at its first cell, `B` has cells left; `S` becomes solid with
one more cell and the next chunk starts. -/
theorem adv_wrap (n a r q : ℕ) :
    nSteps brocard28 4 (advCfg n a (r + 1) 0 q) = some (advCfg n a (r + 1) (q + 1) 0) := by
  rw [advCfg_solid]
  change nSteps brocard28 4 ⟨13, Tape.mk' ((ones r ((ones a (NL n)).cons 0)).cons 1)
      (((ones q B0).cons 0).cons 0)⟩ =
    some ⟨13, Tape.mk' ((ones r ((ones a (NL n)).cons 0)).cons 1)
      ((((ones q B0).cons 1).cons 0))⟩
  simp only [mk'_cons, nSteps_succ, sTR0_0, nSteps_zero, Option.bind_some, sTR1_0, mkL_cons,
    sSB_0, sSC_1]

/-- The wrap with `B` exhausted: success, `M0` starts the gate on the last cell of `B`. -/
theorem adv_success (n a q : ℕ) :
    nSteps brocard28 4 (advCfg n a 0 0 q) =
      some ⟨23, mkL (ones a (NL n)) (((ones (q + 1) B0).cons 0).cons 0)⟩ := by
  change nSteps brocard28 4 ⟨13, Tape.mk' ((ones a (NL n)).cons 0) (((ones q B0).cons 0).cons 0)⟩ =
    some ⟨23, mkL (ones a (NL n)) ((((ones q B0).cons 1).cons 0).cons 0)⟩
  simp only [mk'_cons, nSteps_succ, sTR0_0, nSteps_zero, Option.bind_some, sTR1_0, mkL_cons,
    sSB_0, sSC_0]

/-- A unit with `B` exhausted: `TE` finds the separator, `ER`/`ER2` erase `S`, `ER3` returns,
erasing the last cell of `B`, and the next round starts. -/
theorem adv_fail (n a p q : ℕ) :
    ∃ s, nSteps brocard28 s (advCfg n (a + 1) 0 (p + 1) q) = some (roundCfg n a) := by
  set H := (ones (a + 1) (NL n)).cons 0 with hH
  have h₁ : step brocard28 (advCfg n (a + 1) 0 (p + 1) q) =
      some ⟨14, Tape.mk' (H.cons 0) (ones (p + 1) ((ones q B0).cons 0))⟩ := by
    change step brocard28 ⟨13, Tape.mk' H ((ones (p + 1) ((ones q B0).cons 0)).cons 0)⟩ = _
    rw [mk'_cons, sTR0_0]
  have h₂ := sweepR sTR1_1 (p + 1) (H.cons 0) ((ones q B0).cons 0)
  have h₃ : nSteps brocard28 2 ⟨14, Tape.mk' (ones (p + 1) (H.cons 0)) ((ones q B0).cons 0)⟩ =
      some ⟨17, mkL (ones p (H.cons 0)) ((ones (q + 1) B0).cons 0)⟩ := by
    change nSteps brocard28 2 ⟨14, Tape.mk' ((ones p (H.cons 0)).cons 1) ((ones q B0).cons 0)⟩ =
      some ⟨17, mkL (ones p (H.cons 0)) (((ones q B0).cons 1).cons 0)⟩
    simp only [mk'_cons, nSteps_succ, sTR1_0, mkL_cons, nSteps_zero, Option.bind_some, sSB_1]
  have h₄ := sweepL sTL0_1 p (H.cons 0) ((ones (q + 1) B0).cons 0)
  have h₅ : nSteps brocard28 3 ⟨17, mkL (H.cons 0) (ones p ((ones (q + 1) B0).cons 0))⟩ =
      some ⟨20, Tape.mk' (((ones (a + 1) (NL n)).cons 1).cons 0)
        (ones p ((ones (q + 1) B0).cons 0))⟩ := by
    rw [hH]
    simp only [mkL_cons, nSteps_succ, sTL0_0, nSteps_zero, Option.bind_some, sTL1_0, mk'_cons,
      sTE_0]
  have h₆ := sweepR_erase sER_1 p (((ones (a + 1) (NL n)).cons 1).cons 0) ((ones (q + 1) B0).cons 0)
  set W := ((ones (a + 1) (NL n)).cons 1).cons 0 with hW
  have h₇ : step brocard28 ⟨20, Tape.mk' (zeros p W) ((ones (q + 1) B0).cons 0)⟩ =
      some ⟨21, Tape.mk' ((zeros p W).cons 0) (ones (q + 1) B0)⟩ := by
    rw [mk'_cons, sER_0]
  have h₈ := sweepR_erase sER2_1 (q + 1) ((zeros p W).cons 0) B0
  have h₉ : step brocard28 ⟨21, Tape.mk' (zeros (q + 1) ((zeros p W).cons 0)) B0⟩ =
      some ⟨22, mkL (zeros (q + 1) ((zeros p W).cons 0)) B0⟩ := by
    rw [mkRight_blank, sER2_0, B0_cons_zero]
  have h₁₀ := sweepL_zeros sER3_0 (q + 1) ((zeros p W).cons 0) B0
  rw [zeros_B0] at h₁₀
  have h₁₁ : step brocard28 ⟨22, mkL ((zeros p W).cons 0) B0⟩ = some ⟨22, mkL (zeros p W) B0⟩ := by
    rw [mkL_cons, sER3_0, B0_cons_zero]
  have h₁₂ := sweepL_zeros sER3_0 p W B0
  rw [zeros_B0] at h₁₂
  have h₁₃ : nSteps brocard28 2 ⟨22, mkL W B0⟩ = some (roundCfg n a) := by
    rw [hW]
    change nSteps brocard28 2 ⟨22, mkL ((((ones a (NL n)).cons 1).cons 1).cons 0) B0⟩ =
      some ⟨2, Tape.mk' (ones a (NL n)) (B0.cons 1)⟩
    simp only [mkL_cons, nSteps_succ, sER3_0, B0_cons_zero, nSteps_zero, Option.bind_some, sER3_1,
      mk'_cons]
  exact ⟨_, step_nSteps h₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ (nSteps_bind_eq h₄
    (nSteps_bind_eq h₅ (nSteps_bind_eq h₆ (step_nSteps h₇ (nSteps_bind_eq h₈ (step_nSteps h₉
    (nSteps_bind_eq h₁₀ (step_nSteps h₁₁ (nSteps_bind_eq h₁₂ h₁₃)))))))))))⟩

/-! ## Triangular Numbers and the Chunk Loop -/

/-- `pre s = 0 + 1 + ⋯ + (s - 1)`: the cells of `B` consumed before the chunk of size `s`. -/
def pre : ℕ → ℕ
  | 0 => 0
  | s + 1 => pre s + s

/-- `tri k = 1 + 2 + ⋯ + k`. -/
def tri (k : ℕ) : ℕ := pre (k + 1)

theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := rfl

theorem tri_strictMono : StrictMono tri :=
  strictMono_nat_of_lt_succ fun k => by rw [tri_succ]; omega

theorem tri_eq_iff (j k : ℕ) : tri j = tri k ↔ j = k := tri_strictMono.injective.eq_iff

/-- Nothing strictly between two consecutive triangular numbers is triangular. -/
theorem not_tri_between {k x : ℕ} (h₁ : tri k < x) (h₂ : x < tri (k + 1)) : ¬ ∃ j, x = tri j := by
  rintro ⟨j, rfl⟩
  have := tri_strictMono.lt_iff_lt.mp h₁
  have := tri_strictMono.lt_iff_lt.mp h₂
  omega

/-- The success configuration: `M0` on the last cell of `B` (`a` ones, the hole after them),
`S` solid with `S` cells. -/
def succCfg (n a S : ℕ) : Cfg 28 2 :=
  ⟨23, mkL (ones a (NL n)) (((ones S B0).cons 0).cons 0)⟩

/-- From the start of the chunk of size `s ≥ 1` with `r + 1` cells of `B` left: success if the
cells of `B` form a triangular number, otherwise the next round. -/
theorem chunk_loop (n : ℕ) : ∀ r s a, 1 ≤ s → a = pre s →
    (∃ j, a + r + 1 = tri j ∧ ∃ t, nSteps brocard28 t (advCfg n a (r + 1) s 0) =
      some (succCfg n (a + r + 1) (j + 1))) ∨
    ((¬ ∃ j, a + r + 1 = tri j) ∧ ∃ t, nSteps brocard28 t (advCfg n a (r + 1) s 0) =
      some (roundCfg n (a + r))) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s a hs ha
  rcases Nat.lt_or_ge (r + 1) s with hlt | hge
  · -- not enough cells: fail inside this chunk
    obtain ⟨p', hp'⟩ : ∃ p', s = r + 1 + (p' + 1) := ⟨s - r - 2, by omega⟩
    obtain ⟨t₁, ht₁⟩ := adv_many n (r + 1) a 0 (p' + 1) 0
    rw [Nat.zero_add, ← hp', show a + (r + 1) = a + r + 1 by omega] at ht₁
    obtain ⟨t₂, ht₂⟩ := adv_fail n (a + r) p' (r + 1)
    refine Or.inr ⟨?_, t₁ + t₂, nSteps_bind_eq ht₁ ht₂⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have e1 : tri s' = pre s' + s' := rfl
    have e2 : tri (s' + 1) = pre s' + s' + (s' + 1) := rfl
    have e3 : pre (s' + 1) = pre s' + s' := rfl
    have h1 : tri s' < a + r + 1 := by omega
    have h2 : a + r + 1 < tri (s' + 1) := by omega
    exact not_tri_between h1 h2
  · -- the whole chunk fits
    obtain ⟨r', hr'⟩ : ∃ r', r + 1 = r' + s := ⟨r + 1 - s, by omega⟩
    obtain ⟨t₁, ht₁⟩ := adv_many n s a r' 0 0
    rw [Nat.zero_add, Nat.add_zero, ← hr'] at ht₁
    rcases Nat.eq_zero_or_pos r' with rfl | hr'pos
    · -- exhausted exactly at the wrap: success
      have ht₂ := adv_success n (a + s) s
      refine Or.inl ⟨s, ?_, t₁ + 4, ?_⟩
      · rw [tri, pre, ha]; omega
      · rw [show a + r + 1 = a + s by omega]
        exact nSteps_bind_eq ht₁ ht₂
    · obtain ⟨r'', rfl⟩ : ∃ r'', r' = r'' + 1 := ⟨r' - 1, by omega⟩
      have ht₂ := adv_wrap n (a + s) r'' s
      obtain ⟨j, hj, t₃, ht₃⟩ | ⟨hj, t₃, ht₃⟩ :=
        ih r'' (by omega) (s + 1) (a + s) (by omega) (by rw [ha]; rfl)
      · refine Or.inl ⟨j, ?_, t₁ + 4 + t₃, ?_⟩
        · rw [← hj]; omega
        · rw [show a + r + 1 = a + s + r'' + 1 by omega]
          exact nSteps_bind_eq (nSteps_bind_eq ht₁ ht₂) ht₃
      · refine Or.inr ⟨?_, t₁ + 4 + t₃, ?_⟩
        · rw [show a + r + 1 = a + s + r'' + 1 by omega]; exact hj
        · rw [show a + r = a + s + r'' by omega]
          exact nSteps_bind_eq (nSteps_bind_eq ht₁ ht₂) ht₃

/-- The test of `B` with `M + 1` cells: the first cell is consumed; if `M` is triangular the
machine reaches the success configuration, otherwise the next round with `M` cells. -/
theorem test_run (n M : ℕ) :
    (∃ j, M = tri j ∧ ∃ t, nSteps brocard28 t (testCfg n (M + 1)) =
      some (succCfg n M (j + 1))) ∨
    ((¬ ∃ j, M = tri j) ∧ ∃ t, nSteps brocard28 t (testCfg n (M + 1)) =
      some (roundCfg n (M - 1))) := by
  obtain ⟨t₀, ht₀⟩ := test_start n M
  cases M with
  | zero =>
    exact Or.inl ⟨0, rfl, t₀ + 4, nSteps_bind_eq ht₀ (adv_success n 0 0)⟩
  | succ r =>
    have ht₁ := adv_wrap n 0 r 0
    obtain ⟨j, hj, t, ht⟩ | ⟨hj, t, ht⟩ := chunk_loop n r 1 0 le_rfl rfl
    · simp only [Nat.zero_add] at hj ht
      exact Or.inl ⟨j, hj, t₀ + 4 + t, nSteps_bind_eq (nSteps_bind_eq ht₀ ht₁) ht⟩
    · simp only [Nat.zero_add] at hj ht
      rw [Nat.add_sub_cancel]
      exact Or.inr ⟨hj, t₀ + 4 + t, nSteps_bind_eq (nSteps_bind_eq ht₀ ht₁) ht⟩

/-! ## Gate (States `23`–`27`) and Start (State `0`) -/

/-- `M0`–`M3` count the ones of `B` modulo `4` walking left: four ones return to `M0`. -/
theorem gate_four (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard28 4 ⟨23, mkL (ones (k + 4) L) R⟩ = some ⟨23, mkL (ones k L) (ones 4 R)⟩ := by
  change nSteps brocard28 4 ⟨23, mkL (((((ones k L).cons 1).cons 1).cons 1).cons 1) R⟩ =
    some ⟨23, mkL (ones k L) ((((R.cons 1).cons 1).cons 1).cons 1)⟩
  simp only [mkL_cons, nSteps_succ, sM0_1, nSteps_zero, Option.bind_some, sM1_1, sM2_1, sM3_1]

/-- `4 j` ones of `B` bring `M0` back to `M0`. -/
theorem gate_mult (j : ℕ) : ∀ (k : ℕ) (L R : ListBlank (Fin 2)),
    nSteps brocard28 (4 * j) ⟨23, mkL (ones (4 * j + k) L) R⟩ =
      some ⟨23, mkL (ones k L) (ones (4 * j) R)⟩ := by
  induction j with
  | zero => intro k L R; simp only [Nat.mul_zero, Nat.zero_add, ones_zero]; rfl
  | succ j ih =>
    intro k L R
    have h₁ : nSteps brocard28 4 ⟨23, mkL (ones (4 * (j + 1) + k) L) R⟩ =
        some ⟨23, mkL (ones (4 * j + k) L) (ones 4 R)⟩ := by
      rw [show 4 * (j + 1) + k = 4 * j + k + 4 by omega]; exact gate_four _ L R
    have := nSteps_bind_eq h₁ (ih k L (ones 4 R))
    rwa [← ones_add, show 4 * j + 4 = 4 * (j + 1) by omega,
      show 4 + 4 * j = 4 * (j + 1) by omega] at this

/-- Residue `0`: `M0` reaches the separator and halts (`M0` reading `0` is undefined). -/
theorem gate_halt (n j : ℕ) (Y : ListBlank (Fin 2)) :
    ∃ cfg, nSteps brocard28 (4 * j) ⟨23, mkL (ones (4 * j) (NL n)) Y⟩ = some cfg ∧
      step brocard28 cfg = none := by
  refine ⟨⟨23, mkL (NL n) (ones (4 * j) Y)⟩, ?_, ?_⟩
  · have := gate_mult j 0 (NL n) Y
    rwa [Nat.add_zero, ones_zero] at this
  · rw [NL, mkL_cons, sM0_0]

/-- Residue `2`: `M2` reads the separator and steps right into `Bs`. -/
theorem gate_two (n j : ℕ) (Y : ListBlank (Fin 2)) :
    nSteps brocard28 (4 * j + 3) ⟨23, mkL (ones (4 * j + 2) (NL n)) Y⟩ =
      some ⟨27, Tape.mk' (NL n) (ones (4 * j + 2) Y)⟩ := by
  have h₁ := gate_mult j 2 (NL n) Y
  have h₂ : nSteps brocard28 3 ⟨23, mkL (ones 2 (NL n)) (ones (4 * j) Y)⟩ =
      some ⟨27, Tape.mk' (NL n) (ones (4 * j + 2) Y)⟩ := by
    change nSteps brocard28 3 ⟨23, mkL ((((ones n B0).cons 0).cons 1).cons 1) (ones (4 * j) Y)⟩ =
      some ⟨27, Tape.mk' ((ones n B0).cons 0) (((ones (4 * j) Y).cons 1).cons 1)⟩
    simp only [mkL_cons, nSteps_succ, sM0_1, nSteps_zero, Option.bind_some, sM1_1, sM2_0,
      mk'_cons]
  exact nSteps_bind_eq h₁ h₂

/-- Residue `3`: `M3` reads the separator and steps right into `Bs`. -/
theorem gate_three (n j : ℕ) (Y : ListBlank (Fin 2)) :
    nSteps brocard28 (4 * j + 4) ⟨23, mkL (ones (4 * j + 3) (NL n)) Y⟩ =
      some ⟨27, Tape.mk' (NL n) (ones (4 * j + 3) Y)⟩ := by
  have h₁ := gate_mult j 3 (NL n) Y
  have h₂ : nSteps brocard28 4 ⟨23, mkL (ones 3 (NL n)) (ones (4 * j) Y)⟩ =
      some ⟨27, Tape.mk' (NL n) (ones (4 * j + 3) Y)⟩ := by
    change nSteps brocard28 4
      ⟨23, mkL (((((ones n B0).cons 0).cons 1).cons 1).cons 1) (ones (4 * j) Y)⟩ =
      some ⟨27, Tape.mk' ((ones n B0).cons 0) ((((ones (4 * j) Y).cons 1).cons 1).cons 1)⟩
    simp only [mkL_cons, nSteps_succ, sM0_1, nSteps_zero, Option.bind_some, sM1_1, sM2_1, sM3_0,
      mk'_cons]
  exact nSteps_bind_eq h₁ h₂

/-- After a suppressed success, `Bs` returns over `B` and fills its hole, `ER`/`ER2` erase the
solid `S`, and `ER3` erases the last cell of `B`: the next round. -/
theorem gate_back (n a S : ℕ) :
    ∃ s, nSteps brocard28 s
      ⟨27, Tape.mk' (NL n) (ones (a + 1) (((ones S B0).cons 0).cons 0))⟩ =
      some (roundCfg n a) := by
  set R := ((ones S B0).cons 0).cons 0 with hR
  have h₃ := sweepR sBs_1 (a + 1) (NL n) R
  have h₄ : nSteps brocard28 2 ⟨27, Tape.mk' (ones (a + 1) (NL n)) R⟩ =
      some ⟨21, Tape.mk' (((ones (a + 1) (NL n)).cons 1).cons 0) (ones S B0)⟩ := by
    rw [hR]
    simp only [mk'_cons, nSteps_succ, sBs_0, nSteps_zero, Option.bind_some, sER_0]
  set W := ((ones (a + 1) (NL n)).cons 1).cons 0 with hW
  have h₅ := sweepR_erase sER2_1 S W B0
  have h₆ : step brocard28 ⟨21, Tape.mk' (zeros S W) B0⟩ = some ⟨22, mkL (zeros S W) B0⟩ := by
    rw [mkRight_blank, sER2_0, B0_cons_zero]
  have h₇ := sweepL_zeros sER3_0 S W B0
  rw [zeros_B0] at h₇
  have h₈ : nSteps brocard28 2 ⟨22, mkL W B0⟩ = some (roundCfg n a) := by
    rw [hW]
    change nSteps brocard28 2 ⟨22, mkL ((((ones a (NL n)).cons 1).cons 1).cons 0) B0⟩ =
      some ⟨2, Tape.mk' (ones a (NL n)) (B0.cons 1)⟩
    simp only [mkL_cons, nSteps_succ, sER3_0, B0_cons_zero, nSteps_zero, Option.bind_some, sER3_1,
      mk'_cons]
  exact ⟨_, nSteps_bind_eq h₃ (nSteps_bind_eq h₄ (nSteps_bind_eq h₅ (step_nSteps h₆
    (nSteps_bind_eq h₇ h₈))))⟩

/-- A success whose `B` has `a + 1 ≡ 2` or `3 (mod 4)` ones is suppressed: the next round
starts. -/
theorem gate_suppressed (n a S : ℕ) (h : (a + 1) % 4 = 2 ∨ (a + 1) % 4 = 3) :
    ∃ s, nSteps brocard28 s (succCfg n (a + 1) S) = some (roundCfg n a) := by
  obtain ⟨s₃, hs₃⟩ := gate_back n a S
  rcases h with h | h
  · have h₂ := gate_two n ((a + 1) / 4) (((ones S B0).cons 0).cons 0)
    rw [show 4 * ((a + 1) / 4) + 2 = a + 1 by omega] at h₂
    exact ⟨_, nSteps_bind_eq h₂ hs₃⟩
  · have h₂ := gate_three n ((a + 1) / 4) (((ones S B0).cons 0).cons 0)
    rw [show 4 * ((a + 1) / 4) + 3 = a + 1 by omega] at h₂
    exact ⟨_, nSteps_bind_eq h₂ hs₃⟩

/-- A success whose `B` has `a + 1 ≡ 0 (mod 4)` ones halts. -/
theorem gate_live (n a S : ℕ) (h : (a + 1) % 4 = 0) :
    ∃ s cfg, nSteps brocard28 s (succCfg n (a + 1) S) = some cfg ∧
      step brocard28 cfg = none := by
  obtain ⟨cfg, h₁, hnone⟩ := gate_halt n ((a + 1) / 4) (((ones S B0).cons 0).cons 0)
  rw [show 4 * ((a + 1) / 4) = a + 1 by omega] at h₁
  exact ⟨_, cfg, h₁, hnone⟩

theorem init_eq : (init : Cfg 28 2) = ⟨0, Tape.mk' B0 B0⟩ := rfl

/-- Start, steps `1`–`12`: `GO`, `EC`, `LN0`, `LN1`, `EN`, `X` write `1 0 1 1`; `TLs`, `TLx`,
`TR0` turn it into `1 0 0 1` and move on. -/
theorem seed₁ : nSteps brocard28 12 ⟨0, Tape.mk' B0 B0⟩ =
    some ⟨14, Tape.mk' (((((B0.cons 1).cons 0).cons 0).cons 1).cons 0) B0⟩ := by
  rfl

/-- Start, steps `13`–`24`: one chunk of the test runs on `1 0 0 1`. -/
theorem seed₂ : nSteps brocard28 12
    ⟨14, Tape.mk' (((((B0.cons 1).cons 0).cons 0).cons 1).cons 0) B0⟩ =
    some ⟨14, Tape.mk' (((((B0.cons 1).cons 0).cons 1).cons 0).cons 0) ((B0.cons 1).cons 0)⟩ := by
  rfl

/-- Start, steps `25`–`36`: `TR1`, `SB`, `SC` end the chunk as a success; `M0`, `M1` reading `0`,
`GO`, `LN1`, `EN`, `X` write `1111 0 111`; `TLs` reading `0` enters `TLx`. -/
theorem seed₃ : nSteps brocard28 12
    ⟨14, Tape.mk' (((((B0.cons 1).cons 0).cons 1).cons 0).cons 0) ((B0.cons 1).cons 0)⟩ =
    some ⟨1, Tape.mk' (ListBlank.cons 0
      ((((((((B0.cons 1).cons 1).cons 1).cons 1).cons 0).cons 1).cons 1).cons 1)) B0⟩ := by
  rfl

/-- Start, steps `37`–`46`: `TLx` reading `0`, `EC`, `LN0`, `LN1` walk left to the blank left of
`N`. -/
theorem seed₄ : nSteps brocard28 10
    ⟨1, Tape.mk' (ListBlank.cons 0
      ((((((((B0.cons 1).cons 1).cons 1).cons 1).cons 0).cons 1).cons 1).cons 1)) B0⟩ =
    some ⟨3, mkL B0 (ones 4 ((ones 3 B0).cons 0))⟩ := by
  -- The computed right half includes two trailing blanks.
  have run : nSteps brocard28 10
      ⟨1, Tape.mk' (ListBlank.mk [0, 1, 1, 1, 0, 1, 1, 1, 1]) B0⟩ =
      some ⟨3, ⟨0, B0, ListBlank.mk ([1, 1, 1, 1, 0, 1, 1, 1] ++ List.replicate 2 0)⟩⟩ := rfl
  change nSteps brocard28 10 ⟨1, Tape.mk' (ListBlank.mk [0, 1, 1, 1, 0, 1, 1, 1, 1]) B0⟩ = _
  rw [run, Goldbach21.mk_append_replicate_zero]
  rfl

/-- The start writes `1111 0 111` in `46` steps and ends in `LN1` on the blank left of `N`, the
configuration every round passes through (`ln_exit`). -/
theorem seed : nSteps brocard28 46 init = some ⟨3, mkL B0 (ones 4 ((ones 3 B0).cons 0))⟩ := by
  rw [init_eq]
  exact nSteps_bind_eq seed₁ (nSteps_bind_eq seed₂ (nSteps_bind_eq seed₃ seed₄))

/-! ## Stages -/

/-- `V n = n! / 8`, the number of cells of `B` between rounds. -/
def V (n : ℕ) : ℕ := n.factorial / 8

theorem eight_dvd_factorial {n : ℕ} (hn : 4 ≤ n) : 8 ∣ n.factorial :=
  Nat.dvd_trans (by decide : 8 ∣ Nat.factorial 4) (Nat.factorial_dvd_factorial hn)

theorem V_succ {n : ℕ} (hn : 4 ≤ n) : V (n + 1) = (n + 1) * V n := by
  rw [V, V, Nat.factorial_succ, Nat.mul_div_assoc _ (eight_dvd_factorial hn)]

theorem V_pos {n : ℕ} (hn : 4 ≤ n) : 1 ≤ V n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [V_succ hn]; exact le_trans ih (Nat.le_mul_of_pos_left _ (by omega))

/-- For `n ≥ 8`, `32 ∣ n!`, so `4 ∣ n! / 8`: the gate halts on every success with `n ≥ 8`. -/
theorem V_mod_four {n : ℕ} (hn : 8 ≤ n) : V n % 4 = 0 := by
  obtain ⟨t, ht⟩ :=
    Nat.dvd_trans (by decide : 32 ∣ Nat.factorial 8) (Nat.factorial_dvd_factorial hn)
  rw [V, ht]; omega

/-- `x` is a triangular number `1 + 2 + ⋯ + j`. -/
def IsTri (x : ℕ) : Prop := ∃ j, x = tri j

theorem le_tri (j : ℕ) : j ≤ tri j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => rw [tri_succ]; omega

theorem isTri_iff (x : ℕ) : IsTri x ↔ ∃ j < x + 1, x = tri j :=
  ⟨fun ⟨j, h⟩ => ⟨j, by have := le_tri j; omega, h⟩, fun ⟨j, _, h⟩ => ⟨j, h⟩⟩

instance : DecidablePred IsTri := fun x => decidable_of_iff _ (isTri_iff x).symm

/-- The configuration at the start of the round that multiplies by `n + 1`. -/
def stage (n : ℕ) : Cfg 28 2 := roundCfg n (V n - 1)

theorem stage_to_test {n : ℕ} (hn : 4 ≤ n) :
    ∃ s, 1 ≤ s ∧ nSteps brocard28 s (stage n) = some (testCfg (n + 1) (V (n + 1) + 1)) := by
  obtain ⟨s, hs1, hs⟩ := multiply n (V n - 1) (by omega)
  have := V_pos hn
  rw [show V n - 1 + 1 = V n by omega, ← V_succ hn] at hs
  exact ⟨s, hs1, hs⟩

/-- A round whose test fails. -/
theorem stage_fail {n : ℕ} (hn : 4 ≤ n) (h : ¬ IsTri (V (n + 1))) :
    ∃ s, 1 ≤ s ∧ nSteps brocard28 s (stage n) = some (stage (n + 1)) := by
  obtain ⟨s₁, hs₁1, hs₁⟩ := stage_to_test hn
  rcases test_run (n + 1) (V (n + 1)) with ⟨j, hj, -⟩ | ⟨-, s₂, hs₂⟩
  · exact absurd ⟨j, hj⟩ h
  · exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- A round whose test succeeds with `n + 1 = 5` (`V 5 = 15 ≡ 3`) or `n + 1 = 7`
(`V 7 = 630 ≡ 2 (mod 4)`): suppressed. -/
theorem stage_suppressed {n : ℕ} (hn : 4 ≤ n) (h : IsTri (V (n + 1)))
    (h57 : n + 1 = 5 ∨ n + 1 = 7) :
    ∃ s, 1 ≤ s ∧ nSteps brocard28 s (stage n) = some (stage (n + 1)) := by
  obtain ⟨s₁, hs₁1, hs₁⟩ := stage_to_test hn
  rcases test_run (n + 1) (V (n + 1)) with ⟨j, -, s₂, hs₂⟩ | ⟨h', -⟩
  · have hV := V_pos (show 4 ≤ n + 1 by omega)
    obtain ⟨a, ha⟩ : ∃ a, V (n + 1) = a + 1 := ⟨V (n + 1) - 1, by omega⟩
    have hres : (a + 1) % 4 = 2 ∨ (a + 1) % 4 = 3 := by
      rw [← ha]
      rcases h57 with h5 | h7
      · right; rw [h5]; decide
      · left; rw [h7]; decide
    rw [ha] at hs₁ hs₂
    obtain ⟨s₃, hs₃⟩ := gate_suppressed (n + 1) a (j + 1) hres
    refine ⟨s₁ + s₂ + s₃, by omega, ?_⟩
    change nSteps brocard28 (s₁ + s₂ + s₃) (stage n) = some (roundCfg (n + 1) (V (n + 1) - 1))
    rw [ha, Nat.add_sub_cancel]
    exact nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃
  · exact absurd h h'

/-- A round whose test succeeds with `n + 1 ≥ 8` halts. -/
theorem stage_halt {n : ℕ} (hn : 7 ≤ n) (h : IsTri (V (n + 1))) :
    ∃ s cfg, nSteps brocard28 s (stage n) = some cfg ∧ step brocard28 cfg = none := by
  obtain ⟨s₁, -, hs₁⟩ := stage_to_test (show 4 ≤ n by omega)
  rcases test_run (n + 1) (V (n + 1)) with ⟨j, -, s₂, hs₂⟩ | ⟨h', -⟩
  · have hV := V_pos (show 4 ≤ n + 1 by omega)
    obtain ⟨a, ha⟩ : ∃ a, V (n + 1) = a + 1 := ⟨V (n + 1) - 1, by omega⟩
    have hres : (a + 1) % 4 = 0 := by rw [← ha]; exact V_mod_four (by omega)
    rw [ha] at hs₁ hs₂
    obtain ⟨s₃, cfg, hs₃, hnone⟩ := gate_live (n + 1) a (j + 1) hres
    exact ⟨s₁ + s₂ + s₃, cfg, nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃, hnone⟩
  · exact absurd h h'

theorem isTri_V5 : IsTri (V 5) := ⟨5, by decide⟩

theorem not_isTri_V6 : ¬ IsTri (V 6) :=
  not_tri_between (k := 12) (by decide) (by decide)

theorem isTri_V7 : IsTri (V 7) := ⟨35, by decide⟩

/-- The start reaches the beginning of round `5`: `46` steps write `1111 0 111`, the first
round multiplies by `5`, its test finds `15 = tri 5`, and the gate suppresses the success
(`15 ≡ 3 (mod 4)`). -/
theorem seed_stage : ∃ s, 5 ≤ s ∧ nSteps brocard28 s init = some (stage 5) := by
  obtain ⟨s₃, hs₃⟩ := multiply_en 4 2 (by omega)
  rcases test_run 5 15 with ⟨j, -, s₄, hs₄⟩ | ⟨h, -⟩
  · obtain ⟨s₅, hs₅⟩ := gate_suppressed 5 14 (j + 1) (Or.inr rfl)
    refine ⟨46 + 1 + s₃ + s₄ + s₅, by omega, ?_⟩
    have hV : V 5 - 1 = 14 := by decide
    rw [stage, hV]
    exact nSteps_bind_eq (nSteps_bind_eq (nSteps_bind_eq (nSteps_bind_eq seed
      (step_one (ln_exit 4 2))) hs₃) hs₄) hs₅
  · exact absurd isTri_V5 h

/-- No counterexample with `8 ≤ m ≤ K`. -/
def Clear (K : ℕ) : Prop := ∀ m, 8 ≤ m → m ≤ K → ¬ IsTri (V m)

theorem clear_or_witness (K : ℕ) : Clear K ∨ ∃ m, 8 ≤ m ∧ m ≤ K ∧ IsTri (V m) := by
  induction K with
  | zero => exact Or.inl fun m h8 h0 => absurd (le_trans h8 h0) (by decide)
  | succ K ih =>
    rcases ih with hc | ⟨m, hm8, hmK, hm⟩
    · by_cases hK : 8 ≤ K + 1
      · by_cases ht : IsTri (V (K + 1))
        · exact Or.inr ⟨K + 1, hK, le_rfl, ht⟩
        · refine Or.inl fun m h8 hK1 => ?_
          rcases Nat.lt_or_ge m (K + 1) with h | h
          · exact hc m h8 (by omega)
          · rw [show m = K + 1 by omega]; exact ht
      · exact Or.inl fun m h8 hK1 => absurd (le_trans h8 hK1) hK
    · exact Or.inr ⟨m, hm8, by omega, hm⟩

/-- Without a counterexample up to `n`, the machine reaches the start of round `n` in at least
`n` steps. -/
theorem reach (n : ℕ) (hn : 5 ≤ n) (hc : Clear n) :
    ∃ s, n ≤ s ∧ nSteps brocard28 s init = some (stage n) := by
  induction n, hn using Nat.le_induction with
  | base => exact seed_stage
  | succ n hn ih =>
    obtain ⟨s₁, hs₁n, hs₁⟩ := ih fun m h8 hm => hc m h8 (by omega)
    have step : ∃ s, 1 ≤ s ∧ nSteps brocard28 s (stage n) = some (stage (n + 1)) := by
      rcases Nat.lt_or_ge (n + 1) 8 with h | h
      · obtain rfl | rfl : n = 5 ∨ n = 6 := by omega
        · exact stage_fail (by omega) not_isTri_V6
        · exact stage_suppressed (by omega) isTri_V7 (Or.inr rfl)
      · exact stage_fail (by omega) (hc (n + 1) h le_rfl)
    obtain ⟨s₂, hs₂1, hs₂⟩ := step
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- The first counterexample halts the machine. -/
theorem halt_of (m : ℕ) (hm : 8 ≤ m) (h : IsTri (V m)) (hc : Clear (m - 1)) :
    ∃ s cfg, nSteps brocard28 s init = some cfg ∧ step brocard28 cfg = none := by
  obtain ⟨s₁, -, hs₁⟩ := reach (m - 1) (by omega) hc
  obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_halt (n := m - 1) (by omega)
    (by rw [show m - 1 + 1 = m by omega]; exact h)
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-- The least counterexample has none below it. -/
theorem first_witness (n : ℕ) : 8 ≤ n → IsTri (V n) →
    ∃ m, 8 ≤ m ∧ IsTri (V m) ∧ Clear (m - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h8 hn
  rcases clear_or_witness (n - 1) with hc | ⟨m, hm8, hmn, hm⟩
  · exact ⟨n, h8, hn, hc⟩
  · exact ih m (by omega) hm8 hm

/-! ## Halting Equivalence -/

/-- The 28-state machine `brocard28` (`brocard_28`) halts on the blank tape if and only if
`n! / 8` is a triangular number for some `n ≥ 8`. -/
theorem halts_brocard28_iff_exists_tri :
    ConjectureMachines.Halts brocard28 ↔ ∃ n, 8 ≤ n ∧ IsTri (V n) := by
  unfold ConjectureMachines.Halts
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases clear_or_witness (k + 8) with hc | ⟨m, hm8, -, hm⟩
    · obtain ⟨s, hks, hs⟩ := reach (k + 8) (by omega) hc
      rw [nSteps_eq_none_of_step_none s hk hnone (by omega)] at hs
      cases hs
    · exact ⟨m, hm8, hm⟩
  · rintro ⟨n, h8, hn⟩
    obtain ⟨m, hm8, hm, hc⟩ := first_witness n h8 hn
    obtain ⟨s, cfg, hs, hnone⟩ := halt_of m hm8 hm hc
    rw [Part.dom_iff_mem]
    exact ⟨cfg, mem_eval.mpr ⟨nSteps_reaches hs, hnone⟩⟩

end ConjectureMachines.Brocard28
