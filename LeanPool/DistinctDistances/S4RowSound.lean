/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4SoundApex
public import LeanPool.DistinctDistances.S4SoundBands
public import LeanPool.DistinctDistances.S4SoundBasic
public import LeanPool.DistinctDistances.S4SoundMoment
public import LeanPool.DistinctDistances.S4SoundPalette

/-!
# Soundness of the row builder of the `1/40` certificate

Every row that `Params.build` returns holds at the normalized variables `val P S` of a
configuration `S` in the case `Y_lo ≤ yMean ≤ Y_hi`, given the proved chord conditions
(`Params.build_sound`); so does its integer scaling (`Params.buildInt_sound`). With the box
(`Params.box_sound`), an accepted certificate of `FarkasPackedCheck.check` contradicts the
configuration (`Params.false_of_check`).
-/

@[expose] public section

namespace Esgk.S4

open Esgk.FarkasPackedCheck

variable {n : ℕ}

/-- Every row of the builder holds for the configuration in the case `Y_lo ≤ yMean ≤ Y_hi`. -/
theorem Params.build_sound (P : Params) (S : Setting n) {Ylo Yhi : ℚ}
    (hlo : (Ylo : ℝ) ≤ S.ybar) (hhi : S.ybar ≤ (Yhi : ℝ)) (hch : P.ChordsHold S) :
    ∀ t r, P.build Ylo Yhi t = some r → r.Holds (val P S)
  | .amono _ _, _, h => P.rowAmono_sound S h
  | .xmono _ _, _, h => P.rowXmono_sound S h
  | .xpos _, _, h => P.rowXpos_sound S h
  | .xleq _, _, h => P.rowXleq_sound S h
  | .a2lo _, _, h => P.rowA2lo_sound S h
  | .mlo, _, h => P.rowMlo_sound S h
  | .layer _ _, _, h => P.rowLayer_sound S h
  | .pa _ _ _ _, _, h => P.rowPa_sound S h hch
  | .pb _ _ _ _, _, h => P.rowPb_sound S h hch
  | .pc _ _ _ _, _, h => P.rowPc_sound S h hch
  | .aa _ _ _ _ _, _, h => P.rowAA_sound S h
  | .jj _ _ _ _ _, _, h => P.rowJ_sound S h
  | .ab1 _ _, _, h => P.rowAB1_sound S h
  | .ab2 _, _, h => P.rowAB2_sound S h
  | .ab3 _ _ _, _, h => P.rowAB3_sound S h
  | .ab4 _ _ _, _, h => P.rowAB4_sound S h
  | .ab6u _ _, _, h => P.rowAB6u_sound S h hhi
  | .ab6v _ _ _, _, h => P.rowAB6v_sound S h hhi
  | .caselo, _, h => P.rowCaseLo_sound S h hlo
  | .casehi, _, h => P.rowCaseHi_sound S h hhi

/-- Every integer row of the builder holds for the configuration in the case
`Y_lo ≤ yMean ≤ Y_hi`. -/
theorem Params.buildInt_sound (P : Params) (S : Setting n) {Ylo Yhi : ℚ}
    (hlo : (Ylo : ℝ) ≤ S.ybar) (hhi : S.ybar ≤ (Yhi : ℝ)) (hch : P.ChordsHold S) :
    ∀ t R, P.buildInt Ylo Yhi t = some R → R.Holds (val P S) := by
  intro t R h
  unfold Params.buildInt at h
  cases hb : P.build Ylo Yhi t with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some r =>
    rw [hb] at h
    exact QRow.toRow_sound h (P.build_sound S hlo hhi hch t r hb)

/-- A certificate accepted by the checker in the case `Y_lo ≤ yMean ≤ Y_hi` contradicts the
configuration. -/
theorem Params.false_of_check (P : Params) (S : Setting n) {Ylo Yhi : ℚ}
    {w : WTree Tag} {W : Nat} (hc : check W P.box (P.buildInt Ylo Yhi) w = true)
    (hlo : (Ylo : ℝ) ≤ S.ybar) (hhi : S.ybar ≤ (Yhi : ℝ)) (hch : P.ChordsHold S) : False :=
  check_sound (val P S) (P.buildInt_sound S hlo hhi hch) (P.box_sound S) hc

end Esgk.S4
