/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.Certificates.SeventhPower
public import LeanPool.CatalyticRegisters.Certificates.NinthPower
public import LeanPool.CatalyticRegisters.Certificates.EleventhPower
public import LeanPool.CatalyticRegisters.Certificates.ThirteenthPower
public import LeanPool.CatalyticRegisters.Certificates.FifteenthPower

/-! # Three-register powering correctness and access counts -/

namespace Catalytic

@[expose] public section

universe u

/-- **Theorem T3a (`x^7 ∈ RP^{pass}_R(3, 5)` whenever `576` is a unit in `R`).** -/
theorem three_reg_5call_x7 {R : Type u} [CRing R]
    (inv576 : R) (hinv : inv576 * CRing.intCast 576 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut inv576 prog5Power7) = 5 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut inv576 prog5Power7) (o, u, v) = (o + CRing.pow x 7, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog5_x7_accesses,
   fun x o u v => exec3Poly_certifies_monic prog5Power7 7 576 prog5_x7_cert inv576 hinv x o u v⟩

/-- **Theorem T3b (`x^9 ∈ RP^{pass}_R(3, 6)` whenever `382500000` is a unit in `R`).** -/
theorem three_reg_6call_x9 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 382500000 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog6Power9) = 6 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog6Power9) (o, u, v) = (o + CRing.pow x 9, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog6_x9_accesses,
   fun x o u v => exec3Poly_certifies_monic prog6Power9 9 382500000 prog6_x9_cert invD hinv x o u v⟩

/-- **Theorem T3c (`x^11 ∈ RP^{pass}_R(3, 7)` over `ℚ` and all good prime characteristics).** -/
theorem three_reg_7call_x11 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 68724637549388656012800 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog7Power11) = 7 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog7Power11) (o, u, v) = (o + CRing.pow x 11, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog7_x11_accesses,
   fun x o u v =>
     exec3Poly_certifies_monic prog7Power11 11 68724637549388656012800 prog7_x11_cert invD hinv x o u v⟩

/-- **Theorem T3d (`x^13 ∈ RP^{pass}_R(3, 8)` — smallest constructed 3-register exponent `log_13 8 ≈ 0.810714`).** -/
theorem three_reg_8call_x13 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 2656207148788801777680 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog8Power13) = 8 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog8Power13) (o, u, v) = (o + CRing.pow x 13, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog8_x13_accesses,
   fun x o u v =>
     exec3Poly_certifies_monic prog8Power13 13 2656207148788801777680 prog8_x13_cert invD hinv x o u v⟩

/-- **Theorem T3g (`x^15 ∈ RP^{pass}_R(3, 9)` — post-minimum ascent point `log_15 9 ≈ 0.811368`).** -/
theorem three_reg_9call_x15 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog9Power15) = 9 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog9Power15) (o, u, v) = (o + CRing.pow x 15, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog9_x15_accesses,
   fun x o u v =>
     exec3Poly_certifies_monic prog9Power15 15 876702103804656272895371895753963647960420947968000
       prog9_x15_cert invD hinv x o u v⟩

/-! ## 4. Exact Natural-Number Proof of the Strictly Decreasing Exponent Chain -/

/--
Exact rational separation proving:
  `log_13 8 < 30/37 < log_11 7 < 13/16 < log_9 6 < 9/11 < log_7 5 < 5/6 < log_5 4`
  and `log_13 8 < 30/37 < log_15 9`
using pure `Nat` exponentiation (`a^q < b^p ⇔ log_b a < p/q` for `a, b > 1`).
-/
theorem exponent_strict_improvement_chain :
    (8 ^ 37 < 13 ^ 30) ∧ (11 ^ 30 < 7 ^ 37) ∧
    (7 ^ 16 < 11 ^ 13) ∧ (9 ^ 13 < 6 ^ 16) ∧
    (6 ^ 11 < 9 ^ 9)   ∧ (7 ^ 9 < 5 ^ 11) ∧
    (5 ^ 6 < 7 ^ 5)    ∧ (5 ^ 5 < 4 ^ 6) ∧
    (15 ^ 30 < 9 ^ 37) := by
  decide

/--
**Theorem T3f (Unique Integer Minimizer `t = 8` of `log_{2t - 3} t` for All `t ≥ 4`):**
Pure integer-arithmetic inequality (no register program in statement): via `30 / 37`,
certifies `log_13 8 < 30 / 37 < log_{2t - 3} t` for EVERY integer `t ≥ 4` with `t ≠ 8`:
  1. `8 ^ 37 < 13 ^ 30`, and
  2. `∀ t : Nat, 4 ≤ t → t ≠ 8 → (2 * t - 3) ^ 30 < t ^ 37`.
Proved in pure `Nat` arithmetic using only `[propext, Quot.sound]` (no `Classical.choice`).
-/
theorem exponent_global_integer_optimality :
    (8 ^ 37 < 13 ^ 30) ∧
    (∀ t : Nat, 4 ≤ t → t ≠ 8 → (2 * t - 3) ^ 30 < t ^ 37) := by
  refine ⟨by decide, ?_⟩
  intro t ht4 ht8
  by_cases hlt : t < 20
  · have hcases :
        t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨
        t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have ht20 : 20 ≤ t := by omega
    have h1 : (2 * t - 3) ^ 30 ≤ (2 * t) ^ 30 := Nat.pow_le_pow_left (by omega) 30
    have h2 : (2 * t) ^ 30 = 2 ^ 30 * t ^ 30 := Nat.mul_pow 2 t 30
    have h3 : 2 ^ 30 < 20 ^ 7 := by decide
    have h4 : 20 ^ 7 ≤ t ^ 7 := Nat.pow_le_pow_left ht20 7
    have h5 : 0 < t ^ 30 := Nat.pow_pos (by omega)
    have h6 : 2 ^ 30 * t ^ 30 < t ^ 7 * t ^ 30 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le h3 h4) h5
    have h7 : t ^ 7 * t ^ 30 = t ^ 37 := (Nat.pow_add t 7 30).symm
    exact Nat.lt_of_le_of_lt h1 (by rw [h2, ← h7]; exact h6)

end

end Catalytic
