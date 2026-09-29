/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Core
public import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Radix Magnitude

The magnitude of a nonzero real $x$ is the unique integer $e$ for which
$\beta^{e-1}\le|x|<\beta^e$. These bounds are the basic bridge between logarithmic magnitude,
canonical exponents, and generic-format rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Flocq magnitude is Mathlib's integer logarithm plus one away from zero. -/
theorem magnitude_eq_int_log_add_one (β : Numerics.Radix) (x : ℝ) (hx : x ≠ 0) :
    magnitude β x = Int.log β.base |x| + 1 := by
  simpa [magnitude, hx, Real.logb, Numerics.Radix.toReal] using
    congrArg (fun n : ℤ ↦ n + 1)
      (Real.floor_logb_natCast (b := β.base) (abs_nonneg x))

/-- The logarithmic definition of `magnitude` satisfies the standard Flocq magnitude bounds. -/
theorem magnitude_spec (β : Numerics.Radix) (x : ℝ) (hx : x ≠ 0) :
    bpow β (magnitude β x - 1) ≤ abs x ∧
      abs x < bpow β (magnitude β x) := by
  rw [magnitude_eq_int_log_add_one β x hx]
  have hb : 1 < β.base := β.base_valid
  simpa [bpow, Numerics.Radix.toReal] using
    And.intro (Int.zpow_log_le_self hb (abs_pos.mpr hx))
      (Int.lt_zpow_succ_log_self hb |x|)

/-- Lower magnitude bound for a nonzero real. -/
theorem bpow_magnitude_sub_one_le (β : Numerics.Radix) (x : ℝ) (hx : x ≠ 0) :
    bpow β (magnitude β x - 1) ≤ abs x :=
  (magnitude_spec β x hx).1

/-- Strict upper magnitude bound for a nonzero real. -/
theorem abs_lt_bpow_magnitude (β : Numerics.Radix) (x : ℝ) (hx : x ≠ 0) :
    abs x < bpow β (magnitude β x) :=
  (magnitude_spec β x hx).2

/-- The magnitude of $\beta^e$ is $e+1$. -/
@[simp] theorem magnitude_bpow (β : Numerics.Radix) (e : ℤ) :
    magnitude β (bpow β e) = e + 1 := by
  rw [magnitude_eq_int_log_add_one β _ (bpow.ne_zero β e),
    abs_of_pos (bpow.pos β e)]
  simpa only [bpow, Numerics.Radix.toReal] using
    congrArg (fun n : ℤ ↦ n + 1) (Int.log_zpow β.base_valid e)

/-- Radix powers preserve and reflect exponent order. -/
@[simp] theorem bpow_le_bpow_iff (β : Numerics.Radix) (e₁ e₂ : ℤ) :
    bpow β e₁ ≤ bpow β e₂ ↔ e₁ ≤ e₂ := by
  change β.toReal ^ e₁ ≤ β.toReal ^ e₂ ↔ e₁ ≤ e₂
  exact zpow_le_zpow_iff_right₀ (G₀ := ℝ) (a := β.toReal)
    (m := e₁) (n := e₂) (Numerics.Radix.gt_one β)

/-- Radix powers preserve and reflect strict exponent order. -/
@[simp] theorem bpow_lt_bpow_iff (β : Numerics.Radix) (e₁ e₂ : ℤ) :
    bpow β e₁ < bpow β e₂ ↔ e₁ < e₂ := by
  change β.toReal ^ e₁ < β.toReal ^ e₂ ↔ e₁ < e₂
  exact zpow_lt_zpow_iff_right₀ (G₀ := ℝ) (a := β.toReal)
    (m := e₁) (n := e₂) (Numerics.Radix.gt_one β)

/-- Radix-power bounds uniquely determine magnitude. -/
theorem magnitude_eq_of_bpow_bounds (β : Numerics.Radix) (x : ℝ) (e : ℤ)
    (hx : x ≠ 0) (hlower : bpow β (e - 1) ≤ abs x)
    (hupper : abs x < bpow β e) : magnitude β x = e := by
  have hspec := magnitude_spec β x hx
  have hleft : e - 1 < magnitude β x := by
    exact (bpow_lt_bpow_iff β (e - 1) (magnitude β x)).mp
      (hlower.trans_lt hspec.2)
  have hright : magnitude β x - 1 < e := by
    exact (bpow_lt_bpow_iff β (magnitude β x - 1) e).mp
      (hspec.1.trans_lt hupper)
  linarith

/-- Any strict radix-power upper bound is also an upper bound on magnitude. -/
theorem magnitude_le_of_abs_lt_bpow (β : Numerics.Radix) (x : ℝ) (e : ℤ)
    (hx : x ≠ 0) (hupper : abs x < bpow β e) : magnitude β x ≤ e := by
  have hlower := bpow_magnitude_sub_one_le β x hx
  have hexp : magnitude β x - 1 < e :=
    (bpow_lt_bpow_iff β (magnitude β x - 1) e).mp
      (hlower.trans_lt hupper)
  linarith

/-- Magnitude is monotone on positive real inputs. -/
theorem magnitude_mono_pos (β : Numerics.Radix) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : magnitude β x ≤ magnitude β y := by
  rw [magnitude_eq_int_log_add_one β x hx.ne',
    magnitude_eq_int_log_add_one β y (hx.trans_le hxy).ne']
  have hlog := Int.log_mono_right (b := β.base) hx hxy
  simpa [abs_of_pos hx, abs_of_pos (hx.trans_le hxy)] using add_le_add hlog (le_refl (1 : ℤ))

/-- Magnitude is monotone with respect to absolute value for nonzero inputs. -/
theorem magnitude_mono_abs (β : Numerics.Radix) {x y : ℝ}
    (hx : x ≠ 0) (hxy : abs x ≤ abs y) :
    magnitude β x ≤ magnitude β y := by
  have hy : y ≠ 0 := abs_pos.mp ((abs_pos.mpr hx).trans_le hxy)
  rw [magnitude_eq_int_log_add_one β x hx, magnitude_eq_int_log_add_one β y hy]
  exact add_le_add (Int.log_mono_right (b := β.base) (abs_pos.mpr hx) hxy) le_rfl

/--
A monotone exponent format preserves absolute-value order at canonical exponents of nonzero inputs.
-/
theorem cexp_mono_abs (β : Numerics.Radix)
    {fexp : ℤ → ℤ} [MonotoneExp fexp]
    {x y : ℝ} (hx : x ≠ 0) (hxy : abs x ≤ abs y) :
    cexp β fexp x ≤ cexp β fexp y := by
  apply MonotoneExp.monotone
  exact magnitude_mono_abs β hx hxy

/-- The magnitude of a nonzero product is at most the sum of operand magnitudes. -/
theorem magnitude_mul_le_add (β : Numerics.Radix) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    magnitude β (x * y) ≤ magnitude β x + magnitude β y := by
  apply magnitude_le_of_abs_lt_bpow β (x * y)
  · exact mul_ne_zero hx hy
  · rw [abs_mul, bpow.add_exp]
    exact mul_lt_mul
      (abs_lt_bpow_magnitude β x hx)
      (abs_lt_bpow_magnitude β y hy).le
      (abs_pos.mpr hy)
      (bpow.nonneg β _)

/-- Multiplication by a radix power shifts magnitude by its exponent. -/
theorem magnitude_mul_bpow (β : Numerics.Radix) (x : ℝ) (e : ℤ) (hx : x ≠ 0) :
    magnitude β (x * bpow β e) = magnitude β x + e := by
  apply magnitude_eq_of_bpow_bounds β
  · exact mul_ne_zero hx (bpow.ne_zero β e)
  · rw [abs_mul, abs_of_pos (bpow.pos β e)]
    calc
      bpow β (magnitude β x + e - 1) =
          bpow β (magnitude β x - 1) * bpow β e := by
        rw [← bpow.add_exp]
        congr 1
        ring
      _ ≤ abs x * bpow β e := mul_le_mul_of_nonneg_right
        (bpow_magnitude_sub_one_le β x hx) (bpow.nonneg β e)
  · rw [abs_mul, abs_of_pos (bpow.pos β e)]
    calc
      abs x * bpow β e <
          bpow β (magnitude β x) * bpow β e :=
        mul_lt_mul_of_pos_right
          (abs_lt_bpow_magnitude β x hx) (bpow.pos β e)
      _ = bpow β (magnitude β x + e) :=
        (bpow.add_exp β _ _).symm

/-- A radix power with nonnegative exponent is the cast of a natural number. -/
theorem bpow_eq_natCast_of_nonneg (β : Numerics.Radix) (e : ℤ) (he : 0 ≤ e) :
    ∃ n : ℕ, bpow β e = n := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he
  exact ⟨β.base ^ n, by simp [bpow, Numerics.Radix.toReal]⟩

end FloatLib.Floats.Formats.Flocq
