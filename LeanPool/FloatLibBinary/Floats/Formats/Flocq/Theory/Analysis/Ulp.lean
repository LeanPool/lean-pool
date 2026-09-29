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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Generic

/-!
# Unit in the Last Place

The format-generic `ulp` laws cover the negligible-exponent witness used to define `ulp 0`,
invariance under sign, representability, and the relationship to adjacent rounded values. The
definitions and hypotheses follow Flocq's `Core/Ulp.v`.

These are mathematical analysis lemmas rather than executable kernels. Keeping them in the Flocq
theory namespace makes the provenance and theorem correspondence visible while allowing runtime
formats to depend on smaller exact-arithmetic modules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Two negligible-exponent witnesses select the same format exponent. -/
theorem negligibleExp_value_unique {n m : ℤ}
    (hn : IsNegligibleExp fexp n) (hm : IsNegligibleExp fexp m) :
    fexp n = fexp m := by
  rcases le_total m (fexp n) with hmn | hnm
  · exact (((ValidExp.flocq_valid (fexp := fexp) n).2 hn).2 m hmn).symm
  · have hnfm : n ≤ fexp m := hn.trans (hnm.trans hm)
    exact ((ValidExp.flocq_valid (fexp := fexp) m).2 hm).2 n hnfm

omit [ValidExp fexp] in
/-- Absence of a negligible exponent means `fexp n < n` at every exponent. -/
theorem negligibleExp_none_iff_forall_lt :
    negligibleExp fexp = none ↔ ∀ n, fexp n < n := by
  rw [negligibleExp_eq_none_iff]
  constructor
  · intro h n
    exact lt_of_not_ge (fun hn => h ⟨n, hn⟩)
  · intro h
    rintro ⟨n, hn⟩
    exact (not_le_of_gt (h n)) hn

omit [ValidExp fexp] in
/-- ULP is invariant under negation. -/
@[simp] theorem ulp_neg (x : ℝ) : ulp β fexp (-x) = ulp β fexp x := by
  by_cases hx : x = 0
  · subst x
    simp
  · simp [ulp, hx, cexp]

omit [ValidExp fexp] in
/-- ULP is invariant under absolute value. -/
@[simp] theorem ulp_abs (x : ℝ) : ulp β fexp (abs x) = ulp β fexp x := by
  rcases le_total 0 x with hx | hx
  · simp [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, ulp_neg]

omit [ValidExp fexp] in
/-- The ULP of a radix power is selected at the next magnitude. -/
theorem ulp_bpow (e : ℤ) :
    ulp β fexp (bpow β e) = bpow β (fexp (e + 1)) := by
  rw [ulp.of_ne_zero β fexp _ (bpow.ne_zero β e)]
  simp [cexp]

/-- Exponent functions for which ULP values themselves remain representable. -/
class ExpNotFlushToZero (fexp : ℤ → ℤ) : Prop where
  /-- The radix power selected as a ULP is representable at its own magnitude. -/
  ulpExponent : ∀ e, fexp (fexp e + 1) ≤ fexp e

/-- The zero ULP is representable, including the FLX case where it equals zero. -/
theorem generic_format_ulp_zero : genericFormat β fexp (ulp β fexp 0) := by
  rw [ulp.zero]
  cases hopt : negligibleExp fexp with
  | none =>
      simp
  | some n =>
      have hn := negligibleExp_spec hopt
      apply generic_format_bpow
      exact ((ValidExp.flocq_valid (fexp := fexp) n).2 hn).1

/-- Under the non-flush-to-zero condition, every ULP is representable. -/
theorem generic_format_ulp [ExpNotFlushToZero fexp] (x : ℝ) :
    genericFormat β fexp (ulp β fexp x) := by
  by_cases hx : x = 0
  · subst x
    exact generic_format_ulp_zero
  · rw [ulp.of_ne_zero β fexp x hx]
    exact generic_format_bpow _
      (ExpNotFlushToZero.ulpExponent (fexp := fexp) (magnitude β x))

omit [ValidExp fexp] in
/-- For a nonrepresentable input, directed-up and directed-down rounding differ by one ULP. -/
theorem round_ceil_eq_floor_add_ulp {x : ℝ} (hx : ¬genericFormat β fexp x) :
    round (β := β) (fexp := fexp) ceilRound x =
      round (β := β) (fexp := fexp) floorRound x + ulp β fexp x := by
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    exact hx generic_format_zero
  have hsnot : scaledMantissa β fexp x ∉ Set.range ((↑·) : ℤ → ℝ) := by
    rintro ⟨n, hn⟩
    apply hx
    apply generic_format_of_scaled_mantissa_int (n := n)
    exact hn.symm
  have hceil : ceilRound (scaledMantissa β fexp x) =
      floorRound (scaledMantissa β fexp x) + 1 := by
    exact (Int.ceil_eq_floor_add_one_iff_notMem _).2 hsnot
  rw [ulp.of_ne_zero β fexp x hx0]
  unfold round toReal
  rw [hceil]
  push_cast
  ring

omit [ValidExp fexp] in
/-- One ULP is no larger than the absolute value of a nonzero representable number. -/
theorem ulp_le_abs_of_generic {x : ℝ} (hx0 : x ≠ 0)
    (hx : genericFormat β fexp x) : ulp β fexp x ≤ abs x := by
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp) x hx
  have hn0 : n ≠ 0 := by
    intro hnzero
    have hs0 : scaledMantissa β fexp x = 0 := by simpa [hnzero] using hn
    have hrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
    rw [hs0, zero_mul] at hrepr
    exact hx0 hrepr.symm
  have habsn : (1 : ℝ) ≤ abs (n : ℝ) := by
    exact_mod_cast (Int.one_le_abs hn0)
  have hb := bpow.nonneg β (cexp β fexp x)
  rw [ulp.of_ne_zero β fexp x hx0]
  have hrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
  rw [hn] at hrepr
  calc
    bpow β (cexp β fexp x) =
        1 * bpow β (cexp β fexp x) := by ring
    _ ≤ abs (n : ℝ) * bpow β (cexp β fexp x) :=
      mul_le_mul_of_nonneg_right habsn hb
    _ = abs ((n : ℝ) * bpow β (cexp β fexp x)) := by
      rw [abs_mul, abs_of_nonneg hb]
    _ = abs x := by rw [hrepr]

omit [ValidExp fexp] in
/-- ULP is monotone on positive inputs when the exponent selector is monotone. -/
theorem ulp_mono_pos [MonotoneExp fexp] {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : ulp β fexp x ≤ ulp β fexp y := by
  have hy : 0 < y := hx.trans_le hxy
  have hmag := magnitude_mono_pos β hx hxy
  rw [ulp.of_ne_zero β fexp x hx.ne', ulp.of_ne_zero β fexp y hy.ne']
  exact (bpow_le_bpow_iff β _ _).2
    (MonotoneExp.monotone _ _ hmag)

end FloatLib.Floats.Formats.Flocq
