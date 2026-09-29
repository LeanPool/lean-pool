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
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Formats
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Calculation.Operations

/-!
# Exact Representations for Rounded Arithmetic

The error theorems for addition, multiplication, division, and square root need more than a bound:
they track the grid on which an intermediate value is exactly representable. The lemmas below are
the common representation layer for those developments.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

omit [ValidExp fexp] in
/--
Rounding a mantissa/exponent value can be represented using its original exponent.

If the canonical exponent is no larger than the stored exponent, the input is already generic and
rounding fixes it. Otherwise the rounded canonical mantissa is shifted by an integral radix power.
This is the Lean counterpart of Flocq's `round_repr_same_exp`.
-/
theorem round_toReal_exists_same_exponent (rnd : ℝ → ℤ) [ValidRnd rnd]
    (f : FloatRep β) :
    ∃ m : ℤ,
      round (β := β) (fexp := fexp) rnd (toReal f) =
        toReal ({ mantissa := m, exponent := f.exponent } : FloatRep β) := by
  let x := toReal f
  let e' := cexp β fexp x
  by_cases he : e' ≤ f.exponent
  · refine ⟨f.mantissa, ?_⟩
    have hx : genericFormat β fexp x :=
      generic_format_of_toReal_of_cexp_le f x rfl he
    simpa [x] using round_preserves_generic rnd x hx
  · have he' : f.exponent < e' := lt_of_not_ge he
    obtain ⟨scale, hscale⟩ := bpow_eq_natCast_of_nonneg β
      (e' - f.exponent) (sub_nonneg.mpr he'.le)
    refine ⟨rnd (scaledMantissa β fexp x) * Int.ofNat scale, ?_⟩
    unfold round toReal
    change
      (rnd (scaledMantissa β fexp x) : ℝ) * bpow β e' =
        ((rnd (scaledMantissa β fexp x) * Int.ofNat scale : ℤ) : ℝ) *
          bpow β f.exponent
    rw [show e' = (e' - f.exponent) + f.exponent by ring]
    rw [bpow.add_exp, hscale]
    have hcast : (((Int.ofNat scale : ℤ) : ℝ)) = (scale : ℝ) := by norm_num
    rw [Int.cast_mul, hcast]
    ring

/-- The sum of two mantissa/exponent values has a representation at the smaller exponent. -/
theorem toReal_add_exists_min_exponent (f g : FloatRep β) :
    ∃ h : FloatRep β,
      toReal f + toReal g = toReal h ∧
      h.exponent = min f.exponent g.exponent := by
  exact ⟨FloatRep.addExact f g, (FloatRep.toReal_addExact f g).symm,
    FloatRep.align_exponent f g⟩

/--
An FLX sum is representable when it fits in `prec` radix digits relative to both operand
representations. This is the common-grid lemma used by division and square-root residual proofs.
-/
theorem generic_format_FLX_add_of_repr_bounds (prec : ℤ) (hprec : 0 < prec)
    (f g : FloatRep β) (x y : ℝ)
    (hx : x = toReal f) (hy : y = toReal g)
    (hxf : abs (x + y) < bpow β (prec + f.exponent))
    (hyg : abs (x + y) < bpow β (prec + g.exponent)) :
    genericFormat β (flxExp prec) (x + y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  by_cases hzero : x + y = 0
  · rw [hzero]
    exact generic_format_zero
  obtain ⟨h, hsum, hexp⟩ := toReal_add_exists_min_exponent f g
  have hrepr : x + y = toReal h := by simpa [hx, hy] using hsum
  apply generic_format_of_toReal_of_cexp_le h (x + y) hrepr
  have hmagF : magnitude β (x + y) ≤ prec + f.exponent :=
    magnitude_le_of_abs_lt_bpow β (x + y) _ hzero hxf
  have hmagG : magnitude β (x + y) ≤ prec + g.exponent :=
    magnitude_le_of_abs_lt_bpow β (x + y) _ hzero hyg
  rw [hexp]
  simp only [cexp, flxExp]
  exact le_min (by linarith) (by linarith)

end FloatLib.Floats.Formats.Flocq
