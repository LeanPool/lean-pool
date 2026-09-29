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

/-!
# Flocq-style formats (FIX / FLX / FLT)

Exponent-selection functions `fexp : ℤ → ℤ` describe three real-valued format families:

- `FIX` is a fixed-exponent grid;
- `FLX` has fixed precision and unbounded exponents;
- `FLT` has fixed precision, a lower exponent bound, and gradual underflow.

`FLT` has no upper exponent bound or overflow. Executable binary formats with infinities,
NaNs, and signed zeros are defined in `FloatLib/Floats/Formats/BinaryInterchange/`.

References:

- Flocq project: https://flocq.gitlabpages.inria.fr/flocq/
- S. Boldo, G. Melquiond, “Flocq: a unified Coq library for proving floating-point algorithms
  correct”
  (ARITH 2011), DOI: 10.1109/ARITH.2011.40
- IEEE Standard for Floating-Point Arithmetic (IEEE 754-2019)
-/

@[expose] public section


namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
A positive number of radix digits for FLX, FLT, and FTZ formats.

Raw exponent functions remain available for algebraic proofs, but callers accepting an integer
configuration should first use `FormatPrecision.ofIntOption`.  This prevents a zero or negative
precision from being silently reinterpreted through an absolute-value conversion.

This is Mathlib's proof-erased positive-natural carrier rather than another project-local
structure.
-/
abbrev FormatPrecision := PNat

namespace FormatPrecision

/-- Convert a proof-carrying format precision to the integer parameter used by exponent formulas. -/
def toInt (precision : FormatPrecision) : ℤ := (precision : ℕ)

/-- Check a natural-number precision at a configuration boundary. -/
def ofNatOption (digits : ℕ) : Option FormatPrecision :=
  if h : 0 < digits then some ⟨digits, h⟩ else none

/-- Check an integer precision, rejecting zero and every negative value. -/
def ofIntOption (digits : ℤ) : Option FormatPrecision :=
  if h : 0 < digits then
    some ⟨digits.toNat, by
      have hcast : (digits.toNat : ℤ) = digits := Int.toNat_of_nonneg h.le
      have : (0 : ℤ) < (digits.toNat : ℤ) := by simpa [hcast] using h
      exact_mod_cast this⟩
  else none

/-- A checked precision remains positive after conversion to the integer exponent parameter. -/
@[simp] theorem toInt_pos (precision : FormatPrecision) : 0 < precision.toInt := by
  change (0 : ℤ) < ((precision : ℕ) : ℤ)
  exact_mod_cast precision.2

/-- Natural precision validation fails exactly at zero. -/
@[simp] theorem ofNatOption_eq_none_iff (digits : ℕ) :
    ofNatOption digits = none ↔ digits = 0 := by
  simp [ofNatOption]

/-- Integer precision validation fails exactly for nonpositive inputs. -/
@[simp] theorem ofIntOption_eq_none_iff (digits : ℤ) :
    ofIntOption digits = none ↔ digits ≤ 0 := by
  simp [ofIntOption]

end FormatPrecision

/--
`fixExp emin` is the simplest exponent-selection function: it always returns the same exponent.

This is Flocq's `FIX_exp`. It describes values living on a single fixed grid
$\beta^{\mathtt{emin}}\mathbb{Z}$, as in fixed-point arithmetic or quantization.
-/
def fixExp (emin : ℤ) : ℤ → ℤ := fun _ => emin

/--
`fixExp emin` satisfies the exponent-validity axioms `ValidExp`. Registering the result as an
instance lets the FIX theorems reuse the generic format lemmas shared with FLX and FLT.
-/
instance fixValidExp (emin : ℤ) : ValidExp (fixExp emin) where
  flocq_valid := by
    intro k
    constructor
    · intro h; simp only [fixExp] at h ⊢; exact Int.le_of_lt h
    · intro _; simp [fixExp]

instance fixMonotoneExp (emin : ℤ) : MonotoneExp (fixExp emin) where
  monotone := by simp [fixExp]

instance fixBoundedExpGrowth (emin : ℤ) : BoundedExpGrowth (fixExp emin) where
  boundedGrowth := by simp [fixExp]

/-- The ULP at zero for a fixed-point grid is its fixed grid step. -/
theorem ulp_zero_FIX (emin : ℤ) :
    ulp β (fixExp emin) 0 = bpow β emin := by
  rw [ulp.zero]
  cases hopt : negligibleExp (fixExp emin) with
  | none =>
      have hnone := (negligibleExp_eq_none_iff (fixExp emin)).mp hopt
      exfalso
      apply hnone
      exact ⟨emin, by simp [IsNegligibleExp, fixExp]⟩
  | some n => simp [fixExp]

/--
`FIXFormat emin x` says that `x` is exactly representable on the fixed grid with exponent `emin`.

The predicate is phrased through an existential `FloatRep β` so that it composes with the rest of
the rounding model (`toReal`, ULP bounds and so on).
-/
def FIXFormat (emin : ℤ) (x : ℝ) : Prop :=
  ∃ f : FloatRep β, x = toReal f ∧ f.exponent = emin

/--
`flxExp prec` is the unbounded-exponent family.

This is Flocq's `FLX_exp`: a floating-point format with no exponent bounds and mantissa precision
`prec`. It is a convenient intermediate model for proofs because it removes the underflow and
overflow corner cases while still tracking mantissa rounding.
-/
def flxExp (prec : ℤ) : ℤ → ℤ := fun e => e - prec

/--
`flxExp prec` satisfies `ValidExp` for positive precision.
-/
abbrev flxValidExp (prec : ℤ) (h : 0 < prec) : ValidExp (flxExp prec) where
  flocq_valid := by
    intro k
    constructor
    · intro H; simp [flxExp] at H ⊢; linarith
    · intro H; simp only [flxExp, le_sub_self_iff, tsub_le_iff_right, sub_add_cancel,
      Order.add_one_le_iff, sub_lt_self_iff,
                 sub_left_inj] at H ⊢
      constructor
      · linarith
      · intros l hl; exfalso; linarith [h, H]

/-- `flxExp prec` satisfies the generic exponent axioms exactly when `prec` is positive. -/
theorem validExp_FLX_iff (prec : ℤ) : ValidExp (flxExp prec) ↔ 0 < prec := by
  constructor
  · intro hvalid
    by_contra hprec
    have hnonpos : prec ≤ 0 := le_of_not_gt hprec
    have hsecond := (hvalid.flocq_valid 0).2 (by simp [flxExp]; linarith)
    have := hsecond.1
    simp [flxExp] at this
    linarith
  · exact flxValidExp prec

namespace FormatPrecision

/-- The unbounded exponent selector associated with a checked precision. -/
def flxExp (precision : FormatPrecision) : ℤ → ℤ := Flocq.flxExp precision.toInt

/-- A checked precision automatically discharges the FLX exponent-validity obligation. -/
instance flxExpValid (precision : FormatPrecision) : ValidExp precision.flxExp :=
  flxValidExp precision.toInt precision.toInt_pos

end FormatPrecision


/-- The FLX exponent selector is monotone for every precision parameter. -/
abbrev flxMonotoneExp (prec : ℤ) : MonotoneExp (flxExp prec) where
  monotone := by
    intros k1 k2 hk
    simp [flxExp]
    linarith

/-- The FLX exponent selector has bounded one-step growth. -/
abbrev flxBoundedExpGrowth (prec : ℤ) : BoundedExpGrowth (flxExp prec) where
  boundedGrowth := by simp [flxExp]

/--
Exact representability predicate for `FLX`.

The precision is positive, and $x=m\beta^e$ for an integer mantissa satisfying
$|m|<\beta^{\mathtt{prec}}$.
-/
def FLXFormat (prec : ℤ) (x : ℝ) : Prop :=
  0 < prec ∧
    ∃ f : FloatRep β, x = toReal f ∧ Int.natAbs f.mantissa < β.base ^ prec.toNat

/-- Nonpositive precision is rejected by the explicit FLX format predicate. -/
theorem not_flxFormat_of_nonpos (prec : ℤ) (hprec : prec ≤ 0) (x : ℝ) :
    ¬FLXFormat (β := β) prec x := by
  simp [FLXFormat, not_lt_of_ge hprec]

/-- The unbounded FLX exponent function has no negligible exponent. -/
theorem negligibleExp_FLX (prec : ℤ) (hprec : 0 < prec) :
    negligibleExp (flxExp prec) = none := by
  rw [negligibleExp_eq_none_iff]
  rintro ⟨n, hn⟩
  simp [IsNegligibleExp, flxExp] at hn
  linarith

/-- Consequently, the generic ULP of zero is zero for FLX. -/
theorem ulp_zero_FLX (prec : ℤ) (hprec : 0 < prec) :
    ulp β (flxExp prec) 0 = 0 := by
  simp [ulp, negligibleExp_FLX prec hprec]

/--
`fltExp emin prec` is the lower-exponent-bounded family with gradual underflow.

This is Flocq's `FLT_exp`. The exponent is bounded below by `emin` but has no upper bound, so the
format models gradual underflow but not overflow, infinities, or NaNs. Gradual underflow is
captured by taking `max (e - prec) emin`.
-/
def fltExp (emin prec : ℤ) : ℤ → ℤ := fun e => max (e - prec) emin

/--
`fltExp emin prec` satisfies `ValidExp` for positive precision.

This validity witness connects proofs to an executable binary descriptor through
`BinaryInterchange.Model.fexpOf` and `BinaryInterchange.Model.roundAt`.
-/
abbrev fltValidExp (emin prec : ℤ) (h : 0 < prec) : ValidExp (fltExp emin prec) where
  flocq_valid := by
    intro k
    constructor
    · intro hk
      have hk' : max (k - prec) emin < k := by simpa [fltExp] using hk
      have hprec1 : (1 : ℤ) ≤ prec := by linarith [h]
      have hemin_le : emin ≤ k :=
        le_of_lt (lt_of_le_of_lt (le_max_right (k - prec) emin) hk')
      have hleft_le : k + 1 - prec ≤ k := by linarith [hprec1]
      simpa [fltExp] using (max_le_iff).2 ⟨hleft_le, hemin_le⟩
    · intro hk
      have hk' : k ≤ max (k - prec) emin := by simpa [fltExp] using hk
      have hk_cases : k ≤ k - prec ∨ k ≤ emin := (le_max_iff).1 hk'
      have hprec0 : 0 ≤ prec := le_of_lt h
      have hprec1 : (1 : ℤ) ≤ prec := by linarith [h]
      cases hk_cases with
      | inl hk_le =>
          exfalso
          have : k - prec < k := by linarith [h]
          exact (not_le_of_gt this) hk_le
      | inr hk_le_emin =>
          have hk_fexp : fltExp emin prec k = emin := by
            apply max_eq_right
            have : k - prec ≤ emin - prec := sub_le_sub_right hk_le_emin prec
            exact this.trans (sub_le_self emin hprec0)
          constructor
          · have hleft : emin + 1 - prec ≤ emin := by linarith [hprec1]
            simp only [hk_fexp, ge_iff_le]
            dsimp [fltExp]
            exact (max_le_iff).2 ⟨hleft, le_rfl⟩
          · intro l hl
            have hl' : l ≤ emin := by simpa [hk_fexp] using hl
            have hle : l - prec ≤ emin := (sub_le_self l hprec0).trans hl'
            rw [hk_fexp]
            dsimp [fltExp]
            exact max_eq_right hle

/-- `fltExp emin prec` satisfies the exponent axioms exactly for positive precision. -/
theorem validExp_FLT_iff (emin prec : ℤ) : ValidExp (fltExp emin prec) ↔ 0 < prec := by
  constructor
  · intro hvalid
    by_contra hprec
    have hnonpos : prec ≤ 0 := le_of_not_gt hprec
    have hk : emin ≤ fltExp emin prec emin := by simp [fltExp]
    have hnext := ((hvalid.flocq_valid emin).2 hk).1
    have hlower : fltExp emin prec (fltExp emin prec emin + 1) ≥
        fltExp emin prec emin + 1 := by
      apply le_max_of_le_left
      linarith
    linarith
  · exact fltValidExp emin prec

namespace FormatPrecision

/-- The gradual-underflow exponent selector associated with a checked precision. -/
def fltExp (precision : FormatPrecision) (emin : ℤ) : ℤ → ℤ :=
  Flocq.fltExp emin precision.toInt

/-- A checked precision automatically discharges the gradual-underflow validity obligation. -/
instance fltExpValid (precision : FormatPrecision) (emin : ℤ) :
    ValidExp (precision.fltExp emin) :=
  fltValidExp emin precision.toInt precision.toInt_pos

end FormatPrecision


/-- The gradual-underflow FLT exponent selector has bounded one-step growth. -/
abbrev fltBoundedExpGrowth (emin prec : ℤ) :
    BoundedExpGrowth (fltExp emin prec) where
  boundedGrowth := by
    intro k
    simp only [fltExp]
    have h1 : max (k + 1 - prec) emin ≤ max (k - prec) emin + 1 := by
      simp [max_def]
      split_ifs with h2 h3
      · linarith
      · linarith
      · linarith
      · linarith
    have h2 : max (k - prec) emin ≤ max (k + 1 - prec) emin + 1 := by
      simp [max_def]
      split_ifs with h4 h5
      · linarith
      · linarith
      · linarith
      · linarith
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The gradual-underflow FLT exponent selector is monotone. -/
abbrev fltMonotoneExp (emin prec : ℤ) : MonotoneExp (fltExp emin prec) where
  monotone := by
    intros k1 k2 hk
    simp only [fltExp]
    have h1 : k1 - prec ≤ k2 - prec := by linarith [hk]
    exact max_le_max h1 (le_refl emin)

/--
Exact representability predicate for `FLT`.

The precision is positive, and $x=m\beta^e$ with $|m|<\beta^{\mathtt{prec}}$ and
$\mathtt{emin}\le e$. In particular, every nonzero value has magnitude at least
$\beta^{\mathtt{emin}}$.
-/
def FLTFormat (emin prec : ℤ) (x : ℝ) : Prop :=
  0 < prec ∧
    ∃ f : FloatRep β, x = toReal f ∧
      Int.natAbs f.mantissa < β.base ^ prec.toNat ∧ emin ≤ f.exponent

/-- Nonpositive precision is rejected by the explicit FLT format predicate. -/
theorem not_fltFormat_of_nonpos (emin prec : ℤ) (hprec : prec ≤ 0) (x : ℝ) :
    ¬FLTFormat (β := β) emin prec x := by
  simp [FLTFormat, not_lt_of_ge hprec]

/-- FLT has a negligible-exponent witness at `emin`. -/
theorem exists_negligibleExp_FLT (emin prec : ℤ) :
    ∃ n, IsNegligibleExp (fltExp emin prec) n := by
  refine ⟨emin, ?_⟩
  exact le_max_right _ _

/-- The ULP at zero for FLT is the smallest grid step $\beta^{\mathtt{emin}}$. -/
theorem ulp_zero_FLT (emin prec : ℤ) (hprec : 0 < prec) :
    ulp β (fltExp emin prec) 0 = bpow β emin := by
  rw [ulp.zero]
  cases hopt : negligibleExp (fltExp emin prec) with
  | none =>
      have hnone := (negligibleExp_eq_none_iff (fltExp emin prec)).mp hopt
      exact False.elim (hnone (exists_negligibleExp_FLT emin prec))
  | some n =>
      have hn := negligibleExp_spec hopt
      have hp : 0 ≤ prec := hprec.le
      have hnE : n ≤ emin := by
        rcases (le_max_iff.mp hn) with hbad | hgood
        · exfalso
          linarith
        · exact hgood
      have hselected : fltExp emin prec n = emin := by
        apply max_eq_right
        exact (sub_le_self n hp).trans hnE
      simp [hselected]

end FloatLib.Floats.Formats.Flocq
