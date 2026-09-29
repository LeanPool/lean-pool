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

public import LeanPool.FloatLibBinary.Numerics.Capabilities.Radix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# FloatRep core (Flocq-style rounded arithmetic)

The rounded-real model separates representation, value, and format:

- represent a value with integer mantissa $m$ and exponent $e$,
- interpret it as the real number $m\beta^e$,
- describe the *format* via an exponent-selection function `fexp : ℤ → ℤ` and a rounding operator.

This decomposition is the same one used by the Coq library **Flocq**. It makes many theorems
reusable across formats (fixed-point, unbounded floats, and lower-exponent-bounded floats) and
aligns well
with ULP-style error bounds from numerical analysis.

For executable, bit-level binary semantics (NaN/Inf/signed zero), see
`FloatLib/Floats/Formats/BinaryInterchange/`.

## References

- Flocq project (documentation + sources): https://flocq.gitlabpages.inria.fr/flocq/
- S. Boldo, G. Melquiond, “Flocq: a unified Coq library for proving floating-point algorithms
  correct”
  (ARITH 2011), DOI: 10.1109/ARITH.2011.40
- IEEE Standard for Floating-Point Arithmetic (IEEE 754-2019)
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002
-/

@[expose] public section


namespace FloatLib.Floats.Formats.Flocq

/-- A radix-$\beta$ floating-point representation with integer mantissa and exponent. -/
structure FloatRep (β : Numerics.Radix) where
  /-- Integer mantissa `m`. -/
  mantissa : ℤ
  /-- Integer exponent `e`. -/
  exponent : ℤ

namespace FloatRep

variable {β : Numerics.Radix} (f : FloatRep β)

/-- Structural zero test (mantissa is exactly `0`). -/
def isZero : Prop := f.mantissa = 0

/-- Sign of the mantissa (matches the sign of `toReal` since $\beta^e>0$). -/
def sign : ℤ := Int.sign f.mantissa

end FloatRep

/--
Base power: $\beta^e$ as a real number.

This is Flocq's `bpow` concept: the scaling factor used to interpret mantissa/exponent pairs.
-/
noncomputable def bpow (β : Numerics.Radix) (e : ℤ) : ℝ := β.toReal ^ e

namespace bpow

variable (β : Numerics.Radix)

/-- Base powers are positive: $\beta^e>0$ for any exponent $e$. -/
lemma pos (e : ℤ) : 0 < bpow β e := zpow_pos (Numerics.Radix.pos β) e

/-- Base powers are nonnegative: $\beta^e\ge0$ for any exponent $e$. -/
lemma nonneg (e : ℤ) : 0 ≤ bpow β e := le_of_lt (pos β e)

/-- Base powers are never zero. -/
lemma ne_zero (e : ℤ) : bpow β e ≠ 0 := ne_of_gt (pos β e)

/-- Exponent addition law: $\beta^{e_1+e_2}=\beta^{e_1}\beta^{e_2}$. -/
lemma add_exp (e1 e2 : ℤ) : bpow β (e1 + e2) = bpow β e1 * bpow β e2 := by
  simp [bpow, zpow_add₀ (Numerics.Radix.ne_zero β)]

/-- Negating the exponent inverts the base power:
$\beta^{-e}=(\beta^e)^{-1}$. -/
lemma neg_exp (e : ℤ) : bpow β (-e) = (bpow β e)⁻¹ := by
  simp [bpow, zpow_neg]

/-- Exponent subtraction corresponds to division of radix powers. -/
lemma sub_exp (e₁ e₂ : ℤ) :
    bpow β (e₁ - e₂) = bpow β e₁ / bpow β e₂ := by
  simp [bpow, zpow_sub₀ (Numerics.Radix.ne_zero β)]

end bpow

/--
Interpret a `FloatRep` as the real number $m\beta^e$.
-/
noncomputable def toReal {β : Numerics.Radix} (f : FloatRep β) : ℝ :=
  f.mantissa * bpow β f.exponent

namespace toReal

variable {β : Numerics.Radix} (f : FloatRep β)

/-- `toReal` is zero iff the mantissa is zero (since $\beta^e\ne0$). -/
@[simp, grind =] lemma zero_iff : toReal f = 0 ↔ f.mantissa = 0 := by
  simp [toReal, bpow.ne_zero β f.exponent]

end toReal

/--
Magnitude in base $\beta$ of a real number.

This matches the usual definition
$\operatorname{mag}(x)=\lfloor\log_\beta|x|\rfloor+1$ for $x\ne0$, and $0$ for $x=0$.
It is the bridge between a real input $x$ and the exponent-selection function `fexp`.
-/
noncomputable def magnitude (β : Numerics.Radix) (x : ℝ) : ℤ :=
  if x = 0 then 0
  else
    let base_mag := ⌊Real.log (abs x) / Real.log β.toReal⌋ + 1
    base_mag

/--
Validity predicate for exponent-selection functions.

This is the exponent-validity condition used by Flocq. Properties that are not consequences of
validity, such as monotonicity, are separate classes so generic results do not acquire unnecessary
hypotheses.
-/
class ValidExp (fexp : ℤ → ℤ) : Prop where
  /-- Exponent compatibility at successive magnitudes and below a negligible exponent. -/
  flocq_valid : ∀ k : ℤ,
    (fexp k < k → fexp (k + 1) ≤ k) ∧
    (k ≤ fexp k → fexp (fexp k + 1) ≤ fexp k ∧ ∀ l, l ≤ fexp k → fexp l = fexp k)

/-- Exponent-selection functions that preserve order. -/
class MonotoneExp (fexp : ℤ → ℤ) : Prop where
  /-- Increasing the magnitude cannot decrease the selected exponent. -/
  monotone : ∀ k1 k2 : ℤ, k1 ≤ k2 → fexp k1 ≤ fexp k2

/-- Optional local growth bound used by selected numerical estimates. -/
class BoundedExpGrowth (fexp : ℤ → ℤ) : Prop where
  /-- Successive magnitudes select exponents differing by at most one. -/
  boundedGrowth : ∀ k : ℤ, |fexp (k + 1) - fexp k| ≤ 1

/-- A witness that the format has a lower exponent region, in Flocq's sense. -/
def IsNegligibleExp (fexp : ℤ → ℤ) (n : ℤ) : Prop :=
  n ≤ fexp n

/--
Select a witness $n\le\mathtt{fexp}(n)$ when the format has one. Unbounded formats such as FLX
return
`none`; lower-bounded formats such as FLT return `some n`.
-/
noncomputable def negligibleExp (fexp : ℤ → ℤ) : Option ℤ := by
  classical
  exact if h : ∃ n, IsNegligibleExp fexp n then some (Classical.choose h) else none

/-- A selected negligible exponent satisfies $n\le\mathtt{fexp}(n)$. -/
theorem negligibleExp_spec {fexp : ℤ → ℤ} {n : ℤ}
    (h : negligibleExp fexp = some n) : IsNegligibleExp fexp n := by
  classical
  unfold negligibleExp at h
  split at h
  next hex =>
    have hn : Classical.choose hex = n := Option.some.inj h
    rw [← hn]
    exact Classical.choose_spec hex
  next _ => simp at h

/-- A format has no selected negligible exponent exactly when no negligible exponent exists. -/
theorem negligibleExp_eq_none_iff (fexp : ℤ → ℤ) :
    negligibleExp fexp = none ↔ ¬∃ n, IsNegligibleExp fexp n := by
  classical
  unfold negligibleExp
  split <;> simp_all

/--
Canonical exponent (`cexp` in Flocq terminology).

Apply `fexp` to the input's magnitude; at zero this gives `fexp 0`. No validity assumption
is needed to define the canonical exponent.
-/
noncomputable def cexp (β : Numerics.Radix) (fexp : ℤ → ℤ) (x : ℝ) : ℤ :=
  fexp (magnitude β x)

/-- A float representation is canonical when its stored exponent is the exponent selected for its
  value. -/
def Canonical (β : Numerics.Radix) (fexp : ℤ → ℤ)
    (f : FloatRep β) : Prop :=
  f.exponent = cexp β fexp (toReal f)

/--
Scaled mantissa $x\beta^{-\operatorname{cexp}(x)}$.

Intuitively: rescale `x` so that rounding “happens around exponent 0”, which is where `rnd` acts.
-/
noncomputable def scaledMantissa (β : Numerics.Radix) (fexp : ℤ → ℤ) (x :
  ℝ) : ℝ :=
  x * bpow β (-cexp β fexp x)

/--
Generic format predicate (Flocq-style).

This says that $x$ is exactly representable in the format picked out by $\beta$ and `fexp`.
One way to read it is: the scaled mantissa is an integer (so there is no rounding error).
-/
def genericFormat (β : Numerics.Radix) (fexp : ℤ → ℤ) (x : ℝ) : Prop :=
  x =
    toReal (β := β)
      { mantissa := ⌊scaledMantissa β fexp x⌋
      , exponent := cexp β fexp x
      }

/--
Unit in the last place (ULP) associated with $x$ and the format selected by `fexp`.

This is the scale of the “one ulp” step at the exponent selected by `cexp`. For round-to-nearest,
many standard bounds have the shape
$|\operatorname{round}(x)-x|\le\operatorname{ulp}(x)/2$.

At zero, a negligible exponent determines the spacing when one exists; otherwise the ULP is zero.
-/
noncomputable def ulp (β : Numerics.Radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  if x = 0 then
    match negligibleExp fexp with
    | some n => bpow β (fexp n)
    | none => 0
  else bpow β (cexp β fexp x)

namespace ulp

variable (β : Numerics.Radix) (fexp : ℤ → ℤ)

/--
`ulp` is always nonnegative.

Informally: an ulp is a step size on a real grid, so it cannot be negative.
-/
lemma nonneg (x : ℝ) : 0 ≤ ulp β fexp x := by
  by_cases hx : x = 0
  · simp [ulp, hx]
    split <;> simp [bpow.nonneg]
  · simp [ulp, hx, bpow.nonneg]

/--
`ulp` is strictly positive away from zero.

If $x\ne0$, the exponent selection $\operatorname{cexp}(x)$ picks a power of $\beta$, which is
strictly positive.
-/
lemma pos_of_ne_zero (x : ℝ) (hx : x ≠ 0) : 0 < ulp β fexp x := by
  simp [ulp, hx, bpow.pos]

/-- The ULP at zero is determined by the format's negligible exponent, when one exists. -/
@[simp] lemma zero :
    ulp β fexp (0 : ℝ) =
      match negligibleExp fexp with
      | some n => bpow β (fexp n)
      | none => 0 := by
  simp [ulp]

/--
Away from zero, `ulp` is the base grid step $\beta^{\operatorname{cexp}(x)}$.
-/
@[simp] lemma of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    ulp β fexp x = bpow β (cexp β fexp x) := by
  simp [ulp, hx]

end ulp

end FloatLib.Floats.Formats.Flocq
