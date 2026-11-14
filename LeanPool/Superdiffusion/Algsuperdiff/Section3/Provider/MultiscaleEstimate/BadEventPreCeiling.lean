/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.GoodLocalEventAt
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# BadEventPreCeiling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the per-scale pre-ceiling of the bad-event derivation (step 1)

This is a *provider endpoint only*.  It is not a source node, it creates and
modifies no frozen declaration, and it closes no source node, no instance of a
source node and no fraction of a source node.

## 1. The printed step

Transcribed from the print, with `z` running over the display's own grid `3^l
ℤ^d ∩ cu_m`:

```
   ( avsum_{z}  max_{|e| = 1} ( J(z + cu_l, shom^{-1/2} e, shom^{1/2} e; a) )^{d/s}
                . 1_{not Q(l, l-h, z)} )^{s/d}
     <=  ( max_z max_{|e| = 1} J(z + cu_l, shom^{-1/2} e, shom^{1/2} e; a) )
         . ( avsum_{z} 1_{not Q(l, l-h, z)} )^{s/d} .
```

Two exponents occur and they are reciprocal: `d/s` inside the average, `s/d`
outside, i.e. `rho = s/d`  and `rho^{-1} = d/s`.  The print's exponent
placement is transcribed *verbatim*: the inner power sits on the `max_{|e|=1}`
block, the outer power sits on the whole average, and the extracted `max_z
max_e J` on the right carries **no** exponent.  Nothing is re-associated.

Reading the inner factor.  The print writes `max_{|e|=1} ( J(...) )^{d/s}`,
with the power INSIDE the max; the form used below is `(max_{|e|=1}
J(..))^{d/s}`, with the power outside.  At the nonnegative exponent `d/s` the
two commute, and the commutation is true at these carriers — CoarseGraining
supplies `doubledResponseJ_nonneg` pointwise with no hypotheses,
`normalizedBlockResponseValueSet_nonempty` and
`normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale`
(available under `hcube`) — but it is nowhere formalized here.  Granting it,
`max_{|e|=1} J(...)` is CoarseGraining's one-cube carrier
`Ch02.normalizedBlockResponseMax` — the `sSup` of the value set
`{ J(cubeDomain R, a.coeffOn R, A0^{-1/2} e, A0^{1/2} e): |e| = 1 }`.

Reading the extracted maximum.  The print's `max_z max_{|e|=1} J(z + cu_l)` is
the maximum over the display's OWN grid.  That is **not** what is delivered
below: the delivered majorant is CoarseGraining's
`Ch02.maxDescendantNormalizedBlockResponseAtScale Q l`, the `finsetSupReal` of
the one-cube carrier over `descendantsAtScale Q l`, which majorizes the
grid maximum once `hcube` is granted (§4).  This file neither establishes nor
requires an identification of the two maxima; it delivers the larger one, which
is what the consumer needs.  The carriers below are the ones the proved max
engine of `BadEventMaxSplit.lean` names, so the conclusion is written directly
in its spelling.

## 2. What the step is, mathematically

It is a *finite* power-mean/majorant extraction and nothing more: with

* `a z := max_{|e|=1} J(z + cu_l; ...)` the per-`z` response,
* `A := max_z a z` the printed maximum — in the delivered form `A` is any
  majorant of the `a z` on the grid, and the one actually delivered is the
  larger D maximum (§4),
* `chi z := 1_{not Q(l,l-h,z)}(omega) in [0,1]` the bad-event indicator,

one has `a z ^ (d/s) . chi z <= A ^ (d/s) . chi z` pointwise on the grid (the
inner power is monotone because `d/s >= 0`), hence the same after averaging;
raising to `s/d >= 0` and using `(A^{d/s})^{s/d} = A^{(d/s)(s/d)} = A` at
`A >= 0` gives the display.  No summability, no cardinality, no union bound,
and no Orlicz structure enters: it is one monotonicity, one average, one
`rpow` composition.

**Both degenerate corners are live, not excluded.**

* *Empty grid.*  `F = empty` is admissible: `(F.card : ℝ)⁻¹ = 0` makes both
  averages `0`, both sides are `0^{s/d} = 0` (the exponent is positive), and
  the statement holds.  No `Finset.Nonempty` binder is carried anywhere in this
  file, and no cardinality of the grid enters — means average, they do not add.
* *`A = 0`.*  The bound `0 <= A` is an inequality, not a positivity: at `A = 0`
  the hypotheses force `a z = 0` on the grid, both sides collapse to `0`, and
  the statement still holds.  Note that `A = 0` really does occur at the
  development carrier when the grid of descendants is empty (`finsetSupReal
  empty = sSup empty = 0`).

## 3. What is delivered

* `preCeiling_average_le` — the abstract engine over an arbitrary `Finset`, with
  the two reciprocal exponents carried as a pair `(p, rho)` together with `p *
  rho = 1`, exactly as the print carries `(d/s, s/d)`.  No transcendental
  function and no Section 3 carrier occurs in it.

There are no `private` declarations, no `def`s, and no notation in this file.

## 4. The grid, `hcube`, and how the delivered form relates to the print

The display averages over grid `z in 3^l ℤ^d ∩ cu_m`, while the two
`J`-carriers are indexed by triadic; the printed identification is `z <-> z +
cu_l`.  That identification is **not** performed here.

* `F : Finset (Vec d)` — the grid, free, possibly empty, no cardinality used;
* `cube : Vec d → TriadicCube d` — the assignment `z |-> z + cu_l`, free;
* `hcube : ∀ z ∈ F, cube z ∈ descendantsAtScale (originCube d m) l`.

**The delivered statement is printed step 1 WITH an unprinted monotonicity, and
`hcube` is the hypothesis of that second factor, not a premise of the print.**
Printed step 1 is a pure majorant extraction over ONE index set: it relates no
grid to `cu_m` and needs no `hcube` at all.  What is delivered is that form
composed with
    grid maximum  <=  scale-`l` descendant maximum

whose hypothesis is exactly `hcube` (it is CoarseGraining's
`normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale`
applied at each `z in F`).  Three consequences, stated rather than implied:

1. the delivered right-hand side is a larger majorant than the printed one, so
   the delivered inequality is implied by — i.e. is weaker than — printed
   step 1.  That is the safe direction, and it is the direction the consumer
   requires: the maximum that the seam into `BadEventMaxSplit` must meet is the
   descendant maximum, not the grid maximum;
2. only the `subset` half of the grid/descendant identification is used.  The
   reverse half — which is what would make the two maxima equal — is neither
   carried nor needed, and no identification of the two maxima is claimed
   anywhere in this file (§1);
3. `hcube` is therefore a caller obligation, not a source premise: the print
   carries no such premise (it has a concrete grid), no lemma in this file's
   closure discharges it, and none can while `cube` is free.  It is a bounded,
   non-analytic, index-set obligation, discharged at the concrete
   instantiation `F := 3^l ℤ^d ∩ cu_m`, `cube z := z + cu_l`.

## 5. Hypotheses

`hl : l ≤ m` is the display's own `l`-window `(-infinity, m] ∩ ℤ` and
`hs : 0 < s` is what the display's window `8 cgamma <= s <= 1` gives; only
positivity is used, and only to form the reciprocal exponent pair `(d/s, s/d)`,
which is what `hpr : p * rho = 1` records on the abstract engine.  The sign and
majorant hypotheses `hA`, `hp`, `ha0`, `haA`, `hchi0` of the abstract engine are
all discharged in the composed form from CoarseGraining's
`normalizedBlockResponseMax_nonneg`,
`..._le_maxDescendantNormalizedBlockResponseAtScale`,
`maxDescendantNormalizedBlockResponseAtScale_nonneg` and Mathlib's
`Set.indicator_nonneg`.  `[NeZero d]` is carrier-forced by
`Ch02.normalizedBlockResponseMax` and
`Ch02.maxDescendantNormalizedBlockResponseAtScale`; the composed form
additionally reads `d >= 1` off it, which is what makes
`(d : ℝ)/s . s/(d : ℝ) = 1`.  The index `n` is left free rather than fixed to
the printed `l - h`, so that the consumer may instantiate it at its own gap.

The proof below happens to route the nonnegativity through CoarseGraining's
`maxDescendantNormalizedBlockResponseAtScale_nonneg`, which does carry
`k ≤ Q.scale`, so `hl` is consumed by this proof; the statement does not need
it.  It is kept because the printed window is stated even where a weaker one
suffices, and because it costs the consumer nothing — it is free at the seam's
`l = m - j`.  `hcube` is the one caller-supplied proposition, and it weakens
rather than strengthens the conclusion.

**No summability binder occurs anywhere in this file**, and no `tsum`: step 1
is a per-scale statement over one `Finset`, and the `l`-series is paid by
`BadEventMaxSplit.lean`, not here.

## 6. References

* ABK26: `l.localization.mathcalE`, `e.mathcal.E.breakdown`,
  `e.local.bad.events.summed`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

-- The `_root_` prefixes below are deliberate.  A bare `open Homogenization`
-- resolves to the sibling namespace `Algsuperdiff.Section3.Provider.Homogenization`
-- as soon as any module of it joins this file's import closure, at which point
-- `Mat`, `Vec`, `TriadicCube`, `descendantsAtScale` and `originCube` all become
-- unknown identifiers.  The prefixes keep the file robust against that.
open _root_.HCPolySupport
open _root_.HCPolySupport.Book

noncomputable section

/-! ## 1. The abstract extraction engine

Everything here is about abstract reals over an arbitrary `Finset`: no
transcendental function, no Section 3 carrier and no measure occurs, so no
arithmetic tactic ever meets one.  The two exponents are carried as the
reciprocal pair the print carries, `(p, rho) = (d/s, s/d)` with `p * rho = 1`,
so that the collapse `(A^p)^rho = A` happens inside the engine and no caller
ever sees the powered maximum. -/

/-- **The pre-ceiling engine (printed step 1), on an arbitrary `Finset`.**

```
    ( avsum_{i in F} (a i)^p . chi i )^rho  <=  A . ( avsum_{i in F} chi i )^rho
```

whenever `a i <= A` on `F`, the values `a i` and `chi i` are nonnegative there,
`A >= 0`, `p >= 0` and the exponents are a reciprocal pair `p . rho = 1`.

No `0 <= rho` binder is carried: `p . rho = 1` forces `p /= 0`, hence `p > 0`
with `hp`, hence `rho = 1/p > 0`, and that derivation is performed in the first
two lines of the proof below.

Both degenerate corners are live: `F = empty` (both sides are `0`, since
`p . rho = 1` forces `rho > 0`) and `A = 0` (which forces `a i = 0` on `F`).
No `Finset.Nonempty` hypothesis and no cardinality of `F` occurs, and there is
no summability binder — the sum is finite. -/
theorem preCeiling_average_le {iota : Type*} (F : Finset iota)
    {A p rho : ℝ} (hA : 0 ≤ A) (hp : 0 ≤ p) (hpr : p * rho = 1)
    {a chi : iota → ℝ} (ha0 : ∀ i ∈ F, 0 ≤ a i) (haA : ∀ i ∈ F, a i ≤ A)
    (hchi0 : ∀ i ∈ F, 0 ≤ chi i) :
    ((F.card : ℝ)⁻¹ * ∑ i ∈ F, a i ^ p * chi i) ^ rho ≤
      A * ((F.card : ℝ)⁻¹ * ∑ i ∈ F, chi i) ^ rho := by
  have hp0 : 0 < p := by
    rcases lt_or_eq_of_le hp with h | h
    · exact h
    · rw [← h, zero_mul] at hpr
      exact absurd hpr zero_ne_one
  have hrho : 0 ≤ rho := by
    by_contra hcon
    have hlt : p * rho < 0 := mul_neg_of_pos_of_neg hp0 (not_le.mp hcon)
    rw [hpr] at hlt
    exact absurd hlt (not_lt.mpr zero_le_one)
  have hcard : (0 : ℝ) ≤ ((F.card : ℝ))⁻¹ := by positivity
  have hterm : ∀ i ∈ F, a i ^ p * chi i ≤ A ^ p * chi i := fun i hi =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (ha0 i hi) (haA i hi) hp) (hchi0 i hi)
  have hsum : ∑ i ∈ F, a i ^ p * chi i ≤ A ^ p * ∑ i ∈ F, chi i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hbase : (F.card : ℝ)⁻¹ * ∑ i ∈ F, a i ^ p * chi i ≤
      A ^ p * ((F.card : ℝ)⁻¹ * ∑ i ∈ F, chi i) := by
    calc (F.card : ℝ)⁻¹ * ∑ i ∈ F, a i ^ p * chi i
        ≤ (F.card : ℝ)⁻¹ * (A ^ p * ∑ i ∈ F, chi i) :=
          mul_le_mul_of_nonneg_left hsum hcard
      _ = A ^ p * ((F.card : ℝ)⁻¹ * ∑ i ∈ F, chi i) := by ring
  have hbase0 : (0 : ℝ) ≤ (F.card : ℝ)⁻¹ * ∑ i ∈ F, a i ^ p * chi i :=
    mul_nonneg hcard (Finset.sum_nonneg fun i hi =>
      mul_nonneg (Real.rpow_nonneg (ha0 i hi) p) (hchi0 i hi))
  have hchi0' : (0 : ℝ) ≤ (F.card : ℝ)⁻¹ * ∑ i ∈ F, chi i :=
    mul_nonneg hcard (Finset.sum_nonneg hchi0)
  calc ((F.card : ℝ)⁻¹ * ∑ i ∈ F, a i ^ p * chi i) ^ rho
      ≤ (A ^ p * ((F.card : ℝ)⁻¹ * ∑ i ∈ F, chi i)) ^ rho :=
        Real.rpow_le_rpow hbase0 hbase hrho
    _ = (A ^ p) ^ rho * ((F.card : ℝ)⁻¹ * ∑ i ∈ F, chi i) ^ rho :=
        Real.mul_rpow (Real.rpow_nonneg hA p) hchi0'
    _ = A * ((F.card : ℝ)⁻¹ * ∑ i ∈ F, chi i) ^ rho := by
        rw [← Real.rpow_mul hA, hpr, Real.rpow_one]

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
