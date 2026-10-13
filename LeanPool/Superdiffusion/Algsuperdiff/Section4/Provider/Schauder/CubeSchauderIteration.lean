/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderFreezing

/-!
# CubeSchauderIteration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the de-randomized Campanato iteration

The recursion produced by the freezing step of `CubeSchauderFreezing` at the
triadic sub-scales of a cube has the shape

```text
  E (k+1) ≤ theta * E k + F * rho ^ k ,
```

where `E k` is the excess at scale `3^{-k}`, `theta` is the contraction factor
supplied by the interior (or reflected boundary) regularity of the frozen
harmonic comparison function, `rho = 3^{-alpha}` is the freezing gain, and `F`
is the `C^{0,alpha}` seminorm of the forcing.  Whenever `theta < rho < 1` the
iteration closes at the *forcing* rate:

```text
  E k ≤ (E 0 + F / (rho - theta)) * rho ^ k ,
```

which is exactly the Campanato bound whose Morrey dual is `∇u ∈ C^{0,alpha}`.

At the development's exponent `alpha = 1/2` the rate is `rho = 3^{-1/2}`, i.e.
the `3^{-k/2}` decay of the target `ZeroDatumCubeSchauder`.

Nothing in this module is an elliptic estimate: every declaration is an
unconditional statement about real sequences, plus the triadic dictionary that
identifies `rho ^ k` with the gauge `3^{-k/2}` of the frozen conclusion.

## Main results

* `excess_le_of_recursion` — the sharp induction: the recursion propagates the
  ansatz `theta ^ k * + (F / (rho - theta)) * rho ^ k`.
* `excess_le_geometric` — the Campanato form `E k ≤ ( + F/(rho-theta)) rho^k`.
* `excess_le_geometric_triadic_half` — the same at `rho = 3^{-1/2}`, spelled in
  the frozen gauge `Real.rpow 3 (-(k/2))`.
* `excess_le_of_recursion_of_le` — the degenerate-rate variant `theta ≤ rho`
  with a strict inequality only at the reabsorption step.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`, the display `e.Sch1a.1` and the dyadic geometric
  series preceding `e.Sch1a.2`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support

/-! ## 1. The one-step recursion, iterated -/

/-- **The Campanato induction.**

If a nonnegative sequence contracts at rate `theta` with a forcing remainder
decaying at the strictly larger rate `rho`, then it is dominated by the sum of
the two geometric profiles, with the forcing amplified by the *gap* `rho - theta`
only.  This is the reabsorption at the heart of `e.Sch1a.1`. -/
theorem excess_le_of_recursion {E : ℕ → ℝ} {theta rho F : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < rho) (hF : 0 ≤ F)
    (hstep : ∀ k, E (k + 1) ≤ theta * E k + F * rho ^ k) (k : ℕ) :
    E k ≤ theta ^ k * E 0 + F / (rho - theta) * rho ^ k := by
  have hgap0 : 0 < rho - theta := by linarith only [hgap]
  have hc0 : 0 ≤ F / (rho - theta) := div_nonneg hF hgap0.le
  have hrho0 : 0 ≤ rho := le_trans htheta hgap.le
  induction k with
  | zero =>
      simp only [pow_zero, one_mul, mul_one]
      linarith only [hc0]
  | succ n ih =>
      have hmul : theta * E n ≤ theta * (theta ^ n * E 0 + F / (rho - theta) * rho ^ n) :=
        mul_le_mul_of_nonneg_left ih htheta
      have habsorb : theta * (F / (rho - theta)) + F ≤ F / (rho - theta) * rho := by
        have hid : F / (rho - theta) * (rho - theta) = F := by
          field_simp
        have hexp : F / (rho - theta) * rho - theta * (F / (rho - theta))
            = F / (rho - theta) * (rho - theta) := by ring
        linarith only [hid, hexp]
      have hpow : (0 : ℝ) ≤ rho ^ n := pow_nonneg hrho0 n
      have hrem : theta * (F / (rho - theta) * rho ^ n) + F * rho ^ n
          ≤ F / (rho - theta) * rho ^ (n + 1) := by
        have hfac : theta * (F / (rho - theta) * rho ^ n) + F * rho ^ n
            = (theta * (F / (rho - theta)) + F) * rho ^ n := by ring
        have hgoal : F / (rho - theta) * rho ^ (n + 1)
            = (F / (rho - theta) * rho) * rho ^ n := by ring
        rw [hfac, hgoal]
        exact mul_le_mul_of_nonneg_right habsorb hpow
      have hlead : theta * (theta ^ n * E 0) = theta ^ (n + 1) * E 0 := by ring
      have hstepn := hstep n
      linarith only [hstepn, hmul, hrem, hlead]

/-- **The Campanato bound.**  The iterated recursion decays at the forcing rate
`rho`, with amplitude `E 0 + F / (rho - theta)`. -/
theorem excess_le_geometric {E : ℕ → ℝ} {theta rho F : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < rho) (hF : 0 ≤ F) (hE0 : 0 ≤ E 0)
    (hstep : ∀ k, E (k + 1) ≤ theta * E k + F * rho ^ k) (k : ℕ) :
    E k ≤ (E 0 + F / (rho - theta)) * rho ^ k := by
  have hgap0 : 0 < rho - theta := by linarith only [hgap]
  have hc0 : 0 ≤ F / (rho - theta) := div_nonneg hF hgap0.le
  have hmain := excess_le_of_recursion htheta hgap hF hstep k
  have hpowle : theta ^ k ≤ rho ^ k :=
    pow_le_pow_left₀ htheta hgap.le k
  have hlead : theta ^ k * E 0 ≤ rho ^ k * E 0 :=
    mul_le_mul_of_nonneg_right hpowle hE0
  have hexp : (E 0 + F / (rho - theta)) * rho ^ k
      = rho ^ k * E 0 + F / (rho - theta) * rho ^ k := by ring
  rw [hexp]
  linarith only [hmain, hlead]

/-! ## 2. The triadic gauge -/

/-! ## 3. The sup-over-scales form -/

end Algsuperdiff.Section4.Provider.Schauder
