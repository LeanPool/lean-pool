/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourGeneral
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryHonestRegated
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundFinal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerProducer
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddCompose

/-!
# EdBridgeStepFourDatumSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-4 bridge with the printed datum leg threaded through

`EdBridgeStepFourGeneral.excessDecay_stepFour_slot_general` runs the residue
chain against the join and delivers the Step-4 slot at every centre.  Its join
input is the two-leg one-step; this module runs the same chain against
the anchored one-step with the printed datum leg, whose
boundary disjunct carries its binders honestly and whose conclusion carries the
printed third leg

```text
   C_t(d) · (3^{n-k})^{1/2} · (boundaryDatumLegConst d C k · K_h) .
```

## The additive ride

One risk has to be excluded: the datum leg's fixed-`k` factor `3^{3k/2}` would
be fatal if the leg ever entered the bridge's **absorption inequality** — the `k₀`
selection of `exists_edBridgeStepGen`, which is what forces `k` large enough
that the contraction is `≤ ½·3^{-(k+1)/4}`.  It does not.  The machine witness
is the shape of the generalized recombination `edBridge_recombine_datum`: the
leg appears as a *single free real* `Leg` which

* occurs in exactly two places — the hypothesis `hmain` and the conclusion — both additively;
* occurs in **no** other hypothesis: not in `hgate` (the `δ`-absorption
  `Crem·(P·(Sq·B₁)) ≤ th₂`), not in `hcon` (the contraction absorption
  `Acon·Ejm1 ≤ th₁·Ej`), not in `hth` (`th₁ + th₂ ≤ th`), and not in `hBig`;
* is multiplied by nothing and compared with nothing.

Since `k₀` is chosen by `exists_edBridgeStepGen` from `Cs` alone — a statement this module does
not touch and whose proof mentions no datum object — the `3^{3k/2}` cannot interact with the
selection.  Concretely: `k₀` is fixed first, `k ≥ k₀` is arbitrary, and the leg's constant is
then evaluated at that `k`.  The leg is a `δ`-side summand, not an `E`-side coefficient.

## The consumption shape

`edBridgeDatumLeg_eq` rewrites the leg into's `A^h` shape exactly: at the
slot's own index `j = n+1`,

```text
   C_t(d)·(3^{n-k})^{1/2}·(C_bd(d,C,k)·K_h)  =  edBridgeDatumLegConst d C k · (3^{j/2} · K_h) ,
```

a constant times `3^{j/2}` times the same datum `K_h` the budget's `A^h_j` leg
carries.  So the leg is absorbed by **widening `A^h`'s constant**, not by
touching the `ε`-free flat slot `F` (which is the anchor's `K_hinf` leg).
measured this; the identity proves it.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Step 4.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The four-leg recombination: the datum leg rides additively -/

/-- **`EdBridgeStepFour.edBridge_recombine` with a fourth, purely additive leg.**

`Leg` occurs only in `hmain` and in the conclusion, in both cases as a bare
additive summand.  It touches neither the `δ`-gate `hgate` nor the contraction
absorption `hcon` nor the step budget `hth` — this is the machine form's "the
datum leg rides additively through the `k₀` selection". -/
theorem edBridge_recombine_datum
    {Elhs Acon Ejm1 Ej pj Big Rhat P Crem Sq B₁ B₂ th₁ th₂ th eps Wd Leg : ℝ}
    (hCrem : 0 ≤ Crem) (hSq : 0 ≤ Sq) (hP : 0 ≤ P) (hEj : 0 ≤ Ej)
    (hmain : Elhs ≤ Acon * Ejm1 + Crem * (P * (Sq * Big)) + Leg)
    (hBig : Big ≤ B₁ * Ej + B₂ * pj + Rhat)
    (hcon : Acon * Ejm1 ≤ th₁ * Ej)
    (hgate : Crem * (P * (Sq * B₁)) ≤ th₂)
    (heps : Crem * (P * (Sq * B₂)) = eps)
    (hWd : Crem * (P * (Sq * Rhat)) = Wd)
    (hth : th₁ + th₂ ≤ th) :
    Elhs ≤ th * Ej + eps * pj + (Wd + Leg) := by
  have hstep : Crem * (P * (Sq * Big)) ≤ Crem * (P * (Sq * (B₁ * Ej + B₂ * pj + Rhat))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBig hSq) hP) hCrem
  have hexp : Crem * (P * (Sq * (B₁ * Ej + B₂ * pj + Rhat)))
      = Crem * (P * (Sq * B₁)) * Ej + Crem * (P * (Sq * B₂)) * pj
        + Crem * (P * (Sq * Rhat)) := by ring
  rw [heps, hWd] at hexp
  have hgm : Crem * (P * (Sq * B₁)) * Ej ≤ th₂ * Ej := mul_le_mul_of_nonneg_right hgate hEj
  have hthm : (th₁ + th₂) * Ej ≤ th * Ej := mul_le_mul_of_nonneg_right hth hEj
  have hdis : (th₁ + th₂) * Ej = th₁ * Ej + th₂ * Ej := by ring
  linarith only [hmain, hstep, hexp, hcon, hgm, hthm, hdis]

/-! ## 2. The datum leg and its `A^h` shape -/

/-- The datum leg the bridge's slot carries, at the one-step's own scale `n`:
`C_t(d) · (3^{n-k})^{1/2} · (C_bd(d,Cs,k) · K_h)`. -/
def edBridgeDatumLeg (d : ℕ) (Cs : ℝ) (k : ℕ) (n : ℤ) (Kh : ℝ) : ℝ :=
  taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
    * (boundaryDatumLegConst d Cs k * Kh)

/-- The datum leg's constant once the slot's own `3^{j/2}` is factored out
(`j = n+1`): `C_t(d) · (3^{-(k+1)})^{1/2} · C_bd(d,Cs,k)`. -/
def edBridgeDatumLegConst (d : ℕ) (Cs : ℝ) (k : ℕ) : ℝ :=
  taylorContractionConst d * ((3 : ℝ) ^ (-((k : ℤ) + 1))) ^ (1 / 2 : ℝ)
    * boundaryDatumLegConst d Cs k

theorem edBridgeDatumLegConst_nonneg (d : ℕ) {Cs : ℝ} (hCs : 0 ≤ Cs) (k : ℕ) :
    0 ≤ edBridgeDatumLegConst d Cs k :=
  mul_nonneg (mul_nonneg (taylorContractionConst_nonneg d)
    (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _))
    (boundaryDatumLegConst_nonneg d hCs k)

/-- `(3^m)^{1/2} = 3^{m/2}` for an integer power. -/
theorem zpow_rpow_half_eq_rpow_div_two (m : ℤ) :
    ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ ((m : ℝ) / 2) := by
  rw [← Real.rpow_intCast (3 : ℝ) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- **The datum leg is exactly's `A^h_j` shape at `j = n+1`.**

`edBridgeDatumLeg d Cs k n K_h = edBridgeDatumLegConst d Cs k · (3^{j/2} · K_h)` — a constant
times `3^{j/2}` times the same datum `K_h` the budget's `A^h` leg carries.  So the new leg is
absorbed by widening `A^h`'s constant, not by touching the `ε`-free flat slot. -/
theorem edBridgeDatumLeg_eq (d : ℕ) (Cs : ℝ) (k : ℕ) (n : ℤ) (Kh : ℝ) :
    edBridgeDatumLeg d Cs k n Kh
      = edBridgeDatumLegConst d Cs k * ((3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) / 2) * Kh) := by
  have hsplit : ((3 : ℝ) ^ (-((k : ℤ) + 1))) ^ (1 / 2 : ℝ)
        * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) / 2)
      = ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) := by
    rw [zpow_rpow_half_eq_rpow_div_two, zpow_rpow_half_eq_rpow_div_two,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [edBridgeDatumLeg, edBridgeDatumLegConst, ← hsplit]
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
