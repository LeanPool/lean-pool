/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenEndAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SigmaBarBudget

/-!
# StepSevenSigmaBar

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d: the `σ` comparison at a generic constant

## The gap this module closes

The Step-7d chain hard-codes the printed comparison

```text
  e.shom.m.vs.shom.n :   σ_{n'}  ≤  2 σ_m
```
 at the literal constant `2` in five places along the Step-7d chain — the
data-leg merge, the merged and the pinned energy-density estimates, the end
chain and its narrowed form — while the only comparison proved here is
`Annular.SigmaBarBudget.sigmaBar_ratio_le_four`, i.e. the constant `4`.

The route is the generic-constant collapse pattern already used for `Ccol`:
generic-`Ccmp` siblings of the pinned theorems, leaving the pinned statements
untouched.

The printed `√2` becomes `√Ccmp`; at `Ccmp = 4` that is `2`.  The difference is
immaterial inside `C(d, c_*)` — the deviation that `StepSevenEndAssembly`'s
docstring already describes.

## What `sigmaBar_ratio_le_four` actually gives

`Annular.sigmaBar_ratio_le_four M hS (hnm : n - 2 ≤ m) (hm : m ≤ m0)` reads
`σ_m^{-1}·σ_{n-2} ≤ 4`.  Re-indexed at `n := n' + 2` it is exactly `σ_{n'} ≤
4 σ_m` under `n' ≤ m ≤ m₀` — no adjacency and no plateau hypothesis.

## References

* ABK26, `e.energy.density.estimate`; the assembly.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The proved comparison, in the chain's own slot shape -/

/-- **`e.shom.m.vs.shom.n` at the proved constant `4`.**

`Annular.sigmaBar_ratio_le_four` in the multiplicative form the Step-7d chain
consumes:

```text
  σ_{n'}  ≤  4 σ_m          for  n' ≤ m ≤ m₀ .
```

Derived from conjunct 1 of the frozen Section-3 `inductionState` at the two
scales alone — no adjacency. -/
theorem sigmaBar_le_four_mul_sigmaBar (M : ABKModel d) {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    {n' m : ℤ} (hnm : n' ≤ m) (hm : m ≤ m0) :
    (Annealed.sigmaBar M n' : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) := by
  have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hidx : (n' + 2) - 2 = n' := by ring
  have hratio := Annular.sigmaBar_ratio_le_four M hS (n := n' + 2) (m := m)
    (by linarith only [hnm]) hm
  rw [hidx] at hratio
  have hmul := mul_le_mul_of_nonneg_left hratio hsm.le
  have hcancel : (Annealed.sigmaBar M m : ℝ) *
      (((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M n' : ℝ)) =
      (Annealed.sigmaBar M n' : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  linarith only [hmul]

/-! ## 2. The data-leg collapse, generic in `Ccmp` -/

/-- **The data-leg merge at a generic comparison constant**.

```text
  √σ_{n'} · W · (σ_m^{-1}G + H)  ≤  √Ccmp · W · ((√σ_m)^{-1}G + √σ_m·H) .
```

At `Ccmp := 2` this is the printed data-leg merge verbatim (machine-checked); at
`Ccmp := 4` it is the proved envelope's own comparison, at cost `2`. -/
theorem stepSevenDataLeg_merge_gen {shomNp shomM Ccmp W G H : ℝ} (hshomM : 0 < shomM)
    (hCcmp : 0 ≤ Ccmp) (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM) :
    Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) ≤
      Real.sqrt Ccmp * (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) := by
  have hstep : Real.sqrt shomNp ≤ Real.sqrt Ccmp * Real.sqrt shomM := by
    calc Real.sqrt shomNp ≤ Real.sqrt (Ccmp * shomM) := Real.sqrt_le_sqrt hcomp
      _ = Real.sqrt Ccmp * Real.sqrt shomM := Real.sqrt_mul hCcmp shomM
  have hinv : Real.sqrt shomM * shomM⁻¹ = (Real.sqrt shomM)⁻¹ := by
    have hsq : Real.sqrt shomM * Real.sqrt shomM = shomM := Real.mul_self_sqrt hshomM.le
    field_simp
    linarith only [hsq]
  have hnn : 0 ≤ W * (shomM⁻¹ * G + H) := by
    have : 0 ≤ shomM⁻¹ * G + H :=
      add_nonneg (mul_nonneg (inv_nonneg.mpr hshomM.le) hG) hH
    exact mul_nonneg hW this
  have h1 : Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) ≤
      (Real.sqrt Ccmp * Real.sqrt shomM) * (W * (shomM⁻¹ * G + H)) :=
    mul_le_mul_of_nonneg_right hstep hnn
  have h2 : (Real.sqrt Ccmp * Real.sqrt shomM) * (W * (shomM⁻¹ * G + H)) =
      Real.sqrt Ccmp * (W * ((Real.sqrt shomM * shomM⁻¹) * G + Real.sqrt shomM * H)) := by
    ring
  rw [hinv] at h2
  linarith only [h1, h2.ge, h2.le]

/-! ## 3. `e.energy.density.estimate` with the printed bracket, generic in `Ccmp` -/

/-- **The merged energy-density estimate at a generic comparison constant.**

`stepSevenEnergyDensityEstimate_compose` (already generic in `Ccmp`) followed
by `stepSevenDataLeg_merge_gen` at the SAME comparison, so `e.shom.m.vs.shom.n`
is still consumed exactly once.  At `Ccmp := 2` this is the pinned parent
verbatim. -/
theorem stepSevenEnergyDensityEstimate_merged_gen {Cg Cend Ccmp R34 R14 shomNp shomM
    gradLoc oscTrunc dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM)
    (hR34 : 0 ≤ R34) (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤ Cg * Real.sqrt shomNp * R34 * oscTrunc +
      Cg * R34 * (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hend : oscTrunc ≤ Cend * R14 *
      (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤ Cg * (Real.sqrt Ccmp * (Cend * R14)) * R34 *
        (gradM + Real.sqrt shomM⁻¹ * dataG) +
      Cg * R34 * (Real.sqrt Ccmp *
        (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hbase := stepSevenEnergyDensityEstimate_compose (Ccmp := Ccmp)
    (dataOsc := W * (shomM⁻¹ * G + H)) hCg hCcmp hshomM hR34
    hoscTrunc hcomp hgrad hend
  have hmerge := stepSevenDataLeg_merge_gen hshomM hCcmp hW hG hH hcomp
  have hpush : Cg * R34 * (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM) ≤
      Cg * R34 * (Real.sqrt Ccmp *
        (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCg hR34)
    linarith only [hmerge]
  linarith only [hbase, hpush]

/-- **The energy-density estimate at a generic comparison constant**, i.e.
`e.energy.density.estimate` at the printed exponent `3^{(1-α)(m-n)}` with the
printed data bracket and the `σ` comparison left as a parameter.  At `Ccmp:=
2` this is the pinned parent verbatim. -/
theorem stepSevenEnergyDensityEstimate_gen {alpha : ℝ} {n m : ℤ}
    {Cg Cend Ccmp shomNp shomM gradLoc oscTrunc dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM)
    (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤
      Cg * Real.sqrt shomNp *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hend : oscTrunc ≤
      Cend * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
        (Real.sqrt shomM⁻¹ * (gradM + Real.sqrt shomM⁻¹ * dataG))) :
    gradLoc ≤
      Cg * Real.sqrt Ccmp * Cend * Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
          (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt Ccmp *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hR34 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have h := stepSevenEnergyDensityEstimate_merged_gen hCg hCcmp hshomM hR34 hoscTrunc
    hW hG hH hcomp hgrad hend
  have hprod : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) =
      Real.rpow (3 : ℝ) (stepSixExponent alpha n m) := by
    rw [rpow_three_stepSixExponent_mul]
    norm_num
  have hrw : Cg * (Real.sqrt Ccmp *
        (Cend * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m))) *
      Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
      (gradM + Real.sqrt shomM⁻¹ * dataG) =
      Cg * Real.sqrt Ccmp * Cend *
        (Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m)) *
        (gradM + Real.sqrt shomM⁻¹ * dataG) := by ring
  rw [hrw, hprod] at h
  exact h

/-! ## 4. Step 7d end to end, generic in `Ccmp` -/

/-- **The Step-7d end chain at a generic comparison constant.**

The three proved displays of the node, chained, with `e.shom.m.vs.shom.n` a
parameter rather than the printed `2`.  Each hypothesis is literally the
conclusion of the named theorem, exactly as in the pinned parent, and at
`Ccmp:= 2` the statement IS the pinned parent. -/
theorem stepSevenEnd_chain_gen {alpha : ℝ} {n m : ℤ}
    {Cg Cmean Cemb Cbr Cout Ctr Ccmp shomNp shomM gradLoc oscTrunc oscLoc besovP1 besov
      dataM gradM dataG W G H : ℝ}
    (hCg : 0 ≤ Cg) (hCmean : 0 ≤ Cmean) (hCemb : 0 ≤ Cemb) (hCbr : 0 ≤ Cbr)
    (hCcmp : 0 ≤ Ccmp) (hshomM : 0 < shomM) (hoscTrunc : 0 ≤ oscTrunc)
    (hW : 0 ≤ W) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcomp : shomNp ≤ Ccmp * shomM)
    (hgrad : gradLoc ≤
      Cg * Real.sqrt shomNp *
          Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM))
    (hmean : oscTrunc ≤ Cmean * oscLoc)
    (hembed : oscLoc ≤ Cemb * besovP1)
    (hbridge : besovP1 ≤ Cbr * besov)
    (hpoincare : besov ≤
      Cout * (Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m)) *
        (Real.sqrt shomM⁻¹ * gradM + shomM⁻¹ * dataG)) :
    gradLoc ≤
      Cg * Real.sqrt Ccmp * (Cmean * Cemb * Cbr * Cout * Ctr) *
          Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
          (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
          (Real.sqrt Ccmp *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  have hshomMinv : (0 : ℝ) ≤ shomM⁻¹ := (inv_pos.mpr hshomM).le
  have hend0 := stepSevenOscillationEndpoint hCmean hCemb hCbr hshomMinv hmean hembed
    hbridge hpoincare
  have hassoc : Cmean * Cemb * Cbr *
      (Cout * (Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m))) =
      Cmean * Cemb * Cbr * Cout * Ctr *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by ring
  rw [hassoc] at hend0
  exact stepSevenEnergyDensityEstimate_gen hCg hCcmp hshomM hoscTrunc hW hG hH hcomp
    hgrad hend0

end

end Algsuperdiff.Section4.Provider.Regularity
