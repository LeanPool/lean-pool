/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStabilityEndpoints
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryGradH
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundarySplit

/-!
# BoundaryClauseSkeleton

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary Caccioppoli's `L²` object, reduced to the escalated scalar

```text
  S₀ = |(u − h)_{c + □_{n+2}}| ,   c = wellPlacedCentre x m (n+2) ,
```

This module carries out the composition **parametrized by that scalar**: with
`S` an abstract bound for it, the boundary Caccioppoli's `L²` object splits
into three frozen shapes plus `S`,

```text
  ‖u(·+c) − V‖_{L²(□_{n+2})}
      ≤ 2·3^d ‖u − (u)_{W'}‖_{L²(W')}          (the FIRST leg)
        + C(d)·3^{n+2}·3^d Σᵢ ‖∂ᵢh‖_{L²(W')}    (the FIFTH leg shape)
        + S                                       (the escalated scalar)
        + ‖σ‖_{L²(□_{n+2})} ,                     (the σ leg)
```

`W' = (z+□_{n+3}) ∩ □_m`, `σ = V − h(·+c) ∈ H¹₀(□_{n+2})`.

## The disclosed slot

`S` enters the conclusion **additively, in its own leg**, at coefficient `1`.
That is the honest reading: the scalar is an additive normalization defect of the
`L²` object, not a multiplier of any datum.  A producer supplying
`hmean` at some `S` together with a bound of `S` by the frozen bracket closes the
composition at twice the constant; a producer supplying `S = 0` closes it by
`add_zero`.

## What remains after this module

Exactly two inputs, both already named:

2. **the `σ`-leg choice** — `BoundaryGradH` section 4's fork, i.e. whether the
   `ν`-division is authorized.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2;
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Jensen in the normalized carrier -/

/-! ## 2. The mean-zero Poincaré on the boundary covering cube -/

/-- **The mean-subtracted `L²` Poincaré inequality on the covering cube.**

The covering cube `c + □_{n+2}` is an axis cube of side `3^{n+2}`, so
CoarseGraining's scaled mean-zero Poincaré applies verbatim; the normalization
cancels between the two sides because the same cube carries both. -/
theorem eLpNorm_sub_average_coveringCube_le_meanZeroPoincare {n m : ℤ} {x : Vec d}
    (hnm : n + 2 ≤ m) (h : H1Function (openCubeSet (originCube d m))) :
    (eLpNorm (fun y => h.toFun y -
          volumeAverage ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
            openCubeSet (originCube d (n + 2))) h.toFun) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
            openCubeSet (originCube d (n + 2))))).toReal ≤
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y' => wellPlacedCentre x m (n + 2) + y') ''
                openCubeSet (originCube d (n + 2))))).toReal := by
  classical
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cc : Set (Vec d) :=
    (fun y' => c + y') '' openCubeSet (originCube d (n + 2)) with hcc
  set Lc : ℝ := (3 : ℝ) ^ (n + 2) with hLc
  set A : Vec d := fun i => c i - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 2) with hA
  have hLpos : (0 : ℝ) < Lc := zpow_pos (by norm_num) _
  have hcube : cc = axisCube A Lc := by
    rw [hcc, hA, hLc]
    exact image_add_openCubeSet_eq_axisCube c (n + 2)
  have hccsub : cc ⊆ openCubeSet (originCube d m) := by
    rw [hcc]
    exact image_add_wellPlacedCentre_subset_openCubeSet x hnm
  have hsubA : axisCube A Lc ⊆ openCubeSet (originCube d m) := by
    rw [← hcube]
    exact hccsub
  -- CoarseGraining's scaled mean-zero Poincaré on the axis realization
  have hraw : (eLpNorm (fun y => h.toFun y - integralAverage cc h.toFun) 2
        (volumeMeasureOn cc)).toReal ≤
      unitMeanZeroPoincareConst d * Lc *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2 (volumeMeasureOn cc)).toReal := by
    rw [hcube]
    have hpo := scaled_meanZero_poincare A hLpos
      (h.restrict (isOpen_axisCube A Lc) hsubA)
    have hfun : ((h.restrict (isOpen_axisCube A Lc) hsubA).subAverage).toFun =
        fun y => h.toFun y - integralAverage (axisCube A Lc) h.toFun := by
      funext y
      exact H1Function.subAverage_apply _ y
    rwa [hfun] at hpo
  -- the normalization cancels
  have hiv : integralAverage cc h.toFun = volumeAverage cc h.toFun := rfl
  rw [hiv] at hraw
  have hrestrict : volumeMeasureOn cc = volume.restrict cc := rfl
  rw [hrestrict] at hraw
  simp only [eLpNorm_normalizedVolumeMeasureOn_eq, ENNReal.toReal_mul]
  have hr : (0 : ℝ) ≤ (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal := ENNReal.toReal_nonneg
  calc (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
        (eLpNorm (fun y => h.toFun y - volumeAverage cc h.toFun) 2
          (volume.restrict cc)).toReal
      ≤ (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
          (unitMeanZeroPoincareConst d * Lc *
            ∑ i : Fin d,
              (eLpNorm (fun y => h.grad y i) 2 (volume.restrict cc)).toReal) :=
        mul_le_mul_of_nonneg_left hraw hr
    _ = unitMeanZeroPoincareConst d * Lc *
          ∑ i : Fin d,
            (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
              (eLpNorm (fun y => h.grad y i) 2 (volume.restrict cc)).toReal := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring

/-! ## 3. The covering-cube transport, in real form -/

theorem toReal_eLpNorm_coveringCube_le_anchorWindow {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    {f : Vec d → ℝ}
    (hfin : eLpNorm f 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤) :
    (eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => wellPlacedCentre x m (n + 2) + y) ''
            openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d *
        (eLpNorm f 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  have hbase := eLpNorm_coveringCube_le_anchorWindow hnm hx hgeom f
  have hRne : ENNReal.ofReal ((3 : ℝ) ^ d) *
      eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hstep := ENNReal.toReal_mono hRne hbase
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep

/-! ## 4. The mean-control reduction -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
