/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseAssemblyBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapWindow

/-!
# ResidueCapWindowLegs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The scaled `L²` object and the Dirichlet energy legs, re-cut at the hinge

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

`ResidueCapWindow` re-cut the boundary covering-cube transports at the
**window hinge**

```text
  (W)   c + □_{n+2} ⊆ (z + □_{n+3}) ∩ □_m ,   c = wellPlacedCentre x m (n+2) ,
```

in place of the anchor's geometry binder `hgeom : x + □_n ⊆ (z+□_{n+1}) ∩ □_m`.
This module carries the same re-cut through the two consumers the boundary
assembly actually reads:

* `rpow_three_neg_mul_sqrt_coveringDifference_le_atWindow` — the boundary
  Caccioppoli's parent-`L²` object at the covering cube, scaled by the frame
  factor `3^{-(n+2)}`, priced onto the frozen clause's legs, the open scalar
  `S` and the datum pricing's zero-trace bound `R`;
* `dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow` —
  CoarseGraining's `dirichletEnergyWithRHSRHS` on the covering cube at the pin
  `r = s/2`, priced onto the frozen clause's third leg.

Their two chain steps are re-cut here as well, since the proved proofs consume
`hgeom` only through them:

* `toReal_eLpNorm_coveringCube_atWindow` — the real-valued `L²` transport;
* `normalizedL2On_coveringCube_sub_datum_le_meanControl_atWindow` and
  `normalizedL2On_coveringDifference_le_meanControl_atWindow` — the covering
  cube pricing of `‖u − h‖` modulo the scalar, and its composition with the
  same-boundary-data split.

Every conclusion is byte-identical to the proved one; each proved statement is
recovered by feeding `image_add_wellPlacedCentre_subset_anchorWindow hnm hx
hgeom` for `hcov`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2; `e.cg.RHS`, the Dirichlet
  energy display.
* The proved originals: `BoundaryClauseSkeleton.lean`,
  `CoarseBoundaryClause.lean`, `CoarseAssemblyBudget.lean`,
  `CoarseDirichletEnergy.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `L²` transport in real form, at the hinge -/

/-- **The real-valued `L²` transport onto the anchor's window, at the hinge.**

The re-cut of `toReal_eLpNorm_coveringCube_le_anchorWindow`. -/
theorem toReal_eLpNorm_coveringCube_atWindow {n m : ℤ} {x z : Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
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
  have hbase := eLpNorm_coveringCube_atWindow hcov f
  have hRne : ENNReal.ofReal ((3 : ℝ) ^ d) *
      eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hstep := ENNReal.toReal_mono hRne hbase
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep

/-! ## 2. The covering-cube pricing of `‖u − h‖`, at the hinge -/

/-- **The three legs of the parent-`L²` pricing, at the hinge.**

The re-cut of `normalizedL2On_coveringCube_sub_datum_le_meanControl`: on the
boundary covering cube the `L²` distance between the solution and its own
boundary datum is priced by the frozen clause's leg (mean-minimality and the
window transport of section 1), the frozen leg (the proved data Poincaré on `h`
alone), and the open scalar `S = |(u−h)_{cc}|` at coefficient `1`. -/
theorem normalizedL2On_coveringCube_sub_datum_le_meanControl_atWindow [NeZero d]
    {n m : ℤ} {x z : Vec d} {S : ℝ} (hnm : n + 2 ≤ m)
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (u hdat : H1Function (openCubeSet (originCube d m)))
    (hXfin : eLpNorm (fun y => u.toFun y -
        volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hHfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hmean : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - hdat.toFun y)| ≤ S) :
    normalizedL2On ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - hdat.toFun y) ≤
      (3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal +
        S +
        unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) := by
  classical
  -- the two hinge consumptions, taken before the abbreviations
  have htrans := toReal_eLpNorm_coveringCube_atWindow (x := x) (z := z) hcov
    (f := fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) hXfin
  have hcoordTrans : ∀ i : Fin d,
      (eLpNorm (fun y => hdat.grad y i) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => wellPlacedCentre x m (n + 2) + y) ''
            openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d *
        (eLpNorm (fun y => hdat.grad y i) 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
    intro i
    refine toReal_eLpNorm_coveringCube_atWindow (x := x) (z := z) hcov
      (f := fun y => hdat.grad y i) ?_
    refine ne_top_of_le_ne_top hHfin ?_
    exact eLpNorm_grad_coord_le_eLpNorm_grad hdat.grad i
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cc : Set (Vec d) :=
    (fun y => c + y) '' openCubeSet (originCube d (n + 2)) with hcc
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  have hccsub : cc ⊆ openCubeSet (originCube d m) := by
    rw [hcc, hc]
    exact image_add_wellPlacedCentre_subset_openCubeSet x hnm
  have hccpos : 0 < volume cc := by
    rw [hcc]
    exact lt_of_le_of_ne (zero_le : (0 : ℝ≥0∞) ≤ volume _)
      (Ne.symm (volume_image_add_openCubeSet_ne_zero c (originCube d (n + 2))))
  have hcctop : volume cc ≠ ⊤ := by
    rw [hcc, volume_image_add_openCubeSet]
    exact volume_openCubeSet_ne_top (originCube d (n + 2))
  have hmono : MeasureTheory.volume.restrict cc ≤
      MeasureTheory.volume.restrict (openCubeSet (originCube d m)) :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hccsub
  have : IsFiniteMeasure (MeasureTheory.volume.restrict cc) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hcctop
  -- the anchor's `H¹` data restricted to the covering cube
  have huL : MemLp u.toFun 2 (MeasureTheory.volume.restrict cc) :=
    u.memL2.mono_measure hmono
  have hhL : MemLp hdat.toFun 2 (MeasureTheory.volume.restrict cc) :=
    hdat.memL2.mono_measure hmono
  have huI : IntegrableOn u.toFun cc MeasureTheory.volume := huL.integrable (by norm_num)
  have huI2 : IntegrableOn (fun y => u.toFun y ^ 2) cc MeasureTheory.volume := by
    have h := huL.integrable_sq
    simpa [IntegrableOn] using h
  have huhL : MemLp (fun y => u.toFun y - hdat.toFun y) 2
      (MeasureTheory.volume.restrict cc) := huL.sub hhL
  have hconstL : ∀ b : ℝ, MemLp (fun _ : Vec d => b) 2
      (MeasureTheory.volume.restrict cc) := fun b => memLp_const b
  have huoscL : MemLp (fun y => u.toFun y - volumeAverage cc u.toFun) 2
      (MeasureTheory.volume.restrict cc) := huL.sub (hconstL _)
  have hhoscL : MemLp (fun y => hdat.toFun y - volumeAverage cc hdat.toFun) 2
      (MeasureTheory.volume.restrict cc) := hhL.sub (hconstL _)
  have huWL : MemLp (fun y => u.toFun y - volumeAverage W u.toFun) 2
      (MeasureTheory.volume.restrict cc) := huL.sub (hconstL _)
  -- the three-term decomposition
  have hsplit := normalizedL2On_sub_le_oscillation_add_meanGap_add_datumOscillation
    (W := cc) hccpos hcctop (u := u.toFun) (h := hdat.toFun) huoscL hhoscL
  -- (A) the oscillation leg: mean-minimality, then the hinge transport
  have hmin := normalizedL2On_sub_average_le_sub_const (W := cc) hccpos hcctop
    huI huI2 (volumeAverage W u.toFun)
  have hdictA : normalizedL2On cc (fun y => u.toFun y - volumeAverage W u.toFun) =
      (eLpNorm (fun y => u.toFun y - volumeAverage W u.toFun) 2
        (Support.normalizedVolumeMeasureOn cc)).toReal :=
    normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn hccpos hcctop huWL
  have hlegA : normalizedL2On cc (fun y => u.toFun y - volumeAverage cc u.toFun) ≤
      (3 : ℝ) ^ d *
        (eLpNorm (fun y => u.toFun y - volumeAverage W u.toFun) 2
          (Support.normalizedVolumeMeasureOn W)).toReal := by
    refine hmin.trans ?_
    rw [hdictA]
    exact htrans
  -- (C) the datum leg: the proved data Poincaré, then the per-coordinate transport
  have hdictC : normalizedL2On cc (fun y => hdat.toFun y - volumeAverage cc hdat.toFun) =
      (eLpNorm (fun y => hdat.toFun y - volumeAverage cc hdat.toFun) 2
        (Support.normalizedVolumeMeasureOn cc)).toReal :=
    normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn hccpos hcctop hhoscL
  have hpoin := eLpNorm_sub_average_coveringCube_le_meanZeroPoincare (x := x) hnm hdat
  have hsumTrans : ∑ i : Fin d,
      (eLpNorm (fun y => hdat.grad y i) 2
        (Support.normalizedVolumeMeasureOn cc)).toReal ≤
      (3 : ℝ) ^ d * ((d : ℝ) *
        (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn W)).toReal) := by
    calc ∑ i : Fin d, (eLpNorm (fun y => hdat.grad y i) 2
          (Support.normalizedVolumeMeasureOn cc)).toReal
        ≤ ∑ i : Fin d, (3 : ℝ) ^ d *
            (eLpNorm (fun y => hdat.grad y i) 2
              (Support.normalizedVolumeMeasureOn W)).toReal :=
          Finset.sum_le_sum fun i _ => hcoordTrans i
      _ = (3 : ℝ) ^ d * ∑ i : Fin d,
            (eLpNorm (fun y => hdat.grad y i) 2
              (Support.normalizedVolumeMeasureOn W)).toReal := by
          rw [Finset.mul_sum]
      _ ≤ (3 : ℝ) ^ d * ((d : ℝ) *
            (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn W)).toReal) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_toReal_eLpNorm_grad_coord_le hdat.grad hHfin
  have hPconst : (0 : ℝ) ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) := by
    have h1 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
    have h2 : (0 : ℝ) < (3 : ℝ) ^ (n + 2) := zpow_pos (by norm_num) _
    exact mul_nonneg h1 h2.le
  have hlegC : normalizedL2On cc (fun y => hdat.toFun y - volumeAverage cc hdat.toFun) ≤
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
        ((d : ℝ) * ((3 : ℝ) ^ d *
          (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn W)).toReal)) := by
    rw [hdictC]
    refine hpoin.trans ?_
    refine (mul_le_mul_of_nonneg_left hsumTrans hPconst).trans (le_of_eq ?_)
    ring
  -- the mean gap is the mean of the difference
  have hhI : IntegrableOn hdat.toFun cc MeasureTheory.volume := hhL.integrable (by norm_num)
  have havg : volumeAverage cc (fun y => u.toFun y - hdat.toFun y) =
      volumeAverage cc u.toFun - volumeAverage cc hdat.toFun := by
    unfold volumeAverage
    rw [MeasureTheory.integral_sub huI hhI]
    ring
  rw [havg] at hmean
  -- assemble
  linarith only [hsplit, hlegA, hlegC, hmean]

/-- **The parent-`L²` pricing, composed, at the hinge.**

The re-cut of `normalizedL2On_coveringDifference_le_meanControl`: the boundary
Caccioppoli's parent-`L²` object at the covering cube, priced onto the frozen
legs and the datum pricing's zero-trace leg, with the open scalar `S` threaded
additively at coefficient `1`. -/
theorem normalizedL2On_coveringDifference_le_meanControl_atWindow [NeZero d]
    {n m : ℤ} {x z : Vec d} {S : ℝ} {a : CoeffFamily d} {g : Vec d → Vec d}
    (hnm : n + 2 ≤ m)
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (u hdat : H1Function (openCubeSet (originCube d m)))
    (v : DirichletForcedCubeSolution (originCube d (n + 2)) a g)
    (utr : H1Function (openCubeSet (originCube d (n + 2))))
    (hutr : ∀ y, utr.toFun y = u.toFun (y + wellPlacedCentre x m (n + 2)))
    (hvdat : ∀ y, v.boundaryData.toFun y =
      hdat.toFun (y + wellPlacedCentre x m (n + 2)))
    (hXfin : eLpNorm (fun y => u.toFun y -
        volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hHfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hmean : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - hdat.toFun y)| ≤ S) :
    Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
        (fun y => utr.toFun y - v.toH1.toFun y)) ≤
      (3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal +
        S +
        unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2) *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by
  classical
  have hprice := normalizedL2On_coveringCube_sub_datum_le_meanControl_atWindow
    (x := x) (z := z) (S := S) hnm hcov u hdat hXfin hHfin hmean
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  have hsplit := normalizedL2On_sub_dirichletSolution_le_split
    (originCube d (n + 2)) v utr
  -- the datum leg, moved to the covering cube's own frame
  have hframe : normalizedL2On (openCubeSet (originCube d (n + 2)))
      (fun y => utr.toFun y - v.boundaryData.toFun y) =
      normalizedL2On ((fun y => c + y) '' openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - hdat.toFun y) := by
    have hfun : (fun y => utr.toFun y - v.boundaryData.toFun y) =
        fun y => (fun w => u.toFun w - hdat.toFun w) (y + c) := by
      funext y
      rw [hutr y, hvdat y]
    unfold normalizedL2On
    rw [hfun, image_add_eq_translateSet c (openCubeSet (originCube d (n + 2))),
      Ch01.volumeAverage_translateSet_eq_comp_addRight c
        (openCubeSet (originCube d (n + 2)))
        (fun w => (u.toFun w - hdat.toFun w) ^ 2)]
  have hlhs : Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
      (fun y => utr.toFun y - v.toH1.toFun y)) =
      normalizedL2On (openCubeSet (originCube d (n + 2)))
        (fun y => utr.toFun y - v.toH1.toFun y) := rfl
  rw [hlhs]
  rw [hframe] at hsplit
  linarith only [hsplit, hprice]

/-! ## 3. The scaled parent-`L²` object, at the hinge -/

/-- **The parent-`L²` pricing, scaled by the covering cube's frame factor, at
the hinge.**

The re-cut of `rpow_three_neg_mul_sqrt_coveringDifference_le`: section 2's
composition multiplied by `3^{-(n+2)}` — the weight the datum pricing's
left-hand side already carries — so that the datum-difference leg is discharged
by any bound `R` on the datum pricing's left-hand side. -/
theorem rpow_three_neg_mul_sqrt_coveringDifference_le_atWindow [NeZero d]
    {n m : ℤ} {x z : Vec d} {S R : ℝ} {a : CoeffFamily d} {g : Vec d → Vec d}
    (hnm : n + 2 ≤ m)
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (u hdat : H1Function (openCubeSet (originCube d m)))
    (v : DirichletForcedCubeSolution (originCube d (n + 2)) a g)
    (utr : H1Function (openCubeSet (originCube d (n + 2))))
    (hutr : ∀ y, utr.toFun y = u.toFun (y + wellPlacedCentre x m (n + 2)))
    (hvdat : ∀ y, v.boundaryData.toFun y =
      hdat.toFun (y + wellPlacedCentre x m (n + 2)))
    (hXfin : eLpNorm (fun y => u.toFun y -
        volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hHfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤)
    (hmean : |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y - hdat.toFun y)| ≤ S)
    (hGA1 : cubeBesovScaleWeight (1 : ℝ) (originCube d (n + 2)) *
        cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ≤ R) :
    Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
        Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
          (fun y => utr.toFun y - v.toH1.toFun y)) ≤
      Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          ((3 : ℝ) ^ d *
            (eLpNorm (fun y => u.toFun y -
                volumeAverage ((((fun y' => z + y') ''
                    openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))) u.toFun) 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal) +
        Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * S +
        unitMeanZeroPoincareConst d *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        R := by
  classical
  set w : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hbase := normalizedL2On_coveringDifference_le_meanControl_atWindow
    (x := x) (z := z) (S := S) (a := a) (g := g) hnm hcov u hdat v utr hutr hvdat
    hXfin hHfin hmean
  have hscaled := mul_le_mul_of_nonneg_left hbase hw0
  have hcancel : w * ((3 : ℝ) ^ (n + 2 : ℤ)) = 1 := rpow_three_neg_mul_zpow_self (n + 2)
  have hweight : cubeBesovScaleWeight (1 : ℝ) (originCube d (n + 2)) = w :=
    cubeBesovScaleWeight_one_originCube_eq (n + 2)
  rw [hweight] at hGA1
  have hexpand : w *
      ((3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal +
        S +
        unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 2 : ℤ) *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y)) =
      w * ((3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal) +
        w * S +
        (w * (3 : ℝ) ^ (n + 2 : ℤ)) * (unitMeanZeroPoincareConst d *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal))) +
        w * cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by ring
  rw [hexpand, hcancel, one_mul] at hscaled
  have hlhs : w * normalizedL2On (openCubeSet (originCube d (n + 2)))
      (fun y => utr.toFun y - v.toH1.toFun y) =
      w * Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
        (fun y => utr.toFun y - v.toH1.toFun y)) := rfl
  have hstep : w * Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
      (fun y => utr.toFun y - v.toH1.toFun y)) ≤
      w * ((3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal) +
        w * S +
        unitMeanZeroPoincareConst d *
          ((d : ℝ) * ((3 : ℝ) ^ d *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal)) +
        w * cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := hscaled
  linarith only [hstep, hGA1]

/-! ## 4. The Dirichlet energy right-hand side, at the hinge -/

/-- **The Dirichlet-energy legs, at the hinge.**

The re-cut of the energy leg: CoarseGraining's `dirichletEnergyWithRHSRHS` on
the boundary covering cube at the pin `r = s/2`, priced onto the frozen
clause's third leg.

`hlam` and `hLam` are the two `q = 2` ratio caps of
`CoarseIndexBridges.ae_coveringCubeRatioCap_le` at the indices `s/4` and
`s/2`; `hvgrad` is the boundary-gradient identity carried by the produced
Dirichlet comparison of `BoundaryEnergyRebase`. -/
theorem dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow [NeZero d]
    {n m : ℤ} {x z c : Vec d} {s C₂ K sigma : ℝ} {g : Vec d → Vec d}
    {a : CoeffFamily d} (hcdef : c = wellPlacedCentre x m (n + 2))
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hs : 0 < s) (hs1 : s ≤ 1) (hC₂ : 0 ≤ C₂) (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hdat : H1Function (openCubeSet (originCube d m)))
    (v : DirichletForcedCubeSolution (originCube d (n + 2)) a
      (fun y => -g (y + c)))
    (hvgrad : ∀ y, v.boundaryData.grad y =
      hdat.grad (y + c))
    (hlam : sigma *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4)
        (Ch02.MultiscaleExponent.finite 2) a)⁻¹ ≤ K)
    (hLam : sigma⁻¹ *
      Ch02.LambdaSq (originCube d (n + 2)) (s / 2)
        (Ch02.MultiscaleExponent.finite 2) a ≤ K)
    (hgreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => -g (y + c)))
    (hhreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => hdat.grad (y + c)))
    (hgL2cov : MemLp g 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hgWcov : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))))
    (hhL2cov : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hhWcov : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => c + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hhW : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))))
    (hhL2W : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    dirichletEnergyWithRHSRHS C₂ (originCube d (n + 2)) a (s / 2)
        (fun y => -g (y + c)) v ≤
      C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma⁻¹) *
          (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
            (gagliardoWindowConst d *
              (Support.normalizedGagliardoESeminormOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))) s g).toReal)) +
        C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma) *
          (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
              (eLpNorm hdat.grad 2
                (Support.normalizedVolumeMeasureOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))))).toReal +
            besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
              (gagliardoWindowConst d *
                (Support.normalizedGagliardoESeminormOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) s hdat.grad).toReal)) := by
  classical
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  have hshalf : (0 : ℝ) < s / 2 := by linarith only [hs]
  -- the two ellipticity factors
  have hlamFactor : poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
      (Ch02.MultiscaleExponent.finite 2) ≤ Real.sqrt K * Real.sqrt sigma⁻¹ := by
    rw [poincareLowerEllipticityFactor, show s / 2 / 2 = s / 4 by ring]
    exact rpow_neg_half_le_of_lower_cap
      (Ch02.lambdaSq_nonneg (originCube d (n + 2)) a (by linarith only [hs])
        (by norm_num)) hsigma hK hlam
  have hLamFactor : poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
      (Ch02.MultiscaleExponent.finite 2) ≤ Real.sqrt K * Real.sqrt sigma := by
    rw [poincareUpperEllipticityFactor]
    exact rpow_half_le_of_upper_cap
      (Ch02.LambdaSq_nonneg (originCube d (n + 2)) a hshalf (by norm_num)) hsigma hLam
  -- the force leg: index conversion, then the window transport
  have hgIndex : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
      (fun y => -g (y + c)) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => -g (y + c)) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_le_of_exponent_le (originCube d (n + 2)) _
      (by linarith only [hs]) hgreg
  have hgTrans := besovVectorSeminormTwo_coveringCube_atWindow
    (x := x) (z := z) (g := g) hcov hs hs1 (hcdef ▸ hgL2cov)
    (hcdef ▸ hgWcov) hgW
  rw [← hcdef] at hgTrans
  have hgLeg : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
      (fun y => -g (y + c)) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn W s g).toReal) :=
    hgIndex.trans hgTrans
  -- the boundary-gradient leg
  have hbg : dirichletBoundaryGradientField v = fun y => hdat.grad (y + c) := by
    funext y
    rw [dirichletBoundaryGradientField, hvgrad y]
  have hhIndex : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
      (fun y => hdat.grad (y + c)) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => hdat.grad (y + c)) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_le_of_exponent_le (originCube d (n + 2)) _
      (by linarith only [hs]) hhreg
  have hhTrans := besovVectorSeminormTwo_datumGrad_coveringCube_atWindow
    (x := x) (z := z) (H := hdat.grad) hcov hs hs1 (hcdef ▸ hhL2cov)
    (hcdef ▸ hhWcov) hhW
  rw [← hcdef] at hhTrans
  have hhAvg := sqrt_vecNormSq_cubeAverageVec_coveringCube_atWindow
    (x := x) (z := z) (H := hdat.grad) hcov hhL2W
  rw [← hcdef] at hhAvg
  have hhNorm : scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
      (dirichletBoundaryGradientField v) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
          (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn W)).toReal +
        besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
          (gagliardoWindowConst d *
            (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal) := by
    rw [scaleNormalizedPositiveBesovVectorNormTwo, hbg]
    exact add_le_add hhAvg (hhIndex.trans hhTrans)
  -- assemble
  have hgLeg0 : (0 : ℝ) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
        (fun y => -g (y + c)) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_of_exponent_le hgreg (by linarith only [hs]))
  have hhNorm0 : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
      (dirichletBoundaryGradientField v) := by
    rw [scaleNormalizedPositiveBesovVectorNormTwo]
    refine add_nonneg (Real.sqrt_nonneg _) ?_
    rw [hbg]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_of_exponent_le hhreg (by linarith only [hs]))
  have hlow0 : (0 : ℝ) ≤ poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
      (Ch02.MultiscaleExponent.finite 2) := by
    rw [poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg (Ch02.lambdaSq_nonneg (originCube d (n + 2)) a (by linarith only [hs])
      (by norm_num)) _
  have hupp0 : (0 : ℝ) ≤ poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
      (Ch02.MultiscaleExponent.finite 2) := by
    rw [poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg (Ch02.LambdaSq_nonneg (originCube d (n + 2)) a hshalf (by norm_num)) _
  have hp32 : (0 : ℝ) ≤ Real.rpow (s / 2) (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hshalf.le _
  have hp12 : (0 : ℝ) ≤ Real.rpow (s / 2) (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hshalf.le _
  rw [dirichletEnergyWithRHSRHS]
  refine add_le_add ?_ ?_
  · have hstep : poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
          (Ch02.MultiscaleExponent.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
          (fun y => -g (y + c)) ≤
        (Real.sqrt K * Real.sqrt sigma⁻¹) *
          (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
            (gagliardoWindowConst d *
              (Support.normalizedGagliardoESeminormOn W s g).toReal)) :=
      mul_le_mul hlamFactor hgLeg hgLeg0
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
            (Ch02.MultiscaleExponent.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
            (fun y => -g (y + c))
        = (C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ))) *
            (poincareLowerEllipticityFactor (originCube d (n + 2)) a (s / 2 / 2)
                (Ch02.MultiscaleExponent.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) (s / 2)
                (fun y => -g (y + c))) := by ring
      _ ≤ (C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ))) *
            ((Real.sqrt K * Real.sqrt sigma⁻¹) *
              (besovGagliardoConstant d *
                Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
                (gagliardoWindowConst d *
                  (Support.normalizedGagliardoESeminormOn W s g).toReal))) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC₂ hp32)
      _ = C₂ * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
            (Real.sqrt K * Real.sqrt sigma⁻¹) *
            (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
              (gagliardoWindowConst d *
                (Support.normalizedGagliardoESeminormOn W s g).toReal)) := by ring
  · have hstep : poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
          (Ch02.MultiscaleExponent.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
          (dirichletBoundaryGradientField v) ≤
        (Real.sqrt K * Real.sqrt sigma) *
          (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
              (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn W)).toReal +
            besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
              (gagliardoWindowConst d *
                (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal)) :=
      mul_le_mul hLamFactor hhNorm hhNorm0
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
            (Ch02.MultiscaleExponent.finite 2) *
          scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
            (dirichletBoundaryGradientField v)
        = (C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ))) *
            (poincareUpperEllipticityFactor (originCube d (n + 2)) a (s / 2)
                (Ch02.MultiscaleExponent.finite 2) *
              scaleNormalizedPositiveBesovVectorNormTwo (originCube d (n + 2)) (s / 2)
                (dirichletBoundaryGradientField v)) := by ring
      _ ≤ (C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ))) *
            ((Real.sqrt K * Real.sqrt sigma) *
              (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
                  (eLpNorm hdat.grad 2
                    (Support.normalizedVolumeMeasureOn W)).toReal +
                besovGagliardoConstant d *
                  Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
                  (gagliardoWindowConst d *
                    (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal))) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC₂ hp12)
      _ = C₂ * Real.rpow (s / 2) (-(1 / 2 : ℝ)) *
            (Real.sqrt K * Real.sqrt sigma) *
            (Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
                (eLpNorm hdat.grad 2
                  (Support.normalizedVolumeMeasureOn W)).toReal +
              besovGagliardoConstant d *
                Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
                (gagliardoWindowConst d *
                  (Support.normalizedGagliardoESeminormOn W s hdat.grad).toReal)) := by
          ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
