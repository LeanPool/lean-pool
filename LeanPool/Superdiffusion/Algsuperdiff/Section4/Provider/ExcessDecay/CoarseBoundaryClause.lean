/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseDatumPricing
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseMeanComparison
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryEnergyRebase

/-!
# CoarseBoundaryClause

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary Caccioppoli's parent-`L²` object, priced onto the frozen legs

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

```text
  ‖u(·+c) − v_cc‖_{L²(□_{n+2})} ,    c = wellPlacedCentre x m (n+2) ,
```

priced onto the frozen clause's own legs.  In the same-boundary-data
architecture the split is a two-term triangle, not the plan's quadrangle:

```text
  ‖u(·+c) − v_cc‖ ≤ ‖u − h‖_{L²(c+□_{n+2})}   +   ‖v_cc − h‖_{L²(□_{n+2})} ,
```

the second summand being exactly `CoarseDatumPricing`'s output.  The first
summand is decomposed (§2) as

```text
  ‖u − h‖_{L²(cc)}
      ≤ ‖u − (u)_{cc}‖_{L²(cc)} + |(u−h)_{cc}| + ‖h − (h)_{cc}‖_{L²(cc)}
      ≤ 3^d ‖u − (u)_{W'}‖_{L²(W')}            (mean-minimality + window transport)
        + S                                      (the open scalar, threaded)
        + C(d) 3^{n+2} d 3^d ‖∇h‖_{L²(W')} ,    (data Poincaré on h alone)
```

See `CoarseMeanComparison` for the machine-checked record that the
mean-comparison chain bounds `S` by this very quantity rather than the other
way round.

## References

* ABK26, the boundary application.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The coordinate gradient against the ambient gradient -/

/-- A coordinate of the gradient is dominated by the ambient (sup) norm, in the
normalized `L²` carrier. -/
theorem eLpNorm_grad_coord_le_eLpNorm_grad {A : Set (Vec d)} (G : Vec d → Vec d)
    (i : Fin d) :
    eLpNorm (fun y => G y i) 2 (Support.normalizedVolumeMeasureOn A) ≤
      eLpNorm G 2 (Support.normalizedVolumeMeasureOn A) := by
  by_cases hG : AEStronglyMeasurable G (Support.normalizedVolumeMeasureOn A)
  · refine eLpNorm_mono ((continuous_apply i).comp_aestronglyMeasurable hG) (fun y => ?_)
    rw [Real.norm_eq_abs]
    simpa using norm_le_pi_norm (G y) i
  · rw [eLpNorm_of_not_aestronglyMeasurable hG]
    exact le_top

/-- The coordinate sum of the datum gradient is at most `d` times the ambient
one. -/
theorem sum_toReal_eLpNorm_grad_coord_le {A : Set (Vec d)} (G : Vec d → Vec d)
    (hfin : eLpNorm G 2 (Support.normalizedVolumeMeasureOn A) ≠ ⊤) :
    ∑ i : Fin d, (eLpNorm (fun y => G y i) 2
        (Support.normalizedVolumeMeasureOn A)).toReal ≤
      (d : ℝ) * (eLpNorm G 2 (Support.normalizedVolumeMeasureOn A)).toReal := by
  classical
  calc ∑ i : Fin d, (eLpNorm (fun y => G y i) 2
        (Support.normalizedVolumeMeasureOn A)).toReal
      ≤ ∑ _i : Fin d, (eLpNorm G 2 (Support.normalizedVolumeMeasureOn A)).toReal := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact ENNReal.toReal_mono hfin (eLpNorm_grad_coord_le_eLpNorm_grad G i)
    _ = (d : ℝ) * (eLpNorm G 2 (Support.normalizedVolumeMeasureOn A)).toReal := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 2. The covering-cube pricing of `‖u − h‖`, modulo the scalar -/

/-- **The three legs of the parent-`L²` pricing.**

On the boundary covering cube `cc = c + □_{n+2}` the `L²` distance between the
solution and its own boundary datum is priced by two of the frozen clause's own
legs — one through mean-minimality and the window transport, the other through
the proved data Poincaré on `h` alone — and the open scalar `S =
|(u−h)_{cc}|` **at coefficient 1**.

`hmean` is a conditional A obligation (the mean-comparison bound); every
other input is the anchor's own data. -/
theorem normalizedL2On_coveringCube_sub_datum_le_meanControl
    {n m : ℤ} {x z : Vec d} {S : ℝ} (hnm : n + 2 ≤ m)
    (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
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
    exact lt_of_le_of_ne zero_le
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
  have hmin := normalizedL2On_sub_average_le_sub_const (W := cc) hccpos hcctop
    huI huI2 (volumeAverage W u.toFun)
  have hdictA : normalizedL2On cc (fun y => u.toFun y - volumeAverage W u.toFun) =
      (eLpNorm (fun y => u.toFun y - volumeAverage W u.toFun) 2
        (Support.normalizedVolumeMeasureOn cc)).toReal :=
    normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn hccpos hcctop huWL
  have htrans := toReal_eLpNorm_coveringCube_le_anchorWindow (x := x) (z := z)
    hnm hx hgeom (f := fun y => u.toFun y - volumeAverage W u.toFun) hXfin
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
  have hcoordTrans : ∀ i : Fin d,
      (eLpNorm (fun y => hdat.grad y i) 2
        (Support.normalizedVolumeMeasureOn cc)).toReal ≤
      (3 : ℝ) ^ d *
        (eLpNorm (fun y => hdat.grad y i) 2
          (Support.normalizedVolumeMeasureOn W)).toReal := by
    intro i
    refine toReal_eLpNorm_coveringCube_le_anchorWindow (x := x) (z := z) hnm hx hgeom
      (f := fun y => hdat.grad y i) ?_
    refine ne_top_of_le_ne_top hHfin ?_
    exact eLpNorm_grad_coord_le_eLpNorm_grad hdat.grad i
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

/-! ## 3. The two-term split of the Caccioppoli's parent-`L²` object -/

/-- The normalized `L²` seminorm on an open cube is the cube `L²` norm. -/
theorem normalizedL2On_openCubeSet_eq_cubeLpNorm (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (MeasureTheory.volume.restrict (openCubeSet Q))) :
    normalizedL2On (openCubeSet Q) f = cubeLpNorm Q (2 : ℝ≥0∞) f := by
  have hpos : 0 < volume (openCubeSet Q) :=
    lt_of_le_of_ne zero_le (Ne.symm (volume_openCubeSet_ne_zero Q))
  rw [normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
      hpos (volume_openCubeSet_ne_top Q) hf,
    normalizedVolumeMeasureOn_openCubeSet]
  rfl

/-- **The same-boundary-data split.**

For CoarseGraining's `DirichletForcedCubeSolution` `v` on `Q` and any `H¹`
competitor `utr` on `Q`, the object the boundary Caccioppoli puts on its
right-hand side splits into the datum distance and the datum pricing's
zero-trace leg:

```text
  ‖utr − v‖_{L²(Q)} ≤ ‖utr − h‖_{L²(Q)} + ‖v − h‖_{L²(Q)} .
```

Nothing is subtracted through the operator: `h` is `v`'s own boundary datum and
the force is `g` on both sides. -/
theorem normalizedL2On_sub_dirichletSolution_le_split (Q : TriadicCube d)
    {a : CoeffFamily d} {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (utr : H1Function (openCubeSet Q)) :
    normalizedL2On (openCubeSet Q) (fun y => utr.toFun y - v.toH1.toFun y) ≤
      normalizedL2On (openCubeSet Q) (fun y => utr.toFun y - v.boundaryData.toFun y) +
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by
  have hA : MemLp (fun y => utr.toFun y - v.boundaryData.toFun y) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) := utr.memL2.sub v.boundaryData.memL2
  have hB : MemLp (fun y => v.boundaryData.toFun y - v.toH1.toFun y) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    v.boundaryData.memL2.sub v.toH1.memL2
  have hB' : MemLp (fun y => v.toH1.toFun y - v.boundaryData.toFun y) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    v.toH1.memL2.sub v.boundaryData.memL2
  have hfun : (fun y => utr.toFun y - v.toH1.toFun y) =
      fun y => (utr.toFun y - v.boundaryData.toFun y) +
        (v.boundaryData.toFun y - v.toH1.toFun y) := by
    funext y; ring
  rw [hfun]
  refine (normalizedL2On_add_le hA hB).trans (add_le_add le_rfl (le_of_eq ?_))
  rw [normalizedL2On_sub_comm, normalizedL2On_openCubeSet_eq_cubeLpNorm Q hB']

/-! ## 4. The composed parent-`L²` pricing, modulo the scalar `S` -/

/-- **The parent-`L²` pricing, composed.**

The boundary Caccioppoli's parent-`L²` object at the covering cube, priced onto
the frozen legs and the datum pricing's zero-trace leg, with the open scalar `S`
threaded additively at coefficient 1:

```text
  ‖u(·+c) − v_cc‖_{L²(□_{n+2})}
      ≤ 3^d ‖u − (u)_{W'}‖_{L²(W')}
        + S
        + C_P(d) 3^{n+2} d 3^d ‖∇h‖_{L²(W')}
        + ‖v_cc − h‖_{L²(□_{n+2})} .
```

`hutr` and `hvdat` are exactly the two frame identities
`BoundaryEnergyRebase`'s proof already carries (`utr = u(·+c)` by `rfl`,
`v.boundaryData = h(·+c)` by its own conclusion). -/
theorem normalizedL2On_coveringDifference_le_meanControl [NeZero d]
    {n m : ℤ} {x z : Vec d} {S : ℝ} {a : CoeffFamily d} {g : Vec d → Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
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
  have hprice := normalizedL2On_coveringCube_sub_datum_le_meanControl
    (x := x) (z := z) (S := S) hnm hx hgeom u hdat hXfin hHfin hmean
  have hlhs : Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
      (fun y => utr.toFun y - v.toH1.toFun y)) =
      normalizedL2On (openCubeSet (originCube d (n + 2)))
        (fun y => utr.toFun y - v.toH1.toFun y) := rfl
  rw [hlhs]
  rw [hframe] at hsplit
  linarith only [hsplit, hprice]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
