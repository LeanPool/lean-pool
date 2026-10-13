/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorCellInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitFoldCellMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitProducerLoad

/-!
# GammaTenStripCellSquare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two per-cell second moments of the strip data, regime-free

ABK26, Step 2 of `l.approximate.recurrence.formula`, `e.Pz.def`, `e.Fz.def`,
`e.nablaw.in.L.eight`.

## What this module supplies

`Closure.GammaTenStripBound.gammaTenStrip_cell_average_sq_le` and
`cubeFamilyAverage_integral_sq_stripCellPotentialDatum_le_of_majorant`
both carry a per-cell binder `hDsq` (resp. `hFsq`): *at each cell of the mesh,
the square of the cell datum is sample-integrable*.  This module discharges both
binders at the closure's own corrector families
`Closure.SplitProducerFold.closureDirichletAlong`,
`Closure.SplitProducerFold.closureNeumannAlong`, from **one integrable pathwise
dominator per leg** and nothing else.

* `integrable_stripCellPotentialDatum_sq_closure`
* `integrable_stripCellFluxDatum_sq_closure`

## The route, in one line

Per cell, the datum is below twice its own background cell energy
(`Closure.GammaTenStripEnergy.stripCellPotentialDatum_le_two_mul_energy`, whose
only input is the cell `L^2` membership of the leg field, itself the restriction
of the `L^8` membership `e.nablaw.in.L.eight` on `cu_K`), the cell energy is a
gauge times a cube average
(`Closure.GammaTenStripEnergy.meshCellBackgroundPotentialEnergy_eq_cubeAverage`),
and the *square* of that cube average is below the fourth energy of the leg field
on the whole localization cube times a purely geometric volume ratio:

```
  ( fint_R |u|^2 )^2  <=  fint_R |u|^4  <=  |R|^{-1} |cu_K| . fint_{cu_K} |u|^4 ,
```

the first step Jensen at the cell (CoarseGraining
`sq_cubeAverage_le_cubeAverage_sq_of_memLp`), the second the window/cube
comparison
`LocalizationFluctuationCellIntegrable.mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy'`
read at the cell's own scale.  So

```
  ( datum_R )^2  <=  4 . gauge^2 . |R|^{-1} |cu_K| . fint_{cu_K} |u|^4 ,
```

and the caller's integrable pathwise majorant `G` of `fint_{cu_K} |u|^4`
finishes it through `Integrable.mono'`.  The constant is explicit and depends on
`R`, `K` and `d`; **no uniformity in the cell is claimed or needed**, because the
statement is a per-cell integrability, not an estimate.

Measurability of the datum in the sample is assembled exactly as in
`Closure.SplitFoldCellMoments`: the energy leg through the measurable
`L^2`-class engine
`Closure.SplitFoldCellMoments.measurable_volumeAverage_vecNormSq_of_measurable_class`
at the two proved background classes of
`LocalizationFluctuationBackgroundClass`, the load leg through
`Closure.SplitProducerLoad.measurable_meshCellLoad`.

## Binders, and what is NOT assumed

Beyond the typing binders `d`, `[NeZero d]`, `M`, `n`, `h`, `K`, `e`, `e'`, `jd`,
`R`: the dimension gate `hd : 2 <= d`, the geometric membership `hR` of the cell
in the localization cube, and the three properties `hG0`, `hGint`, `hGD` (resp.
`hGN`) of the caller's dominator.

There is **no** smallness gate, **no** `InductionState`, **no**
`M.gamma <= gamma0`, **no** direction bound `|e| <= 1` or `|e'| <= 1`, **no**
`0 < h`, and no recurrence-parameter hypothesis of any kind.  In particular this
module does **not** route through
`exists_gamma0_integrable_freshShellDirichlet_meshEnergyCell_rpow_four`,
which carries all of those; the potential-leg mirror
`Closure.SplitFoldCellMoments.integrable_meshCellBackgroundPotentialEnergy_sq_of_meshEnergyCell`
is used only as a proof template and is not consumed.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, `e.Pz.def`, `e.Fz.def`,
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

/-! ## Membership bookkeeping -/

/-- `|u|^2` is square-integrable on a cube whose `L^8` membership is known.

This is the local copy of the private helper of `Closure.GammaTenStripEnergy`
(same proof); it is needed here because that one is `private`. -/
private theorem memLp_two_vecNormSq_of_memLp_eight' {d : ℕ} (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MemLp (fun x => vecNormSq (u x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have huE : MemLp (fun x => Book.Ch02.vecNorm (u x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := memLp_vecNorm_of_memLp Q hu
  have huE4 : MemLp (fun x => Book.Ch02.vecNorm (u x)) (4 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := huE.mono_exponent (by norm_num)
  have h := (memLp_norm_rpow_iff (μ := normalizedCubeMeasure Q)
      (f := fun x => Book.Ch02.vecNorm (u x)) (p := (4 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      huE4.aestronglyMeasurable (by norm_num) (by norm_num)).2 huE4
  have hdiv : (4 : ℝ≥0∞) / 2 = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
    rw [mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one]
  rw [hdiv] at h
  have hfun : (fun x => ‖Book.Ch02.vecNorm (u x)‖ ^ ((2 : ℝ≥0∞).toReal)) =
      fun x => vecNormSq (u x) := by
    funext x
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Book.Ch02.vecNorm (u x) ^ (2 : ℕ)),
      Book.Ch02.vecNorm_sq_eq_vecNormSq]
  rwa [hfun] at h

/-- The squared Euclidean length of a measurable vector family is measurable.

This is the local copy of `Closure.Step5InputSideConditions.measurable_vecNormSq_of_measurable`
(same proof); it is copied rather than imported so that this module's import
closure stays inside the four regime-free modules it already needs. -/
private theorem measurable_vecNormSq_of_measurable' {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] {w : Omega → Vec d} (hw : Measurable w) :
    Measurable fun omega => vecNormSq (w omega) := by
  classical
  have hEq : (fun omega => vecNormSq (w omega)) =
      fun omega => ∑ i, w omega i * w omega i := rfl
  rw [hEq]
  exact Finset.measurable_sum _ fun i _ =>
    (((measurable_pi_apply i).comp hw).mul ((measurable_pi_apply i).comp hw))

/-! ## The pathwise cell-to-cube step -/

/-- **The squared cell energy of one field, against the global fourth energy.**

```
  ( fint_R |u|^2 )^2  <=  |R|^{-1} |cu_K| . fint_{cu_K} |u|^4 .
```

Jensen at the cell, then the window/cube comparison of
`LocalizationFluctuationCellIntegrable.mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy'`
read at the cell's own scale.  The ratio is purely geometric; no uniformity in
`R` is claimed.

only on the geometric membership `hR` and the spatial `L^8` membership `hu` on
the localization cube. -/
private theorem sq_cubeAverage_vecNormSq_le_ratio_mul_originCubeFourthEnergy {d : ℕ}
    (K : ℤ) {jd : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d K) jd) (u : Vec d → Vec d)
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d K))) :
    cubeAverage R (fun x => vecNormSq (u x)) ^ (2 : ℕ) ≤
      (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
          (MeasureTheory.volume (openCubeSet (originCube d K))).toReal *
        originCubeFourthEnergy K u := by
  have hwin : Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale = openCubeSet R :=
    openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d K) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hR8 : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hR hu
  have hjensen : cubeAverage R (fun x => vecNormSq (u x)) ^ (2 : ℕ) ≤
      cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ)) :=
    sq_cubeAverage_le_cubeAverage_sq_of_memLp R (fun x => vecNormSq (u x))
      (memLp_two_vecNormSq_of_memLp_eight' R hR8)
  have hfour : IntegrableOn (fun x => vecNormSq (u x) ^ 2)
      (openCubeSet (originCube d K)) volume :=
    integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight (originCube d K) hu
  have hsubwin : Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale ⊆
      openCubeSet (originCube d K) := by rw [hwin]; exact hsub
  have hratio := mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy'
    (K := K) (ell := R.scale) (R := R) u hsubwin hfour
  rw [hwin] at hratio
  have heq : mesoWindowFourthEnergy R.scale u R =
      cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ)) := by
    unfold mesoWindowFourthEnergy
    rw [hwin, volumeAverage_openCubeSet_eq_cubeAverage_fold]
  rw [heq] at hratio
  exact hjensen.trans hratio

/-! ## The potential leg -/

/-- **The second sample moment of the strip's potential cell datum, regime-free.**

At any cell `R` of the localization cube `cu_K` and at the closure's own
corrector families, the square of `Closure.GammaTenStripBound.stripCellPotentialDatum`
is sample-integrable as soon as the caller exhibits one integrable pathwise
majorant `G` of the potential leg's fourth energy `fint_{cu_K} |e' + grad w_D|^4`.

There is no smallness gate, no induction state, no direction bound and no
recurrence parameter.

Proved from `memLp_eight_grad_closureDirichletAlong`. -/
theorem integrable_stripCellPotentialDatum_sq_closure (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d)
    {jd : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) jd)
    {G : CutoffSample d → ℝ} (hG0 : ∀ omega, 0 ≤ G omega)
    (hGint : Integrable G (cutoffSampleLaw M).toMeasure)
    (hGD : ∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
        (fun x => e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)
        ≤ G omega) :
    Integrable (fun omega : CutoffSample d =>
        stripCellPotentialDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQdef
  set sinv : ℝ := ((Annealed.sigmaBar M n : ℝ))⁻¹ with hsinvdef
  set wD : ShellSeq d → H10Function (openCubeSet Q) := closureDirichletAlong M n h K e
    with hwDdef
  set wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q) := closureNeumannAlong M n h K e'
    with hwNdef
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hsolD := isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e
  have hsolN := isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e'
  -- the geometric ratio and the total constant
  set ratio : ℝ := (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
    (MeasureTheory.volume (openCubeSet Q)).toReal with hratiodef
  have hratio0 : (0 : ℝ) ≤ ratio :=
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  set Cst : ℝ := 4 * sinv ^ (2 : ℕ) * ratio with hCstdef
  have hCst0 : (0 : ℝ) ≤ Cst := by
    rw [hCstdef]
    exact mul_nonneg (by positivity) hratio0
  -- `hG0` is recorded: the dominator is nonnegative
  have _hdom0 : ∀ omega : CutoffSample d, 0 ≤ Cst * G omega := fun omega =>
    mul_nonneg hCst0 (hG0 omega)
  -- the spatial `L^8` families
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    fun omega => memLp_eight_grad_closureDirichletAlong hd M n h K e omega
  have hu8 : ∀ omega : ShellSeq d,
      MemLp (fun x => e' + (wD omega).toH1Function.grad x) (8 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := fun omega => (memLp_const e').add (hL8 omega)
  have hg2 : ∀ omega : ShellSeq d,
      MemLp (fun x => (wD omega).toH1Function.grad x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure R) := fun omega =>
    (memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hR (hL8 omega)).mono_exponent
      (by norm_num)
  -- the pathwise bound
  have hpt : ∀ omega : CutoffSample d,
      stripCellPotentialDatum M n h (K : ℤ) e e' wD wN R omega ^ (2 : ℕ) ≤
        Cst * G omega := by
    intro omega
    have hD0 : (0 : ℝ) ≤ stripCellPotentialDatum M n h (K : ℤ) e e' wD wN R omega :=
      stripCellPotentialDatum_nonneg M n h (K : ℤ) e e' wD wN R omega
    have hle := stripCellPotentialDatum_le_two_mul_energy M n h (K : ℤ) e e' wD wN R omega
      (hg2 omega.val)
    have hsq := pow_le_pow_left₀ hD0 hle 2
    rw [meshCellBackgroundPotentialEnergy_eq_cubeAverage] at hsq
    have hcell := sq_cubeAverage_vecNormSq_le_ratio_mul_originCubeFourthEnergy
      (K : ℤ) hR (fun x => e' + (wD omega.val).toH1Function.grad x) (hu8 omega.val)
    have hfac : (0 : ℝ) ≤ 4 * sinv ^ (2 : ℕ) := by positivity
    calc stripCellPotentialDatum M n h (K : ℤ) e e' wD wN R omega ^ (2 : ℕ)
        ≤ (2 * (sinv *
            cubeAverage R
              (fun x => vecNormSq (e' + (wD omega.val).toH1Function.grad x)))) ^ (2 : ℕ) :=
          hsq
      _ = 4 * sinv ^ (2 : ℕ) *
            cubeAverage R
              (fun x => vecNormSq (e' + (wD omega.val).toH1Function.grad x)) ^ (2 : ℕ) := by
          ring
      _ ≤ 4 * sinv ^ (2 : ℕ) *
            (ratio * originCubeFourthEnergy (K : ℤ)
              (fun x => e' + (wD omega.val).toH1Function.grad x)) :=
          mul_le_mul_of_nonneg_left hcell hfac
      _ = Cst * originCubeFourthEnergy (K : ℤ)
            (fun x => e' + (wD omega.val).toH1Function.grad x) := by rw [hCstdef]; ring
      _ ≤ Cst * G omega := mul_le_mul_of_nonneg_left (hGD omega) hCst0
  -- measurability of the datum
  have hgradmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (wD omega).toH1Function.grad :=
    fun omega => (wD omega).toH1Function.grad_memVectorL2
  have haffmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (fun x => e' + (wD omega).toH1Function.grad x) :=
    fun omega => (memLp_const e').add (hgradmem omega)
  have hclassmeas : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hgradmem omega) :=
    measurable_toHilbertVectorL2OfVecField_freshShellDirichletGrad Q sinv n (n + (h : ℤ))
      e wD hsolD hgradmem
  have haffclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (haffmem omega) :=
    measurable_toHilbertVectorL2OfVecField_const_add e' hgradmem haffmem hclassmeas
  have hEmeas : Measurable fun omega : ShellSeq d =>
      volumeAverage (openCubeSet R)
        (fun x => vecNormSq (e' + (wD omega).toH1Function.grad x)) :=
    measurable_volumeAverage_vecNormSq_of_measurable_class (measurableSet_openCubeSet R)
      hsub haffmem haffclass
  have hloadmeas : Measurable (meshCellLoad M n h (K : ℤ) e e' wD wN R) :=
    measurable_meshCellLoad M n h (K : ℤ) e e' wD wN hsolD hsolN hR
  have hdatum : Measurable fun omega : CutoffSample d =>
      stripCellPotentialDatum M n h (K : ℤ) e e' wD wN R omega := by
    have hEq : (fun omega : CutoffSample d =>
        stripCellPotentialDatum M n h (K : ℤ) e e' wD wN R omega) =
        fun omega : CutoffSample d =>
          sinv * volumeAverage (openCubeSet R)
              (fun x => vecNormSq (e' + (wD omega.val).toH1Function.grad x)) +
            vecNormSq (meshCellLoad M n h (K : ℤ) e e' wD wN R omega).1 := by
      funext omega
      rw [stripCellPotentialDatum, meshCellBackgroundPotentialEnergy_eq,
        average_cubeDomain_eq_volumeAverage]
    rw [hEq]
    exact ((hEmeas.comp measurable_subtype_coe).const_mul sinv).add
      (measurable_vecNormSq_of_measurable' (measurable_fst.comp hloadmeas))
  refine (hGint.const_mul Cst).mono' (hdatum.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg
    (stripCellPotentialDatum_nonneg M n h (K : ℤ) e e' wD wN R omega) 2)]
  exact hpt omega

/-! ## The flux leg -/

/-- **The second sample moment of the strip's flux cell datum, regime-free.**

The flux mirror of `integrable_stripCellPotentialDatum_sq_closure`: at any cell
`R` of `cu_K`, the square of `Closure.GammaTenStripBound.stripCellFluxDatum` is
sample-integrable as soon as the caller exhibits one integrable pathwise majorant
`G` of the flux leg's fourth energy `fint_{cu_K} |e + bfF|^4`.

Conditional exactly as its potential mirror, and proved from
`memLp_eight_neumannFluxField_closure`. -/
theorem integrable_stripCellFluxDatum_sq_closure (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d)
    {jd : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) jd)
    {G : CutoffSample d → ℝ} (hG0 : ∀ omega, 0 ≤ G omega)
    (hGint : Integrable G (cutoffSampleLaw M).toMeasure)
    (hGN : ∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
        (fun x => e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
          (n + (h : ℤ)) e' (closureNeumannAlong M n h K e' omega.val) x)
        ≤ G omega) :
    Integrable (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQdef
  set sig : PositiveScalar := Annealed.sigmaBar M n with hsigdef
  set sinv : ℝ := ((sig : ℝ))⁻¹ with hsinvdef
  set wD : ShellSeq d → H10Function (openCubeSet Q) := closureDirichletAlong M n h K e
    with hwDdef
  set wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q) := closureNeumannAlong M n h K e'
    with hwNdef
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hsolD := isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e
  have hsolN := isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e'
  -- the geometric ratio and the total constant
  set ratio : ℝ := (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
    (MeasureTheory.volume (openCubeSet Q)).toReal with hratiodef
  have hratio0 : (0 : ℝ) ≤ ratio :=
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  set Cst : ℝ := 4 * (sig : ℝ) ^ (2 : ℕ) * ratio with hCstdef
  have hCst0 : (0 : ℝ) ≤ Cst := by
    rw [hCstdef]
    exact mul_nonneg (by positivity) hratio0
  -- `hG0` is recorded: the dominator is nonnegative
  have _hdom0 : ∀ omega : CutoffSample d, 0 ≤ Cst * G omega := fun omega =>
    mul_nonneg hCst0 (hG0 omega)
  -- the spatial `L^8` families
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega)) (8 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    fun omega => memLp_eight_neumannFluxField_closure hd M n h K e' omega
  have hu8 : ∀ omega : ShellSeq d,
      MemLp (fun x => e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x)
        (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := fun omega =>
    (memLp_const e).add (hL8 omega)
  have hg2 : ∀ omega : ShellSeq d,
      MemLp (neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure R) := fun omega =>
    (memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hR (hL8 omega)).mono_exponent
      (by norm_num)
  -- the pathwise bound
  have hpt : ∀ omega : CutoffSample d,
      stripCellFluxDatum M n h (K : ℤ) e e' wD wN R omega ^ (2 : ℕ) ≤ Cst * G omega := by
    intro omega
    have hF0 : (0 : ℝ) ≤ stripCellFluxDatum M n h (K : ℤ) e e' wD wN R omega :=
      stripCellFluxDatum_nonneg M n h (K : ℤ) e e' wD wN R omega
    have hle := stripCellFluxDatum_le_two_mul_energy M n h (K : ℤ) e e' wD wN R omega
      (hg2 omega.val)
    have hsq := pow_le_pow_left₀ hF0 hle 2
    rw [meshCellBackgroundFluxEnergy_eq_cubeAverage] at hsq
    have hcell := sq_cubeAverage_vecNormSq_le_ratio_mul_originCubeFourthEnergy
      (K : ℤ) hR
      (fun x => e + neumannFluxField sig omega.val n (n + (h : ℤ)) e' (wN omega.val) x)
      (hu8 omega.val)
    have hfac : (0 : ℝ) ≤ 4 * (sig : ℝ) ^ (2 : ℕ) := by positivity
    calc stripCellFluxDatum M n h (K : ℤ) e e' wD wN R omega ^ (2 : ℕ)
        ≤ (2 * ((sig : ℝ) *
            cubeAverage R (fun x => vecNormSq (e + neumannFluxField sig omega.val n
              (n + (h : ℤ)) e' (wN omega.val) x)))) ^ (2 : ℕ) := hsq
      _ = 4 * (sig : ℝ) ^ (2 : ℕ) *
            cubeAverage R (fun x => vecNormSq (e + neumannFluxField sig omega.val n
              (n + (h : ℤ)) e' (wN omega.val) x)) ^ (2 : ℕ) := by ring
      _ ≤ 4 * (sig : ℝ) ^ (2 : ℕ) *
            (ratio * originCubeFourthEnergy (K : ℤ)
              (fun x => e + neumannFluxField sig omega.val n (n + (h : ℤ)) e'
                (wN omega.val) x)) := mul_le_mul_of_nonneg_left hcell hfac
      _ = Cst * originCubeFourthEnergy (K : ℤ)
            (fun x => e + neumannFluxField sig omega.val n (n + (h : ℤ)) e'
              (wN omega.val) x) := by rw [hCstdef]; ring
      _ ≤ Cst * G omega := mul_le_mul_of_nonneg_left (hGN omega) hCst0
  -- measurability of the datum
  have hgradmemN : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (wN omega).toH1Function.grad :=
    fun omega => (wN omega).toH1Function.grad_memVectorL2
  have hnfmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q)
        (neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega)) := fun omega =>
    (hgradmemN omega).add
      (memVectorL2_openCubeSet_of_continuous Q
        (continuous_streamForcing sinv omega n (n + (h : ℤ)) e'))
  have hnfclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hnfmem omega) :=
    measurable_toHilbertVectorL2OfVecField_neumannFluxField Q sig sinv n (n + (h : ℤ))
      e' e' wN hsolN hnfmem
  have haffmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q)
        (fun x => e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x) :=
    fun omega => (memLp_const e).add (hnfmem omega)
  have haffclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (haffmem omega) :=
    measurable_toHilbertVectorL2OfVecField_const_add e hnfmem haffmem hnfclass
  have hCmeas : Measurable fun omega : ShellSeq d =>
      volumeAverage (openCubeSet R) (fun x =>
        vecNormSq (e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x)) :=
    measurable_volumeAverage_vecNormSq_of_measurable_class (measurableSet_openCubeSet R)
      hsub haffmem haffclass
  have hloadmeas : Measurable (meshCellLoad M n h (K : ℤ) e e' wD wN R) :=
    measurable_meshCellLoad M n h (K : ℤ) e e' wD wN hsolD hsolN hR
  have hdatum : Measurable fun omega : CutoffSample d =>
      stripCellFluxDatum M n h (K : ℤ) e e' wD wN R omega := by
    have hEq : (fun omega : CutoffSample d =>
        stripCellFluxDatum M n h (K : ℤ) e e' wD wN R omega) =
        fun omega : CutoffSample d =>
          (sig : ℝ) * volumeAverage (openCubeSet R) (fun x =>
              vecNormSq (e + neumannFluxField sig omega.val n (n + (h : ℤ)) e'
                (wN omega.val) x)) +
            vecNormSq (meshCellLoad M n h (K : ℤ) e e' wD wN R omega).2 := by
      funext omega
      rw [stripCellFluxDatum, meshCellBackgroundFluxEnergy_eq,
        average_cubeDomain_eq_volumeAverage]
    rw [hEq]
    exact ((hCmeas.comp measurable_subtype_coe).const_mul ((sig : ℝ))).add
      (measurable_vecNormSq_of_measurable' (measurable_snd.comp hloadmeas))
  refine (hGint.const_mul Cst).mono' (hdatum.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg
    (stripCellFluxDatum_nonneg M n h (K : ℤ) e e' wD wN R omega) 2)]
  exact hpt omega

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
