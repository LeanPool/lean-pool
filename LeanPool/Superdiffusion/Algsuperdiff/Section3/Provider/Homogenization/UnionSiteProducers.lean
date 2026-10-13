/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffResponseJ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ResponseCommonDomination
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.UnionConcentration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.MixedAllocation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.SiteFamilyBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz

/-!
# UnionSiteProducers

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Per-site producers for the grid concentration display

The Section 3.5 grid concentration display (ABK26, proof of
`p.homogenization.step`) averages, over the lattice `3 ^ n Z^d cap
square_m`, the centered response

`X_u = J(u + square_n, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L) - E[...]`.

The concentration engine itself is available separately; what it consumes at
each site `u` is a package of four facts about `X_u`.  This module supplies
that package on the genuine cutoff sample law:

1. *The translated-cube observable and its literal identification.*  The one
   measurable coarse-block evaluation
   `Observable.cutoffResponseJFromCommonCoarseBlock M L Q p q` exists for every
   triadic cube `Q`; here it is identified, on one probability-one event and
   simultaneously in both loads, with the literal `ResponseJ (cubeSet Q) p q`
   of the actual coefficient cutoff.  The proved identification was available
   only at the origin cube.

2. *Cube locality.*  Every entry of the coarse block matrix of the cutoff on
   `cubeSet Q` is integral-local, hence so is the quadratic-form evaluation;
   the almost-everywhere passage to the chosen representative is absorbed by
   the local sigma-field, which is the `Subtype.val`-comap of the `M.P`-
   lower-shell local sigma-field (`Cutoff.lowerShellLocalCompletion`) and
   therefore already contains the ambient null sets; the absorption lemma is
   the proved `measurableSet_cutoffSampleLocalSigma_of_ae_eq`
   (`Provider/BadEvents/LambdaLocal.lean`), not a new assumption.  At the
   site cube this gives measurability for `cutoffSampleLocalSigma M L
   (siteRegion n {u})`.

3. *Centering.*  The genuine cutoff sample law is invariant under every real
   translation, and the Chapter 2 response is translation covariant, so the
   site observable is the origin observable composed with the sample
   translation.  Its mean is therefore the mean at the origin cube, and the
   recentred variable integrates to zero.

4. *The per-site two-term tail.*  From a two-term `(Gamma_2, Gamma_{1/2})`
   bound on the mixed-scale homogenization error at the observation cube
   `square_n` and cutoff `a_L`, the pathwise domination `J <= E^2` and the
   square rule for stretched exponentials give a two-term
   `(Gamma_1, Gamma_{1/4})` bound for the absolute value of the recentred site
   response, at the two squared amplitudes.  The mean shift is absorbed into
   the same two lanes through the first-moment bound of each lane.

The last section assembles the four producers: the deterministic mixed
allocation splits each recentred site response into a `Gamma_1` lane and a
`Gamma_{1/4}` lane, both still local for the site's own cube tree and both
centered, and the two-lane grid concentration estimate then produces the
display of ABK26 for every unit direction and every corridor pair `L <= n`,
at the grid gain `3 ^ (-d k / 2)` on both amplitudes.

## References

* ABK26, Proposition `p.homogenization.step`.
* ABK26, (2.4), definition of `J(U, p, q; a)`.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-- The paper-wide bound `2 <= d`, already stored in the standing model, supplies
the nonzero-dimension instance required by CoarseGraining's cube A. -/
private theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩

/-! ## Producer 1: the translated-cube observable and its literal value -/

/-- **The general-cube literal identification of the common coarse-block
response.**  On one probability-one event, and simultaneously for *both* loads,
the scalar evaluation of the single measurable coarse-block representative at
an arbitrary triadic cube `Q` is the literal manuscript quantity `J(Q, p, q;
a_L)`.  The proved instance of this statement was restricted to the origin
cube. -/
theorem ae_forall_cutoffResponseJFromCommonCoarseBlock_eq_responseJ
    (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ p q : Vec d,
        Observable.cutoffResponseJFromCommonCoarseBlock M coefficientScale Q p q omega =
          ResponseJ (cubeSet Q) p q
            (coefficientCutoff M.nu coefficientScale omega).toFun := by
  let : NeZero d := neZero_of_model M
  filter_upwards
    [Observable.ae_forall_blockJObservableCubeSet_eq_cutoffCoarseRepresentative M
      coefficientScale Q] with omega hblock
  intro p q
  set a := coefficientCutoff M.nu coefficientScale omega with ha
  have hzero := hblock (0 : BlockVec d) (0 : BlockVec d)
  have hzeroFirst : 0 ≤ Ch04.restrictionResponseJObservableCubeSet Q 0 0 a :=
    Ch04.restrictionResponseJObservableCubeSet_nonneg Q 0 0 a
  have hzeroSecond :
      0 ≤ Ch04.restrictionResponseJObservableCubeSet Q 0 0 (adjointReg a) :=
    Ch04.restrictionResponseJObservableCubeSet_nonneg Q 0 0 (adjointReg a)
  have hadjointZero :
      Ch04.restrictionResponseJObservableCubeSet Q 0 0 (adjointReg a) = 0 := by
    have hsum :
        (1 / 2 : ℝ) * Ch04.restrictionResponseJObservableCubeSet Q 0 0 a +
            (1 / 2 : ℝ) *
              Ch04.restrictionResponseJObservableCubeSet Q 0 0 (adjointReg a) = 0 := by
      calc
        (1 / 2 : ℝ) * Ch04.restrictionResponseJObservableCubeSet Q 0 0 a +
              (1 / 2 : ℝ) *
                Ch04.restrictionResponseJObservableCubeSet Q 0 0 (adjointReg a) =
            Ch04.blockJObservableCubeSetBlockVec Q (0 : BlockVec d) (0 : BlockVec d) a := by
              simp [Ch04.blockJObservableCubeSetBlockVec]
        _ = Observable.cutoffBlockJFromCoarseFullBlockRepresentative M coefficientScale Q
              (0 : BlockVec d) (0 : BlockVec d) omega := hzero
        _ = 0 := by
          simp [Observable.cutoffBlockJFromCoarseFullBlockRepresentative,
            Ch04.blockJQuadraticFullBlockMat, Ch04.fullBlockQuadraticCh04, Ch04.fullBlockReflect,
            toFullBlockVec, dotProduct, Matrix.mulVec, blockVecDot, vecDot]
    nlinarith
  have hresponse := hblock (Observable.responseJFirstHalfBlockLoad p q)
    (Observable.responseJSecondHalfBlockLoad p q)
  have hpDiff : (1 / 2 : ℝ) • p - (-1 / 2 : ℝ) • p = p := by
    ext i
    simp
    ring
  have hqDiff : (1 / 2 : ℝ) • q - (-1 / 2 : ℝ) • q = q := by
    ext i
    simp
    ring
  have hpAdd : (-1 / 2 : ℝ) • p + (1 / 2 : ℝ) • p = 0 := by
    ext i
    simp
    ring
  have hqAdd : (1 / 2 : ℝ) • q + (-1 / 2 : ℝ) • q = 0 := by
    ext i
    simp
    ring
  calc
    Observable.cutoffResponseJFromCommonCoarseBlock M coefficientScale Q p q omega =
        2 * Observable.cutoffBlockJFromCoarseFullBlockRepresentative M coefficientScale Q
          (Observable.responseJFirstHalfBlockLoad p q)
          (Observable.responseJSecondHalfBlockLoad p q) omega := rfl
    _ = 2 * Ch04.blockJObservableCubeSetBlockVec Q
          (Observable.responseJFirstHalfBlockLoad p q)
          (Observable.responseJSecondHalfBlockLoad p q) a := by rw [hresponse]
    _ = Ch04.restrictionResponseJObservableCubeSet Q p q a := by
      rw [show Ch04.blockJObservableCubeSetBlockVec Q
          (Observable.responseJFirstHalfBlockLoad p q)
          (Observable.responseJSecondHalfBlockLoad p q) a =
          (1 / 2 : ℝ) * Ch04.restrictionResponseJObservableCubeSet Q p q a +
            (1 / 2 : ℝ) *
              Ch04.restrictionResponseJObservableCubeSet Q 0 0 (adjointReg a) by
        simp only [Ch04.blockJObservableCubeSetBlockVec,
          Observable.responseJFirstHalfBlockLoad,
          Observable.responseJSecondHalfBlockLoad, Ch04.blockJObservableCubeSet_apply]
        rw [hpDiff, hqDiff, hpAdd, hqAdd]]
      rw [hadjointZero]
      ring
    _ = ResponseJ (cubeSet Q) p q a.toFun := rfl

/-! ## Producer 2: cube locality -/

/-- The function form of the almost-everywhere absorption of the cutoff-sample
local sigma-field: a modification on a null set of a locally measurable map is
locally measurable, in every codomain. -/
private theorem measurable_cutoffSampleLocalSigma_of_ae_eq {alpha : Type*}
    [MeasurableSpace alpha] (M : ABKModel d) (m : ℤ) (U : Set (Vec d))
    {f g : CutoffSample d → alpha}
    (hf : Measurable[cutoffSampleLocalSigma M m U] f)
    (hfg : g =ᵐ[(cutoffSampleLaw M).toMeasure] f) :
    Measurable[cutoffSampleLocalSigma M m U] g := by
  intro S hS
  exact measurableSet_cutoffSampleLocalSigma_of_ae_eq M m U (hf hS)
    (hfg.fun_comp (· ∈ S))

/-- **Every entry of the coarse block matrix of the actual cutoff on a cube is
integral-local.**  The four block-entry formulas of CoarseGraining express each
entry through the coarse energy `Mu`, whose locality on the closed cube is
proved. -/
private theorem measurable_cutoffCoarseFullBlockRaw_cutoffSampleLocal
    (M : ABKModel d) (L : ℤ) (Q : TriadicCube d) {U : Set (Vec d)}
    (hQU : cubeSet Q ⊆ U) :
    Measurable[cutoffSampleLocalSigma M L U]
      (Observable.cutoffCoarseFullBlockRaw M L Q) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M L U
  have hMu : ∀ P0 : BlockVec d, Measurable fun omega : CutoffSample d =>
      Mu (cubeSet Q) P0 (coefficientCutoff M.nu L omega).toFun :=
    fun P0 => measurable_Mu_coefficientCutoff_cutoffSampleLocal M L Q hQU P0
  change Measurable fun omega : CutoffSample d =>
    (toFullBlockMat (coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff M.nu L omega).toFun) : BlockCoord d → BlockCoord d → ℝ)
  refine Measurable.of_eval fun alpha => Measurable.of_eval fun beta => ?_
  cases alpha with
  | inl i =>
      cases beta with
      | inl j =>
          have hEq : (fun omega : CutoffSample d =>
              toFullBlockMat (coarseBlockMatrix (cubeSet Q)
                (coefficientCutoff M.nu L omega).toFun) (Sum.inl i) (Sum.inl j)) =
              fun omega : CutoffSample d =>
                if i = j then
                  2 * Mu (cubeSet Q) (Pi.single i 1, 0)
                    (coefficientCutoff M.nu L omega).toFun
                else
                  Mu (cubeSet Q) ((Pi.single i 1, 0) + (Pi.single j 1, 0))
                      (coefficientCutoff M.nu L omega).toFun -
                    Mu (cubeSet Q) (Pi.single i 1, 0)
                      (coefficientCutoff M.nu L omega).toFun -
                    Mu (cubeSet Q) (Pi.single j 1, 0)
                      (coefficientCutoff M.nu L omega).toFun := by
            funext omega
            exact coarseBlockMatrix_upperLeft_apply (cubeSet Q)
              (coefficientCutoff M.nu L omega).toFun i j
          rw [hEq]
          by_cases hij : i = j
          · simp only [ite_eq_left hij]
            exact (hMu _).const_mul 2
          · simp only [ite_eq_right hij]
            exact ((hMu _).sub (hMu _)).sub (hMu _)
      | inr j =>
          have hEq : (fun omega : CutoffSample d =>
              toFullBlockMat (coarseBlockMatrix (cubeSet Q)
                (coefficientCutoff M.nu L omega).toFun) (Sum.inl i) (Sum.inr j)) =
              fun omega : CutoffSample d =>
                Mu (cubeSet Q) ((Pi.single i 1, 0) + (0, Pi.single j 1))
                    (coefficientCutoff M.nu L omega).toFun -
                  Mu (cubeSet Q) (Pi.single i 1, 0)
                    (coefficientCutoff M.nu L omega).toFun -
                  Mu (cubeSet Q) (0, Pi.single j 1)
                    (coefficientCutoff M.nu L omega).toFun := by
            funext omega
            exact coarseBlockMatrix_upperRight_apply (cubeSet Q)
              (coefficientCutoff M.nu L omega).toFun i j
          rw [hEq]
          exact ((hMu _).sub (hMu _)).sub (hMu _)
  | inr i =>
      cases beta with
      | inl j =>
          have hEq : (fun omega : CutoffSample d =>
              toFullBlockMat (coarseBlockMatrix (cubeSet Q)
                (coefficientCutoff M.nu L omega).toFun) (Sum.inr i) (Sum.inl j)) =
              fun omega : CutoffSample d =>
                Mu (cubeSet Q) ((0, Pi.single i 1) + (Pi.single j 1, 0))
                    (coefficientCutoff M.nu L omega).toFun -
                  Mu (cubeSet Q) (0, Pi.single i 1)
                    (coefficientCutoff M.nu L omega).toFun -
                  Mu (cubeSet Q) (Pi.single j 1, 0)
                    (coefficientCutoff M.nu L omega).toFun := by
            funext omega
            exact coarseBlockMatrix_lowerLeft_apply (cubeSet Q)
              (coefficientCutoff M.nu L omega).toFun i j
          rw [hEq]
          exact ((hMu _).sub (hMu _)).sub (hMu _)
      | inr j =>
          have hEq : (fun omega : CutoffSample d =>
              toFullBlockMat (coarseBlockMatrix (cubeSet Q)
                (coefficientCutoff M.nu L omega).toFun) (Sum.inr i) (Sum.inr j)) =
              fun omega : CutoffSample d =>
                if i = j then
                  2 * Mu (cubeSet Q) (0, Pi.single i 1)
                    (coefficientCutoff M.nu L omega).toFun
                else
                  Mu (cubeSet Q) ((0, Pi.single i 1) + (0, Pi.single j 1))
                      (coefficientCutoff M.nu L omega).toFun -
                    Mu (cubeSet Q) (0, Pi.single i 1)
                      (coefficientCutoff M.nu L omega).toFun -
                    Mu (cubeSet Q) (0, Pi.single j 1)
                      (coefficientCutoff M.nu L omega).toFun := by
            funext omega
            exact coarseBlockMatrix_lowerRight_apply (cubeSet Q)
              (coefficientCutoff M.nu L omega).toFun i j
          rw [hEq]
          by_cases hij : i = j
          · simp only [ite_eq_left hij]
            exact (hMu _).const_mul 2
          · simp only [ite_eq_right hij]
            exact ((hMu _).sub (hMu _)).sub (hMu _)

private theorem continuous_fullBlockReflect_self :
    Continuous (Ch04.fullBlockReflect (d := d)) := by
  refine continuous_pi_iff.2 fun alpha => ?_
  refine continuous_pi_iff.2 fun beta => ?_
  cases alpha <;> cases beta <;>
    dsimp only [Ch04.fullBlockReflect, toFullBlockMat, ofFullBlockMat, blockReflect] <;>
    fun_prop

private theorem continuous_blockJQuadraticFullBlockMat (P Qv : BlockVec d) :
    Continuous fun A : FullBlockMat d => Ch04.blockJQuadraticFullBlockMat A P Qv := by
  have hquad : ∀ x : FullBlockVec d,
      Continuous fun A : FullBlockMat d => Ch04.fullBlockQuadraticCh04 A x := by
    intro x
    unfold Ch04.fullBlockQuadraticCh04 dotProduct Matrix.mulVec
    fun_prop
  unfold Ch04.blockJQuadraticFullBlockMat
  exact ((continuous_const.mul (hquad (toFullBlockVec P))).add
      (continuous_const.mul
        ((hquad (toFullBlockVec Qv)).comp continuous_fullBlockReflect_self))).sub
    continuous_const

/-- **The translated-cube response observable is cube-local.**  It reads only
the integral-local information of the cutoff `a_L` on any region containing the
closed cube. -/
theorem measurable_cutoffResponseJFromCommonCoarseBlock_cutoffSampleLocal
    (M : ABKModel d) (L : ℤ) (Q : TriadicCube d) {U : Set (Vec d)}
    (hQU : cubeSet Q ⊆ U) (p q : Vec d) :
    Measurable[cutoffSampleLocalSigma M L U]
      (Observable.cutoffResponseJFromCommonCoarseBlock M L Q p q) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M L U
  have hrep : Measurable (Observable.cutoffCoarseFullBlockRepresentative M L Q) :=
    measurable_cutoffSampleLocalSigma_of_ae_eq M L U
      (measurable_cutoffCoarseFullBlockRaw_cutoffSampleLocal M L Q hQU)
      (Observable.cutoffCoarseFullBlockMatrix_ae_eq_representative M L Q).symm
  change Measurable fun omega : CutoffSample d => 2 * Ch04.blockJQuadraticFullBlockMat
    (Observable.cutoffCoarseFullBlockRepresentative M L Q omega)
    (Observable.responseJFirstHalfBlockLoad p q)
    (Observable.responseJSecondHalfBlockLoad p q)
  exact (((continuous_blockJQuadraticFullBlockMat
    (Observable.responseJFirstHalfBlockLoad p q)
    (Observable.responseJSecondHalfBlockLoad p q)).measurable).comp hrep).const_mul 2

/-- The closed site cube sits inside the observation region of its own site. -/
theorem cubeSet_siteCube_subset_siteRegion (n : ℤ) (u : Fin d → ℤ) :
    cubeSet (siteCube n u) ⊆ siteRegion n ({u} : Set (Fin d → ℤ)) := by
  refine subset_trans ?_
    (cubeTreeRegion_subset_siteRegion (Set.mem_singleton u))
  refine cubeSet_subset_cubeTreeRegion_of_mem_descendantsAtScale
    (i := 0) (by simp) ?_
  simp [descendantsAtScale]

/-- **Producer 2.**  The site response observable reads only the integral-local
information of the cutoff `a_L` on the cube tree of its own site, which is the
locality hypothesis consumed by the grid concentration engine. -/
theorem measurable_siteResponseJ_cutoffSampleLocalSigma_siteRegion
    (M : ABKModel d) (L n : ℤ) (u : Fin d → ℤ) (p q : Vec d) :
    Measurable[cutoffSampleLocalSigma M L (siteRegion n ({u} : Set (Fin d → ℤ)))]
      (Observable.cutoffResponseJFromCommonCoarseBlock M L (siteCube n u) p q) :=
  measurable_cutoffResponseJFromCommonCoarseBlock_cutoffSampleLocal M L
    (siteCube n u) (cubeSet_siteCube_subset_siteRegion n u) p q

/-! ## The site observable -/

/-- The Section 3.5 per-site response observable: the common coarse-block
evaluation on the site cube `u + square_n` at the loads
`sigmabar_L^{-1/2} e , sigmabar_L^{1/2} e` of the manuscript. -/
def siteResponseJ (M : ABKModel d) (L n : ℤ) (u : Fin d → ℤ) (e : Vec d) :
    CutoffSample d → ℝ :=
  Observable.cutoffResponseJFromCommonCoarseBlock M L (siteCube n u)
    (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
    (Observable.sqrtLoad (Annealed.sigmaBar M L) e)

theorem measurable_siteResponseJ (M : ABKModel d) (L n : ℤ) (u : Fin d → ℤ)
    (e : Vec d) : Measurable (siteResponseJ M L n u e) :=
  Observable.measurable_cutoffResponseJFromCommonCoarseBlock M L (siteCube n u) _ _

/-- **The literal value of the site observable.**  On one probability-one event
the site observable is the manuscript's
`J(u + square_n, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)`. -/
theorem ae_siteResponseJ_eq_responseJ (M : ABKModel d) (L n : ℤ) (u : Fin d → ℤ)
    (e : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      siteResponseJ M L n u e omega =
        ResponseJ (cubeSet (siteCube n u))
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (coefficientCutoff M.nu L omega).toFun := by
  filter_upwards
    [ae_forall_cutoffResponseJFromCommonCoarseBlock_eq_responseJ M L (siteCube n u)]
    with omega homega
  exact homega _ _

theorem ae_siteResponseJ_nonneg (M : ABKModel d) (L n : ℤ) (u : Fin d → ℤ)
    (e : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, 0 ≤ siteResponseJ M L n u e omega := by
  filter_upwards [ae_siteResponseJ_eq_responseJ M L n u e] with omega homega
  rw [homega]
  exact Ch04.restrictionResponseJObservableCubeSet_nonneg (siteCube n u) _ _ _

/-! ## Producer 3: translation covariance and centering -/

/-- Almost-sure statements travel along the sample translation, because the
genuine cutoff sample law is invariant under it. -/
private theorem ae_comp_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {P : CutoffSample d → Prop}
    (h : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, P omega) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      P (translateCutoffSample z omega) := by
  rw [ae_iff] at h ⊢
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null h
  have hpre : (cutoffSampleLaw M).toMeasure (translateCutoffSample z ⁻¹' N) = 0 := by
    rw [← Measure.map_apply (measurable_translateCutoffSample z) hNmeas,
      map_translateCutoffSample_cutoffSampleLaw]
    exact hN0
  refine measure_mono_null (fun omega homega => ?_) hpre
  have hmem : translateCutoffSample z omega ∈ {a : CutoffSample d | ¬ P a} := homega
  exact hsub hmem

/-- **Translation covariance of the literal cutoff response.**  The response of
the cutoff on a triadic cube is the response on the concentric origin cube of
the translated sample. -/
theorem responseJ_cubeSet_cutoff_translate (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) (p q : Vec d) (omega : CutoffSample d) :
    ResponseJ (cubeSet Q) p q (coefficientCutoff M.nu L omega).toFun =
      ResponseJ (cubeSet (originCube d Q.scale)) p q
        (coefficientCutoff M.nu L
          (translateCutoffSample (triadicCubeShift Q) omega)).toFun := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q,
    ResponseJ_translateSet_eq_translateCoeffField,
    coefficientCutoff_translateCutoffSample]
  rfl

/-- **The site observable is the origin observable of the translated sample.**
This is the exact form in which the manuscript's stationarity is used at the
site cubes of the grid. -/
theorem ae_siteResponseJ_eq_comp_translate (M : ABKModel d) (L n : ℤ)
    (u : Fin d → ℤ) (e : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      siteResponseJ M L n u e omega =
        Observable.cutoffResponseJ M n L e
          (translateCutoffSample (triadicCubeShift (siteCube n u)) omega) := by
  have horigin := ae_comp_translateCutoffSample M (triadicCubeShift (siteCube n u))
    (ae_forall_cutoffResponseJFromCommonCoarseBlock_eq_responseJ M L (originCube d n))
  filter_upwards [ae_siteResponseJ_eq_responseJ M L n u e, horigin]
    with omega hsite hshift
  rw [hsite, responseJ_cubeSet_cutoff_translate M L (siteCube n u)]
  rw [siteCube_scale]
  exact (hshift _ _).symm

/-- **Producer 3, stationarity half.**  The mean of the site observable does not
depend on the site: it is the mean at the origin cube of the same scale. -/
theorem integral_siteResponseJ_eq_integral_cutoffResponseJ (M : ABKModel d)
    (L n : ℤ) (u : Fin d → ℤ) (e : Vec d) :
    ∫ omega, siteResponseJ M L n u e omega ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega, Observable.cutoffResponseJ M n L e omega
        ∂(cutoffSampleLaw M).toMeasure := by
  let : NeZero d := neZero_of_model M
  rw [integral_congr_ae (ae_siteResponseJ_eq_comp_translate M L n u e)]
  calc
    ∫ omega, Observable.cutoffResponseJ M n L e
          (translateCutoffSample (triadicCubeShift (siteCube n u)) omega)
          ∂(cutoffSampleLaw M).toMeasure =
        ∫ y, Observable.cutoffResponseJ M n L e y
          ∂(Measure.map (translateCutoffSample (triadicCubeShift (siteCube n u)))
            (cutoffSampleLaw M).toMeasure) :=
      (integral_map
        (measurable_translateCutoffSample (triadicCubeShift (siteCube n u))).aemeasurable
        (Observable.measurable_cutoffResponseJ M n L e).aestronglyMeasurable).symm
    _ = ∫ y, Observable.cutoffResponseJ M n L e y ∂(cutoffSampleLaw M).toMeasure := by
      rw [map_translateCutoffSample_cutoffSampleLaw]

/-- The recentred site observable of the grid display. -/
def siteCenteredResponseJ (M : ABKModel d) (L n : ℤ) (u : Fin d → ℤ) (e : Vec d) :
    CutoffSample d → ℝ :=
  fun omega => siteResponseJ M L n u e omega -
    ∫ omega', siteResponseJ M L n u e omega' ∂(cutoffSampleLaw M).toMeasure

theorem measurable_siteCenteredResponseJ (M : ABKModel d) (L n : ℤ)
    (u : Fin d → ℤ) (e : Vec d) : Measurable (siteCenteredResponseJ M L n u e) :=
  (measurable_siteResponseJ M L n u e).sub measurable_const

theorem measurable_siteCenteredResponseJ_cutoffSampleLocalSigma_siteRegion
    (M : ABKModel d) (L n : ℤ) (u : Fin d → ℤ) (e : Vec d) :
    Measurable[cutoffSampleLocalSigma M L (siteRegion n ({u} : Set (Fin d → ℤ)))]
      (siteCenteredResponseJ M L n u e) :=
  (measurable_siteResponseJ_cutoffSampleLocalSigma_siteRegion M L n u _ _).sub
    measurable_const

/-- **Producer 3, centering half.**  The recentred site observable integrates to
zero, which is the centering hypothesis consumed by the grid concentration
engine.  Integrability is the only input; it is produced by the per-site tail
below. -/
theorem integral_siteCenteredResponseJ_eq_zero (M : ABKModel d) (L n : ℤ)
    (u : Fin d → ℤ) (e : Vec d)
    (hint : Integrable (siteResponseJ M L n u e) (cutoffSampleLaw M).toMeasure) :
    ∫ omega, siteCenteredResponseJ M L n u e omega
      ∂(cutoffSampleLaw M).toMeasure = 0 := by
  unfold siteCenteredResponseJ
  rw [integral_sub hint (integrable_const _)]
  simp

/-! ## Producer 4: the per-site two-term tail -/

/-- The per-site lane constant at a stretched-exponential exponent: the square
rule of the two-term error bound costs a factor `2`, and absorbing the mean
shift into the same lane costs one more first-moment constant. -/
def siteLaneConst (sig : ℝ) : ℝ := 2 * (1 + gammaMomentConst sig)

theorem siteLaneConst_pos {sig : ℝ} (hsig : 0 < sig) : 0 < siteLaneConst sig := by
  have h := gammaMomentConst_pos hsig
  unfold siteLaneConst
  linarith

/-- A weak-Orlicz upper tail is preserved by the sample translation, because
the genuine cutoff sample law is invariant under it. -/
private theorem isBigOWith_comp_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {Psi : ℝ → ℝ} {Y : CutoffSample d → ℝ} {A : ℝ} (hYm : Measurable Y)
    (hY : IsBigOWith (cutoffSampleLaw M).toMeasure Psi Y A) :
    IsBigOWith (cutoffSampleLaw M).toMeasure Psi
      (fun omega => Y (translateCutoffSample z omega)) A := by
  intro t ht
  have hmeas : MeasurableSet (upperTailEvent Y (A * t)) :=
    measurableSet_lt measurable_const hYm
  have hpre : (cutoffSampleLaw M).toMeasure
        (translateCutoffSample z ⁻¹' upperTailEvent Y (A * t)) =
      (cutoffSampleLaw M).toMeasure (upperTailEvent Y (A * t)) := by
    rw [← Measure.map_apply (measurable_translateCutoffSample z) hmeas,
      map_translateCutoffSample_cutoffSampleLaw]
  calc (cutoffSampleLaw M).toMeasure.real
        (upperTailEvent (fun omega => Y (translateCutoffSample z omega)) (A * t))
      = (cutoffSampleLaw M).toMeasure.real (upperTailEvent Y (A * t)) := by
        unfold MeasureTheory.Measure.real
        exact congrArg ENNReal.toReal hpre
    _ ≤ (Psi t)⁻¹ := hY ht

/-- Adding a nonnegative constant costs exactly that constant in the
weak-Orlicz amplitude. -/
private theorem isBigOWith_add_const {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {Psi : ℝ → ℝ} {Y : Omega → ℝ}
    {A c : ℝ} (hc : 0 ≤ c)
    (hY : IsBigOWith mu Psi Y A) :
    IsBigOWith mu Psi (fun omega => Y omega + c) (A + c) := by
  intro t ht
  refine le_trans (measureReal_mono ?_) (hY ht)
  intro omega homega
  have hgt : (A + c) * t < Y omega + c := homega
  have ht0 : (0 : ℝ) ≤ t - 1 := by linarith
  change A * t < Y omega
  nlinarith

/-- First moment and integrability from a one-sided stretched-exponential tail
of a nonnegative variable. -/
private theorem integrable_and_integral_le_of_isBigOWith_gammaSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {Y : Omega → ℝ} {K sig : ℝ} (hsig : 0 < sig)
    (hK : 0 < K) (hnn : ∀ omega, 0 ≤ Y omega) (hm : Measurable Y)
    (hY : IsBigOWith mu (gammaSigma sig) Y K) :
    Integrable Y mu ∧ ∫ omega, Y omega ∂mu ≤ gammaMomentConst sig * K := by
  have hint := integrable_rpow_of_isBigOWith_gammaSigma (μ := mu) (Y := Y) (K := K)
    (σ := sig) (p := 1) hsig hK le_rfl hnn hm.aemeasurable hY
  have hmom := integral_rpow_le_of_isBigOWith_gammaSigma (μ := mu) (Y := Y) (K := K)
    (σ := sig) (p := 1) hsig hK le_rfl hnn hm.aemeasurable hY
  refine ⟨by simpa only [Real.rpow_one] using hint, ?_⟩
  simpa only [Real.rpow_one, Real.one_rpow, mul_one] using hmom

/-- The two amplitudes of a two-term one-sided weak-Orlicz relation are
positive; the datum already carries their positivity. -/
private theorem pos_of_isTwoTermBigOWith {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {Psi1 Psi2 : ℝ → ℝ} {X : Omega → ℝ} {A1 A2 : ℝ}
    (h : Probability.IsTwoTermBigOWith mu Psi1 Psi2 X A1 A2) : 0 < A1 ∧ 0 < A2 := by
  obtain ⟨-, -, -, -, h1, h2, -, -, -, -, -, -⟩ := h
  exact ⟨h1, h2⟩

/-- **The square rule with the two lanes kept separate.**  A two-term
`(Gamma_2, Gamma_{1/2})` bound for a nonnegative variable squares into two
nonnegative lanes, one `Gamma_1` at the squared linear amplitude and one
`Gamma_{1/4}` at the squared rare amplitude, whose sum dominates the square
everywhere. -/
private theorem exists_squareLanes (M : ABKModel d) (L n : ℤ) {s : ℝ} (hs : 0 < s) {A B : ℝ}
    (hErr : Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationErrorRepresentative M L n hs
        (Annealed.sigmaBar M L)) A B) :
    ∃ Y1 Z1 : CutoffSample d → ℝ,
      Measurable Y1 ∧ Measurable Z1 ∧ (∀ omega, 0 ≤ Y1 omega) ∧
        (∀ omega, 0 ≤ Z1 omega) ∧
          IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1) Y1 (2 * A ^ 2) ∧
            IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) Z1
              (2 * B ^ 2) ∧
              ∀ omega,
                Observable.cutoffHomogenizationErrorRepresentative M L n hs
                    (Annealed.sigmaBar M L) omega ^ 2 ≤ Y1 omega + Z1 omega := by
  obtain ⟨Y, Z, -, -, hA, hB, -, hYm, hZm, hdom, hYt, hZt⟩ := hErr
  refine ⟨fun omega => 2 * max 0 (Y omega) ^ 2, fun omega => 2 * max 0 (Z omega) ^ 2,
    ((measurable_const.max hYm).pow_const 2).const_mul 2,
    ((measurable_const.max hZm).pow_const 2).const_mul 2,
    fun omega => by positivity, fun omega => by positivity, ?_, ?_, ?_⟩
  · have hsq : IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
        (fun omega => max 0 (Y omega) ^ 2) (A ^ 2) := by
      have h := (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
        (μ := (cutoffSampleLaw M).toMeasure) (X := fun omega => max 0 (Y omega))
        (K := A) (σ := 2) hA.le (fun omega => le_max_left _ _)).1
        (Tail.isBigOWith_max_zero hA hYt)
      simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using h
    exact IsBigOWith.const_mul (by norm_num) hsq
  · have hsq : IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
        (fun omega => max 0 (Z omega) ^ 2) (B ^ 2) := by
      have h := (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
        (μ := (cutoffSampleLaw M).toMeasure) (X := fun omega => max 0 (Z omega))
        (K := B) (σ := 1 / 2) hB.le (fun omega => le_max_left _ _)).1
        (Tail.isBigOWith_max_zero hB hZt)
      simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using h
    exact IsBigOWith.const_mul (by norm_num) hsq
  · intro omega
    have hErrnn : 0 ≤ Observable.cutoffHomogenizationErrorRepresentative M L n hs
        (Annealed.sigmaBar M L) omega :=
      Observable.cutoffHomogenizationErrorRepresentative_nonneg M L n hs
        (Annealed.sigmaBar M L) omega
    have hle : Observable.cutoffHomogenizationErrorRepresentative M L n hs
        (Annealed.sigmaBar M L) omega ≤ max 0 (Y omega) + max 0 (Z omega) :=
      (hdom omega).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
    have hsq := pow_le_pow_left₀ hErrnn hle 2
    nlinarith [sq_nonneg (max 0 (Y omega) - max 0 (Z omega))]

/-- **The site lanes.**  The two squared lanes of the error, transported to the
site cube by the sample translation and shifted by the first moment of each
lane, dominate the absolute recentred site response almost surely and carry the
two amplitudes of the display. -/
private theorem exists_siteLanes (M : ABKModel d) (L n : ℤ) {s : ℝ}
    (hs : 0 < s) (u : Fin d → ℤ) {e : Vec d} (he : Ch02.vecNorm e = 1) {A B : ℝ}
    (hErr : Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationErrorRepresentative M L n hs
        (Annealed.sigmaBar M L)) A B) :
    ∃ W1 W4 : CutoffSample d → ℝ,
      Measurable W1 ∧ Measurable W4 ∧
        IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1) W1
          (siteLaneConst 1 * A ^ 2) ∧
          IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) W4
            (siteLaneConst (1 / 4) * B ^ 2) ∧
            Integrable (siteResponseJ M L n u e) (cutoffSampleLaw M).toMeasure ∧
              ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
                |siteCenteredResponseJ M L n u e omega| ≤ W1 omega + W4 omega := by
  obtain ⟨hA, hB⟩ := pos_of_isTwoTermBigOWith hErr
  obtain ⟨Y1, Z1, hY1m, hZ1m, hY1nn, hZ1nn, hY1t, hZ1t, hlane⟩ :=
    exists_squareLanes M L n hs hErr
  set z : Vec d := triadicCubeShift (siteCube n u) with hzdef
  have hmp : MeasurePreserving (translateCutoffSample z)
      (cutoffSampleLaw M).toMeasure (cutoffSampleLaw M).toMeasure :=
    ⟨measurable_translateCutoffSample z, map_translateCutoffSample_cutoffSampleLaw M z⟩
  obtain ⟨hY1int, hY1mom⟩ := integrable_and_integral_le_of_isBigOWith_gammaSigma
    (mu := (cutoffSampleLaw M).toMeasure) (Y := Y1) (K := 2 * A ^ 2) (sig := 1)
    one_pos (by positivity) hY1nn hY1m hY1t
  obtain ⟨hZ1int, hZ1mom⟩ := integrable_and_integral_le_of_isBigOWith_gammaSigma
    (mu := (cutoffSampleLaw M).toMeasure) (Y := Z1) (K := 2 * B ^ 2) (sig := 1 / 4)
    (by norm_num) (by positivity) hZ1nn hZ1m hZ1t
  have horigin : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffResponseJ M n L e omega ≤ Y1 omega + Z1 omega := by
    filter_upwards
      [ae_forall_cutoffResponseJ_le_observationHomogenizationError_sq M n L hs]
      with omega hle
    exact (hle e he).trans (hlane omega)
  have hJnn : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      0 ≤ Observable.cutoffResponseJ M n L e omega := by
    filter_upwards [Observable.ae_forall_cutoffResponseJ_nonneg M n L] with omega homega
    exact homega e
  have hmeanle : ∫ omega, Observable.cutoffResponseJ M n L e omega
        ∂(cutoffSampleLaw M).toMeasure ≤
      gammaMomentConst 1 * (2 * A ^ 2) + gammaMomentConst (1 / 4) * (2 * B ^ 2) := by
    calc ∫ omega, Observable.cutoffResponseJ M n L e omega
          ∂(cutoffSampleLaw M).toMeasure
        ≤ ∫ omega, (Y1 omega + Z1 omega) ∂(cutoffSampleLaw M).toMeasure :=
          integral_mono_of_nonneg hJnn (hY1int.add hZ1int) horigin
      _ = (∫ omega, Y1 omega ∂(cutoffSampleLaw M).toMeasure) +
            ∫ omega, Z1 omega ∂(cutoffSampleLaw M).toMeasure :=
          integral_add hY1int hZ1int
      _ ≤ gammaMomentConst 1 * (2 * A ^ 2) +
            gammaMomentConst (1 / 4) * (2 * B ^ 2) := add_le_add hY1mom hZ1mom
  have hmean0 : 0 ≤ ∫ omega, Observable.cutoffResponseJ M n L e omega
      ∂(cutoffSampleLaw M).toMeasure := integral_nonneg_of_ae hJnn
  have hcomp : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffResponseJ M n L e (translateCutoffSample z omega) ≤
        Y1 (translateCutoffSample z omega) + Z1 (translateCutoffSample z omega) :=
    ae_comp_translateCutoffSample M z horigin
  have hGint : Integrable (fun omega => Y1 (translateCutoffSample z omega) +
      Z1 (translateCutoffSample z omega)) (cutoffSampleLaw M).toMeasure :=
    (hmp.integrable_comp (hY1int.add hZ1int).aestronglyMeasurable).mpr
      (hY1int.add hZ1int)
  have hsiteInt : Integrable (siteResponseJ M L n u e)
      (cutoffSampleLaw M).toMeasure := by
    refine Integrable.mono' hGint
      (measurable_siteResponseJ M L n u e).aestronglyMeasurable ?_
    filter_upwards [ae_siteResponseJ_eq_comp_translate M L n u e,
      ae_siteResponseJ_nonneg M L n u e, hcomp] with omega heq hnn hle
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, heq]
    exact hle
  set m : ℝ := ∫ omega, siteResponseJ M L n u e omega ∂(cutoffSampleLaw M).toMeasure
    with hmdef
  have hmEq : m = ∫ omega, Observable.cutoffResponseJ M n L e omega
      ∂(cutoffSampleLaw M).toMeasure :=
    integral_siteResponseJ_eq_integral_cutoffResponseJ M L n u e
  have hmnn : 0 ≤ m := by rw [hmEq]; exact hmean0
  have hmle : m ≤ gammaMomentConst 1 * (2 * A ^ 2) +
      gammaMomentConst (1 / 4) * (2 * B ^ 2) := by rw [hmEq]; exact hmeanle
  have hc1 : (0 : ℝ) ≤ gammaMomentConst 1 * (2 * A ^ 2) :=
    mul_nonneg (gammaMomentConst_pos one_pos).le (by positivity)
  have hc4 : (0 : ℝ) ≤ gammaMomentConst (1 / 4) * (2 * B ^ 2) :=
    mul_nonneg (gammaMomentConst_pos (by norm_num)).le (by positivity)
  refine ⟨fun omega => Y1 (translateCutoffSample z omega) +
      gammaMomentConst 1 * (2 * A ^ 2),
    fun omega => Z1 (translateCutoffSample z omega) +
      gammaMomentConst (1 / 4) * (2 * B ^ 2),
    (hY1m.comp (measurable_translateCutoffSample z)).add measurable_const,
    (hZ1m.comp (measurable_translateCutoffSample z)).add measurable_const, ?_, ?_,
    hsiteInt, ?_⟩
  · have hamp : 2 * A ^ 2 + gammaMomentConst 1 * (2 * A ^ 2) =
        siteLaneConst 1 * A ^ 2 := by
      unfold siteLaneConst
      ring
    rw [← hamp]
    exact isBigOWith_add_const hc1
      (isBigOWith_comp_translateCutoffSample M z hY1m hY1t)
  · have hamp : 2 * B ^ 2 + gammaMomentConst (1 / 4) * (2 * B ^ 2) =
        siteLaneConst (1 / 4) * B ^ 2 := by
      unfold siteLaneConst
      ring
    rw [← hamp]
    exact isBigOWith_add_const hc4
      (isBigOWith_comp_translateCutoffSample M z hZ1m hZ1t)
  · filter_upwards [ae_siteResponseJ_eq_comp_translate M L n u e,
      ae_siteResponseJ_nonneg M L n u e, hcomp] with omega heq hnn hle
    have hcent : siteCenteredResponseJ M L n u e omega =
        siteResponseJ M L n u e omega - m := rfl
    have hJle : siteResponseJ M L n u e omega ≤
        Y1 (translateCutoffSample z omega) + Z1 (translateCutoffSample z omega) := by
      rw [heq]
      exact hle
    rw [hcent, abs_le]
    constructor <;> linarith

/-- **Producer 4, integrability half.**  The site observable is integrable, so
the centering integral of Producer 3 is available. -/
theorem integrable_siteResponseJ (M : ABKModel d) (L n : ℤ) {s : ℝ} (hs : 0 < s)
    (u : Fin d → ℤ) {e : Vec d} (he : Ch02.vecNorm e = 1) {A B : ℝ} :
    letI : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2))
        (Observable.cutoffHomogenizationErrorRepresentative M L n hs
          (Annealed.sigmaBar M L)) A B →
      Integrable (siteResponseJ M L n u e) (cutoffSampleLaw M).toMeasure := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  intro hErr
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := exists_siteLanes M L n hs u he hErr
  exact hint

/-- **Producer 4.**  The absolute recentred site response carries the
two-term one-sided weak-Orlicz relation at the exponents `1` and `1/4`, with
the two amplitudes obtained by squaring the amplitudes of the preceding-error
clause.  This is the per-member tail hypothesis consumed by the grid
concentration engine, and it is the un-decayed form of the two amplitudes
printed at ABK26. -/
theorem isTwoTermBigOWith_abs_siteCenteredResponseJ (M : ABKModel d) (L n : ℤ)
    {s : ℝ} (hs : 0 < s) (u : Fin d → ℤ) {e : Vec d} (he : Ch02.vecNorm e = 1)
    {A B : ℝ} :
    letI : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2))
        (Observable.cutoffHomogenizationErrorRepresentative M L n hs
          (Annealed.sigmaBar M L)) A B →
      Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma 1) (gammaSigma (1 / 4))
        (fun omega => |siteCenteredResponseJ M L n u e omega|)
        (siteLaneConst 1 * A ^ 2) (siteLaneConst (1 / 4) * B ^ 2) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  intro hErr
  obtain ⟨hA, hB⟩ := pos_of_isTwoTermBigOWith hErr
  obtain ⟨W1, W4, hW1m, hW4m, hW1t, hW4t, -, hdom⟩ :=
    exists_siteLanes M L n hs u he hErr
  exact Tail.isTwoTermBigOWith_of_ae_le
    (Probability.isAdmissibleTail_gammaSigma (by norm_num : (0 : ℝ) < 1))
    (Probability.isAdmissibleTail_gammaSigma (by norm_num : (0 : ℝ) < 1 / 4))
    (mul_pos (siteLaneConst_pos one_pos) (pow_pos hA 2))
    (mul_pos (siteLaneConst_pos (by norm_num)) (pow_pos hB 2))
    (continuous_abs.measurable.comp (measurable_siteCenteredResponseJ M L n u e))
    hW1m hW4m hdom hW1t hW4t

/-- The centering identity of Producer 3, with its integrability input supplied
by the per-site tail. -/
theorem integral_siteCenteredResponseJ_eq_zero_of_twoTerm (M : ABKModel d)
    (L n : ℤ) {s : ℝ} (hs : 0 < s) (u : Fin d → ℤ) {e : Vec d}
    (he : Ch02.vecNorm e = 1) {A B : ℝ} :
    letI : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2))
        (Observable.cutoffHomogenizationErrorRepresentative M L n hs
          (Annealed.sigmaBar M L)) A B →
      ∫ omega, siteCenteredResponseJ M L n u e omega
        ∂(cutoffSampleLaw M).toMeasure = 0 := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  intro hErr
  exact integral_siteCenteredResponseJ_eq_zero M L n u e
    (integrable_siteResponseJ M L n hs u he hErr)

/-! ## Assembly: the grid concentration display -/

/-- **The averaged quantity is the manuscript's.**  Because all site means
coincide (Producer 3), the grid average of the recentred site responses is the
grid average of the responses themselves minus the single number
`E[J(square_n, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)]`, which is what
ABK26 subtracts. -/
theorem gridAverage_siteCenteredResponseJ_eq_sub_integral (M : ABKModel d)
    (L n : ℤ) (k : ℕ) (e : Vec d) (omega : CutoffSample d) :
    ((cubeFinset (d := d) k).card : ℝ)⁻¹ *
        ∑ u ∈ cubeFinset (d := d) k, siteCenteredResponseJ M L n u e omega =
      ((cubeFinset (d := d) k).card : ℝ)⁻¹ *
          (∑ u ∈ cubeFinset (d := d) k, siteResponseJ M L n u e omega) -
        ∫ omega', Observable.cutoffResponseJ M n L e omega'
          ∂(cutoffSampleLaw M).toMeasure := by
  have hcard : ((cubeFinset (d := d) k).card : ℝ) ≠ 0 := by
    have hpos : 0 < (cubeFinset (d := d) k).card := (cubeFinset_nonempty k).card_pos
    exact_mod_cast hpos.ne'
  have hpt : ∀ u ∈ cubeFinset (d := d) k,
      siteCenteredResponseJ M L n u e omega =
        siteResponseJ M L n u e omega -
          ∫ omega', Observable.cutoffResponseJ M n L e omega'
            ∂(cutoffSampleLaw M).toMeasure := by
    intro u _
    change siteResponseJ M L n u e omega -
        ∫ omega', siteResponseJ M L n u e omega' ∂(cutoffSampleLaw M).toMeasure = _
    rw [integral_siteResponseJ_eq_integral_cutoffResponseJ M L n u e]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- **The Section 3.5 grid concentration display at the genuine cutoff law**
(ABK26, proof of `p.homogenization.step`).

For every unit direction `e` and every corridor pair `L <= n`, the grid average
over `3 ^ n Z^d cap square_m` (written at relative depth `k = m - n`) of the
recentred site responses satisfies the one-sided two-term weak-Orlicz relation
at the exponents `1` and `1/4`, with both amplitudes carrying the manuscript's
grid gain `3 ^ (-d k / 2)`: the `Gamma_1` amplitude is a constant times the
square of the linear amplitude of the preceding-error clause, and the
`Gamma_{1/4}` amplitude is a constant times the square of its rare amplitude.
All constants depend only on `d`.

The four per-site inputs of the concentration engine are the producers above;
the engine itself, the colouring, and the deterministic lane allocation are
consumed, not re-derived.  This is a Provider endpoint and carries no
source-node status by itself. -/
theorem isTwoTermBigOWith_gridAverage_siteCenteredResponseJ (M : ABKModel d)
    {L n : ℤ} (hLn : L ≤ n) (k : ℕ) {s : ℝ} (hs : 0 < s) {e : Vec d}
    (he : Ch02.vecNorm e = 1) {A B : ℝ} :
    letI : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2))
        (Observable.cutoffHomogenizationErrorRepresentative M L n hs
          (Annealed.sigmaBar M L)) A B →
      Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma 1) (gammaSigma (1 / 4))
        (fun omega => |((cubeFinset (d := d) k).card : ℝ)⁻¹ *
          ∑ u ∈ cubeFinset (d := d) k, siteCenteredResponseJ M L n u e omega|)
        (gridConcentrationConst d 1 *
          (Orlicz.mixedLinearConst 2 * (siteLaneConst 1 * A ^ 2)) * gridDecay d k)
        (gridConcentrationConst d (1 / 4) *
          (Orlicz.mixedQuarticConst 2 * (siteLaneConst (1 / 4) * B ^ 2)) *
          gridDecay d k) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  intro hErr
  obtain ⟨hA, hB⟩ := pos_of_isTwoTermBigOWith hErr
  have hK1 : (0 : ℝ) < siteLaneConst 1 * A ^ 2 :=
    mul_pos (siteLaneConst_pos one_pos) (pow_pos hA 2)
  have hK4 : (0 : ℝ) < siteLaneConst (1 / 4) * B ^ 2 :=
    mul_pos (siteLaneConst_pos (by norm_num)) (pow_pos hB 2)
  have hlanes : ∀ u : Fin d → ℤ, ∃ Y Z : CutoffSample d → ℝ,
      (∀ omega, siteCenteredResponseJ M L n u e omega = Y omega + Z omega) ∧
        Measurable[cutoffSampleLocalSigma M L
          (siteRegion n ({u} : Set (Fin d → ℤ)))] Y ∧
          Measurable[cutoffSampleLocalSigma M L
            (siteRegion n ({u} : Set (Fin d → ℤ)))] Z ∧
            Measurable Y ∧ Measurable Z ∧
              IsBigO (cutoffSampleLaw M).toMeasure (gammaSigma 1) Y
                (Orlicz.mixedLinearConst 2 * (siteLaneConst 1 * A ^ 2)) ∧
                IsBigO (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) Z
                  (Orlicz.mixedQuarticConst 2 * (siteLaneConst (1 / 4) * B ^ 2)) ∧
                  (∫ omega, Y omega ∂(cutoffSampleLaw M).toMeasure = 0) ∧
                    ∫ omega, Z omega ∂(cutoffSampleLaw M).toMeasure = 0 := by
    intro u
    exact Orlicz.exists_centeredTwoLaneSplit_of_isTwoTermBigOWith_abs
      (m := cutoffSampleLocalSigma M L (siteRegion n ({u} : Set (Fin d → ℤ))))
      hK1 hK4
      (measurable_siteCenteredResponseJ_cutoffSampleLocalSigma_siteRegion M L n u e)
      (measurable_siteCenteredResponseJ M L n u e)
      (isTwoTermBigOWith_abs_siteCenteredResponseJ M L n hs u he hErr)
      (integral_siteCenteredResponseJ_eq_zero_of_twoTerm M L n hs u he hErr)
  choose Y Z hYZ hYloc hZloc hYm hZm hYt hZt hY0 hZ0 using hlanes
  exact isTwoTermBigOWith_gridAverage_of_twoLane M hLn k
    (mul_pos (Orlicz.mixedLinearConst_pos 2) hK1)
    (mul_pos (Orlicz.mixedQuarticConst_pos 2) hK4)
    (X := fun u => siteCenteredResponseJ M L n u e) (Y := Y) (Z := Z)
    (fun u _ omega => hYZ u omega) (fun u _ => hYloc u) hYm (fun u _ => hYt u)
    (fun u _ => hY0 u) (fun u _ => hZloc u) hZm (fun u _ => hZt u)
    fun u _ => hZ0 u

end

end Algsuperdiff.Section3.Provider.Homogenization
