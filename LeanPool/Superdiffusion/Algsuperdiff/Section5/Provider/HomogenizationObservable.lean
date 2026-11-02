/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.LocalizedTailData
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ComparatorComparison
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CutoffFieldLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.ScalarWeakMaximumPrinciple
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationGreen
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorContinuity

/-!
# HomogenizationObservable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The homogenization observable of a triadic cube

The stopped-moment bounds of the displacement estimates take as input an observable that is a
weak solution of the homogeneous equation `-∇ · a ∇u = 0` on a triadic cube for the stream
coefficient, has the trace of a smooth compactly supported function `bd`, agrees with `bd` off
the cube, is bounded, is continuous on the cube, and is measurable.  This file constructs such an
observable for every centre, every scale and every datum.

The construction has three steps.

* *Existence.*  The Dirichlet problem with the datum `bd` and vanishing forcing is solved by
  the Lax–Milgram theorem of the library: the solution is `bd + w` with `w` of zero trace, and
  the skew part of the stream coefficient plays no role since only the coercivity of the
  symmetric part `ν I` enters.
* *The bound.*  The weak maximum principle for the homogeneous equation bounds the solution
  almost everywhere on the cube by the uniform bound of the datum.
* *Continuity.*  The freezing route gives a representative of the solution that is continuous
  on the open cube; reading the solution through that representative on the cube and through
  the datum off the cube produces the observable, and the almost-everywhere bound becomes a
  pointwise one by continuity.

The existence step and the observable are stated for an arbitrary bounded open convex domain,
so that the same construction serves the origin cube and its translates.  The observable is
also returned together with its almost-everywhere identification with the Sobolev solution it
was built from, which the corrector estimates consume.

## Main results

* `exists_h10_isDivFormWeakSolutionOn_add` — the Dirichlet problem with an `H¹` datum and a
  square-integrable forcing is solvable for every elliptic coefficient field.
* `exists_streamObservable_of_zeroTraceDifference` — the observable built from a weak solution
  of the homogeneous equation with the trace of a bounded continuous datum.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Schauder
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open HCPolySupport.PotentialSolenoidalL2Data
open DivergenceFormProcess.Form
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Dirichlet problem with an `H¹` datum -/

section Existence

variable [NeZero d] {U : Set (Vec d)}

/-- **Solvability of the Dirichlet problem with an `H¹` datum.**  For an elliptic coefficient
field on a bounded open convex domain, an `H¹` datum `h` and a square-integrable forcing field
`g`, the problem `-∇ · a ∇u = ∇ · g` has a solution of the form `h + w` with `w` of zero trace.
The zero-trace correction solves the problem with the forcing `-(a ∇h) - g`, by the Lax–Milgram
theorem of the library. -/
theorem exists_h10_isDivFormWeakSolutionOn_add (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (h : H1Function U) {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    ∃ w : H10Function U, IsDivFormWeakSolutionOn a U (h + w.toH1Function) g := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hAh : MemVectorL2 U fun x => matVecMul (a x) (h.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll h.grad_memVectorL2
  have hnAh : MemVectorL2 U fun x => -(matVecMul (a x) (h.grad x)) := hAh.neg
  have hforce : MemVectorL2 U fun x => -(matVecMul (a x) (h.grad x)) - g x := hnAh.sub hg
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := U) (g := fun x => -(matVecMul (a x) (h.grad x)) - g x) (lam := lam)
      (Lam := Lam) hforce
      (hasPotentialZeroTraceClosureRealization_of_convexDomain hU) hne hEll
  refine ⟨w, fun φ => ?_⟩
  have hAw : MemVectorL2 U fun x => matVecMul (a x) (w.toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1Function.grad_memVectorL2
  have hsplit : ∀ x, matVecMul (a x) ((h + w.toH1Function).grad x) =
      (fun x => matVecMul (a x) (h.grad x)) x +
        (fun x => matVecMul (a x) (w.toH1Function.grad x)) x := by
    intro x
    change matVecMul (a x) (h.grad x + w.toH1Function.grad x) = _
    exact matVecMul_add _ _ _
  rw [integral_vecDot_add_split hAh hAw hsplit φ, hw φ,
    integral_vecDot_sub_split hnAh hg (fun _ => rfl) φ, integral_vecDot_neg_split _ φ]
  ring

omit [NeZero d] in
/-- The homogeneous divergence-form equation, read as a scalar-forced weak equation with
vanishing forcing. -/
theorem isScalarForcedWeakSolution_zero_of_isDivFormWeakSolutionOn {a : CoeffField d}
    {u : H1Function U} (hsol : IsDivFormWeakSolutionOn a U u fun _ => (0 : Vec d)) :
    IsScalarForcedWeakSolution a U (fun _ ↦ (0 : ℝ)) u := by
  refine ⟨MemLp.zero, fun φ => ?_⟩
  rw [hsol φ]
  simp only [vecDot_zero_left, integral_zero, neg_zero, zero_mul]

end Existence

/-! ## 2. The stream coefficient on a bounded domain -/

section Stream

variable {gamma : ℝ}

/-- The skew part of the stream coefficient is continuous. -/
theorem continuous_streamCoefficient_sub_smul_one (nu : ℝ) (omega : FullSample d gamma) :
    Continuous fun x : Vec d => streamCoefficient nu omega x - nu • (1 : Mat d) := by
  have hrw : (fun x : Vec d => streamCoefficient nu omega x - nu • (1 : Mat d)) =
      streamField omega := by
    funext x
    ext i j
    simp only [streamCoefficient, Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hrw]
  exact continuous_streamField omega

/-- The stream coefficient is elliptic on every bounded open convex domain, with lower constant
the molecular diffusivity. -/
theorem exists_isEllipticFieldOn_streamCoefficient_of_domain {nu : ℝ} (hnu : 0 < nu)
    (omega : FullSample d gamma) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam U (streamCoefficient nu omega) :=
  ⟨_, isEllipticFieldOn_domainEllipticUpper hU hnu (symmPart_streamCoefficient nu omega)
    (continuous_streamCoefficient_sub_smul_one nu omega).continuousOn⟩

end Stream

/-! ## 3. The observable -/

section Observable

variable [NeZero d] {M : ABKModel d} {omega : FullSample d M.gamma}

/-- **The observable built from a weak solution of the homogeneous equation.**  Given a weak
solution `u` of `-∇ · a ∇u = 0` on a bounded open convex domain for the stream coefficient,
whose trace is that of an `H¹` function `h` agreeing on the domain with a bounded continuous
function `bd` that is itself the value of an `H¹` function `hd`, there is a bounded measurable
function, continuous on the domain and equal to `bd` off it, which is almost everywhere the
solution on the domain, is the value of an `H¹` function solving the homogeneous equation, and
has the trace of `bd`.

The bound is the uniform bound of `bd`, by the weak maximum principle; the continuity is that of
the interior representative supplied by the freezing route. -/
theorem exists_streamObservable_of_zeroTraceDifference {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {bd : Vec d → ℝ} (hbd : Continuous bd) {N : ℝ} (hbdN : ∀ x, |bd x| ≤ N)
    (hd : H1Function U) (hdbd : ∀ x, hd.toFun x = bd x)
    {h u : H1Function U} (hhbd : ∀ x ∈ U, h.toFun x = bd x)
    (hzt : HasZeroTraceDifferenceOn U u h)
    (hsol : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) U u fun _ => (0 : Vec d)) :
    ∃ (uObs : Vec d → ℝ) (Y : H1Function U),
      Measurable uObs ∧ (∀ z, |uObs z| ≤ N) ∧ (∀ z, z ∉ U → uObs z = bd z) ∧
      ContinuousOn uObs U ∧ (∀ z, Y.toFun z = uObs z) ∧
      IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData M omega).a U
        (fun _ ↦ (0 : ℝ)) Y ∧
      MemH10 U (fun z ↦ uObs z - bd z) ∧
      uObs =ᵐ[volume.restrict U] u.toFun := by
  classical
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_streamCoefficient_of_domain M.nu_pos omega hU
  obtain ⟨w, hwf, hwg⟩ := hzt
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have hscalar : IsScalarForcedWeakSolution (streamCoefficient M.nu omega) U
      (fun _ ↦ (0 : ℝ)) u := isScalarForcedWeakSolution_zero_of_isDivFormWeakSolutionOn hsol
  -- the trace of `u` is that of `hd`
  have hq : MemH10 U fun x ↦ u.toFun x - hd.toFun x := by
    have hae : (u - hd).toFun =ᵐ[volume.restrict U] w.toH1Function.toFun := by
      filter_upwards [ae_restrict_mem hUmeas] with x hx
      rw [H1Function.sub_toFun]
      change u.toFun x - hd.toFun x = _
      rw [hwf x, hdbd x, hhbd x hx]
      ring
    have hmem := memH10_of_ae_eq_h10 hU (u - hd) w hae
    rw [H1Function.sub_toFun] at hmem
    exact hmem
  -- the weak maximum principle
  have habs : ∀ᵐ x ∂(volume.restrict U), |u.toFun x| ≤ N :=
    ae_abs_le_of_isScalarForcedWeakSolution_zero hU M.nu_pos hEll hscalar hq
      (fun x => by rw [hdbd x]; exact hbdN x)
  -- the continuous representative
  have hcont : ContinuousOn
      (fun y => streamCoefficient M.nu omega y - M.nu • (1 : Mat d)) U :=
    (continuous_streamCoefficient_sub_smul_one M.nu omega).continuousOn
  have hg : MemScalarLInfOn U fun _ : Vec d => (0 : ℝ) := MemLp.zero
  obtain ⟨v, hvcont, hvae, -⟩ := continuousOn_of_weakSolution_continuousCoeff
    M.shellPrefix.dimension hU.isOpen M.nu_pos (symmPart_streamCoefficient M.nu omega) hcont hg
    hscalar
  -- the observable
  let uObs : Vec d → ℝ := U.piecewise v bd
  have hobsU : ∀ x ∈ U, uObs x = v x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hoff : ∀ z, z ∉ U → uObs z = bd z := fun z hz => Set.piecewise_eq_of_notMem _ _ _ hz
  have hae : uObs =ᵐ[volume.restrict U] u.toFun := by
    filter_upwards [ae_restrict_mem hUmeas, hvae] with x hx hvx
    rw [hobsU x hx, hvx]
  have habsv : ∀ x ∈ U, |v x| ≤ N := by
    refine Algsuperdiff.Section5.Support.le_of_ae_le_of_continuousOn hU.isOpen ?_
      (continuous_abs.comp_continuousOn hvcont) continuousOn_const
    filter_upwards [habs, hvae] with x hx hvx
    rw [hvx]
    exact hx
  have hN : ∀ z, |uObs z| ≤ N := by
    intro z
    by_cases hz : z ∈ U
    · rw [hobsU z hz]
      exact habsv z hz
    · rw [hoff z hz]
      exact hbdN z
  have hucont : ContinuousOn uObs U := hvcont.congr hobsU
  have hmeas : Measurable uObs :=
    ContinuousOn.measurable_piecewise hvcont hbd.continuousOn hUmeas
  -- the `H¹` witness of the observable
  have hL2 : MemL2On U uObs := u.memL2.ae_eq hae.symm
  obtain ⟨Y, hYfun, hYgrad⟩ := exists_h1Function_toFun_eq u hL2 hae
  refine ⟨uObs, Y, hmeas, hN, hoff, hucont, fun z => by rw [hYfun], ?_, ?_, hae⟩
  · refine ⟨MemLp.zero, fun φ => ?_⟩
    change ∫ x in U, vecDot (matVecMul (streamCoefficient M.nu omega x) (Y.grad x))
        (φ.toH1Function.grad x) ∂volume = _
    rw [hYgrad, hsol φ]
    simp only [vecDot_zero_left, integral_zero, neg_zero, zero_mul]
  · have hgu : (fun z => uObs z - bd z) =ᵐ[volume.restrict U] w.toH1Function.toFun := by
      filter_upwards [ae_restrict_mem hUmeas, hae] with x hx hux
      rw [hux, hwf x, hhbd x hx]
      ring
    have hL2' : MemL2On U fun z => uObs z - bd z := w.toH1Function.memL2.ae_eq hgu.symm
    obtain ⟨Z, hZfun, -⟩ := exists_h1Function_toFun_eq w.toH1Function hL2' hgu
    have hmem := memH10_of_ae_eq_h10 hU Z w (by rw [hZfun]; exact hgu)
    rwa [hZfun] at hmem

end Observable

end

end Algsuperdiff.Section5.Provider
