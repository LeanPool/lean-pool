/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.HomogenizationCorrector
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StreamExitTimeH10
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.FieldDivergenceTest

/-!
# HomogenizationCorrectorPointwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The cut-off observables of the displacement bounds, with their pointwise corrector bounds

The stopped-moment bounds on a triadic cube consume an observable together with a bound, at
every point, on its distance to a bounded Borel function vanishing at the centre.  This file
produces, for the cut-off linear and quadratic data `c · (e ⬝ x)` and `c · (e ⬝ x)²` of a smooth
cut-off `c` equal to one on the cube centred at the origin, the homogenization observable of the
cube with all its properties, and the pointwise corrector bounds:

* for the linear datum, `|c (e ⬝ x) − u| ≤ 3^m EB ‖e‖` everywhere — on the cube by the
  corrector estimate read through the continuous representative, off the cube because the
  observable is the datum there;
* for the quadratic datum, the same for the corrected observable `u − 2 sigmaBar (e ⬝ e) w`,
  with `w` the expected exit time from the cube, at every point of the compactified state space
  — on the cube by the corrector estimate at the forcing `-2 sigmaBar (e ⬝ x) e`, off the cube
  because the expected exit time vanishes there, and at infinity because everything vanishes.

The corrected observable solves the forced Dirichlet problem because the expected exit time is
the zero-trace solution of `-∇ · a ∇w = 1`, and the divergence of `(e ⬝ x) e` is `e ⬝ e`.

## Main results

* `isDivFormWeakSolutionOn_quadraticForcing_of_streamExitH10` — the corrected observable solves
  the quadratic problem.
* `exists_cutoffAffineObservable_stream` — the observable of the cut-off linear datum with its
  pointwise corrector bound.
* `exists_cutoffQuadraticObservable_stream` — the observable of the cut-off quadratic datum with
  the pointwise bound on the corrected observable.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support Algsuperdiff.Section4.Provider.Holder
open Algsuperdiff.Section4.Provider.Schauder
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

private theorem h10Sub_toH1Function {U : Set (Vec d)} (v w : H10Function U) :
    (v - w).toH1Function = v.toH1Function - w.toH1Function := rfl

/-! ## 1. The corrected observable solves the quadratic problem -/

/-- The divergence of the field `x ↦ (e ⬝ x) e` is `e ⬝ e`. -/
theorem vecFieldDiv_vecDot_smul (e x : Vec d) :
    vecFieldDiv (fun z : Vec d => (vecDot e z) • e) x = vecDot e e := by
  rw [vecFieldDiv_apply]
  have hterm : ∀ i : Fin d,
      (fderiv ℝ (fun z : Vec d => ((vecDot e z) • e) i) x) (basisVec i) = e i * e i := by
    intro i
    have hshape : (fun z : Vec d => ((vecDot e z) • e) i) =
        fun z : Vec d => (slopeCLM e) z * e i := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, slopeCLM_apply]
    have h1 : HasFDerivAt (fun z : Vec d => (slopeCLM e) z * e i) (e i • slopeCLM e) x :=
      (slopeCLM e).hasFDerivAt.mul_const (e i)
    rw [hshape, h1.fderiv, smul_apply, slopeCLM_apply, vecDot_basisVec_right,
      smul_eq_mul]
  simp only [hterm]
  rfl

/-- The coordinates of the field `x ↦ (e ⬝ x) e` are smooth. -/
theorem contDiff_vecDot_smul_apply (e : Vec d) (i : Fin d) :
    ContDiff ℝ 1 fun z : Vec d => ((vecDot e z) • e) i := by
  change ContDiff ℝ 1 fun z : Vec d => vecDot e z * e i
  exact (contDiff_affineObservable 1 e).mul contDiff_const

variable [NeZero d]

/-- **The corrected observable solves the quadratic problem.**  If `u = h + w` solves the
homogeneous equation on the cube with the trace of the quadratic datum, then
`u − 2 sigmaBar (e ⬝ e) E`, with `E` the zero-trace solution of `-∇ · a ∇E = 1`, solves the
problem with the forcing `-2 sigmaBar (e ⬝ x) e`. -/
theorem isDivFormWeakSolutionOn_quadraticForcing_of_streamExitH10 (M : ABKModel d)
    (omega : FullSample d M.gamma) (m : ℤ) (sigmaBar : ℝ) (e : Vec d)
    {w : H10Function (cubeSetAt (0 : Vec d) m)}
    (hw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt (0 : Vec d) m)
      (quadraticH1 0 m e + w.toH1Function) fun _ => (0 : Vec d)) :
    IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt (0 : Vec d) m)
      (quadraticH1 0 m e +
        (w - (2 * sigmaBar * vecDot e e) • streamExitH10 M omega 0 m).toH1Function)
      (quadraticForcing sigmaBar e) := by
  intro φ
  have hEsol := isScalarForcedWeakSolution_streamExitH10 M omega (0 : Vec d) m
  rw [streamWholeSpaceAnalyticData_a] at hEsol
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_streamCoefficient M.nu_pos omega 0 m
  have hUm : MeasurableSet (cubeSetAt (0 : Vec d) m) := measurableSet_cubeSetAt 0 m
  have hUb : IsBoundedDomain (cubeSetAt (0 : Vec d) m) :=
    (isOpenBoundedConvexDomain_cubeSetAt (0 : Vec d) m).isBoundedDomain
  set E := streamExitH10 M omega (0 : Vec d) m with hE_def
  -- the gradient of the corrected observable
  have hgrad : ∀ x, matVecMul (streamCoefficient M.nu omega x)
      ((quadraticH1 0 m e + (w - (2 * sigmaBar * vecDot e e) • E).toH1Function).grad x) =
      (fun x => matVecMul (streamCoefficient M.nu omega x)
        ((quadraticH1 0 m e + w.toH1Function).grad x)) x -
      (fun x => (2 * sigmaBar * vecDot e e) •
        matVecMul (streamCoefficient M.nu omega x) (E.toH1Function.grad x)) x := by
    intro x
    change matVecMul (streamCoefficient M.nu omega x)
        ((quadraticH1 0 m e).grad x + (w - (2 * sigmaBar * vecDot e e) • E).toH1Function.grad x) =
      matVecMul (streamCoefficient M.nu omega x)
        ((quadraticH1 0 m e).grad x + w.toH1Function.grad x) -
      (2 * sigmaBar * vecDot e e) •
        matVecMul (streamCoefficient M.nu omega x) (E.toH1Function.grad x)
    rw [h10Sub_toH1Function, H1Function.sub_grad]
    change matVecMul (streamCoefficient M.nu omega x)
        ((quadraticH1 0 m e).grad x +
          (w.toH1Function.grad x - ((2 * sigmaBar * vecDot e e) • E.toH1Function).grad x)) = _
    rw [H1Function.smul_grad]
    change matVecMul (streamCoefficient M.nu omega x)
        ((quadraticH1 0 m e).grad x +
          (w.toH1Function.grad x - (2 * sigmaBar * vecDot e e) • E.toH1Function.grad x)) = _
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, matVecMul_smul]
    abel
  have hF : MemVectorL2 (cubeSetAt (0 : Vec d) m) fun x =>
      matVecMul (streamCoefficient M.nu omega x) ((quadraticH1 0 m e + w.toH1Function).grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      (quadraticH1 0 m e + w.toH1Function).grad_memVectorL2
  have hG : MemVectorL2 (cubeSetAt (0 : Vec d) m) fun x =>
      (2 * sigmaBar * vecDot e e) •
        matVecMul (streamCoefficient M.nu omega x) (E.toH1Function.grad x) :=
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll E.toH1Function.grad_memVectorL2).const_smul
      (2 * sigmaBar * vecDot e e)
  have hsmul := integral_vecDot_smul_split (U := cubeSetAt (0 : Vec d) m)
    (2 * sigmaBar * vecDot e e)
    (fun x => matVecMul (streamCoefficient M.nu omega x) (E.toH1Function.grad x)) φ
  rw [integral_vecDot_sub_split hF hG hgrad φ, hw φ, hsmul, hEsol.2 φ]
  -- the forcing field
  have hforce : ∀ x, quadraticForcing sigmaBar e x =
      (-(2 * sigmaBar)) • ((fun z : Vec d => (vecDot e z) • e) x) := by
    intro x
    change (-(2 * sigmaBar) * vecDot e x) • e = (-(2 * sigmaBar)) • ((vecDot e x) • e)
    rw [mul_smul]
  have hIBP := integral_vecDot_h10Grad_eq_neg_integral_vecFieldDiv_mul hUm hUb
    (contDiff_vecDot_smul_apply e) φ
  simp only [vecFieldDiv_vecDot_smul] at hIBP
  have hrhs : ∫ x in cubeSetAt (0 : Vec d) m,
      vecDot (quadraticForcing sigmaBar e x) (φ.toH1Function.grad x) ∂volume =
      (-(2 * sigmaBar)) * ∫ x in cubeSetAt (0 : Vec d) m,
        vecDot ((vecDot e x) • e) (φ.toH1Function.grad x) ∂volume := by
    rw [← integral_vecDot_smul_split]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change vecDot (quadraticForcing sigmaBar e x) (φ.toH1Function.grad x) =
      vecDot ((-(2 * sigmaBar)) • ((fun z : Vec d => (vecDot e z) • e) x)) (φ.toH1Function.grad x)
    rw [hforce x]
  rw [hrhs, hIBP]
  simp only [vecDot_zero_left, integral_zero, neg_zero, zero_sub, one_mul]
  rw [integral_const_mul]
  ring

/-! ## 2. The cut-off linear datum -/

/-- **The observable of the cut-off linear datum, with its pointwise corrector bound.**  For a
smooth cut-off `c` equal to one on the cube centred at the origin and a uniform bound `N` for
`c · (e ⬝ x)`, there is a homogenization observable of the cube with datum `c · (e ⬝ x)`, and it
is everywhere within `3^m EB ‖e‖` of the datum, under the corrector clause of the
renormalization theorem at the sample for the scale `m`. -/
theorem exists_cutoffAffineObservable_stream (M : ABKModel d) (omega : FullSample d M.gamma)
    (m : ℤ) {sigmaBarM EBm : ℝ} (hEB : 0 ≤ EBm)
    (hren : ∀ L : ℤ, m ≤ L →
      ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
        (Kg Kh KhInf : ℝ),
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ : Vec d => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
        HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
        ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
          Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
            EBm * (sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)))
    (e : Vec d) {c : Vec d → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hc1 : ∀ x ∈ cubeSetAt (0 : Vec d) m, c x = 1) {N : ℝ}
    (hbdN : ∀ x, |c x * affineObservable e x| ≤ N) :
    ∃ (u : Vec d → ℝ) (Y : H1Function (cubeSetAt (0 : Vec d) m)),
      Measurable u ∧ (∀ z, |u z| ≤ N) ∧
      (∀ z, z ∉ cubeSetAt (0 : Vec d) m → u z = c z * affineObservable e z) ∧
      ContinuousOn u (cubeSetAt (0 : Vec d) m) ∧ (∀ z, Y.toFun z = u z) ∧
      IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData M omega).a
        (cubeSetAt (0 : Vec d) m) (fun _ ↦ (0 : ℝ)) Y ∧
      MemH10 (cubeSetAt (0 : Vec d) m) (fun z ↦ u z - c z * affineObservable e z) ∧
      ∀ z, |c z * affineObservable e z - u z| ≤ (3 : ℝ) ^ m * (EBm * ‖e‖) := by
  have hU := isOpenBoundedConvexDomain_cubeSetAt (0 : Vec d) m
  have hne := cubeSetAt_nonempty (0 : Vec d) m
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_streamCoefficient M.nu_pos omega 0 m
  obtain ⟨w, hw⟩ := exists_h10_isDivFormWeakSolutionOn_add hU hne hEll (affineH1 0 m e)
    (g := fun _ => (0 : Vec d)) MemLp.zero
  have hbdc : Continuous fun z => c z * affineObservable e z :=
    hc.continuous.mul (continuous_affineObservable e)
  let hd : H1Function (cubeSetAt (0 : Vec d) m) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
      ((hc.of_le (by simp)).mul (contDiff_affineObservable 1 e))
  obtain ⟨uObs, Y, hmeas, hN, hoff, hcont, hY, hharm, htrace, hae⟩ :=
    exists_streamObservable_of_zeroTraceDifference (M := M) (omega := omega) hU hbdc hbdN hd
      (fun _ => rfl) (h := affineH1 0 m e) (u := affineH1 0 m e + w.toH1Function)
      (fun x hx => by
        change affineObservable e x = c x * affineObservable e x
        rw [hc1 x hx, one_mul])
      ⟨w, fun _ => rfl, fun _ => rfl⟩ hw
  have hcorr := ae_abs_sub_affineObservable_le_stream M omega m hren e
    ⟨w, fun _ => rfl, fun _ => rfl⟩ hw
  have hpt : ∀ x ∈ cubeSetAt (0 : Vec d) m,
      |uObs x - affineObservable e x| ≤ (3 : ℝ) ^ m * (EBm * ‖e‖) := by
    refine Algsuperdiff.Section5.Support.le_of_ae_le_of_continuousOn hU.isOpen ?_
      (continuous_abs.comp_continuousOn
        (hcont.sub (continuous_affineObservable e).continuousOn)) continuousOn_const
    filter_upwards [hcorr, hae] with x hx hux
    rw [hux]
    exact hx
  refine ⟨uObs, Y, hmeas, hN, hoff, hcont, hY, hharm, htrace, fun z => ?_⟩
  by_cases hz : z ∈ cubeSetAt (0 : Vec d) m
  · rw [hc1 z hz, one_mul, abs_sub_comm]
    exact hpt z hz
  · rw [hoff z hz, sub_self, abs_zero]
    exact mul_nonneg (zpow_nonneg (by norm_num) m) (mul_nonneg hEB (norm_nonneg e))

/-! ## 3. The cut-off quadratic datum -/

section Process

variable {M : ABKModel d} {omega : FullSample d M.gamma}
  (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : (streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R)
  (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
    R.toContractiveResolvent.operator mu g =
      ((streamWholeSpaceC0BarrierData M omega).resolvent).toContractiveResolvent.operator mu g)

include hcons hid hT in
/-- **The observable of the cut-off quadratic datum, with the pointwise bound on the corrected
observable.**  For a smooth cut-off `c` equal to one on the cube centred at the origin and a
uniform bound `N` for `c · (e ⬝ x)²`, there is a homogenization observable `u` of the cube with
datum `c · (e ⬝ x)²`, and at every point of the compactified state space the datum is within
`5 (3^m)² EB ‖e‖ (∑ |e_i|)` of `u − 2 sigmaBar (e ⬝ e)` times the expected exit time from the
cube, under the corrector clause of the renormalization theorem at the sample for the scale
`m`. -/
theorem exists_cutoffQuadraticObservable_stream (m : ℤ) {sigmaBarM EBm : ℝ}
    (hsigma : 0 < sigmaBarM) (hEB : 0 ≤ EBm)
    (hren : ∀ L : ℤ, m ≤ L →
      ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
        (Kg Kh KhInf : ℝ),
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ : Vec d => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
        HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
        ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
          Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
            EBm * (sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)))
    (e : Vec d) {c : Vec d → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hc1 : ∀ x ∈ cubeSetAt (0 : Vec d) m, c x = 1) {N : ℝ}
    (hbdN : ∀ x, |c x * quadraticObservable e x| ≤ N) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∃ (u : Vec d → ℝ) (Y : H1Function (cubeSetAt (0 : Vec d) m)),
      Measurable u ∧ (∀ z, |u z| ≤ N) ∧
      (∀ z, z ∉ cubeSetAt (0 : Vec d) m → u z = c z * quadraticObservable e z) ∧
      ContinuousOn u (cubeSetAt (0 : Vec d) m) ∧ (∀ z, Y.toFun z = u z) ∧
      IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData M omega).a
        (cubeSetAt (0 : Vec d) m) (fun _ ↦ (0 : ℝ)) Y ∧
      MemH10 (cubeSetAt (0 : Vec d) m) (fun z ↦ u z - c z * quadraticObservable e z) ∧
      ∀ z : OnePoint (Vec d),
        |onePointRealExtension (fun x => c x * quadraticObservable e x) z -
          (onePointRealExtension u z - (2 * sigmaBarM * vecDot e e) *
            (expectedExitTime R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
              (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) z).toReal)| ≤
          ((3 : ℝ) ^ m) ^ (2 : ℕ) * (5 * EBm * (‖e‖ * vecCoordSum e)) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hU := isOpenBoundedConvexDomain_cubeSetAt (0 : Vec d) m
  have hne := cubeSetAt_nonempty (0 : Vec d) m
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_streamCoefficient M.nu_pos omega 0 m
  obtain ⟨w, hw⟩ := exists_h10_isDivFormWeakSolutionOn_add hU hne hEll (quadraticH1 0 m e)
    (g := fun _ => (0 : Vec d)) MemLp.zero
  have hbdc : Continuous fun z => c z * quadraticObservable e z :=
    hc.continuous.mul (continuous_quadraticObservable e)
  let hd : H1Function (cubeSetAt (0 : Vec d) m) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
      ((hc.of_le (by simp)).mul (contDiff_quadraticObservable 1 e))
  obtain ⟨uObs, Y, hmeas, hN, hoff, hcont, hY, hharm, htrace, hae⟩ :=
    exists_streamObservable_of_zeroTraceDifference (M := M) (omega := omega) hU hbdc hbdN hd
      (fun _ => rfl) (h := quadraticH1 0 m e) (u := quadraticH1 0 m e + w.toH1Function)
      (fun x hx => by
        change quadraticObservable e x = c x * quadraticObservable e x
        rw [hc1 x hx, one_mul])
      ⟨w, fun _ => rfl, fun _ => rfl⟩ hw
  -- the corrected observable and its corrector estimate
  set E := streamExitH10 M omega (0 : Vec d) m with hE_def
  have hw₂ := isDivFormWeakSolutionOn_quadraticForcing_of_streamExitH10 M omega m sigmaBarM e hw
  have hcorr := ae_abs_sub_quadraticObservable_le_stream M omega m hsigma hren e
    ⟨w - (2 * sigmaBarM * vecDot e e) • E, fun _ => rfl, fun _ => rfl⟩ hw₂
  have hu₂ : ∀ x, (quadraticH1 0 m e +
      (w - (2 * sigmaBarM * vecDot e e) • E).toH1Function).toFun x =
      (quadraticH1 0 m e + w.toH1Function).toFun x -
        (2 * sigmaBarM * vecDot e e) * streamExitFunction M omega 0 m x := by
    intro x
    change (quadraticH1 0 m e).toFun x + (w - (2 * sigmaBarM * vecDot e e) • E).toH1Function.toFun
      x =
      (quadraticH1 0 m e).toFun x + w.toH1Function.toFun x -
        (2 * sigmaBarM * vecDot e e) * streamExitFunction M omega 0 m x
    rw [h10Sub_toH1Function, H1Function.sub_toFun]
    change (quadraticH1 0 m e).toFun x +
        (w.toH1Function.toFun x - ((2 * sigmaBarM * vecDot e e) • E.toH1Function).toFun x) = _
    rw [H1Function.smul_toFun]
    change (quadraticH1 0 m e).toFun x +
        (w.toH1Function.toFun x - (2 * sigmaBarM * vecDot e e) * E.toH1Function.toFun x) = _
    rw [hE_def, streamExitH10_toFun]
    ring
  set K : ℝ := ((3 : ℝ) ^ m) ^ (2 : ℕ) * (5 * EBm * (‖e‖ * vecCoordSum e)) with hK_def
  have hK0 : 0 ≤ K := by
    rw [hK_def]
    exact mul_nonneg (pow_nonneg (zpow_nonneg (by norm_num) m) 2)
      (mul_nonneg (mul_nonneg (by norm_num) hEB) (mul_nonneg (norm_nonneg e)
        (vecCoordSum_nonneg e)))
  -- pointwise on the cube, by continuity
  have hpt : ∀ x ∈ cubeSetAt (0 : Vec d) m,
      |uObs x - (2 * sigmaBarM * vecDot e e) * streamExitFunction M omega 0 m x -
        quadraticObservable e x| ≤ K := by
    refine Algsuperdiff.Section5.Support.le_of_ae_le_of_continuousOn hU.isOpen ?_
      (continuous_abs.comp_continuousOn
        ((hcont.sub (continuousOn_const.mul (continuousOn_streamExitFunction M omega 0 m))).sub
          (continuous_quadraticObservable e).continuousOn)) continuousOn_const
    filter_upwards [hcorr, hae] with x hx hux
    rw [hu₂ x, ← hux] at hx
    exact hx
  refine ⟨uObs, Y, hmeas, hN, hoff, hcont, hY, hharm, htrace, fun z => ?_⟩
  rw [toReal_expectedExitTime_cubeSetAt_eq_stream R hreg hcons hid hT 0 m z]
  induction z using OnePoint.rec with
  | infty =>
    simp only [onePointRealExtension_infty, mul_zero, sub_self, abs_zero]
    exact hK0
  | coe x =>
    simp only [onePointRealExtension_coe]
    by_cases hx : x ∈ cubeSetAt (0 : Vec d) m
    · rw [hc1 x hx, one_mul, abs_sub_comm]
      exact hpt x hx
    · rw [hoff x hx, streamExitFunction_of_notMem M omega 0 m hx, mul_zero, sub_zero, sub_self,
        abs_zero]
      exact hK0

end Process

end

end Algsuperdiff.Section5.Provider
