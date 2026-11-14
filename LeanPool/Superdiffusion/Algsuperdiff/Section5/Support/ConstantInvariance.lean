/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionMeasurable

/-!
# ConstantInvariance

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Adding a constant to the forcing field does not change the solution

A constant vector field pairs to zero against the gradient of every zero-trace
function, so the divergence-form weak equation does not see it.  Consequently
the localized Dirichlet problem has the same solutions for `g` and for
`g + c`, and in particular for `g` and for the *centred* field
`x ↦ g x - g y`, which has the same `1/2`-Hölder seminorm and vanishes at the
centre.

The vanishing of the pairing comes from the weak-gradient identity for the
constant function `1`: tested against a smooth compactly supported function, it
says exactly that the integral of a partial derivative vanishes.  The passage
from smooth test functions to zero-trace ones is the `H¹₀` approximating
sequence.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory Filter
open Algsuperdiff.Section4.Support
open scoped BigOperators Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. The integral of a partial derivative vanishes -/

/-- **The integral of a partial derivative of a compactly supported test
function vanishes**, read off the weak-gradient identity for the constant
function `1`. -/
theorem setIntegral_fderiv_eq_zero {U : Set (Vec d)} (i : Fin d) {psi : Vec d → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hsupp : HasCompactSupport psi)
    (hsub : tsupport psi ⊆ U) :
    ∫ x in U, (fderiv ℝ psi x) (basisVec i) ∂volume = 0 := by
  have hconst : HasWeakGradientOn U (fun _ : Vec d => (1 : ℝ))
      (fun x _ => (fderiv ℝ (fun _ : Vec d => (1 : ℝ)) x) (basisVec i)) := by
    simpa using
      (HasWeakGradientOn.of_contDiff (U := U)
        (contDiff_const : ContDiff ℝ 1 fun _ : Vec d => (1 : ℝ)))
  have h := hconst i psi hpsi hsupp hsub
  simpa using h

/-! ## 2. The integral of a zero-trace gradient vanishes -/

theorem setIntegral_grad_H10_eq_zero {U : Set (Vec d)} (hUfin : volume U ≠ ⊤)
    (phi : H10Function U) (i : Fin d) :
    ∫ x in U, phi.toH1Function.grad x i ∂volume = 0 := by
  have : IsFiniteMeasure (volume.restrict U) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hUfin
  have hfmem : MemLp (fun x => phi.toH1Function.grad x i) 2 (volume.restrict U) :=
    phi.toH1Function.gradMemL2 i
  have hFmem : ∀ k : ℕ,
      MemLp (fun x => (fderiv ℝ (phi.approx k) x) (basisVec i)) 2 (volume.restrict U) := by
    intro k
    have hcont : Continuous fun x => (fderiv ℝ (phi.approx k) x) (basisVec i) :=
      ((phi.approx_smooth k).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport fun x => (fderiv ℝ (phi.approx k) x) (basisVec i) := by
      simpa using (phi.approx_hasCompactSupport k).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  have hFzero : ∀ k : ℕ,
      ∫ x in U, (fderiv ℝ (phi.approx k) x) (basisVec i) ∂volume = 0 := fun k =>
    setIntegral_fderiv_eq_zero i (phi.approx_smooth k) (phi.approx_hasCompactSupport k)
      (phi.approx_support_subset k)
  have hdiff : ∀ k : ℕ,
      ‖(∫ x in U, (fderiv ℝ (phi.approx k) x) (basisVec i) ∂volume) -
        ∫ x in U, phi.toH1Function.grad x i ∂volume‖ ≤
        Real.sqrt (volume.real U) *
          (eLpNorm (fun x => (fderiv ℝ (phi.approx k) x) (basisVec i) -
            phi.toH1Function.grad x i) 2 (volume.restrict U)).toReal := by
    intro k
    have hsub' : (∫ x in U, (fderiv ℝ (phi.approx k) x) (basisVec i) ∂volume) -
        ∫ x in U, phi.toH1Function.grad x i ∂volume =
        ∫ x in U, ((fderiv ℝ (phi.approx k) x) (basisVec i) -
          phi.toH1Function.grad x i) ∂volume :=
      (integral_sub ((hFmem k).integrable one_le_two) (hfmem.integrable one_le_two)).symm
    have hmemdiff : MemLp (fun x => (fderiv ℝ (phi.approx k) x) (basisVec i) -
        phi.toH1Function.grad x i) 2 (volume.restrict U) := (hFmem k).sub hfmem
    rw [hsub', Real.norm_eq_abs]
    refine (abs_setIntegral_le_sqrt hUfin hmemdiff).trans (le_of_eq ?_)
    congr 1
    have hsq := toReal_eLpNorm_two_sq_eq_integral_sq hmemdiff
    rw [← hsq, Real.sqrt_sq ENNReal.toReal_nonneg]
  have hlim : Tendsto (fun k : ℕ => Real.sqrt (volume.real U) *
      (eLpNorm (fun x => (fderiv ℝ (phi.approx k) x) (basisVec i) -
        phi.toH1Function.grad x i) 2 (volume.restrict U)).toReal) atTop (𝓝 0) := by
    have h0 := phi.tendsto_approx_grad i
    have h1 : Tendsto (fun k : ℕ =>
        (eLpNorm (fun x => (fderiv ℝ (phi.approx k) x) (basisVec i) -
          phi.toH1Function.grad x i) 2 (volume.restrict U)).toReal) atTop (𝓝 0) := by
      simpa using! (ENNReal.tendsto_toReal (by simp)).comp h0
    simpa using h1.const_mul (Real.sqrt (volume.real U))
  have hconv : Tendsto (fun k : ℕ =>
      (∫ x in U, (fderiv ℝ (phi.approx k) x) (basisVec i) ∂volume) -
        ∫ x in U, phi.toH1Function.grad x i ∂volume) atTop (𝓝 0) :=
    squeeze_zero_norm hdiff hlim
  have hconst : Tendsto (fun _ : ℕ =>
      -∫ x in U, phi.toH1Function.grad x i ∂volume) atTop (𝓝 0) := by
    refine hconv.congr fun k => ?_
    rw [hFzero k, zero_sub]
  have := tendsto_nhds_unique hconst tendsto_const_nhds
  linarith [this]

theorem setIntegral_vecDot_const_H10_eq_zero {U : Set (Vec d)} (hUfin : volume U ≠ ⊤)
    (phi : H10Function U) (c : Vec d) :
    ∫ x in U, vecDot c (phi.toH1Function.grad x) ∂volume = 0 := by
  have : IsFiniteMeasure (volume.restrict U) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hUfin
  have hint : ∀ i : Fin d,
      IntegrableOn (fun x => c i * phi.toH1Function.grad x i) U volume :=
    fun i => ((phi.toH1Function.gradMemL2 i).integrable one_le_two).const_mul (c i)
  have hrw : ∫ x in U, vecDot c (phi.toH1Function.grad x) ∂volume =
      ∑ i : Fin d, ∫ x in U, c i * phi.toH1Function.grad x i ∂volume := by
    rw [← integral_finsetSum _ fun i _ => hint i]
    rfl
  rw [hrw]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, setIntegral_grad_H10_eq_zero hUfin phi i, mul_zero]

/-! ## 3. The equation does not see a constant forcing field -/

theorem isDivFormWeakSolutionOn_add_const {W : Set (Vec d)} (hWfin : volume W ≠ ⊤)
    {a : CoeffField d} {u : H1Function W} {g : Vec d → Vec d}
    (hgL2 : MemVectorL2 W g) (c : Vec d) (h : IsDivFormWeakSolutionOn a W u g) :
    IsDivFormWeakSolutionOn a W u fun x => g x + c := by
  have : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWfin
  intro phi
  have hcL2 : MemVectorL2 W fun _ : Vec d => c := memLp_const c
  have hsplit := Section4.Provider.Schauder.integral_vecDot_add_split hgL2 hcL2
    (fun _ => rfl) phi
  rw [hsplit, setIntegral_vecDot_const_H10_eq_zero hWfin phi c, add_zero]
  exact h phi

/-- **Adding a constant to the forcing field leaves the solutions unchanged.** -/
theorem isDirichletSolutionAt_add_const {y : Vec d} {n : ℤ} {a : CoeffField d}
    {u : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hgL2 : MemVectorL2 (cubeSetAt y n) g) (c : Vec d)
    (h : IsDirichletSolutionAt a y n u g) :
    IsDirichletSolutionAt a y n u fun x => g x + c :=
  ⟨h.1, isDivFormWeakSolutionOn_add_const
    ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne hgL2 c h.2⟩

/-- **Centring the forcing field at the centre of the cube leaves the solutions
unchanged.** -/
theorem isDirichletSolutionAt_sub_const {y : Vec d} {n : ℤ} {a : CoeffField d}
    {u : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hgL2 : MemVectorL2 (cubeSetAt y n) g) (c : Vec d)
    (h : IsDirichletSolutionAt a y n u g) :
    IsDirichletSolutionAt a y n u fun x => g x - c := by
  have := isDirichletSolutionAt_add_const hgL2 (-c) h
  simpa [sub_eq_add_neg] using this

end

end Algsuperdiff.Section5.Support
