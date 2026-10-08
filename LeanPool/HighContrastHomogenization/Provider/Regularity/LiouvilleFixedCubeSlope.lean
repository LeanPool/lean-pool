/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CanonicalSlopeLocalCoercivity

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleFixedCubeSlope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A canonical slope on one fixed cube

This module turns vanishing finite-affine excess for exact realizations of one
global gradient into a slope whose joint corrector gradient is that gradient
on the fixed inner cube.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- On one fixed admissible cube, vanishing affine excess identifies the
global gradient with the joint affine-corrector gradient at some slope. -/
theorem exists_jointSlope_of_fixedCubeExcess
    {d : ℕ} [NeZero d] {s : ℝ}
    {a : Book.Ch02.TriadicCoeffFamily d} {delta c : ℝ} {n₀ : ℤ}
    (hthreshold : c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c → ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm e ≤ 2 * euclideanNorm
            (cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad))
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodTail a s delta n₀)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (q : ℕ) (hnq : n₀ ≤ (q : ℤ))
    (u : ∀ j : ℕ,
      Book.Ch03.CubeSolution (originCube d ((q + j + 2 : ℕ) : ℤ)) a)
    (Dv : Vec d → Vec d) (huGrad : ∀ j, (u j).toH1.grad = Dv)
    (hexcess : Tendsto
      (fun j => finiteAffineGradientExcess a (q : ℤ)
        ((q + j + 2 : ℕ) : ℤ) (u j))
      atTop (nhds 0)) :
    ∃ eLim : Vec d,
      (finiteCubeSolutionRestriction a (by omega) (u 0)).toH1.gradToHilbertVectorL2 =
        (jointAffineFullGradientLinearMap a hCauchy q) eLim := by
  have hqj : ∀ j, (q : ℤ) ≤ ((q + j + 2 : ℕ) : ℤ) := by
    intro j
    omega
  obtain ⟨e, heResidual⟩ :=
    exists_boundarySlopeSequence_residual_tendsto_zero
      a (q : ℤ) (fun j => ((q + j + 2 : ℕ) : ℤ)) hqj u hexcess
  have heBound : ∃ R : ℝ, ∀ j, euclideanNorm (e j) ≤ R :=
    exists_uniform_euclideanBound_finiteAffineSlopes_of_residual_tendsto_zero
      hthreshold hdelta hgood q hnq u Dv huGrad e heResidual
  obtain ⟨eLim, φ, hφ, heLim⟩ :=
    exists_tendsto_subsequence_of_uniform_euclideanBound e heBound
  let rho : ℕ → ℕ := fun k => φ k + 2
  let u' : ∀ k : ℕ,
      Book.Ch03.CubeSolution (originCube d ((q + rho k : ℕ) : ℤ)) a :=
    fun k => Eq.mp (by simp only [rho, add_assoc]) (u (φ k))
  have hrho : Tendsto rho atTop atTop := by
    exact tendsto_add_atTop_nat 2 |>.comp hφ.tendsto_atTop
  have hu'Grad : ∀ k, (u' k).toH1.grad = Dv := fun k => huGrad (φ k)
  have heLim' : Tendsto (fun k => e (φ k)) atTop (nhds eLim) := by
    simpa only [Function.comp_apply] using! heLim
  have heResidual' : Tendsto
      (fun k => weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ (u' k).toH1.grad x -
          (finiteAffineSolution a ((q + rho k : ℕ) : ℤ) (e (φ k))).toH1.grad x))
      atTop (nhds 0) := by
    simpa only [u', rho, add_assoc] using! heResidual.comp hφ.tendsto_atTop
  have hid := finiteAffineResidual_identifies_jointLocalGradient_along
    a hCauchy q rho hrho u' Dv hu'Grad (fun k => e (φ k)) eLim
      heLim' heResidual'
  refine ⟨eLim, Eq.trans ?_ hid⟩
  apply MeasureTheory.Lp.ext
  filter_upwards
    [(finiteCubeSolutionRestriction a (by omega) (u 0)).toH1.coeFn_gradToHilbertVectorL2,
     (finiteCubeSolutionRestriction a (by omega) (u' 0)).toH1.coeFn_gradToHilbertVectorL2]
    with x hu hu'
  rw [hu, hu']
  change HilbertVec.ofVec ((u 0).toH1.grad x) =
    HilbertVec.ofVec ((u' 0).toH1.grad x)
  rw [huGrad 0, hu'Grad 0]

end

end HighContrast
end HCPolySupport
