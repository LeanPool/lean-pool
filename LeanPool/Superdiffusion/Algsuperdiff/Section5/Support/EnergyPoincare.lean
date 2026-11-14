/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionCoefficientContinuity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareZeroTrace
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.DifferenceQuotient

/-!
# EnergyPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Poincaré inequality in integral form, and solvability for a general elliptic field

Two ingredients that the measurability of the localized quantities needs.

*The Poincaré inequality in integral form.*  The zero-trace Poincaré estimate of
the ambient layer is stated between the `L²` classes of the value and of the
coordinates of the gradient.  Rewriting both sides as square roots of integrals
turns it into the form the energy estimates are written in, at the price of the
dimensional factor `d` from the supremum norm of the gradient.

*Solvability for a general elliptic field.*  The rough-field existence statement
is specialized to the cutoff coefficient; the same argument works for any field
that is elliptic on the cube, which is what a coefficient-dependent solution map
requires.

## Main results

* `exists_poincare_integral_constant`.
* `exists_isDirichletSolutionAt_of_isEllipticFieldOn`.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. The two `L²` norms as integrals -/

theorem norm_toScalarL2_eq_sqrt {U : Set (Vec d)} (w : H1Function U) :
    ‖w.toScalarL2‖ = Real.sqrt (∫ x in U, w.toFun x ^ (2 : ℕ) ∂volume) := by
  have hsq : ∫ x in U, w.toFun x ^ (2 : ℕ) ∂volume = ‖w.toScalarL2‖ ^ (2 : ℕ) := by
    simpa [H1Function.toScalarL2, HCPolySupport.toScalarL2] using
      (toReal_eLpNorm_two_sq_eq_integral_sq w.memL2).symm
  rw [hsq, Real.sqrt_sq (norm_nonneg _)]

theorem norm_gradCoordToScalarL2_eq_sqrt {U : Set (Vec d)} (w : H1Function U) (i : Fin d) :
    ‖w.gradCoordToScalarL2 i‖ = Real.sqrt (∫ x in U, w.grad x i ^ (2 : ℕ) ∂volume) := by
  have hsq : ∫ x in U, w.grad x i ^ (2 : ℕ) ∂volume =
      ‖w.gradCoordToScalarL2 i‖ ^ (2 : ℕ) := by
    simpa [H1Function.gradCoordToScalarL2, HCPolySupport.toScalarL2] using
      (toReal_eLpNorm_two_sq_eq_integral_sq (w.gradMemL2 i)).symm
  rw [hsq, Real.sqrt_sq (norm_nonneg _)]

/-! ## 2. The gradient sum is dominated by the supremum-norm energy -/

theorem gradientCoordL2NormSum_le {U : Set (Vec d)} (w : H1Function U) :
    w.gradientCoordL2NormSum ≤
      (d : ℝ) * Real.sqrt (∫ x in U, ‖w.grad x‖ ^ (2 : ℕ) ∂volume) := by
  have hgradInt : IntegrableOn (fun x => ‖w.grad x‖ ^ (2 : ℕ)) U volume := by
    have hn : MemLp (fun x => ‖w.grad x‖) 2 (volume.restrict U) := w.grad_memVectorL2.norm
    have := hn.integrable_mul hn
    simpa [Pi.mul_apply, pow_two] using! this
  have hstep : ∀ i : Fin d, ‖w.gradCoordToScalarL2 i‖ ≤
      Real.sqrt (∫ x in U, ‖w.grad x‖ ^ (2 : ℕ) ∂volume) := by
    intro i
    rw [norm_gradCoordToScalarL2_eq_sqrt]
    refine Real.sqrt_le_sqrt ?_
    refine integral_mono ((w.gradMemL2 i).integrable_sq) hgradInt fun x => ?_
    have hle : |w.grad x i| ≤ ‖w.grad x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (w.grad x) i
    calc w.grad x i ^ (2 : ℕ) = |w.grad x i| ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ ‖w.grad x‖ ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  calc w.gradientCoordL2NormSum = ∑ i : Fin d, ‖w.gradCoordToScalarL2 i‖ := rfl
    _ ≤ ∑ _i : Fin d, Real.sqrt (∫ x in U, ‖w.grad x‖ ^ (2 : ℕ) ∂volume) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (d : ℝ) * Real.sqrt (∫ x in U, ‖w.grad x‖ ^ (2 : ℕ) ∂volume) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 3. The Poincaré inequality in integral form -/

/-- **The zero-trace Poincaré inequality, written between integrals.** -/
theorem exists_poincare_integral_constant [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ w : H10Function U,
      Real.sqrt (∫ x in U, w.toH1Function.toFun x ^ (2 : ℕ) ∂volume) ≤
        CP * Real.sqrt (∫ x in U, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) := by
  obtain ⟨C, hC, hbound⟩ :=
    HCPolySupport.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hU
  refine ⟨C * (d : ℝ), by positivity, fun w => ?_⟩
  have h1 := hbound w
  rw [norm_toScalarL2_eq_sqrt] at h1
  have h2 : C * w.toH1Function.gradientCoordL2NormSum ≤
      C * ((d : ℝ) * Real.sqrt (∫ x in U, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) :=
    mul_le_mul_of_nonneg_left (gradientCoordL2NormSum_le w.toH1Function) hC
  calc Real.sqrt (∫ x in U, w.toH1Function.toFun x ^ (2 : ℕ) ∂volume)
      ≤ C * w.toH1Function.gradientCoordL2NormSum := h1
    _ ≤ C * ((d : ℝ) * Real.sqrt (∫ x in U, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) := h2
    _ = C * (d : ℝ) * Real.sqrt (∫ x in U, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) := by
        ring

/-! ## 4. Solvability for a general elliptic field -/

/-- **The Dirichlet problem on `y + □_n` is solvable for every coefficient field
that is elliptic on the cube.** -/
theorem exists_isDirichletSolutionAt_of_isEllipticFieldOn [NeZero d] {y : Vec d} {n : ℤ}
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g) :
    ∃ u : H1Function (cubeSetAt y n), IsDirichletSolutionAt a y n u g := by
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  have hforce : MemVectorL2 (cubeSetAt y n) (fun x => -g x) :=
    (memVectorL2_of_holderSeminormBoundOn_cubeSetAt hKg (by norm_num) hg).neg
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := cubeSetAt y n) (g := fun x => -g x) (lam := lam)
      hforce
      (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
        (isOpenBoundedConvexDomain_cubeSetAt y n))
      (cubeSetAt_nonempty y n) hEll
  refine ⟨w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  exact (isZeroTraceDirichletRhsWeakSolution_iff_isDivFormWeakSolutionOn
    (u := w.toH1Function) (w := w) (fun _ => rfl)).1 hw

end

end Algsuperdiff.Section5.Support
