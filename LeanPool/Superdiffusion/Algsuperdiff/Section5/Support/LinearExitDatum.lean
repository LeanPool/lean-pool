/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.FieldDivergenceTest
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.Translation

/-!
# LinearExitDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The linear datum of the exit-time problem

The exit-time comparison of Section 5.2 writes the constant right-hand side `1`
as the divergence of the linear vector field `g(x) = x_1 e_1`, so that the
exit-time equation becomes an instance of the localized Dirichlet problem
`-∇·a∇w = ∇·g` of Section 5.1, whose homogenization is the injection estimate.

Two facts are needed about that datum: its `1/2`-Hölder seminorm on a cube of
side `3^n` is at most `3^{n/2}`, so that the injection estimate's right-hand
side is `C ε 3^{n/2} · 3^{n/2} = C ε 3^n`; and its weak form is the constant
forcing, `∫ a∇w·∇φ = ∫ φ`, which is the equation `-∇·a∇w = 1`.

## The sign

`IsDirichletSolutionAt` renders `-∇·a∇u = ∇·g` as `∫ a∇u·∇φ = -∫ g·∇φ`.  With
`g(x) = x_1 e_1` the right side is `-∫ x_1 ∂_1φ = +∫ φ`, one integration by
parts against a zero-trace test function; so the datum `g` carries the *positive*
constant forcing and the solution is the (nonnegative) exit-time profile, not its
negative.

## Main definitions

* `linearAxisDatum i` — the field `x ↦ x_i e_i`.

## Main results

* `vecFieldDiv_linearAxisDatum` — `∇·g = 1`.
* `holderSeminormOn_linearAxisDatum_le` — `[g]_{C^{0,1/2}(y+□_n)} ≤ 3^{n/2}`.
* `isDirichletSolutionAt_linearAxisDatum_iff` — the weak form of the datum is
  the constant forcing `∫ a∇u·∇φ = ∫ φ`.

## References

* ABK26, the exit-time comparison of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The field and its divergence -/

/-- **The linear datum `g(x) = x_i e_i`**, whose divergence is the constant
`1`. -/
def linearAxisDatum (i : Fin d) : Vec d → Vec d := fun x => (x i) • basisVec i

private theorem hasFDerivAt_linearAxisDatum_coord (i j : Fin d) (x : Vec d) :
    HasFDerivAt (fun z : Vec d => linearAxisDatum i z j)
      (basisVec i j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)) x :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt).mul_const _

/-- Each component of the linear datum is `C¹`. -/
theorem contDiff_linearAxisDatum_coord (i j : Fin d) :
    ContDiff ℝ 1 fun z : Vec d => linearAxisDatum i z j :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff.mul contDiff_const

/-- **`∇·g = 1`** for the linear datum `g(x) = x_i e_i`. -/
theorem vecFieldDiv_linearAxisDatum (i : Fin d) (x : Vec d) :
    vecFieldDiv (linearAxisDatum i) x = 1 := by
  classical
  rw [vecFieldDiv_apply]
  have hterm : ∀ j : Fin d,
      (fderiv ℝ (fun z : Vec d => linearAxisDatum i z j) x) (basisVec j) =
        basisVec j i * basisVec i j := by
    intro j
    rw [(hasFDerivAt_linearAxisDatum_coord i j x).fderiv]
    by_cases h : j = i <;> simp [h]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji, Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## 2. The Hölder seminorm of the linear datum -/

private theorem rpow_zpow_three_half (n : ℤ) :
    ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) = Real.rpow 3 ((n : ℝ) / 2) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_intCast (3 : ℝ) n, ← Real.rpow_mul h3.le, mul_one_div]
  rfl

/-- **The `1/2`-Hölder bound for the linear datum on a cube of side `3^n`.**
The dimensional constant is `1`: the increment of `g` is one coordinate
increment, which the supremum norm dominates. -/
theorem holderSeminormBoundOn_linearAxisDatum (i : Fin d) (y : Vec d) (n : ℤ) :
    HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (Real.rpow 3 ((n : ℝ) / 2))
      (linearAxisDatum i) := by
  intro x hx z hz
  have hdist : ‖x - z‖ ≤ (3 : ℝ) ^ n := (norm_sub_lt_of_mem_cubeSetAt hx hz).le
  have hbase : ‖linearAxisDatum i x - linearAxisDatum i z‖ ≤ ‖x - z‖ := by
    have hsub : linearAxisDatum i x - linearAxisDatum i z = (x i - z i) • basisVec i := by
      funext j
      simp only [linearAxisDatum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsub, norm_smul, Real.norm_eq_abs]
    have hb : ‖basisVec i‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      rw [Real.norm_eq_abs, basisVec_apply]
      by_cases hj : j = i <;> simp [hj]
    have hcoord : |x i - z i| ≤ ‖x - z‖ := by
      have := norm_le_pi_norm (x - z) i
      rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    calc |x i - z i| * ‖basisVec i‖ ≤ |x i - z i| * 1 :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = |x i - z i| := mul_one _
      _ ≤ ‖x - z‖ := hcoord
  have hsplit : ‖x - z‖ ^ (1 / 2 : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ) = ‖x - z‖ := by
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num : (1 / 2 : ℝ) + 1 / 2 ≠ 0)]
    norm_num
  have hmono : ‖x - z‖ ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hdist (by norm_num)
  calc ‖linearAxisDatum i x - linearAxisDatum i z‖ ≤ ‖x - z‖ := hbase
    _ = ‖x - z‖ ^ (1 / 2 : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ) := hsplit.symm
    _ ≤ ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (norm_nonneg _) _)
    _ = Real.rpow 3 ((n : ℝ) / 2) * ‖x - z‖ ^ (1 / 2 : ℝ) := by
        rw [rpow_zpow_three_half]

/-- **The `ℝ≥0∞` form of the Hölder bound for the linear datum.** -/
theorem holderSeminormOn_linearAxisDatum_le (i : Fin d) (y : Vec d) (n : ℤ) :
    holderSeminormOn (cubeSetAt y n) (1 / 2) (linearAxisDatum i) ≤
      ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) :=
  (holderSeminormOn_le_ofReal_iff (Real.rpow_nonneg (by norm_num) _)).2
    (holderSeminormBoundOn_linearAxisDatum i y n)

/-! ## 3. The weak form: the constant forcing -/

/-- **The linear datum tests as the constant `1`.** -/
theorem integral_vecDot_linearAxisDatum_h10Grad (i : Fin d) (y : Vec d) (n : ℤ)
    (phi : H10Function (cubeSetAt y n)) :
    ∫ x in cubeSetAt y n, vecDot (linearAxisDatum i x) (phi.toH1Function.grad x) ∂volume =
      -∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume := by
  have h := integral_vecDot_h10Grad_eq_neg_integral_vecFieldDiv_mul
    (measurableSet_cubeSetAt y n)
    (isOpenBoundedConvexDomain_cubeSetAt y n).isBoundedDomain
    (F := linearAxisDatum i) (fun j => contDiff_linearAxisDatum_coord i j) phi
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [vecFieldDiv_linearAxisDatum, one_mul]

/-- **The divergence-form equation at the linear datum is the constant forcing
`-∇·a∇u = 1`.** -/
theorem isDivFormWeakSolutionOn_linearAxisDatum_iff {a : CoeffField d} {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} (i : Fin d) :
    IsDivFormWeakSolutionOn a (cubeSetAt y n) u (linearAxisDatum i) ↔
      ∀ phi : H10Function (cubeSetAt y n),
        ∫ x in cubeSetAt y n,
            vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) ∂volume =
          ∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume := by
  rw [isDivFormWeakSolutionOn_def]
  constructor
  · intro h phi
    rw [h phi, integral_vecDot_linearAxisDatum_h10Grad i y n phi, neg_neg]
  · intro h phi
    rw [h phi, integral_vecDot_linearAxisDatum_h10Grad i y n phi, neg_neg]

/-- **The localized Dirichlet problem at the linear datum**: zero boundary values
and the constant forcing. -/
theorem isDirichletSolutionAt_linearAxisDatum_iff {a : CoeffField d} {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} (i : Fin d) :
    IsDirichletSolutionAt a y n u (linearAxisDatum i) ↔
      (∃ w : H10Function (cubeSetAt y n),
          (∀ x, u.toFun x = w.toH1Function.toFun x) ∧
            (∀ x, u.grad x = w.toH1Function.grad x)) ∧
        ∀ phi : H10Function (cubeSetAt y n),
          ∫ x in cubeSetAt y n,
              vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) ∂volume =
            ∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume := by
  rw [isDirichletSolutionAt_def, isDivFormWeakSolutionOn_linearAxisDatum_iff i]

end

end Algsuperdiff.Section5.Support
