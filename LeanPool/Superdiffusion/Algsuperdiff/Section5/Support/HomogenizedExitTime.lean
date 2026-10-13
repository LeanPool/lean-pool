/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ComparatorComparison
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ExitTimeBarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LinearExitDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedFinite
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RepresentativeComparator

/-!
# HomogenizedExitTime

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The homogenized exit time on a cube

The comparator problem of Section 5.1 at the linear datum `g(x) = x_i e_i` is the
homogenized exit-time problem

```text
  -σ_n Δ w = 1  in y + □_n ,      w = 0  on ∂(y + □_n) ,
```

and `exitTimeScale` is the pre-`T_r` expression `3^{2n}/σ_n` from display
(5.7).  The conversion using `(1 ± C γ^{1/2}|log γ|)` to the definition of
`T_r` is deferred.  This module proves that `w` and this scale are comparable,
with a dimensional constant:

```text
  C^{-1} ‖w‖_{L^∞(y+□_n)} ≤ T(3^n) ≤ C inf_{x ∈ y+□_{n-1}} w(x) .
```

The upper bound is the gradient bound of the comparator, which the interior
Schauder estimate supplies at the datum `g` in the form `‖∇w‖_∞ ≤ C σ_n^{-1}3^n`,
together with the zero boundary values: a zero-trace function with a bounded
gradient is bounded by the gradient bound times half the side length.  The lower
bound includes the coordinate sum and is `d · Ksup · 3^n / 2`.  The lower bound
is the comparison with a bump barrier of height `T(3^n)/K` supported
strictly inside the cube and constant on a ball containing the inner cube.

Both bounds are stated for an arbitrary solution of the comparator problem and an
arbitrary representative of it continuous on the cube: the solution is unique
away from a null set, and its continuous representative is then unique at every
point of the cube, so the two sides do not depend on either choice.

## Main definitions

* `exitTimeScale M n` — the pre-`T_r` scale `3^{2n}/σ_n`.

## Main results

* `homogenized_exit_time_bounds` — the two-sided comparison above.

## References

* ABK26, the exit-time comparison of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The time scale -/

/-- **The pre-`T_r` exit-time scale**, `3^{2n}/σ_n`. -/
def exitTimeScale (M : ABKModel d) (n : ℤ) : ℝ :=
  ((3 : ℝ) ^ n) ^ (2 : ℕ) / (Annealed.sigmaBar M n : ℝ)

theorem exitTimeScale_pos (M : ABKModel d) (n : ℤ) : 0 < exitTimeScale M n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hs : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  rw [exitTimeScale]
  positivity

/-! ## 2. An elementary bridge -/

private theorem vecDot_matVecMul_smul_one_left (c : ℝ) (x z : Vec d) :
    vecDot (matVecMul (c • (1 : Mat d)) x) z = c * vecDot x z := by
  have h : matVecMul (c • (1 : Mat d)) x = c • x := by
    funext j
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [h]
  simp [vecDot, Finset.mul_sum, mul_assoc]

/-! ## 3. The two-sided comparison -/

/-- **The homogenized exit time is comparable to the time scale `3^{2n}/σ_n`.**
The constant depends only on the dimension. -/
theorem homogenized_exit_time_bounds (d : ℕ) (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (n : ℤ) (y : Vec d) (i : Fin d)
        (v : H1Function (cubeSetAt y n)) (vRep : Vec d → ℝ),
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v
            (linearAxisDatum i) →
        IsCubeRepresentative y n v vRep →
        supNormOn (cubeSetAt y n) vRep ≤ ENNReal.ofReal (C * exitTimeScale M n) ∧
          ∀ x ∈ cubeSetAt y (n - 1), exitTimeScale M n ≤ C * vRep x := by
  obtain ⟨Cs, hCs, hmain⟩ := exists_lipschitzRepresentative_comparator d hdim
  obtain ⟨K, hK, hKbd⟩ := exists_bumpLaplacian_bound d
  have hd : 0 < d := by omega
  refine ⟨max ((d : ℝ) * Cs / 2) K, lt_of_lt_of_le hK (le_max_right _ _), ?_⟩
  intro M n y i v vRep hv hvRep
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  set t : ℝ := Real.rpow 3 ((n : ℝ) / 2) with ht_def
  have ht : (0 : ℝ) < t := Real.rpow_pos_of_pos (by norm_num) _
  have htt : t * t = (3 : ℝ) ^ n := by
    rw [ht_def]
    show (3 : ℝ) ^ ((n : ℝ) / 2) * (3 : ℝ) ^ ((n : ℝ) / 2) = (3 : ℝ) ^ n
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show (n : ℝ) / 2 + (n : ℝ) / 2 = ((n : ℤ) : ℝ) by ring, Real.rpow_intCast]
  constructor
  · -- the upper bound
    obtain ⟨v', vRep', Ksup, KHol, hv'sol, hKsup, hKHol, -, -, hest, hae', hLip, hsupN, -⟩ :=
      hmain M n y (linearAxisDatum i) t (holderSeminormBoundOn_linearAxisDatum i y n)
    have hrep' : IsCubeRepresentative y n v' vRep' :=
      ⟨hae'.symm, hLip.continuous.continuousOn⟩
    have heq : Set.EqOn vRep vRep' (cubeSetAt y n) :=
      isCubeRepresentative_eqOn (isDirichletSolutionAt_ae_unique_comparator M n y hv hv'sol).2
        hvRep hrep'
    have hhalf : Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)) = t := by
      rw [ht_def]
      congr 1
      ring
    have hneg : Real.rpow 3 (-((1 / 2 : ℝ) * (n : ℝ))) = t⁻¹ := by
      rw [← hhalf]
      show (3 : ℝ) ^ (-((1 / 2 : ℝ) * (n : ℝ))) = ((3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)))⁻¹
      exact Real.rpow_neg (by norm_num) _
    rw [hhalf, hneg] at hest
    have h1 : t⁻¹ * Ksup ≤ Cs * t⁻¹ * ((Annealed.sigmaBar M n : ℝ)⁻¹ * t * t) := by
      linarith only [hest, hKHol]
    have h2 : Ksup ≤ Cs * ((Annealed.sigmaBar M n : ℝ)⁻¹ * (3 : ℝ) ^ n) := by
      have hmul := mul_le_mul_of_nonneg_left h1 ht.le
      rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at hmul
      calc Ksup ≤ t * (Cs * t⁻¹ * ((Annealed.sigmaBar M n : ℝ)⁻¹ * t * t)) := hmul
        _ = Cs * ((Annealed.sigmaBar M n : ℝ)⁻¹ * (t * t)) := by field_simp
        _ = Cs * ((Annealed.sigmaBar M n : ℝ)⁻¹ * (3 : ℝ) ^ n) := by rw [htt]
    have hbound : (d : ℝ) * Ksup * (3 : ℝ) ^ n / 2 ≤
        max ((d : ℝ) * Cs / 2) K * exitTimeScale M n := by
      have hstep : (d : ℝ) * Ksup * (3 : ℝ) ^ n / 2 ≤
          (d : ℝ) * Cs / 2 * exitTimeScale M n := by
        have hmul : (d : ℝ) * Ksup ≤ (d : ℝ) * (Cs * ((Annealed.sigmaBar M n : ℝ)⁻¹ *
            (3 : ℝ) ^ n)) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)
        have hrw : (d : ℝ) * Cs / 2 * exitTimeScale M n =
            (d : ℝ) * (Cs * ((Annealed.sigmaBar M n : ℝ)⁻¹ * (3 : ℝ) ^ n)) * (3 : ℝ) ^ n / 2 := by
          rw [exitTimeScale]
          field_simp
        rw [hrw]
        have hd3 : (0 : ℝ) ≤ (3 : ℝ) ^ n / 2 := by positivity
        calc (d : ℝ) * Ksup * (3 : ℝ) ^ n / 2 = ((d : ℝ) * Ksup) * ((3 : ℝ) ^ n / 2) := by ring
          _ ≤ ((d : ℝ) * (Cs * ((Annealed.sigmaBar M n : ℝ)⁻¹ * (3 : ℝ) ^ n))) *
                ((3 : ℝ) ^ n / 2) := mul_le_mul_of_nonneg_right hmul hd3
          _ = (d : ℝ) * (Cs * ((Annealed.sigmaBar M n : ℝ)⁻¹ * (3 : ℝ) ^ n)) *
                (3 : ℝ) ^ n / 2 := by ring
      refine hstep.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (exitTimeScale_pos M n).le
    calc supNormOn (cubeSetAt y n) vRep = supNormOn (cubeSetAt y n) vRep' :=
          supNormOn_congr heq
      _ ≤ ENNReal.ofReal ((d : ℝ) * Ksup * (3 : ℝ) ^ n / 2) := hsupN
      _ ≤ ENNReal.ofReal (max ((d : ℝ) * Cs / 2) K * exitTimeScale M n) :=
          ENNReal.ofReal_le_ofReal hbound
  · -- the lower bound
    obtain ⟨bv, hbcont, hbval, hbsub⟩ := exists_exitTimeBarrier d y n hsig hK hKbd
    have hweak : ∀ phi : H10Function (cubeSetAt y n),
        (Annealed.sigmaBar M n : ℝ) *
            ∫ x in cubeSetAt y n, vecDot (v.grad x) (phi.toH1Function.grad x) ∂volume =
          ∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume := by
      intro phi
      have h := ((isDirichletSolutionAt_linearAxisDatum_iff i).1 hv).2 phi
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (Annealed.sigmaBar M n : ℝ) * vecDot (v.grad x) (phi.toH1Function.grad x) =
        vecDot (matVecMul ((Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) (v.grad x))
          (phi.toH1Function.grad x)
      rw [vecDot_matVecMul_smul_one_left]
    have hcmp := ae_le_of_constantForcingSubsolution hd hsig hv.1 hweak bv hbsub
    have haeRep : ∀ᵐ x ∂(volume.restrict (cubeSetAt y n)),
        bv.toH1Function.toFun x ≤ vRep x := by
      filter_upwards [hcmp, hvRep.1] with x h1 h2
      rw [h2]
      exact h1
    have hptw : ∀ x ∈ cubeSetAt y n, bv.toH1Function.toFun x ≤ vRep x :=
      le_of_ae_le_of_continuousOn (isOpen_cubeSetAt y n) haeRep hbcont.continuousOn hvRep.2
    have hsub : cubeSetAt y (n - 1) ⊆ cubeSetAt y n := by
      simpa using cubeSetAt_subset_cubeSetAt_succ y (n - 1)
    intro x hx
    have hval := hbval x hx
    have hle := hptw x (hsub hx)
    rw [hval] at hle
    have hApos : (0 : ℝ) < ((3 : ℝ) ^ n) ^ (2 : ℕ) / ((Annealed.sigmaBar M n : ℝ) * K) := by
      positivity
    have hKA : K * (((3 : ℝ) ^ n) ^ (2 : ℕ) / ((Annealed.sigmaBar M n : ℝ) * K)) =
        exitTimeScale M n := by
      rw [exitTimeScale]
      field_simp
    calc exitTimeScale M n
        = K * (((3 : ℝ) ^ n) ^ (2 : ℕ) / ((Annealed.sigmaBar M n : ℝ) * K)) := hKA.symm
      _ ≤ K * vRep x := mul_le_mul_of_nonneg_left hle hK.le
      _ ≤ max ((d : ℝ) * Cs / 2) K * vRep x :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans hApos.le hle)

end

end Algsuperdiff.Section5.Support
