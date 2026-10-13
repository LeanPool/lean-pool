/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicInteriorGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationDecayAverage
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.DerivativeBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# OscillationDecayGap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The arbitrary-gap oscillation decay for a harmonic gradient

This module proves the estimate that the nested-recentring route of
`OscillationTelescope` consumes once per birth scale: for a function `u` which is
harmonic on the coarse concentric cube `z + cu_{n+k}` and for **any** constant
vector `c`,

```
  || grad u - (grad u)_{z + cu_n} ||_{L2bar (z + cu_n)}
      <= C (d) 3^{-k} || grad u - c ||_{L2bar (z + cu_{n+k})} ,      k >= d + 2 .
```

The gain is the *full* factor `3^{-k}` for an arbitrary gap `k`, obtained by
one direct estimate from the coarse scale to the fine scale.  The `3^{-k}`
above is honest precisely because `k` is large: the estimate is a *single*
interior estimate on a Euclidean ball of radius comparable to `3^{n+k}`, never
an iterated one.

## The argument

1. **Geometry.**  For `k >= d + 2` and `y` in the fine cube, the Euclidean ball
   `B (y, 3^{n+k}/8)` is contained in the coarse cube.  This uses only the free
   (sup-norm) inclusion `closedBall (y, rho) subset y + cu_m` for
   `rho < 3^m/2` together with the concentric containment criterion of
   `OscillationCubeFamily`; no `sqrt d` is paid, and the restriction `k >= 2`
   suffices for this step alone.  The genuine `k >= d + 2` restriction enters
   through `HarmonicGauge` where the fine cube must sit inside the ball.
2. **Interior estimate.**  `d_i u - c_i` is harmonic wherever `u` is
   (`euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero`, plus the fact that a
   constant shift changes neither the Laplacian nor the derivative), so
   `exists_interior_gradient_bound` bounds every second derivative
   `d_j d_i u (y)` by `C (d) / r` times the average of `|d_i u - c_i|` over
   `B (y, r)`, and that average is dominated by the coarse-cube integral.
3. **Mean value inequality.**  `Vec d` carries the sup norm, and
   `norm_clm_le_sum_basisVec_apply` turns the `d` coordinate bounds of step 2
   into a bound for the operator norm of `fderiv (d_i u)`.  The convex mean-value
   inequality on the cube then gives the pointwise oscillation bound with the
   sup-norm diameter `3^n`.
4. **Averaging.**  `OscillationDecayAverage` converts the resulting `L^1` average
   into the normalized `L^2` deviation (Cauchy--Schwarz), integrates the
   pointwise bound, and recentres at the volume average.

The scaling that makes the whole thing work is
`3^n / (3^{n+k}/8) = 8 * 3^{-k}`, i.e. the fine-cube diameter divided by the
interior radius.

## Contents

* `euclideanBall_eighth_subset_openCubeAtScale_of_gap` -- the geometric step.
* `gap_constant_identity` -- the one algebraic rearrangement of the constants.
* `exists_gradient_oscillation_gap_decay` -- **the arbitrary-gap estimate**.

## Divergences from the printed proof

* A **gap restriction** `k >= d + 2` is imposed.  The manuscript's proof runs
  on Euclidean balls and supplies no cube transfer; on cubes a small gap
  genuinely fails.
* The estimate is stated for a **concentric** cube family, which is what the
  nested-recentring argument needs; the printed one-step display is on balls.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ### The geometric step -/

/-- **Interior balls of the fine cube stay inside the coarse cube.**

For a triadic gap `k >= 2` and a centre `y` in the fine cube `z + cu_n`, the
Euclidean ball of radius `3^{n+k}/8` around `y` is contained in the coarse cube
`z + cu_{n+k}`.  Only the free sup-norm inclusion is used, so no dimensional
factor is paid here. -/
theorem euclideanBall_eighth_subset_openCubeAtScale_of_gap {z : Vec d} {n : ℤ} {k : ℕ}
    (hk : d + 2 ≤ k) {y : Vec d} (hy : y ∈ openCubeAtScale z n) :
    euclideanBall y ((3 : ℝ) ^ (n + (k : ℤ)) / 8) ⊆ openCubeAtScale z (n + (k : ℤ)) := by
  have hP : (0 : ℝ) < (3 : ℝ) ^ n := zpow_three_pos n
  have hSpos : (0 : ℝ) < (3 : ℝ) ^ (n + (k : ℤ)) := zpow_three_pos _
  have hnat : 9 ≤ 3 ^ k := by
    have h2 : (2 : ℕ) ≤ k := by omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by omega) h2
  have hQ : (9 : ℝ) ≤ (3 : ℝ) ^ k := by exact_mod_cast hnat
  have hS : (3 : ℝ) ^ (n + (k : ℤ)) = (3 : ℝ) ^ n * (3 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hSP : 9 * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (n + (k : ℤ)) := by
    rw [hS]
    nlinarith
  have hmid : (3 : ℝ) ^ (n + (k : ℤ)) = (3 : ℝ) ^ (n + (k : ℤ) - 1) * 3 := by
    rw [← zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hstep1 : euclideanClosedBall y ((3 : ℝ) ^ (n + (k : ℤ)) / 8)
      ⊆ openCubeAtScale y (n + (k : ℤ) - 1) := by
    refine euclideanClosedBall_subset_openCubeAtScale (by positivity) ?_
    linarith
  have hstep2 : openCubeAtScale y (n + (k : ℤ) - 1) ⊆ openCubeAtScale z (n + (k : ℤ)) := by
    refine openCubeAtScale_subset_of_forall_abs_add_le fun i => ?_
    have hyi : |y i - z i| < (3 : ℝ) ^ n / 2 := (mem_openCubeAtScale_iff z n y).mp hy i
    linarith
  intro x hx
  refine hstep2 (hstep1 ?_)
  have hx' : euclideanSqDist x y < ((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ 2 := hx
  exact le_of_lt hx'

/-! ### The constant bookkeeping -/

/-- The single algebraic rearrangement behind the arbitrary-gap constant:
the interior radius `S/8`, the coarse-cube volume `S^d` and the ball volume
`(S/8)^d omega_d` combine so that the fine-cube diameter `P` produces exactly the
prefactor `8^{d+1} d C / omega_d` times `P / S`. -/
theorem gap_constant_identity (d : ℕ) {S P ω C avg : ℝ}
    (hS : S ≠ 0) (hω : ω ≠ 0) :
    (d : ℝ) * (C / (S / 8) * (S ^ d * avg / ((S / 8) ^ d * ω))) * P
      = 8 ^ (d + 1) * (d : ℝ) * C / ω * (P / S) * avg := by
  have hSd : S ^ d ≠ 0 := pow_ne_zero d hS
  have h8 : ((8 : ℝ)) ^ d ≠ 0 := by positivity
  rw [div_pow]
  field_simp
  ring

/-! ### The arbitrary-gap oscillation estimate -/

private theorem correctorGradient_oscillation_pointwise_bound :
    ∀ {d : ℕ} (C₀ : ℝ),
      (0 : ℝ) ≤ (8 : ℝ) ^ (d + (1 : ℕ)) * (↑d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d →
        ∀ (u : Vec d → ℝ) (z : Vec d) (n : ℤ) (k : ℕ) (c : Vec d) (avg : Fin d → ℝ),
          (∀ (i : Fin d), (0 : ℝ) ≤ avg i) →
            (∀ (i : Fin d),
                ∀ x ∈ openCubeAtScale z n,
                  |euclideanCoordDeriv i u x - euclideanCoordDeriv i u z| ≤
                    (8 : ℝ) ^ (d + (1 : ℕ)) * (↑d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d
                      * (3 : ℝ) ^ (-(↑k : ℤ)) *
                      avg i) →
              (∀ (i : Fin d),
                  avg i ^ (2 : ℕ) ≤
                    Book.Ch01.meanSquareDeviationOn (openCubeAtScale z (n + (↑k : ℤ)))
                      (fun (y : Vec d) => euclideanGradient u y i) (c i)) →
                ∀ x ∈ openCubeAtScale z n,
                  vecNormSq (euclideanGradient u x - euclideanGradient u z) ≤
                    ((8 : ℝ) ^ (d + (1 : ℕ)) * (↑d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
                          (3 : ℝ) ^ (-(↑k : ℤ))) ^
                        (2 : ℕ) *
                      Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (↑k : ℤ)))
                        (euclideanGradient u) c := by
  intro d C₀ hKnn u z n k c avg havgnn hlip hcs x hx
  have hexpand : vecNormSq (euclideanGradient u x - euclideanGradient u z)
      = ∑ i : Fin d, (euclideanCoordDeriv i u x - euclideanCoordDeriv i u z) ^ 2 := by
    simp [vecNormSq, vecDot, sq, euclideanGradient]
  rw [hexpand]
  have hterm : ∀ i : Fin d,
      (euclideanCoordDeriv i u x - euclideanCoordDeriv i u z) ^ 2
        ≤ (8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
            (3 : ℝ) ^ (-(k : ℤ))) ^ 2 * avg i ^ 2 := by
    intro i
    have hb := hlip i x hx
    have hnn : (0 : ℝ) ≤ 8 ^ (d + 1) * (d : ℝ) * C₀ /
        Book.Ch01.euclideanUnitBallVolume d * (3 : ℝ) ^ (-(k : ℤ)) * avg i :=
      mul_nonneg (mul_nonneg hKnn (by positivity)) (havgnn i)
    have hsq : (euclideanCoordDeriv i u x - euclideanCoordDeriv i u z) ^ 2
        ≤ (8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
            (3 : ℝ) ^ (-(k : ℤ)) * avg i) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc (euclideanCoordDeriv i u x - euclideanCoordDeriv i u z) ^ 2
        ≤ (8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
            (3 : ℝ) ^ (-(k : ℤ)) * avg i) ^ 2 := hsq
      _ = (8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
            (3 : ℝ) ^ (-(k : ℤ))) ^ 2 * avg i ^ 2 := by ring
  calc ∑ i : Fin d, (euclideanCoordDeriv i u x - euclideanCoordDeriv i u z) ^ 2
      ≤ ∑ i : Fin d, (8 ^ (d + 1) * (d : ℝ) * C₀ /
            Book.Ch01.euclideanUnitBallVolume d * (3 : ℝ) ^ (-(k : ℤ))) ^ 2 * avg i ^ 2 :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
          (3 : ℝ) ^ (-(k : ℤ))) ^ 2 * ∑ i : Fin d, avg i ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
          (3 : ℝ) ^ (-(k : ℤ))) ^ 2 *
        Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (k : ℤ)))
          (euclideanGradient u) c :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcs i) (sq_nonneg _)

private theorem gradientOscillation_affineLipschitzBound :
    ∀ {d : ℕ},
      (0 : ℕ) < d →
        ∀ (C₀ : ℝ),
          (0 : ℝ) ≤ C₀ →
            (0 : ℝ) < Book.Ch01.euclideanUnitBallVolume d →
              ∀ (u : Vec d → ℝ) (z : Vec d) (n : ℤ) (k : ℕ) (avg : Fin d → ℝ),
                (∀ (i : Fin d), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (euclideanCoordDeriv i u)) →
                  (∀ (i : Fin d),
                      ∀ y ∈ openCubeAtScale z n,
                        ‖fderiv ℝ (euclideanCoordDeriv i u) y‖ ≤
                          (↑d : ℝ) *
                            (C₀ / ((3 : ℝ) ^ (n + (↑k : ℤ)) / (8 : ℝ)) *
                              (((3 : ℝ) ^ (n + (↑k : ℤ))) ^ d * avg i /
                                (((3 : ℝ) ^ (n + (↑k : ℤ)) / (8 : ℝ)) ^ d *
                                  Book.Ch01.euclideanUnitBallVolume d)))) →
                    (∀ (i : Fin d),
                        (↑d : ℝ) *
                              (C₀ / ((3 : ℝ) ^ (n + (↑k : ℤ)) / (8 : ℝ)) *
                                (((3 : ℝ) ^ (n + (↑k : ℤ))) ^ d * avg i /
                                  (((3 : ℝ) ^ (n + (↑k : ℤ)) / (8 : ℝ)) ^ d *
                                    Book.Ch01.euclideanUnitBallVolume d))) *
                            (3 : ℝ) ^ n =
                          (8 : ℝ) ^ (d + (1 : ℕ)) * (↑d : ℝ) * C₀ /
                            Book.Ch01.euclideanUnitBallVolume d *
                              (3 : ℝ) ^ (-(↑k : ℤ)) *
                            avg i) →
                      (∀ (i : Fin d), (0 : ℝ) ≤ avg i) →
                        ∀ (i : Fin d),
                          ∀ x ∈ openCubeAtScale z n,
                            |euclideanCoordDeriv i u x - euclideanCoordDeriv i u z| ≤
                              (8 : ℝ) ^ (d + (1 : ℕ)) * (↑d : ℝ) * C₀ /
                                Book.Ch01.euclideanUnitBallVolume d *
                                  (3 : ℝ) ^ (-(↑k : ℤ)) *
                                avg i := by
  intro d _ C₀ _ _ u z n k avg hDsmooth hopnorm hprefac havgnn i x hx
  have hdiff : ∀ w ∈ openCubeAtScale z n, DifferentiableAt ℝ (euclideanCoordDeriv i u) w :=
    fun w _ => ((hDsmooth i).differentiable (by simp)) w
  have hmvt := (convex_openCubeAtScale z n).norm_image_sub_le_of_norm_fderiv_le
    hdiff (fun w hw => hopnorm i w hw) (mem_openCubeAtScale_self z n) hx
  have hnorm : ‖x - z‖ ≤ (3 : ℝ) ^ n :=
    norm_sub_le_of_mem_openCubeAtScale hx (mem_openCubeAtScale_self z n)
  have hcnn : (0 : ℝ) ≤ (d : ℝ) * (C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
      (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
        / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
            * Book.Ch01.euclideanUnitBallVolume d))) := by
    have := havgnn i
    have h1 : (0 : ℝ) ≤ C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) := by positivity
    have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
        / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
            * Book.Ch01.euclideanUnitBallVolume d) := by positivity
    positivity
  calc |euclideanCoordDeriv i u x - euclideanCoordDeriv i u z|
      ≤ (d : ℝ) * (C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
          (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
            / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
                * Book.Ch01.euclideanUnitBallVolume d))) * ‖x - z‖ := hmvt
    _ ≤ (d : ℝ) * (C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
          (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
            / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
                * Book.Ch01.euclideanUnitBallVolume d))) * (3 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hnorm hcnn
    _ = _ := hprefac i

/-- **The arbitrary-gap oscillation decay for a harmonic gradient.**

If `u` is smooth and harmonic on the coarse concentric cube `z + cu_{n+k}` with
gap `k >= d + 2`, then for every constant vector `c` the normalized mean-square
gradient oscillation on the fine cube `z + cu_n` is at most `C (d) 3^{-k}` times
the normalized `L^2` deviation of `grad u` from `c` on the coarse cube.  The
constant depends only on the dimension.

The estimate is a *direct* one from the coarse scale to the fine scale.  No
adjacent-scale cube recurrence is formed anywhere, and none could be:. -/
theorem exists_gradient_oscillation_gap_decay {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ (z : Vec d) (n : ℤ) (k : ℕ), d + 2 ≤ k →
        (∀ x ∈ openCubeAtScale z (n + (k : ℤ)), euclideanCoordLaplacian u x = 0) →
        ∀ c : Vec d,
          Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n)
              (euclideanGradient u))
            ≤ C * (3 : ℝ) ^ (-(k : ℤ)) *
              Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                (openCubeAtScale z (n + (k : ℤ))) (euclideanGradient u) c) := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := exists_interior_gradient_bound hd
  have hω : 0 < Book.Ch01.euclideanUnitBallVolume d := euclideanUnitBallVolume_pos d
  have hKnn : (0 : ℝ) ≤ 8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg d)) hC₀nn) hω.le
  refine ⟨_, hKnn, ?_⟩
  intro u hu z n k hk hharm c
  -- abbreviations
  have hP : (0 : ℝ) < (3 : ℝ) ^ n := zpow_three_pos n
  have hS : (0 : ℝ) < (3 : ℝ) ^ (n + (k : ℤ)) := zpow_three_pos _
  have hr : (0 : ℝ) < (3 : ℝ) ^ (n + (k : ℤ)) / 8 := by positivity
  have hvolVc : (volume (openCubeAtScale z (n + (k : ℤ)))).toReal
      = ((3 : ℝ) ^ (n + (k : ℤ))) ^ d := volume_openCubeAtScale_toReal z _
  have hvolVcpos : 0 < (volume (openCubeAtScale z (n + (k : ℤ)))).toReal :=
    volume_openCubeAtScale_toReal_pos z _
  have hvolVfpos : 0 < (volume (openCubeAtScale z n)).toReal :=
    volume_openCubeAtScale_toReal_pos z n
  obtain ⟨avg, havg⟩ : ∃ f : Fin d → ℝ, ∀ i : Fin d,
      f i = volumeAverage (openCubeAtScale z (n + (k : ℤ)))
        (fun x => |euclideanCoordDeriv i u x - c i|) := ⟨_, fun _ => rfl⟩
  -- smoothness and continuity of the coordinate derivatives
  have hDsmooth : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i u) := fun i =>
    contDiff_euclideanCoordDeriv hu i
  have hDcont : ∀ i : Fin d, Continuous (euclideanCoordDeriv i u) := fun i =>
    (hDsmooth i).continuous
  -- a constant shift changes neither the coordinate derivative nor the Laplacian
  have hgderiv : ∀ (i p : Fin d),
      euclideanCoordDeriv p (fun x => euclideanCoordDeriv i u x - c i)
        = euclideanCoordDeriv p (euclideanCoordDeriv i u) := by
    intro i p
    funext w
    change fderiv ℝ (fun x => euclideanCoordDeriv i u x - c i) w (basisVec p)
      = fderiv ℝ (euclideanCoordDeriv i u) w (basisVec p)
    rw [fderiv_sub_const]
  have hglap : ∀ (i : Fin d) (x : Vec d),
      euclideanCoordLaplacian (fun y => euclideanCoordDeriv i u y - c i) x
        = euclideanCoordLaplacian (euclideanCoordDeriv i u) x := by
    intro i x
    change ∑ p : Fin d, euclideanCoordSecondDeriv p p
        (fun y => euclideanCoordDeriv i u y - c i) x
      = ∑ p : Fin d, euclideanCoordSecondDeriv p p (euclideanCoordDeriv i u) x
    refine Finset.sum_congr rfl fun p _ => ?_
    change fderiv ℝ (euclideanCoordDeriv p (fun y => euclideanCoordDeriv i u y - c i)) x
        (basisVec p)
      = fderiv ℝ (euclideanCoordDeriv p (euclideanCoordDeriv i u)) x (basisVec p)
    rw [hgderiv i p]
  have hDharm : ∀ (i : Fin d) (x : Vec d), x ∈ openCubeAtScale z (n + (k : ℤ)) →
      euclideanCoordLaplacian (euclideanCoordDeriv i u) x = 0 := fun i x hx =>
    euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero hu
      (isOpen_openCubeAtScale z (n + (k : ℤ))) hharm hx i
  -- integrability on the coarse cube
  have hintAbs : ∀ i : Fin d, IntegrableOn
      (fun x => |euclideanCoordDeriv i u x - c i|)
      (openCubeAtScale z (n + (k : ℤ))) volume := fun i =>
    integrableOn_openCubeAtScale_of_continuous
      (((hDcont i).sub continuous_const).abs) z _
  have hAavg : ∀ i : Fin d,
      ∫ x in openCubeAtScale z (n + (k : ℤ)), |euclideanCoordDeriv i u x - c i| ∂volume
        = ((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i := by
    intro i
    have hstep : avg i = (volume (openCubeAtScale z (n + (k : ℤ)))).toReal⁻¹ *
        ∫ x in openCubeAtScale z (n + (k : ℤ)),
          |euclideanCoordDeriv i u x - c i| ∂volume := by
      rw [havg i]
      rfl
    rw [hstep, ← hvolVc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hvolVcpos), one_mul]
  -- step 2: the interior second-derivative bound at every point of the fine cube
  have hkey : ∀ (i j : Fin d) (y : Vec d), y ∈ openCubeAtScale z n →
      |fderiv ℝ (euclideanCoordDeriv i u) y (basisVec j)|
        ≤ C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
            (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
              / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
                  * Book.Ch01.euclideanUnitBallVolume d)) := by
    intro i j y hy
    have hball := euclideanBall_eighth_subset_openCubeAtScale_of_gap hk hy
    have hgharm : ∀ x ∈ euclideanBall y ((3 : ℝ) ^ (n + (k : ℤ)) / 8),
        euclideanCoordLaplacian (fun w => euclideanCoordDeriv i u w - c i) x = 0 := by
      intro x hx
      rw [hglap i x]
      exact hDharm i x (hball hx)
    have hbound := hC₀ (fun w => euclideanCoordDeriv i u w - c i)
      ((hDsmooth i).sub contDiff_const) _ hr y hgharm j
    have hcoord : euclideanCoordDeriv j (fun w => euclideanCoordDeriv i u w - c i) y
        = fderiv ℝ (euclideanCoordDeriv i u) y (basisVec j) := by
      rw [hgderiv i j]
      rfl
    rw [hcoord] at hbound
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hvolball : (volume (euclideanBall y ((3 : ℝ) ^ (n + (k : ℤ)) / 8))).toReal
        = ((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d * Book.Ch01.euclideanUnitBallVolume d :=
      volume_euclideanBall_toReal y hr
    have hmono : ∫ x in euclideanBall y ((3 : ℝ) ^ (n + (k : ℤ)) / 8),
          |euclideanCoordDeriv i u x - c i| ∂volume
        ≤ ∫ x in openCubeAtScale z (n + (k : ℤ)),
            |euclideanCoordDeriv i u x - c i| ∂volume :=
      setIntegral_mono_set (hintAbs i)
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hball hx)
    rw [hvolball, ← hAavg i]
    exact div_le_div_of_nonneg_right hmono (by positivity)
  -- step 3: the mean value inequality on the convex fine cube
  have hopnorm : ∀ (i : Fin d) (y : Vec d), y ∈ openCubeAtScale z n →
      ‖fderiv ℝ (euclideanCoordDeriv i u) y‖
        ≤ (d : ℝ) * (C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
            (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
              / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
                  * Book.Ch01.euclideanUnitBallVolume d))) := by
    intro i y hy
    refine (HCPolySupport.norm_clm_le_sum_basisVec_apply
      (fderiv ℝ (euclideanCoordDeriv i u) y)).trans ?_
    calc ∑ _j : Fin d, ‖fderiv ℝ (euclideanCoordDeriv i u) y (basisVec _j)‖
        ≤ ∑ _j : Fin d, C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
            (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
              / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
                  * Book.Ch01.euclideanUnitBallVolume d)) :=
          Finset.sum_le_sum fun j _ => hkey i j y hy
      _ = (d : ℝ) * (C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
            (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
              / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
                  * Book.Ch01.euclideanUnitBallVolume d))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hprefac : ∀ i : Fin d,
      (d : ℝ) * (C₀ / ((3 : ℝ) ^ (n + (k : ℤ)) / 8) *
          (((3 : ℝ) ^ (n + (k : ℤ))) ^ d * avg i
            / (((3 : ℝ) ^ (n + (k : ℤ)) / 8) ^ d
                * Book.Ch01.euclideanUnitBallVolume d))) * (3 : ℝ) ^ n
        = 8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
            (3 : ℝ) ^ (-(k : ℤ)) * avg i := by
    intro i
    have hnegk : (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ n / (3 : ℝ) ^ (n + (k : ℤ)) := by
      rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    rw [hnegk]
    exact gap_constant_identity d (ne_of_gt hS) (ne_of_gt hω)
  have havgnn : ∀ i : Fin d, 0 ≤ avg i := by
    intro i
    rw [havg i]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x => abs_nonneg _)
  have hlip := @gradientOscillation_affineLipschitzBound (d) (hd) (C₀) (hC₀nn) (hω) (u) (z) (n)
    (k) (avg) (hDsmooth) (hopnorm) (hprefac) (havgnn)
  -- step 4: from the pointwise bound to the mean-square oscillation
  have hcs : ∀ i : Fin d, avg i ^ 2 ≤
      Book.Ch01.meanSquareDeviationOn (openCubeAtScale z (n + (k : ℤ)))
        (fun y => euclideanGradient u y i) (c i) := by
    intro i
    rw [havg i]
    exact sq_volumeAverage_abs_sub_le_meanSquareDeviationOn
      (volume_openCubeAtScale_ne_top z _) hvolVcpos
      (integrableOn_openCubeAtScale_of_continuous ((hDcont i).sub continuous_const) z _)
      (integrableOn_openCubeAtScale_of_continuous
        (((hDcont i).sub continuous_const).pow 2) z _)
  have hptw := @correctorGradient_oscillation_pointwise_bound (d) (C₀) (hKnn) (u) (z) (n) (k) (c)
    (avg) (havgnn) (hlip) (hcs)
  have hdev : Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n)
      (euclideanGradient u) (euclideanGradient u z)
      ≤ (8 ^ (d + 1) * (d : ℝ) * C₀ / Book.Ch01.euclideanUnitBallVolume d *
          (3 : ℝ) ^ (-(k : ℤ))) ^ 2 *
        Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (n + (k : ℤ)))
          (euclideanGradient u) c :=
    meanSquareDeviationVecOn_le_of_forall_vecNormSq_le
      (measurableSet_openCubeAtScale z n) (volume_openCubeAtScale_ne_top z n) hvolVfpos
      (fun i => integrableOn_openCubeAtScale_of_continuous
        (((hDcont i).sub continuous_const).pow 2) z n) hptw
  have hosc : Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale z n)
      (euclideanGradient u)
      ≤ Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z n)
        (euclideanGradient u) (euclideanGradient u z) :=
    meanSquareOscillationVecOn_le_meanSquareDeviationVecOn
      (volume_openCubeAtScale_ne_top z n) hvolVfpos (euclideanGradient u z)
      (fun i => integrableOn_openCubeAtScale_of_continuous (hDcont i) z n)
      (fun i => integrableOn_openCubeAtScale_of_continuous ((hDcont i).pow 2) z n)
  have hfinal := Real.sqrt_le_sqrt (hosc.trans hdev)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
    (mul_nonneg hKnn (by positivity))] at hfinal
  exact hfinal

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
