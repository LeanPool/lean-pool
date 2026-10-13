/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.HomogenizationCorrectorPointwise
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsCubeStream
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RenormalizationAtRandomScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ZeroTraceSupNorm
public import LeanPool.Superdiffusion.Support.Sobolev.Foundations.Cutoff.OpenSet

/-!
# StoppedMomentsCubeModel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stopped moments of the stream process on a triadic cube, at the model

The stopped-moment bounds of the displacement estimates are composed here at the model: the
process is the stream process of a full sample, the cube is the triadic cube centred at the
origin at a scale `m`, the observables are the linear and quadratic data cut off by a smooth
function equal to one on the closed cube, and the corrector bounds are the ones of the
renormalization theorem at the sample.

The objects the quenched moment composition takes as free parameters are defined:

* `cubeCutoff d m` — a smooth cut-off between `0` and `1`, equal to one on the closed cube of
  scale `m` centred at the origin and supported in the open cube of the next scale;
* `cubeExitProbability M omega m t` — the probability that the stream process started at the
  origin has left the cube of scale `m` by the time `t`;
* `cubeStoppedMean M omega m t` — the vector whose `i`-th coordinate is the mean, at the exit
  time from the cube truncated at `t`, of the cut-off linear observable in the direction `i`;

and the two stopped bounds are proved for them, in the exact form that composition consumes:

* the squared norm of the stopped mean vector is at most `4 d (3^m)² EB²`;
* in every direction, the stopped mean of the cut-off quadratic observable is within
  `10 (3^m)² EB + 2 sigmaBar t` times the exit probability of `2 sigmaBar t`.

Both are proved under the corrector clause of the renormalization theorem at the sample and the
scale `m`, with the effective diffusivity `sigmaBar` and the error value `EB` of that clause; the
clause holds almost surely at every scale for the families of
`exists_renormalizationFamily_corrector`, and the almost-sure form on the full-sample carrier is
recorded at the end.  The side condition
`d sigmaBar t ≤ (3^m)²` of the composition is derived from the defining property of the
confinement scale.

## Main definitions

* `cubeCutoff`, `cubeExitProbability`, `cubeStoppedMean`.

## Main results

* `vecNormSq_cubeStoppedMean_le` — the squared stopped mean.
* `abs_cubeStoppedQuadratic_sub_le` — the stopped second moment in every direction.
* `dim_mul_sigmaBar_mul_le_three_zpow_sq_of_isConfinementScale` — the side condition.
* `ae_renormalizationCorrector_fullSample` — the corrector clause holds almost surely on the
  full-sample carrier, at every scale.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support Algsuperdiff.Section4.Provider.Holder
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## 1. The cut-off of the cube -/

/-- A smooth cut-off between `0` and `1`, equal to one on the closed cube of scale `m` centred at
the origin and supported in the open cube of the next scale. -/
theorem exists_cubeCutoff (d : ℕ) (m : ℤ) :
    ∃ c : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) c ∧ (∀ x, 0 ≤ c x ∧ c x ≤ 1) ∧
      (∀ x ∈ closure (cubeSetAt (0 : Vec d) m), c x = 1) ∧
      tsupport c ⊆ cubeSetAt (0 : Vec d) (m + 1) := by
  have hK : IsCompact (closure (cubeSetAt (0 : Vec d) m)) :=
    (isOpenBoundedConvexDomain_cubeSetAt (0 : Vec d) m).isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨χ, hχ, hbd, hone, hsupp⟩ := exists_contDiff_one_on_compact_tsupport_subset hK
    (closure_cubeSetAt_subset_cubeSetAt_succ (0 : Vec d) m) (isOpen_cubeSetAt (0 : Vec d) (m + 1))
  exact ⟨χ, hχ, hbd, fun x hx => hone hx, hsupp⟩

/-- **The cut-off of the cube of scale `m` centred at the origin**: smooth, between `0` and `1`,
equal to one on the closed cube, supported in the open cube of the next scale. -/
def cubeCutoff (d : ℕ) (m : ℤ) : Vec d → ℝ := Classical.choose (exists_cubeCutoff d m)

theorem contDiff_cubeCutoff (d : ℕ) (m : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (cubeCutoff d m) :=
  (Classical.choose_spec (exists_cubeCutoff d m)).1

theorem cubeCutoff_mem_Icc (d : ℕ) (m : ℤ) (x : Vec d) :
    0 ≤ cubeCutoff d m x ∧ cubeCutoff d m x ≤ 1 :=
  (Classical.choose_spec (exists_cubeCutoff d m)).2.1 x

theorem cubeCutoff_eq_one_of_mem_closure {m : ℤ} {x : Vec d}
    (hx : x ∈ closure (cubeSetAt (0 : Vec d) m)) : cubeCutoff d m x = 1 :=
  (Classical.choose_spec (exists_cubeCutoff d m)).2.2.1 x hx

theorem cubeCutoff_eq_one_of_mem {m : ℤ} {x : Vec d} (hx : x ∈ cubeSetAt (0 : Vec d) m) :
    cubeCutoff d m x = 1 :=
  cubeCutoff_eq_one_of_mem_closure (subset_closure hx)

theorem tsupport_cubeCutoff_subset (d : ℕ) (m : ℤ) :
    tsupport (cubeCutoff d m) ⊆ cubeSetAt (0 : Vec d) (m + 1) :=
  (Classical.choose_spec (exists_cubeCutoff d m)).2.2.2

theorem hasCompactSupport_cubeCutoff (d : ℕ) (m : ℤ) : HasCompactSupport (cubeCutoff d m) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    ((isOpenBoundedConvexDomain_cubeSetAt (0 : Vec d) (m + 1)).isBoundedDomain.isBounded.subset
      (tsupport_cubeCutoff_subset d m))

theorem continuous_cubeCutoff (d : ℕ) (m : ℤ) : Continuous (cubeCutoff d m) :=
  (contDiff_cubeCutoff d m).continuous

theorem abs_cubeCutoff_le_one (d : ℕ) (m : ℤ) (x : Vec d) : |cubeCutoff d m x| ≤ 1 :=
  abs_le.2 ⟨by linarith only [(cubeCutoff_mem_Icc d m x).1], (cubeCutoff_mem_Icc d m x).2⟩

theorem cubeCutoff_eq_zero_of_notMem {m : ℤ} {x : Vec d}
    (hx : x ∉ cubeSetAt (0 : Vec d) (m + 1)) : cubeCutoff d m x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_cubeCutoff_subset d m h)

/-! ## 2. The bounds for the cut-off observables -/

/-- A point of the cube of scale `m + 1` has supremum norm below half its side. -/
theorem norm_lt_of_mem_cubeSetAt_zero {m : ℤ} {x : Vec d} (hx : x ∈ cubeSetAt (0 : Vec d) m) :
    ‖x‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  rw [cubeSetAt_zero_eq] at hx
  exact norm_lt_of_mem_openCubeSet_originCube hx

/-- The cut-off linear observables are uniformly bounded, in every direction. -/
theorem abs_cubeCutoff_mul_affineObservable_le (d : ℕ) (m : ℤ) (i : Fin d) (z : Vec d) :
    |cubeCutoff d m z * affineObservable (basisVec i) z| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) := by
  have hB : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) := by positivity
  by_cases hz : z ∈ cubeSetAt (0 : Vec d) (m + 1)
  · have hnorm := (norm_lt_of_mem_cubeSetAt_zero hz).le
    have hzi : |z i| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
    rw [abs_mul, show affineObservable (basisVec i) z = z i from vecDot_basisVec_left i z]
    calc |cubeCutoff d m z| * |z i| ≤ 1 * ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) :=
          mul_le_mul (abs_cubeCutoff_le_one d m z) (hzi.trans hnorm) (abs_nonneg _) zero_le_one
      _ = (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) := one_mul _
  · rw [cubeCutoff_eq_zero_of_notMem hz, zero_mul, abs_zero]
    exact hB

/-- The cut-off quadratic observables are uniformly bounded, in every direction. -/
theorem abs_cubeCutoff_mul_quadraticObservable_le (d : ℕ) (m : ℤ) (i : Fin d) (z : Vec d) :
    |cubeCutoff d m z * quadraticObservable (basisVec i) z| ≤
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
  have hB : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) := by positivity
  by_cases hz : z ∈ cubeSetAt (0 : Vec d) (m + 1)
  · have hnorm := (norm_lt_of_mem_cubeSetAt_zero hz).le
    have hzi : |z i| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
    have hq : quadraticObservable (basisVec i) z = z i * z i := by
      show vecDot (basisVec i) z * vecDot (basisVec i) z = z i * z i
      rw [vecDot_basisVec_left]
    rw [abs_mul, hq, abs_mul]
    calc |cubeCutoff d m z| * (|z i| * |z i|)
        ≤ 1 * (((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) * ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1))) := by
          refine mul_le_mul (abs_cubeCutoff_le_one d m z) ?_ (by positivity) zero_le_one
          exact mul_le_mul (hzi.trans hnorm) (hzi.trans hnorm) (abs_nonneg _) hB
      _ = ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by ring
  · rw [cubeCutoff_eq_zero_of_notMem hz, zero_mul, abs_zero]
    positivity

theorem measurable_cubeCutoff_mul_quadraticObservable (d : ℕ) (m : ℤ) (i : Fin d) :
    Measurable fun z => cubeCutoff d m z * quadraticObservable (basisVec i) z :=
  ((continuous_cubeCutoff d m).mul (continuous_quadraticObservable (basisVec i))).measurable

theorem measurable_cubeCutoff_mul_affineObservable (d : ℕ) (m : ℤ) (i : Fin d) :
    Measurable fun z => cubeCutoff d m z * affineObservable (basisVec i) z :=
  ((continuous_cubeCutoff d m).mul (continuous_affineObservable (basisVec i))).measurable

/-! ## 3. The basis directions -/

theorem norm_basisVec_le_one (i : Fin d) : ‖(basisVec i : Vec d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  rw [basisVec_apply, Real.norm_eq_abs]
  split_ifs <;> simp

theorem vecCoordSum_basisVec (i : Fin d) : vecCoordSum (basisVec i : Vec d) = 1 := by
  simp only [vecCoordSum, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem vecDot_basisVec_self (i : Fin d) : vecDot (basisVec i : Vec d) (basisVec i) = 1 := by
  rw [vecDot_basisVec_left, basisVec_apply, ite_eq_left rfl]

theorem affineObservable_zero (e : Vec d) : affineObservable e 0 = 0 := by
  simp [affineObservable, vecDot]

theorem quadraticObservable_zero (e : Vec d) : quadraticObservable e 0 = 0 := by
  simp [quadraticObservable, vecDot]

/-! ## 4. The process quantities -/

section Model

variable [NeZero d]

/-- **The exit probability**: the probability that the stream process started at the origin has
left the cube of scale `m` centred at the origin by the time `t`. -/
def cubeExitProbability (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ) (t : NNReal) :
    ℝ :=
  letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  ((streamExhaustionTailInput M omega).wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))
    (survivalEvent (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t)ᶜ).toReal

theorem cubeExitProbability_nonneg (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ)
    (t : NNReal) : 0 ≤ cubeExitProbability M omega m t :=
  ENNReal.toReal_nonneg

/-- **The stopped mean vector**: its `i`-th coordinate is the mean, under the stream process
started at the origin, of the cut-off linear observable in the direction `i` at the position of
the path at its exit time from the cube of scale `m` centred at the origin, truncated at `t`. -/
def cubeStoppedMean (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ) (t : NNReal) :
    Vec d :=
  fun i =>
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∫ path, onePointRealExtension (fun z => cubeCutoff d m z * affineObservable (basisVec i) z)
        (path (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t path))
      ∂((streamExhaustionTailInput M omega).wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d)))

/-! ## 5. The squared stopped mean -/

/-- **The squared norm of the stopped mean vector.**  Each coordinate is the stopped mean of the
cut-off linear observable in that direction, which is within `2 · 3^m EB` of zero by the stopped
mean bound and the corrector estimate at the linear datum; summing the squares over the `d`
directions gives `4 d (3^m)² EB²`. -/
theorem vecNormSq_cubeStoppedMean_le (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ)
    {sigmaBarM EBm : ℝ} (hEB : 0 ≤ EBm)
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
    (t : NNReal) :
    vecNormSq (cubeStoppedMean M omega m t) ≤
      (4 * d) * ((3 : ℝ) ^ m) ^ (2 : ℕ) * EBm ^ (2 : ℕ) := by
  let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ m := zpow_nonneg (by norm_num) m
  have hcoord : ∀ i : Fin d, cubeStoppedMean M omega m t i * cubeStoppedMean M omega m t i ≤
      4 * (((3 : ℝ) ^ m) ^ (2 : ℕ) * EBm ^ (2 : ℕ)) := by
    intro i
    obtain ⟨u, Y, hu, hN, hoff, hucont, hY, hharm, htrace, hKb⟩ :=
      exists_cutoffAffineObservable_stream M omega m hEB hren (basisVec i)
        (contDiff_cubeCutoff d m) (fun x hx => cubeCutoff_eq_one_of_mem hx)
        (abs_cubeCutoff_mul_affineObservable_le d m i)
    have hbd : ContDiff ℝ (⊤ : ℕ∞) fun z => cubeCutoff d m z * affineObservable (basisVec i) z :=
      (contDiff_cubeCutoff d m).mul (contDiff_affineObservable _ (basisVec i))
    have hbdCompact : HasCompactSupport
        fun z => cubeCutoff d m z * affineObservable (basisVec i) z :=
      (hasCompactSupport_cubeCutoff d m).mul_right
    have hK0 : 0 ≤ (3 : ℝ) ^ m * (EBm * ‖(basisVec i : Vec d)‖) :=
      mul_nonneg h3 (mul_nonneg hEB (norm_nonneg _))
    have hb0 : cubeCutoff d m 0 * affineObservable (basisVec i) 0 = 0 := by
      rw [affineObservable_zero, mul_zero]
    have hsq := sq_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_stream
      (streamWholeSpaceResolvent M omega) (streamExhaustionTailInput M omega).toOnePointRegular
      (isConservative_streamKernelSemigroup M omega)
      (kernelResolventIdentifiesAnalyticMinimal_stream M omega) (fun _ _ => rfl) 0 m hbd
      hbdCompact hu hN hoff hucont Y hY hharm htrace
      (measurable_cubeCutoff_mul_affineObservable d m i) hK0 hKb hb0 t
    have hK : (3 : ℝ) ^ m * (EBm * ‖(basisVec i : Vec d)‖) ≤ (3 : ℝ) ^ m * EBm := by
      calc (3 : ℝ) ^ m * (EBm * ‖(basisVec i : Vec d)‖) ≤ (3 : ℝ) ^ m * (EBm * 1) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (norm_basisVec_le_one i) hEB) h3
        _ = (3 : ℝ) ^ m * EBm := by ring
    have hKsq : ((3 : ℝ) ^ m * (EBm * ‖(basisVec i : Vec d)‖)) ^ (2 : ℕ) ≤
        ((3 : ℝ) ^ m) ^ (2 : ℕ) * EBm ^ (2 : ℕ) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hK0 hK 2
    have hcoordSq : cubeStoppedMean M omega m t i ^ (2 : ℕ) ≤
        4 * ((3 : ℝ) ^ m * (EBm * ‖(basisVec i : Vec d)‖)) ^ (2 : ℕ) := hsq
    rw [← pow_two]
    exact hcoordSq.trans (mul_le_mul_of_nonneg_left hKsq (by norm_num))
  calc vecNormSq (cubeStoppedMean M omega m t)
      = ∑ i : Fin d, cubeStoppedMean M omega m t i * cubeStoppedMean M omega m t i := rfl
    _ ≤ ∑ _i : Fin d, 4 * (((3 : ℝ) ^ m) ^ (2 : ℕ) * EBm ^ (2 : ℕ)) :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = (4 * d) * ((3 : ℝ) ^ m) ^ (2 : ℕ) * EBm ^ (2 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## 6. The stopped second moment -/

/-- **The stopped second moment in every direction.**  The stopped mean of the cut-off quadratic
observable in the direction `i` is within `10 (3^m)² EB` plus `2 sigmaBar t` times the exit
probability of `2 sigmaBar t`, by the stopped second-moment bound with the corrected observable
and the corrector estimate at the quadratic datum. -/
theorem abs_cubeStoppedQuadratic_sub_le (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ)
    {sigmaBarM EBm : ℝ} (hsigma : 0 < sigmaBarM) (hEB : 0 ≤ EBm)
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
    (t : NNReal) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∀ i : Fin d,
      |(∫ path, onePointRealExtension
            (fun z => cubeCutoff d m z * quadraticObservable (basisVec i) z)
            (path (ContinuousPath.exitTimeTrunc
              (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t path))
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d)))) -
          (2 * sigmaBarM) * (t : ℝ)| ≤
        10 * ((3 : ℝ) ^ m) ^ (2 : ℕ) * EBm +
          2 * (sigmaBarM * (t : ℝ)) * cubeExitProbability M omega m t := by
  let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  intro i
  obtain ⟨u, Y, hu, hN, hoff, hucont, hY, hharm, htrace, hKb⟩ :=
    exists_cutoffQuadraticObservable_stream (streamWholeSpaceResolvent M omega)
      (streamExhaustionTailInput M omega).toOnePointRegular
      (isConservative_streamKernelSemigroup M omega)
      (kernelResolventIdentifiesAnalyticMinimal_stream M omega) (fun _ _ => rfl) m hsigma hEB hren
      (basisVec i) (contDiff_cubeCutoff d m) (fun x hx => cubeCutoff_eq_one_of_mem hx)
      (abs_cubeCutoff_mul_quadraticObservable_le d m i)
  have hbd : ContDiff ℝ (⊤ : ℕ∞) fun z => cubeCutoff d m z * quadraticObservable (basisVec i) z :=
    (contDiff_cubeCutoff d m).mul (contDiff_quadraticObservable _ (basisVec i))
  have hbdCompact : HasCompactSupport
      fun z => cubeCutoff d m z * quadraticObservable (basisVec i) z :=
    (hasCompactSupport_cubeCutoff d m).mul_right
  have hsigma' : 0 ≤ 2 * sigmaBarM * vecDot (basisVec i : Vec d) (basisVec i) := by
    rw [vecDot_basisVec_self]
    linarith only [hsigma]
  have hq0 : cubeCutoff d m 0 * quadraticObservable (basisVec i) 0 = 0 := by
    rw [quadraticObservable_zero, mul_zero]
  have hmain := abs_integral_eval_exitTimeTrunc_onePointRealExtension_sub_mul_le_cubeSetAt_stream
    (streamWholeSpaceResolvent M omega) (streamExhaustionTailInput M omega).toOnePointRegular
    (isConservative_streamKernelSemigroup M omega)
    (kernelResolventIdentifiesAnalyticMinimal_stream M omega) (fun _ _ => rfl) 0 m hbd
    hbdCompact hu hN hoff hucont Y hY hharm htrace
    (measurable_cubeCutoff_mul_quadraticObservable d m i)
    (abs_cubeCutoff_mul_quadraticObservable_le d m i) hsigma' hKb hq0 t
  rw [vecDot_basisVec_self, mul_one] at hmain
  have h3 : (0 : ℝ) ≤ ((3 : ℝ) ^ m) ^ (2 : ℕ) := by positivity
  have hK : ((3 : ℝ) ^ m) ^ (2 : ℕ) *
      (5 * EBm * (‖(basisVec i : Vec d)‖ * vecCoordSum (basisVec i : Vec d))) ≤
      ((3 : ℝ) ^ m) ^ (2 : ℕ) * (5 * EBm) := by
    rw [vecCoordSum_basisVec, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ h3
    calc 5 * EBm * ‖(basisVec i : Vec d)‖ ≤ 5 * EBm * 1 :=
          mul_le_mul_of_nonneg_left (norm_basisVec_le_one i) (by linarith only [hEB])
      _ = 5 * EBm := mul_one _
  refine hmain.trans ?_
  have hP : (0 : ℝ) ≤ cubeExitProbability M omega m t := cubeExitProbability_nonneg M omega m t
  calc 2 * (((3 : ℝ) ^ m) ^ (2 : ℕ) *
        (5 * EBm * (‖(basisVec i : Vec d)‖ * vecCoordSum (basisVec i : Vec d)))) +
        2 * sigmaBarM * ((t : ℝ) * cubeExitProbability M omega m t)
      ≤ 2 * (((3 : ℝ) ^ m) ^ (2 : ℕ) * (5 * EBm)) +
        2 * sigmaBarM * ((t : ℝ) * cubeExitProbability M omega m t) :=
        add_le_add (mul_le_mul_of_nonneg_left hK (by norm_num)) le_rfl
    _ = 10 * ((3 : ℝ) ^ m) ^ (2 : ℕ) * EBm +
        2 * (sigmaBarM * (t : ℝ)) * cubeExitProbability M omega m t := by ring

end Model

/-! ## 7. The side condition of the composition -/

/-- **The confinement scale dominates the diffusive scale.**  At a confinement scale `m` for the
length `K |log γ|^{1/2} R(t)`, with `K² ≥ 2 d`, the running diffusivity satisfies
`d sigmaBar t ≤ (3^m)²`, once the disorder parameter is small enough that
`d (1 + 2 C) γ^{1/2} |log γ| ≤ 1/2`. -/
theorem dim_mul_sigmaBar_mul_le_three_zpow_sq_of_isConfinementScale {nu cstar gamma t K : ℝ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4)
    (ht : 0 < t) (hK : 1 ≤ K) (hKd : 2 * (d : ℝ) ≤ K ^ (2 : ℕ)) {Stilde : ℤ → ℝ≥0∞} {m : ℤ}
    (hm : IsConfinementScale Stilde
      (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) m)
    {sigmaBar C : ℝ} (hsigma : 0 < sigmaBar) (hC : 0 ≤ C)
    (hsmall : C * Real.sqrt gamma * |Real.log gamma| ≤ 1 / 2)
    (hsmall' : (d : ℝ) * (1 + 2 * C) * Real.sqrt gamma * |Real.log gamma| ≤ 1 / 2)
    (hprofile : |sigmaBar - effectiveDiffusivity nu cstar gamma ((3 : ℝ) ^ m)| ≤
      C * Real.sqrt gamma * |Real.log gamma| * sigmaBar) :
    (d : ℝ) * (sigmaBar * t) ≤ ((3 : ℝ) ^ m) ^ (2 : ℕ) := by
  have hR := intrinsicScale_pos hnu hcstar hgamma ht
  have hlog := one_le_abs_log hgamma hgamma4
  have hsqrt : 0 ≤ Real.sqrt |Real.log gamma| := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hbound := abs_intrinsicScale_sq_sub_mul_le_of_isConfinementScale hnu hcstar hgamma hgamma4
    ht hK hm hsigma hC hsmall hprofile
  have hRle : K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t ≤ (3 : ℝ) ^ m :=
    le_three_zpow_of_isConfinementScale' le_rfl hm
  have hLnn : 0 ≤ K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t := by
    positivity
  have hsq : (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) ^ (2 : ℕ) ≤
      ((3 : ℝ) ^ m) ^ (2 : ℕ) := pow_le_pow_left₀ hLnn hRle 2
  have hexpand : (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) ^ (2 : ℕ) =
      K ^ (2 : ℕ) * |Real.log gamma| * intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by
    have := Real.sq_sqrt (abs_nonneg (Real.log gamma))
    calc (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) ^ (2 : ℕ)
        = K ^ (2 : ℕ) * (Real.sqrt |Real.log gamma|) ^ (2 : ℕ) *
            intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by ring
      _ = K ^ (2 : ℕ) * |Real.log gamma| * intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by
            rw [this]
  rw [hexpand] at hsq
  -- `2 d R² ≤ K² |log γ| R² ≤ (3^m)²`
  have hRsq : 0 ≤ intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by positivity
  have hcoef : 2 * (d : ℝ) ≤ K ^ (2 : ℕ) * |Real.log gamma| := by
    calc 2 * (d : ℝ) ≤ K ^ (2 : ℕ) := hKd
      _ = K ^ (2 : ℕ) * 1 := (mul_one _).symm
      _ ≤ K ^ (2 : ℕ) * |Real.log gamma| :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  have hdR : 2 * (d : ℝ) * intrinsicScale nu cstar gamma t ^ (2 : ℕ) ≤ ((3 : ℝ) ^ m) ^ (2 : ℕ) :=
    (mul_le_mul_of_nonneg_right hcoef hRsq).trans hsq
  -- `sigmaBar t ≤ R² + (1 + 2C) γ^{1/2} |log γ| (3^m)²`
  have hst : sigmaBar * t ≤ intrinsicScale nu cstar gamma t ^ (2 : ℕ) +
      (1 + 2 * C) * Real.sqrt gamma * |Real.log gamma| * ((3 : ℝ) ^ m) ^ (2 : ℕ) := by
    have := (abs_le.1 hbound).1
    linarith only [this]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h3 : (0 : ℝ) ≤ ((3 : ℝ) ^ m) ^ (2 : ℕ) := by positivity
  calc (d : ℝ) * (sigmaBar * t)
      ≤ (d : ℝ) * (intrinsicScale nu cstar gamma t ^ (2 : ℕ) +
          (1 + 2 * C) * Real.sqrt gamma * |Real.log gamma| * ((3 : ℝ) ^ m) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hst hd0
    _ = (1 / 2 : ℝ) * (2 * (d : ℝ) * intrinsicScale nu cstar gamma t ^ (2 : ℕ)) +
          ((d : ℝ) * (1 + 2 * C) * Real.sqrt gamma * |Real.log gamma|) *
            ((3 : ℝ) ^ m) ^ (2 : ℕ) := by ring
    _ ≤ (1 / 2 : ℝ) * ((3 : ℝ) ^ m) ^ (2 : ℕ) + (1 / 2 : ℝ) * ((3 : ℝ) ^ m) ^ (2 : ℕ) :=
        add_le_add (mul_le_mul_of_nonneg_left hdR (by norm_num))
          (mul_le_mul_of_nonneg_right hsmall' h3)
    _ = ((3 : ℝ) ^ m) ^ (2 : ℕ) := by ring

/-! ## 8. The corrector clause on the full-sample carrier -/

/-- **The corrector clause holds almost surely on the full-sample carrier, at every scale.**
The clause of the renormalization families is almost sure on the cutoff-sample carrier at each
scale; countability of the scales and the identification of the full-sample law with the
cutoff-sample law transport it. -/
theorem ae_renormalizationCorrector_fullSample (M : ABKModel d) {sigmaBar : ℤ → ℝ}
    {EB : ℤ → Cutoff.CutoffSample d → ℝ}
    (hdir : ∀ m : ℤ, ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : ℤ, m ≤ L →
        ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
          (Kg Kh KhInf : ℝ),
          IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
            (originCube d m) u h g →
          IsDirichletSolutionOn (fun _ : Vec d => sigmaBar m • (1 : Mat d))
            (originCube d m) v h g →
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
          (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
          HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
          ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
            Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
              EB m omega * ((sigmaBar m)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh))) :
    ∀ᵐ omega ∂(fullSampleLaw M).toMeasure, ∀ m : ℤ,
      ∀ L : ℤ, m ≤ L →
        ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
          (Kg Kh KhInf : ℝ),
          IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField
            (originCube d m) u h g →
          IsDirichletSolutionOn (fun _ : Vec d => sigmaBar m • (1 : Mat d))
            (originCube d m) v h g →
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
          (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
          HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
          ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
            Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
              EB m omega.1 * ((sigmaBar m)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) := by
  have hall := ae_all_iff.2 hdir
  rw [← map_fullSampleLaw_val M] at hall
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hall

end

end Algsuperdiff.Section5.Provider
