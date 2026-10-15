/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.OriginConcentration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementDerivativeBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# IncrementLinfty

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The small-cube `L∞` stream bound: ABK26's `e.k.ell.upscales.infty`

ABK26 upgrades the value estimate at the origin to a uniform estimate
on the whole cube `cu_n`:

`‖k_m - k_n‖_{L∞(cu_n)} ≤ √d 3^n ‖∇(k_m - k_n)‖_{L∞(cu_n)} + |(k_m - k_n)(0)|
   ≤ O_{Γ₂}(C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`,

which is the source's `e.km.kn.Linfty.smallcube` before squaring.

As in `Algsuperdiff.Section3.Provider.Stream.IncrementDerivativeBounds`, the
statement is split into a deterministic part and a probabilistic part, because
the finite increment `k_m - k_n = ∑_{k ∈ (n,m]} j_k` is not itself a shell and
so carries no `localCubeControl` gauge.

* `matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound` is the
  deterministic mean-value bridge: at *every* point of `cu_n` the increment is
  dominated by the single random variable `incrementSupBound n m`, built from
  the value at the origin and the summed first-derivative gauges.
* `isBigOWith_gammaSigma_incrementSupBound` is the probabilistic estimate for
  that random variable, at the source amplitude.

Composing the two gives the source display for every realization.

Deviations from the source, all absorbed by its `C(d)`:

* the mean value theorem is applied to each of the `d²` matrix entries along
  the segment from `0` to `x`, and the entries are recombined through
  `matrixOperatorNorm ≤ matrixOperatorNorm(centre) + ∑_{i,l} |·|`; this costs a
  factor `d²` relative to the source's direct matrix-norm argument;
* the geometric factor is `√d · 3^n / 2` rather than the source's `√d · 3^n`,
  because `cu_n` has half-side `3^n/2`; this is a strengthening.

## Main definitions

* `Algsuperdiff.Section3.Provider.Stream.incrementSupBound`

## Main results

*
`Algsuperdiff.Section3.Provider.Stream.matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_incrementSupBound`

## References

* ABK26, `e.k.ell.upscales.infty`.
* ABK26, `e.km.kn.Linfty.smallcube`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Scaling of the exact Euclidean norms -/

/-- The exact Euclidean matrix operator norm is absolutely homogeneous. -/
theorem matrixOperatorNorm_smul_real (c : ℝ) (A : Mat d) :
    matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A := by
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • A)‖ =
    |c| * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- The exact Euclidean vector norm is absolutely homogeneous. -/
theorem vecNorm_smul_real (c : ℝ) (x : Vec d) :
    vecNorm (c • x) = |c| * vecNorm x := by
  have hsq : vecNorm (c • x) ^ 2 = (|c| * vecNorm x) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, vecNormSq_smul, mul_pow, sq_abs,
      vecNorm_sq_eq_vecNormSq]
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (vecNorm_nonneg _),
    Real.sqrt_sq (mul_nonneg (abs_nonneg c) (vecNorm_nonneg x))] at h

/-- The exact induced first-derivative norm controls the matrix values at
every input, with the Euclidean vector norm of the input as the factor. -/
theorem matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm
    (D : ShellField.MatrixDerivative d) (v : Vec d) :
    matrixOperatorNorm (D v) ≤ ShellField.matrixDerivativeNorm D * vecNorm v := by
  rcases eq_or_lt_of_le (vecNorm_nonneg v) with h0 | hpos
  · have hzero : v = 0 := by
      refine vecNormSq_eq_zero ?_
      rw [← vecNorm_sq_eq_vecNormSq, ← h0]
      norm_num
    rw [hzero, map_zero, matrixOperatorNorm_zero]
    exact mul_nonneg (ShellField.matrixDerivativeNorm_nonneg D) (vecNorm_nonneg _)
  · have hw : vecNorm ((vecNorm v)⁻¹ • v) ≤ 1 := by
      rw [vecNorm_smul_real, abs_of_nonneg (inv_nonneg.2 hpos.le),
        inv_mul_cancel₀ hpos.ne']
    have hDv : D v = (vecNorm v) • D ((vecNorm v)⁻¹ • v) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rw [hDv, matrixOperatorNorm_smul_real, abs_of_nonneg hpos.le, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm _ _ hw) hpos.le

/-! ## Geometry of the origin cube -/

/-- The origin cube is star-shaped about the origin. -/
theorem smul_mem_openCubeSet_originCube {n : ℤ} {x : Vec d} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ openCubeSet (originCube d n)) :
    t • x ∈ openCubeSet (originCube d n) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h := hx i
  have habs : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    rw [abs_lt]
    exact ⟨by linarith [h.1], h.2⟩
  have habst : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hmul : |t * x i| ≤ |x i| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (x i), abs_nonneg t]
  have hlt : |t * x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := lt_of_le_of_lt hmul habs
  rw [abs_lt] at hlt
  have happ : (t • x) i = t * x i := rfl
  rw [happ]
  exact ⟨by linarith [hlt.1], hlt.2⟩

/-- Points of the origin cube of scale `n` have Euclidean norm at most
`√d 3^n / 2`. -/
theorem vecNorm_le_of_mem_openCubeSet_originCube {n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d n)) :
    vecNorm x ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) := by
  have hb := mem_openCubeSet_originCube_iff.mp hx
  have hsq : vecNormSq x ≤ (d : ℝ) * ((3 : ℝ) ^ n / 2) ^ 2 := by
    have hstep : ∀ i : Fin d, x i * x i ≤ ((3 : ℝ) ^ n / 2) ^ 2 := by
      intro i
      nlinarith [(hb i).1, (hb i).2]
    calc vecNormSq x = ∑ i, x i * x i := rfl
      _ ≤ ∑ _i : Fin d, ((3 : ℝ) ^ n / 2) ^ 2 :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = (d : ℝ) * ((3 : ℝ) ^ n / 2) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hB : (0 : ℝ) ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) := by
    have : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
    positivity
  have hsq' : vecNorm x ^ 2 ≤ (Real.sqrt d * ((3 : ℝ) ^ n / 2)) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    exact hsq
  have h := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq (vecNorm_nonneg x), Real.sqrt_sq hB] at h

/-! ## The mean-value bridge -/

/-- The finite stream increment evaluates to the finite sum of shell values. -/
theorem finiteShellIncrement_eq_sum (omega : ShellSeq d) (n m : ℤ) (x : Vec d) :
    finiteShellIncrement omega n m x = ∑ k ∈ Finset.Ioc n m, (omega k) x := by
  rw [finiteShellIncrement_apply]
  rfl

/-- The mean value theorem along the segment from the origin, applied to a
single matrix entry of the finite stream increment. -/
theorem abs_entry_sum_sub_origin_le (omega : ShellSeq d) (n m : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d n)) (i l : Fin d) :
    |(∑ k ∈ Finset.Ioc n m, (omega k) x) i l -
        (∑ k ∈ Finset.Ioc n m, (omega k) 0) i l| ≤
      (∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)) * vecNorm x := by
  set f : ℝ → ℝ := fun t =>
    (matrixEntryCLM i l) (∑ k ∈ Finset.Ioc n m, (omega k) (t • x)) with hf
  set f' : ℝ → ℝ := fun t =>
    (matrixEntryCLM i l)
      ((∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) (t • x)) x) with hf'
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' t) (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have hpath : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have hS : HasFDerivAt (fun y : Vec d => ∑ k ∈ Finset.Ioc n m, (omega k) y)
        (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) (t • x)) (t • x) :=
      HasFDerivAt.fun_sum fun k _ => (omega k).hasFDerivAt (t • x)
    exact (((matrixEntryCLM i l).hasFDerivAt).comp_hasDerivAt t
      (hS.comp_hasDerivAt t hpath)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖f' t‖ ≤ (∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)) * vecNorm x := by
    intro t ht
    have htx : t • x ∈ openCubeSet (originCube d n) :=
      smul_mem_openCubeSet_originCube ⟨ht.1, le_of_lt ht.2⟩ hx
    calc ‖f' t‖
        = |(∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) (t • x)) x i l| := rfl
      _ ≤ matrixOperatorNorm
            ((∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) (t • x)) x) :=
          abs_entry_le_matrixOperatorNorm _ _ _
      _ ≤ ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) (t • x)) * vecNorm x :=
          matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm _ _
      _ ≤ (∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)) * vecNorm x :=
          mul_le_mul_of_nonneg_right
            (matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm n
              (Finset.Ioc n m) omega htx) (vecNorm_nonneg x)
  have hkey := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩)
  have hf1 : f 1 = (∑ k ∈ Finset.Ioc n m, (omega k) x) i l := by
    simp only [hf, one_smul]
    rfl
  have hf0 : f 0 = (∑ k ∈ Finset.Ioc n m, (omega k) 0) i l := by
    simp only [hf, zero_smul]
    rfl
  rw [hf1, hf0] at hkey
  simpa only [Real.norm_eq_abs, sub_zero, mul_one] using hkey

/-- The single random variable dominating `‖k_m - k_n‖_{L∞(cu_n)}`: the value
at the origin plus the geometric factor times the summed first-derivative
gauges. -/
def incrementSupBound (n m : ℤ) (omega : ShellSeq d) : ℝ :=
  matrixOperatorNorm (finiteShellIncrement omega n m 0) +
    (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
      ∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)

/-- The deterministic half of ABK26's `e.k.ell.upscales.infty`: at every point
of `cu_n` the finite stream increment is dominated by `incrementSupBound`. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound
    (omega : ShellSeq d) (n m : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d n)) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      incrementSupBound n m omega := by
  have hG : 0 ≤ ∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k) :=
    Finset.sum_nonneg fun k _ => localCubeDerivNorm_nonneg n (omega k)
  have hvec := vecNorm_le_of_mem_openCubeSet_originCube (d := d) (n := n) hx
  have hentries : ∑ i : Fin d, ∑ l : Fin d,
      |finiteShellIncrement omega n m x i l -
        finiteShellIncrement omega n m 0 i l| ≤
      (d : ℝ) ^ 2 * ((∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)) *
        (Real.sqrt d * ((3 : ℝ) ^ n / 2))) := by
    have hstep : ∀ i : Fin d, ∀ l : Fin d,
        |finiteShellIncrement omega n m x i l -
          finiteShellIncrement omega n m 0 i l| ≤
        (∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)) *
          (Real.sqrt d * ((3 : ℝ) ^ n / 2)) := by
      intro i l
      rw [finiteShellIncrement_eq_sum, finiteShellIncrement_eq_sum]
      refine (abs_entry_sum_sub_origin_le omega n m hx i l).trans ?_
      exact mul_le_mul_of_nonneg_left hvec hG
    calc ∑ i : Fin d, ∑ l : Fin d,
          |finiteShellIncrement omega n m x i l -
            finiteShellIncrement omega n m 0 i l|
        ≤ ∑ _i : Fin d, ∑ _l : Fin d,
            (∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)) *
              (Real.sqrt d * ((3 : ℝ) ^ n / 2)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hstep i l
      _ = (d : ℝ) ^ 2 * ((∑ k ∈ Finset.Ioc n m, localCubeDerivNorm n (omega k)) *
            (Real.sqrt d * ((3 : ℝ) ^ n / 2))) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
          ring
  refine (matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
    (finiteShellIncrement omega n m x) (finiteShellIncrement omega n m 0)).trans ?_
  rw [incrementSupBound]
  refine add_le_add (le_refl _) (hentries.trans (le_of_eq ?_))
  ring

/-! ## The probabilistic estimate -/

/-- The explicit dimensional constant of ABK26's `e.k.ell.upscales.infty`. -/
def streamLinftyConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
    (geometricConcentrationConst + Real.sqrt d / 2)

theorem streamLinftyConst_pos (hd : 0 < d) : 0 < streamLinftyConst d := by
  have hC : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hgeo : (0 : ℝ) < geometricConcentrationConst := geometricConcentrationConst_pos
  have hsqrt : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  rw [streamLinftyConst]
  have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 := by
    positivity
  exact mul_pos h1 (by linarith)

/-- The summed first-derivative gauge estimate, with the second-derivative term
discarded. -/
theorem isBigOWith_gammaSigma_shellDerivNormSum_Ioc (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
        localCubeDerivNorm n (omega k))
      (IndependentSums.gammaTriangleConst 2 *
        (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))) := by
  refine (isBigOWith_gammaSigma_shellDerivGaugeSum_Ioc M hnm).of_le fun omega => ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have h2 : 0 ≤ (3 : ℝ) ^ n * localCubeSecondDerivNorm n (omega k) :=
    mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) n).le
      (localCubeSecondDerivNorm_nonneg n (omega k))
  linarith

/-- Reassembling the geometric factor: `3^n · 3^{(γ-1)n} = 3^{γn}`. -/
theorem zpow_mul_rpow_gamma_sub_one (gamma : ℝ) (n : ℤ) :
    (3 : ℝ) ^ n * (3 : ℝ) ^ ((gamma - 1) * (n : ℝ)) =
      (3 : ℝ) ^ (gamma * (n : ℝ)) := by
  rw [← Real.rpow_intCast (3 : ℝ) n, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- Two-term generalized triangle inequality for `Γ_σ` tails. -/
theorem isBigO_gammaSigma_add_of_isBigO {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} [MeasureTheory.IsFiniteMeasure mu]
    {X Y : Omega → ℝ} {A B sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hB : 0 < B)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X A)
    (hY : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) Y B)
    (hXm : Measurable X) (hYm : Measurable Y) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => X omega + Y omega)
      (IndependentSums.gammaTriangleConst sigma * (A + B)) := by
  classical
  have hsum : ∑ i ∈ Finset.range 2, (fun i : ℕ => if i = 0 then A else B) i = A + B := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have h := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma (μ := mu)
    (Finset.range 2) (X := fun i : ℕ => if i = 0 then X else Y)
    (a := fun i : ℕ => if i = 0 then A else B) (σ := sigma) hsigma
    (Finset.nonempty_range_iff.2 (by norm_num))
    (fun i _ => by split_ifs <;> assumption)
    (fun i _ => by split_ifs <;> assumption)
    (fun i _ => by split_ifs <;> assumption)
  rw [hsum] at h
  have hfun : (fun omega => ∑ i ∈ Finset.range 2,
      (fun i : ℕ => if i = 0 then X else Y) i omega) =
      fun omega => X omega + Y omega := by
    funext omega
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rwa [hfun] at h

/-- The value of the finite stream increment at the origin is a measurable
random variable. -/
theorem measurable_matrixOperatorNorm_finiteShellIncrement_origin (n m : ℤ) :
    Measurable (fun omega : ShellSeq d =>
      matrixOperatorNorm (finiteShellIncrement omega n m 0)) := by
  have hvec : Measurable (fun omega : ShellSeq d =>
      finiteShellIncrement omega n m 0) := by
    have hMAdd : MeasurableAdd₂ (Mat d) := by
      change MeasurableAdd₂ (Fin d → Fin d → ℝ)
      infer_instance
    have hrw : (fun omega : ShellSeq d => finiteShellIncrement omega n m 0) =
        fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m, (omega k) 0 := by
      funext omega
      exact finiteShellIncrement_eq_sum omega n m 0
    rw [hrw]
    exact Finset.measurable_sum (Finset.Ioc n m) fun k _ =>
      (ShellField.measurable_eval (0 : Vec d)).comp (measurable_pi_apply k)
  exact (ShellField.continuous_matrixOperatorNorm).measurable.comp hvec

/-- The lower-scale amplitude `3^{γn}` is dominated by the source amplitude. -/
theorem rpow_gamma_mul_le_min_mul (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    (3 : ℝ) ^ (M.gamma * (n : ℝ)) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
  have hgamma := M.shellPrefix.gamma_pos
  have hquarter := M.shellPrefix.gamma_le_quarter
  have hnm_real : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
  have hginv : 0 < M.gamma⁻¹ := inv_pos.2 hgamma
  have hgi : M.gamma⁻¹ * M.gamma = 1 := inv_mul_cancel₀ hgamma.ne'
  have h4 : (4 : ℝ) ≤ M.gamma⁻¹ := by nlinarith [hgi, hginv, hgamma, hquarter]
  have hone_le_min : (1 : ℝ) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) := by
    refine le_min ?_ ?_
    · calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt M.gamma⁻¹ := Real.sqrt_le_sqrt (by linarith)
    · calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt ((m : ℝ) - (n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
  have hmono : (3 : ℝ) ^ (M.gamma * (n : ℝ)) ≤ (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by linarith) hgamma.le)
  have hKm : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [hmono, hone_le_min, hKm]

/-- Combine measurable value and derivative envelopes at the stream scale. -/
theorem isBigOWith_gammaSigma_streamEnvelope (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) {X D : ShellSeq d → ℝ}
    (hX0 : ∀ omega, 0 ≤ X omega) (hD0 : ∀ omega, 0 ≤ D omega)
    (hXm : Measurable X) (hDm : Measurable D)
    (hX : IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2) X
      (IndependentSums.gammaTriangleConst 2 * ((d : ℝ) ^ 2 *
        (geometricConcentrationConst *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))))))
    (hD : IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2) D
      (IndependentSums.gammaTriangleConst 2 * (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ)))) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega => X omega + (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) * D omega)
      (streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hCT : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hKm : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hmn_real : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hmin_pos : 0 < min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) :=
    lt_min (Real.sqrt_pos.2 (inv_pos.2 M.shellPrefix.gamma_pos))
      (Real.sqrt_pos.2 (by linarith))
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hr : (0 : ℝ) < (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgeo : (0 : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) := by positivity
  have hA : (0 : ℝ) < geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    mul_pos (mul_pos geometricConcentrationConst_pos hmin_pos) hKm
  have ha0 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 *
      ((d : ℝ) ^ 2 * (geometricConcentrationConst *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)))) :=
    mul_pos hCT (mul_pos (by positivity) hA)
  have ha1 : (0 : ℝ) < (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
      (IndependentSums.gammaTriangleConst 2 *
        (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))) := by positivity
  have hY0 := (Orlicz.isBigOWith_iff_isBigO_of_nonneg hX0).1 hX
  have hY1 := (Orlicz.isBigOWith_iff_isBigO_of_nonneg
    (fun omega => mul_nonneg hgeo (hD0 omega))).1 (hD.const_mul hgeo)
  have hcomb := isBigO_gammaSigma_add_of_isBigO (by norm_num : (0 : ℝ) < 2)
    ha0 ha1 hY0 hY1 hXm (hDm.const_mul _)
  refine (Orlicz.isBigOWith_iff_isBigO_of_nonneg
    (fun omega => add_nonneg (hX0 omega) (mul_nonneg hgeo (hD0 omega)))).2
    (hcomb.mono_scale ?_)
  have hpow := zpow_mul_rpow_gamma_sub_one M.gamma n
  have hbound := rpow_gamma_mul_le_min_mul M hnm
  have hc : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 ^ 2 *
      ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) := by positivity
  rw [streamLinftyConst]
  calc IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          ((d : ℝ) ^ 2 * (geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)))) +
          (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
            (IndependentSums.gammaTriangleConst 2 *
              (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))))
      = IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) +
          IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) *
            ((3 : ℝ) ^ n * (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))) := by ring
    _ = IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) +
          IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) *
            (3 : ℝ) ^ (M.gamma * (n : ℝ)) := by rw [hpow]
    _ ≤ IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) +
          IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) *
            (min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
              (3 : ℝ) ^ (M.gamma * (m : ℝ))) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hbound hc)
    _ = IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
          (geometricConcentrationConst + Real.sqrt d / 2) *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by ring

/-- The probabilistic half of ABK26's `e.k.ell.upscales.infty`:

`incrementSupBound ≤ O_{Γ₂}(C(d) min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`.

Combined with `matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound`,
this is the source's `‖k_m - k_n‖_{L∞(cu_n)} ≤ O_{Γ₂}(C min{γ^{-1/2},
(m-n)^{1/2}} 3^{γm})`, that is, `e.km.kn.Linfty.smallcube` before squaring. -/
theorem isBigOWith_gammaSigma_incrementSupBound (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (incrementSupBound n m)
      (streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
  exact isBigOWith_gammaSigma_streamEnvelope M hnm
    (fun omega => matrixOperatorNorm_nonneg (finiteShellIncrement omega n m 0))
    (fun omega => Finset.sum_nonneg fun k _ => localCubeDerivNorm_nonneg n (omega k))
    (measurable_matrixOperatorNorm_finiteShellIncrement_origin n m)
    (Finset.measurable_sum (Finset.Ioc n m) fun k _ =>
      (measurable_localCubeDerivNorm n).comp (measurable_pi_apply k))
    (isBigOWith_gammaSigma_originIncrement M hnm)
    (isBigOWith_gammaSigma_shellDerivNormSum_Ioc M hnm)

/-- ABK26's `e.km.kn.Linfty.smallcube`:

`‖k_m - k_n‖²_{L∞(cu_n)} ≤ O_{Γ₁}(C min{γ^{-1}, m-n} 3^{2γm})`.

This is the square of `isBigOWith_gammaSigma_incrementSupBound`, obtained from
the proved power rule `e.powerofGammasigma` at `p = 2`, which moves the tail
exponent from `σ = 2` to `σ = 1`. -/
theorem isBigOWith_gammaSigma_one_incrementSupBound_sq (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => incrementSupBound n m omega ^ 2)
      (streamLinftyConst d ^ 2 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hginv : 0 < M.gamma⁻¹ := inv_pos.2 M.shellPrefix.gamma_pos
  have hmn_real : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hmin_nonneg : (0 : ℝ) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hKm : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hK : (0 : ℝ) ≤ streamLinftyConst d *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    mul_nonneg (mul_nonneg (streamLinftyConst_pos hd).le hmin_nonneg) hKm.le
  have hnonneg : ∀ omega : ShellSeq d, 0 ≤ incrementSupBound n m omega := by
    intro omega
    have hgeo : (0 : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) := by
      have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
      positivity
    refine add_nonneg (matrixOperatorNorm_nonneg _) ?_
    exact mul_nonneg hgeo
      (Finset.sum_nonneg fun k _ => localCubeDerivNorm_nonneg n (omega k))
  have h := (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg (μ := M.P.toMeasure)
    (X := incrementSupBound n m) (σ := 2) hK hnonneg).1
      (isBigOWith_gammaSigma_incrementSupBound M hnm)
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
  refine h.mono_scale (le_of_eq ?_)
  have hs : (min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ)))) ^ 2 =
      min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) := by
    rcases le_total M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) with hle | hle
    · rw [min_eq_left (Real.sqrt_le_sqrt hle), min_eq_left hle,
        Real.sq_sqrt hginv.le]
    · rw [min_eq_right (Real.sqrt_le_sqrt hle), min_eq_right hle,
        Real.sq_sqrt (by linarith)]
  have hK2 : ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (m : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  calc (streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2
      = streamLinftyConst d ^ 2 *
          (min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ)))) ^ 2 *
          ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 := by ring
    _ = streamLinftyConst d ^ 2 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by rw [hs, hK2]

end

end Algsuperdiff.Section3.Provider.Stream
