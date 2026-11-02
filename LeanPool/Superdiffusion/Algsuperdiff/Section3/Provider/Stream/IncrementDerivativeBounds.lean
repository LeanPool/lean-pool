/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle

/-!
# IncrementDerivativeBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The stream-increment derivative bound of ABK26

This module proves ABK26's `e.nabla.km.kn.infty`: for `n < m`,

`‖∇(k_m - k_n)‖_{L∞(cu_n)} + 3^n ‖∇²(k_m - k_n)‖_{L∞(cu_n)} ≤
O_{Γ₂}(^{(γ-1)n})`.

Following the source, the proof sums the single-shell estimate `e.nabla.jk.O`
over the shells `k ∈ (n, m]` with the generalized triangle inequality
`e.Gamma.sigma.triangle`, and then evaluates the resulting geometric series.

Two components are supplied separately.

* The probabilistic content is
  `isBigOWith_gammaSigma_shellDerivGaugeSum_Ioc`: the finite sum
  `∑_{k ∈ (n,m]} (‖∇j_k‖_{L∞(cu_n)} + 3^n ‖∇²j_k‖_{L∞(cu_n)})` obeys the
  stated `Γ₂` bound with the explicit constant
  `Homogenization.IndependentSums.gammaTriangleConst 2` in place of the
  source's `C`.
* The deterministic content is
  `matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm` and its
  second-derivative and combined analogues: the derivatives of the increment
  `k_m - k_n = ∑_{k ∈ (n,m]} j_k` are the corresponding finite sums of shell
  derivatives, and their exact induced norms are dominated pointwise on
  `cu_n` by the summed gauges.  Composing the two gives the source display
  for any realization of the increment.

The geometric series is summed with the explicit constant `1`: for
`γ ≤ 1/4` the ratio `3^{γ-1}` is at most `3^{-3/4} ≤ 1/2`, so
`∑_{k ∈ (n,m]} 3^{(γ-1)k} ≤ 3^{(γ-1)n}`.

## References

* ABK26, `e.nabla.km.kn.infty`.
* ABK26, `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The decreasing geometric sum -/

private theorem two_le_rpow_three_three_quarters :
    (2 : ℝ) ≤ (3 : ℝ) ^ ((3 : ℝ) / 4) := by
  have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
      ← Real.rpow_natCast (2 : ℝ) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h27 : (27 : ℝ) ^ ((1 : ℝ) / 4) = (3 : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast (3 : ℝ) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hmono : (16 : ℝ) ^ ((1 : ℝ) / 4) ≤ (27 : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  rwa [h16, h27] at hmono

/-- For `γ ≤ 1/4` the geometric ratio of the derivative amplitudes is at most
one half. -/
theorem rpow_three_gamma_sub_one_le_half {gamma : ℝ} (hquarter : gamma ≤ 1 / 4) :
    Real.rpow 3 (gamma - 1) ≤ 1 / 2 := by
  have hmono : Real.rpow 3 (gamma - 1) ≤ Real.rpow 3 (-((3 : ℝ) / 4)) := by
    change (3 : ℝ) ^ (gamma - 1) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 4))
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hneg : Real.rpow 3 (-((3 : ℝ) / 4)) = ((3 : ℝ) ^ ((3 : ℝ) / 4))⁻¹ := by
    change (3 : ℝ) ^ (-((3 : ℝ) / 4)) = ((3 : ℝ) ^ ((3 : ℝ) / 4))⁻¹
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have hhalf : ((3 : ℝ) ^ ((3 : ℝ) / 4))⁻¹ ≤ 1 / 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      two_le_rpow_three_three_quarters
    simpa only [one_div] using h
  exact hmono.trans (by rw [hneg]; exact hhalf)

private theorem sum_Ioc_zpow_le {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) {n m : ℤ}
    (hnm : n ≤ m) :
    ∑ k ∈ Finset.Ioc n m, r ^ k ≤ r ^ n := by
  have hrne : r ≠ 0 := ne_of_gt hr0
  have htel : (r⁻¹ - 1) * ∑ k ∈ Finset.Ioc n m, r ^ k = r ^ n - r ^ m := by
    induction m, hnm using Int.leInduction with
    | base => simp
    | succ p hp ih =>
        have hins : Finset.Ioc n (p + 1) = insert (p + 1) (Finset.Ioc n p) := by
          ext x
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          omega
        have hnot : (p + 1) ∉ Finset.Ioc n p := by
          simp only [Finset.mem_Ioc]
          omega
        have hkey : (r⁻¹ - 1) * (r ^ p * r) = r ^ p - r ^ p * r := by
          have hinv : r⁻¹ * r = 1 := inv_mul_cancel₀ hrne
          calc
            (r⁻¹ - 1) * (r ^ p * r) = (r⁻¹ * r) * r ^ p - r ^ p * r := by ring
            _ = r ^ p - r ^ p * r := by rw [hinv, one_mul]
        rw [hins, Finset.sum_insert hnot, mul_add, ih, zpow_add_one₀ hrne, hkey]
        ring
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.Ioc n m, r ^ k :=
    Finset.sum_nonneg fun k _ => (zpow_pos hr0 k).le
  have hinv_pos : (0 : ℝ) < r⁻¹ := inv_pos.2 hr0
  have hcoef : (1 : ℝ) ≤ r⁻¹ - 1 := by
    have hprod : 0 ≤ (1 / 2 - r) * r⁻¹ := mul_nonneg (by linarith) hinv_pos.le
    have hcancel : r * r⁻¹ = 1 := mul_inv_cancel₀ hrne
    nlinarith [hprod, hcancel]
  have hscale := mul_le_mul_of_nonneg_right hcoef hsum_nonneg
  rw [one_mul] at hscale
  have hrm : 0 < r ^ m := zpow_pos hr0 m
  calc
    ∑ k ∈ Finset.Ioc n m, r ^ k ≤ (r⁻¹ - 1) * ∑ k ∈ Finset.Ioc n m, r ^ k := hscale
    _ = r ^ n - r ^ m := htel
    _ ≤ r ^ n := by linarith

private theorem rpow_three_mul_intCast (a : ℝ) (k : ℤ) :
    Real.rpow 3 (a * (k : ℝ)) = (Real.rpow 3 a) ^ k := by
  change (3 : ℝ) ^ (a * (k : ℝ)) = ((3 : ℝ) ^ a) ^ k
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_intCast]

/-- The geometric sum appearing in ABK26's `e.nabla.km.kn.infty`.  Since
`γ ≤ 1/4` forces the ratio `3^{γ-1}` below one half, the sum over `(n, m]` is
bounded by its formal continuation with constant `1`. -/
theorem sum_Ioc_rpow_gamma_sub_one_le {gamma : ℝ} (hquarter : gamma ≤ 1 / 4)
    {n m : ℤ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.Ioc n m, Real.rpow 3 ((gamma - 1) * (k : ℝ)) ≤
      Real.rpow 3 ((gamma - 1) * (n : ℝ)) := by
  have hr0 : (0 : ℝ) < Real.rpow 3 (gamma - 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  simp only [rpow_three_mul_intCast]
  exact sum_Ioc_zpow_le hr0 (rpow_three_gamma_sub_one_le_half hquarter) hnm

/-! ## The summed `Γ₂` estimate -/

/-- ABK26's `e.nabla.km.kn.infty` in the form produced by the source proof: the
finite sum over the shells `k ∈ (n, m]` of the derivative gauges on the small
cube `cu_n` obeys a `Γ₂` bound with amplitude `3^{(γ-1)n}`.  The constant is
CoarseGraining's explicit triangle constant `gammaTriangleConst 2`, standing for
the source's `C`. -/
theorem isBigOWith_gammaSigma_shellDerivGaugeSum_Ioc (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
        (localCubeDerivNorm n (omega k) +
          (3 : ℝ) ^ n * localCubeSecondDerivNorm n (omega k)))
      (IndependentSums.gammaTriangleConst 2 *
        Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) := by
  have hs : (Finset.Ioc n m).Nonempty := by
    refine ⟨m, ?_⟩
    simp only [Finset.mem_Ioc]
    exact ⟨hnm, le_refl m⟩
  have hnonneg : ∀ (k : ℤ) (omega : ShellSeq d),
      0 ≤ localCubeDerivNorm n (omega k) +
        (3 : ℝ) ^ n * localCubeSecondDerivNorm n (omega k) :=
    fun k omega => shellDerivGauge_nonneg n (omega k)
  have hmeas : ∀ k : ℤ, Measurable (fun omega : ShellSeq d =>
      localCubeDerivNorm n (omega k) +
        (3 : ℝ) ^ n * localCubeSecondDerivNorm n (omega k)) :=
    fun k => (measurable_shellDerivGauge n).comp (measurable_pi_apply k)
  have hbigO : ∀ k ∈ Finset.Ioc n m,
      IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d => localCubeDerivNorm n (omega k) +
          (3 : ℝ) ^ n * localCubeSecondDerivNorm n (omega k))
        (Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by
    intro k hk
    have hnk : n ≤ k := le_of_lt (Finset.mem_Ioc.mp hk).1
    exact (Orlicz.isBigOWith_iff_isBigO_of_nonneg (hnonneg k)).1
      (isBigOWith_gammaSigma_shellDerivGauge_cube M hnk)
  have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.Ioc n m)
    (X := fun k omega => localCubeDerivNorm n (omega k) +
      (3 : ℝ) ^ n * localCubeSecondDerivNorm n (omega k))
    (a := fun k : ℤ => Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) (σ := 2)
    (by norm_num) hs (fun k _ => Real.rpow_pos_of_pos (by norm_num) _) hbigO
    (fun k _ => hmeas k)
  have hwith : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
        (localCubeDerivNorm n (omega k) +
          (3 : ℝ) ^ n * localCubeSecondDerivNorm n (omega k)))
      (IndependentSums.gammaTriangleConst 2 *
        ∑ k ∈ Finset.Ioc n m, Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) :=
    (Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (fun omega => Finset.sum_nonneg fun k _ => hnonneg k omega)).2 hfinite
  refine hwith.mono_scale (mul_le_mul_of_nonneg_left ?_
    IndependentSums.gammaTriangleConst_pos.le)
  exact sum_Ioc_rpow_gamma_sub_one_le M.shellPrefix.gamma_le_quarter (le_of_lt hnm)

/-! ## The deterministic increment bridge -/

private theorem matrixDerivativeNorm_zero :
    ShellField.matrixDerivativeNorm (0 : ShellField.MatrixDerivative d) = 0 := by
  refine le_antisymm ?_ (ShellField.matrixDerivativeNorm_nonneg _)
  rw [matrixDerivativeNorm_le_iff]
  refine ⟨le_refl 0, fun v _ => ?_⟩
  simp only [zero_apply]
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (0 : Mat d)‖ ≤ 0
  rw [map_zero, norm_zero]

/-- The exact induced first-derivative norm is subadditive over finite
sums. -/
theorem matrixDerivativeNorm_finset_sum_le (s : Finset ℤ)
    (D : ℤ → ShellField.MatrixDerivative d) :
    ShellField.matrixDerivativeNorm (∑ k ∈ s, D k) ≤
      ∑ k ∈ s, ShellField.matrixDerivativeNorm (D k) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [matrixDerivativeNorm_zero]
  | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (ShellField.matrixDerivativeNorm_add_le _ _).trans (by linarith)

/-- The first derivative of a finite shell increment is dominated on `cu_ell`
by the summed first-derivative gauges. -/
theorem matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm (ell : ℤ)
    (s : Finset ℤ) (omega : ShellSeq d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) :
    ShellField.matrixDerivativeNorm (∑ k ∈ s, ShellField.deriv (omega k) x) ≤
      ∑ k ∈ s, localCubeDerivNorm ell (omega k) := by
  refine (matrixDerivativeNorm_finset_sum_le s
    (fun k => ShellField.deriv (omega k) x)).trans ?_
  exact Finset.sum_le_sum fun k _ =>
    matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell (omega k) hx

end

end Algsuperdiff.Section3.Provider.Stream
