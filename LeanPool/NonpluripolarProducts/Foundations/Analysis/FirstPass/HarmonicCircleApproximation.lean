/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Global harmonic approximation of continuous circle data

Finite Fourier sums on `AddCircle (2 * π)` extend to global harmonic
functions on the complex plane: positive modes use holomorphic powers of the
normalized affine coordinate, while negative modes use their complex
conjugates.  Density of the Fourier span then gives uniform approximation of
continuous real boundary data by globally harmonic real functions.
-/

@[expose] public section

open Set Metric TopologicalSpace ContinuousMap Submodule
open scoped Real ComplexConjugate Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The standard parametrization of the radius-`R` circle by the additive
circle of period `2π`. -/
def harmonicCircleParam (c : ℂ) (R : ℝ) (q : AddCircle (2 * Real.pi)) : ℂ :=
  c + R * (AddCircle.homeomorphCircle' q : ℂ)

theorem continuous_harmonicCircleParam (c : ℂ) (R : ℝ) :
    Continuous (harmonicCircleParam c R) := by
  unfold harmonicCircleParam
  fun_prop

@[simp] theorem harmonicCircleParam_coe (c : ℂ) (R t : ℝ) :
    harmonicCircleParam c R (t : AddCircle (2 * Real.pi)) = circleMap c R t := by
  simp [harmonicCircleParam, circleMap, AddCircle.homeomorphCircle'_apply_mk]

/-- The global harmonic extension of the `n`-th Fourier character. -/
def globalHarmonicFourierMode (c : ℂ) (R : ℝ) (n : ℤ) (z : ℂ) : ℂ :=
  if 0 ≤ n then ((z - c) / (R : ℂ)) ^ n.toNat
  else conj (((z - c) / (R : ℂ)) ^ (-n).toNat)

theorem globalHarmonicFourierMode_harmonicOnNhd (c : ℂ) (R : ℝ) (n : ℤ) :
    InnerProductSpace.HarmonicOnNhd (globalHarmonicFourierMode c R n) univ := by
  intro z _
  unfold globalHarmonicFourierMode
  split_ifs with hn
  · exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => ((w - c) / (R : ℂ)) ^ n.toNat) z).harmonicAt
  · exact (by fun_prop : AnalyticAt ℂ
        (fun w : ℂ => ((w - c) / (R : ℂ)) ^ (-n).toNat) z).harmonicAt_conj

theorem globalHarmonicFourierMode_param (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (n : ℤ) (q : AddCircle (2 * Real.pi)) :
    globalHarmonicFourierMode c R n (harmonicCircleParam c R q) =
      fourier n q := by
  induction q using QuotientAddGroup.induction_on
  rename_i t
  rw [harmonicCircleParam_coe, fourier_coe_apply]
  have hfourierExponent :
      (2 : ℂ) * Real.pi * Complex.I * (n : ℂ) * (t : ℂ) /
          ((2 * Real.pi : ℝ) : ℂ) =
        (n : ℂ) * ((t : ℂ) * Complex.I) := by
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  unfold globalHarmonicFourierMode
  split_ifs with hn
  · have hcoord : (circleMap c R t - c) / (R : ℂ) = Complex.exp (t * Complex.I) := by
      rw [circleMap_sub_center]
      simp [circleMap_zero, hR]
    rw [hcoord, ← Complex.exp_nat_mul, hfourierExponent]
    have hcast : (n.toNat : ℂ) = (n : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    rw [hcast]
  · have hcoord : (circleMap c R t - c) / (R : ℂ) = Complex.exp (t * Complex.I) := by
      rw [circleMap_sub_center]
      simp [circleMap_zero, hR]
    rw [hcoord, ← Complex.exp_nat_mul, ← Complex.exp_conj]
    rw [map_mul, map_natCast, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [hfourierExponent]
    congr 1
    have hneg : 0 ≤ -n := by omega
    have hcast : ((-n).toNat : ℂ) = ((-n : ℤ) : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg hneg
    rw [hcast]
    push_cast
    ring

/-- Every finite Fourier sum has an exactly matching global harmonic extension
to the complex plane. -/
theorem exists_global_harmonic_extension_of_mem_span_fourier
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (p : C(AddCircle (2 * Real.pi), ℂ))
    (hp : p ∈ span ℂ (range (@fourier (2 * Real.pi)))) :
    ∃ H : ℂ → ℂ,
      InnerProductSpace.HarmonicOnNhd H univ ∧
      ∀ q, H (harmonicCircleParam c R q) = p q := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨n, rfl⟩ := hp
      exact ⟨globalHarmonicFourierMode c R n,
        globalHarmonicFourierMode_harmonicOnNhd c R n,
        globalHarmonicFourierMode_param c hR n⟩
  | zero =>
      exact ⟨fun _ ↦ 0, InnerProductSpace.harmonicOnNhd_const 0, by simp⟩
  | add p₁ p₂ _ _ ih₁ ih₂ =>
      obtain ⟨H₁, hH₁, hbdy₁⟩ := ih₁
      obtain ⟨H₂, hH₂, hbdy₂⟩ := ih₂
      refine ⟨H₁ + H₂, hH₁.add hH₂, ?_⟩
      intro q
      simp [hbdy₁ q, hbdy₂ q]
  | smul a p _ ih =>
      obtain ⟨H, hH, hbdy⟩ := ih
      refine ⟨fun z ↦ a * H z, ?_, ?_⟩
      · simpa [Function.comp_def] using
          hH.comp_CLM (ContinuousLinearMap.mul ℝ ℂ a)
      · intro q
        simp [hbdy q]

/-- Continuous real data on the abstract circle can be uniformly approximated,
after affine circle parametrization, by a real-valued global harmonic function. -/
theorem exists_global_harmonic_uniformApprox_circleParam
    (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (g : C(AddCircle (2 * Real.pi), ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd h univ ∧
      ∀ q, |h (harmonicCircleParam c R q) - g q| < ε := by
  let G : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun q ↦ (g q : ℂ), by fun_prop⟩
  have hG : G ∈ (span ℂ (range (@fourier (2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hG ε hε
  obtain ⟨H, hH, hbdy⟩ :=
    exists_global_harmonic_extension_of_mem_span_fourier c hR p hp
  refine ⟨fun z ↦ (H z).re, ?_, ?_⟩
  · simpa [Function.comp_def] using hH.comp_CLM Complex.reCLM
  · intro q
    have hre :
        |(H (harmonicCircleParam c R q)).re - g q| ≤
          ‖H (harmonicCircleParam c R q) - (g q : ℂ)‖ := by
      calc
        |(H (harmonicCircleParam c R q)).re - g q| =
            ‖Complex.reCLM
              (H (harmonicCircleParam c R q) - (g q : ℂ))‖ := by simp
        _ ≤ ‖Complex.reCLM‖ *
            ‖H (harmonicCircleParam c R q) - (g q : ℂ)‖ :=
          Complex.reCLM.le_opNorm _
        _ = ‖H (harmonicCircleParam c R q) - (g q : ℂ)‖ := by
          rw [Complex.reCLM_norm, one_mul]
    refine hre.trans_lt ?_
    rw [hbdy q]
    calc
      ‖p q - (g q : ℂ)‖ = ‖(p - G) q‖ := by rfl
      _ ≤ ‖p - G‖ := ContinuousMap.norm_coe_le_norm (p - G) q
      _ = dist p G := by rw [dist_eq_norm]
      _ = dist G p := dist_comm _ _
      _ < ε := hdist

/-- Continuous real data on a positive-radius Euclidean circle can be uniformly
approximated there by a real-valued harmonic function on the whole plane. -/
theorem exists_global_harmonic_uniformApproxOn_sphere
    (c : ℂ) {R : ℝ} (hR : 0 < R)
    {f : ℂ → ℝ} (hf : ContinuousOn f (sphere c R))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd h univ ∧
      ∀ z ∈ sphere c R, |h z - f z| < ε := by
  have hparam : ∀ q, harmonicCircleParam c R q ∈ sphere c R := by
    intro q
    induction q using QuotientAddGroup.induction_on
    rename_i t
    rw [harmonicCircleParam_coe]
    exact circleMap_mem_sphere c hR.le t
  let g : C(AddCircle (2 * Real.pi), ℝ) :=
    ⟨fun q ↦ f (harmonicCircleParam c R q),
      hf.comp_continuous (continuous_harmonicCircleParam c R) hparam⟩
  obtain ⟨h, hharm, happ⟩ :=
    exists_global_harmonic_uniformApprox_circleParam c hR.ne' g hε
  refine ⟨h, hharm, ?_⟩
  intro z hz
  have hz' : z ∈ range (circleMap c R) := by
    rw [range_circleMap, abs_of_pos hR]
    exact hz
  obtain ⟨t, rfl⟩ := hz'
  simpa [g] using happ (t : AddCircle (2 * Real.pi))

end

end SGPT.Foundations.Analysis.FirstPass
