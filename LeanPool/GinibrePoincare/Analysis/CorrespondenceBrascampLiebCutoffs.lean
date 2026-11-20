/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebCutoffs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebJets
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-!
# Correspondence Brascamp Lieb cutoffs

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_cutoff_compact`,
`correspondenceBrascampLieb_cutoff_unit`, `correspondenceBrascampLieb_cutoff_eventually_one`,
`correspondenceBrascampLieb_cutoff_directional_bound`.
-/

@[expose] public section
open Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The smooth bump at `0` with inner radius `1` and outer radius `2`. -/
def correspondenceBrascampLiebBump : ContDiffBump (0 : E) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The rescaled cutoff `x ↦ correspondenceBrascampLiebBump ((k + 1)⁻¹ • x)`. -/
def correspondenceBrascampLiebCutoff (k : ℕ) (x : E) : ℝ :=
  (correspondenceBrascampLiebBump (E := E)) (((k : ℝ)+1)⁻¹ • x)

theorem correspondenceBrascampLieb_cutoff_smooth (k : ℕ) :
    ContDiff ℝ ∞ (correspondenceBrascampLiebCutoff (E := E) k) :=
  (correspondenceBrascampLiebBump (E := E)).contDiff.comp (by fun_prop)

theorem correspondenceBrascampLieb_cutoff_compact (k : ℕ) :
    HasCompactSupport (correspondenceBrascampLiebCutoff (E := E) k) := by
  exact (correspondenceBrascampLiebBump (E := E)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((k : ℝ)+1)⁻¹) (inv_ne_zero (by positivity)))

theorem correspondenceBrascampLieb_cutoff_unit (k : ℕ) (x : E) :
    0 ≤ correspondenceBrascampLiebCutoff k x ∧ correspondenceBrascampLiebCutoff k x ≤ 1 :=
  ⟨(correspondenceBrascampLiebBump (E := E)).nonneg, (correspondenceBrascampLiebBump (E :=
      E)).le_one⟩

theorem correspondenceBrascampLieb_cutoff_fderiv (k : ℕ) (x v : E) :
    fderiv ℝ (correspondenceBrascampLiebCutoff k) x v =
      ((k : ℝ)+1)⁻¹ * fderiv ℝ ((correspondenceBrascampLiebBump (E := E)) : E → ℝ)
        (((k : ℝ)+1)⁻¹ • x) v := by
  have hd := (((correspondenceBrascampLiebBump (E := E)).contDiff (n := 1)).differentiable (by
      norm_num)
    (((k : ℝ)+1)⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul (((k : ℝ)+1)⁻¹))
  unfold correspondenceBrascampLiebCutoff
  simpa [Function.comp_def,
    ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul] using
    congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv

theorem correspondenceBrascampLieb_cutoff_derivative_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (x v : E),
      |fderiv ℝ (correspondenceBrascampLiebCutoff k) x v| ≤
        M / ((k : ℝ)+1) * ‖v‖ := by
  obtain ⟨M, hM⟩ := ((correspondenceBrascampLiebBump (E := E)).contDiff (n := 1)).continuous_fderiv
    one_ne_zero |>.bounded_above_of_compact_support
      ((correspondenceBrascampLiebBump (E := E)).hasCompactSupport.fderiv ℝ)
  refine ⟨M, (norm_nonneg _).trans (hM 0),?_⟩
  intro k x v
  rw [correspondenceBrascampLieb_cutoff_fderiv, abs_mul, abs_of_nonneg (by positivity)]
  have hb : |fderiv ℝ ((correspondenceBrascampLiebBump (E := E)) : E → ℝ)
      (((k : ℝ)+1)⁻¹ • x) v| ≤ M*‖v‖ :=
    ((fderiv ℝ ((correspondenceBrascampLiebBump (E := E)) : E → ℝ)
      (((k : ℝ)+1)⁻¹ • x)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg v))
  calc
    _ ≤ ((k : ℝ)+1)⁻¹ * (M*‖v‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem correspondenceBrascampLieb_cutoff_eventually_one
    (K : Set E) (hK : IsCompact K) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, correspondenceBrascampLiebCutoff k x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  filter_upwards [eventually_ge_atTop (Nat.ceil R)] with k hk
  intro x hx
  apply (correspondenceBrascampLiebBump (E := E)).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖((k : ℝ)+1)⁻¹ • x‖ ≤ (1 : ℝ)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hp : 0 < (k : ℝ)+1 := by positivity
  rw [inv_mul_le_iff₀ hp]
  have hkR : R ≤ (k : ℝ) :=
    (Nat.le_ceil R).trans (by exact_mod_cast hk)
  have hxR := hR x hx
  nlinarith

theorem correspondenceBrascampLieb_cutoff_directional_bound
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (x : E) (i : ι),
      |bakryEmeryGibbsDirectional (correspondenceBrascampLiebCutoff k) (b i) x| ≤
        M / ((k : ℝ)+1) := by
  obtain ⟨M, hM0, hM⟩ := correspondenceBrascampLieb_cutoff_derivative_bound (E := E)
  refine ⟨M, hM0,?_⟩
  intro k x i
  simpa only [bakryEmeryGibbsDirectional, b.orthonormal.norm_eq_one, mul_one] using hM k x (b i)

end
end GinibrePoincare
