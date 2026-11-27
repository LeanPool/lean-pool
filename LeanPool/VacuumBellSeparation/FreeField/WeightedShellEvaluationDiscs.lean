/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceCurve
public import LeanPool.VacuumBellSeparation.Shell.NullDiscs
public import Mathlib.Analysis.Complex.AbsMax

/-!
# The actual null-disc step for weighted source evaluation

The original compact-source Fourier wave is entire along the actual
affine null discs. The maximum modulus principle transfers any uniform
squared bound on the normalized regular target to every shell point
of Euclidean norm at most twice the energy, with no loss of constant.
The regular-target bound is an explicit hypothesis here; it is proved as
`normalizedTarget_weightedSource_evaluation` in `FreeField/WeightedShellEvaluationRegular.lean`.
-/

@[expose] public section

namespace VacuumBellSeparation

open Set Metric

/-- Null disc derivative given by `(0, fun j => (8 * En : ℂ) * n j)`. -/
noncomputable def nullDiscDerivative (En : ℝ) (n : Fin 3 → ℂ) : ComplexSpacetime :=
  (0, fun j => (8 * En : ℂ) * n j)

theorem hasDerivAt_nullDisc (z : ComplexSpacetime) (En : ℝ) (n : Fin 3 → ℂ) (ζ : ℂ) :
    HasDerivAt (nullDisc z En n) (nullDiscDerivative En n) ζ := by
  apply HasDerivAt.prodMk
  · exact hasDerivAt_const ζ z.1
  · apply hasDerivAt_pi.mpr
    intro j
    convert (((hasDerivAt_id ζ).const_mul (8 * En : ℂ)).mul_const (n j)).const_add (z.2 j)
      using 1 <;> first | rfl | simp only [mul_one]

theorem analyticOnNhd_complexSourceWave_nullDisc (u : TimeZeroSource)
    (z : ComplexSpacetime) (En : ℝ) (n : Fin 3 → ℂ) :
    AnalyticOnNhd ℂ (fun ζ => complexSourceWave u (nullDisc z En n ζ)) Set.univ := by
  apply analyticOnNhd_complexSourceWave_curve u (nullDisc z En n)
    (fun _ => nullDiscDerivative En n)
  · unfold nullDisc
    fun_prop
  · exact continuous_const
  · exact hasDerivAt_nullDisc z En n

/-- Literal complexified compact test waves inherit the regular-patch
bound at all requested shell points. The source and all cross terms
are unchanged, and the squared estimate has the same constant. -/
theorem complexSourceWave_bound_of_normalizedTarget
    {m En B : ℝ} (hm : 0 < m) (hEn : m ≤ En) (hB : 0 ≤ B)
    (u v : TimeZeroSource)
    (hregular : ∀ w : ComplexSpacetime, (m / En, scaleBy En w) ∈ normalizedTarget →
      ‖complexSourceWave u w + Complex.I * complexSourceWave v w‖ ^ 2 ≤ B)
    {z : ComplexSpacetime} (hz : z ∈ complexShell m) (hsize : euclidSq z ≤ (2 * En) ^ 2) :
    ‖complexSourceWave u z + Complex.I * complexSourceWave v z‖ ^ 2 ≤ B := by
  obtain ⟨n, hzero, _, hboundary⟩ := exists_null_disc hm hEn hz hsize
  let f : ℂ → ℂ := fun ζ => complexSourceWave u (nullDisc z En n ζ) +
    Complex.I * complexSourceWave v (nullDisc z En n ζ)
  have hfu := analyticOnNhd_complexSourceWave_nullDisc u z En n
  have hfv := analyticOnNhd_complexSourceWave_nullDisc v z En n
  have hf : Differentiable ℂ f := by
    intro ζ
    exact (hfu ζ (mem_univ ζ)).differentiableAt.add
      ((hfv ζ (mem_univ ζ)).differentiableAt.const_mul Complex.I)
  have hb : ∀ ζ ∈ frontier (ball (0 : ℂ) 1), ‖f ζ‖ ≤ Real.sqrt B := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa only [frontier_ball _ one_ne_zero, mem_sphere, dist_zero_right] using hζ
    have hh := hregular (nullDisc z En n ζ) (hboundary ζ hnorm).2.2.2.2
    exact (Real.le_sqrt (norm_nonneg _) hB).2 hh
  have h0 : ‖f 0‖ ≤ Real.sqrt B :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf.diffContOnCl hb
      (subset_closure (by simp : (0 : ℂ) ∈ ball 0 1))
  have hsq := pow_le_pow_left₀ (norm_nonneg (f 0)) h0 2
  rw [Real.sq_sqrt hB] at hsq
  simpa only [f, hzero] using hsq

end VacuumBellSeparation
