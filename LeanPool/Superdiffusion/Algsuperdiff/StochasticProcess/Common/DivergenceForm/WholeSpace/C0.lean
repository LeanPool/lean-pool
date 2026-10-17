/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Vanishing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.FunctionalAnalysis.CompactSupportDenseCore

/-!
# C0

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The analytic minimal resolvent on `C₀`

Compactly supported continuous functions form a uniformly dense core.
Continuity and vanishing at infinity for their analytic minimal resolvents,
together with the uniform resolvent stability estimate, therefore extend to
all of `C₀`.  Dense range is isolated as the explicit remaining analytic
hypothesis allowed by the whole-space construction.
-/

namespace DivergenceFormProcess.Form

open CompactlySupported Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

omit [NeZero d] in
private theorem abs_le_norm_c0 (f : C₀(Vec d, ℝ)) (x : Vec d) : |f x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

omit [NeZero d] in
private theorem pointwise_sub_le_norm_c0 (f g : C₀(Vec d, ℝ)) (x : Vec d) :
    |f x - g x| ≤ ‖f - g‖ := by
  rw [← Real.norm_eq_abs, ← show (f - g) x = f x - g x from rfl,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm (f - g).toBCF x

omit [NeZero d] in
private theorem exists_compactSupportCore_close (f : C₀(Vec d, ℝ)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ g : DivergenceFormProcess.FunctionalAnalysis.CompactSupportCore (Vec d),
      ‖DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0 g - f‖ < eps := by
  have hdense := DivergenceFormProcess.FunctionalAnalysis.denseRange_compactSupportCoreToC0
    (X := Vec d)
  change Dense (Set.range
    (DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0
      (X := Vec d))) at hdense
  rw [Metric.dense_iff] at hdense
  obtain ⟨y, hy, ⟨g, rfl⟩⟩ := hdense f eps heps
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact ⟨g, hy⟩

/-- The real minimal resolvent of every `C₀` datum is continuous. -/
theorem continuous_analyticMinimalResolventReal (mu : PositiveShift)
    (f : C₀(Vec d, ℝ)) :
    Continuous (A.analyticMinimalResolventReal mu f f.continuous.measurable
      (D := ‖f‖) (by exact abs_le_norm_c0 f)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro eps heps
  let delta : ℝ := eps * (mu : ℝ) / 16
  have hdelta : 0 < delta :=
    div_pos (mul_pos heps mu.property) (by norm_num)
  obtain ⟨g, hgclose⟩ := exists_compactSupportCore_close f hdelta
  let g0 : C₀(Vec d, ℝ) :=
    DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0 g
  have hclose : ∀ y, |f y - g0 y| ≤ delta := by
    intro y
    refine (pointwise_sub_le_norm_c0 f g0 y).trans (le_of_lt ?_)
    rw [norm_sub_rev]
    simpa only [g0] using hgclose
  have hgcompact : HasCompactSupport g0 := mem_compactlySupported.mp g.property
  have hgLp : MemLp (fun y => g0 y) 2 volume :=
    g0.continuous.memLp_of_hasCompactSupport hgcompact
  have hgcont := A.continuous_analyticMinimalResolventReal_of_memLp mu
    g0.continuous.measurable (norm_nonneg g0) (abs_le_norm_c0 g0) hgLp
  have hout : ∀ y, |A.analyticMinimalResolventReal mu f f.continuous.measurable
        (abs_le_norm_c0 f) y -
      A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
        (abs_le_norm_c0 g0) y| < eps / 4 := by
    intro y
    have hstable := A.abs_analyticMinimalResolventReal_sub_le mu
      f.continuous.measurable g0.continuous.measurable
      (abs_le_norm_c0 f) (abs_le_norm_c0 g0) hclose y
    have hcalc : delta / (mu : ℝ) = eps / 16 := by
      dsimp only [delta]
      field_simp [ne_of_gt (show 0 < (mu : ℝ) from mu.property)]
    rw [hcalc] at hstable
    have hstable' :
        |A.analyticMinimalResolventReal mu f f.continuous.measurable
            (abs_le_norm_c0 f) y -
          A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_c0 g0) y| ≤ eps / 16 := by
      simpa only using! hstable
    exact hstable'.trans_lt (by linarith only [heps])
  obtain ⟨eta, heta, hlocal⟩ := Metric.continuousAt_iff.1 hgcont.continuousAt
    (eps / 2) (by linarith only [heps])
  refine ⟨eta, heta, fun y hy => ?_⟩
  have hmid := hlocal hy
  rw [Real.dist_eq] at hmid ⊢
  have h1 := hout y
  have h2 := hout x
  calc
    |A.analyticMinimalResolventReal mu f f.continuous.measurable
          (abs_le_norm_c0 f) y -
        A.analyticMinimalResolventReal mu f f.continuous.measurable
          (abs_le_norm_c0 f) x| ≤
      |A.analyticMinimalResolventReal mu f f.continuous.measurable
          (abs_le_norm_c0 f) y -
      A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_c0 g0) y| +
      |A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_c0 g0) y -
        A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_c0 g0) x| +
      |A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_c0 g0) x -
        A.analyticMinimalResolventReal mu f f.continuous.measurable
          (abs_le_norm_c0 f) x| := by
        let Fy := A.analyticMinimalResolventReal mu f f.continuous.measurable
          (abs_le_norm_c0 f) y
        let Fx := A.analyticMinimalResolventReal mu f f.continuous.measurable
          (abs_le_norm_c0 f) x
        let Gy := A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_c0 g0) y
        let Gx := A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_c0 g0) x
        change |Fy - Fx| ≤ |Fy - Gy| + |Gy - Gx| + |Gx - Fx|
        calc
          |Fy - Fx| = |(Fy - Gy) + (Gy - Gx) + (Gx - Fx)| := by
            congr 1
            ring
          _ ≤ |(Fy - Gy) + (Gy - Gx)| + |Gx - Fx| := abs_add_le _ _
          _ ≤ (|Fy - Gy| + |Gy - Gx|) + |Gx - Fx| :=
            add_le_add (abs_add_le _ _) (le_refl _)
    _ < eps / 4 + eps / 2 + eps / 4 := by
      refine add_lt_add (add_lt_add h1 hmid) ?_
      simpa only [abs_sub_comm] using h2
    _ = eps := by ring

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
