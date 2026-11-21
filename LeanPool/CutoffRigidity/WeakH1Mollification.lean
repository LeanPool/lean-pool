/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanL2Coordinates
public import LeanPool.CutoffRigidity.EuclideanMollificationStrongLimit

/-! # Actual strong H¹ mollification from genuine weak derivative identities

Every coordinate of the classical derivative of a smoothing equals the
actual smoothing of its weak derivative. Arbitrary-L² strong convergence
and finite-coordinate reconstruction then give strong vector-gradient
convergence, without assuming closed-domain membership.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual gradient of a compact smoothing lies in Lebesgue L². -/
theorem mollifiedGradient_memLp (φ : ContDiffBump (0 : E)) {g : E → ℝ}
    (hg : LocallyIntegrable g volume) (hgc : HasCompactSupport g) :
    MemLp (gradient (bumpMollification φ g)) 2 volume :=
  c1_compact_gradient_memLp ((bumpMollification_contDiff φ hg).of_le (by norm_num))
    (bumpMollification_hasCompactSupport φ hgc)

/-- The actual L² class of the classical gradient of an actual smoothing. -/
@[expose] noncomputable def mollifiedGradientLp (φ : ContDiffBump (0 : E)) (g : E → ℝ)
    (hg : LocallyIntegrable g volume) (hgc : HasCompactSupport g) : E →₂[volume] E :=
  (mollifiedGradient_memLp φ hg hgc).toLp (gradient (bumpMollification φ g))

/-- The scalar coordinate class of the smoothed gradient is the actual
smoothing of the corresponding genuine weak derivative. -/
theorem project_mollifiedGradientLp_of_weak_derivative (φ : ContDiffBump (0 : E))
    {g : E → ℝ} (hg : LocallyIntegrable g volume) (hgc : HasCompactSupport g)
    (H : E →₂[volume] ℝ) (j : Fin d)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H y * ψ y)) :
    (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp (mollifiedGradientLp φ g hg hgc) =
      bumpMollificationLp φ (fun x => H x) (Lp.stronglyMeasurable H).measurable (Lp.memLp H) := by
  apply Lp.ext
  filter_upwards [(EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp (mollifiedGradientLp φ g hg hgc),
    (mollifiedGradient_memLp φ hg hgc).coeFn_toLp,
    (bumpMollification_L2_contraction φ (Lp.stronglyMeasurable H).measurable (Lp.memLp
      H)).1.coeFn_toLp]
    with x hp hgrad hH
  rw [hp]
  unfold mollifiedGradientLp bumpMollificationLp
  rw [hgrad, hH]
  change (gradient (bumpMollification φ g) x) j = bumpMollification φ (fun y => H y) x
  rw [← fderiv_single_eq_gradient_coordinate]
  exact coordinateDerivative_bumpMollification_of_weak_derivative φ hg
    ((Lp.memLp H).locallyIntegrable (by norm_num)) j hweak x

/-- The genuine weak derivatives provide actual strong vector-gradient
convergence of compact smooth mollifications in Lebesgue L². -/
theorem mollifiedGradientLp_tendsto_of_weak_derivatives
    (φ : ℕ → ContDiffBump (0 : E)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {g : E → ℝ} (hg : LocallyIntegrable g volume) (hgc : HasCompactSupport g)
    (H : Fin d → E →₂[volume] ℝ)
    (hweak : ∀ j : Fin d, ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H j y * ψ y)) :
    Tendsto (fun n => mollifiedGradientLp (φ n) g hg hgc) atTop (𝓝 (euclideanL2Assemble H)) := by
  apply tendsto_euclideanL2_of_coordinate_tendsto
  intro j
  simp_rw [project_mollifiedGradientLp_of_weak_derivative _ hg hgc (H j) j (hweak j)]
  rw [euclideanL2_project_assemble]
  have hh := bumpMollificationLp_tendsto φ hφ (fun x => H j x)
    (Lp.stronglyMeasurable (H j)).measurable (Lp.memLp (H j))
  simpa only [Lp.toLp_coeFn] using hh

end CutoffRigidity
