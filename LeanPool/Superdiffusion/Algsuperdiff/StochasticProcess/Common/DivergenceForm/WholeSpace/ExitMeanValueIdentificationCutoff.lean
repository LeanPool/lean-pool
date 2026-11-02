/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.NestedCubeCutoff
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Cubes

/-!
# ExitMeanValueIdentificationCutoff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A smooth cutoff between two consecutive exhaustion cubes

The Caccioppoli estimate is applied on a pair of consecutive cubes of the exhaustion
`(-3^v, 3^v)^d ⊆ (-3^(v+1), 3^(v+1))^d`, and needs a smooth compactly supported function equal
to one on the inner cube and supported in the outer one, with a uniform bound on its gradient.

The quantitative cutoff of the upstream package is attached to the concentric subcubes of a
triadic cube, so the only work here is the transport: the exhaustion cube of index `v` is the
concentric subcube of relative radius `2` of the triadic cube of scale `v` centered at the
origin, and the exhaustion cube of index `v + 1` is the concentric subcube of relative radius
`6` of that same triadic cube.  The cutoff between relative radii `2` and `4` therefore does what
is needed.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport Set

noncomputable section

variable {d : ℕ}

/-! ## The triadic cube underlying an exhaustion cube -/

/-- The triadic cube of scale `v` centered at the origin.  Its concentric subcubes of relative
radii `2` and `6` are the exhaustion cubes of indices `v` and `v + 1`. -/
def exhaustionTriadicCube (d v : ℕ) : TriadicCube d where
  scale := (v : ℤ)
  index := fun _ ↦ 0

private theorem cubeRadius_exhaustionTriadicCube (d v : ℕ) :
    cubeRadius (exhaustionTriadicCube d v) = (1 / 2 : ℝ) * (3 : ℝ) ^ v := by
  rw [cubeRadius, cubeScaleFactor]
  norm_num [exhaustionTriadicCube]

private theorem cubeCenter_exhaustionTriadicCube (d v : ℕ) (i : Fin d) :
    cubeCenter (exhaustionTriadicCube d v) i = 0 := by
  rw [cubeCenter]
  norm_num [exhaustionTriadicCube]

private theorem wholeSpaceCube_subset_scaledClosedCubeSet (d v : ℕ) :
    wholeSpaceCube d v ⊆ scaledClosedCubeSet (exhaustionTriadicCube d v) 2 := by
  intro x hx i
  rw [cubeRadius_exhaustionTriadicCube, cubeCenter_exhaustionTriadicCube, sub_zero]
  have hxi := mem_wholeSpaceCube_iff.mp hx i
  have hval : (2 : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ v) = (3 : ℝ) ^ v := by ring
  rw [hval]
  exact abs_le.mpr ⟨hxi.1.le, hxi.2.le⟩

private theorem scaledOpenCubeSet_subset_wholeSpaceCube_succ (d v : ℕ) :
    scaledOpenCubeSet (exhaustionTriadicCube d v) 6 ⊆ wholeSpaceCube d (v + 1) := by
  intro x hx
  refine mem_wholeSpaceCube_iff.mpr fun i ↦ ?_
  have hxi := hx i
  rw [cubeRadius_exhaustionTriadicCube, cubeCenter_exhaustionTriadicCube, sub_zero] at hxi
  have hval : (6 : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ v) = (3 : ℝ) ^ (v + 1) := by
    rw [pow_succ]
    ring
  rw [hval] at hxi
  exact abs_lt.mp hxi

/-! ## The cutoff -/

/-- **A smooth cutoff between two consecutive exhaustion cubes.**  It equals one on the inner
cube, is supported in the outer cube, and has a uniformly bounded coordinate gradient. -/
theorem exists_wholeSpaceCubeCutoff (d v : ℕ) :
    ∃ eta : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
      tsupport eta ⊆ wholeSpaceCube d (v + 1) ∧
      (∀ x ∈ wholeSpaceCube d v, eta x = 1) ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ x, vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) ≤ K := by
  set Q : TriadicCube d := exhaustionTriadicCube d v with hQ
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h24 : (2 : ℝ) < 4 := by norm_num
  have h46 : (4 : ℝ) < 6 := by norm_num
  refine ⟨QuantitativeCubeCutoff.canonicalFun Q 2 4,
    QuantitativeCubeCutoff.canonicalFun_smooth Q h2 h24,
    QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q h2 h24, ?_, ?_, ?_⟩
  · exact (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledOpenCubeSet
      Q h2 h24 h46).trans (scaledOpenCubeSet_subset_wholeSpaceCube_succ d v)
  · intro x hx
    exact QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner h2 h24
      (wholeSpaceCube_subset_scaledClosedCubeSet d v hx)
  · refine ⟨(d : ℝ) * ((d : ℝ) * smoothTransitionProfile.derivBound *
      (2 / (((4 : ℝ) - 2) * cubeRadius Q))) ^ 2, ?_, ?_⟩
    · positivity
    · intro x
      exact QuantitativeCubeCutoff.vecNormSq_canonicalFun_gradient_le Q h2 h24 x

end

end DivergenceFormProcess.Form
