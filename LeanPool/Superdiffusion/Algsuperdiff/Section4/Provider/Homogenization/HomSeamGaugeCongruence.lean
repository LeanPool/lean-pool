/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutSupport

/-!
# HomSeamGaugeCongruence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The multiscale clause's `∀ G` slot: the gauge is an a.e. functional

## What this file supplies

The energy residue's multiscale conjunct is
quantified over EVERY field `G` that agrees with `∇u − ∇v` on the open cube:

```text
  ∀ G, (∀ x ∈ □_m, G x = ∇u x − ∇v x) → CoarseGrainingFinitePMultiscale … G F.
```

The quantifier is FREE.  The multiscale clause reads its gradient
slot only through the depth gauge, which reads it only through the cell
averages `(G)_R` of the grid descendants `R ⊆ □_m`, and the cube average is an
a.e. functional of its integrand.  So the whole `∀ G` family collapses onto ONE
representative — the canonical `fun x => u.grad x - v.grad x`.

The congruence below is that collapse, stated in exactly the shape the supply's
clause slot asks for.
-/

open HCPolySupport MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube average is an a.e. functional -/

/-- The scalar cube average sees its integrand only a.e. on the closed cube. -/
private theorem seamCubeAverage_congr_ae (R : TriadicCube d) {u v : Vec d → ℝ}
    (h : u =ᵐ[volume.restrict (cubeSet R)] v) :
    cubeAverage R u = cubeAverage R v := by
  unfold cubeAverage
  exact congrArg (fun t : ℝ => (cubeVolume R)⁻¹ * t) (integral_congr_ae h)

/-- The vector cube average sees its field only a.e. on the closed cube. -/
private theorem seamCubeAverageVec_congr_ae (R : TriadicCube d) {u v : Vec d → Vec d}
    (h : u =ᵐ[volume.restrict (cubeSet R)] v) :
    cubeAverageVec R u = cubeAverageVec R v := by
  funext i
  refine seamCubeAverage_congr_ae R ?_
  filter_upwards [h] with x hx
  exact congrFun hx i

/-- **THE CELL AVERAGE OF A DESCENDANT IS BLIND TO THE PARENT'S NULL SETS.**

If two fields agree pointwise on the OPEN parent cube, then every grid
descendant's cell average agrees.  This is the only way the finite-`p` gauge
touches its field. -/
theorem cubeAverageVec_congr_of_eqOn_openCube {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) {G G' : Vec d → Vec d}
    (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    cubeAverageVec R G = cubeAverageVec R G' :=
  seamCubeAverageVec_congr_ae R
    (ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR
      (ae_restrict_of_forall_mem (measurableSet_openCubeSet Q) hG))

/-! ## 2. The finite-`p` gauge, transported -/

/-- The depth-`j` `ℓ^p` mean is unchanged. -/
theorem negBesovLpDepthMean_congr_of_eqOn (Q : TriadicCube d) (p : ℝ) (j : ℕ)
    {G G' : Vec d → Vec d} (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    negBesovLpDepthMean Q p G j = negBesovLpDepthMean Q p G' j := by
  have hsum : (descendantsAverage Q j fun R =>
        Real.sqrt (vecNormSq (cubeAverageVec R G)) ^ p) =
      descendantsAverage Q j fun R =>
        Real.sqrt (vecNormSq (cubeAverageVec R G')) ^ p := by
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, Real.sqrt (vecNormSq (cubeAverageVec R G)) ^ p =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, Real.sqrt (vecNormSq (cubeAverageVec R G')) ^ p
    refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [cubeAverageVec_congr_of_eqOn_openCube hR hG]
  rw [negBesovLpDepthMean_def, negBesovLpDepthMean_def, hsum]

/-- The weighted depth-`j` quantity is unchanged. -/
theorem negBesovLpDepthSeminorm_congr_of_eqOn (Q : TriadicCube d) (s p : ℝ) (j : ℕ)
    {G G' : Vec d → Vec d} (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    negBesovLpDepthSeminorm Q s p G j = negBesovLpDepthSeminorm Q s p G' j := by
  rw [negBesovLpDepthSeminorm_def, negBesovLpDepthSeminorm_def,
    negBesovLpDepthMean_congr_of_eqOn Q p j hG]

end

end Algsuperdiff.Section4.Provider.Homogenization
