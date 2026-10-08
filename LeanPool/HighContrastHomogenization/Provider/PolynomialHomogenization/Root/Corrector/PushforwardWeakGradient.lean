/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardCovariance
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CorrectorEquationFamilyComposition

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardWeakGradient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pushforward pair is a global weak-gradient pair

`hasWeakGradientOn_affinePullback` transports a weak-gradient pair along an
invertible matrix, but it demands `L²` control on the *source domain*, which no
corrector satisfies globally.  The locality lemma
(`hasWeakGradientOn_univ_of_localGradientCube`) and reverse sandwich
(`exists_localGradientCube_subset_matImage`) are exactly what lets it be
applied cube by cube and assembled on `Set.univ`.

The gauge root is symmetric, so the transpose factor produced by the pullback
is the inverse root itself and the conclusion is literally `pushforwardGradient`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The inverse gauge root is invertible. -/
theorem isUnit_det_gaugeRoot_inv [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) : IsUnit ((gaugeRoot abar)⁻¹).det := by
  have hL : IsUnit (gaugeRoot abar).det := isUnit_det_gaugeRoot hS
  rw [Matrix.det_nonsing_inv]
  exact hL.ringInverse

/-- The inverse gauge root is symmetric. -/
theorem matTranspose_gaugeRoot_inv [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    matTranspose (gaugeRoot abar)⁻¹ = (gaugeRoot abar)⁻¹ := by
  have hinvT : matTranspose (gaugeRoot abar)⁻¹ =
      (matTranspose (gaugeRoot abar))⁻¹ := by
    simpa [matTranspose] using Matrix.transpose_nonsing_inv (A := gaugeRoot abar)
  rw [hinvT, matTranspose_gaugeRoot hS]

/-- **Clause (3) for the pushforward family.**  The affine pushforward of a
normalized-gauge carrier's canonical representatives is a weak-gradient pair on
all of `Vec d`. -/
theorem hasWeakGradientOn_univ_pushforward [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (G : NormalizedLocalH1Carrier d) :
    HasWeakGradientOn Set.univ (pushforwardValue abar G) (pushforwardGradient abar G) := by
  have hL : IsUnit (gaugeRoot abar).det := isUnit_det_gaugeRoot hS
  have hLinv : IsUnit ((gaugeRoot abar)⁻¹).det := isUnit_det_gaugeRoot_inv hS
  obtain ⟨k, hk⟩ := exists_localGradientCube_subset_matImage (gaugeRoot abar) hL
  refine hasWeakGradientOn_univ_of_localGradientCube fun n => ?_
  refine hasWeakGradientOn_subset (hk n) ?_
  have hU : MeasurableSet (localGradientCube d (n + k)) :=
    (isOpen_openCubeSet (originCube d ((n + k : ℕ) : ℤ))).measurableSet
  have hu : MemL2On (localGradientCube d (n + k)) G.globalValueRepresentative :=
    G.memLp_globalValueRepresentative (n + k)
  have hDu : GradMemL2On (localGradientCube d (n + k))
      G.globalGradientRepresentative := by
    intro i
    have hmem := G.memLp_globalGradientRepresentative (n + k)
    refine MemLp.mono hmem ((continuous_apply i).comp_aestronglyMeasurable
      hmem.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun x =>
      norm_le_pi_norm (G.globalGradientRepresentative x) i
  have hweak : HasWeakGradientOn (localGradientCube d (n + k))
      G.globalValueRepresentative G.globalGradientRepresentative :=
    hasWeakGradientOn_subset (Set.subset_univ _)
      G.hasWeakGradientOn_globalRepresentatives
  have hpull := hasWeakGradientOn_affinePullback hLinv hU hu hDu hweak
  rw [Matrix.nonsing_inv_nonsing_inv _ hL, matTranspose_gaugeRoot_inv hS] at hpull
  exact hpull

end

end Root
end HighContrast
end HCPolySupport
