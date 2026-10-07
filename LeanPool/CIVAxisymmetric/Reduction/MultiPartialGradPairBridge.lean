/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CIVAxisymmetric.Statements.PartialLaplacian
public import LeanPool.CIVAxisymmetric.Statements.GradPair
public import LeanPool.CIVAxisymmetric.Analysis.CurlCutoff
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial

/-!
The identification of this repository's three independent spatial-derivative
formalisms — the multi-index `multiPartial`/`spatialPartial` pair used to state
the pointwise vorticity-equation bounds of Serrin's route, the `gradVec`/`classicalGradient` pair
used by the cutoff library, and the `gradPair`/`partialLaplacian` pair used by the
Green's-identity machinery of the local Caccioppoli inequality — so that a bound
proved in one idiom is available in the others for the proof of `lem:aniso:annulus`'s
interior estimates.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem spatialPartial_eq_gradPair (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) :
    CKN.spatialPartial g i z = gradPair 3 g z (basisVec i) := by
  rfl

theorem gradVec_eq_gradPair_comp_fst (χ : Vec3 → ℝ) (x : Vec3) (τ : ℝ) (i : Fin 3) :
    gradVec χ x i = gradPair 3 (fun z : Vec3 × ℝ => χ z.1) (x, τ) (basisVec i) := by
  rfl

theorem partialLaplacian_three_eq_sum_spatialSecondPartial (g : ParabolicPoint → ℝ)
    (z : ParabolicPoint) :
    partialLaplacian 3 3 g z = ∑ i : Fin 3, CKN.spatialSecondPartial g i i z := by
  unfold partialLaplacian
  simp [CKN.spatialSecondPartial, CKN.spatialPartial]

theorem multiPartial_single_eq_spatialPartial (g : ParabolicPoint → ℝ) (i : Fin 3) :
    multiPartial g (Pi.single i 1) = CKN.spatialPartial g i := by
  fin_cases i <;> simp [multiPartial, Pi.single]

end CIV
