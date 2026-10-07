/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorPhysicalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzMollifyRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildPathContinuity

/-!
# Real velocities in the complex physical tensor map

The diagonal complex physical tensor is the complexification of the
original real regularized mild nonlinearity.
-/

public section

open MeasureTheory FourierTransform Filter
open scoped ENNReal FourierTransform SchwartzMap Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The continuous complex bilinear tensor agrees with the real
regularized mild tensor on the real L² subspace. -/
theorem regularisedTensorPhysicalMap_real_diagonal
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) :
    regularisedTensorPhysicalMap ρ ε hε
        (complexifyVectorL2 b) (complexifyVectorL2 b) =
      complexifyTensorL2 (regularizedMildTensor ρ ε hε b) := by
  let P := regularisedTensorPhysicalMap ρ ε hε
  have hMild : Continuous (regularizedMildTensor ρ ε hε) := by
    rw [continuous_iff_continuousAt]
    intro b₀
    exact regularizedMildTensor_continuousAt ρ ε hε id b₀ tendsto_id
  have hClosed : IsClosed {b₀ : RealVectorL2 |
      P (complexifyVectorL2 b₀) (complexifyVectorL2 b₀) =
        complexifyTensorL2 (regularizedMildTensor ρ ε hε b₀)} := by
    exact isClosed_eq
      (P.continuous₂.comp₂ complexifyVectorL2.continuous
        complexifyVectorL2.continuous)
      (complexifyTensorL2.continuous.comp hMild)
  have hDense : DenseRange
      (fun φ : 𝓢(L2Vec3, L2Vec3) => (φ.toLp 2 : RealVectorL2)) := by
    have h : DenseRange
        (SchwartzMap.toLpCLM ℝ L2Vec3 2 (volume : Measure L2Vec3)) :=
      SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
    exact h
  refine hDense.induction_on (p := fun b₀ =>
    P (complexifyVectorL2 b₀) (complexifyVectorL2 b₀) =
      complexifyTensorL2 (regularizedMildTensor ρ ε hε b₀)) b hClosed ?_
  intro φ
  dsimp only [P]
  rw [complexify_toLp_realSchwartz]
  change regularisedTensorPhysicalMap ρ ε hε
      ((complexifyRealSchwartz φ).toLp 2)
      ((complexifyRealSchwartz φ).toLp 2) = _
  rw [regularisedTensorPhysicalMap_schwartz]
  exact regularisedSchwartzTensor_complexifyReal_toLp ρ ε hε φ

end CKN.Leray

end
