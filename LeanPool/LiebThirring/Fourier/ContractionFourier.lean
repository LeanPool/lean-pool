/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionTensor
public import LeanPool.LiebThirring.Fourier.Functoriality

/-!
# Fourier invariance of tensor contraction

Outer Fourier transforms preserve the contraction against a spatial-and-spin
one-particle vector. These identities hold for arbitrary complete complex
Hilbert fibers and require no integrability beyond L².
-/

public section

open MeasureTheory
open scoped FourierTransform

namespace LiebThirring.Fourier

variable {V ι H : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Outer Fourier transforms act on the spatial factor of a tensor insertion. -/
theorem fourier_tensorInsertion
    (f : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure V)) (v : H) :
    𝓕 (tensorInsertion (H := H) f v) = tensorInsertion (H := H) (𝓕 f) v := by
  change 𝓕 ((tensorInsertionBilinear v).compLp f) =
    (tensorInsertionBilinear v).compLp (𝓕 f)
  exact fourier_compLp _ f

/-- Simultaneous outer Fourier transforms leave tensor contraction unchanged. -/
theorem tensorContraction_fourier
    (f : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure V))
    (h : Lp (PiLp 2 (fun _ : ι => H)) 2 (volume : Measure V)) :
    tensorContraction (H := H) (𝓕 f) (𝓕 h) = tensorContraction (H := H) f h := by
  apply ext_inner_left ℂ
  intro v
  change inner ℂ v ((tensorInsertion (H := H) (𝓕 f)).adjoint (𝓕 h)) =
    inner ℂ v ((tensorInsertion (H := H) f).adjoint h)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← fourier_tensorInsertion]
  exact Lp.inner_fourier_eq _ _

end LiebThirring.Fourier
end
