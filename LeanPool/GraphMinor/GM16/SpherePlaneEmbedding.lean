/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.Surface.Jordan
import Mathlib.Analysis.Complex.Basic

/-!
# A coordinate plane in the sphere

Use the sphere's defining homeomorphism with the one-point
compactification of the Euclidean plane. The inclusion of the plane
is an open embedding. Real coordinate pairs identify with that plane,
so the finite wall drawing of XVI (4.2) can be placed in any sphere.
-/

public section
namespace GraphMinor.GM16
open Topology GraphMinor.Surface
universe u

/-- Every sphere contains an embedded copy of the real coordinate
plane, as used for the drawing in XVI (4.2), page 53. -/
theorem exists_plane_openEmbedding_of_isSphere {S : Type u} [TopologicalSpace S]
    (hS : IsSphere S) : ∃ f : (ℝ × ℝ) → S, IsOpenEmbedding f := by
  obtain ⟨h⟩ := hS
  let e : (ℝ × ℝ) ≃ₜ EuclideanPlane :=
    Complex.equivRealProdCLM.toHomeomorph.symm.trans complexPlane.toHomeomorph
  let f : (ℝ × ℝ) → S := fun x => h.symm ((e x : EuclideanPlane) : OnePoint EuclideanPlane)
  exact ⟨f,h.symm.isOpenEmbedding.comp (OnePoint.isOpenEmbedding_coe.comp e.isOpenEmbedding)⟩

/-- Every sphere contains an embedded coordinate plane. -/
theorem exists_plane_embedding_of_isSphere {S : Type u} [TopologicalSpace S]
    (hS : IsSphere S) : ∃ f : (ℝ × ℝ) → S, IsEmbedding f := by
  obtain ⟨f,hf⟩ := exists_plane_openEmbedding_of_isSphere hS
  exact ⟨f,hf.isEmbedding⟩

end GraphMinor.GM16
