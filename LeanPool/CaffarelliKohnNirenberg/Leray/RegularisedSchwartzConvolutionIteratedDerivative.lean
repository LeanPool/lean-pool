/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzConvolutionDerivative

/-!
# Iterated derivatives of Schwartz convolution

Every finite ordered spatial derivative may be transferred from the
convolution to its scalar Schwartz kernel.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic LineDeriv Fin

/-- All finite ordered line derivatives commute with convolution by a
scalar Schwartz kernel. -/
theorem regularised_schwartz_convolution_iteratedLineDeriv
    (κ : 𝓢(L2Vec3, ℂ)) (ψ : 𝓢(L2Vec3, ComplexVec3))
    (n : ℕ) (m : Fin n → L2Vec3) :
    ∂^{m} (SchwartzMap.convolution
      (ContinuousLinearMap.lsmul ℂ ℂ) κ ψ) =
      SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ) (∂^{m} κ) ψ := by
  induction n generalizing κ with
  | zero => simp
  | succ n ih =>
      rw [iteratedLineDerivOp_succ_left,
        ih κ (tail m),
        regularised_schwartz_convolution_lineDeriv,
        iteratedLineDerivOp_succ_left]

end CKN.Leray

end
