/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzConvolutionIteratedDerivative

/-!
# Ordered derivative bound for Schwartz mollification

Each finite ordered spatial derivative of the mollified velocity is
uniformly bounded by the input spatial L² norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic LineDeriv

/-- Differentiating the mollified vector field in any finite ordered
directions costs only the L² norm of the corresponding kernel derivative. -/
theorem regularisedSchwartzMollify_iteratedLineDeriv_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) (n : ℕ)
    (m : Fin n → L2Vec3) (x : L2Vec3) :
    ‖∂^{m} (regularisedSchwartzMollify ρ ε hε ψ) x‖ ≤
      ‖(∂^{m} (regularisedComplexMollifierSchwartz ρ ε hε)).toLp 2‖ *
        ‖ψ.toLp 2‖ := by
  rw [regularisedSchwartzMollify,
    regularised_schwartz_convolution_iteratedLineDeriv]
  exact regularised_schwartz_convolution_norm_le _ _ _

end CKN.Leray

end
