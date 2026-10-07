/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorPointwiseBound

/-!
# L² bound for the bilinear Schwartz tensor

The pointwise mollifier bound and the rank-one tensor norm give a
uniform bilinear estimate in the spatial L² carrier.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- One mollifier constant controls the L² norm of the two-input
regularized tensor of Schwartz velocity fields. -/
theorem regularisedSchwartzTensorBilinear_L2_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g f : 𝓢(L2Vec3, ComplexVec3),
        ‖(regularisedSchwartzTensorBilinear ρ ε hε g f).toLp 2‖ ≤
          C * ‖g.toLp 2‖ * ‖f.toLp 2‖ := by
  obtain ⟨C, hC, hPoint⟩ :=
    regularisedSchwartzTensorBilinear_pointwise_norm_le ρ ε hε
  refine ⟨C, hC, ?_⟩
  intro g f
  let T := regularisedSchwartzTensorBilinear ρ ε hε g f
  have hTrep : (T.toLp 2 : ComplexTensorL2) =ᵐ[volume]
      (T : L2Vec3 → ComplexTensor3) := T.coeFn_toLp 2 volume
  have hFrep : (f.toLp 2 : ComplexVectorL2) =ᵐ[volume]
      (f : L2Vec3 → ComplexVec3) := f.coeFn_toLp 2 volume
  have hpoint : ∀ᵐ x ∂volume,
      ‖(T.toLp 2 : ComplexTensorL2) x‖ ≤
        C * ‖g.toLp 2‖ * ‖(f.toLp 2 : ComplexVectorL2) x‖ := by
    filter_upwards [hTrep, hFrep] with x hTx hFx
    rw [hTx, hFx]
    exact hPoint g f x
  exact Lp.norm_le_mul_norm_of_ae_le_mul hpoint

end CKN.Leray

end
