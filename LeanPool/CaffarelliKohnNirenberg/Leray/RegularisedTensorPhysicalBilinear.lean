/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBilinearDenseExtension
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBilinearLinear
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorL2Bound

/-!
# Physical L² extension of the regularized tensor

The regularized bilinear Schwartz tensor has a bounded extension to two
complex spatial L² inputs.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The L² class of the Schwartz tensor is complex bilinear in its two inputs. -/
@[expose]
def regularisedSchwartzTensorBilinearL2Linear
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ]
      𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ] ComplexTensorL2 :=
  (regularisedSchwartzTensorBilinearLinear ρ ε hε).compr₂ₛₗ
    (SchwartzMap.toLpCLM ℂ ComplexTensor3 2 volume).toLinearMap

/-- The bilinear L² map evaluates to the canonical Schwartz tensor class. -/
theorem regularisedSchwartzTensorBilinearL2Linear_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (g f : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedSchwartzTensorBilinearL2Linear ρ ε hε g f =
      (regularisedSchwartzTensorBilinear ρ ε hε g f).toLp 2 := rfl

/-- A fixed L² bound selects a continuous bilinear extension of the
regularized tensor on physical complex velocity fields. -/
theorem regularisedSchwartzTensorBilinear_L2_extension
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ F : ComplexVectorL2 →L[ℂ] ComplexVectorL2 →L[ℂ] ComplexTensorL2,
        ‖F‖ ≤ C ∧
          ∀ g f : 𝓢(L2Vec3, ComplexVec3),
            F (g.toLp 2) (f.toLp 2) =
              (regularisedSchwartzTensorBilinear ρ ε hε g f).toLp 2 := by
  obtain ⟨C, hC, hBound⟩ :=
    regularisedSchwartzTensorBilinear_L2_norm_le ρ ε hε
  let e : 𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ] ComplexVectorL2 :=
    (SchwartzMap.toLpCLM ℂ ComplexVec3 2 volume).toLinearMap
  have he : DenseRange e := by
    have hSchwartz : DenseRange
        (SchwartzMap.toLpCLM ℝ (E := L2Vec3) ComplexVec3 2 volume) :=
      SchwartzMap.denseRange_toLpCLM (E := L2Vec3)
        (F := ComplexVec3) (μ := volume) ENNReal.ofNat_ne_top
    exact hSchwartz
  have heApply (g : 𝓢(L2Vec3, ComplexVec3)) : e g = g.toLp 2 := rfl
  clear_value e
  have hNorm : ∀ g f : 𝓢(L2Vec3, ComplexVec3),
      ‖regularisedSchwartzTensorBilinearL2Linear ρ ε hε g f‖ ≤
        C * ‖e g‖ * ‖e f‖ := by
    intro g f
    rw [regularisedSchwartzTensorBilinearL2Linear_apply,
      heApply, heApply]
    exact hBound g f
  obtain ⟨F, hF, hAgree⟩ := regularised_bilinear_dense_extension
    e e he he (regularisedSchwartzTensorBilinearL2Linear ρ ε hε)
    C hC hNorm
  refine ⟨C, hC, F, hF, ?_⟩
  intro g f
  have h := hAgree g f
  simpa only [heApply,
    regularisedSchwartzTensorBilinearL2Linear_apply] using h

end CKN.Leray

end
