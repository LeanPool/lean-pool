/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBilinearDenseExtension
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBilinearLinear
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzLinear

/-!
# Extension of the regularized tensor to complete Sobolev data

The Schwartz tensor's bilinear H²ᵏ bound extends uniquely to
L² × H²ᵏ with the same operator norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The canonical complete tensor lift of the Schwartz bilinear
regularized nonlinearity is itself bilinear. -/
@[expose]
def regularisedSchwartzTensorBilinearBesselLinear
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (s : ℝ) :
    𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ]
      𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ]
        BesselPotentialSpace L2Vec3 ComplexTensor3 s 2 :=
  (regularisedSchwartzTensorBilinearLinear ρ ε hε).compr₂ₛₗ
    (regularisedTensorBesselSchwartzLinear s)

/-- The bundled Bessel tensor map is the canonical lift of the
regularized Schwartz tensor. -/
theorem regularisedSchwartzTensorBilinearBesselLinear_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (s : ℝ) (g f : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedSchwartzTensorBilinearBesselLinear ρ ε hε s g f =
      regularisedTensorBesselOfSchwartz s
        (regularisedSchwartzTensorBilinear ρ ε hε g f) := rfl

/-- The H²ᵏ tensor estimate on Schwartz fields yields a bounded
bilinear map from spatial L² × complete H²ᵏ into complete tensor H²ᵏ. -/
theorem regularisedSchwartzTensorBilinear_bessel_even_extension_of_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧
      ∀ g f : 𝓢(L2Vec3, ComplexVec3),
        ‖((regularisedSchwartzTensorBilinear ρ ε hε g f).memSobolev
            (s := ((2 * k : ℕ) : ℝ)) (p := 2)).toBesselPotentialSpace‖ ≤
          C * ‖g.toLp 2‖ *
            ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ F : ComplexVectorL2 →L[ℂ]
          BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2 →L[ℂ]
            BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2,
        ‖F‖ ≤ C ∧
          ∀ g f : 𝓢(L2Vec3, ComplexVec3),
            F (g.toLp 2)
                (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f) =
              regularisedTensorBesselOfSchwartz ((2 * k : ℕ) : ℝ)
                (regularisedSchwartzTensorBilinear ρ ε hε g f) := by
  obtain ⟨C, hC, hBound⟩ := hB
  let eV : 𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ] ComplexVectorL2 :=
    (SchwartzMap.toLpCLM ℂ ComplexVec3 2 volume).toLinearMap
  let eW := regularisedBesselSchwartzLinear ((2 * k : ℕ) : ℝ)
  have heV : DenseRange eV := by
    have hSchwartz : DenseRange
        (SchwartzMap.toLpCLM ℝ (E := L2Vec3) ComplexVec3 2 volume) :=
      SchwartzMap.denseRange_toLpCLM (E := L2Vec3)
        (F := ComplexVec3) (μ := volume) ENNReal.ofNat_ne_top
    exact hSchwartz
  have heW : DenseRange eW :=
    regularisedBesselOfSchwartz_denseRange ((2 * k : ℕ) : ℝ)
  have heVapply (g : 𝓢(L2Vec3, ComplexVec3)) : eV g = g.toLp 2 := rfl
  have heWapply (f : 𝓢(L2Vec3, ComplexVec3)) :
      eW f = regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f := rfl
  clear_value eV eW
  have hNorm : ∀ g f : 𝓢(L2Vec3, ComplexVec3),
      ‖regularisedSchwartzTensorBilinearBesselLinear ρ ε hε
          ((2 * k : ℕ) : ℝ) g f‖ ≤ C * ‖eV g‖ * ‖eW f‖ := by
    intro g f
    rw [regularisedSchwartzTensorBilinearBesselLinear_apply,
      heVapply, heWapply]
    exact hBound g f
  obtain ⟨F, hF, hAgree⟩ := regularised_bilinear_dense_extension
    eV eW heV heW
    (regularisedSchwartzTensorBilinearBesselLinear ρ ε hε ((2 * k : ℕ) : ℝ))
    C hC hNorm
  refine ⟨C, hC, F, hF, ?_⟩
  intro g f
  have h := hAgree g f
  rw [heVapply, heWapply,
    regularisedSchwartzTensorBilinearBesselLinear_apply] at h
  exact h

end CKN.Leray

end
