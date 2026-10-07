/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBesselExtension
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBessel

/-!
# The bounded regularized tensor map on complete Sobolev spaces

The Schwartz estimate and the dense bilinear extension select one
bounded tensor map on L² × H²ᵏ.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

theorem regularisedBesselTensorExtension_exists
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ F : ComplexVectorL2 →L[ℂ]
          BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2 →L[ℂ]
            BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2,
        ‖F‖ ≤ C ∧
          ∀ g f : 𝓢(L2Vec3, ComplexVec3),
            F (g.toLp 2)
                (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f) =
              regularisedTensorBesselOfSchwartz ((2 * k : ℕ) : ℝ)
                (regularisedSchwartzTensorBilinear ρ ε hε g f) :=
  regularisedSchwartzTensorBilinear_bessel_even_extension_of_bound
    ρ ε hε k
    (regularisedSchwartzTensorBilinear_bessel_even_norm_le ρ ε hε k)

/-- A finite nonnegative operator bound for the complete regularized
tensor map at even Sobolev order. -/
@[expose]
def regularisedBesselTensorConstant
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) : ℝ :=
  Classical.choose (regularisedBesselTensorExtension_exists ρ ε hε k)

/-- The complete H²ᵏ regularized tensor map, linear in both the
spatial L² input and the complete H²ᵏ input. -/
@[expose]
def regularisedBesselTensorMap
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) :
    ComplexVectorL2 →L[ℂ]
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2 →L[ℂ]
        BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2 :=
  Classical.choose
    (Classical.choose_spec (regularisedBesselTensorExtension_exists ρ ε hε k)).2

/-- The chosen tensor operator has its advertised nonnegative bound. -/
theorem regularisedBesselTensorMap_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) :
    0 ≤ regularisedBesselTensorConstant ρ ε hε k ∧
      ‖regularisedBesselTensorMap ρ ε hε k‖ ≤
        regularisedBesselTensorConstant ρ ε hε k := by
  constructor
  · exact (Classical.choose_spec
      (regularisedBesselTensorExtension_exists ρ ε hε k)).1
  · exact (Classical.choose_spec
      (Classical.choose_spec
        (regularisedBesselTensorExtension_exists ρ ε hε k)).2).1

/-- On Schwartz data, the complete tensor map equals the canonical
Bessel lift of the original Schwartz product. -/
theorem regularisedBesselTensorMap_schwartz
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (g f : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedBesselTensorMap ρ ε hε k (g.toLp 2)
        (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f) =
      regularisedTensorBesselOfSchwartz ((2 * k : ℕ) : ℝ)
        (regularisedSchwartzTensorBilinear ρ ε hε g f) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (regularisedBesselTensorExtension_exists ρ ε hε k)).2).2 g f

end CKN.Leray

end
