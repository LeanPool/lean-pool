/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CubicalClifford

/-!
# Exhaustive classification of the two cubical four-component sectors

The cubical flavor involution commutes with every native cubical transport
generator and with the mass grading.  This file proves the missing converse:
its `+1` and `-1` eigenspaces are exactly the images of the two already
constructed four-component embeddings.  Consequently the eight-corner
fiber is the direct sum of two, and only two, rank-four sectors.

This is an algebraic prediction of the declared cubical root.  It does not
assert that a measurement dynamically selects one sector, nor that the two
sectors are two independently localized particles.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open Complex

/-- Project a cube amplitude to the positive eigenspace of the flavor involution. -/
def cubicalFlavorPlusProjection (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => (amplitude corner + cubicalFlavor amplitude corner) / 2

/-- Project a cube amplitude to the negative eigenspace of the flavor involution. -/
def cubicalFlavorMinusProjection (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => (amplitude corner - cubicalFlavor amplitude corner) / 2

theorem cubical_flavor_projection_decomposition (amplitude : CubicalCell8) :
    (fun corner =>
      cubicalFlavorPlusProjection amplitude corner +
        cubicalFlavorMinusProjection amplitude corner) = amplitude := by
  funext corner
  simp [cubicalFlavorPlusProjection, cubicalFlavorMinusProjection]
  ring

private def cubicalFlavorLinear : CubicalCell8 →ₗ[ℂ] CubicalCell8 where
  toFun := cubicalFlavor
  map_add' first second := by
    funext corner
    simp [cubicalFlavor, mul_add]
  map_smul' scalar amplitude := by
    funext corner
    simp [cubicalFlavor]
    ring

theorem cubical_flavor_plus_projection_is_positive (amplitude : CubicalCell8) :
    cubicalFlavor (cubicalFlavorPlusProjection amplitude) =
      cubicalFlavorPlusProjection amplitude := by
  have hprojection : cubicalFlavorPlusProjection amplitude =
      (2 : ℂ)⁻¹ • (amplitude + cubicalFlavor amplitude) := by
    funext corner
    simp [cubicalFlavorPlusProjection, div_eq_mul_inv, mul_comm]
  rw [hprojection]
  change cubicalFlavorLinear ((2 : ℂ)⁻¹ • (amplitude + cubicalFlavorLinear amplitude)) = _
  have hi : cubicalFlavorLinear (cubicalFlavorLinear amplitude) = amplitude :=
    cubical_flavor_involution amplitude
  rw [map_smul, map_add, hi, add_comm]
  rfl

theorem cubical_flavor_minus_projection_is_negative (amplitude : CubicalCell8) :
    cubicalFlavor (cubicalFlavorMinusProjection amplitude) =
      fun corner => -cubicalFlavorMinusProjection amplitude corner := by
  have hprojection : cubicalFlavorMinusProjection amplitude =
      (2 : ℂ)⁻¹ • (amplitude - cubicalFlavor amplitude) := by
    funext corner
    simp [cubicalFlavorMinusProjection, div_eq_mul_inv, mul_comm]
  rw [hprojection]
  change cubicalFlavorLinear ((2 : ℂ)⁻¹ • (amplitude - cubicalFlavorLinear amplitude)) =
    -((2 : ℂ)⁻¹ • (amplitude - cubicalFlavorLinear amplitude))
  have hi : cubicalFlavorLinear (cubicalFlavorLinear amplitude) = amplitude :=
    cubical_flavor_involution amplitude
  rw [map_smul, map_sub, hi, ← smul_neg, neg_sub]

/-- Four standard coordinates recovered from a positive-flavor amplitude. -/
def cubicalPositiveFlavorRead (amplitude : CubicalCell8) : CubicalCell4
  | 0 => amplitude 5
  | 1 => -amplitude 0
  | 2 => amplitude 1
  | _ => amplitude 4

theorem positive_flavor_is_exactly_plus_embedding
    (amplitude : CubicalCell8) (hflavor : cubicalFlavor amplitude = amplitude) :
    cubicalDiracEmbedPlus (cubicalPositiveFlavorRead amplitude) = amplitude := by
  funext corner
  fin_cases corner
  · exact neg_neg _
  · rfl
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedPlus, cubicalEmbedPlus, standardToCubicalPlus,
      cubicalPositiveFlavorRead]
      using congrFun hflavor 2
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedPlus, cubicalEmbedPlus, standardToCubicalPlus,
      cubicalPositiveFlavorRead]
      using congrFun hflavor 3
  · rfl
  · rfl
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedPlus, cubicalEmbedPlus, standardToCubicalPlus,
      cubicalPositiveFlavorRead]
      using congrFun hflavor 6
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedPlus, cubicalEmbedPlus, standardToCubicalPlus,
      cubicalPositiveFlavorRead]
      using congrFun hflavor 7

theorem negative_flavor_is_exactly_minus_embedding
    (amplitude : CubicalCell8)
    (hflavor : cubicalFlavor amplitude = fun corner => -amplitude corner) :
    cubicalDiracEmbedMinus (cubicalNegativeFlavorRead amplitude) = amplitude := by
  funext corner
  fin_cases corner
  · rfl
  · exact neg_neg _
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedMinus, cubicalEmbedMinus, standardToCubicalMinus,
      cubicalNegativeFlavorRead]
      using congrArg Neg.neg (congrFun hflavor 2)
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedMinus, cubicalEmbedMinus, standardToCubicalMinus,
      cubicalNegativeFlavorRead]
      using congrArg Neg.neg (congrFun hflavor 3)
  · rfl
  · rfl
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedMinus, cubicalEmbedMinus, standardToCubicalMinus,
      cubicalNegativeFlavorRead]
      using congrArg Neg.neg (congrFun hflavor 6)
  · simpa [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2, cubicalBit2,
      cubicalDiracEmbedMinus, cubicalEmbedMinus, standardToCubicalMinus,
      cubicalNegativeFlavorRead]
      using congrArg Neg.neg (congrFun hflavor 7)

theorem cubical_flavor_copies_intersect_only_at_zero
    (amplitude : CubicalCell8)
    (hplus : cubicalFlavor amplitude = amplitude)
    (hminus : cubicalFlavor amplitude = fun corner => -amplitude corner) :
    amplitude = 0 := by
  funext corner
  have h := congrFun (hplus.symm.trans hminus) corner
  simp only [Pi.zero_apply]
  have hzero : amplitude corner - (-amplitude corner) = 0 :=
    sub_eq_zero.mpr h
  linear_combination (1 / 2 : ℂ) * hzero

/-- The decomposition of the oriented cube into its two four-component flavor eigenspaces. -/
structure CubicalFlavorClassificationCertificate : Prop where
  everyAmplitudeDecomposes : ∀ amplitude,
    (fun corner =>
      cubicalFlavorPlusProjection amplitude corner +
        cubicalFlavorMinusProjection amplitude corner) = amplitude
  positiveProjectionHasPositiveFlavor : ∀ amplitude,
    cubicalFlavor (cubicalFlavorPlusProjection amplitude) =
      cubicalFlavorPlusProjection amplitude
  negativeProjectionHasNegativeFlavor : ∀ amplitude,
    cubicalFlavor (cubicalFlavorMinusProjection amplitude) =
      fun corner => -cubicalFlavorMinusProjection amplitude corner
  positiveCopyIsExhaustive : ∀ amplitude,
    cubicalFlavor amplitude = amplitude →
      cubicalDiracEmbedPlus (cubicalPositiveFlavorRead amplitude) = amplitude
  negativeCopyIsExhaustive : ∀ amplitude,
    cubicalFlavor amplitude = (fun corner => -amplitude corner) →
      cubicalDiracEmbedMinus (cubicalNegativeFlavorRead amplitude) = amplitude
  positiveEmbeddingIsInjective : Function.Injective cubicalDiracEmbedPlus
  negativeEmbeddingIsInjective : Function.Injective cubicalDiracEmbedMinus
  copyIntersectionIsZero : ∀ amplitude,
    cubicalFlavor amplitude = amplitude →
    cubicalFlavor amplitude = (fun corner => -amplitude corner) →
      amplitude = 0

theorem cubical_flavor_classification :
    CubicalFlavorClassificationCertificate where
  everyAmplitudeDecomposes := cubical_flavor_projection_decomposition
  positiveProjectionHasPositiveFlavor :=
    cubical_flavor_plus_projection_is_positive
  negativeProjectionHasNegativeFlavor :=
    cubical_flavor_minus_projection_is_negative
  positiveCopyIsExhaustive := positive_flavor_is_exactly_plus_embedding
  negativeCopyIsExhaustive := negative_flavor_is_exactly_minus_embedding
  positiveEmbeddingIsInjective := cubical_dirac_embed_plus_injective
  negativeEmbeddingIsInjective := cubical_dirac_embed_minus_injective
  copyIntersectionIsZero := cubical_flavor_copies_intersect_only_at_zero

end
end LeanDirac.V2
