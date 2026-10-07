/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorPhysicalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorBesselEmbedding
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzPhysical

/-!
# Compatibility of the Sobolev and physical tensor maps

The bounded tensor map on L² × H²ᵏ represents the bounded physical
bilinear tensor on the underlying spatial L² fields.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete tensor map and the physical L² tensor map agree
on every L² × H²ᵏ pair after taking the physical realization. -/
theorem regularisedBesselTensorMap_physical
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (g : ComplexVectorL2)
    (f : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselTensorMap ρ ε hε k g f) =
    regularisedTensorPhysicalMap ρ ε hε g
      (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity) f) := by
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  let T := regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ) (by positivity)
  let H := regularisedBesselTensorMap ρ ε hε k
  let P := regularisedTensorPhysicalMap ρ ε hε
  have hCore (g₀ f₀ : 𝓢(L2Vec3, ComplexVec3)) :
      T (H (g₀.toLp 2)
        (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f₀)) =
      P (g₀.toLp 2) (E
        (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f₀)) := by
    dsimp only [T, H, P, E]
    rw [regularisedBesselTensorMap_schwartz,
      regularisedTensorBesselSobolevToL2_schwartz,
      regularisedBesselSobolevToL2CLM_apply,
      regularisedBesselSobolevToL2_schwartz,
      regularisedTensorPhysicalMap_schwartz]
  have hDenseL2 : DenseRange
      (SchwartzMap.toLpCLM ℝ (E := L2Vec3) ComplexVec3 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (E := L2Vec3)
      (F := ComplexVec3) (μ := volume) ENNReal.ofNat_ne_top
  have hFixedCore (f₀ : 𝓢(L2Vec3, ComplexVec3)) (g₁ : ComplexVectorL2) :
      T (H g₁ (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f₀)) =
      P g₁ (E (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f₀)) := by
    let u₀ := regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f₀
    refine hDenseL2.induction_on (p := fun x =>
      T (H x u₀) = P x (E u₀)) g₁ ?_ ?_
    · exact isClosed_eq
        (T.comp (H.flip u₀)).continuous
        (P.flip (E u₀)).continuous
    · intro g₀
      exact hCore g₀ f₀
  have hDenseH : DenseRange
      (regularisedBesselSchwartzLinear ((2 * k : ℕ) : ℝ)) :=
    regularisedBesselOfSchwartz_denseRange ((2 * k : ℕ) : ℝ)
  refine hDenseH.induction_on (p := fun u => T (H g u) = P g (E u)) f ?_ ?_
  · exact isClosed_eq
      (T.comp (H g)).continuous
      ((P g).comp E).continuous
  · intro f₀
    exact hFixedCore f₀ g

end CKN.Leray

end
