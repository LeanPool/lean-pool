/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine

/-! # Translation of the affine support, intrinsic law, and barycenter -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology

namespace FunctionalInequalities.Probability


universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

  (μ : ProbabilityMeasure E) (b : E)

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- On the affine support, the intrinsic coordinate of a point is its displacement from the chosen
support point. -/
theorem coe_intrinsicMap_of_mem {x : E} (hx : x ∈ affineSupport μ) :
    (intrinsicMap μ x : E) = x - supportPoint μ := by
  have hret : retraction μ x = ⟨x, hx⟩ := Subtype.ext (coe_retraction_of_mem μ hx)
  rw [intrinsicMap, hret, coordinateEquiv, AffineIsometryEquiv.coe_vaddConst_symm]
  rfl

/-- The affine support of the translated law is the translate of the affine support. -/
theorem affineSupport_translateLaw :
    affineSupport (translateLaw μ b) =
      (affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap := by
  apply le_antisymm
  · apply affineSupport_le_of_ae_mem
    · exact
        ((affineSupport μ).map
            (AffineEquiv.constVAdd ℝ E b).toAffineMap).closed_of_finiteDimensional
    · rw [coe_translateLaw]
      refine
        (ae_map_iff (measurable_const_add b).aemeasurable
              ((affineSupport μ).map
                  (AffineEquiv.constVAdd ℝ E
                      b).toAffineMap).closed_of_finiteDimensional.measurableSet).2
          ?_
      filter_upwards [ae_mem_affineSupport μ] with x hx
      exact ⟨x, hx, rfl⟩
  · rw [AffineSubspace.map_le_iff_le_comap]
    apply affineSupport_le_of_ae_mem
    · change IsClosed ((fun x : E ↦ b + x) ⁻¹' (affineSupport (translateLaw μ b) : Set E))
      exact (isClosed_affineSupport _).preimage (continuous_const.add continuous_id)
    · have h := ae_mem_affineSupport (translateLaw μ b)
      rw [coe_translateLaw] at h
      filter_upwards [ae_of_ae_map (measurable_const_add b).aemeasurable h] with x hx
      exact hx

/-- Translation does not change the direction of the affine support. -/
theorem direction_affineSupport_translateLaw :
    (affineSupport (translateLaw μ b)).direction = (affineSupport μ).direction := by
  rw [affineSupport_translateLaw, AffineSubspace.map_direction]
  simp [Submodule.map_id]

/-- The linear isometric identification of the two (equal) direction submodules. -/
def translateDirectionEquiv :
    (affineSupport μ).direction ≃ₗᵢ[ℝ] (affineSupport (translateLaw μ b)).direction :=
  LinearIsometryEquiv.ofEq _ _ (direction_affineSupport_translateLaw μ b).symm

@[simp]
theorem coe_translateDirectionEquiv (v : (affineSupport μ).direction) :
    (translateDirectionEquiv μ b v : E) = v :=
  LinearIsometryEquiv.coe_ofEq_apply _ _

/-- The translate of the chosen support point lies in the translated affine support. -/
theorem add_supportPoint_mem_affineSupport_translateLaw :
    b + supportPoint μ ∈ affineSupport (translateLaw μ b) := by
  rw [affineSupport_translateLaw]
  exact ⟨supportPoint μ, (origin μ).property, rfl⟩

/-- The shift between the two intrinsic coordinate presentations: the translated support point of
`μ` minus the support point chosen for the translated law, as a direction vector. -/
def translateShift : (affineSupport (translateLaw μ b)).direction :=
  ⟨b + supportPoint μ - supportPoint (translateLaw μ b),
    AffineSubspace.vsub_mem_direction (add_supportPoint_mem_affineSupport_translateLaw μ b)
      (origin (translateLaw μ b)).property⟩

@[simp]
theorem coe_translateShift :
    (translateShift μ b : E) = b + supportPoint μ - supportPoint (translateLaw μ b) := rfl

/-- On the affine support, intrinsic coordinates of the translated law are the shifted isometric
image of the intrinsic coordinates of `μ`. -/
theorem intrinsicMap_translateLaw {x : E} (hx : x ∈ affineSupport μ) :
    intrinsicMap (translateLaw μ b) (b + x) =
      translateShift μ b + translateDirectionEquiv μ b (intrinsicMap μ x) := by
  apply Subtype.ext
  have hx' : b + x ∈ affineSupport (translateLaw μ b) := by
    rw [affineSupport_translateLaw]
    exact ⟨x, hx, rfl⟩
  rw [coe_intrinsicMap_of_mem _ hx', Submodule.coe_add, coe_translateDirectionEquiv,
    coe_intrinsicMap_of_mem μ hx, coe_translateShift]
  abel

/-- The intrinsic law of the translated law is the translate, inside the direction space, of the
isometric image of the intrinsic law of `μ`. -/
theorem intrinsicMeasure_translateLaw :
    intrinsicMeasure (translateLaw μ b) =
      translateLaw (mapLinearIsometryEquiv (intrinsicMeasure μ) (translateDirectionEquiv μ b))
        (translateShift μ b) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [intrinsicMeasure, ProbabilityMeasure.toMeasure_map, coe_translateLaw,
    coe_mapLinearIsometryEquiv]
  rw [Measure.map_map (measurable_intrinsicMap _) (measurable_const_add b),
    Measure.map_map (measurable_const_add _)
      (translateDirectionEquiv μ b).continuous.measurable,
    Measure.map_map
      ((measurable_const_add _).comp (translateDirectionEquiv μ b).continuous.measurable)
      (measurable_intrinsicMap μ)]
  refine Measure.map_congr ?_
  filter_upwards [ae_mem_affineSupport μ] with x hx
  simp only [Function.comp_apply]
  exact intrinsicMap_translateLaw μ b hx

end FunctionalInequalities.Probability

namespace FunctionalInequalities.Probability

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]


section TranslationMeans

omit [FiniteDimensional ℝ V]
/-- The barycenter of a translated law is the translated barycenter. -/
theorem integral_id_translateLaw (ν : ProbabilityMeasure V) (hint : Integrable id (ν : Measure V))
    (c : V) : ∫ x, x ∂(translateLaw ν c : Measure V) = c + ∫ x, x ∂(ν : Measure V) := by
  rw [coe_translateLaw, integral_map (measurable_const_add c).aemeasurable
    continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V ↦ x) (ν : Measure V) := hint
  rw [integral_add (integrable_const c) hint', integral_const, probReal_univ, one_smul]

/-- Translating by the negative barycenter centers the law. -/
theorem integral_id_translateLaw_neg_integral (ν : ProbabilityMeasure V)
    (hint : Integrable id (ν : Measure V)) :
    ∫ x, x ∂(translateLaw ν (-∫ x, x ∂(ν : Measure V)) : Measure V) = 0 := by
  rw [integral_id_translateLaw ν hint]
  simp

end TranslationMeans

end FunctionalInequalities.Probability
