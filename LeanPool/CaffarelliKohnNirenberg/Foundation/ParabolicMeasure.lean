/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# The parabolic-point measure and product coordinates

parabolicHomeomorph identifies CKN's ParabolicPoint with `Vec3 × ℝ`; it
preserves the Lebesgue measures in both directions.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic

namespace CKN

/-- The CKN parabolic measure transported through the product-coordinate homeomorphism. -/
theorem parabolicHomeomorphSymm_measurePreserving :
    MeasurePreserving parabolicHomeomorph.symm
      (volume : Measure (Vec3 × ℝ)) (volume : Measure ParabolicPoint) := by
  constructor
  · exact parabolicHomeomorph.symm.measurable
  · have hfun : (parabolicHomeomorph.symm : Vec3 × ℝ → ParabolicPoint) =
      (fun q : Vec3 × ℝ => (q : ParabolicPoint)) := by
        funext q
        rfl
    rw [hfun]
    change Measure.map (id : Vec3 × ℝ → Vec3 × ℝ) (volume : Measure (Vec3 × ℝ)) = volume
    exact Measure.map_id

/-- Product Lebesgue measure transported to CKN's parabolic-point measure. -/
theorem parabolicHomeomorph_measurePreserving :
    MeasurePreserving parabolicHomeomorph
      (volume : Measure ParabolicPoint) (volume : Measure (Vec3 × ℝ)) := by
  constructor
  · exact parabolicHomeomorph.measurable
  · have hfun : (parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) =
      (fun p : ParabolicPoint => (p.1, p.2)) := by
        funext p
        rfl
    rw [hfun]
    change Measure.map (id : Vec3 × ℝ → Vec3 × ℝ) (volume : Measure (Vec3 × ℝ)) = volume
    exact Measure.map_id

/-- Set integrals on a space-time product agree in CKN and product coordinates. -/
theorem setIntegral_parabolic_to_product
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ} :
    (∫ p in spaceTimeSet Ω I, F p ∂(volume : Measure ParabolicPoint)) =
      ∫ q in Ω ×ˢ I, F (parabolicHomeomorph.symm q)
        ∂(volume : Measure (Vec3 × ℝ)) := by
  have himage : parabolicHomeomorph '' spaceTimeSet Ω I = Ω ×ˢ I := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hq
      refine ⟨parabolicHomeomorph.symm q, ?_, ?_⟩
      · exact hq
      · exact parabolicHomeomorph.apply_symm_apply q
  have htrans := parabolicHomeomorph_measurePreserving.setIntegral_image_emb
    parabolicHomeomorph.measurableEmbedding
    (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q)) (spaceTimeSet Ω I)
  rw [himage] at htrans
  have hright :
      (∫ p in spaceTimeSet Ω I,
        F (parabolicHomeomorph.symm (parabolicHomeomorph p))
          ∂(volume : Measure ParabolicPoint)) =
      ∫ p in spaceTimeSet Ω I, F p ∂(volume : Measure ParabolicPoint) := by
    apply integral_congr_ae
    filter_upwards [] with p
    exact congrArg F (parabolicHomeomorph.left_inv p)
  exact hright.symm.trans htrans.symm

/-- Each coordinate of a locally integrable finite-product-valued function is
locally integrable. -/
theorem locallyIntegrableOn_pi_eval
    {X ι E : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set X} {f : X → ι → E} {μ : Measure X}
    (hf : LocallyIntegrableOn f s μ) (i : ι) :
    LocallyIntegrableOn (fun x => f x i) s μ := by
  intro x hx
  rcases hf x hx with ⟨t, htx, hfield⟩
  refine ⟨t, htx, ?_⟩
  have hcomponentMeasurable : AEStronglyMeasurable (fun y => f y i) (μ.restrict t) :=
    (continuous_apply i).comp_aestronglyMeasurable hfield.1
  have hcomponentBound : ∀ᵐ y ∂(μ.restrict t), ‖f y i‖ ≤ ‖‖f y‖‖ := by
    filter_upwards [] with y
    calc
      ‖f y i‖ ≤ ‖f y‖ := norm_le_pi_norm (f y) i
      _ = ‖‖f y‖‖ := by simp
  exact hfield.norm.mono hcomponentMeasurable hcomponentBound

end CKN
