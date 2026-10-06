/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.Definitions

/-!
# Coarse-graining support: Support.Sobolev.Fractional.DefinitionsAPI

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Additional API for the fractional Sobolev seminorm

Reuse-surface lemmas that are not needed by the `W^{s,p}` versus `B^s_{p,p}`
comparison proofs themselves:

* the `p = ∞` Hölder-endpoint characterization;
* swap symmetry of the unnormalized `Set`-variant (the kernel is odd under
  the pair swap, the seminorm even);
* the cube/`Set` relation (the `⨍∫` normalization is a volume factor at
  power `1/p`);
* translation covariance along the triadic lattice (`translateCube`), via
  the translation pushforward of the product measure.

A.e.-congruence lemmas live in `CongruenceAE.lean`.
-/

namespace HCPolySupport
namespace Gagliardo

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At `p = ∞` the fractional Sobolev seminorm is the essential Hölder
`C^{0,s}` seminorm: the kernel exponent collapses to `s` and the `eLpNorm`
becomes an essential supremum. -/
theorem cubeGagliardoESeminorm_top (Q : TriadicCube d) (s : ℝ) (u : Vec d → E)
    (hu : AEStronglyMeasurable (gagliardoKernel s ∞ u) (gagliardoCubeMeasure Q)) :
    cubeGagliardoESeminorm Q s ∞ u =
      essSup (fun z : Vec d × Vec d =>
        ‖(dist z.1 z.2 ^ (-s)) • (u z.1 - u z.2)‖ₑ)
        (gagliardoCubeMeasure Q) := by
  rw [Internal.cubeGagliardoESeminorm_def, eLpNorm_exponent_top hu,
    eLpNormEssSup]
  simp only [gagliardoKernel, kernelExponent_top]

/-- Swap symmetry of the unnormalized seminorm: precomposing the kernel with
the pair swap changes nothing, since the kernel is odd under the swap and the
seminorm is even. -/
theorem gagliardoESeminormOn_comp_swap (A : Set (Vec d)) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → E) :
    eLpNorm (gagliardoKernel s p u ∘ Prod.swap) p
        ((MeasureTheory.volume.restrict A).prod
          (MeasureTheory.volume.restrict A)) =
      gagliardoESeminormOn A s p u := by
  have hswap : gagliardoKernel s p u ∘ Prod.swap =
      -(gagliardoKernel (d := d) s p u) := by
    funext z
    change gagliardoKernel s p u (z.2, z.1) = -(gagliardoKernel s p u z)
    rw [gagliardoKernel_apply, gagliardoKernel_apply]
    simp only [dist_comm z.2 z.1]
    rw [show u z.2 - u z.1 = -(u z.1 - u z.2) by abel, smul_neg]
  rw [hswap, gagliardoESeminormOn]
  exact eLpNorm_neg _ _ _

/-- Relation between the cube-normalized seminorm and the unnormalized
`Set`-variant: the manuscript's `⨍∫` normalization contributes the volume
factor at power `1/p`. -/
theorem cubeGagliardoESeminorm_eq_smul_gagliardoESeminormOn
    (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞} (u : Vec d → E) :
    cubeGagliardoESeminorm Q s p u =
      ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p).toReal •
        gagliardoESeminormOn (HCPolySupport.cubeSet Q) s p u := by
  have : SFinite (MeasureTheory.volume.restrict (HCPolySupport.cubeSet Q)) :=
    inferInstance
  rw [Internal.cubeGagliardoESeminorm_def, gagliardoESeminormOn,
    gagliardoCubeMeasure, HCPolySupport.normalizedCubeMeasure,
    HCPolySupport.cubeMeasure, Measure.prod_smul_left,
    eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos Q))).ne']

section Translation

/-- The real translation vector realizing `translateCube shift Q`. -/
@[expose]
noncomputable def cubeShiftVector (shift : Fin d → ℤ) (Q : TriadicCube d) :
    Vec d :=
  fun i => (shift i : ℝ) * cubeScaleFactor Q

/-- Translation covariance of the fractional Sobolev seminorm: translating
the cube matches precomposing with the translation, for every exponent
`p`. -/
theorem cubeGagliardoESeminorm_translate (shift : Fin d → ℤ)
    (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞}
    (u : Vec d → E) :
    cubeGagliardoESeminorm (translateCube shift Q) s p u =
      cubeGagliardoESeminorm Q s p
        (fun x => u (x + cubeShiftVector shift Q)) := by
  set v := cubeShiftVector shift Q with hv
  set T : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight v with hT
  have hTapp : ∀ x, T x = x + v := fun x => rfl
  -- volume is translation invariant
  have hmapT : Measure.map T MeasureTheory.volume = MeasureTheory.volume := by
    have hco : (⇑T : Vec d → Vec d) = (· + v) := rfl
    rw [hco]
    exact (measurePreserving_add_right MeasureTheory.volume v).map_eq
  -- the translated cube's restricted volume is the pushforward
  have hpre : (⇑T) ⁻¹' HCPolySupport.cubeSet (translateCube shift Q) =
      HCPolySupport.cubeSet Q := by
    ext x
    simp only [Set.mem_preimage, hTapp, mem_cubeSet_translateCube_iff]
    have : x + v - (fun i => (shift i : ℝ) * cubeScaleFactor Q) = x := by
      funext i
      simp [hv, cubeShiftVector]
    rw [this]
  have hres : MeasureTheory.volume.restrict
      (HCPolySupport.cubeSet (translateCube shift Q)) =
      Measure.map T (MeasureTheory.volume.restrict (HCPolySupport.cubeSet Q)) := by
    rw [← hpre, ← Measure.restrict_map T.measurable
      (HCPolySupport.measurableSet_cubeSet (translateCube shift Q)), hmapT]
  -- volumes agree
  have hvol : cubeVolume (translateCube shift Q) = cubeVolume Q := rfl
  -- the Gagliardo product measure is the pushforward under the pair translation
  have : SFinite (MeasureTheory.volume.restrict (HCPolySupport.cubeSet Q)) :=
    inferInstance
  have hprod : gagliardoCubeMeasure (translateCube shift Q) =
      Measure.map (Prod.map ⇑T ⇑T) (gagliardoCubeMeasure Q) := by
    rw [gagliardoCubeMeasure, gagliardoCubeMeasure,
      HCPolySupport.normalizedCubeMeasure, HCPolySupport.normalizedCubeMeasure,
      HCPolySupport.cubeMeasure, HCPolySupport.cubeMeasure, hvol, hres,
      Measure.prod_smul_left, Measure.prod_smul_left,
      Measure.map_prod_map _ _ T.measurable T.measurable,
      Measure.map_smul _ (T.measurable.prodMap T.measurable).aemeasurable]
  have hMP : MeasureTheory.MeasurePreserving (⇑(T.prodCongr T))
      (gagliardoCubeMeasure Q) (gagliardoCubeMeasure (translateCube shift Q)) := by
    refine ⟨(T.prodCongr T).measurable, ?_⟩
    rw [hprod]
    rfl
  -- kernel covariance under the pair translation
  have hker : ∀ z : Vec d × Vec d,
      gagliardoKernel s p u ((T.prodCongr T) z) =
        gagliardoKernel s p (fun x => u (x + v)) z := by
    intro z
    change gagliardoKernel s p u (T z.1, T z.2) = _
    rw [gagliardoKernel_apply, gagliardoKernel_apply, hTapp, hTapp,
      dist_add_right]
  -- conclude through the pushforward under the pair translation
  rw [Internal.cubeGagliardoESeminorm_def, Internal.cubeGagliardoESeminorm_def,
    ← hMP.map_eq, (T.prodCongr T).measurableEmbedding.eLpNorm_map_measure]
  congr 1
  funext z
  exact hker z

end Translation

end

end Gagliardo
end HCPolySupport
