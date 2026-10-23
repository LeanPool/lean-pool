/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! # Randomized inverses of maps of a uniform variable

Disintegration supplies a randomized inverse even when a map has fibers of
positive measure. This is the extra randomness needed to handle atoms in Sklar's theorem.
-/

public section

open MeasureTheory Set Filter Function
open scoped unitInterval

namespace ProbabilityTheory

/-- A measurable map of a uniform variable has a randomized inverse that recovers
the uniform law and inverts the map almost everywhere. -/
theorem exists_randomized_inverse {B : Type*} [MeasurableSpace B] [StandardBorelSpace B]
    (q : I → B) (hq : Measurable q) :
    ∃ g : B → I → I, Measurable (uncurry g) ∧
      ((volume.map q).prod volume).map (uncurry g) = volume ∧
      ∀ᵐ p ∂((volume.map q).prod volume), q (g p.1 p.2) = p.1 := by
  let κ := condDistrib (id : I → I) q volume
  obtain ⟨g, hg, hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let H : B × I → B × I := fun p => (p.1, g p.1 p.2)
  have hH : Measurable H := measurable_fst.prodMk hg
  have hgraph : ((volume.map q).prod volume).map H = (volume.map q) ⊗ₘ κ := by
    ext s hs
    rw [Measure.map_apply hH hs, Measure.prod_apply (hH hs), Measure.compProd_apply hs]
    apply lintegral_congr
    intro b
    rw [← hmap b, Measure.map_apply hg.of_uncurry_left (measurable_prodMk_left hs)]
    rfl
  have hdis : (volume.map q) ⊗ₘ κ = volume.map (fun t : I => (q t, t)) := by
    exact compProd_map_condDistrib hq.aemeasurable measurable_id.aemeasurable
  have hunif : ((volume.map q).prod volume).map (uncurry g) = volume := by
    have hp : Measurable (fun t : I => (q t, t)) := hq.prodMk measurable_id
    have h := congrArg (fun m : Measure (B × I) => m.map Prod.snd) (hgraph.trans hdis)
    rw [Measure.map_map measurable_snd hH,
      Measure.map_map measurable_snd hp] at h
    simpa only [comp_def, H, uncurry_def, Measure.map_id'] using h
  refine ⟨g, hg, hunif, ?_⟩
  have hae : ∀ᵐ p ∂(volume.map (fun t : I => (q t, t))), q p.2 = p.1 := by
    apply (ae_map_iff (hq.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hq.comp measurable_snd) measurable_fst)).mpr
    exact Eventually.of_forall fun _ => rfl
  rw [← hdis, ← hgraph] at hae
  exact ae_of_ae_map hH.aemeasurable hae

end ProbabilityTheory
