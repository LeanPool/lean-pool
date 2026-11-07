/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.Basic
import LeanPool.Copula.Distribution.RandomizedInverse

/-! # Lifting joint laws through marginal sampling maps -/

public section

open MeasureTheory Set Filter Function
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- If each coordinate law can be sampled from a uniform variable, a joint law
can be lifted to a copula through those sampling maps. -/
theorem exists_lift {d : ℕ} {B : Type*} [MeasurableSpace B] [StandardBorelSpace B]
    (μ : ProbabilityMeasure (Fin d → B)) (q : Fin d → I → B) (hq : ∀ i, Measurable (q i))
    (hqm : ∀ i, volume.map (q i) = μ.toMeasure.map (fun x => x i)) :
    ∃ C : Copula d, C.toMeasure.map (fun u i => q i (u i)) = μ.toMeasure := by
  choose g hg hgm hgi using fun i => exists_randomized_inverse (q i) (hq i)
  let P : ProbabilityMeasure ((Fin d → B) × I) := ⟨μ.toMeasure.prod volume, inferInstance⟩
  let U : (Fin d → B) × I → Fin d → I := fun p i => g i (p.1 i) p.2
  have hproj (i : Fin d) : Measurable (fun p : (Fin d → B) × I => (p.1 i, p.2)) := by
    fun_prop
  have hproj_map (i : Fin d) :
      P.toMeasure.map (fun p => (p.1 i, p.2)) = (volume.map (q i)).prod volume := by
    rw [hqm]
    change (μ.toMeasure.prod volume).map (Prod.map (fun x => x i) id) = _
    have h := Measure.map_prod_map μ.toMeasure (volume : Measure I)
      (measurable_pi_apply i) measurable_id
    simpa only [Measure.map_id] using h.symm
  have hU : Measurable U := by
    apply Measurable.of_eval
    intro i
    exact (hg i).comp (hproj i)
  have hUm (i : Fin d) : P.toMeasure.map (fun p => U p i) = volume := by
    calc
      _ = (P.toMeasure.map (fun p => (p.1 i, p.2))).map (uncurry (g i)) :=
        (Measure.map_map (hg i) (hproj i)).symm
      _ = volume := by rw [hproj_map, hgm]
  let C := ofMap P U hU hUm
  refine ⟨C, ?_⟩
  have hrecover (i : Fin d) : ∀ᵐ p ∂P.toMeasure, q i (U p i) = p.1 i := by
    have h := hgi i
    rw [← hproj_map i] at h
    exact ae_of_ae_map (hproj i).aemeasurable h
  have hall : (fun p => fun i => q i (U p i)) =ᵐ[P.toMeasure] Prod.fst := by
    filter_upwards [ae_all_iff.mpr hrecover] with p hp
    exact funext hp
  change (P.toMeasure.map U).map (fun u i => q i (u i)) = _
  have hQ : Measurable (fun u : Fin d → I => fun i => q i (u i)) :=
    Measurable.of_eval fun i => (hq i).comp (measurable_pi_apply i)
  rw [Measure.map_map hQ hU]
  change P.toMeasure.map (fun p i => q i (U p i)) = _
  rw [Measure.map_congr hall]
  change (μ.toMeasure.prod volume).map Prod.fst = _
  simp

end ProbabilityTheory.Copula
