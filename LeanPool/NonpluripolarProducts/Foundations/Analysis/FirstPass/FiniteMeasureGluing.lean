/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Disjointed

/-!
# Gluing actual measures on a finite measurable cover

The constructor is a sum of restrictions to disjointified sets. Its overlap
and uniqueness theorems require genuine equalities of restricted measures,
with no local finiteness or sigma-finiteness assumption.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.FirstPass.FiniteMeasureGluing

noncomputable section

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

theorem measurableSet_disjointed (U : Fin m → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (i : Fin m) :
    MeasurableSet (disjointed U i) :=
  disjointedRec (p := MeasurableSet) (fun {_t j} ht => ht.diff (hU j)) (hU i)

/-- No compatibility is assumed in constructing this actual measure. -/
def glue (U : Fin m → Set X) (μ : Fin m → Measure X) : Measure X :=
  Measure.sum (fun i => (μ i).restrict (disjointed U i))

/-- If all local measures agree with a measure on an additional measurable
set covered by the domains, their glued measure agrees there as well. -/
theorem glue_restrict (U : Fin m → Set X) (μ : Fin m → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) {W : Set X} (hW : MeasurableSet W)
    (hcover : W ⊆ ⋃ i, U i) (ν : Measure X)
    (hcompat : ∀ i, (μ i).restrict (U i ∩ W) = ν.restrict (U i ∩ W)) :
    (glue U μ).restrict W = ν.restrict W := by
  have hD := measurableSet_disjointed U hU
  have hpiece (i : Fin m) :
      ((μ i).restrict (disjointed U i)).restrict W =
        ν.restrict (W ∩ disjointed U i) := by
    rw [Measure.restrict_restrict hW]
    have hsub : W ∩ disjointed U i ⊆ U i ∩ W :=
      fun _ hx => ⟨disjointed_subset U i hx.2, hx.1⟩
    have h := congrArg (fun κ : Measure X => κ.restrict (W ∩ disjointed U i))
      (hcompat i)
    simpa only [Measure.restrict_restrict_of_subset hsub] using h
  have hd : Pairwise (fun i j =>
      Disjoint (W ∩ disjointed U i) (W ∩ disjointed U j)) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  rw [glue, Measure.restrict_sum _ hW]
  simp_rw [hpiece]
  rw [← Measure.restrict_iUnion hd (fun i => hW.inter (hD i))]
  congr 1
  rw [← inter_iUnion, iUnion_disjointed]
  exact inter_eq_left.mpr hcover

/-- Pairwise agreement of the local restrictions gives agreement on every
member of the cover; no assertion is made outside its union. -/
theorem glue_restrict_member (U : Fin m → Set X) (μ : Fin m → Measure X)
    (hU : ∀ i, MeasurableSet (U i))
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) =
      (μ j).restrict (U i ∩ U j)) (j : Fin m) :
    (glue U μ).restrict (U j) = (μ j).restrict (U j) :=
  glue_restrict U μ hU (hU j) (subset_iUnion U j) (μ j) (fun i => hcompat i j)

/-- A measure is recovered from all of its restrictions to a finite cover. -/
theorem glue_eq_of_restrict_eq (U : Fin m → Set X) (μ : Fin m → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (ν : Measure X) (hν : ∀ i, (μ i).restrict (U i) = ν.restrict (U i)) :
    glue U μ = ν := by
  have h := glue_restrict U μ hU MeasurableSet.univ
    (by rw [hcover]) ν (by simpa only [inter_univ] using hν)
  simpa only [Measure.restrict_univ] using h

/-- Equality of local restrictions on a finite measurable cover determines
the measure, even when its mass is infinite. -/
theorem ext_of_restrict_eq (U : Fin m → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    {μ ν : Measure X} (h : ∀ i, μ.restrict (U i) = ν.restrict (U i)) : μ = ν := by
  have hμ := glue_eq_of_restrict_eq U (fun _ => μ) hU hcover μ (fun _ => rfl)
  have hν := glue_eq_of_restrict_eq U (fun _ => μ) hU hcover ν h
  exact hμ.symm.trans hν

end

end SGPT.Foundations.Analysis.FirstPass.FiniteMeasureGluing
