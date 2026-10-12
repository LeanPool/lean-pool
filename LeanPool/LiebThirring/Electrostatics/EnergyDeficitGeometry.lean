/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasure
public import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Nearest-nucleus geometry for the energy deficit

A finite configuration with at least two nuclei has a nearest other index.

The finite minimum agrees with the extended nearest-other distance.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring

variable {M : ℕ}

/-- A finite configuration with at least two nuclei has a nearest other index. -/
theorem exists_nearest_other_nucleus (R : Fin M → Position) (hM : 2 ≤ M) (k : Fin M) :
    ∃ l : Fin M, l ≠ k ∧ ∀ p : Fin M, p ≠ k → ‖R k - R l‖ ≤ ‖R k - R p‖ := by
  classical
  have : Nontrivial (Fin M) := Fin.nontrivial_iff_two_le.mpr hM
  obtain ⟨l, hl⟩ := exists_ne k
  have : Nonempty {p : Fin M // p ≠ k} := ⟨⟨l, hl⟩⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_min_image Finset.univ
    (fun p : {p : Fin M // p ≠ k} => ‖R k - R p‖) Finset.univ_nonempty
  exact ⟨p, p.property, fun q hq => hp ⟨q, hq⟩ (Finset.mem_univ _)⟩

/-- The finite minimum agrees with the extended nearest-other distance. -/
theorem nearestOtherNucleusDistance_eq_of_nearest (R : Fin M → Position)
    {k l : Fin M} (hkl : l ≠ k)
    (hl : ∀ p : Fin M, p ≠ k → ‖R k - R l‖ ≤ ‖R k - R p‖) :
    nearestOtherNucleusDistance R k = ENNReal.ofReal ‖R k - R l‖ := by
  change (⨅ p : {p : Fin M // p ≠ k}, ENNReal.ofReal ‖R k - R p‖) = _
  apply le_antisymm
  · exact iInf_le (fun p : {p : Fin M // p ≠ k} => ENNReal.ofReal ‖R k - R p‖) ⟨l, hkl⟩
  · exact le_iInf (fun p => ENNReal.ofReal_le_ofReal (hl p p.property))

theorem nearestOtherNucleusDistance_pos (R : Fin M → Position)
    (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M) :
    0 < nearestOtherNucleusDistance R k := by
  obtain ⟨l, hl, hmin⟩ := exists_nearest_other_nucleus R hM k
  rw [nearestOtherNucleusDistance_eq_of_nearest R hl hmin]
  exact ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hl.symm)))

theorem nearestOtherNucleusDistance_lt_top (R : Fin M → Position)
    (hM : 2 ≤ M) (k : Fin M) : nearestOtherNucleusDistance R k < ⊤ := by
  obtain ⟨l, hl, hmin⟩ := exists_nearest_other_nucleus R hM k
  rw [nearestOtherNucleusDistance_eq_of_nearest R hl hmin]
  exact ENNReal.ofReal_lt_top

theorem nearestOtherNucleusDistance_toReal_pos (R : Fin M → Position)
    (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M) :
    0 < (nearestOtherNucleusDistance R k).toReal :=
  ENNReal.toReal_pos (nearestOtherNucleusDistance_pos R hR hM k).ne'
    (nearestOtherNucleusDistance_lt_top R hM k).ne

/-- The nearest-other half-space lies in the cell exterior, with the radius. -/
theorem exists_nearest_exterior_halfSpace (R : Fin M → Position)
    (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M) :
    ∃ l : Fin M, l ≠ k ∧
      nearestOtherNucleusDistance R k = ENNReal.ofReal ‖R l - R k‖ ∧
      {x : Position | (nearestOtherNucleusDistance R k).toReal / 2 ≤
        inner ℝ (bisectorNormal R k l) (x - R k)} ⊆ (voronoiCell R k)ᶜ := by
  obtain ⟨l, hl, hmin⟩ := exists_nearest_other_nucleus R hM k
  have he : nearestOtherNucleusDistance R k = ENNReal.ofReal ‖R l - R k‖ := by
    rw [nearestOtherNucleusDistance_eq_of_nearest R hl hmin, norm_sub_rev]
  refine ⟨l, hl, he, ?_⟩
  rw [he, ENNReal.toReal_ofReal (norm_nonneg _)]
  exact exterior_halfSpace_subset_compl_voronoiCell R hR hl.symm

/-- Every genuine face has either incident nucleus as a nearest one. -/
theorem nearestNucleusDistance_eq_of_mem_voronoiFace (R : Fin M → Position)
    {k l : Fin M} {x : Position} (hx : x ∈ voronoiFace R k l) :
    nearestNucleusDistance R x = ENNReal.ofReal ‖x - R k‖ :=
  nearestNucleusDistance_eq_of_mem_closedVoronoiCell R k (voronoiFace_subset_closed R k l hx)

end LiebThirring

end
