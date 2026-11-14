/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ForMathlib.StandardExponents
public import LeanPool.CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Standard monomials in a filtered coordinate ring

Degree lexicographic standard representatives (`Ideal.exists_standard_representative_degLex`)
preserve the total-degree filtration, giving an exact combinatorial model for the dimensions
of the filtered coordinate spaces.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Standard representatives describe precisely each filtered coordinate space. -/
private theorem map_bounded_standard_eq {K σ : Type*} [Field K]
    [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (restrictSupport K (Ideal.boundedStandardExponents I MonomialOrder.degLex N)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap = filteredCoordinateSpace I N := by
  apply le_antisymm
  · apply Submodule.map_mono
    exact restrictSupport_mono K (fun _ ha => ha.2)
  · rintro y ⟨f, hf, rfl⟩
    obtain ⟨r, hr, hdegree, hI⟩ := Ideal.exists_standard_representative_degLex I f
    refine Submodule.mem_map.mpr ⟨r, ?_, ?_⟩
    · intro a ha
      exact ⟨hr ha, (le_totalDegree ha).trans
        (hdegree.trans ((mem_restrictTotalDegree σ N f).mp hf))⟩
    · have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hI
      rw [map_sub, sub_eq_zero] at hq
      exact hq.symm

/-- The filtered Hilbert function counts the standard monomials of bounded degree. -/
theorem filteredCoordinateSpace_finrank_eq_standard_card {K σ : Type*} [Field K]
    [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Nat.card (Ideal.boundedStandardExponents I MonomialOrder.degLex N) := by
  let V := restrictSupport K (Ideal.boundedStandardExponents I MonomialOrder.degLex N)
  let φ := (Ideal.Quotient.mkₐ K I).toLinearMap.comp V.subtype
  have hinj : Function.Injective φ := by
    intro f g h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Ideal.eq_zero_of_mem_restrictSupport_standardExponents I MonomialOrder.degLex
    · apply Submodule.sub_mem
      · exact restrictSupport_mono K (fun _ ha => ha.1) f.property
      · exact restrictSupport_mono K (fun _ ha => ha.1) g.property
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (Ideal.Quotient.mkₐ K I) (f.val - g.val) = 0
      rw [map_sub, sub_eq_zero]
      exact h
  have hrange : φ.range = filteredCoordinateSpace I N := by
    rw [show φ = (Ideal.Quotient.mkₐ K I).toLinearMap.comp V.subtype from rfl,
      LinearMap.range_comp, Submodule.range_subtype]
    exact map_bounded_standard_eq I N
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

end
end CCDN
