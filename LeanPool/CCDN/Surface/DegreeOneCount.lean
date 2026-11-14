/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import LeanPool.CCDN.Plane.IntegralAffineLine
public import Mathlib.RingTheory.Ideal.Height
import LeanPool.CCDN.Plane.DegreeOneAffineLine
import LeanPool.CCDN.Surface.LineContribution

/-!
The proved line contribution applies to degree-one prime
components, with the original number of components as the additive cost.

A finite family of degree-one prime components gives a finite
set of rational affine lines with the same rational zero-set union. Empty
rational loci are discarded, and repeated line sets are counted only once.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- The union of the rational zero sets of finitely many degree-one affine curves in
three-space is a union of at most as many rational affine lines, each of which is the zero set
of one of the curves. -/
theorem degree_one_components_line_cover
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (hcurve : ∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1) :
    ∃ lines : Finset (Set (RatPoint 3)),
      (⋃ P ∈ S, idealZeroLocus P) = (⋃ L ∈ lines, L) ∧
      lines.card ≤ S.card ∧
      ∀ L ∈ lines, (∃ P ∈ S, L = idealZeroLocus P) ∧
        ∃ a v : RatPoint 3, v ≠ 0 ∧ L = rationalAffineLine a v := by
  classical
  let T := S.filter (fun P => (idealZeroLocus P).Nonempty)
  let lines := T.image idealZeroLocus
  refine ⟨lines, ?_, (Finset.card_image_le).trans (Finset.card_le_card
    (Finset.filter_subset _ _)), ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hx
      have hPT : P ∈ T := Finset.mem_filter.mpr ⟨hPS, ⟨x, hxP⟩⟩
      exact Set.mem_iUnion.mpr ⟨idealZeroLocus P,
        Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨P, hPT, rfl⟩, hxP⟩⟩
    · intro hx
      obtain ⟨L, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hLs, hxL⟩ := Set.mem_iUnion.mp hx
      obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hLs
      exact Set.mem_iUnion.mpr ⟨P,
        Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hPT).1, hxL⟩⟩
  · intro L hL
    obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hPS, z, hz⟩ := Finset.mem_filter.mp hPT
    obtain ⟨hp, hheight, hdegree⟩ := hcurve P hPS
    have : P.IsPrime := hp
    obtain ⟨v, hv, he, _⟩ :=
      degree_one_zeroLocus_eq_rationalAffineLine P hheight hdegree z hz
    exact ⟨⟨P, hPS, rfl⟩, z, v, hv, he⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- There is an absolute constant `C` such that, for an integer surface equation `f` of degree
`d ≥ 3` with absolutely irreducible top-degree form, the integral points of height at most `B`
on a finite family `S` of degree-one curves on the surface number at most
`C d⁶ B + #S`. -/
theorem surface_degree_one_component_contribution :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree → ∀ B : ℝ, 0 ≤ B →
      ∀ S : Finset (Ideal (CoordinatePolynomial 3)),
      (∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1) →
      (∀ P ∈ S, map (Int.castRingHom ℚ) f ∈ P) →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 6 * B + S.card := by
  obtain ⟨C, hC, hline⟩ := surface_line_contribution
  refine ⟨C, hC, ?_⟩
  intro f hir hd B hB S hcurve hSf
  obtain ⟨lines, hcover, hcard, hlines⟩ := degree_one_components_line_cover S hcurve
  have hh := (hline f hir hd B hB lines (by
    intro L hL
    obtain ⟨a, v, _, he⟩ := (hlines L hL).2
    exact ⟨a, v, he⟩) (by
      intro L hL x hx
      obtain ⟨P, hPS, rfl⟩ := (hlines L hL).1
      exact hx _ (hSf P hPS))).2
  rw [← hcover] at hh
  have hcardR : (lines.card : ℝ) ≤ S.card := by exact_mod_cast hcard
  exact hh.trans (add_le_add le_rfl hcardR)

end
end CCDN
