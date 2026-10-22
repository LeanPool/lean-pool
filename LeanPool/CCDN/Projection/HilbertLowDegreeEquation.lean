/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
import LeanPool.CCDN.Hilbert.CoordinateIndependence
import LeanPool.CCDN.Projection.HilbertProjectionDegree

/-! A proper positive-codimension prime ideal of positive Hilbert dimension
contains a nonzero equation of degree at most its Hilbert multiplicity.
The independent coordinate subtuple and the equation are both constructed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A prime ideal of projective dimension `n` and degree `d` in more than `n + 1` variables contains
a nonzero polynomial of total degree at most `d`. -/
theorem exists_mem_ideal_degree_le_multiplicity
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ] {n : ℕ}
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I n d) (hcodim : n + 1 < Fintype.card σ) :
    ∃ f : MvPolynomial σ K, f ≠ 0 ∧ f ∈ I ∧ f.totalDegree ≤ d := by
  classical
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  rw [Nat.card_eq_fintype_card, hdimdeg.natDegree_eq] at hU
  let e : Fin (n + 1) ≃ U := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hU.symm)
  obtain ⟨v, hv⟩ : ∃ v : σ, v ∉ U := by
    by_contra! hn
    have hUniv : U = Set.univ := Set.eq_univ_iff_forall.mpr hn
    have hcard : Fintype.card U = Fintype.card σ := by simp [hUniv]
    omega
  let j : Fin (n + 2) → σ := Fin.lastCases v (fun i => (e i).val)
  have hj : Function.Injective j := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · intro _
        rfl
      · intro h
        have he : v = (e k).val := by simpa only [j, Fin.lastCases_last,
          Fin.lastCases_castSucc] using h
        exact (hv (he ▸ (e k).property)).elim
    · intro k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · intro h
        have he : (e i).val = v := by simpa only [j, Fin.lastCases_last,
          Fin.lastCases_castSucc] using h
        exact (hv (he ▸ (e i).property)).elim
      · intro h
        have he : (e i).val = (e k).val := by simpa only [j, Fin.lastCases_castSucc] using h
        exact congrArg Fin.castSucc (e.injective (Subtype.ext he))
  let a : Fin (n + 2) → MvPolynomial σ K := fun i => X (j i)
  let b : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K := fun i => X i.castSucc
  have ha : ∀ i, (a i).totalDegree ≤ 1 := fun i => by simp [a]
  have hb : ∀ i, (b i).totalDegree ≤ 1 := fun i => by simp [b]
  have hi : AlgebraicIndependent K (fun i => projectionCoordinateMap I a (b i)) := by
    simpa only [projectionCoordinateMap, AlgHom.comp_apply, b, aeval_X, a, j,
      Fin.lastCases_castSucc, Function.comp_def, Ideal.Quotient.mkₐ_eq_mk] using
      hAI.comp e e.injective
  obtain ⟨f, hf, _, hfd, hker⟩ := exists_hypersurface_projection_equation_degree_le
    I a ha d hdimdeg b hb hi
  have he : aeval a = rename j := (rename_eq_aeval j).symm
  refine ⟨aeval a f, ?_, ?_, ?_⟩
  · rw [he]
    exact fun hz => hf.ne_zero ((rename_injective j hj) (by simpa only [map_zero] using hz))
  · have hmem : f ∈ RingHom.ker (projectionCoordinateMap I a) := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton f)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem
  · exact (aeval_totalDegree_le a ha f).trans (by simpa using hfd)

end
end CCDN
