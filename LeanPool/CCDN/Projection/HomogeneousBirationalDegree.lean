/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import LeanPool.CCDN.Algebra.CoordinatePowerGeneration
import LeanPool.CCDN.Hilbert.PolynomialComparison
import LeanPool.CCDN.Projection.HomogeneousFilteredProjection
import Mathlib.LinearAlgebra.FreeModule.PID

/-! A homogeneous linear projection with a nonzero conductor preserves
Hilbert multiplicity. The conductor shifts the filtration by a fixed amount,
which leaves the leading coefficient of the Hilbert polynomial unchanged. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem conductor_filtered_finrank_le
    {K σ τ : Type*} [Field K] [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (c : MvPolynomial τ K) (hc : (Ideal.Quotient.mk I) c ≠ 0)
    (hconductor : ∀ x : MvPolynomial τ K ⧸ I, ∃ p : MvPolynomial σ K,
      projectionCoordinateMap I a p = (Ideal.Quotient.mk I) c * x)
    (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank K (filteredCoordinateSpace
        (RingHom.ker (projectionCoordinateMap I a)) (c.totalDegree + N)) := by
  classical
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite τ
  let ψ := projectionCoordinateMap I a
  let J := RingHom.ker ψ
  let V := filteredCoordinateSpace I N
  let W := filteredCoordinateSpace J (c.totalDegree + N)
  let b := Module.finBasis K V
  have hcl : (Ideal.Quotient.mk I) c ∈ filteredCoordinateSpace I c.totalDegree :=
    Submodule.mem_map.mpr ⟨c, (mem_restrictTotalDegree _ _ _).mpr le_rfl, rfl⟩
  have hpre (i : Fin (Module.finrank K V)) :
      ∃ p : MvPolynomial σ K, p.totalDegree ≤ c.totalDegree + N ∧
        ψ p = (Ideal.Quotient.mk I) c * (b i).val := by
    obtain ⟨p, hp⟩ := hconductor (b i).val
    have hm : ψ p ∈ filteredCoordinateSpace I (c.totalDegree + N) := by
      rw [hp]
      exact filteredCoordinateSpace_mul_mem I hcl (b i).property
    obtain ⟨q, hq, he⟩ :=
      homogeneous_projection_filtered_lift I hI a ha p (c.totalDegree + N) hm
    exact ⟨q, hq, he.trans hp⟩
  choose p hp he using hpre
  let w : Fin (Module.finrank K V) → W := fun i =>
    ⟨(Ideal.Quotient.mk J) (p i),
      Submodule.mem_map.mpr ⟨p i, (mem_restrictTotalDegree _ _ _).mpr (hp i), rfl⟩⟩
  let T : (MvPolynomial τ K ⧸ I) →ₗ[K] (MvPolynomial τ K ⧸ I) :=
    { toFun := fun x => (Ideal.Quotient.mk I) c * x
      map_add' := fun x y => mul_add _ x y
      map_smul' := fun r x => by simp only [mul_smul_comm, RingHom.id_apply] }
  have hT : Function.Injective (T.comp V.subtype) := by
    intro x y heq
    apply Subtype.ext
    exact mul_left_cancel₀ hc heq
  have hli := b.linearIndependent.map' (T.comp V.subtype) (LinearMap.ker_eq_bot.mpr hT)
  have hwi : LinearIndependent K w := by
    apply LinearIndependent.of_comp ((Ideal.kerLiftAlg ψ).toLinearMap.comp W.subtype)
    convert hli using 1
    funext i
    exact he i
  simpa only [Fintype.card_fin] using hwi.fintype_card_le_finrank

private theorem filteredHilbertPolynomial_leadingCoeff_le_of_shift
    {K L σ τ : Type*} [Field K] [Field L] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L))
    (hI : I ≠ ⊤) (hJ : J ≠ ⊤)
    (hd : (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree)
    (D : ℕ)
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J (D + N))) :
    (filteredHilbertPolynomial I).leadingCoeff ≤
      (filteredHilbertPolynomial J).leadingCoeff := by
  let Q := (filteredHilbertPolynomial J).comp (Polynomial.X + Polynomial.C (D : ℚ))
  have hQdeg : Q.natDegree = (filteredHilbertPolynomial J).natDegree := by
    simp only [Q, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  have hQlc : Q.leadingCoeff = (filteredHilbertPolynomial J).leadingCoeff := by
    dsimp only [Q]
    rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  have hh := polynomial_leadingCoeff_le_of_eventual_nat_eval_le
    (filteredHilbertPolynomial I) Q (filteredHilbertPolynomial_leadingCoeff_pos I hI)
    (by rw [hQlc]; exact filteredHilbertPolynomial_leadingCoeff_pos J hJ)
    (hd.trans hQdeg.symm) (by
      obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
      obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec J
      refine ⟨max M N, fun n hn => ?_⟩
      rw [hM n ((le_max_left _ _).trans hn)]
      simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [show (n : ℚ) + D = ((D + n : ℕ) : ℚ) by push_cast; ring,
        hN (D + n) (by omega)]
      exact_mod_cast hle n)
  simpa only [hQlc] using hh

/-- A nonzero conductor yields equality of Hilbert multiplicities
for a homogeneous linear birational projection. -/
theorem homogeneous_projection_leadingCoeff_eq
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hd : (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).natDegree =
      (filteredHilbertPolynomial I).natDegree)
    (c : MvPolynomial τ K) (hc : (Ideal.Quotient.mk I) c ≠ 0)
    (hconductor : ∀ x : MvPolynomial τ K ⧸ I, ∃ p : MvPolynomial σ K,
      projectionCoordinateMap I a p = (Ideal.Quotient.mk I) c * x) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff := by
  have hIproper : I ≠ ⊤ := Ideal.IsPrime.ne_top ‹I.IsPrime›
  have hJproper : RingHom.ker (projectionCoordinateMap I a) ≠ ⊤ :=
    RingHom.ker_ne_top _
  apply le_antisymm
  · exact filteredHilbertPolynomial_leadingCoeff_le _ _ hJproper hIproper hd
      (linear_projection_filtered_finrank_le I a (fun i => (ha i).totalDegree_le))
  · exact filteredHilbertPolynomial_leadingCoeff_le_of_shift _ _ hIproper hJproper hd.symm
      c.totalDegree (conductor_filtered_finrank_le I hI a ha c hc hconductor)

end
end CCDN
