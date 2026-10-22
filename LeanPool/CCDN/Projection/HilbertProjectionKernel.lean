/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import LeanPool.CCDN.Algebra.BinomialSectionBound
import LeanPool.CCDN.Hilbert.LinearCoordinates
import LeanPool.CCDN.Hilbert.PolynomialComparison
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleModule.Basic

/-! Hypersurface projection kernels in arbitrary dimension.
The proper-intersection estimate excludes a second independent equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem proper_intersection_hilbert_dimension_le
    {K : Type*} [Field K] {n : ℕ}
    {f g : MvPolynomial (Fin (n + 2)) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin (n + 2)) K)) (hI : I ≠ ⊤)
    (hIf : f ∈ I) (hIg : g ∈ I) :
    (filteredHilbertPolynomial I).natDegree ≤ n := by
  let Q := Polynomial.C ((f.totalDegree * g.totalDegree : ℕ) : ℚ) *
    Polynomial.preHilbertPoly ℚ n 0
  have hQ : Q.natDegree ≤ n := by
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_preHilbertPoly, zero_add]
    exact le_rfl
  apply (polynomial_natDegree_le_of_eventual_nat_eval_le
    (filteredHilbertPolynomial I) Q (filteredHilbertPolynomial_leadingCoeff_pos I hI) ?_).trans hQ
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  refine ⟨max M (f.totalDegree + g.totalDegree), fun N hN => ?_⟩
  rw [hM N ((le_max_left _ _).trans hN)]
  dsimp [Q]
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (by omega : 0 ≤ N + n)]
  simp only [Nat.sub_zero, Nat.add_comm N n]
  exact_mod_cast filteredCoordinateSpace_codim_two_bound hf hfg I hIf hIg
    ((le_max_right _ _).trans hN)

/-- An irreducible equation generates the whole kernel whenever the image
contains the expected number of independent linear coordinates. -/
theorem hypersurface_map_eq_zero_iff_dvd
    {K A : Type*} [Field K] [CommRing A] [Nontrivial A] [Algebra K A] {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin (n + 2)) K →ₐ[K] A) (hψ : ψ f = 0)
    (b : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hb : ∀ i, (b i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => ψ (b i)))
    (g : MvPolynomial (Fin (n + 2)) K) : ψ g = 0 ↔ f ∣ g := by
  constructor
  · intro hg
    by_contra hnd
    let I := RingHom.ker ψ
    let φ := Ideal.kerLiftAlg ψ
    have hAI : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (b i)) := by
      apply AlgebraicIndependent.of_comp φ
      exact hi
    have hlo := independent_linear_card_le_hilbert_dimension I b hb hAI
    have hhi := proper_intersection_hilbert_dimension_le hf.prime hnd I
      (RingHom.ker_ne_top ψ) hψ hg
    simp only [Fintype.card_fin] at hlo
    omega
  · rintro ⟨u, rfl⟩
    rw [map_mul, hψ, zero_mul]

/-- A linear projection with one more coordinate than Hilbert dimension
and an independent subtuple has a principal prime equation. -/
theorem exists_hypersurface_projection_equation
    {K τ : Type*} [Field K] [Fintype τ] [LinearOrder τ] {n : ℕ}
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin (n + 2) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hd : (filteredHilbertPolynomial I).natDegree < n + 2)
    (b : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hb : ∀ i, (b i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => projectionCoordinateMap I a (b i))) :
    ∃ f : MvPolynomial (Fin (n + 2)) K, Irreducible f ∧
      RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f} := by
  let ψ := projectionCoordinateMap I a
  have hker : RingHom.ker ψ ≠ ⊥ := by
    intro he
    exact linear_projection_not_injective_of_hilbert_dimension_lt I a ha
      (by simpa only [Fintype.card_fin] using hd)
      ((RingHom.injective_iff_ker_eq_bot ψ.toRingHom).mpr he)
  have hprime : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ.toRingHom
  obtain ⟨f, hfmem, hf⟩ := hprime.exists_mem_prime_of_ne_bot hker
  refine ⟨f, hf.irreducible, ?_⟩
  ext g
  exact (hypersurface_map_eq_zero_iff_dvd f hf.irreducible ψ hfmem b hb hi g).trans
    Ideal.mem_span_singleton.symm

end
end CCDN
