/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.FormalPlaneDifferentiation
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import LeanPool.CCDN.Determinant.FormalBranchMultiplicity
import LeanPool.CCDN.ForMathlib.MvPolynomialDerivative
import LeanPool.CCDN.Noether.FormalBranchFaithful
import LeanPool.CCDN.Noether.FormalBranchOrder
import Mathlib.FieldTheory.Finite.Basic

/-!
Frobenius auxiliary polynomials: noncancellation, tangent-derivative
constraints, and their resulting count of smooth rational points.

A polynomial criterion for the multiplicity form of plane Bézout.
All formal branches are constructed from the nonsingularity assumptions.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Successive tangent derivatives vanishing at distinct smooth points force
N times their cardinality to be at most the section-degree product. -/
private theorem plane_tangent_multiplicity_bound {K ι : Type*} [Field K]
    [Fintype ι]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : ι → Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv (j i).rev f) ≠ 0)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) (N : ℕ)
    (hchar : ∀ n, 0 < n → n < N → (n : K) ≠ 0)
    (hvan : ∀ i r, r < N → eval (z i) ((planeTangent f (j i))^[r] g) = 0) :
    Fintype.card ι * N ≤ f.totalDegree * g.totalDegree := by
  classical
  have hb (i : ι) := exists_faithful_formal_plane_branch f hf (z i) (j i).rev
    (hzero i) (hsmooth i)
  choose ψ hconst hparam hfaith using hb
  apply formal_plane_multiplicity_bound f hf z hz ψ
    (fun i => (hfaith i f).mpr dvd_rfl) hconst j
    (by simpa only [Fin.rev_rev] using hparam) g hnd N
  intro i
  exact formal_plane_multiplicity_of_tangent f (ψ i) ((hfaith i f).mpr dvd_rfl)
    (z i) (hconst i) (j i) (by simpa only [Fin.rev_rev] using hparam i)
    (hsmooth i) g N hchar (hvan i)

/-- Characteristic p allows all requested multiplicities up to p. -/
private theorem plane_tangent_multiplicity_bound_charP {K ι : Type*} [Field K]
    [Fintype ι] (p : ℕ) [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : ι → Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv (j i).rev f) ≠ 0)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) (N : ℕ) (hN : N ≤ p)
    (hvan : ∀ i r, r < N → eval (z i) ((planeTangent f (j i))^[r] g) = 0) :
    Fintype.card ι * N ≤ f.totalDegree * g.totalDegree := by
  classical
  exact plane_tangent_multiplicity_bound f hf z hz hzero j hsmooth g hnd N
    (fun _ hn hnN ↦ CharP.natCast_ne_zero_of_lt K hn.ne' (hnN.trans_le hN)) hvan

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Polynomial used in the Stepanov construction. -/
private def planeFrobeniusAuxiliary {K ι : Type*} [Field K] [Fintype ι]
    (p : ℕ) (h a : ι → MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  ∑ i, h i * (a i) ^ p

private lemma planeFrobeniusAuxiliary_degree {K ι : Type*} [Field K] [Fintype ι]
    (p : ℕ) (h a : ι → MvPolynomial (Fin 2) K) {D A : ℕ}
    (hd : ∀ i, (h i).totalDegree ≤ D) (ha : ∀ i, (a i).totalDegree ≤ A) :
    (planeFrobeniusAuxiliary p h a).totalDegree ≤ D + p * A := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hd i)
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left p (ha i))))

/-- A nontrivial coefficient class gives a proper section, with the precise
low-degree restriction d*D<p. -/
private theorem planeFrobeniusAuxiliary_not_dvd {K ι : Type*} [Field K]
    [Fintype ι] (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2) (hz : eval z f = 0)
    (hj : eval z (pderiv j f) ≠ 0)
    (h a : ι → MvPolynomial (Fin 2) K) {D : ℕ} (hD : f.totalDegree * D < p)
    (hd : ∀ i, (h i).totalDegree ≤ D)
    (hi : LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (h i)))
    (ha : ∃ i, ¬ f ∣ a i) : ¬ f ∣ planeFrobeniusAuxiliary p h a := by
  classical
  obtain ⟨ψ, hconst, hparam, hfaith⟩ := exists_faithful_formal_plane_branch f hf z j hz hj
  intro hdiv
  have hrel : ∑ i, ψ (h i) * (ψ (a i)) ^ (p ^ 1) = 0 := by
    have he := (hfaith _).mpr hdiv
    simpa only [planeFrobeniusAuxiliary, map_sum, map_mul, map_pow, pow_one] using he
  have hzero := formal_plane_frobenius_relation_trivial p 1 f hf ψ
    ((hfaith f).mpr dvd_rfl) j.rev (z j.rev) hparam (by simpa only [pow_one] using hD)
    h hd hi (fun i => ψ (a i)) hrel
  obtain ⟨i, hai⟩ := ha
  exact hai ((hfaith (a i)).mp (hzero i))

private lemma derivation_prime_power_zero {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (D : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K))
    (g : MvPolynomial (Fin 2) K) : D (g ^ p) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

private lemma planeFrobeniusAuxiliary_iterate {K ι : Type*} [Field K] [Fintype ι]
    (p : ℕ) [CharP K p]
    (D : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K))
    (h a : ι → MvPolynomial (Fin 2) K) (r : ℕ) :
    D^[r] (planeFrobeniusAuxiliary p h a) = ∑ i, D^[r] (h i) * (a i) ^ p := by
  induction r with
  | zero => rfl
  | succ r hr =>
    rw [Function.iterate_succ_apply', hr, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Derivation.leibniz, derivation_prime_power_zero p, smul_zero, zero_add,
      smul_eq_mul, Function.iterate_succ_apply']
    exact mul_comm _ _

/-- Divisibility constraints on the unpowered coefficients force all requested
tangent derivatives to vanish at every rational point over the prime field. -/
private theorem planeFrobeniusAuxiliary_tangent_vanishing {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (j : Fin 2)
    (h a : ι → MvPolynomial (Fin 2) (ZMod p)) (r : ℕ)
    (hdiv : f ∣ ∑ i, (planeTangent f j)^[r] (h i) * a i)
    (z : Fin 2 → ZMod p) (hz : eval z f = 0) :
    eval z ((planeTangent f j)^[r] (planeFrobeniusAuxiliary p h a)) = 0 := by
  rw [planeFrobeniusAuxiliary_iterate]
  have he : eval z (∑ i, (planeTangent f j)^[r] (h i) * a i) = 0 := by
    obtain ⟨u, hu⟩ := hdiv
    rw [hu, map_mul, hz, zero_mul]
  simpa only [map_sum, map_mul, map_pow, ZMod.pow_card] using he

/-- The smooth rational-point bound supplied by any nontrivial solution of
the finite linear system defining a Frobenius auxiliary polynomial. -/
theorem planeFrobeniusAuxiliary_point_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv j.rev f) ≠ 0)
    (h a : κ → MvPolynomial (Fin 2) (ZMod p)) {D A N : ℕ}
    (hD : f.totalDegree * D < p) (hN : N ≤ p)
    (hd : ∀ k, (h k).totalDegree ≤ D) (ha : ∀ k, (a k).totalDegree ≤ A)
    (hi : LinearIndependent (ZMod p)
      (fun k => (Ideal.Quotient.mkₐ (ZMod p) (Ideal.span {f})) (h k)))
    (hne : ∃ k, ¬ f ∣ a k)
    (hdiv : ∀ r < N, f ∣ ∑ k, (planeTangent f j)^[r] (h k) * a k) :
    Fintype.card ι * N ≤ f.totalDegree * (D + p * A) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he => simp
  | inr he =>
    obtain ⟨i⟩ := he
    have hnd := planeFrobeniusAuxiliary_not_dvd p f hf (z i) j.rev (hzero i)
      (hsmooth i) h a hD hd hi hne
    have hb := plane_tangent_multiplicity_bound_charP p f hf z hz hzero (fun _ => j)
      hsmooth (planeFrobeniusAuxiliary p h a) hnd N hN
      (fun i r hr => planeFrobeniusAuxiliary_tangent_vanishing p f j h a r (hdiv r hr)
        (z i) (hzero i))
    exact hb.trans (Nat.mul_le_mul_left _ (planeFrobeniusAuxiliary_degree p h a hd ha))

end
end CCDN
