/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
public import LeanPool.CCDN.Noether.LeadingDirection
public import LeanPool.CCDN.Noether.PlaneShear

/-! Bounded integral shears give full outer degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- Variable zero corresponds to the outer variable of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_X_zero {R : Type*} [CommRing R] :
    bivariatePolynomialEquiv R (MvPolynomial.X 0) = (X : R[X][X]) := by
  simp [bivariatePolynomialEquiv, MvPolynomial.finSuccEquiv_X_zero]

/-- Variable one corresponds to the inner variable of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_X_one {R : Type*} [CommRing R] :
    bivariatePolynomialEquiv R (MvPolynomial.X 1) = (C X : R[X][X]) := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp

/-- Constants correspond to constants of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_C {R : Type*} [CommRing R] (a : R) :
    bivariatePolynomialEquiv R (MvPolynomial.C a) = C (C a) := by
  exact (bivariatePolynomialEquiv R).commutes a

/-- The integral shear in nested polynomial coordinates. -/
def bivariateShear (R : Type*) [CommRing R] (a : R) : R[X][X] ≃ₐ[R] R[X][X] :=
  (bivariatePolynomialEquiv R).symm.trans ((planeShear R a).trans (bivariatePolynomialEquiv R))

/-- Restrict the sheared polynomial to the outer coordinate axis. -/
private def directionAxisHom (R : Type*) [CommRing R] (a : R) :
    MvPolynomial (Fin 2) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![X, C a * X]

private lemma directionAxisHom_eq_shear_axis {R : Type*} [CommRing R] (a : R)
    (f : MvPolynomial (Fin 2) R) :
    directionAxisHom R a f =
      Polynomial.map (Polynomial.evalRingHom 0)
        (bivariatePolynomialEquiv R (planeShear R a f)) := by
  suffices hh : directionAxisHom R a =
      (Polynomial.mapRingHom (Polynomial.evalRingHom 0)).comp
        ((bivariatePolynomialEquiv R).toRingHom.comp (planeShear R a).toRingHom) from
    congrArg (fun h : MvPolynomial (Fin 2) R →+* R[X] => h f) hh
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [directionAxisHom, planeShear, planeShearHom, bivariatePolynomialEquiv_C]
  · intro i
    fin_cases i <;>
      simp [directionAxisHom, planeShear, planeShearHom,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one, bivariatePolynomialEquiv_C]

private lemma directionAxisHom_monomial {R : Type*} [CommRing R]
    (a : R) (m : Fin 2 →₀ ℕ) (c : R) :
    directionAxisHom R a (MvPolynomial.monomial m c) = monomial (m 0 + m 1) (c * a ^ m 1) := by
  change MvPolynomial.eval₂Hom C ![X, C a * X] (MvPolynomial.monomial m c) = _
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← C_mul_X_pow_eq_monomial, mul_pow, ← map_pow, map_mul, pow_add]
  ring

/-- A two-variable exponent vector `m` equals `Finsupp.cons i (Finsupp.single 0 j)` if and only if
its components are `i` and `j`. -/
lemma bivariate_exponent_eq_iff (m : Fin 2 →₀ ℕ) (i j : ℕ) :
    Finsupp.cons i (Finsupp.single 0 j) = m ↔ m 0 = i ∧ m 1 = j := by
  constructor
  · intro h
    have h₀ := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h
    have h₁ := congrArg (fun s : Fin 2 →₀ ℕ => s (Fin.succ (0 : Fin 1))) h
    simp only [Finsupp.cons_zero] at h₀
    simp only [Finsupp.cons_succ, Finsupp.single_eq_same] at h₁
    exact ⟨h₀.symm, h₁.symm⟩
  · rintro ⟨h₀,h₁⟩
    rw [← h₀, ← h₁, ← bivariate_exponent_eq m]

private lemma leadingDirectionPolynomial_monomial {R : Type*} [CommRing R]
    (m : Fin 2 →₀ ℕ) (c : R) (d : ℕ) :
    leadingDirectionPolynomial (bivariatePolynomialEquiv R (MvPolynomial.monomial m c)) d =
      if m 0 + m 1 = d then monomial (m 1) c else 0 := by
  classical
  by_cases hsum : m 0 + m 1 = d
  · rw [ite_eq_left hsum]
    ext j
    rw [leadingDirectionPolynomial_coeff, bivariatePolynomialEquiv_coeff, coeff_monomial]
    have he : m = Finsupp.cons (d - j) (Finsupp.single 0 j) ↔ m 1 = j := by
      rw [eq_comm, bivariate_exponent_eq_iff]
      omega
    simp only [MvPolynomial.coeff_monomial, he]
    by_cases hj : m 1 = j
    · have hjd : j ≤ d := by omega
      simp [hj, hjd]
    · simp [hj]
  · rw [ite_eq_right hsum]
    ext j
    rw [leadingDirectionPolynomial_coeff, bivariatePolynomialEquiv_coeff, coeff_zero]
    by_cases hj : j ≤ d
    · have he : m ≠ Finsupp.cons (d - j) (Finsupp.single 0 j) := by
        intro h
        have hh := (bivariate_exponent_eq_iff m (d - j) j).mp h.symm
        omega
      simp [MvPolynomial.coeff_monomial, hj, he]
    · simp [hj]

private lemma leadingDirectionPolynomial_add {R : Type*} [CommRing R]
    (f g : R[X][X]) (d : ℕ) :
    leadingDirectionPolynomial (f + g) d =
      leadingDirectionPolynomial f d + leadingDirectionPolynomial g d := by
  simp [leadingDirectionPolynomial, Finset.sum_add_distrib]

/-- The direction polynomial computes the leading axis coefficient. -/
private theorem directionAxisHom_coeff {R : Type*} [CommRing R]
    (a : R) (f : MvPolynomial (Fin 2) R) (d : ℕ) :
    (directionAxisHom R a f).coeff d =
      (leadingDirectionPolynomial (bivariatePolynomialEquiv R f) d).eval a := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [map_add, coeff_add, leadingDirectionPolynomial_add, eval_add, hf, hg]
  | monomial m c =>
    rw [directionAxisHom_monomial, leadingDirectionPolynomial_monomial, coeff_monomial]
    split_ifs <;> simp [eval_monomial]

private lemma bivariateShear_totalDegree {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) (f : R[X][X]) :
    bivariateTotalDegree (bivariateShear R a f) = bivariateTotalDegree f := by
  unfold bivariateTotalDegree bivariateShear
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  exact planeShear_totalDegree _ _

/-- A plane shear preserves irreducibility of bivariate polynomials. -/
lemma bivariateShear_irreducible_iff {R : Type*} [CommRing R]
    (a : R) (f : R[X][X]) : Irreducible (bivariateShear R a f) ↔ Irreducible f :=
  MulEquiv.irreducible_iff (f := bivariateShear R a)

private lemma bivariateShear_axis_coeff {R : Type*} [CommRing R]
    (a : R) (f : R[X][X]) (d : ℕ) :
    ((bivariateShear R a f).coeff d).coeff 0 = (leadingDirectionPolynomial f d).eval a := by
  have h := congrArg (fun q : R[X] => q.coeff d)
    (directionAxisHom_eq_shear_axis a ((bivariatePolynomialEquiv R).symm f))
  rw [directionAxisHom_coeff, AlgEquiv.apply_symm_apply, coeff_map] at h
  change (leadingDirectionPolynomial f d).eval a =
    Polynomial.eval 0 ((bivariateShear R a f).coeff d) at h
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h
  exact h.symm

/-- Every nonzero integer plane equation admits a shear with parameter in
0,...,d whose outer degree is exactly its original total degree. -/
theorem exists_bounded_full_outer_shear (f : ℤ[X][X]) (hf : f ≠ 0) :
    ∃ a : ℕ, a ≤ bivariateTotalDegree f ∧
      (bivariateShear ℤ (a : ℤ) f).natDegree = bivariateTotalDegree f ∧
      bivariateTotalDegree (bivariateShear ℤ (a : ℤ) f) = bivariateTotalDegree f := by
  obtain ⟨a, ha, he⟩ := exists_bounded_leading_direction f hf
  refine ⟨a, ha, ?_, bivariateShear_totalDegree _ _⟩
  have hc : ((bivariateShear ℤ (a : ℤ) f).coeff (bivariateTotalDegree f)).coeff 0 ≠ 0 := by
    rw [bivariateShear_axis_coeff]
    exact he
  have hp : (bivariateShear ℤ (a : ℤ) f).coeff (bivariateTotalDegree f) ≠ 0 := by
    intro hz
    exact hc (by rw [hz, coeff_zero])
  have hlo := le_natDegree_of_ne_zero hp
  have hhi := bivariate_natDegree_le_totalDegree (bivariateShear ℤ (a : ℤ) f)
  rw [bivariateShear_totalDegree] at hhi
  omega

/-- The identification of two-variable polynomials with nested polynomials commutes with applying a
coefficient ring homomorphism. -/
lemma bivariatePolynomialEquiv_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Fin 2) R) :
    bivariateMap φ (bivariatePolynomialEquiv R f) =
      bivariatePolynomialEquiv S (MvPolynomial.map φ f) := by
  ext i j
  simp only [bivariateMap_coeff, bivariatePolynomialEquiv_coeff, MvPolynomial.coeff_map]

/-- The nested plane shear corresponds to the plane shear of two-variable polynomials. -/
lemma bivariateShear_equiv {R : Type*} [CommRing R]
    (a : R) (f : MvPolynomial (Fin 2) R) :
    bivariateShear R a (bivariatePolynomialEquiv R f) =
      bivariatePolynomialEquiv R (planeShear R a f) := by
  simp only [bivariateShear, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- Applying a coefficient ring homomorphism `φ` commutes with shearing, the shear parameter `a`
becoming `φ a`. -/
lemma bivariateShear_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (f : R[X][X]) :
    bivariateMap φ (bivariateShear R a f) =
      bivariateShear S (φ a) (bivariateMap φ f) := by
  obtain ⟨g, rfl⟩ := (bivariatePolynomialEquiv R).surjective f
  simp only [bivariateShear_equiv, bivariatePolynomialEquiv_map, planeShear_map]

/-- Shearing does not change the set of bad primes, including reductions
where the degree drops. -/
theorem bivariateBadReduction_shear_iff (a : ℤ) (f : ℤ[X][X]) (d p : ℕ) :
    BivariateBadReduction (bivariateShear ℤ a f) d p ↔ BivariateBadReduction f d p := by
  constructor
  · rintro ⟨hp, hbad⟩
    refine ⟨hp, ?_⟩
    let : Fact p.Prime := ⟨hp⟩
    change bivariateTotalDegree (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p)))
      (bivariateShear ℤ a f)) ≠ d ∨ ¬Irreducible
        (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p))) (bivariateShear ℤ a f)) at hbad
    rw [bivariateShear_map, bivariateShear_totalDegree, bivariateShear_irreducible_iff] at hbad
    exact hbad
  · rintro ⟨hp, hbad⟩
    refine ⟨hp, ?_⟩
    let : Fact p.Prime := ⟨hp⟩
    change bivariateTotalDegree (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p)))
      (bivariateShear ℤ a f)) ≠ d ∨ ¬Irreducible
        (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p))) (bivariateShear ℤ a f))
    rw [bivariateShear_map, bivariateShear_totalDegree, bivariateShear_irreducible_iff]
    exact hbad

end
end CCDN
