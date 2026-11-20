/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.HarmonicCoefficients
public import LeanPool.NoncommutativeAMGM.ScalarHomogeneousSpace

/-!
# Homogeneous coefficient spaces and the up/down operators

The finite dimensional orthogonal decomposition used in Appendix C is constructed
for the actual subset-incidence operators.
-/

@[expose] public section
namespace NoncommutativeAMGM

open scoped BigOperators RealInnerProductSpace

/-- Euclidean coefficient space of real homogeneous square-free polynomials. -/
abbrev HomogeneousSpace (n r : ℕ) := ScalarHomogeneousSpace ℝ n r

/-- The incidence operator adding one new variable to a square-free monomial. -/
noncomputable def homogeneousUp (n r : ℕ) :
    HomogeneousSpace n r →ₗ[ℝ] HomogeneousSpace n (r + 1) :=
  scalarHomogeneousUp ℝ n r

/-- The coefficient Laplacian, removing one variable from a square-free monomial. -/
noncomputable def homogeneousDown (n r : ℕ) :
    HomogeneousSpace n (r + 1) →ₗ[ℝ] HomogeneousSpace n r :=
  scalarHomogeneousDown ℝ n r

theorem homogeneousUp_apply {n r : ℕ} (c : HomogeneousSpace n r)
    (T : HomogeneousIndex n (r + 1)) :
    homogeneousUp n r c T = ∑ S : HomogeneousIndex n r,
      if S.val ⊆ T.val then c S else 0 :=
  scalarHomogeneousUp_apply ℝ c T

theorem homogeneousDown_apply {n r : ℕ} (c : HomogeneousSpace n (r + 1))
    (S : HomogeneousIndex n r) :
    homogeneousDown n r c S = ∑ T : HomogeneousIndex n (r + 1),
      if S.val ⊆ T.val then c T else 0 :=
  scalarHomogeneousDown_apply ℝ c S

/-- The actual subset-incidence up operator is the adjoint of the Laplacian. -/
theorem homogeneousUp_eq_adjoint (n r : ℕ) :
    homogeneousUp n r = (homogeneousDown n r).adjoint :=
  scalarHomogeneousUp_eq_adjoint ℝ n r

/-- Orthogonality to all raised polynomials is exactly harmonicity. -/
theorem homogeneousUp_range_orthogonal (n r : ℕ) :
    (homogeneousUp n r).rangeᗮ = (homogeneousDown n r).ker :=
  scalarHomogeneousUp_range_orthogonal ℝ n r

/-- Every homogeneous coefficient vector is a harmonic vector plus a raised vector. -/
theorem homogeneous_harmonic_decomposition {n r : ℕ} (c : HomogeneousSpace n (r + 1)) :
    ∃ h : HomogeneousSpace n (r + 1), ∃ q : HomogeneousSpace n r,
      homogeneousDown n r h = 0 ∧ c = h + homogeneousUp n r q :=
  scalarHomogeneous_harmonic_decomposition ℝ c

/-- Extend a homogeneous coefficient vector by zero outside its degree. -/
noncomputable def homogeneousCoefficient {n r : ℕ} (c : HomogeneousSpace n r)
    (S : Finset (Fin n)) : ℝ := if h : S.card = r then c ⟨S, h⟩ else 0

theorem homogeneousDown_eq_upperSum {n r : ℕ} (c : HomogeneousSpace n (r + 1))
    (S : HomogeneousIndex n r) :
    homogeneousDown n r c S = homogeneousUpperSum (r + 1) (homogeneousCoefficient c) S := by
  classical
  rw [homogeneousDown_apply, homogeneousUpperSum]
  rw [Finset.sum_subtype (p := fun T : Finset (Fin n) ↦ T.card = r + 1)
    ((Finset.univ : Finset (Fin n)).powersetCard (r + 1))
    (by intro T; simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and])]
  apply Finset.sum_congr rfl
  intro T _
  simp [homogeneousCoefficient, T.property]

/-- The kernel used in the decomposition is exactly the paper's harmonic coefficient equations. -/
theorem homogeneousDown_eq_zero_iff {n r : ℕ} (c : HomogeneousSpace n (r + 1)) :
    homogeneousDown n r c = 0 ↔ HarmonicCoefficients (r + 1) (homogeneousCoefficient c) := by
  constructor
  · intro hc S hS
    have hcard : S.card = r := by omega
    rw [← homogeneousDown_eq_upperSum c ⟨S, hcard⟩, hc]
    rfl
  · intro hc
    ext S
    rw [homogeneousDown_eq_upperSum]
    exact hc S.val (by rw [S.property])

/-- The polynomial represented by a homogeneous coefficient vector. -/
noncomputable def homogeneousPolynomial {n r : ℕ} (c : HomogeneousSpace n r) :
    BooleanPolynomial n := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm
    (fun S : BooleanMonomial n ↦ homogeneousCoefficient c S.toFinset))

theorem homogeneousPolynomial_coeff {n r : ℕ} (c : HomogeneousSpace n r)
    (T : BooleanMonomial n) :
    (homogeneousPolynomial c).coeff T = homogeneousCoefficient c T.toFinset := by
  simp [homogeneousPolynomial]

theorem homogeneousPolynomial_add {n r : ℕ} (c d : HomogeneousSpace n r) :
    homogeneousPolynomial (c + d) = homogeneousPolynomial c + homogeneousPolynomial d := by
  classical
  apply MonoidAlgebra.ext
  ext T
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, homogeneousPolynomial_coeff]
  by_cases hT : T.toFinset.card = r <;>
    simp [homogeneousCoefficient, PiLp.add_apply, hT]

theorem homogeneousPolynomial_smul {n r : ℕ} (a : ℝ) (c : HomogeneousSpace n r) :
    homogeneousPolynomial (a • c) = a • homogeneousPolynomial c := by
  classical
  apply MonoidAlgebra.ext
  ext T
  simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, homogeneousPolynomial_coeff]
  simp [homogeneousCoefficient, PiLp.smul_apply]

theorem homogeneousPolynomial_degree {n r : ℕ} (c : HomogeneousSpace n r) :
    BooleanDegreeLE (homogeneousPolynomial c) r := by
  intro T hT
  rw [homogeneousPolynomial_coeff] at hT
  change T.toFinset.card ≤ r
  by_contra h
  exact hT (by simp [homogeneousCoefficient, ne_of_gt (Nat.lt_of_not_ge h)])

end NoncommutativeAMGM
