/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ForMathlib.IntegerPolynomialL1
public import LeanPool.CCDN.ForMathlib.Matrix
public import LeanPool.CCDN.Noether.AmbientNoetherForms
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanPool.CCDN.Determinant.GenericPlaneEulerMinorCharZero
import LeanPool.CCDN.Determinant.UniversalPlaneMinor
import LeanPool.CCDN.Noether.AmbientNoetherHeight
import LeanPool.CCDN.Noether.AmbientNoetherVanishing
import LeanPool.CCDN.Noether.EulerPairSpecialization
import Mathlib.Data.Sym.Card

/-!
A finite family of universal integer Noether forms, with the exact
degree and coefficient bound of CCDN Theorem 3.2.2.

Characteristic-zero nonvanishing of the ambient integer
coefficient forms, descended from the algebraic closure.

Every absolutely irreducible characteristic-zero hypersurface of degree
d at least two gives a nonzero Euler minor of order d²−1 in the universal
affine-plane parameter ring.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma eulerClosedFormCoefficientMatrix_smul {R : Type*} [CommRing R]
    (u : R) (k : ℕ) (f : Polynomial (Polynomial R)) :
    eulerClosedFormCoefficientMatrix k (u • f) = u • eulerClosedFormCoefficientMatrix k f := by
  ext row col
  change eulerCoefficientEntryLinear k row col (u • f) =
    u • eulerCoefficientEntryLinear k row col f
  exact map_smul _ _ _

private lemma eulerClosedForm_minor_smul {R : Type*} [CommRing R]
    (u : R) (k r : ℕ) (f : Polynomial (Polynomial R))
    (a : Fin r → ℕ × ℕ) (c : Fin r → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (u • f)).submatrix a c).det =
      u ^ r * ((eulerClosedFormCoefficientMatrix k f).submatrix a c).det := by
  rw [eulerClosedFormCoefficientMatrix_smul]
  change (u • (eulerClosedFormCoefficientMatrix k f).submatrix a c).det = _
  rw [Matrix.det_smul, Fintype.card_fin]

/-- The universal affine-plane family has a nonzero determinant of
the precise Noether order. -/
private theorem exists_universalPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Finite σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : f.totalDegree = k + 2) :
    (eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).HasNonzeroMinor
      ((k + 2) ^ 2 - 1) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨a, b, hb, _, rows, cols, hdet⟩ :=
    exists_positioned_genericPlane_euler_minor_charZero k f hf hd
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  have hne : φ (((eulerClosedFormCoefficientMatrix k
      (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).submatrix
        rows cols).det) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hdet
  rw [eulerClosedForm_minor_map, normalized_genericPlane_universal_specialization,
    eulerClosedForm_minor_smul, ← eulerClosedForm_minor_map] at hne
  refine ⟨rows, cols, ?_⟩
  intro he
  exact hne (by rw [he, map_zero, mul_zero])

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Some constructed universal form detects every absolutely irreducible
homogeneous equation in characteristic zero. -/
theorem exists_ambientNoetherForm_nonzero {K σ : Type*}
    [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous (k + 2))
    (hir : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    ∃ (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)
      (m : PlaneParameters (Option σ) →₀ ℕ),
      homogeneousCoefficientSpecialization (k + 2) f
        (ambientNoetherForm (Option σ) k rows cols m) ≠ 0 := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hd : (MvPolynomial.map φ f).totalDegree = k + 2 := (hf.map φ).totalDegree hir.ne_zero
  obtain ⟨rows, cols, hdet⟩ := exists_universalPlane_euler_minor_charZero
    k (MvPolynomial.map φ f) hir hd
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hdet
  refine ⟨rows, cols, m, ?_⟩
  intro hz
  apply hm
  rw [← ambientEuler_minor_map φ k f rows cols, coeff_map,
    ← ambientNoetherForm_specialize k f hf rows cols m, hz, map_zero]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma finite_homogeneous_coefficientL1_bounded (σ : Type*) [Finite σ]
    (r H : ℕ) :
    {f : MvPolynomial σ ℤ | f.IsHomogeneous r ∧ l1Norm f ≤ H}.Finite := by
  classical
  let := Fintype.ofFinite σ
  let C := ↥(Finset.Icc (-(H : ℤ)) (H : ℤ))
  let F : (Sym σ r → C) → MvPolynomial σ ℤ :=
    fun c => ∑ i, monomial (homogeneousCoefficientExponent σ r i) (c i).val
  apply (Set.finite_range F).subset
  intro f hf
  let c : Sym σ r → C := fun i => ⟨f.coeff (homogeneousCoefficientExponent σ r i), by
    have hh := (natAbs_coeff_le_l1Norm f (homogeneousCoefficientExponent σ r i)).trans hf.2
    have ha : |f.coeff (homogeneousCoefficientExponent σ r i)| ≤ (H : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hh
    exact Finset.mem_Icc.mpr (abs_le.mp ha)⟩
  refine ⟨c, ?_⟩
  exact homogeneousCoefficientData_reconstruct r f hf.1

/-- For fixed `σ` and `k`, there are only finitely many ambient Noether forms. -/
lemma finite_ambientNoetherForms (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) :
    {f | ∃ rows cols m, f = ambientNoetherForm σ k rows cols m}.Finite := by
  apply (finite_homogeneous_coefficientL1_bounded (Sym σ (k + 2))
    ((k + 2) ^ 2 - 1)
    ((k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
      (Fintype.card (Sym σ (k + 2)) * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1))).subset
  rintro f ⟨rows,cols,m,rfl⟩
  exact ⟨ambientNoetherForm_homogeneous σ k rows cols m,
    ambientNoetherForm_coefficientL1_le σ k rows cols m⟩

/-- The finite collection of universal Noether forms of degree `k + 2` in the variables `σ`: the
extracted plane-parameter coefficients of all Euler minors of the universal plane restriction of
the universal homogeneous form. -/
def universalNoetherForms (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) :
    Finset (MvPolynomial (Sym σ (k + 2)) ℤ) :=
  (finite_ambientNoetherForms σ k).toFinset

private lemma mem_universalNoetherForms {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Sym σ (k + 2)) ℤ) :
    f ∈ universalNoetherForms σ k ↔ ∃ rows cols m, f = ambientNoetherForm σ k rows cols m := by
  exact Set.Finite.mem_toFinset _

/-- Every universal Noether form is homogeneous of degree `(k + 2) ^ 2 - 1`. -/
theorem universalNoetherForms_homogeneous {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℕ) (g : MvPolynomial (Sym σ (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms σ k) :
    g.IsHomogeneous ((k + 2) ^ 2 - 1) := by
  obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k g).mp hg
  exact ambientNoetherForm_homogeneous σ k rows cols m

private lemma card_homogeneousCoefficientIndices (n d : ℕ) :
    Fintype.card (Sym (Option (Fin n)) d) = (n + d).choose n := by
  rw [Sym.card_sym_eq_choose, Fintype.card_option, Fintype.card_fin]
  have he : n + 1 + d - 1 = n + d := by omega
  rw [he, ← Nat.choose_symm (show d ≤ n + d by omega)]
  congr 1
  omega

/-- The printed integer coefficient bound: in `n + 1` homogeneous variables, every universal
Noether form has coefficient ℓ¹-norm at most
`(k + 2) ^ (3 * (k + 2) ^ 2 - 3) * (choose (n + k + 2) n * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1)`. -/
theorem universalNoetherForms_coefficientL1_le (n k : ℕ)
    (g : MvPolynomial (Sym (Option (Fin n)) (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms (Option (Fin n)) k) :
    l1Norm g ≤
      (k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
        ((n + (k + 2)).choose n * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1) := by
  obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k g).mp hg
  simpa only [card_homogeneousCoefficientIndices] using
    ambientNoetherForm_coefficientL1_le (Option (Fin n)) k rows cols m

/-- Every universal Noether form vanishes on a geometrically reducible homogeneous equation of
degree `k + 2`, over an arbitrary field, with no characteristic assumption. -/
theorem universalNoetherForms_vanish {K σ : Type*} [Field K]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous (k + 2))
    (hred : ¬Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (g : MvPolynomial (Sym σ (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms σ k) :
    homogeneousCoefficientSpecialization (k + 2) f g = 0 := by
  obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k g).mp hg
  exact ambientNoetherForm_eq_zero_of_not_absolutely_irreducible k f hf hred rows cols m

/-- In characteristic zero, an absolutely irreducible homogeneous equation of degree `k + 2`
makes at least one universal Noether form nonzero. -/
theorem universalNoetherForms_nonvanishing {K σ : Type*} [Field K] [CharZero K]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous (k + 2))
    (hir : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    ∃ g ∈ universalNoetherForms (Option σ) k,
      homogeneousCoefficientSpecialization (k + 2) f g ≠ 0 := by
  obtain ⟨rows,cols,m,hne⟩ := exists_ambientNoetherForm_nonzero k f hf hir
  exact ⟨_, (mem_universalNoetherForms _ _).mpr ⟨rows,cols,m,rfl⟩, hne⟩

end
end CCDN
