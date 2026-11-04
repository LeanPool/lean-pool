/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Polynomial.Basic

/-! Homogeneity in the coefficient variables, while retaining independent
polynomial parameters. This property survives determinant expansion and
extraction of any parameter coefficient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A polynomial `f` in the variables `σ` with coefficients in `MvPolynomial τ R` is coefficientwise
homogeneous of degree `d` if each of its coefficients is a homogeneous polynomial of degree `d` in
the variables `τ`. -/
def CoefficientwiseHomogeneous {R σ τ : Type*} [CommRing R]
    (f : MvPolynomial σ (MvPolynomial τ R)) (d : ℕ) : Prop :=
  ∀ m, (f.coeff m).IsHomogeneous d

namespace CoefficientwiseHomogeneous

variable {R σ τ : Type*} [CommRing R]

/-- The zero polynomial is coefficientwise homogeneous of every degree. -/
lemma zero (d : ℕ) : CoefficientwiseHomogeneous (0 : MvPolynomial σ (MvPolynomial τ R)) d := by
  intro m
  simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using isHomogeneous_zero τ R d

/-- A sum of two coefficientwise homogeneous polynomials of degree `d` is coefficientwise
homogeneous of degree `d`. -/
lemma add {f g : MvPolynomial σ (MvPolynomial τ R)} {d : ℕ}
    (hf : CoefficientwiseHomogeneous f d) (hg : CoefficientwiseHomogeneous g d) :
    CoefficientwiseHomogeneous (f + g) d := by
  intro m
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (hf m).add (hg m)

/-- The negation of a coefficientwise homogeneous polynomial of degree `d` is coefficientwise
homogeneous of degree `d`. -/
lemma neg {f : MvPolynomial σ (MvPolynomial τ R)} {d : ℕ}
    (hf : CoefficientwiseHomogeneous f d) :
    CoefficientwiseHomogeneous (-f) d := by
  intro m
  rw [coeff_neg]
  exact (hf m).neg

/-- A finite sum of coefficientwise homogeneous polynomials of degree `d` is coefficientwise
homogeneous of degree `d`. -/
lemma sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ R)) (d : ℕ)
    (hf : ∀ i ∈ s, CoefficientwiseHomogeneous (f i) d) :
    CoefficientwiseHomogeneous (∑ i ∈ s, f i) d := by
  intro m
  rw [coeff_sum]
  exact IsHomogeneous.sum s _ d (fun i hi => hf i hi m)

/-- The product of coefficientwise homogeneous polynomials of degrees `d` and `e` is coefficientwise
homogeneous of degree `d + e`. -/
lemma mul {f g : MvPolynomial σ (MvPolynomial τ R)} {d e : ℕ}
    (hf : CoefficientwiseHomogeneous f d) (hg : CoefficientwiseHomogeneous g e) :
    CoefficientwiseHomogeneous (f * g) (d + e) := by
  classical
  intro m
  rw [coeff_mul]
  exact IsHomogeneous.sum _ _ _ (fun ij _ => (hf ij.1).mul (hg ij.2))

/-- The constant polynomial `C f` is coefficientwise homogeneous of degree `d` when `f` is a
homogeneous polynomial of degree `d` in the variables `τ`. -/
lemma C_of_isHomogeneous {f : MvPolynomial τ R} {d : ℕ} (hf : f.IsHomogeneous d) :
    CoefficientwiseHomogeneous (MvPolynomial.C f : MvPolynomial σ (MvPolynomial τ R)) d := by
  classical
  intro m
  rw [coeff_C]
  split_ifs
  · exact hf
  · exact isHomogeneous_zero τ R d

/-- The polynomial `1` is coefficientwise homogeneous of degree `0`. -/
lemma one : CoefficientwiseHomogeneous (1 : MvPolynomial σ (MvPolynomial τ R)) 0 := by
  simpa only [map_one] using C_of_isHomogeneous (σ := σ) (isHomogeneous_one τ R)

/-- A polynomial over `R`, with its coefficients viewed as constants of `MvPolynomial τ R`, is
coefficientwise homogeneous of degree `0`. -/
lemma map_C (f : MvPolynomial σ R) :
    CoefficientwiseHomogeneous
      (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) f) 0 := by
  intro m
  rw [coeff_map]
  exact isHomogeneous_C _ _

/-- A finite product of coefficientwise homogeneous polynomials of degrees `d i` is coefficientwise
homogeneous of degree `∑ i ∈ s, d i`. -/
lemma prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ R))
    (d : ι → ℕ) (hf : ∀ i ∈ s, CoefficientwiseHomogeneous (f i) (d i)) :
    CoefficientwiseHomogeneous (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using one (R := R) (σ := σ) (τ := τ)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The determinant of an `r × r` matrix whose entries are coefficientwise homogeneous of degree `1`
is coefficientwise homogeneous of degree `r`. -/
lemma det {r : ℕ} (M : Matrix (Fin r) (Fin r) (MvPolynomial σ (MvPolynomial τ R)))
    (hM : ∀ i j, CoefficientwiseHomogeneous (M i j) 1) :
    CoefficientwiseHomogeneous M.det r := by
  classical
  rw [Matrix.det_apply']
  apply sum
  intro π _
  have hp := prod Finset.univ (fun i => M (π i) i) (fun _ => 1) (fun i _ => hM _ i)
  have hp' : CoefficientwiseHomogeneous (∏ i, M (π i) i) r := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hp
  have hc : CoefficientwiseHomogeneous
      (MvPolynomial.C (MvPolynomial.C ((Equiv.Perm.sign π : ℤ) : R)) :
        MvPolynomial σ (MvPolynomial τ R)) 0 :=
    C_of_isHomogeneous (isHomogeneous_C τ _)
  have hh := hc.mul hp'
  simpa only [zero_add, map_intCast] using hh

end CoefficientwiseHomogeneous
end
end CCDN
