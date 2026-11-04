/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Degrees, homogeneous components and dimensions of homogeneous submodules

## Main results

* `MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_left`: multiplication by a
  homogeneous polynomial of degree `d` shifts homogeneous components by `d`.
* `MvPolynomial.finrank_homogeneousSubmodule`: over a field, the homogeneous polynomials of
  degree `n` in finitely many variables `σ` form a space of dimension
  `(Fintype.card σ + n - 1).choose n`.
* `MvPolynomial.finrank_homogeneousSubmodule_fin`: the same count for `n + 1` variables, in the
  form `(n + M).choose M`.
* `Sym.equivNatSumLeOfFintype`, `Finsupp.degreeLeEquivSym`: exponent vectors of degree at most
  `n` on `α` are multisets of size `n` on `Option α`.
* `MvPolynomial.finrank_restrictTotalDegree`: over a field, the polynomials of total degree at
  most `N` in finitely many variables `σ` form a space of dimension
  `(Fintype.card σ + N).choose N`.
* `MvPolynomial.degreeOf_aeval_le`: substituting polynomials of degree at most `D` in a variable
  `i` into `f` gives degree at most `D * f.totalDegree` in `i`. Since each matrix entry occurs to
  degree at most one in every maximal minor, substituting maximal minors preserves a degree bound
  in every individual matrix coordinate.
* `MvPolynomial.totalDegree_map_of_injective`: mapping coefficients along an injective ring
  homomorphism preserves the total degree.
* `MvPolynomial.totalDegree_pos_of_ne_zero_of_not_isUnit`: over a field, a nonzero nonunit has
  positive total degree.
* `MvPolynomial.homogeneousComponent_totalDegree_ne_zero`: the homogeneous component of top
  degree of a nonzero polynomial is nonzero.
-/

@[expose] public section

namespace Sym

variable (α : Type*) [DecidableEq α] [Fintype α] (n : ℕ)

/-- Multisets of size `n` on `Option α` correspond to functions `α → ℕ` with sum at most `n`;
the multiplicity of `none` records the slack. -/
noncomputable def equivNatSumLeOfFintype : Sym (Option α) n ≃ {P : α → ℕ // ∑ i, P i ≤ n} :=
  (equivNatSumOfFintype (Option α) n).trans
    (show {P : Option α → ℕ // ∑ i, P i = n} ≃ {P : α → ℕ // ∑ i, P i ≤ n} from
    { toFun q := ⟨fun i ↦ q.val (some i), by
        have h := q.property
        rw [Fintype.sum_option] at h
        change ∑ i, q.val (some i) ≤ n
        omega⟩
      invFun p := ⟨fun j ↦ j.elim (n - ∑ i, p.val i) p.val, by
        simp only [Fintype.sum_option, Option.elim_none, Option.elim_some]
        exact Nat.sub_add_cancel p.property⟩
      left_inv q := by
        apply Subtype.ext
        funext j
        cases j with
        | none =>
          have h := q.property
          rw [Fintype.sum_option] at h
          dsimp
          omega
        | some j => rfl
      right_inv p := rfl })

end Sym

namespace Finsupp

/-- Exponent vectors of degree at most `n` on a finite type `α` correspond to multisets of
size `n` on `Option α`. -/
noncomputable def degreeLeEquivSym (α : Type*) [DecidableEq α] [Fintype α] (n : ℕ) :
    {P : α →₀ ℕ // P.degree ≤ n} ≃ Sym (Option α) n :=
  (equivFunOnFinite.subtypeEquiv fun P ↦ by simp [degree_eq_sum]).trans
    (Sym.equivNatSumLeOfFintype α n).symm

end Finsupp

namespace MvPolynomial

variable {σ K : Type*}

section TotalDegree

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Mapping coefficients never increases the total degree. -/
theorem totalDegree_map_le (f : R →+* S) (p : MvPolynomial σ R) :
    (map f p).totalDegree ≤ p.totalDegree :=
  Finset.sup_mono (support_map_subset _ _)

/-- Mapping coefficients along an injective ring homomorphism preserves the total degree. -/
theorem totalDegree_map_of_injective {f : R →+* S} (hf : Function.Injective f)
    (p : MvPolynomial σ R) : (map f p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective p hf]

/-- Over a field, a nonzero polynomial which is not a unit has positive total degree. -/
theorem totalDegree_pos_of_ne_zero_of_not_isUnit [Field K] {f : MvPolynomial σ K} (hf : f ≠ 0)
    (hu : ¬IsUnit f) : 0 < f.totalDegree := by
  refine Nat.pos_of_ne_zero fun hd ↦ hu ?_
  rw [totalDegree_eq_zero_iff_eq_C.mp hd] at hf ⊢
  exact (isUnit_iff_ne_zero.mpr fun h ↦ hf (by rw [h, map_zero])).map C

/-- Over a field, an irreducible polynomial has positive total degree. -/
theorem totalDegree_pos_of_irreducible [Field K] {f : MvPolynomial σ K} (hf : Irreducible f) :
    0 < f.totalDegree :=
  totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit

/-- The homogeneous component of top degree of a nonzero polynomial is nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun s => s.degree)
  have hdeg : m.degree = p.totalDegree := hd.symm
  intro h
  have hc := congrArg (fun g : MvPolynomial σ R => g.coeff m) h
  rw [coeff_homogeneousComponent, ite_eq_left hdeg] at hc
  exact (mem_support_iff.mp hm) hc

end TotalDegree

/-- Multiplication by a homogeneous polynomial of degree `d` shifts homogeneous components
by `d`. -/
theorem homogeneousComponent_mul_of_isHomogeneous_left [CommRing K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (u : MvPolynomial σ K) (k : ℕ) :
    homogeneousComponent (d + k) (f * u) = f * homogeneousComponent k u := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  have ht := DirectSum.coe_decompose_mul_add_of_left_mem
    (homogeneousSubmodule σ K) (j := k) hf (b := u)
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] using ht

/-- The homogeneous polynomials of degree `n` in finitely many variables `σ` form a space of
dimension `(Fintype.card σ + n - 1).choose n`, the number of monomials of degree `n`. -/
theorem finrank_homogeneousSubmodule [Field K] [Fintype σ] (n : ℕ) :
    Module.finrank K (homogeneousSubmodule σ K n) = (Fintype.card σ + n - 1).choose n := by
  classical
  let e : {p : σ →₀ ℕ // p.degree = n} ≃ Sym σ n :=
    ((Sym.equivNatSum σ n).trans
      (Equiv.subtypeEquivRight fun p => by simp [Finsupp.degree_apply, Finsupp.sum])).symm
  have he : homogeneousSubmodule σ K n = restrictSupport K {p | p.degree = n} := by
    rw [homogeneousSubmodule_eq_finsupp_supported]
    rfl
  rw [he, Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {p : σ →₀ ℕ // p.degree = n} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]

/-- The polynomials of total degree at most `N` in finitely many variables `σ` form a space of
dimension `(Fintype.card σ + N).choose N`, the number of monomials of degree at most `N`. -/
theorem finrank_restrictTotalDegree [Field K] [Fintype σ] (N : ℕ) :
    Module.finrank K (restrictTotalDegree σ K N) = (Fintype.card σ + N).choose N := by
  classical
  have he : restrictTotalDegree σ K N = restrictSupport K {p | p.degree ≤ N} := rfl
  rw [he, Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {p : σ →₀ ℕ // p.degree ≤ N} = _
  rw [Nat.card_congr (Finsupp.degreeLeEquivSym σ N), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_option]
  congr 1
  omega

/-- The homogeneous polynomials of degree `M` in `n + 1` variables form a space of dimension
`(n + M).choose M`. -/
theorem finrank_homogeneousSubmodule_fin [Field K] (n M : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (n + 1)) K M) = (n + M).choose M := by
  rw [finrank_homogeneousSubmodule, Fintype.card_fin]
  congr 1
  omega

/-- Substituting polynomials of degree at most `D` in the variable `i` into `f` gives a
polynomial of degree at most `D * f.totalDegree` in `i`. -/
theorem degreeOf_aeval_le
    {K σ τ : Type*} [Field K] [Finite σ]
    (a : σ → MvPolynomial τ K) (i : τ) (D : ℕ)
    (ha : ∀ j, (a j).degreeOf i ≤ D) (f : MvPolynomial σ K) :
    (aeval a f).degreeOf i ≤ D * f.totalDegree := by
  classical
  let := Fintype.ofFinite σ
  conv_lhs => rw [f.as_sum, map_sum]
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro e he
  rw [aeval_monomial]
  change (C (f.coeff e) * e.prod (fun j k => a j ^ k)).degreeOf i ≤ _
  apply (degreeOf_C_mul_le _ _ _).trans
  rw [Finsupp.prod_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ j, (a j ^ e j).degreeOf i := degreeOf_prod_le _ _ _
    _ ≤ ∑ j, e j * D := Finset.sum_le_sum (fun j _ =>
      (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (ha j)))
    _ = D * e.sum (fun _ k => k) := by
      rw [← Finset.sum_mul, Finsupp.sum_fintype _ _ (by simp), Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left D (le_totalDegree he)

end MvPolynomial
