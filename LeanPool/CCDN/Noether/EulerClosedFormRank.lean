/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateTotalDegree
public import LeanPool.CCDN.Noether.EulerClosedForms
public import LeanPool.CCDN.Noether.EulerPairSpace
import LeanPool.CCDN.Noether.ClosedFormScaling
import LeanPool.CCDN.Noether.ShearNormalization

/-! The Euler-constrained closed-form operator has full rank d^2-1 for
irreducible bivariate equations of full outer degree in characteristic zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The explicit Euler pair, in the nested polynomial ring used by the
closed-form classification. -/
def eulerBivariatePair (R : Type*) [CommRing R] (k : ℕ) :
    EulerPairSpace R k →ₗ[R] R[X][X] × R[X][X] :=
  ((bivariatePolynomialEquiv R).toLinearMap.prodMap
    (bivariatePolynomialEquiv R).toLinearMap).comp (eulerPairCoordinates R k)

private lemma eulerBivariatePair_fst_degree {R : Type*} [CommRing R] (k : ℕ)
    (u : EulerPairSpace R k) : bivariateTotalDegree (eulerBivariatePair R k u).1 ≤ k + 1 := by
  change ((bivariatePolynomialEquiv R).symm
    (bivariatePolynomialEquiv R (eulerPairCoordinates R k u).1)).totalDegree ≤ _
  rw [AlgEquiv.symm_apply_apply]
  exact eulerPairCoordinates_fst_degree k u

private lemma eulerBivariatePair_snd_degree {R : Type*} [CommRing R] (k : ℕ)
    (u : EulerPairSpace R k) : bivariateTotalDegree (eulerBivariatePair R k u).2 ≤ k + 1 := by
  change ((bivariatePolynomialEquiv R).symm
    (bivariatePolynomialEquiv R (eulerPairCoordinates R k u).2)).totalDegree ≤ _
  rw [AlgEquiv.symm_apply_apply]
  exact eulerPairCoordinates_snd_degree k u

private lemma eulerBivariatePair_contraction_degree {R : Type*} [CommRing R] (k : ℕ)
    (u : EulerPairSpace R k) :
    bivariateTotalDegree (bivariateEulerContraction R (eulerBivariatePair R k u)) ≤ k + 1 := by
  simp only [bivariateEulerContraction, eulerBivariatePair, LinearMap.comp_apply,
    LinearMap.prodMap_apply, AlgEquiv.toLinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← bivariatePolynomialEquiv_X_zero, ← bivariatePolynomialEquiv_X_one,
    ← map_mul, ← map_mul, ← map_add]
  change ((bivariatePolynomialEquiv R).symm (bivariatePolynomialEquiv R _)).totalDegree ≤ _
  rw [AlgEquiv.symm_apply_apply]
  exact eulerPairCoordinates_contraction_degree k u

private lemma eulerBivariatePair_injective {F : Type*} [Field F] (k : ℕ) :
    Function.Injective (eulerBivariatePair F k) := by
  intro u v huv
  apply eulerPairCoordinates_injective k
  apply Prod.ext
  · apply (bivariatePolynomialEquiv F).injective
    exact congrArg Prod.fst huv
  · apply (bivariatePolynomialEquiv F).injective
    exact congrArg Prod.snd huv

/-- Closed-form operator on exactly d^2-1 explicit polynomial parameters. -/
def eulerClosedFormOperator {R : Type*} [CommRing R] (k : ℕ) (f : R[X][X]) :
    EulerPairSpace R k →ₗ[R] R[X][X] :=
  (closedFormOperator f).comp (eulerBivariatePair R k)

/-- The Euler constraint removes the only characteristic-zero closed-form
kernel, so the restricted operator is injective. -/
private theorem eulerClosedFormOperator_injective {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hdeg : f.natDegree = k + 2) : Function.Injective (eulerClosedFormOperator k f) := by
  have hzero : ∀ u, eulerClosedFormOperator k f u = 0 → u = 0 := by
    intro u hu
    let p := (eulerBivariatePair F k u).1
    let q := (eulerBivariatePair F k u).2
    have hp : p.degree < f.degree := by
      rw [degree_eq_natDegree hf.ne_zero, hdeg]
      apply degree_le_natDegree.trans_lt
      have hh : p.natDegree < k + 2 := lt_of_le_of_lt
        ((bivariate_natDegree_le_totalDegree p).trans (eulerBivariatePair_fst_degree k u))
        (by omega)
      exact_mod_cast hh
    have hq : q.degree < f.degree := by
      rw [degree_eq_natDegree hf.ne_zero, hdeg]
      apply degree_le_natDegree.trans_lt
      have hh : q.natDegree < k + 2 := lt_of_le_of_lt
        ((bivariate_natDegree_le_totalDegree q).trans (eulerBivariatePair_snd_degree k u))
        (by omega)
      exact_mod_cast hh
    have he : (bivariateEulerContraction F (p, q)).coeff f.natDegree = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hh := (bivariate_natDegree_le_totalDegree
        (bivariateEulerContraction F (eulerBivariatePair F k u))).trans
          (eulerBivariatePair_contraction_degree k u)
      change (bivariateEulerContraction F (eulerBivariatePair F k u)).natDegree < _
      omega
    obtain ⟨hp0,hq0⟩ := bivariate_euler_closed_form_eq_zero f p q hf hm (by omega) hp hq hu he
    apply eulerBivariatePair_injective k
    rw [map_zero]
    exact Prod.ext hp0 hq0
  intro u v huv
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, huv, sub_self]

/-- Over an algebraically closed field of characteristic zero, the Euler closed-form operator of
an irreducible `f` of outer degree `k + 2` whose outer leading coefficient is a nonzero constant
is injective. Scalar normalization changes neither the domain nor injectivity. -/
theorem eulerClosedFormOperator_injective_of_constant_leading
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : F[X][X]) (hf : Irreducible f) (a : F) (ha : a ≠ 0)
    (hl : f.leadingCoeff = C a) (hdeg : f.natDegree = k + 2) :
    Function.Injective (eulerClosedFormOperator k f) := by
  have hm := bivariate_monic_normalize a ha f hl
  have hi := (bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mpr hf
  have hd : (a⁻¹ • f).natDegree = k + 2 := by
    rw [natDegree_smul f (inv_ne_zero ha), hdeg]
  intro u v huv
  apply eulerClosedFormOperator_injective k (a⁻¹ • f) hi hm hd
  change closedFormOperator (a⁻¹ • f) (eulerBivariatePair F k u) =
    closedFormOperator (a⁻¹ • f) (eulerBivariatePair F k v)
  rw [closedFormOperator_smul_equation, closedFormOperator_smul_equation]
  exact congrArg (a⁻¹ • ·) huv

end
end CCDN
