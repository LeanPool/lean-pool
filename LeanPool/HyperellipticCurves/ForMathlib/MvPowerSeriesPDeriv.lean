/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution

import Mathlib.RingTheory.MvPowerSeries.PiTopology

/-!
# Substitution and partial derivatives of multivariate power series

Additions to Mathlib's `MvPowerSeries.subst` and `MvPowerSeries.pderiv`, the substitution of
a family of power series and the formal partial derivative with respect to a variable. The
chain rule for substitution (`MvPowerSeries.pderiv_subst`) is proved by continuity and
density from the polynomial case: both sides are continuous for the product topologies with
*any* ring topology, so the proof instals the discrete topology and the statement remains
topology-free.

The prime in `MvPowerSeries.continuous_subst'` distinguishes it from Mathlib's
`MvPowerSeries.continuous_subst`, which assumes the discrete uniformity on the coefficients,
whereas here they may carry any ring topology.

## Main definitions

* `MvPowerSeries.substRingHom`: substitution as a ring homomorphism, for use where a plain
  ring homomorphism is wanted — in particular between series over *different* variable types.

## Main statements

* `MvPowerSeries.continuous_subst'`, `MvPowerSeries.continuous_pderiv`: substitution and
  partial differentiation are continuous for the product topologies.
* `MvPowerSeries.pderiv_subst`: the chain rule, and `MvPowerSeries.pderiv_subst_eq_zero` its
  consequence for a family all of whose members are annihilated by the derivative.
* `MvPowerSeries.coeff_sum_X_mul_pderiv`: the Euler identity, `∑ s, X s * ∂/∂X s` acting on
  the degree-`n` part as multiplication by `n`.
* `MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero`: substituting a family without
  constant terms preserves the constant coefficient (Mathlib's
  `MvPowerSeries.constantCoeff_subst_eq_zero` only kills it, at the price of a hypothesis on
  the series substituted into).
* `MvPowerSeries.pderiv_comm`, `MvPowerSeries.rename_pderiv`, `MvPowerSeries.map_pderiv`:
  partial derivatives commute with each other, with renaming the variables along an
  equivalence, and with a coefficient ring homomorphism.
-/

@[expose] public section

open Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace MvPowerSeries

section subst

variable {σ R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Substitution of power series is continuous, coefficientwise: each coefficient of
`subst a f` is a fixed finite linear combination of coefficients of `f`.
This generalizes `MvPowerSeries.continuous_subst` from discrete coefficients to any
topological ring of coefficients. -/
theorem continuous_subst' {τ : Type*} {a : τ → MvPowerSeries σ R}
    (ha : MvPowerSeries.HasSubst a) :
    Continuous (MvPowerSeries.subst a : MvPowerSeries τ R → MvPowerSeries σ R) := by
  classical
  have hc (e : σ →₀ ℕ) : (Function.support fun d : τ →₀ ℕ ↦
      MvPowerSeries.coeff e (d.prod fun s i ↦ (a s) ^ i)).Finite := by
    have h1 := MvPowerSeries.coeff_subst_finite ha
      ((fun _ ↦ 1) : MvPowerSeries τ R) e
    simpa [Function.HasFiniteSupport, show ∀ d, MvPowerSeries.coeff (R := R) d
      ((fun _ ↦ 1) : MvPowerSeries τ R) = 1 from fun d ↦ rfl] using h1
  refine continuous_pi fun e ↦ ?_
  change Continuous fun f : MvPowerSeries τ R ↦ MvPowerSeries.coeff e (MvPowerSeries.subst a f)
  have heq : (fun f : MvPowerSeries τ R ↦ MvPowerSeries.coeff e (MvPowerSeries.subst a f))
      = fun f ↦ ∑ d ∈ (hc e).toFinset,
          MvPowerSeries.coeff d f * MvPowerSeries.coeff e (d.prod fun s i ↦ (a s) ^ i) := by
    funext f
    rw [MvPowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset]
    · exact Finset.sum_congr rfl fun d _ ↦ smul_eq_mul _ _
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      exact fun h0 ↦ hd (by rw [h0, smul_zero])
  rw [heq]
  exact continuous_finsetSum _ fun d _ ↦
    (MvPowerSeries.WithPiTopology.continuous_coeff R d).mul continuous_const

end subst

variable {σ R : Type*} [CommRing R]

/-- Substitution along families with vanishing constant coefficients preserves the
constant coefficient. Unlike Mathlib's `MvPowerSeries.constantCoeff_subst_eq_zero`, no
hypothesis on `f`: the constant coefficient is preserved, not just killed. -/
theorem constantCoeff_subst_of_constantCoeff_zero {τ : Type*}
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    (ha' : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries τ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  classical
  rw [constantCoeff_subst ha, finsum_eq_single _ 0 ?_]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
    rw [Finsupp.prod, map_prod, smul_eq_mul,
      Finset.prod_eq_zero hs (by
        rw [map_pow, ha' s, zero_pow (Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp hs)).ne']), mul_zero]

section substitution

variable {τ : Type*} {a : τ → MvPowerSeries σ R}

/-- Base change of a family with vanishing constant coefficients is again substitutable. -/
theorem hasSubst_map_of_constantCoeff_zero {S : Type*} [CommRing S] [Finite τ] (φ : R →+* S)
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst fun s ↦ map φ (a s) :=
  hasSubst_of_constantCoeff_zero fun s ↦ by rw [constantCoeff_map, ha s, map_zero]

/-- Substitution of a substitutable family of power series, as a ring homomorphism. Same
underlying function as `MvPowerSeries.substAlgHom`, but usable where a plain ring
homomorphism is wanted (in particular between series over *different* variable types with no
algebra structure relating them). -/
noncomputable def substRingHom (ha : HasSubst a) :
    MvPowerSeries τ R →+* MvPowerSeries σ R :=
  (substAlgHom ha).toRingHom

theorem substRingHom_apply (ha : HasSubst a) (f : MvPowerSeries τ R) :
    substRingHom ha f = subst a f :=
  substAlgHom_apply ha f

@[simp]
theorem substRingHom_X (ha : HasSubst a) (s : τ) : substRingHom ha (X s) = a s := by
  rw [substRingHom_apply, subst_X ha]

theorem substRingHom_comp_C (ha : HasSubst a) :
    (substRingHom ha).comp (C : R →+* MvPowerSeries τ R) = C :=
  RingHom.ext fun r ↦ by rw [RingHom.comp_apply, substRingHom_apply, subst_C]

theorem constantCoeff_substRingHom (ha : HasSubst a) (ha' : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries τ R) : constantCoeff (substRingHom ha f) = constantCoeff f := by
  rw [substRingHom_apply, constantCoeff_subst_of_constantCoeff_zero ha ha']

/-- Base change commutes with substitution. -/
theorem map_substRingHom {S : Type*} [CommRing S] (φ : R →+* S) (ha : HasSubst a)
    (haφ : HasSubst fun s ↦ map φ (a s)) (f : MvPowerSeries τ R) :
    map φ (substRingHom ha f) = substRingHom haφ (map φ f) := by
  rw [substRingHom_apply, substRingHom_apply, map_subst ha]

end substitution

/-- `pderiv s` is continuous for the product topology: each coefficient of the derivative is
a fixed multiple of a single coefficient of the argument. Together with `continuous_subst'`
this is what carries the chain rule `pderiv_subst` from polynomials to power series by
density. -/
theorem continuous_pderiv [TopologicalSpace R] [IsTopologicalSemiring R] (s : σ) :
    Continuous (pderiv s : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_pi fun d ↦ ?_
  change Continuous fun h : MvPowerSeries σ R ↦ coeff d (pderiv s h)
  simp only [coeff_pderiv]
  exact (WithPiTopology.continuous_coeff R _).mul continuous_const

-- The chain rule at a polynomial. The general case follows by density (`pderiv_subst`);
-- the induction is on the polynomial, so it cannot be run on a power series directly.
private theorem pderiv_subst_coe {τ : Type*} [Fintype τ] {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a) (s : σ) (p : MvPolynomial τ R) :
    pderiv s (subst a (p : MvPowerSeries τ R))
      = ∑ t : τ, subst a (pderiv t (p : MvPowerSeries τ R)) * pderiv s (a t) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hCc : subst a (C c : MvPowerSeries τ R) = C c := by
      rw [← coe_substAlgHom ha]
      exact (substAlgHom ha).commutes c
    have h0 : subst a (0 : MvPowerSeries τ R) = 0 := by
      rw [← MvPowerSeries.coe_substAlgHom ha]
      exact map_zero _
    rw [MvPolynomial.coe_C, hCc, pderiv_C]
    symm
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    rw [pderiv_C, h0, zero_mul]
  | add p q hp hq =>
    push_cast
    rw [MvPowerSeries.subst_add ha, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [map_add, MvPowerSeries.subst_add ha]
    ring
  | mul_X p i ih =>
    push_cast
    rw [MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul, ih]
    have hexp (t : τ) : subst a (pderiv t ((p : MvPowerSeries τ R) * X i))
        = (if i = t then subst a (p : MvPowerSeries τ R) else 0)
          + a i * subst a (pderiv t (p : MvPowerSeries τ R)) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X, Pi.single_apply,
        MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha,
        MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha]
      split
      · rw [← MvPowerSeries.coe_substAlgHom ha, map_one, mul_one]
      · rw [← MvPowerSeries.coe_substAlgHom ha, map_zero, mul_zero]
    simp only [hexp, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    ring

/-- The chain rule for formal partial derivatives of a substitution. -/
theorem pderiv_subst {τ : Type*} [Fintype τ] {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a) (s : σ) (f : MvPowerSeries τ R) :
    pderiv s (subst a f) = ∑ t : τ, subst a (pderiv t f) * pderiv s (a t) := by
  let : UniformSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  have key := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (σ := τ) (R := R)
  have h1 : Continuous fun f : MvPowerSeries τ R ↦ pderiv s (subst a f) :=
    (continuous_pderiv s).comp (continuous_subst' ha)
  have h2 : Continuous fun f : MvPowerSeries τ R ↦
      ∑ t : τ, subst a (pderiv t f) * pderiv s (a t) :=
    continuous_finsetSum _ fun t _ ↦
      ((continuous_subst' ha).comp (continuous_pderiv t)).mul_const _
  exact congrFun (key.equalizer h1 h2 (funext (pderiv_subst_coe ha s))) f

/-- Formal partial derivatives commute. -/
theorem pderiv_comm (s t : σ) (h : MvPowerSeries σ R) :
    pderiv s (pderiv t h) = pderiv t (pderiv s h) := by
  ext d
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv,
    add_right_comm d (Finsupp.single s 1) (Finsupp.single t 1)]
  rcases eq_or_ne s t with rfl | hst
  · ring
  · have h1 : (d + Finsupp.single s 1 : σ →₀ ℕ) t = d t := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hst), add_zero]
    have h2 : (d + Finsupp.single t 1 : σ →₀ ℕ) s = d s := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hst, add_zero]
    rw [h1, h2]
    ring

/-- A substitution whose family is annihilated by `∂_s` is annihilated by `∂_s`. -/
theorem pderiv_subst_eq_zero {τ : Type*} [Finite τ] {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a) (s : σ) (hz : ∀ t, pderiv s (a t) = 0) (f : MvPowerSeries τ R) :
    pderiv s (subst a f) = 0 := by
  cases nonempty_fintype τ
  rw [pderiv_subst ha]
  exact Finset.sum_eq_zero fun t _ ↦ by rw [hz t, mul_zero]

theorem coeff_X_mul_pderiv (s : σ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (X s * pderiv s f) = ((d s : ℕ) : R) * coeff d f := by
  classical
  rw [mul_comm, show (X s : MvPowerSeries σ R) = monomial (Finsupp.single s 1) 1 from rfl,
    coeff_mul_monomial]
  rcases eq_or_ne (d s) 0 with h0 | h0
  · rw [ite_eq_right fun hle ↦ by simpa [h0] using Finsupp.single_le_iff.mp hle, h0]
    simp
  · have hle : Finsupp.single s 1 ≤ d :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
    have h1 : ((d - Finsupp.single s 1 : σ →₀ ℕ) s : R) + 1 = (d s : R) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h0)]
      ring
    rw [ite_eq_left hle, mul_one, coeff_pderiv, tsub_add_cancel_of_le hle, h1, mul_comm]

/-- The Euler identity for formal power series: the operator `∑ s, X s * ∂/∂X s` acts on
the degree-`n` homogeneous part as multiplication by `n`. -/
theorem coeff_sum_X_mul_pderiv [Fintype σ] (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (∑ s, X s * pderiv s f) = ((d.degree : ℕ) : R) * coeff d f := by
  rw [map_sum, Finset.sum_congr rfl fun s _ ↦ coeff_X_mul_pderiv s f d, ← Finset.sum_mul,
    Finsupp.degree_eq_sum]
  push_cast
  rfl

theorem coeff_rename_equiv {τ : Type*} (e : σ ≃ τ) (f : MvPowerSeries σ R) (d : τ →₀ ℕ) :
    coeff d (rename (⇑e) f) = coeff (Finsupp.equivMapDomain e.symm d) f := by
  have hemb : Finsupp.embDomain e.toEmbedding = Finsupp.equivMapDomain (M := ℕ) e := by
    funext v
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain]
    rfl
  have hd : Finsupp.embDomain e.toEmbedding (Finsupp.equivMapDomain e.symm d) = d := by
    rw [hemb, ← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self,
      Finsupp.equivMapDomain_refl]
  calc coeff d (rename (⇑e) f)
      = coeff (Finsupp.embDomain e.toEmbedding (Finsupp.equivMapDomain e.symm d))
          (rename (⇑e) f) := by rw [hd]
    _ = coeff (Finsupp.equivMapDomain e.symm d) f := coeff_embDomain_rename _ _ _

/-- Formal partial derivatives commute with variable renaming along an equivalence. -/
theorem rename_pderiv {τ : Type*} (e : σ ≃ τ) (s : σ) (f : MvPowerSeries σ R) :
    rename (⇑e) (pderiv s f) = pderiv (e s) (rename (⇑e) f) := by
  ext d
  rw [coeff_pderiv, coeff_rename_equiv, coeff_rename_equiv, coeff_pderiv]
  have h1 : Finsupp.equivMapDomain e.symm (d + Finsupp.single (e s) 1)
      = Finsupp.equivMapDomain e.symm d + Finsupp.single s 1 := by
    ext t
    classical
    simp [Finsupp.single_apply, e.injective.eq_iff]
  have h2 : Finsupp.equivMapDomain e.symm d s = d (e s) := by simp
  rw [h1, h2]

/-- Formal partial derivatives commute with a coefficient ring homomorphism. -/
theorem map_pderiv {S : Type*} [CommRing S] (f : R →+* S) (s : σ) (g : MvPowerSeries σ R) :
    map f (pderiv s g) = pderiv s (map f g) := by
  ext d
  simp [coeff_pderiv]

end MvPowerSeries

end
