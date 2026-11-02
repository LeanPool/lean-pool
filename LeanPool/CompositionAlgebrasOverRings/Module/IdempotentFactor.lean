/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Modules over an idempotent factor of a ring

For an idempotent `e` of a commutative ring `k`, the quotient `S = k ⧸ (1 - e)` is the factor of
`k` cut out by `e`, and `Spec S` is the clopen set of primes containing `1 - e`. This file
compares modules over `S` with modules over `k`.

An `S`-module `P` is a `k`-module by restriction of scalars, and as such it is the base change of
itself (`Module.isBaseChange_self_of_surjective`): `S ⊗[k] P ≅ P`. If `P` is finitely generated
projective over `S`, it is finitely generated projective over `k`, and its rank at a prime `p` of
`k` is its rank over `S` at the corresponding prime when `1 - e ∈ p`, and `0` otherwise.

The point is `Module.free_of_forall_free_of_isIdempotentElem`: if every finitely generated
projective `k`-module of constant rank is free, then so is every finitely generated projective
`S`-module of constant rank. A constant-rank-`r` module `P` over `S` becomes one over `k` after
adding the free module of rank `r` over the complementary factor `k ⧸ (e)`; that sum is free over
`k`, and `P` is its base change to `S`. This is the reduction used tacitly in `GPR 22.16` when the
freeness hypothesis on `k` is applied to the rank components of a composition algebra.

## Main results

* `Module.isBaseChange_self_of_surjective` : over a surjection `k → S`, an `S`-module is its own
  base change.
* `Module.projective_of_isIdempotentElem`, `Module.finite_of_isIdempotentElem` : a finitely
  generated projective module over `k ⧸ (1 - e)` is finitely generated projective over `k`.
* `Module.rankAtStalk_comap_of_isIdempotentElem`,
  `Module.rankAtStalk_eq_zero_of_isIdempotentElem` : its rank over `k`.
* `Module.free_of_forall_free_of_isIdempotentElem` : freeness of constant-rank projectives passes
  from `k` to its idempotent factors.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 9.31, 22.16.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

section Surjective

variable {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Algebra k S]
  (hS : Function.Surjective (algebraMap k S))
  (P : Type w) [AddCommGroup P] [Module k P] [Module S P] [IsScalarTower k S P]

include hS in
/-- Over a surjection `k → S`, an `S`-module is its own base change: `S ⊗[k] P ≅ P`, by
`a ⊗ x ↦ a • x`. Every `a ∈ S` lifts to `k`, so every tensor is of the form `1 ⊗ x`. -/
theorem isBaseChange_self_of_surjective :
    IsBaseChange S ((LinearMap.id : P →ₗ[S] P).restrictScalars k) := by
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g ↦ ?_
  -- A `k`-linear map out of an `S`-module is `S`-linear, since every scalar of `S` lifts to `k`.
  let g' : P →ₗ[S] Q :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun a x ↦ by
        obtain ⟨b, rfl⟩ := hS a
        rw [algebraMap_smul, g.map_smul, RingHom.id_apply, algebraMap_smul] }
  refine ⟨g', LinearMap.ext fun _ ↦ rfl, fun g'' hg'' ↦ LinearMap.ext fun x ↦ ?_⟩
  exact LinearMap.congr_fun hg'' x

end Surjective

section Idempotent

variable {k : Type u} [CommRing k] {e : k} (he : IsIdempotentElem e)

/-- In `k ⧸ (1 - e)` the element `e` becomes `1`. -/
theorem algebraMap_quotient_one_sub_self :
    algebraMap k (k ⧸ Ideal.span {1 - e}) e = 1 := by
  rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
    show e - 1 = -(1 - e) by ring]
  exact Submodule.neg_mem _ (Ideal.mem_span_singleton_self _)

include he in
/-- The factor `k ⧸ (1 - e)` is a direct summand of `k`: the class of `x` ↦ `e x` splits the
quotient map. -/
theorem projective_quotient_one_sub :
    Module.Projective k (k ⧸ Ideal.span {1 - e}) := by
  let I : Ideal k := Ideal.span {1 - e}
  have hle : I ≤ LinearMap.ker (LinearMap.mulLeft k e) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.mulLeft_apply, mul_sub, mul_one, he.eq, sub_self]
  refine Module.Projective.of_split (M := k) (I.liftQ (LinearMap.mulLeft k e) hle) I.mkQ ?_
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
    LinearMap.mulLeft_apply, LinearMap.id_comp]
  rw [Submodule.Quotient.eq, ← sub_one_mul, ← neg_sub, neg_mul]
  exact I.neg_mem (I.mul_mem_right x (Ideal.mem_span_singleton_self _))

variable (P : Type w) [AddCommGroup P] [Module (k ⧸ Ideal.span {1 - e}) P] [Module k P]
  [IsScalarTower k (k ⧸ Ideal.span {1 - e}) P]

include he in
/-- A projective module over the factor `k ⧸ (1 - e)` is projective over `k`. -/
theorem projective_of_isIdempotentElem [Module.Projective (k ⧸ Ideal.span {1 - e}) P] :
    Module.Projective k P := by
  classical
  have := projective_quotient_one_sub he
  have : Module.Projective k (P →₀ (k ⧸ Ideal.span {1 - e})) :=
    Module.Projective.of_equiv' (finsuppLequivDFinsupp k).symm
  obtain ⟨s, hs⟩ := ‹Module.Projective (k ⧸ Ideal.span {1 - e}) P›.out
  exact Module.Projective.of_split (s.restrictScalars k)
    ((Finsupp.linearCombination _ id).restrictScalars k) (LinearMap.ext hs)

/-- A finitely generated module over the factor `k ⧸ (1 - e)` is finitely generated over `k`. -/
theorem finite_of_isIdempotentElem [Module.Finite (k ⧸ Ideal.span {1 - e}) P] :
    Module.Finite k P :=
  Module.Finite.trans (k ⧸ Ideal.span {1 - e}) P

variable [Module.Finite (k ⧸ Ideal.span {1 - e}) P] [Module.Projective (k ⧸ Ideal.span {1 - e}) P]

include he in
/-- At a prime of `k` containing `1 - e`, the rank of a finitely generated projective module over
`k ⧸ (1 - e)` is its rank over the factor. -/
theorem rankAtStalk_comap_of_isIdempotentElem (q : PrimeSpectrum (k ⧸ Ideal.span {1 - e})) :
    rankAtStalk (R := k) P (q.comap (algebraMap k (k ⧸ Ideal.span {1 - e}))) =
      rankAtStalk (R := k ⧸ Ideal.span {1 - e}) P q := by
  have := projective_of_isIdempotentElem he P
  have := finite_of_isIdempotentElem (e := e) P
  exact (rankAtStalk_isBaseChange
    (isBaseChange_self_of_surjective Ideal.Quotient.mk_surjective P) q).symm

include he in
/-- At a prime of `k` not containing `1 - e`, a finitely generated projective module over
`k ⧸ (1 - e)` has rank zero: `1 - e` kills it and is a unit there. -/
theorem rankAtStalk_eq_zero_of_isIdempotentElem (p : PrimeSpectrum k)
    (hp : 1 - e ∉ p.asIdeal) : rankAtStalk (R := k) P p = 0 := by
  have := projective_of_isIdempotentElem he P
  have := finite_of_isIdempotentElem (e := e) P
  rw [rankAtStalk_eq_zero_iff_notMem_support, Module.mem_support_iff_of_finite]
  refine fun h ↦ hp (h (Module.mem_annihilator.mpr fun x ↦ ?_))
  rw [← algebraMap_smul (k ⧸ Ideal.span {1 - e}), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_smul]

omit [Module.Finite (k ⧸ Ideal.span {1 - e}) P] [Module.Projective (k ⧸ Ideal.span {1 - e}) P]
  [Module k P] [IsScalarTower k (k ⧸ Ideal.span {1 - e}) P] in
include he in
/-- **Freeness passes to idempotent factors.** If every finitely generated projective `k`-module of
constant rank is free, so is every finitely generated projective module of constant rank over the
factor `k ⧸ (1 - e)`.

A module `P` of constant rank `r` over `k ⧸ (1 - e)` is, as a `k`-module, of rank `r` on the primes
containing `1 - e` and of rank `0` on the others; adding the free module of rank `r` over the
complementary factor `k ⧸ (e)` gives a `k`-module `N` of constant rank `r`. `N` is free by
hypothesis, hence so is its base change to `k ⧸ (1 - e)`, which is `P`. -/
theorem free_of_forall_free_of_isIdempotentElem
    (hfree : ∀ (N : Type (max u w)) [AddCommGroup N] [Module k N] [Module.Finite k N]
      [Module.Projective k N] (r : ℕ), rankAtStalk (R := k) N = (fun _ ↦ r) → Module.Free k N)
    (P : Type (max u w)) [AddCommGroup P] [Module (k ⧸ Ideal.span {1 - e}) P]
    [Module.Finite (k ⧸ Ideal.span {1 - e}) P] [Module.Projective (k ⧸ Ideal.span {1 - e}) P]
    (r : ℕ) (hP : rankAtStalk (R := k ⧸ Ideal.span {1 - e}) P = fun _ ↦ r) :
    Module.Free (k ⧸ Ideal.span {1 - e}) P := by
  set S := k ⧸ Ideal.span {1 - e}
  set S' := k ⧸ Ideal.span {1 - (1 - e)}
  have he' : IsIdempotentElem (1 - e) := he.one_sub
  let : Module k P := Module.compHom P (algebraMap k S)
  have : IsScalarTower k S P :=
    ⟨fun a b x ↦ by
      change (a • b) • x = algebraMap k S a • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
  have := projective_of_isIdempotentElem he P
  have := finite_of_isIdempotentElem (e := e) P
  have := projective_of_isIdempotentElem he' (Fin r → S')
  have := finite_of_isIdempotentElem (e := 1 - e) (Fin r → S')
  -- The padded module has constant rank `r` over `k`.
  have hN : rankAtStalk (R := k) (P × (Fin r → S')) = fun _ ↦ r := by
    funext p
    rw [rankAtStalk_prod, Pi.add_apply]
    by_cases h : 1 - e ∈ p.asIdeal
    · obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap k S)) := by
        change p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {1 - e})))
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
          PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker,
          SetLike.coe_subset_coe, Ideal.span_le, Set.singleton_subset_iff]
        exact h
      rw [rankAtStalk_comap_of_isIdempotentElem he P q, hP,
        rankAtStalk_eq_zero_of_isIdempotentElem he' (Fin r → S') _ ?_, add_zero]
      rw [sub_sub_cancel]
      intro he₀
      have : (1 : k) ∈ (q.comap (algebraMap k S)).asIdeal := by
        simpa using Ideal.add_mem _ h he₀
      exact (q.comap (algebraMap k S)).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    · have he₀ : 1 - (1 - e) ∈ p.asIdeal := by
        rw [sub_sub_cancel]
        refine (p.isPrime.mem_or_mem ?_).resolve_right h
        rw [he.mul_one_sub_self]
        exact p.asIdeal.zero_mem
      obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap k S')) := by
        change p ∈ Set.range
          (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {1 - (1 - e)})))
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
          PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker,
          SetLike.coe_subset_coe, Ideal.span_le, Set.singleton_subset_iff]
        exact he₀
      have : Nontrivial S' := Ideal.Quotient.nontrivial_iff.mpr fun htop ↦
        (q.comap (algebraMap k S')).isPrime.ne_top
          (top_le_iff.mp (htop ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr he₀)))
      rw [rankAtStalk_eq_zero_of_isIdempotentElem he P _ h,
        rankAtStalk_comap_of_isIdempotentElem he' (Fin r → S') q,
        rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun, zero_add]
      rfl
  have := hfree (P × (Fin r → S')) r hN
  -- The base change of the padding to `k ⧸ (1 - e)` vanishes: `e` acts as `1` there, as `0` on it.
  have hzero : Subsingleton (S ⊗[k] (Fin r → S')) := by
    refine subsingleton_of_forall_eq 0 fun t ↦ ?_
    induction t using TensorProduct.inductionOn with
    | tmul a f =>
      have hf : e • f = 0 := by
        funext i
        rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def,
          show algebraMap k S' e = 0 by
            rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
            rw [show (1 : k) - (1 - e) = e from sub_sub_cancel 1 e]
            exact Ideal.mem_span_singleton_self _,
          zero_mul]
      rw [← one_smul S a, ← algebraMap_quotient_one_sub_self (e := e), algebraMap_smul,
        TensorProduct.smul_tmul, hf, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  let : Unique (S ⊗[k] (Fin r → S')) := uniqueOfSubsingleton 0
  let φ : S ⊗[k] (P × (Fin r → S')) ≃ₗ[S] P :=
    TensorProduct.prodRight k S S P (Fin r → S') ≪≫ₗ LinearEquiv.prodUnique ≪≫ₗ
      (isBaseChange_self_of_surjective Ideal.Quotient.mk_surjective P).equiv
  exact Module.Free.of_equiv φ

end Idempotent

end Module
