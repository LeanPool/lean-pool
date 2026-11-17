/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Associated primes under a flat extension

Let `F` be a flat `A`-module and `p` a prime of `A`. Multiplication by `a ∉ p` is injective on
`F / pF = (A ⧸ p) ⊗ F`. Consequently, if `F` is moreover a `B`-module for an `A`-algebra `B` and
`N` is a `B`-submodule of `F` whose underlying `A`-submodule is `pF`, every associated prime of
the `B`-module `F / N` lies over `p`.

## Main statements

* `Module.Flat.mem_smul_top_of_smul_mem`: if `a ∉ p`, then `a • x ∈ pF` forces `x ∈ pF`.
* `Submodule.IsAssociatedPrime.comap_eq_of_flat`: associated primes of `F / N` lie over `p`.
-/

public section

open TensorProduct

variable {A : Type*} [CommRing A] {F : Type*} [AddCommGroup F] [Module A F]

/-- Multiplication by `a ∉ p` is injective on `F / pF` when `F` is flat. -/
theorem Module.Flat.mem_smul_top_of_smul_mem [Module.Flat A F] {p : Ideal A} [p.IsPrime]
    {a : A} (ha : a ∉ p) {x : F} (hx : a • x ∈ p • (⊤ : Submodule A F)) :
    x ∈ p • (⊤ : Submodule A F) := by
  set e := quotTensorEquivQuotSMul F p
  -- multiplication by `a` on `A/p` is injective, since `A/p` is a domain
  have hf : Function.Injective (LinearMap.lsmul A (A ⧸ p) a) := by
    intro u v huv
    have h : Ideal.Quotient.mk p a * u = Ideal.Quotient.mk p a * v := by
      simpa [Algebra.smul_def] using huv
    refine mul_left_cancel₀ ?_ h
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective (fun t : (A ⧸ p) ⊗[A] F ↦ a • t) := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := F) _ hf
    convert this using 1
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul u y => simp [TensorProduct.smul_tmul']
    | add u v hu hv => simp only [smul_add, map_add] at hu hv ⊢; rw [hu, hv]
  have hx0 : a • (Submodule.Quotient.mk x : F ⧸ p • (⊤ : Submodule A F)) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hx
  have key : e.symm (Submodule.Quotient.mk x) = 0 := by
    apply hinj
    simp only [smul_zero]
    rw [← map_smul, hx0, map_zero]
  rw [← Submodule.Quotient.mk_eq_zero, ← e.symm.map_eq_zero_iff]
  exact key

variable {B : Type*} [CommRing B] [Algebra A B] [Module B F] [IsScalarTower A B F]

/-- Let `F` be a `B`-module, flat over `A`, `p` a prime of `A`, and `N` a `B`-submodule of `F`
whose underlying `A`-submodule is `pF`. Every associated prime `P` of the `B`-module `F/N` lies
over `p`. -/
theorem Submodule.IsAssociatedPrime.comap_eq_of_flat [Module.Flat A F] {p : Ideal A}
    [hp : p.IsPrime] {N : Submodule B F} {P : Ideal B} (hP : N.IsAssociatedPrime P)
    (hN : N.restrictScalars A = p • (⊤ : Submodule A F)) : P.comap (algebraMap A B) = p := by
  obtain ⟨hPp, x, rfl⟩ := hP
  have memN : ∀ y : F, y ∈ N ↔ y ∈ p • (⊤ : Submodule A F) := fun y ↦ by
    rw [← hN]; rfl
  ext a
  rw [Ideal.mem_comap, Ideal.mem_radical_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [Submodule.mem_colon_singleton, ← map_pow, algebraMap_smul, memN] at hn
    by_contra ha
    have hx : x ∈ N :=
      (memN x).2 (Module.Flat.mem_smul_top_of_smul_mem (fun h ↦ ha (hp.mem_of_pow_mem n h)) hn)
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, Ideal.mem_radical_iff]
    exact ⟨1, by rw [Submodule.mem_colon_singleton, one_pow, one_smul]; exact hx⟩
  · intro ha
    refine ⟨1, ?_⟩
    rw [pow_one, Submodule.mem_colon_singleton, algebraMap_smul, memN]
    exact Submodule.smul_mem_smul ha trivial
