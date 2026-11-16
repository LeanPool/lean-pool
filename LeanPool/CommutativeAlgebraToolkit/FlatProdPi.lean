/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flatness of finite products

A finite product of modules is flat if and only if each factor is flat; in particular the product
`M × N` of two flat modules is flat.

## Main statements

* `Module.Flat.pi_iff`: `Π i, M i` is flat iff every `M i` is, for a finite index.
* `Module.Flat.prod_iff`: `M × N` is flat iff `M` and `N` are.
* `Module.Flat.prod`: the product of two flat modules is flat.
-/

public section

universe u v w

open TensorProduct

namespace Module.Flat

variable {R : Type u} {M : Type v} {N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

theorem pi_iff {ι : Type v} {M : ι → Type w} [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)]
    [Finite ι] : Flat R (Π i, M i) ↔ ∀ i, Flat R (M i) := by
  classical
  have := Fintype.ofFinite ι
  rw [← directSum_iff]
  exact equiv_iff (DirectSum.linearEquivFunOnFintype R ι M).symm

theorem prod_iff : Flat R (M × N) ↔ Flat R M ∧ Flat R N := by
  have key {P : Type u} [AddCommMonoid P] [Module R P] (Q : Submodule R P) :
      Function.Injective (Q.subtype.rTensor (M × N)) ↔
        Function.Injective (Q.subtype.rTensor M) ∧ Function.Injective (Q.subtype.rTensor N) := by
    have : (prodRight R R P M N).toLinearMap ∘ₗ Q.subtype.rTensor (M × N) =
        (Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N) ∘ₗ
          (prodRight R R Q M N).toLinearMap := by
      ext <;> simp
    simpa [LinearMap.coe_prodMap, Prod.map_injective] using congr(Function.Injective ⇑$this)
  simp_rw [iff_rTensor_injectiveₛ, key, forall_and]

/-- The product of two flat `R`-modules is flat. -/
instance prod [Flat R M] [Flat R N] : Flat R (M × N) := prod_iff.mpr ⟨‹_›, ‹_›⟩

end Module.Flat
