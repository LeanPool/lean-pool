/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Filtration

/-!
# Baer's criterion for `I`-primary torsion modules

Let `A` be a Noetherian ring, `I` an ideal and `Q` an `A`-module equal to its `I`-primary
component `Γ_I(Q)`. Then `Q` is injective as soon as linear maps into `Q` extend along the
inclusions of submodules of `A ⧸ I ^ n`, for all `n`: a map from an ideal `J` to `Q` is killed by
some `I ^ n`, and by the Artin–Rees lemma it factors through the image of `J` in
`A ⧸ I ^ (n + k)`. The prototypical example is the `I`-primary component of an injective module,
which is injective (Tau Ceti's `Ideal.injective_primaryComponent`).

## Main statements

* `Ideal.baer_of_primaryComponent_eq_top`: such a `Q` satisfies Baer's criterion.
* `Ideal.injective_of_primaryComponent_eq_top`: such a `Q` is injective.
-/

public section

variable {A : Type*} [CommRing A]

open Submodule Module Set Function

namespace Ideal

variable (I : Ideal A)

universe v

variable {Q : Type v} [AddCommGroup Q] [Module A Q] [IsNoetherianRing A]

private lemma exists_pow_smul_eq_zero_of_primaryComponent_eq_top
    (hQ : primaryComponent Q I = ⊤) (J : Ideal A) (g : J →ₗ[A] Q) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ x : J, a • g x = 0 := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := J)
  have h (x : Q) : ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
    obtain ⟨n, hn⟩ := (primaryComponent_mem Q I x).1 (hQ ▸ mem_top)
    exact ⟨n, fun a ha ↦ (mem_torsionBySet_iff _ _).1 hn ⟨a, ha⟩⟩
  choose e he using fun i ↦ h (g (s i))
  refine ⟨Finset.univ.sup e, fun a ha x ↦ ?_⟩
  have hx : x ∈ Submodule.span A (Set.range s) := hs ▸ mem_top
  induction hx using span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact he i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, smul_comm, hy, smul_zero]

theorem baer_of_primaryComponent_eq_top (hQ : primaryComponent Q I = ⊤)
    (h : ∀ (n : ℕ) (N : Submodule A (A ⧸ I ^ n)) (f : N →ₗ[A] Q),
      ∃ g : A ⧸ I ^ n →ₗ[A] Q, ∀ x : N, g x = f x) :
    Module.Baer A Q := by
  intro J g
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_primaryComponent_eq_top I hQ J g
  -- `g` vanishes on `I ^ n • J`.
  have hgIJ (x : A) (hx : x ∈ I ^ n • J) : g ⟨x, smul_le_right hx⟩ = 0 := by
    induction hx using smul_induction_on' with
    | smul a ha y hy => exact (map_smul g a ⟨y, hy⟩).trans (hn a ha _)
    | add x hx y hy hx' hy' =>
      exact (map_add g ⟨x, smul_le_right hx⟩ ⟨y, smul_le_right hy⟩).trans
        (by rw [hx', hy', add_zero])
  -- Artin–Rees: `J ⊓ I ^ (n + k) ≤ I ^ n • J`.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
  have hAR (x : A) (hxJ : x ∈ J) (hxm : x ∈ I ^ (n + k)) : x ∈ I ^ n • J := by
    have h1 : x ∈ I ^ (n + k) • (⊤ : Ideal A) ⊓ J := ⟨by simpa using hxm, hxJ⟩
    rw [hk (n + k) (by lia), Nat.add_sub_cancel] at h1
    exact smul_mono le_rfl inf_le_right h1
  -- `g` factors through the image of `J` in `A ⧸ I ^ (n + k)`.
  let φ : J →ₗ[A] A ⧸ I ^ (n + k) := (I ^ (n + k)).mkQ ∘ₗ J.subtype
  have hker : LinearMap.ker φ ≤ LinearMap.ker g := fun x hx ↦ by
    have hxm : (x : A) ∈ I ^ (n + k) := by
      simpa [φ, Ideal.Quotient.eq_zero_iff_mem] using hx
    simpa using hgIJ x (hAR x x.2 hxm)
  obtain ⟨w, hw⟩ := h (n + k) (LinearMap.range φ)
    ((LinearMap.ker φ).liftQ g hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap)
  refine ⟨w ∘ₗ (I ^ (n + k)).mkQ, fun x hx ↦ ?_⟩
  have := hw ⟨φ ⟨x, hx⟩, LinearMap.mem_range_self φ _⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  exact this

/-- Over a Noetherian ring, a module `Q` with `Q(I) = Q` is injective as soon as linear maps
into `Q` extend along the inclusions of submodules of `A ⧸ I ^ n`, for all `n`. -/
theorem injective_of_primaryComponent_eq_top (hQ : primaryComponent Q I = ⊤)
    (h : ∀ (n : ℕ) (N : Submodule A (A ⧸ I ^ n)) (f : N →ₗ[A] Q),
      ∃ g : A ⧸ I ^ n →ₗ[A] Q, ∀ x : N, g x = f x) :
    Module.Injective A Q :=
  (baer_of_primaryComponent_eq_top I hQ h).injective

end Ideal
