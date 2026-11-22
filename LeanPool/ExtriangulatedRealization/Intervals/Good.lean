/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Injective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# A pointwise description of the subcategory `B_E`

For a finite set `E ⊆ I`, call a representation `M` of `I_*` *`E`-good* if it is pointwise
finite-dimensional, its structure maps between points of `I` are surjective, a structure map
`M(s ≤ t)` with `s, t ∈ I` is injective when no `e ∈ E` satisfies `s ≤ e < t`, and `M` vanishes
beyond `E`. The intervals `Y`, `A e`, `P e` (`e ∈ E`) are good, and good representations are
closed under extensions (Lemma 2.1, Step 2) and retracts. In `Intervals/Decomposition.lean`
every good representation is shown to be a finite direct sum of such intervals.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- The structure map `M(s ≤ t)` as a linear map. -/
noncomputable abbrev smap (M : Rep k I) {s t : WithBot I} (h : s ≤ t) : M.obj s →ₗ[k] M.obj t :=
  (M.map (homOfLE h)).hom

lemma smap_comp (M : Rep k I) {s t r : WithBot I} (h₁ : s ≤ t) (h₂ : t ≤ r) (m : M.obj s) :
    smap M h₂ (smap M h₁ m) = smap M (h₁.trans h₂) m := by
  rw [smap, smap, smap, ← ModuleCat.comp_apply, ← Functor.map_comp]
  rfl

lemma smap_self (M : Rep k I) (s : WithBot I) (m : M.obj s) : smap M (le_refl s) m = m := by
  rw [smap, show homOfLE (le_refl s) = 𝟙 s from rfl, CategoryTheory.Functor.map_id]
  rfl

lemma smap_naturality {M N : Rep k I} (f : M ⟶ N) {s t : WithBot I} (h : s ≤ t) (m : M.obj s) :
    (f.app t).hom (smap M h m) = smap N h ((f.app s).hom m) := by
  rw [smap, smap, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, f.naturality]

/-- `E`-good representations. -/
structure IsGood (E : Finset I) (M : Rep k I) : Prop where
  finite : ∀ t, FiniteDimensional k (M.obj t)
  surj : ∀ {s t : I} (h : s ≤ t), Function.Surjective (smap M (WithBot.coe_le_coe.mpr h))
  inj : ∀ {s t : I} (h : s ≤ t), (∀ e ∈ E, ¬ (s ≤ e ∧ e < t)) →
    Function.Injective (smap M (WithBot.coe_le_coe.mpr h))
  zero : ∀ t : I, (∀ e ∈ E, e < t) → Subsingleton (M.obj t)

/-! ### Vector-space four lemmas -/

section FourLemma

variable {A₁ B₁ C₁ A₂ B₂ C₂ : Type*} [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]
  [AddCommGroup A₂] [AddCommGroup B₂] [AddCommGroup C₂] [Module k A₁] [Module k B₁] [Module k C₁]
  [Module k A₂] [Module k B₂] [Module k C₂]
  {f₁ : A₁ →ₗ[k] B₁} {g₁ : B₁ →ₗ[k] C₁} {f₂ : A₂ →ₗ[k] B₂} {g₂ : B₂ →ₗ[k] C₂}
  {a : A₁ →ₗ[k] A₂} {b : B₁ →ₗ[k] B₂} {c : C₁ →ₗ[k] C₂}

lemma four_surjective (hex₂ : Function.Exact f₂ g₂) (hg₁ : Function.Surjective g₁)
    (h₁ : ∀ x, b (f₁ x) = f₂ (a x)) (h₂ : ∀ y, c (g₁ y) = g₂ (b y))
    (ha : Function.Surjective a) (hc : Function.Surjective c) : Function.Surjective b := by
  intro y
  obtain ⟨z, hz⟩ := hc (g₂ y)
  obtain ⟨w, rfl⟩ := hg₁ z
  have : g₂ (y - b w) = 0 := by rw [map_sub, ← h₂, hz, sub_self]
  obtain ⟨x₂, hx₂⟩ := (hex₂ _).mp this
  obtain ⟨x₁, rfl⟩ := ha x₂
  exact ⟨w + f₁ x₁, by rw [map_add, h₁, hx₂, add_sub_cancel]⟩

lemma four_injective (hex₁ : Function.Exact f₁ g₁) (hf₂ : Function.Injective f₂)
    (h₁ : ∀ x, b (f₁ x) = f₂ (a x)) (h₂ : ∀ y, c (g₁ y) = g₂ (b y))
    (ha : Function.Injective a) (hc : Function.Injective c) : Function.Injective b := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have : g₁ y = 0 := hc (by rw [h₂, hy, map_zero, map_zero])
  obtain ⟨x, rfl⟩ := (hex₁ _).mp this
  have : a x = 0 := hf₂ (by rw [← h₁, hy, map_zero])
  rw [show x = 0 from ha (by rw [this, map_zero]), map_zero]

lemma three_subsingleton (hex : Function.Exact f₁ g₁) [Subsingleton A₁] [Subsingleton C₁] :
    Subsingleton B₁ := by
  refine ⟨fun y y' => ?_⟩
  have key : ∀ z : B₁, z = 0 := fun z => by
    obtain ⟨x, rfl⟩ := (hex z).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim x 0, map_zero]
  rw [key y, key y']

end FourLemma

/-! ### Closure properties -/

variable (E : Finset I)

/-- Pointwise data of a short exact sequence of representations. -/
lemma shortExact_app {S : ShortComplex (Rep k I)} (hS : S.ShortExact) (t : WithBot I) :
    Function.Injective (S.f.app t).hom ∧ Function.Surjective (S.g.app t).hom ∧
      Function.Exact (S.f.app t).hom (S.g.app t).hom := by
  have h := hS.map_of_exact ((evaluation (WithBot I) (ModuleCat.{u} k)).obj t)
  exact ⟨(ModuleCat.mono_iff_injective _).mp h.mono_f, (ModuleCat.epi_iff_surjective _).mp h.epi_g,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact⟩

lemma IsGood.of_shortExact {S : ShortComplex (Rep k I)} (hS : S.ShortExact) (h₁ : IsGood E S.X₁)
    (h₃ : IsGood E S.X₃) : IsGood E S.X₂ where
  finite t := by
    obtain ⟨hf, hg, hex⟩ := shortExact_app hS t
    have := h₁.finite t
    have := h₃.finite t
    exact Module.Finite.of_exact hex hg
  surj {s t} h := by
    obtain ⟨_, hg, _⟩ := shortExact_app hS (s : WithBot I)
    obtain ⟨_, _, hex⟩ := shortExact_app hS (t : WithBot I)
    exact four_surjective hex hg (fun x => (smap_naturality S.f _ x).symm)
      (fun y => (smap_naturality S.g _ y).symm) (h₁.surj h) (h₃.surj h)
  inj {s t} h hE := by
    obtain ⟨_, _, hex⟩ := shortExact_app hS (s : WithBot I)
    obtain ⟨hf, _, _⟩ := shortExact_app hS (t : WithBot I)
    exact four_injective hex hf (fun x => (smap_naturality S.f _ x).symm)
      (fun y => (smap_naturality S.g _ y).symm) (h₁.inj h hE) (h₃.inj h hE)
  zero t ht := by
    obtain ⟨_, _, hex⟩ := shortExact_app hS (t : WithBot I)
    have := h₁.zero t ht
    have := h₃.zero t ht
    exact three_subsingleton hex

/-- The third term of a short exact sequence of good representations is good. -/
lemma IsGood.of_shortExact_right {S : ShortComplex (Rep k I)} (hS : S.ShortExact)
    (h₁ : IsGood E S.X₁) (h₂ : IsGood E S.X₂) : IsGood E S.X₃ where
  finite t := by
    obtain ⟨_, hg, _⟩ := shortExact_app hS t
    have := h₂.finite t
    exact Module.Finite.of_surjective _ hg
  surj {s t} h := by
    obtain ⟨_, hgt, _⟩ := shortExact_app hS (t : WithBot I)
    intro z
    obtain ⟨y, rfl⟩ := hgt z
    obtain ⟨x, rfl⟩ := h₂.surj h y
    exact ⟨(S.g.app s).hom x, (smap_naturality S.g _ x).symm⟩
  inj {s t} h hE := by
    obtain ⟨_, hgs, _⟩ := shortExact_app hS (s : WithBot I)
    obtain ⟨_, _, hext⟩ := shortExact_app hS (t : WithBot I)
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := hgs z
    have hy : (S.g.app t).hom (smap S.X₂ (WithBot.coe_le_coe.mpr h) y) = 0 := by
      rw [smap_naturality]
      exact hz
    obtain ⟨a', ha'⟩ := (hext _).mp hy
    obtain ⟨a, rfl⟩ := h₁.surj h a'
    have hya : y = (S.f.app s).hom a := h₂.inj h hE (by rw [← smap_naturality, ha'])
    rw [hya, ← ModuleCat.comp_apply, ← NatTrans.comp_app, S.zero]
    rfl
  zero t ht := by
    obtain ⟨_, hg, _⟩ := shortExact_app hS t
    have := h₂.zero t ht
    exact hg.subsingleton

lemma IsGood.of_retract {K M : Rep k I} (i : K ⟶ M) (p : M ⟶ K) (hip : i ≫ p = 𝟙 K)
    (hM : IsGood E M) : IsGood E K := by
  have hpt : ∀ t (x : K.obj t), (p.app t).hom ((i.app t).hom x) = x := fun t x => by
    rw [← ModuleCat.comp_apply, ← NatTrans.comp_app, hip]
    rfl
  refine ⟨fun t => ?_, fun {s t} h => ?_, fun {s t} h hE => ?_, fun t ht => ?_⟩
  · have := hM.finite t
    exact Module.Finite.of_injective (i.app t).hom (Function.LeftInverse.injective (hpt t))
  · intro y
    obtain ⟨x, hx⟩ := hM.surj h ((i.app t).hom y)
    refine ⟨(p.app s).hom x, ?_⟩
    rw [← smap_naturality, hx, hpt]
  · intro x x' hxx'
    rw [← hpt s x, ← hpt s x']
    congr 1
    apply hM.inj h hE
    rw [← smap_naturality, ← smap_naturality, hxx']
  · have := hM.zero t ht
    exact (Function.LeftInverse.injective (hpt t)).subsingleton

end ExtriangulatedRealization
