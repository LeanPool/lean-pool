/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.FinitePresentation

import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Gluing projective modules over two comaximal localisations

Let `f, g ∈ R` be comaximal, and let `R_f`, `R_g`, `R_fg` be localisations of `R` away from
`f`, `g` and `fg`. Given a finitely generated projective `R_f`-module `M₁`, a finitely
generated projective `R_g`-module `M₂` and an `R_fg`-linear isomorphism
`α : R_fg ⊗[R_f] M₁ ≅ R_fg ⊗[R_g] M₂`, the `R`-module
`M = {(x₁, x₂) ∈ M₁ × M₂ | α (1 ⊗ x₁) = 1 ⊗ x₂}` is finitely generated projective, and its
localisations away from `f` and `g` are `M₁` and `M₂` (Lombardi–Quitté, concrete local-global
principle XV.4.4 bis and XV.2.2, item 4).

The two projections `M → M₁` and `M → M₂` are localisations away from `f` and `g`
(`glue_fst_isLocalizedModule`); this needs no comaximality. Comaximality enters through the
local nature of flatness and of finite presentation.

## Main results

* `glue`: the glued module, as a submodule of `M₁ × M₂`.
* `glue_fst_isLocalizedModule`: the first projection is a localisation away from `f`.
* `exists_finite_projective_glue`: the gluing theorem.

## References

* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
-/

@[expose] public section

universe u v w

open TensorProduct

namespace LeanPool.QuillenSuslin

section Away

variable {R : Type*} [CommRing R] {S T : Type*} [CommRing S] [CommRing T] [Algebra R S]
  [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- If `S` is the localisation of `R` away from `y` and `T` that away from `x * y`, then `T` is
the localisation of `S` away from the image of `x`. -/
theorem isLocalization_away_algebraMap_of_mul (x y : R) [IsLocalization.Away y S]
    [IsLocalization.Away (x * y) T] : IsLocalization.Away (algebraMap R S x) T := by
  have hy : IsUnit (algebraMap R T y) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_left y x)
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun a b h => ?_)
  · rw [← IsScalarTower.algebraMap_apply]
    exact IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_right x y)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (x * y) z
    refine ⟨n, algebraMap R S a * IsLocalization.Away.invSelf y ^ n, ?_⟩
    apply (hy.pow n).mul_left_injective
    have hinv : algebraMap S T (IsLocalization.Away.invSelf y) * algebraMap R T y = 1 := by
      rw [IsScalarTower.algebraMap_apply R S T y, ← map_mul, mul_comm,
        IsLocalization.Away.mul_invSelf, map_one]
    simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    calc z * algebraMap R T x ^ n * algebraMap R T y ^ n = z * algebraMap R T (x * y) ^ n := by
          rw [map_mul, mul_pow]; ring
      _ = algebraMap R T a := ha
      _ = algebraMap R T a * (algebraMap S T (IsLocalization.Away.invSelf y) *
            algebraMap R T y) ^ n := by rw [hinv, one_pow, mul_one]
      _ = _ := by ring
  · obtain ⟨n, a', ha'⟩ := IsLocalization.Away.surj y a
    obtain ⟨m, b', hb'⟩ := IsLocalization.Away.surj y b
    have h' : algebraMap R T (a' * y ^ m) = algebraMap R T (b' * y ^ n) := by
      rw [map_mul, map_mul, IsScalarTower.algebraMap_apply R S T a',
        IsScalarTower.algebraMap_apply R S T b', ← ha', ← hb']
      simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, h]
      ring
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (x * y) h'
    refine ⟨k, ?_⟩
    have hu : IsUnit (algebraMap R S y ^ (k + n + m)) :=
      (IsLocalization.Away.algebraMap_isUnit y).pow _
    apply hu.mul_right_injective
    have := congrArg (algebraMap R S) hk
    simp only [map_mul, map_pow, ← ha', ← hb'] at this
    calc algebraMap R S y ^ (k + n + m) * (algebraMap R S x ^ k * a) =
          (algebraMap R S x * algebraMap R S y) ^ k * (a * algebraMap R S y ^ n *
            algebraMap R S y ^ m) := by ring
      _ = (algebraMap R S x * algebraMap R S y) ^ k * (b * algebraMap R S y ^ m *
            algebraMap R S y ^ n) := this
      _ = _ := by ring

end Away

section Glue

variable {R : Type u} [CommRing R]
variable {S₁ S₂ T : Type w} [CommRing S₁] [CommRing S₂] [CommRing T] [Algebra R S₁]
  [Algebra R S₂] [Algebra R T] [Algebra S₁ T] [Algebra S₂ T] [IsScalarTower R S₁ T]
  [IsScalarTower R S₂ T]
variable {N₁ N₂ : Type v} [AddCommGroup N₁] [Module S₁ N₁] [Module R N₁] [IsScalarTower R S₁ N₁]
  [AddCommGroup N₂] [Module S₂ N₂] [Module R N₂] [IsScalarTower R S₂ N₂]

/-- The `R`-linear map `(x₁, x₂) ↦ α (1 ⊗ x₁) - 1 ⊗ x₂`, whose kernel is the glued module. -/
def glueMap (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) : N₁ × N₂ →ₗ[R] T ⊗[S₂] N₂ :=
  ((α.toLinearMap.restrictScalars R ∘ₗ (TensorProduct.mk S₁ T N₁ 1).restrictScalars R) ∘ₗ
    LinearMap.fst R N₁ N₂) - (TensorProduct.mk S₂ T N₂ 1).restrictScalars R ∘ₗ
      LinearMap.snd R N₁ N₂

/-- The module glued from `N₁` and `N₂` along `α`: the pairs `(x₁, x₂)` with
`α (1 ⊗ x₁) = 1 ⊗ x₂`. -/
def glue (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) : Submodule R (N₁ × N₂) :=
  LinearMap.ker (glueMap (R := R) α)

theorem mem_glue (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) (x : N₁ × N₂) :
    x ∈ glue (R := R) α ↔ α ((1 : T) ⊗ₜ x.1) = (1 : T) ⊗ₜ x.2 := by
  simp [glue, glueMap, sub_eq_zero]

/-- The first projection of the glued module, as an `R`-linear map. -/
def glueFst (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) : glue (R := R) α →ₗ[R] N₁ :=
  LinearMap.fst R N₁ N₂ ∘ₗ (glue α).subtype

/-- If `f` is a unit of `S₁` and `T` is the localisation of `S₂` away from `f`, the first
projection of the glued module is a localisation away from `f`. -/
theorem glue_fst_isLocalizedModule (f : R) (hf : IsUnit (algebraMap R S₁ f))
    [IsLocalization.Away (algebraMap R S₂ f) T] (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) :
    IsLocalizedModule (Submonoid.powers f) (glueFst (R := R) α) := by
  have hψ : IsLocalizedModule (Submonoid.powers f)
      ((TensorProduct.mk S₂ T N₂ 1).restrictScalars R) :=
    IsLocalizedModule.restrictScalars_powers f _
  refine ⟨fun s => ?_, fun y => ?_, fun {x x'} h => ?_⟩
  · obtain ⟨_, n, rfl⟩ := s
    have hu : IsUnit (algebraMap R S₁ (f ^ n)) := by rw [map_pow]; exact hf.pow n
    rw [Module.End.isUnit_iff]
    have key : ∀ m : N₁, (algebraMap R (Module.End R N₁) (f ^ n)) m =
        algebraMap R S₁ (f ^ n) • m := fun m => by
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    constructor
    · intro a b hab
      simp only [key] at hab
      simpa [smul_smul] using congrArg (fun m => hu.unit⁻¹.val • m) hab
    · intro b
      refine ⟨hu.unit⁻¹.val • b, ?_⟩
      rw [key, smul_smul, IsUnit.mul_val_inv, one_smul]
  · obtain ⟨⟨x₂, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      ((TensorProduct.mk S₂ T N₂ 1).restrictScalars R) (α ((1 : T) ⊗ₜ y))
    have hmem : ((s : R) • y, x₂) ∈ glue (R := R) α := by
      rw [mem_glue]
      simp only [LinearMap.coe_restrictScalars, mk_apply] at hs
      have h1 : (1 : T) ⊗ₜ[S₁] ((s : R) • y) = algebraMap R T s • ((1 : T) ⊗ₜ[S₁] y) := by
        rw [← algebraMap_smul S₁ (s : R) y, tmul_smul, algebraMap_smul, algebraMap_smul]
      rw [h1, map_smul, ← hs, algebraMap_smul]
      rfl
    exact ⟨⟨⟨_, hmem⟩, s⟩, rfl⟩
  · have hx := (mem_glue α x).mp x.2
    have hx' := (mem_glue α x').mp x'.2
    have h1 : x.1.1 = x'.1.1 := h
    rw [h1, hx'] at hx
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := (TensorProduct.mk S₂ T N₂ 1).restrictScalars R) (x₁ := x.1.2) (x₂ := x'.1.2)
      (by simpa using hx.symm)
    refine ⟨c, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp [h1]
    · simpa using hc

/-- The second projection of the glued module, as an `R`-linear map. -/
def glueSnd (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) : glue (R := R) α →ₗ[R] N₂ :=
  LinearMap.snd R N₁ N₂ ∘ₗ (glue α).subtype

/-- Gluing along `α` and along `α⁻¹` give isomorphic modules, by swapping the factors. -/
def glueSwap (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) :
    glue (R := R) α ≃ₗ[R] glue (R := R) α.symm where
  toFun x := ⟨(x.1.2, x.1.1), by
    rw [mem_glue, LinearEquiv.symm_apply_eq]
    exact ((mem_glue α x.1).mp x.2).symm⟩
  invFun x := ⟨(x.1.2, x.1.1), by
    rw [mem_glue]
    exact ((LinearEquiv.symm_apply_eq α).mp ((mem_glue α.symm x.1).mp x.2)).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem glueSnd_eq (α : T ⊗[S₁] N₁ ≃ₗ[T] T ⊗[S₂] N₂) :
    glueSnd (R := R) α = glueFst α.symm ∘ₗ (glueSwap α).toLinearMap :=
  rfl

end Glue

section Transfer

variable {R : Type u} [CommRing R] (r : R) (S : Type w) [CommRing S] [Algebra R S]
  [IsLocalization.Away r S]
variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- If `φ : M → N` is a localisation away from `r` onto a finitely generated projective module
over a localisation `S` of `R` away from `r`, then the canonical localisation of `M` away from `r`
is finitely presented over `R_r`. -/
theorem finitePresentation_localizedModule (φ : M →ₗ[R] N)
    [IsLocalizedModule (Submonoid.powers r) φ] [Module.Finite S N] [Module.Projective S N] :
    Module.FinitePresentation (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M) := by
  let L := Localization.Away r
  let σ := IsLocalization.algEquiv (Submonoid.powers r) S L
  let _ : Algebra S L := σ.toRingHom.toAlgebra
  have : IsScalarTower R S L :=
    IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  let e1 := (IsLocalizedModule.isBaseChange (Submonoid.powers r) L
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv
  let e2 := (IsLocalizedModule.isBaseChange (Submonoid.powers r) S φ).equiv
  let e3 := AlgebraTensorModule.cancelBaseChange R S L L M
  let e4 := e2.baseChange S L _ _
  let e : LocalizedModule (Submonoid.powers r) M ≃ₗ[L] L ⊗[S] N := e1.symm ≪≫ₗ e3.symm ≪≫ₗ e4
  have : Module.Finite L (LocalizedModule (Submonoid.powers r) M) := Module.Finite.equiv e.symm
  have : Module.Projective L (LocalizedModule (Submonoid.powers r) M) :=
    Module.Projective.of_equiv' e.symm
  exact Module.finitePresentation_of_projective _ _

end Transfer

section Main

variable {R : Type u} [CommRing R] {f g : R}
variable {Rf Rg Rfg : Type w} [CommRing Rf] [CommRing Rg] [CommRing Rfg] [Algebra R Rf]
  [Algebra R Rg] [Algebra R Rfg] [IsLocalization.Away f Rf] [IsLocalization.Away g Rg]
  [IsLocalization.Away (f * g) Rfg] [Algebra Rf Rfg] [Algebra Rg Rfg] [IsScalarTower R Rf Rfg]
  [IsScalarTower R Rg Rfg]

/-- The gluing theorem, for modules already equipped with their `R`-module structures. -/
theorem exists_finite_projective_glue_aux (hfg : IsCoprime f g) (M₁ M₂ : Type v)
    [AddCommGroup M₁] [Module Rf M₁] [Module R M₁] [IsScalarTower R Rf M₁]
    [Module.Finite Rf M₁] [Module.Projective Rf M₁]
    [AddCommGroup M₂] [Module Rg M₂] [Module R M₂] [IsScalarTower R Rg M₂]
    [Module.Finite Rg M₂] [Module.Projective Rg M₂] (α : Rfg ⊗[Rf] M₁ ≃ₗ[Rfg] Rfg ⊗[Rg] M₂) :
    Module.Finite R (glue (R := R) α) ∧ Module.Projective R (glue (R := R) α) ∧
      Nonempty (Rf ⊗[R] glue (R := R) α ≃ₗ[Rf] M₁) ∧
        Nonempty (Rg ⊗[R] glue (R := R) α ≃ₗ[Rg] M₂) := by
  have : IsLocalization.Away (algebraMap R Rg f) Rfg :=
    isLocalization_away_algebraMap_of_mul f g
  have : IsLocalization.Away (g * f) Rfg := by rw [mul_comm]; infer_instance
  have : IsLocalization.Away (algebraMap R Rf g) Rfg :=
    isLocalization_away_algebraMap_of_mul g f
  have h₁ : IsLocalizedModule (Submonoid.powers f) (glueFst (R := R) α) :=
    glue_fst_isLocalizedModule f (IsLocalization.Away.algebraMap_isUnit f) α
  have : IsLocalizedModule (Submonoid.powers g) (glueFst (R := R) α.symm) :=
    glue_fst_isLocalizedModule g (IsLocalization.Away.algebraMap_isUnit g) α.symm
  have h₂ : IsLocalizedModule (Submonoid.powers g) (glueSnd (R := R) α) := by
    rw [glueSnd_eq]
    exact IsLocalizedModule.of_linearEquiv_right _ _ _
  have hspan : Ideal.span ({f, g} : Set R) = ⊤ := by
    obtain ⟨a, b, hab⟩ := hfg
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  have hflat : Module.Flat R (glue (R := R) α) := by
    refine Module.flat_of_isLocalized_span R (glue (R := R) α) ({f, g} : Set R) hspan
      (fun r => LocalizedModule (Submonoid.powers r.1) (glue (R := R) α))
      (fun r => LocalizedModule.mkLinearMap _ _) fun ⟨r, hr⟩ => ?_
    rcases hr with rfl | rfl
    · have : Module.Flat R Rf := IsLocalization.flat Rf (Submonoid.powers r)
      have : Module.Flat R M₁ := Module.Flat.trans R Rf M₁
      exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso _ (glueFst (R := R) α))
    · have : Module.Flat R Rg := IsLocalization.flat Rg (Submonoid.powers r)
      have : Module.Flat R M₂ := Module.Flat.trans R Rg M₂
      exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso _ (glueSnd (R := R) α))
  have hfp : Module.FinitePresentation R (glue (R := R) α) := by
    refine Module.FinitePresentation.of_localizationSpan' ({f, g} : Set R) hspan
      (Rₚ := fun r => Localization.Away r.1)
      (Mₚ := fun r => LocalizedModule (Submonoid.powers r.1) (glue (R := R) α))
      (fun r => LocalizedModule.mkLinearMap _ _) fun ⟨r, hr⟩ => ?_
    rcases hr with rfl | rfl
    · exact finitePresentation_localizedModule r Rf (glueFst (R := R) α)
    · exact finitePresentation_localizedModule r Rg (glueSnd (R := R) α)
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation,
    ⟨(IsLocalizedModule.isBaseChange (Submonoid.powers f) Rf (glueFst (R := R) α)).equiv⟩,
    ⟨(IsLocalizedModule.isBaseChange (Submonoid.powers g) Rg (glueSnd (R := R) α)).equiv⟩⟩

/-- **3.6.** Zariski gluing: for comaximal `f, g ∈ R`, a finitely generated projective
`R_f`-module and a finitely generated projective `R_g`-module that are isomorphic over `R_fg`
glue to a finitely generated projective `R`-module in their universe (Lombardi–Quitté,
XV.4.4 bis, p. 866, and XV.2.2, item 4, p. 852). -/
theorem exists_finite_projective_glue (hfg : IsCoprime f g) (M₁ M₂ : Type v) [AddCommGroup M₁]
    [Module Rf M₁] [Module.Finite Rf M₁] [Module.Projective Rf M₁] [AddCommGroup M₂]
    [Module Rg M₂] [Module.Finite Rg M₂] [Module.Projective Rg M₂]
    (α : Rfg ⊗[Rf] M₁ ≃ₗ[Rfg] Rfg ⊗[Rg] M₂) :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module R M), Module.Finite R M ∧
      Module.Projective R M ∧ Nonempty (Rf ⊗[R] M ≃ₗ[Rf] M₁) ∧
        Nonempty (Rg ⊗[R] M ≃ₗ[Rg] M₂) := by
  let _ : Module R M₁ := Module.compHom M₁ (algebraMap R Rf)
  let _ : Module R M₂ := Module.compHom M₂ (algebraMap R Rg)
  have : IsScalarTower R Rf M₁ := ⟨fun a b m => by
    change (a • b) • m = algebraMap R Rf a • b • m
    rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower R Rg M₂ := ⟨fun a b m => by
    change (a • b) • m = algebraMap R Rg a • b • m
    rw [Algebra.smul_def, mul_smul]⟩
  exact ⟨glue (R := R) α, inferInstance, inferInstance,
    exists_finite_projective_glue_aux hfg M₁ M₂ α⟩

end Main

end LeanPool.QuillenSuslin

