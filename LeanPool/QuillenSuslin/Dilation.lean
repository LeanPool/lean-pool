/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.WittVector.IsPoly

/-!
# Quillen's dilation lemma

Let `R` be an `A`-algebra, not necessarily commutative, `f ∈ A`, `R_f = A_f ⊗[A] R`, and `θ` a
unit of `R_f[X]` with `θ(0) = 1`. Then there is `k` such that, whenever `g₁ − g₂ ∈ fᵏ A`, the unit
`θ(g₁X) θ(g₂X)⁻¹` comes from a unit `ψ` of `R[X]` with `ψ(0) = 1` (Quillen 1976, Lemma 1).

The proof isolates an abstract form of the localisation `R → R_f`: an `A`-algebra map
`ι : S → S'` such that `f` is a unit of `S'`, every element of `S'` times a power of `f` comes
from `S`, and the kernel of `ι` is `f`-power torsion (`IsAwayMap`). This is stable under passing
to polynomial rings. For such a map, every unit `u` of `S'[Z]` with `u(0) = 1` becomes, after
the dilation `Z ↦ fˢ Z`, the image of a unit of `S[Z]` with constant term `1`
(`exists_unit_lift_dilate`). Applied with `S = R[Y]` to `u = θ(Y + Z) θ(Y)⁻¹` and specialised at
`Y = g₂ X`, `Z = c X`, this gives the dilation lemma.

## Main results

* `dilate`: the substitution `X ↦ c X`, a ring endomorphism of `S[X]` for central `c`.
* `IsAwayMap`, `IsAwayMap.polynomial`: the abstract localisation and its polynomial extension.
* `IsAwayMap.of_isLocalizedModule`: algebra maps that are localisations of modules.
* `exists_unit_lift_dilate`: units with constant term `1` lift after a dilation.
* `exists_unit_lift_dilation`: Quillen's dilation lemma.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u w

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A]

section Dilate

variable {S : Type*} [Ring S] [Algebra A S]

theorem commute_smul_X (c : A) (p : S[X]) : Commute p (c • X : S[X]) := by
  rw [Algebra.smul_def]
  exact (show Commute p (algebraMap A S[X] c) from (Algebra.commutes c p).symm).mul_right
    (commute_X _).symm

theorem commute_C_smul_X (c : A) (a : S) : Commute (C a) (c • X : S[X]) :=
  commute_smul_X c _

/-- The dilation `X ↦ c X` of `S[X]`, a ring endomorphism since `c ∈ A` is central. -/
def dilate (c : A) : S[X] →+* S[X] :=
  eval₂RingHom' C (c • X) (commute_C_smul_X c)

theorem dilate_apply (c : A) (p : S[X]) : dilate c p = p.eval₂ C (c • X) := rfl

@[simp]
theorem dilate_C (c : A) (a : S) : dilate c (C a) = C a := eval₂_C _ _

@[simp]
theorem dilate_X (c : A) : dilate c (X : S[X]) = c • X := eval₂_X _ _

theorem coeff_dilate (c : A) (p : S[X]) (n : ℕ) :
    (dilate c p).coeff n = algebraMap A S c ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]
  | monomial m a =>
    have hX : (c • X : S[X]) ^ m = C (algebraMap A S c ^ m) * X ^ m := by
      rw [Algebra.smul_def c (X : S[X]), Polynomial.algebraMap_apply,
        (commute_X (C (algebraMap A S c))).symm.mul_pow, C_pow]
    rw [dilate_apply, eval₂_monomial, hX, ← mul_assoc, ← C_mul, ← C_mul_X_pow_eq_monomial,
      coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h
      rw [← map_pow]
      exact (Algebra.commutes (c ^ n) a).symm
    · rw [mul_zero]

@[simp]
theorem coeff_zero_dilate (c : A) (p : S[X]) : (dilate c p).coeff 0 = p.coeff 0 := by
  rw [coeff_dilate, pow_zero, one_mul]

theorem dilate_dilate (a b : A) (p : S[X]) : dilate a (dilate b p) = dilate (a * b) p := by
  ext n
  rw [coeff_dilate, coeff_dilate, coeff_dilate, ← mul_assoc, map_mul,
    ((Commute.all a b).map (algebraMap A S)).mul_pow]

theorem dilate_one (p : S[X]) : dilate (1 : A) p = p := by
  ext n
  rw [coeff_dilate, map_one, one_pow, one_mul]

theorem map_dilate {S' : Type*} [Ring S'] [Algebra A S'] (ι : S →ₐ[A] S') (c : A) (p : S[X]) :
    (dilate c p).map (ι : S →+* S') = dilate c (p.map (ι : S →+* S')) := by
  ext n
  rw [coeff_map, coeff_dilate, coeff_dilate, coeff_map, map_mul, map_pow]
  simp

theorem dilate_X_mul (c : A) (p : S[X]) :
    dilate c (X * p) = C (algebraMap A S c) * (X * dilate c p) := by
  rw [map_mul, dilate_X, Algebra.smul_def, Polynomial.algebraMap_apply, mul_assoc]

end Dilate

section IsAwayMap

variable (f : A) {S S' : Type*} [Ring S] [Ring S'] [Algebra A S] [Algebra A S']

/-- An `A`-algebra map `ι : S → S'` behaves like the localisation of `S` away from `f ∈ A`:
`f` is a unit of `S'`, every element of `S'` times a power of `f` lies in the image of `ι`, and
the kernel of `ι` consists of `f`-power torsion. -/
structure IsAwayMap (ι : S →ₐ[A] S') : Prop where
  isUnit : IsUnit (algebraMap A S' f)
  surj : ∀ x : S', ∃ (e : ℕ) (r : S), algebraMap A S' f ^ e * x = ι r
  ker : ∀ r : S, ι r = 0 → ∃ e : ℕ, algebraMap A S f ^ e * r = 0

variable {f}

/-- The polynomial extension of an `IsAwayMap` is one. -/
theorem IsAwayMap.polynomial {ι : S →ₐ[A] S'} (h : IsAwayMap f ι) :
    IsAwayMap f (mapAlgHom ι) := by
  classical
  refine ⟨?_, fun p => ?_, fun p hp => ?_⟩
  · rw [Polynomial.algebraMap_apply]
    exact h.isUnit.map C
  · induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨e₁, r₁, h₁⟩ := hp
      obtain ⟨e₂, r₂, h₂⟩ := hq
      refine ⟨e₁ + e₂, C (algebraMap A S f ^ e₂) * r₁ + C (algebraMap A S f ^ e₁) * r₂, ?_⟩
      simp only [Polynomial.algebraMap_apply, coe_mapAlgHom] at h₁ h₂ ⊢
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, ← h₁, ← h₂]
      simp only [RingHom.coe_coe, map_pow, AlgHom.commutes]
      rw [pow_add, mul_add, ← mul_assoc, ← mul_assoc, pow_mul_comm]
    | monomial n x =>
      obtain ⟨e, r, hr⟩ := h.surj x
      refine ⟨e, monomial n r, ?_⟩
      simp only [Polynomial.algebraMap_apply, coe_mapAlgHom, ← C_mul_X_pow_eq_monomial]
      rw [← C_pow, ← mul_assoc, ← C_mul, hr, Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X]
      rfl
  · have hc : ∀ n, ι (p.coeff n) = 0 := fun n => by
      have := congrArg (fun q => q.coeff n) hp
      simpa using this
    choose e he using fun n => h.ker _ (hc n)
    refine ⟨p.support.sum e, ?_⟩
    ext n
    rw [Polynomial.algebraMap_apply, ← C_pow, coeff_C_mul, coeff_zero]
    by_cases hn : n ∈ p.support
    · rw [← Finset.add_sum_erase _ _ hn, pow_add, ← pow_mul_comm, mul_assoc, he, mul_zero]
    · rw [notMem_support_iff.mp hn, mul_zero]

omit [Algebra A S] in
theorem eq_one_add_X_mul_divX {p : S[X]} (hp : p.coeff 0 = 1) : p = 1 + X * p.divX := by
  conv_lhs => rw [← X_mul_divX_add p, hp, C_1]
  rw [add_comm]

/-- A polynomial without constant term that is killed by `fᵗ` is killed by the dilation
`X ↦ fᵗ X`. -/
theorem dilate_eq_zero_of_mul_eq_zero {t : ℕ} {w : S[X]} (hw0 : w.coeff 0 = 0)
    (hw : algebraMap A S[X] f ^ t * w = 0) : dilate (f ^ t) w = 0 := by
  have hw' : w = X * w.divX := by
    conv_lhs => rw [← X_mul_divX_add w, hw0, C_0, add_zero]
  have hcomm : Commute (C (algebraMap A S (f ^ t))) (X : S[X]) := (commute_X _).symm
  have hd : C (algebraMap A S (f ^ t)) * w.divX = 0 := by
    apply isRegular_X.left
    rw [Polynomial.algebraMap_apply, ← C_pow, ← map_pow, hw', ← mul_assoc, hcomm.eq,
      mul_assoc] at hw
    simpa using hw
  rw [hw', dilate_X_mul, ← mul_assoc, hcomm.eq, mul_assoc,
    ← dilate_C (f ^ t) (algebraMap A S (f ^ t)), ← map_mul, hd, map_zero, mul_zero]

/-- **Units with constant term `1` lift after a dilation.** For an `IsAwayMap` `ι : S → S'`
and a unit `u` of `S'[X]` with `u(0) = 1`, there are `s` and a unit `v` of `S[X]` with
`v(0) = 1` whose image is the dilation `u(fˢ X)`. -/
theorem exists_unit_lift_dilate {ι : S →ₐ[A] S'} (h : IsAwayMap f ι) (u : S'[X]ˣ)
    (hu : (u : S'[X]).coeff 0 = 1) :
    ∃ (s : ℕ) (v : S[X]ˣ), (v : S[X]).coeff 0 = 1 ∧
      (v : S[X]).map (ι : S →+* S') = dilate (f ^ s) (u : S'[X]) := by
  have hP := h.polynomial
  have hu' : ((u⁻¹ : S'[X]ˣ) : S'[X]).coeff 0 = 1 := by
    have := congrArg (fun q => q.coeff 0) u.mul_inv
    simpa only [mul_coeff_zero, hu, one_mul, AddMonoidAlgebra.coeff_one_zero] using this
  obtain ⟨e₁, Q₁, hQ₁⟩ := hP.surj (u : S'[X]).divX
  obtain ⟨e₂, Q₂, hQ₂⟩ := hP.surj ((u⁻¹ : S'[X]ˣ) : S'[X]).divX
  set e := e₁ + e₂
  -- the lifts of the dilated units
  have lift : ∀ (w : S'[X]) (k₁ k₂ : ℕ) (Q : S[X]), w.coeff 0 = 1 →
      algebraMap A S'[X] f ^ k₁ * w.divX = mapAlgHom ι Q →
      (1 + X * dilate (f ^ (k₁ + k₂)) (C (algebraMap A S (f ^ k₂)) * Q)).map (ι : S →+* S') =
        dilate (f ^ (k₁ + k₂)) w := by
    intro w k₁ k₂ Q hw hQ
    have hQ' : Q.map (ι : S →+* S') = C (algebraMap A S' (f ^ k₁)) * w.divX := by
      rw [← coe_mapAlgHom, ← hQ, Polynomial.algebraMap_apply, ← C_pow, ← map_pow]
    have e1 : (C (algebraMap A S (f ^ k₂)) * Q).map (ι : S →+* S') =
        C (algebraMap A S' (f ^ (k₁ + k₂))) * w.divX := by
      rw [Polynomial.map_mul, map_C, hQ', ← mul_assoc, ← C_mul, RingHom.coe_coe,
        AlgHom.commutes, ← map_mul, ← pow_add, add_comm k₂ k₁]
    conv_rhs => rw [eq_one_add_X_mul_divX hw]
    rw [Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul, map_X, map_dilate, e1,
      map_add, map_one, dilate_X_mul, map_mul, dilate_C, ← mul_assoc, ← mul_assoc,
      (commute_X _).eq]
  have hφ := lift _ e₁ e₂ Q₁ hu hQ₁
  have hφ' := lift _ e₂ e₁ Q₂ hu' hQ₂
  rw [add_comm e₂ e₁] at hφ'
  set φ := 1 + X * dilate (f ^ e) (C (algebraMap A S (f ^ e₂)) * Q₁)
  set φ' := 1 + X * dilate (f ^ e) (C (algebraMap A S (f ^ e₁)) * Q₂)
  have hφ0 : φ.coeff 0 = 1 := by simp [φ]
  have hφ0' : φ'.coeff 0 = 1 := by simp [φ']
  have hk₁ : mapAlgHom ι (φ * φ' - 1) = 0 := by
    rw [map_sub, map_mul, map_one, coe_mapAlgHom, hφ, hφ', ← map_mul, Units.mul_inv, map_one,
      sub_self]
  have hk₂ : mapAlgHom ι (φ' * φ - 1) = 0 := by
    rw [map_sub, map_mul, map_one, coe_mapAlgHom, hφ, hφ', ← map_mul, Units.inv_mul, map_one,
      sub_self]
  obtain ⟨t₁, ht₁⟩ := hP.ker _ hk₁
  obtain ⟨t₂, ht₂⟩ := hP.ker _ hk₂
  set t := t₁ + t₂
  have key : ∀ (a b : S[X]) (k₁ k₂ : ℕ), a.coeff 0 = 1 → b.coeff 0 = 1 →
      algebraMap A S[X] f ^ k₁ * (a * b - 1) = 0 →
        dilate (f ^ (k₁ + k₂)) a * dilate (f ^ (k₁ + k₂)) b = 1 := by
    intro a b k₁ k₂ ha hb hk
    have h0 : (a * b - 1).coeff 0 = 0 := by
      rw [coeff_sub, mul_coeff_zero, ha, hb, one_mul, AddMonoidAlgebra.coeff_one_zero, sub_self]
    have hk' : algebraMap A S[X] f ^ (k₁ + k₂) * (a * b - 1) = 0 := by
      rw [add_comm, pow_add, mul_assoc, hk, mul_zero]
    have := dilate_eq_zero_of_mul_eq_zero h0 hk'
    rwa [map_sub, map_mul, map_one, sub_eq_zero] at this
  refine ⟨t₁ + t₂ + e, ⟨dilate (f ^ (t₁ + t₂)) φ, dilate (f ^ (t₁ + t₂)) φ',
    key φ φ' t₁ t₂ hφ0 hφ0' ht₁, ?_⟩, ?_, ?_⟩
  · rw [add_comm t₁ t₂]
    exact key φ' φ t₂ t₁ hφ0' hφ0 ht₂
  · simp [hφ0]
  · change (dilate (f ^ (t₁ + t₂)) φ).map (ι : S →+* S') = _
    rw [map_dilate, hφ, dilate_dilate, ← pow_add]

/-- An `A`-algebra map whose underlying `A`-linear map is a localisation at the powers of `f`,
and which sends `f` to a unit, is an `IsAwayMap`. -/
theorem IsAwayMap.of_isLocalizedModule {ι : S →ₐ[A] S'}
    [IsLocalizedModule (Submonoid.powers f) ι.toLinearMap] (hu : IsUnit (algebraMap A S' f)) :
    IsAwayMap f ι := by
  refine ⟨hu, fun x => ?_, fun r hr => ?_⟩
  · obtain ⟨⟨r, ⟨_, e, rfl⟩⟩, hr⟩ := IsLocalizedModule.surj (Submonoid.powers f) ι.toLinearMap x
    refine ⟨e, r, ?_⟩
    rw [← map_pow, ← Algebra.smul_def]
    exact hr
  · obtain ⟨⟨_, e, rfl⟩, he⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := ι.toLinearMap) (x₁ := r) (x₂ := 0) (by simpa using hr)
    refine ⟨e, ?_⟩
    rw [← map_pow, ← Algebra.smul_def]
    simpa [Submonoid.smul_def] using he

end IsAwayMap

section Dilation

variable (R : Type w) [Ring R] [Algebra A R] (f : A)

/-- The map `R → R_f = A_f ⊗[A] R` is an `IsAwayMap`. -/
theorem isAwayMap_includeRight :
    IsAwayMap f (Algebra.TensorProduct.includeRight : R →ₐ[A] Localization.Away f ⊗[A] R) := by
  have : IsLocalizedModule (Submonoid.powers f)
      (Algebra.TensorProduct.includeRight : R →ₐ[A] Localization.Away f ⊗[A] R).toLinearMap :=
    inferInstanceAs (IsLocalizedModule _ (TensorProduct.mk A (Localization.Away f) R 1))
  refine .of_isLocalizedModule ?_
  rw [Algebra.TensorProduct.algebraMap_apply]
  exact (IsLocalization.Away.algebraMap_isUnit f).map
    (Algebra.TensorProduct.includeLeftRingHom : Localization.Away f →+* _)

end Dilation

section Substitutions

variable (S : Type*) [Ring S] [Algebra A S]

/-- The substitution `Y ↦ Y + Z` from `S[Y]` to `S[Y][Z]`. -/
def shiftHom : S[X] →+* S[X][X] :=
  eval₂RingHom' (C.comp C) (C X + X) fun a =>
    ((commute_X (C a)).symm.map C).add_right (commute_X _).symm

@[simp]
theorem shiftHom_C (a : S) : shiftHom S (C a) = C (C a) := eval₂_C _ _

@[simp]
theorem shiftHom_X : shiftHom S X = C X + X := eval₂_X _ _

theorem coeff_zero_shiftHom (p : S[X]) : (shiftHom S p).coeff 0 = p := by
  have h : constantCoeff.comp (shiftHom S) = RingHom.id S[X] :=
    ringHom_ext (fun _ => by simp) (by simp)
  exact RingHom.congr_fun h p

/-- The specialisation `Y ↦ g X`, `Z ↦ c X` from `S[Y][Z]` to `S[X]`. -/
def specHom (g c : A) : S[X][X] →+* S[X] :=
  eval₂RingHom' (dilate g) (c • X) fun _ => commute_smul_X c _

@[simp]
theorem specHom_C (g c : A) (p : S[X]) : specHom S g c (C p) = dilate g p := eval₂_C _ _

@[simp]
theorem specHom_X (g c : A) : specHom S g c X = c • X := eval₂_X _ _

theorem coeff_zero_specHom (g c : A) (v : S[X][X]) :
    (specHom S g c v).coeff 0 = (v.coeff 0).coeff 0 := by
  have h : constantCoeff.comp (specHom S g c) = constantCoeff.comp constantCoeff :=
    ringHom_ext (fun a => by simp [specHom_C]) (by simp [specHom_X])
  exact RingHom.congr_fun h v

theorem specHom_dilate_shiftHom (g c d : A) (p : S[X]) :
    specHom S g c (dilate d (shiftHom S p)) = dilate (g + c * d) p := by
  have h : ((specHom S g c).comp (dilate d)).comp (shiftHom S) = dilate (g + c * d) := by
    refine ringHom_ext (fun a => ?_) ?_
    · simp [shiftHom, specHom_C]
    · have hd : dilate d (C (X : S[X]) + X) = C X + C (algebraMap A S[X] d) * X := by
        rw [map_add, dilate_C, dilate_X, Algebra.smul_def, Polynomial.algebraMap_apply]
      simp only [RingHom.coe_comp, Function.comp_apply, shiftHom_X, hd, map_add, map_mul,
        specHom_C, specHom_X, dilate_X, Polynomial.algebraMap_apply, dilate_C]
      rw [← Polynomial.algebraMap_apply, ← Algebra.smul_def, smul_smul, mul_comm d c, ← add_smul]
  exact RingHom.congr_fun h p

theorem map_specHom {S' : Type*} [Ring S'] [Algebra A S'] (ι : S →ₐ[A] S') (g c : A)
    (v : S[X][X]) :
    (specHom S g c v).map (ι : S →+* S') =
      specHom S' g c (v.map ((mapAlgHom ι : S[X] →ₐ[A] S'[X]) : S[X] →+* S'[X])) := by
  have h : (mapRingHom (ι : S →+* S')).comp (specHom S g c) =
      (specHom S' g c).comp (mapRingHom ((mapAlgHom ι : S[X] →ₐ[A] S'[X]) : S[X] →+* S'[X])) := by
    refine ringHom_ext (fun a => ?_) ?_
    · simp [map_dilate]
    · simp only [RingHom.coe_comp, Function.comp_apply, specHom_X, coe_mapRingHom, map_X,
        Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.map_mul, map_C, RingHom.coe_coe,
        AlgHom.commutes]
  exact RingHom.congr_fun h v

end Substitutions

/-- The dilation lemma for an abstract `IsAwayMap` `ι : S → S'`: for a unit `θ` of `S'[X]`
there is `k` such that whenever `g₁ − g₂ ∈ fᵏA`, some unit `ψ` of `S[X]` with `ψ(0) = 1`
satisfies `ψ · θ(g₂X) = θ(g₁X)` in `S'[X]`. -/
theorem IsAwayMap.exists_unit_lift_dilation {f : A} {S S' : Type*} [Ring S] [Ring S']
    [Algebra A S] [Algebra A S'] {ι : S →ₐ[A] S'} (h : IsAwayMap f ι) (θ : S'[X]ˣ) :
    ∃ k : ℕ, ∀ g₁ g₂ : A, g₁ - g₂ ∈ Ideal.span {f ^ k} →
      ∃ ψ : S[X]ˣ, (ψ : S[X]).coeff 0 = 1 ∧
        (ψ : S[X]).map (ι : S →+* S') * dilate g₂ (θ : S'[X]) = dilate g₁ (θ : S'[X]) := by
  have hι := h.polynomial
  let u : S'[X][X]ˣ := Units.map (shiftHom S' : S'[X] →* S'[X][X]) θ *
    Units.map ((C : S'[X] →+* S'[X][X]) : S'[X] →* S'[X][X]) θ⁻¹
  have hu : (u : S'[X][X]).coeff 0 = 1 := by
    simp only [u, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, mul_coeff_zero,
      coeff_zero_shiftHom, coeff_C_zero, Units.mul_inv]
  obtain ⟨s, v, hv0, hv⟩ := exists_unit_lift_dilate hι u hu
  refine ⟨s, fun g₁ g₂ hg => ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg
  refine ⟨Units.map (specHom S g₂ c : S[X][X] →* S[X]) v, ?_, ?_⟩
  · simp [coeff_zero_specHom, hv0]
  · have h1 := map_specHom S ι g₂ c v
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rw [h1, hv]
    simp only [u, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, map_mul, dilate_C,
      specHom_C]
    rw [mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]
    exact (specHom_dilate_shiftHom _ g₂ c (f ^ s) (θ : S'[X])).trans
      (by rw [hc, add_sub_cancel])

/-- **3.2.** Quillen's dilation lemma: let `R` be an `A`-algebra, not necessarily commutative,
`f ∈ A`, and `θ` a unit of `R_f[X]`, where `R_f = A_f ⊗[A] R`. Then there is `k` such that
whenever `g₁ − g₂ ∈ fᵏA`, some unit `ψ` of `R[X]` with `ψ(0) = 1` has image `θ(g₁X) θ(g₂X)⁻¹`
in `R_f[X]`, stated with the inverse multiplied out (Quillen 1976, Lemma 1, pp. 167–168).
Quillen assumes `θ(0) = 1`; the proof does not need it. -/
theorem exists_unit_lift_dilation (R : Type w) [Ring R] [Algebra A R] (f : A)
    (θ : (Localization.Away f ⊗[A] R)[X]ˣ) :
    ∃ k : ℕ, ∀ g₁ g₂ : A, g₁ - g₂ ∈ Ideal.span {f ^ k} →
      ∃ ψ : R[X]ˣ, (ψ : R[X]).coeff 0 = 1 ∧
        (ψ : R[X]).map (Algebra.TensorProduct.includeRight : R →ₐ[A] Localization.Away f ⊗[A] R) *
            (θ : (Localization.Away f ⊗[A] R)[X]).eval₂ C (g₂ • X) =
          (θ : (Localization.Away f ⊗[A] R)[X]).eval₂ C (g₁ • X) :=
  (isAwayMap_includeRight R f).exists_unit_lift_dilation θ

end LeanPool.QuillenSuslin
