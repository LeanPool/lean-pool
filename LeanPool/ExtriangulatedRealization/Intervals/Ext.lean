/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Endomorphisms
public import LeanPool.ExtriangulatedRealization.Intervals.Exact
public import LeanPool.ExtriangulatedRealization.Intervals.Injective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# First extensions between interval representations (4.1)

Since `P i` and `Y` are injective, `Ext¹(-, P i) = Ext¹(-, Y) = 0`. Applying `Hom(B, -)` to
`0 → A i → P i → Y → 0` shows that every class in `Ext¹(B, A i)` is `g^* ε_i` for some
`g : B ⟶ Y`, where `ε_i` is the class of the sequence, and `g^* ε_i = 0` exactly when `g`
factors through `c_i : P i ⟶ Y`. With table (2.2) this gives the only nonzero first extension
spaces between intervals: `Ext¹(Y, A i) ≃ k` and `Ext¹(P j, A i) ≃ k` for `j < i`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Abelian

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasExt.standard

/-! ### Generalities: transport along isomorphisms, biproducts, zero objects -/

section Transport

universe w

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

/-- Postcomposition with an isomorphism, as a linear equivalence of `Ext`. -/
noncomputable def Ext.postcompIso (X : C) {Y Y' : C} (e : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃ₗ[R] Ext X Y' n where
  toFun x := x.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun x := x.comp (Ext.mk₀ e.inv) (add_zero n)
  map_add' x y := Ext.add_comp _ _ _ _
  map_smul' r x := Ext.smul_comp _ _ _ _
  left_inv x := by
    simp only
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.comp_mk₀_id]
  right_inv x := by
    simp only
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.comp_mk₀_id]

/-- Precomposition with an isomorphism, as a linear equivalence of `Ext`. -/
noncomputable def Ext.precompIso {X X' : C} (e : X ≅ X') (Y : C) (n : ℕ) :
    Ext X Y n ≃ₗ[R] Ext X' Y n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  map_add' x y := Ext.comp_add _ _ _ _
  map_smul' r x := Ext.comp_smul _ _ _ _
  left_inv x := by
    simp only
    rw [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    simp only
    rw [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]

/-- `Ext` is invariant under isomorphisms of both arguments, as a linear equivalence. -/
noncomputable def Ext.linearEquivOfIso {X X' Y Y' : C} (e₁ : X ≅ X') (e₂ : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃ₗ[R] Ext X' Y' n :=
  (Ext.postcompIso X e₂ n).trans (Ext.precompIso e₁ Y' n)

/-- `Ext(⨁ f, Y)` vanishes when every `Ext(f j, Y)` does. -/
lemma Ext.eq_zero_of_source_biproduct {J : Type*} [Finite J] (f : J → C) [HasBiproduct f]
    {Y : C} {n : ℕ} (h : ∀ j (η : Ext (f j) Y n), η = 0) (η : Ext (⨁ f) Y n) : η = 0 := by
  let := Fintype.ofFinite J
  rw [← Ext.mk₀_id_comp η, ← biproduct.total, Ext.mk₀_sum, Ext.sum_comp]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    h j ((Ext.mk₀ (biproduct.ι f j)).comp η (zero_add n)), Ext.comp_zero]

/-- `Ext(X, ⨁ g)` vanishes when every `Ext(X, g j)` does. -/
lemma Ext.eq_zero_of_target_biproduct {J : Type*} [Finite J] (g : J → C) [HasBiproduct g]
    {X : C} {n : ℕ} (h : ∀ j (η : Ext X (g j) n), η = 0) (η : Ext X (⨁ g) n) : η = 0 := by
  let := Fintype.ofFinite J
  rw [← Ext.comp_mk₀_id η, ← biproduct.total, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    h j (η.comp (Ext.mk₀ (biproduct.π g j)) (add_zero n)), Ext.zero_comp]

/-- `Ext` out of a zero object vanishes. -/
lemma Ext.eq_zero_of_isZero_source {X Y : C} (hX : IsZero X) {n : ℕ} (η : Ext X Y n) : η = 0 := by
  rw [← Ext.mk₀_id_comp η, hX.eq_of_src (𝟙 X) 0, Ext.mk₀_zero, Ext.zero_comp]

/-- `Ext` into a zero object vanishes. -/
lemma Ext.eq_zero_of_isZero_target {X Y : C} (hY : IsZero Y) {n : ℕ} (η : Ext X Y n) : η = 0 := by
  rw [← Ext.comp_mk₀_id η, hY.eq_of_src (𝟙 Y) 0, Ext.mk₀_zero, Ext.comp_zero]

end Transport

/-! ### The interval class `ε_i` -/

/-- The class `ε_i ∈ Ext¹(Y, A i)` of `0 → A i → P i → Y → 0`. -/
noncomputable def epsRep (i : I) : Ext ((Y (I := I)).rep k) ((A i).rep k) 1 :=
  (intervalSeq_shortExact (k := k) i).extClass

lemma ext_one_P_eq_zero {B : Rep k I} (i : I) (ξ : Ext B ((P i).rep k) 1) : ξ = 0 :=
  haveI := injective_P (k := k) i
  Ext.eq_zero_of_injective ξ

lemma ext_one_Y_eq_zero {B : Rep k I} (ξ : Ext B ((Y (I := I)).rep k) 1) : ξ = 0 :=
  haveI := injective_Y (k := k) (I := I)
  Ext.eq_zero_of_injective ξ

/-- Every class in `Ext¹(B, A i)` is a pullback of `ε_i`. -/
lemma exists_eq_comp_epsRep {B : Rep k I} (i : I) (ξ : Ext B ((A i).rep k) 1) :
    ∃ g : B ⟶ (Y (I := I)).rep k, (Ext.mk₀ g).comp (epsRep i) (zero_add 1) = ξ := by
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ B (intervalSeq_shortExact (k := k) i) ξ
    (ext_one_P_eq_zero i _) (zero_add 1)
  exact ⟨Ext.homEquiv₀ (show Ext B ((Y (I := I)).rep k) 0 from x₃),
    by rw [Ext.mk₀_homEquiv₀_apply]; exact hx₃⟩

/-- `g^* ε_i = 0` exactly when `g` factors through `c_i`. -/
lemma comp_epsRep_eq_zero_iff {B : Rep k I} (i : I) (g : B ⟶ (Y (I := I)).rep k) :
    (Ext.mk₀ g).comp (epsRep i) (zero_add 1) = 0 ↔ ∃ h : B ⟶ (P i).rep k, h ≫ cMap i = g := by
  constructor
  · intro hg
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ B (intervalSeq_shortExact (k := k) i)
      (Ext.mk₀ g) (zero_add 1) hg
    refine ⟨Ext.homEquiv₀ (show Ext B ((P i).rep k) 0 from x₂), (Ext.mk₀_bijective _ _).1 ?_⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hx₂
  · rintro ⟨h, rfl⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
    erw [(intervalSeq_shortExact (k := k) i).comp_extClass]
    exact Ext.comp_zero (Ext.mk₀ h) ((A i).rep k) 1 1 _

/-! ### The table (4.1) -/

lemma ext_one_A_A_eq_zero (i j : I) (ξ : Ext ((A j).rep k) ((A i).rep k) 1) : ξ = 0 := by
  obtain ⟨g, rfl⟩ := exists_eq_comp_epsRep i ξ
  rw [hom_A_Y_eq_zero j g, Ext.mk₀_zero]
  rw [Ext.zero_comp]

lemma ext_one_P_A_eq_zero {i j : I} (hij : i ≤ j) (ξ : Ext ((P j).rep k) ((A i).rep k) 1) :
    ξ = 0 := by
  obtain ⟨g, rfl⟩ := exists_eq_comp_epsRep i ξ
  rw [comp_epsRep_eq_zero_iff]
  refine ⟨coeffBot (show HasBot (k := k) Y from trivial)
    g • pMap hij, ?_⟩
  rw [Linear.smul_comp, pMap_comp_cMap]
  exact (hom_to_Y_eq_smul (l := P j) (cMap j) (coeffBot_cMap j) g).symm

/-- `Ext¹(Y, A i)` is spanned by the nonzero class `ε_i`. -/
lemma ext_one_Y_A (i : I) :
    ∃ v : Ext ((Y (I := I)).rep k) ((A i).rep k) 1, v ≠ 0 ∧ ∀ w, ∃ r : k, r • v = w := by
  refine ⟨epsRep i, fun h => ?_, fun w => ?_⟩
  · have h' : (Ext.mk₀ (𝟙 _)).comp (epsRep (k := k) i) (zero_add 1) = 0 := by
      rw [Ext.mk₀_id_comp]; exact h
    obtain ⟨φ, hφ⟩ := (comp_epsRep_eq_zero_iff i _).mp h'
    rw [hom_Y_P_eq_zero i φ, zero_comp] at hφ
    exact label_id_ne_zero (k := k) Y hφ.symm
  · obtain ⟨g, rfl⟩ := exists_eq_comp_epsRep i w
    refine ⟨coeffBot (show HasBot (k := k) Y from trivial)
      g, ?_⟩
    conv_rhs => rw [hom_to_Y_eq_smul (l := Y) (𝟙 _) (coeffBot_id _) g]
    rw [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]

/-- `Ext¹(P j, A i)` for `j < i` is spanned by the nonzero class `c_j^* ε_i`. -/
lemma ext_one_P_A {i j : I} (hji : j < i) :
    ∃ v : Ext ((P j).rep k) ((A i).rep k) 1, v ≠ 0 ∧ ∀ w, ∃ r : k, r • v = w := by
  refine ⟨(Ext.mk₀ (cMap j)).comp (epsRep i) (zero_add 1), fun h => ?_, fun w => ?_⟩
  · obtain ⟨φ, hφ⟩ := (comp_epsRep_eq_zero_iff i _).mp h
    have h1 := congrArg (coeffBot (show HasBot (k := k) Y from trivial)) hφ
    rw [coeffBot_comp (l' := P i) trivial _, coeffBot_cMap, coeffBot_cMap,
      coeffBot_eq_zero_of_P (l := P j) i
        (fun h => absurd (WithBot.coe_le_coe.mp (Set.mem_Iic.mp h)) (not_le.mpr hji)) φ,
      zero_mul] at h1
    exact zero_ne_one h1
  · obtain ⟨g, rfl⟩ := exists_eq_comp_epsRep i w
    refine ⟨coeffBot (show HasBot (k := k) Y from trivial) g, ?_⟩
    conv_rhs => rw [hom_to_Y_eq_smul (l := P j) (cMap j) (coeffBot_cMap j) g]
    rw [Ext.mk₀_smul, Ext.smul_comp]

end ExtriangulatedRealization
