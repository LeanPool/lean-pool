/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Homs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Endomorphisms and isomorphisms of interval representations

A morphism between interval representations is determined by its values on `1` at the common
points. Every endomorphism of `k_U` is a scalar, since `U` is order-connected in the linear
order `I_*`. Morphisms `A j ⟶ Y` and `Y ⟶ P i` vanish, and a morphism from `Y` or `P j` to `Y`
is determined by its value at `*` (table (2.2)). Isomorphic interval representations have the
same support, so the labels `Y`, `A i`, `P i` give pairwise nonisomorphic representations.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- Morphisms of interval representations agreeing on `1` at all common points are equal. -/
lemma intervalRep_hom_ext {U V : Set (WithBot I)} [U.OrdConnected] [V.OrdConnected]
    {φ ψ : (intervalRep U : Rep k I) ⟶ intervalRep V}
    (h : ∀ t (_ : t ∈ U) (hV : t ∈ V),
      (φ.app t).hom (oneAt U t) ⟨(), hV⟩ = (ψ.app t).hom (oneAt U t) ⟨(), hV⟩) : φ = ψ := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext x
  by_cases hU : t ∈ U
  · rw [app_apply_eq_mul φ hU f x, app_apply_eq_mul ψ hU f x, h t hU x.2]
  · rw [intervalRep_obj_eq_zero hU f, map_zero, map_zero]

lemma oneAt_ne_zero {U : Set (WithBot I)} [U.OrdConnected] {t : WithBot I} (ht : t ∈ U) :
    oneAt (k := k) U t ≠ 0 := fun h => one_ne_zero (congrFun h ⟨(), ht⟩)

/-- The identity of a nonempty interval representation is nonzero. -/
lemma intervalRep_id_ne_zero {U : Set (WithBot I)} [U.OrdConnected] {t : WithBot I}
    (ht : t ∈ U) : 𝟙 (intervalRep U : Rep k I) ≠ 0 := fun h =>
  oneAt_ne_zero ht (congrArg (fun φ : (intervalRep U : Rep k I) ⟶ _ => (φ.app t).hom
    (oneAt U t)) h)

lemma label_id_ne_zero (l : IntervalLabel I) : 𝟙 (l.rep k) ≠ 0 := by
  rcases l with _ | i | i
  · exact intervalRep_id_ne_zero (U := (Y (I := I)).support) (t := ⊥) (Set.mem_Iic.mpr le_rfl)
  · exact intervalRep_id_ne_zero (U := (A i).support) (mem_A_self i)
  · exact intervalRep_id_ne_zero (U := (P i).support) (t := (i : WithBot I))
      (Set.mem_Iic.mpr le_rfl)

/-- The value of a morphism of interval representations on `1` is the same at all common
points. -/
lemma intervalRep_value_eq {U V : Set (WithBot I)} [U.OrdConnected] [V.OrdConnected]
    (φ : (intervalRep U : Rep k I) ⟶ intervalRep V) {s t : WithBot I} (hsU : s ∈ U)
    (hsV : s ∈ V) (htV : t ∈ V) (hst : s ≤ t) :
    (φ.app t).hom (oneAt U t) ⟨(), htV⟩ = (φ.app s).hom (oneAt U s) ⟨(), hsV⟩ := by
  have h := intervalRep_app_map φ hst (oneAt U s) ⟨(), htV⟩
  have h1 : ((intervalRep U : Rep k I).map (homOfLE hst)).hom (oneAt U s) = oneAt U t := by
    funext x
    rw [intervalRep_map_apply, dite_eq_left hsU]
  rw [h1, dite_eq_left hsV] at h
  exact h

/-- A morphism of interval representations is determined by its value on `1` at one common
point. -/
lemma intervalRep_hom_ext_of_value {U V : Set (WithBot I)} [U.OrdConnected] [V.OrdConnected]
    {t₀ : WithBot I} (hU₀ : t₀ ∈ U) (hV₀ : t₀ ∈ V)
    {φ ψ : (intervalRep U : Rep k I) ⟶ intervalRep V}
    (h : (φ.app t₀).hom (oneAt U t₀) ⟨(), hV₀⟩ = (ψ.app t₀).hom (oneAt U t₀) ⟨(), hV₀⟩) :
    φ = ψ := by
  apply intervalRep_hom_ext
  intro t hU hV
  rcases le_total t₀ t with ht | ht
  · rw [intervalRep_value_eq φ hU₀ hV₀ hV ht, intervalRep_value_eq ψ hU₀ hV₀ hV ht, h]
  · rw [← intervalRep_value_eq φ hU hV hV₀ ht, ← intervalRep_value_eq ψ hU hV hV₀ ht, h]

/-- Morphism spaces between interval representations have dimension at most one. -/
lemma rank_intervalRep_hom_le_one (U V : Set (WithBot I)) [U.OrdConnected] [V.OrdConnected] :
    Module.rank k ((intervalRep U : Rep k I) ⟶ intervalRep V) ≤ 1 := by
  by_cases h : ∃ t, t ∈ U ∧ t ∈ V
  · obtain ⟨t₀, hU₀, hV₀⟩ := h
    let ev : ((intervalRep U : Rep k I) ⟶ intervalRep V) →ₗ[k] k :=
      { toFun := fun φ => (φ.app t₀).hom (oneAt U t₀) ⟨(), hV₀⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective ev := fun φ ψ hφψ => intervalRep_hom_ext_of_value hU₀ hV₀ hφψ
    exact (LinearMap.rank_le_of_injective ev hinj).trans_eq (by simp)
  · have : Subsingleton ((intervalRep U : Rep k I) ⟶ intervalRep V) :=
      ⟨fun φ ψ => intervalRep_hom_ext fun t hU hV => absurd ⟨t, hU, hV⟩ h⟩
    rw [rank_zero_iff.mpr this]
    exact zero_le_one

/-- Every endomorphism of an interval representation is a scalar. -/
lemma intervalRep_endo_eq_smul {U : Set (WithBot I)} [U.OrdConnected] {t₀ : WithBot I}
    (h₀ : t₀ ∈ U) (φ : (intervalRep U : Rep k I) ⟶ intervalRep U) :
    φ = (φ.app t₀).hom (oneAt U t₀) ⟨(), h₀⟩ • 𝟙 _ := by
  apply intervalRep_hom_ext
  intro t hU hV
  change _ = (φ.app t₀).hom (oneAt U t₀) ⟨(), h₀⟩ * 1
  rw [mul_one]
  rcases le_total t₀ t with h | h
  · exact intervalRep_value_eq φ h₀ h₀ hV h
  · exact (intervalRep_value_eq φ hV hV h₀ h).symm

/-- Every endomorphism of a labelled interval is a scalar. -/
lemma label_endo_eq_smul (l : IntervalLabel I) (φ : l.rep k ⟶ l.rep k) :
    ∃ c : k, φ = c • 𝟙 _ := by
  rcases l with _ | i | i
  · exact ⟨_, intervalRep_endo_eq_smul (U := (Y (I := I)).support) (t₀ := ⊥)
      (Set.mem_Iic.mpr le_rfl) φ⟩
  · exact ⟨_, intervalRep_endo_eq_smul (U := (A i).support) (mem_A_self i) φ⟩
  · exact ⟨_, intervalRep_endo_eq_smul (U := (P i).support) (t₀ := (i : WithBot I))
      (Set.mem_Iic.mpr le_rfl) φ⟩

lemma mem_Y_iff {t : WithBot I} : t ∈ (Y (I := I)).support ↔ t = ⊥ := by
  change t ∈ Set.Iic ⊥ ↔ _
  rw [Set.mem_Iic, le_bot_iff]

/-- `Hom(A j, Y) = 0`. -/
lemma hom_A_Y_eq_zero (j : I) (φ : (A j).rep k ⟶ (Y (I := I)).rep k) : φ = 0 :=
  intervalRep_hom_ext fun _ hU hV =>
    absurd ((mem_Y_iff.mp hV) ▸ hU) (not_bot_mem_A j)

/-- `Hom(Y, P i) = 0`. -/
lemma hom_Y_P_eq_zero (i : I) (φ : (Y (I := I)).rep k ⟶ (P i).rep k) : φ = 0 := by
  apply intervalRep_hom_ext
  intro t hU hV
  obtain rfl := mem_Y_iff.mp hU
  exact coeffBot_eq_zero_of_P (l := Y) trivial i (coe_not_mem_Y i) φ

/-- A morphism into `Y` from an interval containing `*` is determined by its value at `*`. -/
lemma hom_to_Y_ext {l : IntervalLabel I} (hl : HasBot (k := k) l)
    {φ ψ : l.rep k ⟶ (Y (I := I)).rep k}
    (h : coeffBot hl (show HasBot (k := k) Y from trivial) φ =
      coeffBot hl (show HasBot (k := k) Y from trivial) ψ) : φ = ψ := by
  apply intervalRep_hom_ext
  intro t hU hV
  obtain rfl := mem_Y_iff.mp hV
  exact h

/-- A morphism into `Y` from an interval containing `*` is a multiple of any morphism with
value `1` at `*`. -/
lemma hom_to_Y_eq_smul {l : IntervalLabel I} (hl : HasBot (k := k) l)
    (g : l.rep k ⟶ (Y (I := I)).rep k)
    (hg : coeffBot hl (show HasBot (k := k) Y from trivial) g = 1)
    (φ : l.rep k ⟶ (Y (I := I)).rep k) :
    φ = coeffBot hl (show HasBot (k := k) Y from trivial) φ • g := by
  apply hom_to_Y_ext hl
  rw [coeffBot_smul, hg, mul_one]

lemma coeffBot_cMap (j : I) :
    coeffBot (show HasBot (k := k) (P j) from trivial) (show HasBot (k := k) Y from trivial)
      (cMap (k := k) j) = 1 :=
  (intervalMap_app_apply (k := k) _ _ _ ⊥ _ _).trans
    (dite_eq_left (show (⊥ : WithBot I) ∈ (P j).support from Set.mem_Iic.mpr bot_le))

/-- Isomorphic interval representations have the same support. -/
lemma support_eq_of_iso {U V : Set (WithBot I)} [U.OrdConnected] [V.OrdConnected]
    (e : (intervalRep U : Rep k I) ≅ intervalRep V) : U = V := by
  have key : ∀ {U V : Set (WithBot I)} [U.OrdConnected] [V.OrdConnected]
      (e : (intervalRep U : Rep k I) ≅ intervalRep V) (t : WithBot I), t ∈ U → t ∈ V := by
    intro U V _ _ e t hU
    by_contra hV
    apply oneAt_ne_zero (k := k) hU
    have h := congrArg (fun φ : (intervalRep U : Rep k I) ⟶ _ => (φ.app t).hom (oneAt U t))
      e.hom_inv_id
    change (e.inv.app t).hom ((e.hom.app t).hom (oneAt U t)) = oneAt U t at h
    rw [intervalRep_obj_eq_zero hV ((e.hom.app t).hom (oneAt U t)), map_zero] at h
    exact h.symm
  ext t
  exact ⟨key e t, key e.symm t⟩

/-- The support determines the label. -/
lemma support_injective : Function.Injective (IntervalLabel.support (I := I)) := by
  have hbotP : ∀ i : I, (⊥ : WithBot I) ∈ (P i).support := fun i => Set.mem_Iic.mpr bot_le
  have hiP : ∀ i : I, (i : WithBot I) ∈ (P i).support := fun i => Set.mem_Iic.mpr le_rfl
  intro l l' h
  rcases l with _ | i | i <;> rcases l' with _ | j | j
  · rfl
  · exact absurd (h ▸ (show (⊥ : WithBot I) ∈ (Y (I := I)).support from Set.mem_Iic.mpr le_rfl))
      (not_bot_mem_A j)
  · exact absurd (h.symm ▸ hiP j) (coe_not_mem_Y j)
  · exact absurd (h.symm ▸ (show (⊥ : WithBot I) ∈ (Y (I := I)).support from
      Set.mem_Iic.mpr le_rfl)) (not_bot_mem_A i)
  · have h₁ := coe_mem_A.mp (h ▸ mem_A_self i)
    have h₂ := coe_mem_A.mp (h.symm ▸ mem_A_self j)
    rw [le_antisymm h₁ h₂]
  · exact absurd (h.symm ▸ hbotP j) (not_bot_mem_A i)
  · exact absurd (h ▸ hiP i) (coe_not_mem_Y i)
  · exact absurd (h ▸ hbotP i) (not_bot_mem_A j)
  · have h₁ : (i : WithBot I) ∈ (P j).support := h ▸ hiP i
    have h₂ : (j : WithBot I) ∈ (P i).support := h.symm ▸ hiP j
    rw [le_antisymm (WithBot.coe_le_coe.mp (Set.mem_Iic.mp h₁))
      (WithBot.coe_le_coe.mp (Set.mem_Iic.mp h₂))]

/-- Isomorphic labelled intervals have equal labels. -/
lemma label_eq_of_iso {l l' : IntervalLabel I} (e : l.rep k ≅ l'.rep k) : l = l' :=
  support_injective (support_eq_of_iso e)

end ExtriangulatedRealization
