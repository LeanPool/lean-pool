/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Statement
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Canonical maps between interval representations

For intervals `U, V` of `I_*`, the formula `f ↦ (t ↦ [t ∈ U] f)` defines a morphism
`k_U ⟶ k_V` as soon as, for `s ≤ t` with `t ∈ V` and `s ∈ U`, one has `t ∈ U ↔ s ∈ V`.
This covers the canonical quotient maps `a_{ji} : A j ⟶ A i`, `p_{ji} : P j ⟶ P i` and
`c_i : P i ⟶ Y`, and the inclusion `b_i : A i ⟶ P i` of the manuscript (diagram (2.1)).
We also show that `0 → A i → P i → Y → 0` is short exact (Lemma 2.1).
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- The compatibility condition under which the canonical formula is natural. -/
def IntervalCompatible (U V : Set (WithBot I)) : Prop :=
  ∀ ⦃s t : WithBot I⦄, s ≤ t → t ∈ V → s ∈ U → (t ∈ U ↔ s ∈ V)

open Classical in
/-- The canonical morphism `k_U ⟶ k_V`. -/
noncomputable def intervalMap (U V : Set (WithBot I)) [U.OrdConnected] [V.OrdConnected]
    (h : IntervalCompatible U V) : (intervalRep U : Rep k I) ⟶ intervalRep V where
  app t := ModuleCat.ofHom
    { toFun := fun f _ => if ht : t ∈ U then f ⟨(), ht⟩ else 0
      map_add' := fun f g => by funext x; split_ifs <;> simp
      map_smul' := fun r f => by funext x; split_ifs <;> simp }
  naturality s t hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    funext x
    change (if ht : t ∈ U then (if hs : s ∈ U then f ⟨(), hs⟩ else 0) else 0) =
      (if hs : s ∈ V then (if hs' : s ∈ U then f ⟨(), hs'⟩ else 0) else 0)
    by_cases hs : s ∈ U
    · have key := h (leOfHom hst) x.2 hs
      by_cases ht : t ∈ U
      · simp [hs, ht, key.mp ht]
      · simp [ht, mt key.mpr ht]
    · simp [hs]

open Classical in
lemma intervalMap_app_apply (U V : Set (WithBot I)) [U.OrdConnected] [V.OrdConnected]
    (h : IntervalCompatible U V) (t : WithBot I) (f : (intervalRep U : Rep k I).obj t)
    (x : {_x : Unit // t ∈ V}) :
    ((intervalMap U V h).app t).hom f x = if ht : t ∈ U then f ⟨(), ht⟩ else 0 := rfl

open IntervalLabel

lemma mem_A {i : I} {t : WithBot I} : t ∈ (A i).support ↔ ⊥ < t ∧ t ≤ i := Iff.rfl

lemma mem_P {i : I} {t : WithBot I} : t ∈ (P i).support ↔ t ≤ i := Iff.rfl

lemma mem_Y {t : WithBot I} : t ∈ (Y (I := I)).support ↔ t = ⊥ :=
  show t ≤ ⊥ ↔ t = ⊥ from le_bot_iff

lemma compatible_A {i j : I} (hij : i ≤ j) : IntervalCompatible (A j).support (A i).support := by
  intro s t hst ht hs
  exact ⟨fun _ => ⟨hs.1, hst.trans ht.2⟩, fun _ => ⟨ht.1, ht.2.trans (WithBot.coe_le_coe.mpr hij)⟩⟩

lemma compatible_P {i j : I} (hij : i ≤ j) : IntervalCompatible (P j).support (P i).support := by
  intro s t hst ht hs
  exact ⟨fun _ => hst.trans ht, fun _ => (show t ≤ (i : WithBot I) from ht).trans
    (WithBot.coe_le_coe.mpr hij)⟩

lemma compatible_b (i : I) : IntervalCompatible (A i).support (P i).support := by
  intro s t hst ht hs
  exact ⟨fun _ => hs.2, fun _ => ⟨lt_of_lt_of_le hs.1 hst, ht⟩⟩

lemma compatible_c (i : I) : IntervalCompatible (P i).support (Y (I := I)).support := by
  intro s t hst ht hs
  have ht' : t = ⊥ := mem_Y.mp ht
  have hs' : s = ⊥ := le_bot_iff.mp (ht' ▸ hst)
  subst ht' hs'
  exact ⟨fun _ => mem_Y.mpr rfl, fun _ => (bot_le : (⊥ : WithBot I) ≤ i)⟩


/-- The canonical quotient map `a_{ji} : A j ⟶ A i` for `i ≤ j`. -/
noncomputable def aMap {i j : I} (hij : i ≤ j) : (A j).rep k ⟶ (A i).rep k :=
  intervalMap _ _ (compatible_A hij)

/-- The canonical quotient map `p_{ji} : P j ⟶ P i` for `i ≤ j`. -/
noncomputable def pMap {i j : I} (hij : i ≤ j) : (P j).rep k ⟶ (P i).rep k :=
  intervalMap _ _ (compatible_P hij)

/-- The canonical inclusion `b_i : A i ⟶ P i`. -/
noncomputable def bMap (i : I) : (A i).rep k ⟶ (P i).rep k :=
  intervalMap _ _ (compatible_b i)

/-- The canonical quotient map `c_i : P i ⟶ Y`. -/
noncomputable def cMap (i : I) : (P i).rep k ⟶ (Y (I := I)).rep k :=
  intervalMap _ _ (compatible_c i)

open Classical in
/-- Composition of canonical maps. -/
lemma intervalMap_comp (U V W : Set (WithBot I)) [U.OrdConnected] [V.OrdConnected]
    [W.OrdConnected] (h₁ : IntervalCompatible U V) (h₂ : IntervalCompatible V W)
    (h₃ : IntervalCompatible U W) (h : ∀ t, t ∈ W → t ∈ U → t ∈ V) :
    intervalMap (k := k) U V h₁ ≫ intervalMap V W h₂ = intervalMap U W h₃ := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext x
  change (if htV : t ∈ V then (if htU : t ∈ U then f ⟨(), htU⟩ else 0) else 0) =
    (if htU : t ∈ U then f ⟨(), htU⟩ else 0)
  by_cases htU : t ∈ U
  · simp [htU, h t x.2 htU]
  · simp [htU]

lemma compatible_AP {i j : I} (hij : i ≤ j) : IntervalCompatible (A j).support (P i).support := by
  intro s t hst ht hs
  exact ⟨fun _ => hst.trans ht, fun _ => ⟨lt_of_lt_of_le hs.1 hst,
    (show t ≤ (i : WithBot I) from ht).trans (WithBot.coe_le_coe.mpr hij)⟩⟩

lemma aMap_comp_bMap {i j : I} (hij : i ≤ j) :
    aMap (k := k) hij ≫ bMap i = intervalMap _ _ (compatible_AP hij) :=
  intervalMap_comp _ _ _ _ _ _ (fun _ ht hA => ⟨hA.1, ht⟩)

lemma bMap_comp_pMap {i j : I} (hij : i ≤ j) :
    bMap (k := k) j ≫ pMap hij = intervalMap _ _ (compatible_AP hij) :=
  intervalMap_comp _ _ _ _ _ _ (fun _ _ hA => hA.2)

lemma pMap_comp_cMap {i j : I} (hij : i ≤ j) : pMap (k := k) hij ≫ cMap i = cMap j :=
  intervalMap_comp _ _ _ _ _ _ (fun t ht _ => by
    rw [mem_Y.mp ht]
    exact (bot_le : (⊥ : WithBot I) ≤ i))

open Classical in
lemma bMap_comp_cMap (i : I) : bMap (k := k) i ≫ cMap i = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext x
  change (if ht : t ∈ (P i).support then
    (if ht' : t ∈ (A i).support then f ⟨(), ht'⟩ else 0) else 0) = 0
  have : t ∉ (A i).support := fun h => (lt_irrefl _) (lt_of_lt_of_le h.1 (le_of_eq (mem_Y.mp x.2)))
  simp [this]

open Classical in
lemma coeffRep_aMap {i j : I} (hij : i ≤ j) : coeffRep (aMap (k := k) hij) = 1 := by
  change (if ht : (i : WithBot I) ∈ (A j).support then (1 : k) else 0) = 1
  rw [dite_eq_left (coe_mem_A.mpr hij)]

end ExtriangulatedRealization
