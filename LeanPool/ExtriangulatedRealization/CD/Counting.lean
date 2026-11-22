/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Indecomposables
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Counting in `C(D)`

Morphism spaces of `C(D)` have at most countable dimension when every `D_i` does: between
single objects they are `k`, `D_i`, `0`, or a morphism space between interval representations,
of dimension at most one, and `Hom(M, N)` is the finite product of the spaces between the
entries. Every indecomposable is isomorphic to a single object, so it has endomorphism ring `k`
and the extension spaces between indecomposables have dimension at most one by (4.1); the
isomorphism classes of indecomposables are in bijection with the labels `X`, `Y`, `A i`, `P i`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Abelian Cardinal

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

attribute [local instance] HasExt.standard

/-! ### Dimensions of morphism spaces -/

lemma rank_pi_le_aleph0 {ι : Type*} [Finite ι] {M : ι → Type u} [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] (h : ∀ i, Module.rank k (M i) ≤ ℵ₀) :
    Module.rank k (∀ i, M i) ≤ ℵ₀ := by
  rw [rank_pi]
  calc Cardinal.sum (fun i => Module.rank k (M i)) ≤ Cardinal.sum (fun _ : ι => ℵ₀) :=
        Cardinal.sum_le_sum _ _ h
    _ = Cardinal.lift #ι * Cardinal.lift ℵ₀ := Cardinal.sum_const _ _
    _ ≤ ℵ₀ := by
        rw [Cardinal.lift_aleph0]
        exact (Cardinal.mul_le_max _ _).trans (max_le (max_le
          (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0) le_rfl) le_rfl)

/-- Morphism spaces between labels have at most countable dimension. -/
lemma rank_indCat_hom_le (hD : ∀ i, Module.rank k (D.obj (op i)) ≤ ℵ₀) (l l' : IndCat D) :
    Module.rank k (l ⟶ l') ≤ ℵ₀ := by
  rcases l with _ | a <;> rcases l' with _ | b
  · change Module.rank k k ≤ ℵ₀
    simp
  · rcases b with _ | i | i
    · change Module.rank k PUnit ≤ ℵ₀
      simp
    · exact hD i
    · change Module.rank k PUnit ≤ ℵ₀
      simp
  · change Module.rank k PUnit ≤ ℵ₀
    simp
  · change Module.rank k (a ⟶ b) ≤ ℵ₀
    rw [(InducedCategory.homLinearEquiv (R := k)).rank_eq]
    exact (rank_intervalRep_hom_le_one _ _).trans Cardinal.one_le_aleph0

/-- Every morphism space of `C(D)` has at most countable dimension. -/
lemma rank_hom_le_aleph0 (hD : ∀ i, Module.rank k (D.obj (op i)) ≤ ℵ₀) (X Y : CD D) :
    Module.rank k (X ⟶ Y) ≤ ℵ₀ := by
  change Module.rank k (∀ i j, X.X i ⟶ Y.X j) ≤ ℵ₀
  exact rank_pi_le_aleph0 fun i => rank_pi_le_aleph0 fun j => rank_indCat_hom_le D hD _ _

/-! ### Indecomposables -/

/-- Every indecomposable of `C(D)` has endomorphism ring `k`. -/
lemma existsUnique_smul_of_isIndecomposable {X : CD D} (hX : Indecomposable X) (f : X ⟶ X) :
    ∃! c : k, f = c • 𝟙 X := by
  obtain ⟨l, ⟨e⟩⟩ := exists_iso_single_of_isIndecomposable D hX
  have h : ∀ g : X ⟶ X, ∃ c : k, g = c • 𝟙 X := fun g => by
    obtain ⟨c, hc⟩ := single_endo_eq_smul D l (e.inv ≫ g ≫ e.hom)
    refine ⟨c, ?_⟩
    have hg : g = e.hom ≫ (e.inv ≫ g ≫ e.hom) ≫ e.inv := by simp
    rw [hg, hc]
    simp
  exact existsUnique_smul_id (fun h0 => hX.1 ((IsZero.iff_id_eq_zero X).mpr h0)) h f

/-- Extension spaces between indecomposables have dimension at most one. -/
lemma rank_ext_le_one_of_isIndecomposable {A C : CD D} (hA : Indecomposable A)
    (hC : Indecomposable C) : Module.rank k ((cdData D).Ext C A) ≤ 1 := by
  classical
  obtain ⟨a, ⟨eA⟩⟩ := exists_iso_single_of_isIndecomposable D hA
  obtain ⟨c, ⟨eC⟩⟩ := exists_iso_single_of_isIndecomposable D hC
  let e : (cdData D).Ext C A ≃ₗ[k] (cdData D).Ext (single D c) (single D a) :=
    Ext.linearEquivOfIso ((rho D).mapIso eC) ((rho D).mapIso eA) 1
  rw [e.rank_eq, rank_ext_single]
  split_ifs <;> simp

/-- The isomorphism class of a single object. -/
def indClass (l : IndCat D) : IndecomposableClasses (CD D) :=
  ⟨{Y | Nonempty (Y ≅ single D l)}, single D l, single_isIndecomposable D l, rfl⟩

lemma indClass_bijective : Function.Bijective (indClass D) := by
  refine ⟨fun l l' h => ?_, fun ⟨s, X, hX, hs⟩ => ?_⟩
  · have hmem : single D l ∈ (indClass D l').1 := by
      rw [← h]
      exact ⟨Iso.refl _⟩
    obtain ⟨e⟩ := hmem
    exact eq_of_single_iso D e
  · obtain ⟨l, ⟨e⟩⟩ := exists_iso_single_of_isIndecomposable D hX
    refine ⟨l, Subtype.ext ?_⟩
    change {Y | Nonempty (Y ≅ single D l)} = s
    rw [hs]
    ext Y
    exact ⟨fun ⟨e'⟩ => ⟨e' ≪≫ e.symm⟩, fun ⟨e'⟩ => ⟨e' ≪≫ e⟩⟩

lemma lift_mk_indecomposableClasses :
    Cardinal.lift.{u} #(IndecomposableClasses (CD D)) = Cardinal.lift.{max 1 u} #(IndCat D) :=
  (Cardinal.mk_congr_lift (Equiv.ofBijective _ (indClass_bijective D))).symm

/-- The labels `Y`, `A i`, `P i`. -/
def intervalLabelEquiv : IntervalLabel I ≃ Option (I ⊕ I) where
  toFun
    | .Y => none
    | .A i => some (.inl i)
    | .P i => some (.inr i)
  invFun
    | none => .Y
    | some (.inl i) => .A i
    | some (.inr i) => .P i
  left_inv l := by rcases l <;> rfl
  right_inv o := by rcases o with _ | _ | _ <;> rfl

/-- With `#I = ℵ₁`, there are `ℵ₁` labels. -/
lemma mk_indCat (hI : #I = ℵ₁) : #(IndCat D) = ℵ₁ := by
  have h : ℵ₀ ≤ ℵ₁ := aleph0_le_aleph 1
  change #(Option (IntervalLabel I)) = ℵ₁
  rw [mk_option, mk_congr (intervalLabelEquiv (I := I)), mk_option, mk_sum, lift_id, hI,
    add_eq_self h, add_one_eq h, add_one_eq h]

/-- With `#I = ℵ₁`, there are `ℵ₁` isomorphism classes of indecomposables. -/
lemma mk_indecomposableClasses (hI : #I = ℵ₁) : #(IndecomposableClasses (CD D)) = ℵ₁ := by
  have h := lift_mk_indecomposableClasses D
  rw [mk_indCat D hI, lift_aleph, lift_id'] at h
  simpa using h

end ExtriangulatedRealization
