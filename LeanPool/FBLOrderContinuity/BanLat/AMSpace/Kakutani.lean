/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.FBLOrderContinuity.BanLat.AMSpace.Characters
public import LeanPool.FBLOrderContinuity.BanLat.Convergences.Uniform
public import LeanPool.OrderClosures.BanLat.Examples.CofK.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass



/-!
# Kakutani's representation theorem for AM-spaces with unit

This file proves the Bohnenblust--Kakutani--Krein representation theorem:
every non-trivial AM-space with unit is Banach-lattice isomorphic to the space
of continuous real-valued functions on its compact character space.
-/

@[expose] public section

namespace AMSpaceWithUnit

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [AMSpaceWithUnit X]

/-- The **Gelfand transform** sends an element `x : X` to the continuous
function `φ ↦ φ x` on the character space. -/
noncomputable def gelfand (x : X) : C(LatticeCharacter X, ℝ) where
  toFun φ := φ x
  continuous_toFun := LatticeCharacter.continuous_eval X x

@[simp] theorem gelfand_apply (x : X) (φ : LatticeCharacter X) :
    gelfand x φ = φ x := rfl

@[simp] theorem gelfand_unit :
    gelfand (AMSpaceWithUnit.unit : X) = 1 := by
  ext φ
  exact φ.map_unit

/-- The Gelfand transform is a vector lattice homomorphism. -/
theorem gelfand_isVecLatHom :
    IsVecLatHom (gelfand : X → C(LatticeCharacter X, ℝ)) where
  map_add x y := by
    ext φ
    exact map_add φ.toVecLatHom x y
  map_smul r x := by
    ext φ
    exact map_smul φ.toVecLatHom r x
  map_sup' x y := by
    ext φ
    change φ (x ⊔ y) = max (φ x) (φ y)
    exact LatticeCharacter.map_sup φ x y
  map_inf' x y := by
    ext φ
    change φ (x ⊓ y) = min (φ x) (φ y)
    exact LatticeCharacter.map_inf φ x y

/-- The Gelfand transform preserves norms. -/
theorem norm_gelfand [Nontrivial X] (x : X) :
    ‖(gelfand x : C(LatticeCharacter X, ℝ))‖ = ‖x‖ := by
  have : Nonempty (LatticeCharacter X) := by
    obtain ⟨φ, _⟩ := LatticeCharacter.exists_abs_apply_eq_norm (X := X) x
    exact ⟨φ⟩
  apply le_antisymm
  · rw [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_le
    intro φ
    rw [gelfand_apply, Real.norm_eq_abs]
    exact φ.abs_apply_le_norm x
  · obtain ⟨φ, hφ⟩ := LatticeCharacter.exists_abs_apply_eq_norm (X := X) x
    calc
      ‖x‖ = |φ x| := hφ.symm
      _ = ‖gelfand x φ‖ := by simp [gelfand_apply, Real.norm_eq_abs]
      _ ≤ ‖(gelfand x : C(LatticeCharacter X, ℝ))‖ :=
        ContinuousMap.norm_coe_le_norm _ _

/-- The Gelfand transform is an isometry. -/
theorem gelfand_isometry [Nontrivial X] :
    Isometry (gelfand : X → C(LatticeCharacter X, ℝ)) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : gelfand x - gelfand y = gelfand (x - y) := by
    have h2 : gelfand (x - y) + gelfand y = gelfand x := by
      rw [← gelfand_isVecLatHom.map_add, sub_add_cancel]
    rw [← h2]
    abel
  rw [h1, norm_gelfand]

/-- The Gelfand transform is surjective. -/
theorem gelfand_surjective [Nontrivial X] :
    Function.Surjective (gelfand : X → C(LatticeCharacter X, ℝ)) := by
  set L : Set C(LatticeCharacter X, ℝ) := Set.range gelfand with hL_def
  have hL_inf : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨x ⊓ y, gelfand_isVecLatHom.map_inf' x y⟩
  have hL_sup : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨x ⊔ y, gelfand_isVecLatHom.map_sup' x y⟩
  have hL_ne : L.Nonempty := ⟨gelfand 0, 0, rfl⟩
  have hL_sep : L.SeparatesPointsStrongly := by
    intro v φ ψ
    by_cases hφψ : φ = ψ
    · subst hφψ
      refine ⟨gelfand ((v φ) • AMSpaceWithUnit.unit), ⟨(v φ) • AMSpaceWithUnit.unit, rfl⟩,
        ?_, ?_⟩
      · change φ ((v φ) • AMSpaceWithUnit.unit) = v φ
        have h1 : φ ((v φ) • (AMSpaceWithUnit.unit : X)) =
            (v φ) * φ (AMSpaceWithUnit.unit : X) := map_smul φ.toVecLatHom _ _
        rw [h1, φ.map_unit_apply, mul_one]
      · change φ ((v φ) • AMSpaceWithUnit.unit) = v φ
        have h1 : φ ((v φ) • (AMSpaceWithUnit.unit : X)) =
            (v φ) * φ (AMSpaceWithUnit.unit : X) := map_smul φ.toVecLatHom _ _
        rw [h1, φ.map_unit_apply, mul_one]
    · have hex : ∃ x : X, φ x ≠ ψ x := by
        by_contra h
        push Not at h
        apply hφψ
        exact DFunLike.ext _ _ h
      obtain ⟨x, hx⟩ := hex
      set d := φ x - ψ x with hd_def
      have hd_ne : d ≠ 0 := sub_ne_zero.mpr hx
      set α := (v φ - v ψ) / d with hα_def
      set β := v φ - α * φ x with hβ_def
      refine ⟨gelfand (α • x + β • AMSpaceWithUnit.unit),
        ⟨α • x + β • AMSpaceWithUnit.unit, rfl⟩, ?_, ?_⟩
      · change φ (α • x + β • AMSpaceWithUnit.unit) = v φ
        have h1 : φ (α • x + β • (AMSpaceWithUnit.unit : X)) =
            α * φ x + β * φ (AMSpaceWithUnit.unit : X) := by
          rw [show φ (α • x + β • (AMSpaceWithUnit.unit : X)) =
            φ (α • x) + φ (β • AMSpaceWithUnit.unit) from map_add φ.toVecLatHom _ _]
          rw [show φ (α • x) = α * φ x from map_smul φ.toVecLatHom _ _]
          rw [show φ (β • (AMSpaceWithUnit.unit : X)) =
            β * φ (AMSpaceWithUnit.unit : X) from map_smul φ.toVecLatHom _ _]
        rw [h1, φ.map_unit_apply, mul_one, hβ_def]
        ring
      · change ψ (α • x + β • AMSpaceWithUnit.unit) = v ψ
        have h1 : ψ (α • x + β • (AMSpaceWithUnit.unit : X)) =
            α * ψ x + β * ψ (AMSpaceWithUnit.unit : X) := by
          rw [show ψ (α • x + β • (AMSpaceWithUnit.unit : X)) =
            ψ (α • x) + ψ (β • AMSpaceWithUnit.unit) from map_add ψ.toVecLatHom _ _]
          rw [show ψ (α • x) = α * ψ x from map_smul ψ.toVecLatHom _ _]
          rw [show ψ (β • (AMSpaceWithUnit.unit : X)) =
            β * ψ (AMSpaceWithUnit.unit : X) from map_smul ψ.toVecLatHom _ _]
        rw [h1, ψ.map_unit_apply, mul_one]
        have key : α * (φ x - ψ x) = v φ - v ψ := by
          rw [hα_def, ← hd_def]
          field_simp
        rw [hβ_def]
        linarith [key]
  have hL_closure : closure L = Set.univ :=
    ContinuousMap.sublattice_closure_eq_top L hL_ne hL_inf hL_sup hL_sep
  have hL_closed : IsClosed L := (gelfand_isometry (X := X)).isClosedEmbedding.isClosed_range
  rw [hL_closed.closure_eq] at hL_closure
  intro f
  exact (Set.eq_univ_iff_forall.mp hL_closure f)

variable (X)

/-- The Gelfand transform as a real-linear map. -/
noncomputable def gelfandLinear :
    X →ₗ[ℝ] C(LatticeCharacter X, ℝ) where
  toFun := gelfand
  map_add' := gelfand_isVecLatHom.map_add
  map_smul' := gelfand_isVecLatHom.map_smul

/-- The Gelfand transform as a real-linear isometry. -/
noncomputable def gelfandLinearIsometry [Nontrivial X] :
    X →ₗᵢ[ℝ] C(LatticeCharacter X, ℝ) where
  toLinearMap := gelfandLinear (X := X)
  norm_map' := norm_gelfand

/-- **Kakutani's representation theorem** for non-trivial AM-spaces with unit. -/
noncomputable def kakutaniEquiv [Nontrivial X] :
    BanachLatEquiv X C(LatticeCharacter X, ℝ) where
  toLinearIsometryEquiv :=
    LinearIsometryEquiv.ofSurjective (gelfandLinearIsometry (X := X))
      (gelfand_surjective (X := X))
  map_sup' := fun a b => gelfand_isVecLatHom.map_sup' a b
  map_inf' := fun a b => gelfand_isVecLatHom.map_inf' a b

@[simp] theorem kakutaniEquiv_apply [Nontrivial X] (x : X) (φ : LatticeCharacter X) :
    kakutaniEquiv X x φ = φ x := by
  rfl

/-- Under the Kakutani isomorphism, the unit corresponds to the constant
function `1`. -/
theorem kakutaniEquiv_unit [Nontrivial X] :
    kakutaniEquiv X (AMSpaceWithUnit.unit : X) = 1 := by
  ext φ
  rw [kakutaniEquiv_apply]
  exact φ.map_unit

end AMSpaceWithUnit

namespace OrderIdeal

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- In a uniformly complete vector lattice, every nonzero positive principal
ideal, equipped with its gauge norm and inherited vector lattice structure, is
lattice isometric to continuous functions on a compact space. -/
noncomputable def principalKakutaniEquiv
    [IsUniformlyCompleteVectorLattice X] {e : X} (he : 0 < e) :
    letI := principalNormedAddCommGroup e
    letI : Lattice ↥(principal e) := instLatticePrincipal e
    letI : IsOrderedAddMonoid ↥(principal e) := instIsOrderedAddMonoidPrincipal e
    letI : AMSpaceWithUnit ↥(principal e) :=
      principalAMSpaceWithUnit he.le
        (IsUniformlyCompleteVectorLattice.complete_principal e he)
    BanachLatEquiv ↥(principal e)
      C(AMSpaceWithUnit.LatticeCharacter ↥(principal e), ℝ) := by
  letI := principalNormedAddCommGroup e
  letI : Lattice ↥(principal e) := instLatticePrincipal e
  letI : IsOrderedAddMonoid ↥(principal e) := instIsOrderedAddMonoidPrincipal e
  letI : AMSpaceWithUnit ↥(principal e) :=
    principalAMSpaceWithUnit he.le
      (IsUniformlyCompleteVectorLattice.complete_principal e he)
  haveI : Nontrivial ↥(principal e) := by
    refine ⟨⟨0, ⟨e, self_mem_principal e⟩, ?_⟩⟩
    intro h
    exact (ne_of_gt he) (by simpa using (congrArg Subtype.val h).symm)
  exact AMSpaceWithUnit.kakutaniEquiv ↥(principal e)

end OrderIdeal
