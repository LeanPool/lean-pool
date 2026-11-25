/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Action
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Modular ranks on lattices and finite-dimensional subspaces
-/

@[expose] public section

namespace KPFamLat

theorem act_one {G L : Type*} [Monoid G] [Preorder L] (act : G → L ≃o L)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (x : L) : act 1 x = x := by
  apply (act 1).injective
  rw [← hmul, one_mul]

/-- The rank of intersection with a fixed element is supermodular. -/
theorem inf_rank_supermodular {L : Type*} [Lattice L] (rk : L → ℤ) (monotone : Monotone rk)
    (modular : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y) (x y z : L) :
    rk (x ⊓ y) + rk (x ⊓ z) ≤ rk (x ⊓ (y ⊔ z)) + rk (x ⊓ (y ⊓ z)) := by
  have sup_le' : (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have inf_le' : (x ⊓ y) ⊓ (x ⊓ z) ≤ x ⊓ (y ⊓ z) :=
    le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  rw [← modular]
  exact add_le_add (monotone sup_le') (monotone inf_le')

end KPFamLat

namespace AlmostInvariant

open Module

section FiniteDimensional

variable {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem finrank_strictMono_int [FiniteDimensional K V] :
    StrictMono (fun S : Submodule K V => (finrank K S : ℤ)) :=
  fun S T h => by
    change (finrank K S : ℤ) < finrank K T
    exact_mod_cast Submodule.finrank_lt_finrank_of_lt h

theorem finrank_modular_int [FiniteDimensional K V] (S T : Submodule K V) :
    (finrank K (S ⊔ T : Submodule K V) : ℤ) + finrank K (S ⊓ T : Submodule K V) =
      finrank K S + finrank K T := by
  exact_mod_cast Submodule.finrank_sup_add_finrank_inf_eq S T

theorem finrank_linearAct_int [Monoid G] (ρ : G →* (V ≃ₗ[K] V)) (g : G) (S : Submodule K V) :
    (finrank K (linearAct ρ g S : Submodule K V) : ℤ) = finrank K S := by
  exact_mod_cast LinearEquiv.finrank_map_eq (ρ g) S

theorem finrank_orbit_sub_le [Monoid G] (ρ : G →* (V ≃ₗ[K] V)) (g : G)
    (S : Submodule K V) (r : ℕ)
    (bound : finrank K S ≤ finrank K (S.map (ρ g : V →ₗ[K] V) ⊓ S : Submodule K V) + r) :
    (finrank K S : ℤ) - finrank K (linearAct ρ g S ⊓ S : Submodule K V) ≤ r := by
  have cast_bound : (finrank K S : ℤ) ≤
      finrank K (S.map (ρ g : V →ₗ[K] V) ⊓ S : Submodule K V) + r := by exact_mod_cast bound
  rw [add_comm] at cast_bound
  exact sub_le_iff_le_add.mpr cast_bound

end FiniteDimensional

end AlmostInvariant
