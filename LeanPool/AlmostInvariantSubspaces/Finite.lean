/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Length
public import Mathlib.Algebra.Order.Group.End

/-!
# The theorem

`G` is a finite group that acts on a module `M` by linear automorphisms, and `A` is a submodule
such that
`A / (A ∩ gA)` has length at most `r` for each `g`. Then there is an invariant submodule `W` with
`length (A / (A ∩ W)) + length (W / (A ∩ W)) ≤ 2 r (1 - 1/|G|)`.
-/

@[expose] public section

open Submodule Finset

namespace AlmostInvariant

variable {R M G : Type*} [Ring R] [AddCommGroup M] [Module R M] [Group G]

/-- The image of a submodule under a group element. The group acts by automorphisms of the lattice
of submodules; a linear or
semilinear action on the module gives such an action. -/
def act (ρ : G →* (Submodule R M ≃o Submodule R M)) (g : G) (S : Submodule R M)
    : Submodule R M := ρ g S

variable (ρ : G →* (Submodule R M ≃o Submodule R M))

theorem act_one (S : Submodule R M) : act ρ 1 S = S := by
  simp [act]

theorem act_mul (g h : G) (S : Submodule R M) : act ρ (g * h) S = act ρ g (act ρ h S) := by
  simp [act]

theorem act_mono (g : G) {S T : Submodule R M} (h : S ≤ T) : act ρ g S ≤ act ρ g T := (ρ
    g).monotone h

theorem delta_act (g : G) (S T : Submodule R M) : delta (act ρ g S) (act ρ g T)
    = delta S T := delta_map _ _ _

theorem d_act (g : G) (S T : Submodule R M) : d (act ρ g S) (act ρ g T) = d S T := d_map _ _ _

variable [Fintype G]

/-- The sum of the distances from `S` to the translates of `A`. -/
noncomputable def cost (A S : Submodule R M) : ℕ∞ := ∑ g : G, delta (act ρ g A) S

theorem cost_act (A S : Submodule R M) (h : G) : cost ρ A (act ρ h S) = cost ρ A S := by
  unfold cost
  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Equiv.coe_mulLeft, act_mul, delta_act]

theorem cost_submodular (A S T : Submodule R M) :
    cost ρ A (S ⊓ T) + cost ρ A (S ⊔ T) ≤ cost ρ A S + cost ρ A T := by
  unfold cost
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun g _ => delta_submodular _ S T

theorem delta_le_cost (A S : Submodule R M) : delta A S ≤ cost ρ A S := by
  unfold cost
  have := Finset.single_le_sum (f := fun g : G => delta (act ρ g A) S) (fun _ _ => bot_le)
      (Finset.mem_univ 1)
  simpa [act_one] using this

/-- **Main theorem.** A submodule whose translates are at finite distance from it is close to an
invariant submodule: the distance is
at most the mean of the distances to its translates. -/
theorem exists_invariant (A : Submodule R M) (hA : cost ρ A A ≠ ⊤) :
    ∃ W : Submodule R M, (∀ g, act ρ g W = W) ∧ (Fintype.card G : ℕ∞) * delta A W ≤ cost ρ A A := by
  classical
  -- a minimizer of the cost
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, ∀ S, cost ρ A S₀ ≤ cost ρ A S := by
    obtain ⟨y, ⟨S₀, rfl⟩, hy⟩ := WellFounded.has_min (wellFounded_lt (α := ℕ∞))
        (Set.range (cost ρ A)) ⟨_, A, rfl⟩
    exact ⟨S₀, fun S => not_lt.mp (hy _ ⟨S, rfl⟩)⟩
  set m := cost ρ A S₀ with hm
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top hA (hS₀ A)
  -- for a minimizer the two parts of the distance to `A` are finite, and at most `m`
  have fin1 : ∀ S, cost ρ A S = m → d A S ≤ m := fun S hS =>
    (le_self_add.trans (delta_le_cost ρ A S)).trans hS.le
  have fin2 : ∀ S, cost ρ A S = m → d S A ≤ m := fun S hS =>
    (le_add_self.trans (delta_le_cost ρ A S)).trans hS.le
  -- minimizers are closed under intersections
  have hinf : ∀ S T, cost ρ A S = m → cost ρ A T = m → cost ρ A (S ⊓ T) = m := by
    intro S T hS hT
    refine le_antisymm ?_ (hS₀ _)
    have h := cost_submodular ρ A S T
    rw [hS, hT] at h
    have h' : cost ρ A (S ⊓ T) + m ≤ m + m := (add_le_add le_rfl (hS₀ (S ⊔ T))).trans h
    exact (WithTop.add_le_add_iff_right hmtop).mp h'
  -- a least minimizer
  let p : Submodule R M → ℕ := fun S => (m.toNat - (d A S).toNat) + (d S A).toNat
  obtain ⟨W, hWm, hWp⟩ : ∃ W, cost ρ A W = m ∧ ∀ S, cost ρ A S = m → p W ≤ p S := by
    obtain ⟨y, ⟨W, hW, rfl⟩, hy⟩ := WellFounded.has_min (wellFounded_lt (α := ℕ))
      (p '' {S | cost ρ A S = m}) ⟨_, S₀, rfl, rfl⟩
    exact ⟨W, hW, fun S hS => not_lt.mp (hy _ ⟨S, hS, rfl⟩)⟩
  have hleast : ∀ S, cost ρ A S = m → W ≤ S := by
    intro S hS
    have hI := hinf W S hWm hS
    have hp := hWp _ hI
    have a1 : d A W ≤ d A (W ⊓ S) := d_anti_right inf_le_left
    have b1 : d (W ⊓ S) A ≤ d W A := d_mono_left inf_le_left
    have tA : d A W ≠ ⊤ := ne_top_of_le_ne_top hmtop (fin1 _ hWm)
    have tI : d A (W ⊓ S) ≠ ⊤ := ne_top_of_le_ne_top hmtop (fin1 _ hI)
    have tW : d W A ≠ ⊤ := ne_top_of_le_ne_top hmtop (fin2 _ hWm)
    have tJ : d (W ⊓ S) A ≠ ⊤ := ne_top_of_le_ne_top hmtop (fin2 _ hI)
    have n1 : (d A W).toNat ≤ (d A (W ⊓ S)).toNat := ENat.toNat_le_toNat a1 tI
    have n2 : (d (W ⊓ S) A).toNat ≤ (d W A).toNat := ENat.toNat_le_toNat b1 tW
    have n3 : (d A (W ⊓ S)).toNat ≤ m.toNat := ENat.toNat_le_toNat (fin1 _ hI) hmtop
    simp only [p] at hp
    have e1 : (d A W).toNat = (d A (W ⊓ S)).toNat := by omega
    have e2 : (d (W ⊓ S) A).toNat = (d W A).toNat := by omega
    have e1' : d A W = d A (W ⊓ S) := by
      rw [← ENat.natCast_toNat tA, ← ENat.natCast_toNat tI, e1]
    have e2' : d (W ⊓ S) A = d W A := by
      rw [← ENat.natCast_toNat tJ, ← ENat.natCast_toNat tW, e2]
    have := eq_of_d_eq (S := W) (S' := W ⊓ S) (U := A) inf_le_left e1' e2' tA tW
    rw [← this]
    exact inf_le_right
  -- it is invariant
  have hinv : ∀ g, act ρ g W = W := by
    have hle : ∀ g, W ≤ act ρ g W := fun g => hleast _ ((cost_act ρ A W g).trans hWm)
    intro g
    refine le_antisymm ?_ (hle g)
    have h := act_mono ρ g (hle g⁻¹)
    rwa [← act_mul, mul_inv_cancel, act_one] at h
  refine ⟨W, hinv, ?_⟩
  have hc : cost ρ A W = (Fintype.card G : ℕ∞) * delta A W := by
    unfold cost
    rw [Finset.sum_congr rfl (fun g _ => ?_), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nth_rewrite 1 [← hinv g]
    exact delta_act ρ g A W
  rw [← hc, hWm]
  exact hS₀ A

/-- The form with the bound `r`: the total distance is at most `2 r (1 - 1/|G|)`. -/
theorem exists_invariant_of_le (A : Submodule R M) (r : ℕ) (hr : ∀ g, d A (act ρ g A) ≤ r) :
    ∃ W : Submodule R M, (∀ g, act ρ g W = W) ∧
      (Fintype.card G : ℕ∞) * (d A W + d W A) ≤ 2 * r * (Fintype.card G - 1 : ℕ) := by
  classical
  have h1 : ∀ g, delta (act ρ g A) A ≤ 2 * r := by
    intro g
    have e : d (act ρ g A) A = d A (act ρ g⁻¹ A) := by
      rw [← d_act ρ g⁻¹ (act ρ g A) A, ← act_mul, inv_mul_cancel, act_one]
    rw [delta, e, two_mul]
    exact add_le_add (hr _) (hr _)
  have h2 : cost ρ A A ≤ 2 * r * (Fintype.card G - 1 : ℕ) := by
    unfold cost
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)), act_one]
    have z : delta A A = 0 := by simp [delta, d_eq_zero]
    rw [z, zero_add]
    calc ∑ g ∈ Finset.univ.erase (1 : G), delta (act ρ g A) A
        ≤ ∑ _g ∈ Finset.univ.erase (1 : G), (2 * r : ℕ∞) := Finset.sum_le_sum fun g _ => h1 g
      _ = 2 * r * (Fintype.card G - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            nsmul_eq_mul, mul_comm]
  have hfinite : (2 * r * (Fintype.card G - 1) : ℕ∞) ≠ ⊤ := by
    exact_mod_cast ENat.natCast_ne_top (2 * r * (Fintype.card G - 1))
  obtain ⟨W, hW, hd⟩ := exists_invariant ρ A (ne_top_of_le_ne_top hfinite h2)
  exact ⟨W, hW, hd.trans h2⟩

end AlmostInvariant
