/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Order.ModularLattice
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Almost invariant subspaces for finite groups

D. Kazhdan and A. Polishchuk (Almost invariant subspaces and operators, arXiv 2107.08085, Pure
Appl. Math. Q. 19 (2023))
proved: if `dim A / (A ∩ gA) ≤ r` for all `g` then there is an invariant subspace `W` with `dim W
/ (W ∩ A) ≤ r` and
`dim A / (W ∩ A) ≤ r (r+1)^(r+1)`, and conjectured that the last bound can be replaced by a
polynomial, possibly linear,
function of `r`, at least for finite groups.

Here, for finite `G`, every field and every subspace:
* `almost_invariant_subspace`: there is an invariant `W` with `dim W / (W ∩ A) + dim A / (W ∩ A) ≤
  2r` (`< 2r` if `r > 0`);
* `almost_invariant_subspace_one_sided`: there is an invariant `W` with `dim W / (W ∩ A) ≤ r` and
  `dim A / (W ∩ A) ≤ r (r+1)`.

Proof: for weights `α, β` the function `f s = ∑ g, (α dim (gA / (gA ∩ s)) + β dim (s / (gA ∩ s)))`
is submodular, so its
minimizers are closed under intersection; the smallest minimizer is unique, hence invariant.
-/

@[expose] public section

namespace AlmostInvariant.OneSided

/-- Lattice form. A finite group acts by order automorphisms on a lattice with a strictly
monotone, modular, invariant integer
rank function. For every `u` and all weights `α ≥ 1`, `β ≥ 0` there is a fixed element `w` with
`|G| (α rk(u / u ⊓ w) + β rk(w / u ⊓ w)) ≤ (α + β) ∑ g, rk(u / gu ⊓ u)`. -/
theorem lattice_form {L G : Type*} [Lattice L] [Group G] [Fintype G]
    (act : G → L ≃o L) (hmul : ∀ g h a, act (g * h) a = act g (act h a))
    (rk : L → ℤ) (hstrict : StrictMono rk)
    (hmod : ∀ a b, rk (a ⊔ b) + rk (a ⊓ b) = rk a + rk b)
    (hinv : ∀ g a, rk (act g a) = rk a) (u : L) (α β : ℤ) (hα : 1 ≤ α) (hβ : 0 ≤ β) :
    ∃ w, (∀ g, act g w = w) ∧
      (Fintype.card G : ℤ) * (α * (rk u - rk (w ⊓ u)) + β * (rk w - rk (w ⊓ u))) ≤
        (α + β) * ∑ g, (rk u - rk (act g u ⊓ u)) := by
  classical
  have hmono : Monotone rk := hstrict.monotone
  set f : L → ℤ := fun s => ∑ g, (α * (rk (act g u) - rk (act g u ⊓ s)) + β * (rk s - rk (act g u
      ⊓ s)))
    with hf
  have hA : ∀ a s : L, 0 ≤ rk a - rk (a ⊓ s) := fun a s => sub_nonneg.mpr (hmono inf_le_left)
  have hB : ∀ a s : L, 0 ≤ rk s - rk (a ⊓ s) := fun a s => sub_nonneg.mpr (hmono inf_le_right)
  have hterm : ∀ a s : L, 0 ≤ α * (rk a - rk (a ⊓ s)) + β * (rk s - rk (a ⊓ s)) := fun a s =>
    add_nonneg (mul_nonneg (by linarith) (hA a s)) (mul_nonneg hβ (hB a s))
  have hnn : ∀ s, 0 ≤ f s := fun s => Finset.sum_nonneg fun g _ => hterm _ _
  have hsub : ∀ s t, f (s ⊓ t) + f (s ⊔ t) ≤ f s + f t := by
    intro s t
    simp only [hf]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun g _ => ?_
    set a := act g u
    have h1 := hmod (a ⊓ s) (a ⊓ t)
    have h2 : rk ((a ⊓ s) ⊔ (a ⊓ t)) ≤ rk (a ⊓ (s ⊔ t)) :=
      hmono (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
    have h3 : rk ((a ⊓ s) ⊓ (a ⊓ t)) ≤ rk (a ⊓ (s ⊓ t)) :=
      hmono (le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
    have h4 := hmod s t
    have h5 : rk (a ⊓ s) + rk (a ⊓ t) ≤ rk (a ⊓ (s ⊔ t)) + rk (a ⊓ (s ⊓ t)) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (show 0 ≤ α + β by linarith)
    have h7 : β * rk (s ⊔ t) + β * rk (s ⊓ t) = β * rk s + β * rk t := by
      rw [← mul_add, h4, mul_add]
    linarith
  have hfinv : ∀ h s, f (act h s) = f s := by
    intro h s
    simp only [hf]
    symm
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    have e1 : act (h * g) u = act h (act g u) := hmul h g u
    simp only [Equiv.coe_mulLeft]
    rw [e1, ← (act h).map_inf, hinv h (act g u), hinv h s, hinv h (act g u ⊓ s)]
  have hex : ∃ n : ℕ, ∃ s, f s = n := ⟨(f u).toNat, u, (Int.toNat_of_nonneg (hnn u)).symm⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  set n0 := Nat.find hex with hn0
  have hmin : ∀ s, (n0 : ℤ) ≤ f s := by
    intro s
    have h := Nat.find_min' hex ⟨s, (Int.toNat_of_nonneg (hnn s)).symm⟩
    have h' : (n0 : ℤ) ≤ ((f s).toNat : ℤ) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg (hnn s)] at h'
  have hone : ∀ a, act 1 a = a := by
    intro a
    apply (act 1).injective
    rw [← hmul, one_mul]
  -- the rank of a minimizer is bounded below
  have hlow : ∀ s, f s = n0 → rk u - n0 ≤ rk s := by
    intro s hs
    have h1 : α * (rk (act 1 u) - rk (act 1 u ⊓ s)) + β * (rk s - rk (act 1 u ⊓ s)) ≤ f s :=
      Finset.single_le_sum
        (f := fun g => α * (rk (act g u) - rk (act g u ⊓ s)) + β * (rk s - rk (act g u ⊓ s)))
        (fun g _ => hterm _ _) (Finset.mem_univ 1)
    rw [hone] at h1
    have h2 : rk (u ⊓ s) ≤ rk s := hmono inf_le_right
    have h3 : 1 * (rk u - rk (u ⊓ s)) ≤ α * (rk u - rk (u ⊓ s)) :=
      mul_le_mul_of_nonneg_right hα (hA u s)
    have h4 := mul_nonneg hβ (hB u s)
    linarith
  have hex2 : ∃ k : ℕ, ∃ s, f s = n0 ∧ rk s = rk u - n0 + k :=
    ⟨(rk s0 - (rk u - n0)).toNat, s0, hs0, by
      rw [Int.toNat_of_nonneg (by linarith [hlow s0 hs0])]; ring⟩
  obtain ⟨w, hw, hwk⟩ := Nat.find_spec hex2
  have hwmin : ∀ t, f t = n0 → rk w ≤ rk t := by
    intro t ht
    have h := Nat.find_min' hex2 (m := (rk t - (rk u - n0)).toNat) ⟨t, ht, by
      rw [Int.toNat_of_nonneg (by linarith [hlow t ht])]; ring⟩
    have h' : ((Nat.find hex2 : ℕ) : ℤ) ≤ (((rk t - (rk u - n0)).toNat : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [Int.toNat_of_nonneg (by linarith [hlow t ht])] at h'
    linarith
  have hle : ∀ t, f t = n0 → w ≤ t := by
    intro t ht
    have h1 := hsub w t
    have h2 := hmin (w ⊔ t)
    have h3 := hmin (w ⊓ t)
    have h4 : f (w ⊓ t) = n0 := by linarith
    have h5 := hwmin _ h4
    by_contra hcon
    have h6 : w ⊓ t < w := inf_lt_left.mpr hcon
    exact absurd (hstrict h6) (not_lt.mpr h5)
  have hfix : ∀ g, act g w = w := by
    intro g
    apply le_antisymm
    · have h1 : w ≤ act g⁻¹ w := hle _ (by rw [hfinv, hw])
      have h2 : act g w ≤ act g (act g⁻¹ w) := (act g).monotone h1
      rwa [← hmul, mul_inv_cancel, hone] at h2
    · exact hle _ (by rw [hfinv, hw])
  refine ⟨w, hfix, ?_⟩
  have e1 : f w = (Fintype.card G : ℤ) * (α * (rk u - rk (w ⊓ u)) + β * (rk w - rk (w ⊓ u))) := by
    have : ∀ g, α * (rk (act g u) - rk (act g u ⊓ w)) + β * (rk w - rk (act g u ⊓ w)) =
        α * (rk u - rk (w ⊓ u)) + β * (rk w - rk (w ⊓ u)) := by
      intro g
      have h1 : act g u ⊓ w = act g (u ⊓ w) := by rw [(act g).map_inf, hfix]
      rw [h1, hinv, hinv, inf_comm u w]
    simp only [hf, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e2 : f u = (α + β) * ∑ g, (rk u - rk (act g u ⊓ u)) := by
    simp only [hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hinv]; ring
  rw [← e1, ← e2, hw]
  exact hmin u

/-- The weighted bound with a uniform hypothesis. -/
theorem lattice_bound {L G : Type*} [Lattice L] [Group G] [Finite G]
    (act : G → L ≃o L) (hmul : ∀ g h a, act (g * h) a = act g (act h a))
    (rk : L → ℤ) (hstrict : StrictMono rk)
    (hmod : ∀ a b, rk (a ⊔ b) + rk (a ⊓ b) = rk a + rk b)
    (hinv : ∀ g a, rk (act g a) = rk a) (u : L) (r : ℤ)
    (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) (α β : ℤ) (hα : 1 ≤ α) (hβ : 0 ≤ β) :
    ∃ w, (∀ g, act g w = w) ∧
      α * (rk u - rk (w ⊓ u)) + β * (rk w - rk (w ⊓ u)) ≤ (α + β) * r ∧
      (0 < r → α * (rk u - rk (w ⊓ u)) + β * (rk w - rk (w ⊓ u)) < (α + β) * r) := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨w, hfix, hw⟩ := lattice_form act hmul rk hstrict hmod hinv u α β hα hβ
  have hone : ∀ a, act 1 a = a := by
    intro a
    apply (act 1).injective
    rw [← hmul, one_mul]
  have hcard : (0 : ℤ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ g, (rk u - rk (act g u ⊓ u)) ≤ ((Fintype.card G : ℤ) - 1) * r := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)), hone, inf_idem]
    have h1 : ∑ g ∈ Finset.univ.erase (1 : G), (rk u - rk (act g u ⊓ u)) ≤
        ∑ g ∈ Finset.univ.erase (1 : G), r :=
      Finset.sum_le_sum fun g _ => by linarith [hr g]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub Fintype.card_pos] at h1
    simpa using h1
  have hsum' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ α + β by linarith)
  have h0 : 0 ≤ r := by
    have := hr 1
    rw [hone, inf_idem] at this
    linarith
  set X := α * (rk u - rk (w ⊓ u)) + β * (rk w - rk (w ⊓ u)) with hX
  have hle : X ≤ (α + β) * r := by
    by_contra hcon
    have hcon' : (α + β) * r + 1 ≤ X := by linarith
    have h1 := mul_le_mul_of_nonneg_left hcon' hcard.le
    have h2 : 0 ≤ (α + β) * r := mul_nonneg (by linarith) h0
    nlinarith
  refine ⟨w, hfix, hle, fun hpos => ?_⟩
  by_contra hcon
  have hcon' : (α + β) * r ≤ X := not_lt.mp hcon
  have h1 := mul_le_mul_of_nonneg_left hcon' hcard.le
  have h2 : 0 < (α + β) * r := mul_pos (by linarith) hpos
  nlinarith

open Module

/-- The weighted bound for subspaces. `G` is a finite group, `V` a finite-dimensional
representation of `G` over a field `K`,
`A` a subspace with `dim A ≤ dim (gA ∩ A) + r` for all `g`. -/
theorem weighted {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] [Finite G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r)
    (α β : ℤ) (hα : 1 ≤ α) (hβ : 0 ≤ β) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      α * ((finrank K A : ℤ) - finrank K (W ⊓ A : Submodule K V)) +
        β * ((finrank K W : ℤ) - finrank K (W ⊓ A : Submodule K V)) ≤ (α + β) * r ∧
      (0 < r → α * ((finrank K A : ℤ) - finrank K (W ⊓ A : Submodule K V)) +
        β * ((finrank K W : ℤ) - finrank K (W ⊓ A : Submodule K V)) < (α + β) * r) := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨W, h1, h2, h3⟩ := lattice_bound (L := Submodule K V) (G := G)
    (fun g => Submodule.orderIsoMapComap (ρ g))
    (by
      intro g h a
      ext x
      simp only [Submodule.orderIsoMapComap_apply, Submodule.mem_map, map_mul]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨ρ h y, ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, rfl⟩)
    (fun S => (finrank K S : ℤ))
    (fun S T hST => by
      have h := Submodule.finrank_lt_finrank_of_lt hST
      change (finrank K S : ℤ) < finrank K T
      exact_mod_cast h)
    (fun S T => by
      have h := Submodule.finrank_sup_add_finrank_inf_eq S T
      change (finrank K (S ⊔ T : Submodule K V) : ℤ) + finrank K (S ⊓ T : Submodule K V) =
        finrank K S + finrank K T
      exact_mod_cast h)
    (fun g S => by
      have h := LinearEquiv.finrank_map_eq (ρ g) S
      change (finrank K (S.map (ρ g : V →ₗ[K] V)) : ℤ) = finrank K S
      exact_mod_cast h)
    A r
    (fun g => by
      have h' : (finrank K A : ℤ) ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V)
          + r := by
        exact_mod_cast hr g
      have h'' : (Submodule.orderIsoMapComap (ρ g)) A = A.map (ρ g : V →ₗ[K] V) := rfl
      rw [h'']
      linarith)
    α β hα hβ
  exact ⟨W, h1, h2, fun hpos => h3 (by exact_mod_cast hpos)⟩

/-- **Linear bound for the total error.** There is an invariant subspace `W` with
`dim W / (W ∩ A) + dim A / (W ∩ A) ≤ 2r`, strictly less if `r > 0`. -/
theorem almost_invariant_subspace {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] [Finite G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r ∧
      (0 < r → finrank K W + finrank K A < 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r) := by
  obtain ⟨W, h1, h2, h3⟩ := weighted ρ A r hr 1 1 le_rfl zero_le_one
  refine ⟨W, h1, ?_, fun hpos => ?_⟩
  · have : (finrank K W : ℤ) + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r := by
      linarith
    exact_mod_cast this
  · have h4 := h3 hpos
    have : (finrank K W : ℤ) + finrank K A < 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r := by
      linarith
    exact_mod_cast this

/-- **The one-sided form of Kazhdan and Polishchuk with a quadratic bound.** There is an invariant
subspace `W` with
`dim W / (W ∩ A) ≤ r` and `dim A / (W ∩ A) ≤ r (r + 1)`. -/
theorem almost_invariant_subspace_one_sided {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] [Finite G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1) := by
  rcases Nat.eq_zero_or_pos r with h | hpos
  · subst h
    obtain ⟨W, h1, h2, -⟩ := almost_invariant_subspace ρ A 0 hr
    have hA : finrank K (W ⊓ A : Submodule K V) ≤ finrank K A := Submodule.finrank_mono inf_le_right
    have hW : finrank K (W ⊓ A : Submodule K V) ≤ finrank K W := Submodule.finrank_mono inf_le_left
    exact ⟨W, h1, by omega, by omega⟩
  obtain ⟨W, h1, h2, h3⟩ := weighted ρ A r hr 1 r le_rfl (by positivity)
  have hA : (finrank K (W ⊓ A : Submodule K V) : ℤ) ≤ finrank K A := by
    exact_mod_cast Submodule.finrank_mono (inf_le_right : W ⊓ A ≤ A)
  have hW : (finrank K (W ⊓ A : Submodule K V) : ℤ) ≤ finrank K W := by
    exact_mod_cast Submodule.finrank_mono (inf_le_left : W ⊓ A ≤ W)
  set a : ℤ := (finrank K A : ℤ) - finrank K (W ⊓ A : Submodule K V) with ha
  set b : ℤ := (finrank K W : ℤ) - finrank K (W ⊓ A : Submodule K V) with hb
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hrb : 0 ≤ (r : ℤ) * b := mul_nonneg hr0 hb0
  have hbr : b ≤ r := by
    have h4 := h3 hpos
    by_contra hcon
    have h5 : (r : ℤ) + 1 ≤ b := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 hr0
    nlinarith
  refine ⟨W, h1, ?_, ?_⟩
  · have : (finrank K W : ℤ) ≤ finrank K (W ⊓ A : Submodule K V) + r := by linarith
    exact_mod_cast this
  · have : (finrank K A : ℤ) ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1) := by nlinarith
    exact_mod_cast this

end AlmostInvariant.OneSided
