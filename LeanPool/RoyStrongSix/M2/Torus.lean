/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import LeanPool.RoyStrongSix.CM.Unmixedness
public import LeanPool.RoyStrongSix.M2.Component
public import LeanPool.RoyStrongSix.M2.Geom

/-!
# The torus is irreducible

* `eq_zero_of_eval_coords`: a polynomial in `K[X, Y]` vanishing on `K^{d₀} × (K^×)^{d₁}` is zero
  (`K` infinite).
* `ψ : K[X, Y, Z] → K[X, Y][1/∏Y]`, `Z_j ↦ Y_j⁻¹`. Evaluation at `g ∈ G` factors through `ψ`
  (`ev_comp_ψ`), and `I(G) = ker ψ` (`vanish_univ_eq_ker`).
* **`vanish_univ_isPrime`**: `I(G)` is prime, because `K[X, Y][1/∏Y]` is a domain.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K
local notation "R0" => MvPolynomial (Var d0 d1) K

/-- `∏ Y_j ∈ K[X, Y]`. -/
noncomputable def yprod : MvPolynomial (Var d0 d1) K := ∏ j, X (Sum.inr j)

omit [CharZero K] in
theorem eval_yprod (g : GPt K d0 d1) : eval g.coords (yprod : R0) = ∏ j, ((g.2 j : Kˣ) : K) := by
  simp [yprod, GPt.coords]

omit [CharZero K] in
theorem yprod_ne_zero : (yprod : R0) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => X_ne_zero _

/-- **Zariski density of the torus.** -/
theorem eq_zero_of_eval_coords {a : R0} (h : ∀ g : GPt K d0 d1, eval g.coords a = 0) : a = 0 := by
  have : a * yprod = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : ∀ j, x (Sum.inr j) ≠ 0
    · let g : GPt K d0 d1 := (fun k => x (Sum.inl k), fun j => Units.mk0 _ (hx j))
      have hgx : g.coords = x := by funext v; rcases v with k | j <;> rfl
      rw [← hgx, h g, zero_mul]
    · push Not at hx
      obtain ⟨j, hj⟩ := hx
      have : eval x (yprod : R0) = 0 := by
        simp only [yprod, map_prod, eval_X]
        exact Finset.prod_eq_zero (Finset.mem_univ j) hj
      rw [this, mul_zero]
  exact (mul_eq_zero.mp this).resolve_right yprod_ne_zero

theorem exists_coords_ne_zero {a : R0} (ha : a ≠ 0) : ∃ g : GPt K d0 d1, eval g.coords a ≠ 0 := by
  by_contra h; push Not at h; exact ha (eq_zero_of_eval_coords h)

/-! ### The Laurent model -/

local notation "Loc" => Localization.Away (yprod : MvPolynomial (Var d0 d1) K)

/-- `Z_j ↦ Y_j⁻¹ = (∏_{k ≠ j} Y_k) / ∏ Y`. -/
noncomputable def ψv : V3 d0 d1 → Localization.Away (yprod : MvPolynomial (Var d0 d1) K) :=
  Sum.elim (fun k => algebraMap R0 Loc (X (Sum.inl k)))
    (Sum.elim (fun j => algebraMap R0 Loc (X (Sum.inr j)))
      (fun j => algebraMap R0 Loc (∏ k ∈ Finset.univ.erase j, X (Sum.inr k)) *
        IsLocalization.Away.invSelf (yprod : R0)))

/-- `ψ : K[X, Y, Z] → K[X, Y][1/∏Y]`. -/
noncomputable def ψ : B →+* Localization.Away (yprod : MvPolynomial (Var d0 d1) K) :=
  eval₂Hom ((algebraMap R0 Loc).comp C) ψv

omit [CharZero K] in
theorem isUnit_eval_yprod (g : GPt K d0 d1) : IsUnit (eval g.coords (yprod : R0)) := by
  rw [eval_yprod]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun j _ => (g.2 j).ne_zero)

/-- Evaluation at `g`, extended to the localization. -/
noncomputable def ev (g : GPt K d0 d1) : Localization.Away (yprod : MvPolynomial (Var d0 d1) K)
  →+* K :=
  IsLocalization.Away.lift (yprod : R0) (isUnit_eval_yprod g)

omit [CharZero K] in
theorem ev_algebraMap (g : GPt K d0 d1) (a : R0) : ev g (algebraMap R0 Loc a) = eval g.coords a :=
  IsLocalization.Away.lift_eq _ _ _

omit [CharZero K] in
theorem ev_invSelf (g : GPt K d0 d1) :
    ev g (IsLocalization.Away.invSelf (yprod : R0)) = (∏ j, ((g.2 j : Kˣ) : K))⁻¹ := by
  have h := congrArg (ev g) (IsLocalization.Away.mul_invSelf (S := Loc) (yprod : R0))
  rw [map_mul, ev_algebraMap, map_one, eval_yprod] at h
  exact eq_inv_of_mul_eq_one_right h

omit [CharZero K] in
theorem ev_comp_ψ (g : GPt K d0 d1) : (ev g).comp ψ = eval (pt g) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [ψ, ev_algebraMap]
  · intro v
    rcases v with k | j | j
    · simp [ψ, ψv, ev_algebraMap, pt, GPt.coords]
    · simp [ψ, ψv, ev_algebraMap, pt, GPt.coords]
    · simp only [ψ, ψv, RingHom.coe_comp, Function.comp_apply, coe_eval₂Hom, eval₂_X,
        Sum.elim_inr, map_mul, ev_algebraMap, ev_invSelf, map_prod, eval_X, eval_X, pt]
      simp only [GPt.coords, Sum.elim_inr, Units.val_inv_eq_inv_val]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => (g.2 k).ne_zero), one_mul]

theorem vanish_univ_eq_ker : vanish (Set.univ : Set (GPt K d0 d1)) = RingHom.ker ψ := by
  ext F
  constructor
  · intro hF
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (yprod : R0)) (ψ F)
    have ha : a = 0 := eq_zero_of_eval_coords fun g => by
      have := congrArg (ev g) hs
      simp only [map_mul, ev_algebraMap] at this
      rw [← RingHom.comp_apply (ev g) ψ, ev_comp_ψ, hF g (Set.mem_univ _), zero_mul] at this
      exact this.symm
    simp only [ha, map_zero] at hs
    have hu : IsUnit (algebraMap R0 Loc s) := IsLocalization.map_units Loc s
    exact RingHom.mem_ker.mpr (hu.mul_left_eq_zero.mp hs)
  · intro hF g _
    rw [← ev_comp_ψ g, RingHom.comp_apply, RingHom.mem_ker.mp hF, map_zero]

/-- **`I(G)` is prime.** -/
theorem vanish_univ_isPrime : (vanish (Set.univ : Set (GPt K d0 d1))).IsPrime := by
  rw [vanish_univ_eq_ker]
  have : IsDomain Loc :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors yprod_ne_zero)
  exact RingHom.ker_isPrime ψ

end StrongSix.M2

end LeanPool
