/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import LeanPool.RoyStrongSix.Roy.Support
public import LeanPool.RoyStrongSix.Roy.Theorem1

/-!
# Counting inequivalent points

Let `η₁, …, η_ℓ` span `Y` over `ℚ`, let `s : E → E'` be `ℂ`-linear, and put `Y' = s(Y)`. With
`ρ' = dim Y' − dim (Y' ∩ Ω')`, we find indices `idx : Fin ρ' → Fin ℓ` such that the
`s(η_{idx k})` are `ℚ`-linearly independent modulo `Ω'` (`exists_indep_mod_Omega`).

Consequently the grid points `Σ_k a_k η_{idx k}` (`a ∈ ℕ^{ρ'}`) have pairwise differences outside
`s⁻¹(Ω')` (`eq_of_sub_mem_Omega`). By `sMap_sub_mem_Omega` they are then pairwise inequivalent
modulo the obstruction subgroup. This is the lower bound `card((Σ + H)/H) ≥ (S+1)^{ρ'}`.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

namespace StrongSix.Thm1

open StrongSix.Roy

variable {d0 d1 k0 k1 ℓ : ℕ}

/-- **Independent generators modulo `Ω'`.** -/
theorem exists_indep_mod_Omega (η : Fin ℓ → E d0 d1) (s : E d0 d1 →ₗ[ℂ] E k0 k1) :
    ∃ idx : Fin (finrank ℚ ((span ℚ (Set.range η)).map (s.restrictScalars ℚ)) -
        finrank ℚ ↥((span ℚ (Set.range η)).map (s.restrictScalars ℚ) ⊓ Omega k0 k1)) → Fin ℓ,
      ∀ c : Fin _ → ℚ, (∑ k, c k • s (η (idx k))) ∈ Omega k0 k1 → c = 0 := by
  classical
  set Ω := Omega k0 k1
  set Y' := (span ℚ (Set.range η)).map (s.restrictScalars ℚ) with hY'
  set π : E d0 d1 →ₗ[ℚ] E k0 k1 ⧸ Ω := Ω.mkQ ∘ₗ s.restrictScalars ℚ with hπ
  set t : Set (E k0 k1 ⧸ Ω) := Set.range (π ∘ η) with ht
  -- `dim span t = ρ'`
  have hspan_t : span ℚ t = Y'.map Ω.mkQ := by
    rw [ht, Set.range_comp, ← Submodule.map_span, hπ, Submodule.map_comp, hY']
  have hY'eq : Y' = span ℚ (Set.range fun j => s (η j)) := by
    rw [hY', Submodule.map_span, ← Set.range_comp]; rfl
  have : FiniteDimensional ℚ Y' := by
    rw [hY'eq]; exact FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hdim : finrank ℚ (span ℚ t) = finrank ℚ Y' - finrank ℚ ↥(Y' ⊓ Ω) := by
    have := finrank_map_add_inf_ker Ω.mkQ Y'
    rw [Submodule.ker_mkQ] at this
    rw [hspan_t]; omega
  obtain ⟨b, hbt, hbspan, hli⟩ := exists_linearIndependent ℚ t
  let _ : Fintype b := ((Set.finite_range _).subset hbt).fintype
  have hcard : Fintype.card b = finrank ℚ Y' - finrank ℚ ↥(Y' ⊓ Ω) := by
    rw [← hdim, ← hbspan, ← finrank_span_eq_card hli, Subtype.range_coe]
  let e : Fin (finrank ℚ Y' - finrank ℚ ↥(Y' ⊓ Ω)) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ x : b, ∃ j, π (η j) = x := fun x => by
    obtain ⟨j, hj⟩ := hbt x.2
    exact ⟨j, hj⟩
  choose f hf using hpre
  refine ⟨fun k => f (e k), fun c hc => ?_⟩
  have h0 : ∑ k, c k • ((e k : b) : E k0 k1 ⧸ Ω) = 0 := by
    have : Ω.mkQ (∑ k, c k • s (η (f (e k)))) = 0 := (Submodule.Quotient.mk_eq_zero Ω).mpr hc
    rw [map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hf (e k)]
    rfl
  have hli' : LinearIndependent ℚ fun k => ((e k : b) : E k0 k1 ⧸ Ω) := hli.comp e e.injective
  funext k
  exact (Fintype.linearIndependent_iff.mp hli') c h0 k

/-- **Grid points are pairwise inequivalent.** If the `s(η_{idx k})` are independent modulo `Ω'`,
two natural coefficient vectors whose points differ by an element of `s⁻¹(Ω')` are equal. -/
theorem eq_of_sub_mem_Omega {ρ : ℕ} (η : Fin ℓ → E d0 d1) (s : E d0 d1 →ₗ[ℂ] E k0 k1)
    (idx : Fin ρ → Fin ℓ)
    (hidx : ∀ c : Fin ρ → ℚ, (∑ k, c k • s (η (idx k))) ∈ Omega k0 k1 → c = 0)
    (a b : Fin ρ → ℕ)
    (h : s ((∑ k, (a k : ℂ) • η (idx k)) - ∑ k, (b k : ℂ) • η (idx k)) ∈ Omega k0 k1) :
    a = b := by
  have hc : (∑ k, ((a k : ℚ) - b k) • s (η (idx k))) ∈ Omega k0 k1 := by
    convert h using 1
    rw [map_sub, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, ← sub_smul, ← Rat.cast_smul_eq_qsmul ℂ]
    push_cast; rfl
  have := hidx _ hc
  funext k
  have hk := congrFun this k
  simp only [Pi.zero_apply, sub_eq_zero] at hk
  exact_mod_cast hk

end StrongSix.Thm1

end LeanPool
