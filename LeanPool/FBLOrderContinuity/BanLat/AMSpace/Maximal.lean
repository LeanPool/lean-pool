/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.AMSpace.Basic
public import Mathlib.Order.Zorn



/-!
# Maximal ideals in AM-spaces with unit

This file proves that every proper order ideal in an AM-space with unit is
contained in a maximal proper order ideal.
-/

@[expose] public section

namespace AMSpaceWithUnit

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [AMSpaceWithUnit X]

/-- An ideal in an AM-space with unit is the whole space iff it contains the
distinguished unit. -/
theorem top_iff_unit_mem (I : OrderIdeal X) :
    I = ⊤ ↔ (AMSpaceWithUnit.unit : X) ∈ I := by
  constructor
  · intro h
    rw [h]
    exact OrderIdeal.mem_top
  · intro hunit
    have hprincipal_le : OrderIdeal.principal (AMSpaceWithUnit.unit : X) ≤ I := by
      intro x hx
      rw [OrderIdeal.mem_principal] at hx
      obtain ⟨c, hc, hxle⟩ := hx
      have hcunit : c • (AMSpaceWithUnit.unit : X) ∈ I :=
        I.toSubmodule.smul_mem c hunit
      have hxle' : |x| ≤ c • (AMSpaceWithUnit.unit : X) := by
        simpa [abs_of_nonneg (unit_nonneg (X := X))] using hxle
      exact I.mem_of_abs_mem (I.solid hcunit (abs_nonneg x) hxle')
    exact le_antisymm le_top (by
      rw [← principal_unit_eq_top (X := X)]
      exact hprincipal_le)

private theorem directedOn_toSubmodule_of_chain {c : Set (OrderIdeal X)}
    (hchain : IsChain (· ≤ ·) c) :
    DirectedOn (· ≤ ·) ((fun J : OrderIdeal X => J.toSubmodule) '' c) := by
  rintro _ ⟨J₁, hJ₁, rfl⟩ _ ⟨J₂, hJ₂, rfl⟩
  by_cases heq : J₁ = J₂
  · exact ⟨J₁.toSubmodule, ⟨J₁, hJ₁, rfl⟩, le_refl _, heq ▸ le_refl _⟩
  · rcases hchain hJ₁ hJ₂ heq with h | h
    · exact ⟨J₂.toSubmodule, ⟨J₂, hJ₂, rfl⟩, fun _ hx => h hx, le_refl _⟩
    · exact ⟨J₁.toSubmodule, ⟨J₁, hJ₁, rfl⟩, le_refl _, fun _ hx => h hx⟩

/-- **Every proper order ideal is contained in a maximal proper order ideal.**
This is the usual Zorn lemma argument applied to the poset of proper order
ideals containing the given ideal. -/
theorem exists_le_maximal (I : OrderIdeal X) (hI : I ≠ ⊤) :
    ∃ M : OrderIdeal X, I ≤ M ∧ M ≠ ⊤ ∧
      ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M := by
  classical
  set S : Set (OrderIdeal X) := {J | I ≤ J ∧ J ≠ ⊤} with hS_def
  have hIS : I ∈ S := ⟨le_refl _, hI⟩
  have hzorn : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hchain y hyc
    set SM : Set (Submodule ℝ X) :=
      (fun J : OrderIdeal X => J.toSubmodule) '' c with hSM_def
    have hSMne : SM.Nonempty := ⟨y.toSubmodule, y, hyc, rfl⟩
    have hdir : DirectedOn (· ≤ ·) SM := directedOn_toSubmodule_of_chain hchain
    refine ⟨OrderIdeal.ofSolid (sSup SM) ?_, ⟨?_, ?_⟩, ?_⟩
    · intro x w hx hxw
      rw [Submodule.mem_sSup_of_directed hSMne hdir] at hx
      obtain ⟨_, ⟨J, hJ, rfl⟩, hxJ⟩ := hx
      rw [Submodule.mem_sSup_of_directed hSMne hdir]
      exact ⟨J.toSubmodule, ⟨J, hJ, rfl⟩, J.mem_of_abs_le_abs hxJ hxw⟩
    · change I.toSubmodule ≤ sSup SM
      exact le_trans (fun _ hx => (hcS hyc).1 hx) (le_sSup ⟨y, hyc, rfl⟩)
    · intro hU_top
      have hmem : (AMSpaceWithUnit.unit : X) ∈ sSup SM := by
        have : (AMSpaceWithUnit.unit : X) ∈ (⊤ : OrderIdeal X) := OrderIdeal.mem_top
        rw [← hU_top] at this
        exact this
      rw [Submodule.mem_sSup_of_directed hSMne hdir] at hmem
      obtain ⟨_, ⟨J, hJ, rfl⟩, heJ⟩ := hmem
      exact (hcS hJ).2 ((top_iff_unit_mem J).mpr heJ)
    · intro J hJ
      change J.toSubmodule ≤ sSup SM
      exact le_sSup ⟨J, hJ, rfl⟩
  obtain ⟨M, hIM, hMax⟩ := zorn_le_nonempty₀ S hzorn I hIS
  refine ⟨M, hIM, hMax.prop.2, ?_⟩
  intro J hMJ hJne
  have hJS : J ∈ S := ⟨le_trans hIM hMJ, hJne⟩
  exact hMax.eq_of_ge hJS hMJ

end AMSpaceWithUnit
