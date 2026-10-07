/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A uniform bound at each fixed derivative order

On a compact set where every multi-index derivative is continuous, all derivatives of one
fixed order `k` are bounded by a single constant, because there are finitely many multi-indices
of order `k`. This starts the induction on the derivative order in the proof of
`thm:analytic:interior`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section



namespace CIV

/-- The multi-indices of a fixed order form a finite set. -/
theorem finite_setOf_multiIndex_order (k : ℕ) :
    {γ : Fin 3 → ℕ | γ 0 + γ 1 + γ 2 = k}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin 3 => Set.Iic k) fun _ => Set.finite_Iic k).subset ?_
  intro γ hγ
  simp only [Set.mem_ofPred_eq] at hγ
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, forall_const]
  intro i
  fin_cases i <;> simp <;> omega

/-- On a compact set where every multi-index derivative is continuous, the derivatives of one
fixed order are bounded by one constant. -/
theorem exists_bound_multiPartial_of_continuousOn {g : ParabolicPoint → ℝ}
    {Kc : Set (Vec3 × ℝ)} (hK : IsCompact Kc)
    (hcont : ∀ γ : Fin 3 → ℕ, ContinuousOn (fun z : Vec3 × ℝ => multiPartial g γ z) Kc)
    (k : ℕ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ z ∈ Kc, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k →
      |multiPartial g γ z| ≤ N := by
  have hb : ∀ γ : Fin 3 → ℕ, ∃ C : ℝ, ∀ z ∈ Kc, ‖multiPartial g γ z‖ ≤ C :=
    fun γ => hK.exists_bound_of_continuousOn (hcont γ)
  choose C hC using hb
  set T := (finite_setOf_multiIndex_order k).toFinset
  refine ⟨∑ γ ∈ T, max (C γ) 0, Finset.sum_nonneg fun γ _ => le_max_right _ _, ?_⟩
  intro z hz γ hγ
  have hmem : γ ∈ T := (Set.Finite.mem_toFinset _).2 hγ
  have h1 : |multiPartial g γ z| ≤ C γ := by
    simpa [Real.norm_eq_abs] using hC γ z hz
  have h2 : max (C γ) 0 ≤ ∑ γ' ∈ T, max (C γ') 0 :=
    Finset.single_le_sum (f := fun γ' => max (C γ') 0) (fun γ' _ => le_max_right _ _) hmem
  exact h1.trans ((le_max_left _ _).trans h2)

end CIV
