/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalFunctionalDomination
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The positive order-normal cone is closed in the full dual norm

For a bounded positive directed set with supremum X, every member has norm
at most norm X. A single operator-norm approximation therefore controls all
its functional values at once. This retains arbitrary directed suprema,
and does not replace the dual norm by a pointwise or weak-star topology.
No converse density of dominated functionals is asserted.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isNormalFunctional_of_norm_approximation (M : VonNeumannAlgebra H)
    (f : StrongDual ℂ M.toStarSubalgebra)
    (hf : ∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : StrongDual ℂ M.toStarSubalgebra,
      IsNormalFunctional M g ∧ ‖g - f‖ < ε) :
    IsNormalFunctional M f := by
  intro s hs hd hp X hX
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    have h := (Complex.le_def.mp (hf (X - Y) (sub_nonneg.mpr (hX.1 hY)))).1
    simpa only [map_sub, Complex.sub_re, Complex.zero_re, sub_nonneg] using h
  · intro r hr
    by_contra hnot
    have hgap : 0 < (f X).re - r := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨δ, hδ, hδgap⟩ := exists_pos_mul_lt hgap (2 * ‖X‖)
    obtain ⟨g, hgn, hgf⟩ := happrox δ hδ
    have herr (Y : M.toStarSubalgebra) : |(g Y - f Y).re| ≤ δ * ‖Y‖ := by
      calc
        |(g Y - f Y).re| ≤ ‖g Y - f Y‖ := Complex.abs_re_le_norm _
        _ ≤ ‖g - f‖ * ‖Y‖ := (g - f).le_opNorm Y
        _ ≤ δ * ‖Y‖ := mul_le_mul_of_nonneg_right hgf.le (norm_nonneg Y)
    have hupper : (g X).re ≤ r + δ * ‖X‖ := by
      apply (hgn s hs hd hp X hX).2
      rintro _ ⟨Y, hY, rfl⟩
      have he := (abs_le.mp (herr Y)).2
      have hn : ‖Y‖ ≤ ‖X‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg (hX.1 hY) (hp Y hY)
      have hmul := mul_le_mul_of_nonneg_left hn hδ.le
      have hb := hr ⟨Y, hY, rfl⟩
      simp only [Complex.sub_re] at he
      linarith
    have he := (abs_le.mp (herr X)).1
    simp only [Complex.sub_re] at he
    nlinarith

/-- Literal positivity and order-normality form a norm-closed subset of the
original full continuous dual, including the zero functional. -/
theorem isClosed_positive_normal_cone (M : VonNeumannAlgebra H) :
    IsClosed {f : StrongDual ℂ M.toStarSubalgebra |
      (∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X) ∧ IsNormalFunctional M f} := by
  apply isClosed_of_closure_subset
  intro f hf
  have hpos : ∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X := by
    intro X hX
    have hc : IsClosed {g : StrongDual ℂ M.toStarSubalgebra | 0 ≤ g X} :=
      isClosed_le continuous_const (continuous_id.clm_apply continuous_const)
    have hsub : {g : StrongDual ℂ M.toStarSubalgebra |
        (∀ Y : M.toStarSubalgebra, 0 ≤ Y → 0 ≤ g Y) ∧ IsNormalFunctional M g} ⊆
        {g | 0 ≤ g X} := fun g hg => hg.1 X hX
    exact closure_minimal hsub hc hf
  refine ⟨hpos, isNormalFunctional_of_norm_approximation M f hpos ?_⟩
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
  refine ⟨g, hg.2, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hfg

/-- This is only the sound inclusion into the normal positive cone.
Approximating every normal positive functional by dominated ones is separate. -/
theorem closure_dominated_positive_subset_normal (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) :
    closure {f : StrongDual ℂ M.toStarSubalgebra |
      (∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ X : M.toStarSubalgebra, 0 ≤ X → f X ≤ C • φ X} ⊆
      {f : StrongDual ℂ M.toStarSubalgebra |
        (∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X) ∧ IsNormalFunctional M f} := by
  apply closure_minimal ?_ (isClosed_positive_normal_cone M)
  rintro f ⟨hf, C, hC, hdom⟩
  exact ⟨hf, isNormalFunctional_of_dual_domination M φ hn f hf C hC hdom⟩

end VacuumBellSeparation.Bipartite
