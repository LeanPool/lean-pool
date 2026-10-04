/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.DiffQuotientBound


/-!
# Uniqueness of the whole-space weak derivative

`HasWeakDeriv k g g'` (`EllipticPdes.Regularity.DiffQuotientBound`) pins `g'` only through
its integrals against smooth compactly supported test functions. Those integrals determine
`g'` as an `L²` class, because the test classes are dense in `L²(ℝᵈ)`
(`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`), so two weak `k`-derivatives of the same
class agree.

The identification steps of higher interior regularity (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2) produce a second derivative twice, once as a limit
of difference quotients and once through the Leibniz rule, and need them to be the same
class. This file supplies that step.

## Main declarations

* `annihilates_of_forall_testCls`: an `L²` class orthogonal to every smooth compactly
  supported class is zero.
* `HasWeakDeriv.unique`: the weak `k`-derivative is unique as an `L²` class.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Vanishing of an `L²` class orthogonal to every test class.** The classes of smooth compactly
supported functions are dense in `L²(ℝᵈ)`, and `y ↦ ⟪w, y⟫` is continuous, so a pairing that
vanishes on that family vanishes everywhere, in particular against `w` itself. -/
theorem annihilates_of_forall_testCls {w : EucL2 d}
    (hw : ∀ ρ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
      ∫ x, (w x : ℝ) * ρ x = 0) : w = 0 := by
  classical
  set S : Set (EucL2 d) := {y : EucL2 d | ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ,
    y =ᵐ[volume] ρ ∧ HasCompactSupport ρ ∧ ContDiff ℝ (⊤ : ℕ∞) ρ} with hS
  have hdense : Dense S :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (by norm_num)
  have hbase : ∀ y ∈ S, ⟪w, y⟫ = 0 := by
    rintro y ⟨ρ, hyρ, hρcs, hρcd⟩
    have hrepr : ⟪w, y⟫ = ∫ x, (w x : ℝ) * ρ x := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hyρ] with x hx
      rw [Real.inner_apply, hx]
    rw [hrepr, hw ρ hρcd hρcs]
  have hclosed : IsClosed {y : EucL2 d | ⟪w, y⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hall : ∀ y : EucL2 d, ⟪w, y⟫ = 0 := by
    have hsub : closure S ⊆ {y : EucL2 d | ⟪w, y⟫ = 0} :=
      hclosed.closure_subset_iff.mpr hbase
    rw [hdense.closure_eq] at hsub
    exact fun y => hsub (Set.mem_univ y)
  exact inner_self_eq_zero.mp (hall w)

/-- **Uniqueness of the whole-space weak derivative.** Two `L²` weak `k`-derivatives of the
same class coincide: their difference is orthogonal to every smooth compactly supported test
class, hence zero by `annihilates_of_forall_testCls`. -/
theorem HasWeakDeriv.unique {k : Fin d} {g w₁ w₂ : EucL2 d}
    (h₁ : HasWeakDeriv k g w₁) (h₂ : HasWeakDeriv k g w₂) : w₁ = w₂ := by
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hzero : w₁ - w₂ = 0 := by
    refine annihilates_of_forall_testCls (fun ρ hρcd hρcs => ?_)
    have hsplit : ∫ x, ((w₁ - w₂) x : ℝ) * ρ x
        = (∫ x, (w₁ x : ℝ) * ρ x) - ∫ x, (w₂ x : ℝ) * ρ x := by
      have hρL2 : MemLp ρ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
        hρcd.continuous.memLp_of_hasCompactSupport hρcs
      have hi₁ : Integrable (fun x => (w₁ x : ℝ) * ρ x) volume :=
        (Lp.memLp w₁).integrable_mul hρL2
      have hi₂ : Integrable (fun x => (w₂ x : ℝ) * ρ x) volume :=
        (Lp.memLp w₂).integrable_mul hρL2
      rw [← integral_sub hi₁ hi₂]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub w₁ w₂] with x hx
      rw [hx, Pi.sub_apply, sub_mul]
    have hw₁ := h₁ ρ hρcd hρcs
    have hw₂ := h₂ ρ hρcd hρcs
    rw [hsplit]
    have : (∫ x, (w₁ x : ℝ) * ρ x) = ∫ x, (w₂ x : ℝ) * ρ x := by
      have := hw₁.symm.trans hw₂
      linarith [this]
    rw [this, sub_self]
  exact sub_eq_zero.mp hzero

end EllipticPdes.Regularity
