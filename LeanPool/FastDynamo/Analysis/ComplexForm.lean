/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.AntiDual

/-!
# Coercive complex forms

The paper writes complex inner products and sesquilinear forms **linear in
the first argument** and conjugate-linear in the second.  Mathlib uses the
opposite inner-product convention.  Accordingly, a continuous form on a
complex Hilbert space `V` is represented here as

`V →L[ℂ] (V →L⋆[ℂ] ℂ)`.

Thus the first argument is linear and the second is conjugate-linear.  The
Riesz representative `complexFormOperator a` is characterized by

`a u v = inner ℂ v (complexFormOperator a u)`.

Mathlib's Lax--Milgram theorem is formulated for real bilinear forms.
This file proves the complex positive-real-part version needed by the
formalisation.  In particular, coercivity gives a quantitative lower bound,
injectivity, closed range, surjectivity, and finally a continuous linear
equivalence.  No form-representation theorem or paper-specific axiom is used.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- A continuous complex form in the paper's linear-first convention.

The outer continuous linear map encodes linearity in the first argument; its
values lie in the continuous anti-dual, encoding conjugate-linearity in the
second argument. -/
abbrev ComplexForm (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] := V →L[ℂ] (V →L⋆[ℂ] ℂ)

/-- The Riesz representative of a complex form in the convention of the paper. -/
def complexFormOperator (a : ComplexForm V) : V →L[ℂ] V :=
  (complexToAntiDual (E := V)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp a

/-- Evaluation of a form through its Riesz representative, with Mathlib's
conjugate-linear-first inner-product convention made explicit. -/
theorem complexForm_eq_inner (a : ComplexForm V) (u v : V) :
    a u v = inner ℂ v (complexFormOperator a u) := by
  change a u v =
    (complexToAntiDual ((complexToAntiDual (E := V)).symm (a u))) v
  rw [(complexToAntiDual (E := V)).apply_symm_apply]

/-- Positive-real-part coercivity for complex forms in the convention of the paper. -/
def IsComplexCoercive (a : ComplexForm V) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ u : V, c * ‖u‖ * ‖u‖ ≤ (a u u).re

/-- Coercivity gives a quantitative lower bound for the Riesz representative. -/
theorem IsComplexCoercive.boundedBelow {a : ComplexForm V}
    (ha : IsComplexCoercive a) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : V, c * ‖u‖ ≤ ‖complexFormOperator a u‖ := by
  rcases ha with ⟨c, hc, hcoercive⟩
  refine ⟨c, hc, ?_⟩
  intro u
  by_cases hu : 0 < ‖u‖
  · apply le_of_mul_le_mul_right (a := ‖u‖) _ hu
    calc
      c * ‖u‖ * ‖u‖ ≤ (a u u).re := hcoercive u
      _ ≤ ‖a u u‖ := Complex.re_le_norm _
      _ = ‖inner ℂ u (complexFormOperator a u)‖ := by
        rw [complexForm_eq_inner]
      _ ≤ ‖u‖ * ‖complexFormOperator a u‖ := norm_inner_le_norm _ _
      _ = ‖complexFormOperator a u‖ * ‖u‖ := mul_comm _ _
  · have hn : ‖u‖ = 0 := le_antisymm (not_lt.mp hu) (norm_nonneg _)
    have huz : u = 0 := norm_eq_zero.mp hn
    simp [huz]

namespace IsComplexCoercive

/-- A coercive complex form has an antilipschitz Riesz representative. -/
theorem antilipschitz {a : ComplexForm V} (ha : IsComplexCoercive a) :
    ∃ c : NNReal, 0 < c ∧ AntilipschitzWith c (complexFormOperator a) := by
  rcases ha.boundedBelow with ⟨c, hc, hbound⟩
  refine ⟨c⁻¹.toNNReal, Real.toNNReal_pos.mpr (inv_pos.mpr hc), ?_⟩
  refine ContinuousLinearMap.antilipschitz_of_bound (complexFormOperator a) ?_
  simp_rw [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr hc), ←
    inv_mul_le_iff₀ (inv_pos.mpr hc)]
  simpa using hbound

/-- The Riesz representative of a coercive complex form is injective. -/
theorem injective {a : ComplexForm V} (ha : IsComplexCoercive a) :
    Function.Injective (complexFormOperator a) := by
  rcases ha.antilipschitz with ⟨_, _, hanti⟩
  exact hanti.injective

/-- The kernel of the Riesz representative of a coercive form is trivial. -/
theorem ker_eq_bot {a : ComplexForm V} (ha : IsComplexCoercive a) :
    (complexFormOperator a).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact ha.injective

/-- The range of the Riesz representative of a coercive form is closed. -/
theorem isClosed_range {a : ComplexForm V} (ha : IsComplexCoercive a) :
    IsClosed ((complexFormOperator a).range : Set V) := by
  rcases ha.antilipschitz with ⟨_, _, hanti⟩
  exact hanti.isClosed_range (complexFormOperator a).uniformContinuous

/-- The range of the Riesz representative of a coercive complex form is all of
the Hilbert space.  The proof uses closed range together with orthogonal
complements, and applies coercivity once more to kill the orthogonal
complement. -/
theorem range_eq_top {a : ComplexForm V} (ha : IsComplexCoercive a) :
    (complexFormOperator a).range = ⊤ := by
  have := ha.isClosed_range.completeSpace_coe
  rw [← (complexFormOperator a).range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro v w hw
  rcases ha with ⟨c, hc, hcoercive⟩
  obtain rfl : w = 0 := by
    have horth : inner ℂ (complexFormOperator a w) w = 0 :=
      hw _ ⟨w, rfl⟩
    have hbound := hcoercive w
    rw [complexForm_eq_inner] at hbound
    have hre : (inner ℂ w (complexFormOperator a w)).re =
        (inner ℂ (complexFormOperator a w) w).re :=
      (inner_re_symm (𝕜 := ℂ) (complexFormOperator a w) w).symm
    rw [hre, horth] at hbound
    simp only [Complex.zero_re] at hbound
    have hn : ‖w‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      apply not_lt.mp
      intro hnpos
      have hprod : 0 < c * ‖w‖ * ‖w‖ :=
        mul_pos (mul_pos hc hnpos) hnpos
      exact (not_lt_of_ge hbound) hprod
    exact norm_eq_zero.mp hn
  exact inner_zero_left _

/-- Complex Lax--Milgram: a bounded, positive-real-part coercive complex form
defines a continuous linear equivalence of its Hilbert space. -/
def continuousLinearEquiv (a : ComplexForm V) (ha : IsComplexCoercive a) :
    V ≃L[ℂ] V :=
  ContinuousLinearEquiv.ofBijective (complexFormOperator a)
    ha.ker_eq_bot ha.range_eq_top

/-- The forward map in complex Lax--Milgram is the form's Riesz
representative. -/
@[simp] theorem continuousLinearEquiv_apply (a : ComplexForm V)
    (ha : IsComplexCoercive a) (u : V) :
    continuousLinearEquiv a ha u = complexFormOperator a u :=
  rfl

end IsComplexCoercive

end

end FastDynamo
