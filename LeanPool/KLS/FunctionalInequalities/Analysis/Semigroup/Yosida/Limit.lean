/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Exponential.Limit
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Yosida.Laws

/-!
# The adjoint-product identification: the Yosida exponentials converge strongly

The adjoint-product identification for the Yosida approximation
`L_s = s⁻¹ (1 - J_s)` of `T†T`: for `T` closed and densely defined,
`exp (-t • L_s) f` converges as `s ↓ 0`, for every `f : H₀` and every `t ≥ 0`.

The proof is pure composition. The corrected abstract statement
(`exists_limit_exp_neg_smul`, `Exponential/Limit.lean`) is applied to the family `s ↦ L_s` with the
dense set `D(T†T)`: nonnegativity is `yosida_nonneg`, commutation is
(`yosida_comp_comm`), density is density of D(T†T) (`dense_adjointComp_domain`), and the Cauchy
property on
`D(T†T)` follows from the convergence `L_s f → T†T f`
(`exists_delta_norm_yosida_sub_adjointComp_lt`) by the triangle inequality.

This module proves convergence to `g`. The named operator and semigroup laws are constructed in
`Generated/{Basic,Laws}.lean`, and `Generated/Generator.lean` identifies the generator on its
stated domain. Markov properties, Bakry–Émery calculus and heat/Buser estimates belong to
separate consumers.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- On `D(T†T)` the Yosida approximations `L_s f` are Cauchy as `s ↓ 0`: they converge to
`T†T f` (`exists_delta_norm_yosida_sub_adjointComp_lt`). -/
theorem yosida_cauchy_on_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (v : H₀) (hv : v ∈ ((adjointComp T).domain : Set H₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s r : ℝ} (hs : 0 < s) (hr : 0 < r), s < δ → r < δ →
      ‖yosida T hT hs v - yosida T hT hr v‖ < ε := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_delta_norm_yosida_sub_adjointComp_lt T hT hd ⟨v, hv⟩ (half_pos hε)
  refine ⟨δ, hδ, fun {s r} hs hr hsδ hrδ => ?_⟩
  have h1 : ‖yosida T hT hs v - adjointComp T ⟨v, hv⟩‖ < ε / 2 := h hs hsδ
  have h2 : ‖yosida T hT hr v - adjointComp T ⟨v, hv⟩‖ < ε / 2 := h hr hrδ
  calc ‖yosida T hT hs v - yosida T hT hr v‖
      = ‖(yosida T hT hs v - adjointComp T ⟨v, hv⟩)
          - (yosida T hT hr v - adjointComp T ⟨v, hv⟩)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖yosida T hT hs v - adjointComp T ⟨v, hv⟩‖
          + ‖yosida T hT hr v - adjointComp T ⟨v, hv⟩‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

/--
**The adjoint-product identification for the Yosida approximation.** For `T` closed and densely
defined, every
`t ≥ 0` and every `f : H₀`, the vectors `exp (-t • L_s) f` converge as `s ↓ 0`, in the `ε`–`δ`
sense forced by the proof argument `0 < s` carried by `L_s`. -/
theorem exists_limit_exp_neg_smul_yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : H₀,
      ∀ {ε : ℝ},
        0 < ε →
          ∃ δ : ℝ,
            0 < δ ∧
              ∀ {s : ℝ} (hs : 0 < s),
                s < δ → ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε := by
  obtain ⟨g, hg⟩ :=
    exists_limit_exp_neg_smul (fun s hs => yosida T hT hs)
      (fun s hs v => yosida_nonneg T hT hs v) (fun s r hs hr => yosida_comp_comm T hT hs hr)
      ((adjointComp T).domain : Set H₀) (dense_adjointComp_domain T hT hd)
      (fun v hv ε hε => yosida_cauchy_on_adjointComp_domain T hT hd v hv hε) f ht
  refine ⟨g, fun {ε} hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  exact ⟨δ, hδ, fun {s} hs hsδ => h s hs hsδ⟩

end FunctionalInequalities.Analysis.Semigroup
