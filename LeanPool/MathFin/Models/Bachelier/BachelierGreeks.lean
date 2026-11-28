/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Bachelier.Bachelier
public import LeanPool.MathFin.Probability.Analysis.DerivOfDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Bachelier model Greeks

For the Bachelier call price `V_bach(S, σ, T) = (S − K) Φ(d) + σ √T ϕ(d)`
where `d = (S − K)/(σ √T)`, we derive four Greeks:

* **Delta**: `∂V/∂S = Φ(d)`.
* **Gamma**: `∂²V/∂S² = ϕ(d) / (σ √T)`.
* **Vega**: `∂V/∂σ = √T · ϕ(d)`.
* **Theta**: `∂V/∂T = σ · ϕ(d) / (2 √T)`.

These parallel the Black–Scholes Greeks but with much simpler algebra
(no exponential, no log). All cancellation goes through the identity
`(S − K)/(σ √T) = d`.

## Main definitions

* `bachelierV`: the Bachelier call price `(S - K) Φ d + σ √T ϕ d` with `d = (S - K) / (σ √T)`, as a
  function of the spot `S`.

## Main results

* `hasDerivAt_bachelierV_S`: delta, `∂V/∂S = Φ d`, for `0 < σ` and `0 < T`.
* `hasDerivAt_deriv_bachelierV_S`: gamma, `∂²V/∂S² = ϕ d / (σ √T)`, for `0 < σ` and `0 < T`.
* `hasDerivAt_bachelierV_sigma`: vega, `∂V/∂σ = √T · ϕ d`, for `0 < T` and `0 < σ`.
* `hasDerivAt_bachelierV_T`: theta, `∂V/∂T = σ · ϕ d / (2 √T)`, for `0 < σ` and `0 < T`.

## Tags

Bachelier model, Greeks, delta, gamma, vega, theta, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- The Bachelier call price as a function of `(S, σ)`:
`V_bach = (S − K) Φ(d) + σ √T ϕ(d)` where `d = (S − K)/(σ √T)`. -/
noncomputable def bachelierV (K σ T : ℝ) (S : ℝ) : ℝ :=
  (S - K) * Phi (bachelierD S K σ T) +
    σ * Real.sqrt T * gaussianPDFReal 0 1 (bachelierD S K σ T)

/-- `∂_S [bachelierD S K σ T] = 1 / (σ √T)`. -/
private lemma hasDerivAt_bachelierD_S {K σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (S : ℝ) :
    HasDerivAt (fun s ↦ bachelierD s K σ T) (1 / (σ * Real.sqrt T)) S := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_στ_pos : 0 < σ * Real.sqrt T := mul_pos hσ h_sqrt_pos
  have h_num : HasDerivAt (fun s : ℝ ↦ s - K) 1 S := by
    convert (hasDerivAt_id S).sub_const K using 1; rfl
  exact h_num.div_const (σ * Real.sqrt T)

/-- **Bachelier delta**: `∂V/∂S = Φ(d)`. -/
lemma hasDerivAt_bachelierV_S {K σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (S : ℝ) :
    HasDerivAt (fun s ↦ bachelierV K σ T s) (Phi (bachelierD S K σ T)) S := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrt_ne : Real.sqrt T ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_d_S := hasDerivAt_bachelierD_S (K := K) hσ hT S
  -- Chain rule: ∂_S Φ(d(S)) = ϕ(d) · ∂_S d
  have h_Phi_chain := (hasDerivAt_Phi (bachelierD S K σ T)).comp S h_d_S
  -- Chain rule: ∂_S ϕ(d(S)) = -d · ϕ(d) · ∂_S d
  have h_pdf_chain := (hasDerivAt_gaussianPDFReal_zero_one (bachelierD S K σ T)).comp S h_d_S
  -- ∂_S [(S - K)] = 1
  have h_S_sub : HasDerivAt (fun s : ℝ ↦ s - K) 1 S := by
    convert (hasDerivAt_id S).sub_const K using 1; rfl
  -- ∂_S [(S-K) · Φ(d(S))] = Φ(d) + (S-K) · ϕ(d) · ∂_S d
  have h_term1 := h_S_sub.mul h_Phi_chain
  -- ∂_S [σ √T · ϕ(d(S))] = σ √T · (-d ϕ(d)) · ∂_S d
  have h_term2 := h_pdf_chain.const_mul (σ * Real.sqrt T)
  have h_full := h_term1.add h_term2
  unfold bachelierV
  convert h_full using 1 <;> try rfl
  -- Value match: (S - K) ϕ(d) · 1/(σ√T) - σ√T · d · ϕ(d) · 1/(σ√T)
  --            = ϕ(d) · [(S-K)/(σ√T) - d] = ϕ(d) · [d - d] = 0
  -- so Φ(d) = Φ(d) + 0. trivially.
  simp only [Function.comp]
  change Phi (bachelierD S K σ T) =
    (1 * Phi (bachelierD S K σ T) + (S - K) *
        (gaussianPDFReal 0 1 (bachelierD S K σ T) * (1 / (σ * Real.sqrt T))))
    + σ * Real.sqrt T *
        (-(bachelierD S K σ T * gaussianPDFReal 0 1 (bachelierD S K σ T)) * (1 / (σ * Real.sqrt T)))
  rw [bachelierD]
  field_simp
  ring

/-- **Bachelier vega**: `∂V/∂σ = √T · ϕ(d)`. -/
lemma hasDerivAt_bachelierV_sigma {K T : ℝ} (hT : 0 < T)
    {S σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s ↦ bachelierV K s T S)
      (Real.sqrt T * gaussianPDFReal 0 1 (bachelierD S K σ T)) σ := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrt_ne : Real.sqrt T ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  -- ∂_σ [bachelierD] = -(S - K) / (σ² √T) = -d/σ
  have h_d_σ : HasDerivAt (fun s ↦ bachelierD S K s T)
      (-((S - K) / (σ^2 * Real.sqrt T))) σ := by
    have h_quot : HasDerivAt (fun s : ℝ ↦ (S - K) / (s * Real.sqrt T))
        ((0 * (σ * Real.sqrt T) - (S - K) * (1 * Real.sqrt T)) / (σ * Real.sqrt T)^2) σ := by
      have h_const : HasDerivAt (fun _ : ℝ ↦ (S - K)) 0 σ := hasDerivAt_const _ _
      have h_denom : HasDerivAt (fun s : ℝ ↦ s * Real.sqrt T) (1 * Real.sqrt T) σ := by
        convert (hasDerivAt_id σ).mul_const (Real.sqrt T) using 1; rfl
      exact h_const.div h_denom (mul_pos hσ h_sqrt_pos).ne'
    convert h_quot using 1 <;> try rfl
    field_simp
    ring
  -- Chain rules
  have h_Phi_chain := (hasDerivAt_Phi (bachelierD S K σ T)).comp σ h_d_σ
  have h_pdf_chain := (hasDerivAt_gaussianPDFReal_zero_one (bachelierD S K σ T)).comp σ h_d_σ
  -- ∂_σ [(S-K) Φ(d(σ))] = (S-K) ϕ(d) · ∂_σ d
  have h_term1 := h_Phi_chain.const_mul (S - K)
  -- ∂_σ [σ √T] = √T
  have h_σ_sqrt : HasDerivAt (fun s : ℝ ↦ s * Real.sqrt T) (Real.sqrt T) σ := by
    convert (hasDerivAt_id σ).mul_const (Real.sqrt T) using 1 <;> first | rfl | ring
  -- ∂_σ [σ √T · ϕ(d(σ))] = √T · ϕ(d) + σ √T · (-d ϕ(d)) · ∂_σ d
  have h_term2 := h_σ_sqrt.mul h_pdf_chain
  have h_full := h_term1.add h_term2
  unfold bachelierV
  convert h_full using 1 <;> try rfl
  simp only [Function.comp]
  rw [bachelierD]
  field_simp
  ring

/-- **The Bachelier gamma formula**: the S-derivative of the delta `Φ(d(S))` is
`ϕ(d) / (σ √T)`, by the chain rule. The second derivative of the price itself is
`hasDerivAt_deriv_bachelierV_S`. -/
private lemma hasDerivAt_bachelierV_SS {K σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (S : ℝ) :
    HasDerivAt (fun s ↦ Phi (bachelierD s K σ T))
      (gaussianPDFReal 0 1 (bachelierD S K σ T) / (σ * Real.sqrt T)) S := by
  -- `S` is `bachelierD`'s first argument, so the chain rule is elaborated before its target
  have h := (hasDerivAt_Phi (bachelierD S K σ T)).comp S (hasDerivAt_bachelierD_S (K := K) hσ hT S)
  exact h.congr_deriv (mul_one_div _ _)

/-- **Bachelier gamma**: `∂²V/∂S² = ϕ(d) / (σ √T)`, for the price itself: the delta `Φ(d)` is
`∂V/∂S` at every spot (`hasDerivAt_bachelierV_S`), and its derivative is the gamma formula
(`hasDerivAt_bachelierV_SS`). -/
theorem hasDerivAt_deriv_bachelierV_S {K σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (S : ℝ) :
    HasDerivAt (deriv fun s ↦ bachelierV K σ T s)
      (gaussianPDFReal 0 1 (bachelierD S K σ T) / (σ * Real.sqrt T)) S :=
  hasDerivAt_deriv_of_eventually
    (.of_forall (hasDerivAt_bachelierV_S hσ hT))
    (hasDerivAt_bachelierV_SS hσ hT S)

/-- **Bachelier theta**: `∂V/∂T = σ · ϕ(d) / (2 √T)`.

Chain-rule contributions through `d` cancel via `(S − K) · d / √T = σ · d²`. -/
lemma hasDerivAt_bachelierV_T {K σ : ℝ} (hσ : 0 < σ) {S T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun t ↦ bachelierV K σ t S)
      (σ * gaussianPDFReal 0 1 (bachelierD S K σ T) / (2 * Real.sqrt T)) T := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrt_ne : Real.sqrt T ≠ 0 := h_sqrt_pos.ne'
  have hT_ne : T ≠ 0 := hT.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_sqrt_sq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  -- ∂_T [bachelierD] = -(S - K) / (2 σ T^(3/2)) = -d / (2 T)
  have h_d_T : HasDerivAt (fun t ↦ bachelierD S K σ t)
      (-((S - K) / (2 * σ * T * Real.sqrt T))) T := by
    have h_const : HasDerivAt (fun _ : ℝ ↦ (S - K)) 0 T := hasDerivAt_const _ _
    have h_sqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt T)) T := Real.hasDerivAt_sqrt hT.ne'
    have h_σsqrt : HasDerivAt (fun t : ℝ ↦ σ * Real.sqrt t) (σ / (2 * Real.sqrt T)) T := by
      have := h_sqrt.const_mul σ
      convert this using 1
      field_simp
    have h_quot : HasDerivAt (fun t : ℝ ↦ (S - K) / (σ * Real.sqrt t))
        ((0 * (σ * Real.sqrt T) - (S - K) * (σ / (2 * Real.sqrt T))) / (σ * Real.sqrt T)^2) T := by
      exact h_const.div h_σsqrt (mul_pos hσ h_sqrt_pos).ne'
    convert h_quot using 1 <;> try rfl
    field_simp
    rw [show Real.sqrt T ^ 2 = T from h_sqrt_sq]
    ring
  -- Chain rules
  have h_Phi := (hasDerivAt_Phi (bachelierD S K σ T)).comp T h_d_T
  have h_pdf := (hasDerivAt_gaussianPDFReal_zero_one (bachelierD S K σ T)).comp T h_d_T
  -- ∂_T [(S - K) Φ(d(T))] = (S - K) · ϕ(d) · ∂_T d
  have h_term1 := h_Phi.const_mul (S - K)
  -- ∂_T [σ √T] = σ / (2√T)
  have h_σsqrt' : HasDerivAt (fun t : ℝ ↦ σ * Real.sqrt t) (σ / (2 * Real.sqrt T)) T := by
    have h := (Real.hasDerivAt_sqrt hT.ne').const_mul σ
    convert h using 1
    field_simp
  -- ∂_T [σ √T · ϕ(d(T))] = (σ/(2√T)) · ϕ(d) + σ √T · (-d ϕ(d)) · ∂_T d
  have h_term2 := h_σsqrt'.mul h_pdf
  have h_full := h_term1.add h_term2
  unfold bachelierV
  convert h_full using 1 <;> try rfl
  simp only [Function.comp]
  rw [bachelierD]
  field_simp
  ring

end MathFin
