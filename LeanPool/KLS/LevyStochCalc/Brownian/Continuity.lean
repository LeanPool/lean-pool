/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Construction
public import LeanPool.KLS.LevyStochCalc.Brownian.ContinuityDyadicChaining
public import LeanPool.KLS.LevyStochCalc.Brownian.ContinuityKolmogorovBounds
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Kolmogorov-Chentsov continuous modification

Mathlib has only `IsKolmogorovProcess` (the *condition*); the modification
result is missing. We port the classical proof (Karatzas-Shreve §2.2 Thm 2.8 /
Le Gall 2016 Thm 2.9):

  *If `(X_t)_{t ≥ 0}` satisfies `𝔼[ |X_t − X_s|^p ] ≤ M · |t − s|^q` for some
  `p, q > 0` with `q > 1` and constant `M`, then there exists a modification
  `Xtilde` with continuous paths.*

The sub-lemmas of the proof live in two imported modules of the same namespace:
`LevyStochCalc.Brownian.ContinuityDyadicChaining` (Hölder extension from a dense
set, the dyadic rationals, dyadic truncation and the deterministic chaining
bound) and `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` (the Markov tail
bound, the per-level Borel-Cantelli estimates, almost-sure local Hölder
regularity and the modification identity). This module assembles them into
`kolmogorovChentsov_modification` and applies it to Brownian motion, whose
fourth increment moment is computed here from the Gaussian moment generating
function.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Kolmogorov–Chentsov continuous modification.** A real-valued process
satisfying the Kolmogorov moment condition
`∫⁻ ω, edist (X s ω) (X t ω)^p ∂P ≤ M · edist s t ^ q` with `q > 1` admits a
modification with continuous paths (Karatzas–Shreve 2.2.8 / Le Gall 2.9). The
modification is the dyadic `extendFrom` of `X`; continuity comes from a.s. local
Hölder regularity (`kc_ae_nbhd_holder`) via `extendFrom`, and the modification
property from `kolmogorov_modification_ae_eq`. The Hölder exponent is
`α := (q−1)/(2p)` (`0 < α`, `αp < q−1`). -/
theorem kolmogorovChentsov_modification
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (hq : 1 < q) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω) := by
  have hp : 0 < p := hX.p_pos
  set α : ℝ := (q - 1) / (2 * p) with hα_def
  have hα0 : 0 < α := by rw [hα_def]; exact div_pos (by linarith) (by linarith)
  have hαpq : α * p < q - 1 := by
    have h2p : 0 < 2 * p := by linarith
    rw [hα_def, div_mul_eq_mul_div, div_lt_iff₀ h2p]
    nlinarith [mul_pos (show (0:ℝ) < q - 1 from by linarith) hp]
  set Y : ℝ → Ω → ℝ :=
    fun t ω => extendFrom dyadicRationals (fun s => X s ω) t with hY_def
  have hnbhd := kc_ae_nbhd_holder P X hX hα0 hαpq
  have hcont : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω) := by
    filter_upwards [hnbhd] with ω hω
    exact continuous_extendFrom dense_dyadicRationals
      (fun t => exists_tendsto_of_local_holder dense_dyadicRationals hα0 t (hω t))
  refine ⟨Y, hcont, ?_⟩
  refine kolmogorov_modification_ae_eq P X hX Y hcont ?_
  intro s hs
  filter_upwards [hnbhd] with ω hω
  -- `Y s ω = extendFrom dyadicRationals (· ↦ X · ω) s = X s ω`
  refine extendFrom_eq (subset_closure hs) ?_
  obtain ⟨K, ρ, hρ, hK0, hHol⟩ := hω s
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min ρ ((ε / (K + 1)) ^ (1 / α)),
    lt_min hρ (Real.rpow_pos_of_pos (by positivity) _), fun u hu hdu => ?_⟩
  have huρ : u ∈ Set.Ioo (s - ρ) (s + ρ) := by
    rw [Real.dist_eq] at hdu
    have := lt_of_lt_of_le hdu (min_le_left _ _)
    rw [abs_lt] at this; exact ⟨by linarith, by linarith⟩
  have hsρ : s ∈ Set.Ioo (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
  have hb := hHol u hu s hs huρ hsρ
  have hdu2 : |u - s| < (ε / (K + 1)) ^ (1 / α) := by
    rw [← Real.dist_eq]; exact lt_of_lt_of_le hdu (min_le_right _ _)
  have hpow : |u - s| ^ α < ε / (K + 1) := by
    have h1 := Real.rpow_lt_rpow (abs_nonneg _) hdu2 hα0
    rwa [show ((ε / (K + 1)) ^ (1 / α)) ^ α = ε / (K + 1) from by
      rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hα0),
          Real.rpow_one]] at h1
  rw [Real.dist_eq]
  calc |X u ω - X s ω| ≤ K * |u - s| ^ α := hb
    _ ≤ (K + 1) * |u - s| ^ α := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ < (K + 1) * (ε / (K + 1)) := by apply mul_lt_mul_of_pos_left hpow (by positivity)
    _ = ε := by field_simp

/-- **Integrability set is `univ` for Gaussian.** `0 ∈ interior (integrableExpSet
id (gaussianReal 0 v))`. -/
lemma zero_mem_interior_integrableExpSet_gaussianReal (v : ℝ≥0) :
    0 ∈ interior
      (ProbabilityTheory.integrableExpSet id (ProbabilityTheory.gaussianReal 0 v)) := by
  rw [ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [interior_univ]
  exact Set.mem_univ 0

/-- **First derivative of `t ↦ exp(c · t²)`.** -/
lemma deriv_exp_quadratic (c : ℝ) :
    deriv (fun t : ℝ => Real.exp (c * t^2)) = fun t => 2 * c * t * Real.exp (c * t^2) := by
  funext t
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_outer : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  rw [h_outer.deriv]
  ring

/-- **First derivative at 0 is 0.** `f'(0) = 2c·0·exp(0) = 0`. -/
lemma iteratedDeriv1_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => Real.exp (c * t^2)) 0 = 0 := by
  rw [iteratedDeriv_one, deriv_exp_quadratic]
  ring

/-- **Second derivative of `t ↦ exp(c · t²)`.** `f''(t) = (2c + 4c²t²) · exp(c·t²)`.

(Equivalently: `f'' = 2c·exp + 4c²·t²·exp`.) -/
lemma deriv2_exp_quadratic (c : ℝ) :
    deriv (deriv (fun t : ℝ => Real.exp (c * t^2)))
      = fun t => (2 * c + 4 * c^2 * t^2) * Real.exp (c * t^2) := by
  rw [deriv_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => 2*c*t * exp(c*t^2)) t = (2c + 4c²t²) exp(c*t²)
  -- Product rule: deriv (g · h) = g' · h + g · h' where g(t) = 2*c*t, h(t) = exp(c*t²).
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  have h_lin : HasDerivAt (fun t : ℝ => 2 * c * t) (2 * c) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * c)
  have h_prod : HasDerivAt (fun t : ℝ => 2 * c * t * Real.exp (c * t^2))
      (2 * c * Real.exp (c * t^2) + 2 * c * t * (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_lin.mul h_exp
  rw [h_prod.deriv]
  ring

/-- **Second derivative at 0 is `2c`.** -/
lemma iteratedDeriv2_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => Real.exp (c * t^2)) 0 = 2 * c := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      deriv2_exp_quadratic]
  simp [Real.exp_zero, mul_comm]

/-- **Third derivative of `t ↦ exp(c · t²)`.**
`f'''(t) = (12c²t + 8c³t³) · exp(c·t²)`. -/
lemma deriv3_exp_quadratic (c : ℝ) :
    deriv (deriv (deriv (fun t : ℝ => Real.exp (c * t^2))))
      = fun t => (12 * c^2 * t + 8 * c^3 * t^3) * Real.exp (c * t^2) := by
  rw [deriv2_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => (2c + 4c²t²) · exp(c*t²)) t = (12c²t + 8c³t³) exp(c*t²)
  -- Use product rule: g(t) := 2c + 4c²t², h(t) := exp(c*t²).
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  have h_quad : HasDerivAt (fun t : ℝ => 2 * c + 4 * c^2 * t^2)
      (4 * c^2 * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (4 * c^2)).const_add (2 * c)
    simpa [pow_one] using this
  have h_prod : HasDerivAt
      (fun t : ℝ => (2 * c + 4 * c^2 * t^2) * Real.exp (c * t^2))
      (4 * c^2 * (2 * t) * Real.exp (c * t^2)
        + (2 * c + 4 * c^2 * t^2) * (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_quad.mul h_exp
  rw [h_prod.deriv]
  ring

/-- **Third derivative at 0 is `0`.** -/
lemma iteratedDeriv3_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => Real.exp (c * t^2)) 0 = 0 := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, deriv3_exp_quadratic]
  ring

/-- **Fourth derivative of `t ↦ exp(c · t²)`.**
`f⁽⁴⁾(t) = (12c² + 48c³t² + 16c⁴t⁴) · exp(c·t²)`. -/
lemma deriv4_exp_quadratic (c : ℝ) :
    deriv (deriv (deriv (deriv (fun t : ℝ => Real.exp (c * t^2)))))
      = fun t => (12 * c^2 + 48 * c^3 * t^2 + 16 * c^4 * t^4) * Real.exp (c * t^2) := by
  rw [deriv3_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => (12c²t + 8c³t³) · exp(c·t²)) t
  --     = (12c² + 48c³t² + 16c⁴t⁴) exp(c·t²)
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  -- Derivative of (12c²t + 8c³t³).
  have h_lin : HasDerivAt (fun t : ℝ => 12 * c^2 * t)
      (12 * c^2) t := by
    simpa using (hasDerivAt_id t).const_mul (12 * c^2)
  have h_cub : HasDerivAt (fun t : ℝ => 8 * c^3 * t^3)
      (8 * c^3 * (3 * t^2)) t := by
    have := (hasDerivAt_pow 3 t).const_mul (8 * c^3)
    simpa using this
  have h_poly : HasDerivAt (fun t : ℝ => 12 * c^2 * t + 8 * c^3 * t^3)
      (12 * c^2 + 8 * c^3 * (3 * t^2)) t := h_lin.add h_cub
  have h_prod : HasDerivAt
      (fun t : ℝ => (12 * c^2 * t + 8 * c^3 * t^3) * Real.exp (c * t^2))
      ((12 * c^2 + 8 * c^3 * (3 * t^2)) * Real.exp (c * t^2)
        + (12 * c^2 * t + 8 * c^3 * t^3) *
          (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_poly.mul h_exp
  rw [h_prod.deriv]
  ring

/-- **Fourth derivative at 0 is `12c²`.** -/
lemma iteratedDeriv4_exp_quadratic_at_zero' (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (c * t^2)) 0 = 12 * c^2 := by
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_succ, iteratedDeriv_one, deriv4_exp_quadratic]
  simp [Real.exp_zero]

/-- **Connection**: rewrite from MGF to exponential at the function level. -/
lemma mgf_id_gaussianReal_eq_exp_quadratic (v : ℝ≥0) :
    ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v)
      = fun t : ℝ => Real.exp ((v : ℝ) / 2 * t^2) := by
  rw [ProbabilityTheory.mgf_id_gaussianReal]
  funext t
  ring_nf

/-- **MGF at 0**: `mgf id (gaussianReal 0 v) 0 = 1`. (`exp(0) = 1`.) -/
lemma mgf_id_gaussianReal_at_zero (v : ℝ≥0) :
    ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v) 0 = 1 := by
  rw [mgf_id_gaussianReal_eq_exp_quadratic]
  simp [Real.exp_zero]

/-- **Fourth derivative of `t ↦ exp(c · t²)` at `t = 0` is `12 c²`.**

Real direct calculation via 4 successive applications of chain + product rule.
Proved via `iteratedDeriv4_exp_quadratic_at_zero'` below. -/
lemma iteratedDeriv4_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (c * t^2)) 0 = 12 * c^2 :=
  iteratedDeriv4_exp_quadratic_at_zero' c

/-- **Gaussian fourth moment.** `∫ x^4 ∂(gaussianReal 0 v) = 3 v²`.

Real proof using the chain:
1. `mgf id (gaussianReal 0 v) = fun t ↦ exp(v t² / 2)` by `mgf_id_gaussianReal`.
2. `iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0 = ∫ x^4 ∂(gaussianReal 0 v)`
   by `iteratedDeriv_mgf_zero` (with integrability from
   `zero_mem_interior_integrableExpSet_gaussianReal`).
3. `iteratedDeriv 4 (fun t ↦ exp((v/2) · t²)) 0 = 12 (v/2)² = 3v²` by our
   `iteratedDeriv4_exp_quadratic_at_zero` (with `c = v/2`). -/
lemma gaussianReal_fourth_moment (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂(ProbabilityTheory.gaussianReal 0 v) = 3 * (v : ℝ)^2 := by
  -- Step 1: ∫ x^4 = iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0
  have h_int := zero_mem_interior_integrableExpSet_gaussianReal v
  have h_mgf_deriv :=
    ProbabilityTheory.iteratedDeriv_mgf_zero (X := id)
      (μ := ProbabilityTheory.gaussianReal 0 v) h_int 4
  -- h_mgf_deriv : iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0 = μ[id^4]
  -- where μ[id^4] = ∫ x, id x ^ 4 ∂μ = ∫ x, x^4 ∂μ.
  -- Step 2: rewrite mgf using mgf_id_gaussianReal
  have h_mgf : ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v)
      = fun t => Real.exp ((v : ℝ) * t^2 / 2) := by
    rw [ProbabilityTheory.mgf_id_gaussianReal]
    funext t; ring_nf
  -- Step 3: equality of the two functions at the iteratedDeriv level
  have h_funeq : (fun t : ℝ => Real.exp ((v : ℝ) * t^2 / 2))
      = (fun t : ℝ => Real.exp (((v : ℝ) / 2) * t^2)) := by
    funext t; ring_nf
  -- Step 4: apply iteratedDeriv4_exp_quadratic_at_zero with c = v/2
  have h4 := iteratedDeriv4_exp_quadratic_at_zero ((v : ℝ) / 2)
  -- h4 : iteratedDeriv 4 (fun t => exp((v/2) * t^2)) 0 = 12 * (v/2)^2
  -- Combine
  rw [show ∫ x, x^4 ∂(ProbabilityTheory.gaussianReal 0 v)
      = (ProbabilityTheory.gaussianReal 0 v)[id^4] from by
        simp [Pi.pow_apply]]
  rw [← h_mgf_deriv, h_mgf, h_funeq, h4]
  ring

/-- **Brownian increment fourth moment.** For a process `X` with Brownian-law
increments, `𝔼[(X_t − X_s)⁴] = 3 (t − s)²` for `s < t`. -/
lemma brownian_increment_fourth_moment
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩)
    {s t : ℝ} (hst : s < t) :
    ∫ ω, (X t ω - X s ω) ^ 4 ∂P = 3 * (t - s) ^ 2 := by
  -- Push to the pushforward measure via integral_map.
  have h_meas_diff : Measurable (fun ω => X t ω - X s ω) :=
    (h_meas t).sub (h_meas s)
  rw [show ∫ ω, (X t ω - X s ω) ^ 4 ∂P
        = ∫ x, x ^ 4 ∂(P.map (fun ω => X t ω - X s ω)) from
    (MeasureTheory.integral_map h_meas_diff.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 4) _)).symm]
  rw [h_increment hst]
  -- Goal: ∫ x, x^4 ∂(gaussianReal 0 ⟨t-s, _⟩) = 3 * (t-s)^2.
  have h := gaussianReal_fourth_moment ⟨t - s, by linarith⟩
  exact h

/-- **Auxiliary: Kolmogorov bound for Brownian increments (`s < t` case).**
For a process `X` with Brownian-law increments,
`∫⁻ ω, edist (X s ω) (X t ω)^4 ∂P ≤ 3 * edist s t ^ 2` when `s < t`.

Proof: convert `edist^4` to `ENNReal.ofReal ((X s ω - X t ω)^4)` (via
`edist_dist` and `|x|^4 = x^4`), push forward through the increment map,
apply `h_increment` to get `gaussianReal 0 ⟨t - s, _⟩`, then use
`gaussianReal_fourth_moment` and ENNReal arithmetic. -/
lemma brownian_continuous_modification_kol_aux
    {P : Measure Ω}
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩)
    {s t : ℝ} (hst : s < t) :
    ∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P ≤ 3 * edist s t ^ 2 := by
  have h_pow_abs : ∀ x : ℝ, |x|^4 = x^4 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have h_edist_pow : ∀ ω, edist (X s ω) (X t ω) ^ 4
      = ENNReal.ofReal ((X s ω - X t ω)^4) := by
    intro ω
    rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _), h_pow_abs]
  have h_meas_diff : Measurable (fun ω => X t ω - X s ω) :=
    (h_meas t).sub (h_meas s)
  have h_neg_pow : ∀ ω, (X s ω - X t ω)^4 = (X t ω - X s ω)^4 := fun ω => by ring
  rw [show (∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((X t ω - X s ω)^4) ∂P from
      by apply lintegral_congr; intro ω; rw [h_edist_pow ω, h_neg_pow ω]]
  rw [show (∫⁻ ω, ENNReal.ofReal ((X t ω - X s ω)^4) ∂P)
       = ∫⁻ y, ENNReal.ofReal (y^4) ∂(P.map (fun ω => X t ω - X s ω)) from
      by rw [lintegral_map (by fun_prop) h_meas_diff]]
  rw [h_increment hst]
  set v : NNReal := ⟨t - s, by linarith⟩ with hv_def
  have h_v_eq : (v : ℝ) = t - s := rfl
  have h_int : MeasureTheory.Integrable (fun x : ℝ => x^4)
      (ProbabilityTheory.gaussianReal 0 v) := by
    have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 4
        (ProbabilityTheory.gaussianReal 0 v) :=
      ProbabilityTheory.IsGaussian.memLp_id
        (ProbabilityTheory.gaussianReal 0 v) 4 (by simp)
    have h := h_memLp.integrable_norm_pow (p := 4) (by norm_num)
    convert h using 1
    ext x
    change x^4 = ‖x‖^4
    rw [Real.norm_eq_abs, h_pow_abs]
  have h_nn : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 v] fun x : ℝ => x^4 := by
    filter_upwards with x
    positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  rw [gaussianReal_fourth_moment v, h_v_eq]
  have h_edist_st : edist s t = ENNReal.ofReal (t - s) := by
    rw [edist_dist, Real.dist_eq]
    congr 1
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hst)]
  rw [h_edist_st]
  rw [show (3 : ENNReal) = ENNReal.ofReal 3 from by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : (0 : ℝ) ≤ 3)]
    norm_cast]
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr (le_of_lt hst))]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- **Continuous modification of a Brownian-increment process.** Any
real-valued process whose increments have the Brownian law
`(W_t − W_s) ~ 𝒩(0, t − s)` admits a continuous modification.

Proof structure:
* The Gaussian fourth moment identity (via `gaussianReal_fourth_moment`)
  gives `𝔼[(X_t − X_s)^4] = 3 (t − s)^2`, so the process satisfies
  `IsKolmogorovProcess` with `p = 4`, `q = 2`, `M = 3`.
* Apply `kolmogorovChentsov_modification` with `q = 2 > 1`.

The hypothesis `h_increment` is stated for **all** real `s < t` (no
nonnegativity constraint). This is consistent with a two-sided BM and is
required because the Kolmogorov bound must hold for all `s, t : ℝ`. -/
theorem brownian_continuous_modification
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω) := by
  have h_kolmogorov :
      ProbabilityTheory.IsKolmogorovProcess X P 4 2 3 :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
      h_meas
      (h_kol := ?_)
      (hp := by norm_num) (hq := by norm_num)
  · exact kolmogorovChentsov_modification P X h_kolmogorov (by norm_num)
  · -- Sub-goal: ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P ≤ 3 * edist s t ^ 2.
    intro s t
    -- The Kolmogorov condition uses ENNReal rpow `^ (4 : ℝ)`, but our aux
    -- uses Nat pow `^ (4 : ℕ)`. Bridge via `ENNReal.rpow_natCast`.
    have h_rpow_nat : ∀ ω, edist (X s ω) (X t ω) ^ (4 : ℝ)
        = edist (X s ω) (X t ω) ^ (4 : ℕ) := fun ω => by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num,
          ENNReal.rpow_natCast]
    have h_int_eq :
        (∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℝ) ∂P)
          = ∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℕ) ∂P := by
      apply lintegral_congr
      exact h_rpow_nat
    have h_rhs : edist s t ^ (2 : ℝ) = edist s t ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
          ENNReal.rpow_natCast]
    rw [h_int_eq, h_rhs]
    rcases lt_trichotomy s t with hst | hst | hst
    · -- Case s < t. Use brownian_increment_fourth_moment.
      exact brownian_continuous_modification_kol_aux X h_meas h_increment hst
    · -- Case s = t. Both sides = 0.
      subst hst
      simp
    · -- Case s > t. By symmetry of edist, reduce to t < s.
      have h_swap : (∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℕ) ∂P)
          = ∫⁻ ω, edist (X t ω) (X s ω) ^ (4 : ℕ) ∂P := by
        apply lintegral_congr
        intro ω
        rw [edist_comm]
      rw [h_swap, edist_comm s t]
      exact brownian_continuous_modification_kol_aux X h_meas h_increment hst

end LevyStochCalc.Brownian.Continuity
