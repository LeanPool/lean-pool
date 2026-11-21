/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Distances

/-!
# Heavy tails: second moment and infinite Wasserstein distance

* `integrable_sq_mul_equilibrium_iff'`: `∫ |x|² v_∞ < ∞` iff `m > d/(d+2)`.
* `wassersteinSq_eq_top'`: if `(d-2)/d < m ≤ d/(d+2)` then `W₂²(v(t), v_∞) = +∞` for `t > 0`.

For the second statement we use a moment argument rather than tail asymptotics. Let
`q = 2p - d ∈ (0, 2]` with `p = 1/(1-m)`, so that `N(r) = ∫ |x|ʳ v_∞` is finite for `r < q`
and `N(r) → ∞` as `r → q⁻` (explicitly `N(r) ≥ L / (q - r)`). If `γ` is a coupling of
`law(aX + h)` and `law(X)` (`X ∼ v_∞`, `0 < a < 1`) with finite quadratic cost, then the
elementary inequality `(u+v)ʳ ≤ cʳ uʳ + (c/(c-1))ʳ vʳ` (`c > 1`) gives
`N(r) ≤ (c²a)ʳ N(r) + K` with `K` independent of `r ∈ [q/2, q)`; choosing `c² a < 1`
this bounds `N(r)` uniformly, a contradiction.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

namespace HeavyTail

/-! ### Elementary real inequalities -/

/-- The power-tail bound for a shifted monomial, for `u ≥ 1`. -/
alias add_rpow_neg_ge := Radial.add_rpow_neg_ge

/-- The power-tail bound after multiplication by `u^s`. -/
alias pointwise_ge := Radial.pointwise_ge

/-- `(u + v)ʳ ≤ cʳ uʳ + (c/(c-1))ʳ vʳ` for `c > 1`. -/
lemma rpow_add_le {u v r c : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r) (hc : 1 < c) :
    (u + v) ^ r ≤ c ^ r * u ^ r + (c / (c - 1)) ^ r * v ^ r := by
  have hc1 : 0 < c - 1 := by linarith
  rcases le_or_gt v ((c - 1) * u) with hvu | hvu
  · have : (u + v) ^ r ≤ c ^ r * u ^ r := by
      rw [← Real.mul_rpow (by linarith) hu]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith) hr
    have : 0 ≤ (c / (c - 1)) ^ r * v ^ r := by positivity
    linarith
  · have : (u + v) ^ r ≤ (c / (c - 1)) ^ r * v ^ r := by
      rw [← Real.mul_rpow (by positivity) hv]
      refine Real.rpow_le_rpow (by positivity) ?_ hr
      rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
      nlinarith
    have : 0 ≤ c ^ r * u ^ r := by positivity
    linarith

/-- `tʳ ≤ 1 + t²` for `t ≥ 0` and `0 ≤ r ≤ 2`. -/
lemma rpow_le_one_add_sq {t r : ℝ} (ht : 0 ≤ t) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    t ^ r ≤ 1 + t ^ 2 := by
  rcases le_or_gt t 1 with h1 | h1
  · have := Real.rpow_le_one ht h1 hr0
    nlinarith [sq_nonneg t]
  · have := Real.rpow_le_rpow_of_exponent_le h1.le hr2
    rw [Real.rpow_two] at this
    linarith

/-- `cʳ ≤ c²` for `c ≥ 1` and `r ≤ 2`. -/
lemma rpow_le_sq {c r : ℝ} (hc : 1 ≤ c) (hr2 : r ≤ 2) : c ^ r ≤ c ^ 2 := by
  have := Real.rpow_le_rpow_of_exponent_le hc hr2
  rwa [Real.rpow_two] at this

/-! ### Integrals on `(0, ∞)` -/

/-- A shifted power with tail exponent at least `-1` has divergent integral. -/
alias not_integrableOn := Radial.not_integrableOn_affine_rpow_tail

/-- Lower bound `∫₀^∞ u^s (C + b u)^{-p} du ≥ (C+b)^{-p} / (-(s - p + 1))` when `s - p < -1`. -/
lemma integral_ge {C b p s : ℝ} (hC : 0 < C) (hb : 0 < b) (hp : 0 ≤ p) (hs : s - p < -1)
    (hI : IntegrableOn (fun u => u ^ s * (C + b * u) ^ (-p)) (Ioi 0)) :
    (C + b) ^ (-p) * (-1 / (s - p + 1)) ≤ ∫ u in Ioi 0, u ^ s * (C + b * u) ^ (-p) := by
  calc (C + b) ^ (-p) * (-1 / (s - p + 1)) = ∫ u in Ioi 1, (C + b) ^ (-p) * u ^ (s - p) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hs zero_lt_one, Real.one_rpow]
    _ ≤ ∫ u in Ioi 1, u ^ s * (C + b * u) ^ (-p) :=
        setIntegral_mono_on ((integrableOn_Ioi_rpow_of_lt hs zero_lt_one).const_mul _)
          (hI.mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi
          (fun u hu => pointwise_ge hC hb hp (le_of_lt hu))
    _ ≤ _ := by
        refine setIntegral_mono_set hI ?_ (Filter.Eventually.of_forall fun _ hx => Ioi_subset_Ioi
          zero_le_one hx)
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
        have hu' : (0 : ℝ) < u := hu
        simp only [Pi.zero_apply]
        positivity

end HeavyTail

open Radial Barenblatt Distances Wasserstein HeavyTail

/-- `v_∞` has a finite second moment if and only if `m > d/(d+2)` (Section 1.2). -/
theorem integrable_sq_mul_equilibrium_iff' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) :
    Integrable (fun x => ‖x‖ ^ 2 * equilibrium d m x) ↔ (d : ℝ) / (d + 2) < m := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  refine ⟨fun hI => ?_, integrable_sq_mul_equilibrium h⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rcases lt_or_gt_of_ne hm1 with hm | hm
  swap
  · exact lt_trans ((div_lt_one (by linarith)).2 (by linarith)) hm
  by_contra hle
  push Not at hle
  have hp := half_lt_p_full h hm
  have hb := b_full_pos hm hm0
  have hC := fullBarenblattConst_pos hp hb
  set p := 1 / (1 - m)
  set b := (1 - m) / (2 * m)
  set C := fullBarenblattConst d p b
  have hq2 : 2 * p - d ≤ 2 := by
    have h1 : 0 < 1 - m := by linarith
    rw [le_div_iff₀ (by linarith)] at hle
    have : 2 / (1 - m) ≤ d + 2 := by rw [div_le_iff₀ h1]; nlinarith
    have e : 2 * p = 2 / (1 - m) := by simp only [p]; ring
    linarith
  rw [show equilibrium d m = fun x => (C + b * ‖x‖ ^ 2) ^ (-p) from
    funext fun y => by rw [equilibrium_eq_fullBarenblatt h hm]; rfl] at hI
  have hI' : Integrable (fun x : E d => ‖x‖ ^ (2 : ℝ) * (fun u => (C + b * u) ^ (-p)) (‖x‖ ^ 2))
    := by
    simpa only [Real.rpow_two] using hI
  exact not_integrableOn hC hb (by linarith) (s := (d + 2) / 2 - 1) (by linarith)
    ((radial hd _ 2).1.1 hI')

namespace HeavyTail

/-- Abstract heavy-tail argument: let `ν` be a probability measure on `ℝᵈ` whose moments
`N(r) = ∫ |x|ʳ dν` are finite for `r ∈ [q/2, q)` but unbounded. Then every coupling of
`law(aX + h)` and `ν = law(X)` with `0 < a < 1` has infinite quadratic cost. -/
theorem lintegral_cost_eq_top {d : ℕ} (ν : Measure (E d)) [IsProbabilityMeasure ν] {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (h : E d) {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (N : ℝ → ℝ)
    (hN : ∀ r, q / 2 ≤ r → r < q →
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ r) ∂ν = ENNReal.ofReal (N r))
    (hNunb : ∀ K : ℝ, ∃ r, q / 2 ≤ r ∧ r < q ∧ K < N r)
    (γ : Measure (E d × E d)) [IsProbabilityMeasure γ]
    (h1 : γ.map Prod.fst = ν.map (fun y => a • y + h)) (h2 : γ.map Prod.snd = ν) :
    ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ = ⊤ := by
  by_contra hne
  set cost := ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ with hcost
  -- choose `c > 1` with `c² a < 1`
  have hia : 1 < √(1 / a) := by
    rw [Real.lt_sqrt zero_le_one, one_pow, one_lt_div ha0]
    exact ha1
  obtain ⟨c, hc1, hc2⟩ := exists_between hia
  have hca : c * c * a < 1 := by
    have := (Real.lt_sqrt (by linarith)).1 hc2
    rw [lt_div_iff₀ ha0] at this
    nlinarith
  have hc0 : 0 < c := by linarith
  set c' := c / (c - 1) with hc'_def
  have hc' : 1 ≤ c' := by rw [hc'_def, le_div_iff₀ (by linarith)]; linarith
  have hθpos : 0 < c * c * a := by positivity
  set θ0 := (c * c * a) ^ (q / 2)
  have hθ0 : θ0 < 1 := Real.rpow_lt_one hθpos.le hca (by positivity)
  set K := c ^ 2 * c' ^ 2 * (1 + ‖h‖ ^ 2) + c' ^ 2 * (1 + cost.toReal)
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨r, hr1, hr2, hNr⟩ := hNunb (K / (1 - θ0))
  have hr0 : 0 ≤ r := by linarith
  have hr2' : r ≤ 2 := by linarith
  have hNr0 : 0 < N r := lt_of_le_of_lt (div_nonneg hK0 (by linarith)) hNr
  set θ := (c * c * a) ^ r
  have hθ : θ ≤ θ0 := Real.rpow_le_rpow_of_exponent_ge hθpos hca.le hr1
  have hθ0' : 0 ≤ θ := by positivity
  have hmeas : Measurable (fun y : E d => ENNReal.ofReal (‖y‖ ^ r)) := by fun_prop
  have hmeas' : Measurable (fun y : E d => ENNReal.ofReal (c ^ r * ‖y‖ ^ r)) := by fun_prop
  -- the first marginal
  have hfirst : ∫⁻ p, ENNReal.ofReal (c ^ r * ‖p.1‖ ^ r) ∂γ ≤
      ENNReal.ofReal θ * ENNReal.ofReal (N r) +
        ENNReal.ofReal (c ^ 2 * c' ^ 2 * (1 + ‖h‖ ^ 2)) := by
    rw [← lintegral_map hmeas' measurable_fst, h1,
      lintegral_map hmeas' (by fun_prop), ← hN r hr1 hr2, ← lintegral_const_mul _ hmeas]
    calc ∫⁻ y, ENNReal.ofReal (c ^ r * ‖a • y + h‖ ^ r) ∂ν
        ≤ ∫⁻ y, (ENNReal.ofReal θ * ENNReal.ofReal (‖y‖ ^ r) +
            ENNReal.ofReal (c ^ 2 * c' ^ 2 * (1 + ‖h‖ ^ 2))) ∂ν := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul hθ0', ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hy : ‖a • y + h‖ ≤ a * ‖y‖ + ‖h‖ := by
            calc ‖a • y + h‖ ≤ ‖a • y‖ + ‖h‖ := norm_add_le _ _
              _ = a * ‖y‖ + ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg ha0.le]
          have e1 : ‖a • y + h‖ ^ r ≤ c ^ r * (a * ‖y‖) ^ r + c' ^ r * ‖h‖ ^ r :=
            (Real.rpow_le_rpow (norm_nonneg _) hy hr0).trans
              (rpow_add_le (by positivity) (norm_nonneg _) hr0 hc1)
          have e2 : c ^ r * (c ^ r * (a * ‖y‖) ^ r) = θ * ‖y‖ ^ r := by
            simp only [θ]
            rw [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow (by positivity)
              ha0.le, Real.mul_rpow hc0.le hc0.le]
            ring
          have e3 : c ^ r * (c' ^ r * ‖h‖ ^ r) ≤ c ^ 2 * c' ^ 2 * (1 + ‖h‖ ^ 2) := by
            rw [← mul_assoc]
            exact mul_le_mul (mul_le_mul (rpow_le_sq hc1.le hr2') (rpow_le_sq hc' hr2')
              (by positivity) (by positivity)) (rpow_le_one_add_sq (norm_nonneg _) hr0 hr2')
              (by positivity) (by positivity)
          calc c ^ r * ‖a • y + h‖ ^ r
              ≤ c ^ r * (c ^ r * (a * ‖y‖) ^ r + c' ^ r * ‖h‖ ^ r) :=
                mul_le_mul_of_nonneg_left e1 (by positivity)
            _ ≤ _ := by rw [mul_add, e2]; linarith
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  -- the main inequality
  have key : ENNReal.ofReal (N r) ≤ ENNReal.ofReal (θ * N r + K) := by
    calc ENNReal.ofReal (N r) = ∫⁻ p, ENNReal.ofReal (‖p.2‖ ^ r) ∂γ := by
          rw [← hN r hr1 hr2, ← h2, lintegral_map hmeas measurable_snd]
      _ ≤ ∫⁻ p, (ENNReal.ofReal (c ^ r * ‖p.1‖ ^ r) +
            ENNReal.ofReal (c' ^ 2) * (1 + edist p.1 p.2 ^ 2)) ∂γ := by
          refine lintegral_mono fun p => ?_
          rw [edist_sq_eq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hy : ‖p.2‖ ≤ ‖p.1‖ + ‖p.1 - p.2‖ := by
            calc ‖p.2‖ = ‖p.1 - (p.1 - p.2)‖ := by rw [sub_sub_cancel]
              _ ≤ _ := norm_sub_le _ _
          have e1 := (Real.rpow_le_rpow (norm_nonneg _) hy hr0).trans
            (rpow_add_le (norm_nonneg p.1) (norm_nonneg (p.1 - p.2)) hr0 hc1)
          have e2 : c' ^ r * ‖p.1 - p.2‖ ^ r ≤ c' ^ 2 * (1 + ‖p.1 - p.2‖ ^ 2) :=
            mul_le_mul (rpow_le_sq hc' hr2') (rpow_le_one_add_sq (norm_nonneg _) hr0 hr2')
              (by positivity) (by positivity)
          linarith
      _ = ∫⁻ p, ENNReal.ofReal (c ^ r * ‖p.1‖ ^ r) ∂γ +
            ENNReal.ofReal (c' ^ 2) * (1 + cost) := by
          rw [lintegral_add_left (f := fun p : E d × E d => ENNReal.ofReal (c ^ r * ‖p.1‖ ^ r))
            (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal θ * ENNReal.ofReal (N r) +
            ENNReal.ofReal (c ^ 2 * c' ^ 2 * (1 + ‖h‖ ^ 2)) +
            ENNReal.ofReal (c' ^ 2) * (1 + cost) := by gcongr
      _ = ENNReal.ofReal (θ * N r + K) := by
          rw [← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg,
            ← ENNReal.ofReal_mul hθ0', ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          simp only [K]
          ring_nf
  have key' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key
  have : N r * (1 - θ0) ≤ K := by nlinarith
  rw [div_lt_iff₀ (by linarith)] at hNr
  linarith

end HeavyTail

/-- When `(d-2)/d < m ≤ d/(d+2)`, the Wasserstein distance between `v(t)` and `v_∞` is infinite
for every `t > 0` (Section 1.3). -/
theorem wassersteinSq_eq_top' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hmd : ((d : ℝ) - 2) / d < m) (hm2 : m ≤ (d : ℝ) / (d + 2)) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    wassersteinSq (densityMeasure (solution d m x₀ t)) (densityMeasure (equilibrium d m)) = ⊤ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : m < 1 := lt_of_le_of_lt hm2 ((div_lt_one (by linarith)).2 (by linarith))
  have h : Admissible d m := ⟨hd, hm0, hm.ne, hmd⟩
  have hp := half_lt_p_full h hm
  have hb := b_full_pos hm hm0
  have hC := fullBarenblattConst_pos hp hb
  set p := 1 / (1 - m)
  set b := (1 - m) / (2 * m)
  set C := fullBarenblattConst d p b
  set q := 2 * p - d with hq
  have hq0 : 0 < q := by linarith
  have hq2 : q ≤ 2 := by
    have h1 : 0 < 1 - m := by linarith
    rw [le_div_iff₀ (by linarith)] at hm2
    have : 2 / (1 - m) ≤ d + 2 := by rw [div_le_iff₀ h1]; nlinarith
    have e : 2 * p = 2 / (1 - m) := by simp only [p]; ring
    linarith
  have hv := measurable_equilibrium h
  have hv0 := equilibrium_nonneg h
  have hveq : ∀ y, equilibrium d m y = (C + b * ‖y‖ ^ 2) ^ (-p) := fun y => by
    rw [equilibrium_eq_fullBarenblatt h hm]; rfl
  have := (equilibrium_isProbabilityDensity' hd hm0 hm.ne hmd).2
  set ν := densityMeasure (equilibrium d m)
  set N : ℝ → ℝ := fun r => ∫ y, ‖y‖ ^ r * equilibrium d m y
  have hInt : ∀ r, 0 ≤ r → r < q → Integrable (fun y : E d => ‖y‖ ^ r * equilibrium d m y) :=
    fun r hr0 hrq => by
      simp only [hveq]
      exact integrable_rpow_norm_mul_add_sq_rpow_neg hd (by linarith) (by linarith) hC hb
  have hN : ∀ r, q / 2 ≤ r → r < q →
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ r) ∂ν = ENNReal.ofReal (N r) := by
    intro r hr1 hr2
    have hI : Integrable (fun y : E d => ‖y‖ ^ r) ν := by
      rw [integrable_densityMeasure_iff hv hv0]
      simpa only [smul_eq_mul, mul_comm] using hInt r (by linarith) hr2
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ => by positivity),
      integral_densityMeasure hv hv0]
    simp only [smul_eq_mul, N, mul_comm]
  -- the lower bound `N(r) ≥ L / (q - r)`
  set κ := π ^ ((d : ℝ) / 2) / Gamma (d / 2)
  have hκ : 0 < κ := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < d / 2 by positivity)
    positivity
  set L := κ * ((C + b) ^ (-p) * 2)
  have hL : 0 < L := by positivity
  have hlow : ∀ r, 0 ≤ r → r < q → L / (q - r) ≤ N r := by
    intro r hr0 hrq
    have hrad := radial hd (fun u => (C + b * u) ^ (-p)) r
    have hI : IntegrableOn (fun u => u ^ ((d + r) / 2 - 1) * (C + b * u) ^ (-p)) (Ioi 0) :=
      hrad.1.1 (by simpa only [hveq] using hInt r hr0 hrq)
    have hge := integral_ge hC hb (by linarith) (by linarith) hI
    have e : N r = κ * ∫ u in Ioi (0 : ℝ), u ^ ((d + r) / 2 - 1) * (C + b * u) ^ (-p) := by
      simp only [N, hveq]
      exact hrad.2
    rw [e]
    have e2 : L / (q - r) = κ * ((C + b) ^ (-p) * (-1 / ((d + r) / 2 - 1 - p + 1))) := by
      have e3 : (d + r) / 2 - 1 - p + 1 = -((q - r) / 2) := by rw [hq]; ring
      have : q - r ≠ 0 := by linarith
      rw [e3, div_neg, neg_div, neg_neg, one_div_div]
      simp only [L]
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left hge hκ.le
  have hNunb : ∀ K : ℝ, ∃ r, q / 2 ≤ r ∧ r < q ∧ K < N r := by
    intro K
    set η := min (q / 2) (L / (|K| + 1))
    have hη : 0 < η := lt_min (by linarith) (by positivity)
    refine ⟨q - η, by linarith [min_le_left (q / 2) (L / (|K| + 1))], by linarith, ?_⟩
    have h1 := hlow (q - η) (by linarith [min_le_left (q / 2) (L / (|K| + 1))]) (by linarith)
    have h2 : L / (L / (|K| + 1)) ≤ L / (q - (q - η)) := by
      rw [sub_sub_cancel]
      exact div_le_div_of_nonneg_left hL.le hη (min_le_right _ _)
    have h3 : L / (L / (|K| + 1)) = |K| + 1 := by field_simp
    linarith [le_abs_self K]
  -- every coupling has infinite cost
  unfold wassersteinSq
  refine eq_top_iff.2 (le_iInf fun γ => le_iInf fun hγ => le_iInf fun h1 => le_iInf fun h2 => ?_)
  have := hγ
  rw [densityMeasure_solution h x₀ ht] at h1
  rw [lintegral_cost_eq_top ν (scaleFactor_pos h ht) (scaleFactor_lt_one h ht) _ hq0 hq2 N hN
    hNunb γ h1 h2]

/-- `v_∞` has a finite second moment if and only if `m > d/(d+2)` (Section 1.2). -/
alias integrable_sq_mul_equilibrium_iff := integrable_sq_mul_equilibrium_iff'

/-- When `(d-2)/d < m ≤ d/(d+2)`, the Wasserstein distance between `v(t)` and `v_∞` is infinite
for every `t > 0` (Section 1.3). -/
alias wassersteinSq_eq_top := wassersteinSq_eq_top'

end Cutfast
