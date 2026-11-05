/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Rosser
public import LeanPool.IwaniecLinearSieve.LinearSieve.Calculus
public import LeanPool.IwaniecLinearSieve.PrimeSums.Error
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaEleven
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaSeven
import LeanPool.IwaniecLinearSieve.PrimeSums.Lemma13
import LeanPool.IwaniecLinearSieve.SieveMajorants.Lemmas
import LeanPool.IwaniecLinearSieve.SieveMajorants.Properties
import Mathlib.Algebra.Order.Star.Real
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# [I71, Corollaries 1 and 3 to Lemma 13]

With `L = log y` and `t_p = L / log p`, so that the inner level of the recursion at `p` is
`(y/p, p)` with parameter `t_p - 1` (`log (y/p) = log p · (t_p - 1)`).

* `lemma13_param`: Lemma 13 in the variable `t = L / log u`: for `F ≥ 0` antitone on `[α, β]`,
  `|∑_{y^{1/β} ≤ p ≤ y^{1/α}} F(t_p)/p - ∫_α^β F(t)/t dt| ≤ C F(α) pntE(y^{1/β})`
  (substitution `u = e^{L/t}` in `lemma13_mono_of_subset`).
* `cor1`: Corollary 1, for the primes `y^{1/β} ≤ p < y^{1/α}` and any `M ≥ 0` antitone on
  `[α - 1, β - 1]`.
* `cor3`: Corollary 3, for the primes `y^{1/b} ≤ p` in `rosserPrimes lower y (y^{1/s})`
  (the primes of the recursion), uniformly in `sMin lower ≤ s`, with `s₀ = e^{32}` and the upper
  limit `ξ` replaced by any `b ≥ s₀` with `160 b² log⁴ b ≤ L²` and `y^{1/b} ≥ 2`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Finset

namespace IwaniecLinearSieve

/-! ### Lemma 13 in the variable `t = log y / log u` -/
theorem integral_comp_log_div {F : ℝ → ℝ} {y α β : ℝ} (hy : 1 < y) (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ u in y ^ (1 / β)..y ^ (1 / α), F (log y / log u) / (u * log u) =
      ∫ t in α..β, F t / t := by
  set L := log y
  have hL : 0 < L := log_pos hy
  have hy0 : 0 < y := by linarith
  set f : ℝ → ℝ := fun t => exp (L * t⁻¹)
  set f' : ℝ → ℝ := fun t => exp (L * t⁻¹) * (L * -(t ^ 2)⁻¹)
  have hpos : ∀ x ∈ uIcc α β, 0 < x := fun x hx => by
    rw [uIcc_of_le hαβ] at hx; linarith [hx.1]
  have hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x := fun x hx =>
    ((hasDerivAt_inv hx.ne').const_mul L).exp
  have hfA : ∀ γ, f γ = y ^ (1 / γ) := fun γ => by
    simp only [f]; rw [rpow_def_of_pos hy0, one_div]
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := α) (b := β) (f := f)
    (f' := f') (g := fun u => F (L / log u) / (u * log u))
    (continuousOn_of_forall_continuousAt fun x hx => (hderiv x (hpos x hx)).continuousAt)
    (fun x hx => hderiv x (by
      rw [min_eq_left hαβ] at hx; linarith [hx.1]))
    (fun x hx => by
      simp only [f']
      rw [mul_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
        (neg_nonpos.2 (mul_nonneg hL.le (by positivity))))
  rw [hfA, hfA, intervalIntegral.integral_symm (y ^ (1 / β)) (y ^ (1 / α))] at h
  have hcongr : ∫ x in α..β, ((fun u => F (L / log u) / (u * log u)) ∘ f) x * f' x =
      ∫ x in α..β, -(F x / x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 := hpos x hx
    simp only [Function.comp, f, f', log_exp]
    have : L / (L * x⁻¹) = x := by field_simp
    rw [this]
    have := exp_pos (L * x⁻¹)
    field_simp
  rw [hcongr, intervalIntegral.integral_neg, neg_inj] at h
  exact h.symm

theorem log_rpow_one_div {y : ℝ} (hy : 0 < y) (γ : ℝ) : log (y ^ (1 / γ)) = log y / γ := by
  rw [log_rpow hy]; ring

/-- For `u ∈ [y^{1/β}, y^{1/α}]`, `log y / log u ∈ [α, β]`. -/
theorem div_log_mem_Icc {y α β u : ℝ} (hy : 1 < y) (hα : 0 < α) (hαβ : α ≤ β)
    (hu : u ∈ Icc (y ^ (1 / β)) (y ^ (1 / α))) : 0 < log u ∧ log y / log u ∈ Icc α β := by
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hβ : 0 < β := hα.trans_le hαβ
  have hB0 : 0 < y ^ (1 / β) := rpow_pos_of_pos hy0 _
  have hu0 : 0 < u := hB0.trans_le hu.1
  have h1 : log y / β ≤ log u := log_rpow_one_div hy0 β ▸ log_le_log hB0 hu.1
  have h2 : log u ≤ log y / α := log_rpow_one_div hy0 α ▸ log_le_log hu0 hu.2
  have hlu : 0 < log u := (div_pos hL hβ).trans_le h1
  refine ⟨hlu, ?_, ?_⟩
  · rw [le_div_iff₀ hlu]; rw [le_div_iff₀ hα] at h2; linarith
  · rw [div_le_iff₀ hlu]; rw [div_le_iff₀ hβ] at h1; linarith

/-- [I71, Lemma 13] in the variable `t = log y / log u`: for `F ≥ 0` antitone on `[α, β]`, and any
set `S` of primes between those in `(y^{1/β}, y^{1/α})` and those in `[y^{1/β}, y^{1/α}]`,
`|∑_{p ∈ S} F(t_p)/p - ∫_α^β F(t)/t dt| ≤ C F(α) pntE(y^{1/β})`. -/
theorem lemma13_param : ∃ C, 0 ≤ C ∧ ∀ (F : ℝ → ℝ) (y α β : ℝ) (S : Finset ℕ), 1 < y → 0 < α →
    α ≤ β → 2 ≤ y ^ (1 / β) → AntitoneOn F (Icc α β) → (∀ t ∈ Icc α β, 0 ≤ F t) →
    (∀ p ∈ S, p.Prime ∧ y ^ (1 / β) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / α)) →
    (∀ p : ℕ, p.Prime → y ^ (1 / β) < p → (p : ℝ) < y ^ (1 / α) → p ∈ S) →
    |∑ p ∈ S, F (log y / log p) / p - ∫ t in α..β, F t / t| ≤ C * F α * pntE (y ^ (1 / β)) := by
  obtain ⟨C, hC0, hC⟩ := lemma13_mono_of_subset
  refine ⟨C, hC0, fun F y α β S hy hα hαβ hB hF hF0 hS1 hS2 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hBA : y ^ (1 / β) ≤ y ^ (1 / α) :=
    rpow_le_rpow_of_exponent_le hy.le (one_div_le_one_div_of_le hα hαβ)
  have hmono : MonotoneOn (fun u => F (log y / log u)) (Icc (y ^ (1 / β)) (y ^ (1 / α))) := by
    intro u hu v hv huv
    obtain ⟨hlu, hmu⟩ := div_log_mem_Icc hy hα hαβ hu
    obtain ⟨hlv, hmv⟩ := div_log_mem_Icc hy hα hαβ hv
    exact hF hmv hmu (div_le_div_of_nonneg_left hL.le hlu
      (log_le_log (by linarith [hu.1]) huv))
  have h := hC (fun u => F (log y / log u)) (y ^ (1 / α)) (y ^ (1 / β)) S hB hBA hmono
    (fun u hu => hF0 _ (div_log_mem_Icc hy hα hαβ hu).2) hS1 hS2
  rwa [integral_comp_log_div hy hα hαβ, log_rpow_one_div hy0, div_div_cancel₀ hL.ne'] at h

/-! ### Corollary 1 -/
theorem log_div_prime_eq {y : ℝ} {p : ℕ} (hy : 0 < y) (hp : 1 < p) :
    log (y / p) = log p * (log y / log p - 1) := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  rw [log_div hy.ne' (by positivity), mul_sub, mul_div_cancel₀ _ hlp.ne', mul_one]

/-- `log y / log p ≥ α` for `p ≤ y^{1/α}`. -/
theorem le_div_log_of_le_rpow {y α : ℝ} {p : ℕ} (hy : 1 < y) (hα : 0 < α) (hp : 1 < p)
    (hpA : (p : ℝ) ≤ y ^ (1 / α)) : α ≤ log y / log p := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h := log_le_log (by positivity) hpA
  rw [log_rpow_one_div (by linarith)] at h
  rw [le_div_iff₀ hlp]; rw [le_div_iff₀ hα] at h; linarith

theorem antitoneOn_div_sub_one : AntitoneOn (fun t : ℝ => t / (t - 1)) (Ioi 1) := by
  intro u hu v hv huv
  have hu1 : 0 < u - 1 := by linarith [hu.out]
  have hv1 : 0 < v - 1 := by linarith [hv.out]
  simp only
  rw [div_le_div_iff₀ hv1 hu1]; nlinarith

/-- [I71, Corollary 1 to Lemma 13]: for `M ≥ 0` antitone on `[α - 1, β - 1]`, `2 ≤ α ≤ β`,
`y^{1/β} ≥ 2`,
`|∑_{y^{1/β} ≤ p < y^{1/α}} M(t_p - 1)/(p log (y/p)) - L⁻¹ ∫_α^β M(t-1)/(t-1) dt|
  ≤ C M(α - 1) pntE(y^{1/β}) / L`. -/
theorem cor1 : ∃ C, 0 ≤ C ∧ ∀ (M : ℝ → ℝ) (y α β : ℝ), 1 < y → 2 ≤ α → α ≤ β →
    2 ≤ y ^ (1 / β) → AntitoneOn M (Icc (α - 1) (β - 1)) → (∀ t ∈ Icc (α - 1) (β - 1), 0 ≤ M t) →
    |∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
        M (log y / log p - 1) / (p * log (y / p)) -
      (∫ t in α..β, M (t - 1) / (t - 1)) / log y| ≤
      C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by
  obtain ⟨C, hC0, hC⟩ := lemma13_param
  refine ⟨2 * C, by linarith, fun M y α β hy hα hαβ hB hM hM0 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  set F : ℝ → ℝ := fun t => M (t - 1) * (t / (t - 1)) / log y with hFdef
  have hMt : AntitoneOn (fun t => M (t - 1)) (Icc α β) := fun u hu v hv huv =>
    hM ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by linarith [hv.1], by linarith [hv.2]⟩
      (by linarith)
  have hF : AntitoneOn F (Icc α β) := by
    have := antitoneOn_mul_of_nonneg hMt (antitoneOn_div_sub_one.mono fun t ht =>
      show (1 : ℝ) < t by linarith [ht.1])
      (fun t ht => hM0 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      fun t ht => div_nonneg (by linarith [ht.1]) (by linarith [ht.1])
    exact fun u hu v hv huv => div_le_div_of_nonneg_right (this hu hv huv) hL.le
  have hF0 : ∀ t ∈ Icc α β, 0 ≤ F t := fun t ht =>
    div_nonneg (mul_nonneg (hM0 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (div_nonneg (by linarith [ht.1]) (by linarith [ht.1]))) hL.le
  have h := hC F y α β ((primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p)) hy
    (by linarith) hαβ hB hF hF0
    (fun p hp => by
      rw [mem_filter, mem_primesLT] at hp
      exact ⟨hp.1.1, hp.2, hp.1.2.le⟩)
    (fun p hp h1 h2 => by
      rw [mem_filter, mem_primesLT]; exact ⟨⟨hp, h2⟩, h1.le⟩)
  have hsum : ∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
      F (log y / log p) / p = ∑ p ∈ (primesLT (y ^ (1 / α))).filter
        (fun p : ℕ => y ^ (1 / β) ≤ p), M (log y / log p - 1) / (p * log (y / p)) := by
    refine sum_congr rfl fun p hp => ?_
    rw [mem_filter, mem_primesLT] at hp
    have hp1 := hp.1.1.one_lt
    have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp1)
    have ht := le_div_log_of_le_rpow hy (by linarith) hp1 hp.1.2.le
    rw [log_div_prime_eq hy0 hp1]
    simp only [F]
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp
  have hint : ∫ t in α..β, F t / t = (∫ t in α..β, M (t - 1) / (t - 1)) / log y := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hαβ] at ht
    have : 0 < t := by linarith [ht.1]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    simp only [F]
    field_simp
  have hFα : F α ≤ 2 * M (α - 1) / log y := by
    have hMα := hM0 (α - 1) ⟨le_rfl, by linarith⟩
    have : α / (α - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    simp only [F]
    exact div_le_div_of_nonneg_right (by nlinarith) hL.le
  rw [hsum, hint] at h
  refine h.trans ?_
  calc C * F α * pntE (y ^ (1 / β)) ≤ C * (2 * M (α - 1) / log y) * pntE (y ^ (1 / β)) := by
        have := pntE_pos (y ^ (1 / β))
        gcongr
    _ = 2 * C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by ring

/-- [I71, Corollary 1 to Lemma 13], one-sided form. -/
theorem cor1_le : ∃ C, 0 ≤ C ∧ ∀ (M : ℝ → ℝ) (y α β : ℝ), 1 < y → 2 ≤ α → α ≤ β →
    2 ≤ y ^ (1 / β) → AntitoneOn M (Icc (α - 1) (β - 1)) → (∀ t ∈ Icc (α - 1) (β - 1), 0 ≤ M t) →
    ∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
        M (log y / log p - 1) / (p * log (y / p)) ≤
      (∫ t in α..β, M (t - 1) / (t - 1)) / log y + C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by
  obtain ⟨C, hC0, hC⟩ := cor1
  exact ⟨C, hC0, fun M y α β hy hα hαβ hB hM hM0 => by
    linarith [(abs_le.1 (hC M y α β hy hα hαβ hB hM hM0)).2]⟩

/-! ### Corollary 3 -/

/-- `G'(s-1) s²/(s-1)² ≤ 32 s² G(s)` for `s ≥ 2` (Lemma 8 and the Corollary to Lemma 6). -/
theorem errMaj_shift_sq_le (lower lower' : Bool) {s : ℝ} (hs : 2 ≤ s) :
    errMaj lower' (s - 1) * (s ^ 2 / (s - 1) ^ 2) ≤ 32 * s ^ 2 * errMaj lower s := by
  have hs1 : 0 < s - 1 := by linarith
  have hq : s ^ 2 / (s - 1) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (pow_pos hs1 2)]; nlinarith
  have hq0 : 0 ≤ s ^ 2 / (s - 1) ^ 2 := by positivity
  have hG' := errMaj_pos lower' (s - 1)
  have hG := (errMaj_mem lower s).1
  have h8 : errMaj lower' (s - 1) ≤ 8 * s ^ 2 * errMaj lower s := by
    rcases le_total 3 s with h3 | h3
    · have := (errMaj_mem lower' (s - 1)).2
      have := bigM_sub_one_lt h3
      nlinarith
    · have := errMaj_le_two lower' (s - 1)
      have hB : bigM 3 ≤ bigM s := bigM_antitone h3
      have := bigM_three_gt
      have : 1 / 2 ≤ errMaj lower s := by linarith
      nlinarith
  calc errMaj lower' (s - 1) * (s ^ 2 / (s - 1) ^ 2) ≤ 8 * s ^ 2 * errMaj lower s * 4 :=
        mul_le_mul h8 hq hq0 (by have := errMaj_pos lower s; positivity)
    _ = 32 * s ^ 2 * errMaj lower s := by ring

/-- `(1 + t² log⁵ t / L²)^{5(t-1)} ≤ δ(a, y)` for `1 ≤ t ≤ a`. -/
theorem growth_le_delta {y t a : ℝ} (ht : 1 ≤ t) (hta : t ≤ a) :
    (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) ≤ delta a y := by
  have hlt := log_nonneg ht
  have hla : log t ≤ log a := log_le_log (by linarith) hta
  have hx0 := lsx_nonneg (log y) ht
  have hxa : t ^ 2 * log t ^ 5 / log y ^ 2 ≤ a ^ 2 * log a ^ 5 / log y ^ 2 := by
    gcongr
  rw [delta]
  calc (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1))
      ≤ (1 + a ^ 2 * log a ^ 5 / log y ^ 2) ^ (5 * (t - 1)) :=
        rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- The summand of Corollary 3: with `t = t_p ≥ 2`, `log (y/p) = L (t-1)/t`, so
`δ(t - 1, y/p) G(t-1) / (p log² (y/p))
  ≤ (1 + t² log⁵ t / L²)^{5(t-1)} G(t-1) (t²/(t-1)²) / L² / p`. -/
theorem cor3_summand_le {G : ℝ → ℝ} {y : ℝ} {p : ℕ} (hy : 1 < y) (hp : 1 < p)
    (ht : 2 ≤ log y / log p) (hG : 0 ≤ G (log y / log p - 1)) :
    delta (log y / log p - 1) (y / p) * G (log y / log p - 1) / (p * log (y / p) ^ 2) ≤
      (1 + (log y / log p) ^ 2 * log (log y / log p) ^ 5 / log y ^ 2) ^
        (5 * (log y / log p - 1)) * G (log y / log p - 1) *
        ((log y / log p) ^ 2 / (log y / log p - 1) ^ 2) / log y ^ 2 / p := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have hy0 : 0 < y := by linarith
  have hyp := log_div_prime_eq hy0 hp
  set t := log y / log p with htdef
  have hLt : log y = log p * t := by rw [htdef]; field_simp
  have ht1 : 0 < t - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by positivity
  have hb : (t - 1) ^ 2 * log (t - 1) ^ 5 / log (y / p) ^ 2 =
      t ^ 2 * log (t - 1) ^ 5 / log y ^ 2 := by
    rw [hyp, hLt]; field_simp
  have hl1 : 0 ≤ log (t - 1) := log_nonneg (by linarith)
  have hl2 : log (t - 1) ≤ log t := log_le_log ht1 (by linarith)
  have hbase : t ^ 2 * log (t - 1) ^ 5 / log y ^ 2 ≤ t ^ 2 * log t ^ 5 / log y ^ 2 := by
    gcongr
  have hb0 : 0 ≤ t ^ 2 * log (t - 1) ^ 5 / log y ^ 2 := by positivity
  rw [delta, hb]
  have hrest : G (t - 1) / (p * log (y / p) ^ 2) =
      G (t - 1) * (t ^ 2 / (t - 1) ^ 2) / log y ^ 2 / p := by
    rw [hyp, hLt]; field_simp
  calc (1 + t ^ 2 * log (t - 1) ^ 5 / log y ^ 2) ^ (5 * (t - 1)) * G (t - 1) /
        (p * log (y / p) ^ 2)
      = (1 + t ^ 2 * log (t - 1) ^ 5 / log y ^ 2) ^ (5 * (t - 1)) *
          (G (t - 1) / (p * log (y / p) ^ 2)) := by ring
    _ ≤ (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) *
          (G (t - 1) / (p * log (y / p) ^ 2)) := by
        gcongr
    _ = _ := by rw [hrest]; ring

theorem errMaj_not_eq_majG (lower : Bool) : errMaj (!lower) = majG (if lower then 1 else 0) := by
  cases lower
  · simp [majG_of_even (⟨0, rfl⟩ : Even 0)]
  · simp [majG_of_odd odd_one]

theorem errMaj_eq_majG_succ (lower : Bool) :
    errMaj lower = majG ((if lower then 1 else 0) + 1) := by
  cases lower
  · simp [majG_of_odd odd_one]
  · simp [majG_of_even (⟨1, rfl⟩ : Even 2)]

/-- Corollary 3 on `[s, b]` with `e^{32} ≤ s` (Lemmas 11, 12 and 13). `S` is any set of primes
between those in `(y^{1/b}, y^{1/s})` and those in `[y^{1/b}, y^{1/s}]`. -/
theorem cor3_large : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s b : ℝ) (S : Finset ℕ), 1 < y →
    exp 32 ≤ s → s ≤ b → 2 ≤ y ^ (1 / b) → b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160 →
    (∀ p ∈ S, p.Prime ∧ y ^ (1 / b) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / s)) →
    (∀ p : ℕ, p.Prime → y ^ (1 / b) < p → (p : ℝ) < y ^ (1 / s) → p ∈ S) →
    ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
        (p * log (y / p) ^ 2) ≤
      delta s y * errMaj lower s / log y ^ 2 * (1 + C * b ^ 2 * pntE (y ^ (1 / b))) := by
  obtain ⟨C, hC0, hC⟩ := lemma13_param
  refine ⟨32 * C, by linarith, fun lower y s b S hy hs hsb hB hb hS1 hS2 => ?_⟩
  set r : ℕ := if lower then 1 else 0
  have hG' := errMaj_not_eq_majG lower
  have hGs : errMaj lower s = majG (r + 1) s := by rw [errMaj_eq_majG_succ]
  have hL : 0 < log y := log_pos hy
  have hL2 : 0 < log y ^ 2 := by positivity
  have hs4 := four_lt_of_exp_le hs
  set Φ : ℝ → ℝ := fun t => (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) *
    (t ^ 2 / (t - 1) ^ 2) / log y ^ 2 with hΦdef
  have hΦ : AntitoneOn Φ (Icc s b) := fun u hu v hv huv =>
    div_le_div_of_nonneg_right (antitoneOn_cor3Weight r hs hb hu hv huv) hL2.le
  have hΦ0 : ∀ t ∈ Icc s b, 0 ≤ Φ t := fun t ht => by
    have ht1 : (1 : ℝ) ≤ t := by linarith [ht.1]
    have := lsx_nonneg (log y) ht1
    have := majG_pos r (t - 1)
    exact div_nonneg (mul_nonneg (mul_nonneg (rpow_pos_of_pos (by linarith) _).le this.le)
      (by positivity)) hL2.le
  have h13 := hC Φ y s b S hy (by linarith) hsb hB hΦ hΦ0 hS1 hS2
  have hsum : ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
      (p * log (y / p) ^ 2) ≤ ∑ p ∈ S, Φ (log y / log p) / p := by
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hpp, hpB, hpA⟩ := hS1 p hp
    have ht := (div_log_mem_Icc hy (by linarith) hsb ⟨hpB, hpA⟩).2
    rw [hG']
    exact cor3_summand_le hy hpp.one_lt (by linarith [ht.1]) (majG_pos _ _).le
  have hint : ∫ t in s..b, Φ t / t = (∫ t in s..b, (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^
      (5 * (t - 1)) * majG r (t - 1) * t / (t - 1) ^ 2) / log y ^ 2 := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hsb] at ht
    have : t ≠ 0 := by linarith [ht.1]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    simp only [Φ]
    field_simp
  have h11 := lemma11 r hs hsb hb
  have hΦs : Φ s ≤ delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2 := by
    have h1 := growth_le_delta (y := y) (by linarith : (1 : ℝ) ≤ s) le_rfl
    have h2 := errMaj_shift_sq_le lower (!lower) (by linarith : (2 : ℝ) ≤ s)
    rw [hG', hGs] at h2
    have h3 : 0 ≤ majG r (s - 1) * (s ^ 2 / (s - 1) ^ 2) := by
      have := majG_pos r (s - 1); positivity
    change (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * (s - 1)) * majG r (s - 1) *
      (s ^ 2 / (s - 1) ^ 2) / log y ^ 2 ≤ _
    rw [mul_assoc _ (majG r (s - 1))]
    exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 h3 (delta_pos (by linarith) y).le)
      hL2.le
  rw [abs_le] at h13
  rw [hint] at h13
  have hpE := pntE_pos (y ^ (1 / b))
  have hδ := delta_pos (by linarith : (1 : ℝ) ≤ s) y
  have hG := majG_pos (r + 1) s
  have hsb2 : s ^ 2 ≤ b ^ 2 := by gcongr
  rw [hGs]
  have e1 : C * Φ s * pntE (y ^ (1 / b)) ≤
      C * (delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2) * pntE (y ^ (1 / b)) := by
    gcongr
  have e2 : C * (delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2) * pntE (y ^ (1 / b)) ≤
      delta s y * majG (r + 1) s / log y ^ 2 * (32 * C * b ^ 2 * pntE (y ^ (1 / b))) := by
    have h0 : 0 ≤ C * delta s y * majG (r + 1) s * pntE (y ^ (1 / b)) * 32 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hδ.le) hG.le) hpE.le) (by norm_num)
    calc C * (delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2) * pntE (y ^ (1 / b))
        = C * delta s y * majG (r + 1) s * pntE (y ^ (1 / b)) * 32 * s ^ 2 / log y ^ 2 := by
          ring
      _ ≤ C * delta s y * majG (r + 1) s * pntE (y ^ (1 / b)) * 32 * b ^ 2 / log y ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsb2 h0) hL2.le
      _ = _ := by ring
  have e3 : (∫ t in s..b, (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) *
      majG r (t - 1) * t / (t - 1) ^ 2) / log y ^ 2 ≤ delta s y * majG (r + 1) s / log y ^ 2 :=
    div_le_div_of_nonneg_right h11.le hL2.le
  calc _ ≤ ∑ p ∈ S, Φ (log y / log p) / p := hsum
    _ ≤ _ := by nlinarith

/-- Corollary 3 on `[s, a]` with `a ≤ e^{32}`: here `δ(t_p - 1, y/p) ≤ δ(e^{32}, y)` and Lemma 13
is applied to `G'(t-1) t²/(t-1)²` directly. -/
theorem cor3_small : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s a : ℝ) (S : Finset ℕ), 1 < y →
    errLower lower ≤ s → s ≤ a → a ≤ exp 32 → 2 ≤ y ^ (1 / a) →
    (∀ p ∈ S, p.Prime ∧ y ^ (1 / a) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / s)) →
    (∀ p : ℕ, p.Prime → y ^ (1 / a) < p → (p : ℝ) < y ^ (1 / s) → p ∈ S) →
    ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
        (p * log (y / p) ^ 2) ≤
      delta (exp 32) y / log y ^ 2 *
        (errMaj lower s - errMaj lower a + C * s ^ 2 * errMaj lower s * pntE (y ^ (1 / a))) := by
  obtain ⟨C, hC0, hC⟩ := lemma13_param
  refine ⟨32 * C, by linarith, fun lower y s a S hy hs hsa ha hB hS1 hS2 => ?_⟩
  have hs2 : 2 ≤ s := (two_le_errLower lower).trans hs
  have hL : 0 < log y := log_pos hy
  have hL2 : 0 < log y ^ 2 := by positivity
  set F : ℝ → ℝ := fun t => errMaj (!lower) (t - 1) * (t ^ 2 / (t - 1) ^ 2) with hFdef
  have hF : AntitoneOn F (Icc s a) :=
    antitoneOn_mul_of_nonneg (fun u _ v _ huv => errMaj_antitone _ (by linarith))
      (antitoneOn_sq_div_sq_sub_one.mono fun t ht => show (1 : ℝ) < t by linarith [ht.1])
      (fun t _ => (errMaj_pos _ _).le) fun t _ => by positivity
  have hF0 : ∀ t ∈ Icc s a, 0 ≤ F t := fun t _ => by
    have := errMaj_pos (!lower) (t - 1); positivity
  have h13 := hC F y s a S hy (by linarith) hsa hB hF hF0 hS1 hS2
  have hδ0 : 0 ≤ delta (exp 32) y :=
    (delta_pos (by linarith [four_lt_of_exp_le (le_refl (exp 32))]) y).le
  have hsum : ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
      (p * log (y / p) ^ 2) ≤ delta (exp 32) y / log y ^ 2 * ∑ p ∈ S, F (log y / log p) / p := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hpp, hpB, hpA⟩ := hS1 p hp
    have ht := (div_log_mem_Icc hy (by linarith) hsa ⟨hpB, hpA⟩).2
    refine (cor3_summand_le hy hpp.one_lt (by linarith [ht.1]) (errMaj_pos _ _).le).trans ?_
    have hg := growth_le_delta (y := y) (by linarith [ht.1] : (1 : ℝ) ≤ log y / log p)
      (ht.2.trans ha)
    have hF1 : 0 ≤ F (log y / log p) := hF0 _ ht
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc _ = (1 + (log y / log p) ^ 2 * log (log y / log p) ^ 5 / log y ^ 2) ^
            (5 * (log y / log p - 1)) * F (log y / log p) / log y ^ 2 / p := by
          simp only [F]; ring
      _ ≤ delta (exp 32) y * F (log y / log p) / log y ^ 2 / p := by gcongr
      _ = _ := by ring
  have hint : ∫ t in s..a, F t / t = errMaj lower s - errMaj lower a := by
    rw [← integral_errMaj_shift lower hs hsa]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hsa] at ht
    have : t ≠ 0 := by linarith [ht.1]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    simp only [F]
    field_simp
  have hFs : F s ≤ 32 * s ^ 2 * errMaj lower s := errMaj_shift_sq_le lower (!lower) hs2
  rw [abs_le, hint] at h13
  have hpE := pntE_pos (y ^ (1 / a))
  have hmain : ∑ p ∈ S, F (log y / log p) / p ≤
      errMaj lower s - errMaj lower a + 32 * C * s ^ 2 * errMaj lower s * pntE (y ^ (1 / a)) := by
    have : C * F s * pntE (y ^ (1 / a)) ≤
        C * (32 * s ^ 2 * errMaj lower s) * pntE (y ^ (1 / a)) := by gcongr
    linarith [h13.2]
  calc _ ≤ _ := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (div_nonneg hδ0 hL2.le)

theorem rpow_one_div_le_rpow_one_div {y u v : ℝ} (hy : 1 ≤ y) (hu : 0 < u) (huv : u ≤ v) :
    y ^ (1 / v) ≤ y ^ (1 / u) :=
  rpow_le_rpow_of_exponent_le hy (one_div_le_one_div_of_le hu huv)

/-- [I71, Corollary 3 to Lemma 13] for the primes `y^{1/b} ≤ p < y^{1/s}`, `errLower lower ≤ s`
(so `s ≥ 2`, and `s ≥ 3` for the upper sieve, where (3.13) holds). -/
theorem cor3_primesLT : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s b : ℝ), 1 < y →
    errLower lower ≤ s → exp 32 ≤ b → 2 ≤ y ^ (1 / b) → b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160 →
    ∑ p ∈ (primesLT (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * b ^ 2 * pntE (y ^ (1 / b))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := cor3_large
  obtain ⟨C₂, hC₂, h₂⟩ := cor3_small
  refine ⟨C₁ + C₂, by linarith, fun lower y s b hy hs hb32 hB hb => ?_⟩
  set s₀ := exp 32 with hs₀
  have hs2 : 2 ≤ s := (two_le_errLower lower).trans hs
  have hs₀4 : 4 < s₀ := four_lt_of_exp_le le_rfl
  have hL2 : 0 < log y ^ 2 := by have := log_pos hy; positivity
  have hpE := pntE_pos (y ^ (1 / b))
  have hGs := errMaj_pos lower s
  set S := (primesLT (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p) with hS
  have hRHS : 0 ≤ delta (max s s₀) y * errMaj lower s / log y ^ 2 *
      (1 + (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b))) := by
    have := delta_pos (by linarith [le_max_left s s₀] : (1 : ℝ) ≤ max s s₀) y
    have : 0 ≤ (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b)) :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg b)) hpE.le
    positivity
  rcases lt_or_ge b s with hbs | hsb
  · -- no primes
    have hempty : S = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      rw [hS, mem_filter, mem_primesLT] at hp
      have := rpow_one_div_le_rpow_one_div hy.le (by linarith) hbs.le
      linarith [hp.1.2, hp.2]
    rw [hempty, sum_empty]
    exact hRHS
  rcases le_total s₀ s with hs₀s | hss₀
  · -- `s ≥ s₀`: Lemma 11 directly
    rw [max_eq_left hs₀s]
    refine (h₁ lower y s b S hy hs₀s hsb hB hb (fun p hp => ?_) fun p hp h1 h2 => ?_).trans ?_
    · rw [hS, mem_filter, mem_primesLT] at hp; exact ⟨hp.1.1, hp.2, hp.1.2.le⟩
    · rw [hS, mem_filter, mem_primesLT]; exact ⟨⟨hp, h2⟩, h1.le⟩
    · have := delta_pos (by linarith : (1 : ℝ) ≤ s) y
      gcongr
      linarith
  -- `s < s₀`: split at `y^{1/s₀}`
  rw [max_eq_right hss₀]
  have hB₀ : y ^ (1 / b) ≤ y ^ (1 / s₀) := rpow_one_div_le_rpow_one_div hy.le (by linarith) hb32
  have hB₀s : y ^ (1 / s₀) ≤ y ^ (1 / s) := rpow_one_div_le_rpow_one_div hy.le (by linarith) hss₀
  rw [← sum_filter_add_sum_filter_not S (fun p : ℕ => y ^ (1 / s₀) ≤ p)]
  have e₁ := h₂ lower y s s₀ (S.filter fun p : ℕ => y ^ (1 / s₀) ≤ p) hy hs hss₀ le_rfl
    (by linarith) (fun p hp => by
      rw [mem_filter, hS, mem_filter, mem_primesLT] at hp
      exact ⟨hp.1.1.1, hp.2, hp.1.1.2.le⟩)
    (fun p hp h1 h2 => by
      rw [mem_filter, hS, mem_filter, mem_primesLT]
      exact ⟨⟨⟨hp, h2⟩, by linarith⟩, h1.le⟩)
  have e₂ := h₁ lower y s₀ b (S.filter fun p : ℕ => ¬ y ^ (1 / s₀) ≤ p) hy le_rfl hb32 hB hb
    (fun p hp => by
      rw [mem_filter, hS, mem_filter, mem_primesLT] at hp
      exact ⟨hp.1.1.1, hp.1.2, (not_le.1 hp.2).le⟩)
    (fun p hp h1 h2 => by
      rw [mem_filter, hS, mem_filter, mem_primesLT]
      exact ⟨⟨⟨hp, by linarith⟩, h1.le⟩, not_le.2 h2⟩)
  refine (add_le_add e₁ e₂).trans ?_
  -- combine
  have hδ := delta_pos (by linarith : (1 : ℝ) ≤ s₀) y
  have hG₀ := errMaj_pos lower s₀
  have hGG : errMaj lower s₀ ≤ errMaj lower s := errMaj_antitone lower hss₀
  have hpE₀ : pntE (y ^ (1 / s₀)) ≤ pntE (y ^ (1 / b)) :=
    pntE_le_pntE (by linarith) hB₀
  have hsb2 : s ^ 2 * pntE (y ^ (1 / s₀)) ≤ b ^ 2 * pntE (y ^ (1 / b)) := by
    have : s ^ 2 ≤ b ^ 2 := by gcongr
    exact mul_le_mul this hpE₀ (pntE_pos _).le (sq_nonneg b)
  have i1 : C₂ * errMaj lower s * (s ^ 2 * pntE (y ^ (1 / s₀))) ≤
      C₂ * errMaj lower s * (b ^ 2 * pntE (y ^ (1 / b))) :=
    mul_le_mul_of_nonneg_left hsb2 (mul_nonneg hC₂ hGs.le)
  have i2 : C₁ * (b ^ 2 * pntE (y ^ (1 / b))) * errMaj lower s₀ ≤
      C₁ * (b ^ 2 * pntE (y ^ (1 / b))) * errMaj lower s :=
    mul_le_mul_of_nonneg_left hGG (mul_nonneg hC₁ (mul_nonneg (sq_nonneg b) hpE.le))
  have hinner : errMaj lower s - errMaj lower s₀ +
      C₂ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / s₀)) +
      errMaj lower s₀ * (1 + C₁ * b ^ 2 * pntE (y ^ (1 / b))) ≤
      errMaj lower s * (1 + (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b))) := by
    nlinarith
  have hk : 0 ≤ delta s₀ y / log y ^ 2 := div_nonneg hδ.le hL2.le
  calc delta s₀ y / log y ^ 2 * (errMaj lower s - errMaj lower s₀ +
        C₂ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / s₀))) +
      delta s₀ y * errMaj lower s₀ / log y ^ 2 * (1 + C₁ * b ^ 2 * pntE (y ^ (1 / b)))
      = delta s₀ y / log y ^ 2 * (errMaj lower s - errMaj lower s₀ +
        C₂ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / s₀)) +
        errMaj lower s₀ * (1 + C₁ * b ^ 2 * pntE (y ^ (1 / b)))) := by ring
    _ ≤ delta s₀ y / log y ^ 2 *
        (errMaj lower s * (1 + (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b)))) :=
        mul_le_mul_of_nonneg_left hinner hk
    _ = _ := by ring

/-- `p < y^{1/max s 3} ↔ p < y^{1/s} ∧ p³ < y` (for `y > 1`, `s > 0`, `p ≥ 0`). -/
theorem lt_rpow_one_div_max_three {y s x : ℝ} (hy : 1 < y) (hs : 0 < s) (hx : 0 ≤ x) :
    x < y ^ (1 / max s 3) ↔ x < y ^ (1 / s) ∧ x ^ 3 < y := by
  have h3 : x < y ^ (1 / (3 : ℝ)) ↔ x ^ 3 < y := by
    rw [one_div, lt_rpow_inv_iff_of_pos hx (by linarith) (by norm_num)]
    norm_cast
  rcases le_total s 3 with hs3 | hs3
  · rw [max_eq_right hs3, h3]
    have := rpow_one_div_le_rpow_one_div hy.le hs hs3
    constructor
    · intro h; exact ⟨lt_of_lt_of_le (h3.2 h) this, h⟩
    · exact fun h => h.2
  · rw [max_eq_left hs3]
    have := rpow_one_div_le_rpow_one_div hy.le (by norm_num) hs3
    exact ⟨fun h => ⟨h, h3.1 (lt_of_lt_of_le h this)⟩, fun h => h.1⟩

/-- [I71, Corollary 3 to Lemma 13], for the primes of the Rosser recursion: with
`t_p = log y / log p`, `s₀ = e^{32}`, `sMin lower ≤ s`, any `b ≥ s₀` with `y^{1/b} ≥ 2` and
`160 b² log⁴ b ≤ log² y` (e.g. `b = ξ(y)` for large `y`, `exists_xi_large`),

`∑_{p ∈ rosserPrimes lower y (y^{1/s}), p ≥ y^{1/b}}
    δ(t_p - 1, y/p) G(!lower)(t_p - 1) / (p log² (y/p))
  ≤ δ(max s s₀, y) G(lower)(s) / L² · (1 + C b² pntE(y^{1/b}))`.

For the upper sieve and `s < 3` the primes are those `< y^{1/3}` and `𝔉(s) = 𝔉(3) = 1`, so this
reduces to `s = 3`. -/
theorem cor3 : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s b : ℝ), 1 < y → sMin lower ≤ s →
    exp 32 ≤ b → 2 ≤ y ^ (1 / b) → b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160 →
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * b ^ 2 * pntE (y ^ (1 / b))) := by
  obtain ⟨C, hC0, hC⟩ := cor3_primesLT
  refine ⟨C, hC0, fun lower y s b hy hs hb32 hB hb => ?_⟩
  cases lower
  · -- upper sieve: replace `s` by `max s 3`
    have hs1 : (1 : ℝ) ≤ s := hs
    have hset : (rosserPrimes false y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p) =
        (primesLT (y ^ (1 / max s 3))).filter (fun p : ℕ => y ^ (1 / b) ≤ p) := by
      ext p
      simp only [mem_filter, mem_rosserPrimes, mem_primesLT, Bool.false_eq_true, false_or]
      rw [lt_rpow_one_div_max_three hy (by linarith) (Nat.cast_nonneg p)]
      tauto
    have hG : errMaj false (max s 3) = errMaj false s := by
      rcases le_total s 3 with h | h
      · rw [max_eq_right h, errMaj_false_of_le_three le_rfl, errMaj_false_of_le_three h]
      · rw [max_eq_left h]
    have hmax : max (max s 3) (exp 32) = max s (exp 32) := by
      have : (3 : ℝ) ≤ exp 32 := by linarith [four_lt_of_exp_le (le_refl (exp 32))]
      rw [max_assoc, max_eq_right this]
    rw [hset, ← hG, ← hmax]
    exact hC false y (max s 3) b hy (le_max_right _ _) hb32 hB hb
  · rw [rosserPrimes_true]
    exact hC true y s b hy hs hb32 hB hb

/-- The hypothesis `160 b² log⁴ b ≤ L²` passes to smaller `b ≥ 1`. -/
theorem sq_mul_log_pow_four_le_of_le {b b' X : ℝ} (hb : 1 ≤ b) (hbb' : b ≤ b')
    (h : b' ^ 2 * log b' ^ 4 ≤ X) : b ^ 2 * log b ^ 4 ≤ X := by
  have := log_nonneg hb
  have : log b ≤ log b' := log_le_log (by linarith) hbb'
  have : b ^ 2 * log b ^ 4 ≤ b' ^ 2 * log b' ^ 4 := by gcongr
  linarith

/-- Corollary 3 with `b = ξ(y)`, for `y ≥ y₀`. -/
theorem cor3_xi : ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ (lower : Bool) (y s : ℝ), y₀ ≤ y → sMin lower ≤ s →
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) := by
  obtain ⟨C, hC0, hC⟩ := cor3
  obtain ⟨y₀, hy₀⟩ := exists_xi_large
  refine ⟨C, y₀, hC0, fun lower y s hy hs => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hy₀ y hy
  exact hC lower y s (xi y) h1 hs h2 h4 h3

end IwaniecLinearSieve
