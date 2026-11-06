/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.PairBound
public import LeanPool.RareSubtreePatterns.Setup.Toolkit

/-!
# Removing the bridge conditioning: Lemma `lem:error_est` and Corollary `cor:pip`

Work package WP5 of the bridge plan. Source lines 1631–1658 (Lemma 4.2, Corollary 4.3),
inventory step P08. Notation: `Ψ_m(x) = walkProb μ m x`, `walkVecLaw μ n` is the law of
`(X_1, …, X_n)`, `bridgeLaw μ n` its conditioning on `S_n = -1`, `qProb`/`pProb` as in
`Bridge/Truncation0.lean`, `π_n = markProb μ G k n`.

## Main statements

* `exists_cond_take_le` (**Lemma `lem:error_est`**, corrected as in F1): one constant `C`
  depending only on the toolkit such that, for `N_n → ∞`, `m_n = o(N_n)`, `z_n = o(a_{N_n})`,
  eventually `P(H(X_1..X_{m_n}) | S_{N_n} = k) ≤ C P(H(X_1..X_{m_n}))` for every compatible
  endpoint `|k| ≤ z_n` (`Ψ_{N_n}(k) ≠ 0`) and every event `H`.
* `cond_walkVecLaw_real_eq`, `qProb_le_inv_mul`: `q ≤ Ψ_n(-1)⁻¹ P(G(𝒯) = 1)` at every `n`.
* `exists_qProb_le_mul_markProb` (**Corollary `cor:pip`**, at every admissible size, F5):
  `q_n ≤ C π_n` for all admissible `n ≥ 1`.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-- **Lemma `lem:error_est`** (source lines 1633–1648), corrected for periodic laws (F1): one
constant `C > 0`, depending only on the toolkit, such that for all total lengths `N_n → ∞`,
window lengths `m_n = o(N_n)` and endpoint ranges `z_n = o(a_{N_n})`, eventually in `n`,
for every endpoint `k` with `|k| ≤ z_n` and `Ψ_{N_n}(k) ≠ 0` and for every event `H` on the
first `m_n` increments,
`P(H(X_1, …, X_{m_n}) | S_{N_n} = k) ≤ C P(H(X_1, …, X_{m_n}))`.

The source's `sup_{|k| ≤ z_n}` ranges over zero-probability endpoints in the periodic case; here
`k` ranges over the compatible endpoints `Ψ_{N_n}(k) ≠ 0`, and the constant is uniform in
`N, m, z, n, k, H`. Proof as in the source: Markov property at time `m_n`
(`cond_real_take`), `Ψ_{N_n}(k) ≥ L / (2 a_{N_n})` (`eventually_bounds`) and
`Ψ_{N_n - m_n} ≤ C / a_{N_n}` (`exists_le_div_of_le_two_mul`). -/
theorem exists_cond_take_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N m : ℕ → ℕ} {z : ℕ → ℝ}, Tendsto N atTop atTop →
      (fun n => (m n : ℝ)) =o[atTop] (fun n => (N n : ℝ)) →
      z =o[atTop] (fun n => a (N n)) →
      ∀ᶠ n in atTop, ∀ k : ℤ, |(k : ℝ)| ≤ z n → walkProb μ (N n) k ≠ 0 →
        ∀ H : List ℤ → Prop,
          (cond (walkVecLaw μ (N n)) {ω | ∑ i, ω i = k}).real
              {ω | H ((List.ofFn ω).take (m n))} ≤
            C * (walkVecLaw μ (m n)).real {ω | H (List.ofFn ω)} := by
  obtain ⟨d, L, hloc⟩ := hT.lattice
  obtain ⟨C₁, hC₁, hle⟩ := hT.exists_le_div_of_le_two_mul
  have hL := hloc.L_pos
  refine ⟨2 * C₁ / L + 1, by positivity, fun {N m z} hN hm hz => ?_⟩
  have hm0 : (fun _ : ℕ => ((0 : ℕ) : ℝ)) =o[atTop] (fun n => (N n : ℝ)) := by simp
  have h2m : ∀ᶠ n in atTop, 2 * m n ≤ N n := by
    filter_upwards [hm.bound (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have : ((2 * m n : ℕ) : ℝ) ≤ N n := by push_cast; linarith
    exact_mod_cast this
  filter_upwards [hT.eventually_bounds hloc hN hm0 hz, h2m, hN.eventually_ge_atTop 1]
    with n hb h2m hN1 k hk hk0 H
  have hmN : m n ≤ N n := by omega
  have hdk : (d : ℤ) ∣ k + ((N n - 0 : ℕ) : ℤ) := by
    simpa using hloc.support (N n) k hk0
  obtain ⟨hlow, -⟩ := hb 0 le_rfl k hdk hk
  simp only [Nat.sub_zero] at hlow
  have haN : 0 < a (N n) := hT.pos _ hN1
  have hpos : 0 < walkProb μ (N n) k := lt_of_lt_of_le (by positivity) hlow
  rw [cond_real_take μ hmN]
  set P := (walkVecLaw μ (m n)).real {ω | H (List.ofFn ω)} with hP
  have hP0 : 0 ≤ P := measureReal_nonneg
  have hint : ∫ b, {b : Fin (m n) → ℤ | H (List.ofFn b)}.indicator 1 b *
      walkProb μ ((N n - m n : ℕ) : ℤ) (k - ∑ i, b i) ∂walkVecLaw μ (m n) ≤
      C₁ / a (N n) * P := by
    have hg : Integrable ({b : Fin (m n) → ℤ | H (List.ofFn b)}.indicator
        (fun _ => C₁ / a (N n))) (walkVecLaw μ (m n)) :=
      (integrable_const _).indicator MeasurableSet.of_discrete
    calc _ ≤ ∫ b, {b : Fin (m n) → ℤ | H (List.ofFn b)}.indicator
          (fun _ => C₁ / a (N n)) b ∂walkVecLaw μ (m n) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun b => ?_) hg
            (Eventually.of_forall fun b => ?_)
          · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) b)
              (walkProb_nonneg μ _ _)
          · dsimp only
            by_cases hb : b ∈ {b : Fin (m n) → ℤ | H (List.ofFn b)}
            · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, Pi.one_apply, one_mul]
              exact hle (N n) (N n - m n) hN1 (by omega) (by omega) _
            · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, zero_mul]
      _ = C₁ / a (N n) * P := by
          rw [integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_comm]
  have hinv : (walkProb μ (N n) k)⁻¹ ≤ 2 * a (N n) / L := by
    calc (walkProb μ (N n) k)⁻¹ ≤ (L / 2 / a (N n))⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 * a (N n) / L := by field_simp
  calc (walkProb μ (N n) k)⁻¹ * ∫ b, {b : Fin (m n) → ℤ | H (List.ofFn b)}.indicator 1 b *
        walkProb μ ((N n - m n : ℕ) : ℤ) (k - ∑ i, b i) ∂walkVecLaw μ (m n)
      ≤ 2 * a (N n) / L * (C₁ / a (N n) * P) := by
        refine mul_le_mul hinv hint ?_ (by positivity)
        exact integral_nonneg fun b => mul_nonneg (Set.indicator_nonneg
          (fun _ _ => zero_le_one) b) (walkProb_nonneg μ _ _)
    _ = 2 * C₁ / L * P := by field_simp
    _ ≤ (2 * C₁ / L + 1) * P := by nlinarith


/-- `P(A | S_n = s) = Ψ_n(s)⁻¹ P(A, S_n = s)` in `ℝ`. -/
theorem cond_walkVecLaw_real_eq (μ : PMF ℕ) (n : ℕ) (s : ℤ) (A : Set (Fin n → ℤ)) :
    (cond (walkVecLaw μ n) {ω | ∑ i, ω i = s}).real A =
      (walkProb μ n s)⁻¹ * (walkVecLaw μ n).real ({ω | ∑ i, ω i = s} ∩ A) := by
  rw [measureReal_def, cond_apply (Set.to_countable _).measurableSet, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, walkProb_natCast]

/-- The crude bound `q ≤ Ψ_n(-1)⁻¹ P(G(𝒯) = 1)`, valid for every `n` and every cutoff. -/
theorem qProb_le_inv_mul (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    qProb μ G M n ≤ (walkProb μ n (-1))⁻¹ * (bienayme μ).real {T | G T} := by
  rw [qProb, bridgeLaw, cond_walkVecLaw_real_eq]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (walkProb_nonneg μ _ _))
  have hsub : {ω : Fin n → ℤ | ∑ i, ω i = -1} ∩ {ω | FirstMarked G M (List.ofFn ω)} ⊆
      {ω | ∃ T ∈ {T : PlaneTree | G T}, ofSeq (List.ofFn ω) = some T} := by
    rintro ω ⟨-, h⟩
    obtain ⟨T, hT, -, hG⟩ := firstMarked_iff.mp h
    exact ⟨T, hG, hT⟩
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    ((measure_mono hsub).trans (walkVecLaw_ofSeq_mem_le μ n _))

/-- **Corollary `cor:pip`** (source lines 1651–1658), at every admissible size (correction F5):
for any sequence `M = o(n)`, there is `C` with `q_n ≤ C π_n` for every admissible `n ≥ 1`.
Neither positivity nor divergence of `M` is needed. -/
theorem exists_qProb_le_mul_markProb (hT : StableToolkit μ α a) (G : ℕ → PlaneTree → Prop)
    (k : ℕ → ℕ) {M : ℕ → ℕ}
    (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → Admissible μ n →
      qProb μ (G (k n)) (M n) n ≤ C * markProb μ G k n := by
  obtain ⟨C₀, hC₀, hbr⟩ := exists_cond_take_le hT
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  have hz : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n => a ((fun n : ℕ => n) n)) := by
    rw [isLittleO_one_left_iff]
    exact tendsto_abs_atTop_atTop.comp hT.tendsto_atTop
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    (hbr (N := fun n => n) (m := M) (z := fun _ => 1) tendsto_id hM hz)
  refine ⟨max C₀ (a n₀ / c), lt_max_of_lt_left hC₀, fun n hn1 hadm => ?_⟩
  have hπ : 0 ≤ markProb μ G k n := measureReal_nonneg
  have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hadm
  rcases le_or_gt n₀ n with h | h
  · have := hn₀ n h (-1) (by simp) hψ.ne' (FirstMarked (G (k n)) (M n))
    simp only [firstMarked_take_iff] at this
    calc qProb μ (G (k n)) (M n) n ≤ C₀ * pProb μ (G (k n)) (M n) := this
      _ ≤ C₀ * markProb μ G k n := mul_le_mul_of_nonneg_left (pProb_le μ _ _) hC₀.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hπ
  · have han := hT.pos n hn1
    have hinv : (walkProb μ n (-1))⁻¹ ≤ a n₀ / c := by
      calc (walkProb μ n (-1))⁻¹ ≤ (c / a n)⁻¹ := inv_anti₀ (by positivity) (hlow n hn1 hψ)
        _ = a n / c := inv_div _ _
        _ ≤ a n₀ / c := by gcongr; exact hT.monotone h.le
    calc qProb μ (G (k n)) (M n) n ≤ (walkProb μ n (-1))⁻¹ * markProb μ G k n :=
          qProb_le_inv_mul μ _ _ n
      _ ≤ a n₀ / c * markProb μ G k n := mul_le_mul_of_nonneg_right hinv hπ
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hπ

end PoissonDeclumping.Bridge
