/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.ErrorTerms

import LeanPool.RareSubtreePatterns.Bridge.CriterionM
import LeanPool.RareSubtreePatterns.Bridge.Microscopic
import LeanPool.RareSubtreePatterns.RegularVariation.Consequences

/-!
# Boundary cases: Lemma `lem:extreme_means`

Work package WP7 (first half) of the bridge plan. Source lines 1997–2089 (Lemma 4.10, proof step
`P13`). Notation as in `Bridge/Truncation.lean` and `Bridge/ErrorTerms.lean`:
`W_n^M = cyclicSum (G (k n)) (M n) (List.ofFn ω)` under `bridgeLaw μ n = P(· | S_n = -1)`,
`I_{i+1}^{(M)} = 1_{cycEvent G M n i}`, `q_n = qProb`, `p_n = pProb`, `π_n = markProb μ G k n`.
The paper writes `μ_n = n q_n` (line 2024); here that is `n * qProb …` (correction F15: `μ` is
the offspring law).

## Main statements

* `walkVecLaw_real_two_blocks_inter_sum_le`: the two-block Markov formula
  (`walkVecLaw_real_two_blocks_inter_sum`) under a uniform bound on `Ψ_{n-m₁-m₂}`, giving
  `P(H₁(X_1..X_{m₁}), H₂(X_{j+1}..X_{j+m₂}), S_n = s) ≤ K P(H₁) P(H₂)`.
* `eventually_pairBridge_le` (**separated pairs**, source lines 2042–2079): for every `δ > 0`,
  eventually along admissible sizes, `P(I_1 = I_{1+ℓ} = 1 | S_n = -1) ≤ (1 + δ) p_n²` uniformly
  for `M_n ≤ ℓ ≤ n - M_n`. Only the toolkit and the cutoff are used. The two blocks are
  independent only under the unconditioned law; the bridge weight
  `Ψ_{n-2M_n}(-1 - S_{M_n} - Z) / Ψ_n(-1)` is `≤ 1 + δ` on the good blocks
  (`|S| ≤ r_n` and `S ≡ -M_n (mod d)`, compatible endpoints, F4/F15) and bounded on the bad
  blocks, whose probability is `o(p_n)` (Lemma `lem:pnqn`(i)).
* `integral_cyclicSum_sq`, `bridgeLaw_real_le_abs_cyclicSum_sub_le` (Chebyshev),
  `sum_sum_cycEvent_inter_le` (diagonal + nearby + separated pairs).
* `exists_eventually_errorB2_le`, `eventually_errorB2_le` (**nearby pairs**, source lines
  2029–2040): `b_2 = o((n π_n)²)` under (C), with no assumption on the size of `n π_n`.
* `tendsto_bridgeLaw_one_le_cyclicSum` (**Lemma `lem:extreme_means`(i)**) and
  `tendsto_bridgeLaw_abs_cyclicSum_div_sub_one` (**Lemma `lem:extreme_means`(ii)**).
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-! ### Two disjoint blocks under the bridge -/

/-- **Two disjoint blocks with a bounded bridge weight** (source lines 2058–2075): for `m₁ ≤ j`,
`j + m₂ ≤ n`, if `Ψ_{n-m₁-m₂}(s - S_{m₁} - S'_{m₂}) ≤ K` whenever both blocks satisfy their
events, then `P(H₁(X_1..X_{m₁}), H₂(X_{j+1}..X_{j+m₂}), S_n = s) ≤ K P(H₁) P(H₂)`. -/
theorem walkVecLaw_real_two_blocks_inter_sum_le (μ : PMF ℕ) {m₁ j m₂ n : ℕ} (hj : m₁ ≤ j)
    (hn : j + m₂ ≤ n) (H₁ H₂ : List ℤ → Prop) (s : ℤ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ a : Fin m₁ → ℤ, H₁ (List.ofFn a) → ∀ c : Fin m₂ → ℤ, H₂ (List.ofFn c) →
      walkProb μ ((n - m₁ - m₂ : ℕ) : ℤ) (s - ∑ i, a i - ∑ i, c i) ≤ K) :
    (walkVecLaw μ n).real {ω | H₁ ((List.ofFn ω).take m₁) ∧
        H₂ (((List.ofFn ω).drop j).take m₂) ∧ ∑ i, ω i = s} ≤
      K * (walkVecLaw μ m₁).real {a | H₁ (List.ofFn a)} *
        (walkVecLaw μ m₂).real {c | H₂ (List.ofFn c)} := by
  rw [walkVecLaw_real_two_blocks_inter_sum μ hj hn]
  set P₂ := (walkVecLaw μ m₂).real {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} with hP₂
  set I₁ : (Fin m₁ → ℤ) → ℝ := {a : Fin m₁ → ℤ | H₁ (List.ofFn a)}.indicator 1 with hI₁
  set I₂ : (Fin m₂ → ℤ) → ℝ := {c : Fin m₂ → ℤ | H₂ (List.ofFn c)}.indicator 1 with hI₂
  have hI₂01 : ∀ c, 0 ≤ I₂ c ∧ I₂ c ≤ 1 := fun c => indicator_one_mem_Icc _ c
  have hI₁01 : ∀ a, 0 ≤ I₁ a ∧ I₁ a ≤ 1 := fun a => indicator_one_mem_Icc _ a
  have hP₂0 : 0 ≤ P₂ := measureReal_nonneg
  have hinner : ∀ a, ∫ c, I₁ a * I₂ c * walkProb μ ((n - m₁ - m₂ : ℕ) : ℤ)
      (s - ∑ i, a i - ∑ i, c i) ∂walkVecLaw μ m₂ ≤ I₁ a * (K * P₂) := by
    intro a
    by_cases ha : H₁ (List.ofFn a)
    · have hIa : I₁ a = 1 :=
        Set.indicator_of_mem (show a ∈ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha) _
      rw [hIa, one_mul]
      have hg : Integrable (fun c => K * I₂ c) (walkVecLaw μ m₂) := by
        refine integrable_walkVecLaw_of_abs_le μ K fun c => ?_
        rw [abs_of_nonneg (mul_nonneg hK0 (hI₂01 c).1)]
        exact mul_le_of_le_one_right hK0 (hI₂01 c).2
      calc ∫ c, 1 * I₂ c * walkProb μ ((n - m₁ - m₂ : ℕ) : ℤ) (s - ∑ i, a i - ∑ i, c i)
            ∂walkVecLaw μ m₂ ≤ ∫ c, K * I₂ c ∂walkVecLaw μ m₂ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun c => ?_) hg
              (Eventually.of_forall fun c => ?_)
            · exact mul_nonneg (mul_nonneg zero_le_one (hI₂01 c).1) (walkProb_nonneg μ _ _)
            · dsimp only
              by_cases hc : H₂ (List.ofFn c)
              · have hIc : I₂ c = 1 :=
                  Set.indicator_of_mem (show c ∈ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc) _
                rw [hIc, one_mul, one_mul, mul_one]
                exact hK a ha c hc
              · have hIc : I₂ c = 0 :=
                  Set.indicator_of_notMem (show c ∉ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc) _
                rw [hIc, mul_zero, zero_mul, mul_zero]
        _ = K * P₂ := by
            rw [integral_const_mul, hI₂, integral_indicator_one MeasurableSet.of_discrete]
    · have hIa : I₁ a = 0 :=
        Set.indicator_of_notMem (show a ∉ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha) _
      simp [hIa]
  have hg : Integrable (fun a => I₁ a * (K * P₂)) (walkVecLaw μ m₁) := by
    refine integrable_walkVecLaw_of_abs_le μ (K * P₂) fun a => ?_
    rw [abs_of_nonneg (mul_nonneg (hI₁01 a).1 (mul_nonneg hK0 hP₂0))]
    exact mul_le_of_le_one_left (mul_nonneg hK0 hP₂0) (hI₁01 a).2
  calc ∫ a, ∫ c, I₁ a * I₂ c * walkProb μ ((n - m₁ - m₂ : ℕ) : ℤ) (s - ∑ i, a i - ∑ i, c i)
        ∂walkVecLaw μ m₂ ∂walkVecLaw μ m₁
      ≤ ∫ a, I₁ a * (K * P₂) ∂walkVecLaw μ m₁ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun a => ?_) hg
          (Eventually.of_forall hinner)
        exact integral_nonneg fun c => mul_nonneg (mul_nonneg (hI₁01 a).1 (hI₂01 c).1)
          (walkProb_nonneg μ _ _)
    _ = K * (walkVecLaw μ m₁).real {a | H₁ (List.ofFn a)} * P₂ := by
        rw [integral_mul_const, hI₁, integral_indicator_one MeasurableSet.of_discrete]
        ring

/-- The null event `{d ∤ S_m + m}`. -/
theorem walkVecLaw_real_not_dvd {d : ℕ} {L : ℝ} (hloc : LatticeLocal μ a d L) (m : ℕ) :
    (walkVecLaw μ m).real {b : Fin m → ℤ | ¬(d : ℤ) ∣ ∑ i, b i + m} = 0 := by
  rw [measureReal_eq_zero_iff]
  exact ae_iff.mp (ae_dvd_sum_add hloc m)

/-- **Separated pairs** (source lines 2042–2079, claim of the proof of Lemma
`lem:extreme_means`(ii)): for every `δ > 0`, eventually along admissible sizes,
`P(I_1^{(M_n)} = I_{1+ℓ}^{(M_n)} = 1 | S_n = -1) ≤ (1 + δ) p_n²` for every `ℓ` with
`M_n ≤ ℓ ≤ n - M_n` (pairs at cyclic distance at least `M_n`, by cyclic exchangeability).
Proof: the two-block Markov formula at the bridge endpoint `-1` (the blocks are independent under
the unconditioned law only), the ratio limit `Ψ_{n-2M_n}(-1 - S_{M_n} - Z) / Ψ_n(-1) ≤ 1 + δ/2`
for `|S_{M_n}|, |Z| ≤ r_n = √(a_{M_n} a_n)` at compatible endpoints (`S ≡ -M_n mod d` almost
surely, F4/F15), the bound `Ψ_{n-2M_n}(·) ≤ C Ψ_n(-1)` elsewhere, and
`P(I_1^{(M_n)} = 1, |S_{M_n}| > r_n) = o(p_n)` (Lemma `lem:pnqn`(i)). Toolkit and cutoff only. -/
theorem eventually_pairBridge_le (hT : StableToolkit μ α a) (G : ℕ → PlaneTree → Prop)
    (k : ℕ → ℕ) {M : ℕ → ℕ} (hM : IsCutoff M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ, ∀ ℓ : ℕ, M n ≤ ℓ → ℓ + M n ≤ n →
      pairBridge μ (G (k n)) (M n) n ℓ ≤ (1 + ε) * pProb μ (G (k n)) (M n) ^ 2 := by
  obtain ⟨d, L, hloc⟩ := hT.lattice
  obtain ⟨C₁, hC₁, hle⟩ := hT.exists_le_div_of_le_two_mul
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hsq := hT.regularlyVarying.tendsto_sqrt_div hT.monotone hT.pos hT.rho_pos
    hM.tendsto_atTop hM.isLittleO
  have hz : (fun n => 2 * √(a (M n) * a n) + 1) =o[atTop]
      (fun n => a ((fun n : ℕ => n) n)) := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn h
      exact absurd h (hT.pos n hn).ne'
    · have h1 : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hT.tendsto_atTop
      have h2 := (hsq.2.const_mul 2).add h1
      rw [mul_zero, add_zero] at h2
      refine h2.congr' (Eventually.of_forall fun n => ?_)
      simp only [add_div, one_div, mul_div_assoc]
  have h2Mo : (fun n => (((fun n => 2 * M n) n : ℕ) : ℝ)) =o[atTop]
      (fun n => (((fun n : ℕ => n) n : ℕ) : ℝ)) := by
    have := hM.isLittleO.const_mul_left 2
    refine this.congr_left fun n => ?_
    push_cast
    ring
  have h4M : ∀ᶠ n in atTop, 4 * M n ≤ n := by
    filter_upwards [hM.isLittleO.bound (show (0 : ℝ) < 1 / 4 by norm_num)] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have : ((4 * M n : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  set C' : ℝ := C₁ / c with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [hl (hT.eventually_abs_div_sub_one_le hloc (N := fun n => n)
      (m := fun n => 2 * M n) tendsto_id h2Mo hz hε2),
    (isLittleO_walkVecLaw_firstMarked_abs_sum_gt_admissible hT G k hM).def
      (show 0 < ε / 4 / (C' + 1) by positivity),
    hl h4M, hl (eventually_ge_atTop 1), hadm] with n hratio htail h4Mn hn1 hadmn
  intro ℓ hℓ1 hℓ2
  have hM1 : 1 ≤ M n := hM.pos n hn1
  set r : ℝ := √(a (M n) * a n) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have han : 0 < a n := hT.pos n hn1
  set ψ : ℝ := walkProb μ n (-1) with hψdef
  have hψ : 0 < ψ := (walkProb_neg_one_pos_iff μ n).2 hadmn
  have hψlow : c / a n ≤ ψ := hlow n hn1 hψ
  have hdn := dvd_sub_one_of_admissible hloc hadmn
  set H : List ℤ → Prop := FirstMarked (G (k n)) (M n) with hH
  set Hg : List ℤ → Prop := fun x => H x ∧ |((x.sum : ℤ) : ℝ)| ≤ r ∧ (d : ℤ) ∣ x.sum + M n
    with hHg
  set Hb : List ℤ → Prop := fun x => H x ∧ ¬(|((x.sum : ℤ) : ℝ)| ≤ r ∧ (d : ℤ) ∣ x.sum + M n)
    with hHb
  set p : ℝ := pProb μ (G (k n)) (M n) with hp
  set t : ℝ := (walkVecLaw μ (M n)).real {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
      √(a (M n) * a n) < |((∑ i, ω i : ℤ) : ℝ)|} with ht
  have hp0 : 0 ≤ p := measureReal_nonneg
  have ht0 : 0 ≤ t := measureReal_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg hp0] at htail
  -- the probabilities of the good and bad block events
  have hPg : (walkVecLaw μ (M n)).real {b : Fin (M n) → ℤ | Hg (List.ofFn b)} ≤ p :=
    measureReal_mono (fun b hb => hb.1)
  have hPH : (walkVecLaw μ (M n)).real {b : Fin (M n) → ℤ | H (List.ofFn b)} = p := rfl
  have hPb : (walkVecLaw μ (M n)).real {b : Fin (M n) → ℤ | Hb (List.ofFn b)} ≤ t := by
    have hsub : {b : Fin (M n) → ℤ | Hb (List.ofFn b)} ⊆
        {ω : Fin (M n) → ℤ | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
          √(a (M n) * a n) < |((∑ i, ω i : ℤ) : ℝ)|} ∪
        {b : Fin (M n) → ℤ | ¬(d : ℤ) ∣ ∑ i, b i + M n} := by
      rintro b ⟨hHb1, hHb2⟩
      rw [List.sum_ofFn] at hHb2
      by_cases hS : |((∑ i, b i : ℤ) : ℝ)| ≤ r
      · exact Or.inr fun hd => hHb2 ⟨hS, hd⟩
      · exact Or.inl ⟨hHb1, lt_of_not_ge hS⟩
    calc _ ≤ _ := measureReal_mono hsub
      _ ≤ t + 0 := by
          refine (measureReal_union_le _ _).trans (add_le_add le_rfl ?_)
          exact (walkVecLaw_real_not_dvd hloc (M n)).le
      _ = t := add_zero t
  -- the pair event in block form: good–good, bad–any, any–bad
  have hset : {ω : Fin n → ℤ | ∑ i, ω i = -1} ∩
      {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
        FirstMarked (G (k n)) (M n) ((List.ofFn ω).rotate ℓ)} ⊆
      ({ω | Hg ((List.ofFn ω).take (M n)) ∧ Hg (((List.ofFn ω).drop ℓ).take (M n)) ∧
          ∑ i, ω i = -1} ∪
        {ω | Hb ((List.ofFn ω).take (M n)) ∧ H (((List.ofFn ω).drop ℓ).take (M n)) ∧
          ∑ i, ω i = -1}) ∪
        {ω | H ((List.ofFn ω).take (M n)) ∧ Hb (((List.ofFn ω).drop ℓ).take (M n)) ∧
          ∑ i, ω i = -1} := by
    rintro ω ⟨hs, h1, h2⟩
    have hlen : ℓ + M n ≤ (List.ofFn ω).length := by rw [List.length_ofFn]; exact hℓ2
    have h1' : H ((List.ofFn ω).take (M n)) := firstMarked_take_iff.mpr h1
    have h2' : H (((List.ofFn ω).drop ℓ).take (M n)) :=
      firstMarked_take_iff.mpr ((firstMarked_rotate_iff_drop hlen).mp h2)
    by_cases g1 : |(((((List.ofFn ω).take (M n)).sum : ℤ)) : ℝ)| ≤ r ∧
        (d : ℤ) ∣ ((List.ofFn ω).take (M n)).sum + M n
    · by_cases g2 : |((((((List.ofFn ω).drop ℓ).take (M n)).sum : ℤ)) : ℝ)| ≤ r ∧
          (d : ℤ) ∣ (((List.ofFn ω).drop ℓ).take (M n)).sum + M n
      · exact Or.inl (Or.inl ⟨⟨h1', g1⟩, ⟨h2', g2⟩, hs⟩)
      · exact Or.inr ⟨h1', ⟨h2', g2⟩, hs⟩
    · exact Or.inl (Or.inr ⟨⟨h1', g1⟩, h2', hs⟩)
  -- the ratio limit on the good blocks (compatible endpoints)
  have hK_g : ∀ a' : Fin (M n) → ℤ, Hg (List.ofFn a') → ∀ c' : Fin (M n) → ℤ,
      Hg (List.ofFn c') →
      walkProb μ ((n - M n - M n : ℕ) : ℤ) (-1 - ∑ i, a' i - ∑ i, c' i) ≤ (1 + ε / 2) * ψ := by
    rintro a' ⟨-, ha1, ha2⟩ c' ⟨-, hc1, hc2⟩
    rw [List.sum_ofFn] at ha1 ha2 hc1 hc2
    have hdx : (d : ℤ) ∣ (-1 - ∑ i, a' i - ∑ i, c' i) + ((n - 2 * M n : ℕ) : ℤ) := by
      have := Int.dvd_sub (Int.dvd_sub hdn ha2) hc2
      convert this using 1
      push_cast [show 2 * M n ≤ n by omega]
      ring
    have hdy : (d : ℤ) ∣ (-1 : ℤ) + (n : ℤ) := by
      rwa [show (-1 : ℤ) + n = n - 1 by ring]
    have hx : |(((-1 - ∑ i, a' i - ∑ i, c' i : ℤ)) : ℝ)| ≤ 2 * r + 1 := by
      push_cast
      rw [abs_le] at ha1 hc1 ⊢
      push_cast at ha1 hc1
      constructor <;> linarith [ha1.1, ha1.2, hc1.1, hc1.2]
    have hy : |(((-1 : ℤ)) : ℝ)| ≤ 2 * r + 1 := by simp; linarith
    have h : |walkProb μ ((n - 2 * M n : ℕ) : ℤ) (-1 - ∑ i, a' i - ∑ i, c' i) / ψ - 1| ≤
        ε / 2 := hratio (2 * M n) le_rfl _ _ hdx hdy hx hy
    rw [show n - M n - M n = n - 2 * M n by omega]
    have h' : walkProb μ ((n - 2 * M n : ℕ) : ℤ) (-1 - ∑ i, a' i - ∑ i, c' i) / ψ ≤
        1 + ε / 2 := by
      have := (abs_le.mp h).2
      linarith
    rwa [div_le_iff₀ hψ] at h'
  -- the crude bound on the bad blocks
  have hK_b : ∀ x : ℤ, walkProb μ ((n - M n - M n : ℕ) : ℤ) x ≤ C' * ψ := by
    intro x
    have h1 := hle n (n - M n - M n) hn1 (by omega) (by omega) x
    calc walkProb μ ((n - M n - M n : ℕ) : ℤ) x ≤ C₁ / a n := h1
      _ = C' * (c / a n) := by rw [hC']; field_simp
      _ ≤ C' * ψ := mul_le_mul_of_nonneg_left hψlow hC'0
  have hgg := walkVecLaw_real_two_blocks_inter_sum_le μ hℓ1 hℓ2 Hg Hg (-1)
    (by positivity) hK_g
  have hbh := walkVecLaw_real_two_blocks_inter_sum_le μ hℓ1 hℓ2 Hb H (-1)
    (by positivity) (fun a' _ c' _ => hK_b _)
  have hhb := walkVecLaw_real_two_blocks_inter_sum_le μ hℓ1 hℓ2 H Hb (-1)
    (by positivity) (fun a' _ c' _ => hK_b _)
  rw [hPH] at hbh hhb
  have hPg0 : 0 ≤ (walkVecLaw μ (M n)).real {b : Fin (M n) → ℤ | Hg (List.ofFn b)} :=
    measureReal_nonneg
  have hPb0 : 0 ≤ (walkVecLaw μ (M n)).real {b : Fin (M n) → ℤ | Hb (List.ofFn b)} :=
    measureReal_nonneg
  have hCt : C' * t ≤ ε / 4 * p := by
    calc C' * t ≤ C' * (ε / 4 / (C' + 1) * p) := mul_le_mul_of_nonneg_left htail hC'0
      _ ≤ (C' + 1) * (ε / 4 / (C' + 1) * p) := by
          gcongr
          linarith
      _ = ε / 4 * p := by field_simp
  rw [pairBridge, bridgeLaw, cond_walkVecLaw_real_eq, inv_mul_le_iff₀ hψ]
  calc (walkVecLaw μ n).real ({ω : Fin n → ℤ | ∑ i, ω i = -1} ∩
        {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
          FirstMarked (G (k n)) (M n) ((List.ofFn ω).rotate ℓ)})
      ≤ _ := measureReal_mono hset
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ (1 + ε / 2) * ψ * p * p + C' * ψ * t * p + C' * ψ * p * t := by
        refine add_le_add (add_le_add (hgg.trans ?_) (hbh.trans ?_)) (hhb.trans ?_)
        · gcongr
        · gcongr
        · gcongr
    _ = ψ * p * ((1 + ε / 2) * p + 2 * (C' * t)) := by ring
    _ ≤ ψ * p * ((1 + ε / 2) * p + 2 * (ε / 4 * p)) := by gcongr
    _ = ψ * ((1 + ε) * p ^ 2) := by ring

/-! ### Second moment of the truncated count -/

/-- A bounded function of `(X_1, …, X_n)` is integrable under the bridge. -/
theorem integrable_bridgeLaw_of_abs_le (μ : PMF ℕ) {n : ℕ} {f : (Fin n → ℤ) → ℝ} (C : ℝ)
    (h : ∀ ω, |f ω| ≤ C) : Integrable f (bridgeLaw μ n) :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact h ω)

/-- `W_n^M = ∑_i 1_{E_i}` in `ℝ`. -/
theorem cyclicSum_cast_eq_sum_indicator (G : PlaneTree → Prop) (M : ℕ) {n : ℕ}
    (ω : Fin n → ℤ) :
    (cyclicSum G M (List.ofFn ω) : ℝ) =
      ∑ i : Fin n, (cycEvent G M n i).indicator (1 : (Fin n → ℤ) → ℝ) ω := by
  rw [cyclicSum_ofFn_eq_sum_indicator, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ω ∈ cycEvent G M n i
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- **Second moment**: `E[(W_n^M)² | S_n = -1] = ∑_i ∑_j P(I_i = I_j = 1 | S_n = -1)`. -/
theorem integral_cyclicSum_sq (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    ∫ ω, (cyclicSum G M (List.ofFn ω) : ℝ) ^ 2 ∂bridgeLaw μ n =
      ∑ i : Fin n, ∑ j : Fin n, (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j) := by
  have hmul : ∀ (s t : Set (Fin n → ℤ)) (ω : Fin n → ℤ),
      s.indicator (1 : (Fin n → ℤ) → ℝ) ω * t.indicator 1 ω = (s ∩ t).indicator 1 ω := by
    intro s t ω
    rw [Set.inter_indicator_one, Pi.mul_apply]
  have hint : ∀ s : Set (Fin n → ℤ), Integrable (s.indicator (1 : (Fin n → ℤ) → ℝ))
      (bridgeLaw μ n) := fun s =>
    integrable_bridgeLaw_of_abs_le μ 1 fun ω => by
      rw [abs_of_nonneg (indicator_one_mem_Icc s ω).1]
      exact (indicator_one_mem_Icc s ω).2
  simp_rw [cyclicSum_cast_eq_sum_indicator, sq, Finset.sum_mul_sum, hmul]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint _]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact integral_indicator_one ((measurableSet_cycEvent G M n i).inter
    (measurableSet_cycEvent G M n j))

/-- **Chebyshev's inequality for `W_n^M`** under `P(· | S_n = -1)`: for `t > 0`,
`P(|W_n^M - n q| ≥ t) ≤ (∑_i ∑_j P(I_i = I_j = 1) - (n q)²) / t²`. -/
theorem bridgeLaw_real_le_abs_cyclicSum_sub_le (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ}
    (hn : Admissible μ n) {t : ℝ} (ht : 0 < t) :
    (bridgeLaw μ n).real {ω | t ≤ |(cyclicSum G M (List.ofFn ω) : ℝ) - n * qProb μ G M n|} ≤
      (∑ i : Fin n, ∑ j : Fin n, (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j) -
        ((n : ℝ) * qProb μ G M n) ^ 2) / t ^ 2 := by
  have := isProbabilityMeasure_bridgeLaw hn
  set W : (Fin n → ℤ) → ℝ := fun ω => (cyclicSum G M (List.ofFn ω) : ℝ) with hW
  set c : ℝ := (n : ℝ) * qProb μ G M n with hc
  have hWn : ∀ ω, |W ω| ≤ n := by
    intro ω
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have := cyclicSum_le_length G M (List.ofFn ω)
    rw [List.length_ofFn] at this
    change (cyclicSum G M (List.ofFn ω) : ℝ) ≤ n
    exact_mod_cast this
  have hWint : Integrable W (bridgeLaw μ n) := integrable_cyclicSum_bridgeLaw μ G M n
  have hW2int : Integrable (fun ω => W ω ^ 2) (bridgeLaw μ n) := by
    refine integrable_bridgeLaw_of_abs_le μ ((n : ℝ) ^ 2) fun ω => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hWn ω) 2
  have hEW : ∫ ω, W ω ∂bridgeLaw μ n = c := by
    rw [hW, integral_cyclicSum_bridgeLaw, setOf_firstIndicator_eq_one]
    rfl
  have hvar : ∫ ω, (W ω - c) ^ 2 ∂bridgeLaw μ n = ∫ ω, W ω ^ 2 ∂bridgeLaw μ n - c ^ 2 := by
    have h : ∀ ω, (W ω - c) ^ 2 = W ω ^ 2 - 2 * c * W ω + c ^ 2 := fun ω => by ring
    simp_rw [h]
    have e1 : ∫ ω, (W ω ^ 2 - 2 * c * W ω + c ^ 2) ∂bridgeLaw μ n =
        ∫ ω, (W ω ^ 2 - 2 * c * W ω) ∂bridgeLaw μ n + ∫ _ω, c ^ 2 ∂bridgeLaw μ n :=
      integral_add (hW2int.sub (hWint.const_mul _)) (integrable_const _)
    have e2 : ∫ ω, (W ω ^ 2 - 2 * c * W ω) ∂bridgeLaw μ n =
        ∫ ω, W ω ^ 2 ∂bridgeLaw μ n - ∫ ω, 2 * c * W ω ∂bridgeLaw μ n :=
      integral_sub hW2int (hWint.const_mul _)
    rw [e1, e2, integral_const_mul, hEW, integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hVint : Integrable (fun ω => (W ω - c) ^ 2) (bridgeLaw μ n) := by
    refine integrable_bridgeLaw_of_abs_le μ (((n : ℝ) + |c|) ^ 2) fun ω => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hWn ω) le_rfl)) 2
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := bridgeLaw μ n)
    (f := fun ω => (W ω - c) ^ 2) (Eventually.of_forall fun ω => sq_nonneg _) hVint (t ^ 2)
  rw [hvar, hW, integral_cyclicSum_sq] at hmk
  have hsub : {ω : Fin n → ℤ | t ≤ |(cyclicSum G M (List.ofFn ω) : ℝ) - c|} ⊆
      {ω | t ^ 2 ≤ ((cyclicSum G M (List.ofFn ω) : ℝ) - c) ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    calc t ^ 2 ≤ |(cyclicSum G M (List.ofFn ω) : ℝ) - c| ^ 2 := pow_le_pow_left₀ ht.le hω 2
      _ = _ := sq_abs _
  rw [le_div_iff₀ (by positivity), mul_comm]
  calc t ^ 2 * (bridgeLaw μ n).real {ω | t ≤ |(cyclicSum G M (List.ofFn ω) : ℝ) - c|}
      ≤ t ^ 2 * (bridgeLaw μ n).real
          {ω | t ^ 2 ≤ ((cyclicSum G M (List.ofFn ω) : ℝ) - c) ^ 2} := by
        gcongr
        exact measure_ne_top (bridgeLaw μ n) _
    _ ≤ _ := hmk

/-- **Splitting the second moment** into diagonal, nearby and separated pairs: if every pair at
cyclic distance at least `M` has bridge probability at most `S`, then
`∑_i ∑_j P(I_i = I_j = 1) ≤ n q + b_2 + n² S`. -/
theorem sum_sum_cycEvent_inter_le (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ} (hM : 0 < M)
    {S : ℝ} (hS0 : 0 ≤ S) (hS : ∀ ℓ : ℕ, M ≤ ℓ → ℓ + M ≤ n → pairBridge μ G M n ℓ ≤ S) :
    ∑ i : Fin n, ∑ j : Fin n, (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j) ≤
      n * qProb μ G M n + errorB2 μ G M n + (n : ℝ) ^ 2 * S := by
  have hsep : ∀ i j : Fin n, j ∉ cycNbhd n M i →
      (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j) ≤ S := by
    intro i j hj
    rw [mem_cycNbhd, not_lt] at hj
    rw [bridgeLaw_real_cycEvent_inter]
    have hi := i.2
    have hj' := j.2
    apply hS
    · unfold cycGap
      unfold cycDist at hj
      split_ifs <;> omega
    · unfold cycGap
      unfold cycDist at hj
      split_ifs <;> omega
  have hrow : ∀ i : Fin n, ∑ j : Fin n, (bridgeLaw μ n).real
      (cycEvent G M n i ∩ cycEvent G M n j) ≤ qProb μ G M n +
        ∑ j ∈ cycNbhd n M i \ {i}, (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j) +
          n * S := by
    intro i
    rw [← Finset.sum_add_sum_compl (cycNbhd n M i),
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (mem_cycNbhd_self hM i), Set.inter_self,
      bridgeLaw_real_cycEvent]
    refine add_le_add le_rfl ?_
    calc ∑ j ∈ (cycNbhd n M i)ᶜ, (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j)
        ≤ ∑ _j ∈ (cycNbhd n M i)ᶜ, S :=
          Finset.sum_le_sum fun j hj => hsep i j (Finset.mem_compl.mp hj)
      _ = ((cycNbhd n M i)ᶜ.card : ℝ) * S := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * S := by
          gcongr
          exact (Finset.card_le_univ _).trans (by simp)
  calc ∑ i : Fin n, ∑ j : Fin n, (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j)
      ≤ ∑ i : Fin n, (qProb μ G M n + ∑ j ∈ cycNbhd n M i \ {i},
          (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j) + n * S) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = n * qProb μ G M n + errorB2 μ G M n + (n : ℝ) ^ 2 * S := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, errorB2]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Nearby pairs -/

/-- The bound on `b_2` from the proof of Lemma `lem:boundb2` (source lines 1815–1857), without
the bounded-mean hypothesis: eventually along admissible sizes,
`b_2 ≤ 2 C₀ (n M_n π_n² + n ∑_{ℓ=1}^{M_n} A_n(ℓ))`. -/
theorem exists_eventually_errorB2_le (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ n in admissibleSizes μ, errorB2 μ (G (k n)) (M n) n ≤
      2 * C₀ * ((n : ℝ) * M n * markProb μ G k n ^ 2 +
        (n : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ) := by
  obtain ⟨C₀, hC₀, hbr⟩ := exists_cond_take_le hT
  refine ⟨C₀, hC₀, ?_⟩
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hz : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n => a ((fun n : ℕ => n) n)) := by
    rw [isLittleO_one_left_iff]
    exact tendsto_abs_atTop_atTop.comp hT.tendsto_atTop
  have h2Mo : (fun n => ((2 * M n : ℕ) : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
    have := hM.isLittleO.const_mul_left 2
    refine this.congr_left fun n => ?_
    push_cast
    ring
  have h2M : ∀ᶠ n in atTop, 2 * M n ≤ n := by
    filter_upwards [hM.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have : ((2 * M n : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  filter_upwards [hl (hbr (N := fun n => n) (m := fun n => 2 * M n) (z := fun _ => 1)
    tendsto_id h2Mo hz), hl h2M, hadm] with n hn h2Mn hadmn
  have hψ : walkProb μ n (-1) ≠ 0 := ((walkProb_neg_one_pos_iff μ n).2 hadmn).ne'
  have hpair : ∀ ℓ ∈ Finset.Icc 1 (M n - 1), pairBridge μ (G (k n)) (M n) n ℓ ≤
      C₀ * (markProb μ G k n ^ 2 + pairProb μ G k n ℓ) := by
    intro ℓ hℓ
    have hℓM : ℓ + M n ≤ 2 * M n := by
      have := (Finset.mem_Icc.mp hℓ).2
      omega
    have h := hn (-1) (by simp) hψ
      (fun y => FirstMarked (G (k n)) (M n) y ∧ FirstMarked (G (k n)) (M n) (y.rotate ℓ))
    have hset : {ω : Fin n → ℤ | FirstMarked (G (k n)) (M n) ((List.ofFn ω).take (2 * M n)) ∧
        FirstMarked (G (k n)) (M n) (((List.ofFn ω).take (2 * M n)).rotate ℓ)} =
        {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
          FirstMarked (G (k n)) (M n) ((List.ofFn ω).rotate ℓ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      exact firstMarked_pair_take_iff hℓM (by rw [List.length_ofFn]; exact h2Mn)
    rw [hset] at h
    calc pairBridge μ (G (k n)) (M n) n ℓ ≤ C₀ * (walkVecLaw μ (2 * M n)).real
          {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
            FirstMarked (G (k n)) (M n) ((List.ofFn ω).rotate ℓ)} := h
      _ ≤ C₀ * (markProb μ G k n ^ 2 + pairProb μ G k n ℓ) :=
        mul_le_mul_of_nonneg_left (walkVecLaw_real_pair_le_markProb μ G k n hℓM) hC₀.le
  have hA0 : ∀ ℓ, 0 ≤ pairProb μ G k n ℓ := fun _ => measureReal_nonneg
  have hsumA : ∑ ℓ ∈ Finset.Icc 1 (M n - 1), pairProb μ G k n ℓ ≤
      ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.sub_le _ _))
      fun ℓ _ _ => hA0 ℓ
  have hcard : ((Finset.Icc 1 (M n - 1)).card : ℝ) ≤ M n := by
    rw [Nat.card_Icc]
    exact_mod_cast (show M n - 1 + 1 - 1 ≤ M n by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc errorB2 μ (G (k n)) (M n) n
      ≤ n * (2 * ∑ ℓ ∈ Finset.Icc 1 (M n - 1), pairBridge μ (G (k n)) (M n) n ℓ) :=
        errorB2_le μ _ _ n
    _ ≤ n * (2 * ∑ ℓ ∈ Finset.Icc 1 (M n - 1),
          C₀ * (markProb μ G k n ^ 2 + pairProb μ G k n ℓ)) := by
        gcongr with ℓ hℓ
        exact hpair ℓ hℓ
    _ = 2 * C₀ * ((n : ℝ) * ((Finset.Icc 1 (M n - 1)).card * markProb μ G k n ^ 2) +
          n * ∑ ℓ ∈ Finset.Icc 1 (M n - 1), pairProb μ G k n ℓ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 * C₀ * ((n : ℝ) * (M n * markProb μ G k n ^ 2) +
          n * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ) := by
        gcongr
    _ = _ := by ring

/-- **Nearby pairs** (source lines 2029–2040): under Assumption (C) and `M_n = o(n)`,
`b_2 = o((n π_n)²)` along admissible sizes, with no assumption on the size of `n π_n`. -/
theorem eventually_errorB2_le (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hC : NonClustering μ G k M) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in admissibleSizes μ,
      errorB2 μ (G (k n)) (M n) n ≤ η * ((n : ℝ) * markProb μ G k n) ^ 2 := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_eventually_errorB2_le hT (G := G) (k := k) hM
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hc : 0 < η / (4 * C₀) := by positivity
  filter_upwards [hb, hl (hM.isLittleO.bound hc), hC.bound hc] with n hbn hMn hCn
  rw [Real.norm_natCast, Real.norm_natCast] at hMn
  have hA0 : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ :=
    Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hπ0 : 0 ≤ markProb μ G k n := measureReal_nonneg
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA0,
    abs_of_nonneg (by positivity)] at hCn
  have h1 : 2 * C₀ * ((n : ℝ) * M n * markProb μ G k n ^ 2) ≤
      η / 2 * ((n : ℝ) * markProb μ G k n) ^ 2 := by
    have : 2 * C₀ * (M n : ℝ) ≤ η / 2 * n := by
      have := mul_le_mul_of_nonneg_left hMn (show 0 ≤ 2 * C₀ by positivity)
      calc 2 * C₀ * (M n : ℝ) ≤ 2 * C₀ * (η / (4 * C₀) * n) := this
        _ = η / 2 * n := by field_simp; ring
    have h' := mul_le_mul_of_nonneg_right this (show 0 ≤ (n : ℝ) * markProb μ G k n ^ 2 by
      positivity)
    calc 2 * C₀ * ((n : ℝ) * M n * markProb μ G k n ^ 2)
        = 2 * C₀ * (M n : ℝ) * ((n : ℝ) * markProb μ G k n ^ 2) := by ring
      _ ≤ η / 2 * n * ((n : ℝ) * markProb μ G k n ^ 2) := h'
      _ = η / 2 * ((n : ℝ) * markProb μ G k n) ^ 2 := by ring
  have h2 : 2 * C₀ * ((n : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ) ≤
      η / 2 * ((n : ℝ) * markProb μ G k n) ^ 2 := by
    have h' := mul_le_mul_of_nonneg_left hCn (show 0 ≤ 2 * C₀ * (n : ℝ) by positivity)
    calc 2 * C₀ * ((n : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ)
        = 2 * C₀ * (n : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ := by ring
      _ ≤ 2 * C₀ * (n : ℝ) * (η / (4 * C₀) * ((n : ℝ) * markProb μ G k n ^ 2)) := h'
      _ = η / 2 * ((n : ℝ) * markProb μ G k n) ^ 2 := by field_simp; ring
  calc errorB2 μ (G (k n)) (M n) n ≤ _ := hbn
    _ = 2 * C₀ * ((n : ℝ) * M n * markProb μ G k n ^ 2) +
        2 * C₀ * ((n : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ) := by ring
    _ ≤ η / 2 * ((n : ℝ) * markProb μ G k n) ^ 2 + η / 2 * ((n : ℝ) * markProb μ G k n) ^ 2 :=
        add_le_add h1 h2
    _ = η * ((n : ℝ) * markProb μ G k n) ^ 2 := by ring

/-- The arithmetic of the Chebyshev bound in Lemma `lem:extreme_means`(ii): with
`N q ≤ 2 N π`, `p ≤ (1 + δ) q`, `28 δ ≤ θ`, `N π ≥ 2/θ + 1` and `b ≤ θ (N π)²`,
`N q + b + N² (1 + δ) p² - (N q)² ≤ 3 θ (N π)²`. -/
theorem chebyshev_arith {N π q p δ θ b : ℝ} (hN : 0 ≤ N) (hq0 : 0 ≤ q) (hp0 : 0 ≤ p)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδθ : 28 * δ ≤ θ) (hθ0 : 0 < θ) (hqπ : q ≤ 2 * π)
    (hpq : p ≤ (1 + δ) * q) (hNπ : 2 / θ + 1 ≤ N * π) (hb : b ≤ θ * (N * π) ^ 2) :
    N * q + b + N ^ 2 * ((1 + δ) * p ^ 2) - (N * q) ^ 2 ≤ 3 * θ * (N * π) ^ 2 := by
  have h2θ : 0 < 2 / θ := by positivity
  have hmpos : 0 < N * π := by linarith
  have hnq : N * q ≤ 2 * (N * π) := by
    calc N * q ≤ N * (2 * π) := mul_le_mul_of_nonneg_left hqπ hN
      _ = 2 * (N * π) := by ring
  have h2 : 2 ≤ θ * (N * π) := by
    calc (2 : ℝ) = θ * (2 / θ) := by field_simp
      _ ≤ θ * (N * π) := mul_le_mul_of_nonneg_left (by linarith) hθ0.le
  have hA : N * q ≤ θ * (N * π) ^ 2 := by
    calc N * q ≤ 2 * (N * π) := hnq
      _ ≤ (θ * (N * π)) * (N * π) := mul_le_mul_of_nonneg_right h2 hmpos.le
      _ = θ * (N * π) ^ 2 := by ring
  have hp2 : p ^ 2 ≤ (1 + δ) ^ 2 * q ^ 2 := by
    calc p ^ 2 ≤ ((1 + δ) * q) ^ 2 := pow_le_pow_left₀ hp0 hpq 2
      _ = (1 + δ) ^ 2 * q ^ 2 := by ring
  have h3 : (1 + δ) ^ 3 - 1 ≤ 7 * δ := by
    have hδ2 : δ * δ ≤ δ := mul_le_of_le_one_left hδ0 hδ1
    have hδ3 : δ * δ * δ ≤ δ := by
      calc δ * δ * δ ≤ δ * δ := mul_le_of_le_one_right (mul_nonneg hδ0 hδ0) hδ1
        _ ≤ δ := hδ2
    have e : (1 + δ) ^ 3 - 1 = 3 * δ + 3 * (δ * δ) + δ * δ * δ := by ring
    rw [e]
    linarith
  have h3' : 0 ≤ (1 + δ) ^ 3 - 1 := by
    have : (1 : ℝ) ≤ (1 + δ) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hq2 : (N * q) ^ 2 ≤ 4 * (N * π) ^ 2 := by
    calc (N * q) ^ 2 ≤ (2 * (N * π)) ^ 2 := pow_le_pow_left₀ (mul_nonneg hN hq0) hnq 2
      _ = 4 * (N * π) ^ 2 := by ring
  have hsep : N ^ 2 * ((1 + δ) * p ^ 2) - (N * q) ^ 2 ≤ θ * (N * π) ^ 2 := by
    calc N ^ 2 * ((1 + δ) * p ^ 2) - (N * q) ^ 2
        ≤ N ^ 2 * ((1 + δ) * ((1 + δ) ^ 2 * q ^ 2)) - (N * q) ^ 2 := by gcongr
      _ = ((1 + δ) ^ 3 - 1) * (N * q) ^ 2 := by ring
      _ ≤ 7 * δ * (4 * (N * π) ^ 2) := mul_le_mul h3 hq2 (sq_nonneg _) (by positivity)
      _ = (28 * δ) * (N * π) ^ 2 := by ring
      _ ≤ θ * (N * π) ^ 2 := mul_le_mul_of_nonneg_right hδθ (sq_nonneg _)
  linarith

/-! ### Lemma `lem:extreme_means` -/

/-- **Lemma `lem:extreme_means`(i)** (source lines 2010, 2019–2021): under Assumption (M), if
`n π_n → 0`, then `W_n^{M_n} → 0` in probability under `P(· | S_n = -1)`; since `W_n^{M_n}` is
integer valued this is `P(W_n^{M_n} ≥ 1 | S_n = -1) → 0`. Proof: Markov's inequality and
`E[W_n^{M_n} | S_n = -1] = n q_n ≤ 2 n π_n` eventually. -/
theorem tendsto_bridgeLaw_one_le_cyclicSum {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hmic : Microscopic μ G k M)
    (h0 : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) (𝓝 0)) :
    Tendsto (fun n => (bridgeLaw μ n).real
      {ω | 1 ≤ cyclicSum (G (k n)) (M n) (List.ofFn ω)}) (admissibleSizes μ) (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 2 * ((n : ℝ) * markProb μ G k n)) (admissibleSizes μ)
      (𝓝 0) := by
    simpa using h0.const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_abs_qProb_sub_markProb_le hmic one_pos] with n hq
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := bridgeLaw μ n)
    (f := fun ω => (cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ))
    (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (integrable_cyclicSum_bridgeLaw μ _ _ n) 1
  rw [one_mul, integral_cyclicSum_bridgeLaw, setOf_firstIndicator_eq_one] at hmk
  have hset : {ω : Fin n → ℤ | 1 ≤ cyclicSum (G (k n)) (M n) (List.ofFn ω)} =
      {ω | (1 : ℝ) ≤ (cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Nat.one_le_cast]
  rw [hset]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_le, one_mul] at hq
  calc _ ≤ (n : ℝ) * qProb μ (G (k n)) (M n) n := hmk
    _ ≤ 2 * ((n : ℝ) * markProb μ G k n) := by nlinarith

/-- **Lemma `lem:extreme_means`(ii)** (source lines 2012, 2023–2088): under Assumptions (M) and
(C), if `n π_n → ∞`, then `W_n^{M_n} / (n π_n) → 1` in probability under `P(· | S_n = -1)`.

Proof (Chebyshev): `Var(W_n^{M_n}) ≤ n q_n + b_2 + n² max_{sep} P(I_i = I_j = 1) - (n q_n)²`
(`bridgeLaw_real_le_abs_cyclicSum_sub_le`, `sum_sum_cycEvent_inter_le`); the diagonal term is
`n q_n = o((n π_n)²)`, the nearby pairs give `b_2 = o((n π_n)²)` (`eventually_errorB2_le`), and
separated pairs have probability `≤ (1 + δ) p_n²` (`eventually_pairBridge_le`), with
`p_n ∼ q_n ∼ π_n` (Lemma `lem:pnqn`). -/
theorem tendsto_bridgeLaw_abs_cyclicSum_div_sub_one (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M) (hmic : Microscopic μ G k M)
    (hC : NonClustering μ G k M)
    (hdiv : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (bridgeLaw μ n).real {ω | ε <
      |(cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|})
      (admissibleSizes μ) (𝓝 0) := by
  refine tendsto_zero_of_forall_eventually_le (fun n => measureReal_nonneg) fun η hη => ?_
  set e : ℝ := ε / 2 with he
  have he0 : 0 < e := half_pos hε
  set θ : ℝ := η * e ^ 2 / 3 with hθ
  have hθ0 : 0 < θ := by positivity
  set δ : ℝ := min 1 (θ / 28) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδθ : δ ≤ θ / 28 := min_le_right _ _
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  filter_upwards [hdiv.eventually_ge_atTop (2 / θ + 1),
    eventually_abs_qProb_sub_markProb_le hmic (show 0 < min δ e from lt_min hδ0 he0),
    eventually_errorB2_le hT hM hC hθ0, eventually_pairBridge_le hT G k hM hδ0,
    (isEquivalent_pProb_qProb hT G k hM).isLittleO.def hδ0,
    hadm, hl (eventually_ge_atTop 1)] with n hnπ hq hb2 hsep hpq hadmn hn1
  set π : ℝ := markProb μ G k n with hπdef
  set q : ℝ := qProb μ (G (k n)) (M n) n with hqdef
  set p : ℝ := pProb μ (G (k n)) (M n) with hpdef
  have hπ0 : 0 ≤ π := measureReal_nonneg
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2θ : 0 < 2 / θ := by positivity
  have hmpos : 0 < (n : ℝ) * π := by linarith
  have hmin1 : min δ e ≤ δ := min_le_left _ _
  have hmin2 : min δ e ≤ e := min_le_right _ _
  have hq' : |q - π| ≤ e * π := hq.trans (mul_le_mul_of_nonneg_right hmin2 hπ0)
  rw [abs_le] at hq
  have hqπ : q ≤ 2 * π := by
    have := mul_le_mul_of_nonneg_right (hmin1.trans hδ1) hπ0
    linarith [hq.2]
  have hqπ' : |(n : ℝ) * q - n * π| ≤ e * ((n : ℝ) * π) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hn0]
    have h : |q - π| ≤ e * π := hq'
    calc (n : ℝ) * |q - π| ≤ n * (e * π) := mul_le_mul_of_nonneg_left h hn0
      _ = e * ((n : ℝ) * π) := by ring
  have hpq' : p ≤ (1 + δ) * q := by
    rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq0, abs_le] at hpq
    linarith [hpq.2]
  -- Chebyshev and the splitting of the second moment
  have hcheb := bridgeLaw_real_le_abs_cyclicSum_sub_le μ (G (k n)) (M := M n) hadmn
    (show 0 < e * ((n : ℝ) * π) by positivity)
  have hsum := sum_sum_cycEvent_inter_le μ (G (k n)) (hM.pos n hn1)
    (show 0 ≤ (1 + δ) * p ^ 2 by positivity) hsep
  -- the event is contained in `{|W - n q| ≥ e n π}`
  have hsub : {ω : Fin n → ℤ | ε <
      |(cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) / ((n : ℝ) * π) - 1|} ⊆
      {ω | e * ((n : ℝ) * π) ≤ |(cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) - n * q|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    set W : ℝ := (cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ)
    rw [div_sub_one hmpos.ne', abs_div, abs_of_pos hmpos, lt_div_iff₀ hmpos] at hω
    have htri : |W - n * π| ≤ |W - n * q| + |(n : ℝ) * q - n * π| := by
      have := abs_sub_le W ((n : ℝ) * q) (n * π)
      linarith
    have hεe : ε * ((n : ℝ) * π) = 2 * (e * ((n : ℝ) * π)) := by rw [he]; ring
    linarith
  -- the variance bound
  have hV : ∑ i : Fin n, ∑ j : Fin n, (bridgeLaw μ n).real
      (cycEvent (G (k n)) (M n) n i ∩ cycEvent (G (k n)) (M n) n j) - ((n : ℝ) * q) ^ 2 ≤
      3 * θ * ((n : ℝ) * π) ^ 2 :=
    (sub_le_sub_right hsum _).trans (chebyshev_arith hn0 hq0 hp0 hδ0.le hδ1 (by linarith)
      hθ0 hqπ hpq' hnπ hb2)
  calc (bridgeLaw μ n).real {ω | ε <
        |(cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) / ((n : ℝ) * π) - 1|}
      ≤ (bridgeLaw μ n).real {ω | e * ((n : ℝ) * π) ≤
          |(cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) - n * q|} :=
        measureReal_mono hsub (measure_ne_top (bridgeLaw μ n) _)
    _ ≤ _ := hcheb
    _ ≤ 3 * θ * ((n : ℝ) * π) ^ 2 / (e * ((n : ℝ) * π)) ^ 2 := by gcongr
    _ = η := by
        have hπne : π ≠ 0 := fun h => by rw [h, mul_zero] at hmpos; exact lt_irrefl _ hmpos
        have hnne : (n : ℝ) ≠ 0 := fun h => by rw [h, zero_mul] at hmpos; exact lt_irrefl _ hmpos
        rw [hθ]
        field_simp

end PoissonDeclumping.Bridge
