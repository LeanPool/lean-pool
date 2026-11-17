/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Kingman.Truncate

/-!
# Kingman's subadditive ergodic theorem

`bkingman` (the bounded form), the truncation ladder that removes the bound, and `kingman`
itself, which assumes only `∫ (f 1)⁺ < ∞`. Also the backward form and `L1_orbit_decay`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-- **Kingman's subadditive ergodic theorem for a family with a linear lower bound.**

The `b` is for *bounded below*: the extra hypothesis is `-(K·n) ≤ f n ω` pointwise. This is what
makes the zero-one transition of `exists_transition` a real number rather than `-∞` — without it
every threshold set can be null, which is the `C = -∞` case. It costs nothing downstream: the
truncated family `gᴹₙ = max(fₙ, -Mn)` satisfies it by construction with `K = M`, so `kingman`
supplies it for free.

Non-positivity, which Steele's greedy estimate needs, is arranged separately by `normalize`. -/
theorem bkingman (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ)
    (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f) (hL1 : ∀ n, Integrable (f n) μ)
    (K : ℝ) (hK : 0 ≤ K) (hlb : ∀ n ω, -(K * n) ≤ f n ω)
    (C : ℝ) (hC : Tendsto (fun n : ℕ => (∫ ω, f n ω ∂μ) / n) atTop (nhds C)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω / n) atTop (nhds C) := by
  have hmp : MeasurePreserving σ μ μ := hσ.toMeasurePreserving
  have hgsub : SubadditiveFamily σ (SubadditiveFamily.normalize σ f) :=
    hf.normalize_subadditive hmp.measurable
  have hgnonpos : ∀ n, 1 ≤ n → ∀ ω, SubadditiveFamily.normalize σ f n ω ≤ 0 :=
    fun n hn ω => hf.normalize_nonpos n hn ω
  have hbs : ∀ n : ℕ, Integrable (fun ω => birkhoffSum σ (f 1) n ω) μ := by
    intro n
    simp only [birkhoffSum]
    exact integrable_finsetSum _
      (fun i _ => (hmp.iterate i).integrable_comp_of_integrable (hL1 1))
  have hgint : ∀ n, Integrable (SubadditiveFamily.normalize σ f n) μ := fun n =>
    (hL1 n).sub (hbs n)
  have hgintegral : ∀ n : ℕ, ∫ ω, SubadditiveFamily.normalize σ f n ω ∂μ
      = (∫ ω, f n ω ∂μ) - n * ∫ ω, f 1 ω ∂μ := by
    intro n
    simp only [SubadditiveFamily.normalize]
    rw [integral_sub (hL1 n) (hbs n), integral_birkhoffSum hmp (f 1) (hL1 1) n]
  -- (i) the zero-one law for the normalised family's thresholds
  have hzo := SubadditiveFamily.measure_liminfGE_zero_or_one μ σ hσ
    (SubadditiveFamily.normalize σ f) hgsub
  -- (ii) one conull threshold, from the linear lower bound
  have hlow : μ (liminfGE (fun n ω => SubadditiveFamily.normalize σ f n ω / n)
      (-K - (∫ ω, f 1 ω ∂μ) - 1)) = 1 :=
    SubadditiveFamily.liminfGE_normalize_full μ σ hσ f hf.1 (hL1 1) K hlb _ (by linarith)
  -- (iii) one null threshold: the normalised averages are `≤ 0`, so `liminf ≥ 1` is impossible
  have hhigh : μ (liminfGE (fun n ω => SubadditiveFamily.normalize σ f n ω / n) 1) = 0 := by
    have hempty : liminfGE (fun n ω => SubadditiveFamily.normalize σ f n ω / n) 1 = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
      simp only [liminfGE, Set.mem_ofPred_eq] at hx
      obtain ⟨N, hN⟩ := hx 1 (by norm_num)
      have hlt := hN (max N 1) (le_max_left N 1)
      have h0 := hgnonpos (max N 1) (le_max_right N 1) x
      have hd : SubadditiveFamily.normalize σ f (max N 1) x / ((max N 1 : ℕ) : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg h0 (Nat.cast_nonneg _)
      norm_num at hlt
      linarith
    rw [hempty, measure_empty]
  -- (iv) Steele's theorem at the transition
  obtain ⟨γ, habove, hbelow⟩ := exists_transition hzo hlow hhigh
  have hgtend : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => SubadditiveFamily.normalize σ f n x / n) atTop (nhds γ) :=
    SubadditiveFamily.ae_tendsto_of_transition μ σ hσ (SubadditiveFamily.normalize σ f)
      hgsub hgnonpos γ habove hbelow
  -- (v) undo the normalisation with Birkhoff
  have hbirk := ae_tendsto_birkhoffAverage_of_ergodic hσ (f 1) (hf.1 1) (hL1 1)
  have hftend : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / n) atTop
      (nhds (γ + ∫ ω, f 1 ω ∂μ)) := by
    filter_upwards [hgtend, hbirk] with x h1 h2
    have hrw : ∀ n : ℕ, f n x / n
        = SubadditiveFamily.normalize σ f n x / n + birkhoffAverage ℝ σ (f 1) n x :=
      fun n => SubadditiveFamily.normalize_div_add σ f n x
    simp only [hrw]
    exact h1.add h2
  -- (vi) identify the a.e. limit with `C`, by Fatou in both directions
  have hupper : γ + (∫ ω, f 1 ω ∂μ) ≤ C := by
    have hnn : ∀ (n : ℕ) (ω : Ω), 0 ≤ f n ω / n + K := by
      intro n ω
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hK
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have hKn : -K ≤ f n ω / n := by rw [le_div_iff₀ hn0]; linarith [hlb n ω]
        linarith
    have hint' : ∀ n : ℕ, Integrable (fun ω => f n ω / n + K) μ := fun n =>
      ((hL1 n).div_const _).add (integrable_const K)
    have hlim' : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω / n + K) atTop
        (nhds (γ + (∫ ω, f 1 ω ∂μ) + K)) := by
      filter_upwards [hftend] with ω hω
      exact hω.add_const K
    have hInt : Tendsto (fun n : ℕ => ∫ ω, (f n ω / n + K) ∂μ) atTop (nhds (C + K)) := by
      have hEq : ∀ n : ℕ, ∫ ω, (f n ω / n + K) ∂μ = (∫ ω, f n ω ∂μ) / n + K := by
        intro n
        rw [integral_add ((hL1 n).div_const _) (integrable_const K), integral_div]
        simp
      simp only [hEq]
      exact hC.add_const K
    have := le_of_tendsto_integral_of_nonneg (μ := μ) (fun n ω => f n ω / n + K) hint' hnn
      (γ + (∫ ω, f 1 ω ∂μ) + K) (C + K) hlim' hInt
    linarith
  have hlower : C ≤ γ + (∫ ω, f 1 ω ∂μ) := by
    have hnn : ∀ (n : ℕ) (ω : Ω), 0 ≤ -(SubadditiveFamily.normalize σ f n ω / n) := by
      intro n ω
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [neg_nonneg]
        exact div_nonpos_of_nonpos_of_nonneg (hgnonpos n hn ω) (Nat.cast_nonneg n)
    have hint' : ∀ n : ℕ, Integrable (fun ω => -(SubadditiveFamily.normalize σ f n ω / n)) μ :=
      fun n => ((hgint n).div_const _).neg
    have hlim' : ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => -(SubadditiveFamily.normalize σ f n ω / n)) atTop (nhds (-γ)) := by
      filter_upwards [hgtend] with ω hω
      exact hω.neg
    have hInt : Tendsto (fun n : ℕ => ∫ ω, -(SubadditiveFamily.normalize σ f n ω / n) ∂μ)
        atTop (nhds (-C + ∫ ω, f 1 ω ∂μ)) := by
      have hbase : Tendsto (fun n : ℕ => -((∫ ω, f n ω ∂μ) / n) + ∫ ω, f 1 ω ∂μ) atTop
          (nhds (-C + ∫ ω, f 1 ω ∂μ)) := hC.neg.add_const _
      refine hbase.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      have hsplit : ((∫ ω, f n ω ∂μ) - n * ∫ ω, f 1 ω ∂μ) / n
          = (∫ ω, f n ω ∂μ) / n - ∫ ω, f 1 ω ∂μ := by field_simp
      rw [integral_neg, integral_div, hgintegral n, hsplit]
      ring
    have := le_of_tendsto_integral_of_nonneg (μ := μ)
      (fun n ω => -(SubadditiveFamily.normalize σ f n ω / n)) hint' hnn
      (-γ) (-C + ∫ ω, f 1 ω ∂μ) hlim' hInt
    linarith
  have hCeq : γ + (∫ ω, f 1 ω ∂μ) = C := le_antisymm hupper hlower
  rwa [hCeq] at hftend

/-- For an `L¹` family the `lowerIntegral` mean clause of `kingman` is the ordinary Bochner one.

This is the whole content of the former `kingman_of_integrable`: an `L¹` subadditive family
satisfies `kingman`'s hypothesis (`(f 1)⁺` is integrable because `f 1` is), so the stronger
theorem applies directly, and only the mean clause has to be translated. Keeping a separate `L¹`
Kingman would have meant a second copy of the truncation ladder. -/
theorem tendsto_mean_of_lowerIntegral {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} (hL1 : ∀ n, Integrable (f n) μ) {C : EReal}
    (h : Tendsto (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop (nhds C)) :
    Tendsto (fun n : ℕ => ((∫ ω, f n ω ∂μ) / n : EReal)) atTop (nhds C) := by
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [lowerIntegral_eq_integral ((hL1 n).div_const (n : ℝ)), integral_div]
  exact (coe_div_natCast _ n).symm

/-- **The `M → ∞` step of Kingman's theorem, abstracted.**

Given averages `a n` whose truncations `max (a n) (-M)` converge a.e. to constants `c M`
decreasing in `M`, the averages themselves converge a.e. to `⨅ M, c M` in `EReal`. Nothing about
subadditivity, ergodicity or integrability enters: this is pure order/limit bookkeeping, and it
is what lets the forward, backward, balanced and one-sided forms of Kingman all be extended from
their `L¹` versions by the same three lines. -/
theorem ae_tendsto_of_ae_tendsto_max {μ : Measure Ω}
    {a : ℕ → Ω → ℝ} {c : ℕ → ℝ} (hcanti : ∀ M M' : ℕ, M ≤ M' → c M' ≤ c M)
    (hcae : ∀ M : ℕ, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => max (a n ω) (-(M : ℝ))) atTop (nhds (c M))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (a n ω : EReal)) atTop
      (nhds (⨅ M : ℕ, (c M : EReal))) := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have : NeZero μ := ⟨hμ⟩
  have hF2 : ∀ M : ℕ, (⨅ M : ℕ, (c M : EReal)) ≤ (c M : EReal) := fun M => iInf_le _ M
  have hF1 : ∀ b : ℝ, (⨅ M : ℕ, (c M : EReal)) < (b : EReal) → ∃ M : ℕ, c M < b := by
    intro b hb
    obtain ⟨M, hM⟩ := iInf_lt_iff.1 hb
    exact ⟨M, EReal.coe_lt_coe_iff.1 hM⟩
  rcases eq_or_ne (⨅ M : ℕ, (c M : EReal)) ⊥ with hCbot | hCbot
  · rw [hCbot]
    have hall : ∀ᵐ ω ∂μ, ∀ q : ℚ, ∀ᶠ n : ℕ in atTop, a n ω < (q : ℝ) := by
      refine ae_all_iff.mpr (fun q => ?_)
      obtain ⟨M, hM⟩ := hF1 (q : ℝ) (by rw [hCbot]; exact EReal.bot_lt_coe _)
      filter_upwards [hcae M] with ω hω
      filter_upwards [(tendsto_order.mp hω).2 (q : ℝ) hM] with n hn
      exact lt_of_le_of_lt (le_max_left _ _) hn
    filter_upwards [hall] with ω hω
    refine EReal.tendsto_coe_nhds_bot_iff.mpr (tendsto_atBot.mpr (fun b => ?_))
    obtain ⟨q, hq⟩ := exists_rat_lt b
    filter_upwards [hω q] with n hn
    exact le_of_lt (lt_trans hn hq)
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, (⨅ M : ℕ, (c M : EReal)) = (r : EReal) :=
      ⟨(⨅ M : ℕ, (c M : EReal)).toReal,
        (EReal.coe_toReal
          (lt_of_le_of_lt (iInf_le (fun M : ℕ => (c M : EReal)) 0)
            (EReal.coe_lt_top _)).ne hCbot).symm⟩
    rw [hr]
    obtain ⟨M₀, hM₀⟩ : ∃ M : ℕ, -(M : ℝ) < r := by
      obtain ⟨M, hM⟩ := exists_nat_gt (-r)
      exact ⟨M, by linarith⟩
    have hkey : ∀ M : ℕ, M₀ ≤ M →
        ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => a n ω) atTop (nhds (c M)) := by
      intro M hM
      have hlt : -(M : ℝ) < c M := by
        have h1' : r ≤ c M := by
          have := hF2 M; rw [hr] at this; exact EReal.coe_le_coe_iff.1 this
        have h2 : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        linarith
      filter_upwards [hcae M] with ω hω
      refine Filter.Tendsto.congr' ?_ hω
      filter_upwards [(tendsto_order.mp hω).1 (-(M : ℝ)) hlt] with n hn
      rcases max_cases (a n ω) (-(M : ℝ)) with ⟨h1', -⟩ | ⟨h1', -⟩
      · exact h1'
      · rw [h1'] at hn; exact absurd hn (lt_irrefl _)
    have hcM0 : c M₀ = r := by
      refine le_antisymm ?_ (by have := hF2 M₀; rw [hr] at this; exact EReal.coe_le_coe_iff.1 this)
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨b, hb1, hb2⟩ := exists_between hcon
      obtain ⟨M, hM⟩ := hF1 b (by rw [hr]; exact_mod_cast hb1)
      obtain ⟨ω, h1', h2⟩ := ((hkey (max M M₀) (le_max_right _ _)).and
        (hkey M₀ (le_refl _))).exists
      have heq : c (max M M₀) = c M₀ := tendsto_nhds_unique h1' h2
      have := hcanti M (max M M₀) (le_max_left _ _)
      rw [heq] at this
      linarith
    filter_upwards [hkey M₀ (le_refl _)] with ω hω
    rw [← hcM0]
    exact EReal.tendsto_coe.2 hω

/-- **The truncation constants of a subadditive family.**

For each level `M` the truncation `gᴹ = max(f, -M·)` is a genuinely `L¹` subadditive family
(bounded below by `-Mn`, above by the Birkhoff sums of `(f 1)⁺`), so `bkingman` plus Fekete give
a real constant `c M`, decreasing in `M`, with `max (f n / n) (-M) → c M` almost everywhere. The
Kingman constant is `⨅ M, c M`, and the means converge to it.

This is the whole content of `kingman` bar the final `M → ∞` step, factored out because the
balanced and one-sided forms need exactly the same constants. -/
theorem SubadditiveFamily.exists_truncation_limits {μ : Measure Ω} [IsProbabilityMeasure μ]
    {σ : Ω → Ω} (hσ : Ergodic σ μ) {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily σ f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) :
    ∃ c : ℕ → ℝ,
      (∀ M M' : ℕ, M ≤ M' → c M' ≤ c M) ∧
      (∀ M : ℕ, Tendsto (fun n : ℕ =>
        (∫ ω, SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ) n ω ∂μ) / n)
        atTop (nhds (c M))) ∧
      (∀ M : ℕ, ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ => max (f n ω / n) (-(M : ℝ))) atTop (nhds (c M))) ∧
      (∀ n : ℕ, 1 ≤ n →
        (⨅ M : ℕ, (c M : EReal)) ≤ lowerIntegral μ (fun ω => f n ω / n)) ∧
      Tendsto (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop
        (nhds (⨅ M : ℕ, (c M : EReal))) := by
  have hmp : MeasurePreserving σ μ μ := hσ.toMeasurePreserving
  set F : ℕ → Ω → ℝ := Function.update f 0 0 with hFdef
  have hF : SubadditiveFamily σ F := hf.update_zero
  have hFeq : ∀ {n : ℕ}, 1 ≤ n → F n = f n := fun {n} hn => SubadditiveFamily.update_zero_apply f hn
  have hFint : ∀ (M : ℕ) (n : ℕ), Integrable (SubadditiveFamily.truncate F (M : ℝ) n) μ :=
    fun M n => hf.truncate_integrable_update hmp h1 (M : ℝ) (Nat.cast_nonneg M) n
  -- for each truncation level, `bkingman` supplies a real Fekete constant
  have hmain : ∀ M : ℕ, ∃ c : ℝ,
      Tendsto (fun n : ℕ => (∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ) / n)
        atTop (nhds c) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => max (F n ω / n) (-(M : ℝ))) atTop (nhds c)) ∧
      (∀ n : ℕ, 1 ≤ n → c ≤ (∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ) / n) := by
    intro M
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hgsub : SubadditiveFamily σ (SubadditiveFamily.truncate F (M : ℝ)) :=
      hF.truncate_subadditive (M : ℝ)
    have hbdd : BddBelow (Set.range fun n : ℕ =>
        (∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ) / n) :=
      SubadditiveFamily.truncate_integral_bddBelow (M : ℝ) (hFint M)
    have husub : Subadditive (fun n => ∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ) :=
      SubadditiveFamily.subadditive_integral μ σ hmp _ hgsub (hFint M)
    refine ⟨husub.lim, husub.tendsto_lim hbdd, ?_, fun n hn => husub.lim_le_div hbdd (by omega)⟩
    have hlb : ∀ n ω, -((M : ℝ) * n) ≤ SubadditiveFamily.truncate F (M : ℝ) n ω :=
      fun n ω => le_max_right _ _
    filter_upwards [bkingman μ σ hσ (SubadditiveFamily.truncate F (M : ℝ)) hgsub (hFint M)
      (M : ℝ) hM0 hlb husub.lim (husub.tendsto_lim hbdd)] with ω hω
    exact hω.congr (fun n => SubadditiveFamily.truncate_div F hM0 n ω)
  choose c hcmean hcae hclb using hmain
  have hFeq' : ∀ {n : ℕ}, 1 ≤ n → F n = f n := hFeq
  have hcanti : ∀ M M' : ℕ, M ≤ M' → c M' ≤ c M := by
    intro M M' hMM'
    refine le_of_tendsto_of_tendsto' (hcmean M') (hcmean M) (fun n => ?_)
    have : (∫ ω, SubadditiveFamily.truncate F (M' : ℝ) n ω ∂μ)
        ≤ ∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ :=
      integral_mono (hFint M' n) (hFint M n)
        (fun ω => SubadditiveFamily.truncate_antitone F (by exact_mod_cast hMM') n ω)
    gcongr
  have hC3 : ∀ n : ℕ, 1 ≤ n →
      (⨅ M : ℕ, (c M : EReal)) ≤ lowerIntegral μ (fun ω => f n ω / n) := by
    intro n hn
    rw [lowerIntegral_div_eq n]
    refine le_iInf (fun M => ?_)
    refine le_trans (iInf_le (fun M : ℕ => (c M : EReal)) M) ?_
    have hcl := hclb M n hn
    have hFt : SubadditiveFamily.truncate F (M : ℝ) n = SubadditiveFamily.truncate f (M : ℝ) n := by
      funext ω; rw [SubadditiveFamily.truncate, SubadditiveFamily.truncate, hFeq hn]
    rw [hFt] at hcl
    exact_mod_cast hcl
  refine ⟨c, hcanti, hcmean, ?_, hC3, ?_⟩
  · -- transfer the truncated convergence from `F` to `f` (they agree from index 1 on)
    intro M
    filter_upwards [hcae M] with ω hω
    refine Filter.Tendsto.congr' ?_ hω
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hFeq hn]
  · -- the means, exactly as in `kingman`
    have hb : ∀ M : ℕ, Tendsto (fun n : ℕ =>
        (((∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ) / n : ℝ) : EReal)) atTop
        (nhds ((c M : EReal))) := fun M => EReal.tendsto_coe.2 (hcmean M)
    have hale : ∀ M : ℕ, ∀ᶠ n : ℕ in atTop,
        lowerIntegral μ (fun ω => f n ω / n)
          ≤ (((∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ) / n : ℝ) : EReal) := by
      intro M
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [lowerIntegral_div_eq n]
      refine le_trans (iInf_le _ M) (le_of_eq ?_)
      have hFt : SubadditiveFamily.truncate f (M : ℝ) n
          = SubadditiveFamily.truncate F (M : ℝ) n := by
        funext ω; rw [SubadditiveFamily.truncate, SubadditiveFamily.truncate, hFeq hn]
      rw [hFt]
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · refine le_liminf_of_le ?_ ?_
      · exact ⟨⊤, fun a _ => le_top⟩
      · filter_upwards [eventually_ge_atTop 1] with n hn using hC3 n hn
    · refine le_iInf (fun M => ?_)
      calc limsup (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop
          ≤ limsup (fun n : ℕ =>
              (((∫ ω, SubadditiveFamily.truncate F (M : ℝ) n ω ∂μ) / n : ℝ) : EReal)) atTop :=
            limsup_le_limsup (hale M)
        _ = (c M : EReal) := (hb M).limsup_eq

/-- **Kingman's subadditive ergodic theorem.**

For a subadditive family over an ergodic system, `f_n / n` converges almost everywhere to a
constant `C ∈ [-∞, ∞)`, which is also the limit of the means `(1/n) ∫ f_n`.

**Hypothesis.** Only `∫ (f 1)⁺ < ∞` is required — the positive part of the *first* level alone.
This is what the intended callers can actually supply: a cocycle's standing assumption is
`log⁺‖𝓛_ω‖ ∈ L¹`, and since `ρ_k ≤ ‖T‖` that gives `log⁺ ρ_k ≤ log⁺‖𝓛‖` and nothing whatever
about the negative part, which is `-∞` once `k` exceeds the rank.
The `L¹` form, as stated in `proof_met.tex` (l.406) and Kingman's original paper, states
it — cannot be applied there at all. That is why there is no separate `kingman_of_integrable`:
for the `L¹` case, invoke `kingman` and discharge the positive-part hypothesis from `f 1`.

**The mean clause** is stated with `lowerIntegral`, which supplies the meaning of `∫ f_n` off
`L¹`; on `L¹` it is the ordinary Bochner integral.

**Proof.** Truncate at level `-Mn`: `gᴹ = max(f, -M·)` is subadditive, bounded below, and bounded
above by the Birkhoff sums of `(f 1)⁺`, hence integrable, so `bkingman` applies and Fekete gives a
real constant `c M`. Set `C := ⨅_M c M`. The `M → ∞` argument is then the same one that already
takes `bkingman` to the `L¹` Kingman theorem, one level up — and it is *simpler* there, because
"some truncation level beats any `b > C`" is now just `iInf_lt_iff` rather than an appeal to
dominated convergence in `M`. The mean clause is likewise free: both limits are infima (Fekete
gives `lim = inf`), so they commute, and `liminf ≥ C` is immediate from `C ≤ (1/n) ∫ f_n`.

The degenerate index is handled by replacing `f` with `Function.update f 0 0`: subadditivity
forces `0 ≤ f 0` but never bounds it above, so `f 0` can fail to be integrable no matter how
well-behaved the rest of the family is. Every conclusion concerns `n → ∞`, so this costs
nothing. -/
theorem kingman (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ)
    (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) :
    ∃ C : EReal, C < ⊤ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => (f n ω / n : EReal)) atTop (nhds C)) ∧
      (∀ n : ℕ, 1 ≤ n → C ≤ lowerIntegral μ (fun ω => f n ω / n)) ∧
      Tendsto (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop (nhds C) := by
  obtain ⟨c, hcanti, -, hcae, hC3, hmean⟩ := hf.exists_truncation_limits hσ h1
  exact ⟨⨅ M : ℕ, (c M : EReal), lt_of_le_of_lt (iInf_le _ 0) (EReal.coe_lt_top _),
    ae_tendsto_of_ae_tendsto_max hcanti hcae, hC3, hmean⟩

/-- `zIter σ (-n)` is the `n`-fold iterate of `σ⁻¹`, as the definition intends. -/
theorem zIter_neg_natCast (σ : Ω ≃ᵐ Ω) (n : ℕ) (ω : Ω) :
    zIter σ (-(n : ℤ)) ω = (σ.symm)^[n] ω := by
  cases n with
  | zero => simp [zIter]
  | succ k => rfl

/-- `zIter σ n` on a natural `n` is the plain forward iterate. -/
theorem zIter_natCast (σ : Ω ≃ᵐ Ω) (n : ℕ) (ω : Ω) : zIter σ (n : ℤ) ω = σ^[n] ω := rfl

/-- `σ^n` undoes `(σ⁻¹)^n`. -/
theorem iterate_symm_cancel (σ : Ω ≃ᵐ Ω) : ∀ (m : ℕ) (y : Ω), σ^[m] ((σ.symm)^[m] y) = y := by
  intro m
  induction m with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', σ.apply_symm_apply]
    exact ih y

/-- **Corollary** (backward version, for invertible ergodic systems): the backward averages
`(1/n) f_n(σ⁻ⁿω)` converge a.e. to the *same* constant `C` given by Kingman's theorem for the
forward averages. -/
theorem kingman_backward_of_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hL1 : ∀ n, Integrable (f n) μ) (C : EReal)
    (hC : Tendsto (fun n => ((∫ ω, f n ω ∂μ) / n : EReal)) atTop (nhds C)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (f n (zIter σ (-n) ω) / n : EReal)) atTop (nhds C) := by
  -- Run `kingman` on the *inverse* system with the reversed family `F_n = f_n ∘ (σ⁻¹)ⁿ`.
  -- Subadditivity transposes: `f_{m+n} ≤ f_n ∘ σ^m + f_m` at the point `(σ⁻¹)^{m+n} ω` is
  -- exactly `F_{m+n}(ω) ≤ F_m((σ⁻¹)^n ω) + F_n(ω)`, because `σ^m (σ⁻¹)^{m+n} = (σ⁻¹)^n`.
  have hτerg : Ergodic ((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω) μ := hσ.symm
  have hτmp : MeasurePreserving ((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω) μ μ := hτerg.toMeasurePreserving
  have hcancel := iterate_symm_cancel σ
  have hFsub : SubadditiveFamily ((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)
      (fun n ω => f n ((σ.symm)^[n] ω)) := by
    refine ⟨fun n => (hf.1 n).comp (hτmp.measurable.iterate n), fun m n ω => ?_⟩
    have hsplit : ((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[m + n] ω
        = ((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[m] (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[n] ω) :=
      Function.iterate_add_apply _ m n ω
    have h := hf.2 n m (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[m]
      (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[n] ω))
    rw [hcancel m (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[n] ω), Nat.add_comm n m] at h
    change f (m + n) (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[m + n] ω)
      ≤ f m (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[m] (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[n] ω))
        + f n (((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω)^[n] ω)
    rw [hsplit]
    linarith
  have hFint : ∀ n, Integrable (fun ω => f n ((σ.symm)^[n] ω)) μ :=
    fun n => (hτmp.iterate n).integrable_comp_of_integrable (hL1 n)
  have hFmean : ∀ n : ℕ, ∫ ω, f n ((σ.symm)^[n] ω) ∂μ = ∫ ω, f n ω ∂μ := by
    intro n
    have hmap : Measure.map ((σ.symm)^[n]) μ = μ := (hτmp.iterate n).map_eq
    calc ∫ ω, f n ((σ.symm)^[n] ω) ∂μ = ∫ ω, f n ω ∂(Measure.map ((σ.symm)^[n]) μ) :=
          (integral_map (hτmp.iterate n).measurable.aemeasurable
            (by rw [hmap]; exact (hL1 n).aestronglyMeasurable)).symm
      _ = ∫ ω, f n ω ∂μ := by rw [hmap]
  obtain ⟨C', -, hC'ae, -, hC'mean⟩ :=
    kingman μ ((σ.symm : Ω ≃ᵐ Ω) : Ω → Ω) hτerg (fun n ω => f n ((σ.symm)^[n] ω)) hFsub
      ((hFint 1).sup (integrable_const 0))
  have hC'int := tendsto_mean_of_lowerIntegral hFint hC'mean
  have hCC' : C' = C := by
    refine tendsto_nhds_unique ?_ hC
    simpa only [hFmean] using hC'int
  rw [hCC'] at hC'ae
  filter_upwards [hC'ae] with ω hω
  refine hω.congr (fun n => ?_)
  rw [zIter_neg_natCast]

/-- **L¹ orbit-decay.** For a measure-preserving `σ` and `g ∈ L¹`,
`(1/n) g(σⁿ ω) → 0` almost everywhere. The general Birkhoff adapter supplies convergence
of the averages; their telescoping difference tends to `L - L = 0`.
This argument needs measure preservation, independently of ergodicity or Kingman's theorem. -/
theorem L1_orbit_decay (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω)
    (hmp : MeasurePreserving σ μ μ) (g : Ω → ℝ) (hg : Measurable g) (hgL1 : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => g (σ^[n] ω) / n) atTop (nhds 0) := by
  set h : ℕ → Ω → ℝ := fun n => birkhoffSum σ g n with hh
  -- `(n+1)/n → 1`, obtained as the reciprocal of `n/(n+1) → 1`.
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (nhds 1) := by
    have := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ one_ne_zero
    simpa [inv_div] using this
  filter_upwards [ae_tendsto_birkhoffAverage hmp g hg hgL1] with ω hωex
  obtain ⟨L, hL⟩ := hωex
  have hω : Tendsto (fun n => h n ω / (n : ℝ)) atTop (nhds L) := by
    simpa only [birkhoffAverage_real, hh] using hL
  -- `h_{n+1}(ω)/(n+1) → L`, then `h_{n+1}(ω)/n → L`.
  have hshift : Tendsto (fun n => h (n + 1) ω / ((n : ℝ) + 1)) atTop (nhds L) := by
    have := hω.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
  have hshift' : Tendsto (fun n => h (n + 1) ω / (n : ℝ)) atTop (nhds L) := by
    have hp := hshift.mul hratio
    rw [mul_one] at hp
    refine hp.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  -- `g(σⁿω)/n = h_{n+1}(ω)/n - h_n(ω)/n → L - L = 0`.
  have hdiff : Tendsto (fun n => h (n + 1) ω / (n : ℝ) - h n ω / (n : ℝ)) atTop (nhds 0) := by
    have := hshift'.sub hω
    rwa [sub_self] at this
  refine hdiff.congr ?_
  intro n
  have hstep : h (n + 1) ω = h n ω + g (σ^[n] ω) := by
    simp only [hh]
    simpa only [Pi.add_apply, Function.comp_apply] using congrFun (birkhoffSum_succ σ g n) ω
  rw [← sub_div, hstep]
  ring

end MultiplicativeErgodic
