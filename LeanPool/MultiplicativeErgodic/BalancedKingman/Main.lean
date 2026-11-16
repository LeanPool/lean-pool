/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BalancedKingman.Pointwise

/-!
# The balanced Kingman theorem

`balancedKingman` and `kingsyn`, in the general form assuming only that the positive parts are
integrable, together with the `L¹` sibling `balancedKingman_of_integrable`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-- Ordinary forward and backward Kingman limits give the upper bound for balanced averages. -/
private theorem balanced_averages_eventually_lt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hL1 : ∀ n, Integrable (f n) μ) (C : ℝ)
    (hC : Tendsto (fun n => (∫ ω, f n ω ∂μ) / n) atTop (nhds C)) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, C < b →
      ∀ᶠ n in atTop, f (2 * n) (zIter σ (-n) ω) / (2 * n) < b := by
  -- `zIter σ (n : ℤ)` is the plain forward iterate `σ^[n]`, and `σ^[n]` cancels `zIter σ (-n)`.
  -- Needed to unfold subadditivity at the point `zIter σ (-n) ω`.
  have hcast : ∀ (n : ℕ) (ω : Ω), zIter σ (n : ℤ) ω = σ^[n] ω := fun n ω => by
    rw [zIter_eq_zpow, zpow_natCast, Equiv.Perm.coe_pow,
      show (⇑σ.toEquiv : Ω → Ω) = ⇑σ from MeasurableEquiv.coe_toEquiv σ]
  have hcancel : ∀ (n : ℕ) (ω : Ω), σ^[n] (zIter σ (-(n : ℤ)) ω) = ω := by
    intro n ω
    rw [← hcast n (zIter σ (-(n : ℤ)) ω), ← zIter_add,
      show (n : ℤ) + -(n : ℤ) = 0 from by ring, zIter_zero_apply]
  -- Ordinary (forward and backward) Kingman, identifying both limits with `C` via `hC`.
  have hCae : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω / n) atTop (nhds C) :=
    kingman_real_of_integrable μ σ hσ f hf hL1 C hC
  have hCback : ∀ᵐ ω ∂μ, Tendsto (fun n => f n (zIter σ (-n) ω) / n) atTop (nhds C) :=
    kingman_backward_real_of_integrable μ σ hσ f hf hL1 C hC
  -- **Upper bound `limsup (1/2n) f_{2n}(σ⁻ⁿω) ≤ C`** (paper `human/proof_met.tex` lines 496-503):
  -- subadditivity gives `f_{2n}(σ⁻ⁿω) ≤ f_n(σ⁻ⁿω) + f_n(ω)`, and dividing by `2n` and averaging the
  -- two (ordinary) Kingman limits gives a sequence `≥` the balanced average that itself tends to
  -- `C`; hence the balanced average is eventually `< b` for every `b > C`. This half needs only
  -- `kingman_of_integrable`/`kingman_backward_of_integrable`, no Vitali machinery.
  have hupper : ∀ᵐ ω ∂μ, ∀ b : ℝ, C < b →
      ∀ᶠ n in atTop, f (2 * n) (zIter σ (-n) ω) / (2 * n) < b := by
    filter_upwards [hCae, hCback] with ω hae hback
    intro b hb
    have hcomb : Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) * (f n (zIter σ (-n) ω) / n) + (1 / 2 : ℝ) * (f n ω / n))
        atTop (nhds ((1 / 2 : ℝ) * C + (1 / 2 : ℝ) * C)) :=
      (hback.const_mul (1 / 2 : ℝ)).add (hae.const_mul (1 / 2 : ℝ))
    have hRHS : Tendsto (fun n : ℕ => f n (zIter σ (-n) ω) / (2 * n) + f n ω / (2 * n))
        atTop (nhds C) := by
      have heq : (1 / 2 : ℝ) * C + (1 / 2 : ℝ) * C = C := by ring
      rw [heq] at hcomb
      refine hcomb.congr (fun n => ?_)
      ring
    filter_upwards [(tendsto_order.mp hRHS).2 b hb, eventually_gt_atTop (0 : ℕ)] with n hlt hpos
    have hle : f (2 * n) (zIter σ (-n) ω) ≤ f n (zIter σ (-n) ω) + f n ω := by
      have h := hf.2 n n (zIter σ (-n) ω)
      rw [hcancel n ω, ← two_mul] at h
      linarith
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have h2n : (0 : ℝ) < 2 * (n : ℝ) := by linarith
    calc f (2 * n) (zIter σ (-n) ω) / (2 * (n : ℝ))
        ≤ (f n (zIter σ (-n) ω) + f n ω) / (2 * (n : ℝ)) :=
          div_le_div_of_nonneg_right hle h2n.le
      _ = f n (zIter σ (-n) ω) / (2 * (n : ℝ)) + f n ω / (2 * (n : ℝ)) := by ring
      _ < b := hlt
  exact hupper

/-- **Theorem \ref{balancedkingman} (Kingman's theorem for balanced intervals).** For an
ergodic system with invertible base and an `L¹` subadditive family, the *balanced* averages
`(1/2n) f_{2n}(σ⁻ⁿω)` converge a.e. to the same Kingman constant `C`. This is the paper's own
refinement of Kingman's theorem and its hardest single argument (it uses `backwardVitali`
essentially). -/
theorem balancedKingman_of_integrable [StandardBorelSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hL1 : ∀ n, Integrable (f n) μ) (C : ℝ)
    (hC : Tendsto (fun n => (∫ ω, f n ω ∂μ) / n) atTop (nhds C)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f (2 * n) (zIter σ (-n) ω) / (2 * n)) atTop (nhds C) := by
  have hcast : ∀ (n : ℕ) (ω : Ω), zIter σ (n : ℤ) ω = σ^[n] ω := fun n ω => by
    rw [zIter_eq_zpow, zpow_natCast, Equiv.Perm.coe_pow,
      show (⇑σ.toEquiv : Ω → Ω) = ⇑σ from MeasurableEquiv.coe_toEquiv σ]
  have hupper := balanced_averages_eventually_lt μ σ hσ f hf hL1 C hC
  -- **The hard direction (`liminf ≥ C`), paper `human/proof_met.tex` lines 504-612.**
  -- Notation: `a n ω := f (2n) (σ⁻ⁿω) / (2n)`, the balanced average sequence itself.
  set a : ℕ → Ω → ℝ := fun n ω => f (2 * n) (zIter σ (-n) ω) / (2 * n) with hadef
  have hupper' : ∀ᵐ ω ∂μ, ∀ b : ℝ, C < b → ∀ᶠ n in atTop, a n ω < b := hupper
  -- `zIter σ (-n)` is `(σ⁻¹)ⁿ`, which is what makes `a n` measurable and lets the shift
  -- computation below be read as a statement about the *inverse* map.
  have hameas : ∀ n : ℕ, Measurable (a n) := by
    intro n
    have h1 : a n = fun ω => f (2 * n) ((σ.symm : Ω ≃ᵐ Ω)^[n] ω) / (2 * n) := by
      funext ω
      simp only [hadef]
      rw [zIter_neg_natCast]
    rw [h1]
    exact ((hf.1 (2 * n)).comp (σ.symm.measurable.iterate n)).div_const _
  -- **Paper's key shift computation (first display of the `liminf` argument), Step 1 of 2:**
  -- the pure-subadditivity inequality `f_{2n}(σ^{-(n+1)}ω) ≥ f_{2(n+1)}(σ^{-(n+1)}ω) -
  -- f_2(σ^{n-1}ω)`,
  -- from `SubadditiveFamily` applied with `(m,k) = (2, 2n)` at the point `x = σ^{-(n+1)}ω`
  -- (so `σ^{2n} x = σ^{n-1}ω`).
  have hstep : ∀ (n : ℕ) (ω : Ω),
      f (2 * (n + 1)) (zIter σ (-((n : ℤ) + 1)) ω) ≤
        f 2 (zIter σ ((n : ℤ) - 1) ω) + f (2 * n) (zIter σ (-((n : ℤ) + 1)) ω) := by
    intro n ω
    have h := hf.2 2 (2 * n) (zIter σ (-((n : ℤ) + 1)) ω)
    have hσiter : σ^[2 * n] (zIter σ (-((n : ℤ) + 1)) ω) = zIter σ ((n : ℤ) - 1) ω := by
      rw [← hcast (2 * n) (zIter σ (-((n : ℤ) + 1)) ω), ← zIter_add]
      congr 1
      push_cast; ring
    rw [hσiter, show (2 + 2 * n) = 2 * (n + 1) from by ring] at h
    exact h
  -- **Step 2: the boundary term of the shift vanishes.** `f_2(σ^{n-1}ω)/(2n) → 0` a.e., by
  -- `L1_orbit_decay` for the single `L¹` observable `f 2`, reindexed along `n ↦ n - 1`
  -- (`tendsto_orbit_div_of_ratio`, ratio `→ 1`).
  have hdecay : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => f 2 (zIter σ ((n : ℤ) - 1) ω) / (2 * (n : ℝ))) atTop (nhds 0) := by
    filter_upwards [L1_orbit_decay μ σ hσ (f 2) (hf.1 2) (hL1 2)] with ω hω
    have hidx : Tendsto (fun n : ℕ => n - 1) atTop atTop := tendsto_sub_atTop_nat 1
    have hratio : Tendsto (fun n : ℕ => (((n - 1 : ℕ)) : ℝ) / n) atTop (nhds 1) := by
      have hbase : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
      rw [sub_zero] at hbase
      refine hbase.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by
        have : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn
        exact ne_of_gt this
      have hcast' : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
        have : (1 : ℕ) ≤ n := hn
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast']
      field_simp
    have h0 := tendsto_orbit_div_of_ratio hω (fun n => n - 1) hidx 1 hratio
    have h1 := h0.div_const 2
    rw [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hz : zIter σ ((n : ℤ) - 1) ω = σ^[n - 1] ω := by
      rw [← hcast (n - 1) ω]
      congr 1
      have : (1 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub this]
      ring
    rw [hz]
    ring
  -- **Step 3: the threshold sets are `σ⁻¹`-invariant, hence null or conull.**
  -- `liminf a(σ⁻¹ω) ≥ liminf a(ω)` is exactly `S ⊆ (σ⁻¹)⁻¹ S` for `S = {liminf a ≥ q}`, the
  -- shape `measure_liminfGE_eq_zero_or_one'` wants; `Ergodic.symm` supplies ergodicity of `σ⁻¹`.
  -- `σ^{-n}(σ⁻¹ω) = σ^{-(n+1)}ω`, the point identity behind the shift.
  have hshiftpt : ∀ (n : ℕ) (ω : Ω),
      zIter σ (-(n : ℤ)) ((σ.symm : Ω → Ω) ω) = zIter σ (-((n : ℤ) + 1)) ω := by
    intro n ω
    rw [zIter_neg_natCast,
      show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) from by push_cast; ring,
      zIter_neg_natCast, Function.iterate_succ_apply]
  have hinv : ∀ q : ℝ, (liminfGE a q : Set Ω) ≤ᵐ[μ] (σ.symm : Ω → Ω) ⁻¹' liminfGE a q := by
    intro q
    filter_upwards [hdecay] with ω hdec hmem
    simp only [liminfGE] at hmem ⊢
    intro ε hε
    have hε0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨ε', hε'pos, hε'lt⟩ : ∃ e : ℚ, 0 < e ∧ (e : ℝ) ≤ (ε : ℝ) / 3 :=
      ⟨ε / 3, by positivity, by push_cast; linarith⟩
    obtain ⟨N₀, hN₀⟩ := hmem ε' hε'pos
    -- the two correction terms, both `→ 0`
    have h2 : Tendsto (fun n : ℕ => (q - (ε' : ℝ)) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hdec ((ε : ℝ) / 3) (by positivity)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp h2 ((ε : ℝ) / 3) (by positivity)
    refine ⟨max (max N₀ N₁) (max N₂ 1), fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right N₂ 1) (le_max_right _ _)) hn
    have hnN₀ : N₀ ≤ n + 1 :=
      le_trans (le_trans (le_trans (le_max_left N₀ N₁) (le_max_left _ _)) hn) (Nat.le_succ n)
    have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_right N₀ N₁) (le_max_left _ _)) hn
    have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_left N₂ 1) (le_max_right _ _)) hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    -- `a n (σ⁻¹ω)` is the balanced average at the shifted base point
    have hbase : a n ((σ.symm : Ω → Ω) ω)
        = f (2 * n) (zIter σ (-((n : ℤ) + 1)) ω) / (2 * (n : ℝ)) := by
      simp only [hadef]
      rw [hshiftpt n ω]
    -- rewrite `f (2(n+1)) (σ^{-(n+1)}ω)` as `2(n+1) · a (n+1) ω`
    have hAeq : a (n + 1) ω
        = f (2 * (n + 1)) (zIter σ (-((n : ℤ) + 1)) ω) / (2 * ((n : ℝ) + 1)) := by
      simp only [hadef]
      push_cast
      rfl
    have hnext : f (2 * (n + 1)) (zIter σ (-((n : ℤ) + 1)) ω)
        = 2 * ((n : ℝ) + 1) * a (n + 1) ω := by
      have hne : (2 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [hAeq]
      field_simp
    have hineq := hstep n ω
    rw [hnext] at hineq
    -- divide through by `2n`
    have hkey : 2 * ((n : ℝ) + 1) * a (n + 1) ω / (2 * (n : ℝ))
        - f 2 (zIter σ ((n : ℤ) - 1) ω) / (2 * (n : ℝ)) ≤ a n ((σ.symm : Ω → Ω) ω) := by
      rw [hbase, ← sub_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      linarith
    -- `(1 + 1/n) · a(n+1)ω ≥ (q - ε') + (q - ε')/n`
    have hA : (q : ℝ) - (ε' : ℝ) < a (n + 1) ω := hN₀ (n + 1) hnN₀
    have hsplit : 2 * ((n : ℝ) + 1) * a (n + 1) ω / (2 * (n : ℝ))
        = a (n + 1) ω + a (n + 1) ω / (n : ℝ) := by field_simp
    have hfrac : ((q : ℝ) - (ε' : ℝ)) / (n : ℝ) ≤ a (n + 1) ω / (n : ℝ) :=
      div_le_div_of_nonneg_right hA.le hn0.le
    have hb1 := hN₁ n hnN₁
    have hb2 := hN₂ n hnN₂
    rw [Real.dist_eq, sub_zero, abs_lt] at hb1 hb2
    have hle3 : (ε' : ℝ) ≤ (ε : ℝ) / 3 := hε'lt
    rw [hsplit] at hkey
    linarith [hkey, hA, hfrac, hb1.1, hb1.2, hb2.1, hb2.2]
  have hzo : ∀ q : ℝ, μ (liminfGE a q) = 0 ∨ μ (liminfGE a q) = 1 := fun q =>
    measure_liminfGE_eq_zero_or_one' hσ.symm hameas q (hinv q)
  -- **Step 4 (the paper's covering argument, `proof_met.tex` lines 517-612): `C ≤ C_hat`.**
  --
  -- Stated in the null-threshold form, which is what the zero-one law consumes: if a.e. `ω` has
  -- `liminf a < q` — equivalently the good times `{j : f_{-j→j}(ω) < 2jq}` are infinite a.e. —
  -- then `C ≤ q`. Everything above is independent of this, and the final assembly below needs
  -- nothing else from the covering machinery.
  --
  -- **The argument**, all of it discharged by `covering_bound` (`BalancedKingman.Pointwise`),
  -- which is where the map of the chain lives. Two things about it are worth knowing here:
  --
  --  * `exists_good_windows` applies `backwardVitali`, and so **needs `[StandardBorelSpace Ω]`
  --    and `[NullSingletonClass μ]`** — the paper's "Lebesgue probability space" hypothesis,
  --    absent from a bare `Ergodic σ μ`. That is why this theorem, `kingsyn` and `Cocycle` all
  --    carry them.
  --  * The integration, not Birkhoff, is what closes the estimate: `(1/n) ∫ S_n g = ∫ g` is pure
  --    measure preservation (`integral_birkhoffSum`), so the covering argument needs no
  --    pointwise ergodic theorem of its own.
  --
  -- Finally let `n → ∞` then `ε → 0` in `C - ε ≤ q + ε(|q| + ε) + 3ε + 2Mε/n`.
  have hcovering : ∀ q : ℝ, μ (liminfGE a q) = 0 → C ≤ q := by
    intro q hq
    refine covering_bound μ σ hσ f hf hL1 C hC q ?_
    have hae : ∀ᵐ ω ∂μ, ω ∉ liminfGE a q := by
      rw [ae_iff]
      simpa using hq
    filter_upwards [hae] with ω hω
    -- `ω ∉ {liminf a ≥ q}` gives a rational margin `ep` and infinitely many times below it
    have hex : ∃ ep : ℚ, 0 < ep ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ω ≤ q - (ep : ℝ) := by
      by_contra hc
      refine hω (fun ep hep => ?_)
      by_contra hc2
      exact hc ⟨ep, hep, fun N => by
        by_contra hc3
        exact hc2 ⟨N, fun n hn => by
          by_contra hc4
          exact hc3 ⟨n, hn, le_of_not_gt hc4⟩⟩⟩
    obtain ⟨ep, hep, hN⟩ := hex
    intro k
    obtain ⟨n, hn, hle⟩ := hN (max k 1)
    have hk : k ≤ n := le_trans (le_max_left _ _) hn
    have h1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    refine ⟨n, hk, h1, ?_⟩
    have hepR : (0 : ℝ) < (ep : ℝ) := by exact_mod_cast hep
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h1
    have hlt : f (2 * n) (zIter σ (-(n : ℤ)) ω) / (2 * (n : ℝ)) < q := by
      have hlt' : a n ω < q := by linarith
      exact hlt'
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (n : ℝ))] at hlt
    calc f (2 * n) (zIter σ (-(n : ℤ)) ω) < q * (2 * (n : ℝ)) := hlt
      _ = 2 * (n : ℝ) * q := by ring
  -- **Assembly.** Below `C` every threshold set is conull (by `hcovering` + the zero-one law),
  -- so `liminf a ≥ C` a.e.; `hupper` gives `limsup a ≤ C`; together, `a n ω → C`.
  have hfull : ∀ q : ℚ, (q : ℝ) < C → μ (liminfGE a (q : ℝ)) = 1 := by
    intro q hq
    rcases hzo (q : ℝ) with h | h
    · exact absurd (hcovering (q : ℝ) h) (not_le.mpr hq)
    · exact h
  have hmemq : ∀ᵐ ω ∂μ, ∀ q : ℚ, (q : ℝ) < C → ω ∈ liminfGE a (q : ℝ) := by
    refine ae_all_iff.mpr (fun q => ?_)
    by_cases hq : (q : ℝ) < C
    · have hmeas : MeasurableSet (liminfGE a (q : ℝ)) := measurableSet_liminfGE hameas _
      have hcompl : μ (liminfGE a (q : ℝ))ᶜ = 0 := by
        rw [measure_compl hmeas (measure_ne_top μ _), hfull q hq, measure_univ, tsub_self]
      have hae : ∀ᵐ ω ∂μ, ω ∈ liminfGE a (q : ℝ) := ae_iff.mpr hcompl
      filter_upwards [hae] with ω hω _
      exact hω
    · filter_upwards with ω h; exact absurd h hq
  filter_upwards [hupper', hmemq] with ω hup hlow
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- upper: eventually `a n ω < C + δ`
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hup (C + δ) (by linarith))
  -- lower: pick a rational `q ∈ (C - δ/2, C)` and a rational `ε` with `q - ε > C - δ`
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show C - δ / 2 < C by linarith)
  obtain ⟨e, he1, he2⟩ : ∃ e : ℚ, 0 < e ∧ C - δ < (q : ℝ) - (e : ℝ) := by
    obtain ⟨e, he1, he2⟩ := exists_rat_btwn (show (0:ℝ) < (q : ℝ) - (C - δ) by linarith)
    exact ⟨e, by exact_mod_cast he1, by linarith⟩
  obtain ⟨N₂, hN₂⟩ := hlow q hq2 e he1
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Kingman's theorem for balanced intervals, under the general hypothesis.**

The `L¹` form is `balancedKingman_of_integrable`. The extension is again by truncation, and it
needs none of the covering argument redone: the `L¹` theorem applied to `gᴹ = max(f, -M·)` gives
`max (f_{2n}(σ⁻ⁿω)/(2n)) (-M) → c M` for the *same* constants `c M` that
`exists_truncation_limits` produces — the balanced theorem's hypothesis is about the ordinary
means, so the constants agree — and `ae_tendsto_of_ae_tendsto_max` takes `M → ∞`. -/
theorem balancedKingman [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily (⇑σ) f) (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) :
    ∃ C : EReal, C < ⊤ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f (2 * n) (zIter σ (-n) ω) / (2 * n) : EReal)) atTop
        (nhds C)) ∧
      Tendsto (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop (nhds C) := by
  have hmp : MeasurePreserving (⇑σ) μ μ := hσ.toMeasurePreserving
  obtain ⟨c, hcanti, hcmean, -, -, hmean⟩ := hf.exists_truncation_limits hσ h1
  have hF : SubadditiveFamily (⇑σ) (Function.update f 0 0) := hf.update_zero
  have hFeq : ∀ {n : ℕ}, 1 ≤ n → Function.update f 0 0 n = f n :=
    fun {n} hn => SubadditiveFamily.update_zero_apply f hn
  have hstep : ∀ M : ℕ, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => max (f (2 * n) (zIter σ (-n) ω) / (2 * n)) (-(M : ℝ))) atTop
        (nhds (c M)) := by
    intro M
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hint := fun n => hf.truncate_integrable_update hmp h1 (M : ℝ) hM0 n
    have hres := balancedKingman_of_integrable μ σ hσ
      (SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ))
      (hF.truncate_subadditive (M : ℝ)) hint (c M) (hcmean M)
    filter_upwards [hres] with ω hω
    refine Filter.Tendsto.congr' ?_ hω
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h2n : 1 ≤ 2 * n := by omega
    have hdiv := SubadditiveFamily.truncate_div (Function.update f 0 0) hM0 (2 * n)
      (zIter σ (-(n : ℤ)) ω)
    have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rw [← hcast, hdiv, hFeq h2n]
  exact ⟨⨅ M : ℕ, (c M : EReal), lt_of_le_of_lt (iInf_le _ 0) (EReal.coe_lt_top _),
    ae_tendsto_of_ae_tendsto_max hcanti hstep, hmean⟩

/-- **All three convergence types, from the forward one alone.**

If a subadditive family with `∫ (f 1)⁺ < ∞` has `f_n/n → C` almost everywhere for a *real* `C`,
then the shifted and balanced averages converge a.e. to the same `C`. The three general theorems
each produce their own constant, but all three also converge to it in the mean
(`lowerIntegral`), so uniqueness of limits identifies them with each other and — via the given
forward convergence — with `C`.

Packaged because `kingsyn` needs exactly this, for two families at once. -/
theorem SubadditiveFamily.three_limits [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {σ : Ω ≃ᵐ Ω} (hσ : Ergodic (⇑σ) μ)
    {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily (⇑σ) f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) (C : ℝ)
    (hC : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω / n) atTop (nhds C)) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n (σ^[n] ω) / n) atTop (nhds C)) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (2 * n) (zIter σ (-n) ω) / (2 * n)) atTop (nhds C)) := by
  obtain ⟨C1, -, hae1, -, hm1⟩ := kingman μ (⇑σ) hσ f hf h1
  obtain ⟨C2, -, hae2, hm2⟩ := easyking μ (⇑σ) hσ f hf h1
  obtain ⟨C3, -, hae3, hm3⟩ := balancedKingman μ σ hσ f hf h1
  -- all three constants are the limit of the same sequence of means
  have h12 : C1 = C2 := tendsto_nhds_unique hm1 hm2
  have h13 : C1 = C3 := tendsto_nhds_unique hm1 hm3
  -- and the forward clause identifies `C1` with `C`
  have hCC : C1 = (C : EReal) := by
    obtain ⟨ω, hω1, hωC⟩ := (hae1.and hC).exists
    exact tendsto_nhds_unique hω1 (EReal.tendsto_coe.2 hωC)
  rw [hCC] at h12 h13
  constructor
  · filter_upwards [hae2] with ω hω
    rw [← h12] at hω
    exact EReal.tendsto_coe.1 hω
  · filter_upwards [hae3] with ω hω
    rw [← h13] at hω
    exact EReal.tendsto_coe.1 hω

/-- **The three limits agree, with an `EReal` constant** -- so the case `C = -∞` is covered.

This is the form `kingman`, `easyking` and `balancedKingman` actually produce, and it is strictly
more general than `three_limits` above, which requires the constant to be finite. It is also
shorter: the real version has to coerce in and out of `EReal` at both ends, whereas here the three
constants supplied by the three theorems are compared directly. -/
theorem SubadditiveFamily.three_limits_ereal [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {σ : Ω ≃ᵐ Ω} (hσ : Ergodic (⇑σ) μ)
    {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily (⇑σ) f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) (C : EReal)
    (hC : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n ω / n : EReal)) atTop (nhds C)) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n (σ^[n] ω) / n : EReal)) atTop (nhds C)) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
        (f (2 * n) (zIter σ (-n) ω) / (2 * n) : EReal)) atTop (nhds C)) := by
  obtain ⟨C1, -, hae1, -, hm1⟩ := kingman μ (⇑σ) hσ f hf h1
  obtain ⟨C2, -, hae2, hm2⟩ := easyking μ (⇑σ) hσ f hf h1
  obtain ⟨C3, -, hae3, hm3⟩ := balancedKingman μ σ hσ f hf h1
  have h12 : C1 = C2 := tendsto_nhds_unique hm1 hm2
  have h13 : C1 = C3 := tendsto_nhds_unique hm1 hm3
  have hCC : C1 = C := by
    obtain ⟨ω, hω1, hωC⟩ := (hae1.and hC).exists
    exact tendsto_nhds_unique hω1 hωC
  rw [hCC] at h12 h13
  refine ⟨?_, ?_⟩
  · filter_upwards [hae2] with ω hω; rwa [h12]
  · filter_upwards [hae3] with ω hω; rwa [h13]

/-- **Synthesis for weakly subadditive families, under the general hypothesis.**

There is no `L¹` sibling: `f` and `g` need only `∫ (f 1)⁺ < ∞` and `∫ (g 1)⁺ < ∞` — the same
condition as `kingman` — so for an `L¹` family just invoke this and discharge those from `f 1`,
`g 1`. The flat additive slop `Cconst`, `Dconst` is absorbed exactly as before, since
`max (u + c) 0 ≤ max u 0 + |c|`. (`kingsyn`, below, drops this theorem's restriction to *finite*
`Cf`, `Cg`.)

**The constants are given by their almost-everywhere limits, not their means.** An `L¹` version
would take `hCf : (1/n) ∫ f_n → Cf`; off `L¹` that would have to be read through `lowerIntegral`,
and
relating `lowerIntegral (f_n + c)` to `lowerIntegral f_n` needs `⨅`-arithmetic in `EReal` that
Mathlib does not provide. Taking the hypothesis as `f_n/n → Cf` almost everywhere avoids it
entirely: the shift by `Cconst/n → 0` is then visible pointwise. It is also the form the cocycle
application has to hand, since that is what `kingman` produces. `Cf`, `Cg` are real, which is
exactly the assumption that the two constants are finite — needed anyway, since `Cf + t * Cg` is
not well defined in `EReal` for `t < 0`. -/
theorem kingsyn_real [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ)
    (f g : ℕ → Ω → ℝ) (Cconst Dconst : ℝ)
    (hf : (∀ n, Measurable (f n)) ∧ ∀ m n ω, f (m + n) ω ≤ f m (σ^[n] ω) + f n ω + Cconst)
    (hg : (∀ n, Measurable (g n)) ∧ ∀ m n ω, g (m + n) ω ≤ g m (σ^[n] ω) + g n ω + Dconst)
    (hf1 : Integrable (fun ω => max (f 1 ω) 0) μ)
    (hg1 : Integrable (fun ω => max (g 1 ω) 0) μ)
    (t : ℝ) (Cf Cg : ℝ)
    (hCf : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω / n) atTop (nhds Cf))
    (hCg : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => g n ω / n) atTop (nhds Cg)) :
    let h : ℕ → Ω → ℝ := fun n ω => f n ω + t * g n ω
    ∀ᵐ ω ∂μ, Tendsto (fun n => h n (σ^[n] ω) / n) atTop (nhds (Cf + t * Cg)) ∧
      Tendsto (fun n => h (2 * n) (zIter σ (-n) ω) / (2 * n)) atTop (nhds (Cf + t * Cg)) ∧
      Tendsto (fun n => h n ω / n) atTop (nhds (Cf + t * Cg)) := by
  change ∀ᵐ ω ∂μ,
      Tendsto (fun n => (f n (σ^[n] ω) + t * g n (σ^[n] ω)) / n) atTop (nhds (Cf + t * Cg)) ∧
      Tendsto (fun n => (f (2 * n) (zIter σ (-n) ω) + t * g (2 * n) (zIter σ (-n) ω)) / (2 * n))
        atTop (nhds (Cf + t * Cg)) ∧
      Tendsto (fun n => (f n ω + t * g n ω) / n) atTop (nhds (Cf + t * Cg))
  set f' : ℕ → Ω → ℝ := fun n ω => f n ω + Cconst with hf'def
  set g' : ℕ → Ω → ℝ := fun n ω => g n ω + Dconst with hg'def
  have hf'sub : SubadditiveFamily (⇑σ) f' := by
    refine ⟨fun n => (hf.1 n).add_const Cconst, fun m n ω => ?_⟩
    have := hf.2 m n ω
    simp only [hf'def]
    linarith
  have hg'sub : SubadditiveFamily (⇑σ) g' := by
    refine ⟨fun n => (hg.1 n).add_const Dconst, fun m n ω => ?_⟩
    have := hg.2 m n ω
    simp only [hg'def]
    linarith
  -- the positive-part hypothesis survives the flat shift
  have hshift : ∀ (u : Ω → ℝ) (c : ℝ), Measurable u → Integrable (fun ω => max (u ω) 0) μ →
      Integrable (fun ω => max (u ω + c) 0) μ := by
    intro u c hum hu
    refine Integrable.mono' (hu.add (integrable_const |c|))
      ((hum.add_const c).max measurable_const).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    have h1 : u ω ≤ max (u ω) 0 := le_max_left _ _
    have h2 : (0 : ℝ) ≤ max (u ω) 0 := le_max_right _ _
    have h3 : c ≤ |c| := le_abs_self c
    have h5 : (0 : ℝ) ≤ |c| := abs_nonneg c
    rcases max_choice (u ω + c) 0 with h | h <;> rw [h]
    · have hge : (0 : ℝ) ≤ u ω + c := by rw [← h]; exact le_max_right _ _
      rw [abs_of_nonneg hge]
      simp only [Pi.add_apply]; linarith
    · simp only [Pi.add_apply, abs_zero]; linarith
  have hf'1 : Integrable (fun ω => max (f' 1 ω) 0) μ := hshift (f 1) Cconst (hf.1 1) hf1
  have hg'1 : Integrable (fun ω => max (g' 1 ω) 0) μ := hshift (g 1) Dconst (hg.1 1) hg1
  -- the shift does not move the a.e. constant, since `Cconst / n → 0`
  have hshiftlim : ∀ (u : ℕ → Ω → ℝ) (c C : ℝ),
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => u n ω / n) atTop (nhds C)) →
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (u n ω + c) / n) atTop (nhds C) := by
    intro u c C hu
    filter_upwards [hu] with ω hω
    have := hω.add (tendsto_const_div_atTop_nhds_zero_nat c)
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hCf' : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f' n ω / n) atTop (nhds Cf) := hshiftlim f Cconst
    Cf hCf
  have hCg' : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => g' n ω / n) atTop (nhds Cg) := hshiftlim g Dconst
    Cg hCg
  obtain ⟨hf'easy, hf'bal⟩ := hf'sub.three_limits hσ hf'1 Cf hCf'
  obtain ⟨hg'easy, hg'bal⟩ := hg'sub.three_limits hσ hg'1 Cg hCg'
  have hf'plain := hCf'
  have hg'plain := hCg'
  -- Recombine: `h_n = f'_n + t g'_n - (Cconst + t Dconst)` pointwise, and the correction term
  -- vanishes in the limit after dividing by `n` (or `2n`).
  filter_upwards [hf'plain, hg'plain, hf'easy, hg'easy, hf'bal, hg'bal]
    with ω hf'p hg'p hf'e hg'e hf'b hg'b
  refine ⟨?_, ?_, ?_⟩
  · have hsum : Tendsto
        (fun n => f' n (σ^[n] ω) / (n : ℝ) + t * (g' n (σ^[n] ω) / (n : ℝ))
          - (Cconst + t * Dconst) / n) atTop (nhds (Cf + t * Cg - 0)) :=
      (hf'e.add (hg'e.const_mul t)).sub (tendsto_const_div_atTop_nhds_zero_nat (Cconst + t *
        Dconst))
    rw [sub_zero] at hsum
    refine hsum.congr (fun n => ?_)
    simp only [hf'def, hg'def]
    ring
  · have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n => by change n ≤ 2 * n; omega) tendsto_id
    have hvanish : Tendsto (fun n : ℕ => (Cconst + t * Dconst) / (2 * (n : ℝ)))
        atTop (nhds 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (Cconst + t * Dconst)).comp h2
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n _
      simp
    have hsum : Tendsto
        (fun n => f' (2 * n) (zIter σ (-n) ω) / (2 * (n : ℝ))
          + t * (g' (2 * n) (zIter σ (-n) ω) / (2 * (n : ℝ)))
          - (Cconst + t * Dconst) / (2 * (n : ℝ))) atTop (nhds (Cf + t * Cg - 0)) :=
      (hf'b.add (hg'b.const_mul t)).sub hvanish
    rw [sub_zero] at hsum
    refine hsum.congr (fun n => ?_)
    simp only [hf'def, hg'def]
    ring
  · have hsum : Tendsto
        (fun n => f' n ω / (n : ℝ) + t * (g' n ω / (n : ℝ)) - (Cconst + t * Dconst) / n)
        atTop (nhds (Cf + t * Cg - 0)) :=
      (hf'p.add (hg'p.const_mul t)).sub (tendsto_const_div_atTop_nhds_zero_nat (Cconst + t *
        Dconst))
    rw [sub_zero] at hsum
    refine hsum.congr (fun n => ?_)
    simp only [hf'def, hg'def]
    ring

theorem tendsto_atBot_add_nhds {u w : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto u atTop atBot) (hw : Tendsto w atTop (nhds c)) :
    Tendsto (fun n => u n + w n) atTop atBot := by
  rw [tendsto_atBot]
  intro b
  filter_upwards [hw.eventually (gt_mem_nhds (show c < c + 1 by linarith)),
    tendsto_atBot.mp hu (b - (c + 1))] with n h1 h2
  have h1' : w n < c + 1 := h1
  linarith

theorem tendsto_atBot_add_atBot {u w : ℕ → ℝ}
    (hu : Tendsto u atTop atBot) (hw : Tendsto w atTop atBot) :
    Tendsto (fun n => u n + w n) atTop atBot := by
  rw [tendsto_atBot]
  intro b
  filter_upwards [tendsto_atBot.mp hu b, tendsto_atBot.mp hw 0] with n h1 h2
  linarith

theorem tendsto_nhds_add_atTop {u w : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto u atTop (nhds c)) (hw : Tendsto w atTop atTop) :
    Tendsto (fun n => u n + w n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [hu.eventually (lt_mem_nhds (show c - 1 < c by linarith)),
    tendsto_atTop.mp hw (b - (c - 1))] with n h1 h2
  have h1' : c - 1 < u n := h1
  linarith

/-- **The linear combination of two `EReal` limits.** The only excluded case is the one that is
genuinely undefined: both limits `-∞` with `t < 0`, where `C_f + tC_g` reads `-∞ + ∞`. -/
theorem tendsto_coe_add_const_mul {u v : ℕ → ℝ} {Cf Cg : EReal} {t : ℝ}
    (hCf : Cf ≠ ⊤) (hCg : Cg ≠ ⊤) (hdef : Cf = ⊥ → Cg = ⊥ → 0 ≤ t)
    (hu : Tendsto (fun n => ((u n : ℝ) : EReal)) atTop (nhds Cf))
    (hv : Tendsto (fun n => ((v n : ℝ) : EReal)) atTop (nhds Cg)) :
    Tendsto (fun n => ((u n + t * v n : ℝ) : EReal)) atTop (nhds (Cf + (t : EReal) * Cg)) := by
  rcases eq_or_ne Cf ⊥ with hfb | hfb
  · subst hfb
    have hua : Tendsto u atTop atBot := EReal.tendsto_coe_nhds_bot_iff.mp hu
    rcases eq_or_ne Cg ⊥ with hgb | hgb
    · subst hgb
      have ht : 0 ≤ t := hdef rfl rfl
      have hva : Tendsto v atTop atBot := EReal.tendsto_coe_nhds_bot_iff.mp hv
      rcases eq_or_lt_of_le ht with ht0 | htpos
      · rw [← ht0]
        simp only [EReal.coe_zero, zero_mul, add_zero]
        refine EReal.tendsto_coe_nhds_bot_iff.mpr ?_
        simpa using hua
      · have : (t : EReal) * ⊥ = ⊥ := EReal.coe_mul_bot_of_pos htpos
        rw [this, EReal.bot_add]
        refine EReal.tendsto_coe_nhds_bot_iff.mpr ?_
        exact tendsto_atBot_add_atBot hua
          ((tendsto_const_mul_atBot_of_pos htpos).mpr hva)
    · obtain ⟨s, hs⟩ : ∃ s : ℝ, Cg = (s : EReal) := ⟨Cg.toReal, (EReal.coe_toReal hCg hgb).symm⟩
      subst hs
      have hvs : Tendsto v atTop (nhds s) := EReal.tendsto_coe.mp hv
      rw [EReal.bot_add]
      refine EReal.tendsto_coe_nhds_bot_iff.mpr ?_
      exact tendsto_atBot_add_nhds hua (hvs.const_mul t)
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, Cf = (r : EReal) := ⟨Cf.toReal, (EReal.coe_toReal hCf hfb).symm⟩
    subst hr
    have hur : Tendsto u atTop (nhds r) := EReal.tendsto_coe.mp hu
    rcases eq_or_ne Cg ⊥ with hgb | hgb
    · subst hgb
      have hva : Tendsto v atTop atBot := EReal.tendsto_coe_nhds_bot_iff.mp hv
      rcases lt_trichotomy t 0 with htneg | ht0 | htpos
      · rw [EReal.coe_mul_bot_of_neg htneg, EReal.coe_add_top]
        refine EReal.tendsto_coe_nhds_top_iff.mpr ?_
        exact tendsto_nhds_add_atTop hur ((tendsto_const_mul_atTop_of_neg htneg).mpr hva)
      · subst ht0
        simp only [EReal.coe_zero, zero_mul, add_zero]
        refine EReal.tendsto_coe.mpr ?_
        simpa using hur
      · rw [EReal.coe_mul_bot_of_pos htpos, EReal.add_bot]
        refine EReal.tendsto_coe_nhds_bot_iff.mpr ?_
        exact tendsto_atBot_add_nhds ((tendsto_const_mul_atBot_of_pos htpos).mpr hva) hur
          |>.congr (fun n => by ring)
    · obtain ⟨s, hs⟩ : ∃ s : ℝ, Cg = (s : EReal) := ⟨Cg.toReal, (EReal.coe_toReal hCg hgb).symm⟩
      subst hs
      have hvs : Tendsto v atTop (nhds s) := EReal.tendsto_coe.mp hv
      have : ((r : EReal) + (t : EReal) * (s : EReal)) = ((r + t * s : ℝ) : EReal) := by
        rw [EReal.coe_add, EReal.coe_mul]
      rw [this]
      exact EReal.tendsto_coe.mpr (hur.add (hvs.const_mul t))

/-- Two real sequences that differ by a null sequence have the same `EReal` limit -- including
when that limit is `±∞`. -/
theorem tendsto_coe_of_sub_tendsto_zero {a b : ℕ → ℝ} {C : EReal}
    (ha : Tendsto (fun n => ((a n : ℝ) : EReal)) atTop (nhds C))
    (hab : Tendsto (fun n => a n - b n) atTop (nhds 0)) :
    Tendsto (fun n => ((b n : ℝ) : EReal)) atTop (nhds C) := by
  rcases eq_or_ne C ⊥ with hb | hb
  · subst hb
    refine EReal.tendsto_coe_nhds_bot_iff.mpr ?_
    have haa : Tendsto a atTop atBot := EReal.tendsto_coe_nhds_bot_iff.mp ha
    rw [tendsto_atBot]
    intro c
    filter_upwards [hab.eventually (lt_mem_nhds (show (-1:ℝ) < 0 by norm_num)),
      tendsto_atBot.mp haa (c - 1)] with n h1 h2
    have h1' : (-1:ℝ) < a n - b n := h1
    linarith
  rcases eq_or_ne C ⊤ with ht | ht
  · subst ht
    refine EReal.tendsto_coe_nhds_top_iff.mpr ?_
    have haa : Tendsto a atTop atTop := EReal.tendsto_coe_nhds_top_iff.mp ha
    rw [tendsto_atTop]
    intro c
    filter_upwards [hab.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num)),
      tendsto_atTop.mp haa (c + 1)] with n h1 h2
    have h1' : a n - b n < 1 := h1
    linarith
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, C = (r : EReal) := ⟨C.toReal, (EReal.coe_toReal ht hb).symm⟩
    subst hr
    refine EReal.tendsto_coe.mpr ?_
    have har : Tendsto a atTop (nhds r) := EReal.tendsto_coe.mp ha
    have := har.sub hab
    simpa using this

/-- **Synthesis for weakly subadditive families, with extended-real constants.** -/
theorem kingsyn [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ)
    (f g : ℕ → Ω → ℝ) (Cconst Dconst : ℝ)
    (hf : (∀ n, Measurable (f n)) ∧ ∀ m n ω, f (m + n) ω ≤ f m (σ^[n] ω) + f n ω + Cconst)
    (hg : (∀ n, Measurable (g n)) ∧ ∀ m n ω, g (m + n) ω ≤ g m (σ^[n] ω) + g n ω + Dconst)
    (hf1 : Integrable (fun ω => max (f 1 ω) 0) μ)
    (hg1 : Integrable (fun ω => max (g 1 ω) 0) μ)
    (t : ℝ) (Cf Cg : EReal) (hCf : Cf ≠ ⊤) (hCg : Cg ≠ ⊤)
    (hdef : Cf = ⊥ → Cg = ⊥ → 0 ≤ t)
    (hCfl : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n ω / n : EReal)) atTop (nhds Cf))
    (hCgl : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (g n ω / n : EReal)) atTop (nhds Cg)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ((f n (σ^[n] ω) + t * g n (σ^[n] ω)) / n : EReal)) atTop
          (nhds (Cf + (t : EReal) * Cg)) ∧
      Tendsto (fun n : ℕ =>
          ((f (2 * n) (zIter σ (-n) ω) + t * g (2 * n) (zIter σ (-n) ω)) / (2 * n) : EReal))
          atTop (nhds (Cf + (t : EReal) * Cg)) ∧
      Tendsto (fun n : ℕ => ((f n ω + t * g n ω) / n : EReal)) atTop
          (nhds (Cf + (t : EReal) * Cg)) := by
  set f' : ℕ → Ω → ℝ := fun n ω => f n ω + Cconst with hf'def
  set g' : ℕ → Ω → ℝ := fun n ω => g n ω + Dconst with hg'def
  have hf'sub : SubadditiveFamily (⇑σ) f' := by
    refine ⟨fun n => (hf.1 n).add_const Cconst, fun m n ω => ?_⟩
    have := hf.2 m n ω; simp only [hf'def]; linarith
  have hg'sub : SubadditiveFamily (⇑σ) g' := by
    refine ⟨fun n => (hg.1 n).add_const Dconst, fun m n ω => ?_⟩
    have := hg.2 m n ω; simp only [hg'def]; linarith
  have hshift : ∀ (u : Ω → ℝ) (c : ℝ), Measurable u → Integrable (fun ω => max (u ω) 0) μ →
      Integrable (fun ω => max (u ω + c) 0) μ := by
    intro u c hum hu
    refine Integrable.mono' (hu.add (integrable_const |c|))
      ((hum.add_const c).max measurable_const).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    have h1 : u ω ≤ max (u ω) 0 := le_max_left _ _
    have h2 : (0 : ℝ) ≤ max (u ω) 0 := le_max_right _ _
    have h3 : c ≤ |c| := le_abs_self c
    have h5 : (0 : ℝ) ≤ |c| := abs_nonneg c
    rcases max_choice (u ω + c) 0 with h | h <;> rw [h]
    · have hge : (0 : ℝ) ≤ u ω + c := by rw [← h]; exact le_max_right _ _
      rw [abs_of_nonneg hge]; simp only [Pi.add_apply]; linarith
    · simp only [Pi.add_apply, abs_zero]; linarith
  have hf'1 : Integrable (fun ω => max (f' 1 ω) 0) μ := hshift (f 1) Cconst (hf.1 1) hf1
  have hg'1 : Integrable (fun ω => max (g' 1 ω) 0) μ := hshift (g 1) Dconst (hg.1 1) hg1
  -- the flat shift does not move the constant
  have hshiftlim : ∀ (u : ℕ → Ω → ℝ) (c : ℝ) (C : EReal) (ω : Ω),
      Tendsto (fun n : ℕ => (u n ω / n : EReal)) atTop (nhds C) →
      Tendsto (fun n : ℕ => ((u n ω + c) / n : EReal)) atTop (nhds C) := by
    intro u c C ω hu
    refine tendsto_coe_of_sub_tendsto_zero hu ?_
    have hc : Tendsto (fun n : ℕ => -(c / n)) atTop (nhds 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat c).neg
    refine hc.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
      ring
  have hCf' : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f' n ω / n : EReal)) atTop (nhds Cf) := by
    filter_upwards [hCfl] with ω hω using hshiftlim f Cconst Cf ω hω
  have hCg' : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (g' n ω / n : EReal)) atTop (nhds Cg) := by
    filter_upwards [hCgl] with ω hω using hshiftlim g Dconst Cg ω hω
  obtain ⟨hf'e, hf'b⟩ := hf'sub.three_limits_ereal hσ hf'1 Cf hCf'
  obtain ⟨hg'e, hg'b⟩ := hg'sub.three_limits_ereal hσ hg'1 Cg hCg'
  filter_upwards [hCf', hCg', hf'e, hg'e, hf'b, hg'b] with ω h1 h2 h3 h4 h5 h6
  -- a single recombination, applied to each of the three sequences
  have combine : ∀ (a b c : ℕ → ℝ) (den : ℕ → ℝ),
      Tendsto (fun n => ((a n / den n : ℝ) : EReal)) atTop (nhds Cf) →
      Tendsto (fun n => ((b n / den n : ℝ) : EReal)) atTop (nhds Cg) →
      Tendsto (fun n => ((Cconst + t * Dconst) / den n) : ℕ → ℝ) atTop (nhds 0) →
      (∀ n, c n = (a n - Cconst) + t * (b n - Dconst)) →
      Tendsto (fun n => ((c n / den n : ℝ) : EReal)) atTop (nhds (Cf + (t : EReal) * Cg)) := by
    intro a b c den ha hb hden hc
    have hcomb := tendsto_coe_add_const_mul (t := t) hCf hCg hdef ha hb
    refine tendsto_coe_of_sub_tendsto_zero hcomb ?_
    refine hden.congr fun n => ?_
    rcases eq_or_ne (den n) 0 with h0 | h0
    · simp [h0, hc n]
    · rw [hc n]; field_simp; ring
  have hden2 : Tendsto (fun n : ℕ => (Cconst + t * Dconst) / (2 * n : ℝ)) atTop (nhds 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat ((Cconst + t * Dconst) / 2)).congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
  refine ⟨?_, ?_, ?_⟩
  · exact combine (fun n => f' n (σ^[n] ω)) (fun n => g' n (σ^[n] ω))
      (fun n => f n (σ^[n] ω) + t * g n (σ^[n] ω)) (fun n => (n : ℝ))
      h3 h4 (tendsto_const_div_atTop_nhds_zero_nat _)
      (fun n => by simp only [hf'def, hg'def]; ring)
  · exact combine (fun n => f' (2 * n) (zIter σ (-n) ω)) (fun n => g' (2 * n) (zIter σ (-n) ω))
      (fun n => f (2 * n) (zIter σ (-n) ω) + t * g (2 * n) (zIter σ (-n) ω))
      (fun n => (2 * n : ℝ)) h5 h6 hden2
      (fun n => by simp only [hf'def, hg'def]; ring)
  · exact combine (fun n => f' n ω) (fun n => g' n ω) (fun n => f n ω + t * g n ω)
      (fun n => (n : ℝ)) h1 h2 (tendsto_const_div_atTop_nhds_zero_nat _)
      (fun n => by simp only [hf'def, hg'def]; ring)

end MultiplicativeErgodic
