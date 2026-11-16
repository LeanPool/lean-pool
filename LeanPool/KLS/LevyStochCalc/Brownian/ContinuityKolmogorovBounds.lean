/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ContinuityDyadicChaining

/-!
# Almost-sure Hölder bounds from the Kolmogorov condition

The probabilistic half of the Kolmogorov-Chentsov construction. For a process `X` with
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M · edist s t ^ q`, Markov's inequality bounds each
increment tail by `M · edist s t ^ q / lam ^ p`; summing over the `2^n` level-`n` dyadic
intervals of `[0, 1]` makes the bad sets `{|increment| > ((1/2)^α)^n}` summable whenever
`α * p < q - 1`, so Borel-Cantelli gives an almost-sure bound on all small-scale dyadic
increments. Feeding those bounds to the deterministic chaining yields almost-sure local
`α`-Hölder continuity on the dyadics, and the convergence-in-measure form of the same tail
bound identifies the dyadic extension as a modification of `X`
(`kolmogorov_modification_ae_eq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Markov / Chebyshev bound from the Kolmogorov condition.**

For a process satisfying the Kolmogorov moment condition
`∫⁻ ω, edist (X s ω) (X t ω)^p ∂P ≤ M · edist s t ^ q` and any threshold
`0 < lam < ⊤`,

  `P {ω | lam ≤ edist (X s ω) (X t ω)} ≤ M · edist s t ^ q / lam ^ p`.

This is the per-pair tail bound underlying both the convergence-in-measure
argument (`kolmogorov_modification_ae_eq`) and the per-dyadic-level Borel–
Cantelli step of the continuous-modification construction. -/
lemma kolmogorov_markov_bound
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ≥0∞} (hlam_pos : 0 < lam) (hlam_top : lam ≠ ⊤) :
    P {ω | lam ≤ edist (X s ω) (X t ω)}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / lam ^ p := by
  have hp_pos : 0 < p := hX.p_pos
  -- {lam ≤ edist} = {lam^p ≤ edist^p} since `· ^ p` is strictly monotone.
  have h_set_eq :
      {ω | lam ≤ edist (X s ω) (X t ω)}
        = {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p} := by
    ext ω; exact (ENNReal.rpow_le_rpow_iff hp_pos).symm
  have h_edist_aemeas : AEMeasurable
      (fun ω => edist (X s ω) (X t ω) ^ p) P :=
    ((hX.measurable_edist (s := s) (t := t)).pow_const p).aemeasurable
  have h_Kol : ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
      ≤ (M : ℝ≥0∞) * edist s t ^ q := hX.kolmogorovCondition s t
  have h_Markov :
      lam ^ p * P {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p}
        ≤ ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P :=
    MeasureTheory.mul_meas_ge_le_lintegral₀ h_edist_aemeas (lam ^ p)
  have h_chain :
      lam ^ p * P {ω | lam ≤ edist (X s ω) (X t ω)}
        ≤ (M : ℝ≥0∞) * edist s t ^ q := by
    rw [h_set_eq]; exact le_trans h_Markov h_Kol
  have hlamp_pos : 0 < lam ^ p := by
    apply ENNReal.rpow_pos_of_nonneg hlam_pos
    exact hp_pos.le
  have hlamp_ne_top : lam ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp_pos.le hlam_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hlamp_pos.ne') (Or.inl hlamp_ne_top),
      mul_comm]
  exact h_chain

/-- Real-threshold form of the tail bound: for `lam > 0`,
`P {ω | lam < |X s ω − X t ω|} ≤ M · edist s t ^ q / (ofReal lam) ^ p`. -/
lemma kolmogorov_real_tail_bound
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    P {ω | lam < |X s ω - X t ω|}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / ENNReal.ofReal lam ^ p := by
  refine le_trans (measure_mono ?_)
    (kolmogorov_markov_bound P X hX s t
      (ENNReal.ofReal_pos.mpr hlam) ENNReal.ofReal_ne_top)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (le_of_lt hω)

/-- **Lemma A: per-level bad-set bound.** The union over level-`n` dyadic
intervals in `[0,1]` of the events `{ |increment| > ((1/2)^α)^n }` has measure
`≤ ofReal((M:ℝ)·ρⁿ)` with `ρ = (1/2)^{q−αp−1}`. (Borel–Cantelli summability
follows when `αp < q−1`, i.e. `ρ < 1`.) -/
lemma kc_level_bad_measure
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (n : ℕ) :
    P (⋃ k ∈ Finset.range (2 ^ n),
        {ω | ((1 / 2 : ℝ) ^ α) ^ n
            < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|})
      ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n) := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hrn0 : 0 < r ^ n := pow_pos hr0 n
  have hhalf_n : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hrnp0 : (0 : ℝ) < (r ^ n) ^ p := Real.rpow_pos_of_pos hrn0 p
  -- Per-interval Markov term, converted to `ofReal`.
  have hterm : ∀ k ∈ Finset.range (2 ^ n),
      P {ω | r ^ n < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|}
        ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (r ^ n) ^ p) := by
    intro k _
    have hb := kolmogorov_real_tail_bound P X hX
      (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n) hrn0
    refine le_trans hb (le_of_eq ?_)
    have hedist : edist (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n)
        = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [edist_dist, Real.dist_eq]
      congr 1
      rw [show ((k : ℝ) + 1) / 2 ^ n - (k : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ n from by
        rw [div_pow, one_pow]; ring]
      exact abs_of_pos hhalf_n
    rw [hedist, ENNReal.ofReal_rpow_of_pos hhalf_n,
        ENNReal.ofReal_rpow_of_pos hrn0, ← ENNReal.ofReal_coe_nnreal (p := M),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos hrnp0]
  refine le_trans (measure_biUnion_finset_le (Finset.range (2 ^ n)) _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) from by
        rw [← ENNReal.ofReal_natCast]; norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq ?_
  congr 1
  rw [hr_def, show (2 : ℝ) ^ n
        * ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p)
      = (M : ℝ) * ((2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q
          / (((1 / 2 : ℝ) ^ α) ^ n) ^ p) from by ring,
      kc_exponent_identity]

/-- **Limit existence from local Hölder.** If `f` is α-Hölder on `A ∩ (t−ρ, t+ρ)`
for some `ρ > 0`, `K ≥ 0`, then `f` has a limit along `𝓝[A] t` (`A` dense). The
limit-along-dyadics is what `extendFrom` needs to build the continuous path. -/
lemma exists_tendsto_of_local_holder {A : Set ℝ} (hA : Dense A) {f : ℝ → ℝ}
    {α : ℝ} (hα : 0 < α) (t : ℝ)
    (hloc : ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ A, ∀ s' ∈ A,
      s ∈ Set.Ioo (t - ρ) (t + ρ) → s' ∈ Set.Ioo (t - ρ) (t + ρ) →
        |f s - f s'| ≤ K * |s - s'| ^ α) :
    ∃ y, Filter.Tendsto f (𝓝[A] t) (nhds y) := by
  obtain ⟨K, ρ, hρ, hK, hHol⟩ := hloc
  have hFne : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hA t)
  have hcauchy : Cauchy (Filter.map f (𝓝[A] t)) := by
    rw [Metric.cauchy_iff]
    refine ⟨hFne.map _, fun ε hε => ?_⟩
    -- choose `ρ' ≤ ρ` with `K·(2ρ')^α < ε`
    obtain ⟨ρ', hρ'0, hρ'ρ, hρ'b⟩ :
        ∃ ρ', 0 < ρ' ∧ ρ' ≤ ρ ∧ K * (2 * ρ') ^ α < ε := by
      have hδ : 0 < (ε / (K + 1)) ^ (1 / α) :=
        Real.rpow_pos_of_pos (by positivity) _
      refine ⟨min ρ ((ε / (K + 1)) ^ (1 / α) / 3), lt_min hρ (by positivity),
        min_le_left _ _, ?_⟩
      have h2 : 2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3) < (ε / (K + 1)) ^ (1 / α) := by
        have := min_le_right ρ ((ε / (K + 1)) ^ (1 / α) / 3)
        linarith
      have hpow : (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α < ε / (K + 1) := by
        have h1 := Real.rpow_lt_rpow (by positivity) h2 hα
        rwa [show ((ε / (K + 1)) ^ (1 / α)) ^ α = ε / (K + 1) from by
          rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / (K + 1)), one_div,
              inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]] at h1
      calc K * (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α
          ≤ (K + 1) * (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ < (K + 1) * (ε / (K + 1)) := by
            apply mul_lt_mul_of_pos_left hpow (by positivity)
        _ = ε := by field_simp
    refine ⟨f '' (A ∩ Set.Ioo (t - ρ') (t + ρ')), ?_, ?_⟩
    · rw [Filter.mem_map]
      refine Filter.mem_of_superset ?_ (Set.subset_preimage_image f _)
      exact inter_mem_nhdsWithin A
        (Ioo_mem_nhds (by linarith) (by linarith))
    · rintro x ⟨s, ⟨hsA, hsI⟩, rfl⟩ y ⟨s', ⟨hs'A, hs'I⟩, rfl⟩
      have hIs : s ∈ Set.Ioo (t - ρ) (t + ρ) :=
        ⟨by have := hsI.1; linarith, by have := hsI.2; linarith⟩
      have hIs' : s' ∈ Set.Ioo (t - ρ) (t + ρ) :=
        ⟨by have := hs'I.1; linarith, by have := hs'I.2; linarith⟩
      have hb := hHol s hsA s' hs'A hIs hIs'
      have hss' : |s - s'| ≤ 2 * ρ' := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have h1 := hsI.1; have h2 := hs'I.2; linarith
        · have h1 := hsI.2; have h2 := hs'I.1; linarith
      rw [Real.dist_eq]
      calc |f s - f s'| ≤ K * |s - s'| ^ α := hb
        _ ≤ K * (2 * ρ') ^ α := by
            apply mul_le_mul_of_nonneg_left _ hK
            exact Real.rpow_le_rpow (abs_nonneg _) hss' hα.le
        _ < ε := hρ'b
  obtain ⟨y, hy⟩ := CompleteSpace.complete hcauchy
  exact ⟨y, hy⟩

/-- **Translation invariance of the Kolmogorov condition.** If `X` satisfies
the Kolmogorov condition, so does the time-shifted process `s ↦ X (s + a)`
(the bound depends only on `edist s t = edist (s+a) (t+a)`). Used to transport
the `[0,1]` construction to every interval `[j, j+1]`. -/
lemma isKolmogorovProcess_comp_add_right
    {P : Measure Ω} (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (a : ℝ) :
    ProbabilityTheory.IsKolmogorovProcess (fun s ω => X (s + a) ω) P p q M where
  measurablePair s t := hX.measurablePair (s + a) (t + a)
  kolmogorovCondition s t := by
    have he : edist s t = edist (s + a) (t + a) := by
      rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
          show (s + a) - (t + a) = s - t from by ring]
    rw [he]
    exact hX.kolmogorovCondition (s + a) (t + a)
  p_pos := hX.p_pos
  q_pos := hX.q_pos

/-- **Lemma B: a.s. dyadic increment bound (Borel–Cantelli).** When
`α·p < q − 1`, almost every path has, for some level `N`, all consecutive
level-`n` dyadic increments in `[0,1]` bounded by `((1/2)^α)^n` for every
`n ≥ N`. This supplies the hypothesis of `dyadic_holder_chaining`. -/
lemma kc_ae_increment_bound
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|
        ≤ ((1 / 2 : ℝ) ^ α) ^ n := by
  set ρ : ℝ := (1 / 2 : ℝ) ^ (q - α * p - 1) with hρ_def
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  set A : ℕ → Set Ω := fun n => ⋃ k ∈ Finset.range (2 ^ n),
      {ω | ((1 / 2 : ℝ) ^ α) ^ n
          < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|} with hA_def
  have hAle : ∀ n, P (A n) ≤ ENNReal.ofReal ((M : ℝ) * ρ ^ n) := fun n =>
    kc_level_bad_measure P X hX n
  have hsummable_real : Summable (fun n => (M : ℝ) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have htsum_ne : (∑' n, P (A n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hAle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable_real]
    exact ENNReal.ofReal_ne_top
  have hlimsup : P (Filter.limsup A Filter.atTop) = 0 :=
    measure_limsup_atTop_eq_zero htsum_ne
  have hae : ∀ᵐ ω ∂P, ω ∉ Filter.limsup A Filter.atTop := by
    rw [ae_iff]; simp only [not_not, Set.ofPred_mem_eq]; exact hlimsup
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently,
      Filter.eventually_atTop] at hω
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn k hk0 hk1 => ?_⟩
  have hωn : ω ∉ A n := hN n hn
  rw [hA_def] at hωn
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hωn
  have hk'mem : k.toNat ∈ Finset.range (2 ^ n) := by
    rw [Finset.mem_range]
    have hcast2 : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
    omega
  have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  have hb := hωn k.toNat hk'mem
  rw [hcast] at hb
  exact hb

/-- **Per-interval a.s. Hölder.** For `αp < q − 1`, almost every path is
α-Hölder (at small scales) on the dyadics of every unit interval `[j, j+1]`.
Obtained by transporting `dyadic_holder_chaining` (on `[0,1]`) to `[j,j+1]` via
the time-shifted process `X(·+j)` (translation-invariant Kolmogorov condition),
intersected over the countable family `j : ℤ`. -/
lemma kc_ae_interval_holder
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ j : ℤ, ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
      ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
        (j : ℝ) ≤ s → s ≤ (j : ℝ) + 1 → (j : ℝ) ≤ t → t ≤ (j : ℝ) + 1 →
        |s - t| ≤ (1 / 2 : ℝ) ^ N → |X s ω - X t ω| ≤ K * |s - t| ^ α := by
  rw [MeasureTheory.ae_all_iff]
  intro j
  have hXj : ProbabilityTheory.IsKolmogorovProcess (fun s ω => X (s + (j : ℝ)) ω) P p q M :=
    isKolmogorovProcess_comp_add_right X hX j
  filter_upwards [kc_ae_increment_bound P (fun s ω => X (s + (j : ℝ)) ω) hXj hαpq] with ω hω
  obtain ⟨N, hN⟩ := hω
  obtain ⟨K, hK0, hKbound⟩ :=
    dyadic_holder_chaining (f := fun u => X (u + (j : ℝ)) ω) (α := α) (C := 1) (N := N)
      hα0 (by norm_num) (fun n hn k hk0 hk1 => by
        rw [one_mul]
        simp only [Int.cast_add, Int.cast_one]
        exact hN n hn k hk0 hk1)
  refine ⟨K, N, hK0, fun s hs t ht hjs hsj1 hjt htj1 hst => ?_⟩
  have hu : s - (j : ℝ) ∈ dyadicRationals := sub_intCast_mem_dyadicRationals hs j
  have hv : t - (j : ℝ) ∈ dyadicRationals := sub_intCast_mem_dyadicRationals ht j
  have hKb := hKbound (s - (j : ℝ)) hu (t - (j : ℝ)) hv (by linarith) (by linarith)
    (by linarith) (by linarith)
    (by rw [show s - (j : ℝ) - (t - (j : ℝ)) = s - t from by ring]; exact hst)
  rw [show s - (j : ℝ) + (j : ℝ) = s from by ring,
      show t - (j : ℝ) + (j : ℝ) = t from by ring,
      show s - (j : ℝ) - (t - (j : ℝ)) = s - t from by ring] at hKb
  exact hKb

/-- **Neighbourhood Hölder.** For a.e. path, every point `t` has an open
neighbourhood on whose dyadics `X(·)ω` is α-Hölder. At a point near an integer
`c`, pairs straddling `c` are handled by chaining through `c` (`X c` is defined
since `c` is dyadic), using the two adjacent unit-interval bounds. This is the
hypothesis of `exists_tendsto_of_local_holder`. -/
lemma kc_ae_nbhd_holder
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
      ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α := by
  filter_upwards [kc_ae_interval_holder P X hX hα0 hαpq] with ω hIH
  intro t
  set c : ℤ := ⌊t + 1 / 2⌋ with hc
  obtain ⟨KL, NL, hKL0, hHL⟩ := hIH (c - 1)
  obtain ⟨K₀, N₀, hK₀0, hH₀⟩ := hIH c
  have hcdy : (c : ℝ) ∈ dyadicRationals := intCast_mem_dyadicRationals c
  -- `t` lies within `1/2` of `c`.
  have htlo : (c : ℝ) - 1 / 2 ≤ t := by
    have := Int.floor_le (t + 1 / 2); linarith
  have hthi : t < (c : ℝ) + 1 / 2 := by
    have := Int.lt_floor_add_one (t + 1 / 2); linarith
  refine ⟨2 * (KL + K₀),
    min (min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2) (1 / 2), ?_, by positivity, ?_⟩
  · have : (0 : ℝ) < min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) := by positivity
    exact lt_min (by positivity) (by norm_num)
  · set ρ := min (min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2) (1 / 2) with hρ
    have hρ12 : ρ ≤ 1 / 2 := min_le_right _ _
    have hrhoNL : 2 * ρ ≤ (1 / 2 : ℝ) ^ NL := by
      have h1 : ρ ≤ min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2 := min_le_left _ _
      have h2 : min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀)
          ≤ (1 / 2 : ℝ) ^ NL := min_le_left _ _
      linarith
    have hρN₀ : 2 * ρ ≤ (1 / 2 : ℝ) ^ N₀ := by
      have h1 : ρ ≤ min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2 := min_le_left _ _
      have h2 : min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀)
          ≤ (1 / 2 : ℝ) ^ N₀ := min_le_right _ _
      linarith
    -- ordered-pair core
    have key : ∀ a b, a ∈ dyadicRationals → b ∈ dyadicRationals →
        (c : ℝ) - 1 < a → a ≤ b → b < (c : ℝ) + 1 → |a - b| ≤ 2 * ρ →
        |X a ω - X b ω| ≤ 2 * (KL + K₀) * |a - b| ^ α := by
      intro a b ha hb halo hab bhi habs
      have habsL : |a - b| ≤ (1 / 2 : ℝ) ^ NL := le_trans habs hrhoNL
      have habs₀ : |a - b| ≤ (1 / 2 : ℝ) ^ N₀ := le_trans habs hρN₀
      rcases le_or_gt b (c : ℝ) with hbc | hbc
      · -- both in [c-1, c]
        have h := hHL a ha b hb (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) habsL
        have : KL ≤ 2 * (KL + K₀) := by nlinarith
        calc |X a ω - X b ω| ≤ KL * |a - b| ^ α := h
          _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
              apply mul_le_mul_of_nonneg_right this (by positivity)
      · rcases le_or_gt (c : ℝ) a with hca | hca
        · -- both in [c, c+1]
          have h := hH₀ a ha b hb (by linarith) (by linarith)
            (by linarith) (by linarith) habs₀
          have : K₀ ≤ 2 * (KL + K₀) := by nlinarith
          calc |X a ω - X b ω| ≤ K₀ * |a - b| ^ α := h
            _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
                apply mul_le_mul_of_nonneg_right this (by positivity)
        · -- straddle: a < c < b, chain through c
          have hac_le : |a - (c : ℝ)| ≤ |a - b| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have hcb_le : |(c : ℝ) - b| ≤ |a - b| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have h1 := hHL a ha (c : ℝ) hcdy (by push_cast; linarith) (by push_cast; linarith)
            (by push_cast; linarith) (by push_cast; linarith) (le_trans hac_le habsL)
          have h2 := hH₀ (c : ℝ) hcdy b hb (by linarith) (by linarith)
            (by linarith) (by linarith) (le_trans hcb_le habs₀)
          have hacα : |a - (c : ℝ)| ^ α ≤ |a - b| ^ α :=
            Real.rpow_le_rpow (abs_nonneg _) hac_le hα0.le
          have hcbα : |(c : ℝ) - b| ^ α ≤ |a - b| ^ α :=
            Real.rpow_le_rpow (abs_nonneg _) hcb_le hα0.le
          calc |X a ω - X b ω|
              ≤ |X a ω - X (c : ℝ) ω| + |X (c : ℝ) ω - X b ω| := abs_sub_le _ _ _
            _ ≤ KL * |a - (c : ℝ)| ^ α + K₀ * |(c : ℝ) - b| ^ α := by gcongr
            _ ≤ KL * |a - b| ^ α + K₀ * |a - b| ^ α := by gcongr
            _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
                nlinarith [Real.rpow_nonneg (abs_nonneg (a - b)) α]
    intro s hs s' hs' hsb hs'b
    have hsbnd : (c : ℝ) - 1 < s ∧ s < (c : ℝ) + 1 :=
      ⟨by have := hsb.1; linarith, by have := hsb.2; linarith⟩
    have hs'bnd : (c : ℝ) - 1 < s' ∧ s' < (c : ℝ) + 1 :=
      ⟨by have := hs'b.1; linarith, by have := hs'b.2; linarith⟩
    have hdist : |s - s'| ≤ 2 * ρ := by
      rw [abs_le]; constructor
      · have := hsb.1; have := hs'b.2; linarith
      · have := hsb.2; have := hs'b.1; linarith
    rcases le_total s s' with hss | hss
    · exact key s s' hs hs' hsbnd.1 hss hs'bnd.2 hdist
    · rw [abs_sub_comm, abs_sub_comm s s']
      exact key s' s hs' hs hs'bnd.1 hss hsbnd.2 (by rw [abs_sub_comm] at hdist; exact hdist)

/-- **Step 3: extended process equals X a.s. at each t.**

By the Kolmogorov condition (Markov inequality), `X_{t_n} → X_t` in probability
as `t_n → t`. Combined with the a.s.-pointwise dyadic limit (Y is continuous
and equals X on dyadics), the extended process equals X almost surely at
each `t`.

Sub-steps:
1. **Continuity in probability of X**: `X t_n → X t` in probability via Markov
   + Kolmogorov condition.
2. **Y_{t_n} → Y_t** almost surely as t_n → t along any sequence (since Y is
   continuous a.s.).
3. **X_{t_n} = Y_{t_n}** for dyadic t_n (hypothesis).
4. Combine: at each fixed t, X_t = Y_t a.s. (limit of equal-a.s. sequences,
   one converging in probability the other a.s., are equal a.s.). -/
lemma kolmogorov_modification_ae_eq
    (P : Measure Ω)
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (Y : ℝ → Ω → ℝ)
    (h_continuous : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (h_dyadic_eq : ∀ s ∈ dyadicRationals, ∀ᵐ ω ∂P, Y s ω = X s ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω := by
  intro t
  -- Step 1: pick dyadic sequence u_n strictly increasing to t.
  obtain ⟨u, _hu_mono, hu_dyadic, hu_tendsto⟩ := exists_seq_dyadic_tendsto t
  -- Step 2: each X(s) is measurable (from Mathlib's IsKolmogorovProcess.measurable
  -- which needs MeasurableSpace + BorelSpace + SecondCountableTopology on E = ℝ,
  -- all of which ℝ has).
  have h_X_meas : ∀ s : ℝ, Measurable (X s) := fun s => hX.measurable s
  -- Step 3: Chebyshev / Markov on the Kolmogorov moment bound gives
  -- convergence-in-measure of X(u n) → X(t).
  have hp_pos : 0 < p := hX.p_pos
  have hq_pos : 0 < q := hX.q_pos
  -- Direct Markov: P {ω | δ^p ≤ edist^p} ≤ (∫⁻ edist^p) / δ^p
  --   ≤ M·edist(u n,t)^q/δ^p.
  -- For real-valued X, edist (X s ω) (X t ω) = ‖X s ω - X t ω‖ₑ (PseudoEMetric on ℝ
  -- via |·|), so this is convergence of (X (u n)) → X t in measure.
  have h_TIM : MeasureTheory.TendstoInMeasure P (fun n => X (u n)) Filter.atTop (X t) := by
    intro δ hδ
    -- Handle δ = ⊤ separately: edist : ENNReal-valued from real-valued X is
    -- always < ⊤, so {ω | ⊤ ≤ edist} is empty, P = 0, tendsto trivially.
    by_cases hδ_top : δ = ⊤
    · subst hδ_top
      simp_rw [top_le_iff]
      have h_set_empty : ∀ n,
          {ω | edist (X (u n) ω) (X t ω) = ⊤} = ∅ := by
        intro n; ext ω
        simp
      simp_rw [h_set_empty]
      simp
    -- Now δ ≠ ⊤. Step D: edist (u n) t → 0 from u n → t.
    have h_edist_tendsto : Filter.Tendsto (fun n => edist (u n) t)
        Filter.atTop (nhds 0) :=
      (tendsto_iff_edist_tendsto_0.mp hu_tendsto)
    -- Step E: edist (u n) t ^ q → 0 (continuity of x^q at 0, with 0^q = 0 for q > 0).
    have h_pow_tendsto : Filter.Tendsto (fun n => edist (u n) t ^ q)
        Filter.atTop (nhds 0) := by
      have := h_edist_tendsto.ennrpow_const q
      rwa [ENNReal.zero_rpow_of_pos hq_pos] at this
    -- Step F: M · edist^q → 0 (M ≠ ⊤ since M : ℝ≥0).
    have hM_ne_top : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h_M_pow_tendsto : Filter.Tendsto
        (fun n => (M : ℝ≥0∞) * edist (u n) t ^ q)
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul h_pow_tendsto (Or.inr hM_ne_top)
      simpa using this
    -- Step G: divide the per-pair Markov bound by δ^p (δ^p ≠ 0 for the
    -- constant-division tendsto below).
    have hδp_pos : 0 < δ ^ p := by
      apply ENNReal.rpow_pos_of_nonneg hδ
      exact hp_pos.le
    -- The bound on P {δ ≤ edist}: the per-pair Markov/Chebyshev tail bound.
    have h_set_bound : ∀ n, P {ω | δ ≤ edist (X (u n) ω) (X t ω)}
        ≤ ((M : ℝ≥0∞) * edist (u n) t ^ q) / δ ^ p :=
      fun n => kolmogorov_markov_bound P X hX (u n) t hδ hδ_top
    -- Step G applied: (M · edist^q) / δ^p → 0 from h_M_pow_tendsto (constant division).
    have h_bound_tendsto : Filter.Tendsto
        (fun n => ((M : ℝ≥0∞) * edist (u n) t ^ q) / δ ^ p)
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.div_const h_M_pow_tendsto (Or.inr hδp_pos.ne')
      simpa using this
    -- Step H: squeeze 0 ≤ P {δ ≤ edist} ≤ bound → 0.
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_bound_tendsto (fun _ => bot_le) h_set_bound
  -- Step 4: extract a.s.-converging subsequence.
  obtain ⟨ns, _hns_mono, hns_ae⟩ := h_TIM.exists_seq_tendsto_ae
  -- Step 5: combine on the full-measure intersection.
  -- A := {ω : Continuous Y(·) ω}              (from h_continuous, P-full)
  -- B_k := {ω : Y(u (ns k)) ω = X(u (ns k)) ω}  (from h_dyadic_eq, P-full)
  -- C := {ω : X(u (ns k)) ω → X(t) ω}           (from hns_ae, P-full)
  -- D := A ∩ ⋂_k B_k ∩ C  (countable intersection of full sets = full)
  -- On D: Y(u (ns k)) ω = X(u (ns k)) ω → X(t) ω.
  --       Also Y(u (ns k)) ω → Y(t) ω (by continuity of Y at t along u (ns k) → t).
  --       By uniqueness of limits in ℝ: Y(t) ω = X(t) ω.
  filter_upwards [h_continuous, hns_ae,
    MeasureTheory.ae_all_iff.mpr (fun k => h_dyadic_eq (u (ns k)) (hu_dyadic (ns k)).2)]
    with ω h_Y_cont h_X_tendsto h_eq_seq
  -- u (ns k) → t (subsequence of u → t via StrictMono ns → atTop atTop)
  have h_subseq_tendsto : Filter.Tendsto (fun k => u (ns k)) Filter.atTop (nhds t) :=
    hu_tendsto.comp _hns_mono.tendsto_atTop
  -- Y is continuous at t (from a.s. continuity)
  have h_Y_tendsto : Filter.Tendsto (fun k => Y (u (ns k)) ω) Filter.atTop (nhds (Y t ω)) :=
    (h_Y_cont.tendsto t).comp h_subseq_tendsto
  -- So X(u (ns k)) ω → Y(t) ω (substitute Y(u (ns k)) ω = X(u (ns k)) ω),
  -- and also → X(t) ω. By uniqueness of limits in ℝ, Y(t) ω = X(t) ω.
  have h_X_to_Y : Filter.Tendsto (fun k => X (u (ns k)) ω) Filter.atTop (nhds (Y t ω)) := by
    have h_eq : (fun k => X (u (ns k)) ω) = fun k => Y (u (ns k)) ω := by
      funext k
      exact (h_eq_seq k).symm
    rw [h_eq]
    exact h_Y_tendsto
  exact tendsto_nhds_unique h_X_to_Y h_X_tendsto

end LevyStochCalc.Brownian.Continuity
