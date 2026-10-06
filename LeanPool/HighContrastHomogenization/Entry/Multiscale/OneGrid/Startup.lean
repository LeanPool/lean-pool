/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.StartupMoments

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.Startup

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 5 — startup, the absorbed drift and the drift-carrying span

Group H of the printed proof (`p.fixed.geometry.one.grid.propagation`), second part: **conjuncts 4
and
8**, `e.fixed.geometry.profile.startup` and `e.fixed.geometry.fixed.span.propagation`, with
the absorbed drift advance between them.

Part of the proof of `HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of the group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
statement in `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.

-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Conjunct 4**, `e.fixed.geometry.profile.startup` (`p.fixed.geometry.one.grid.propagation`
display
`e.fixed.geometry.profile.startup`). -/
theorem profile_startup (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ L : ℤ, 1 ≤ L →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (metric : Mat d), metric.PosDef →
                  ∀ n : ℤ, (jStar : ℤ) ≤ n →
                    history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n ≤ 1 →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (n + L) ≤
                        C * (L : ℝ) *
                          (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                            Real.exp ((bigQ d γ : ℝ) *
                              detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                                n (n + L)) - 1) := by
  obtain ⟨Csrc, hCsrc, C3, hC3, hfl⟩ := startup_fluctuation_sum_le d hd γ hγ
  obtain ⟨C2, hC2, hmean⟩ := meanPenalty_new_terms_span_sum_le d hd γ hγ
  refine ⟨Csrc, hCsrc, 1 + C2 + C3, by positivity, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag L hL jStar hjStar hsrc metric hmetric n hn hH1
  let := hP
  have hnL : n ≤ n + L := by omega
  have hfluc : 0 ≤ fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar n := by
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro _hj
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact (bigQ_even d γ).pow_nonneg _
  have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
  have hH0 : 0 ≤ history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n := by
    unfold history
    linarith only [hfluc, hmean0]
  have hx0 : 0 ≤ (bigQ d γ : ℝ) * detIncrement P (Geometry.explicitRoundedGrid jStar metric) n
    (n + L) :=
    mul_nonneg (Nat.cast_nonneg _)
      (Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
        n (n + L) hn hnL)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := by linarith only [hL1]
  have hR0 : 0 ≤ history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
      Real.exp ((bigQ d γ : ℝ) * detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n
        + L)) -
        1 := by
    have hone := Real.one_le_exp hx0
    linarith only [hH0, hone]
  have hflb := hfl P E Ψ K S hP hstat hunit hdag L hL jStar hjStar hsrc metric hmetric n hn hH1
  have hmeanb := hmean P E Ψ K S hP hstat hunit hdag L hL jStar hjStar metric hmetric n hn
  have hpen0 := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n (n + L) hn hnL).2.2.2.2.2
  have hpenle := meanPenalty_normalizedMean_le_exp_sub_one d hd γ hγ P E Ψ K S hP hstat hunit
    hdag jStar hjStar metric hmetric n (n + L) hn hnL
  have hcast : ((n + L : ℤ) : ℝ) - (n : ℝ) = (L : ℝ) := by push_cast; ring
  have hweight : (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (n : ℝ))) ≤ 1 := by
    rw [hcast]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    nlinarith only [hγ.2, hL1]
  have hAB : (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (n : ℝ))) *
      (1 + meanPenalty (bigQ d γ)
        (relMean P (Geometry.explicitRoundedGrid jStar metric) n (n + L))) ≤
      Real.exp ((bigQ d γ : ℝ) *
        detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) := by
    have hb0 : 0 ≤ 1 + meanPenalty (bigQ d γ)
        (relMean P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) := by linarith only
          [hpen0]
    have hstep := mul_le_of_le_one_left hb0 hweight
    have hble : 1 + meanPenalty (bigQ d γ)
        (relMean P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) ≤
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) := by linarith
            only [hpenle]
    linarith only [hstep, hble]
  have hT : (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (n : ℝ))) *
      (1 + meanPenalty (bigQ d γ)
        (relMean P (Geometry.explicitRoundedGrid jStar metric) n (n + L))) *
      history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n ≤
      history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1 := by
    have hstep2 := mul_le_mul_of_nonneg_right hAB hH0
    have hstep3 := exp_mul_le_add_exp_sub_one
      ((bigQ d γ : ℝ) * detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L))
      (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n) hx0 hH0 hH1
    linarith only [hstep2, hstep3]
  have hexpsub : Real.exp ((bigQ d γ : ℝ) *
      detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1 ≤
      history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1 := by
    linarith only [hH0]
  have hmeanb2 := hmeanb.trans (mul_le_mul_of_nonneg_left hexpsub (mul_nonneg hC2.le hLnonneg))
  have hTL : history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
      Real.exp ((bigQ d γ : ℝ) *
        detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1 ≤
      (L : ℝ) * (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1) := by
    nlinarith only [hR0, hL1]
  have hring : (1 + C2 + C3) * (L : ℝ) *
      (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1) =
      (L : ℝ) * (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
          Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1) +
        C2 * (L : ℝ) * (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
          Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1) +
        C3 * (L : ℝ) * (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
          Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1) := by ring
  unfold profile meanHistory
  linarith only [hT, hmeanb2, hflb, hTL, hring]

/-- The absorbed drift advance (`p.fixed.geometry.one.grid.propagation`): when `D_{q,j_*}(m) ≤ 1`,
applying
`e^x a ≤ a + e^x - 1` to `e.fixed.geometry.drift.advance` gives coefficient one on the drift
and the printed `2` on the remainder. -/
theorem determinantDrift_advance_absorbed (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ L : ℤ, 1 ≤ L →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ∀ (metric : Mat d), metric.PosDef →
            ∀ m : ℤ, (jStar : ℤ) ≤ m →
              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤ 1 →
                determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + L) ≤
                  determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                    2 * (Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                      m (m + L)) - 1) := by
  intro P E Ψ K S hprob hstat hunit hdagger L hL jStar hjStar metric hmetric m hm hD_bound
  let : IsProbabilityMeasure P := hprob
  let q := Geometry.explicitRoundedGrid jStar metric
  let D := determinantDrift P γ q jStar m
  let Δ := detIncrement P q m (m + L)
  change determinantDrift P γ q jStar (m + L) ≤ D + 2 * (Real.exp Δ - 1)
  have hmk : m ≤ m + L := by omega
  have hD_nonneg : 0 ≤ D :=
    determinantDrift_nonneg d hd γ P E Ψ K S hprob hstat hunit hdagger jStar hjStar
      metric hmetric m
  have hΔ_nonneg : 0 ≤ Δ := by
    dsimp [Δ, q]
    exact HCPolySupport.HighContrast.Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdagger
      jStar hjStar metric hmetric m (m + L) hm hmk
  have hcoeff_exp_nonpos : -((1 - γ) / 8) * (L : ℝ) ≤ 0 := by
    have hLnonnegZ : (0 : ℤ) ≤ L := by omega
    have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLnonnegZ
    have hγnonneg : 0 ≤ (1 - γ) / 8 := by linarith only [hγ.2.le]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγnonneg) hLnonneg
  have hcoeff :
      (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hcoeff_exp_nonpos
  have hterm :
      (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) * Real.exp Δ * D ≤
        Real.exp Δ * D := by
    calc
      (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) * Real.exp Δ * D =
          (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) * (Real.exp Δ * D) := by ring
      _ ≤ 1 * (Real.exp Δ * D) := by
        exact mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (Real.exp_nonneg Δ) hD_nonneg)
      _ = Real.exp Δ * D := by ring
  have habsorb : Real.exp Δ * D ≤ D + Real.exp Δ - 1 :=
    exp_mul_le_add_exp_sub_one Δ D hΔ_nonneg hD_nonneg hD_bound
  have hadvance :
      determinantDrift P γ q jStar (m + L) ≤
        (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) * Real.exp Δ * D +
          Real.exp Δ - 1 := by
    dsimp [D, Δ]
    exact
      determinantDrift_advance_of_posDef_antitone P γ hγ.2.le q jStar m L hm hL
        (fun j _ => by
          dsimp [q]
          exact HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat
            hdagger jStar hjStar metric hmetric j)
        (fun j hj => by
          dsimp [q]
          exact HCPolySupport.HighContrast.Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat
            hdagger jStar hjStar metric hmetric (j - 1) j (by
              rw [Set.mem_Icc] at hj
              omega) (by omega))
  calc
    determinantDrift P γ q jStar (m + L) ≤
        (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) * Real.exp Δ * D +
          Real.exp Δ - 1 := hadvance
    _ ≤ D + 2 * (Real.exp Δ - 1) := by linarith only [hterm, habsorb]

/-- **Conjunct 8**, `e.fixed.geometry.fixed.span.propagation`: add the absorbed drift advance to
the fixed-span estimate when `m ≥ n+h`, and to
the startup estimate when `m = n` using `𝒫_q(n;n) = ℋ_q(n)`; then
`e^{Δ^q_{m,m+L}} - 1 ≤ e^{QΔ^q_{m,m+L}} - 1`. -/
theorem fixed_span_propagation (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
            ∀ L : ℤ, 1 ≤ L →
              ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                  ∀ (metric : Mat d), metric.PosDef →
                    ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
                      (m = n ∨ n + (h : ℤ) ≤ m) →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                              jStar m ≤ 1 →
                          profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                                (m + L) ≤
                            C * (L : ℝ) *
                              (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                                determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                  jStar m +
                                Real.exp ((bigQ d γ : ℝ) *
                                  detIncrement P (Geometry.explicitRoundedGrid jStar metric) m
                                    (m + L)) - 1) := by
  obtain ⟨Csrc1, hC1s, C1, hC1, hfix⟩ := profile_fixed_span d hd γ hγ
  obtain ⟨Csrc2, hC2s, C2, hC2, hstart⟩ := profile_startup d hd γ hγ
  refine ⟨max Csrc1 Csrc2, lt_max_of_lt_left hC1s, C1 + C2 + 3, by positivity, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc metric hmetric n m hn hnm
    hcase hsum
  let := hP
  have hlogb : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 3)
      (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) ≤ 2 * K)
  have hsrc1 : ⌈Csrc1 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    le_trans (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogb)) hsrc
  have hsrc2 : ⌈Csrc2 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    le_trans (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right _ _) hlogb)) hsrc
  set q := Geometry.explicitRoundedGrid jStar metric with hqdef
  have hQ1 : (1 : ℝ) ≤ (bigQ d γ : ℝ) := by
    have hQ2 := bigQ_two_le d γ hγ
    have : (1 : ℕ) ≤ bigQ d γ := by omega
    exact_mod_cast this
  have hLr1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  -- nonnegativity of the profile p := profile P γ q jStar n m
  have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
  have hfluc : 0 ≤ fluctuationHistory P γ q jStar n := by
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro _hj
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact (bigQ_even d γ).pow_nonneg _
  have hhistory : 0 ≤ history P γ q jStar n := add_nonneg hfluc hmean0
  have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n m hn hnm).2.2.2.2.2
  have hw (x : ℝ) : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * x) := Real.rpow_nonneg (by norm_num) _
  have hp0 : 0 ≤ profile P γ q jStar n m := by
    unfold profile
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (mul_nonneg (hw _) (by linarith only [hpen])) hhistory)
        (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
          jStar hjStar metric hmetric n m hn hnm)
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw _) (Real.exp_nonneg _))
        (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)
  have hD0 : 0 ≤ determinantDrift P γ q jStar m :=
    determinantDrift_nonneg d hd γ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric m
  have hp1 : profile P γ q jStar n m ≤ 1 := by linarith only [hsum, hD0]
  have hD1 : determinantDrift P γ q jStar m ≤ 1 := by linarith only [hsum, hp0]
  have hΔ : 0 ≤ detIncrement P q m (m + L) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + L) (by omega) (by omega)
  have hx0 : 0 ≤ (bigQ d γ : ℝ) * detIncrement P q m (m + L) :=
    mul_nonneg (Nat.cast_nonneg _) hΔ
  have hexpx1 : 0 ≤ Real.exp ((bigQ d γ : ℝ) * detIncrement P q m (m + L)) - 1 := by
    have := Real.one_le_exp hx0
    linarith only [this]
  have hexpmono : Real.exp (detIncrement P q m (m + L)) - 1 ≤
      Real.exp ((bigQ d γ : ℝ) * detIncrement P q m (m + L)) - 1 := by
    have hle : detIncrement P q m (m + L) ≤ (bigQ d γ : ℝ) * detIncrement P q m (m + L) := by
      nlinarith only [hQ1, hΔ]
    have := Real.exp_le_exp.mpr hle
    linarith only [this]
  have hDm1 : determinantDrift P γ q jStar (m + L) ≤
      determinantDrift P γ q jStar m +
        2 * (Real.exp (detIncrement P q m (m + L)) - 1) :=
    determinantDrift_advance_absorbed d hd γ hγ P E Ψ K S hP hstat hunit hdag
      L hL jStar hjStar metric hmetric m (by omega) hD1
  rcases hcase with heq | hcase
  · -- startup case: m = n
    rw [heq] at hDm1 hp0 hD0 hp1 hD1 hx0 hΔ hexpmono hexpx1 ⊢
    have hdiag : profile P γ q jStar n n = history P γ q jStar n :=
      profile_diagonal_eq_history d hd γ hγ P E Ψ K S hP hstat hunit hdag
        jStar hjStar metric hmetric n
    rw [hdiag] at hp0 hp1 ⊢
    have hstartn := hstart P E Ψ K S hP hstat hunit hdag L hL jStar hjStar hsrc2
      metric hmetric n hn hp1
    nlinarith only [hstartn, hDm1, hexpmono, hp0, hD0, hLr1, hC1.le, hC2.le, hexpx1,
      mul_nonneg (mul_nonneg hC1.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hD0,
      mul_nonneg (mul_nonneg hC2.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hp0,
      mul_nonneg (mul_nonneg hC2.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hD0,
      mul_nonneg (mul_nonneg hC2.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hexpx1,
      mul_nonneg (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ)) hD0,
      mul_nonneg (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ)) hexpx1,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith only [hLr1] : (0:ℝ) ≤
        (L:ℝ))) hp0,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith only [hLr1] : (0:ℝ) ≤
        (L:ℝ))) hD0,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith only [hLr1] : (0:ℝ) ≤
        (L:ℝ))) hexpx1]
  · -- fixed-span case: n + h ≤ m
    have hfixm := hfix P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc1
      metric hmetric n m hn hcase hp1
    nlinarith only [hfixm, hDm1, hexpmono, hp0, hD0, hLr1, hC1.le, hC2.le, hexpx1,
      mul_nonneg (mul_nonneg hC1.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hD0,
      mul_nonneg (mul_nonneg hC2.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hp0,
      mul_nonneg (mul_nonneg hC2.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hD0,
      mul_nonneg (mul_nonneg hC2.le (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ))) hexpx1,
      mul_nonneg (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ)) hD0,
      mul_nonneg (by linarith only [hLr1] : (0:ℝ) ≤ (L:ℝ)) hexpx1,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith only [hLr1] : (0:ℝ) ≤
        (L:ℝ))) hp0,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith only [hLr1] : (0:ℝ) ≤
        (L:ℝ))) hD0,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith only [hLr1] : (0:ℝ) ≤
        (L:ℝ))) hexpx1]

end

end HCPolySupport.HighContrast.Multiscale
