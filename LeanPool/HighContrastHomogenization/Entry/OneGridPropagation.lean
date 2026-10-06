/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.Startup

/-!
# High-contrast homogenization: Entry.OneGridPropagation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One-grid propagation

The type repeats the statement of
`HCPoly/Entry/Statements/OneGridPropagation.lean` (`p.fixed.geometry.one.grid.propagation`): same
binders, same
binder kinds and order, same eight guarded conjuncts, the source-lower-scale premise
where the statement has it, and no additional hypothesis.  This source-facing statement carries
the source lower scale
exactly; the internal algebraic and history lemmas it assembles (in
`HCPoly/Entry/Multiscale/OneGrid/`) include stronger statements that omit an unused source-scale
threshold,
and the generic integration helpers among them take finiteness, integrability or
measurability inputs that are proved at their own use sites, not extra premises of this
proposition.

The eight conjuncts are proved in `HCPoly/Entry/Multiscale/OneGrid/`, one printed step per file;
this file only assembles them under one `Csrc` and one `C = C(d,γ)` chosen before the law,
the geometry, `h`, `L` and `j_*`, as the statement requires.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory

noncomputable section

/-- **The eight-conclusion form** of `p.fixed.geometry.one.grid.propagation`: the four printed
conclusions (i)–(iv) of the proposition together with the four estimates that the paper
proves on the way (`e.fixed.geometry.profile.contraction`, `e.fixed.geometry.profile.fixed.span`,
`e.fixed.geometry.profile.startup`, `e.fixed.geometry.carried.majorization`), all under one
`C_src` and one `C = C(d,γ)`. The proposition's own statement projects out of this one.

Assembled from the eight conjunct proofs by taking one `Csrc` and one `C` above all of theirs.
The proposition's own `C` is a single `C(d,γ)`; the printed proof's "`C` may change from line to
line" is realized by the per-conjunct existentials, never by a constant that sees the law, the
geometry, `h`, `L` or `j_*`. -/
theorem fixed_geometry_one_grid_propagation_full
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
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
                  history P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                      C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h :
                        ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m
                                  + L)) - 1)) ∧
                    (m = n →
                      history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (n + L) ≤
                          C * (L : ℝ) *
                            (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n
                                  + L)) - 1)) ∧
                    fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                          meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) (jStar :
                            ℤ) m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                        C * (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m) ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h :
                        ℤ)) +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            (m + (h : ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m) +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    (∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
                      ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                        ∑ k ∈ Finset.range Ksteps,
                            synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ)
                              (m₀ + (k : ℤ) * (h : ℤ)) ≤
                          (h : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                              (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ))) ∧
                    ((m = n ∨ n + (h : ℤ) ≤ m) →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                              jStar (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m
                                  (m + L)) - 1)) := by
  obtain ⟨C1, hC1, hhist⟩ := Multiscale.history_le_profile d hd γ hγ
  obtain ⟨Csrc2, hCs2, C2, hC2, hcontr⟩ := Multiscale.profile_contraction d hd γ hγ
  obtain ⟨Csrc3, hCs3, C3, hC3, hfix⟩ := Multiscale.profile_fixed_span d hd γ hγ
  obtain ⟨Csrc4, hCs4, C4, hC4, hstart⟩ := Multiscale.profile_startup d hd γ hγ
  obtain ⟨C5, hC5, hcarry⟩ := Multiscale.carried_history_majorization d hd γ hγ
  obtain ⟨Csrc6, hCs6, C6, hC6, hsync⟩ := Multiscale.synchronized_propagation d hd γ hγ
  obtain ⟨Csrc8, hCs8, C8, hC8, hspan⟩ := Multiscale.fixed_span_propagation d hd γ hγ
  have hmult := Multiscale.synchronized_multiplicity d hd γ hγ
  refine ⟨max Csrc2 (max Csrc3 (max Csrc4 (max Csrc6 Csrc8))), lt_max_of_lt_left hCs2,
    C1 + C2 + C3 + C4 + C5 + C6 + C8,
    by linarith only [hC1, hC2, hC3, hC4, hC5, hC6, hC8], ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc metric hmetric n m hn hnm
  let := hP
  have hlogb : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 3)
      (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) ≤ 2 * K)
  have hmono : ∀ c : ℝ, c ≤ max Csrc2 (max Csrc3 (max Csrc4 (max Csrc6 Csrc8))) →
      ⌈c * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) := fun c hc =>
    le_trans (Int.ceil_mono (mul_le_mul_of_nonneg_right hc hlogb)) hsrc
  have hsrc2 : ⌈Csrc2 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) := hmono _ (le_max_left _ _)
  have hsrc3 : ⌈Csrc3 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hmono _ (le_max_of_le_right (le_max_left _ _))
  have hsrc4 : ⌈Csrc4 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hmono _ (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hsrc6 : ⌈Csrc6 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hmono _ (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  have hsrc8 : ⌈Csrc8 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hmono _ (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
  have hQ2 : 2 ≤ bigQ d γ := Multiscale.bigQ_two_le d γ hγ
  have hh1 : 1 ≤ h := by omega
  have hQ0 : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hjm : (jStar : ℤ) ≤ m := le_trans hn hnm
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ L)
  have hmean0 := Multiscale.meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
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
    exact (Multiscale.bigQ_even d γ).pow_nonneg _
  have hH0 : 0 ≤ history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n := add_nonneg
    hfluc hmean0
  have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n m hn hnm).2.2.2.2.2
  have hw (x : ℝ) : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * x) := Real.rpow_nonneg (by norm_num) _
  have hp0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m := by
    unfold profile
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (mul_nonneg (hw _) (by linarith only [hpen])) hH0)
        (Multiscale.meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
          jStar hjStar metric hmetric n m hn hnm)
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw _) (Real.exp_nonneg _))
        (integral_nonneg fun _ => (Multiscale.bigQ_even d γ).pow_nonneg _)
  have hD0 : 0 ≤ determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m :=
    Multiscale.determinantDrift_nonneg d hd γ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric m
  have hDmL : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + L) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + L) hjm (by omega)
  have hexpmL : 0 ≤ Real.exp ((bigQ d γ : ℝ) *
      detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + L)) - 1 := by
    have := Real.one_le_exp (mul_nonneg hQ0 hDmL)
    linarith only [this]
  have hDnL : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      n (n + L) hn (by omega)
  have hexpnL : 0 ≤ Real.exp ((bigQ d γ : ℝ) *
      detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1 := by
    have := Real.one_le_exp (mul_nonneg hQ0 hDnL)
    linarith only [this]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hA := hhist P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
    have hB : 0 ≤ (C2 + C3 + C4 + C5 + C6 + C8) *
        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m :=
      mul_nonneg (by linarith only [hC2, hC3, hC4, hC5, hC6, hC8]) hp0
    linarith only [hA, hB]
  · intro hnhm
    have hA := hcontr P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc2 metric hmetric
      n m hn hnhm
    have hsyncle := Multiscale.logDetLoss_le_synchronizedLogDetLoss d hd γ hγ P E Ψ K S
      hP hstat hunit hdag h hh1 jStar hjStar metric hmetric m (m + (h : ℤ))
      (by omega) (by omega) le_rfl
    rw [add_sub_cancel_right] at hsyncle
    have hlog0 : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ)) :=
      Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
        m (m + (h : ℤ)) hjm (by omega)
    have hDhat0 : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m :=
      le_trans hlog0 hsyncle
    have hexph : 0 ≤ Real.exp ((bigQ d γ : ℝ) *
        synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1 := by
      have := Real.one_le_exp (mul_nonneg hQ0 hDhat0)
      linarith only [this]
    have hB : 0 ≤ (C1 + C3 + C4 + C5 + C6 + C8) *
        (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) :=
      mul_nonneg (by linarith only [hC1, hC3, hC4, hC5, hC6, hC8]) hexph
    linarith only [hA, hB]
  · intro hnhm hple
    have hA := hfix P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc3 metric hmetric
      n m hn hnhm hple
    have hB : 0 ≤ (C1 + C2 + C4 + C5 + C6 + C8) * (L : ℝ) *
        (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + L)) - 1) :=
      mul_nonneg (mul_nonneg (by linarith only [hC1, hC2, hC4, hC5, hC6, hC8]) hL0)
        (by linarith only [hp0, hexpmL])
    linarith only [hA, hB]
  · intro _hmn hhle
    have hA := hstart P E Ψ K S hP hstat hunit hdag L hL jStar hjStar hsrc4 metric hmetric
      n hn hhle
    have hB : 0 ≤ (C1 + C2 + C3 + C5 + C6 + C8) * (L : ℝ) *
        (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
          Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n + L)) - 1) :=
      mul_nonneg (mul_nonneg (by linarith only [hC1, hC2, hC3, hC5, hC6, hC8]) hL0)
        (by linarith only [hH0, hexpnL])
    linarith only [hA, hB]
  · have hA := hcarry P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
    have hB : 0 ≤ (C1 + C2 + C3 + C4 + C6 + C8) *
        (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m) :=
      mul_nonneg (by linarith only [hC1, hC2, hC3, hC4, hC6, hC8])
        (by linarith only [hp0, hD0])
    linarith only [hA, hB]
  · intro hnhm
    have hA := hsync P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc6 metric hmetric
      n m hn hnhm
    have hsyncle := Multiscale.logDetLoss_le_synchronizedLogDetLoss d hd γ hγ P E Ψ K S
      hP hstat hunit hdag h hh1 jStar hjStar metric hmetric m (m + (h : ℤ))
      (by omega) (by omega) le_rfl
    rw [add_sub_cancel_right] at hsyncle
    have hlog0 : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ)) :=
      Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
        m (m + (h : ℤ)) hjm (by omega)
    have hDhat0 : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m :=
      le_trans hlog0 hsyncle
    have hexph : 0 ≤ Real.exp ((bigQ d γ : ℝ) *
        synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1 := by
      have := Real.one_le_exp (mul_nonneg hQ0 hDhat0)
      linarith only [this]
    have hB : 0 ≤ (C1 + C2 + C3 + C4 + C5 + C8) *
        (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) :=
      mul_nonneg (by linarith only [hC1, hC2, hC3, hC4, hC5, hC8]) hexph
    linarith only [hA, hB]
  · exact hmult P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric
  · intro hcase hle1
    have hA := hspan P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc8 metric hmetric
      n m hn hnm hcase hle1
    have hB : 0 ≤ (C1 + C2 + C3 + C4 + C5 + C6) * (L : ℝ) *
        (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
          Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + L)) - 1) :=
      mul_nonneg (mul_nonneg (by linarith only [hC1, hC2, hC3, hC4, hC5, hC6]) hL0)
        (by linarith only [hp0, hD0, hexpmL])
    linarith only [hA, hB]

/-- **The statement proved for `p.fixed.geometry.one.grid.propagation`**: the four printed
conclusions
(i)–(iv), projected out of `fixed_geometry_one_grid_propagation_full`, whose eight conclusions
list them as the first, sixth, eighth and seventh. The statement repeats the statement
`HCPolySupport.HighContrast.fixed_geometry_one_grid_propagation`
(`HCPoly/Entry/Statements/OneGridPropagation.lean`)
byte for byte. -/
theorem fixedGeometryPropagation
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
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
                  history P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                      C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h :
                        ℤ)) +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            (m + (h : ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m) +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    ((m = n ∨ n + (h : ℤ) ≤ m) →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                              jStar (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m
                                  (m + L)) - 1)) ∧
                    (∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
                      ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                        ∑ k ∈ Finset.range Ksteps,
                            synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ)
                              (m₀ + (k : ℤ) * (h : ℤ)) ≤
                          (h : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                              (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ))) := by
  obtain ⟨Csrc, hCsrc, C, hC, hfull⟩ := fixed_geometry_one_grid_propagation_full d hd γ hγ
  refine ⟨Csrc, hCsrc, C, hC, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc metric hmetric n m hn hnm
  obtain ⟨h1, -, -, -, -, h6, h7, h8⟩ :=
    hfull P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc metric hmetric n m hn hnm
  exact ⟨h1, h6, h8, h7⟩

end

end HCPolySupport.HighContrast.Entry
