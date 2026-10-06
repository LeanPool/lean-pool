/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.SpanFluctuationSeeds

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.FixedSpan

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 4 — propagation over a fixed span

Group G of the printed proof (`p.fixed.geometry.one.grid.propagation`), third part: the old and
new terms of `𝒫_q(m+L;n)` and **conjunct 3**, `e.fixed.geometry.profile.fixed.span`.

Part of the proof of the statement in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of this group:
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

/-- The generations up to `m` in `𝒫_q(m+L;n)` (`p.fixed.geometry.one.grid.propagation`): the
initial-history term,
the old fluctuation sum and the mean-history contribution all pick up the factor
`3^{-¼(1-γ)L}e^{QΔ^q_{m,m+L}}`, and `𝒫_q(m;n) ≤ 1` converts that into an additive remainder. -/
theorem profile_old_terms_advance_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ L : ℤ, 1 ≤ L →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ∀ (metric : Mat d), metric.PosDef →
              ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
                profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                  (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (n : ℝ))) *
                          (1 + meanPenalty (bigQ d γ)
                            (relMean P (Geometry.explicitRoundedGrid jStar metric) n (m + L))) *
                          history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                        (∑ j ∈ Finset.Ico n m,
                          (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
                            meanPenalty (bigQ d γ)
                              (relMean P (Geometry.explicitRoundedGrid jStar metric)
                                j (m + L))) +
                        ∑ j ∈ Finset.Icc (n + 1) m,
                          (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (j : ℝ))) *
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) j (m
                                  + L)) *
                            ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                                (normalizedFluctuationSelf P
                                  (Geometry.explicitRoundedGrid jStar metric) j a) ^ bigQ d γ ∂P ≤
                    profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                      C * (Real.exp ((bigQ d γ : ℝ) *
                        detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + L)) -
                          1) := by
  let B : ℝ := (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹
  have hB : 0 < B := by
    apply inv_pos.mpr
    apply sub_pos.mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith only [hγ.2]
  refine ⟨1 + B, by linarith only [hB], ?_⟩
  intro P E Ψ K S hP hstat hunit hdag L hL jStar hjStar metric hmetric n m hn hnm hprof
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  let w : ℝ → ℝ := fun x => (3 : ℝ) ^ (-((1 - γ) / 4) * x)
  let p : ℤ → ℤ → ℝ := fun j k => meanPenalty (bigQ d γ) (relMean P q j k)
  let v : ℤ → ℝ := fun j => ∫ a, absSchattenNorm (bigQ d γ : ℝ)
    (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P
  let e := Real.exp ((bigQ d γ : ℝ) * detIncrement P q m (m + L))
  have hw (x : ℝ) : 0 ≤ w x := Real.rpow_nonneg (by norm_num) _
  have hwL : w (L : ℝ) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hγ.2]) (by exact_mod_cast (by omega
      : (0 : ℤ) ≤ L))
  have hsplit (x : ℝ) : w ((L : ℝ) + x) = w (L : ℝ) * w x := by
    dsimp only [w]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have he : 1 ≤ e := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _)
    (Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + L) (hn.trans hnm) (by omega)))
  have hadv (j : ℤ) (hj : (jStar : ℤ) ≤ j) (hjm : j ≤ m) :
      1 + p j (m + L) ≤ e * (1 + p j m) := by
    have h := meanPenalty_normalizedMean_advance d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric j m (m + L) hj hjm (by omega)
    change p j (m + L) ≤ e * p j m + e - 1 at h
    linarith only [h]
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
  have hhistory : 0 ≤ history P γ q jStar n := add_nonneg hfluc
    (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn)
  have hfirst : w (((m + L : ℤ) : ℝ) - (n : ℝ)) * (1 + p n (m + L)) *
      history P γ q jStar n ≤ w (L : ℝ) * e *
        (w ((m : ℝ) - (n : ℝ)) * (1 + p n m) * history P γ q jStar n) := by
    have hweight : w (((m + L : ℤ) : ℝ) - (n : ℝ)) =
        w (L : ℝ) * w ((m : ℝ) - (n : ℝ)) := by
      convert hsplit ((m : ℝ) - (n : ℝ)) using 1; congr 1; push_cast; ring
    rw [hweight]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hadv n hn hnm) (mul_nonneg (hw (L : ℝ)) (hw ((m : ℝ) - (n :
        ℝ))))) hhistory
    (convert h using 1; try rfl)
    ring
  have hmean : (∑ j ∈ Finset.Ico n m,
      w (((m + L : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + L)) ≤
      w (L : ℝ) * e * meanHistory P γ q n m + B * (e - 1) := by
    have hterms : (∑ j ∈ Finset.Ico n m,
        w (((m + L : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + L)) ≤
        ∑ j ∈ Finset.Ico n m, (w (L : ℝ) * e *
          (w ((m : ℝ) - 1 - (j : ℝ)) * p j m) +
          (w (L : ℝ) * (e - 1)) * w ((m : ℝ) - 1 - (j : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have had := hadv j (hn.trans (Finset.mem_Ico.mp hj).1) (Finset.mem_Ico.mp hj).2.le
      have hweight : w (((m + L : ℤ) : ℝ) - 1 - (j : ℝ)) =
          w (L : ℝ) * w ((m : ℝ) - 1 - (j : ℝ)) := by
        convert hsplit ((m : ℝ) - 1 - (j : ℝ)) using 1; congr 1; push_cast; ring
      rw [hweight]
      have hp : p j (m + L) ≤ e * p j m + (e - 1) := by linarith only [had]
      have h := mul_le_mul_of_nonneg_left hp (mul_nonneg (hw (L : ℝ)) (hw ((m : ℝ) - 1 - (j : ℝ))))
      convert h using 1
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hterms
    have hs := profile_geometric_weight_sum_le γ hγ n m
    change ∑ j ∈ Finset.Ico n m, w ((m : ℝ) - 1 - (j : ℝ)) ≤ B at hs
    have htail : (w (L : ℝ) * (e - 1)) *
        (∑ j ∈ Finset.Ico n m, w ((m : ℝ) - 1 - (j : ℝ))) ≤ B * (e - 1) := by
      calc
        _ ≤ (w (L : ℝ) * (e - 1)) * B :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg (hw _) (sub_nonneg.mpr he))
        _ ≤ B * (e - 1) := by
          have h := mul_le_mul_of_nonneg_right hwL (mul_nonneg (sub_nonneg.mpr he) hB.le)
          convert h using 1 <;> first | rfl | ring
    exact hterms.trans (add_le_add le_rfl htail)
  have hsum : (∑ j ∈ Finset.Icc (n + 1) m,
      w (((m + L : ℤ) : ℝ) - (j : ℝ)) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + L)) * v j) =
      w (L : ℝ) * e * ∑ j ∈ Finset.Icc (n + 1) m,
        w ((m : ℝ) - (j : ℝ)) * Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hweight : w (((m + L : ℤ) : ℝ) - (j : ℝ)) =
        w (L : ℝ) * w ((m : ℝ) - (j : ℝ)) := by
      convert hsplit ((m : ℝ) - (j : ℝ)) using 1; congr 1; push_cast; ring
    rw [hweight, ← logDetLoss_add P q j m (m + L), mul_add, Real.exp_add]
    dsimp only [e]
    ring
  have hprof0 : 0 ≤ profile P γ q jStar n m := by
    have hp := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric n m hn hnm).2.2.2.2.2
    unfold profile
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (mul_nonneg (hw _) (by linarith only [hp])) hhistory)
        (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
          jStar hjStar metric hmetric n m hn hnm)
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw _) (Real.exp_nonneg _))
        (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)
  have htotal := add_le_add (add_le_add hfirst hmean) (le_of_eq hsum)
  have hbound : w (L : ℝ) * e * profile P γ q jStar n m ≤
      profile P γ q jStar n m + (e - 1) := by
    calc
      _ ≤ e * profile P γ q jStar n m := by
        have h := mul_le_mul_of_nonneg_right hwL (mul_nonneg (by linarith only [he]) hprof0)
        convert h using 1 <;> first | rfl | ring
      _ ≤ _ := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hprof)]
  change _ ≤ profile P γ q jStar n m + (1 + B) * (e - 1)
  have hcollect :
      w (L : ℝ) * e * (w ((m : ℝ) - (n : ℝ)) * (1 + p n m) * history P γ q jStar n) +
        (w (L : ℝ) * e * meanHistory P γ q n m + B * (e - 1)) +
        w (L : ℝ) * e * (∑ j ∈ Finset.Icc (n + 1) m,
          w ((m : ℝ) - (j : ℝ)) * Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) * v j) =
        w (L : ℝ) * e * profile P γ q jStar n m + B * (e - 1) := by
    dsimp only [profile, w, p, v]
    ring
  rw [hcollect] at htotal
  exact htotal.trans (by nlinarith only [hbound])

/-- The new mean terms of an arbitrary advance (`p.fixed.geometry.one.grid.propagation`): `L`
indices, weights at
most one, each penalty at most `e^{QΔ^q_{m,m+L}} - 1`. -/
theorem meanPenalty_new_terms_span_sum_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
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
                ∑ j ∈ Finset.Ico m (m + L),
                    (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
                      meanPenalty (bigQ d γ)
                        (relMean P (Geometry.explicitRoundedGrid jStar metric) j (m + L)) ≤
                  C * (L : ℝ) *
                    (Real.exp ((bigQ d γ : ℝ) *
                      detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + L)) - 1)
                        := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag L hL jStar hjStar metric hmetric m hm
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  have hterm (j : ℤ) (hj : j ∈ Finset.Ico m (m + L)) :
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
      meanPenalty (bigQ d γ) (relMean P q j (m + L)) ≤
      Real.exp ((bigQ d γ : ℝ) * detIncrement P q m (m + L)) - 1 := by
    have hj' := Finset.mem_Ico.mp hj
    have hpen := meanPenalty_normalizedMean_le_exp_sub_one d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric j (m + L) (hm.trans hj'.1) hj'.2.le
    have hp := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric j (m + L) (hm.trans hj'.1) hj'.2.le).2.2.2.2.2
    have hweight : (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - 1 - (j : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith only [hγ.2])
      have : (0 : ℤ) ≤ m + L - 1 - j := by omega
      exact_mod_cast this
    have hinc := Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric m j hm hj'.1
    have hadd := logDetLoss_add P q m j (m + L)
    have hloss : detIncrement P q j (m + L) ≤ detIncrement P q m (m + L) := by
      linarith only [hinc, hadd]
    exact (mul_le_of_le_one_left hp hweight).trans (hpen.trans
      (sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hloss (Nat.cast_nonneg
        _))) 1))
  have hsum := Finset.sum_le_sum hterm
  have hcard : ((Finset.Ico m (m + L)).card : ℝ) = (L : ℝ) := by
    rw [Int.card_Ico, show m + L - m = L by ring]
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ L)
  simpa only [Finset.sum_const, nsmul_eq_mul, hcard, one_mul] using hsum

/-- **Conjunct 3**, `e.fixed.geometry.profile.fixed.span`
(`p.fixed.geometry.one.grid.propagation`). -/
theorem profile_fixed_span (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
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
                    ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                                  m (m + L)) - 1) := by
  obtain ⟨Csrc, hCsrc, C3, hC3, hnew⟩ := new_fluctuations_span_le d hd γ hγ
  obtain ⟨C1, hC1, hold⟩ := profile_old_terms_advance_le d hd γ hγ
  obtain ⟨C2, hC2, hmean⟩ := meanPenalty_new_terms_span_sum_le d hd γ hγ
  refine ⟨Csrc, hCsrc, 1 + C1 + C2 + C3, by positivity, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc metric hmetric n m hn hnm hprof
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric with hq_def
  have hnm' : n ≤ m := by omega
  have hm : (jStar : ℤ) ≤ m := hn.trans hnm'
  have hold' := hold P E Ψ K S hP hstat hunit hdag L hL jStar hjStar metric hmetric n m hn hnm'
    hprof
  have hmean' := hmean P E Ψ K S hP hstat hunit hdag L hL jStar hjStar metric hmetric m hm
  have hnew' := hnew P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc metric hmetric
    n m hn hnm hprof
  set p := profile P γ q jStar n m with hp_def
  set x := (bigQ d γ : ℝ) * detIncrement P q m (m + L) with hx_def
  have hp0 : 0 ≤ p := by
    have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric n m hn hnm').2.2.2.2.2
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
    have hhistory : 0 ≤ history P γ q jStar n := add_nonneg hfluc
      (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
        jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn)
    rw [hp_def]
    unfold profile
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (by linarith only [hpen])) hhistory)
        (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
          jStar hjStar metric hmetric n m hn hnm')
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.exp_nonneg _)) (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _)
    (Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + L) hm (by omega))
  have he'0 : 0 ≤ Real.exp x - 1 := by linarith only [Real.one_le_exp hx0]
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by
    have : (0 : ℤ) ≤ L := by omega
    exact_mod_cast this
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  conv_lhs => unfold profile meanHistory
  have hIcoEq : Finset.Ico n (m + L) = Finset.Ico n m ∪ Finset.Ico m (m + L) :=
    (Finset.Ico_union_Ico_eq_Ico hnm' (by omega : m ≤ m + L)).symm
  have hIcoDisj : Disjoint (Finset.Ico n m) (Finset.Ico m (m + L)) :=
    Finset.Ico_disjoint_Ico_consecutive n m (m + L)
  have hIccEq : Finset.Icc (n + 1) (m + L) =
      Finset.Icc (n + 1) m ∪ Finset.Icc (m + 1) (m + L) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hIccDisj : Disjoint (Finset.Icc (n + 1) m) (Finset.Icc (m + 1) (m + L)) :=
    Finset.disjoint_left.2 (by intro y hy hy'; simp only [Finset.mem_Icc] at hy hy'; omega)
  rw [hIcoEq, Finset.sum_union hIcoDisj, hIccEq, Finset.sum_union hIccDisj]
  have h1 : 0 ≤ ((L : ℝ) - 1) * p := mul_nonneg (by linarith only [hL1]) hp0
  have h2 : 0 ≤ C1 * (((L : ℝ) - 1) * (Real.exp x - 1)) :=
    mul_nonneg hC1.le (mul_nonneg (by linarith only [hL1]) he'0)
  have h3 : 0 ≤ C1 * ((L : ℝ) * p) := mul_nonneg hC1.le (mul_nonneg hL0 hp0)
  have h4 : 0 ≤ C2 * ((L : ℝ) * p) := mul_nonneg hC2.le (mul_nonneg hL0 hp0)
  have h5 : 0 ≤ (L : ℝ) * (Real.exp x - 1) := mul_nonneg hL0 he'0
  nlinarith only [hold', hmean', hnew', h1, h2, h3, h4, h5]


end

end HCPolySupport.HighContrast.Multiscale
