/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.Contraction

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.SynchronizedPropagation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 3 — the drift advance and synchronized propagation

Group F of the printed proof (`p.fixed.geometry.one.grid.propagation`): the determinant-drift
advance and **conjunct 6**, `e.fixed.geometry.synchronized.propagation`.

Part of the proof of
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of the group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
source-facing module `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused source-scale threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.

The declaration text of this file is copied unchanged; only this
header, the imports and the namespace frame are new.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group F. Step 3 — the drift advance and the synchronized propagation
(`p.fixed.geometry.one.grid.propagation`) -/

/-- `e.fixed.geometry.drift.advance` at the actual
stochastic use site: the helper `determinantDrift_advance_of_posDef_antitone` composed with
`Annealed.adaptedMean_posDef` and `Annealed.adaptedMean_antitone`.  It needs only `m ≥ j_*`, so
it also serves the diagonal case of Step 5. -/
theorem determinantDrift_advance (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ m L : ℤ, (jStar : ℤ) ≤ m → 1 ≤ L →
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + L) ≤
              (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) *
                    Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m +
                      L)) *
                    determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                  Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m +
                    L)) - 1 := by
  intro P E Ψ K S hprob hstat _hunit hdag jStar hjStar metric hmetric m L hm hL
  let : IsProbabilityMeasure P := hprob
  exact
    HCPolySupport.HighContrast.Multiscale.determinantDrift_advance_of_posDef_antitone P γ hγ.2.le
      (Geometry.explicitRoundedGrid jStar metric) jStar m L hm hL
      (fun j _ =>
        HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar
          hjStar metric hmetric j)
      (fun j hj =>
        HCPolySupport.HighContrast.Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar
          hjStar metric hmetric (j - 1) j (by
            rw [Set.mem_Icc] at hj
            omega) (by omega))

/-- **Conjunct 6**, `e.fixed.geometry.synchronized.propagation`
(`p.fixed.geometry.one.grid.propagation`): the drift advance at `L = h` gives `D_{q,j_*}(m+h) ≤
⅛e^{QΔ̂^q_h(m)}D_{q,j_*}(m) +
C(e^{QΔ̂^q_h(m)}-1)`, which is added to the profile contraction. -/
theorem synchronized_propagation (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (metric : Mat d), metric.PosDef →
                  ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                    profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                          (m + (h : ℤ)) ≤
                      1 / 8 *
                          Real.exp ((bigQ d γ : ℝ) *
                            synchCharge P
                              (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
                          (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                              jStar m) +
                        C * (Real.exp ((bigQ d γ : ℝ) *
                          synchCharge P
                            (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) := by
  obtain ⟨Csrc, hCsrc, C, hC, hcon⟩ := profile_contraction d hd γ hγ
  refine ⟨Csrc, hCsrc, C + 1, by linarith only [hC], ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc metric hmetric n m hn hnm
  let := hP
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hh1 : 1 ≤ h := by omega
  have hjm : (jStar : ℤ) ≤ m := by omega
  have hL1 : (1 : ℤ) ≤ (h : ℤ) := by omega
  have hP1 := hcon P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc metric hmetric n m hn hnm
  have hD := determinantDrift_advance d hd γ hγ P E Ψ K S hP hstat hunit hdag jStar hjStar
    metric hmetric m (h : ℤ) hjm hL1
  push_cast at hD
  have hD0 : 0 ≤ determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m :=
    determinantDrift_nonneg d hd γ P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric m
  have hlog0 : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ)) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + (h : ℤ)) hjm (by omega)
  have hsync0 := logDetLoss_le_synchronizedLogDetLoss d hd γ hγ P E Ψ K S hP hstat hunit hdag
    h hh1 jStar hjStar metric hmetric m (m + (h : ℤ)) (by omega) (by omega) (le_refl _)
  rw [add_sub_cancel_right] at hsync0
  have hDhat0 : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m :=
    le_trans hlog0 hsync0
  have hQ1 : (1 : ℝ) ≤ (bigQ d γ : ℝ) := by exact_mod_cast (by omega : 1 ≤ bigQ d γ)
  have hDeltaQ : detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ)) ≤
      (bigQ d γ : ℝ) * synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m :=
    hsync0.trans (le_mul_of_one_le_left hDhat0 hQ1)
  have hE : Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ))) ≤
      Real.exp ((bigQ d γ : ℝ) *
        synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) :=
    Real.exp_le_exp.mpr hDeltaQ
  have hcoef := three_rpow_neg_eighth_span_lt d hd γ hγ h hh
  have hb1nn : 0 ≤ Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m +
    (h : ℤ))) :=
    Real.exp_nonneg _
  have hab : (3 : ℝ) ^ (-((1 - γ) / 8) * (h : ℝ)) *
      Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ))) ≤
      1 / 8 * Real.exp ((bigQ d γ : ℝ) *
        synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) := by
    calc (3 : ℝ) ^ (-((1 - γ) / 8) * (h : ℝ)) *
        Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ)))
        ≤ 1 / 8 * Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h
          : ℤ))) :=
          mul_le_mul_of_nonneg_right hcoef.le hb1nn
      _ ≤ 1 / 8 * Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) :=
          mul_le_mul_of_nonneg_left hE (by norm_num)
  have hDfinal : determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + (h
    : ℤ)) ≤
      1 / 8 * Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
      (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) := by
    have hmul := mul_le_mul_of_nonneg_right hab hD0
    linarith only [hD, hmul, hE]
  have hsum := add_le_add hP1 hDfinal
  have heq :
      (1 / 8 * Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
        C * (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1)) +
      (1 / 8 * Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
        (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1)) =
      1 / 8 * Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
        (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m) +
      (C + 1) * (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) := by
    ring
  rw [heq] at hsum
  exact hsum

end

end HCPolySupport.HighContrast.Multiscale
