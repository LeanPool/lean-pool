/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.BadScaleTailDenominator

/-!
# Coarse-graining support: Support.Book.Ch05.Theorems.Section57.BadScaleTailRaw

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Raw-constant bad-scale component inputs

This file exposes the mixed high-bottom fixed-pair estimate with the raw high
and crude pair estimates supplied as hypotheses.  This keeps the constants used
by the top, mixed-bottom, and crude-bottom branches synchronized for the final
bad-scale assembly.
-/

noncomputable section

private theorem measureReal_le_softPairTail_of_threshold_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E F : Set Ω} {pref lower lam exponent : ℝ}
    (hEF : E ⊆ F) (hpref : 0 ≤ pref) (hexponent : 0 < exponent)
    (hlower : lower ≤ lam)
    (hbound : 1 ≤ lam → μ.real F ≤ pref * Real.exp (-(lam ^ exponent))) :
    μ.real E ≤ softPairTail pref lower exponent := by
  have hsoft : μ.real E ≤ softPairTail pref lam exponent := by
    by_cases hlam : 1 ≤ lam
    · exact (measureReal_mono (μ := μ) hEF).trans
        ((hbound hlam).trans
          (pref_mul_exp_le_softPairTail_of_one_le_lam hpref hlam))
    · exact (measureReal_le_one (μ := μ) (s := E)).trans
        (one_le_softPairTail_of_not_one_le_lam hlam)
  exact hsoft.trans (softPairTail_mono_lam hexponent hlower)

private theorem measureReal_le_soft_branch_maximum_of_threshold_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E F : Set Ω} {pref lower₁ lower₂ lam₁ lam₂ exponent₁ exponent₂ : ℝ}
    (hEF : E ⊆ F) (hpref : 0 ≤ pref)
    (hexponent₁ : 0 < exponent₁) (hexponent₂ : 0 < exponent₂)
    (hlower₁ : lower₁ ≤ lam₁) (hlower₂ : lower₂ ≤ lam₂)
    (hbound₁ : 1 ≤ lam₁ → μ.real F ≤ pref * Real.exp (-(lam₁ ^ exponent₁)))
    (hbound₂ : 1 ≤ lam₂ → μ.real F ≤ pref * Real.exp (-(lam₂ ^ exponent₂))) :
    μ.real E ≤ max 1 pref *
      Real.exp (1 - max ((max 1 lower₁) ^ exponent₁) ((max 1 lower₂) ^ exponent₂)) := by
  exact le_maxExponent_softPairTail_of_le_both
    (measureReal_le_softPairTail_of_threshold_bound hEF hpref hexponent₁ hlower₁ hbound₁)
    (measureReal_le_softPairTail_of_threshold_bound hEF hpref hexponent₂ hlower₂ hbound₂)

private theorem bottom_branch_tailParameters_lower_bounds
    {d : ℕ} [NeZero d] {K Cfluct Ccrude θ a t αbad : ℝ} {q m n : ℕ}
    (hK_pos : 0 < K) (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (hθ : 0 < θ) (ha : 0 < a) (ht : 0 < t) (hαt : αbad < t)
    (hell : selectedBadPairScale K a t αbad q m n < n)
    (hnq : n ≤ q) (hqm : q ≤ m) :
    let x : ℝ := αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let ell : ℕ := selectedBadPairScale K a t αbad q m n
    let b : ℝ := (d : ℝ) / 2
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
        (2 * K * Cfluct * θ ^ (2 : ℕ)) ≤
      (3 : ℝ) ^ (-x) /
        (2 * K * (Cfluct *
          (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) * θ ^ (2 : ℕ))) ∧
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) + (t - αbad) * ((m - q : ℕ) : ℝ)) /
        (K * Ccrude * θ ^ (2 : ℕ)) ≤
      (3 : ℝ) ^ (-x) / (K * (Ccrude * θ ^ (2 : ℕ))) := by
  constructor
  · exact highBottom_tailParameter_interpolation_lower_bound
      hK_pos hCfluct hθ ha ht hαt hell hnq hqm
  · exact crudeBottom_tailParameter_discount_lower_bound hK_pos hCcrude hθ hnq hqm

/-- Exact fixed-pair mixed-bottom estimate with the high and crude raw pair
estimates supplied externally, so downstream assembly can use one shared set
of constants. -/
theorem shiftedHighBottomPairMeasure_le_softMax_of_pairBounds
    {d : ℕ} [NeZero d] {σ Cfluct Ccrude Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (_hCentry : 0 < Centry) (ha : 0 < a)
    (hhighRaw :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let ell : ℕ :=
          Nat.ceil
            ((a * Real.log 3)⁻¹ *
              (Real.log (max (2 * K) 1) + x * Real.log 3))
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let tau : ℝ := min σ 2
        let scale : ℝ :=
          Cfluct *
            (3 : ℝ) ^
              ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ)
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / (2 * K * scale)
        ell < n → n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))))
    (hcrudeRaw :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {N0 q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / scale
        n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ)))) :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let tau : ℝ := min σ 2
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          max 1 pref *
            Real.exp
              (1 - max ((max 1 highA) ^ tau) ((max 1 crudeA) ^ σ)) := by
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hnm hqm ht hαt
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ell : ℕ := selectedBadPairScale K a t αbad q m n
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let tau : ℝ := min σ 2
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let highA : ℝ :=
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  by_cases hnq : n ≤ q
  · by_cases hell : selectedBadPairScale K a t αbad q m n < n
    · let highScale : ℝ :=
        Cfluct *
          (3 : ℝ) ^
            ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)
      let T : ℝ := Real.rpow (3 : ℝ) (-x)
      let highLam : ℝ := T / (2 * K * highScale)
      let crudeScale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
      let crudeLam : ℝ := T / crudeScale
      obtain ⟨hHighLam, hCrudeLam⟩ :=
        bottom_branch_tailParameters_lower_bounds
          (d := d) (K := K) (Cfluct := Cfluct) (Ccrude := Ccrude)
          (θ := hΓ.thetaHat) (by simpa [K] using quenchedProbeEnvelopeConst_pos d)
          hCfluct hCcrude hΓ.thetaHat_pos ha ht hαt hell hnq hqm
      have htau_pos : 0 < tau := by
        dsimp [tau]
        exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
      refine measureReal_le_soft_branch_maximum_of_threshold_bounds
        (F := badPairEvent Hshift t αbad q m n)
        (lam₁ := highLam) (lam₂ := crudeLam) (by intro ω hω; exact hω.2.2)
        (by dsimp [pref]; positivity) htau_pos hσ_pos hHighLam hCrudeLam ?_ ?_
      · intro hlam
        have hraw :=
          hhighRaw (t := t) (αbad := αbad)
            hP hStruct hΓ hσ_eq hparams
            (q := q) (m := m) (n := n)
        dsimp only at hraw
        have hbad :
            P.real (badPairEvent Hshift t αbad q m n) ≤
              (S.card : ℝ) *
                ((D.card : ℝ) * Real.exp (-(highLam ^ tau))) := by
          simpa [K, x, ell, selectedBadPairScale, N0, Hshift, D, S, tau,
            highScale, T, highLam] using
            hraw hell hnm hqm hlam
        simpa [pref, mul_assoc] using hbad
      · intro hlam
        have hraw :=
          hcrudeRaw (t := t) (αbad := αbad)
            hP hStruct hΓ hσ_eq hparams
            (N0 := N0) (q := q) (m := m) (n := n)
        dsimp only at hraw
        have hbad :
            P.real (badPairEvent Hshift t αbad q m n) ≤
              (S.card : ℝ) *
                ((D.card : ℝ) * Real.exp (-(crudeLam ^ σ))) := by
          simpa [K, Hshift, x, D, S, crudeScale, T, crudeLam] using
            hraw hnm hqm hlam
        simpa [pref, mul_assoc] using hbad
    · have hempty :
          highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [highBottomPairEvent, hell]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact mul_nonneg
        ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))
        (Real.exp_pos _).le
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, hnq]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact mul_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))
      (Real.exp_pos _).le

private theorem maximum_one_product_le_weighted_prefactor
    {S D w : ℝ} {q r : ℕ} (hD_nonneg : 0 ≤ D) (hw : 1 ≤ w)
    (hDcard : D ≤ w ^ q * w ^ r) :
    max 1 (S * D) ≤ max 1 S * w ^ q * w ^ r := by
  have hpref_le : S * D ≤ max 1 S * w ^ q * w ^ r := by
    calc
      S * D ≤ max 1 S * (w ^ q * w ^ r) :=
        mul_le_mul (le_max_right 1 S) hDcard hD_nonneg
          (zero_le_one.trans (le_max_left 1 S))
      _ = max 1 S * w ^ q * w ^ r := by ring
  have hone : 1 ≤ max 1 S * w ^ q * w ^ r := by
    have hmaxS : 1 ≤ max 1 S := le_max_left 1 S
    have hwq_one : 1 ≤ w ^ q := one_le_pow₀ hw
    have hwr_one : 1 ≤ w ^ r := one_le_pow₀ hw
    nlinarith [hmaxS, hwq_one, hwr_one]
  exact max_le hone hpref_le

private theorem mixed_bottom_offset_nonnegative
    {a b K τ : ℝ} (ha : 0 < a) (hb_pos : 0 < b) (hτ_pos : 0 < τ) :
    0 ≤ τ * b * ((a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1) + 1) := by
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
  have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
    Real.log_nonneg (le_max_right (2 * K) 1)
  positivity

private theorem mixedBottom_row_power_le_branch_maximum
    {d : ℕ} [NeZero d] {σ t αbad L Dhigh Dcrude Den : ℝ} {q r m n : ℕ}
    (hσ_pos : 0 < σ) (ht : 0 < t) (htb : t ≤ (d : ℝ) / 2) (hαt : αbad < t)
    (hm_sub_q : m - q = r)
    (hη_pos : 0 < finiteQuenchedTailExponent d σ t)
    (hτ_pos : 0 < finiteQuenchedTailTau σ)
    (hDhigh_pos : 0 < Dhigh) (hDcrude_pos : 0 < Dcrude) (hDen : 0 < Den)
    (hDen_high : Dhigh ^ finiteQuenchedTailTau σ ≤
      Den ^ finiteQuenchedTailExponent d σ t)
    (hDen_crude : Dcrude ^ σ ≤ Den ^ finiteQuenchedTailExponent d σ t)
    (hoff_nonneg : 0 ≤ finiteQuenchedTailTau σ * ((d : ℝ) / 2) * (L + 1)) :
    let b : ℝ := (d : ℝ) / 2
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := finiteQuenchedTailExponent d σ t
    let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
    let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
    (A * ρ ^ r) ^ η ≤
      max
        ((max 1 ((3 : ℝ) ^
          (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
            (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) / Dhigh)) ^ τ)
        ((max 1 ((3 : ℝ) ^
          (t * ((q - n : ℕ) : ℝ) +
            (t - αbad) * ((m - q : ℕ) : ℝ)) / Dcrude)) ^ σ) := by
  let b : ℝ := (d : ℝ) / 2
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let highA : ℝ :=
    (3 : ℝ) ^
      (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
        (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) / Dhigh
  let crudeA : ℝ :=
    (3 : ℝ) ^
      (t * ((q - n : ℕ) : ℝ) +
        (t - αbad) * ((m - q : ℕ) : ℝ)) / Dcrude
  let row : ℝ := τ * (t - αbad)
  let offset : ℝ := τ * b * (L + 1)
  let X : ℝ := η * (q : ℝ) - offset + row * (r : ℝ)
  let Xhigh : ℝ :=
    τ *
      (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
        (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1))
  let Xcrude : ℝ :=
    σ *
      (t * ((q - n : ℕ) : ℝ) +
        (t - αbad) * ((m - q : ℕ) : ℝ))
  have hcollapse_raw :
      η * (q : ℝ) + τ * (t - αbad) * (r : ℝ) ≤
        max
          (τ *
            (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
              (t - αbad) * (r : ℝ)))
          (σ * (t * ((q - n : ℕ) : ℝ) + (t - αbad) * (r : ℝ))) := by
    have hmain :=
      finiteQuenchedTailExponent_mul_nat_add_row_le_max_bottom
        (d := d) (q := q) (n := n) (r := r)
        (σ := σ) (t := t) (α := αbad) hσ_pos ht hαt
        (by simpa [b] using htb)
    simpa [b, τ, η] using hmain
  have hcollapse :
      X ≤ max Xhigh Xcrude := by
    have hsub :=
      sub_nonneg_le_max_sub_left_of_le_max
        (c := offset) (by simpa [offset] using hoff_nonneg)
        hcollapse_raw
    have hX_eq :
        X = η * (q : ℝ) + τ * (t - αbad) * (r : ℝ) - offset := by
      dsimp [X, row]
      ring
    have hXhigh_eq :
        Xhigh =
          τ *
            (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
              (t - αbad) * (r : ℝ)) - offset := by
      dsimp [Xhigh, offset]
      rw [hm_sub_q]
      ring
    have hXcrude_eq :
        Xcrude =
          σ * (t * ((q - n : ℕ) : ℝ) + (t - αbad) * (r : ℝ)) := by
      dsimp [Xcrude]
      rw [hm_sub_q]
    rw [hX_eq, hXhigh_eq, hXcrude_eq]
    exact hsub
  have hAρ :
      A * ρ ^ r = (3 : ℝ) ^ (X / η) / Den := by
    simpa [A, ρ, X, row, offset] using
      rpow_three_row_parameter_div_eq
        (q := q) (r := r) (offset := offset)
        (row := row) (Den := Den) (η := η) hη_pos
  have hhigh_exp :
      Xhigh / τ =
        b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1) := by
    dsimp [Xhigh]
    field_simp [hτ_pos.ne']
  have hcrude_exp :
      Xcrude / σ =
        t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) := by
    dsimp [Xcrude]
    field_simp [hσ_pos.ne']
  have hpow :
      (A * ρ ^ r) ^ η ≤
        max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ) := by
    rw [hAρ]
    have hgeneric :=
      rpow_three_div_den_le_branch_max_of_exponent_le_max
        (X := X) (Xhigh := Xhigh) (Xcrude := Xcrude)
        (Dhigh := Dhigh) (Dcrude := Dcrude) (Den := Den)
        (η := η) (τ := τ) (σ := σ)
        hη_pos hτ_pos hσ_pos hDhigh_pos hDcrude_pos hDen
        (by simpa [Dhigh, τ, η] using hDen_high)
        (by simpa [Dcrude, η] using hDen_crude)
        hcollapse
    rw [hhigh_exp, hcrude_exp] at hgeneric
    simpa [highA, crudeA] using hgeneric
  exact hpow

/-- Convert the synchronized mixed-bottom soft fixed-pair estimate into the
weighted row estimate with the corrected finite exponent. -/
theorem shiftedHighBottomPairProbability_le_interpolatedWeightedRow_of_softMaximum
    {d : ℕ} [NeZero d] {σ Cfluct Ccrude Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (_hCentry : 0 < Centry) (ha : 0 < a)
    (hpair :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let tau : ℝ := min σ 2
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          max 1 pref *
            Real.exp
              (1 - max ((max 1 highA) ^ tau) ((max 1 crudeA) ^ σ))) :
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        t ≤ b →
        αbad < t →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        Dcrude ^ σ ≤ Den ^ η →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
  intro t αbad Den P hP hStruct hΓ hσ_eq hparams q r j
  dsimp only
  intro ht htb hαt hDen hDen_high hDen_crude
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let m : ℕ := q + r
  let n : ℕ := q - j.val
  by_cases hnm : n < m
  · let D : Finset (TriadicCube d) :=
      descendantsAtScale
        (originCube d (((N0 + m : ℕ) : ℤ)))
        (((N0 + n : ℕ) : ℤ))
    let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
    let highA : ℝ :=
      (3 : ℝ) ^
          (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
            (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
        Dhigh
    let crudeA : ℝ :=
      (3 : ℝ) ^
          (t * ((q - n : ℕ) : ℝ) +
            (t - αbad) * ((m - q : ℕ) : ℝ)) /
        Dcrude
    have hqm : q ≤ m := by
      dsimp [m]
      exact Nat.le_add_right q r
    have hx :=
      hpair (t := t) (αbad := αbad)
        hP hStruct hΓ hσ_eq hparams (q := q) (m := m) (n := n)
    dsimp only at hx
    have hfixed :
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          max 1 pref *
            Real.exp
              (1 - max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ)) := by
      simpa [K, N0, Hshift, D, S, b, L, τ, pref, highA, crudeA,
        Dhigh, Dcrude] using!
        hx hnm hqm ht hαt
    have hη_pos : 0 < η := by
      simpa [η] using
        finiteQuenchedTailExponent_pos
          (d := d) (σ := σ) (t := t) hσ_pos ht
    have hτ_pos : 0 < τ := by
      simpa [τ] using finiteQuenchedTailTau_pos hσ_pos
    have hb_pos : 0 < b := by
      dsimp [b]
      have hd : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      positivity
    have hK_pos : 0 < K := by
      simpa [K] using quenchedProbeEnvelopeConst_pos d
    have hDhigh_pos : 0 < Dhigh := by
      dsimp [Dhigh]
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos) hCfluct)
        (pow_pos hΓ.thetaHat_pos 2)
    have hDcrude_pos : 0 < Dcrude := by
      dsimp [Dcrude]
      exact mul_pos (mul_pos hK_pos hCcrude) (pow_pos hΓ.thetaHat_pos 2)
    have hoff_nonneg : 0 ≤ τ * b * (L + 1) :=
      mixed_bottom_offset_nonnegative ha hb_pos hτ_pos
    have hw_pos : 0 < w := by
      dsimp [w]
      exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
    have hw_one : 1 ≤ w := by
      have hn : 1 ≤ 3 ^ d :=
        Nat.succ_le_of_lt (pow_pos (by norm_num : (0 : ℕ) < 3) d)
      simpa [w] using (by exact_mod_cast hn : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ))
    have hDcard :
        (D.card : ℝ) ≤ w ^ q * w ^ r := by
      have hnm_le : n ≤ m := le_of_lt hnm
      simpa [D, w, m, n] using
        descendantsAtScale_bottom_row_card_le_weight
          (d := d) (N := N0) (q := q) (r := r) (j := j) hnm_le
    have hpref_bound : max 1 pref ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
      exact maximum_one_product_le_weighted_prefactor (by positivity) hw_one hDcard
    have hpow :
        (A * ρ ^ r) ^ η ≤
          max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ) := by
      exact mixedBottom_row_power_le_branch_maximum
        hσ_pos ht htb hαt (by dsimp [m]; omega)
        hη_pos hτ_pos hDhigh_pos hDcrude_pos hDen hDen_high hDen_crude hoff_nonneg
    have hCpref_nonneg : 0 ≤ max 1 (S.card : ℝ) := by
      exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (S.card : ℝ))
    have hrow :=
      le_weighted_row_of_le_soft_maxExponent
        (x := P.real (highBottomPairEvent Hshift K a t αbad q m n))
        (pref := pref) (highA := highA) (crudeA := crudeA)
        (τ := τ) (σ := σ) (A := A) (ρ := ρ) (η := η)
        (C := max 1 (S.card : ℝ)) (w := w)
        (q := q) (r := r)
        hfixed hpref_bound hCpref_nonneg hw_pos.le hpow
    change
      P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
        (Cpref * w ^ q) *
          (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))
    calc
      P.real (highBottomPairEvent Hshift K a t αbad q m n)
          ≤ (Real.exp 1 * max 1 (S.card : ℝ) * w ^ q) *
              (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := hrow
      _ = (Cpref * w ^ q) *
              (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
            dsimp [Cpref]
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, badPairEvent, hnm]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    positivity

/-- Sum synchronized mixed-bottom row estimates into the high-bottom component
bound, still without choosing new constants. -/
theorem shiftedHighBottomBadScaleProbability_le_interpolated_weighted_kernel_of_rowBound
    {d : ℕ} [NeZero d] {σ Cfluct Ccrude Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hrow :
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ →
        hΓ.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        t ≤ b →
        αbad < t →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        Dcrude ^ σ ≤ Den ^ η →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ →
        hΓ.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let τ : ℝ := finiteQuenchedTailTau σ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
        let A : ℝ :=
          (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
        let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        t ≤ b →
        αbad < t →
        0 < Den →
        Dhigh ^ τ ≤ Den ^ η →
        Dcrude ^ σ ≤ Den ^ η →
        1 ≤ A →
        P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * (Cpref * w ^ q) *
            (Real.exp (-(A ^ η)) *
              weightedGeometricExpKernelConst w (ρ ^ η)) := by
  intro t αbad Den P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht htb hαt hDen hDen_high hDen_crude hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let τ : ℝ := finiteQuenchedTailTau σ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hΓ.thetaHat ^ (2 : ℕ)
  let A : ℝ :=
    (3 : ℝ) ^ ((q : ℝ) - (τ * b * (L + 1)) / η) / Den
  let ρ : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have hη_pos : 0 < η := by
    simpa [η] using
      finiteQuenchedTailExponent_pos
        (d := d) (σ := σ) (t := t) hσ_pos ht
  have hτ_pos : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ_pos
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hρ_gt : 1 < ρ := by
    have hexp_pos : 0 < τ * (t - αbad) / η := by
      exact div_pos (mul_pos hτ_pos (sub_pos.mpr hαt)) hη_pos
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (τ * (t - αbad) / η) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hexp_pos
  have hC_nonneg : 0 ≤ Cpref * w ^ q := by
    dsimp [Cpref]
    positivity
  exact
    measureReal_highBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (A := A) (ρ := ρ) (η := η)
      (C := Cpref * w ^ q) (w := w)
      hC_nonneg hw_pos hA_one hρ_gt hη_pos
      (by
        intro r j
        simpa [K, N0, Hshift, S, b, L, τ, η, w, Dhigh, Dcrude,
          A, ρ, Cpref] using
          hrow (t := t) (αbad := αbad) (Den := Den)
            hP hStruct hΓ hσ_eq hparams
            (q := q) (r := r) (j := j)
            ht htb hαt hDen hDen_high hDen_crude)

end

end Section57
end Ch05
end Book
end HCPolySupport
