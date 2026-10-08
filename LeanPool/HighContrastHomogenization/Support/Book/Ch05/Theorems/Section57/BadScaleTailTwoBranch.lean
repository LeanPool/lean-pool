/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.BadScaleTailExponent
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.BadScaleComponentRows

/-!
# Coarse-graining support: Support.Book.Ch05.Theorems.Section57.BadScaleTailTwoBranch

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
# Two-branch bad-scale tails

This file starts the theorem-facing bad-scale tail assembly.  The first step is
still fixed-pair: in the mixed bottom range, use the localized and crude
mechanisms separately for the same selected scale and then keep the better of
the two tails by taking the maximum of their stretched-exponential exponents.
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

/-- If a quantity is bounded by `max y z`, then subtracting a nonnegative
offset only from the left branch still controls the offset quantity. -/
theorem sub_nonneg_le_max_sub_left_of_le_max
    {x y z c : ℝ} (hc : 0 ≤ c) (h : x ≤ max y z) :
    x - c ≤ max (y - c) z := by
  by_cases hyz : y ≤ z
  · have hxz : x ≤ z := by simpa [max_eq_right hyz] using h
    exact le_max_of_le_right (by linarith)
  · have hzy : z ≤ y := le_of_not_ge hyz
    have hxy : x ≤ y := by simpa [max_eq_left hzy] using h
    exact le_max_of_le_left (by linarith)

/-- Multiplicative row parameters written as a single triadic exponent. -/
theorem rpow_three_row_parameter_div_eq
    {q r : ℕ} {offset row Den η : ℝ} (hη : 0 < η) :
    ((3 : ℝ) ^ ((q : ℝ) - offset / η) / Den) *
        (((3 : ℝ) ^ (row / η)) ^ r) =
      (3 : ℝ) ^ ((η * (q : ℝ) - offset + row * (r : ℝ)) / η) / Den := by
  have hpow :
      (((3 : ℝ) ^ (row / η)) ^ r) =
        (3 : ℝ) ^ ((row / η) * (r : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hpow]
  calc
    ((3 : ℝ) ^ ((q : ℝ) - offset / η) / Den) *
        (3 : ℝ) ^ ((row / η) * (r : ℝ))
        =
      ((3 : ℝ) ^ ((q : ℝ) - offset / η) *
        (3 : ℝ) ^ ((row / η) * (r : ℝ))) / Den := by
          ring
    _ =
      (3 : ℝ) ^ (((q : ℝ) - offset / η) + (row / η) * (r : ℝ)) /
          Den := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ =
      (3 : ℝ) ^ ((η * (q : ℝ) - offset + row * (r : ℝ)) / η) / Den := by
        congr 2
        field_simp [hη.ne']

/-- Deterministic comparison turning an exponent-level maximum into a
tail-parameter maximum, with explicit denominator domination. -/
theorem rpow_three_div_den_le_branch_max_of_exponent_le_max
    {X Xhigh Xcrude Dhigh Dcrude Den η τ σ : ℝ}
    (hη : 0 < η) (hτ : 0 < τ) (hσ : 0 < σ)
    (hDhigh : 0 < Dhigh) (hDcrude : 0 < Dcrude) (hDen : 0 < Den)
    (hDen_high : Dhigh ^ τ ≤ Den ^ η)
    (hDen_crude : Dcrude ^ σ ≤ Den ^ η)
    (hX : X ≤ max Xhigh Xcrude) :
    ((3 : ℝ) ^ (X / η) / Den) ^ η ≤
      max
        ((max 1 ((3 : ℝ) ^ (Xhigh / τ) / Dhigh)) ^ τ)
        ((max 1 ((3 : ℝ) ^ (Xcrude / σ) / Dcrude)) ^ σ) := by
  have hthree_pos : 0 < (3 : ℝ) := by norm_num
  have hthree_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  have hDenη_pos : 0 < Den ^ η := Real.rpow_pos_of_pos hDen η
  have hDhighτ_pos : 0 < Dhigh ^ τ := Real.rpow_pos_of_pos hDhigh τ
  have hDcrudeσ_pos : 0 < Dcrude ^ σ := Real.rpow_pos_of_pos hDcrude σ
  have hleft_eq :
      ((3 : ℝ) ^ (X / η) / Den) ^ η =
        (3 : ℝ) ^ X / Den ^ η := by
    rw [Real.div_rpow (Real.rpow_nonneg hthree_nonneg _) hDen.le η]
    congr 1
    rw [← Real.rpow_mul hthree_nonneg]
    congr 1
    field_simp [hη.ne']
  have hhigh_eq :
      ((3 : ℝ) ^ (Xhigh / τ) / Dhigh) ^ τ =
        (3 : ℝ) ^ Xhigh / Dhigh ^ τ := by
    rw [Real.div_rpow (Real.rpow_nonneg hthree_nonneg _) hDhigh.le τ]
    congr 1
    rw [← Real.rpow_mul hthree_nonneg]
    congr 1
    field_simp [hτ.ne']
  have hcrude_eq :
      ((3 : ℝ) ^ (Xcrude / σ) / Dcrude) ^ σ =
        (3 : ℝ) ^ Xcrude / Dcrude ^ σ := by
    rw [Real.div_rpow (Real.rpow_nonneg hthree_nonneg _) hDcrude.le σ]
    congr 1
    rw [← Real.rpow_mul hthree_nonneg]
    congr 1
    field_simp [hσ.ne']
  have hhigh_base_nonneg :
      0 ≤ (3 : ℝ) ^ (Xhigh / τ) / Dhigh := by
    exact div_nonneg (Real.rpow_pos_of_pos hthree_pos _).le hDhigh.le
  have hcrude_base_nonneg :
      0 ≤ (3 : ℝ) ^ (Xcrude / σ) / Dcrude := by
    exact div_nonneg (Real.rpow_pos_of_pos hthree_pos _).le hDcrude.le
  have hhigh_power_le :
      ((3 : ℝ) ^ (Xhigh / τ) / Dhigh) ^ τ ≤
        (max 1 ((3 : ℝ) ^ (Xhigh / τ) / Dhigh)) ^ τ :=
    Real.rpow_le_rpow hhigh_base_nonneg
      (le_max_right 1 ((3 : ℝ) ^ (Xhigh / τ) / Dhigh)) hτ.le
  have hcrude_power_le :
      ((3 : ℝ) ^ (Xcrude / σ) / Dcrude) ^ σ ≤
        (max 1 ((3 : ℝ) ^ (Xcrude / σ) / Dcrude)) ^ σ :=
    Real.rpow_le_rpow hcrude_base_nonneg
      (le_max_right 1 ((3 : ℝ) ^ (Xcrude / σ) / Dcrude)) hσ.le
  by_cases hbranch : Xhigh ≤ Xcrude
  · have hXcrude : X ≤ Xcrude := by
      simpa [max_eq_right hbranch] using hX
    have hpow :
        (3 : ℝ) ^ X ≤ (3 : ℝ) ^ Xcrude :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hXcrude
    have hraw :
        (3 : ℝ) ^ X / Den ^ η ≤
          (3 : ℝ) ^ Xcrude / Dcrude ^ σ := by
      calc
        (3 : ℝ) ^ X / Den ^ η
            ≤ (3 : ℝ) ^ Xcrude / Den ^ η :=
              div_le_div_of_nonneg_right hpow hDenη_pos.le
        _ ≤ (3 : ℝ) ^ Xcrude / Dcrude ^ σ :=
              div_le_div_of_nonneg_left
                (Real.rpow_pos_of_pos hthree_pos Xcrude).le
                hDcrudeσ_pos hDen_crude
    rw [hleft_eq]
    exact le_max_of_le_right (hraw.trans (by simpa [hcrude_eq] using hcrude_power_le))
  · have hcrude_le_high : Xcrude ≤ Xhigh := le_of_not_ge hbranch
    have hXhigh : X ≤ Xhigh := by
      simpa [max_eq_left hcrude_le_high] using hX
    have hpow :
        (3 : ℝ) ^ X ≤ (3 : ℝ) ^ Xhigh :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hXhigh
    have hraw :
        (3 : ℝ) ^ X / Den ^ η ≤
          (3 : ℝ) ^ Xhigh / Dhigh ^ τ := by
      calc
        (3 : ℝ) ^ X / Den ^ η
            ≤ (3 : ℝ) ^ Xhigh / Den ^ η :=
              div_le_div_of_nonneg_right hpow hDenη_pos.le
        _ ≤ (3 : ℝ) ^ Xhigh / Dhigh ^ τ :=
              div_le_div_of_nonneg_left
                (Real.rpow_pos_of_pos hthree_pos Xhigh).le
                hDhighτ_pos hDen_high
    rw [hleft_eq]
    exact le_max_of_le_left (hraw.trans (by simpa [hhigh_eq] using hhigh_power_le))

/-- Convert a max-exponent soft fixed-pair estimate into the weighted row
shape used by the bad-scale summation lemmas. -/
theorem le_weighted_row_of_le_soft_maxExponent
    {x pref highA crudeA τ σ A ρ η C w : ℝ} {q r : ℕ}
    (hx :
      x ≤ max 1 pref *
        Real.exp
          (1 - max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ)))
    (hpref : max 1 pref ≤ C * w ^ q * w ^ r)
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hpow :
      (A * ρ ^ r) ^ η ≤
        max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ)) :
    x ≤
      (Real.exp 1 * C * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
  have hexp :
      Real.exp
          (1 - max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ)) ≤
        Real.exp (1 - (A * ρ ^ r) ^ η) :=
    Real.exp_le_exp.mpr (by linarith)
  have hrow_nonneg : 0 ≤ C * w ^ q * w ^ r := by
    positivity
  have hexp_split :
      Real.exp (1 - (A * ρ ^ r) ^ η) =
        Real.exp 1 * Real.exp (-((A * ρ ^ r) ^ η)) := by
    rw [← Real.exp_add]
    congr 1
  calc
    x ≤ max 1 pref *
        Real.exp
          (1 - max ((max 1 highA) ^ τ) ((max 1 crudeA) ^ σ)) := hx
    _ ≤ (C * w ^ q * w ^ r) *
        Real.exp (1 - (A * ρ ^ r) ^ η) :=
          mul_le_mul hpref hexp (Real.exp_pos _).le hrow_nonneg
    _ =
        (Real.exp 1 * C * w ^ q) *
          (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
          rw [hexp_split]
          ring

/-- Exact fixed-pair mixed-bottom estimate with the better of the localized
and crude mechanisms retained as a maximum of exponents. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_max_mixed
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
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
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hhighRaw⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  obtain ⟨Ccrude, hCcrude, hcrudeRaw⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
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
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      have hHighLam : highA ≤ highLam := by
        simpa [K, x, ell, b, L, highScale, T, highLam, highA] using
          highBottom_tailParameter_interpolation_lower_bound
            (d := d) (K := K) (Cfluct := Cfluct)
            (θ := hΓ.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (m := m) (n := n)
            hK_pos hCfluct hΓ.thetaHat_pos ha ht hαt hell hnq hqm
      have hCrudeLam : crudeA ≤ crudeLam := by
        simpa [K, x, crudeScale, T, crudeLam, crudeA] using
          crudeBottom_tailParameter_discount_lower_bound
            (K := K) (C := Ccrude) (θ := hΓ.thetaHat)
            (t := t) (α := αbad) (q := q) (m := m) (n := n)
            hK_pos hCcrude hΓ.thetaHat_pos hnq hqm
      have htau_pos : 0 < tau := by
        dsimp [tau]
        exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
      have hhighSoft :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            softPairTail pref highA tau := by
        refine measureReal_le_softPairTail_of_threshold_bound
          (F := badPairEvent Hshift t αbad q m n)
          (lam := highLam) (by intro ω hω; exact hω.2.2)
          (by dsimp [pref]; positivity) htau_pos hHighLam ?_
        intro hlam
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
      have hcrudeSoft :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            softPairTail pref crudeA σ := by
        refine measureReal_le_softPairTail_of_threshold_bound
          (F := badPairEvent Hshift t αbad q m n)
          (lam := crudeLam) (by intro ω hω; exact hω.2.2)
          (by dsimp [pref]; positivity) hσ_pos hCrudeLam ?_
        intro hlam
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
      exact
        le_maxExponent_softPairTail_of_le_both
          (x := P.real (highBottomPairEvent Hshift K a t αbad q m n))
          (pref := pref) (lam₁ := highA) (lam₂ := crudeA)
          (η₁ := tau) (η₂ := σ) hhighSoft hcrudeSoft
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
    exact mul_div_cancel_left₀ _ (show τ ≠ 0 from hτ_pos.ne')
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
        (by simpa only [τ, η] using hDen_high)
        (by simpa only [η] using hDen_crude)
        hcollapse
    rw [hhigh_exp, hcrude_exp] at hgeneric
    simpa [highA, crudeA] using hgeneric
  exact hpow

/-- Concrete mixed-bottom fixed-pair estimate in the weighted row shape, with
the corrected finite bad-scale exponent.  The only remaining denominator
conditions are explicit algebraic domination conditions for the chosen
normalizing denominator `Den`. -/
theorem measureReal_shiftedHighBottomPairProbability_le_interpolated_weighted_row
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
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
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hpair⟩ :=
    measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_max_mixed
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
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
    have hlog3_pos : 0 < Real.log (3 : ℝ) :=
      Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have hL_nonneg : 0 ≤ L := by
      have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
      have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
        Real.log_nonneg (le_max_right (2 * K) 1)
      dsimp [L]
      positivity
    have hoff_nonneg : 0 ≤ τ * b * (L + 1) := by
      positivity
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

/-- Summed high-bottom component estimate with the corrected finite
interpolated exponent, conditional only on the explicit denominator choice and
the deterministic lower cutoff `1 <= A`. -/
theorem shiftedHighBottomBadScaleProbability_le_interpolated_weighted_kernel
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
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
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hrow⟩ :=
    measureReal_shiftedHighBottomPairProbability_le_interpolated_weighted_row
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
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
