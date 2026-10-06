/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapTransferInputs

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBootstrapFiniteBandTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrected-tilt transfer across its finite adapter band

The raw reverse-adapter construction has a unit-size premise.  Its law factor is
paid by the endpoint's linear level-schedule start, so that premise is available once
the corrected scale gap reaches the corresponding finite band.  Before that
band, monotonicity and the entry floor imply the endpoint transfer directly:
the endpoint prefactor times the triadic decay is at least one there.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A reverse-adapter factor paid at generation `nF` is still paid at every
later generation `R`. -/
theorem adapter_factor_le_at_finite_band {rate adapter : ℝ} {nF R : ℕ}
    (hrate : 0 ≤ rate) (hnF : nF ≤ R)
    (hadapter : adapter ≤ Real.rpow (3 : ℝ) (rate * (nF : ℝ))) :
    adapter ≤ Real.rpow (3 : ℝ) (rate * (R : ℝ)) := by
  have hcast : (nF : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hnF
  have hexp : rate * (nF : ℝ) ≤ rate * (R : ℝ) :=
    mul_le_mul_of_nonneg_left hcast hrate
  exact hadapter.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

/-- Once the scale gap reaches the delay exponent, the raw construction's absorbed
size coefficient is at most one. -/
theorem finite_band_adapter_size_le_one {rate : ℝ} {R gap : ℕ}
    (hlate : rate * (R : ℝ) ≤ (gap : ℝ)) :
    Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
        Real.rpow (3 : ℝ) (-(gap : ℝ)) ≤ 1 := by
  calc
    Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
          Real.rpow (3 : ℝ) (-(gap : ℝ)) =
        Real.rpow (3 : ℝ) (rate * (R : ℝ) + -(gap : ℝ)) :=
      (Real.rpow_add (x := (3 : ℝ)) (by norm_num)
        (rate * (R : ℝ)) (-(gap : ℝ))).symm
    _ ≤ Real.rpow (3 : ℝ) 0 :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith only [hlate])
    _ = 1 := by norm_num

/-- Before the adapter delay, the endpoint coefficient cancels the triadic
decay and leaves at least the a-priori unit floor. -/
theorem one_le_finite_band_transfer_decay {rate floor0 : ℝ} {R gap : ℕ}
    (hfloor0 : 0 ≤ floor0)
    (hearly : (gap : ℝ) < rate * (R : ℝ)) :
    1 ≤ (1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
        Real.rpow (3 : ℝ) (-(gap : ℝ)) := by
  have hpow : 1 ≤ Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
      Real.rpow (3 : ℝ) (-(gap : ℝ)) := by
    calc
      1 = Real.rpow (3 : ℝ) 0 := by norm_num
      _ ≤ Real.rpow (3 : ℝ) (rate * (R : ℝ) + -(gap : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by linarith only [hearly])
      _ = Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
          Real.rpow (3 : ℝ) (-(gap : ℝ)) :=
        Real.rpow_add (x := (3 : ℝ)) (by norm_num)
          (rate * (R : ℝ)) (-(gap : ℝ))
  have hfloor1 : (1 : ℝ) ≤ 1 + floor0 := by
    linarith only [hfloor0]
  calc
    1 = 1 * 1 := by ring
    _ ≤ (1 + floor0) *
        (Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
          Real.rpow (3 : ℝ) (-(gap : ℝ))) :=
      mul_le_mul hfloor1 hpow (by norm_num) (by linarith only [hfloor0])
    _ = (1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
        Real.rpow (3 : ℝ) (-(gap : ℝ)) := by ring

/-- The endpoint coefficient is at least one already at the boundary scale. -/
theorem one_le_finite_band_transfer_prefactor {rate floor0 : ℝ} {R : ℕ}
    (hrate : 0 ≤ rate) (hfloor0 : 0 ≤ floor0) :
    1 ≤ (9 / 2 : ℝ) *
      ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ))) := by
  have hexp : 0 ≤ rate * (R : ℝ) :=
    mul_nonneg hrate (Nat.cast_nonneg R)
  have hpow : 1 ≤ Real.rpow (3 : ℝ) (rate * (R : ℝ)) := by
    calc
      1 = Real.rpow (3 : ℝ) 0 := by norm_num
      _ ≤ Real.rpow (3 : ℝ) (rate * (R : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hfloor1 : (1 : ℝ) ≤ 1 + floor0 := by
    linarith only [hfloor0]
  have hcore : 1 ≤
      (1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ)) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ)) :=
        mul_le_mul hfloor1 hpow (by norm_num) (by linarith only [hfloor0])
  calc
    1 = 1 * 1 := by ring
    _ ≤ (9 / 2 : ℝ) *
        ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ))) :=
      mul_le_mul (by norm_num) hcore (by norm_num) (by norm_num)

/-- **The corrected outer transfer with a finite adapter band.**  Entry
smallness handles the boundary, the a-priori floor handles the finite band,
and the raw corrected-tilt construction handles every later generation. -/
theorem outer_transfer_of_corrected_tilt_inputs_of_finite_band [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k)
    {n₀ nF R : ℕ} {cStar rate floor0 adapter : ℝ}
    (hentry : annealedContrast P 0 - 1 ≤ cStar)
    (hcStar1 : cStar ≤ 1)
    (hrate : 0 ≤ rate) (hfloor0 : 0 ≤ floor0)
    (hnF : nF ≤ R)
    (hadapter : adapter ≤ Real.rpow (3 : ℝ) (rate * (nF : ℝ)))
    (hpack : ∀ m : ℕ, 2 * n₀ < m → ∀ A : ℝ,
      adapter ≤ A →
      A * Real.rpow (3 : ℝ)
          (-((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ)) ≤ 1 →
      ∃ c : ℝ, 0 ≤ c ∧
        BlockMatLoewnerLE
          (blockSub (annealedBlock P (centeredCube d (m : ℤ)))
            (adaptedMean P q (Prop42Scalar.correctedTiltScale n₀ m : ℤ)))
          (blockScale c E) ∧
        c * blockSize E
            (adaptedMean P q
              (Prop42Scalar.correctedTiltScale n₀ m : ℤ)) ≤ 1 ∧
        (9 / 2 : ℝ) * (c * blockSize E
            (adaptedMean P q
              (Prop42Scalar.correctedTiltScale n₀ m : ℤ))) ≤
          (9 / 2 : ℝ) * A * Real.rpow (3 : ℝ)
            (-((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ)))
    (hx1 : ∀ m : ℕ, 2 * n₀ < m →
      (d : ℝ) * (adaptedHattedContrast P q
        (Prop42Scalar.correctedTiltScale n₀ m : ℤ) - 1) ≤ 1) :
    ∀ m : ℕ, 2 * n₀ ≤ m →
      annealedContrast P (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast P q
            (Prop42Scalar.correctedTiltScale n₀ m : ℤ) - 1)) +
          (9 / 2 : ℝ) *
            ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ))) *
            Real.rpow (3 : ℝ)
              (-((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ)) := by
  classical
  have hcStarA : cStar ≤ (9 / 2 : ℝ) *
      ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ))) :=
    hcStar1.trans (one_le_finite_band_transfer_prefactor hrate hfloor0)
  have hadapterR : adapter ≤
      Real.rpow (3 : ℝ) (rate * (R : ℝ)) :=
    adapter_factor_le_at_finite_band hrate hnF hadapter
  intro m hm
  rcases eq_or_lt_of_le hm with hEq | hLt
  · subst hEq
    exact corrected_tilt_base_transfer hstat hdag hq
      (hfin (Prop42Scalar.correctedTiltScale n₀ (2 * n₀) : ℤ)) hentry hcStarA
  · by_cases hlate : rate * (R : ℝ) ≤
        ((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ)
    · have hcap := finite_band_adapter_size_le_one hlate
      obtain ⟨c, hc0, hsub, heta1, herror⟩ := hpack m hLt
        (Real.rpow (3 : ℝ) (rate * (R : ℝ))) hadapterR hcap
      have hadd := blockContrast_sub_one_le_tilt_sum_of_adapter
        (isSymmetricBlockMat_annealedBlock P (centeredCube d (m : ℤ)))
        (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag (m : ℤ))
        hdag.refBlock_isSymm hdag.refBlock_posDef hq
        (hfin (Prop42Scalar.correctedTiltScale n₀ m : ℤ)) hc0 hsub heta1
        (hx1 m hLt)
      have hpow0 : 0 ≤ Real.rpow (3 : ℝ) (rate * (R : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hfloorFactor : Real.rpow (3 : ℝ) (rate * (R : ℝ)) ≤
          (1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ)) := by
        calc
          Real.rpow (3 : ℝ) (rate * (R : ℝ)) =
              1 * Real.rpow (3 : ℝ) (rate * (R : ℝ)) := by ring
          _ ≤ (1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith only [hfloor0]) hpow0
      have hcoefficient : (9 / 2 : ℝ) *
            Real.rpow (3 : ℝ) (rate * (R : ℝ)) ≤
          (9 / 2 : ℝ) *
            ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ))) :=
        mul_le_mul_of_nonneg_left hfloorFactor (by norm_num)
      have hdecay0 : 0 ≤ Real.rpow (3 : ℝ)
          (-((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have herror' := herror.trans
        (mul_le_mul_of_nonneg_right hcoefficient hdecay0)
      rw [annealedContrast]
      linarith only [hadd, herror']
    · have hearly :
          ((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ) <
            rate * (R : ℝ) := lt_of_not_ge hlate
      have hband := one_le_finite_band_transfer_decay hfloor0 hearly
      have hmono := annealedContrast_antitone hstat hdag (Nat.zero_le m)
      change annealedContrast P (m : ℤ) ≤ annealedContrast P 0 at hmono
      have hcontrast : annealedContrast P (m : ℤ) - 1 ≤ cStar := by
        linarith only [hmono, hentry]
      have hhat1 := one_le_adaptedHattedContrast_of_rounded hq
        (hfin (Prop42Scalar.correctedTiltScale n₀ m : ℤ))
      have hhatted0 : 0 ≤ (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast P q
            (Prop42Scalar.correctedTiltScale n₀ m : ℤ) - 1)) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hhat1))
      have herror1 : 1 ≤ (9 / 2 : ℝ) *
          ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ))) *
          Real.rpow (3 : ℝ)
            (-((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ)) := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ (9 / 2 : ℝ) *
              ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ)) *
                Real.rpow (3 : ℝ)
                  (-((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ))) :=
            mul_le_mul (by norm_num) hband (by norm_num) (by norm_num)
          _ = (9 / 2 : ℝ) *
              ((1 + floor0) * Real.rpow (3 : ℝ) (rate * (R : ℝ))) *
              Real.rpow (3 : ℝ)
                (-((m - Prop42Scalar.correctedTiltScale n₀ m : ℕ) : ℝ)) := by
            ring
      linarith only [hcontrast, hcStar1, herror1, hhatted0]

end

end HCPolySupport.HighContrast.Quenched
