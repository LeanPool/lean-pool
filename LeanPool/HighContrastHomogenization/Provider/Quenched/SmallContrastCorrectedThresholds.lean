/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnInPolynomial
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEndpointDataMinimal
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42CanonicalMetric

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedThresholds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The threshold caps at the canonical metric

The burn-in exponent of `SmallContrastBurnInPolynomial`, at a grid metric
whose eccentricity is bounded by the reference aspect ratio: the adapter
factor gains exactly one aspect-ratio factor over the identity-metric
form, which the telescope base absorbs as one more power.  This is that
bridge.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The adapter factor at an eccentricity-bounded metric is the identity
form times the aspect ratio. -/
theorem bootstrapAdapterFactor_le_aspect_mul [Nonempty (Fin d)]
    {Cd g K : ℝ} {E : BlockMat d} {mAl : Mat d} {Pi : ℝ}
    (hecc : witnessEccentricity mAl ≤ Pi)
    (hfac0 : 0 ≤ (1 + K ^ 2) ^ g * euclideanReferenceRatio Cd g K E) :
    bootstrapAdapterFactor Cd g K E mAl ≤
      Pi * bootstrapAdapterFactor Cd g K E (1 : Mat d) := by
  rw [bootstrapAdapterFactor, bootstrapAdapterFactor,
    witnessEccentricity_one, one_mul]
  exact mul_le_mul_of_nonneg_right hecc hfac0

/-- **The burn-in exponent at an eccentricity-bounded metric.** -/
theorem exists_burnIn_exponent_canonical (d : ℕ) [Nonempty (Fin d)]
    (Cd g sigma CB : ℝ)
    (hCd : 0 ≤ Cd) (hg1 : g ≤ 1) (hzeta : 0 ≤ zetaG g)
    (hsigma : 0 < sigma) (hCB : 0 ≤ CB) :
    ∃ cburn : ℝ, 0 ≤ cburn ∧
      ∀ (E : BlockMat d) (K : ℝ) (mAl : Mat d),
        1 ≤ aspectRatio E → 1 ≤ K →
        0 ≤ kappaRef E → kappaRef E ≤ 1 + 6 * sigma →
        witnessEccentricity mAl ≤ aspectRatio E →
        0 ≤ (1 + K ^ 2) ^ g * euclideanReferenceRatio Cd g K E →
        ∀ sK gap : ℤ,
          (3 : ℝ) ^ sK ≤ (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * (3 * growthBar K) →
          (3 : ℝ) ^ gap ≤
            3 * max 1 (CB * bootstrapAdapterFactor Cd g K E mAl / sigma) →
          (3 : ℝ) ^ (sK + 1 + gap) ≤
            Real.rpow (2 + aspectRatio E * K) cburn := by
  obtain ⟨cR, hcR0, hcR⟩ :=
    exists_rpow_ge_uniform ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 3)
  obtain ⟨cQ, hcQ0, hcQ⟩ :=
    exists_rpow_ge_uniform (CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g)) / sigma)
  refine ⟨cR + cQ + 7, by linarith only [hcR0, hcQ0], ?_⟩
  intro E K mAl haspect hK hkap0 hkap hecc hfacE0 sK gap hsK hgap
  set base : ℝ := 2 + aspectRatio E * K with hbasedef
  have hKle : K ≤ aspectRatio E * K := by
    have := mul_le_mul_of_nonneg_right haspect
      (by linarith only [hK] : (0 : ℝ) ≤ K)
    linarith only [this]
  have hbase : (3 : ℝ) ≤ base := by
    rw [hbasedef]; linarith only [hK, hKle]
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hGbase : growthBar K ≤ base := by
    rw [hbasedef]
    exact growthBar_le_base (E := E) haspect (by linarith only [hK])
  have hG2 : (2 : ℝ) ≤ growthBar K := le_max_left 2 K
  have haspbase : aspectRatio E ≤ base := by
    rw [hbasedef]
    nlinarith only [haspect, hK]
  -- the source-scale factor
  have hR : (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 3 ≤ Real.rpow base cR :=
    hcR base hbase
  have hsK1 : (3 : ℝ) ^ sK ≤ Real.rpow base (cR + 1) := by
    have hstep : (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * (3 * growthBar K) ≤
        Real.rpow base cR * base := by
      have heq : (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * (3 * growthBar K) =
          (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 3 * growthBar K := by ring
      rw [heq]
      have ha : (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 3 * growthBar K ≤
          Real.rpow base cR * growthBar K :=
        mul_le_mul_of_nonneg_right hR (by linarith only [hG2])
      have hrpow0 : (0 : ℝ) ≤ Real.rpow base cR :=
        Real.rpow_nonneg hbase0.le _
      have hb : Real.rpow base cR * growthBar K ≤ Real.rpow base cR * base :=
        mul_le_mul_of_nonneg_left hGbase hrpow0
      linarith only [ha, hb]
    have hadd : Real.rpow base (cR + 1) = Real.rpow base cR * base := by
      change base ^ (cR + 1) = base ^ cR * base
      rw [Real.rpow_add hbase0, Real.rpow_one]
    rw [hadd]
    linarith only [hsK, hstep]
  -- the gap factor, with the aspect multiplier
  have hfac := bootstrapAdapterFactor_one_le (E := E) (K := K) hg1 hCd hzeta
    hsigma.le hkap0 hkap
  have hfacC : bootstrapAdapterFactor Cd g K E mAl ≤
      aspectRatio E * bootstrapAdapterFactor Cd g K E (1 : Mat d) :=
    bootstrapAdapterFactor_le_aspect_mul hecc hfacE0
  have hK1 : (1 : ℝ) ≤ 1 + K ^ 2 := by nlinarith only [sq_nonneg K]
  have hKsq : 1 + K ^ 2 ≤ base ^ (2 : ℕ) := by
    rw [hbasedef]
    nlinarith only [hK, hKle]
  have hbasepow0 : (0 : ℝ) ≤ base ^ (2 : ℕ) := by positivity
  have hQ0 : (0 : ℝ) ≤ (1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g)) := by
    have h1 : (0 : ℝ) ≤ 1 + 6 * sigma := by linarith only [hsigma]
    have h2 : (0 : ℝ) ≤ 3 * growthBar K := by linarith only [hG2]
    exact mul_nonneg h1 (mul_nonneg h2 (mul_nonneg hCd hzeta))
  have hfacle : bootstrapAdapterFactor Cd g K E (1 : Mat d) ≤
      base ^ (2 : ℕ) * ((1 + 6 * sigma) * (3 * base * (Cd * zetaG g))) := by
    refine le_trans hfac ?_
    have hb1 : (1 + K ^ 2) *
          ((1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g))) ≤
        base ^ (2 : ℕ) *
          ((1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g))) :=
      mul_le_mul_of_nonneg_right hKsq hQ0
    have hcdz : (0 : ℝ) ≤ Cd * zetaG g := mul_nonneg hCd hzeta
    have hs0 : (0 : ℝ) ≤ 1 + 6 * sigma := by linarith only [hsigma]
    have hb2 : (1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g)) ≤
        (1 + 6 * sigma) * (3 * base * (Cd * zetaG g)) := by
      refine mul_le_mul_of_nonneg_left ?_ hs0
      have h3 : 3 * growthBar K ≤ 3 * base := by linarith only [hGbase]
      exact mul_le_mul_of_nonneg_right h3 hcdz
    have hb3 : base ^ (2 : ℕ) *
          ((1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g))) ≤
        base ^ (2 : ℕ) * ((1 + 6 * sigma) * (3 * base * (Cd * zetaG g))) :=
      mul_le_mul_of_nonneg_left hb2 hbasepow0
    linarith only [hb1, hb3]
  have hQval : CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g)) / sigma ≤
      Real.rpow base cQ := hcQ base hbase
  have hquot : CB * bootstrapAdapterFactor Cd g K E mAl / sigma ≤
      Real.rpow base (4 + cQ) := by
    have hadfac0 : 0 ≤ bootstrapAdapterFactor Cd g K E (1 : Mat d) := by
      rw [bootstrapAdapterFactor, witnessEccentricity_one, one_mul]
      exact hfacE0
    have hnum : CB * bootstrapAdapterFactor Cd g K E mAl ≤
        CB * (aspectRatio E * (base ^ (2 : ℕ) *
          ((1 + 6 * sigma) * (3 * base * (Cd * zetaG g))))) := by
      refine mul_le_mul_of_nonneg_left (le_trans hfacC ?_) hCB
      refine mul_le_mul_of_nonneg_left hfacle ?_
      linarith only [haspect]
    have hnum2 : CB * (aspectRatio E * (base ^ (2 : ℕ) *
          ((1 + 6 * sigma) * (3 * base * (Cd * zetaG g))))) ≤
        CB * (base * (base ^ (2 : ℕ) *
          ((1 + 6 * sigma) * (3 * base * (Cd * zetaG g))))) := by
      refine mul_le_mul_of_nonneg_left ?_ hCB
      refine mul_le_mul_of_nonneg_right haspbase ?_
      exact mul_nonneg hbasepow0 (le_trans hQ0 (by
        have h3 : 3 * growthBar K ≤ 3 * base := by linarith only [hGbase]
        have hcdz : (0 : ℝ) ≤ Cd * zetaG g := mul_nonneg hCd hzeta
        have hs0 : (0 : ℝ) ≤ 1 + 6 * sigma := by linarith only [hsigma]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h3 hcdz) hs0))
    have hid : CB * (base * (base ^ (2 : ℕ) *
          ((1 + 6 * sigma) * (3 * base * (Cd * zetaG g))))) =
        (CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g))) *
          (base ^ (2 : ℕ) * base * base) := by ring
    have hpow4 : base ^ (2 : ℕ) * base * base = Real.rpow base 4 := by
      change base ^ (2 : ℕ) * base * base = base ^ (4 : ℝ)
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hdiv : CB * bootstrapAdapterFactor Cd g K E mAl / sigma ≤
        (CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g)) / sigma) *
          Real.rpow base 4 := by
      rw [div_le_iff₀ hsigma]
      have hstep : CB * bootstrapAdapterFactor Cd g K E mAl ≤
          (CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g))) *
            Real.rpow base 4 := by
        rw [← hpow4, ← hid]
        exact le_trans hnum hnum2
      have hval : (CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g)) / sigma) *
            Real.rpow base 4 * sigma =
          (CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g))) *
            Real.rpow base 4 := by
        field_simp
      linarith only [hstep, hval.le, hval.ge]
    have hrp0 : (0 : ℝ) ≤ Real.rpow base 4 := Real.rpow_nonneg hbase0.le _
    have hmul : (CB * (1 + 6 * sigma) * (3 * (Cd * zetaG g)) / sigma) *
          Real.rpow base 4 ≤ Real.rpow base cQ * Real.rpow base 4 :=
      mul_le_mul_of_nonneg_right hQval hrp0
    have hadd : Real.rpow base (4 + cQ) =
        Real.rpow base cQ * Real.rpow base 4 := by
      change base ^ (4 + cQ) = base ^ cQ * base ^ (4 : ℝ)
      rw [Real.rpow_add hbase0]
      ring
    rw [hadd]
    linarith only [hdiv, hmul]
  have hgap1 : (3 : ℝ) ^ gap ≤ Real.rpow base (4 + cQ + 1) :=
    le_trans hgap
      (three_mul_max_one_le_rpow hbase (by linarith only [hcQ0]) hquot)
  -- combine
  have hcomb := three_zpow_burnIn_le_rpow (sK := sK) (gap := gap) hbase hsK1
    hgap1
  have hexp : cR + 1 + (4 + cQ + 1) + 1 = cR + cQ + 7 := by ring
  rwa [hexp] at hcomb

end

end HCPolySupport.HighContrast.Quenched
