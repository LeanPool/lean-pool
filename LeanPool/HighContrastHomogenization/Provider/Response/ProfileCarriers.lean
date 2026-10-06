/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormCarriers
public import LeanPool.HighContrastHomogenization.Setup.SelectionObjects

/-!
# High-contrast homogenization: Provider.Response.ProfileCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Terminal profile carriers

This file names the centered, below-start, and complete terminal maxima from
`e.scale.selection.fluctuation.history` and from the below-start source maximum
at the response scale.  It also records the finite window coefficients, bad-event
majorant, and response-energy load used in the passage from the terminal profiles
to the response bounds in `p.response.transfer`.

The two suprema and their moments take values in `ℝ≥0∞`, so divergence is
represented by the top element.  The window coefficients remain finite sums;
no sign is assumed for `1 / 2 - rhoMax`.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Centered and below-start maxima -/

/-- The centered terminal maximum `Z_t`. -/
@[expose]
def profileCenteredMaximum (P : Measure (CoeffSpace d)) (rhoMax : ℝ)
    (q : Mat d) (jStar t : ℤ) (a : CoeffSpace d) : ℝ≥0∞ :=
  ⨆ (k : ℤ) (_ : jStar ≤ k) (_ : k ≤ t) (w : Fin d → ℤ)
      (_ : adaptedCellCenter q k w ∈ adaptedCell q t),
    ENNReal.ofReal
      ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
        blockSize
          (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
          (adaptedMean P q t))

/-- The defining equation for `Z_t`. -/
theorem profileCenteredMaximum_eq (P : Measure (CoeffSpace d))
    (rhoMax : ℝ) (q : Mat d) (jStar t : ℤ) (a : CoeffSpace d) :
    profileCenteredMaximum P rhoMax q jStar t a =
      ⨆ (k : ℤ) (_ : jStar ≤ k) (_ : k ≤ t) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q k w ∈ adaptedCell q t),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
            blockSize
              (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
              (adaptedMean P q t)) := rfl

/-- The exact below-start maximum `B_src(t)`. -/
@[expose]
def profileSourceMaximum (rhoMax : ℝ) (q : Mat d) (jStar t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) : ℝ≥0∞ :=
  belowStartSup rhoMax q jStar t (fun k ↦ containedCenters q k t) F a

/-- The defining equation for `B_src(t)`. -/
theorem profileSourceMaximum_eq (rhoMax : ℝ) (q : Mat d)
    (jStar t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    profileSourceMaximum rhoMax q jStar t F a =
      belowStartSup rhoMax q jStar t (fun k ↦ containedCenters q k t) F a := rfl

/-- The source moment `b_Q(t)`. -/
@[expose]
def profileSourceMoment (P : Measure (CoeffSpace d)) (Q rhoMax : ℝ)
    (q : Mat d) (jStar t : ℤ) (F : BlockMat d) : ℝ≥0∞ :=
  eLpNorm (profileSourceMaximum rhoMax q jStar t F) (ENNReal.ofReal Q) P

/-- The complete terminal maximum `W_t = Z_t + B_src(t)`. -/
@[expose]
def profileTotalMaximum (P : Measure (CoeffSpace d)) (rhoMax : ℝ)
    (q : Mat d) (jStar t : ℤ) (F : BlockMat d) (a : CoeffSpace d) : ℝ≥0∞ :=
  profileCenteredMaximum P rhoMax q jStar t a +
    profileSourceMaximum rhoMax q jStar t F a

/-- The defining equation for `W_t`. -/
theorem profileTotalMaximum_eq (P : Measure (CoeffSpace d))
    (rhoMax : ℝ) (q : Mat d) (jStar t : ℤ) (F : BlockMat d)
    (a : CoeffSpace d) :
    profileTotalMaximum P rhoMax q jStar t F a =
      profileCenteredMaximum P rhoMax q jStar t a +
        profileSourceMaximum rhoMax q jStar t F a := rfl

/-- The complete terminal history `ᵍ_t^tot = E[W_t^Q]`. -/
@[expose]
def profileTotalHistory (P : Measure (CoeffSpace d)) (Q rhoMax : ℝ)
    (q : Mat d) (jStar t : ℤ) (F : BlockMat d) : ℝ≥0∞ :=
  ∫⁻ a, profileTotalMaximum P rhoMax q jStar t F a ^ Q ∂P

/-! ## Scalar coefficients -/

/-- The two-branch correlated bad-event majorant `𝔅_Q(h,β)`. -/
@[expose]
def profileBadMajorant (Q h beta : ℝ) : ℝ :=
  if beta < 1 then
    (h ^ Q⁻¹ + beta) * (1 - beta) ^ (1 - Q / 2) *
      h ^ (1 / 2 - Q⁻¹)
  else
    h ^ Q⁻¹ + beta

/-- The defining equation for the small-drift branch of `𝔅_Q`. -/
theorem profileBadMajorant_of_lt_one {Q h beta : ℝ} (hbeta : beta < 1) :
    profileBadMajorant Q h beta =
      (h ^ Q⁻¹ + beta) * (1 - beta) ^ (1 - Q / 2) *
        h ^ (1 / 2 - Q⁻¹) := by
  simp only [profileBadMajorant, ite_eq_left hbeta]

/-- The defining equation for the large-drift branch of `𝔅_Q`. -/
theorem profileBadMajorant_of_one_le {Q h beta : ℝ} (hbeta : 1 ≤ beta) :
    profileBadMajorant Q h beta = h ^ Q⁻¹ + beta := by
  simp only [profileBadMajorant, ite_eq_right (not_lt.mpr hbeta)]

/-- **The two-branch bad-event majorant at a released split level.**  The
fixed-level `profileBadMajorant` is this at `lev = 1`: the guard `beta < 1`
becomes `beta < lev`, and the drift denominator `1 - beta` becomes
`lev - beta`. -/
@[expose]
def profileBadMajorantAt (Q h beta lev : ℝ) : ℝ :=
  if beta < lev then
    (h ^ Q⁻¹ + beta) * (lev - beta) ^ (1 - Q / 2) * h ^ (1 / 2 - Q⁻¹)
  else
    h ^ Q⁻¹ + beta

/-- The small-drift branch. -/
theorem profileBadMajorantAt_of_lt {Q h beta lev : ℝ} (hbeta : beta < lev) :
    profileBadMajorantAt Q h beta lev =
      (h ^ Q⁻¹ + beta) * (lev - beta) ^ (1 - Q / 2) * h ^ (1 / 2 - Q⁻¹) := by
  simp only [profileBadMajorantAt, ite_eq_left hbeta]

/-- The large-drift branch. -/
theorem profileBadMajorantAt_of_ge {Q h beta lev : ℝ} (hbeta : lev ≤ beta) :
    profileBadMajorantAt Q h beta lev = h ^ Q⁻¹ + beta := by
  simp only [profileBadMajorantAt, ite_eq_right (not_lt.mpr hbeta)]

theorem profileBadMajorantAt_nonneg {Q h beta lev : ℝ} (hh : 0 ≤ h)
    (hbeta : 0 ≤ beta) : 0 ≤ profileBadMajorantAt Q h beta lev := by
  by_cases hlt : beta < lev
  · rw [profileBadMajorantAt_of_lt hlt]
    exact mul_nonneg
      (mul_nonneg (add_nonneg (Real.rpow_nonneg hh _) hbeta)
        (Real.rpow_nonneg (by linarith only [hlt]) _))
      (Real.rpow_nonneg hh _)
  · rw [profileBadMajorantAt_of_ge (not_lt.mp hlt)]
    exact add_nonneg (Real.rpow_nonneg hh _) hbeta

/-- The finite centered-window coefficient `S_cen`. -/
@[expose]
def centeredWindowCoefficient (H : ℕ) (rhoMax : ℝ) : ℝ :=
  2 * ∑ r ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-(1 / 2 - rhoMax) * (r : ℝ))

/-- The defining equation for `S_cen`. -/
theorem centeredWindowCoefficient_eq (H : ℕ) (rhoMax : ℝ) :
    centeredWindowCoefficient H rhoMax =
      2 * ∑ r ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-(1 / 2 - rhoMax) * (r : ℝ)) := rfl

/-- The finite nonlinear cell coefficient `S_nl^cell`. -/
@[expose]
def nonlinearCellWindowCoefficient (H : ℕ) (a Q : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 H,
    (3 : ℝ) ^ (-(r : ℝ) / 2 + a * ((r : ℝ) - 1) / Q)

/-- The finite nonlinear averaged-defect coefficient `S_nl^av`. -/
@[expose]
def nonlinearAverageWindowCoefficient (H : ℕ) (a Q : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 H,
    (3 : ℝ) ^ (-a * (r : ℝ) + a * ((r : ℝ) - 1) / (2 * Q))

/-- The constant contribution `c_const = (1 - 3⁻¹˲²)⁻¹`. -/
@[expose]
def constantSeminormCoefficient : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 : ℝ) / 2))⁻¹

/-- The defining equation for `c_const`. -/
theorem constantSeminormCoefficient_eq :
    constantSeminormCoefficient =
      (1 - (3 : ℝ) ^ (-(1 : ℝ) / 2))⁻¹ := rfl

/-- The response-energy load `Λ_t = ((L_t)^2 + |p·q|)¹˲²`. -/
@[expose]
def profileEnergyLoad (L : ℝ) (p q : Vec d) : ℝ :=
  Real.sqrt (L ^ 2 + |vecDot p q|)

/-- The defining equation for `Λ_t`. -/
theorem profileEnergyLoad_eq (L : ℝ) (p q : Vec d) :
    profileEnergyLoad L p q = Real.sqrt (L ^ 2 + |vecDot p q|) := rfl

theorem profileEnergyLoad_nonneg (L : ℝ) (p q : Vec d) :
    0 ≤ profileEnergyLoad L p q :=
  Real.sqrt_nonneg _

end

end HCPolySupport.HighContrast.Response
