/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileMaximumBadLp
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBadLevelResidue

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# At the matched threshold the good-set residue is zero, and the source leg stays geometric

The two machine questions the released level has to answer before it is worth
releasing anywhere.

**Does the residue vanish?**  The residue enters because the excess is taken
above a threshold *below* the maximum's own deterministic level: with the level
held at `1 / 2` and the almost-sure envelope at `R / 2`, the excess off the bad
event is bounded by `(R - 1) / 2` rather than by `0`, and its fourth power is
the constant summand of the scaled bad-moment majorant.  The vanishing of the
good-set excess below is the one line that changes when the threshold is
matched to the
envelope, and `lintegral_pow_eq_setLIntegral_of_matched_threshold` is its
consequence for the moment: **the good set contributes nothing at all**, so the
moment bound is the bad-set bound with no additive term.

**Does the source leg stay geometric?**  This is the residue's own
fail-closed requirement: nonnegativity of a replacement majorant is not enough,
it must admit the geometric leg in the shape the entry-slot clause reads.
`profileBadMajorantAt_badMoment_le` is that leg at the released level, and
the start bound is it at the account's own use site — the same shape as
the established pair, with one `Π`-polynomial factor `R` in front of a constant the
source slot already permits to be `Π`-polynomial.

Nothing here is imported by any established file.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

/-! ## The residue vanishes at the matched threshold -/

/-- **The moment loses its constant summand.**  When the threshold is matched to
the good-set envelope, the excess vanishes off the bad set and the moment
integral is the bad set's alone — no residue is added. -/
theorem lintegral_pow_eq_setLIntegral_of_matched_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Q beta : ℝ} (hQ : 0 < Q)
    {M W : Ω → ℝ≥0∞} {G : Set Ω} (hG : MeasurableSet G)
    (hWdef : ∀ a, W a = M a - ENNReal.ofReal beta)
    (hgood : ∀ᵐ a ∂P, a ∉ G → M a ≤ ENNReal.ofReal beta) :
    ∫⁻ a, W a ^ Q ∂P = ∫⁻ a in G, W a ^ Q ∂P := by
  have hzero : ∫⁻ a in Gᶜ, W a ^ Q ∂P = 0 := by
    have hae : ∀ᵐ a ∂(P.restrict Gᶜ), W a ^ Q = 0 := by
      rw [ae_restrict_iff' hG.compl]
      filter_upwards [hgood] with a ha hmem
      rw [hWdef a, tsub_eq_zero_of_le (ha hmem), ENNReal.zero_rpow_of_pos hQ]
    have hcongr : ∫⁻ a in Gᶜ, W a ^ Q ∂P = ∫⁻ _ in Gᶜ, (0 : ℝ≥0∞) ∂P :=
      lintegral_congr_ae hae
    rw [hcongr, lintegral_zero]
  calc ∫⁻ a, W a ^ Q ∂P
      = ∫⁻ a in G, W a ^ Q ∂P + ∫⁻ a in Gᶜ, W a ^ Q ∂P :=
        (lintegral_add_compl _ hG).symm
    _ = ∫⁻ a in G, W a ^ Q ∂P := by rw [hzero, add_zero]

/-! ## The source leg is still geometric -/

/-- **The geometric bad-event leg at the released level.**  The counterpart of
the profile bad-majorant moment bound, for the residue-free majorant
`R ^ 4 · badMomentMajorant`
at the matched threshold `(beta, lev) = (R / 2, R)`.  The rate is the printed
half rate, unchanged; the cost of the released level is the single factor `R`. -/
theorem profileBadMajorantAt_badMoment_le (K : ℝ) {R : ℝ} (hR : 1 ≤ R)
    {Delta : ℤ} (hD : 0 ≤ Delta) :
    Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta) (R / 2) R ≤
      R * badSourceConstant K * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (Delta : ℝ)) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hS := sourceMomentSix_nonneg K
  have hc0 : (0 : ℝ) ≤ sourceMomentSix K / 16 := by linarith only [hS]
  have hD0 : (0 : ℝ) ≤ (Delta : ℝ) := by exact_mod_cast hD
  have h3 : (0 : ℝ) < 3 := by norm_num
  set A : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ) * (Delta : ℝ)) with hA
  set B : ℝ := (sourceMomentSix K / 16) ^ (4 : ℝ)⁻¹ with hB
  have hA0 : 0 < A := Real.rpow_pos_of_pos h3 _
  have hB0 : 0 ≤ B := Real.rpow_nonneg hc0 _
  have hA1 : A ≤ 1 := by
    rw [hA]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    nlinarith only [hD0]
  -- the majorant factorizes exactly as at the fixed level
  have hpow0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((2 : ℝ) * (Delta : ℝ))) :=
    Real.rpow_nonneg h3.le _
  have hm0 : (0 : ℝ) ≤ badMomentMajorant K Delta := badMomentMajorant_nonneg K Delta
  have hfac : badMomentMajorant K Delta =
      (3 : ℝ) ^ (-((2 : ℝ) * (Delta : ℝ))) * (sourceMomentSix K / 16) := by
    rw [badMomentMajorant]
    ring
  have hexp : -((2 : ℝ) * (Delta : ℝ)) * (4 : ℝ)⁻¹ = -(1 / 2 : ℝ) * (Delta : ℝ) := by
    ring
  have hquarter : (badMomentMajorant K Delta) ^ (4 : ℝ)⁻¹ = A * B := by
    rw [hfac, Real.mul_rpow hpow0 hc0, ← Real.rpow_mul h3.le, hexp, hA, hB]
  -- the scaling factor comes out of the quarter power
  have hR4 : (R ^ 4 : ℝ) ^ ((4 : ℝ)⁻¹) = R := by
    rw [← Real.rpow_natCast R 4, ← Real.rpow_mul hR0.le]
    norm_num
  have hu : (R ^ 4 * badMomentMajorant K Delta) ^ ((4 : ℝ)⁻¹) = R * (A * B) := by
    rw [Real.mul_rpow (by positivity) hm0, hR4, hquarter]
  -- the two exponents of the small-drift branch
  have hlast : (1 : ℝ) / 2 - (4 : ℝ)⁻¹ = (4 : ℝ)⁻¹ := by norm_num
  have hmid : (R - R / 2) ^ ((1 : ℝ) - (4 : ℝ) / 2) = 2 / R := by
    have hb : (R - R / 2 : ℝ) = R / 2 := by ring
    have he : ((1 : ℝ) - (4 : ℝ) / 2) = -(1 : ℝ) := by norm_num
    rw [hb, he, Real.rpow_neg (by positivity), Real.rpow_one]
    field_simp
  have hbetalev : R / 2 < R := by linarith only [hR0]
  have hprofile :
      Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta) (R / 2) R =
        R * (2 * (A ^ 2 * B ^ 2) + A * B) := by
    rw [Response.profileBadMajorantAt_of_lt hbetalev, hlast, hu, hmid]
    field_simp
  have hsq : A ^ 2 ≤ A := by nlinarith only [hA0, hA1]
  have hkey : (0 : ℝ) ≤ B ^ 2 * (A - A ^ 2) :=
    mul_nonneg (sq_nonneg B) (by linarith only [hsq])
  have hinner : 2 * (A ^ 2 * B ^ 2) + A * B ≤ badSourceConstant K * A := by
    rw [badSourceConstant, ← hB]
    nlinarith only [hkey]
  rw [hprofile]
  have hmul := mul_le_mul_of_nonneg_left hinner hR0.le
  calc R * (2 * (A ^ 2 * B ^ 2) + A * B) ≤ R * (badSourceConstant K * A) := hmul
    _ = R * badSourceConstant K * A := by ring

end

end HCPolySupport.HighContrast.Quenched
