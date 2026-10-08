/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.ScaleFactorArithmetic
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderCertificateInhabitation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RootInterface.CertificateMonotone

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Monotonicity of the printed-order certificate, and fold arithmetic

Two facts make the root's certificate instantiation possible.

* The printed-order quantitative certificate is **upward closed in the scale**
  and **downward closed in the rate**: its power tail is read above the scale
  with a negative exponent, so enlarging the scale and shrinking the rate both
  weaken it.  Consequently the certificate produced at the raw quenched scale
  and the quenched row rate is available at every larger scale and every smaller
  positive rate — which is exactly what is needed to place it at the *common
  affine scale* the rate-bearing predicate forces, and at a rate inside the
  frozen order window `κ ≤ (1 + g) / 4`.

* Two eccentricity fold factors multiply into one: `fold p * fold q ≤ fold (p+q)`.
  The certificate leg and the provider leg can therefore be carried by a single
  power.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory
open RowSupply (eccentricityFoldFactor one_le_eccentricityFoldFactor
  witnessEccentricity_nonneg)

noncomputable section

variable {d : ℕ}

/-! ## Fold arithmetic -/

/-- `max 1` is submultiplicative on nonnegative reals. -/
theorem max_one_mul_le {u v : ℝ} (_hu : 0 ≤ u) (hv : 0 ≤ v) :
    max 1 (u * v) ≤ max 1 u * max 1 v := by
  have hu1 : u ≤ max 1 u := le_max_right _ _
  have hv1 : v ≤ max 1 v := le_max_right _ _
  have hmu : (1 : ℝ) ≤ max 1 u := le_max_left _ _
  have hmv : (1 : ℝ) ≤ max 1 v := le_max_left _ _
  refine max_le (one_le_mul_of_one_le_of_one_le hmu hmv) ?_
  exact mul_le_mul hu1 hv1 hv (le_trans zero_le_one hmu)

/-- `max 1` commutes with nonnegative real powers on nonnegative arguments. -/
theorem max_one_rpow {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    (max 1 u) ^ t = max 1 (u ^ t) := by
  rcases le_or_gt 1 u with hu1 | hu1
  · rw [max_eq_right hu1, max_eq_right (Real.one_le_rpow hu1 ht)]
  · rw [max_eq_left hu1.le, Real.one_rpow,
      max_eq_left (Real.rpow_le_one hu hu1.le ht)]

/-- **Two fold factors multiply into one.** -/
theorem eccentricityFoldFactor_mul_le (abar : Mat d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    eccentricityFoldFactor abar p * eccentricityFoldFactor abar q ≤
      eccentricityFoldFactor abar (p + q) := by
  have hecc : 0 ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  unfold RowSupply.eccentricityFoldFactor
  rcases le_or_gt 1 (witnessEccentricity (symmPart abar)) with h1 | h1
  · have hp1 : (1 : ℝ) ≤ witnessEccentricity (symmPart abar) ^ p :=
      Real.one_le_rpow h1 hp
    have hq1 : (1 : ℝ) ≤ witnessEccentricity (symmPart abar) ^ q :=
      Real.one_le_rpow h1 hq
    have hpq1 : (1 : ℝ) ≤ witnessEccentricity (symmPart abar) ^ (p + q) :=
      Real.one_le_rpow h1 (by linarith only [hp, hq])
    rw [max_eq_right hp1, max_eq_right hq1, max_eq_right hpq1,
      ← Real.rpow_add (lt_of_lt_of_le zero_lt_one h1)]
  · have hp1 : witnessEccentricity (symmPart abar) ^ p ≤ 1 :=
      Real.rpow_le_one hecc h1.le hp
    have hq1 : witnessEccentricity (symmPart abar) ^ q ≤ 1 :=
      Real.rpow_le_one hecc h1.le hq
    rw [max_eq_left hp1, max_eq_left hq1, one_mul]
    exact le_max_left _ _

/-- A law-free amplitude times an eccentricity power, raised to a nonnegative
power, is again of that shape. -/
theorem max_one_mul_rpow_le_fold {abar : Mat d} {A t p : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (_hp : 0 ≤ p) :
    max 1 (A * witnessEccentricity (symmPart abar) ^ p) ^ t ≤
      max 1 (A ^ t) * eccentricityFoldFactor abar (p * t) := by
  have hecc : 0 ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  have heccp : 0 ≤ witnessEccentricity (symmPart abar) ^ p :=
    Real.rpow_nonneg hecc _
  have hstep : max 1 (A * witnessEccentricity (symmPart abar) ^ p) ≤
      max 1 A * max 1 (witnessEccentricity (symmPart abar) ^ p) :=
    max_one_mul_le hA heccp
  have hpos : (0 : ℝ) ≤ max 1 (A * witnessEccentricity (symmPart abar) ^ p) :=
    le_trans zero_le_one (le_max_left _ _)
  have hmono :
      max 1 (A * witnessEccentricity (symmPart abar) ^ p) ^ t ≤
        (max 1 A * max 1 (witnessEccentricity (symmPart abar) ^ p)) ^ t :=
    Real.rpow_le_rpow hpos hstep ht
  refine hmono.trans (le_of_eq ?_)
  rw [Real.mul_rpow (le_trans zero_le_one (le_max_left (1 : ℝ) A))
      (le_trans zero_le_one (le_max_left (1 : ℝ)
        (witnessEccentricity (symmPart abar) ^ p))),
    max_one_rpow hA ht, max_one_rpow heccp ht, ← Real.rpow_mul hecc]
  rfl

/-! ## The certificate is upward closed in the scale -/

theorem ScalarIdentityPowerTail.mono_scale
    {a : Book.Ch02.TriadicCoeffFamily d} {s amplitude kappa x y : ℝ}
    (h : ScalarIdentityPowerTail a s amplitude kappa x)
    (hamp : 0 ≤ amplitude) (hkappa : 0 < kappa) (hx : 0 < x) (hxy : x ≤ y) :
    ScalarIdentityPowerTail a s amplitude kappa y := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hrebase := h.rebase hx hy hxy
  refine hrebase.mono_amplitude ?_ hy
  have hratio : (1 : ℝ) ≤ y / x := (one_le_div hx).mpr hxy
  have hle : (y / x) ^ (-kappa) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hratio (neg_nonpos.mpr hkappa.le)
  calc amplitude * (y / x) ^ (-kappa) ≤ amplitude * 1 :=
        mul_le_mul_of_nonneg_left hle hamp
    _ = amplitude := mul_one amplitude

/-! ## The certificate is downward closed in the rate -/

theorem ScalarIdentityPowerTail.mono_rate
    {a : Book.Ch02.TriadicCoeffFamily d} {s amplitude kappa kappa' x : ℝ}
    (h : ScalarIdentityPowerTail a s amplitude kappa x)
    (hamp : 0 ≤ amplitude) (hx : 0 < x) (hkappa : kappa' ≤ kappa) :
    ScalarIdentityPowerTail a s amplitude kappa' x := by
  intro k hxk
  have hratio : (1 : ℝ) ≤ ((3 : ℝ) ^ k) / x := (one_le_div hx).mpr hxk
  have hpow : (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤ (((3 : ℝ) ^ k) / x) ^ (-kappa') :=
    Real.rpow_le_rpow_of_exponent_le hratio (neg_le_neg hkappa)
  exact (h k hxk).trans (mul_le_mul_of_nonneg_left hpow hamp)

/-- **The printed-order certificate is available at every larger scale and every
smaller positive rate.** -/
theorem PrintOrderQuantitativeNormalizedReferenceCertificate.mono
    [NeZero d] {abar : Mat d} {g amplitude kappa kappa' x y : ℝ}
    {a : CoeffSpace d}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappa x a)
    (hkappa' : 0 < kappa') (hkappa : kappa' ≤ kappa) (hxy : x ≤ y) :
    PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappa' y a := by
  obtain ⟨hS, aRef, hs, hsHalf, hamp, hkap, hx, haRef, htail⟩ := h
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  refine ⟨hS, aRef, hs, hsHalf, hamp, hkappa', hx.trans hxy, haRef, ?_⟩
  exact ScalarIdentityPowerTail.mono_rate
    (ScalarIdentityPowerTail.mono_scale htail hamp hkap hx0 hxy) hamp
    (lt_of_lt_of_le hx0 hxy) hkappa

/-! ## The physical block row is downward closed in the rate -/

theorem hasAllLaterPhysicalBlockRow_mono_rate
    {rho kappa kappa' C : ℝ} {Abar : BlockMat d} {S X : CoeffSpace d → ℝ}
    {a : CoeffSpace d}
    (h : Quenched.HasAllLaterPhysicalBlockRow rho kappa C Abar S X a)
    (hC : 0 ≤ C) (hX : 0 < X a) (hkappa : kappa' ≤ kappa) :
    Quenched.HasAllLaterPhysicalBlockRow rho kappa' C Abar S X a := by
  intro m hm
  have hratio : (1 : ℝ) ≤ ((3 : ℝ) ^ m) / X a := (one_le_div hX).mpr hm
  have hpow : (((3 : ℝ) ^ m) / X a) ^ (-kappa) ≤
      (((3 : ℝ) ^ m) / X a) ^ (-kappa') :=
    Real.rpow_le_rpow_of_exponent_le hratio (neg_le_neg hkappa)
  exact (h m hm).trans (mul_le_mul_of_nonneg_left hpow hC)

end

end RootInterface
end HighContrast
end HCPolySupport
