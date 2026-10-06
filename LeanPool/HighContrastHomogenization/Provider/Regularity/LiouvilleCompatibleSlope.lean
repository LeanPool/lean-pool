/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleFixedCubeSlope

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleCompatibleSlope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Compatibility of fixed-cube Liouville slopes

Local slope selections become one global slope because the selected canonical
full-gradient classes form a compatible projective family and the canonical
slope map is injective on every admissible cube.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Compatible fixed-cube gradient classes represented by canonical slopes
are represented by one and the same slope on every admissible cube. -/
theorem exists_common_jointSlope_of_compatible_localGradients
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d} {n : ℤ}
    (hcoercive : ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
      (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
      euclideanNorm e ≤ 2 * euclideanNorm
        (localGradientClassAverage
          ((show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)))
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (g : ∀ q : ℕ, LocalGradientL2 d q)
    (hcompat : ∀ {q r : ℕ} (hqr : q ≤ r),
      localGradientRestrict hqr (g r) = g q)
    (hslope : ∀ q : ℕ, n ≤ (q : ℤ) → ∃ e : Vec d,
      g q = (jointAffineFullGradientLinearMap a hCauchy q) e) :
    ∃ e : Vec d, ∀ q : ℕ, n.toNat ≤ q →
      g q = (jointAffineFullGradientLinearMap a hCauchy q) e := by
  have hnbase : n ≤ (n.toNat : ℤ) := Int.self_le_toNat n
  obtain ⟨e, he⟩ := hslope n.toNat hnbase
  refine ⟨e, ?_⟩
  intro q hbaseq
  have hnq : n ≤ (q : ℤ) := hnbase.trans (by exact_mod_cast hbaseq)
  obtain ⟨eq, heq⟩ := hslope q hnq
  have hcanonical :
      (jointAffineFullGradientLinearMap a hCauchy n.toNat) eq =
        (jointAffineFullGradientLinearMap a hCauchy n.toNat) e := by
    calc
      (jointAffineFullGradientLinearMap a hCauchy n.toNat) eq =
          localGradientRestrict hbaseq
            ((jointAffineFullGradientLinearMap a hCauchy q) eq) :=
        (localGradientRestrict_jointAffineFullGradientLinearMap
          a hCauchy hbaseq eq).symm
      _ = localGradientRestrict hbaseq (g q) := by rw [heq]
      _ = g n.toNat := hcompat hbaseq
      _ = (jointAffineFullGradientLinearMap a hCauchy n.toNat) e := he
  have heqe : eq = e :=
    canonicalSlope_eq_of_localFullGradient_eq hcoercive hCauchy
      eq e n.toNat hnbase hcanonical
  simpa only [heqe] using heq

end

end HighContrast
end HCPolySupport
