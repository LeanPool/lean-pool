/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderNormalizedReferencePowerTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.MidpointResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RealScaleTriadicBracket
public import LeanPool.HighContrastHomogenization.Provider.Quenched.PhysicalScaleBlockRow

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.TriadicPhysicalBlockRowTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Triadic transport of a physical block row

The physical block row is transported before the normalized-response
all-depth sum is formed.  Its activation scale becomes one, while the lost
fraction of the original activation is retained in the row amplitude.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- The amplitude of the row after a triadic rescaling which places its
activation below the unit generation. -/
@[expose]
noncomputable def triadicallyScaledRowAmplitude
    (delta x : ℝ) (N : ℕ) (kappa : ℝ) : ℝ :=
  delta * (x / (3 : ℝ) ^ N) ^ kappa

/-- An all-later physical row transports to the restored coefficient sample.
The new row starts at one, and its amplitude records the exact activation
ratio `x / 3^N`. -/
theorem hasAllLaterPhysicalBlockRow_physicalScaleCoeff
    (rho kappa delta : ℝ) (Abar : BlockMat d)
    (S X : CoeffSpace d → ℝ) (a : CoeffSpace d) (N : ℕ)
    (hrow : Quenched.HasAllLaterPhysicalBlockRow
      rho kappa delta Abar S X a)
    (hXone : 1 ≤ X a) (hburn : S a ≤ X a)
    (hactive : X a ≤ (3 : ℝ) ^ N) :
    Quenched.HasAllLaterPhysicalBlockRow rho kappa
      (triadicallyScaledRowAmplitude delta (X a) N kappa) Abar
      (fun _ ↦ 1) (fun _ ↦ 1) (Quenched.physicalScaleCoefficient N a) := by
  intro m hm
  have hm0 : 0 ≤ m := by
    by_contra hmneg
    have hpow : (3 : ℝ) ^ m < 1 :=
      zpow_lt_one_of_neg₀ (by norm_num) (lt_of_not_ge hmneg)
    exact (not_lt_of_ge hm) hpow
  have hmnat : ((m.toNat : ℕ) : ℤ) = m := by
    exact Int.toNat_of_nonneg hm0
  have hsourceRatio : S a / (3 : ℝ) ^ N ≤ 1 := by
    apply (div_le_one (by positivity)).2
    exact hburn.trans hactive
  have hsourceFloor : max 1 (S a / (3 : ℝ) ^ N) = 1 :=
    max_eq_left hsourceRatio
  have hsourceActive : X a ≤ (3 : ℝ) ^ ((N : ℤ) + m) := by
    calc
      X a ≤ (3 : ℝ) ^ N := hactive
      _ = (3 : ℝ) ^ (N : ℤ) := by rw [zpow_natCast]
      _ ≤ (3 : ℝ) ^ ((N : ℤ) + m) := by
        exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).2
          (by omega)
  have hsource := hrow ((N : ℤ) + m) hsourceActive
  have hrowEq :
      Quenched.physicalBlockRowAtInteger rho Abar (fun _ ↦ 1)
          (Quenched.physicalScaleCoefficient N a) m =
        Quenched.physicalBlockRowAtInteger rho Abar S a ((N : ℤ) + m) := by
    unfold Quenched.physicalBlockRowAtInteger
    rw [show ((N : ℤ) + m).toNat = N + m.toNat by omega]
    simpa only [hsourceFloor] using
      (Quenched.quenched_block_row_physical_scale_coeff
        rho Abar (S a) N m.toNat a)
  rw [hrowEq]
  calc
    Quenched.physicalBlockRowAtInteger rho Abar S a ((N : ℤ) + m) ≤
        delta *
          (((3 : ℝ) ^ ((N : ℤ) + m)) / X a) ^ (-kappa) := hsource
    _ = triadicallyScaledRowAmplitude delta (X a) N kappa *
          (((3 : ℝ) ^ m) / 1) ^ (-kappa) := by
      unfold triadicallyScaledRowAmplitude
      have hthree : 0 < (3 : ℝ) ^ N := by positivity
      have hX : 0 < X a := zero_lt_one.trans_le hXone
      rw [div_one, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
      rw [show ((3 : ℝ) ^ N * (3 : ℝ) ^ m) / X a =
          ((3 : ℝ) ^ m) / (X a / (3 : ℝ) ^ N) by
        field_simp [hthree.ne', hX.ne']]
      rw [Real.div_rpow (by positivity) (by positivity)]
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      have hA : ((3 : ℝ) ^ m) ^ kappa ≠ 0 :=
        (Real.rpow_pos_of_pos (by positivity) _).ne'
      have hB : (X a / (3 : ℝ) ^ N) ^ kappa ≠ 0 :=
        (Real.rpow_pos_of_pos (by positivity) _).ne'
      field_simp [hA, hB]

end

end RowSupply
end HighContrast
end HCPolySupport
