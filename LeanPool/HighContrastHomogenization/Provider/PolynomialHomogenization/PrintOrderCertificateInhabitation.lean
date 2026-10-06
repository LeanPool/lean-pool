/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedResponseQuenchedRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootEnclosure
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledPhysicalBlockDecay
public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.QuantitativeGoodTail
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderQuantitativeCertificate

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.PrintOrderCertificateInhabitation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Printed-order certificate inhabitation

The row-to-reference comparison is kept at the original measurable scale.
Its deterministic enclosure and exponent-gap prefactor is retained in the
amplitude.  Taking the square root then gives exactly the halved row-decay
rate used by the printed reconstruction.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The deterministic coefficient multiplying the squared physical row in
the normalized-reference comparison at one fixed enclosure shift. -/
@[expose]
noncomputable def normalizedReferencePowerPrefactor
    (d : ℕ) (s rho : ℝ) (G : ℕ) : ℝ :=
  (6 * (d : ℝ) * Real.sqrt d) *
    ((3 : ℝ) ^ (rho * (G : ℝ)) *
      (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))))

/-- The square-root amplitude retained from the physical block-row bound. -/
@[expose]
noncomputable def normalizedReferencePowerAmplitude
    (d : ℕ) (s rho delta : ℝ) (G : ℕ) : ℝ :=
  Real.sqrt (normalizedReferencePowerPrefactor d s rho G) *
    Real.sqrt delta

/-- A physical block row produces one global exactly normalized reference
family whose identity weak errors retain the square-root amplitude and the
halved row-decay rate at the original real scale. -/
theorem exists_normalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow
    [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s rho kappa delta : ℝ)
    (S X : CoeffSpace d → ℝ) (G : ℕ)
    (hG : witnessEccentricity (symmPart abar) * Real.sqrt d ≤
      (3 : ℝ) ^ (G : ℤ))
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hrhoGap : rho < 2 * s) (hkappa : 0 < kappa) (hdelta : 0 ≤ delta)
    (hrow : Quenched.HasAllLaterPhysicalBlockRow rho kappa delta
      (Book.Ch02.constantBlockMatrix abar) S X a)
    (hXone : 1 ≤ X a) (hburn : S a ≤ X a) :
    ∃ aRef : Book.Ch03.CoeffFamily d,
      (∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ⇑(normalizedCenteredCoeff a abar hS).1) ∧
      ScalarIdentityPowerTail aRef s
        (normalizedReferencePowerAmplitude d s rho delta G)
        (kappa / 2) (X a) := by
  classical
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  obtain ⟨aRef, haRef⟩ :=
    exists_normalizedReferenceCoeffFamily a abar hS 0
  have haRefGlobal : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1 := by
    intro Q
    simpa only [CoeffSpace.coeffOn_toCoeffField] using haRef Q
  have henclose : ∀ t : ℕ,
      adaptedCell (Selection.normalizedRoot (symmPart abar)) (t : ℤ) ⊆
        centeredCube d ((t + G : ℕ) : ℤ) := by
    intro t
    have hcell := Selection.adaptedCell_subset_centeredCube_add hd
      (T := (t : ℤ)) (G := G) (q := Selection.normalizedRoot (symmPart abar))
      (by
        rw [Selection.norm_normalizedRoot_eq_witnessEccentricity hS]
        simpa only [zpow_natCast] using hG)
    simpa only [Nat.cast_add] using hcell
  let B : ℝ := (3 : ℝ) ^ (rho * (G : ℝ)) *
    (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))))
  let D : ℝ := 6 * (d : ℝ) * Real.sqrt d
  let C : ℝ := D * B
  have hgap : 0 < 2 * s - rho := sub_pos.mpr hrhoGap
  have hratioGap : (3 : ℝ) ^ (-(2 * s - rho)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr hgap)
  have hBpos : 0 < B := by
    dsimp only [B]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (one_div_pos.mpr (sub_pos.mpr hratioGap))
  have hDpos : 0 < D := by
    dsimp only [D]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
    positivity
  have hCpos : 0 < C := by
    dsimp only [C]
    exact mul_pos hDpos hBpos
  refine ⟨aRef, haRefGlobal, ?_⟩
  change ScalarIdentityPowerTail aRef s
    (Real.sqrt C * Real.sqrt delta) (kappa / 2) (X a)
  have hXpos : 0 < X a := lt_of_lt_of_le zero_lt_one hXone
  intro k hXpow
  have hOnePow : (3 : ℝ) ^ (0 : ℤ) ≤ (3 : ℝ) ^ k := by
    simpa only [zpow_zero] using hXone.trans hXpow
  have hk0 : 0 ≤ k :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hOnePow
  have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  have hpowNat : (3 : ℝ) ^ k.toNat = (3 : ℝ) ^ k := by
    rw [← zpow_natCast, hkcast]
  have hXpowNat : X a ≤ (3 : ℝ) ^ k.toNat := by
    rwa [hpowNat]
  have hpowAdd : (3 : ℝ) ^ k.toNat ≤ (3 : ℝ) ^ (k.toNat + G) := by
    rw [pow_add]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  have hXpowAdd : X a ≤ (3 : ℝ) ^ (k.toNat + G) :=
    hXpowNat.trans hpowAdd
  have hactive : S a ≤ (3 : ℝ) ^ (k.toNat + G) :=
    hburn.trans hXpowAdd
  have herr :=
    homogenizationErrorOnCube_normalizedReference_infinity_two_sq_le_row
      k.toNat G a abar hS aRef haRef s rho (S a) hrho hrho1 hrhoGap
        (henclose k.toNat) hactive
  have hdecayAt := hrow (((k.toNat + G : ℕ) : ℤ)) (by
    simpa only [zpow_natCast] using hXpowAdd)
  have hdecay :
      Quenched.quenched_block_row rho
          (Book.Ch02.constantBlockMatrix abar) (S a) a (k.toNat + G) ≤
        delta *
          (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^
            (-kappa) := by
    simpa only [Quenched.physical_block_row_at_int, Int.toNat_natCast] using
      hdecayAt
  have hfill := normalizedRoot_fillingBoundaryFactor_le hd hS
  have hB0 : 0 ≤ B := hBpos.le
  have hsmall0 : 0 ≤ max 1
      (6 * (d : ℝ) * Real.sqrt d *
        ‖(Selection.normalizedRoot (symmPart abar))⁻¹‖) :=
    zero_le_one.trans (le_max_left _ _)
  have hpref0 : 0 ≤ max 1
      (6 * (d : ℝ) * Real.sqrt d *
        ‖(Selection.normalizedRoot (symmPart abar))⁻¹‖) * B :=
    mul_nonneg hsmall0 hB0
  have hratioShift0 : 0 ≤
      (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^ (-kappa) :=
    Real.rpow_nonneg (by positivity) _
  have hdeltaRatio0 : 0 ≤ delta *
      (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^ (-kappa) :=
    mul_nonneg hdelta hratioShift0
  have herr' : scalarIdentityWeakError aRef s k ^ 2 ≤
      max 1 (6 * (d : ℝ) * Real.sqrt d *
          ‖(Selection.normalizedRoot (symmPart abar))⁻¹‖) * B *
        Quenched.quenched_block_row rho
          (Book.Ch02.constantBlockMatrix abar) (S a) a (k.toNat + G) := by
    simpa only [scalarIdentityWeakError, hkcast, B, mul_assoc] using herr
  have hsqC : scalarIdentityWeakError aRef s k ^ 2 ≤
      C * (delta *
        (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^
          (-kappa)) := by
    calc
      scalarIdentityWeakError aRef s k ^ 2 ≤
          max 1 (6 * (d : ℝ) * Real.sqrt d *
              ‖(Selection.normalizedRoot (symmPart abar))⁻¹‖) * B *
            Quenched.quenched_block_row rho
              (Book.Ch02.constantBlockMatrix abar) (S a) a
                (k.toNat + G) := herr'
      _ ≤ max 1 (6 * (d : ℝ) * Real.sqrt d *
              ‖(Selection.normalizedRoot (symmPart abar))⁻¹‖) * B *
            (delta *
              (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^
                (-kappa)) :=
        mul_le_mul_of_nonneg_left hdecay hpref0
      _ ≤ D * B *
            (delta *
              (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^
                (-kappa)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfill hB0) hdeltaRatio0
      _ = C * (delta *
            (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^
              (-kappa)) := by rfl
  have hpowOrder :
      (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ)) := by
    rw [← hkcast, zpow_natCast, zpow_natCast]
    exact hpowAdd
  have hratioOrder :
      ((3 : ℝ) ^ k) / X a ≤
        ((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a :=
    div_le_div_of_nonneg_right hpowOrder hXpos.le
  have hdecayOrder :
      (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^ (-kappa) ≤
        (((3 : ℝ) ^ k) / X a) ^ (-kappa) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hratioOrder
      (neg_nonpos.mpr hkappa.le)
  have hsq : scalarIdentityWeakError aRef s k ^ 2 ≤
      C * (delta * (((3 : ℝ) ^ k) / X a) ^ (-kappa)) :=
    hsqC.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdecayOrder hdelta) hCpos.le)
  have hratioPos : 0 < ((3 : ℝ) ^ k) / X a := by positivity
  have hfactorSq :
      ((((3 : ℝ) ^ k) / X a) ^ (-(kappa / 2))) ^ 2 =
        (((3 : ℝ) ^ k) / X a) ^ (-kappa) := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul hratioPos.le]
    congr 1
    ring
  have htarget0 : 0 ≤
      (Real.sqrt C * Real.sqrt delta) *
        (((3 : ℝ) ^ k) / X a) ^ (-(kappa / 2)) :=
    mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hratioPos.le _)
  apply (sq_le_sq₀ (scalarIdentityWeakError_nonneg aRef s k) htarget0).mp
  calc
    scalarIdentityWeakError aRef s k ^ 2 ≤
        C * (delta * (((3 : ℝ) ^ k) / X a) ^ (-kappa)) := hsq
    _ = ((Real.sqrt C * Real.sqrt delta) *
          (((3 : ℝ) ^ k) / X a) ^ (-(kappa / 2))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hCpos.le,
        Real.sq_sqrt hdelta, hfactorSq]
      ring

end

end HighContrast
end HCPolySupport
