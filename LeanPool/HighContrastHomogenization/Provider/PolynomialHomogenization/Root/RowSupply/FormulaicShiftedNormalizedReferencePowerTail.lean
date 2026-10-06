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

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.FormulaicShiftedNormalizedReferencePowerTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Formulaically shifted power tails for an exactly normalized reference coefficient

One global affine-pullback coefficient family supplies every reference cube.
A fixed enclosure of the exact normalized root controls every physical row,
and a further natural generation shift absorbs the resulting geometric and
exponent-gap factor.  The shift is the ceiling of an explicit logarithmic
expression, so the same witness used by the tail proof has a deterministic
upper bound.
-/

namespace HCPolySupport
namespace HighContrast
namespace Certificate

open Book.Ch02

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The deterministic prefactor absorbed by the generation shift. -/
@[expose]
noncomputable def shiftedTailAbsorptionPrefactor
    (d : ℕ) (s rho : ℝ) (G : ℕ) : ℝ :=
  (6 * (d : ℝ) * Real.sqrt d) *
    ((3 : ℝ) ^ (rho * (G : ℝ)) *
      (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))))

/-- The formulaic generation shift used in the normalized-reference tail. -/
@[expose]
noncomputable def formulaicNormalizedReferenceTailShift
    (d : ℕ) (s rho kappa : ℝ) (G : ℕ) : ℕ :=
  ⌈max 0
    (Real.logb 3 (shiftedTailAbsorptionPrefactor d s rho G) / kappa)⌉₊

/-- The formulaic shift absorbs its prefactor and lies strictly below the
corresponding logarithmic threshold plus one. -/
theorem formulaicNormalizedReferenceTailShift_spec
    {d : ℕ} {s rho kappa : ℝ} {G : ℕ}
    (hkappa : 0 < kappa)
    (hC : 0 < shiftedTailAbsorptionPrefactor d s rho G) :
    shiftedTailAbsorptionPrefactor d s rho G ≤
        (3 : ℝ) ^
          (kappa * (formulaicNormalizedReferenceTailShift d s rho kappa G : ℝ)) ∧
      (formulaicNormalizedReferenceTailShift d s rho kappa G : ℝ) <
        max 0
          (Real.logb 3 (shiftedTailAbsorptionPrefactor d s rho G) / kappa) + 1 := by
  let y : ℝ := max 0
    (Real.logb 3 (shiftedTailAbsorptionPrefactor d s rho G) / kappa)
  have hy : 0 ≤ y := le_max_left _ _
  have hratio :
      Real.logb 3 (shiftedTailAbsorptionPrefactor d s rho G) / kappa ≤ y :=
    le_max_right _ _
  have hLlower :
      y ≤ (formulaicNormalizedReferenceTailShift d s rho kappa G : ℝ) := by
    exact Nat.le_ceil y
  have hlog :
      Real.logb 3 (shiftedTailAbsorptionPrefactor d s rho G) ≤
        kappa * (formulaicNormalizedReferenceTailShift d s rho kappa G : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hratio hkappa.le
    rw [mul_div_cancel₀ _ hkappa.ne'] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left hLlower hkappa.le)
  constructor
  · have hmono := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hlog
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hC] at hmono
  · change (⌈y⌉₊ : ℝ) < y + 1
    exact Nat.ceil_lt_add_one hy

private theorem physical_ratio_rpow_le_geometric_gap
    {x kappa : ℝ} {n k : ℤ} (hx : 0 < x)
    (hxn : x ≤ (3 : ℝ) ^ n) (hkappa : 0 < kappa) :
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
      (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
  have hkpow : 0 < (3 : ℝ) ^ k := by positivity
  have hratio : 0 < ((3 : ℝ) ^ k) / x := div_pos hkpow hx
  have hgap : 0 < (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by positivity
  have hbase :
      (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) ≤ ((3 : ℝ) ^ k) / x := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
      Real.rpow_intCast, Real.rpow_intCast]
    exact div_le_div_of_nonneg_left hkpow.le hx hxn
  calc
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
        ((3 : ℝ) ^ ((k : ℝ) - (n : ℝ))) ^ (-kappa) :=
      (Real.rpow_le_rpow_iff_of_neg hratio hgap (neg_neg_of_pos hkappa)).2 hbase
    _ = (3 : ℝ) ^ (((k : ℝ) - (n : ℝ)) * (-kappa)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    _ = (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
      congr 1
      ring

private theorem prefactor_mul_physical_ratio_le_shifted_decay
    {C x kappa : ℝ} {N L G : ℕ} {k : ℤ}
    (hC : C ≤ (3 : ℝ) ^ (kappa * (L : ℝ)))
    (hx : 0 < x) (hxN : x ≤ (3 : ℝ) ^ (N : ℤ))
    (hkappa : 0 < kappa) :
    C * (((3 : ℝ) ^ (k + (G : ℤ))) / x) ^ (-kappa) ≤
      (3 : ℝ) ^
        (-kappa * ((k : ℝ) - ((N + L : ℕ) : ℝ))) := by
  have hratio := physical_ratio_rpow_le_geometric_gap
    (n := (N : ℤ)) (k := k + (G : ℤ)) hx hxN hkappa
  have hratio0 : 0 ≤ (((3 : ℝ) ^ (k + (G : ℤ))) / x) ^ (-kappa) :=
    Real.rpow_nonneg (by positivity) _
  have hpow0 : 0 ≤ (3 : ℝ) ^ (kappa * (L : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hexponent :
      kappa * (L : ℝ) +
          -kappa * (((k + (G : ℤ) : ℤ) : ℝ) - (N : ℝ)) ≤
        -kappa * ((k : ℝ) - ((N + L : ℕ) : ℝ)) := by
    push_cast
    calc
      kappa * (L : ℝ) +
          -kappa * ((k : ℝ) + (G : ℝ) - (N : ℝ)) =
          -kappa * ((k : ℝ) - ((N : ℝ) + (L : ℝ))) -
            kappa * (G : ℝ) := by ring
      _ ≤ -kappa * ((k : ℝ) - ((N : ℝ) + (L : ℝ))) :=
        sub_le_self _ (mul_nonneg hkappa.le (Nat.cast_nonneg G))
  calc
    C * (((3 : ℝ) ^ (k + (G : ℤ))) / x) ^ (-kappa) ≤
        (3 : ℝ) ^ (kappa * (L : ℝ)) *
          (((3 : ℝ) ^ (k + (G : ℤ))) / x) ^ (-kappa) :=
      mul_le_mul_of_nonneg_right hC hratio0
    _ ≤ (3 : ℝ) ^ (kappa * (L : ℝ)) *
        (3 : ℝ) ^
          (-kappa * (((k + (G : ℤ) : ℤ) : ℝ) - (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio hpow0
    _ = (3 : ℝ) ^
        (kappa * (L : ℝ) +
          -kappa * (((k + (G : ℤ) : ℤ) : ℝ) - (N : ℝ))) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ ≤ (3 : ℝ) ^
        (-kappa * ((k : ℝ) - ((N + L : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- A physical block row produces one global exactly normalized reference
family whose identity weak errors retain the square-root amplitude and the
halved row-decay rate above the shifted triadic scale. -/
theorem exists_formulaicShiftedNormalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow
    [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s rho kappa delta : ℝ)
    (S X : CoeffSpace d → ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hrhoGap : rho < 2 * s) (hkappa : 0 < kappa) (hdelta : 0 ≤ delta)
    (hrow : Quenched.HasAllLaterPhysicalBlockRow rho kappa delta
      (Book.Ch02.constantBlockMatrix abar) S X a)
    (hXone : 1 ≤ X a) (hburn : S a ≤ X a) :
    ∃ G : ℕ, ∃ aRef : Book.Ch03.CoeffFamily d, ∃ L : ℕ,
      witnessEccentricity (symmPart abar) * Real.sqrt d ≤
          (3 : ℝ) ^ (G : ℤ) ∧
      (3 : ℝ) ^ (G : ℤ) ≤
          1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) ∧
      L = formulaicNormalizedReferenceTailShift d s rho kappa G ∧
      (L : ℝ) <
          max 0
            (Real.logb 3 (shiftedTailAbsorptionPrefactor d s rho G) / kappa) + 1 ∧
      (∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ⇑(normalizedCenteredCoeff a abar hS).1) ∧
      ScalarIdentityPowerTail aRef s (Real.sqrt delta) (kappa / 2)
        ((3 : ℝ) ^
          ((Quenched.triadicCeilingIndex (X a) + L : ℕ) : ℤ)) := by
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
  have hecc0 :
      0 ≤ witnessEccentricity (symmPart abar) := by
    simpa only [witnessEccentricity] using
      (Real.sqrt_nonneg
        (specBound (symmPart abar) * specBound (symmPart abar)⁻¹))
  obtain ⟨G, hG, hGupper⟩ := Entry.exists_pow_three_bracket
    (x := witnessEccentricity (symmPart abar) * Real.sqrt d)
    (mul_nonneg hecc0 (Real.sqrt_nonneg d))
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
  let C : ℝ := shiftedTailAbsorptionPrefactor d s rho G
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
    dsimp only [C, shiftedTailAbsorptionPrefactor, D, B]
    exact mul_pos hDpos hBpos
  let L : ℕ := formulaicNormalizedReferenceTailShift d s rho kappa G
  have hLspec := formulaicNormalizedReferenceTailShift_spec hkappa hCpos
  have hLabsorb : C ≤ (3 : ℝ) ^ (kappa * (L : ℝ)) := hLspec.1
  have hLupper : (L : ℝ) <
      max 0 (Real.logb 3 (shiftedTailAbsorptionPrefactor d s rho G) / kappa) + 1 :=
    hLspec.2
  refine ⟨G, aRef, L, hG, hGupper, rfl, hLupper, haRefGlobal, ?_⟩
  let N : ℕ := Quenched.triadicCeilingIndex (X a)
  have hceilNat : X a ≤ (3 : ℝ) ^ N := by
    simpa only [N] using Quenched.le_pow_triadicCeilingIndex hXone
  have hceil : X a ≤ (3 : ℝ) ^ (N : ℤ) := by
    simpa only [zpow_natCast] using hceilNat
  have hXpos : 0 < X a := lt_of_lt_of_le zero_lt_one hXone
  have hweak : ∀ k : ℤ, ((N + L : ℕ) : ℤ) ≤ k →
      scalarIdentityWeakError aRef s k ≤
        Real.sqrt delta *
          (3 : ℝ) ^
            (-(kappa / 2) *
              ((k : ℝ) - ((N + L : ℕ) : ℝ))) := by
    intro k hstart
    have hNstart : (N : ℤ) ≤ ((N + L : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_add_right N L
    have hNk : (N : ℤ) ≤ k := hNstart.trans hstart
    have hk0 : 0 ≤ k := (Int.natCast_nonneg (N + L)).trans hstart
    have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
    have hXpow : X a ≤ (3 : ℝ) ^ k :=
      hceil.trans (zpow_le_zpow_right₀ (by norm_num) hNk)
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
    have hratio0 : 0 ≤
        (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^ (-kappa) :=
      Real.rpow_nonneg (by positivity) _
    have hdeltaRatio0 : 0 ≤ delta *
        (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^ (-kappa) :=
      mul_nonneg hdelta hratio0
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
    have habsorb := prefactor_mul_physical_ratio_le_shifted_decay
      (C := C) (x := X a) (kappa := kappa) (N := N) (L := L) (G := G)
        (k := k) hLabsorb hXpos hceil hkappa
    have habsorb' : C *
          (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^ (-kappa) ≤
        (3 : ℝ) ^
          (-kappa * ((k : ℝ) - ((N + L : ℕ) : ℝ))) := by
      simpa only [Nat.cast_add, hkcast] using habsorb
    have hsq : scalarIdentityWeakError aRef s k ^ 2 ≤
        delta * (3 : ℝ) ^
          (-kappa * ((k : ℝ) - ((N + L : ℕ) : ℝ))) := by
      calc
        scalarIdentityWeakError aRef s k ^ 2 ≤
            C * (delta *
              (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^
                (-kappa)) := hsqC
        _ = delta * (C *
              (((3 : ℝ) ^ (((k.toNat + G : ℕ) : ℤ))) / X a) ^
                (-kappa)) := by ring
        _ ≤ delta * (3 : ℝ) ^
              (-kappa * ((k : ℝ) - ((N + L : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left habsorb' hdelta
    have hfactorSq :
        ((3 : ℝ) ^
          (-(kappa / 2) *
            ((k : ℝ) - ((N + L : ℕ) : ℝ)))) ^ 2 =
          (3 : ℝ) ^
            (-kappa * ((k : ℝ) - ((N + L : ℕ) : ℝ))) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring_nf
    have htarget0 : 0 ≤ Real.sqrt delta *
        (3 : ℝ) ^
          (-(kappa / 2) *
            ((k : ℝ) - ((N + L : ℕ) : ℝ))) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)
    apply (sq_le_sq₀ (scalarIdentityWeakError_nonneg aRef s k) htarget0).mp
    rw [mul_pow, Real.sq_sqrt hdelta, hfactorSq]
    exact hsq
  change ScalarIdentityPowerTail aRef s (Real.sqrt delta) (kappa / 2)
    ((3 : ℝ) ^ ((N + L : ℕ) : ℤ))
  intro k hscale
  have hstart : ((N + L : ℕ) : ℤ) ≤ k :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hscale
  have hratio :
      ((((3 : ℝ) ^ k) /
          ((3 : ℝ) ^ ((N + L : ℕ) : ℤ))) ^ (-(kappa / 2))) =
        (3 : ℝ) ^
          (-(kappa / 2) *
            ((k : ℝ) - ((N + L : ℕ) : ℝ))) := by
    rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0),
      ← Real.rpow_intCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  rw [hratio]
  exact hweak k hstart

end

end Certificate
end HighContrast
end HCPolySupport
