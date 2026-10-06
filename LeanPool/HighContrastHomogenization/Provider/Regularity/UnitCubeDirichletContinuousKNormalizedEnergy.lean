/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeDirichletContinuousKIntegralSplit

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeDirichletContinuousKNormalizedEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized continuous K-energy for the unit-cube Dirichlet map

The low and root scale intervals are recombined after multiplying the
continuum energy by `2s`.  The exact endpoint contribution then merges with
the normalized Euclidean `L²` square, leaving the sharp factor `A^(2s)`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

@[expose]
public noncomputable def unitCubeEuclideanL2FieldToCenteredCubeZero
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    CenteredCubeEuclideanL2Field d 0 where
  toField := F
  euclideanMemL2 := by
    simpa only [centeredCubeDomain, unitCenteredCubeDomain] using F.euclideanMemL2

@[simp] private theorem unitCubeEuclideanL2FieldToCenteredCubeZero_apply
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldToCenteredCubeZero F x = F x :=
  rfl

private theorem unitCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le
    {d : ℕ} [NeZero d] (h : UnitCubeEuclideanL2Field d)
    (w : H10Function (openCubeSet (originCube d 0)))
    (hproblem : CubeDirichletDivergenceProblem (originCube d 0) w h) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (unitCubeGradientEuclideanL2Field w) ≤
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h := by
  have hbound :=
    centeredCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le
      (unitCubeEuclideanL2FieldToCenteredCubeZero h) w
      (by
        simpa only [unitCubeEuclideanL2FieldToCenteredCubeZero_apply] using! hproblem)
  simpa only [centeredCubeDomain, unitCenteredCubeDomain,
    unitCubeEuclideanL2FieldToCenteredCubeZero_apply,
    centeredCubeGradientEuclideanL2Field_apply,
    unitCubeGradientEuclideanL2Field_apply] using! hbound

private theorem continuousKSeminormIntegral_eq_low_add_root
    {d : ℕ} {A : ℝ} (hzeroInv : 0 ≤ A⁻¹) (hinvOne : A⁻¹ ≤ 1)
    (sigma : ℝ) (F : UnitCubeEuclideanL2Field d) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand sigma F t) =
      (∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
        continuousKSeminormIntegrand sigma F t) +
        ∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
          continuousKSeminormIntegrand sigma F t := by
  let f : ℝ → ℝ≥0∞ := continuousKSeminormIntegrand sigma F
  have hIooIoc (a b : ℝ) :
      (∫⁻ t in Set.Ioo a b, f t) = ∫⁻ t in Set.Ioc a b, f t := by
    rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := MeasureTheory.volume))]
  rw [show (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      continuousKSeminormIntegrand sigma F t) =
        ∫⁻ t in Set.Ioc (0 : ℝ) 1, f t from hIooIoc 0 1]
  rw [show (∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
      continuousKSeminormIntegrand sigma F t) =
        ∫⁻ t in Set.Ioc (0 : ℝ) A⁻¹, f t from hIooIoc 0 A⁻¹]
  rw [show (∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
      continuousKSeminormIntegrand sigma F t) =
        ∫⁻ t in Set.Ioc A⁻¹ (1 : ℝ), f t from hIooIoc A⁻¹ 1]
  calc
    (∫⁻ t in Set.Ioc (0 : ℝ) 1, f t) =
        ∫⁻ t in Set.Ioc (0 : ℝ) A⁻¹ ∪ Set.Ioc A⁻¹ (1 : ℝ), f t := by
      rw [Set.Ioc_union_Ioc_eq_Ioc hzeroInv hinvOne]
    _ = (∫⁻ t in Set.Ioc (0 : ℝ) A⁻¹, f t) +
        ∫⁻ t in Set.Ioc A⁻¹ (1 : ℝ), f t :=
      lintegral_union measurableSet_Ioc
        (Set.Ioc_disjoint_Ioc_of_le (a := (0 : ℝ)) (d := (1 : ℝ)) le_rfl)

private theorem normalizedContinuousKRootCoefficient
    {A : ℝ} (honeA : 1 ≤ A) (s : FractionalOrder) :
    1 + ENNReal.ofReal (2 * s.1) *
        ENNReal.ofReal ((Real.rpow A (2 * s.1) - 1) / (2 * s.1)) =
      (ENNReal.ofReal A) ^ (2 * s.1) := by
  let p : ℝ := 2 * s.1
  let x : ℝ := Real.rpow A p
  let q : ℝ := (x - 1) / p
  have hA : 0 < A := zero_lt_one.trans_le honeA
  have hp : 0 < p := mul_pos (by norm_num) (FractionalOrder.pos s)
  have honeX : 1 ≤ x := by
    exact Real.one_le_rpow honeA hp.le
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr honeX) hp.le
  have hreal : 1 + p * q = x := by
    calc
      1 + p * q = 1 + (x - 1) := by
        rw [show q = (x - 1) / p by rfl, mul_div_cancel₀ _ hp.ne']
      _ = x := by ring
  have hmul : ENNReal.ofReal (p * q) =
      ENNReal.ofReal p * ENNReal.ofReal q :=
    ENNReal.ofReal_mul hp.le
  have hadd : ENNReal.ofReal (1 + p * q) =
      ENNReal.ofReal 1 + ENNReal.ofReal (p * q) :=
    ENNReal.ofReal_add zero_le_one (mul_nonneg hp.le hq)
  have hpow : ENNReal.ofReal x = (ENNReal.ofReal A) ^ p := by
    exact (ENNReal.ofReal_rpow_of_pos hA).symm
  change 1 + ENNReal.ofReal p * ENNReal.ofReal q =
    (ENNReal.ofReal A) ^ p
  calc
    1 + ENNReal.ofReal p * ENNReal.ofReal q =
        ENNReal.ofReal 1 + ENNReal.ofReal (p * q) := by
      rw [ENNReal.ofReal_one, hmul]
    _ = ENNReal.ofReal (1 + p * q) := hadd.symm
    _ = ENNReal.ofReal x := congrArg ENNReal.ofReal hreal
    _ = (ENNReal.ofReal A) ^ p := hpow

/-- A dimension-dependent expansion factor, fixed before the fractional
order and analytic inputs, controls the normalized quadratic continuous
`K`-energy of the unit-cube identity Dirichlet gradient by the datum energy
with the exact multiplier `A^(2s)`. -/
theorem exists_unitCubeDirichletContinuousKNormalizedEnergyBound
    (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (s : FractionalOrder) (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0))),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
                (2 : ℝ≥0∞) (unitCubeGradientEuclideanL2Field w)) ^ 2 +
              ENNReal.ofReal (2 * s.1) *
                (∫⁻ t in Set.Ioo (0 : ℝ) 1,
                  continuousKSeminormIntegrand s.1
                    (unitCubeGradientEuclideanL2Field w) t) ≤
            (ENNReal.ofReal A) ^ (2 * s.1) *
              (((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
                    (2 : ℝ≥0∞) h) ^ 2 +
                ENNReal.ofReal (2 * s.1) *
                  ∫⁻ t in Set.Ioo (0 : ℝ) 1,
                    continuousKSeminormIntegrand s.1 h t) := by
  rcases exists_unitCubeDirichletContinuousKIntegralSplitBound d with
    ⟨A, honeA, hsplit⟩
  have hA : 0 < A := zero_lt_one.trans_le honeA
  have hzeroInv : 0 ≤ A⁻¹ := (inv_pos.mpr hA).le
  have hinvOne : A⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ honeA
  refine ⟨A, honeA, ?_⟩
  intro s h w hproblem
  rcases hsplit s h w hproblem with ⟨hlow, hroot⟩
  let out : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field w
  let Lout : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) out
  let Lin : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h
  let Ilow : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹, continuousKSeminormIntegrand s.1 out t
  let Iroot : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ), continuousKSeminormIntegrand s.1 out t
  let Iin : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 h t
  let p : ℝ≥0∞ := ENNReal.ofReal (2 * s.1)
  let c : ℝ≥0∞ := (ENNReal.ofReal A) ^ (2 * s.1)
  let q : ℝ≥0∞ :=
    ENNReal.ofReal ((Real.rpow A (2 * s.1) - 1) / (2 * s.1))
  have henergy : Lout ≤ Lin := by
    simpa only [Lout, Lin, out] using
      unitCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le h w hproblem
  have henergySq : Lout ^ 2 ≤ Lin ^ 2 := by
    gcongr
  have hlow' : Ilow ≤ c * Iin := by
    simpa only [Ilow, Iin, c, out] using hlow
  have hroot' : Iroot ≤ q * Lin ^ 2 := by
    simpa only [Iroot, q, Lin, out] using hroot
  have hinterval :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 out t) =
        Ilow + Iroot := by
    simpa only [Ilow, Iroot] using
      continuousKSeminormIntegral_eq_low_add_root hzeroInv hinvOne s.1 out
  have hcoefficient : 1 + p * q = c := by
    simpa only [p, q, c] using normalizedContinuousKRootCoefficient honeA s
  change Lout ^ 2 + p *
      (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 out t) ≤
    c * (Lin ^ 2 + p * Iin)
  calc
    Lout ^ 2 + p *
        (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 out t) =
      Lout ^ 2 + p * (Ilow + Iroot) := by rw [hinterval]
    _ ≤ Lin ^ 2 + p * (c * Iin + q * Lin ^ 2) := by
      have hscaled : p * (Ilow + Iroot) ≤
          p * (c * Iin + q * Lin ^ 2) := by
        simpa only [mul_comm] using
          (mul_le_mul_left (add_le_add hlow' hroot') p)
      exact add_le_add henergySq hscaled
    _ = (1 + p * q) * Lin ^ 2 + c * (p * Iin) := by ring
    _ = c * Lin ^ 2 + c * (p * Iin) := by rw [hcoefficient]
    _ = c * (Lin ^ 2 + p * Iin) := by ring

end

end HighContrast
end HCPolySupport
