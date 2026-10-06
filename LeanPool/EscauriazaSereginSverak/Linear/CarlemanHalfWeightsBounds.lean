/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfWeightsDerivatives

public section


open CKN CKN.Foundation.Parabolic Set Filter
open scoped Topology

noncomputable section

namespace ESS

/-- The half-space phase has squared gradient equal to the sum of its
tangential and normal contributions. -/
theorem halfSpacePhase_scalarGradSq (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) :
    scalarGradSq (halfSpacePhase a α) z =
      z.1 0 ^ 2 / (16 * z.2 ^ 2) + z.1 1 ^ 2 / (16 * z.2 ^ 2) +
        halfSpaceGradientTwo a α z ^ 2 := by
  rcases hz with ⟨_, ht⟩
  have ht0 : z.2 ≠ 0 := ne_of_gt ht.1
  have h0 := halfSpacePhase_spatialPartial a α ⟨by assumption, ht⟩ 0
  have h1 := halfSpacePhase_spatialPartial a α ⟨by assumption, ht⟩ 1
  have h2 := halfSpacePhase_spatialPartial a α ⟨by assumption, ht⟩ 2
  rw [scalarGradSq, Fin.sum_univ_three]
  simp [h0, h1, h2]
  field_simp [ht0]
  ring_nf

/-- The anisotropic spatial phase is at least one on the half-space slab. -/
theorem halfSpacePhase_anisotropicFactor_ge_one (α : ℝ)
    {z : ParabolicPoint} (hz : z ∈ halfSpaceDomain)
    (hα : 0 < α) :
    1 ≤ z.1 2 ^ (2 * α) / z.2 ^ α := by
  rcases hz with ⟨hx, ht⟩
  have hbase : 1 ≤ z.1 2 := le_of_lt hx
  have hexp : 0 ≤ 2 * α := by positivity
  have hxpow : 1 ≤ z.1 2 ^ (2 * α) := Real.one_le_rpow hbase hexp
  have htpowPos : 0 < z.2 ^ α := Real.rpow_pos_of_pos ht.1 α
  have htpowLe : z.2 ^ α ≤ 1 := Real.rpow_le_one (le_of_lt ht.1) ht.2.le hα.le
  have hdiv : 1 ≤ (z.1 2 ^ (2 * α)) / (z.2 ^ α) :=
    (one_le_div htpowPos).2 (le_trans htpowLe hxpow)
  exact hdiv

/-- The time derivative of the half-space phase gives the pointwise
gradient estimate used in `prop:carleman-halfspace`. -/
theorem halfSpacePhase_timeGradient_bound (a α : ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) (ha : 2 ≤ a) (hα : 0 < α) (hα1 : α ≤ 1) :
    z.2 * (2 * scalarGradSq (halfSpacePhase a α) z -
        timePartial (halfSpacePhase a α) z) ≤
      2 * z.2 * halfSpaceGradientTwo a α z ^ 2 +
        a * z.1 2 ^ (2 * α) / z.2 ^ α := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hxpos : 0 < z.1 2 := lt_trans (by norm_num) hx
  have hα0 : 0 ≤ α := hα.le
  have h1α0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hB : α + (1 - α) * z.2 ≤ 1 := by
    calc
      α + (1 - α) * z.2 ≤ α + (1 - α) * 1 := by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left ht.2.le h1α0) α
      _ = 1 := by ring
  have hX : 0 < z.1 2 ^ (2 * α) := Real.rpow_pos_of_pos hxpos (2 * α)
  have hta : 0 < z.2 ^ α := Real.rpow_pos_of_pos htpos α
  rw [halfSpacePhase_scalarGradSq a α ⟨hx, ht⟩,
    halfSpacePhase_timePartial a α ⟨hx, ht⟩]
  have hcoef : 0 ≤ a * z.1 2 ^ (2 * α) / z.2 ^ α := by
    positivity
  have hnormal :
      2 * z.2 * halfSpaceGradientTwo a α z ^ 2 +
          a * z.1 2 ^ (2 * α) / z.2 ^ α *
            (α + (1 - α) * z.2) ≤
        2 * z.2 * halfSpaceGradientTwo a α z ^ 2 +
          a * z.1 2 ^ (2 * α) / z.2 ^ α := by
    have := mul_le_mul_of_nonneg_left hB hcoef
    nlinarith only [this]
  have hpowScale : z.2 ^ (-α - 1 : ℝ) = (z.2 ^ α * z.2)⁻¹ := by
    rw [show (-α - 1 : ℝ) = -(α + 1) by ring,
      Real.rpow_neg htpos.le, Real.rpow_add htpos α 1, Real.rpow_one]
  let g : ℝ := halfSpaceGradientTwo a α z
  have hTan : z.2 * (2 * (z.1 0 ^ 2 / (16 * z.2 ^ 2) +
      z.1 1 ^ 2 / (16 * z.2 ^ 2)) -
      ((z.1 0 ^ 2 + z.1 1 ^ 2) / 8 * z.2 ^ (-2 : ℝ))) = 0 := by
    rw [Real.rpow_neg htpos.le (2 : ℝ)]
    field_simp [ht0]
    norm_num
    right
    ring
  have hNormalEq : z.2 * (2 * g ^ 2 +
      a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 1 : ℝ) *
        (α + (1 - α) * z.2)) =
      2 * z.2 * g ^ 2 + a * z.1 2 ^ (2 * α) / z.2 ^ α *
        (α + (1 - α) * z.2) := by
    rw [hpowScale]
    field_simp [ht0, ne_of_gt hta]
  change z.2 * (2 * (z.1 0 ^ 2 / (16 * z.2 ^ 2) +
      z.1 1 ^ 2 / (16 * z.2 ^ 2) + g ^ 2) -
    ((z.1 0 ^ 2 + z.1 1 ^ 2) / 8 * z.2 ^ (-2 : ℝ) -
      a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 1 : ℝ) *
        (α + (1 - α) * z.2))) ≤
    2 * z.2 * g ^ 2 + a * z.1 2 ^ (2 * α) / z.2 ^ α
  calc
    _ = z.2 * (2 * g ^ 2 + a * z.1 2 ^ (2 * α) *
          z.2 ^ (-α - 1 : ℝ) * (α + (1 - α) * z.2)) +
        z.2 * (2 * (z.1 0 ^ 2 / (16 * z.2 ^ 2) +
          z.1 1 ^ 2 / (16 * z.2 ^ 2)) -
          ((z.1 0 ^ 2 + z.1 1 ^ 2) / 8 * z.2 ^ (-2 : ℝ))) := by ring
    _ = 2 * z.2 * g ^ 2 + a * z.1 2 ^ (2 * α) / z.2 ^ α *
          (α + (1 - α) * z.2) := by rw [hTan, hNormalEq]; ring
    _ ≤ 2 * z.2 * g ^ 2 + a * z.1 2 ^ (2 * α) / z.2 ^ α := hnormal

/-- After cancellation of the two tangential coordinates, the half-space
commutator density has only the normal derivative term and a scalar weight
coefficient. -/
theorem halfSpacePhase_commutatorDensity_expand (a α : ℝ)
    (v : ParabolicPoint → ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) :
    carlemanCommutatorDensity (halfSpacePhase a α) v z =
      z.2 * spatialPartial v 2 z ^ 2 +
        4 * z.2 ^ 2 * spatialSecondPartial (halfSpacePhase a α) 2 2 z *
          spatialPartial v 2 z ^ 2 +
        z.2 ^ 2 * v z ^ 2 *
          (4 * spatialSecondPartial (halfSpacePhase a α) 2 2 z *
              halfSpaceGradientTwo a α z ^ 2 +
            (-(spatialPartial (halfSpacePhase a α) 0 z ^ 2 +
                spatialPartial (halfSpacePhase a α) 1 z ^ 2) / z.2) +
            timePartial (fun y => timePartial (halfSpacePhase a α) y) z -
            4 * ∑ i : Fin 3,
              spatialPartial (halfSpacePhase a α) i z *
                timePartial (fun y => spatialPartial (halfSpacePhase a α) i y) z -
            ∑ i : Fin 3, ∑ j : Fin 3,
              spatialSecondPartial
                (fun y => spatialSecondPartial (halfSpacePhase a α) i i y) j j z -
    scalarGradSq (halfSpacePhase a α) z / z.2 +
            timePartial (halfSpacePhase a α) z / z.2) := by
  rcases hz with ⟨_, ht⟩
  have ht0 : z.2 ≠ 0 := ne_of_gt ht.1
  have hαpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht.1 α)
  simp [carlemanCommutatorDensity, scalarGradSq, Fin.sum_univ_three,
    halfSpacePhase_spatialPartial a α ⟨by assumption, ht⟩,
    halfSpacePhase_spatialSecondPartial a α ⟨by assumption, ht⟩,
    halfSpacePhase_spatialFourthDiagonal a α ⟨by assumption, ht⟩,
    halfSpacePhase_timeSpatialPartial a α ⟨by assumption, ht⟩]
  field_simp [ht0, hαpow]
  ring_nf

@[expose] noncomputable def halfSpaceCommutatorScalarCoefficient
    (a α : ℝ) (z : ParabolicPoint) : ℝ :=
  4 * spatialSecondPartial (halfSpacePhase a α) 2 2 z *
      halfSpaceGradientTwo a α z ^ 2 -
    (spatialPartial (halfSpacePhase a α) 0 z ^ 2 +
      spatialPartial (halfSpacePhase a α) 1 z ^ 2) / z.2 +
    timePartial (fun y => timePartial (halfSpacePhase a α) y) z -
    4 * ∑ i : Fin 3,
      spatialPartial (halfSpacePhase a α) i z *
        timePartial (fun y => spatialPartial (halfSpacePhase a α) i y) z -
    ∑ i : Fin 3, ∑ j : Fin 3,
      spatialSecondPartial
        (fun y => spatialSecondPartial (halfSpacePhase a α) i i y) j j z -
    scalarGradSq (halfSpacePhase a α) z / z.2 +
    timePartial (halfSpacePhase a α) z / z.2

private theorem halfSpacePhase_scalarCoefficient_lower
    (a α : ℝ) {z : ParabolicPoint} (hz : z ∈ halfSpaceDomain)
    (ha : 2 ≤ a) (hαlo : 1 / 2 < α) (hαhi : α < 1) :
    a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ (α + 2) +
        halfSpaceGradientTwo a α z ^ 2 / z.2 ≤
      halfSpaceCommutatorScalarCoefficient a α z := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hxpos : 0 < z.1 2 := lt_trans (by norm_num) hx
  have hαpos : 0 < α := by linarith only [hαlo]
  have hθpos : 0 < 2 * α - 1 := by linarith only [hαlo]
  have h1αpos : 0 < 1 - α := by linarith only [hαhi]
  have h2α1pos : 0 < 3 - 2 * α := by linarith only [hαhi]
  have hpowα : 0 < z.2 ^ α := Real.rpow_pos_of_pos htpos α
  have hpowα0 : z.2 ^ α ≠ 0 := ne_of_gt hpowα
  have hpowPlus : 0 < z.2 ^ (α + 1) := Real.rpow_pos_of_pos htpos (α + 1)
  have hpowPlus0 : z.2 ^ (α + 1) ≠ 0 := ne_of_gt hpowPlus
  have hxexp : 0 < 2 * α + 2 := by linarith only [hαlo]
  have hxpow : 1 ≤ z.1 2 ^ (2 * α + 2) :=
    Real.one_le_rpow (le_of_lt hx) hxexp.le
  have htpow : z.2 ^ (α + 1) ≤ 1 :=
    Real.rpow_le_one (le_of_lt htpos) ht.2.le (by linarith only [hαlo])
  have hratio : 1 ≤ z.1 2 ^ (2 * α + 2) / z.2 ^ (α + 1) :=
    (one_le_div hpowPlus).2 (le_trans htpow hxpow)
  let g : ℝ := halfSpaceGradientTwo a α z
  let gt : ℝ := timePartial
    (fun y => spatialPartial (halfSpacePhase a α) 2 y) z
  let b : ℝ := α + (1 - α) * z.2
  let A1 : ℝ := -2 * g * gt
  let delta4 : ℝ :=
    2 * α * (2 * α - 1) * (2 * α - 2) * (2 * α - 3) * a *
      (1 - z.2) * z.1 2 ^ (2 * α - 4) / z.2 ^ α
  let A2 : ℝ := A1 - delta4 - g ^ 2 / z.2
  let A3 : ℝ := a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 2) *
    (α ^ 2 - (1 - α) ^ 2 * z.2)
  let H : ℝ := spatialSecondPartial (halfSpacePhase a α) 2 2 z
  have hgt : gt = -2 * α * a * z.1 2 ^ (2 * α - 1) *
      z.2 ^ (-α - 1) * b := by
    simpa [gt, b] using halfSpacePhase_timeSpatialPartial a α ⟨hx, ht⟩ 2
  have htimeScale : z.2 ^ (-α - 1 : ℝ) = (z.2 ^ α * z.2)⁻¹ := by
    rw [show (-α - 1 : ℝ) = -(α + 1) by ring,
      Real.rpow_neg htpos.le, Real.rpow_add htpos α 1, Real.rpow_one]
  have hInvScale : (z.2 ^ α)⁻¹ / z.2 = z.2 ^ (-α - 1 : ℝ) := by
    calc
      (z.2 ^ α)⁻¹ / z.2 = (z.2 ^ α * z.2)⁻¹ := by field_simp [ht0]
      _ = z.2 ^ (-α - 1 : ℝ) := htimeScale.symm
  have hg0 : 0 ≤ g := by
    dsimp [g, halfSpaceGradientTwo]
    have htime : 0 ≤ 1 - z.2 := sub_nonneg.mpr ht.2.le
    have hpow : 0 < z.1 2 ^ (2 * α - 1) := Real.rpow_pos_of_pos hxpos _
    positivity
  have hC0 : 0 ≤ 2 * α * a * z.1 2 ^ (2 * α - 1) *
      z.2 ^ (-α - 1 : ℝ) := by positivity
  have hBracket : 0 ≤ 2 * b - (1 - z.2) := by
    have hEq : 2 * b - (1 - z.2) =
        (2 * α - 1) + (3 - 2 * α) * z.2 := by dsimp [b]; ring
    rw [hEq]
    positivity
  have hBracketMin : 2 * α - 1 ≤ 2 * b - (1 - z.2) := by
    have hEq : 2 * b - (1 - z.2) =
        (2 * α - 1) + (3 - 2 * α) * z.2 := by dsimp [b]; ring
    rw [hEq]
    have hcoef : 0 ≤ 3 - 2 * α := le_of_lt h2α1pos
    nlinarith only [hcoef, htpos]
  have hA1Factor : A1 - g ^ 2 / z.2 =
      g * (2 * α * a * z.1 2 ^ (2 * α - 1) *
        z.2 ^ (-α - 1 : ℝ) * (2 * b - (1 - z.2))) := by
    change -2 * g * gt - g ^ 2 / z.2 = _
    rw [hgt]
    dsimp [g, halfSpaceGradientTwo]
    rw [htimeScale]
    field_simp [ht0, hpowα0]
  have hA1 : g ^ 2 / z.2 ≤ A1 := by
    have hnonneg := mul_nonneg hg0 (mul_nonneg hC0 hBracket)
    apply sub_nonneg.mp
    rw [hA1Factor]
    exact hnonneg
  have hA1strong :
      g * (2 * α * a * z.1 2 ^ (2 * α - 1) *
        z.2 ^ (-α - 1 : ℝ) * (2 * α - 1)) ≤ A1 - g ^ 2 / z.2 := by
    rw [hA1Factor]
    apply mul_le_mul_of_nonneg_left _ hg0
    exact mul_le_mul_of_nonneg_left hBracketMin hC0
  let F : ℝ := a * (2 * α - 1) * (1 - z.2) *
    z.1 2 ^ (2 * α - 4) / z.2 ^ α
  let R : ℝ := 4 * α ^ 2 * a * z.1 2 ^ (2 * α + 2) *
    z.2 ^ (-α - 1 : ℝ)
  let d : ℝ := 2 * α * (2 * α - 2) * (2 * α - 3)
  have hxprod :
      z.1 2 ^ (2 * α - 1) * z.1 2 ^ (2 * α - 1) =
        z.1 2 ^ (2 * α - 4) * z.1 2 ^ (2 * α + 2) := by
    calc
      _ = z.1 2 ^ ((2 * α - 1) + (2 * α - 1)) :=
        (Real.rpow_add hxpos _ _).symm
      _ = z.1 2 ^ ((2 * α - 4) + (2 * α + 2)) := by congr 1; ring
      _ = _ := Real.rpow_add hxpos _ _
  have hFR : g * (2 * α * a * z.1 2 ^ (2 * α - 1) *
      z.2 ^ (-α - 1 : ℝ) * (2 * α - 1)) = F * R := by
    dsimp [g, F, R, halfSpaceGradientTwo]
    rw [div_eq_mul_inv]
    ring_nf
    rw [show (z.1 2 ^ (-1 + α * 2)) ^ 2 =
        z.1 2 ^ (-4 + α * 2) * z.1 2 ^ (2 + α * 2) from by
          rw [pow_two]
          convert hxprod using 1 <;> congr 1 <;> ring_nf]
    field_simp [ht0, hpowα0]
  have hdelta : delta4 = F * d := by
    dsimp [delta4, F, d]
    ring
  have hA2Factor : F * (R - d) ≤ A2 := by
    calc
      F * (R - d) = F * R - F * d := by ring
      _ = g * (2 * α * a * z.1 2 ^ (2 * α - 1) *
            z.2 ^ (-α - 1 : ℝ) * (2 * α - 1)) - delta4 := by
        rw [hFR, hdelta]
      _ ≤ (A1 - g ^ 2 / z.2) - delta4 := by
        exact sub_le_sub_right hA1strong delta4
      _ = A2 := by dsimp [A2]; ring
  have hRas : R = 4 * α ^ 2 * a *
      (z.1 2 ^ (2 * α + 2) / z.2 ^ (α + 1)) := by
    dsimp [R]
    rw [show (-α - 1 : ℝ) = -(α + 1) by ring, Real.rpow_neg htpos.le]
    ring
  have hRlower : 8 * α ^ 2 ≤ R := by
    rw [hRas]
    have hcoef : 0 ≤ 4 * α ^ 2 := by positivity
    calc
      8 * α ^ 2 = 4 * α ^ 2 * 2 := by ring
      _ ≤ 4 * α ^ 2 * a := mul_le_mul_of_nonneg_left ha hcoef
      _ ≤ 4 * α ^ 2 * a *
            (z.1 2 ^ (2 * α + 2) / z.2 ^ (α + 1)) := by
        have hnonneg : 0 ≤ 4 * α ^ 2 * a := by positivity
        calc
          4 * α ^ 2 * a = 4 * α ^ 2 * a * 1 := by ring
          _ ≤ 4 * α ^ 2 * a *
              (z.1 2 ^ (2 * α + 2) / z.2 ^ (α + 1)) :=
            mul_le_mul_of_nonneg_left hratio hnonneg
  have hdidentity : 8 * α ^ 2 - d =
      4 * α * (2 * α - 1) * (3 - α) := by dsimp [d]; ring
  have hRminus : 0 ≤ R - d := by
    have hbase : 0 ≤ 8 * α ^ 2 - d := by
      have h3α : 0 < 3 - α := by linarith only [hαhi]
      rw [hdidentity]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        hαpos.le) hθpos.le) h3α.le
    nlinarith only [hRlower, hbase]
  have hF0 : 0 ≤ F := by
    change 0 ≤ a * (2 * α - 1) * (1 - z.2) *
      z.1 2 ^ (2 * α - 4) / z.2 ^ α
    have ht1 : 0 ≤ 1 - z.2 := sub_nonneg.mpr ht.2.le
    have hxpowPos : 0 < z.1 2 ^ (2 * α - 4) :=
      Real.rpow_pos_of_pos hxpos _
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (le_trans (by norm_num) ha)
        (le_of_lt hθpos)) ht1) hxpowPos.le) hpowα.le
  have hA2 : 0 ≤ A2 := le_trans (mul_nonneg hF0 hRminus) hA2Factor
  have hB3 : 2 * α - 1 ≤ α ^ 2 - (1 - α) ^ 2 * z.2 := by
    have hsq : 0 ≤ (1 - α) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left ht.2.le hsq
    nlinarith only [hmul]
  have htimeA3 : z.2 ^ (-α - 2 : ℝ) = (z.2 ^ (α + 2))⁻¹ := by
    rw [show (-α - 2 : ℝ) = -(α + 2) by ring,
      Real.rpow_neg htpos.le]
  have hA3coef : 0 ≤ a * z.1 2 ^ (2 * α) / z.2 ^ (α + 2) := by
    positivity
  have hA3 : a * (2 * α - 1) * z.1 2 ^ (2 * α) /
      z.2 ^ (α + 2) ≤ A3 := by
    dsimp [A3]
    rw [htimeA3]
    have hmul := mul_le_mul_of_nonneg_left hB3 hA3coef
    calc
      a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ (α + 2) =
          a * z.1 2 ^ (2 * α) / z.2 ^ (α + 2) * (2 * α - 1) := by ring
      _ ≤ a * z.1 2 ^ (2 * α) / z.2 ^ (α + 2) *
          (α ^ 2 - (1 - α) ^ 2 * z.2) := hmul
      _ = a * z.1 2 ^ (2 * α) * (z.2 ^ (α + 2))⁻¹ *
          (α ^ 2 - (1 - α) ^ 2 * z.2) := by rw [div_eq_mul_inv]
  have hH : 0 ≤ H := by
    rw [show H = spatialSecondPartial (halfSpacePhase a α) 2 2 z by rfl,
      halfSpacePhase_spatialSecondPartial a α ⟨hx, ht⟩]
    simp
    have htime : 0 ≤ 1 - z.2 := sub_nonneg.mpr ht.2.le
    positivity
  let q : ℝ := z.1 0 ^ 2 + z.1 1 ^ 2
  let p0 : ℝ := -z.1 0 / (4 * z.2)
  let p1 : ℝ := -z.1 1 / (4 * z.2)
  have hpowTwoNat : z.2 ^ (2 : ℝ) = z.2 ^ (2 : ℕ) := by
    norm_num [Real.rpow_natCast]
  have hpowThreeNat : z.2 ^ (3 : ℝ) = z.2 ^ (3 : ℕ) := by
    norm_num [Real.rpow_natCast]
  have htminus2 : z.2 ^ (-2 : ℝ) = (z.2 ^ 2)⁻¹ := by
    rw [Real.rpow_neg htpos.le (2 : ℝ)]
    rw [hpowTwoNat]
  have htminus3 : z.2 ^ (-3 : ℝ) = (z.2 ^ 3)⁻¹ := by
    rw [Real.rpow_neg htpos.le (3 : ℝ)]
    rw [hpowThreeNat]
  have hTangZero :
      -(((-z.1 0 / (4 * z.2)) ^ 2 + (-z.1 1 / (4 * z.2)) ^ 2) / z.2) -
        ((z.1 0 ^ 2 + z.1 1 ^ 2) / 4) * (z.2 ^ 3)⁻¹ -
        4 * ((-z.1 0 / (4 * z.2)) *
          (z.1 0 / 4 * (z.2 ^ 2)⁻¹) +
          (-z.1 1 / (4 * z.2)) *
            (z.1 1 / 4 * (z.2 ^ 2)⁻¹)) -
        ((-z.1 0 / (4 * z.2)) ^ 2 + (-z.1 1 / (4 * z.2)) ^ 2) / z.2 +
        (((z.1 0 ^ 2 + z.1 1 ^ 2) / 8) * (z.2 ^ 2)⁻¹) / z.2 = 0 := by
    field_simp [ht0]
    ring
  have htInv : z.2 ^ (-1 : ℝ) = z.2⁻¹ := by
    rw [Real.rpow_neg htpos.le, Real.rpow_one]
  have hnormalShift : z.2 ^ (-α - 1 : ℝ) / z.2 =
      z.2 ^ (-α - 2 : ℝ) := by
    calc
      z.2 ^ (-α - 1 : ℝ) / z.2 =
          z.2 ^ (-α - 1 : ℝ) * z.2 ^ (-1 : ℝ) := by
        rw [div_eq_mul_inv, ← htInv]
      _ = z.2 ^ ((-α - 1) + (-1 : ℝ)) :=
        (Real.rpow_add htpos _ _).symm
      _ = z.2 ^ (-α - 2 : ℝ) := by congr 1; ring
  have hnormalShiftB : z.2 ^ (-α - 1 : ℝ) * b / z.2 =
      z.2 ^ (-α - 2 : ℝ) * b := by
    calc
      z.2 ^ (-α - 1 : ℝ) * b / z.2 =
          (z.2 ^ (-α - 1 : ℝ) / z.2) * b := by ring
      _ = z.2 ^ (-α - 2 : ℝ) * b := by rw [hnormalShift]
  have hnormalTerm : a * z.1 2 ^ (2 * α) *
      z.2 ^ (-α - 1 : ℝ) * b / z.2 =
      a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 2 : ℝ) * b := by
    calc
      a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 1 : ℝ) * b / z.2 =
      a * z.1 2 ^ (2 * α) *
            (z.2 ^ (-α - 1 : ℝ) * b / z.2) := by ring
      _ = a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 2 : ℝ) * b := by
        rw [hnormalShiftB]
        ac_rfl
  have hNormalId : A3 =
      a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 2 : ℝ) *
        (α * (α + 1) + α * (1 - α) * z.2) -
      a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 1 : ℝ) *
        (α + (1 - α) * z.2) / z.2 := by
    dsimp [A3, b]
    have hnormalTerm' := hnormalTerm
    dsimp [b] at hnormalTerm'
    rw [hnormalTerm']
    ring
  have hCoeffExpand : halfSpaceCommutatorScalarCoefficient a α z =
      4 * spatialSecondPartial (halfSpacePhase a α) 2 2 z *
          halfSpaceGradientTwo a α z ^ 2 -
        (p0 ^ 2 + p1 ^ 2) / z.2 +
        (-(q / 4) * z.2 ^ (-3 : ℝ) +
          a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 2 : ℝ) *
            (α * (α + 1) + α * (1 - α) * z.2)) -
        4 * (p0 * (z.1 0 / 4 * z.2 ^ (-2 : ℝ)) +
          p1 * (z.1 1 / 4 * z.2 ^ (-2 : ℝ)) +
          halfSpaceGradientTwo a α z *
            (-2 * α * a * z.1 2 ^ (2 * α - 1) *
              z.2 ^ (-α - 1 : ℝ) * (α + (1 - α) * z.2))) -
        delta4 - ((p0 ^ 2 + p1 ^ 2) + halfSpaceGradientTwo a α z ^ 2) / z.2 +
        (q / 8 * z.2 ^ (-2 : ℝ) -
          a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 1 : ℝ) *
            (α + (1 - α) * z.2)) / z.2 := by
    simp [halfSpaceCommutatorScalarCoefficient, scalarGradSq, Fin.sum_univ_three,
      p0, p1, q, delta4, halfSpacePhase_spatialPartial a α ⟨hx, ht⟩,
      halfSpacePhase_spatialSecondPartial a α ⟨hx, ht⟩,
      halfSpacePhase_spatialFourthDiagonal a α ⟨hx, ht⟩,
      halfSpacePhase_timePartial a α ⟨hx, ht⟩,
      halfSpacePhase_timeSecondPartial a α ⟨hx, ht⟩,
      halfSpacePhase_timeSpatialPartial a α ⟨hx, ht⟩]
  have hA1A2 : A1 + A2 =
      -4 * g * (-2 * α * a * z.1 2 ^ (2 * α - 1) *
        z.2 ^ (-α - 1 : ℝ) * (α + (1 - α) * z.2)) -
      delta4 - g ^ 2 / z.2 := by
    dsimp [A1, A2, gt]
    rw [halfSpacePhase_timeSpatialPartial a α ⟨hx, ht⟩ 2]
    simp
    ring
  have hA1A2Sum : 4 * H * g ^ 2 + A1 + A2 + A3 =
      4 * H * g ^ 2 +
        (-4 * g * (-2 * α * a * z.1 2 ^ (2 * α - 1) *
          z.2 ^ (-α - 1 : ℝ) * (α + (1 - α) * z.2)) -
          delta4 - g ^ 2 / z.2) + A3 := by
    calc
      4 * H * g ^ 2 + A1 + A2 + A3 =
          4 * H * g ^ 2 + (A1 + A2) + A3 := by ring
      _ = 4 * H * g ^ 2 +
          (-4 * g * (-2 * α * a * z.1 2 ^ (2 * α - 1) *
            z.2 ^ (-α - 1 : ℝ) * (α + (1 - α) * z.2)) -
            delta4 - g ^ 2 / z.2) + A3 := by
        rw [hA1A2]
  have hCoeffId : halfSpaceCommutatorScalarCoefficient a α z =
      4 * H * g ^ 2 + A1 + A2 + A3 := by
    calc
      halfSpaceCommutatorScalarCoefficient a α z =
          4 * spatialSecondPartial (halfSpacePhase a α) 2 2 z *
            halfSpaceGradientTwo a α z ^ 2 - (p0 ^ 2 + p1 ^ 2) / z.2 +
            (-(q / 4) * z.2 ^ (-3 : ℝ) +
              a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 2 : ℝ) *
                (α * (α + 1) + α * (1 - α) * z.2)) -
            4 * (p0 * (z.1 0 / 4 * z.2 ^ (-2 : ℝ)) +
              p1 * (z.1 1 / 4 * z.2 ^ (-2 : ℝ)) +
              halfSpaceGradientTwo a α z *
                (-2 * α * a * z.1 2 ^ (2 * α - 1) *
                  z.2 ^ (-α - 1 : ℝ) * b)) -
            delta4 - ((p0 ^ 2 + p1 ^ 2) + halfSpaceGradientTwo a α z ^ 2) / z.2 +
            (q / 8 * z.2 ^ (-2 : ℝ) -
              a * z.1 2 ^ (2 * α) * z.2 ^ (-α - 1 : ℝ) * b) / z.2 := hCoeffExpand
      _ = 4 * H * g ^ 2 +
          (-4 * g * (-2 * α * a * z.1 2 ^ (2 * α - 1) *
            z.2 ^ (-α - 1 : ℝ) * (α + (1 - α) * z.2)) -
            delta4 - g ^ 2 / z.2) + A3 := by
        dsimp [p0, p1, q, H, g, delta4, halfSpaceGradientTwo]
          at hTangZero ⊢
        rw [htminus2, htminus3] at ⊢
        rw [hNormalId]
        linear_combination hTangZero
      _ = 4 * H * g ^ 2 + A1 + A2 + A3 := hA1A2Sum.symm
  calc
    a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ (α + 2) + g ^ 2 / z.2
        ≤ A3 + A1 + A2 + 4 * H * g ^ 2 := by
          nlinarith only [hA1, hA2, hA3, hH]
    _ = halfSpaceCommutatorScalarCoefficient a α z := by
      rw [hCoeffId]
      ring

/-- The half-space Carleman commutator density has the pointwise lower bound
used in `prop:carleman-halfspace`. -/
theorem halfSpacePhase_commutatorDensity_lower (a α : ℝ)
    (v : ParabolicPoint → ℝ) {z : ParabolicPoint}
    (hz : z ∈ halfSpaceDomain) (ha : 2 ≤ a)
    (hαlo : 1 / 2 < α) (hαhi : α < 1) :
    a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ α * v z ^ 2 +
        z.2 * halfSpaceGradientTwo a α z ^ 2 * v z ^ 2 ≤
      carlemanCommutatorDensity (halfSpacePhase a α) v z := by
  rcases hz with ⟨hx, ht⟩
  have htpos : 0 < z.2 := ht.1
  have ht0 : z.2 ≠ 0 := ne_of_gt htpos
  have hαpos : 0 < α := by linarith only [hαlo]
  have hpowα : 0 < z.2 ^ α := Real.rpow_pos_of_pos htpos α
  have hpowα0 : z.2 ^ α ≠ 0 := ne_of_gt hpowα
  have hpowTwoNat : z.2 ^ (2 : ℝ) = z.2 ^ (2 : ℕ) := by
    norm_num [Real.rpow_natCast]
  have hpowAdd : z.2 ^ (α + 2) = z.2 ^ α * z.2 ^ 2 := by
    calc
      z.2 ^ (α + 2) = z.2 ^ (α + (2 : ℝ)) := by ring
      _ = z.2 ^ α * z.2 ^ (2 : ℝ) := Real.rpow_add htpos α 2
      _ = z.2 ^ α * z.2 ^ 2 := by rw [hpowTwoNat]
  have hscale1 :
      z.2 ^ 2 * (a * (2 * α - 1) * z.1 2 ^ (2 * α) /
        z.2 ^ (α + 2)) =
      a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ α := by
    rw [div_eq_mul_inv, div_eq_mul_inv, hpowAdd]
    field_simp [ht0, hpowα0]
  have hscale2 : z.2 ^ 2 * (halfSpaceGradientTwo a α z ^ 2 / z.2) =
      z.2 * halfSpaceGradientTwo a α z ^ 2 := by
    field_simp [ht0]
  have hcoeff := halfSpacePhase_scalarCoefficient_lower
    a α ⟨hx, ht⟩ ha hαlo hαhi
  have hcoeffScaled :
      a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ α * v z ^ 2 +
        z.2 * halfSpaceGradientTwo a α z ^ 2 * v z ^ 2 ≤
      z.2 ^ 2 * v z ^ 2 *
        halfSpaceCommutatorScalarCoefficient a α z := by
    calc
      a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ α * v z ^ 2 +
          z.2 * halfSpaceGradientTwo a α z ^ 2 * v z ^ 2 =
          (a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ α +
            z.2 * halfSpaceGradientTwo a α z ^ 2) * v z ^ 2 := by ring
      _ = z.2 ^ 2 * v z ^ 2 *
          (a * (2 * α - 1) * z.1 2 ^ (2 * α) /
              z.2 ^ (α + 2) +
            halfSpaceGradientTwo a α z ^ 2 / z.2) := by
        rw [← hscale1, ← hscale2]
        ring
      _ ≤ z.2 ^ 2 * v z ^ 2 *
          halfSpaceCommutatorScalarCoefficient a α z := by
        apply mul_le_mul_of_nonneg_left hcoeff
        positivity
  have hnormalTerm : 0 ≤ z.2 * spatialPartial v 2 z ^ 2 := by
    positivity
  have hsecondTerm :
      0 ≤ 4 * z.2 ^ 2 *
        spatialSecondPartial (halfSpacePhase a α) 2 2 z *
        spatialPartial v 2 z ^ 2 := by
    have hθpos : 0 < 2 * α - 1 := by linarith only [hαlo]
    have hH : 0 ≤ spatialSecondPartial (halfSpacePhase a α) 2 2 z := by
      rw [halfSpacePhase_spatialSecondPartial a α ⟨hx, ht⟩ 2 2]
      simp
      have htime : 0 ≤ 1 - z.2 := sub_nonneg.mpr ht.2.le
      have hxpos : 0 < z.1 2 := lt_trans (by norm_num) hx
      have hxpow : 0 < z.1 2 ^ (2 * α - 2) :=
        Real.rpow_pos_of_pos hxpos _
      positivity
    positivity
  have hInline :
      4 * spatialSecondPartial (halfSpacePhase a α) 2 2 z *
          halfSpaceGradientTwo a α z ^ 2 +
        -(spatialPartial (halfSpacePhase a α) 0 z ^ 2 +
          spatialPartial (halfSpacePhase a α) 1 z ^ 2) / z.2 +
        timePartial (fun y => timePartial (halfSpacePhase a α) y) z -
        4 * ∑ i : Fin 3,
          spatialPartial (halfSpacePhase a α) i z *
            timePartial (fun y => spatialPartial (halfSpacePhase a α) i y) z -
        ∑ i : Fin 3, ∑ j : Fin 3,
          spatialSecondPartial
            (fun y => spatialSecondPartial (halfSpacePhase a α) i i y) j j z -
        scalarGradSq (halfSpacePhase a α) z / z.2 +
        timePartial (halfSpacePhase a α) z / z.2 =
      halfSpaceCommutatorScalarCoefficient a α z := by
    unfold halfSpaceCommutatorScalarCoefficient
    ring
  rw [halfSpacePhase_commutatorDensity_expand a α v ⟨hx, ht⟩]
  rw [hInline]
  calc
    _ ≤ z.2 ^ 2 * v z ^ 2 *
        halfSpaceCommutatorScalarCoefficient a α z := hcoeffScaled
    _ ≤ z.2 * spatialPartial v 2 z ^ 2 +
        4 * z.2 ^ 2 *
          spatialSecondPartial (halfSpacePhase a α) 2 2 z *
          spatialPartial v 2 z ^ 2 +
        z.2 ^ 2 * v z ^ 2 *
          halfSpaceCommutatorScalarCoefficient a α z := by
      have hderiv := add_nonneg hnormalTerm hsecondTerm
      calc
        _ = 0 +
            z.2 ^ 2 * v z ^ 2 *
              halfSpaceCommutatorScalarCoefficient a α z := by ring
        _ ≤ (z.2 * spatialPartial v 2 z ^ 2 +
              4 * z.2 ^ 2 *
                spatialSecondPartial (halfSpacePhase a α) 2 2 z *
                spatialPartial v 2 z ^ 2) +
            z.2 ^ 2 * v z ^ 2 *
              halfSpaceCommutatorScalarCoefficient a α z :=
          by
            simpa using add_le_add_right hderiv
              (z.2 ^ 2 * v z ^ 2 *
                halfSpaceCommutatorScalarCoefficient a α z)
        _ = _ := by ring

/-- The real-variable absorption used at the end of
`prop:carleman-halfspace`. -/
theorem halfSpaceAbsorption (P U V G D X a θ : ℝ)
    (hθ : 0 < θ) (ha : 2 ≤ a) (hV0 : 0 ≤ V) (hVU : V ≤ U)
    (hG0 : 0 ≤ G) (hMass : a * θ * U + G ≤ P)
    (hX : |X| ≤ Real.sqrt (V * P))
    (hD : D ≤ |X| + 2 * G + a * U) :
    a * V + 2 * D ≤ (5 + 7 / (2 * θ)) * P := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hU0 : 0 ≤ U := le_trans hV0 hVU
  have hA0 : 0 ≤ a * θ * U := by positivity
  have hP0 : 0 ≤ P := le_trans (add_nonneg hA0 hG0) hMass
  have hA : a * θ * U ≤ P := by nlinarith only [hMass, hG0]
  have haθ : 0 < a * θ := by positivity
  have hAU : a * U ≤ P / θ := by
    apply (le_div_iff₀ hθ).2
    nlinarith only [hA]
  have hAV : a * V ≤ P / θ := by
    calc
      a * V ≤ a * U := mul_le_mul_of_nonneg_left hVU ha0
      _ ≤ P / θ := hAU
  have hG : G ≤ P := by nlinarith only [hA0, hG0, hMass]
  have hVP : V * P ≤ U * P := mul_le_mul_of_nonneg_right hVU hP0
  have hSqrtMono : Real.sqrt (V * P) ≤ Real.sqrt (U * P) :=
    Real.sqrt_le_sqrt hVP
  let A : ℝ := a * θ * U
  let B : ℝ := P / (a * θ)
  have hAA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hAB : A * B = U * P := by
    dsimp [A, B]
    field_simp [ne_of_gt haθ]
  have hYoung : Real.sqrt (U * P) ≤ (A + B) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [sq_nonneg (A - B), hAB]
  have hA_le : A ≤ P := by dsimp [A]; exact hA
  have hDen : 0 < 2 * θ := by positivity
  have hDenLe : 2 * θ ≤ a * θ := by nlinarith only [ha, hθ]
  have hBbound : B ≤ P / (2 * θ) := by
    dsimp [B]
    exact div_le_div_of_nonneg_left hP0 hDen hDenLe
  have hCross : |X| ≤ (1 / 2 + 1 / (4 * θ)) * P := by
    calc
      |X| ≤ Real.sqrt (V * P) := hX
      _ ≤ Real.sqrt (U * P) := hSqrtMono
      _ ≤ (A + B) / 2 := hYoung
      _ ≤ (P + P / (2 * θ)) / 2 := by
        gcongr
      _ = (1 / 2 + 1 / (4 * θ)) * P := by ring
  have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have hDscaled : a * V + 2 * D ≤ a * V + 2 * (|X| + 2 * G + a * U) :=
    by simpa [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hD h2nonneg) (a * V)
  calc
    a * V + 2 * D ≤ a * V + 2 * (|X| + 2 * G + a * U) := hDscaled
    _ ≤ P / θ + 2 * ((1 / 2 + 1 / (4 * θ)) * P) + 4 * P + 2 * (P / θ) := by
      nlinarith only [hAV, hCross, hG, hAU]
    _ = (5 + 7 / (2 * θ)) * P := by ring

end ESS
