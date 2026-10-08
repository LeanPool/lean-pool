/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormGood

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormPrimal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem diagonalWeakNorm_primal_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hrho2 : rho < 2)
    (hs : rho / 2 < s) (hs1 : s ≤ 1) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) {a : CoeffSpace d} (p r : Vec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
      if diagonalWeakMaximum rho q t E a = ⊤ then ⊤ else
        ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
              (diagonalWeakCellSum q t H s E a +
                diagonalWeakAverageSum q t H s rho E a) +
            (16 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
                diagonalWeakMetricFactor m E) *
              (if delta < (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else
                  (3 : ℝ) ^ (-((s - rho / 2) * (H : ℝ)))) *
                diagonalWeakEnergy hq t a p r) := by
  by_cases htop : diagonalWeakMaximum rho q t E a = ⊤
  · rw [ite_eq_left htop]
    exact le_top
  rw [ite_eq_right htop]
  let K := diagonalWeakMetricFactor m E
  let L := diagonalWeakLoadMinus E p r
  let U := diagonalWeakCellSum q t H s E a +
    diagonalWeakAverageSum q t H s rho E a
  let M := (diagonalWeakMaximum rho q t E a).toReal
  let En := diagonalWeakEnergy hq t a p r
  let G := (Real.sqrt delta)⁻¹ / (2 * s - rho)
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hL0 : 0 ≤ L := diagonalWeakLoadMinus_nonneg E p r
  have hU0 : 0 ≤ U := add_nonneg
    (diagonalWeakCellSum_nonneg q t H s E a)
    (diagonalWeakAverageSum_nonneg q t H s rho E a)
  have hEn0 : 0 ≤ En := diagonalWeakEnergy_nonneg hq t a p r
  have hparams : 0 < 2 * s - rho ∧ rho < 2 :=
    ⟨by linarith only [hs], hrho2⟩
  have hden : 0 < 2 * s - rho := hparams.1
  have hG0 : 0 ≤ G := div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hden.le
  have hroot2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  by_cases hbad : delta < M
  · rw [ite_eq_left hbad]
    have hraw := normalized_adaptedWeakSeminorm_bad_le hq t hsymm hsq hm
      hE hEpd hrho hs hs1 hdelta hdelta1 p r htop hbad
    have hrootM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
    have hcoeff :
        (Real.sqrt 2 * K * En) * (8 * G * Real.sqrt M) ≤
          16 * G * K * Real.sqrt M * En := by
      have hrest0 : 0 ≤ 8 * G * K * Real.sqrt M * En := by positivity
      calc
        (Real.sqrt 2 * K * En) * (8 * G * Real.sqrt M) =
            Real.sqrt 2 * (8 * G * K * Real.sqrt M * En) := by ring
        _ ≤ 2 * (8 * G * K * Real.sqrt M * En) :=
          mul_le_mul_of_nonneg_right hroot2 hrest0
        _ = 16 * G * K * Real.sqrt M * En := by ring
    have hrecent0 : 0 ≤ 16 * K * L * U := by positivity
    have hfinal :
        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
          adaptedWeakSeminorm q t s (fun x =>
            blockMatVecMul (blockDiag S S⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r))) ≤
          ENNReal.ofReal
            (16 * K * L * U + 16 * G * K * Real.sqrt M * En) := by
      calc
        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
            adaptedWeakSeminorm q t s (fun x =>
              blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r))) ≤
          ENNReal.ofReal ((Real.sqrt 2 * K * En) *
            (8 * G * Real.sqrt M)) := by
          dsimp only [K, En, G, M]
          convert hraw using 1
          congr 1
          ring
        _ ≤ ENNReal.ofReal (16 * G * K * Real.sqrt M * En) :=
          ENNReal.ofReal_le_ofReal hcoeff
        _ ≤ ENNReal.ofReal
            (16 * K * L * U + 16 * G * K * Real.sqrt M * En) :=
          ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hrecent0)
    convert hfinal using 1
    congr 1
    dsimp only [K, L, U, M, En, G]
    ring
  · rw [ite_eq_right hbad]
    have hgood : M ≤ delta := le_of_not_gt hbad
    have hraw := normalized_adaptedWeakSeminorm_good_le hq t H hsymm hsq hm
      hE hEpd hrho hs hs1 hdelta hdelta1 p r htop hgood
    let R := (3 : ℝ) ^ (-((s - rho / 2) * (H : ℝ)))
    let Rnext := (3 : ℝ) ^
      (-((s - rho / 2) * ((H + 1 : ℕ) : ℝ)))
    have ha0 : 0 < s - rho / 2 := by linarith only [hs]
    have hR0 : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
    have hRnext0 : 0 ≤ Rnext := Real.rpow_nonneg (by norm_num) _
    have hRnext : Rnext ≤ R := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        push_cast
        have hcast : (H : ℝ) ≤ (H : ℝ) + 1 := by linarith only []
        exact neg_le_neg (mul_le_mul_of_nonneg_left hcast ha0.le))
    have hrecent : 4 * K * L * U ≤ 16 * K * L * U := by
      have hprod0 : 0 ≤ K * L * U := by positivity
      linarith only [hprod0]
    have hold : (Real.sqrt 2 * K * En) * (8 * G * Rnext) ≤
        16 * G * K * R * En := by
      have hcoef : Real.sqrt 2 * Rnext ≤ 2 * R := by
        calc
          Real.sqrt 2 * Rnext ≤ 2 * Rnext :=
            mul_le_mul_of_nonneg_right hroot2 hRnext0
          _ ≤ 2 * R := mul_le_mul_of_nonneg_left hRnext (by norm_num)
      have hrest0 : 0 ≤ 8 * G * K * En := by positivity
      calc
        (Real.sqrt 2 * K * En) * (8 * G * Rnext) =
            (Real.sqrt 2 * Rnext) * (8 * G * K * En) := by ring
        _ ≤ (2 * R) * (8 * G * K * En) :=
          mul_le_mul_of_nonneg_right hcoef hrest0
        _ = 16 * G * K * R * En := by ring
    have hraw' :
        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
            adaptedWeakSeminorm q t s (fun x =>
              blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r))) ≤
          ENNReal.ofReal
            (4 * K * L * U + (Real.sqrt 2 * K * En) * (8 * G * Rnext)) := by
      dsimp only [K, L, U, M, En, G, Rnext]
      convert hraw using 1
      congr 1
      ring
    have hfinal := hraw'.trans
      (ENNReal.ofReal_le_ofReal (add_le_add hrecent hold))
    convert hfinal using 1
    congr 1
    dsimp only [K, L, U, G, R, En]
    ring_nf

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The maximum-group coefficient at a released split level.  It is `16` at the
fixed level. -/
@[expose]
def maxGroupConstantAtLevel (delta : ℝ) : ℝ :=
  8 * (1 + Real.sqrt delta) * max 1 (Real.sqrt delta)⁻¹

theorem zero_le_maxGroupConstantAtLevel (delta : ℝ) :
    0 ≤ maxGroupConstantAtLevel delta := by
  have hsd : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hmax : (0 : ℝ) ≤ max 1 (Real.sqrt delta)⁻¹ :=
    le_trans zero_le_one (le_max_left _ _)
  rw [maxGroupConstantAtLevel]
  positivity

/-- The primal all-scale estimate at a released split level. -/
theorem diagonalWeakNorm_primal_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho)
    (hs : rho / 2 < s) (hs1 : s ≤ 1) (hdelta : 0 < delta)
    {a : CoeffSpace d} (p r : Vec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
      if diagonalWeakMaximum rho q t E a = ⊤ then ⊤ else
        ENNReal.ofReal
          (recentConstantAtLevel delta * diagonalWeakMetricFactor m E *
              diagonalWeakLoadMinus E p r *
              (diagonalWeakCellSum q t H s E a +
                diagonalWeakAverageSum q t H s rho E a) +
            (maxGroupConstantAtLevel delta / (2 * s - rho) *
                diagonalWeakMetricFactor m E) *
              (if delta < (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else
                  (3 : ℝ) ^ (-((s - rho / 2) * (H : ℝ)))) *
                diagonalWeakEnergy hq t a p r) := by
  by_cases htop : diagonalWeakMaximum rho q t E a = ⊤
  · rw [ite_eq_left htop]
    exact le_top
  rw [ite_eq_right htop]
  set K : ℝ := diagonalWeakMetricFactor m E with hKdef
  set L : ℝ := diagonalWeakLoadMinus E p r with hLdef
  set U : ℝ := diagonalWeakCellSum q t H s E a +
    diagonalWeakAverageSum q t H s rho E a with hUdef
  set M : ℝ := (diagonalWeakMaximum rho q t E a).toReal with hMdef
  set En : ℝ := diagonalWeakEnergy hq t a p r with hEndef
  set crec : ℝ := recentConstantAtLevel delta with hcrecdef
  set cmax : ℝ := maxGroupConstantAtLevel delta with hcmaxdef
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hL0 : 0 ≤ L := diagonalWeakLoadMinus_nonneg E p r
  have hU0 : 0 ≤ U := add_nonneg
    (diagonalWeakCellSum_nonneg q t H s E a)
    (diagonalWeakAverageSum_nonneg q t H s rho E a)
  have hEn0 : 0 ≤ En := diagonalWeakEnergy_nonneg hq t a p r
  have hcrec0 : 0 ≤ crec := zero_le_recentConstantAtLevel delta
  have hden : 0 < 2 * s - rho := by linarith only [hs]
  have hsd0 : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsdinv0 : (0 : ℝ) ≤ (Real.sqrt delta)⁻¹ :=
    inv_nonneg.mpr hsd0
  have hmax1 : (1 : ℝ) ≤ max 1 (Real.sqrt delta)⁻¹ := le_max_left _ _
  have hmaxinv : (Real.sqrt delta)⁻¹ ≤ max 1 (Real.sqrt delta)⁻¹ :=
    le_max_right _ _
  have hroot2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hroot20 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hrecent0 : 0 ≤ crec * K * L * U := by positivity
  have ha0 : 0 < s - rho / 2 := by linarith only [hs]
  by_cases hbad : delta < M
  · rw [ite_eq_left hbad]
    have hraw := normalized_adaptedWeakSeminorm_bad_at_level_le hq t hsymm hsq
      hm hE hEpd hrho hs hs1 hdelta p r htop hbad
    have hM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
    have hnum : Real.sqrt 2 * (4 * (1 + Real.sqrt delta) *
        (Real.sqrt delta)⁻¹) ≤ cmax := by
      rw [hcmaxdef, maxGroupConstantAtLevel]
      have hstep : Real.sqrt 2 * (4 * (1 + Real.sqrt delta) *
          (Real.sqrt delta)⁻¹) ≤
          2 * (4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹) :=
        mul_le_mul_of_nonneg_right hroot2 (by positivity)
      have hstep2 : 2 * (4 * (1 + Real.sqrt delta) *
          (Real.sqrt delta)⁻¹) ≤
          8 * (1 + Real.sqrt delta) * max 1 (Real.sqrt delta)⁻¹ := by
        have hb0 : (0 : ℝ) ≤ 8 * (1 + Real.sqrt delta) := by positivity
        calc
          2 * (4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹) =
              (8 * (1 + Real.sqrt delta)) * (Real.sqrt delta)⁻¹ := by ring
          _ ≤ (8 * (1 + Real.sqrt delta)) * max 1 (Real.sqrt delta)⁻¹ :=
            mul_le_mul_of_nonneg_left hmaxinv hb0
          _ = 8 * (1 + Real.sqrt delta) * max 1 (Real.sqrt delta)⁻¹ := rfl
      linarith only [hstep, hstep2]
    have hcoeff : (Real.sqrt 2 * K * En) *
        (4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
          Real.sqrt M) ≤
        (cmax / (2 * s - rho) * K) * Real.sqrt M * En := by
      have hrest : (0 : ℝ) ≤ K * Real.sqrt M * En := by positivity
      have hkey : (Real.sqrt 2 * (4 * (1 + Real.sqrt delta) *
          (Real.sqrt delta)⁻¹)) * (K * Real.sqrt M * En) ≤
          cmax * (K * Real.sqrt M * En) :=
        mul_le_mul_of_nonneg_right hnum hrest
      have hLform : (Real.sqrt 2 * K * En) *
          (4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹ /
            (2 * s - rho) * Real.sqrt M) =
          ((Real.sqrt 2 * (4 * (1 + Real.sqrt delta) *
            (Real.sqrt delta)⁻¹)) * (K * Real.sqrt M * En)) /
              (2 * s - rho) := by
        field_simp
      have hRform : (cmax / (2 * s - rho) * K) * Real.sqrt M * En =
          (cmax * (K * Real.sqrt M * En)) / (2 * s - rho) := by
        field_simp
      rw [hLform, hRform]
      exact (div_le_div_iff_of_pos_right hden).2 hkey
    calc
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
          adaptedWeakSeminorm q t s (fun x =>
            blockMatVecMul (blockDiag S S⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r))) ≤
          ENNReal.ofReal ((Real.sqrt 2 * K * En) *
            (4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹ /
              (2 * s - rho) * Real.sqrt M)) := hraw
      _ ≤ ENNReal.ofReal ((cmax / (2 * s - rho) * K) * Real.sqrt M * En) :=
        ENNReal.ofReal_le_ofReal hcoeff
      _ ≤ ENNReal.ofReal (crec * K * L * U +
          (cmax / (2 * s - rho) * K) * Real.sqrt M * En) :=
        ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hrecent0)
  · rw [ite_eq_right hbad]
    have hgood : M ≤ delta := le_of_not_gt hbad
    have hraw := normalized_adaptedWeakSeminorm_good_at_level_le hq t H hsymm
      hsq hm hE hEpd hrho hs hs1 p r htop hgood
    set R : ℝ := (3 : ℝ) ^ (-((s - rho / 2) * (H : ℝ))) with hRdef
    set Rnext : ℝ := (3 : ℝ) ^ (-((s - rho / 2) * ((H + 1 : ℕ) : ℝ)))
      with hRnextdef
    have hR0 : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
    have hRnext0 : 0 ≤ Rnext := Real.rpow_nonneg (by norm_num) _
    have hRnext : Rnext ≤ R := by
      rw [hRdef, hRnextdef]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      push_cast
      have hcast : (H : ℝ) ≤ (H : ℝ) + 1 := by linarith only []
      exact neg_le_neg (mul_le_mul_of_nonneg_left hcast ha0.le)
    have hnum : Real.sqrt 2 * (4 * (1 + Real.sqrt delta)) ≤ cmax := by
      rw [hcmaxdef, maxGroupConstantAtLevel]
      have hstep : Real.sqrt 2 * (4 * (1 + Real.sqrt delta)) ≤
          2 * (4 * (1 + Real.sqrt delta)) :=
        mul_le_mul_of_nonneg_right hroot2 (by positivity)
      have hb0 : (0 : ℝ) ≤ 8 * (1 + Real.sqrt delta) := by positivity
      calc
        Real.sqrt 2 * (4 * (1 + Real.sqrt delta)) ≤
            2 * (4 * (1 + Real.sqrt delta)) := hstep
        _ = 8 * (1 + Real.sqrt delta) := by ring
        _ ≤ 8 * (1 + Real.sqrt delta) * max 1 (Real.sqrt delta)⁻¹ :=
          le_mul_of_one_le_right hb0 hmax1
    have hcoeff : (Real.sqrt 2 * K * En) *
        (4 * (1 + Real.sqrt delta) / (2 * s - rho) * Rnext) ≤
        (cmax / (2 * s - rho) * K) * R * En := by
      have hstepR : (Real.sqrt 2 * (4 * (1 + Real.sqrt delta))) * Rnext ≤
          cmax * R := by
        have h1 : (Real.sqrt 2 * (4 * (1 + Real.sqrt delta))) * Rnext ≤
            (Real.sqrt 2 * (4 * (1 + Real.sqrt delta))) * R :=
          mul_le_mul_of_nonneg_left hRnext (by positivity)
        have h2 : (Real.sqrt 2 * (4 * (1 + Real.sqrt delta))) * R ≤
            cmax * R := mul_le_mul_of_nonneg_right hnum hR0
        linarith only [h1, h2]
      have hrest : (0 : ℝ) ≤ K * En := by positivity
      have hkey : ((Real.sqrt 2 * (4 * (1 + Real.sqrt delta))) * Rnext) *
          (K * En) ≤ (cmax * R) * (K * En) :=
        mul_le_mul_of_nonneg_right hstepR hrest
      have hLform : (Real.sqrt 2 * K * En) *
          (4 * (1 + Real.sqrt delta) / (2 * s - rho) * Rnext) =
          (((Real.sqrt 2 * (4 * (1 + Real.sqrt delta))) * Rnext) *
            (K * En)) / (2 * s - rho) := by
        field_simp
      have hRform : (cmax / (2 * s - rho) * K) * R * En =
          ((cmax * R) * (K * En)) / (2 * s - rho) := by
        field_simp
      rw [hLform, hRform]
      exact (div_le_div_iff_of_pos_right hden).2 hkey
    calc
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
          adaptedWeakSeminorm q t s (fun x =>
            blockMatVecMul (blockDiag S S⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r))) ≤
          ENNReal.ofReal (crec * K * L * U +
            (Real.sqrt 2 * K * En) *
              (4 * (1 + Real.sqrt delta) / (2 * s - rho) * Rnext)) := hraw
      _ ≤ ENNReal.ofReal (crec * K * L * U +
          (cmax / (2 * s - rho) * K) * R * En) :=
        ENNReal.ofReal_le_ofReal (add_le_add le_rfl hcoeff)

end

end HCPolySupport.HighContrast.Response
