/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingModulus

/-!
# Integrability of the rescaled momentum flux

On a finite spacetime cylinder, the velocity, gradient, pressure, and smooth
test derivatives combine into an `L^(3/2)` momentum flux. This is the analytic
input to the pairing modulus in `lem:compactness` of the CKN manuscript.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The three terms in the momentum pairing belong uniformly to `L^(3/2)` on
a finite spacetime cylinder when the velocity is locally `L³`, the gradient
is `L²`, and the pressure is `L^(3/2)`. -/
theorem blowup_limit_momentum_flux_memLp_three_halves
    {μ : Measure ParabolicPoint} [IsFiniteMeasure μ]
    (U : ℕ → ParabolicPoint → Vec3)
    (DU : ℕ → ParabolicPoint → Fin 3 → Fin 3 → ℝ)
    (P : ℕ → ParabolicPoint → ℝ)
    (Dw : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (divw : ParabolicPoint → ℝ)
    (Mvel Mgrad Mpress Mtest Mdiv : ℝ≥0∞)
    (hU : ∀ n i, MemLp (fun z => U n z i) 3 μ ∧
      eLpNorm (fun z => U n z i) 3 μ ≤ Mvel)
    (hDU : ∀ n i j, MemLp (fun z => DU n z i j) 2 μ ∧
      eLpNorm (fun z => DU n z i j) 2 μ ≤ Mgrad)
    (hP : ∀ n, MemLp (P n) (3 / 2 : ℝ≥0∞) μ ∧
      eLpNorm (P n) (3 / 2 : ℝ≥0∞) μ ≤ Mpress)
    (hDw : ∀ i j, MemLp (Dw i j) ⊤ μ ∧
      eLpNorm (Dw i j) ⊤ μ ≤ Mtest)
    (hdivw : MemLp divw ⊤ μ ∧ eLpNorm divw ⊤ μ ≤ Mdiv) :
    ∀ n, MemLp (fun z =>
      (∑ i : Fin 3, ∑ j : Fin 3,
        U n z i * U n z j * Dw i j z) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        DU n z i j * Dw i j z) +
      P n z * divw z) (3 / 2 : ℝ≥0∞) μ ∧
      eLpNorm (fun z =>
        (∑ i : Fin 3, ∑ j : Fin 3,
          U n z i * U n z j * Dw i j z) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          DU n z i j * Dw i j z) +
        P n z * divw z) (3 / 2 : ℝ≥0∞) μ ≤
        (∑ _i : Fin 3, ∑ _j : Fin 3, Mvel * Mvel * Mtest) +
      (∑ _i : Fin 3, ∑ _j : Fin 3,
        Mgrad * μ Set.univ ^ (1 / 6 : ℝ) * Mtest) + Mpress * Mdiv := by
  have hRealHolder : Real.HolderTriple
      (3 : ℝ≥0∞).toReal (3 : ℝ≥0∞).toReal
      (3 / 2 : ℝ≥0∞).toReal := by
    refine ⟨?_, by norm_num, by norm_num⟩
    norm_num
  have : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) :=
    ENNReal.HolderTriple.of_toReal hRealHolder
  have hOneLe : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    exact ENNReal.one_le_ofReal.mpr (by norm_num)
  have hThreeHalvesLeTwo : (3 / 2 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    calc
      ENNReal.ofReal (3 / 2 : ℝ) ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal (by norm_num)
      _ = (2 : ℝ≥0∞) := by norm_num
  intro n
  let conv : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      U n z i * U n z j * Dw i j z
  let diff : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      DU n z i j * Dw i j z
  let pres : ParabolicPoint → ℝ := fun z => P n z * divw z
  have hconvTerm (i j : Fin 3) :
      MemLp (fun z => U n z i * U n z j * Dw i j z)
        (3 / 2 : ℝ≥0∞) μ := by
    have hmul' : MemLp (fun z => U n z i * U n z j)
        (3 / 2 : ℝ≥0∞) μ := by
      exact (hU n i).1.mul (hU n j).1
    exact hmul'.mul (hDw i j).1
  have hconv : MemLp conv (3 / 2 : ℝ≥0∞) μ := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    apply memLp_finsetSum Finset.univ
    intro j hj
    exact hconvTerm i j
  have hdiffTerm (i j : Fin 3) :
      MemLp (fun z => DU n z i j * Dw i j z)
        (3 / 2 : ℝ≥0∞) μ := by
    have hlow : MemLp (fun z => DU n z i j) (3 / 2 : ℝ≥0∞) μ :=
      (hDU n i j).1.mono_exponent (p := (3 / 2 : ℝ≥0∞))
        (q := (2 : ℝ≥0∞)) hThreeHalvesLeTwo
    exact hlow.mul (hDw i j).1
  have hdiff : MemLp diff (3 / 2 : ℝ≥0∞) μ := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    apply memLp_finsetSum Finset.univ
    intro j hj
    exact hdiffTerm i j
  have hpres : MemLp pres (3 / 2 : ℝ≥0∞) μ := by
    have hdiv' : MemLp divw ⊤ μ := hdivw.1
    exact (hP n).1.mul hdiv'
  have hresult : MemLp (conv - diff + pres) (3 / 2 : ℝ≥0∞) μ :=
    (hconv.sub hdiff).add hpres
  have hconvBound : eLpNorm conv (3 / 2 : ℝ≥0∞) μ ≤
      ∑ i : Fin 3, ∑ j : Fin 3, Mvel * Mvel * Mtest := by
    dsimp [conv]
    calc
      eLpNorm (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
          U n z i * U n z j * Dw i j z) (3 / 2 : ℝ≥0∞) μ ≤
        ∑ i : Fin 3, eLpNorm (fun z => ∑ j : Fin 3,
          U n z i * U n z j * Dw i j z) (3 / 2 : ℝ≥0∞) μ := by
            exact eLpNorm_sum_le (p := (3 / 2 : ℝ≥0∞))
              (f := fun i z => ∑ j : Fin 3, U n z i * U n z j * Dw i j z)
              (s := Finset.univ) hOneLe
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (fun z => U n z i * U n z j * Dw i j z)
            (3 / 2 : ℝ≥0∞) μ := by
            apply Finset.sum_le_sum
            intro i hi
            exact eLpNorm_sum_le (p := (3 / 2 : ℝ≥0∞))
              (f := fun j z => U n z i * U n z j * Dw i j z)
              (s := Finset.univ) hOneLe
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, Mvel * Mvel * Mtest := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            have hfirst : eLpNorm (fun z => U n z i * U n z j)
                (3 / 2 : ℝ≥0∞) μ ≤
                eLpNorm (fun z => U n z i) 3 μ * eLpNorm (fun z => U n z j) 3 μ := by
              simpa [Pi.mul_apply] using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
                (p := (3 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
                (r := (3 / 2 : ℝ≥0∞))
                (b := fun x y : ℝ => x * y) (c := 1) continuous_mul
                (hU n i).1.aestronglyMeasurable
                (hU n j).1.aestronglyMeasurable (by
                  filter_upwards [] with z
                  simp [norm_mul]))
            have hsecond : eLpNorm
                (fun z => U n z i * U n z j * Dw i j z)
                (3 / 2 : ℝ≥0∞) μ ≤
                  eLpNorm (fun z => U n z i * U n z j)
                    (3 / 2 : ℝ≥0∞) μ * eLpNorm (Dw i j) ⊤ μ := by
              have hUij : MemLp (fun z => U n z i * U n z j)
                  (3 / 2 : ℝ≥0∞) μ :=
                (hU n i).1.mul (hU n j).1
              have hraw : eLpNorm
                  (fun z => U n z i * U n z j * Dw i j z)
                  (3 / 2 : ℝ≥0∞) μ ≤
                  eLpNorm (fun z => U n z i * U n z j)
                    (3 / 2 : ℝ≥0∞) μ * eLpNorm (Dw i j) ⊤ μ := by
                simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
                  (p := (3 / 2 : ℝ≥0∞)) (q := ⊤)
                  (r := (3 / 2 : ℝ≥0∞))
                  (b := fun x y : ℝ => x * y) (c := 1) continuous_mul
                  hUij.aestronglyMeasurable
                  (hDw i j).1.aestronglyMeasurable (by
                    filter_upwards [] with z
                    simp [norm_mul]))
              exact hraw
            have hfirst' : eLpNorm (fun z => U n z i) 3 μ ≤ Mvel := (hU n i).2
            have hsecond' : eLpNorm (fun z => U n z j) 3 μ ≤ Mvel := (hU n j).2
            have hthird' : eLpNorm (Dw i j) ⊤ μ ≤ Mtest := (hDw i j).2
            have h1 : eLpNorm (fun z => U n z i * U n z j)
                (3 / 2 : ℝ≥0∞) μ ≤ Mvel * Mvel := by
              simpa [mul_assoc] using
                (hfirst.trans (mul_le_mul hfirst' hsecond' (by positivity)
                  (by positivity)))
            have h2 : eLpNorm (fun z => U n z i * U n z j * Dw i j z)
                (3 / 2 : ℝ≥0∞) μ ≤ Mvel * Mvel * Mtest := by
              calc
                _ ≤ eLpNorm (fun z => U n z i * U n z j)
                    (3 / 2 : ℝ≥0∞) μ * eLpNorm (Dw i j) ⊤ μ := by
                      simpa [mul_assoc] using hsecond
                _ ≤ Mvel * Mvel * Mtest := by
                      exact mul_le_mul h1 hthird' (by positivity) (by positivity)
            exact h2
  have hdiffBound : eLpNorm diff (3 / 2 : ℝ≥0∞) μ ≤
      ∑ i : Fin 3, ∑ j : Fin 3,
        Mgrad * μ Set.univ ^ (1 / 6 : ℝ) * Mtest := by
    dsimp [diff]
    calc
      eLpNorm (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
          DU n z i j * Dw i j z) (3 / 2 : ℝ≥0∞) μ ≤
        ∑ i : Fin 3, eLpNorm (fun z => ∑ j : Fin 3,
          DU n z i j * Dw i j z) (3 / 2 : ℝ≥0∞) μ := by
            exact eLpNorm_sum_le (p := (3 / 2 : ℝ≥0∞))
              (f := fun i z => ∑ j : Fin 3, DU n z i j * Dw i j z)
              (s := Finset.univ) hOneLe
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (fun z => DU n z i j * Dw i j z)
            (3 / 2 : ℝ≥0∞) μ := by
            apply Finset.sum_le_sum
            intro i hi
            exact eLpNorm_sum_le (p := (3 / 2 : ℝ≥0∞))
              (f := fun j z => DU n z i j * Dw i j z)
              (s := Finset.univ) hOneLe
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          Mgrad * μ Set.univ ^ (1 / 6 : ℝ) * Mtest := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            have hlow : eLpNorm (fun z => DU n z i j)
                (3 / 2 : ℝ≥0∞) μ ≤
                eLpNorm (fun z => DU n z i j) 2 μ *
                  μ Set.univ ^ (1 / 6 : ℝ) := by
              convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ
                (p := (3 / 2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
                hThreeHalvesLeTwo (hDU n i j).1.aestronglyMeasurable using 1;
                  norm_num
            have htop : eLpNorm
                (fun z => DU n z i j * Dw i j z)
                (3 / 2 : ℝ≥0∞) μ ≤
                eLpNorm (fun z => DU n z i j) (3 / 2 : ℝ≥0∞) μ *
                  eLpNorm (Dw i j) ⊤ μ := by
              have hlow0 : MemLp (fun z => DU n z i j)
                  (3 / 2 : ℝ≥0∞) μ :=
                (hDU n i j).1.mono_exponent (p := (3 / 2 : ℝ≥0∞))
                  (q := (2 : ℝ≥0∞)) hThreeHalvesLeTwo
              have hraw : eLpNorm
                  (fun z => DU n z i j * Dw i j z)
                  (3 / 2 : ℝ≥0∞) μ ≤
                  eLpNorm (fun z => DU n z i j) (3 / 2 : ℝ≥0∞) μ *
                    eLpNorm (Dw i j) ⊤ μ := by
                simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
                  (p := (3 / 2 : ℝ≥0∞)) (q := ⊤)
                  (r := (3 / 2 : ℝ≥0∞))
                  (b := fun x y : ℝ => x * y) (c := 1) continuous_mul
                  hlow0.aestronglyMeasurable
                  (hDw i j).1.aestronglyMeasurable (by
                    filter_upwards [] with z
                    simp [norm_mul]))
              exact hraw
            have hlow' : eLpNorm (fun z => DU n z i j)
                (3 / 2 : ℝ≥0∞) μ ≤
                Mgrad * μ Set.univ ^ (1 / 6 : ℝ) := by
              have hcompare : eLpNorm (fun z => DU n z i j)
                  (3 / 2 : ℝ≥0∞) μ ≤
                  eLpNorm (fun z => DU n z i j) 2 μ *
                    μ Set.univ ^ (1 / 6 : ℝ) := by
                have hpow :
                    1 / (3 / 2 : ℝ≥0∞).toReal -
                      1 / (2 : ℝ≥0∞).toReal = (1 / 6 : ℝ) := by
                  norm_num
                simpa [hpow] using hlow
              exact hcompare.trans (mul_le_mul_of_nonneg_right
                (hDU n i j).2 (by positivity))
            have htop' : eLpNorm (Dw i j) ⊤ μ ≤ Mtest := (hDw i j).2
            calc
              _ ≤ eLpNorm (fun z => DU n z i j) (3 / 2 : ℝ≥0∞) μ *
                  eLpNorm (Dw i j) ⊤ μ := by
                    simpa [mul_assoc] using htop
              _ ≤ Mgrad * μ Set.univ ^ (1 / 6 : ℝ) * Mtest := by
                    exact mul_le_mul hlow' htop' (by positivity) (by positivity)
  have hdivBound : eLpNorm divw ⊤ μ ≤ Mdiv := hdivw.2
  have hpresBound : eLpNorm pres (3 / 2 : ℝ≥0∞) μ ≤ Mpress * Mdiv := by
    dsimp [pres]
    have hmul : eLpNorm (fun z => P n z * divw z) (3 / 2 : ℝ≥0∞) μ ≤
        eLpNorm (P n) (3 / 2 : ℝ≥0∞) μ * eLpNorm divw ⊤ μ := by
      simpa [Pi.mul_apply] using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := (3 / 2 : ℝ≥0∞)) (q := ⊤) (r := (3 / 2 : ℝ≥0∞))
        (b := fun x y : ℝ => x * y) (c := 1) continuous_mul
        (hP n).1.aestronglyMeasurable hdivw.1.aestronglyMeasurable (by
          filter_upwards [] with z
          simp [norm_mul]))
    calc
      _ ≤ eLpNorm (P n) (3 / 2 : ℝ≥0∞) μ * eLpNorm divw ⊤ μ := by
        simpa [mul_assoc] using hmul
      _ ≤ Mpress * Mdiv := by
        exact mul_le_mul (hP n).2 hdivBound (by positivity) (by positivity)
  have hnorm : eLpNorm (conv - diff + pres) (3 / 2 : ℝ≥0∞) μ ≤
      (∑ _i : Fin 3, ∑ _j : Fin 3, Mvel * Mvel * Mtest) +
      (∑ _i : Fin 3, ∑ _j : Fin 3,
        Mgrad * μ Set.univ ^ (1 / 6 : ℝ) * Mtest) + Mpress * Mdiv := by
    calc
      _ ≤ eLpNorm conv (3 / 2 : ℝ≥0∞) μ +
          eLpNorm diff (3 / 2 : ℝ≥0∞) μ +
          eLpNorm pres (3 / 2 : ℝ≥0∞) μ := by
            calc
              _ ≤ eLpNorm (conv - diff) (3 / 2 : ℝ≥0∞) μ +
                  eLpNorm pres (3 / 2 : ℝ≥0∞) μ := eLpNorm_add_le hOneLe
              _ ≤ (eLpNorm conv (3 / 2 : ℝ≥0∞) μ +
                    eLpNorm diff (3 / 2 : ℝ≥0∞) μ) +
                  eLpNorm pres (3 / 2 : ℝ≥0∞) μ := by
                    gcongr
                    exact eLpNorm_sub_le hOneLe
              _ = _ := by ring
      _ ≤ _ := by gcongr
  have hfluxEq : (fun z =>
      (∑ i : Fin 3, ∑ j : Fin 3, U n z i * U n z j * Dw i j z) -
      (∑ i : Fin 3, ∑ j : Fin 3, DU n z i j * Dw i j z) +
      P n z * divw z) = conv - diff + pres := by
    funext z
    simp [conv, diff, pres]
  refine ⟨?_, ?_⟩
  · rw [hfluxEq]
    exact hresult
  · rw [hfluxEq]
    exact hnorm

end ESS

end
