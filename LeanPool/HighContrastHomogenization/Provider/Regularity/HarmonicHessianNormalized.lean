/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientGainIteration

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicHessianNormalized

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport

open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

private theorem depthELpNorm_rawCube_eq_scale_mul_normalized {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (f : Vec d → ℝ) :
    MeasureTheory.eLpNorm f p.exponent (volumeMeasureOn (openCubeSet Q)) =
      (ENNReal.ofReal (cubeScaleFactor Q) ^ ((d : ℝ) / p.exponent.toReal)) *
        MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) := by
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hcoeff :
      ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p.exponent).toReal =
        (ENNReal.ofReal (cubeScaleFactor Q) ^
          ((d : ℝ) / p.exponent.toReal))⁻¹ := by
    rw [cubeVolume_eq_scaleFactor_pow,
      ENNReal.ofReal_inv_of_pos (pow_pos hscale d)]
    rw [ENNReal.ofReal_pow hscale.le, ENNReal.inv_rpow,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    simp only [one_div, ENNReal.toReal_inv]
    field_simp [ne_of_gt (ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne)]
  have hnorm : MeasureTheory.eLpNorm f p.exponent
      (normalizedCubeMeasure Q) =
      (ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p.exponent).toReal) *
        MeasureTheory.eLpNorm f p.exponent
          (volumeMeasureOn (openCubeSet Q)) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact MeasureTheory.eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q)))
      f p.exponent _
  rw [hcoeff] at hnorm
  set a : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q) ^
    ((d : ℝ) / p.exponent.toReal)
  have ha0 : a ≠ 0 := ne_of_gt <|
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hscale) ENNReal.ofReal_ne_top
  have hat : a ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  rw [hnorm]
  calc
    _ = (a * a⁻¹) * MeasureTheory.eLpNorm f p.exponent
        (volumeMeasureOn (openCubeSet Q)) := by
      simp [a, ENNReal.mul_inv_cancel ha0 hat]
    _ = _ := by ring

private theorem depthRaw_eLpNorm_two_toReal_eq_scale_pow_mul_cubeLpNorm
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f 2 (normalizedCubeMeasure Q)) :
    (MeasureTheory.eLpNorm f 2 (volumeMeasureOn (openCubeSet Q))).toReal =
      (cubeScaleFactor Q) ^ ((d : ℝ) / 2) * cubeLpNorm Q 2 f := by
  have hraw := depthELpNorm_rawCube_eq_scale_mul_normalized
    Q FiniteLpExponent.two f
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have htop : ENNReal.ofReal (cubeScaleFactor Q) ^ ((d : ℝ) / 2) *
      MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      hf.eLpNorm_ne_top
  have hreal := congrArg ENNReal.toReal hraw
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hscale.le] at hreal
  simpa [cubeLpNorm] using hreal

private theorem depthHessianCoordL2NormSum_eq_sum_raw_eLpNorm {d : ℕ}
    {U : Set (Vec d)} {u : H1Function U} (H : HasWeakHessianOn U u) :
    H.hessianCoordL2NormSum =
      ∑ i : Fin d, ∑ j : Fin d,
        (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
          (volumeMeasureOn U)).toReal := by
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [HasWeakHessianOn.hessCoordToScalarL2, HCPolySupport.toScalarL2,
    MeasureTheory.Lp.norm_toLp]

private theorem depthEnnreal_le_of_toReal_le {a b : ℝ≥0∞}
    (ha : a ≠ ∞) (hb : b ≠ ∞) (h : a.toReal ≤ b.toReal) : a ≤ b :=
  (ENNReal.toReal_le_toReal ha hb).mp h

private theorem exists_harmonic_centralChild_normalized_hessian_energy_bound_real
    {d : ℕ} :
    ∃ A : ℝ, 0 < A ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
            uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
              ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
              cubeScaleFactor (centralChild Q) *
                ∑ i : Fin d, ∑ j : Fin d,
                  cubeLpNorm (centralChild Q) 2 (fun x => H.hess i j x) ≤
                A * ∑ j : Fin d,
                  cubeLpNorm Q 2 (fun x => u.grad x j) := by
  obtain ⟨A, hApos, hA⟩ := exists_harmonic_innerHalf_hessian_energy_bound d
  let B : ℝ := A * (3 : ℝ) ^ ((d : ℝ) / 2 - 1)
  refine ⟨B, mul_pos hApos (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro Q u h
  obtain ⟨uS, huval, hugrad, H, hH⟩ := hA Q u h
  refine ⟨uS, huval, hugrad, H, ?_⟩
  let P : TriadicCube d := centralChild Q
  let S : ℝ := ∑ i : Fin d, ∑ j : Fin d,
    cubeLpNorm P 2 (fun x => H.hess i j x)
  let T : ℝ := ∑ j : Fin d, cubeLpNorm Q 2 (fun x => u.grad x j)
  have hPsub : openCubeSet P ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
    (openCubeSet_subset_cubeSet P).trans (by simpa [P] using
      centralChild_cubeSet_subset_scaledOpenInnerHalf Q)
  have hrawrow : ∀ i j : Fin d,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
        (volumeMeasureOn (openCubeSet P))).toReal ≤
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
        (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal := by
    intro i j
    apply ENNReal.toReal_mono (H.hess_memL2 i j).eLpNorm_ne_top
    exact MeasureTheory.eLpNorm_mono_measure _
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hPsub)
  have hrawsum : ∑ i : Fin d, ∑ j : Fin d,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
        (volumeMeasureOn (openCubeSet P))).toReal ≤
      H.hessianCoordL2NormSum := by
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
            (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hrawrow i j
      _ = _ := (depthHessianCoordL2NormSum_eq_sum_raw_eLpNorm H).symm
  have hPmem : ∀ i j : Fin d,
      MeasureTheory.MemLp (fun x => H.hess i j x) 2
        (normalizedCubeMeasure P) := by
    intro i j
    exact memL2On_openCubeSet_normalizedCubeMeasure
      ((H.restrict (isOpen_openCubeSet P) hPsub).hess_memL2 i j)
  have hQmem : ∀ j : Fin d,
      MeasureTheory.MemLp (fun x => u.grad x j) 2
        (normalizedCubeMeasure Q) := by
    intro j
    exact u.grad_memL2_normalizedCubeMeasure j
  have hrawP : (cubeScaleFactor P) ^ ((d : ℝ) / 2) * S ≤
      H.hessianCoordL2NormSum := by
    calc
      (cubeScaleFactor P) ^ ((d : ℝ) / 2) * S =
          ∑ i : Fin d, ∑ j : Fin d,
            (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
              (volumeMeasureOn (openCubeSet P))).toReal := by
        dsimp [S]
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (depthRaw_eLpNorm_two_toReal_eq_scale_pow_mul_cubeLpNorm
          P _ (hPmem i j)).symm
      _ ≤ _ := hrawsum
  have hrawQ : u.gradientCoordL2NormSum =
      (cubeScaleFactor Q) ^ ((d : ℝ) / 2) * T := by
    rw [gradientCoordL2NormSum_eq_sum_eLpNorm]
    dsimp [T]
    calc
      _ = ∑ j : Fin d, (cubeScaleFactor Q) ^ ((d : ℝ) / 2) *
          cubeLpNorm Q 2 (fun x => u.grad x j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact depthRaw_eLpNorm_two_toReal_eq_scale_pow_mul_cubeLpNorm
          Q _ (hQmem j)
      _ = _ := by rw [Finset.mul_sum]
  have hscaleP : cubeScaleFactor P = cubeScaleFactor Q / 3 := by
    have h := cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
    simpa [P, centralChild] using h
  have hscaleQpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hscalePpos : 0 < cubeScaleFactor P := by rw [hscaleP]; positivity
  have hpower : cubeScaleFactor P =
      (cubeScaleFactor P) ^ ((d : ℝ) / 2) *
        (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) := by
    rw [← Real.rpow_add hscalePpos]
    norm_num
  have hratio : (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) =
      (cubeScaleFactor Q) ^ (1 - (d : ℝ) / 2) *
        (3 : ℝ) ^ ((d : ℝ) / 2 - 1) := by
    rw [hscaleP, Real.div_rpow hscaleQpos.le (by norm_num : 0 ≤ (3 : ℝ))]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))]
    congr 1
    ring_nf
  calc
    cubeScaleFactor (centralChild Q) * ∑ i : Fin d, ∑ j : Fin d,
        cubeLpNorm (centralChild Q) 2 (fun x => H.hess i j x) =
        cubeScaleFactor P * S := by rfl
    _ = (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) *
        ((cubeScaleFactor P) ^ ((d : ℝ) / 2) * S) := by
      calc
        cubeScaleFactor P * S =
            ((cubeScaleFactor P) ^ ((d : ℝ) / 2) *
              (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2)) * S := by
          rw [← hpower]
        _ = _ := by ring
    _ ≤ (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) *
        H.hessianCoordL2NormSum := by gcongr
    _ ≤ (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) *
        (A * (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum) := by gcongr
    _ = B * T := by
      rw [hratio, hrawQ]
      dsimp [B]
      have hqpower : (cubeScaleFactor Q) ^ (1 - (d : ℝ) / 2) *
          (cubeScaleFactor Q) ^ ((d : ℝ) / 2) = cubeScaleFactor Q := by
        rw [← Real.rpow_add hscaleQpos]
        norm_num
      calc
        _ = A * (3 : ℝ) ^ ((d : ℝ) / 2 - 1) *
            ((cubeScaleFactor Q) ^ (1 - (d : ℝ) / 2) *
              (cubeScaleFactor Q) ^ ((d : ℝ) / 2) *
                (cubeScaleFactor Q)⁻¹) * T := by ring
        _ = _ := by rw [hqpower, mul_inv_cancel₀ hscaleQpos.ne', mul_one]

/-- A dimension-only normalized Hessian-energy carrier for a harmonic
function on the central child of a Euclidean cube. -/
theorem exists_harmonic_centralChild_normalized_hessian_energy_bound
    {d : ℕ} :
    ∃ A : ℝ≥0∞, 0 < A ∧ A ≠ ∞ ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
            uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
              ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
              ENNReal.ofReal (cubeScaleFactor (centralChild Q)) *
                ∑ i : Fin d, ∑ j : Fin d,
                  MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
                    (normalizedCubeMeasure (centralChild Q)) ≤
                A * ∑ j : Fin d,
                  MeasureTheory.eLpNorm (fun x => u.grad x j) 2
                    (normalizedCubeMeasure Q) := by
  obtain ⟨A, hApos, hA⟩ :=
    exists_harmonic_centralChild_normalized_hessian_energy_bound_real
      (d := d)
  refine ⟨ENNReal.ofReal A, ENNReal.ofReal_pos.mpr hApos,
    ENNReal.ofReal_ne_top, ?_⟩
  intro Q u h
  obtain ⟨uS, huval, hugrad, H, hH⟩ := hA Q u h
  refine ⟨uS, huval, hugrad, H, ?_⟩
  let P : TriadicCube d := centralChild Q
  let L : ℝ≥0∞ := ∑ i : Fin d, ∑ j : Fin d,
    MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
      (normalizedCubeMeasure P)
  let R : ℝ≥0∞ := ∑ j : Fin d,
    MeasureTheory.eLpNorm (fun x => u.grad x j) 2
      (normalizedCubeMeasure Q)
  have hPsub : openCubeSet P ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
    (openCubeSet_subset_cubeSet P).trans (by simpa [P] using
      centralChild_cubeSet_subset_scaledOpenInnerHalf Q)
  have hLrowtop : ∀ i : Fin d,
      (∑ j : Fin d, MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
        (normalizedCubeMeasure P)) ≠ ∞ := fun i =>
    ENNReal.sum_ne_top.2 fun j _ =>
      (memL2On_openCubeSet_normalizedCubeMeasure
        ((H.restrict (isOpen_openCubeSet P) hPsub).hess_memL2 i j)).eLpNorm_ne_top
  have hLtop : L ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => hLrowtop i
  have hRtop : R ≠ ∞ := ENNReal.sum_ne_top.2 fun j _ =>
    (u.grad_memL2_normalizedCubeMeasure j).eLpNorm_ne_top
  have hlefttop : ENNReal.ofReal (cubeScaleFactor P) * L ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop
  have hrighttop : ENNReal.ofReal A * R ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRtop
  have hLtoReal : L.toReal = ∑ i : Fin d, ∑ j : Fin d,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
        (normalizedCubeMeasure P)).toReal := by
    dsimp [L]
    rw [ENNReal.toReal_sum (fun i _ => hLrowtop i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_sum]
    intro j _
    exact (memL2On_openCubeSet_normalizedCubeMeasure
      ((H.restrict (isOpen_openCubeSet P) hPsub).hess_memL2 i j)).eLpNorm_ne_top
  have hRtoReal : R.toReal = ∑ j : Fin d,
      (MeasureTheory.eLpNorm (fun x => u.grad x j) 2
        (normalizedCubeMeasure Q)).toReal := by
    dsimp [R]
    rw [ENNReal.toReal_sum]
    intro j _
    exact (u.grad_memL2_normalizedCubeMeasure j).eLpNorm_ne_top
  apply depthEnnreal_le_of_toReal_le hlefttop hrighttop
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    simpa [cubeScaleFactor] using
      le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) P.scale)),
    hLtoReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal hApos.le, hRtoReal]
  simpa [P, cubeLpNorm] using hH

end CubeCalderonZygmund

end

end HCPolySupport
