/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Model

/-!
# Cstar

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Frozen.Assumptions.ShellField
  (zeroShellRegLaw_stationary_of_zeroShellLaw_stationary)

open HCPolySupport MeasureTheory

namespace Algsuperdiff.Section3.Disorder

noncomputable section



variable {d : ℕ}

theorem existsUnique_cstar_raw
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d))
    (hd : 2 ≤ d)
    (hJ1 : Algsuperdiff.Frozen.Assumptions.ShellLawJ1 d P)
    (hJ2 : Algsuperdiff.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ4 : Algsuperdiff.Frozen.Assumptions.ShellLawJ4 d P hd hJ1 hJ2) :
    ∃! value : ℝ, 0 < value ∧
      ∀ e : {e : Vec d // HCPolySupport.Book.Ch02.vecNorm e = 1},
        ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
            P
            (zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
                P hJ1.stationary)
            e.1
            (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
              P hJ2.gaussian_tail e.1 e.2)‖ ^ 2 =
          value * Real.log 3 := by
  obtain ⟨value, hvalue_pos, hvalue⟩ := hJ4.nondegenerate
  refine ⟨value, ⟨hvalue_pos, hvalue⟩, ?_⟩
  intro other hother
  let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) hd⟩
  let e : Vec d := Pi.single i 1
  have he_sq : vecNormSq e = 1 := by
    dsimp only [e]
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · norm_num
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  have he : HCPolySupport.Book.Ch02.vecNorm e = 1 := by
    apply (sq_eq_sq₀ (HCPolySupport.Book.Ch02.vecNorm_nonneg e) (by norm_num)).mp
    rw [HCPolySupport.Book.Ch02.vecNorm_sq_eq_vecNormSq, he_sq]
    norm_num
  let unitE : {e : Vec d // HCPolySupport.Book.Ch02.vecNorm e = 1} := ⟨e, he⟩
  have hvalue_at_e := hvalue unitE
  have hother_at_e := hother.2 unitE
  rw [hvalue_at_e] at hother_at_e
  exact (mul_right_cancel₀ (ne_of_gt (Real.log_pos (by norm_num))) hother_at_e).symm

/-- The positive J4 non-degeneracy constant selected from the standing ABK
model. -/
noncomputable def cstar (M : ABKModel d) : ℝ :=
  Classical.choose (existsUnique_cstar_raw d M.P M.shellPrefix.dimension M.J1 M.J2 M.J4)

/-- The canonical `cstar` is positive, has the literal J4 energy identity on
every unit direction, and is the unique value with those two properties. -/
theorem cstar_characterization (M : ABKModel d) :
    0 < cstar M ∧
      (∀ e : {e : Vec d // HCPolySupport.Book.Ch02.vecNorm e = 1},
        ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
            M.P
            (zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
                M.P M.J1.stationary)
            e.1
            (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
              M.P M.J2.gaussian_tail e.1 e.2)‖ ^ 2 =
          cstar M * Real.log 3) ∧
      ∀ other : ℝ,
        0 < other →
        (∀ e : {e : Vec d // HCPolySupport.Book.Ch02.vecNorm e = 1},
          ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
              M.P
              (zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
                  M.P M.J1.stationary)
              e.1
              (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
                M.P M.J2.gaussian_tail e.1 e.2)‖ ^ 2 =
            other * Real.log 3) →
          other = cstar M := by
  have hspec := Classical.choose_spec
    (existsUnique_cstar_raw d M.P M.shellPrefix.dimension M.J1 M.J2 M.J4)
  refine ⟨hspec.1.1, hspec.1.2, ?_⟩
  intro other hother_pos hother
  exact hspec.2 other ⟨hother_pos, hother⟩

private theorem measurable_originFrobeniusIntegrand (d : ℕ) :
    Measurable (fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦
      HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0)) := by
  unfold HCPolySupport.Book.Ch02.matrixFrobeniusNormSq
  exact Finset.univ.measurable_sum fun i _ ↦
    Finset.univ.measurable_sum fun j _ ↦
      (((Algsuperdiff.Frozen.Assumptions.ShellField.measurable_eval_entry (d := d) 0 i j).comp
        Algsuperdiff.Frozen.Assumptions.ShellField.measurable_zeroShellMap).pow_const 2)

/-- J2's Gaussian tail makes the literal zero-shell Frobenius mass integrable. -/
theorem integrable_originFrobeniusMass (M : ABKModel d) :
    Integrable (fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦
      HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0)) M.P.toMeasure := by
  let X : (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d) → ℝ :=
    fun F ↦ Algsuperdiff.Frozen.Assumptions.ShellField.j2Observable d (F 0)
  have hXmeas : Measurable X :=
    (Algsuperdiff.Frozen.Assumptions.ShellField.j2Observable_measurable d).comp
      Algsuperdiff.Frozen.Assumptions.ShellField.measurable_zeroShellMap
  have hXnonneg : ∀ F, 0 ≤ X F := fun F ↦
    Algsuperdiff.Frozen.Assumptions.ShellField.j2Observable_nonneg d (F 0)
  have hXmem : MemLp X 2 M.P.toMeasure :=
    Algsuperdiff.Probability.memLp_two_of_gaussian_tail hXmeas hXnonneg M.J2.gaussian_tail
  have hXsq : Integrable (fun F ↦ X F ^ 2) M.P.toMeasure := by
    convert hXmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0) using 1
    ext F
    simp only [Real.norm_eq_abs, abs_of_nonneg (hXnonneg F)]
  apply Integrable.mono' (hXsq.const_mul ((d : ℝ) ^ 2))
  · exact (measurable_originFrobeniusIntegrand d).aestronglyMeasurable
  · filter_upwards with F
    rw [Real.norm_eq_abs,
      abs_of_nonneg (HCPolySupport.Book.Ch02.matrixFrobeniusNormSq_nonneg ((F 0) 0))]
    have hunit :
        Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeValueNorm (F 0) ≤ X F := by
      calc
        Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeValueNorm (F 0) ≤
            Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeValueNorm (F 0) +
              Real.sqrt d * Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeDerivNorm (F 0) :=
          le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _)
            (Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeDerivNorm_nonneg (F 0)))
        _ ≤ Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeValueNorm (F 0) +
              Real.sqrt d * Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeDerivNorm (F 0) +
              (d : ℝ) * Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeSecondDerivNorm (F 0) :=
          le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg d)
            (Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeSecondDerivNorm_nonneg (F 0)))
        _ = X F := rfl
    have hop : HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) ≤ X F := by
      calc
        HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) ≤
            Algsuperdiff.Frozen.Assumptions.ShellField.unitCubeValueNorm (F 0) :=
          Algsuperdiff.Frozen.Assumptions.ShellField.matrixOperatorNorm_zero_le_unitCubeValueNorm
            (F 0)
        _ ≤ X F := hunit
    calc
      HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0) ≤
          (d : ℝ) ^ 2 * HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) ^ 2 :=
        calc
          HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0) =
              HCPolySupport.Book.Ch02.matrixFrobeniusNorm ((F 0) 0) ^ 2 := by
            rw [HCPolySupport.Book.Ch02.matrixFrobeniusNorm,
              Real.sq_sqrt (HCPolySupport.Book.Ch02.matrixFrobeniusNormSq_nonneg ((F 0) 0))]
          _ ≤ ((d : ℝ) * HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0)) ^ 2 :=
            (sq_le_sq₀ (HCPolySupport.Book.Ch02.matrixFrobeniusNorm_nonneg ((F 0) 0))
              (mul_nonneg (Nat.cast_nonneg d)
                (HCPolySupport.Book.Ch02.matrixOperatorNorm_nonneg ((F 0) 0)))).mpr
              (HCPolySupport.Book.Ch02.matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm ((F 0) 0))
          _ = (d : ℝ) ^ 2 * HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) ^ 2 := by
            ring
      _ ≤ (d : ℝ) ^ 2 * X F ^ 2 :=
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (HCPolySupport.Book.Ch02.matrixOperatorNorm_nonneg ((F 0) 0))
            (hXnonneg F)).mpr hop)
          (sq_nonneg _)

/-- The literal squared Frobenius mass of the zero shell at the origin.  The
preceding theorem admits this expectation from the standing J2 tail bound. -/
noncomputable def originFrobeniusMass (M : ABKModel d) : ℝ :=
  ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
    HCPolySupport.Book.Ch02.matrixFrobeniusNormSq ((F 0) 0) ∂M.P.toMeasure

private theorem norm_sq_zeroShellPotentialCorrector_le_norm_sq_zeroShellForcingL2
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d))
    (hstationary : ∀ z : Vec d,
      Measure.map
          (HCPolySupport.translateReg z)
          (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure =
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure)
    (e : Vec d)
    (hmem : MemLp
      (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing e) 2
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure) :
    ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
        P hstationary e hmem‖ ^ 2 ≤
      ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2 P e hmem‖ ^ 2 := by
  let := Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant P hstationary
  have hnorm :=
    Submodule.norm_starProjection_apply_le
      (Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
        (μ := (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure) (d := d))
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2 P e hmem)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (norm_nonneg
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2 P e hmem))).mpr hnorm
  simpa only [Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector,
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellProjectedForcing,
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialSubspace,
    norm_neg] using! hsq

private theorem norm_sq_zeroShellForcingL2_eq_raw_integral
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d))
    (e : Vec d)
    (hmem : MemLp
      (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing e) 2
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure) :
    ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2 P e hmem‖ ^ 2 =
      ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
        vecNormSq (matVecMul ((F 0) 0) e) ∂P.toMeasure := by
  let f : RegCoeffField d → ℝ :=
    fun a ↦ ‖Algsuperdiff.Frozen.Assumptions.ShellField.originForcing e a‖ ^ 2
  calc
    ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2 P e hmem‖ ^ 2 =
        ∫ a, f a ∂(Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Algsuperdiff.Frozen.Assumptions.ShellField.coeFn_zeroShellForcingL2
        P e hmem] with a ha
      rw [ha]
      exact real_inner_self_eq_norm_sq _
    _ = ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
        f (Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell (F 0)) ∂P.toMeasure := by
      have hfmeas : AEStronglyMeasurable f
          (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure := by
        change AEStronglyMeasurable
          (fun a ↦ ‖Algsuperdiff.Frozen.Assumptions.ShellField.originForcing e a‖ ^ 2)
          (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure
        exact hmem.aestronglyMeasurable.norm.pow 2
      change ∫ a, f a ∂Measure.map
          (Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell ∘
            fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦ F 0) P.toMeasure = _
      exact integral_map
        (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_zeroShellRegMap (d :=
          d)).aemeasurable
        hfmeas
    _ = ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
        vecNormSq (matVecMul ((F 0) 0) e) ∂P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with F
      simpa [f, vecNormSq] using
        Algsuperdiff.Frozen.Assumptions.ShellField.norm_sq_originForcing e
          (Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell (F 0))

private theorem measurable_originDirectionalEnergy (d : ℕ) (e : Vec d) :
    Measurable (fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦
      vecNormSq (matVecMul ((F 0) 0) e)) := by
  unfold vecNormSq vecDot matVecMul
  exact Finset.univ.measurable_sum fun i _ ↦
    (Finset.univ.measurable_sum fun j _ ↦
      (((Algsuperdiff.Frozen.Assumptions.ShellField.measurable_eval_entry (d := d) 0 i j).comp
        Algsuperdiff.Frozen.Assumptions.ShellField.measurable_zeroShellMap).mul_const (e j))).mul
      (Finset.univ.measurable_sum fun j _ ↦
        (((Algsuperdiff.Frozen.Assumptions.ShellField.measurable_eval_entry (d := d) 0 i j).comp
          Algsuperdiff.Frozen.Assumptions.ShellField.measurable_zeroShellMap).mul_const (e j)))

private theorem integrable_originDirectionalEnergy (M : ABKModel d)
    (e : Vec d) (he : HCPolySupport.Book.Ch02.vecNorm e = 1) :
    Integrable (fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦
      vecNormSq (matVecMul ((F 0) 0) e)) M.P.toMeasure := by
  apply Integrable.mono' (integrable_originFrobeniusMass M)
  · exact (measurable_originDirectionalEnergy d e).aestronglyMeasurable
  · filter_upwards with F
    rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _)]
    have he_sq : vecNormSq e = 1 := by
      rw [← HCPolySupport.Book.Ch02.vecNorm_sq_eq_vecNormSq, he]
      norm_num
    simpa [he_sq] using
      HCPolySupport.Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq
        ((F 0) 0) e

private theorem sum_standardBasis_directionalEnergy_eq_frobenius
    (A : Mat d) :
    ∑ i : Fin d, vecNormSq (matVecMul A (Pi.single i 1 : Vec d)) =
      HCPolySupport.Book.Ch02.matrixFrobeniusNormSq A := by
  simp only [vecNormSq, vecDot, matVecMul, Pi.single_apply]
  rw [Finset.sum_comm]
  congr with j
  simp [pow_two]

/-- The normalized Frobenius origin-mass constant. -/
noncomputable def cstarPlus (M : ABKModel d) : ℝ :=
  originFrobeniusMass M / Real.log 3

/-- The Frobenius constant is normalized so that its defining origin mass is
`cstarPlus * log 3`. -/
theorem cstarPlus_characterization (M : ABKModel d) :
    originFrobeniusMass M = cstarPlus M * Real.log 3 := by
  rw [cstarPlus, div_mul_cancel₀]
  exact ne_of_gt (Real.log_pos (by norm_num))

/-- The Frobenius constant is nonnegative because its defining mass is an
expectation of a squared Frobenius norm. -/
theorem cstarPlus_nonneg (M : ABKModel d) : 0 ≤ cstarPlus M := by
  unfold cstarPlus originFrobeniusMass
  exact div_nonneg
    (integral_nonneg fun F ↦
      HCPolySupport.Book.Ch02.matrixFrobeniusNormSq_nonneg ((F 0) 0))
    (Real.log_nonneg (by norm_num))

private theorem vecNorm_single_eq_one (i : Fin d) :
    HCPolySupport.Book.Ch02.vecNorm (Pi.single i 1 : Vec d) = 1 := by
  have he_sq : vecNormSq (Pi.single i 1 : Vec d) = 1 := by
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · norm_num
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  apply (sq_eq_sq₀
    (HCPolySupport.Book.Ch02.vecNorm_nonneg (Pi.single i 1 : Vec d))
    (by norm_num)).mp
  rw [HCPolySupport.Book.Ch02.vecNorm_sq_eq_vecNormSq, he_sq]
  norm_num

private theorem cstar_mul_log_le_originDirectionalEnergy
    (M : ABKModel d) (e : Vec d)
    (he : HCPolySupport.Book.Ch02.vecNorm e = 1) :
    cstar M * Real.log 3 ≤
      ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
        vecNormSq (matVecMul ((F 0) 0) e) ∂M.P.toMeasure := by
  have hstationary :=
    zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      M.P M.J1.stationary
  have hmem : MemLp
      (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing e) 2
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw M.P).toMeasure :=
    Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
      M.P M.J2.gaussian_tail e he
  rw [← (cstar_characterization M).2.1 ⟨e, he⟩]
  calc
    ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
        M.P hstationary e hmem‖ ^ 2 ≤
        ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2
          M.P e hmem‖ ^ 2 :=
      norm_sq_zeroShellPotentialCorrector_le_norm_sq_zeroShellForcingL2
        M.P hstationary e hmem
    _ = ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
        vecNormSq (matVecMul ((F 0) 0) e) ∂M.P.toMeasure :=
      norm_sq_zeroShellForcingL2_eq_raw_integral M.P e hmem

private theorem sum_standardBasis_directionalEnergy_eq_originFrobeniusMass
    (M : ABKModel d) :
    (∑ i : Fin d, ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
      vecNormSq (matVecMul ((F 0) 0) (Pi.single i 1 : Vec d)) ∂M.P.toMeasure) =
        originFrobeniusMass M := by
  rw [← integral_finsetSum]
  · unfold originFrobeniusMass
    apply integral_congr_ae
    filter_upwards with F
    exact sum_standardBasis_directionalEnergy_eq_frobenius ((F 0) 0)
  · intro i _
    exact integrable_originDirectionalEnergy M (Pi.single i 1 : Vec d)
      (vecNorm_single_eq_one i)

private theorem dim_mul_cstar_mul_log_le_originFrobeniusMass
    (M : ABKModel d) :
    (d : ℝ) * (cstar M * Real.log 3) ≤ originFrobeniusMass M := by
  calc
    (d : ℝ) * (cstar M * Real.log 3) =
        ∑ _i : Fin d, cstar M * Real.log 3 := by
      simp [Finset.sum_const, Fintype.card_fin]
    _ ≤ ∑ i : Fin d, ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d,
        vecNormSq (matVecMul ((F 0) 0) (Pi.single i 1 : Vec d)) ∂M.P.toMeasure :=
      Finset.sum_le_sum fun i _ ↦
        cstar_mul_log_le_originDirectionalEnergy M (Pi.single i 1 : Vec d)
          (vecNorm_single_eq_one i)
    _ = originFrobeniusMass M :=
      sum_standardBasis_directionalEnergy_eq_originFrobeniusMass M

/-- J4's directional energy is controlled, after summing an orthonormal basis,
by the J2-admissible Frobenius origin mass. -/
theorem dim_mul_cstar_le_cstarPlus (M : ABKModel d) :
    (d : ℝ) * cstar M ≤ cstarPlus M := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_of_pos_right hlog).mp
  rw [← cstarPlus_characterization M]
  rw [mul_assoc]
  exact dim_mul_cstar_mul_log_le_originFrobeniusMass M

/-- The normalized Frobenius origin-mass constant is strictly positive. -/
theorem cstarPlus_pos (M : ABKModel d) : 0 < cstarPlus M := by
  have hd_nat : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hd_nat
  exact lt_of_lt_of_le (mul_pos hd (cstar_characterization M).1)
    (dim_mul_cstar_le_cstarPlus M)

end

end Algsuperdiff.Section3.Disorder
