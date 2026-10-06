/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesModulusCore
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The explicit pairing modulus: the estimate

The estimate behind clause (b) of `prop:blowup-limit`, for one field. The
change of the pairing of the slices of `f` with a smooth test `w` is the
space-time integral of the momentum flux. The viscous term is integrated by
parts on each slice, and the three terms are bounded by the slice `L²` bound
of `f`, the `L^{3/2}` bound of the pressure, and the norms `‖∇w‖_∞`, `‖Δw‖₂`,
`‖div w‖_∞`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Space-time volume restricted to a product set is the product of the
restricted volumes. -/
theorem blowupLimitClauses_restrict_prod_eq (C : Set Vec3) (I : Set ℝ) :
    (volume : Measure ParabolicPoint).restrict (spaceTimeSet C I) =
      (volume.restrict C).prod (volume.restrict I) := by
  rw [Measure.prod_restrict]
  rfl

/-- Tonelli on a product set, integrating in space first. -/
theorem blowupLimitClauses_lintegral_prod_eq (C : Set Vec3) (I : Set ℝ)
    {F : ParabolicPoint → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in spaceTimeSet C I, F z = ∫⁻ τ in I, ∫⁻ x in C, F (x, τ) := by
  rw [blowupLimitClauses_restrict_prod_eq]
  exact lintegral_prod_symm' _ hF

/-- Fubini on a product set, integrating in space first. -/
theorem blowupLimitClauses_integral_prod_eq (C : Set Vec3) (I : Set ℝ)
    {F : ParabolicPoint → ℝ} (hF : Integrable F (volume.restrict (spaceTimeSet C I))) :
    ∫ z in spaceTimeSet C I, F z = ∫ τ in I, ∫ x in C, F (x, τ) := by
  rw [blowupLimitClauses_restrict_prod_eq] at hF ⊢
  exact integral_prod_symm _ hF

/-- A uniform slice bound integrates to a space-time bound. -/
theorem blowupLimitClauses_slice_energy_le {C : Set Vec3} {s t : ℝ}
    {f : ParabolicPoint → Vec3} (hf : Measurable f) {S : ℝ}
    (hslice : ∀ τ, ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (f (x, τ))) ^ (2 : ℝ) ≤
      ENNReal.ofReal S) :
    ∫⁻ z in spaceTimeSet C (Ioc s t), ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ (2 : ℝ) ≤
      ENNReal.ofReal S * ENNReal.ofReal (t - s) := by
  have hm : Measurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ (2 : ℝ)) :=
    (ENNReal.measurable_ofReal.comp
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp hf)).pow_const _
  rw [blowupLimitClauses_lintegral_prod_eq C _ hm]
  calc
    ∫⁻ τ in Ioc s t, ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (f (x, τ))) ^ (2 : ℝ) ≤
        ∫⁻ _ in Ioc s t, ENNReal.ofReal S := lintegral_mono fun τ => hslice τ
    _ = ENNReal.ofReal S * ENNReal.ofReal (t - s) := by
      rw [setLIntegral_const, Real.volume_Ioc]

/-- The coordinate sup norm of a vector is at most its Euclidean norm, in
extended form. -/
theorem blowupLimitClauses_enorm_le_euclid (v : Vec3) :
    ‖v‖ₑ ≤ ENNReal.ofReal (vec3EuclideanNorm v) := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm v)

/-- The transport flux is bounded by the square of the Euclidean norm. -/
theorem blowupLimitClauses_abs_transport_le (v : Vec3) (c : Fin 3 → Fin 3 → ℝ) {M : ℝ}
    (hc : ∀ i j, |c i j| ≤ M) :
    |∑ i : Fin 3, ∑ j : Fin 3, v i * v j * c i j| ≤ 9 * M * vec3EuclideanNorm v ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hc 0 0)
  have he : 0 ≤ vec3EuclideanNorm v := vec3EuclideanNorm_nonneg v
  have hterm : ∀ i j, |v i * v j * c i j| ≤ vec3EuclideanNorm v * vec3EuclideanNorm v * M := by
    intro i j
    rw [abs_mul, abs_mul]
    have hi := abs_apply_le_vec3EuclideanNorm v i
    have hj := abs_apply_le_vec3EuclideanNorm v j
    have h1 : |v i| * |v j| ≤ vec3EuclideanNorm v * vec3EuclideanNorm v :=
      mul_le_mul hi hj (abs_nonneg _) he
    exact mul_le_mul h1 (hc i j) (abs_nonneg _) (mul_nonneg he he)
  calc
    |∑ i : Fin 3, ∑ j : Fin 3, v i * v j * c i j| ≤
        ∑ i : Fin 3, ∑ j : Fin 3, |v i * v j * c i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, vec3EuclideanNorm v * vec3EuclideanNorm v * M :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 9 * M * vec3EuclideanNorm v ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A continuous compactly supported real function is bounded. -/
theorem blowupLimitClauses_abs_bound_of_compact {g : Vec3 → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |g x| ≤ M := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

/-- The explicit pairing modulus for one field (`prop:blowup-limit`,
clause (b)). -/
theorem blowupLimitClauses_modulus_of_formula
    {C : Set Vec3} (hC : IsCompact C) {R : ℝ} (hCR : C ⊆ vec3Ball 0 R) {a b : ℝ}
    {f : ParabolicPoint → Vec3} (hf : Measurable f)
    {Df : ParabolicPoint → Fin 3 → Vec3} (hDf : Measurable Df)
    {P : ParabolicPoint → ℝ}
    {S : ℝ} (hS0 : 0 ≤ S)
    (hslice : ∀ τ, ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (f (x, τ))) ^ (2 : ℝ) ≤
      ENNReal.ofReal S)
    (hDfL2 : MemLp Df 2 (volume.restrict (C ×ˢ Icc a b)))
    (hP : MemLp P (3 / 2 : ℝ≥0∞) (volume.restrict (C ×ˢ Icc a b)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : eLpNorm P (3 / 2 : ℝ≥0∞) (volume.restrict (C ×ˢ Icc a b)) ≤ ENNReal.ofReal B)
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Icc a b)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) R) (fun x => f (x, τ) i)
        (fun x => Df (x, τ) i))
    {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwC : tsupport w ⊆ C)
    {Gw Lw Dw : ℝ} (hGw : 0 ≤ Gw) (hLw : 0 ≤ Lw) (hDw : 0 ≤ Dw)
    (hgradw : ∀ x i j, |spatialDeriv (fun y => w y i) j x| ≤ Gw)
    (hlapw : ∀ i, eLpNorm (fun x => ∑ j : Fin 3,
      spatialDeriv (fun y => spatialDeriv (fun z => w z i) j y) j x) 2 volume ≤
        ENNReal.ofReal Lw)
    (hdivw : ∀ x, |∑ i : Fin 3, spatialDeriv (fun y => w y i) i x| ≤ Dw)
    {G : ℝ → ℝ}
    (hformula : ∀ s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      G t - G s = ∫ z in C ×ˢ Ioc s t,
        (∑ i : Fin 3, ∑ j : Fin 3,
          f z i * f z j * spatialDeriv (fun y => w y i) j z.1) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          Df z i j * spatialDeriv (fun y => w y i) j z.1) +
        P z * ∑ i : Fin 3, spatialDeriv (fun y => w y i) i z.1) :
    ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
      |G t - G s| ≤ (9 * S + 3 * Real.sqrt S + B * (volume C).toReal ^ (1 / 3 : ℝ)) *
        (|t - s| * (Lw + Gw) + |t - s| ^ (1 / 3 : ℝ) * Dw) := by
  -- reduce to ordered times
  have hmain : ∀ s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      |G t - G s| ≤ (9 * S + 3 * Real.sqrt S + B * (volume C).toReal ^ (1 / 3 : ℝ)) *
        ((t - s) * (Lw + Gw) + (t - s) ^ (1 / 3 : ℝ) * Dw) := by
    intro s t hs ht hst
    have hts0 : 0 ≤ t - s := sub_nonneg.mpr hst
    set I : Set ℝ := Ioc s t with hIdef
    set Q : Set ParabolicPoint := spaceTimeSet C I with hQdef
    set μ : Measure ParabolicPoint := volume.restrict Q with hμdef
    have hIsub : I ⊆ Icc a b := fun τ hτ => ⟨le_trans hs.1 hτ.1.le, le_trans hτ.2 ht.2⟩
    have hQsub : Q ⊆ C ×ˢ Icc a b := fun z hz =>
      ⟨hz.1, le_trans hs.1 hz.2.1.le, le_trans hz.2.2 ht.2⟩
    have hμle : μ ≤ volume.restrict (C ×ˢ Icc a b) := Measure.restrict_mono hQsub le_rfl
    have hCm : MeasurableSet C := hC.measurableSet
    have hvolC : volume C < ⊤ := hC.measure_lt_top
    have hμuniv : μ univ = volume C * ENNReal.ofReal (t - s) := by
      rw [hμdef, Measure.restrict_apply_univ]
      show (volume : Measure (Vec3 × ℝ)) (C ×ˢ Ioc s t) = _
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc]
    have : IsFiniteMeasure μ := ⟨by
      rw [hμuniv]
      exact ENNReal.mul_lt_top hvolC ENNReal.ofReal_lt_top⟩
    -- the test function and its derivatives
    have hwi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => w y i) := fun i =>
      (contDiff_apply ℝ ℝ i).comp hw
    have hwic : ∀ i, HasCompactSupport (fun y => w y i) := fun i =>
      hwc.comp_left (g := fun v : Vec3 => v i) rfl
    set φ : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j x => spatialDeriv (fun y => w y i) j x
      with hφdef
    have hφs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (φ i j) := fun i j =>
      blowupLimitClauses_spatialDeriv_contDiff (hwi i) j
    have hφcs : ∀ i j, HasCompactSupport (φ i j) := fun i j =>
      blowupLimitClauses_spatialDeriv_hasCompactSupport (hwic i) j
    set ψ : Fin 3 → Vec3 → ℝ := fun i x => ∑ j : Fin 3,
      spatialDeriv (fun y => spatialDeriv (fun z => w z i) j y) j x with hψdef
    have hψterm : ∀ i j, Continuous (fun x => spatialDeriv (φ i j) j x) ∧
        HasCompactSupport (fun x => spatialDeriv (φ i j) j x) := fun i j =>
      ⟨(blowupLimitClauses_spatialDeriv_contDiff (hφs i j) j).continuous,
        blowupLimitClauses_spatialDeriv_hasCompactSupport (hφcs i j) j⟩
    have hψc : ∀ i, Continuous (ψ i) := fun i =>
      continuous_finsetSum _ fun j _ => (hψterm i j).1
    have hψbd : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |ψ i x| ≤ M := by
      intro i
      choose M hM0 hM using fun j => blowupLimitClauses_abs_bound_of_compact
        (hψterm i j).1 (hψterm i j).2
      refine ⟨∑ j, M j, Finset.sum_nonneg fun j _ => hM0 j, fun x => ?_⟩
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hM j x)
    set d : Vec3 → ℝ := fun x => ∑ i : Fin 3, φ i i x with hddef
    have hdc : Continuous d := continuous_finsetSum _ fun i _ => (hφs i i).continuous
    -- the square integrability of the slices on the slab
    have hfE := blowupLimitClauses_slice_energy_le (C := C) (s := s) (t := t) hf hslice
    have hfL2 : MemLp f 2 μ := by
      rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        hf.aestronglyMeasurable]
      apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      apply ne_of_lt
      calc
        (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ≤
            ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ (2 : ℝ) := by
          apply lintegral_mono
          intro z
          rw [ENNReal.toReal_ofNat]
          exact ENNReal.rpow_le_rpow (blowupLimitClauses_enorm_le_euclid _) (by norm_num)
        _ ≤ ENNReal.ofReal S * ENNReal.ofReal (t - s) := hfE
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hfi : ∀ i, MemLp (fun z => f z i) 2 μ := fun i => hfL2.eval i
    have hDfμ : MemLp Df 2 μ := hDfL2.mono_measure hμle
    have hPμ : MemLp P (3 / 2 : ℝ≥0∞) μ := hP.mono_measure hμle
    have hP1 : Integrable P μ := hPμ.integrable (by
      rw [← CKN.ofReal_threeHalves]
      exact ENNReal.one_le_ofReal.mpr (by norm_num))
    -- the four integrands
    set A1 : ParabolicPoint → ℝ := fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      f z i * f z j * spatialDeriv (fun y => w y i) j z.1 with hA1def
    set A2 : ParabolicPoint → ℝ := fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      Df z i j * spatialDeriv (fun y => w y i) j z.1 with hA2def
    set A3 : ParabolicPoint → ℝ := fun z =>
      P z * ∑ i : Fin 3, spatialDeriv (fun y => w y i) i z.1 with hA3def
    set Bf : ParabolicPoint → ℝ := fun z => ∑ i : Fin 3, f z i * ψ i z.1 with hBfdef
    have hφm : ∀ i j, Measurable (fun z : ParabolicPoint => φ i j z.1) := fun i j =>
      (hφs i j).continuous.measurable.comp measurable_fst
    have hA1int : Integrable A1 μ := by
      refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
      exact ((hfi i).integrable_mul (hfi j)).mul_bdd (c := Gw)
        (hφm i j).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact hgradw z.1 i j)
    have hA2int : Integrable A2 μ := by
      refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
      have hDij : Integrable (fun z => Df z i j) μ :=
        ((hDfμ.eval i).eval j).integrable (by norm_num)
      exact hDij.mul_bdd (c := Gw) (hφm i j).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact hgradw z.1 i j)
    have hA3int : Integrable A3 μ :=
      hP1.mul_bdd (c := Dw) (hdc.measurable.comp measurable_fst).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact hdivw z.1)
    have hBfint : Integrable Bf μ := by
      refine integrable_finsetSum _ fun i _ => ?_
      obtain ⟨M, -, hM⟩ := hψbd i
      exact ((hfi i).integrable (by norm_num)).mul_bdd (c := M)
        ((hψc i).measurable.comp measurable_fst).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact hM z.1)
    -- the viscous term, integrated by parts on each slice
    have hA2Bf : ∫ z in Q, A2 z = -∫ z in Q, Bf z := by
      rw [blowupLimitClauses_integral_prod_eq C I hA2int,
        blowupLimitClauses_integral_prod_eq C I hBfint, ← integral_neg]
      apply integral_congr_ae
      -- slices of the gradient are square integrable at almost every time
      have hDm : Measurable (fun z : ParabolicPoint => ‖Df z‖ₑ ^ (2 : ℝ)) :=
        (hDf.enorm).pow_const _
      have hDfin : (∫⁻ z in Q, ‖Df z‖ₑ ^ (2 : ℝ)) < ⊤ := by
        have h := hDfμ.eLpNorm_lt_top
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hDfμ.aestronglyMeasurable] at h
        simp only [ENNReal.toReal_ofNat] at h
        exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h
      rw [blowupLimitClauses_lintegral_prod_eq C I hDm] at hDfin
      have hslicemeas : Measurable (fun τ : ℝ => ∫⁻ x in C, ‖Df (x, τ)‖ₑ ^ (2 : ℝ)) :=
        hDm.lintegral_prod_left'
      have hDslice := ae_lt_top hslicemeas hDfin.ne
      have hgradI : ∀ᵐ τ ∂(volume.restrict I), ∀ i : Fin 3,
          HasWeakGradientOn (vec3Ball (0 : Vec3) R) (fun x => f (x, τ) i)
            (fun x => Df (x, τ) i) :=
        ae_restrict_of_ae_restrict_of_subset hIsub hgrad
      filter_upwards [hDslice, hgradI] with τ hτD hτg
      have hfs : Measurable (fun x : Vec3 => f (x, τ)) := hf.comp measurable_prodMk_right
      have hDfs : Measurable (fun x : Vec3 => Df (x, τ)) := hDf.comp measurable_prodMk_right
      have hg2 : MemLp (fun x => f (x, τ)) 2 (volume.restrict C) := by
        rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hfs.aestronglyMeasurable]
        apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        apply ne_of_lt
        calc
          (∫⁻ x in C, ‖f (x, τ)‖ₑ ^ (2 : ℝ≥0∞).toReal) ≤
              ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (f (x, τ))) ^ (2 : ℝ) := by
            apply lintegral_mono
            intro x
            rw [ENNReal.toReal_ofNat]
            exact ENNReal.rpow_le_rpow (blowupLimitClauses_enorm_le_euclid _) (by norm_num)
          _ ≤ ENNReal.ofReal S := hslice τ
          _ < ⊤ := ENNReal.ofReal_lt_top
      have hDg2 : MemLp (fun x => Df (x, τ)) 2 (volume.restrict C) := by
        rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hDfs.aestronglyMeasurable]
        apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        simp only [ENNReal.toReal_ofNat]
        exact hτD.ne
      have h := blowupLimitClauses_slice_ibp hCR hg2 hDg2 hτg hw hwc hwC
      simp only [A2, Bf, ψ]
      rw [h]
    -- the three bounds
    have hK1 : |∫ z in Q, A1 z| ≤ 9 * Gw * S * (t - s) := by
      have heuc_m : Measurable (fun z => vec3EuclideanNorm (f z)) :=
        CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp hf
      have hsqE : ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (f z) ^ 2) ≤
          ENNReal.ofReal S * ENNReal.ofReal (t - s) := by
        refine le_trans (le_of_eq ?_) hfE
        apply lintegral_congr
        intro z
        rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
        exact (ENNReal.rpow_two _).symm
      have heucL2 : MemLp (fun z => vec3EuclideanNorm (f z)) 2 μ := by
        rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          heuc_m.aestronglyMeasurable]
        apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        apply ne_of_lt
        calc
          (∫⁻ z, ‖vec3EuclideanNorm (f z)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) =
              ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ (2 : ℝ) := by
            apply lintegral_congr
            intro z
            rw [ENNReal.toReal_ofNat, Real.enorm_of_nonneg (vec3EuclideanNorm_nonneg _)]
          _ ≤ ENNReal.ofReal S * ENNReal.ofReal (t - s) := hfE
          _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hsq : Integrable (fun z => vec3EuclideanNorm (f z) ^ 2) μ := heucL2.integrable_sq
      have hint : ∫ z in Q, vec3EuclideanNorm (f z) ^ 2 ≤ S * (t - s) := by
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
          (heuc_m.pow_const 2).aestronglyMeasurable]
        calc
          (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (f z) ^ 2)).toReal ≤
              (ENNReal.ofReal S * ENNReal.ofReal (t - s)).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              ENNReal.ofReal_ne_top) hsqE
          _ = S * (t - s) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hS0, ENNReal.toReal_ofReal hts0]
      have hbound : ∀ z, ‖A1 z‖ ≤ 9 * Gw * vec3EuclideanNorm (f z) ^ 2 := by
        intro z
        rw [Real.norm_eq_abs]
        exact blowupLimitClauses_abs_transport_le (f z)
          (fun i j => spatialDeriv (fun y => w y i) j z.1) (fun i j => hgradw z.1 i j)
      calc
        |∫ z in Q, A1 z| = ‖∫ z in Q, A1 z‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z in Q, 9 * Gw * vec3EuclideanNorm (f z) ^ 2 :=
          norm_integral_le_of_norm_le (hsq.const_mul _) (Eventually.of_forall hbound)
        _ = 9 * Gw * ∫ z in Q, vec3EuclideanNorm (f z) ^ 2 := integral_const_mul _ _
        _ ≤ 9 * Gw * (S * (t - s)) := mul_le_mul_of_nonneg_left hint (by positivity)
        _ = 9 * Gw * S * (t - s) := by ring
    have hK2 : |∫ z in Q, Bf z| ≤ 3 * Real.sqrt S * Lw * (t - s) := by
      have h22 : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
      have heuc_m : Measurable (fun z => vec3EuclideanNorm (f z)) :=
        CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp hf
      have hpt : ∀ z, ENNReal.ofReal ‖Bf z‖ ≤ ∑ i : Fin 3,
          ENNReal.ofReal (vec3EuclideanNorm (f z)) * ‖ψ i z.1‖ₑ := by
        intro z
        have h1 : ‖Bf z‖ ≤ ∑ i : Fin 3, vec3EuclideanNorm (f z) * |ψ i z.1| := by
          rw [Real.norm_eq_abs]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_apply_le_vec3EuclideanNorm _ i) (abs_nonneg _)
        calc
          ENNReal.ofReal ‖Bf z‖ ≤
              ENNReal.ofReal (∑ i : Fin 3, vec3EuclideanNorm (f z) * |ψ i z.1|) :=
            ENNReal.ofReal_le_ofReal h1
          _ = ∑ i : Fin 3, ENNReal.ofReal (vec3EuclideanNorm (f z) * |ψ i z.1|) :=
            ENNReal.ofReal_sum_of_nonneg fun i _ =>
              mul_nonneg (vec3EuclideanNorm_nonneg _) (abs_nonneg _)
          _ = ∑ i : Fin 3, ENNReal.ofReal (vec3EuclideanNorm (f z)) * ‖ψ i z.1‖ₑ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _), Real.enorm_eq_ofReal_abs]
      have hmeasTerm : ∀ i, Measurable (fun z : ParabolicPoint =>
          ENNReal.ofReal (vec3EuclideanNorm (f z)) * ‖ψ i z.1‖ₑ) := fun i =>
        (ENNReal.measurable_ofReal.comp heuc_m).mul
          ((hψc i).measurable.comp measurable_fst).enorm
      have hlap : ∀ i, (∫⁻ x in C, ‖ψ i x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Lw := by
        intro i
        have h := hlapw i
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          (hψc i).aestronglyMeasurable] at h
        simp only [ENNReal.toReal_ofNat] at h
        refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num)) h
        exact lintegral_mono' Measure.restrict_le_self le_rfl
      have hslab : ∀ i, ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (f z)) * ‖ψ i z.1‖ₑ ≤
          ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw * ENNReal.ofReal (t - s) := by
        intro i
        rw [blowupLimitClauses_lintegral_prod_eq C I (hmeasTerm i)]
        calc
          ∫⁻ τ in I, ∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (f (x, τ))) * ‖ψ i x‖ₑ ≤
              ∫⁻ _ in I, ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw := by
            apply lintegral_mono
            intro τ
            have hfs : Measurable (fun x : Vec3 => f (x, τ)) := hf.comp measurable_prodMk_right
            have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict C) h22
              (f := fun x => ENNReal.ofReal (vec3EuclideanNorm (f (x, τ))))
              (g := fun x => ‖ψ i x‖ₑ)
              (ENNReal.measurable_ofReal.comp
                (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
                  hfs)).aemeasurable
              ((hψc i).measurable.enorm.aemeasurable)
            refine le_trans (le_of_eq ?_) (hH.trans (mul_le_mul' ?_ (hlap i)))
            · rfl
            · exact ENNReal.rpow_le_rpow (hslice τ) (by norm_num)
          _ = ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw * ENNReal.ofReal (t - s) := by
            rw [setLIntegral_const, Real.volume_Ioc]
      have htot : ∫⁻ z in Q, ENNReal.ofReal ‖Bf z‖ ≤
          3 * (ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw * ENNReal.ofReal (t - s)) := by
        calc
          ∫⁻ z in Q, ENNReal.ofReal ‖Bf z‖ ≤ ∫⁻ z in Q, ∑ i : Fin 3,
              ENNReal.ofReal (vec3EuclideanNorm (f z)) * ‖ψ i z.1‖ₑ := lintegral_mono hpt
          _ = ∑ i : Fin 3, ∫⁻ z in Q,
              ENNReal.ofReal (vec3EuclideanNorm (f z)) * ‖ψ i z.1‖ₑ :=
            lintegral_finsetSum _ fun i _ => hmeasTerm i
          _ ≤ ∑ _i : Fin 3,
              ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw * ENNReal.ofReal (t - s) :=
            Finset.sum_le_sum fun i _ => hslab i
          _ = 3 * (ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw * ENNReal.ofReal (t - s)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
      have hfin : 3 * (ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw *
          ENNReal.ofReal (t - s)) ≠ ⊤ := by
        apply ENNReal.mul_ne_top (by norm_num)
        apply ENNReal.mul_ne_top (ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
        exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
      calc
        |∫ z in Q, Bf z| = ‖∫ z in Q, Bf z‖ := (Real.norm_eq_abs _).symm
        _ ≤ (∫⁻ z in Q, ENNReal.ofReal ‖Bf z‖).toReal := norm_integral_le_lintegral_norm _
        _ ≤ (3 * (ENNReal.ofReal S ^ (1 / 2 : ℝ) * ENNReal.ofReal Lw *
            ENNReal.ofReal (t - s))).toReal := ENNReal.toReal_mono hfin htot
        _ = 3 * Real.sqrt S * Lw * (t - s) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
            ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hS0, ENNReal.toReal_ofReal hLw,
            ENNReal.toReal_ofReal hts0, ← Real.sqrt_eq_rpow]
          norm_num
          ring
    have hK3 : |∫ z in Q, A3 z| ≤
        Dw * B * (volume C).toReal ^ (1 / 3 : ℝ) * (t - s) ^ (1 / 3 : ℝ) := by
      have hbound : ∀ z, ‖A3 z‖ ≤ Dw * ‖P z‖ := by
        intro z
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hdivw z.1)
          (norm_nonneg _)
      have hexp : 1 / (1 : ℝ≥0∞).toReal - 1 / (3 / 2 : ℝ≥0∞).toReal = 1 / 3 := by
        rw [ENNReal.toReal_one, ENNReal.toReal_div]
        norm_num
      have hL1 : eLpNorm P 1 μ ≤ ENNReal.ofReal B *
          (volume C * ENNReal.ofReal (t - s)) ^ (1 / 3 : ℝ) := by
        have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (μ := μ) (p := (1 : ℝ≥0∞)) (q := (3 / 2 : ℝ≥0∞)) (by
            rw [← CKN.ofReal_threeHalves]
            exact ENNReal.one_le_ofReal.mpr (by norm_num)) hP1.aestronglyMeasurable
        rw [hexp, hμuniv] at h
        refine h.trans ?_
        gcongr
        exact (eLpNorm_mono_measure _ hμle).trans hB
      have hint : ∫ z in Q, ‖P z‖ = (eLpNorm P 1 μ).toReal := by
        rw [integral_norm_eq_lintegral_enorm hP1.aestronglyMeasurable,
          eLpNorm_one_eq_lintegral_enorm]
        exact hP1.aestronglyMeasurable
      have hfin : ENNReal.ofReal B * (volume C * ENNReal.ofReal (t - s)) ^ (1 / 3 : ℝ) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ENNReal.mul_ne_top hvolC.ne ENNReal.ofReal_ne_top))
      have hreal : (eLpNorm P 1 μ).toReal ≤
          B * (volume C).toReal ^ (1 / 3 : ℝ) * (t - s) ^ (1 / 3 : ℝ) := by
        calc
          (eLpNorm P 1 μ).toReal ≤
              (ENNReal.ofReal B * (volume C * ENNReal.ofReal (t - s)) ^ (1 / 3 : ℝ)).toReal :=
            ENNReal.toReal_mono hfin hL1
          _ = B * (volume C).toReal ^ (1 / 3 : ℝ) * (t - s) ^ (1 / 3 : ℝ) := by
            rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal hB0, ENNReal.toReal_ofReal hts0,
              Real.mul_rpow ENNReal.toReal_nonneg hts0]
            ring
      calc
        |∫ z in Q, A3 z| = ‖∫ z in Q, A3 z‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z in Q, Dw * ‖P z‖ :=
          norm_integral_le_of_norm_le (hP1.norm.const_mul _) (Eventually.of_forall hbound)
        _ = Dw * ∫ z in Q, ‖P z‖ := integral_const_mul _ _
        _ ≤ Dw * (B * (volume C).toReal ^ (1 / 3 : ℝ) * (t - s) ^ (1 / 3 : ℝ)) := by
          rw [hint]
          exact mul_le_mul_of_nonneg_left hreal hDw
        _ = Dw * B * (volume C).toReal ^ (1 / 3 : ℝ) * (t - s) ^ (1 / 3 : ℝ) := by ring
    have hsplit : G t - G s = (∫ z in Q, A1 z) + (∫ z in Q, Bf z) + ∫ z in Q, A3 z := by
      have h := hformula s t hs ht hst
      have hEq : (∫ z in C ×ˢ Ioc s t, (∑ i : Fin 3, ∑ j : Fin 3,
          f z i * f z j * spatialDeriv (fun y => w y i) j z.1) -
          (∑ i : Fin 3, ∑ j : Fin 3,
            Df z i j * spatialDeriv (fun y => w y i) j z.1) +
          P z * ∑ i : Fin 3, spatialDeriv (fun y => w y i) i z.1) =
          ∫ z in Q, (A1 z - A2 z + A3 z) := rfl
      rw [h, hEq, integral_add (f := fun z => A1 z - A2 z) (hA1int.sub hA2int) hA3int,
        integral_sub hA1int hA2int, hA2Bf]
      ring
    have hSq : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
    have hV : 0 ≤ (volume C).toReal ^ (1 / 3 : ℝ) := by positivity
    have hT : 0 ≤ (t - s) ^ (1 / 3 : ℝ) := by positivity
    rw [hsplit]
    calc
      |(∫ z in Q, A1 z) + (∫ z in Q, Bf z) + ∫ z in Q, A3 z| ≤
          |∫ z in Q, A1 z| + |∫ z in Q, Bf z| + |∫ z in Q, A3 z| := abs_add_three _ _ _
      _ ≤ 9 * Gw * S * (t - s) + 3 * Real.sqrt S * Lw * (t - s) +
          Dw * B * (volume C).toReal ^ (1 / 3 : ℝ) * (t - s) ^ (1 / 3 : ℝ) := by
        linarith only [hK1, hK2, hK3]
      _ ≤ (9 * S + 3 * Real.sqrt S + B * (volume C).toReal ^ (1 / 3 : ℝ)) *
          ((t - s) * (Lw + Gw) + (t - s) ^ (1 / 3 : ℝ) * Dw) := by
        have h1 : 0 ≤ 9 * S * ((t - s) * Lw) := by positivity
        have h2 : 0 ≤ 3 * Real.sqrt S * ((t - s) * Gw) := by positivity
        have h3 : 0 ≤ B * (volume C).toReal ^ (1 / 3 : ℝ) * ((t - s) * (Lw + Gw)) := by
          positivity
        have h4 : 0 ≤ 9 * S * ((t - s) ^ (1 / 3 : ℝ) * Dw) := by positivity
        have h5 : 0 ≤ 3 * Real.sqrt S * ((t - s) ^ (1 / 3 : ℝ) * Dw) := by positivity
        nlinarith only [h1, h2, h3, h4, h5]
  intro s t hs ht
  rcases le_total s t with hst | hts
  · have h := hmain s t hs ht hst
    rwa [abs_of_nonneg (sub_nonneg.mpr hst)]
  · have h := hmain t s ht hs hts
    rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
    exact h

end ESS

end
