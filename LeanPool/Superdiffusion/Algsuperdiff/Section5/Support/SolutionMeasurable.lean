/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.FieldSolutionMap

/-!
# SolutionMeasurable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The solution is a measurable function of the sample

The sample enters the localized quantities only through the continuous matrix
field `a_m(ω)` on the closed cube, which is a measurable function of the sample.
The integral of the solution over a subset of the cube is a *continuous*
function of that field: subtracting the two weak equations bounds the energy of
the difference by the supremum distance of the fields, the zero-trace Poincaré
inequality converts the energy into the `L²` size, and Cauchy-Schwarz against
the constant one converts that into the integral.  Composing gives measurability
in the sample, and the ball-average characterization of a continuous
representative turns it into measurability of the pointwise values.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory Filter
open Algsuperdiff.Section4.Support
open scoped Matrix.Norms.Elementwise Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Auxiliary estimates -/

theorem abs_setIntegral_le_sqrt {U : Set (Vec d)} (hUfin : volume U ≠ ⊤) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    |∫ z in U, f z ∂volume| ≤
      Real.sqrt (volume.real U) * Real.sqrt (∫ z in U, f z ^ (2 : ℕ) ∂volume) := by
  have : IsFiniteMeasure (volume.restrict U) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hUfin
  have hfn : MemLp (fun z => |f z|) 2 (volume.restrict U) := by
    simpa [Real.norm_eq_abs] using hf.norm
  have hone : MemLp (fun _ : Vec d => (1 : ℝ)) 2 (volume.restrict U) :=
    memLp_const (μ := volume.restrict U) (p := 2) 1
  have h1 : |∫ z in U, f z ∂volume| ≤ ∫ z in U, |f z| ∂volume := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict U) (f := f)
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict U)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun z => abs_nonneg (f z))
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hfn) (by simpa using hone)
  have habs2 : ∫ z in U, |f z| ^ (2 : ℝ) ∂volume = ∫ z in U, f z ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show |f z| ^ (2 : ℝ) = f z ^ (2 : ℕ)
    rw [← sq_abs (f z), ← Real.rpow_natCast (|f z|) 2]
    norm_num
  have hone2 : ∫ _z in U, (1 : ℝ) ^ (2 : ℝ) ∂volume = volume.real U := by
    simp
  simp only [mul_one] at hhold
  rw [habs2, hone2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hhold
  calc |∫ z in U, f z ∂volume| ≤ ∫ z in U, |f z| ∂volume := h1
    _ ≤ Real.sqrt (∫ z in U, f z ^ (2 : ℕ) ∂volume) * Real.sqrt (volume.real U) := hhold
    _ = Real.sqrt (volume.real U) * Real.sqrt (∫ z in U, f z ^ (2 : ℕ) ∂volume) := by
        ring

private theorem sqrt_setIntegral_mono {U B : Set (Vec d)} (hBU : B ⊆ U)
    {f : Vec d → ℝ} (hUint : IntegrableOn (fun z => f z ^ (2 : ℕ)) U volume) :
    Real.sqrt (∫ z in B, f z ^ (2 : ℕ) ∂volume) ≤
      Real.sqrt (∫ z in U, f z ^ (2 : ℕ) ∂volume) := by
  refine Real.sqrt_le_sqrt ?_
  exact setIntegral_mono_set hUint (Filter.Eventually.of_forall fun z => by positivity)
    (LE.le.eventuallyLE hBU)

/-! ## 2. The parameter integral is continuous -/

/-- The integral of the parameter solution over a subset of the cube. -/
def fieldSetIntegral (M : ABKModel d) (y : Vec d) (n : ℤ) {g : Vec d → Vec d} {Kg : ℝ}
    (hKg : 0 ≤ Kg) (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    (B : Set (Vec d)) (A : ellipticCube M.nu y n) : ℝ :=
  ∫ z in B, (solutionOfField M y n hKg hg A).toFun z ∂volume

/-- **The parameter integral is continuous.** -/
theorem continuous_fieldSetIntegral (M : ABKModel d) (y : Vec d) (n : ℤ)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    {B : Set (Vec d)} (hBsub : B ⊆ cubeSetAt y n) :
    Continuous (fieldSetIntegral M y n hKg hg B) := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  have hfin : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  obtain ⟨CP, hCP, hpoin⟩ :=
    exists_poincare_integral_constant (isOpenBoundedConvexDomain_cubeSetAt y n)
  have hcubefin : volume (cubeSetAt y n) ≠ ⊤ :=
    ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne
  have hBfin : volume B ≠ ⊤ :=
    ((measure_mono hBsub).trans_lt (lt_top_iff_ne_top.2 hcubefin)).ne
  rw [Metric.continuous_iff]
  intro A0 eps heps
  obtain ⟨Lam0, hEll0⟩ := exists_isEllipticFieldOn_extendCoeff M.nu_pos y n A0.2
  have hu0 := isDirichletSolutionAt_solutionOfField M y n hKg hg A0
  have hE0nn : (0 : ℝ) ≤ Real.sqrt (∫ x in cubeSetAt y n,
      ‖(solutionOfField M y n hKg hg A0).grad x‖ ^ (2 : ℕ) ∂volume) := Real.sqrt_nonneg _
  set Const : ℝ := Real.sqrt (volume.real B) * CP *
      (M.nu⁻¹ * ((d : ℝ) * (d : ℝ)) *
        Real.sqrt (∫ x in cubeSetAt y n,
          ‖(solutionOfField M y n hKg hg A0).grad x‖ ^ (2 : ℕ) ∂volume)) with hConst
  have hConstNN : (0 : ℝ) ≤ Const := by
    rw [hConst]
    have : (0 : ℝ) ≤ M.nu⁻¹ := (inv_pos.2 M.nu_pos).le
    positivity
  refine ⟨eps / (Const + 1), by positivity, fun A hA => ?_⟩
  obtain ⟨LamA, hEllA⟩ := exists_isEllipticFieldOn_extendCoeff M.nu_pos y n A.2
  have huA := isDirichletSolutionAt_solutionOfField M y n hKg hg A
  -- the entrywise distance of the two coefficient fields on the cube
  have hentry : ∀ x ∈ cubeSetAt y n, ∀ i j,
      |extendCoeff y n A.1 x i j - extendCoeff y n A0.1 x i j| ≤ dist A.1 A0.1 := by
    intro x hx i j
    have hxK : x ∈ closedCubeAt y n := cubeSetAt_subset_closedCubeAt y n hx
    rw [extendCoeff_apply_of_mem A.1 hxK, extendCoeff_apply_of_mem A0.1 hxK]
    have hsub : A.1 ⟨x, hxK⟩ i j - A0.1 ⟨x, hxK⟩ i j =
        (A.1 ⟨x, hxK⟩ - A0.1 ⟨x, hxK⟩) i j := by
      rw [Matrix.sub_apply]
    rw [hsub]
    let _ : Norm C(closedCubeAt y n, Mat d) := ContinuousMap.instNorm
    let _ : SeminormedAddCommGroup C(closedCubeAt y n, Mat d) :=
      ContinuousMap.instSeminormedAddCommGroup
    calc |(A.1 ⟨x, hxK⟩ - A0.1 ⟨x, hxK⟩) i j| ≤ ‖A.1 ⟨x, hxK⟩ - A0.1 ⟨x, hxK⟩‖ := by
          simpa [Real.norm_eq_abs] using
            Matrix.norm_entry_le_entrywise_sup_norm
              (A := A.1 ⟨x, hxK⟩ - A0.1 ⟨x, hxK⟩) (i := i) (j := j)
      _ = ‖(A.1 - A0.1) ⟨x, hxK⟩‖ := by rfl
      _ ≤ ‖A.1 - A0.1‖ := (A.1 - A0.1).norm_coe_le_norm _
      _ = dist A.1 A0.1 := (dist_eq_norm A.1 A0.1).symm
  have hbv : MemVectorL2 (cubeSetAt y n) fun x =>
      matVecMul (extendCoeff y n A0.1 x) ((solutionOfField M y n hKg hg A0).grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll0
      (solutionOfField M y n hKg hg A0).grad_memVectorL2
  have hEnergy := sqrt_energy_grad_sub_le (dist_nonneg) hEllA hentry hbv huA hu0
  -- the zero-trace difference
  obtain ⟨w, hwf, hwg⟩ :
      ∃ w : H10Function (cubeSetAt y n),
        (∀ x, w.toH1Function.toFun x =
          (solutionOfField M y n hKg hg A).toFun x -
            (solutionOfField M y n hKg hg A0).toFun x) ∧
          (∀ x, w.toH1Function.grad x =
            (solutionOfField M y n hKg hg A).grad x -
              (solutionOfField M y n hKg hg A0).grad x) := by
    obtain ⟨w1, h1f, h1g⟩ := huA.1
    obtain ⟨w2, h2f, h2g⟩ := hu0.1
    refine ⟨w1 - w2, fun x => ?_, fun x => ?_⟩
    · rw [h1f x, h2f x]
      show (w1.toH1Function - w2.toH1Function).toFun x = _
      simp only [H1Function.sub_toFun]
    · rw [h1g x, h2g x]
      show (w1.toH1Function - w2.toH1Function).grad x = _
      simp only [H1Function.sub_grad]
  have hgradEq : (∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) =
      ∫ x in cubeSetAt y n,
        ‖(solutionOfField M y n hKg hg A).grad x -
          (solutionOfField M y n hKg hg A0).grad x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖w.toH1Function.grad x‖ ^ (2 : ℕ) =
      ‖(solutionOfField M y n hKg hg A).grad x -
        (solutionOfField M y n hKg hg A0).grad x‖ ^ (2 : ℕ)
    rw [hwg x]
  have hpoinW := hpoin w
  rw [hgradEq] at hpoinW
  -- the integral over `B`
  have hwL2 : MemLp w.toH1Function.toFun 2 (volume.restrict B) :=
    w.toH1Function.memL2.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hwL2U : IntegrableOn (fun z => w.toH1Function.toFun z ^ (2 : ℕ))
      (cubeSetAt y n) volume := w.toH1Function.memL2.integrable_sq
  have hsplit : fieldSetIntegral M y n hKg hg B A - fieldSetIntegral M y n hKg hg B A0 =
      ∫ z in B, w.toH1Function.toFun z ∂volume := by
    have : IsFiniteMeasure (volume.restrict B) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2 hBfin
    have hintA : IntegrableOn (solutionOfField M y n hKg hg A).toFun B volume :=
      ((solutionOfField M y n hKg hg A).memL2.mono_measure
        (Measure.restrict_mono hBsub le_rfl)).integrable one_le_two
    have hintA0 : IntegrableOn (solutionOfField M y n hKg hg A0).toFun B volume :=
      ((solutionOfField M y n hKg hg A0).memL2.mono_measure
        (Measure.restrict_mono hBsub le_rfl)).integrable one_le_two
    rw [fieldSetIntegral, fieldSetIntegral, ← integral_sub hintA hintA0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (solutionOfField M y n hKg hg A).toFun z -
      (solutionOfField M y n hKg hg A0).toFun z = w.toH1Function.toFun z
    rw [hwf z]
  rw [Real.dist_eq, hsplit]
  have hchain : |∫ z in B, w.toH1Function.toFun z ∂volume| ≤ Const * dist A.1 A0.1 := by
    calc |∫ z in B, w.toH1Function.toFun z ∂volume|
        ≤ Real.sqrt (volume.real B) *
            Real.sqrt (∫ z in B, w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) :=
          abs_setIntegral_le_sqrt hBfin hwL2
      _ ≤ Real.sqrt (volume.real B) *
            Real.sqrt (∫ z in cubeSetAt y n,
              w.toH1Function.toFun z ^ (2 : ℕ) ∂volume) := by
          exact mul_le_mul_of_nonneg_left (sqrt_setIntegral_mono hBsub hwL2U)
            (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (volume.real B) * (CP *
            Real.sqrt (∫ x in cubeSetAt y n,
              ‖(solutionOfField M y n hKg hg A).grad x -
                (solutionOfField M y n hKg hg A0).grad x‖ ^ (2 : ℕ) ∂volume)) := by
          exact mul_le_mul_of_nonneg_left hpoinW (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (volume.real B) * (CP *
            (M.nu⁻¹ * ((d : ℝ) * (d : ℝ) * dist A.1 A0.1) *
              Real.sqrt (∫ x in cubeSetAt y n,
                ‖(solutionOfField M y n hKg hg A0).grad x‖ ^ (2 : ℕ) ∂volume))) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEnergy hCP) (Real.sqrt_nonneg _)
      _ = Const * dist A.1 A0.1 := by rw [hConst]; ring
  have hdistlt : dist A.1 A0.1 < eps / (Const + 1) := by
    simpa [Subtype.dist_eq] using hA
  have hfinal : Const * dist A.1 A0.1 < eps := by
    have hCd : Const * dist A.1 A0.1 ≤ Const * (eps / (Const + 1)) :=
      mul_le_mul_of_nonneg_left hdistlt.le hConstNN
    have hfrac : Const * (eps / (Const + 1)) < eps := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [heps, hConstNN]
    linarith
  linarith [hchain, hfinal]

/-! ## 3. Measurability in the sample -/

theorem measurable_fieldSetIntegral (M : ABKModel d) (y : Vec d) (n : ℤ)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    {B : Set (Vec d)} (hBsub : B ⊆ cubeSetAt y n) :
    Measurable (fieldSetIntegral M y n hKg hg B) :=
  (continuous_fieldSetIntegral M y n hKg hg hBsub).measurable

/-- **The integral of the selected solution over a subset of the cube is a
measurable function of the sample.** -/
theorem measurable_setIntegral_solutionAt (M : ABKModel d) (m n : ℤ) (y : Vec d)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    {B : Set (Vec d)} (hBsub : B ⊆ cubeSetAt y n) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      ∫ z in B, (solutionAt M m n y omega hg).toFun z ∂volume := by
  obtain ⟨ell, hell⟩ := exists_closedCubeAt_subset_openCubeSet y n
  have hmeasA : Measurable fun omega : Cutoff.CutoffSample d =>
      (⟨coefficientCutoffRestrict M.nu m (closedCubeAt y n) omega,
        coefficientCutoffRestrict_mem_ellipticCube M m y n omega⟩ :
          ellipticCube M.nu y n) :=
    Measurable.subtype_mk
      (measurable_coefficientCutoffRestrict M.nu (closedCubeAt y n) m ell hell)
  have hcomp := (measurable_fieldSetIntegral M y n hKg hg hBsub).comp hmeasA
  have hEq : (fun omega : Cutoff.CutoffSample d =>
      ∫ z in B, (solutionAt M m n y omega hg).toFun z ∂volume) =
      fun omega : Cutoff.CutoffSample d =>
        fieldSetIntegral M y n hKg hg B
          ⟨coefficientCutoffRestrict M.nu m (closedCubeAt y n) omega,
            coefficientCutoffRestrict_mem_ellipticCube M m y n omega⟩ := by
    funext omega
    have h1 := isDirichletSolutionAt_solutionAt M m n y omega hg
    have h2 := isDirichletSolutionAt_solutionOfField_cutoff M m y n omega hKg hg
    have hae := (isDirichletSolutionAt_ae_unique_cutoff M m n y omega h1 h2).2
    rw [fieldSetIntegral]
    exact integral_congr_ae (hae.filter_mono (ae_mono (Measure.restrict_mono hBsub le_rfl)))
  rw [hEq]
  exact hcomp

end

end Algsuperdiff.Section5.Support
