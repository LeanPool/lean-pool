/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Rellich Balls Core

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open Set Metric
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Foundation

/-- A bounded smooth cutoff turns a local vector-valued `L²` field into a
global `L²` field when its support lies in the local region. -/
theorem memLp_two_cutoff_vec3_global
    {K : Set Vec3} (hK : MeasurableSet K)
    (f : Vec3 → L2Vec3) (hf : MemLp f 2 (volume.restrict K))
    (χ : Vec3 → ℝ) (hχ : Measurable χ) (hχsupport : tsupport χ ⊆ K)
    (hχbound : ∀ x, |χ x| ≤ 1) :
    MemLp (fun x => χ x • f x) 2 (volume : Measure Vec3) := by
  have hlocal : MemLp (fun x => χ x • f x) 2 (volume.restrict K) := by
    apply (MemLp.of_le_mul (c := (1 : ℝ)) hf
      (hχ.aestronglyMeasurable.smul hf.aestronglyMeasurable))
    filter_upwards [] with x
    change ‖χ x • f x‖ ≤ _
    rw [norm_smul]
    simpa only [Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (hχbound x) (norm_nonneg (f x))
  have hglobal : MemLp (K.indicator (fun x => χ x • f x)) 2 volume :=
    (memLp_indicator_iff_restrict hK).2 hlocal
  have heq : K.indicator (fun x => χ x • f x) = (fun x => χ x • f x) := by
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · have hχzero : χ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx' => hx (hχsupport hx'))
      simp [hx, hχzero]
  rw [heq] at hglobal
  exact hglobal

/-- The global `L²` norm after a cutoff bounded by one does not exceed the
local `L²` norm of the original field. -/
theorem eLpNorm_two_cutoff_vec3_global_le
    {K : Set Vec3} (hK : MeasurableSet K)
    (f : Vec3 → L2Vec3) (hf : MemLp f 2 (volume.restrict K))
    (χ : Vec3 → ℝ) (hχ : Measurable χ) (hχsupport : tsupport χ ⊆ K)
    (hχbound : ∀ x, |χ x| ≤ 1) :
    eLpNorm (fun x => χ x • f x) 2 (volume : Measure Vec3) ≤
      eLpNorm f 2 (volume.restrict K) := by
  have hmem := memLp_two_cutoff_vec3_global hK f hf χ hχ hχsupport hχbound
  have hpoint : ∀ x : Vec3,
      ‖χ x • f x‖ ≤ ‖K.indicator f x‖ := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, norm_smul, Real.norm_eq_abs]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hχbound x) (norm_nonneg (f x))
    · have hχzero : χ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx' => hx (hχsupport hx'))
      simp [hχzero, Set.indicator_of_notMem hx]
  calc
    eLpNorm (fun x => χ x • f x) 2 volume ≤
        eLpNorm (K.indicator f) 2 volume :=
      eLpNorm_mono_ae hmem.aestronglyMeasurable (Filter.Eventually.of_forall hpoint)
    _ = eLpNorm f 2 (volume.restrict K) := eLpNorm_indicator_eq_eLpNorm_restrict hK

/-- A local squared-integral bound controls the Hilbert norm of a bounded
cutoff of the field. -/
theorem norm_toLp_two_cutoff_vec3_le
    {K : Set Vec3} (hK : MeasurableSet K)
    (f : Vec3 → L2Vec3) (hf : MemLp f 2 (volume.restrict K))
    (χ : Vec3 → ℝ) (hχ : Measurable χ) (hχsupport : tsupport χ ⊆ K)
    (hχbound : ∀ x, |χ x| ≤ 1)
    (M : ℝ≥0∞) (hM : M < ⊤)
    (henergy : ∫⁻ x in K, ‖f x‖ₑ ^ (2 : ℝ) ∂volume ≤ M) :
    ‖(memLp_two_cutoff_vec3_global hK f hf χ hχ hχsupport hχbound).toLp
      (fun x => χ x • f x)‖ ≤ (M ^ (1 / 2 : ℝ)).toReal := by
  let hcut := memLp_two_cutoff_vec3_global hK f hf χ hχ hχsupport hχbound
  have hlocal : eLpNorm f 2 (volume.restrict K) ≤ M ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hf.aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofNat] using
      (ENNReal.rpow_le_rpow henergy (by norm_num : (0 : ℝ) ≤ 1 / 2))
  rw [Lp.norm_toLp]
  have hMroot : M ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne
  exact ENNReal.toReal_mono hMroot.ne
    ((eLpNorm_two_cutoff_vec3_global_le hK f hf χ hχ hχsupport hχbound).trans hlocal)

/-- The weak-gradient ball Poincaré estimate in `L⁶` implies the corresponding
`L²` estimate, with the finite-measure factor made explicit. This is the
small-ball estimate used in the spatial compactness argument for
lem:compactness. -/
theorem eLpNorm_two_sub_average_le_of_h1_on_euclidean_ball
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (u : CKN.H1Function (CKN.euclideanBall x₀ r)) :
    eLpNorm
        (fun x => u.toFun x -
          average (volume.restrict (CKN.euclideanBall x₀ r)) u.toFun)
        2 (volume.restrict (CKN.euclideanBall x₀ r)) ≤
      CKN.sobolevPoincareL6Constant *
        eLpNorm u.grad 2 (volume.restrict (CKN.euclideanBall x₀ r)) *
        (volume (CKN.euclideanBall x₀ r)) ^ (1 / 3 : ℝ) := by
  let B : Set Vec3 := CKN.euclideanBall x₀ r
  let μ : Measure Vec3 := volume.restrict B
  have hmeas : AEStronglyMeasurable
      (fun x => u.toFun x - average μ u.toFun) μ := by
    exact u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := (2 : ℝ≥0∞)) (q := (6 : ℝ≥0∞)) (by norm_num) hmeas
  have hpoincare := CKN.sobolevPoincare_L6_ball_weak x₀ hr u
  have hpoincare' :
      eLpNorm
          (fun x => u.toFun x - average μ u.toFun)
          6 μ ≤
        CKN.sobolevPoincareL6Constant * eLpNorm u.grad 2 μ := by
    simpa [B, μ, CKN.lpNormOn, CKN.weakGradientLpNormOn] using hpoincare
  have hcompareBall :
      eLpNorm
          (fun x => u.toFun x -
            average (volume.restrict (CKN.euclideanBall x₀ r)) u.toFun)
          2 (volume.restrict (CKN.euclideanBall x₀ r)) ≤
        eLpNorm
          (fun x => u.toFun x -
            average (volume.restrict (CKN.euclideanBall x₀ r)) u.toFun)
          6 (volume.restrict (CKN.euclideanBall x₀ r)) *
          (volume (CKN.euclideanBall x₀ r)) ^
            ((2 : ℝ≥0∞).toReal⁻¹ - (6 : ℝ≥0∞).toReal⁻¹) := by
    simpa [B, μ] using hcompare
  calc
    eLpNorm
        (fun x => u.toFun x -
          average (volume.restrict (CKN.euclideanBall x₀ r)) u.toFun)
        2 (volume.restrict (CKN.euclideanBall x₀ r)) ≤
        eLpNorm
          (fun x => u.toFun x -
            average (volume.restrict (CKN.euclideanBall x₀ r)) u.toFun)
          6 (volume.restrict (CKN.euclideanBall x₀ r)) *
          (volume (CKN.euclideanBall x₀ r)) ^ (1 / 3 : ℝ) := by
      calc
        _ ≤ _ := hcompareBall
        _ = _ := by congr 2; norm_num [ENNReal.toReal_ofNat]
    _ ≤ (CKN.sobolevPoincareL6Constant *
          eLpNorm u.grad 2 (volume.restrict (CKN.euclideanBall x₀ r))) *
          (volume (CKN.euclideanBall x₀ r)) ^ (1 / 3 : ℝ) := by
      gcongr
    _ = _ := by ring

/-- A finite squared vec3EuclideanNorm integral gives local `L²` membership
in the CKN vector-valued function space. -/
theorem memLp_two_vec3_of_lintegral_sq_lt_top
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → Vec3)
    (hf : Measurable f)
    (hfinite : ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (f x)) ^ (2 : ℝ)
      ∂μ < ∞) :
    MemLp (fun x => (WithLp.toLp 2 (f x) : L2Vec3)) 2 μ := by
  let g : α → L2Vec3 := fun x => WithLp.toLp 2 (f x)
  have hg : Measurable g := by
    exact (WithLp.measurable_toLp (p := (2 : ℝ≥0∞)) (X := Vec3)).comp hf
  have hnorm (x : α) : ‖g x‖ₑ = ENNReal.ofReal (vec3EuclideanNorm (f x)) := by
    rw [← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
  have hfinite' : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
    calc
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ =
          ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (f x)) ^ (2 : ℝ) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [] with x
        rw [hnorm x]
      _ < ∞ := hfinite
  have hgSM : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hnormLp : MemLp (fun x => ‖g x‖) 2 μ := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) (by norm_num) hgSM.norm]
    simpa [ENNReal.toReal_ofNat] using hfinite'
  exact (memLp_norm_iff hgSM).mp hnormLp

/-- A finite squared integral of a measurable real function gives `L²`
membership. -/
theorem memLp_two_real_of_lintegral_sq_lt_top
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Measurable f)
    (hfinite : ∫⁻ x, ENNReal.ofReal |f x| ^ (2 : ℝ) ∂μ < ∞) :
    MemLp f 2 μ := by
  have hsm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hsm]
  simpa [ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs] using hfinite

/-- The same squared-norm bound gives `L²` membership for Vec3 with its
native CKN function-space carrier. -/
theorem memLp_two_vec3_raw_of_lintegral_sq_lt_top
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → Vec3)
    (hf : Measurable f)
    (hfinite : ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (f x)) ^ (2 : ℝ)
      ∂μ < ∞) :
    MemLp f 2 μ := by
  rw [MeasureTheory.memLp_pi_iff]
  intro i
  apply memLp_two_real_of_lintegral_sq_lt_top μ (fun x => f x i)
  · exact (measurable_pi_apply i).comp hf
  · have hnormSq (x : α) : vec3EuclideanNorm (f x) ^ 2 =
        ∑ j : Fin 3, (f x j) ^ 2 := by
      rw [vec3EuclideanNorm, Real.sq_sqrt]
      exact Finset.sum_nonneg fun j hj => sq_nonneg (f x j)
    have hcomponent (x : α) :
        (f x i) ^ 2 ≤ vec3EuclideanNorm (f x) ^ 2 := by
      rw [hnormSq]
      exact Finset.single_le_sum
        (fun j hj => sq_nonneg (f x j)) (Finset.mem_univ i)
    have hpoint (x : α) :
        ENNReal.ofReal |f x i| ^ (2 : ℝ) ≤
          ENNReal.ofReal (vec3EuclideanNorm (f x)) ^ (2 : ℝ) := by
      have hpow (a : ℝ) (ha : 0 ≤ a) : ENNReal.ofReal a ^ (2 : ℝ) =
          ENNReal.ofReal (a ^ 2) := by
        calc
          _ = ENNReal.ofReal a ^ (2 : ℕ) := ENNReal.rpow_natCast _ _
          _ = ENNReal.ofReal (a ^ 2) := (ENNReal.ofReal_pow ha 2).symm
      rw [hpow |f x i| (abs_nonneg _), hpow (vec3EuclideanNorm (f x))
        (by unfold vec3EuclideanNorm; positivity)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [sq_abs] using hcomponent x
    exact lt_of_le_of_lt (lintegral_mono (μ := μ) hpoint) hfinite

/-- A finite local space-time squared norm gives `L²` membership of almost
every spatial slice. -/
theorem ae_memLp_two_vec3_slice_of_lintegral_sq_lt_top
    {K : Set Vec3} {J : Set ℝ} (f : ParabolicPoint → Vec3)
    (hf : Measurable f)
    (hfinite :
      (∫⁻ t in J, ∫⁻ x in K,
        ENNReal.ofReal (vec3EuclideanNorm (f (x, t))) ^ (2 : ℝ) ∂volume) < ∞) :
    ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x => (WithLp.toLp 2 (f (x, t)) : L2Vec3))
        2 (volume.restrict K) := by
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ (2 : ℝ)
  have hF : Measurable F := by
    dsimp [F]
    have hnorm : Measurable (fun z => vec3EuclideanNorm (f z)) := by
      unfold vec3EuclideanNorm
      fun_prop
    fun_prop
  let A : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in K, F (x, t) ∂volume
  have hA : Measurable A := by
    dsimp [A]
    exact hF.lintegral_prod_left'
  have hAE : ∀ᵐ t ∂(volume.restrict J), A t < ∞ := by
    apply ae_lt_top' hA.aemeasurable
    simpa [A, F] using hfinite.ne
  filter_upwards [hAE] with t ht
  apply memLp_two_vec3_of_lintegral_sq_lt_top
    (volume.restrict K) (fun x => f (x, t)) ?_ ?_
  · exact hf.comp measurable_prodMk_right
  · simpa [A, F] using ht

/-- Finite local space-time squared norm gives native vector-valued `L²`
membership of almost every spatial slice. -/
theorem ae_memLp_two_vec3_raw_slice_of_lintegral_sq_lt_top
    {K : Set Vec3} {J : Set ℝ} (f : ParabolicPoint → Vec3)
    (hf : Measurable f)
    (hfinite :
      (∫⁻ t in J, ∫⁻ x in K,
        ENNReal.ofReal (vec3EuclideanNorm (f (x, t))) ^ (2 : ℝ) ∂volume) < ∞) :
    ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x => f (x, t)) 2 (volume.restrict K) := by
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ (2 : ℝ)
  have hF : Measurable F := by
    dsimp [F]
    have hnorm : Measurable (fun z => vec3EuclideanNorm (f z)) := by
      unfold vec3EuclideanNorm
      fun_prop
    fun_prop
  let A : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in K, F (x, t) ∂volume
  have hA : Measurable A := by
    dsimp [A]
    exact hF.lintegral_prod_left'
  have hAE : ∀ᵐ t ∂(volume.restrict J), A t < ∞ := by
    apply ae_lt_top' hA.aemeasurable
    simpa [A, F] using hfinite.ne
  filter_upwards [hAE] with t ht
  exact memLp_two_vec3_raw_of_lintegral_sq_lt_top
    (volume.restrict K) (fun x => f (x, t))
    (hf.comp measurable_prodMk_right) (by simpa [A, F] using ht)

/-- Finite spatial gradient energy gives `L²` membership of the matrix field
on that spatial region. -/
theorem memLp_two_spatial_gradient_of_finite_energy
    {K : Set Vec3} (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (t : ℝ)
    (hDu : Measurable Du)
    (henergy : ∫⁻ x in K,
      ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume < ∞) :
    MemLp (fun x => Du (x, t)) 2 (volume.restrict K) := by
  have hslice : Measurable (fun x : Vec3 => Du (x, t)) :=
    hDu.comp measurable_prodMk_right
  rw [MeasureTheory.memLp_pi_iff]
  intro i
  rw [MeasureTheory.memLp_pi_iff]
  intro j
  apply memLp_two_real_of_lintegral_sq_lt_top
  · exact Measurable.eval (a := j) (Measurable.eval (a := i) hslice)
  · have hterm (x : Vec3) :
      (Du (x, t) i j) ^ 2 ≤ CKN.spatialGradientSq u Du (x, t) := by
      unfold CKN.spatialGradientSq
      calc
        (Du (x, t) i j) ^ 2 ≤ ∑ k : Fin 3, (Du (x, t) i k) ^ 2 :=
          Finset.single_le_sum (fun k hk => sq_nonneg (Du (x, t) i k))
            (Finset.mem_univ j)
        _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, (Du (x, t) k l) ^ 2 :=
          Finset.single_le_sum
            (fun k hk => Finset.sum_nonneg fun l hl => sq_nonneg (Du (x, t) k l))
            (Finset.mem_univ i)
    have hpoint (x : Vec3) :
        ENNReal.ofReal |Du (x, t) i j| ^ (2 : ℝ) ≤
          ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) := by
      have hpow : ENNReal.ofReal |Du (x, t) i j| ^ (2 : ℝ) =
          ENNReal.ofReal ((Du (x, t) i j) ^ 2) := by
        calc
          _ = ENNReal.ofReal |Du (x, t) i j| ^ (2 : ℕ) :=
            ENNReal.rpow_natCast _ _
          _ = ENNReal.ofReal (|Du (x, t) i j| ^ 2) :=
            (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
          _ = _ := by rw [sq_abs]
      rw [hpow]
      exact ENNReal.ofReal_le_ofReal (hterm x)
    have hmono := lintegral_mono (μ := volume.restrict K) hpoint
    exact lt_of_le_of_lt hmono henergy

/-- Finite local space-time gradient energy gives `L²` membership of almost
every spatial gradient slice. -/
theorem ae_memLp_two_spatial_gradient_slice_of_lintegral_lt_top
    {K : Set Vec3} {J : Set ℝ} (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (hDu : Measurable Du)
    (hfinite :
      (∫⁻ t in J, ∫⁻ x in K,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) < ∞) :
    ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x => Du (x, t)) 2 (volume.restrict K) := by
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (CKN.spatialGradientSq u Du z)
  have hsq : Measurable (fun z => CKN.spatialGradientSq u Du z) := by
    unfold CKN.spatialGradientSq
    fun_prop
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  let A : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in K, F (x, t) ∂volume
  have hA : Measurable A := by
    dsimp [A]
    exact hF.lintegral_prod_left'
  have hAE : ∀ᵐ t ∂(volume.restrict J), A t < ∞ := by
    apply ae_lt_top' hA.aemeasurable
    simpa [A, F] using hfinite.ne
  filter_upwards [hAE] with t ht
  exact memLp_two_spatial_gradient_of_finite_energy u Du t hDu (by
    simpa [A, F] using ht)

/-- Slice bounds and the weak-gradient identity restrict a vector field to a
scalar `H¹` function on each Euclidean ball. The matrix convention is
`Du x i j = ∂ⱼ uᵢ`. -/
theorem exists_h1_component_on_euclidean_ball_of_slice_data
    {U : Set Vec3} {x₀ : Vec3} {r : ℝ}
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3)
    (hu : MemLp u 2 (volume.restrict U))
    (hDu : MemLp Du 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u x i) (fun x => Du x i))
    (hball : CKN.euclideanBall x₀ r ⊆ U) :
    ∀ i : Fin 3, ∃ v : CKN.H1Function (CKN.euclideanBall x₀ r),
      v.toFun = (fun x => u x i) ∧ v.grad = (fun x => Du x i) := by
  intro i
  have hBopen : IsOpen (CKN.euclideanBall x₀ r) := by
    change IsOpen {x : Vec3 | CKN.euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (CKN.contDiff_euclideanSqDist_left x₀).continuous
      continuous_const
  let v : CKN.H1Function (CKN.euclideanBall x₀ r) := {
    toFun := fun x => u x i
    grad := fun x => Du x i
    memL2 := (MemLp.eval hu i).mono_measure
      (Measure.restrict_mono_set volume hball)
    gradMemL2 := fun j =>
      (MemLp.eval (MemLp.eval hDu i) j).mono_measure
        (Measure.restrict_mono_set volume hball)
    hasWeakGradient := (hweak i).restrict hBopen hball }
  exact ⟨v, rfl, rfl⟩

/-- The field-level slice bounds and weak-gradient identities imply the scalar
ball-average error estimate on every component. This is the estimate later
integrated in time in the local compactness argument. -/
theorem eLpNorm_two_component_sub_average_le_of_slice_data
    {U : Set Vec3} {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3)
    (hu : MemLp u 2 (volume.restrict U))
    (hDu : MemLp Du 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u x i) (fun x => Du x i))
    (hball : CKN.euclideanBall x₀ r ⊆ U)
     :
    ∀ i : Fin 3,
      eLpNorm
        (fun x => u x i - average (volume.restrict (CKN.euclideanBall x₀ r))
          (fun y => u y i))
        2 (volume.restrict (CKN.euclideanBall x₀ r)) ≤
        CKN.sobolevPoincareL6Constant *
          eLpNorm (fun x => Du x i) 2
            (volume.restrict (CKN.euclideanBall x₀ r)) *
          (volume (CKN.euclideanBall x₀ r)) ^ (1 / 3 : ℝ) := by
  intro i
  obtain ⟨v, hv, hgrad⟩ :=
    exists_h1_component_on_euclidean_ball_of_slice_data u Du hu hDu hweak hball i
  simpa [hv, hgrad] using
    eLpNorm_two_sub_average_le_of_h1_on_euclidean_ball x₀ hr v

/-- An `L²` seminorm estimate for scalar functions gives the corresponding
inequality between their squared-integral densities. -/
theorem lintegral_sq_le_of_eLpNorm_two_le
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [ContinuousENorm E]
    [NormedAddCommGroup F] [ContinuousENorm F]
    {μ : Measure α} {f : α → E} {g : α → F} {C : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfg : eLpNorm f 2 μ ≤ C * eLpNorm g 2 μ) :
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      C ^ (2 : ℕ) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  have hf2 : eLpNorm f (2 : NNReal) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (by norm_num : (2 : NNReal) ≠ 0) hf
  have hg2 : eLpNorm g (2 : NNReal) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (by norm_num : (2 : NNReal) ≠ 0) hg
  have hfg2 : eLpNorm f 2 μ ^ (2 : ℝ) ≤
      (C * eLpNorm g 2 μ) ^ (2 : ℝ) := by
    gcongr
  calc
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = eLpNorm f 2 μ ^ (2 : ℝ) := by
      simpa using hf2.symm
    _ ≤ (C * eLpNorm g 2 μ) ^ (2 : ℝ) := hfg2
    _ = C ^ (2 : ℕ) * eLpNorm g 2 μ ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      simp only [ENNReal.rpow_ofNat]
    _ = C ^ (2 : ℕ) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
      rw [show eLpNorm g 2 μ = eLpNorm g (2 : NNReal) μ by norm_num]
      rw [← hg2]

/-- Scalar ball averages of a jointly measurable field are measurable in
time. -/
theorem measurable_average_scalar_slice
    {B : Set Vec3} (f : ParabolicPoint → ℝ) (hf : Measurable f) :
    Measurable
      (fun t : ℝ => average (volume.restrict B) (fun x => f (x, t))) := by
  have hswap : StronglyMeasurable (fun z : ℝ × Vec3 => f z.swap) :=
    hf.stronglyMeasurable.comp_measurable measurable_swap
  have hint : StronglyMeasurable
      (fun t : ℝ => ∫ x : Vec3, f (x, t) ∂(volume.restrict B)) := by
    simpa [Prod.swap] using hswap.integral_prod_right'
  have havg (t : ℝ) : average (volume.restrict B) (fun x => f (x, t)) =
      ((volume.restrict B).real Set.univ)⁻¹ •
        ∫ x : Vec3, f (x, t) ∂(volume.restrict B) := by
    exact average_eq (volume.restrict B) (fun x : Vec3 => f (x, t))
  have havgStrong : StronglyMeasurable
      (fun t : ℝ => average (volume.restrict B) (fun x => f (x, t))) := by
    rw [funext havg]
    exact hint.const_smul ((volume.restrict B).real Set.univ)⁻¹
  exact havgStrong.measurable

/-- Almost-everywhere slice `L²` estimates integrate to the corresponding
space-time squared-integral estimate on a product of measurable regions. -/
theorem lintegral_prod_sq_le_of_ae_eLpNorm_two_le
    {K : Set Vec3} {J : Set ℝ} {E F : Type*}
    [NormedAddCommGroup E] [ContinuousENorm E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [ContinuousENorm F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {f : ParabolicPoint → E} {g : ParabolicPoint → F}
    {C : ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hle : ∀ᵐ t ∂(volume.restrict J),
      eLpNorm (fun x => f (x, t)) 2 (volume.restrict K) ≤
        C * eLpNorm (fun x => g (x, t)) 2 (volume.restrict K)) :
    (∫⁻ t in J, ∫⁻ x in K, ‖f (x, t)‖ₑ ^ (2 : ℝ) ∂volume) ≤
      C ^ (2 : ℕ) *
        (∫⁻ t in J, ∫⁻ x in K, ‖g (x, t)‖ₑ ^ (2 : ℝ) ∂volume) := by
  let F : ParabolicPoint → ℝ≥0∞ := fun z => ‖f z‖ₑ ^ (2 : ℝ)
  let G : ParabolicPoint → ℝ≥0∞ := fun z => ‖g z‖ₑ ^ (2 : ℝ)
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  let A : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in K, F (x, t) ∂volume
  let B : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in K, G (x, t) ∂volume
  have hA : Measurable A := by
    dsimp [A]
    exact hF.lintegral_prod_left'
  have hB : Measurable B := by
    dsimp [B]
    exact hG.lintegral_prod_left'
  have hpoint : ∀ᵐ t ∂(volume.restrict J), A t ≤ C ^ (2 : ℕ) * B t := by
    filter_upwards [hle] with t ht
    have hfst : AEStronglyMeasurable (fun x => f (x, t)) (volume.restrict K) :=
      (hf.comp measurable_prodMk_right).aestronglyMeasurable
    have hgst : AEStronglyMeasurable (fun x => g (x, t)) (volume.restrict K) :=
      (hg.comp measurable_prodMk_right).aestronglyMeasurable
    have hsq := lintegral_sq_le_of_eLpNorm_two_le hfst hgst ht
    simpa [A, B, F, G] using hsq
  calc
    (∫⁻ t in J, ∫⁻ x in K, ‖f (x, t)‖ₑ ^ (2 : ℝ) ∂volume) ≤
        ∫⁻ t in J, C ^ (2 : ℕ) * B t ∂volume := by
      exact lintegral_mono_ae hpoint
    _ = C ^ (2 : ℕ) *
        (∫⁻ t in J, ∫⁻ x in K, ‖g (x, t)‖ₑ ^ (2 : ℝ) ∂volume) := by
      rw [lintegral_const_mul'' _ hB.aemeasurable]

/-- The local slice bound, integrated gradient bound, and almost-everywhere
weak-gradient identity give the ball-average error estimate on almost every
time slice. -/
theorem ae_eLpNorm_two_component_sub_average_le_of_field_energy
    {U : Set Vec3} {J : Set ℝ} {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (huMeas : Measurable u)
    (hDuMeas : Measurable Du)
    (huenergy :
      (∫⁻ t in J, ∫⁻ x in U,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (2 : ℝ) ∂volume) < ∞)
    (hweak : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    (henergy :
      (∫⁻ t in J, ∫⁻ x in U,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) < ∞)
    (hball : CKN.euclideanBall x₀ r ⊆ U) :
    ∀ᵐ t ∂(volume.restrict J),
      ∀ i : Fin 3,
        eLpNorm
          (fun x => u (x, t) i -
            average (volume.restrict (CKN.euclideanBall x₀ r))
              (fun y => u (y, t) i))
          2 (volume.restrict (CKN.euclideanBall x₀ r)) ≤
      CKN.sobolevPoincareL6Constant *
            eLpNorm (fun x => Du (x, t) i) 2
              (volume.restrict (CKN.euclideanBall x₀ r)) *
            (volume (CKN.euclideanBall x₀ r)) ^ (1 / 3 : ℝ) := by
  have huAE := ae_memLp_two_vec3_raw_slice_of_lintegral_sq_lt_top
    u huMeas huenergy
  have hDuAE := ae_memLp_two_spatial_gradient_slice_of_lintegral_lt_top
    u Du hDuMeas henergy
  filter_upwards [huAE, hDuAE, hweak] with t htU htDu htweak i
  exact eLpNorm_two_component_sub_average_le_of_slice_data hr
    (fun x => u (x, t)) (fun x => Du (x, t)) htU htDu htweak hball i

/-- The almost-everywhere ball Poincaré estimates integrate to a space-time
bound for the error from the measurable time-dependent ball averages. -/
theorem lintegral_component_ball_average_error_le_of_field_energy
    {U : Set Vec3} {J : Set ℝ} {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (huMeas : Measurable u) (hDuMeas : Measurable Du)
    (huenergy :
      (∫⁻ t in J, ∫⁻ x in U,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (2 : ℝ) ∂volume) < ∞)
    (hweak : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    (henergy :
      (∫⁻ t in J, ∫⁻ x in U,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) < ∞)
    (hball : CKN.euclideanBall x₀ r ⊆ U) (i : Fin 3) :
    (∫⁻ t in J, ∫⁻ x in CKN.euclideanBall x₀ r,
      ENNReal.ofReal |u (x, t) i -
        average (volume.restrict (CKN.euclideanBall x₀ r))
          (fun y => u (y, t) i)| ^ (2 : ℝ) ∂volume) ≤
      (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall x₀ r)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
      (∫⁻ t in J, ∫⁻ x in CKN.euclideanBall x₀ r,
        ‖Du (x, t) i‖ₑ ^ (2 : ℝ) ∂volume) := by
  let B : Set Vec3 := CKN.euclideanBall x₀ r
  let ui : ParabolicPoint → ℝ := fun z => u z i
  have huiMeas : Measurable ui := (measurable_pi_apply i).comp huMeas
  let avg : ℝ → ℝ := fun t => average (volume.restrict B) (fun y => ui (y, t))
  have havgMeas : Measurable avg :=
    measurable_average_scalar_slice (B := B) ui huiMeas
  let f : ParabolicPoint → ℝ := fun z => ui z - avg z.2
  let g : ParabolicPoint → Vec3 := fun z => Du z i
  have hfMeas : Measurable f := by
    dsimp [f, ui]
    exact huiMeas.sub (havgMeas.comp measurable_snd)
  have hgMeas : Measurable g := by
    dsimp [g]
    exact measurable_pi_apply i |>.comp hDuMeas
  let C : ℝ≥0∞ := CKN.sobolevPoincareL6Constant *
    (volume B) ^ (1 / 3 : ℝ)
  have hle : ∀ᵐ t ∂(volume.restrict J),
      eLpNorm (fun x => f (x, t)) 2 (volume.restrict B) ≤
        C * eLpNorm (fun x => g (x, t)) 2 (volume.restrict B) := by
    have hslice := ae_eLpNorm_two_component_sub_average_le_of_field_energy
      hr u Du huMeas hDuMeas huenergy hweak henergy hball
    filter_upwards [hslice] with t ht
    have hi := ht i
    simpa [f, g, C, B, avg, ui, mul_assoc, mul_left_comm, mul_comm] using hi
  have hsq := lintegral_prod_sq_le_of_ae_eLpNorm_two_le
    hfMeas hgMeas hle
  simpa [f, g, C, B, avg, ui, Real.enorm_eq_ofReal_abs] using hsq

end CKN.Foundation
