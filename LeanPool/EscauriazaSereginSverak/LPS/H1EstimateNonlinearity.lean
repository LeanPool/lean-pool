/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSpatial
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportPairing
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The nonlinear pairing in the strong `H¹` estimate

The finite-Serrin spatial interpolation controls the convection term paired
with a square-integrable Laplacian (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The componentwise trace of a square-integrable Hessian is a
square-integrable vector field (`lem:lps-H1-estimate`). -/
theorem lps_h1_laplacian_memLp_two
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3} {lap : Vec3 → Vec3}
    (hD2u : MemLp D2u 2 volume)
    (hlap : ∀ x i, lap x i = ∑ j : Fin 3, D2u x i j j) :
    MemLp lap 2 volume := by
  apply memLp_pi_iff.mpr
  intro i
  rw [show (fun x : Vec3 => lap x i) =
    fun x => ∑ j : Fin 3, D2u x i j j by
      funext x
      exact hlap x i]
  exact memLp_finsetSum Finset.univ fun j _ =>
    ((hD2u.eval i).eval j).eval j

/-- For a smooth compactly supported vector field, the summed squared
Hessian norm equals the squared vector-Laplacian norm componentwise. This is
the dense smooth case of the whole-space `H²` bridge in
`lem:lps-H1-estimate`. -/
theorem lps_h1_smooth_hessian_eq_laplacian
    {u : Vec3 → Vec3} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huc : HasCompactSupport u) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      ∫ x : Vec3,
        (mixedSecond (fun y : Vec3 => u y i) j k x) ^ (2 : ℕ)) =
      ∑ i : Fin 3, ∫ x : Vec3,
        (spatialLaplacian (fun y : Vec3 => u y i) x) ^ (2 : ℕ) := by
  calc
    _ = ∑ i : Fin 3, ∫ x : Vec3,
        (spatialLaplacian (fun y : Vec3 => u y i) x) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact CKN.hessian_l2_eq_laplacian_l2
        (contDiff_pi.mp hu i) (huc.comp_left (g := fun v : Vec3 => v i) rfl)

private theorem lps_h1_aesm_finset_sum
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {f : ι → α → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∑ i, f i x) μ := by
  classical
  have hsum (s : Finset ι) :
      AEStronglyMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
    induction s using Finset.induction_on with
    | empty => simpa using (aestronglyMeasurable_const (b := (0 : ℝ)))
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hf i).add ih
  simpa using hsum Finset.univ

private theorem lps_h1_convection_laplacian_pointwise
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {lap : Vec3 → Vec3} (x : Vec3) :
    |∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
      3 * vec3EuclideanNorm (u x) *
        (∑ i : Fin 3, ‖Du x i‖) * vec3EuclideanNorm (lap x) := by
  let U := vec3EuclideanNorm (u x)
  let H := ∑ i : Fin 3, ‖Du x i‖
  let L := vec3EuclideanNorm (lap x)
  have hNi (i : Fin 3) :
      |∑ j : Fin 3, u x j * Du x i j| ≤ 3 * U * ‖Du x i‖ := by
    calc
      |∑ j : Fin 3, u x j * Du x i j| ≤
          ∑ j : Fin 3, |u x j * Du x i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, U * ‖Du x i‖ := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [abs_mul]
        exact mul_le_mul
          (CKN.Foundation.Parabolic.abs_apply_le_vec3EuclideanNorm (u x) j)
          (by
            simpa only [Real.norm_eq_abs] using
              (norm_le_pi_norm (Du x i) j))
          (abs_nonneg _) (vec3EuclideanNorm_nonneg _)
      _ = 3 * U * ‖Du x i‖ := by
        simp [U, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hLap (i : Fin 3) : |lap x i| ≤ L :=
    CKN.Foundation.Parabolic.abs_apply_le_vec3EuclideanNorm (lap x) i
  have hsum :
      |∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
        ∑ i : Fin 3, |(∑ j : Fin 3, u x j * Du x i j) * lap x i| :=
    Finset.abs_sum_le_sum_abs _ _
  calc
    |∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
        ∑ i : Fin 3, |(∑ j : Fin 3, u x j * Du x i j) * lap x i| := hsum
    _ ≤ ∑ i : Fin 3, (3 * U * ‖Du x i‖) * L := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul]
      exact mul_le_mul (hNi i) (hLap i) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) (vec3EuclideanNorm_nonneg _))
          (norm_nonneg _))
    _ = 3 * U * L * H := by
      calc
        _ = ∑ i : Fin 3, (3 * U * L) * ‖Du x i‖ := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = (3 * U * L) * ∑ i : Fin 3, ‖Du x i‖ := (Finset.mul_sum _ _ _).symm
        _ = 3 * U * L * H := by rfl
    _ = 3 * U * H * L := by ring

private theorem lps_h1_convection_laplacian_aestronglyMeasurable
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3} {lap : Vec3 → Vec3}
    (huMeas : AEStronglyMeasurable u volume)
    (hDu2 : MemLp Du 2 volume) (hD2u2 : MemLp D2u 2 volume)
    (hlap : ∀ x i, lap x i = ∑ j : Fin 3, D2u x i j j) :
    AEStronglyMeasurable (fun x : Vec3 => ∑ i : Fin 3,
      (∑ j : Fin 3, u x j * Du x i j) * lap x i) volume := by
  apply lps_h1_aesm_finset_sum
  intro i
  have hSumMeas : AEStronglyMeasurable
      (fun x : Vec3 => ∑ j : Fin 3, u x j * Du x i j) volume := by
    apply lps_h1_aesm_finset_sum
    intro j
    exact ((ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable
      huMeas).mul
        ((hDu2.eval i).eval j).aestronglyMeasurable
  have hlapMeas : AEStronglyMeasurable (fun x : Vec3 => lap x i) volume := by
    rw [show (fun x : Vec3 => lap x i) =
      (fun x => ∑ j : Fin 3, D2u x i j j) by funext x; exact hlap x i]
    apply lps_h1_aesm_finset_sum
    intro j
    exact (((hD2u2.eval i).eval j).eval j).aestronglyMeasurable
  exact hSumMeas.mul hlapMeas

private theorem lps_h1_convection_hessian_pointwise
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3} {lap : Vec3 → Vec3}
    (hlap : ∀ x i, lap x i = ∑ j : Fin 3, D2u x i j j) (x : Vec3) :
    ‖∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i‖ ≤
      27 * ((vec3EuclideanNorm (u x) * ∑ i : Fin 3, ‖Du x i‖) * ‖D2u x‖) := by
  let U : Vec3 → ℝ := fun y => vec3EuclideanNorm (u y)
  let H : Vec3 → ℝ := fun y => ∑ i : Fin 3, ‖Du y i‖
  let F : Vec3 → ℝ := fun y => U y * H y
  let L : Vec3 → ℝ := fun y => ‖D2u y‖
  have hpoint := lps_h1_convection_laplacian_pointwise
    (u := u) (Du := Du) (lap := lap) x
  have hD2entry (i j : Fin 3) : |D2u x i j j| ≤ ‖D2u x‖ := by
    calc
      |D2u x i j j| = ‖D2u x i j j‖ := Real.norm_eq_abs _
      _ ≤ ‖D2u x i j‖ := norm_le_pi_norm (D2u x i j) j
      _ ≤ ‖D2u x i‖ := norm_le_pi_norm (D2u x i) j
      _ ≤ ‖D2u x‖ := norm_le_pi_norm (D2u x) i
  have hLapCoord (i : Fin 3) : |lap x i| ≤ 3 * ‖D2u x‖ := by
    rw [hlap x i]
    calc
      |∑ j : Fin 3, D2u x i j j| ≤ ∑ j : Fin 3, |D2u x i j j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, ‖D2u x‖ :=
        Finset.sum_le_sum fun j _ => hD2entry i j
      _ = 3 * ‖D2u x‖ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hLapNorm : vec3EuclideanNorm (lap x) ≤ 9 * ‖D2u x‖ := by
    calc
      vec3EuclideanNorm (lap x) ≤ ∑ i : Fin 3, |lap x i| :=
        CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sum_abs _
      _ ≤ ∑ _i : Fin 3, 3 * ‖D2u x‖ :=
        Finset.sum_le_sum fun i _ => hLapCoord i
      _ = 9 * ‖D2u x‖ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  calc
    ‖∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i‖ ≤
        3 * U x * H x * vec3EuclideanNorm (lap x) := by
      simpa [U, H, Real.norm_eq_abs] using hpoint
    _ ≤ 3 * U x * H x * (9 * ‖D2u x‖) := by
      exact mul_le_mul_of_nonneg_left hLapNorm
        (mul_nonneg (mul_nonneg (by norm_num) (vec3EuclideanNorm_nonneg _))
          (Finset.sum_nonneg fun i _ => norm_nonneg _))
    _ = 27 * (F x * L x) := by dsimp [F, L]; ring

private theorem lps_h1_integral_mul_le_real_l2_norms
    {F L : Vec3 → ℝ} (hF : MemLp F (ENNReal.ofReal 2) volume)
    (hL : MemLp L (ENNReal.ofReal 2) volume)
    (hF0 : ∀ x, 0 ≤ F x) (hL0 : ∀ x, 0 ≤ L x) :
    ∫ x : Vec3, F x * L x ≤
      (eLpNorm F (ENNReal.ofReal 2) volume).toReal *
        (eLpNorm L (ENNReal.ofReal 2) volume).toReal := by
  have hHolder22 : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hHolderIntegral := integral_mul_norm_le_Lp_mul_Lq hHolder22 hF hL
  have hLpNorm_two {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal 2) volume) :
      (eLpNorm f (ENNReal.ofReal 2) volume).toReal =
        (∫ x : Vec3, ‖f x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [toReal_eLpNorm,
      lpNorm_eq_integral_norm_rpow_toReal (p := ENNReal.ofReal 2)
        (by norm_num) (by norm_num)
        hf.aestronglyMeasurable]
    norm_num
  calc
    ∫ x : Vec3, F x * L x = ∫ x : Vec3, ‖F x‖ * ‖L x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Real.norm_eq_abs, abs_of_nonneg (hF0 x), abs_of_nonneg (hL0 x)]
    _ ≤ (∫ x : Vec3, ‖F x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ x : Vec3, ‖L x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hHolderIntegral
    _ = _ := by rw [← hLpNorm_two hF, ← hLpNorm_two hL]

/-- At almost every strong `H²` slice, the finite Serrin interpolation bounds
the convection term paired with the Laplacian. This is the spatial estimate
used before Young absorption in `lem:lps-H1-estimate`. -/
theorem lps_h1_finite_nonlinear_pairing_bound
    {s : ℝ} (hs : 3 < s)
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3} {lap : Vec3 → Vec3}
    (huMeas : AEStronglyMeasurable u volume)
    (huS : MemLp (fun x : Vec3 => vec3EuclideanNorm (u x))
      (ENNReal.ofReal s) volume)
    (hDu2 : MemLp Du 2 volume) (hD2u2 : MemLp D2u 2 volume)
    (hgrad : ∀ i j : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => Du x i j) (fun x k => D2u x i j k))
    (hlap : ∀ x i, lap x i = ∑ j : Fin 3, D2u x i j j) :
    |∫ x : Vec3,
      ∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
      243 * (gagliardoNirenbergSobolevConstant.toReal) ^ (3 / s) *
        (2 : ℝ) ^ (3 / s) *
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u x))
          (ENNReal.ofReal s) volume).toReal *
        (eLpNorm Du 2 volume).toReal ^ ((s - 3) / s) *
        (eLpNorm D2u 2 volume).toReal ^ (1 + 3 / s) := by
  let q : ℝ := 2 * s / (s - 2)
  let θ₀ : ℝ := (s - 3) / s
  let θ₁ : ℝ := 3 / s
  let U : Vec3 → ℝ := fun x => vec3EuclideanNorm (u x)
  let H : Vec3 → ℝ := fun x => ∑ i : Fin 3, ‖Du x i‖
  let F : Vec3 → ℝ := fun x => U x * H x
  let L : Vec3 → ℝ := fun x => ‖D2u x‖
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hs2 : 0 < s - 2 := by linarith only [hs]
  have hs3 : 0 < s - 3 := by linarith only [hs]
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hθ₀pos : 0 < θ₀ := by dsimp [θ₀]; positivity
  have hθ₁pos : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hrecip : s⁻¹ + q⁻¹ = (2 : ℝ)⁻¹ := by
    dsimp [q]
    field_simp [ne_of_gt hs0, ne_of_gt hs2]
    ring
  have htriple : ENNReal.HolderTriple (ENNReal.ofReal s) (ENNReal.ofReal q)
      (ENNReal.ofReal 2) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos hs0, ← ENNReal.ofReal_inv_of_pos hqpos,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity), hrecip]
  have hSobTop : gagliardoNirenbergSobolevConstant < ⊤ :=
    lt_top_iff_ne_top.mpr
      (Classical.choose_spec CKN.sobolev_L6_global).1
  have hSobPowTop : gagliardoNirenbergSobolevConstant ^ (3 / s) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hSobTop.ne
  have hTwoPowTop : (2 : ℝ≥0∞) ^ (3 / s) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)
  have hDuPowTop : (eLpNorm Du 2 volume) ^ θ₀ < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hDu2.eLpNorm_ne_top
  have hD2PowTop : (eLpNorm D2u 2 volume) ^ θ₁ < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hD2u2.eLpNorm_ne_top
  have hInterp := lps_h1_gradient_interpolation hs hDu2 hD2u2 hgrad
  have hRTop :
      (9 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant ^ (3 / s) *
        (2 : ℝ≥0∞) ^ (3 / s) * (eLpNorm Du 2 volume) ^ θ₀ *
          (eLpNorm D2u 2 volume) ^ θ₁ < ⊤ := by
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by norm_num) hSobPowTop) hTwoPowTop)
        hDuPowTop)
      hD2PowTop
  have hHmeas : AEStronglyMeasurable H volume := by
    dsimp [H]
    apply lps_h1_aesm_finset_sum
    intro i
    exact continuous_norm.comp_aestronglyMeasurable
      ((hDu2.eval i).aestronglyMeasurable)
  have hHbound : eLpNorm H (ENNReal.ofReal q) volume ≤
      (9 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant ^ (3 / s) *
        (2 : ℝ≥0∞) ^ (3 / s) * (eLpNorm Du 2 volume) ^ θ₀ *
          (eLpNorm D2u 2 volume) ^ θ₁ := by
    simpa only [H, q, θ₀, θ₁] using hInterp
  have hH : MemLp H (ENNReal.ofReal q) volume := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hHbound hRTop
  have hF : MemLp F (ENNReal.ofReal 2) volume := by
    change MemLp (fun x => U x * H x) (ENNReal.ofReal 2) volume
    exact huS.mul hH (hpqr := htriple)
  have hFbound : eLpNorm F (ENNReal.ofReal 2) volume ≤
      eLpNorm U (ENNReal.ofReal s) volume * eLpNorm H (ENNReal.ofReal q) volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ENNReal.ofReal s) (q := ENNReal.ofReal q) (r := ENNReal.ofReal 2)
      (fun a b : ℝ => a * b) 1 continuous_mul
      (huS.aestronglyMeasurable) hHmeas
      (Filter.Eventually.of_forall fun x => by
        change ‖U x * H x‖ ≤ (1 : ℝ) * ‖U x‖ * ‖H x‖
        rw [norm_mul]
        simp)
    simpa [ENNReal.smul_def, F, one_mul] using h
  have hL : MemLp L (ENNReal.ofReal 2) volume := by
    simpa only [L, show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using
      hD2u2.norm
  have hProd : Integrable (fun x : Vec3 => F x * L x) volume := by
    have hHolder : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    exact memLp_one_iff_integrable.mp
      (MemLp.mul hF hL (hpqr := hHolder.ennrealOfReal))
  have hPmeas := lps_h1_convection_laplacian_aestronglyMeasurable huMeas hDu2 hD2u2 hlap
  have hPbound : ∀ x : Vec3,
      ‖∑ i : Fin 3,
        (∑ j : Fin 3, u x j * Du x i j) * lap x i‖ ≤ 27 * (F x * L x) :=
    lps_h1_convection_hessian_pointwise hlap
  have hPint : Integrable
      (fun x : Vec3 => ∑ i : Fin 3,
        (∑ j : Fin 3, u x j * Du x i j) * lap x i) volume :=
    (hProd.const_mul 27).mono' hPmeas (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hPbound x)
  have hPabs : |∫ x : Vec3,
      ∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
        ∫ x : Vec3, |∑ i : Fin 3,
          (∑ j : Fin 3, u x j * Du x i j) * lap x i| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (fun x : Vec3 => ∑ i : Fin 3,
          (∑ j : Fin 3, u x j * Du x i j) * lap x i))
  have hMajorInt : Integrable (fun x : Vec3 => 27 * (F x * L x)) volume :=
    hProd.const_mul 27
  have hPtoMajor : ∫ x : Vec3, |∑ i : Fin 3,
      (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
        ∫ x : Vec3, 27 * (F x * L x) := by
    apply integral_mono_ae hPint.norm hMajorInt
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hPbound x
  have hholderSimple := lps_h1_integral_mul_le_real_l2_norms hF hL
    (fun x => mul_nonneg (vec3EuclideanNorm_nonneg _)
      (Finset.sum_nonneg fun i _ => norm_nonneg _)) (fun x => norm_nonneg _)
  have hHtoReal : (eLpNorm H (ENNReal.ofReal q) volume).toReal ≤
      ((9 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant ^ (3 / s) *
        (2 : ℝ≥0∞) ^ (3 / s) * (eLpNorm Du 2 volume) ^ θ₀ *
          (eLpNorm D2u 2 volume) ^ θ₁).toReal :=
    ENNReal.toReal_mono hRTop.ne hHbound
  have htoRealConstant :
      ((9 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant ^ (3 / s) *
        (2 : ℝ≥0∞) ^ (3 / s) * (eLpNorm Du 2 volume) ^ θ₀ *
          (eLpNorm D2u 2 volume) ^ θ₁).toReal =
        9 * gagliardoNirenbergSobolevConstant.toReal ^ (3 / s) *
          (2 : ℝ) ^ (3 / s) * (eLpNorm Du 2 volume).toReal ^ θ₀ *
            (eLpNorm D2u 2 volume).toReal ^ θ₁ := by
    simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    norm_num
  have hbase := le_trans hPabs (le_trans hPtoMajor (by
    rw [integral_const_mul]
    ))
  have hFtoReal :
      (eLpNorm F (ENNReal.ofReal 2) volume).toReal ≤
        (eLpNorm U (ENNReal.ofReal s) volume).toReal *
          (eLpNorm H (ENNReal.ofReal q) volume).toReal := by
    have hUtop : eLpNorm U (ENNReal.ofReal s) volume < ⊤ :=
      lt_top_iff_ne_top.mpr (by simpa [U] using huS.eLpNorm_ne_top)
    have hHtop : eLpNorm H (ENNReal.ofReal q) volume < ⊤ :=
      lt_top_iff_ne_top.mpr hH.eLpNorm_ne_top
    have htop : eLpNorm U (ENNReal.ofReal s) volume *
        eLpNorm H (ENNReal.ofReal q) volume < ⊤ :=
      ENNReal.mul_lt_top hUtop hHtop
    have h := ENNReal.toReal_mono htop.ne hFbound
    rw [ENNReal.toReal_mul] at h
    exact h
  have hLtoReal : (eLpNorm L (ENNReal.ofReal 2) volume).toReal =
      (eLpNorm D2u 2 volume).toReal := by
    change (eLpNorm (fun x : Vec3 => ‖D2u x‖) (ENNReal.ofReal 2) volume).toReal = _
    rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num,
      eLpNorm_norm D2u hD2u2.aestronglyMeasurable]
  have hHboundReal : (eLpNorm H (ENNReal.ofReal q) volume).toReal ≤
      9 * gagliardoNirenbergSobolevConstant.toReal ^ (3 / s) *
        (2 : ℝ) ^ (3 / s) * (eLpNorm Du 2 volume).toReal ^ θ₀ *
          (eLpNorm D2u 2 volume).toReal ^ θ₁ := by
    rw [htoRealConstant] at hHtoReal
    exact hHtoReal
  have hEU : 0 ≤ (eLpNorm U (ENNReal.ofReal s) volume).toReal := ENNReal.toReal_nonneg
  have hED : 0 ≤ (eLpNorm D2u 2 volume).toReal := ENNReal.toReal_nonneg
  have hbase' :
      |∫ x : Vec3, ∑ i : Fin 3,
        (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
        243 * gagliardoNirenbergSobolevConstant.toReal ^ (3 / s) *
          (2 : ℝ) ^ (3 / s) *
          (eLpNorm U (ENNReal.ofReal s) volume).toReal *
          (eLpNorm Du 2 volume).toReal ^ θ₀ *
          (eLpNorm D2u 2 volume).toReal ^ (1 + θ₁) := by
    have hPow : (eLpNorm D2u 2 volume).toReal ^ θ₁ *
        (eLpNorm D2u 2 volume).toReal =
        (eLpNorm D2u 2 volume).toReal ^ (1 + θ₁) := by
      have hsumpos : 0 < 1 + θ₁ := by linarith only [hθ₁pos]
      by_cases hzero : (eLpNorm D2u 2 volume).toReal = 0
      · simp [hzero, Real.zero_rpow hθ₁pos.ne', Real.zero_rpow hsumpos.ne']
      · have hpos : 0 < (eLpNorm D2u 2 volume).toReal :=
          lt_of_le_of_ne hED (Ne.symm hzero)
        calc
          _ = (eLpNorm D2u 2 volume).toReal ^ (θ₁ + 1) :=
            (Real.rpow_add_one (ne_of_gt hpos) θ₁).symm
          _ = (eLpNorm D2u 2 volume).toReal ^ (1 + θ₁) := by
            congr 1
            ring
    calc
      _ ≤ 27 * ∫ x : Vec3, F x * L x := hbase
      _ ≤ 27 * ((eLpNorm F (ENNReal.ofReal 2) volume).toReal *
          (eLpNorm L (ENNReal.ofReal 2) volume).toReal) :=
        mul_le_mul_of_nonneg_left hholderSimple (by norm_num)
      _ = 27 * (eLpNorm F (ENNReal.ofReal 2) volume).toReal *
          (eLpNorm D2u 2 volume).toReal := by rw [hLtoReal]; ring
      _ ≤ 27 * ((eLpNorm U (ENNReal.ofReal s) volume).toReal *
          (eLpNorm H (ENNReal.ofReal q) volume).toReal) *
          (eLpNorm D2u 2 volume).toReal :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hFtoReal (by norm_num)) hED
      _ ≤ 27 * ((eLpNorm U (ENNReal.ofReal s) volume).toReal *
          (9 * gagliardoNirenbergSobolevConstant.toReal ^ (3 / s) *
            (2 : ℝ) ^ (3 / s) * (eLpNorm Du 2 volume).toReal ^ θ₀ *
            (eLpNorm D2u 2 volume).toReal ^ θ₁)) *
          (eLpNorm D2u 2 volume).toReal :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hHboundReal hEU) (by norm_num)) hED
      _ = _ := by rw [← hPow]; ring
  simpa [θ₀, θ₁, U] using hbase'

/-- The endpoint (`s = ∞`) convection term paired with the vector Laplacian is
controlled by the spatial essential supremum and the two `L²` factors. This is
the spatial estimate used before endpoint Young absorption in
`lem:lps-H1-estimate`. -/
theorem lps_h1_infinite_nonlinear_pairing_bound
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {lap : Vec3 → Vec3}
    (huMeas : AEStronglyMeasurable u volume)
    (huInf : MemLp (fun x => vec3EuclideanNorm (u x)) ⊤ volume)
    (hDu2 : MemLp Du 2 volume) (hlap2 : MemLp lap 2 volume) :
    |∫ x : Vec3,
      ∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i| ≤
      9 * (eLpNorm (fun x => vec3EuclideanNorm (u x)) ⊤ volume).toReal *
        Real.sqrt (∫ x : Vec3, ‖Du x‖ ^ 2) *
        Real.sqrt (∫ x : Vec3, vec3EuclideanNorm (lap x) ^ 2) := by
  let U : Vec3 → ℝ := fun x => vec3EuclideanNorm (u x)
  let G : Vec3 → ℝ := fun x => ‖Du x‖
  let L : Vec3 → ℝ := fun x => vec3EuclideanNorm (lap x)
  let M : ℝ := (eLpNorm U ⊤ volume).toReal
  let P : Vec3 → ℝ := fun x =>
    ∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * lap x i
  have hUmeas : AEStronglyMeasurable U volume :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huMeas
  have hG : MemLp G 2 volume := by
    simpa [G] using hDu2.norm
  have hL : MemLp L 2 volume := by
    have hmeas : AEStronglyMeasurable L volume :=
      continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hlap2.aestronglyMeasurable
    apply MemLp.of_le_mul hlap2.norm hmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact vec3EuclideanNorm_le_sqrt_three_mul_norm (lap x)
  have hHolder : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ENNReal.HolderConjugate.instTwoTwo
  have hGL : MemLp (fun x : Vec3 => G x * L x) 1 volume :=
    hG.mul hL (hpqr := hHolder)
  have hGLint : Integrable (fun x : Vec3 => G x * L x) volume :=
    memLp_one_iff_integrable.mp hGL
  have hMnonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have hUaebound : ∀ᵐ x ∂volume, U x ≤ M := by
    have hEss := enorm_ae_le_eLpNormEssSup U volume
    rw [← eLpNorm_exponent_top hUmeas] at hEss
    filter_upwards [hEss] with x hx
    have hUeq : ‖U x‖ₑ = ENNReal.ofReal (U x) :=
      Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)
    have hle : ENNReal.ofReal (U x) ≤ eLpNorm U ⊤ volume := by
      simpa only [hUeq] using hx
    have hreal := ENNReal.toReal_mono huInf.eLpNorm_ne_top hle
    rw [ENNReal.toReal_ofReal (vec3EuclideanNorm_nonneg _)] at hreal
    simpa [M] using hreal
  have hPmeas : AEStronglyMeasurable P volume := by
    dsimp [P]
    apply lps_h1_aesm_finset_sum
    intro i
    have hSum : AEStronglyMeasurable
        (fun x : Vec3 => ∑ j : Fin 3, u x j * Du x i j) volume := by
      apply lps_h1_aesm_finset_sum
      intro j
      exact ((ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable
        huMeas).mul ((hDu2.eval i).eval j).aestronglyMeasurable
    exact hSum.mul ((hlap2.eval i).aestronglyMeasurable)
  have hPpoint : ∀ x : Vec3,
      |P x| ≤ 3 * (U x * (∑ i : Fin 3, ‖Du x i‖) * L x) := by
    intro x
    simpa [P, U, L, mul_assoc] using
      (lps_h1_convection_laplacian_pointwise
        (u := u) (Du := Du) (lap := lap) x)
  have hrows : ∀ x : Vec3,
      (∑ i : Fin 3, ‖Du x i‖) ≤ 3 * G x := by
    intro x
    calc
      (∑ i : Fin 3, ‖Du x i‖) ≤ ∑ _i : Fin 3, G x :=
        Finset.sum_le_sum fun i _ => norm_le_pi_norm (Du x) i
      _ = 3 * G x := by
        simp [G, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hPdom : ∀ᵐ x ∂volume,
      ‖P x‖ ≤ 9 * (M * (G x * L x)) := by
    filter_upwards [hUaebound] with x hx
    rw [Real.norm_eq_abs]
    have hGLnonneg : 0 ≤ G x * L x :=
      mul_nonneg (norm_nonneg _) (vec3EuclideanNorm_nonneg _)
    have hU : 0 ≤ U x := vec3EuclideanNorm_nonneg _
    calc
      |P x| ≤ 3 * (U x * (∑ i : Fin 3, ‖Du x i‖) * L x) := hPpoint x
      _ ≤ 9 * (U x * (G x * L x)) := by
        calc
          3 * (U x * (∑ i : Fin 3, ‖Du x i‖) * L x) =
              (3 * U x * L x) * ∑ i : Fin 3, ‖Du x i‖ := by ring
          _ ≤ (3 * U x * L x) * (3 * G x) :=
            mul_le_mul_of_nonneg_left (hrows x)
              (mul_nonneg (mul_nonneg (by norm_num) hU)
                (vec3EuclideanNorm_nonneg _))
          _ = 9 * (U x * (G x * L x)) := by ring
      _ ≤ 9 * (M * (G x * L x)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hx hGLnonneg) (by norm_num)
  have hDom : Integrable (fun x : Vec3 => 9 * (M * (G x * L x))) volume := by
    have h := hGLint.const_mul (9 * M)
    convert h using 1
    ext x
    ring
  have hPint : Integrable P volume := by
    apply hDom.mono' hPmeas
    filter_upwards [hPdom] with x hx
    exact hx
  have hAbsInt : Integrable (fun x : Vec3 => |P x|) volume := hPint.norm
  have hIntegralDom :
      ∫ x : Vec3, |P x| ≤ ∫ x : Vec3, 9 * (M * (G x * L x)) := by
    apply integral_mono_ae hAbsInt hDom
    filter_upwards [hPdom] with x hx
    simpa only [Real.norm_eq_abs] using hx
  have hPair := lps_integral_pairing_le G L hG hL
  have hMpair :
      9 * (M * ∫ x : Vec3, G x * L x) ≤
        9 * M * (Real.sqrt (∫ x : Vec3, G x ^ 2) *
          Real.sqrt (∫ x : Vec3, L x ^ 2)) := by
    calc
      9 * (M * ∫ x : Vec3, G x * L x) =
          (9 * M) * ∫ x : Vec3, G x * L x := by ring
      _ ≤ (9 * M) * (Real.sqrt (∫ x : Vec3, G x ^ 2) *
          Real.sqrt (∫ x : Vec3, L x ^ 2)) :=
        mul_le_mul_of_nonneg_left hPair (by positivity)
      _ = _ := by ring
  calc
    |∫ x : Vec3, P x| ≤ ∫ x : Vec3, |P x| := abs_integral_le_integral_abs
    _ ≤ ∫ x : Vec3, 9 * (M * (G x * L x)) := hIntegralDom
    _ = 9 * (M * ∫ x : Vec3, G x * L x) := by
      calc
        _ = ∫ x : Vec3, (9 * M) * (G x * L x) := by
          congr 1
          funext x
          ring
        _ = (9 * M) * ∫ x : Vec3, G x * L x := integral_const_mul _ _
        _ = _ := by ring
    _ ≤ 9 * M * (Real.sqrt (∫ x : Vec3, G x ^ 2) *
        Real.sqrt (∫ x : Vec3, L x ^ 2)) := hMpair
    _ = 9 * M * Real.sqrt (∫ x : Vec3, ‖Du x‖ ^ 2) *
        Real.sqrt (∫ x : Vec3, vec3EuclideanNorm (lap x) ^ 2) := by
          simp only [G, L]
          ring
    _ = _ := by simp [M, U]

end ESS.LPS

end
