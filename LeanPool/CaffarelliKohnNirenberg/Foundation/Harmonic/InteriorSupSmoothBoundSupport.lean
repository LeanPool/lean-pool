/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimates
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSupThreeQuarters

/-!
# Interior Sup Smooth Bound Support

Supporting estimates for the Navier–Stokes development.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN.Foundation.Heat

/-- Represents a smooth harmonic function on the support of a cutoff by its Newtonian source and boundary terms. -/
theorem smooth_harmonic_annular_representation_on_tsupport
    {H : Vec3 → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hHarm : ∀ y ∈ tsupport (mollifiedBallCutoff x₀ hρ),
      CKN.spatialLaplacian H y = 0)
    {x : Vec3} (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) :
    H x =
      (-∫ y : Vec3, newtonianKernel (x - y) *
          (H y * CKN.spatialLaplacian (mollifiedBallCutoff x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3,
          H y * CKN.spatialDeriv
            (kernelCutoffDerivative x x₀ hρ i) i y := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff x₀ hρ) :=
    mollifiedBallCutoff_smooth x₀ hρ
  have hηc : HasCompactSupport (mollifiedBallCutoff x₀ hρ) :=
    mollifiedBallCutoff_hasCompactSupport x₀ hρ
  have hprod : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * H y) := hη.mul hH
  have hprodSupport : HasCompactSupport
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * H y) :=
    hηc.mul_right (f' := H)
  have hηx : mollifiedBallCutoff x₀ hρ x = 1 :=
    mollifiedBallCutoff_eq_one_on_inner x₀ hρ hx
  let Cfun : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) *
      CKN.spatialLaplacian (fun z : Vec3 =>
        mollifiedBallCutoff x₀ hρ z * H z) y
  let Bfun : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) * CKN.spatialGradDot
      (mollifiedBallCutoff x₀ hρ) H y
  let Afun : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) *
      (H y * CKN.spatialLaplacian (mollifiedBallCutoff x₀ hρ) y)
  have hCcont : Continuous
      (CKN.spatialLaplacian (fun z : Vec3 =>
        mollifiedBallCutoff x₀ hρ z * H z)) :=
    (CKN.contDiff_spatialLaplacian_smooth hprod).continuous
  have hCcompact : HasCompactSupport
      (CKN.spatialLaplacian (fun z : Vec3 =>
        mollifiedBallCutoff x₀ hρ z * H z)) :=
    laplacian_compact_support hprodSupport
  have hCint : Integrable Cfun volume :=
    newtonianKernel_mul_compact_integrable hCcont hCcompact x
  have hBi : ∀ i : Fin 3, Integrable (fun y : Vec3 =>
      newtonianKernel (x - y) *
        CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
          CKN.spatialDeriv H i y) volume := by
    intro i
    have hi := kernelCutoffDerivative_integrable_mul_left hH x x₀ hρ hx i
    simpa [kernelCutoffDerivative, eta, mul_assoc, mul_left_comm, mul_comm] using hi
  have hBint : Integrable Bfun volume := by
    have hsum : Integrable (fun y : Vec3 =>
        ∑ i : Fin 3, newtonianKernel (x - y) *
          CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
            CKN.spatialDeriv H i y) volume := by
      simpa only [Fin.sum_univ_three] using
        (integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
          (fun i _hi => hBi i))
    have hrewrite : Bfun = fun y : Vec3 => ∑ i : Fin 3,
        newtonianKernel (x - y) *
          CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
            CKN.spatialDeriv H i y := by
      funext y
      simp only [Bfun, CKN.spatialGradDot, Finset.mul_sum, mul_assoc]
    exact hrewrite ▸ hsum
  have hharm_eta : ∀ y : Vec3,
      mollifiedBallCutoff x₀ hρ y * CKN.spatialLaplacian H y = 0 := by
    intro y
    by_cases hy : y ∈ tsupport (mollifiedBallCutoff x₀ hρ)
    · rw [hHarm y hy, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hprod_rule : ∀ y : Vec3,
      CKN.spatialLaplacian (fun z : Vec3 =>
          mollifiedBallCutoff x₀ hρ z * H z) y =
        mollifiedBallCutoff x₀ hρ y * CKN.spatialLaplacian H y +
          2 * CKN.spatialGradDot (mollifiedBallCutoff x₀ hρ) H y +
          H y * CKN.spatialLaplacian (mollifiedBallCutoff x₀ hρ) y := by
    intro y
    exact congrFun (CKN.spatialLaplacian_mul_smooth hη hH) y
  have hCeq : Cfun = fun y => Afun y + 2 * Bfun y := by
    funext y
    rw [show Cfun y = newtonianKernel (x - y) *
        CKN.spatialLaplacian (fun z : Vec3 =>
          mollifiedBallCutoff x₀ hρ z * H z) y by rfl,
      hprod_rule y, hharm_eta y]
    simp only [Afun, Bfun]
    ring
  have hAint : Integrable Afun volume := by
    have hdiff := hCint.sub (hBint.const_mul 2)
    apply hdiff.congr
    filter_upwards [] with y
    rw [hCeq]
    simp only [Pi.sub_apply]
    ring
  have hrep : H x = -∫ y : Vec3, Cfun y := by
    have h := newtonian_representation_smooth hprod hprodSupport x
    simpa only [Cfun, hηx, one_mul] using h
  have hBsum : (∫ y : Vec3, Bfun y) =
      ∑ i : Fin 3, ∫ y : Vec3,
        newtonianKernel (x - y) *
          CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
            CKN.spatialDeriv H i y := by
    rw [show Bfun = fun y : Vec3 => ∑ i : Fin 3,
        newtonianKernel (x - y) *
          CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
            CKN.spatialDeriv H i y by
      funext y
      simp only [Bfun, CKN.spatialGradDot, Finset.mul_sum, mul_assoc]]
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _hi => hBi i)]
  have hIBP (i : Fin 3) :
      ∫ y : Vec3, CKN.spatialDeriv H i y *
          kernelCutoffDerivative x x₀ hρ i y =
        -∫ y : Vec3, H y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
    have h := integral_h_mul_kernelCutoffDerivative_spatialDeriv
      hH x x₀ hρ hx i
    linarith only [h]
  have hsum : (∑ i : Fin 3, ∫ y : Vec3,
        newtonianKernel (x - y) *
          CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
            CKN.spatialDeriv H i y) =
      -∑ i : Fin 3, ∫ y : Vec3, H y *
        CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
    calc
      (∑ i : Fin 3, ∫ y : Vec3,
          newtonianKernel (x - y) *
            CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
              CKN.spatialDeriv H i y) =
          ∑ i : Fin 3, -(∫ y : Vec3, H y *
            CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ∫ y : Vec3, newtonianKernel (x - y) *
              CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
                CKN.spatialDeriv H i y =
              ∫ y : Vec3, CKN.spatialDeriv H i y *
                kernelCutoffDerivative x x₀ hρ i y := by
                  congr 1
                  funext y
                  simp [kernelCutoffDerivative, eta, mul_comm]
          _ = -(∫ y : Vec3, H y *
              CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) := hIBP i
      _ = -∑ i : Fin 3, ∫ y : Vec3, H y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by simp
  calc
    H x = -∫ y : Vec3, Cfun y := hrep
    _ = -((∫ y : Vec3, Afun y) + 2 * (∫ y : Vec3, Bfun y)) := by
      rw [hCeq, integral_add hAint (hBint.const_mul 2), integral_const_mul]
    _ = -((∫ y : Vec3, Afun y) + 2 *
        (∑ i : Fin 3, ∫ y : Vec3,
          newtonianKernel (x - y) *
            CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i y *
              CKN.spatialDeriv H i y)) := by rw [hBsum]
    _ = (-∫ y : Vec3, newtonianKernel (x - y) *
          (H y * CKN.spatialLaplacian (mollifiedBallCutoff x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3,
          H y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
      rw [hsum]
      simp only [Afun]
      ring

/-- Produces a smooth compactly supported cutoff equal to one near a compact set. -/
theorem exists_smooth_cutoff_one_near_compact
    {K U : Set Vec3} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ξ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ξ ∧
      HasCompactSupport ξ ∧ (∀ x, 0 ≤ ξ x ∧ ξ x ≤ 1) ∧
      tsupport ξ ⊆ U ∧
      ∃ W : Set Vec3, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∀ x ∈ W, ξ x = 1 := by
  classical
  let d : ∀ x : K, ℝ := fun x => Classical.choose
    (Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hKU x.2)))
  have hd : ∀ x : K, 0 < d x ∧ Metric.closedBall x.1 (d x) ⊆ U := by
    intro x
    exact Classical.choose_spec
      (Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hKU x.2)))
  let b : ∀ x : K, ContDiffBump x.1 := fun x =>
    ⟨d x / 2, d x, half_pos (hd x).1, half_lt_self (hd x).1⟩
  have hbout : ∀ x : K, Metric.closedBall x.1 (b x).rOut ⊆ U := by
    intro x
    simpa [b] using (hd x).2
  have hcover : K ⊆ ⋃ x : K, Metric.ball x.1 (b x).rIn := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    exact Metric.mem_ball_self (b ⟨y, hy⟩).rIn_pos
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball x.1 (b x).rIn)
    (fun _ => Metric.isOpen_ball) hcover
  let W : Set Vec3 := ⋃ x ∈ s, Metric.ball x.1 (b x).rIn
  have hWopen : IsOpen W := by
    dsimp [W]
    exact isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hKW : K ⊆ W := by
    simpa only [W] using hs
  have hWU : W ⊆ U := by
    intro y hy
    rcases Set.mem_iUnion₂.1 hy with ⟨x, hxs, hyx⟩
    apply hbout x
    exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by
        dsimp [b]
        linarith only [(hd x).1]))) hyx
  let P : Finset K → Vec3 → ℝ := fun s y =>
    ∏ x ∈ s, (1 - (b x : Vec3 → ℝ) y)
  have hP : ∀ s : Finset K, ContDiff ℝ (⊤ : ℕ∞) (P s) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa [P] using contDiff_const
    | @insert x t hxt iht =>
      simp only [P, Finset.prod_insert hxt]
      exact (contDiff_const.sub (b x).contDiff).mul iht
  let ξ : Vec3 → ℝ := fun y => 1 - P s y
  have hξ : ContDiff ℝ (⊤ : ℕ∞) ξ := by
    simpa [ξ] using contDiff_const.sub (hP s)
  have hξrange : ∀ y, 0 ≤ ξ y ∧ ξ y ≤ 1 := by
    intro y
    have hPnonneg : 0 ≤ P s y := by
      apply Finset.prod_nonneg
      intro x hx
      exact sub_nonneg.mpr (b x).le_one
    have hPle : P s y ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro x hx
        exact sub_nonneg.mpr (b x).le_one
      · intro x hx
        exact sub_le_self 1 (b x).nonneg
    dsimp [ξ]
    constructor <;> linarith only [hPnonneg, hPle]
  have hξsupport : Function.support ξ ⊆
      ⋃ x ∈ s, Metric.closedBall x.1 (b x).rOut := by
    intro y hy
    by_contra hnot
    have hzero : ∀ x ∈ s, (b x : Vec3 → ℝ) y = 0 := by
      intro x hxs
      have hclosed : y ∉ Metric.closedBall x.1 (b x).rOut := by
        intro hyclosed
        exact hnot (Set.mem_iUnion₂.2 ⟨x, hxs, hyclosed⟩)
      have hball : y ∉ Metric.ball x.1 (b x).rOut := fun hyball =>
        hclosed (Metric.ball_subset_closedBall hyball)
      have hns : y ∉ Function.support (b x : Vec3 → ℝ) := by
        simpa only [(b x).support_eq] using hball
      change ¬ ((b x : Vec3 → ℝ) y ≠ 0) at hns
      exact not_ne_iff.mp hns
    have hPy : P s y = 1 := by
      simp only [P]
      apply Finset.prod_eq_one
      intro x hxs
      simp [hzero x hxs]
    have hξy : ξ y = 0 := by simp [ξ, hPy]
    change ξ y ≠ 0 at hy
    exact hy hξy
  have hTcompact : IsCompact
      (⋃ x ∈ s, Metric.closedBall x.1 (b x).rOut) := by
    exact s.isCompact_biUnion fun x hx => isCompact_closedBall x.1 (b x).rOut
  have hξcompact : HasCompactSupport ξ :=
    HasCompactSupport.of_support_subset_isCompact hTcompact hξsupport
  have hTsubU : (⋃ x ∈ s, Metric.closedBall x.1 (b x).rOut) ⊆ U := by
    intro y hy
    rcases Set.mem_iUnion₂.1 hy with ⟨x, hxs, hyx⟩
    exact hbout x hyx
  have hξtsupport : tsupport ξ ⊆ U := by
    have hclosure : closure (Function.support ξ) ⊆
        ⋃ x ∈ s, Metric.closedBall x.1 (b x).rOut :=
      closure_minimal hξsupport hTcompact.isClosed
    exact hclosure.trans hTsubU
  have hξone : ∀ y ∈ W, ξ y = 1 := by
    intro y hy
    rcases Set.mem_iUnion₂.1 hy with ⟨x, hxs, hyx⟩
    have hclosed : y ∈ Metric.closedBall x.1 (b x).rIn :=
      Metric.ball_subset_closedBall hyx
    have hbval : (b x : Vec3 → ℝ) y = 1 := (b x).one_of_mem_closedBall hclosed
    have hPzero : P s y = 0 := Finset.prod_eq_zero hxs ?_
    · simp [ξ, hPzero]
    · simp [hbval]
  exact ⟨ξ, hξ, hξcompact, hξrange, hξtsupport,
    W, hWopen, hKW, hWU, hξone⟩

/-- Bounds the cutoff annulus away from the three-quarter ball. -/
lemma cutoff_annulus_norm_distance_for_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) :
    ρ / 30 < ‖x - y‖ := by
  have hx' : vec3EuclideanNorm (x - x₀) < 3 * ρ / 4 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hy' : 13 * (4 * ρ / 3) / 20 < vec3EuclideanNorm (y - x₀) := by
    have hnot : y ∉ euclideanClosedBall x₀ (13 * (4 * ρ / 3) / 20) := hy.2
    by_contra hle
    apply hnot
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact le_of_not_gt (by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        using hle)
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (x - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (y - x₀)‖ =
          ‖WithLp.toLp 2 ((y - x) + (x - x₀))‖ := by
            congr 1
            ext i
            simp
      _ ≤ ‖WithLp.toLp 2 (y - x)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := norm_add_le _ _
      _ = _ := by
        rw [show y - x = -(x - y) by ext i; simp,
          WithLp.toLp_neg, norm_neg]
  have hEuclideanGap : 7 * ρ / 60 < vec3EuclideanNorm (x - y) := by
    rw [show 13 * (4 * ρ / 3) / 20 = 13 * ρ / 15 by ring] at hy'
    nlinarith only [hx', hy', htri]
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
  have hthree' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  nlinarith only [hEuclideanGap, hthree', hρ]

/-- Bounds the Newtonian source kernel at the three-quarter scale. -/
lemma source_kernel_bound_scaled_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) :
    |newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y| ≤
      harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
  have hdist := cutoff_annulus_norm_distance_for_three_quarters hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  have hkernel := newtonianKernel_size_bound hxy
  have hdistinv : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
  have hsource := eta_laplacian_bound_global x₀
    (R := 4 * ρ / 3) (by positivity) y
  rw [abs_mul]
  have hkernel' : |newtonianKernel (x - y)| ≤
      (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ :=
    hkernel.trans (mul_le_mul_of_nonneg_left hdistinv (by positivity))
  calc
    |newtonianKernel (x - y)| *
        |CKN.spatialLaplacian (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y| ≤
        ((4 * Real.pi)⁻¹ * (ρ / 30)⁻¹) *
          (3 * cutoffSecondDerivativeConstant / (4 * ρ / 3) ^ 2) := by
            gcongr
    _ = harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
      dsimp [harmonicInteriorSourceConstant]
      field_simp [hρ.ne']
      ring

/-- Bounds the differentiated cutoff kernel at the three-quarter scale. -/
lemma kernel_cutoff_derivative_bound_scaled_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) (i j : Fin 3) :
    |CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) j y| ≤
      harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
  have hdist := cutoff_annulus_norm_distance_for_three_quarters hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  rw [spatialDeriv_kernelCutoffDerivative_of_ne (by positivity) hxy]
  calc
    |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y *
          CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
        newtonianKernel (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) j y| ≤
        |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| *
          |CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y| +
        |newtonianKernel (x - y)| *
          |CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) j y| := by
      calc
        |_ + _| ≤ |_| + |_| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ *
          (cutoffGradientConstant / (4 * ρ / 3)) +
        (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ *
          (cutoffSecondDerivativeConstant / (4 * ρ / 3) ^ 2) := by
      have hderiv := newtonianKernel_spatialDeriv_size_bound hxy j
      have hinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 30) ^ 2)⁻¹ := by gcongr
      have heta := eta_spatialDeriv_bound_global x₀
        (ρ := 4 * ρ / 3) (by positivity) y i
      have hsecond := eta_spatialSecond_bound_global x₀
        (ρ := 4 * ρ / 3) (by positivity) y i j
      have hkernel := newtonianKernel_size_bound hxy
      have hdistinv : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
      have hderiv' : |CKN.spatialDeriv newtonianKernel j (x - y)| ≤
          (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ :=
        hderiv.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
      have hkernel' : |newtonianKernel (x - y)| ≤
          (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ :=
        hkernel.trans (mul_le_mul_of_nonneg_left hdistinv (by positivity))
      rw [show |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| =
          |CKN.spatialDeriv newtonianKernel j (x - y)| by
            rw [spatialDeriv_newtonianKernel_shift_eq_neg hxy, abs_neg]]
      gcongr
    _ = harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
      dsimp [harmonicInteriorGradientConstant]
      field_simp [hρ.ne']
      ring

/-- The differentiated cutoff kernel vanishes outside its annular support. -/
lemma kernel_cutoff_derivative_zero_off_annulus_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∉ cutoffAnnulus x₀ (4 * ρ / 3))
    (i j : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
      x x₀ (by positivity) i) j y = 0 := by
  by_cases hxy : x - y = 0
  · have hxinner : x ∈ euclideanBall x₀ (13 * (4 * ρ / 3) / 20) := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      have hxnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
      have hmargin : 3 * ρ / 4 < 13 * (4 * ρ / 3) / 20 := by
        nlinarith only [hρ]
      exact hxnorm.trans hmargin
    have hzero := spatialDeriv_kernelCutoffDerivative_at_x
      (ρ := 4 * ρ / 3) (by positivity) hxinner i j
    have hyx : y = x := sub_eq_zero.mp hxy |>.symm
    subst y
    exact hzero
  · rw [spatialDeriv_kernelCutoffDerivative_of_ne (by positivity) hxy]
    have hz := eta_derivatives_zero_off_cutoff_annulus (by positivity) hy i j
    simp [hz.1, hz.2]

/-- Equality on an open set transfers the spatial Laplacian there for smooth functions. -/
theorem spatialLaplacian_eq_of_eqOn_open
    {f g : Vec3 → ℝ} {U W : Set Vec3} (hU : IsOpen U) (hW : IsOpen W)
    (hWU : W ⊆ U) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hfg : ∀ x ∈ W, f x = g x) :
    ∀ x ∈ W, CKN.spatialLaplacian f x = CKN.spatialLaplacian g x := by
  intro x hx
  have hfirst : ∀ y ∈ W, ∀ i : Fin 3,
      CKN.spatialDeriv f i y = CKN.spatialDeriv g i y := by
    intro y hy i
    have hEq : f =ᶠ[𝓝 y] g := by
      filter_upwards [hW.mem_nhds hy] with z hz
      exact hfg z hz
    have hfAt := hf.contDiffAt (x := y)
    have hgAt := hg.contDiffAt (hU.mem_nhds (hWU hy))
    have hfdG := (hgAt.differentiableAt (by simp)).hasFDerivAt
    have hfdEq := hfdG.congr_of_eventuallyEq hEq
    have hfd : fderiv ℝ f y = fderiv ℝ g y := by
      rw [hfdEq.fderiv, hfdG.fderiv]
    simp [CKN.spatialDeriv, hfd]
  have hsecond : ∀ i : Fin 3,
      CKN.spatialDeriv (CKN.spatialDeriv f i) i x =
        CKN.spatialDeriv (CKN.spatialDeriv g i) i x := by
    intro i
    have hEq : CKN.spatialDeriv f i =ᶠ[𝓝 x] CKN.spatialDeriv g i := by
      filter_upwards [hW.mem_nhds hx] with y hy
      exact hfirst y hy i
    have hfAt : ContDiffAt ℝ (⊤ : ℕ∞) (CKN.spatialDeriv f i) x :=
      (CKN.contDiff_spatialDeriv_smooth hf i).contDiffAt (x := x)
    have hgAt : ContDiffAt ℝ (⊤ : ℕ∞) (CKN.spatialDeriv g i) x := by
      have hgx := hg.contDiffAt (hU.mem_nhds (hWU hx))
      have hfd := hgx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      change ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => (fderiv ℝ g y) (CKN.basisVec i)) x
      exact hfd.clm_apply contDiffAt_const
    have hfdG := (hgAt.differentiableAt (by simp)).hasFDerivAt
    have hfdEq := hfdG.congr_of_eventuallyEq hEq
    have hfd : fderiv ℝ (CKN.spatialDeriv f i) x =
        fderiv ℝ (CKN.spatialDeriv g i) x := by
      rw [hfdEq.fderiv, hfdG.fderiv]
    simp [CKN.spatialDeriv, hfd]
  unfold CKN.spatialLaplacian
  apply Finset.sum_congr rfl
  intro i hi
  exact hsecond i



end CKN.Foundation.Heat
