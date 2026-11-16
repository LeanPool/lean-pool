/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Order.CompletePartialOrder

/-!
# Affine normalisation of convex bodies

Maximal-volume simplices in a convex body and the elementary geometry of the standard simplex, used
for the
affine normalisation step of Caffarelli's strict convexity argument.

* `simplexEdgeMatrix`, `exists_max_simplexEdgeMatrix_det`;
* `abs_simplexCoord_le_one_of_max`;
* `closedBall_subset_stdSimplex_and_box_subset_closedBall`.
-/

@[expose] public section

noncomputable section

open Set Matrix

namespace FunctionalInequalities.Analysis

/--
The edge matrix of a simplex with vertices `v 0, …, v n` in `ℝⁿ`: column `j` is `v (j+1) − v 0`. -/
def simplexEdgeMatrix {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (v j.succ - v 0) i

private def simplexVolume {n : ℕ} :
    (Fin (n + 1) → EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun v => |(simplexEdgeMatrix v).det|

/-- **A compact convex body contains a simplex of maximal volume with positive volume**
(Caffarelli's argument, affine normalisation). -/
theorem exists_max_simplexEdgeMatrix_det {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hint : (interior K).Nonempty) :
    ∃ v : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, v i ∈ K) ∧
      0 < |(simplexEdgeMatrix v).det| ∧
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
        |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det| := by
  have hcoord :
      ∀ i : Fin n, Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    intro i
    exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i
  have hmatrix :
      Continuous
        (fun v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) =>
          simplexEdgeMatrix v) := by
    apply continuous_matrix
    intro i j
    change Continuous
      (fun v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) => (v j.succ - v 0) i)
    exact (hcoord i).comp ((continuous_apply j.succ).sub (continuous_apply 0))
  have hvolume : Continuous (@simplexVolume n) := by
    unfold simplexVolume
    exact continuous_abs.comp hmatrix.matrix_det
  let S : Set (Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :=
    (Set.univ : Set (Fin (n + 1))).pi (fun _ => K)
  have hScompact : IsCompact S :=
    isCompact_univ_pi (fun _ => hK)
  obtain ⟨x₀, hx₀⟩ := hint
  have hx₀nhds : K ∈ nhds x₀ :=
    mem_interior_iff_mem_nhds.mp hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hx₀nhds
  have hhalf : 0 < δ / 2 :=
    div_pos hδ (by norm_num)
  have hSnonempty : S.Nonempty := by
    refine ⟨fun _ => x₀, ?_⟩
    exact Set.mem_univ_pi.mpr (fun _ => interior_subset hx₀)
  obtain ⟨v, hvS, hvmax⟩ :=
    hScompact.exists_isMaxOn hSnonempty hvolume.continuousOn
  have hmax :
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), w ∈ S →
        simplexVolume w ≤ simplexVolume v := by
    intro w hw
    have hev :
        ∀ᶠ z : Fin (n + 1) → EuclideanSpace ℝ (Fin n)
          in Filter.principal S, simplexVolume z ≤ simplexVolume v :=
      hvmax
    exact (Filter.mem_principal.mp (Filter.eventually_iff.mp hev)) hw
  let w : Fin (n + 1) → EuclideanSpace ℝ (Fin n) :=
    Fin.cases x₀
      (fun j => x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ))
  have hwS : w ∈ S := by
    apply Set.mem_univ_pi.mpr
    intro i
    refine Fin.cases ?_ ?_ i
    · change x₀ ∈ K
      exact interior_subset hx₀
    · intro j
      change x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ) ∈ K
      apply hball
      rw [Metric.mem_ball]
      calc
        dist (x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ)) x₀ =
            ‖(x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ)) - x₀‖ :=
          dist_eq_norm _ _
        _ = ‖(δ / 2) • EuclideanSpace.single j (1 : ℝ)‖ := by
          rw [add_sub_cancel_left]
        _ = ‖δ / 2‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := by
          exact norm_smul (δ / 2) (EuclideanSpace.single j (1 : ℝ))
        _ = δ / 2 := by
          rw [PiLp.norm_single 2 (fun _ : Fin n => ℝ) j (1 : ℝ),
            Real.norm_eq_abs, abs_of_pos hhalf, norm_one, mul_one]
        _ < δ := half_lt_self hδ
  have hmatrix_w :
      simplexEdgeMatrix w =
        (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [simplexEdgeMatrix, w, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hdet_w :
      (simplexEdgeMatrix w).det = (δ / 2) ^ n := by
    rw [hmatrix_w, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hpos_w : 0 < simplexVolume w := by
    unfold simplexVolume
    rw [hdet_w, abs_of_pos (pow_pos hhalf n)]
    exact pow_pos hhalf n
  have hpos_v : 0 < simplexVolume v :=
    lt_of_lt_of_le hpos_w (hmax w hwS)
  have hvK : ∀ i, v i ∈ K :=
    Set.mem_univ_pi.mp hvS
  refine ⟨v, hvK, ?_, ?_⟩
  · exact hpos_v
  · intro u hu
    exact hmax u (Set.mem_univ_pi.mpr hu)

end FunctionalInequalities.Analysis

section MaxSimplexBox

open Set Matrix

/-! Coordinates relative to a maximal simplex are bounded. -/

namespace FunctionalInequalities.Analysis

private lemma simplexEdgeMatrix_update_succ
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin n)) :
    simplexEdgeMatrix (Function.update v j.succ y) =
      (simplexEdgeMatrix v).updateCol j
        ((y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) := by
  ext i k
  by_cases h : k = j
  · subst k
    have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
      (Fin.succ_ne_zero j).symm
    simp [simplexEdgeMatrix, Matrix.updateCol, Function.update, hzero]
  · have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
      (Fin.succ_ne_zero j).symm
    simp [simplexEdgeMatrix, Matrix.updateCol, Function.update, h, hzero]

private lemma simplexEdgeMatrix_update_zero
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) :
    simplexEdgeMatrix (Function.update v 0 y) =
      simplexEdgeMatrix v -
        Matrix.of fun i _ => (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp i := by
  ext i j
  simp [simplexEdgeMatrix, Matrix.sub_apply, Function.update, Fin.succ_ne_zero]

private lemma simplexEdgeMatrix_update_succ_det
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin n))
    (c : Fin n → ℝ)
    (hc :
      (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp =
        fun i => ∑ k, c k • (simplexEdgeMatrix v) i k) :
    (simplexEdgeMatrix (Function.update v j.succ y)).det =
      c j * (simplexEdgeMatrix v).det := by
  rw [simplexEdgeMatrix_update_succ]
  rw [hc]
  simpa [smul_eq_mul] using
    Matrix.det_updateCol_sum (simplexEdgeMatrix v) j c

/-- **Maximality of the simplex confines the body to a box in simplex coordinates** (Caffarelli's
argument): if `v` is a nondegenerate simplex of maximal volume in `K`,
then every `y ∈ K` has simplex coordinates `c = (M v)⁻¹ (y − v 0)` with `|cⱼ| ≤ 1` and
`|1 − ∑ cⱼ| ≤ 1`. -/
theorem abs_simplexCoord_le_one_of_max {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, v i ∈ K)
    (hdet : (simplexEdgeMatrix v).det ≠ 0)
    (hmax : ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
      |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det|)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ K) :
    (∀ j, |((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1) ∧
      |1 - ∑ j, ((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) ℝ := simplexEdgeMatrix v
  let u : Fin n → ℝ := (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp
  let c : Fin n → ℝ := M⁻¹ *ᵥ u
  have hunit : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  have hMu : M *ᵥ c = u := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv M hunit]
    simp
  have hc :
      u = fun i => ∑ k, c k * M i k := by
    funext i
    calc
      u i = (M *ᵥ c) i := (congrFun hMu i).symm
      _ = ∑ k, M i k * c k := by
        simp only [Matrix.mulVec, dotProduct]
      _ = ∑ k, c k * M i k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [mul_comm]
  have hcoord : ∀ j, |c j| ≤ 1 := by
    intro j
    let w := Function.update v j.succ y
    have hw : ∀ i, w i ∈ K := by
      intro i
      by_cases h : i = j.succ
      · subst i
        simpa [w] using hy
      · have hi : w i = v i := by
          simp [w, h]
        rw [hi]
        exact hv i
    have hdetw : |(simplexEdgeMatrix w).det| ≤ |M.det| := by
      simpa [w, M] using hmax w hw
    have hformula : (simplexEdgeMatrix w).det = c j * M.det := by
      change
        (simplexEdgeMatrix (Function.update v j.succ y)).det =
          c j * M.det
      apply simplexEdgeMatrix_update_succ_det v j y c
      simpa [M, u] using hc
    rw [hformula] at hdetw
    have hmul : |c j| * |M.det| ≤ |M.det| := by
      simpa [abs_mul] using hdetw
    have hpos : 0 < |M.det| := abs_pos.mpr (by simpa [M] using hdet)
    nlinarith
  have hsum : |1 - ∑ j, c j| ≤ 1 := by
    let w := Function.update v 0 y
    have hw : ∀ i, w i ∈ K := by
      intro i
      by_cases h : i = 0
      · subst i
        simpa [w] using hy
      · have hi : w i = v i := by
          simp [w, h]
        rw [hi]
        exact hv i
    have hdetw : |(simplexEdgeMatrix w).det| ≤ |M.det| := by
      simpa [w, M] using hmax w hw
    have hc_coord : ∀ z, c z = ∑ x, (M⁻¹) z x * u x := by
      intro z
      simp [c, Matrix.mulVec, dotProduct]
    have hsum' :
        (∑ x, (∑ z, (M⁻¹) z x) * u x) = ∑ z, c z := by
      calc
        (∑ x, (∑ z, (M⁻¹) z x) * u x) =
            ∑ x, ∑ z, (M⁻¹) z x * u x := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_mul]
        _ = ∑ z, ∑ x, (M⁻¹) z x * u x := by
              rw [Finset.sum_comm]
        _ = ∑ z, c z := by
              apply Finset.sum_congr rfl
              intro z hz
              exact (hc_coord z).symm
    have hsecond :
        (simplexEdgeMatrix w).det = M.det * (1 - ∑ j, c j) := by
      change
        (simplexEdgeMatrix (Function.update v 0 y)).det =
          M.det * (1 - ∑ j, c j)
      rw [simplexEdgeMatrix_update_zero]
      let U : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun i _ => -u i
      let V : Matrix (Fin 1) (Fin n) ℝ := Matrix.of fun _ _ => 1
      have hUV :
          M - Matrix.of (fun i _ => u i) = M + U * V := by
        ext i j
        simp [U, V, Matrix.mul_apply]
        ring
      rw [hUV]
      rw [Matrix.det_add_mul U V hunit]
      have hscalar :
          (V * M⁻¹ * U).det = -∑ j, c j := by
        rw [Matrix.det_fin_one]
        simp only [Matrix.mul_apply, V, U, Matrix.of_apply, one_mul, mul_neg,
          Finset.sum_neg_distrib]
        rw [hsum']
      have hplus :
          (1 + V * M⁻¹ * U).det = 1 - ∑ j, c j := by
        rw [Matrix.det_fin_one]
        rw [Matrix.add_apply]
        have hentry :
            (V * M⁻¹ * U) 0 0 = -∑ j, c j := by
          simpa only [Matrix.det_fin_one] using hscalar
        rw [hentry]
        simp [sub_eq_add_neg]
      rw [hplus]
    rw [hsecond] at hdetw
    have hmul : |M.det| * |1 - ∑ j, c j| ≤ |M.det| := by
      simpa [abs_mul, mul_comm] using hdetw
    have hpos : 0 < |M.det| := abs_pos.mpr (by simpa [M] using hdet)
    nlinarith
  simpa [M, c, u] using ⟨hcoord, hsum⟩

end FunctionalInequalities.Analysis

end MaxSimplexBox

section SimplexBall

open Set Metric

/-! A ball inside the standard simplex and the box inside a ball. -/

namespace FunctionalInequalities.Analysis

private lemma sum_abs_sub_le_sqrt_mul_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, |x i| ≤ Real.sqrt n * ‖x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => |x i|) (fun _ => (1 : ℝ))
  have hcs' : (∑ i, |x i|) ^ 2 ≤ (∑ i, x i ^ 2) * (n : ℝ) := by
    simpa only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul] using hcs
  have hnorm : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    calc
      ‖x‖ ^ 2 = (Real.sqrt (∑ i, ‖x i‖ ^ 2)) ^ 2 := by
        rw [EuclideanSpace.norm_eq]
      _ = ∑ i, ‖x i‖ ^ 2 := by
        rw [Real.sq_sqrt]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg (‖x i‖))
      _ = ∑ i, x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.norm_eq_abs, sq_abs]
  have hsq : (∑ i, |x i|) ^ 2 ≤ (Real.sqrt n * ‖x‖) ^ 2 := by
    calc
      (∑ i, |x i|) ^ 2 ≤ (∑ i, x i ^ 2) * (n : ℝ) := hcs'
      _ = ‖x‖ ^ 2 * (n : ℝ) := by rw [← hnorm]
      _ = (Real.sqrt n * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        ring
  exact
    (sq_le_sq₀
      (Finset.sum_nonneg (fun i _ => abs_nonneg (x i)))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

private lemma barycentre_ofLp_apply {n : ℕ} (i : Fin n) :
    (((1 / ((n : ℝ) + 1)) • ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i)
      = 1 / ((n : ℝ) + 1) := by
  simp [Finset.sum_apply]

/-- **The standard simplex contains a ball around its barycentre, and the coordinate box lies in a
ball** (Caffarelli's argument). -/
theorem closedBall_subset_stdSimplex_and_box_subset_closedBall {n : ℕ} (hn : 0 < n) :
    closedBall ((1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ))
        (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) ⊆
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} ∧
    {y : EuclideanSpace ℝ (Fin n) | (∀ i, |y i| ≤ 1) ∧ |1 - ∑ i, y i| ≤ 1} ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) := by
  constructor
  · intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    constructor
    · intro i
      have hi :
          |y i - 1 / ((n : ℝ) + 1)| ≤
            ‖y - ((1 / ((n : ℝ) + 1)) •
              ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        have hi' := PiLp.norm_apply_le
          (y - ((1 / ((n : ℝ) + 1)) •
            ∑ j, EuclideanSpace.single j (1 : ℝ))) i
        rw [Real.norm_eq_abs] at hi'
        have hcoord :
            (y - ((1 / ((n : ℝ) + 1)) •
              ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i =
              y.ofLp i - 1 / ((n : ℝ) + 1) := by
          change y.ofLp i -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i =
              y.ofLp i - 1 / ((n : ℝ) + 1)
          rw [barycentre_ofLp_apply]
        rw [hcoord] at hi'
        exact hi'
      have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
      have hdenpos : 0 < 2 * ((n : ℝ) + 1) := by
        positivity
      have hdenle :
          2 * ((n : ℝ) + 1) ≤
            2 * ((n : ℝ) + 1) * Real.sqrt n := by
        have hnonneg : 0 ≤ 2 * ((n : ℝ) + 1) := by
          positivity
        have hdiff : 0 ≤ Real.sqrt n - 1 := sub_nonneg.mpr hsqrt
        nlinarith [mul_nonneg hnonneg hdiff]
      have hρ :
          1 / (2 * ((n : ℝ) + 1) * Real.sqrt n) ≤
            1 / (2 * ((n : ℝ) + 1)) :=
        one_div_le_one_div_of_le hdenpos hdenle
      have hiρ :
          |y i - 1 / ((n : ℝ) + 1)| ≤
            1 / (2 * ((n : ℝ) + 1)) :=
        le_trans (le_trans hi hy) hρ
      have hlow :
          1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) ≤ y i := by
        have h := (abs_le.mp hiρ).1
        linarith
      have hnonneg :
          0 ≤ 1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) := by
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have heq :
            1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) =
              1 / (2 * ((n : ℝ) + 1)) := by
          field_simp [ne_of_gt hn1]
          ring
        rw [heq]
        positivity
      exact le_trans hnonneg hlow
    · have hsumabs :
          ∑ i, |y i - 1 / ((n : ℝ) + 1)| ≤
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        calc
          ∑ i, |y i - 1 / ((n : ℝ) + 1)| =
              ∑ i, |(y -
                ((1 / ((n : ℝ) + 1)) •
                  ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i| := by
                apply Finset.sum_congr rfl
                intro i hi
                have hcoord :
                    (y - ((1 / ((n : ℝ) + 1)) •
                      ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i =
                      y.ofLp i - 1 / ((n : ℝ) + 1) := by
                  change y.ofLp i -
                      ((1 / ((n : ℝ) + 1)) •
                        ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i =
                      y.ofLp i - 1 / ((n : ℝ) + 1)
                  rw [barycentre_ofLp_apply]
                rw [hcoord]
          _ ≤ Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ :=
            sum_abs_sub_le_sqrt_mul_norm _
      have hsum :
          ∑ i, y i ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        calc
          ∑ i, y i ≤
              ∑ i, (1 / ((n : ℝ) + 1) +
                |y i - 1 / ((n : ℝ) + 1)|) := by
            apply Finset.sum_le_sum
            intro i hi
            linarith [le_abs_self (y i - 1 / ((n : ℝ) + 1))]
          _ = ∑ i, (1 / ((n : ℝ) + 1)) +
              ∑ i, |y i - 1 / ((n : ℝ) + 1)| := by
            rw [Finset.sum_add_distrib]
          _ = n / ((n : ℝ) + 1) +
              ∑ i, |y i - 1 / ((n : ℝ) + 1)| := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            ring
          _ ≤ n / ((n : ℝ) + 1) +
              Real.sqrt n * ‖y -
                ((1 / ((n : ℝ) + 1)) •
                  ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
            simpa [add_comm] using
              add_le_add_left hsumabs (n / ((n : ℝ) + 1))
      calc
        ∑ i, y i ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := hsum
        _ ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n *
              (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) := by
          gcongr
        _ = n / ((n : ℝ) + 1) +
            1 / (2 * ((n : ℝ) + 1)) := by
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
          field_simp [ne_of_gt hsqrtpos]
        _ ≤ 1 := by
          have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          field_simp [ne_of_gt hn1]
          nlinarith
  · intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero]
    have hsq : ‖y‖ ^ 2 ≤ (n : ℝ) := by
      calc
        ‖y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
          exact Finset.sum_nonneg (fun i _ => sq_nonneg (‖y i‖))
        _ ≤ ∑ i, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Real.norm_eq_abs, sq_abs]
          exact (sq_le_one_iff_abs_le_one (y i)).mpr (hy.1 i)
        _ = (n : ℝ) := by
          simp
    have hnorm : 0 ≤ ‖y‖ := norm_nonneg _
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    exact (sq_le_sq₀ hnorm hsqrt).mp (by
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      exact hsq)

end FunctionalInequalities.Analysis

end SimplexBall

section AffineNormalizationAssembly

open Set Metric

/-! Affine normalisation of a convex body: an affine image sandwiched between two balls with
dimensional radii. -/

namespace FunctionalInequalities.Analysis

private noncomputable def simplexCoordinateEquiv {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hunit : IsUnit M.det) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := by
  have h₁ :
      (Matrix.toLpLin 2 2 M⁻¹).comp (Matrix.toLpLin 2 2 M) =
        LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply PiLp.ext
    intro i
    change
      ((Matrix.toLpLin 2 2 M⁻¹)
        ((Matrix.toLpLin 2 2 M) y)).ofLp i = y.ofLp i
    rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    change (M⁻¹.mulVec (M.mulVec y.ofLp)) i = y.ofLp i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hunit]
    simp
  have h₂ :
      (Matrix.toLpLin 2 2 M).comp (Matrix.toLpLin 2 2 M⁻¹) =
        LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply PiLp.ext
    intro i
    change
      ((Matrix.toLpLin 2 2 M)
        ((Matrix.toLpLin 2 2 M⁻¹) y)).ofLp i = y.ofLp i
    rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    change (M.mulVec (M⁻¹.mulVec y.ofLp)) i = y.ofLp i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit]
    simp
  exact LinearEquiv.ofLinearMap
    (Matrix.toLpLin 2 2 M⁻¹) (Matrix.toLpLin 2 2 M) h₁ h₂

/-- **Affine normalisation of convex bodies** (John-type, via a maximal-volume simplex; Caffarelli's
argument): there is a constant `C` depending only on the space such that every
compact convex set with nonempty interior is affinely equivalent to a set squeezed between the unit
ball and the ball of radius `C`. -/
theorem exists_affine_normalization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ e : E ≃ᵃ[ℝ] E, closedBall (0 : E) 1 ⊆ e '' K ∧ e '' K ⊆ closedBall (0 : E) C := by
  classical
  -- Pass to Euclidean coordinates and separate the zero-dimensional case.
  let n : ℕ := Module.finrank ℝ E
  let L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (stdOrthonormalBasis ℝ E).repr
  by_cases hn : n = 0
  · have hzero : ∀ x : E, x = 0 := by
      intro x
      apply L.injective
      apply PiLp.ext
      intro i
      exact Fin.elim0 (hn ▸ i)
    refine ⟨1, zero_lt_one, ?_⟩
    intro K _ _ hint
    obtain ⟨y, hy⟩ := hint
    refine ⟨AffineEquiv.refl ℝ E, ?_, ?_⟩
    · intro x _
      refine ⟨y, interior_subset hy, ?_⟩
      change y = x
      rw [hzero y, hzero x]
    · intro x _
      rw [hzero x]
      simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    let F := EuclideanSpace ℝ (Fin n)
    let c : F :=
      (1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ)
    let ρ : ℝ := 1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)
    have hρ : 0 < ρ := by
      dsimp [ρ]
      positivity
    let C : ℝ := ρ⁻¹ * (Real.sqrt n + ‖c‖) + 1
    have hC : 0 < C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, ?_⟩
    intro K hK hconv hint
    let KF : Set F := L '' K
    have hKF : IsCompact KF := hK.image L.continuous
    have hconvF : Convex ℝ KF :=
      hconv.linear_image L.toLinearMap
    have hintF : (interior KF).Nonempty := by
      change (interior (L '' K)).Nonempty
      have hInt : L '' interior K = interior (L '' K) :=
        L.toHomeomorph.image_interior K
      rw [← hInt]
      exact Set.Nonempty.image L hint
    -- Choose a simplex of maximal determinant in the compact convex set.
    obtain ⟨v, hv, hdet, hmax⟩ :=
      exists_max_simplexEdgeMatrix_det hKF hintF
    let M : Matrix (Fin n) (Fin n) ℝ := simplexEdgeMatrix v
    have hM : M.det ≠ 0 := abs_pos.mp hdet
    have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    let T : F ≃ₗ[ℝ] F := simplexCoordinateEquiv M hunit
    have hTcoord (y : F) :
        (T y).ofLp = M⁻¹.mulVec y.ofLp := by
      change ((Matrix.toLpLin 2 2 M⁻¹) y).ofLp = M⁻¹.mulVec y.ofLp
      rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    let A : F ≃ᵃ[ℝ] F :=
      AffineEquiv.mk' (fun y : F => T (y - v 0)) T 0 (by
        intro y
        simp [sub_eq_add_neg])
    have hAcoord (y : F) :
        (A y).ofLp = M⁻¹.mulVec (y - v 0 : F).ofLp := by
      change (T (y - v 0)).ofLp = M⁻¹.mulVec (y - v 0 : F).ofLp
      exact hTcoord (y - v 0)
    let box : Set F :=
      {y | (∀ j, |y j| ≤ 1) ∧ |1 - ∑ j, y j| ≤ 1}
    let simplex : Set F :=
      {y | (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1}
    have hAKbox : A '' KF ⊆ box := by
      rintro z ⟨y, hy, rfl⟩
      change
        (∀ j, |(A y).ofLp j| ≤ 1) ∧
          |1 - ∑ j, (A y).ofLp j| ≤ 1
      rw [hAcoord y]
      exact abs_simplexCoord_le_one_of_max hv hM hmax hy
    have hsimplexAK : simplex ⊆ A '' KF := by
      intro y hy
      change (∀ i, 0 ≤ y.ofLp i) ∧ ∑ i, y.ofLp i ≤ 1 at hy
      let w : Fin (n + 1) → ℝ :=
        Fin.cases (1 - ∑ j, y.ofLp j) y.ofLp
      let p : F := ∑ i, w i • v i
      have hw0 : ∀ i, 0 ≤ w i := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact sub_nonneg.mpr hy.2
        · intro j
          exact hy.1 j
      have hw1 : ∑ i, w i = 1 := by
        simp [w, Fin.sum_univ_succ]
      have hp : p ∈ KF := by
        apply hconvF.sum_mem
        · intro i _
          exact hw0 i
        · exact hw1
        · intro i _
          exact hv i
      have hpform :
          p = v 0 + ∑ j, y.ofLp j • (v j.succ - v 0) := by
        change (∑ i, w i • v i) =
          v 0 + ∑ j, y.ofLp j • (v j.succ - v 0)
        rw [Fin.sum_univ_succ]
        change
          (1 - ∑ j, y.ofLp j) • v 0 + ∑ j, y.ofLp j • v j.succ =
            v 0 + ∑ j, y.ofLp j • (v j.succ - v 0)
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
          sub_smul, one_smul]
        abel
      have hMp :
          M.mulVec y.ofLp = (p - v 0 : F).ofLp := by
        rw [hpform]
        ext i
        simp only [mulVec, dotProduct, simplexEdgeMatrix, PiLp.sub_apply, of_apply,
          add_sub_cancel_left, WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_sub, Finset.sum_apply,
          Pi.smul_apply, Pi.sub_apply, smul_eq_mul, M]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hcoord :
          M⁻¹.mulVec (p - v 0 : F).ofLp = y.ofLp := by
        rw [← hMp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hunit]
        simp
      refine ⟨p, hp, ?_⟩
      apply PiLp.ext
      intro i
      exact congrFun ((hAcoord p).trans hcoord) i
    have hballs :
        closedBall c ρ ⊆ A '' KF ∧
          A '' KF ⊆ closedBall (0 : F) (Real.sqrt n) := by
      have hgeom := closedBall_subset_stdSimplex_and_box_subset_closedBall hnpos
      exact ⟨hgeom.1.trans hsimplexAK, hAKbox.trans hgeom.2⟩
    let V : F ≃ᵃ[ℝ] F := AffineEquiv.constVAdd ℝ F (-c)
    let H : F ≃ᵃ[ℝ] F :=
      (LinearEquiv.smulOfNeZero ℝ F ρ⁻¹ (inv_ne_zero hρ.ne')).toAffineEquiv
    let B : F ≃ᵃ[ℝ] F := (A.trans V).trans H
    -- Rescale the simplex coordinates to obtain the two ball inclusions.
    have hBapply (z : F) : B z = ρ⁻¹ • (A z - c) := by
      change ρ⁻¹ • (-c + A z) = ρ⁻¹ • (A z - c)
      congr 1
      abel
    have hinner : closedBall (0 : F) 1 ⊆ B '' KF := by
      intro x hx
      have hx' : ‖x‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using hx
      have hu : c + ρ • x ∈ closedBall c ρ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left,
          norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hx' hρ.le
      obtain ⟨z, hz, hAz⟩ := hballs.1 hu
      refine ⟨z, hz, ?_⟩
      rw [hBapply, hAz, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hρ.ne', one_smul]
    have houter : B '' KF ⊆ closedBall (0 : F) C := by
      rintro x ⟨z, hz, rfl⟩
      have hAz : ‖A z‖ ≤ Real.sqrt n := by
        have hmem := hballs.2 ⟨z, hz, rfl⟩
        simpa only [mem_closedBall, dist_zero_right] using hmem
      rw [mem_closedBall, dist_zero_right, hBapply,
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      calc
        ρ⁻¹ * ‖A z - c‖ ≤ ρ⁻¹ * (‖A z‖ + ‖c‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hρ.le)
        _ ≤ ρ⁻¹ * (Real.sqrt n + ‖c‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hAz (le_refl ‖c‖))
            (inv_nonneg.mpr hρ.le)
        _ ≤ C := by
          dsimp [C]
          linarith
    let e : E ≃ᵃ[ℝ] E :=
      L.toLinearEquiv.toAffineEquiv.trans
        (B.trans L.symm.toLinearEquiv.toAffineEquiv)
    have he (x : E) : e x = L.symm (B (L x)) := rfl
    refine ⟨e, ?_, ?_⟩
    · intro x hx
      have hxF : L x ∈ closedBall (0 : F) 1 := by
        simpa only [mem_closedBall, dist_zero_right, L.norm_map] using hx
      obtain ⟨z, hz, hzx⟩ := hinner hxF
      obtain ⟨k, hk, hkz⟩ := hz
      refine ⟨k, hk, ?_⟩
      rw [he, hkz, hzx, L.symm_apply_apply]
    · rintro x ⟨k, hk, rfl⟩
      have hkF : L k ∈ KF := ⟨k, hk, rfl⟩
      have hBx : B (L k) ∈ closedBall (0 : F) C :=
        houter ⟨L k, hkF, rfl⟩
      rw [he]
      simpa only [mem_closedBall, dist_zero_right, L.symm.norm_map] using hBx

end FunctionalInequalities.Analysis

end AffineNormalizationAssembly
