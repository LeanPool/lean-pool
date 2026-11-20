/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartWeakTransfer
public import LeanPool.FastDynamo.Global.CellSeriesSummability
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The concrete added axial velocity: the Euclidean chart fields

This file constructs the smooth Euclidean fields

`a_n * vartheta (|y - p_n| / R_n) * e_3`,

where `|.|` is the EUCLIDEAN norm of the chart and `vartheta` is one on the closed Euclidean
disc of radius `3 / 4` and vanishes off the open Euclidean unit disc (`eq:axial-offset` and
the choice of `ϑ` before it).  Since `ℝ × ℝ` carries the product (sup) metric, the Euclidean
distance of the chart is named `pairEuclideanDist` here and is what the constant-axial-region
statements use;
the sup metric of `bufferDisk` is weaker, so the support statements are kept in it.  The radial
profile `vartheta` itself, which `prop:particle-flow` needs, is in
`Global/TorusAxialPlateauRadial.lean`.

Proved here: the exact constant-core and buffer support statements, pointwise reality, the
displayed classical derivatives and their divergence cancellation, and the scale bounds — all
in the Euclidean chart.  The descent of these fields to the transverse torus, their
pointwise summability and the disjoint-support formulae are in
`Global/TorusAxialVelocityConcrete.lean`, which imports this module; the final identification
of the descended derivative representatives as Fourier weak derivatives is carried out
downstream in `Global/TorusAxialVelocityWeakTransfer.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}

/-! ## A fixed Euclidean-radial plateau and its scale-independent derivative bound -/

/-- The Euclidean distance of the paper's placement chart, read on pair coordinates.

`ℝ × ℝ` carries the product (sup) metric, while `eq:axial-offset` cuts the
added axial velocity off at the *Euclidean* distance `|y - p_n|`.  This is that Euclidean
distance, transported to pair coordinates by `pairToWholePlane`. -/
def pairEuclideanDist (x y : ℝ × ℝ) : ℝ :=
  ‖pairToWholePlane x - pairToWholePlane y‖

/-- The Euclidean chart distance is the `WholePlane` distance of the two images. -/
theorem pairEuclideanDist_eq_dist (x y : ℝ × ℝ) :
    pairEuclideanDist x y = dist (pairToWholePlane x) (pairToWholePlane y) :=
  (dist_eq_norm _ _).symm

/-- The Euclidean chart distance is nonnegative. -/
theorem pairEuclideanDist_nonneg (x y : ℝ × ℝ) : 0 ≤ pairEuclideanDist x y :=
  norm_nonneg _

/-- Triangle inequality for the Euclidean chart distance. -/
theorem pairEuclideanDist_triangle (x y z : ℝ × ℝ) :
    pairEuclideanDist x z ≤ pairEuclideanDist x y + pairEuclideanDist y z := by
  simp only [pairEuclideanDist_eq_dist]
  exact dist_triangle _ _ _

/-- The chart's product (sup) metric is dominated by its Euclidean distance, so every
Euclidean disc sits inside the product-metric ball of the same radius. -/
theorem dist_le_pairEuclideanDist (x y : ℝ × ℝ) :
    dist x y ≤ pairEuclideanDist x y :=
  dist_le_norm_pairToWholePlane_sub x y

/-- Conversely the Euclidean chart distance is at most twice the product metric.  The
factor two is intentionally coarse; every placement margin used here is a factor ten. -/
theorem pairEuclideanDist_le_two_mul_dist (x y : ℝ × ℝ) :
    pairEuclideanDist x y ≤ 2 * dist x y :=
  norm_pairToWholePlane_sub_le_two_mul_dist x y

/-- The squared Euclidean norm of a pair image is the coordinate sum of squares. -/
theorem norm_pairToWholePlane_sq (x : ℝ × ℝ) :
    ‖pairToWholePlane x‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The Euclidean chart distance of two points on a common horizontal line is the absolute
difference of their first coordinates. -/
theorem pairEuclideanDist_eq_abs_of_snd_eq {x y : ℝ × ℝ} (h : x.2 = y.2) :
    pairEuclideanDist x y = |x.1 - y.1| := by
  have hsq : pairEuclideanDist x y ^ 2 = |x.1 - y.1| ^ 2 := by
    rw [pairEuclideanDist, ← map_sub, norm_pairToWholePlane_sq, sq_abs]
    simp [h]
  have h1 : 0 ≤ pairEuclideanDist x y := pairEuclideanDist_nonneg x y
  have h2 : 0 ≤ |x.1 - y.1| := abs_nonneg _
  have hle := (abs_le_of_sq_le_sq' hsq.le h2).2
  have hge := (abs_le_of_sq_le_sq' hsq.ge h1).2
  linarith

/-- The paper's cut-off `ϑ` read as a function of the SQUARED Euclidean radius: it is
`1` on `[0, 9/16]` and vanishes on `[1, ∞)`, so `t ↦ axialPlateauSq (t ^ 2)` is a profile
with `0 ≤ ϑ ≤ 1`, `ϑ = 1` on `[0, 3/4]` and `supp ϑ ⊂ [0, 1)` (§3.3, before `eq:local-copy`).

Using the square rather than the radius keeps the cut-off smooth at a cell centre —
`‖y‖ ^ 2` is a polynomial in the chart coordinates, while `‖y‖` is not differentiable at
`0` — and it makes the profile *provably* radial, which `prop:particle-flow` needs.
Mathlib's `ContDiffBump` cannot supply radiality: its base
function is produced by `Classical.choice` and only evenness is recorded. -/
def axialPlateauSq (s : ℝ) : ℝ :=
  Real.smoothTransition (16 / 7 * (1 - s))

/-- The squared-radius profile takes values in `[0, 1]` (`0 ≤ ϑ ≤ 1`, §3.3). -/
theorem axialPlateauSq_mem_Icc (s : ℝ) : axialPlateauSq s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The profile is one through squared radius `9 / 16`, i.e. `ϑ = 1` on `[0, 3/4]`. -/
theorem axialPlateauSq_eq_one_of_le {s : ℝ} (hs : s ≤ 9 / 16) :
    axialPlateauSq s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The profile vanishes from squared radius `1` on, i.e. `supp ϑ ⊂ [0, 1)`. -/
theorem axialPlateauSq_eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    axialPlateauSq s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The squared-radius profile is smooth. -/
theorem axialPlateauSq_contDiff {n : ℕ∞} : ContDiff ℝ n axialPlateauSq := by
  have h : ContDiff ℝ n fun s : ℝ ↦ 16 / 7 * (1 - s) :=
    contDiff_const.mul (contDiff_const.sub contDiff_id)
  exact Real.smoothTransition.contDiff.comp h

/-- The fixed cut-off `ϑ(|y|)` of `eq:axial-offset` in pair coordinates.  It is
radial for the EUCLIDEAN norm of the chart: one on the closed Euclidean disc of radius
`3 / 4` and zero outside the open Euclidean unit disc. -/
def axialPlateauBump (y : ℝ × ℝ) : ℝ :=
  axialPlateauSq (y.1 ^ 2 + y.2 ^ 2)

/-- The plateau written through the squared Euclidean norm of the chart image. -/
theorem axialPlateau_eq_axialPlateauSq (y : ℝ × ℝ) :
    axialPlateauBump y = axialPlateauSq (‖pairToWholePlane y‖ ^ 2) := by
  rw [axialPlateauBump, norm_pairToWholePlane_sq]

/-- The fixed plateau takes values in `[0, 1]`. -/
theorem axialPlateau_mem_Icc (x : ℝ × ℝ) :
    axialPlateauBump x ∈ Set.Icc (0 : ℝ) 1 :=
  axialPlateauSq_mem_Icc _

/-- The fixed plateau is nonnegative. -/
theorem axialPlateau_nonneg (x : ℝ × ℝ) : 0 ≤ axialPlateauBump x :=
  (axialPlateau_mem_Icc x).1

/-- The fixed plateau is bounded by one. -/
theorem axialPlateau_le_one (x : ℝ × ℝ) : axialPlateauBump x ≤ 1 :=
  (axialPlateau_mem_Icc x).2

/-- The plateau equals `1` on the closed EUCLIDEAN disc of radius `3 / 4`, the
paper's normalization `ϑ = 1` on `[0, 3/4]` (§3.3, the choice of `ϑ` before `eq:local-copy`).
-/
theorem axialPlateau_eq_one_of_norm_pairToWholePlane_le {x : ℝ × ℝ}
    (hx : ‖pairToWholePlane x‖ ≤ 3 / 4) : axialPlateauBump x = 1 := by
  rw [axialPlateau_eq_axialPlateauSq]
  exact axialPlateauSq_eq_one_of_le (by nlinarith [norm_nonneg (pairToWholePlane x)])

/-- The plateau equals `1` on the product-metric ball of radius `1 / 2`: that ball lies in
the Euclidean disc of radius `√2 / 2 < 3 / 4`. -/
theorem axialPlateau_eq_one_of_norm_le_half {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1 / 2) :
    axialPlateauBump x = 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hx
  have h1 : |x.1| ≤ 1 / 2 := (le_max_left _ _).trans hx
  have h2 : |x.2| ≤ 1 / 2 := (le_max_right _ _).trans hx
  rw [axialPlateauBump]
  refine axialPlateauSq_eq_one_of_le ?_
  nlinarith [sq_abs x.1, sq_abs x.2, abs_nonneg x.1, abs_nonneg x.2]

/-- The plateau vanishes outside the open unit ball of the product metric, boundary
included.  The Euclidean unit disc lies inside that ball, so this is the paper's
`supp ϑ ⊂ [0, 1)` in its weakest chart form. -/
theorem axialPlateau_eq_zero_of_one_le_norm {x : ℝ × ℝ} (hx : 1 ≤ ‖x‖) :
    axialPlateauBump x = 0 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hx
  rw [axialPlateauBump]
  refine axialPlateauSq_eq_zero_of_one_le ?_
  rcases le_max_iff.mp hx with h | h
  · nlinarith [sq_abs x.1, sq_nonneg x.2, abs_nonneg x.1]
  · nlinarith [sq_abs x.2, sq_nonneg x.1, abs_nonneg x.2]

/-- The fixed plateau is smooth, being the smooth transition composed with a polynomial. -/
theorem axialPlateau_contDiff {n : ℕ∞} : ContDiff ℝ n axialPlateauBump := by
  have h : ContDiff ℝ n fun y : ℝ × ℝ ↦ y.1 ^ 2 + y.2 ^ 2 :=
    (contDiff_fst.pow 2).add (contDiff_snd.pow 2)
  exact axialPlateauSq_contDiff.comp h

/-- The fixed plateau has compact support: it vanishes off the closed product-metric unit
ball, which is compact. -/
theorem axialPlateau_hasCompactSupport : HasCompactSupport axialPlateauBump := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) 1) ?_
  intro x hx
  refine axialPlateau_eq_zero_of_one_le_norm ?_
  have hlt : 1 < ‖x‖ := by
    simpa [mem_closedBall, dist_zero_right, not_le] using hx
  exact hlt.le

/-- A canonical Lipschitz constant for the fixed plateau. -/
def axialPlateauLipschitzConstant : NNReal :=
  Classical.choose
    (ContDiff.lipschitzWith_of_hasCompactSupport
      axialPlateau_hasCompactSupport
      (axialPlateau_contDiff : ContDiff ℝ 1 axialPlateauBump)
      (by norm_num))

/-- The fixed radial plateau `ϑ` is Lipschitz with the constant `axialPlateauLipschitzConstant`
chosen for it; this is the defining property of that constant. -/
theorem axialPlateau_lipschitzWith :
    LipschitzWith axialPlateauLipschitzConstant axialPlateauBump :=
  Classical.choose_spec
    (ContDiff.lipschitzWith_of_hasCompactSupport
      axialPlateau_hasCompactSupport
      (axialPlateau_contDiff : ContDiff ℝ 1 axialPlateauBump)
      (by norm_num))

/-- The Fréchet derivative of the fixed plateau vanishes also on the outer
boundary.  At a zero of this nonnegative smooth function, the point is a
global (hence local) minimum. -/
theorem fderiv_axialPlateau_eq_zero_of_one_le_norm {x : ℝ × ℝ}
    (hx : 1 ≤ ‖x‖) : fderiv ℝ axialPlateauBump x = 0 := by
  have hzero : axialPlateauBump x = 0 :=
    axialPlateau_eq_zero_of_one_le_norm hx
  have hmin : IsLocalMin axialPlateauBump x :=
    Filter.Eventually.of_forall (fun y ↦ by
      rw [hzero]
      exact axialPlateau_nonneg y)
  exact hmin.fderiv_eq_zero

/-- The Fréchet derivative of the plateau is bounded, in operator norm, by its Lipschitz
constant; this is the fixed, scale-independent `‖ϑ'‖_∞` of the paper. -/
theorem norm_fderiv_axialPlateau_le (x : ℝ × ℝ) :
    ‖fderiv ℝ axialPlateauBump x‖ ≤
      (axialPlateauLipschitzConstant : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ axialPlateau_lipschitzWith

/-! ## One Euclidean axial cell -/

/-- The normalized buffer coordinate `(y - pₙ) / Rₙ`. -/
def axialBufferCoordinate
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (x : ℝ × ℝ) : ℝ × ℝ :=
  (P.scaleFamily.bufferRadius n)⁻¹ •
    (x - P.scaleFamily.cellCenter n)

/-- Norm of the normalized buffer coordinate: `‖(y - p_n)/R_n‖ = dist (y, p_n) / R_n`, so
membership in the buffer disc is exactly the statement that this norm is `< 1`. -/
theorem norm_axialBufferCoordinate
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (x : ℝ × ℝ) :
    ‖P.axialBufferCoordinate n x‖ =
      dist x (P.scaleFamily.cellCenter n) /
        P.scaleFamily.bufferRadius n := by
  calc
    ‖P.axialBufferCoordinate n x‖ =
        ‖(P.scaleFamily.bufferRadius n)⁻¹‖ *
          ‖x - P.scaleFamily.cellCenter n‖ := by
      rw [axialBufferCoordinate, norm_smul]
    _ = (P.scaleFamily.bufferRadius n)⁻¹ *
          ‖x - P.scaleFamily.cellCenter n‖ := by
      rw [Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (P.scaleFamily.bufferRadius_pos n))]
    _ = dist x (P.scaleFamily.cellCenter n) /
          P.scaleFamily.bufferRadius n := by
      rw [dist_eq_norm, div_eq_inv_mul]

/-- Euclidean norm of the normalized buffer coordinate:
`|(y - p_n)/R_n| = |y - p_n| / R_n`, the argument of `ϑ` in `eq:axial-offset`. -/
theorem norm_pairToWholePlane_axialBufferCoordinate
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (x : ℝ × ℝ) :
    ‖pairToWholePlane (P.axialBufferCoordinate n x)‖ =
      pairEuclideanDist x (P.scaleFamily.cellCenter n) /
        P.scaleFamily.bufferRadius n := by
  have hR := P.scaleFamily.bufferRadius_pos n
  rw [axialBufferCoordinate, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), pairEuclideanDist, ← map_sub, div_eq_inv_mul]

/-- The scalar cutoff `ϑ ((y-pₙ)/Rₙ)`. -/
def axialCellCutoff
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (x : ℝ × ℝ) : ℝ :=
  axialPlateauBump (P.axialBufferCoordinate n x)

/-- The scaled cutoff `ϑ((y - p_n)/R_n)` is smooth, being the plateau composed with an affine
map. -/
theorem axialCellCutoff_contDiff
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (P.axialCellCutoff n) := by
  apply axialPlateau_contDiff.comp
  have hscale : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : ℝ × ℝ ↦ (P.scaleFamily.bufferRadius n)⁻¹) :=
    contDiff_const
  have hsub : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ × ℝ ↦ x - P.scaleFamily.cellCenter n) :=
    contDiff_id.sub contDiff_const
  exact hscale.smul hsub

/-- The scaled cutoff takes values in `[0, 1]`, inherited from the plateau. -/
theorem axialCellCutoff_mem_Icc
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (x : ℝ × ℝ) : P.axialCellCutoff n x ∈ Set.Icc (0 : ℝ) 1 :=
  axialPlateau_mem_Icc _

/-- The exact core of the paper: the cutoff equals one throughout
`D(pₙ, 3 Rₙ / 4)`, with a closed-radius version for convenient use. -/
theorem axialCellCutoff_eq_one_of_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4) :
    P.axialCellCutoff n x = 1 := by
  apply axialPlateau_eq_one_of_norm_pairToWholePlane_le
  rw [P.norm_pairToWholePlane_axialBufferCoordinate n x]
  apply (div_le_iff₀ (P.scaleFamily.bufferRadius_pos n)).2
  nlinarith

/-- The cutoff vanishes pointwise off the open buffer disc, including its
boundary. -/
theorem axialCellCutoff_eq_zero_of_not_mem_bufferDisk
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {x : ℝ × ℝ} (hx : x ∉ P.scaleFamily.bufferDisk n) :
    P.axialCellCutoff n x = 0 := by
  apply axialPlateau_eq_zero_of_one_le_norm
  rw [P.norm_axialBufferCoordinate n x]
  apply (le_div_iff₀ (P.scaleFamily.bufferRadius_pos n)).2
  simpa [ScaleFamily.bufferDisk, mem_ball, not_lt] using hx

/-- The actual coordinate derivative of the scaled scalar cutoff. -/
def axialCellCutoffDerivative
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (j : Fin 2) (x : ℝ × ℝ) : ℝ :=
  (P.scaleFamily.bufferRadius n)⁻¹ *
    fderiv ℝ axialPlateauBump (P.axialBufferCoordinate n x) (pairBasis j)

/-- The normalized buffer coordinate `y ↦ (y - p_n)/R_n` is affine with Fréchet derivative the
constant map `R_n⁻¹ • id`. -/
theorem axialBufferCoordinate_hasFDerivAt
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (x : ℝ × ℝ) :
    HasFDerivAt (P.axialBufferCoordinate n)
      ((P.scaleFamily.bufferRadius n)⁻¹ •
        ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
  change HasFDerivAt
    (fun y : ℝ × ℝ ↦ (P.scaleFamily.bufferRadius n)⁻¹ •
      (y - P.scaleFamily.cellCenter n)) _ x
  exact ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const
    (P.scaleFamily.cellCenter n)).const_smul
      (P.scaleFamily.bufferRadius n)⁻¹

/-- Chain rule for the scaled cutoff: its Fréchet derivative at `x` is the plateau's derivative at
`(x - p_n)/R_n` composed with `R_n⁻¹ • id`. -/
theorem axialCellCutoff_hasFDerivAt
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (x : ℝ × ℝ) :
    HasFDerivAt (P.axialCellCutoff n)
      ((fderiv ℝ axialPlateauBump (P.axialBufferCoordinate n x)).comp
        ((P.scaleFamily.bufferRadius n)⁻¹ •
          ContinuousLinearMap.id ℝ (ℝ × ℝ))) x := by
  have hd : Differentiable ℝ (axialPlateauBump : (ℝ × ℝ) → ℝ) :=
    (axialPlateau_contDiff : ContDiff ℝ 1 axialPlateauBump).differentiable
      (by norm_num)
  exact (hd (P.axialBufferCoordinate n x)).hasFDerivAt.comp x
    (P.axialBufferCoordinate_hasFDerivAt n x)

/-- Evaluating the derivative of the scaled cutoff on the `j`-th coordinate basis vector returns
the displayed formula `axialCellCutoffDerivative`, i.e. `R_n⁻¹ ∂_j ϑ((x - p_n)/R_n)`. -/
theorem fderiv_axialCellCutoff_apply_pairBasis
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (j : Fin 2) (x : ℝ × ℝ) :
    fderiv ℝ (P.axialCellCutoff n) x (pairBasis j) =
      P.axialCellCutoffDerivative n j x := by
  rw [(P.axialCellCutoff_hasFDerivAt n x).fderiv]
  simp [axialCellCutoffDerivative]

/-- The displayed derivative of the scaled cutoff vanishes off the buffer disc: outside the disc
the plateau is at a global minimum, so its derivative there is zero. -/
theorem axialCellCutoffDerivative_eq_zero_of_not_mem_bufferDisk
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (j : Fin 2) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    P.axialCellCutoffDerivative n j x = 0 := by
  have hnorm : 1 ≤ ‖P.axialBufferCoordinate n x‖ := by
    rw [P.norm_axialBufferCoordinate n x]
    apply (le_div_iff₀ (P.scaleFamily.bufferRadius_pos n)).2
    simpa [ScaleFamily.bufferDisk, mem_ball, not_lt] using hx
  rw [axialCellCutoffDerivative,
    fderiv_axialPlateau_eq_zero_of_one_le_norm hnorm]
  simp

/-- The displayed cutoff derivative obeys the scale bound `‖∂_j χ_n‖ ≤ ‖ϑ'‖_∞ / R_n`, the
`R_n⁻¹` scaling behind the paper's bound `‖∇u_n^ax‖_∞ ≤ (a_n/R_n)‖ϑ'‖_∞` (§3.3; the parametrix
cut-offs obey the same scaling in `eq:parametrix-cutoff-bounds`). -/
theorem norm_axialCellCutoffDerivative_le
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (j : Fin 2) (x : ℝ × ℝ) :
    ‖P.axialCellCutoffDerivative n j x‖ ≤
      (axialPlateauLipschitzConstant : ℝ) /
        P.scaleFamily.bufferRadius n := by
  have hbasis : ‖pairBasis j‖ = 1 := by
    fin_cases j <;> simp [pairBasis, Prod.norm_def]
  have hRinv : 0 ≤ (P.scaleFamily.bufferRadius n)⁻¹ :=
    (inv_pos.mpr (P.scaleFamily.bufferRadius_pos n)).le
  have happly :
      ‖fderiv ℝ axialPlateauBump (P.axialBufferCoordinate n x)
          (pairBasis j)‖ ≤ (axialPlateauLipschitzConstant : ℝ) := by
    calc
      ‖fderiv ℝ axialPlateauBump (P.axialBufferCoordinate n x)
          (pairBasis j)‖ ≤
          ‖fderiv ℝ axialPlateauBump (P.axialBufferCoordinate n x)‖ *
            ‖pairBasis j‖ :=
        (fderiv ℝ axialPlateauBump
          (P.axialBufferCoordinate n x)).le_opNorm _
      _ ≤ (axialPlateauLipschitzConstant : ℝ) * ‖pairBasis j‖ :=
        mul_le_mul_of_nonneg_right
          (norm_fderiv_axialPlateau_le (P.axialBufferCoordinate n x))
          (norm_nonneg _)
      _ = (axialPlateauLipschitzConstant : ℝ) := by rw [hbasis, mul_one]
  calc
    ‖P.axialCellCutoffDerivative n j x‖ =
        (P.scaleFamily.bufferRadius n)⁻¹ *
          ‖fderiv ℝ axialPlateauBump (P.axialBufferCoordinate n x)
            (pairBasis j)‖ := by
      rw [axialCellCutoffDerivative, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg hRinv]
    _ ≤ (P.scaleFamily.bufferRadius n)⁻¹ *
        (axialPlateauLipschitzConstant : ℝ) :=
      mul_le_mul_of_nonneg_left happly hRinv
    _ = (axialPlateauLipschitzConstant : ℝ) /
        P.scaleFamily.bufferRadius n := by
      rw [div_eq_inv_mul]

/-- The real axial unit vector. -/
def axialUnitR3 : R3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

/-- The real axial unit vector `e₃` has components `δ_{i2}`. -/
@[simp] theorem axialUnitR3_apply (i : Fin 3) :
    axialUnitR3 i = if i = 2 then 1 else 0 := by
  simp [axialUnitR3]

/-- The axial unit vector `e₃` has norm one. -/
@[simp] theorem norm_axialUnitR3 : ‖axialUnitR3‖ = 1 := by
  simp [axialUnitR3]

/-- The Euclidean added axial velocity in cell `n`. -/
def axialOffsetEuclidean
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (x : ℝ × ℝ) : R3 :=
  (P.scaleFamily.axialAmplitude tau n * P.axialCellCutoff n x) • axialUnitR3

/-- Its displayed classical transverse coordinate derivatives. -/
def axialOffsetEuclideanDerivative
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (j : Fin 2) (x : ℝ × ℝ) : R3 :=
  (P.scaleFamily.axialAmplitude tau n *
    P.axialCellCutoffDerivative n j x) • axialUnitR3

/-- The Euclidean axial cell field `a_n ϑ((y - p_n)/R_n) e₃` is smooth. -/
theorem axialOffsetEuclidean_contDiff
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (P.axialOffsetEuclidean tau n) := by
  exact (ContDiff.const_smul (P.scaleFamily.axialAmplitude tau n)
    (P.axialCellCutoff_contDiff n)).smul_const axialUnitR3

/-- The Euclidean axial cell field is measurable, being continuous. -/
theorem axialOffsetEuclidean_measurable
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ) :
    Measurable (P.axialOffsetEuclidean tau n) :=
  (P.axialOffsetEuclidean_contDiff tau n).continuous.measurable

/-- The displayed transverse derivative of the Euclidean axial cell field is measurable, using
measurability of `x ↦ fderiv` applied to a fixed vector. -/
theorem axialOffsetEuclideanDerivative_measurable
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (j : Fin 2) : Measurable (P.axialOffsetEuclideanDerivative tau n j) := by
  have hmeas : Measurable
      (fun x : ℝ × ℝ ↦
        fderiv ℝ (P.axialCellCutoff n) x (pairBasis j)) :=
    measurable_fderiv_apply_const ℝ (P.axialCellCutoff n) (pairBasis j)
  have hcut : Measurable (P.axialCellCutoffDerivative n j) := by
    convert hmeas using 1
    funext x
    exact (P.fderiv_axialCellCutoff_apply_pairBasis n j x).symm
  exact (hcut.const_mul _).smul_const axialUnitR3

/-- The Fréchet derivative of the Euclidean axial cell field, evaluated on the `j`-th coordinate
basis vector, is the displayed field `axialOffsetEuclideanDerivative`, namely
`a_n (∂_j χ_n) e₃`. -/
theorem fderiv_axialOffsetEuclidean_apply_pairBasis
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (j : Fin 2) (x : ℝ × ℝ) :
    fderiv ℝ (P.axialOffsetEuclidean tau n) x (pairBasis j) =
      P.axialOffsetEuclideanDerivative tau n j x := by
  have hscalar := (P.axialCellCutoff_hasFDerivAt n x).const_mul
    (P.scaleFamily.axialAmplitude tau n)
  have hvector := hscalar.smul_const axialUnitR3
  change fderiv ℝ
      (fun y ↦ (P.scaleFamily.axialAmplitude tau n *
        P.axialCellCutoff n y) • axialUnitR3) x (pairBasis j) = _
  rw [hvector.fderiv]
  simp [axialOffsetEuclideanDerivative, axialCellCutoffDerivative]

/-- On the constant axial region `D(p_n, 3R_n/4)` — the EUCLIDEAN disc — the cell field equals
the constant `a_n e₃`, since the plateau is `1` there (`eq:axial-offset` and the paragraph after
it). -/
theorem axialOffsetEuclidean_eq_axialAmplitude_of_core
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4) :
    P.axialOffsetEuclidean tau n x =
      P.scaleFamily.axialAmplitude tau n • axialUnitR3 := by
  simp [axialOffsetEuclidean,
    P.axialCellCutoff_eq_one_of_dist_le_three_quarters n hx]

/-- The Euclidean axial cell field vanishes off the open buffer disc `D(p_n, R_n)`. -/
theorem axialOffsetEuclidean_eq_zero_of_not_mem_bufferDisk
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    {x : ℝ × ℝ} (hx : x ∉ P.scaleFamily.bufferDisk n) :
    P.axialOffsetEuclidean tau n x = 0 := by
  simp [axialOffsetEuclidean,
    P.axialCellCutoff_eq_zero_of_not_mem_bufferDisk n hx]

/-- The displayed derivative of the Euclidean axial cell field vanishes off the open buffer
disc. -/
theorem axialOffsetEuclideanDerivative_eq_zero_of_not_mem_bufferDisk
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (j : Fin 2) {x : ℝ × ℝ} (hx : x ∉ P.scaleFamily.bufferDisk n) :
    P.axialOffsetEuclideanDerivative tau n j x = 0 := by
  simp [axialOffsetEuclideanDerivative,
    P.axialCellCutoffDerivative_eq_zero_of_not_mem_bufferDisk n j hx]

/-- Pointwise real value bound, in the paper amplitude scale. -/
theorem norm_axialOffsetEuclidean_le
    (P : TorusCellPlacement (r := r) supportRadius) {tau : ℝ} (htau : 0 ≤ tau)
    (n : ℕ) (x : ℝ × ℝ) :
    ‖P.axialOffsetEuclidean tau n x‖ ≤
      P.scaleFamily.axialAmplitude tau n := by
  have ha : 0 ≤ P.scaleFamily.axialAmplitude tau n := by
    unfold ScaleFamily.axialAmplitude
    exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
      (P.scaleFamily.ell_pos n).le
  have hcut := (P.axialCellCutoff_mem_Icc n x).2
  simp only [axialOffsetEuclidean, norm_smul, norm_axialUnitR3, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha
      (P.axialCellCutoff_mem_Icc n x).1)]
  nlinarith

/-- Each coordinate derivative has the expected `aₙ/Rₙ` scale. -/
theorem norm_axialOffsetEuclideanDerivative_le
    (P : TorusCellPlacement (r := r) supportRadius) {tau : ℝ} (htau : 0 ≤ tau)
    (n : ℕ) (j : Fin 2) (x : ℝ × ℝ) :
    ‖P.axialOffsetEuclideanDerivative tau n j x‖ ≤
      (axialPlateauLipschitzConstant : ℝ) *
        P.scaleFamily.axialGradientScale tau n := by
  have ha : 0 ≤ P.scaleFamily.axialAmplitude tau n := by
    unfold ScaleFamily.axialAmplitude
    exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
      (P.scaleFamily.ell_pos n).le
  calc
    ‖P.axialOffsetEuclideanDerivative tau n j x‖ =
        P.scaleFamily.axialAmplitude tau n *
          ‖P.axialCellCutoffDerivative n j x‖ := by
      simp [axialOffsetEuclideanDerivative, norm_smul, norm_axialUnitR3,
        Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ P.scaleFamily.axialAmplitude tau n *
        ((axialPlateauLipschitzConstant : ℝ) /
          P.scaleFamily.bufferRadius n) :=
      mul_le_mul_of_nonneg_left
        (P.norm_axialCellCutoffDerivative_le n j x) ha
    _ = (axialPlateauLipschitzConstant : ℝ) *
        P.scaleFamily.axialGradientScale tau n := by
      unfold ScaleFamily.axialGradientScale
      ring

/-- The field is purely axial, so its two transverse divergence components
vanish pointwise. -/
theorem axialOffsetEuclideanDerivative_transverseDivergence
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (x : ℝ × ℝ) :
    P.axialOffsetEuclideanDerivative tau n 0 x 0 +
      P.axialOffsetEuclideanDerivative tau n 1 x 1 = 0 := by
  simp [axialOffsetEuclideanDerivative, axialUnitR3]

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
