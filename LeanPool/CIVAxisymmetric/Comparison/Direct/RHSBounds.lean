/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Direct.AnchorFubini
public import LeanPool.CIVAxisymmetric.Comparison.Commutator
public import LeanPool.CIVAxisymmetric.Comparison.CommutatorL2SqCongr

/-!
# Uniform bounds for the right side of the mollified equation

At a time `s` at which the slice `q(·, s)` is measurable and essentially bounded by `Mq`, and the
drift slice is bounded and Lipschitz with constant `Λ` with divergence bounded by `Λ`, each term
of the right side of `eq:aniso:comparison:mollified` is bounded uniformly in `x`, with a constant
depending only on `m`, `d`, `ε`, `Λ` and `Mq`. The bound on the commutator is the one stated after
`eq:aniso:comparison:mollified`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

/-- Convolution of an essentially bounded function against a kernel dominated by an integrable
majorant. -/
theorem abs_integral_kernel_sub_mul_le {k K g : Vec m → ℝ} {M : ℝ} (hK : Integrable K volume)
    (hkK : ∀ w, |k w| ≤ K w) (hg : ∀ᵐ y ∂volume, |g y| ≤ M) (x : Vec m) :
    |∫ y, k (x - y) * g y| ≤ M * (∫ w, K w) := by
  have hKx : Integrable (fun y => K (x - y) * M) volume := (hK.comp_sub_left x).mul_const M
  have hle : ∀ᵐ y ∂volume, |k (x - y) * g y| ≤ K (x - y) * M := by
    filter_upwards [hg] with y hy
    rw [abs_mul]
    have hK0 : 0 ≤ K (x - y) := le_trans (abs_nonneg _) (hkK (x - y))
    calc |k (x - y)| * |g y| ≤ K (x - y) * |g y| :=
          mul_le_mul_of_nonneg_right (hkK (x - y)) (abs_nonneg _)
      _ ≤ K (x - y) * M := mul_le_mul_of_nonneg_left hy hK0
  have hint : ∫ y, |k (x - y) * g y| ≤ ∫ y, K (x - y) * M :=
    integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hKx hle
  have hconst : ∫ y, K (x - y) * M = M * ∫ w, K w := by
    rw [integral_mul_const, integral_sub_left_eq_self, mul_comm]
  calc |∫ y, k (x - y) * g y| ≤ ∫ y, |k (x - y) * g y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, K (x - y) * M := hint
    _ = M * ∫ w, K w := hconst

theorem abs_partialLaplacian_mollifySlice_le (d : ℕ) {ε : ℝ} (hε : 0 < ε) {q : Vec m × ℝ → ℝ}
    {τ M : ℝ} (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) (x : Vec m) :
    |partialLaplacian m d (mollifySlice m ε q) (x, τ)|
      ≤ M * (∫ w, |partialLaplacianKernel m d ε w|) := by
  rw [partialLaplacian_mollifySlice d hε q τ M hmeas hbdd x]
  exact abs_integral_kernel_sub_mul_le
    ((continuous_partialLaplacianKernel m d ε).integrable_of_hasCompactSupport
      (hasCompactSupport_partialLaplacianKernel d hε)).abs
    (fun w => le_refl _) hbdd x

theorem abs_fderiv_mollifierKernel_apply_le (ε : ℝ) (w v : Vec m) :
    |fderiv ℝ (mollifierKernel m ε) w v|
      ≤ ‖v‖ * ∑ i, |fderiv ℝ (mollifierKernel m ε) w (basisVec i)| := by
  rw [apply_eq_sum_basisVec, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hvi : |v i| ≤ ‖v‖ := by
    have h := norm_le_pi_norm v i
    rwa [Real.norm_eq_abs] at h
  exact mul_le_mul_of_nonneg_right hvi (abs_nonneg _)

theorem abs_gradPair_mollifySlice_le {ε : ℝ} (hε : 0 < ε) {q : Vec m × ℝ → ℝ}
    {τ M : ℝ} (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) (x v : Vec m) :
    |gradPair m (mollifySlice m ε q) (x, τ) v| ≤ M * (‖v‖ * (mollifierGradConst m / ε)) := by
  rw [gradPair_mollifySlice hε q τ M hmeas hbdd x v, ← integral_sum_abs_fderiv_mollifierKernel hε,
    ← integral_const_mul]
  exact abs_integral_kernel_sub_mul_le
    ((integrable_sum_abs_fderiv_mollifierKernel hε).const_mul ‖v‖)
    (fun w => abs_fderiv_mollifierKernel_apply_le ε w v) hbdd x

/-- The commutator bound `|R_ε| ≤ C(m, η) Λ M` of `eq:aniso:comparison:mollified`, for a
transported function bounded only almost everywhere. -/
theorem abs_diPernaLionsCommutator_le_of_ae {ε M : ℝ} {Λ : NNReal} (hε : 0 < ε) (hM : 0 ≤ M)
    {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hg : ∀ᵐ y ∂volume, |g y| ≤ M) (hgm : AEStronglyMeasurable g volume) (x : Vec m) :
    |diPernaLionsCommutator m ε b divb g x| ≤ Λ * M * (mollifierGradConst m + 1) := by
  set g' : Vec m → ℝ := fun y => max (-M) (min M (g y)) with hg'def
  have hclamp : Continuous fun t : ℝ => max (-M) (min M t) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hg'm : AEStronglyMeasurable g' volume := hclamp.comp_aestronglyMeasurable hgm
  have hg'b : ∀ y, |g' y| ≤ M := by
    intro y
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith only [hM]) (min_le_left _ _)
  have hgg' : g =ᵐ[volume] g' := by
    filter_upwards [hg] with y hy
    rw [abs_le] at hy
    simp only [hg'def]
    rw [min_eq_right hy.2, max_eq_right hy.1]
  rw [diPernaLionsCommutator_congr_ae_slice hgg' x]
  exact abs_diPernaLionsCommutator_le hε hM hlip hdivb hdivbm hg'b hg'm x

/-- The constant bounding the right side of the mollified equation at a good time. -/
@[expose] def mollifiedRHSBound (m d : ℕ) (ε Λ Mq : ℝ) : ℝ :=
  Mq * (∫ w, |partialLaplacianKernel m d ε w|) + Mq * (Λ * (mollifierGradConst m / ε))
    + Λ * Mq * (mollifierGradConst m + 1)

theorem abs_mollifiedRHS_le (d : ℕ) {ε Mq : ℝ} {Λ : NNReal} (hε : 0 < ε) (hMq : 0 ≤ Mq)
    {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ} {s : ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, s)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, s)| ≤ Mq)
    (hBb : ∀ x, ‖B (x, s)‖ ≤ Λ) (hBlip : LipschitzWith Λ (fun x => B (x, s)))
    (hdiv : ∀ x, |divB (x, s)| ≤ Λ) (hdivm : AEStronglyMeasurable (fun x => divB (x, s)) volume)
    (x : Vec m) :
    |mollifiedRHS m d ε B divB q x s| ≤ mollifiedRHSBound m d ε Λ Mq := by
  unfold mollifiedRHS mollifiedRHSBound
  have h1 := abs_partialLaplacian_mollifySlice_le d hε hmeas hbdd x
  have h2 := abs_gradPair_mollifySlice_le hε hmeas hbdd x (B (x, s))
  have h3 := abs_diPernaLionsCommutator_le_of_ae (m := m) hε hMq hBlip hdiv hdivm hbdd hmeas x
  have hG : 0 ≤ mollifierGradConst m / ε := div_nonneg mollifierGradConst_nonneg hε.le
  have h2' : Mq * (‖B (x, s)‖ * (mollifierGradConst m / ε))
      ≤ Mq * ((Λ : ℝ) * (mollifierGradConst m / ε)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hBb x) hG) hMq
  have htri := abs_add_le (partialLaplacian m d (mollifySlice m ε q) (x, s)
    - gradPair m (mollifySlice m ε q) (x, s) (B (x, s)))
    (diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
      (fun y => q (y, s)) x)
  have htri2 := abs_sub (partialLaplacian m d (mollifySlice m ε q) (x, s))
    (gradPair m (mollifySlice m ε q) (x, s) (B (x, s)))
  linarith only [h1, h2, h3, h2', htri, htri2]

end CIV
