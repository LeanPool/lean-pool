/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseWeightedLeibniz
public import LeanPool.FastDynamo.Global.BackgroundMultiplierScalarAlgebra
public import LeanPool.FastDynamo.Global.TorusAxialVelocityWeakTransfer

/-!
# One placed cell of the background multiplier

`eq:background-multiplier` (in the proof of `prop:background-resolvent`) sets

`s_n = Σ_m r_m ϑ(|y - p_m|/R_m)`,  `β_n = F(s_n)`,  `F(s) = (s-1)/(1+s)²`.

Because the summands of `s_n` have pairwise disjoint supports, `β_n` is **not** built by a
`W^{1,∞}` chain rule (which the transverse Fourier-graph model does not support) but as the
placed disjoint-support series

`β_n + 1 = Σ_m (F(r_m ϑ_m) + 1)`,

whose `m`-th summand `Ψ_{r_m} ∘ ϑ_m` is a smooth compactly supported function on the
Euclidean chart, with `Ψ_ρ(0) = 0`.  This module constructs that single summand, descends it to
the transverse torus through the placed-chart machinery of `Global/TorusChartWeakTransfer.lean`,
and proves that the displayed derivative is the periodic Fourier weak derivative, by
whole-plane integration by parts against a Fourier monomial — the same route as
`Global/TorusAxialVelocityWeakTransfer.lean`, whose cut-off `ϑ_m` is reused unchanged.

The series and the multiplier `β_n` itself are assembled in
`Global/TorusBackgroundMultiplier.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped BigOperators ENNReal Topology

/-! ## The scalar cell profile `Ψ_ρ(t) = F(ρ t) + 1` -/

/-- `Ψ_ρ(t) = F(ρt) + 1`, the summand profile of the placed series
`β_n + 1 = Σ_m (F(r_m ϑ_m) + 1)` (`eq:background-multiplier`).
It vanishes at `t = 0`, which is exactly what makes the
series a disjoint-support series. -/
def backgroundCellProfile (ρ t : ℝ) : ℝ := backgroundMultiplierF (ρ * t) + 1

/-- The derivative of `Ψ_ρ`, namely `F'(ρt)ρ`. -/
def backgroundCellProfileDeriv (ρ t : ℝ) : ℝ := backgroundMultiplierDeriv (ρ * t) * ρ

/-- `Ψ_ρ(0) = F(0) + 1 = 0`. -/
@[simp] theorem backgroundCellProfile_zero (ρ : ℝ) : backgroundCellProfile ρ 0 = 0 := by
  simp [backgroundCellProfile, backgroundMultiplierF]

/-- `Ψ_ρ(t) - 1 = F(ρ t)`: the series reconstructs `β_n` after subtracting the constant one. -/
theorem backgroundCellProfile_sub_one (ρ t : ℝ) :
    backgroundCellProfile ρ t - 1 = backgroundMultiplierF (ρ * t) := by
  rw [backgroundCellProfile]
  ring

/-- `Ψ_ρ` is differentiable wherever `ρ t ≠ -1`, with derivative `F'(ρt)ρ`. -/
theorem hasDerivAt_backgroundCellProfile {ρ t : ℝ} (hs : 1 + ρ * t ≠ 0) :
    HasDerivAt (backgroundCellProfile ρ) (backgroundCellProfileDeriv ρ t) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ ρ * s) ρ t := by
    simpa using (hasDerivAt_id t).const_mul ρ
  have hcomp := (hasDerivAt_backgroundMultiplierF hs).comp t hinner
  exact hcomp.add_const 1

/-- The shifted profile is nonnegative on `[0, ∞)`: `Ψ_ρ(t) = (ρt)(3 + ρt)/(1 + ρt)²`. -/
theorem backgroundCellProfile_nonneg {ρ t : ℝ} (hs : 0 ≤ ρ * t) :
    0 ≤ backgroundCellProfile ρ t := by
  have h1 : (0 : ℝ) < (1 + ρ * t) ^ 2 := by positivity
  rw [backgroundCellProfile, backgroundMultiplierF]
  rw [div_add' _ _ _ (ne_of_gt h1), le_div_iff₀ h1]
  nlinarith [hs, sq_nonneg (ρ * t)]

/-- `Ψ_ρ(t) ≤ 3ρt` for `ρt ≥ 0`, since `(3 + s)/(1 + s)² ≤ 3`. -/
theorem backgroundCellProfile_le_three_mul {ρ t : ℝ} (hs : 0 ≤ ρ * t) :
    backgroundCellProfile ρ t ≤ 3 * (ρ * t) := by
  have h1 : (0 : ℝ) < (1 + ρ * t) ^ 2 := by positivity
  rw [backgroundCellProfile, backgroundMultiplierF]
  rw [div_add' _ _ _ (ne_of_gt h1), div_le_iff₀ h1]
  nlinarith [hs, sq_nonneg (ρ * t), mul_nonneg hs hs]

/-- `|Ψ_ρ(t)| ≤ 3ρ` for `t ∈ [0,1]` and `ρ ≥ 0`.  This is what makes the placed series
absolutely convergent in `L∞`: the `m`-th summand has size `3 r_m = 3ℓ_m/ℓ_n`. -/
theorem abs_backgroundCellProfile_le {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |backgroundCellProfile ρ t| ≤ 3 * ρ := by
  have hs : 0 ≤ ρ * t := mul_nonneg hρ ht0
  have hlow := backgroundCellProfile_nonneg hs
  have hhigh := backgroundCellProfile_le_three_mul hs
  have hmul : ρ * t ≤ ρ := by nlinarith
  rw [abs_of_nonneg hlow]
  nlinarith

/-- `|Ψ'_ρ(t)| ≤ 3ρ`, from the sharp bound `|F'| ≤ 3` on `[0, ∞)`. -/
theorem abs_backgroundCellProfileDeriv_le {ρ t : ℝ} (hρ : 0 ≤ ρ)
    (ht0 : 0 ≤ t) : |backgroundCellProfileDeriv ρ t| ≤ 3 * ρ := by
  have hs : 0 ≤ ρ * t := mul_nonneg hρ ht0
  rw [backgroundCellProfileDeriv, abs_mul, abs_of_nonneg hρ]
  have h := abs_backgroundMultiplierDeriv_le_three hs
  nlinarith [abs_nonneg (backgroundMultiplierDeriv (ρ * t))]

namespace ScaleFamily.TorusCellPlacement

open EuclideanCellSourceCertificate

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}
variable (P : TorusCellPlacement (r := r) supportRadius)

/-! ## The placed Euclidean summand `Ψ_ρ ∘ ϑ_m` -/

/-- One placed summand `Ψ_ρ(ϑ_m)` of `β_n + 1` on the Euclidean chart.  The cut-off `ϑ_m` is
exactly the one of `eq:axial-offset`. -/
def backgroundCellEuclidean (ρ : ℝ) (m : ℕ) (y : ℝ × ℝ) : ℝ :=
  backgroundCellProfile ρ (P.axialCellCutoff m y)

/-- Its displayed coordinate derivative `Ψ'_ρ(ϑ_m) ∂_j ϑ_m`. -/
def backgroundCellEuclideanDeriv (ρ : ℝ) (m : ℕ) (j : Fin 2) (y : ℝ × ℝ) : ℝ :=
  backgroundCellProfileDeriv ρ (P.axialCellCutoff m y) *
    P.axialCellCutoffDerivative m j y

/-- The profile argument stays in `[0, 1]`, so `1 + ρ ϑ_m ≥ 1` and `Ψ_ρ` is differentiable
there. -/
theorem one_add_mul_axialCellCutoff_ne_zero {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (y : ℝ × ℝ) : 1 + ρ * P.axialCellCutoff m y ≠ 0 := by
  have h0 := (P.axialCellCutoff_mem_Icc m y).1
  have : 0 ≤ ρ * P.axialCellCutoff m y := mul_nonneg hρ h0
  linarith

/-- The placed summand is Fréchet differentiable, by the classical chain rule on the chart. -/
theorem backgroundCellEuclidean_hasFDerivAt {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (y : ℝ × ℝ) :
    HasFDerivAt (P.backgroundCellEuclidean ρ m)
      (backgroundCellProfileDeriv ρ (P.axialCellCutoff m y) •
        ((fderiv ℝ axialPlateauBump (P.axialBufferCoordinate m y)).comp
          ((P.scaleFamily.bufferRadius m)⁻¹ •
            ContinuousLinearMap.id ℝ (ℝ × ℝ)))) y :=
  (hasDerivAt_backgroundCellProfile
      (P.one_add_mul_axialCellCutoff_ne_zero hρ m y)).comp_hasFDerivAt y
    (P.axialCellCutoff_hasFDerivAt m y)

/-- The placed summand is differentiable, hence continuous. -/
theorem backgroundCellEuclidean_differentiable {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    Differentiable ℝ (P.backgroundCellEuclidean ρ m) := fun y ↦
  (P.backgroundCellEuclidean_hasFDerivAt hρ m y).differentiableAt

/-- Evaluating the derivative of the placed summand on a coordinate basis vector returns the
displayed field. -/
theorem fderiv_backgroundCellEuclidean_apply_pairBasis {ρ : ℝ} (hρ : 0 ≤ ρ)
    (m : ℕ) (j : Fin 2) (y : ℝ × ℝ) :
    fderiv ℝ (P.backgroundCellEuclidean ρ m) y (pairBasis j) =
      P.backgroundCellEuclideanDeriv ρ m j y := by
  rw [(P.backgroundCellEuclidean_hasFDerivAt hρ m y).fderiv]
  rw [backgroundCellEuclideanDeriv, ← P.fderiv_axialCellCutoff_apply_pairBasis m j y,
    (P.axialCellCutoff_hasFDerivAt m y).fderiv]
  rfl

/-- The placed summand vanishes off the placed buffer disc, since `ϑ_m` does there and
`Ψ_ρ(0) = 0`. -/
theorem backgroundCellEuclidean_eq_zero_of_not_mem_bufferDisk (ρ : ℝ) (m : ℕ)
    {y : ℝ × ℝ} (hy : y ∉ P.scaleFamily.bufferDisk m) :
    P.backgroundCellEuclidean ρ m y = 0 := by
  rw [backgroundCellEuclidean, P.axialCellCutoff_eq_zero_of_not_mem_bufferDisk m hy,
    backgroundCellProfile_zero]

/-- The displayed derivative vanishes off the placed buffer disc. -/
theorem backgroundCellEuclideanDeriv_eq_zero_of_not_mem_bufferDisk (ρ : ℝ)
    (m : ℕ) (j : Fin 2) {y : ℝ × ℝ} (hy : y ∉ P.scaleFamily.bufferDisk m) :
    P.backgroundCellEuclideanDeriv ρ m j y = 0 := by
  rw [backgroundCellEuclideanDeriv,
    P.axialCellCutoffDerivative_eq_zero_of_not_mem_bufferDisk m j hy, mul_zero]

/-- The placed summand is measurable, being continuous. -/
theorem backgroundCellEuclidean_measurable {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    Measurable (P.backgroundCellEuclidean ρ m) :=
  (P.backgroundCellEuclidean_differentiable hρ m).continuous.measurable

/-- The displayed derivative is measurable: `F'` is a rational function and `x ↦ ∂_j ϑ_m` is
measurable by `measurable_fderiv_apply_const`. -/
theorem backgroundCellEuclideanDeriv_measurable (ρ : ℝ) (m : ℕ) (j : Fin 2) :
    Measurable (P.backgroundCellEuclideanDeriv ρ m j) := by
  have hcut : Measurable (P.axialCellCutoff m) :=
    (P.axialCellCutoff_contDiff m).continuous.measurable
  have hderivMeas : Measurable backgroundMultiplierDeriv := by
    unfold backgroundMultiplierDeriv
    fun_prop
  have hcutDeriv : Measurable (P.axialCellCutoffDerivative m j) := by
    have hmeas : Measurable
        (fun y : ℝ × ℝ ↦ fderiv ℝ (P.axialCellCutoff m) y (pairBasis j)) :=
      measurable_fderiv_apply_const ℝ (P.axialCellCutoff m) (pairBasis j)
    convert hmeas using 1
    funext y
    exact (P.fderiv_axialCellCutoff_apply_pairBasis m j y).symm
  exact ((hderivMeas.comp (hcut.const_mul ρ)).mul_const ρ).mul hcutDeriv

/-- Uniform bound `|Ψ_ρ(ϑ_m)| ≤ 3ρ` on the placed summand. -/
theorem abs_backgroundCellEuclidean_le {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (y : ℝ × ℝ) : |P.backgroundCellEuclidean ρ m y| ≤ 3 * ρ :=
  abs_backgroundCellProfile_le hρ (P.axialCellCutoff_mem_Icc m y).1
    (P.axialCellCutoff_mem_Icc m y).2

/-- Uniform bound `|∂_j (Ψ_ρ ∘ ϑ_m)| ≤ 3ρ ‖ϑ'‖_∞ / R_m` on the displayed derivative.  This is
the source of the gradient half of `eq:background-multiplier-bounds`,
because `r_m/R_m = (ℓ_m/R_m)/ℓ_n ≤ d(K₀)/ℓ_n`. -/
theorem abs_backgroundCellEuclideanDeriv_le {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (j : Fin 2) (y : ℝ × ℝ) :
    |P.backgroundCellEuclideanDeriv ρ m j y| ≤
      3 * ρ * ((axialPlateauLipschitzConstant : ℝ) /
        P.scaleFamily.bufferRadius m) := by
  rw [backgroundCellEuclideanDeriv, abs_mul]
  have h1 := abs_backgroundCellProfileDeriv_le hρ (P.axialCellCutoff_mem_Icc m y).1
  have h2 := P.norm_axialCellCutoffDerivative_le m j y
  have h3 : (0 : ℝ) ≤ (axialPlateauLipschitzConstant : ℝ) /
      P.scaleFamily.bufferRadius m :=
    div_nonneg (NNReal.coe_nonneg _) (P.scaleFamily.bufferRadius_pos m).le
  have h4 : 0 ≤ |backgroundCellProfileDeriv ρ (P.axialCellCutoff m y)| := abs_nonneg _
  have h5 : 0 ≤ |P.axialCellCutoffDerivative m j y| := abs_nonneg _
  rw [Real.norm_eq_abs] at h2
  nlinarith [h1, h2, h3, h4, h5, hρ]

/-! ## Descent to the transverse torus -/

/-- The complexified placed summand on the chart. -/
def backgroundCellEuclideanC (ρ : ℝ) (m : ℕ) (y : ℝ × ℝ) : ℂ :=
  ((P.backgroundCellEuclidean ρ m y : ℝ) : ℂ)

/-- The complexified displayed derivative on the chart. -/
def backgroundCellEuclideanDerivC (ρ : ℝ) (m : ℕ) (j : Fin 2) (y : ℝ × ℝ) : ℂ :=
  ((P.backgroundCellEuclideanDeriv ρ m j y : ℝ) : ℂ)

/-- The descended placed summand on the transverse torus. -/
def backgroundCellTorus (ρ : ℝ) (m : ℕ) : TransverseTorus → ℂ :=
  P.torusPeriodizedExtension m (P.backgroundCellEuclideanC ρ m)

/-- The descended displayed derivative on the transverse torus. -/
def backgroundCellTorusDeriv (ρ : ℝ) (m : ℕ) (j : Fin 2) : TransverseTorus → ℂ :=
  P.torusPeriodizedExtension m (P.backgroundCellEuclideanDerivC ρ m j)

/-- The descended summand is measurable. -/
theorem measurable_backgroundCellTorus {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    Measurable (P.backgroundCellTorus ρ m) :=
  P.measurable_torusPeriodizedExtension m _
    (Complex.measurable_ofReal.comp (P.backgroundCellEuclidean_measurable hρ m))

/-- The descended derivative is measurable. -/
theorem measurable_backgroundCellTorusDeriv (ρ : ℝ) (m : ℕ) (j : Fin 2) :
    Measurable (P.backgroundCellTorusDeriv ρ m j) :=
  P.measurable_torusPeriodizedExtension m _
    (Complex.measurable_ofReal.comp (P.backgroundCellEuclideanDeriv_measurable ρ m j))

/-- The descended summand vanishes off its placed torus buffer. -/
theorem backgroundCellTorus_eq_zero_of_not_mem_buffer (ρ : ℝ) (m : ℕ)
    {q : TransverseTorus} (hq : q ∉ P.torusBufferDisk m) :
    P.backgroundCellTorus ρ m q = 0 :=
  P.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk m _ hq

/-- The descended derivative vanishes off its placed torus buffer. -/
theorem backgroundCellTorusDeriv_eq_zero_of_not_mem_buffer (ρ : ℝ) (m : ℕ)
    (j : Fin 2) {q : TransverseTorus} (hq : q ∉ P.torusBufferDisk m) :
    P.backgroundCellTorusDeriv ρ m j q = 0 :=
  P.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk m _ hq

/-- Uniform bound on the descended summand. -/
theorem norm_backgroundCellTorus_le {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (q : TransverseTorus) : ‖P.backgroundCellTorus ρ m q‖ ≤ 3 * ρ := by
  classical
  rw [backgroundCellTorus, torusPeriodizedExtension]
  by_cases hq : q ∈ P.torusBufferDisk m
  · rw [dite_eq_left hq, backgroundCellEuclideanC, Complex.norm_real, Real.norm_eq_abs]
    exact P.abs_backgroundCellEuclidean_le hρ m _
  · rw [dite_eq_right hq, norm_zero]
    positivity

/-- Uniform bound on the descended derivative. -/
theorem norm_backgroundCellTorusDeriv_le {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (j : Fin 2) (q : TransverseTorus) :
    ‖P.backgroundCellTorusDeriv ρ m j q‖ ≤
      3 * ρ * ((axialPlateauLipschitzConstant : ℝ) /
        P.scaleFamily.bufferRadius m) := by
  classical
  rw [backgroundCellTorusDeriv, torusPeriodizedExtension]
  by_cases hq : q ∈ P.torusBufferDisk m
  · rw [dite_eq_left hq, backgroundCellEuclideanDerivC, Complex.norm_real,
      Real.norm_eq_abs]
    exact P.abs_backgroundCellEuclideanDeriv_le hρ m j _
  · rw [dite_eq_right hq, norm_zero]
    have h3 : (0 : ℝ) ≤ (axialPlateauLipschitzConstant : ℝ) /
        P.scaleFamily.bufferRadius m :=
      div_nonneg (NNReal.coe_nonneg _) (P.scaleFamily.bufferRadius_pos m).le
    positivity

/-- The descended summand is pointwise real. -/
theorem backgroundCellTorus_im (ρ : ℝ) (m : ℕ) (q : TransverseTorus) :
    (P.backgroundCellTorus ρ m q).im = 0 := by
  classical
  rw [backgroundCellTorus, torusPeriodizedExtension]
  by_cases hq : q ∈ P.torusBufferDisk m
  · rw [dite_eq_left hq]
    simp [backgroundCellEuclideanC]
  · rw [dite_eq_right hq]
    simp

/-- At a torus point with a representative inside the plateau of cell `m`, the descended
summand takes the constant value `Ψ_ρ(1) = F(ρ) + 1`.  This is what gives `β_n = F(r_m)` on the
core of a nonselected cell (the identity `s_n = r_m` on `supp u_m^loc` in the estimate of `I₂`
in the proof of `prop:background-resolvent`). -/
theorem backgroundCellTorus_eq_of_core (ρ : ℝ) (m : ℕ) {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.backgroundCellTorus ρ m (transverseTorusPoint x) =
      ((backgroundCellProfile ρ 1 : ℝ) : ℂ) := by
  have hbuffer : x ∈ P.scaleFamily.bufferDisk m := by
    have hR := P.scaleFamily.bufferRadius_pos m
    have hd := dist_le_pairEuclideanDist x (P.scaleFamily.cellCenter m)
    simp only [ScaleFamily.bufferDisk, Metric.mem_ball]
    linarith
  change P.periodizedExtension m (P.backgroundCellEuclideanC ρ m) x = _
  rw [P.periodizedExtension_eq_source m (P.backgroundCellEuclideanC ρ m) hbuffer,
    backgroundCellEuclideanC, backgroundCellEuclidean,
    P.axialCellCutoff_eq_one_of_dist_le_three_quarters m hx]

/-- At a torus point represented inside the half-open unit box the descended summand agrees
with the Euclidean summand at that representative. -/
theorem backgroundCellTorus_transverseTorusPoint_eq_euclidean_of_mem_Ioc
    (ρ : ℝ) (m : ℕ) {x : ℝ × ℝ}
    (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    P.backgroundCellTorus ρ m (transverseTorusPoint x) =
      P.backgroundCellEuclideanC ρ m x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hbuffer_iff : transverseTorusPoint x ∈ P.torusBufferDisk m ↔
      x ∈ P.scaleFamily.bufferDisk m := by
    rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative m, hrep]
  by_cases hx : x ∈ P.scaleFamily.bufferDisk m
  · change P.periodizedExtension m (P.backgroundCellEuclideanC ρ m) x = _
    exact P.periodizedExtension_eq_source m _ hx
  · have hq : transverseTorusPoint x ∉ P.torusBufferDisk m :=
      hbuffer_iff.not.mpr hx
    rw [P.backgroundCellTorus_eq_zero_of_not_mem_buffer ρ m hq,
      backgroundCellEuclideanC,
      P.backgroundCellEuclidean_eq_zero_of_not_mem_bufferDisk ρ m hx]
    simp

/-- The same statement for the displayed derivative. -/
theorem backgroundCellTorusDeriv_transverseTorusPoint_eq_euclidean_of_mem_Ioc
    (ρ : ℝ) (m : ℕ) (j : Fin 2) {x : ℝ × ℝ}
    (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    P.backgroundCellTorusDeriv ρ m j (transverseTorusPoint x) =
      P.backgroundCellEuclideanDerivC ρ m j x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hbuffer_iff : transverseTorusPoint x ∈ P.torusBufferDisk m ↔
      x ∈ P.scaleFamily.bufferDisk m := by
    rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative m, hrep]
  by_cases hx : x ∈ P.scaleFamily.bufferDisk m
  · change P.periodizedExtension m (P.backgroundCellEuclideanDerivC ρ m j) x = _
    exact P.periodizedExtension_eq_source m _ hx
  · have hq : transverseTorusPoint x ∉ P.torusBufferDisk m :=
      hbuffer_iff.not.mpr hx
    rw [P.backgroundCellTorusDeriv_eq_zero_of_not_mem_buffer ρ m j hq,
      backgroundCellEuclideanDerivC,
      P.backgroundCellEuclideanDeriv_eq_zero_of_not_mem_bufferDisk ρ m j hx]
    simp

/-! ## The Fourier weak derivative of one placed summand -/

/-- The placed summand read on the coordinate plane `Fin 2 → ℝ`. -/
def backgroundCellSourceCoord (ρ : ℝ) (m : ℕ) (x : Fin 2 → ℝ) : ℂ :=
  P.backgroundCellEuclideanC ρ m (finTwoToPair x)

/-- The displayed derivative read on the coordinate plane `Fin 2 → ℝ`. -/
def backgroundCellDerivCoord (ρ : ℝ) (m : ℕ) (j : Fin 2) (x : Fin 2 → ℝ) : ℂ :=
  P.backgroundCellEuclideanDerivC ρ m j (finTwoToPair x)

/-- The displayed derivative is the line derivative of the placed summand. -/
theorem backgroundCellSourceCoord_hasLineDerivAt {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (j : Fin 2) (x : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (P.backgroundCellSourceCoord ρ m)
      (P.backgroundCellDerivCoord ρ m j x) x (Pi.single j (1 : ℝ)) := by
  have hsource := ((P.backgroundCellEuclidean_differentiable hρ m)
    (finTwoToPair x)).hasFDerivAt.comp x finTwoToPair.hasFDerivAt
  have hcoord := Complex.ofRealCLM.hasFDerivAt.comp x hsource
  have hline := hcoord.hasLineDerivAt (Pi.single j (1 : ℝ))
  have hfun : P.backgroundCellSourceCoord ρ m =
      Complex.ofRealCLM ∘ P.backgroundCellEuclidean ρ m ∘ finTwoToPair := by
    funext y
    rfl
  rw [hfun]
  apply hline.congr_deriv
  change ((fderiv ℝ (P.backgroundCellEuclidean ρ m) (finTwoToPair x)
      (finTwoToPair (Pi.single j (1 : ℝ))) : ℝ) : ℂ) = _
  rw [finTwoToPair_single, P.fderiv_backgroundCellEuclidean_apply_pairBasis hρ m j]
  rfl

/-- The placed summand read on the coordinate plane is continuous. -/
theorem continuous_backgroundCellSourceCoord {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    Continuous (P.backgroundCellSourceCoord ρ m) :=
  Complex.continuous_ofReal.comp
    ((P.backgroundCellEuclidean_differentiable hρ m).continuous.comp
      finTwoToPair.continuous)

/-- The displayed derivative read on the coordinate plane is measurable. -/
theorem measurable_backgroundCellDerivCoord (ρ : ℝ) (m : ℕ) (j : Fin 2) :
    Measurable (P.backgroundCellDerivCoord ρ m j) :=
  Complex.measurable_ofReal.comp
    ((P.backgroundCellEuclideanDeriv_measurable ρ m j).comp
      finTwoToPair.measurable)

/-- The placed summand is supported in the canonical half-open fundamental box, because the
whole placed buffer lies in the placement chart. -/
theorem support_backgroundCellSourceCoord_subset_iocFundamentalBox (ρ : ℝ) (m : ℕ) :
    Function.support (P.backgroundCellSourceCoord ρ m) ⊆ iocFundamentalBox := by
  intro x hx
  have hbuffer : finTwoToPair x ∈ P.scaleFamily.bufferDisk m := by
    by_contra hnot
    apply hx
    rw [backgroundCellSourceCoord, backgroundCellEuclideanC,
      P.backgroundCellEuclidean_eq_zero_of_not_mem_bufferDisk ρ m hnot]
    simp
  have hchart := P.bufferDisk_subset_chart m hbuffer
  rw [ScaleFamily.placementChart, Set.mem_prod, finTwoToPair_apply] at hchart
  intro k
  fin_cases k
  · change x 0 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨hchart.1.1, by linarith [hchart.1.2]⟩
  · change x 1 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨by linarith [hchart.2.1], by linarith [hchart.2.2]⟩

/-- The displayed derivative has the same support. -/
theorem support_backgroundCellDerivCoord_subset_iocFundamentalBox
    (ρ : ℝ) (m : ℕ) (j : Fin 2) :
    Function.support (P.backgroundCellDerivCoord ρ m j) ⊆ iocFundamentalBox := by
  intro x hx
  have hbuffer : finTwoToPair x ∈ P.scaleFamily.bufferDisk m := by
    by_contra hnot
    apply hx
    rw [backgroundCellDerivCoord, backgroundCellEuclideanDerivC,
      P.backgroundCellEuclideanDeriv_eq_zero_of_not_mem_bufferDisk ρ m j hnot]
    simp
  have hchart := P.bufferDisk_subset_chart m hbuffer
  rw [ScaleFamily.placementChart, Set.mem_prod, finTwoToPair_apply] at hchart
  intro k
  fin_cases k
  · change x 0 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨hchart.1.1, by linarith [hchart.1.2]⟩
  · change x 1 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨by linarith [hchart.2.1], by linarith [hchart.2.2]⟩

/-- The placed summand is integrable on the plane. -/
theorem integrable_backgroundCellSourceCoord {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    Integrable (P.backgroundCellSourceCoord ρ m) := by
  apply (P.continuous_backgroundCellSourceCoord hρ m).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_closedFundamentalBox
  exact (P.support_backgroundCellSourceCoord_subset_iocFundamentalBox ρ m).trans
    iocFundamentalBox_subset_closedFundamentalBox

/-- The displayed derivative is integrable on the plane. -/
theorem integrable_backgroundCellDerivCoord {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (j : Fin 2) : Integrable (P.backgroundCellDerivCoord ρ m j) := by
  have hfinite : volume (closedFundamentalBox : Set (Fin 2 → ℝ)) < ∞ :=
    isCompact_closedFundamentalBox.measure_lt_top
  have hbound : ∀ x, ‖P.backgroundCellDerivCoord ρ m j x‖ ≤
      3 * ρ * ((axialPlateauLipschitzConstant : ℝ) /
        P.scaleFamily.bufferRadius m) := by
    intro x
    rw [backgroundCellDerivCoord, backgroundCellEuclideanDerivC, Complex.norm_real,
      Real.norm_eq_abs]
    exact P.abs_backgroundCellEuclideanDeriv_le hρ m j _
  have hon : IntegrableOn (P.backgroundCellDerivCoord ρ m j) closedFundamentalBox :=
    IntegrableOn.of_bound hfinite
      (P.measurable_backgroundCellDerivCoord ρ m j).aestronglyMeasurable.restrict _
      (Filter.Eventually.of_forall hbound)
  apply hon.integrable_of_forall_notMem_eq_zero
  intro x hx
  by_contra hne
  exact hx ((P.support_backgroundCellDerivCoord_subset_iocFundamentalBox ρ m j hne)
    |> iocFundamentalBox_subset_closedFundamentalBox)

/-- Whole-plane integration by parts against a Fourier monomial. -/
theorem integral_euclideanMonomial_mul_backgroundCellDerivCoord
    {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (frequency : TransverseFrequency) (j : Fin 2) :
    (∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x * P.backgroundCellDerivCoord ρ m j x) =
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x * P.backgroundCellSourceCoord ρ m x := by
  let multiplier : ℂ := 2 * Real.pi * Complex.I * ((-frequency) j : ℂ)
  have hsource := P.integrable_backgroundCellSourceCoord hρ m
  have hderiv := P.integrable_backgroundCellDerivCoord hρ m j
  have hmonomial := euclideanMonomial_memLp_top (-frequency)
  have hmono_source : Integrable (fun x : Fin 2 → ℝ ↦
      euclideanMonomial (-frequency) x * P.backgroundCellSourceCoord ρ m x) :=
    hsource.mul_of_top_right hmonomial
  have hmono_deriv : Integrable (fun x : Fin 2 → ℝ ↦
      euclideanMonomial (-frequency) x * P.backgroundCellDerivCoord ρ m j x) :=
    hderiv.mul_of_top_right hmonomial
  have hderivMono : MemLp
      (fun x : Fin 2 → ℝ ↦ multiplier * euclideanMonomial (-frequency) x) ∞ :=
    hmonomial.const_mul multiplier
  have hderivMono_source : Integrable (fun x : Fin 2 → ℝ ↦
      (multiplier * euclideanMonomial (-frequency) x) *
        P.backgroundCellSourceCoord ρ m x) :=
    hsource.mul_of_top_right hderivMono
  have hibp :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (E := Fin 2 → ℝ) (F := ℂ) (G := ℂ) (W := ℂ)
      (B := ContinuousLinearMap.mul ℝ ℂ)
      hderivMono_source hmono_deriv hmono_source
      (fun x _ ↦ by
        simpa [multiplier] using euclideanMonomial_hasLineDerivAt (-frequency) j x)
      (fun x _ ↦ P.backgroundCellSourceCoord_hasLineDerivAt hρ m j x)
  change (∫ x : Fin 2 → ℝ,
      euclideanMonomial (-frequency) x * P.backgroundCellDerivCoord ρ m j x) = _ at hibp
  calc
    (∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x * P.backgroundCellDerivCoord ρ m j x) =
        -∫ x : Fin 2 → ℝ,
          (multiplier * euclideanMonomial (-frequency) x) *
            P.backgroundCellSourceCoord ρ m x := hibp
    _ = -multiplier * ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x * P.backgroundCellSourceCoord ρ m x := by
      rw [← integral_neg, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          ∫ x : Fin 2 → ℝ,
            euclideanMonomial (-frequency) x * P.backgroundCellSourceCoord ρ m x := by
      simp [multiplier]

/-! ## Transfer through the quotient fundamental domain -/

/-- A scalar Fourier coefficient can be computed from any almost-everywhere representative. -/
theorem transverseScalarCoeffCLM_eq_integral_of_coe_ae (u : TransverseScalarL2)
    (v : TransverseTorus → ℂ)
    (hu : (u : TransverseTorus → ℂ) =ᵐ[transverseMeasure] v)
    (frequency : TransverseFrequency) :
    transverseScalarCoeffCLM frequency u =
      ∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * v q ∂transverseMeasure := by
  rw [transverseScalarCoeffCLM_eq_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae frequency, hu] with q hmono hv
  rw [hmono, hv, UnitAddTorus.mFourier_neg, RCLike.inner_apply]
  ring

/-- Transfer of the value pairing from the torus to the plane. -/
theorem torusIntegral_mFourier_mul_backgroundCellSource_eq_euclidean
    (ρ : ℝ) (m : ℕ) (frequency : TransverseFrequency) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorus ρ m q
          ∂transverseMeasure) =
      ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x * P.backgroundCellSourceCoord ρ m x := by
  calc
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorus ρ m q
          ∂transverseMeasure) =
        ∫ x : Fin 2 → ℝ in iocFundamentalBox,
          UnitAddTorus.mFourier (-frequency) (fun k ↦ (x k : UnitAddCircle)) *
            P.backgroundCellTorus ρ m (fun k ↦ (x k : UnitAddCircle)) := by
      rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
        volume_unitAddTorus_eq_haar]
      have hpre := UnitAddTorus.integral_preimage
        (f := fun q : TransverseTorus ↦
          UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorus ρ m q)
        (fun _ : Fin 2 ↦ (0 : ℝ))
      change (∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorus ρ m q
            ∂torusHaarMeasure (Fin 2)) = _ at hpre
      simpa [iocFundamentalBox] using hpre
    _ = ∫ x : Fin 2 → ℝ in iocFundamentalBox,
          euclideanMonomial (-frequency) x * P.backgroundCellSourceCoord ρ m x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_iocFundamentalBox] with x hx
      have hx0 : (finTwoToPair x).1 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (0 : Fin 2)
      have hx1 : (finTwoToPair x).2 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (1 : Fin 2)
      have hq : (fun k ↦ (x k : UnitAddCircle)) =
          transverseTorusPoint (finTwoToPair x) := by
        funext k
        fin_cases k <;> simp
      rw [hq, P.backgroundCellTorus_transverseTorusPoint_eq_euclidean_of_mem_Ioc
        ρ m hx0 hx1, euclideanMonomial_eq_mFourier]
      rfl
    _ = ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x * P.backgroundCellSourceCoord ρ m x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hzero : P.backgroundCellSourceCoord ρ m x = 0 := by
        by_contra hne
        exact hx (P.support_backgroundCellSourceCoord_subset_iocFundamentalBox ρ m hne)
      rw [hzero, mul_zero]

/-- Transfer of the derivative pairing from the torus to the plane. -/
theorem torusIntegral_mFourier_mul_backgroundCellDeriv_eq_euclidean
    (ρ : ℝ) (m : ℕ) (j : Fin 2) (frequency : TransverseFrequency) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorusDeriv ρ m j q
          ∂transverseMeasure) =
      ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x * P.backgroundCellDerivCoord ρ m j x := by
  calc
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorusDeriv ρ m j q
          ∂transverseMeasure) =
        ∫ x : Fin 2 → ℝ in iocFundamentalBox,
          UnitAddTorus.mFourier (-frequency) (fun k ↦ (x k : UnitAddCircle)) *
            P.backgroundCellTorusDeriv ρ m j (fun k ↦ (x k : UnitAddCircle)) := by
      rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
        volume_unitAddTorus_eq_haar]
      have hpre := UnitAddTorus.integral_preimage
        (f := fun q : TransverseTorus ↦
          UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorusDeriv ρ m j q)
        (fun _ : Fin 2 ↦ (0 : ℝ))
      change (∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q * P.backgroundCellTorusDeriv ρ m j q
            ∂torusHaarMeasure (Fin 2)) = _ at hpre
      simpa [iocFundamentalBox] using hpre
    _ = ∫ x : Fin 2 → ℝ in iocFundamentalBox,
          euclideanMonomial (-frequency) x * P.backgroundCellDerivCoord ρ m j x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_iocFundamentalBox] with x hx
      have hx0 : (finTwoToPair x).1 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (0 : Fin 2)
      have hx1 : (finTwoToPair x).2 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (1 : Fin 2)
      have hq : (fun k ↦ (x k : UnitAddCircle)) =
          transverseTorusPoint (finTwoToPair x) := by
        funext k
        fin_cases k <;> simp
      rw [hq, P.backgroundCellTorusDeriv_transverseTorusPoint_eq_euclidean_of_mem_Ioc
        ρ m j hx0 hx1, euclideanMonomial_eq_mFourier]
      rfl
    _ = ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x * P.backgroundCellDerivCoord ρ m j x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hzero : P.backgroundCellDerivCoord ρ m j x = 0 := by
        by_contra hne
        exact hx (P.support_backgroundCellDerivCoord_subset_iocFundamentalBox ρ m j hne)
      rw [hzero, mul_zero]

/-! ## The bundled `L∞` classes and the weak derivative -/

/-- The descended summand as an `L∞` class. -/
def backgroundCellValueLInf {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) : TransverseScalarLInf :=
  (memLp_top_of_bound (P.measurable_backgroundCellTorus hρ m).aestronglyMeasurable
    (3 * ρ)
    (Filter.Eventually.of_forall (P.norm_backgroundCellTorus_le hρ m))).toLp
      (P.backgroundCellTorus ρ m)

/-- The descended derivative as an `L∞` class. -/
def backgroundCellDerivLInf {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (j : Fin 2) :
    TransverseScalarLInf :=
  (memLp_top_of_bound
    (P.measurable_backgroundCellTorusDeriv ρ m j).aestronglyMeasurable
    (3 * ρ * ((axialPlateauLipschitzConstant : ℝ) / P.scaleFamily.bufferRadius m))
    (Filter.Eventually.of_forall
      (P.norm_backgroundCellTorusDeriv_le hρ m j))).toLp
        (P.backgroundCellTorusDeriv ρ m j)

/-- The `L∞` class of the summand is represented by the pointwise field. -/
theorem backgroundCellValueLInf_coe_ae {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    (P.backgroundCellValueLInf hρ m : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] P.backgroundCellTorus ρ m :=
  MemLp.coeFn_toLp _

/-- The `L∞` class of the derivative is represented by the pointwise field. -/
theorem backgroundCellDerivLInf_coe_ae {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (j : Fin 2) :
    (P.backgroundCellDerivLInf hρ m j : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] P.backgroundCellTorusDeriv ρ m j :=
  MemLp.coeFn_toLp _

/-- Sup-norm bound for the summand class. -/
theorem norm_backgroundCellValueLInf_le {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    ‖P.backgroundCellValueLInf hρ m‖ ≤ 3 * ρ := by
  apply norm_transverseScalarLInf_le_of_ae_bound _ (by positivity)
  filter_upwards [P.backgroundCellValueLInf_coe_ae hρ m] with q hq
  rw [hq]
  exact P.norm_backgroundCellTorus_le hρ m q

/-- Sup-norm bound for the derivative class. -/
theorem norm_backgroundCellDerivLInf_le {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (j : Fin 2) :
    ‖P.backgroundCellDerivLInf hρ m j‖ ≤
      3 * ρ * ((axialPlateauLipschitzConstant : ℝ) /
        P.scaleFamily.bufferRadius m) := by
  have h3 : (0 : ℝ) ≤ (axialPlateauLipschitzConstant : ℝ) /
      P.scaleFamily.bufferRadius m :=
    div_nonneg (NNReal.coe_nonneg _) (P.scaleFamily.bufferRadius_pos m).le
  apply norm_transverseScalarLInf_le_of_ae_bound _ (by positivity)
  filter_upwards [P.backgroundCellDerivLInf_coe_ae hρ m j] with q hq
  rw [hq]
  exact P.norm_backgroundCellTorusDeriv_le hρ m j q

/-- **The displayed derivative of one placed summand is its periodic Fourier weak
derivative.** -/
theorem backgroundCell_hasFourierWeakDerivative {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (j : Fin 2) :
    HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 (P.backgroundCellValueLInf hρ m))
      (transverseScalarLInfToL2 (P.backgroundCellDerivLInf hρ m j)) := by
  intro frequency
  have hvalue : ((transverseScalarLInfToL2 (P.backgroundCellValueLInf hρ m)) :
      TransverseTorus → ℂ) =ᵐ[transverseMeasure] P.backgroundCellTorus ρ m := by
    filter_upwards [transverseScalarLInfToL2_coe_ae (P.backgroundCellValueLInf hρ m),
      P.backgroundCellValueLInf_coe_ae hρ m] with q h1 h2
    rw [h1, h2]
  have hderiv : ((transverseScalarLInfToL2 (P.backgroundCellDerivLInf hρ m j)) :
      TransverseTorus → ℂ) =ᵐ[transverseMeasure] P.backgroundCellTorusDeriv ρ m j := by
    filter_upwards [transverseScalarLInfToL2_coe_ae (P.backgroundCellDerivLInf hρ m j),
      P.backgroundCellDerivLInf_coe_ae hρ m j] with q h1 h2
    rw [h1, h2]
  rw [transverseScalarCoeffCLM_eq_integral_of_coe_ae _ _ hderiv,
    transverseScalarCoeffCLM_eq_integral_of_coe_ae _ _ hvalue,
    P.torusIntegral_mFourier_mul_backgroundCellDeriv_eq_euclidean ρ m j frequency,
    P.torusIntegral_mFourier_mul_backgroundCellSource_eq_euclidean ρ m frequency,
    P.integral_euclideanMonomial_mul_backgroundCellDerivCoord hρ m frequency j]
  rfl

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
