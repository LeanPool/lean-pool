/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusGlobalVelocityQualitative

/-!
# Qualitative regularity of the chart-side global velocity

`TorusGlobalVelocityQualitative` builds the paper's chart-side field

`U(x) = ∑_n (Re v_n(x) + a_n ϑ(|x - p_n|/R_n) e₃)`,

named `parameterizedFullGlobalEuclideanRealSource`, and proves its quadratic
decay at the transverse accumulation point `p_∞ = (0, 1/2)`.  This file records
the remaining qualitative statements of `lem:global-velocity` (with its proof),
`rem:scope-intro` and §3.4 (`sec:lipschitz-obstruction`) for that chart-side
representative:

* local finiteness of the cell sum away from `p_∞`, hence `ContDiffAt ℝ ⊤ U x`
  for every `x ≠ p_∞`;
* `Differentiable ℝ U` everywhere, with `fderiv ℝ U p_∞ = 0`;
* an explicit uniform bound `‖fderiv ℝ U x‖ ≤ L` and the resulting
  `LipschitzWith` statement;
* failure of continuity of `fderiv ℝ U` at `p_∞`: the derivative at every cell
  centre is the *same* nonzero map, because the amplitude `ell_n` of the local
  copy exactly cancels its dilation, whereas the derivative at `p_∞` is zero.
  Thus `U` is differentiable but not `C¹`;
* the identification of `U` with the torus-side representative
  `parameterizedFullGlobalRealTorusSource` through the placement chart.

Everything is stated on the Euclidean chart `ℝ × ℝ`, which is the
carrier of the paper's claims; no manifold smoothness on the transverse
torus is asserted.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Metric Set
open scoped ENNReal NNReal Topology LineDeriv SchwartzMap

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

namespace FullVelocityConcrete

/-! ## Coordinate calculus on the pair chart -/

/-- The two pair basis vectors span: `v = v₁ e₁ + v₂ e₂`. -/
theorem smul_pairBasis_add_smul_pairBasis (v : ℝ × ℝ) :
    v.1 • pairBasis 0 + v.2 • pairBasis 1 = v := by
  have h0 : pairBasis 0 = ((1 : ℝ), (0 : ℝ)) := rfl
  have h1 : pairBasis 1 = ((0 : ℝ), (1 : ℝ)) := rfl
  rw [h0, h1]
  simp

/-- Two continuous linear maps out of the pair chart agree as soon as they
agree on the two pair basis vectors. -/
theorem continuousLinearMap_ext_pairBasis {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {T S : (ℝ × ℝ) →L[ℝ] F}
    (h0 : T (pairBasis 0) = S (pairBasis 0))
    (h1 : T (pairBasis 1) = S (pairBasis 1)) : T = S := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v.1 • pairBasis 0 + v.2 • pairBasis 1 = v :=
    smul_pairBasis_add_smul_pairBasis v
  rw [← hv, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h0, h1]

/-- A continuous linear map out of the pair chart vanishes as soon as it kills
the two pair basis vectors. -/
theorem continuousLinearMap_eq_zero_pairBasis {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {T : (ℝ × ℝ) →L[ℝ] F}
    (h0 : T (pairBasis 0) = 0) (h1 : T (pairBasis 1) = 0) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v.1 • pairBasis 0 + v.2 • pairBasis 1 = v :=
    smul_pairBasis_add_smul_pairBasis v
  rw [← hv, map_add, map_smul, map_smul, h0, h1]
  simp

/-- The operator norm of a map out of the sup-normed pair chart is controlled
by the two coordinate images. -/
theorem opNorm_le_add_pairBasis {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : (ℝ × ℝ) →L[ℝ] F) :
    ‖T‖ ≤ ‖T (pairBasis 0)‖ + ‖T (pairBasis 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : T v = v.1 • T (pairBasis 0) + v.2 • T (pairBasis 1) := by
    conv_lhs => rw [← smul_pairBasis_add_smul_pairBasis v]
    rw [map_add, map_smul, map_smul]
  have h1 : |v.1| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using norm_snd_le v
  calc
    ‖T v‖ = ‖v.1 • T (pairBasis 0) + v.2 • T (pairBasis 1)‖ := by rw [hv]
    _ ≤ ‖v.1 • T (pairBasis 0)‖ + ‖v.2 • T (pairBasis 1)‖ := norm_add_le _ _
    _ = |v.1| * ‖T (pairBasis 0)‖ + |v.2| * ‖T (pairBasis 1)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖T (pairBasis 0)‖ + ‖v‖ * ‖T (pairBasis 1)‖ := by
      gcongr
    _ = (‖T (pairBasis 0)‖ + ‖T (pairBasis 1)‖) * ‖v‖ := by ring

/-! ## Smoothness of one combined Euclidean cell -/

variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- The affine cell coordinate `x ↦ (x - p_n)/ell_n` is smooth. -/
theorem contDiff_helicalCellCoordinate (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (helicalCellCoordinate h P n) := by
  change ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × ℝ ↦ (P.scaleFamily.ell n)⁻¹ •
    (pairToWholePlane x - pairToWholePlane (P.scaleFamily.cellCenter n))
  exact (pairToWholePlane.contDiff.sub contDiff_const).const_smul _

/-- The rescaled helical cell source is smooth of every order, being a
Schwartz profile composed with an affine map. -/
theorem contDiff_parameterizedHelicalCellSource (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (parameterizedHelicalCellSource h P angularSpeed axialSpeed n) := by
  change ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × ℝ ↦ P.scaleFamily.ell n •
    parameterizedSmoothedVelocity h angularSpeed axialSpeed
      (helicalCellCoordinate h P n x)
  exact (((parameterizedSmoothedVelocity h angularSpeed axialSpeed).smooth ⊤).comp
    (contDiff_helicalCellCoordinate h P n)).const_smul _

/-- One combined Euclidean cell — the real part of the helical copy plus the
cut-off axial shift — is smooth of every order. -/
theorem contDiff_parameterizedFullEuclideanCellRealSource (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n) := by
  change ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × ℝ ↦
    vecRe (parameterizedHelicalCellSource h P angularSpeed axialSpeed n x) +
      P.axialOffsetEuclidean tau n x
  exact (vecReCLM.contDiff.comp
      (contDiff_parameterizedHelicalCellSource h P angularSpeed axialSpeed n)).add
    (P.axialOffsetEuclidean_contDiff tau n)

/-- One combined Euclidean cell is differentiable. -/
theorem differentiable_parameterizedFullEuclideanCellRealSource (n : ℕ) :
    Differentiable ℝ
      (parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n) :=
  (contDiff_parameterizedFullEuclideanCellRealSource
    h P angularSpeed axialSpeed tau n).differentiable (by simp)

/-! ## The coordinate derivative of one combined cell -/

/-- The displayed coordinate derivative of one combined Euclidean cell:
the real part of the helical derivative plus the axial cutoff derivative. -/
def parameterizedFullEuclideanCellRealSourceDeriv (n : ℕ) (j : Fin 2)
    (x : ℝ × ℝ) : R3 :=
  vecRe (parameterizedHelicalCellSourceDeriv
      h P angularSpeed axialSpeed n j x) +
    P.axialOffsetEuclideanDerivative tau n j x

/-- The displayed coordinate derivative is the Fréchet derivative of
one combined Euclidean cell, evaluated on a pair basis vector. -/
theorem fderiv_parameterizedFullEuclideanCellRealSource_apply_pairBasis
    (n : ℕ) (j : Fin 2) (x : ℝ × ℝ) :
    fderiv ℝ (parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n) x (pairBasis j) =
      parameterizedFullEuclideanCellRealSourceDeriv
        h P angularSpeed axialSpeed tau n j x := by
  have hhelical : HasFDerivAt
      (fun y : ℝ × ℝ ↦ vecRe (parameterizedHelicalCellSource
        h P angularSpeed axialSpeed n y))
      (vecReCLM.comp (parameterizedHelicalCellSourceFDeriv
        h P angularSpeed axialSpeed n x)) x :=
    vecReCLM.hasFDerivAt.comp x
      (parameterizedHelicalCellSource_hasFDerivAt
        h P angularSpeed axialSpeed n x)
  have haxial : HasFDerivAt (P.axialOffsetEuclidean tau n)
      (fderiv ℝ (P.axialOffsetEuclidean tau n) x) x :=
    (((P.axialOffsetEuclidean_contDiff tau n).differentiable
      (by simp)) x).hasFDerivAt
  have hcell : HasFDerivAt
      (parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n)
      (vecReCLM.comp (parameterizedHelicalCellSourceFDeriv
          h P angularSpeed axialSpeed n x) +
        fderiv ℝ (P.axialOffsetEuclidean tau n) x) x :=
    hhelical.fun_add haxial
  rw [hcell.fderiv]
  change vecRe (parameterizedHelicalCellSourceFDeriv
        h P angularSpeed axialSpeed n x (pairBasis j)) +
      fderiv ℝ (P.axialOffsetEuclidean tau n) x (pairBasis j) =
    vecRe (parameterizedHelicalCellSourceDeriv
        h P angularSpeed axialSpeed n j x) +
      P.axialOffsetEuclideanDerivative tau n j x
  rw [parameterizedHelicalCellSourceFDeriv_apply_pairBasis,
    P.fderiv_axialOffsetEuclidean_apply_pairBasis tau n j x]

/-- The displayed coordinate derivative of one combined cell vanishes off that
cell's buffer disc: the helical part is supported in the much smaller local
core, and the axial plateau is at a global extremum there. -/
theorem parameterizedFullEuclideanCellRealSourceDeriv_eq_zero_of_not_mem_bufferDisk
    (n : ℕ) (j : Fin 2) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    parameterizedFullEuclideanCellRealSourceDeriv
      h P angularSpeed axialSpeed tau n j x = 0 := by
  have hcore : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n :=
    fun hmem ↦ hx (P.localCoreDisk_subset_bufferDisk n hmem)
  rw [parameterizedFullEuclideanCellRealSourceDeriv,
    parameterizedHelicalCellSourceDeriv_eq_zero_of_not_mem_localCoreDisk
      h P angularSpeed axialSpeed n j hcore,
    P.axialOffsetEuclideanDerivative_eq_zero_of_not_mem_bufferDisk tau n j hx]
  apply PiLp.ext
  intro i
  simp [vecRe]

/-- The uniform bound for one coordinate derivative of the chart-side global
velocity: the scale-invariant profile gradient plus the paper's axial
cutoff-gradient scale `‖ϑ'‖_∞ a_0 / R_0`. -/
def globalVelocityCoordinateDerivativeBound : ℝ :=
  parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
    (axialPlateauLipschitzConstant : ℝ) *
      P.scaleFamily.axialGradientScale tau 0

/-- The coordinate-derivative bound is nonnegative for nonnegative axial
separation parameters. -/
theorem globalVelocityCoordinateDerivativeBound_nonneg (htau : 0 ≤ tau) :
    0 ≤ globalVelocityCoordinateDerivativeBound
      h P angularSpeed axialSpeed tau := by
  have hscale : 0 ≤ P.scaleFamily.axialGradientScale tau 0 := by
    rw [P.scaleFamily.axialGradientScale_formula tau 0]
    exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
      (P.scaleFamily.bufferRadius_nonneg 0)
  exact add_nonneg
    (parameterizedHelicalFirstDerivativeBound_nonneg h angularSpeed axialSpeed)
    (mul_nonneg (NNReal.coe_nonneg _) hscale)

/-- Each displayed coordinate derivative of one combined cell obeys the
uniform bound, independently of the cell index. -/
theorem norm_parameterizedFullEuclideanCellRealSourceDeriv_le
    (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) (x : ℝ × ℝ) :
    ‖parameterizedFullEuclideanCellRealSourceDeriv
        h P angularSpeed axialSpeed tau n j x‖ ≤
      globalVelocityCoordinateDerivativeBound
        h P angularSpeed axialSpeed tau := by
  calc
    ‖parameterizedFullEuclideanCellRealSourceDeriv
        h P angularSpeed axialSpeed tau n j x‖ ≤
        ‖vecRe (parameterizedHelicalCellSourceDeriv
            h P angularSpeed axialSpeed n j x)‖ +
          ‖P.axialOffsetEuclideanDerivative tau n j x‖ := norm_add_le _ _
    _ ≤ parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed +
        (axialPlateauLipschitzConstant : ℝ) *
          P.scaleFamily.axialGradientScale tau n :=
      add_le_add
        ((norm_vecRe_le _).trans
          (norm_parameterizedHelicalCellSourceDeriv_le
            h P angularSpeed axialSpeed n j x))
        (P.norm_axialOffsetEuclideanDerivative_le htau n j x)
    _ ≤ globalVelocityCoordinateDerivativeBound
        h P angularSpeed axialSpeed tau := by
      have hstep : (axialPlateauLipschitzConstant : ℝ) *
            P.scaleFamily.axialGradientScale tau n ≤
          (axialPlateauLipschitzConstant : ℝ) *
            P.scaleFamily.axialGradientScale tau 0 :=
        mul_le_mul_of_nonneg_left
          (P.scaleFamily.axialGradientScale_le_zero htau n)
          (NNReal.coe_nonneg _)
      rw [globalVelocityCoordinateDerivativeBound]
      linarith

/-! ## Local finiteness of the cell sum away from the accumulation point -/

/-- Every point of the `n`th buffer disc is at distance less than twice the
`n`th centre coordinate from the accumulation point.  Since the centre
coordinates tend to zero, far buffers are invisible near any other point. -/
theorem dist_accumulationPoint_lt_of_mem_bufferDisk
    (f : ScaleFamily r) (n : ℕ) {x : ℝ × ℝ} (hx : x ∈ f.bufferDisk n) :
    dist x accumulationPoint < 2 * f.cellCenterCoordinate n := by
  have hcenter : dist x (f.cellCenter n) < f.bufferRadius n := hx
  have htriangle := dist_triangle x (f.cellCenter n) accumulationPoint
  rw [dist_cellCenter_accumulationPoint] at htriangle
  have hrec := f.cellCenterCoordinate_recursion n
  have hnext := (f.cellCenterCoordinate_pos (n + 1)).le
  have hpos := f.bufferRadius_pos n
  linarith

/-- Away from the accumulation point all but finitely many buffer discs miss a
fixed ball.  This is the local finiteness behind chart-side smoothness. -/
theorem exists_forall_not_mem_bufferDisk_of_ne_accumulationPoint
    (f : ScaleFamily r) {x : ℝ × ℝ} (hx : x ≠ accumulationPoint) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ y ∈ ball x (dist x accumulationPoint / 2), y ∉ f.bufferDisk n := by
  have hd : 0 < dist x accumulationPoint := dist_pos.mpr hx
  have hlimit : Tendsto (fun n : ℕ ↦ 2 * f.cellCenterCoordinate n) atTop (𝓝 0) := by
    simpa using f.tendsto_cellCenterCoordinate_zero.const_mul 2
  have hev : ∀ᶠ n : ℕ in atTop,
      2 * f.cellCenterCoordinate n < dist x accumulationPoint / 2 :=
    hlimit.eventually_lt_const (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn y hy hmem ↦ ?_⟩
  have h1 : dist y accumulationPoint < 2 * f.cellCenterCoordinate n :=
    dist_accumulationPoint_lt_of_mem_bufferDisk f n hmem
  have h2 : dist x y < dist x accumulationPoint / 2 := by
    simpa [mem_ball, dist_comm] using hy
  have h3 := dist_triangle x y accumulationPoint
  have h4 := hN n hn
  linarith

/-- Near any point other than the accumulation point the chart-side global
field is a *finite* sum of combined Euclidean cells. -/
theorem exists_eventuallyEq_finsetSum_of_ne_accumulationPoint
    {x : ℝ × ℝ} (hx : x ≠ accumulationPoint) :
    ∃ N : ℕ,
      parameterizedFullGlobalEuclideanRealSource
          h P angularSpeed axialSpeed tau =ᶠ[𝓝 x]
        fun y ↦ ∑ n ∈ Finset.range N,
          parameterizedFullEuclideanCellRealSource
            h P angularSpeed axialSpeed tau n y := by
  obtain ⟨N, hN⟩ :=
    exists_forall_not_mem_bufferDisk_of_ne_accumulationPoint P.scaleFamily hx
  refine ⟨N, ?_⟩
  filter_upwards [ball_mem_nhds x (half_pos (dist_pos.mpr hx))] with y hy
  refine tsum_eq_sum ?_
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  exact parameterizedFullEuclideanCellRealSource_eq_zero_of_not_mem_bufferDisk
    h P angularSpeed axialSpeed tau n (hN n hn y hy)

/-! ## Smoothness away from the accumulation point -/

/-- The chart-side global velocity is smooth of every order away from the
accumulation point: locally it is a finite sum of smooth cells. -/
theorem contDiffAt_parameterizedFullGlobalEuclideanRealSource
    {x : ℝ × ℝ} (hx : x ≠ accumulationPoint) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) x := by
  obtain ⟨N, heq⟩ :=
    exists_eventuallyEq_finsetSum_of_ne_accumulationPoint
      h P angularSpeed axialSpeed tau hx
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y ↦ ∑ n ∈ Finset.range N,
        parameterizedFullEuclideanCellRealSource
          h P angularSpeed axialSpeed tau n y) x :=
    ContDiffAt.sum fun n _ ↦
      (contDiff_parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n).contDiffAt
  exact hsum.congr_of_eventuallyEq heq

/-- The chart-side global velocity is differentiable everywhere: smooth away
from the accumulation point, and quadratically flat at it. -/
theorem differentiable_parameterizedFullGlobalEuclideanRealSource
    (htau : 0 ≤ tau) :
    Differentiable ℝ
      (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) := by
  intro x
  by_cases hx : x = accumulationPoint
  · subst hx
    exact parameterizedFullGlobalEuclideanRealSource_differentiableAt_accumulationPoint
      h P angularSpeed axialSpeed htau
  · exact (contDiffAt_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau hx).differentiableAt (by simp)

/-- The Fréchet derivative of the chart-side global velocity vanishes at the
accumulation point (`Du = 0` on the accumulation circle). -/
theorem fderiv_parameterizedFullGlobalEuclideanRealSource_accumulationPoint
    (htau : 0 ≤ tau) :
    fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau) accumulationPoint = 0 :=
  (parameterizedFullGlobalEuclideanRealSource_hasFDerivAt_accumulationPoint
    h P angularSpeed axialSpeed htau).fderiv

/-! ## The uniform derivative bound and the Lipschitz constant -/

/-- Inside a buffer disc the chart-side global velocity coincides with a single
cell, hence so does its derivative. -/
theorem fderiv_parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
    {n : ℕ} {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) x =
      fderiv ℝ (parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n) x := by
  apply Filter.EventuallyEq.fderiv_eq
  have hopen : IsOpen (P.scaleFamily.bufferDisk n) := Metric.isOpen_ball
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
    h P angularSpeed axialSpeed tau hy

/-- Each coordinate derivative of the chart-side global velocity obeys the
uniform bound: inside a buffer it is the (scale-invariant) cell derivative, and
elsewhere it vanishes. -/
theorem norm_fderiv_parameterizedFullGlobalEuclideanRealSource_apply_pairBasis_le
    (htau : 0 ≤ tau) (j : Fin 2) (x : ℝ × ℝ) :
    ‖fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) x (pairBasis j)‖ ≤
      globalVelocityCoordinateDerivativeBound
        h P angularSpeed axialSpeed tau := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [fderiv_parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
      h P angularSpeed axialSpeed tau hn,
      fderiv_parameterizedFullEuclideanCellRealSource_apply_pairBasis]
    exact norm_parameterizedFullEuclideanCellRealSourceDeriv_le
      h P angularSpeed axialSpeed tau htau n j x
  · push Not at hbuffer
    have hzero : fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) x (pairBasis j) = 0 := by
      by_cases hx : x = accumulationPoint
      · subst hx
        rw [fderiv_parameterizedFullGlobalEuclideanRealSource_accumulationPoint
          h P angularSpeed axialSpeed tau htau]
        rfl
      · obtain ⟨N, heq⟩ :=
          exists_eventuallyEq_finsetSum_of_ne_accumulationPoint
            h P angularSpeed axialSpeed tau hx
        have hsum : HasFDerivAt
            (fun y ↦ ∑ n ∈ Finset.range N,
              parameterizedFullEuclideanCellRealSource
                h P angularSpeed axialSpeed tau n y)
            (∑ n ∈ Finset.range N,
              fderiv ℝ (parameterizedFullEuclideanCellRealSource
                h P angularSpeed axialSpeed tau n) x) x :=
          HasFDerivAt.fun_sum fun n _ ↦
            ((differentiable_parameterizedFullEuclideanCellRealSource
              h P angularSpeed axialSpeed tau n) x).hasFDerivAt
        have hcellzero : ∀ n ∈ Finset.range N,
            fderiv ℝ (parameterizedFullEuclideanCellRealSource
              h P angularSpeed axialSpeed tau n) x = 0 := by
          intro n _
          refine continuousLinearMap_eq_zero_pairBasis ?_ ?_ <;>
            · rw [fderiv_parameterizedFullEuclideanCellRealSource_apply_pairBasis]
              exact
                parameterizedFullEuclideanCellRealSourceDeriv_eq_zero_of_not_mem_bufferDisk
                  h P angularSpeed axialSpeed tau n _ (hbuffer n)
        rw [(hsum.congr_of_eventuallyEq heq).fderiv,
          Finset.sum_eq_zero hcellzero]
        rfl
    rw [hzero, norm_zero]
    exact globalVelocityCoordinateDerivativeBound_nonneg
      h P angularSpeed axialSpeed tau htau

/-- The explicit global Lipschitz constant of the chart-side velocity: twice
the coordinate-derivative bound, the factor two coming from the sup norm on the
pair chart. -/
def globalVelocityLipschitzBound : ℝ :=
  2 * globalVelocityCoordinateDerivativeBound h P angularSpeed axialSpeed tau

/-- The global Lipschitz bound is nonnegative for nonnegative axial separation
parameters. -/
theorem globalVelocityLipschitzBound_nonneg (htau : 0 ≤ tau) :
    0 ≤ globalVelocityLipschitzBound h P angularSpeed axialSpeed tau := by
  rw [globalVelocityLipschitzBound]
  have := globalVelocityCoordinateDerivativeBound_nonneg
    h P angularSpeed axialSpeed tau htau
  linarith

/-- The uniform derivative bound of the paper: the amplitude `ell_n` of
each local copy exactly cancels its dilation, and the axial cutoff contributes
the bounded scale `a_n / R_n ≤ a_0 / R_0`. -/
theorem norm_fderiv_parameterizedFullGlobalEuclideanRealSource_le
    (htau : 0 ≤ tau) (x : ℝ × ℝ) :
    ‖fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) x‖ ≤
      globalVelocityLipschitzBound h P angularSpeed axialSpeed tau := by
  refine (opNorm_le_add_pairBasis _).trans ?_
  rw [globalVelocityLipschitzBound, two_mul]
  exact add_le_add
    (norm_fderiv_parameterizedFullGlobalEuclideanRealSource_apply_pairBasis_le
      h P angularSpeed axialSpeed tau htau 0 x)
    (norm_fderiv_parameterizedFullGlobalEuclideanRealSource_apply_pairBasis_le
      h P angularSpeed axialSpeed tau htau 1 x)

/-- The chart-side global velocity is Lipschitz with the explicit constant
`globalVelocityLipschitzBound`, by the mean value inequality. -/
theorem lipschitzWith_parameterizedFullGlobalEuclideanRealSource
    (htau : 0 ≤ tau) :
    LipschitzWith
      (Real.toNNReal
        (globalVelocityLipschitzBound h P angularSpeed axialSpeed tau))
      (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) := by
  apply lipschitzWith_of_nnNorm_fderiv_le
    (differentiable_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau htau)
  intro x
  rw [← NNReal.coe_le_coe, coe_nnNorm,
    Real.coe_toNNReal _
      (globalVelocityLipschitzBound_nonneg h P angularSpeed axialSpeed tau htau)]
  exact norm_fderiv_parameterizedFullGlobalEuclideanRealSource_le
    h P angularSpeed axialSpeed tau htau x

/-! ## Failure of continuity of the derivative at the accumulation point -/

/-- The fixed axial plateau has vanishing derivative at the origin, being
identically one on the product-metric ball of radius `1/2`. -/
theorem fderiv_axialPlateauBump_zero :
    fderiv ℝ (axialPlateauBump : (ℝ × ℝ) → ℝ) 0 = 0 := by
  have heq : (axialPlateauBump : (ℝ × ℝ) → ℝ) =ᶠ[𝓝 0] fun _ ↦ (1 : ℝ) := by
    filter_upwards [ball_mem_nhds (0 : ℝ × ℝ) (by norm_num : (0 : ℝ) < 1 / 2)]
      with y hy
    exact axialPlateau_eq_one_of_norm_le_half
      (le_of_lt (by simpa [mem_ball, dist_zero_right] using hy))
  rw [heq.fderiv_eq]
  exact fderiv_const_apply _

/-- The rescaled cell coordinate vanishes at the cell centre. -/
@[simp] theorem helicalCellCoordinate_cellCenter (n : ℕ) :
    helicalCellCoordinate h P n (P.scaleFamily.cellCenter n) = 0 := by
  simp [helicalCellCoordinate]

/-- The normalized buffer coordinate vanishes at the cell centre. -/
@[simp] theorem axialBufferCoordinate_cellCenter (n : ℕ) :
    P.axialBufferCoordinate n (P.scaleFamily.cellCenter n) = 0 := by
  simp [axialBufferCoordinate]

/-- At a cell centre the added axial velocity has zero derivative: the plateau
is constant there. -/
theorem axialOffsetEuclideanDerivative_cellCenter (n : ℕ) (j : Fin 2) :
    P.axialOffsetEuclideanDerivative tau n j
      (P.scaleFamily.cellCenter n) = 0 := by
  rw [axialOffsetEuclideanDerivative, axialCellCutoffDerivative,
    axialBufferCoordinate_cellCenter, fderiv_axialPlateauBump_zero]
  simp

/-- At every cell centre the chart-side derivative is the *same* map, namely
the unrescaled profile derivative at the origin.  The amplitude `ell_n` of the
local copy cancels its dilation exactly, and the axial plateau is flat. -/
theorem fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_apply_pairBasis
    (n : ℕ) (j : Fin 2) :
    fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau)
        (P.scaleFamily.cellCenter n) (pairBasis j) =
      vecRe ((∂_{wholePlaneBasis j}
        (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) 0) := by
  have hmem : P.scaleFamily.cellCenter n ∈ P.scaleFamily.bufferDisk n := by
    rw [ScaleFamily.bufferDisk]
    exact mem_ball_self (P.scaleFamily.bufferRadius_pos n)
  rw [fderiv_parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
    h P angularSpeed axialSpeed tau hmem,
    fderiv_parameterizedFullEuclideanCellRealSource_apply_pairBasis,
    parameterizedFullEuclideanCellRealSourceDeriv,
    axialOffsetEuclideanDerivative_cellCenter, add_zero,
    parameterizedHelicalCellSourceDeriv, helicalCellCoordinate_cellCenter]

/-- Consequently the chart-side derivative takes one and the same value at
every cell centre. -/
theorem fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_eq (n : ℕ) :
    fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter n) =
      fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter 0) := by
  apply continuousLinearMap_ext_pairBasis <;>
    rw [fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_apply_pairBasis,
      fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_apply_pairBasis]

/-- The second component of the profile's first coordinate derivative at the
origin is the angular speed `Ω`: the local flow is `(-Ω y₂ χ, Ω y₁ χ, U χ)`
with `χ(0) = 1`. -/
theorem lineDeriv_parameterizedSmoothedVelocity_zero_apply_one :
    (∂_{wholePlaneBasis (0 : Fin 2)}
        (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
      0 (1 : Fin 3) = (angularSpeed : ℂ) := by
  have hvalue : (parameterizedRadialProfile h).value (0 : WholePlane) = 1 := by
    apply parameterizedRadialProfile_value_one
    have := h.2.2
    simp only [norm_zero]
    linarith
  change (∂_{wholePlaneBasis (0 : Fin 2)}
    (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
      angularSpeed axialSpeed)) 0 (1 : Fin 3) = _
  rw [lineDeriv_squaredRadiusHelicalVelocity_apply_one, hvalue]
  simp [wholePlaneBasis]

/-- The chart-side derivative at every cell centre is nonzero whenever the
local flow rotates.  This is the paper's obstruction to `C¹` regularity. -/
theorem fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_ne_zero
    (hangularSpeed : angularSpeed ≠ 0) (n : ℕ) :
    fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter n) ≠ 0 := by
  intro hzero
  have happly : vecRe ((∂_{wholePlaneBasis (0 : Fin 2)}
      (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) 0) = 0 := by
    rw [← fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_apply_pairBasis
      h P angularSpeed axialSpeed tau n 0, hzero]
    simp
  have hcoord : ((∂_{wholePlaneBasis (0 : Fin 2)}
      (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) 0 (1 : Fin 3)).re = 0 := by
    simpa using congrArg (fun w : R3 ↦ w (1 : Fin 3)) happly
  rw [lineDeriv_parameterizedSmoothedVelocity_zero_apply_one] at hcoord
  simp only [Complex.ofReal_re] at hcoord
  exact hangularSpeed hcoord

/-- The chart-side global velocity is differentiable but not `C¹`: its
derivative is discontinuous at the accumulation point, being zero there and
constantly nonzero along the cell centres. -/
theorem not_continuousAt_fderiv_parameterizedFullGlobalEuclideanRealSource
    (htau : 0 ≤ tau) (hangularSpeed : angularSpeed ≠ 0) :
    ¬ ContinuousAt (fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau)) accumulationPoint := by
  intro hcont
  have hseq : Tendsto
      (fun n : ℕ ↦ fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter n))
      atTop (𝓝 (fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) accumulationPoint)) :=
    hcont.tendsto.comp (tendsto_cellCenter_accumulationPoint P.scaleFamily)
  rw [fderiv_parameterizedFullGlobalEuclideanRealSource_accumulationPoint
    h P angularSpeed axialSpeed tau htau] at hseq
  have hconst : Tendsto
      (fun n : ℕ ↦ fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter n))
      atTop (𝓝 (fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter 0))) := by
    have hfun : (fun n : ℕ ↦ fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter n)) =
        fun _ : ℕ ↦ fderiv ℝ (parameterizedFullGlobalEuclideanRealSource
          h P angularSpeed axialSpeed tau) (P.scaleFamily.cellCenter 0) := by
      funext n
      exact fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_eq
        h P angularSpeed axialSpeed tau n
    rw [hfun]
    exact tendsto_const_nhds
  exact fderiv_parameterizedFullGlobalEuclideanRealSource_cellCenter_ne_zero
    h P angularSpeed axialSpeed tau hangularSpeed 0
      (tendsto_nhds_unique hconst hseq)

/-! ## Identification with the torus-side representative -/

/-- On the canonical `(0,1]²` fundamental rectangle, the descended field of a
cell pulled back along the quotient is the original Euclidean field, provided
the latter vanishes off that cell's buffer disc. -/
theorem torusPeriodizedExtension_transverseTorusPoint_of_mem_Ioc
    {supportRadius : ℝ} (Q : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (g : ℝ × ℝ → E)
    (hg : ∀ y, y ∉ Q.scaleFamily.bufferDisk n → g y = 0)
    {x : ℝ × ℝ} (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    Q.torusPeriodizedExtension n g (transverseTorusPoint x) = g x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hiff : transverseTorusPoint x ∈ Q.torusBufferDisk n ↔
      x ∈ Q.scaleFamily.bufferDisk n := by
    rw [Q.mem_torusBufferDisk_iff_transverseIocRepresentative n, hrep]
  by_cases hx : x ∈ Q.scaleFamily.bufferDisk n
  · exact Q.periodizedExtension_eq_source n g hx
  · rw [Q.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk n g
      (hiff.not.mpr hx), hg x hx]

/-- The descended axial cell field pulled back along the quotient is the
Euclidean axial cell field on the fundamental rectangle. -/
theorem axialOffsetTorus_transverseTorusPoint_of_mem_Ioc
    {supportRadius : ℝ} (Q : TorusCellPlacement (r := r) supportRadius)
    (n : ℕ) {x : ℝ × ℝ} (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    Q.axialOffsetTorus tau n (transverseTorusPoint x) =
      Q.axialOffsetEuclidean tau n x :=
  torusPeriodizedExtension_transverseTorusPoint_of_mem_Ioc Q n _
    (fun _ hy ↦ Q.axialOffsetEuclidean_eq_zero_of_not_mem_bufferDisk tau n hy)
    hxzero hxone

/-- The paper's identification: on the canonical fundamental rectangle the
torus-side global velocity representative is exactly the chart-side Euclidean
cell sum. -/
theorem parameterizedFullGlobalRealTorusSource_transverseTorusPoint_of_mem_Ioc
    {x : ℝ × ℝ} (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint x) =
      parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hiff : ∀ n : ℕ, transverseTorusPoint x ∈ P.torusBufferDisk n ↔
      x ∈ P.scaleFamily.bufferDisk n := by
    intro n
    rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative n, hrep]
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    have hq : transverseTorusPoint x ∈ P.torusBufferDisk n := (hiff n).mpr hn
    rw [parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
      h P angularSpeed axialSpeed tau hn,
      parameterizedFullGlobalRealTorusSource,
      parameterizedHelicalGlobalRealTorusSource,
      parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
        h P angularSpeed axialSpeed hq,
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource_transverseTorusPoint_eq_source_of_mem_Ioc
          hxzero hxone,
      P.axialOffsetGlobalTorus_eq_cell_of_mem_buffer tau hq,
      axialOffsetTorus_transverseTorusPoint_of_mem_Ioc tau P n hxzero hxone]
    rfl
  · push Not at hbuffer
    have hq : ∀ n : ℕ, transverseTorusPoint x ∉ P.torusBufferDisk n :=
      fun n hmem ↦ hbuffer n ((hiff n).mp hmem)
    rw [parameterizedFullGlobalEuclideanRealSource_eq_zero_of_outside_buffers
      h P angularSpeed axialSpeed tau hbuffer,
      parameterizedFullGlobalRealTorusSource,
      parameterizedHelicalGlobalRealTorusSource,
      parameterizedHelicalGlobalTorusSource_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed hq,
      P.axialOffsetGlobalTorus_eq_zero_of_outside_buffers tau hq]
    apply PiLp.ext
    intro i
    simp [vecRe]

/-! ## The bundled qualitative statement -/

/-- The paper's qualitative package for a chart-side velocity field:
everywhere differentiable, smooth away from the transverse accumulation point,
with vanishing derivative there, globally Lipschitz, and with a derivative that
is discontinuous at the accumulation point — so the field is differentiable but
not `C¹` (`lem:global-velocity`, `rem:scope-intro`, `sec:lipschitz-obstruction`). -/
structure GlobalVelocityQualitative (U : ℝ × ℝ → R3) : Prop where
  /-- The field is differentiable at every point of the chart. -/
  differentiable : Differentiable ℝ U
  /-- Away from the accumulation point the field is smooth of every order. -/
  contDiffAt_of_ne_accumulationPoint :
    ∀ x, x ≠ accumulationPoint → ContDiffAt ℝ (⊤ : ℕ∞) U x
  /-- The derivative vanishes at the accumulation point. -/
  fderiv_accumulationPoint : fderiv ℝ U accumulationPoint = 0
  /-- The field is Lipschitz for some finite constant. -/
  exists_lipschitzWith : ∃ L : NNReal, LipschitzWith L U
  /-- The derivative is discontinuous at the accumulation point. -/
  not_continuousAt_fderiv : ¬ ContinuousAt (fderiv ℝ U) accumulationPoint

/-- The chart-side global velocity of the construction satisfies the full
qualitative package, for every nonnegative axial separation parameter and every
nonzero angular speed of the local helical flow. -/
theorem parameterizedFullGlobalEuclideanRealSource_qualitative
    (htau : 0 ≤ tau) (hangularSpeed : angularSpeed ≠ 0) :
    GlobalVelocityQualitative
      (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) where
  differentiable := differentiable_parameterizedFullGlobalEuclideanRealSource
    h P angularSpeed axialSpeed tau htau
  contDiffAt_of_ne_accumulationPoint := fun _ hx ↦
    contDiffAt_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau hx
  fderiv_accumulationPoint :=
    fderiv_parameterizedFullGlobalEuclideanRealSource_accumulationPoint
      h P angularSpeed axialSpeed tau htau
  exists_lipschitzWith :=
    ⟨Real.toNNReal
        (globalVelocityLipschitzBound h P angularSpeed axialSpeed tau),
      lipschitzWith_parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau htau⟩
  not_continuousAt_fderiv :=
    not_continuousAt_fderiv_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau htau hangularSpeed

end FullVelocityConcrete

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
