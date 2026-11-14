/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedFinite

/-!
# SolutionSelector

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The selected solution, the closed cube, and evaluation by ball averages

Three deterministic ingredients of the measurability of the localized
quantities.

*The selected solution.*  The rough-field Dirichlet problem on `y + □_n` has a
solution for every sample and every Hölder forcing field; `solutionAt` names one,
and by the almost-everywhere uniqueness of the problem any other choice differs
from it on a null set only, so every quantity built from its continuous
representative is independent of the choice.

*The closed cube.*  The coefficient field is measured in the supremum norm on a
compact set; `closedCubeAt y n` is the closed cube of side `3^n` centred at `y`,
which contains `y + □_n`, is compact, and sits inside a centred open cube of
large enough scale.  `clampTo` is the coordinatewise retraction onto it.

*Evaluation by ball averages.*  A function continuous on an open set is the limit
of its averages over shrinking balls, and averages depend only on the
almost-everywhere class.  This is what turns pointwise evaluation of a continuous
representative into a countable limit of integrals of the `H¹` witness.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory Filter
open Algsuperdiff.Section4.Support
open scoped Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. The selected solution -/

/-- A solution of the rough-field Dirichlet problem on `y + □_n`.

The solution is obtained by choice from an existence statement whose input
includes the bound `Kg`, although `Kg` does not constrain the solution: two
admissible bounds for the same forcing field may name syntactically different
solutions.  Every consumer must therefore pass through the almost-everywhere
uniqueness of the Dirichlet solution, never through equality of selections. -/
def solutionAt (M : ABKModel d) (m n : ℤ) (y : Vec d) (omega : Cutoff.CutoffSample d)
    {g : Vec d → Vec d} {Kg : ℝ}
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g) :
    H1Function (cubeSetAt y n) :=
  (exists_isDirichletSolutionAt_cutoff M m n y omega hg).choose

theorem isDirichletSolutionAt_solutionAt (M : ABKModel d) (m n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d} {Kg : ℝ}
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g) :
    IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n
      (solutionAt M m n y omega hg) g :=
  (exists_isDirichletSolutionAt_cutoff M m n y omega hg).choose_spec

/-! ## 2. The closed cube -/

/-- The closed cube of side `3^n` centred at `y`. -/
def closedCubeAt (y : Vec d) (n : ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - y i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n}

theorem cubeSetAt_subset_closedCubeAt (y : Vec d) (n : ℤ) :
    cubeSetAt y n ⊆ closedCubeAt y n := by
  intro x hx
  rw [mem_cubeSetAt_iff_forall_coord] at hx
  intro i
  have h := hx i
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem isClosed_closedCubeAt (y : Vec d) (n : ℤ) : IsClosed (closedCubeAt y n) := by
  have hrw : closedCubeAt y n =
      ⋂ i : Fin d, {x : Vec d | |x i - y i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n} := by
    ext x
    simp [closedCubeAt]
  rw [hrw]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le ((continuous_apply i).sub continuous_const).abs continuous_const

theorem isBounded_closedCubeAt (y : Vec d) (n : ℤ) :
    Bornology.IsBounded (closedCubeAt y n) := by
  refine (Metric.isBounded_closedBall (x := y) (r := (1 / 2 : ℝ) * (3 : ℝ) ^ n)).subset ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simpa [Real.norm_eq_abs] using hx i

theorem isCompact_closedCubeAt (y : Vec d) (n : ℤ) : IsCompact (closedCubeAt y n) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_closedCubeAt y n)
    (isBounded_closedCubeAt y n)

instance compactSpace_closedCubeAt (y : Vec d) (n : ℤ) :
    CompactSpace (closedCubeAt y n) :=
  isCompact_iff_compactSpace.1 (isCompact_closedCubeAt y n)

theorem exists_closedCubeAt_subset_openCubeSet (y : Vec d) (n : ℤ) :
    ∃ ell : ℤ, closedCubeAt y n ⊆ openCubeSet (originCube d ell) := by
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt (2 * ‖y‖ + (3 : ℝ) ^ n) (by norm_num : (1 : ℝ) < 3)
  refine ⟨(k : ℤ), fun x hx => ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h1 := abs_le.1 (hx i)
  have hyi : |y i| ≤ ‖y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hy := abs_le.1 hyi
  have hpow : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ k := zpow_natCast 3 k
  rw [hpow]
  constructor <;> linarith only [h1.1, h1.2, hy.1, hy.2, hk]

/-- The coordinatewise retraction onto the closed cube. -/
def clampTo (y : Vec d) (n : ℤ) (x : Vec d) : Vec d :=
  fun i => max (y i - (1 / 2 : ℝ) * (3 : ℝ) ^ n) (min (x i) (y i + (1 / 2 : ℝ) * (3 : ℝ) ^ n))

theorem continuous_clampTo (y : Vec d) (n : ℤ) : Continuous (clampTo y n) :=
  continuous_pi fun i =>
    (continuous_const.max ((continuous_apply i).min continuous_const))

theorem clampTo_mem (y : Vec d) (n : ℤ) (x : Vec d) : clampTo y n x ∈ closedCubeAt y n := by
  intro i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  rw [abs_le]
  constructor
  · have : y i - (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ clampTo y n x i := le_max_left _ _
    simp only [clampTo] at this ⊢
    linarith
  · have hmin : min (x i) (y i + (1 / 2 : ℝ) * (3 : ℝ) ^ n) ≤
        y i + (1 / 2 : ℝ) * (3 : ℝ) ^ n := min_le_right _ _
    have : clampTo y n x i ≤ y i + (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
      simp only [clampTo]
      exact max_le (by linarith) hmin
    simp only [clampTo] at this ⊢
    linarith

theorem clampTo_eq_self {y : Vec d} {n : ℤ} {x : Vec d} (hx : x ∈ closedCubeAt y n) :
    clampTo y n x = x := by
  funext i
  have h := abs_le.1 (hx i)
  simp only [clampTo]
  rw [min_eq_left (by linarith [h.2]), max_eq_right (by linarith [h.1])]

/-! ## 3. Evaluation by ball averages -/

/-- **A function continuous on an open set is the limit of its averages over
shrinking balls centred at a point of the set.** -/
theorem tendsto_setAverage_ball_of_continuousOn {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hcont : ContinuousOn f U) {x : Vec d} (hx : x ∈ U)
    {r : ℕ → ℝ} (hrpos : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => ⨍ z in Metric.ball x (r k), f z ∂volume) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have heps2 : (0 : ℝ) < eps / 2 := by linarith
  obtain ⟨delta1, hdelta1, hcont'⟩ :=
    Metric.continuousAt_iff.1 (hcont.continuousAt (hU.mem_nhds hx)) (eps / 2) heps2
  obtain ⟨delta2, hdelta2, hsub⟩ := Metric.isOpen_iff.1 hU x hx
  have hdelta : (0 : ℝ) < min delta1 delta2 := lt_min hdelta1 hdelta2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr0 (min delta1 delta2 / 2) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  have hrk : 0 < r k := hrpos k
  have hrk' : r k < min delta1 delta2 := by
    have hd := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_pos hrk] at hd
    linarith
  have hclosed : Metric.closedBall x (r k) ⊆ U := by
    refine subset_trans (fun z hz => ?_) hsub
    have : dist z x ≤ r k := Metric.mem_closedBall.1 hz
    exact Metric.mem_ball.2 (lt_of_le_of_lt this (lt_of_lt_of_le hrk' (min_le_right _ _)))
  have hballU : Metric.ball x (r k) ⊆ U :=
    subset_trans Metric.ball_subset_closedBall hclosed
  have hint : IntegrableOn f (Metric.ball x (r k)) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall x (r k))
      (hcont.mono hclosed)).mono_set Metric.ball_subset_closedBall
  have hpos : volume (Metric.ball x (r k)) ≠ 0 := (Metric.measure_ball_pos volume x hrk).ne'
  have htop : volume (Metric.ball x (r k)) ≠ ⊤ := measure_ball_lt_top.ne
  have hV : (0 : ℝ) < volume.real (Metric.ball x (r k)) := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_pos hpos htop
  have hsplit : ∫ z in Metric.ball x (r k), (f z - f x) ∂volume =
      (∫ z in Metric.ball x (r k), f z ∂volume) -
        volume.real (Metric.ball x (r k)) * f x := by
    rw [integral_sub hint (integrableOn_const htop), setIntegral_const, smul_eq_mul]
  have hbound : ∫ z in Metric.ball x (r k), |f z - f x| ∂volume ≤
      volume.real (Metric.ball x (r k)) * (eps / 2) := by
    have hmono : ∫ z in Metric.ball x (r k), |f z - f x| ∂volume ≤
        ∫ _z in Metric.ball x (r k), eps / 2 ∂volume := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
        (integrableOn_const htop) ?_
      refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall fun z hz => ?_)
      have hzx : dist z x < delta1 :=
        lt_of_lt_of_le (Metric.mem_ball.1 hz) (le_of_lt (lt_of_lt_of_le hrk' (min_le_left _ _)))
      have := hcont' hzx
      rw [Real.dist_eq] at this
      exact this.le
    rw [setIntegral_const, smul_eq_mul] at hmono
    exact hmono
  have habs : |∫ z in Metric.ball x (r k), (f z - f x) ∂volume| ≤
      volume.real (Metric.ball x (r k)) * (eps / 2) := by
    refine le_trans ?_ hbound
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Metric.ball x (r k)))
        (f := fun z => f z - f x)
  rw [Real.dist_eq, setAverage_eq, smul_eq_mul]
  have hrewrite : (volume.real (Metric.ball x (r k)))⁻¹ *
      (∫ z in Metric.ball x (r k), f z ∂volume) - f x =
      (volume.real (Metric.ball x (r k)))⁻¹ *
        ∫ z in Metric.ball x (r k), (f z - f x) ∂volume := by
    rw [hsplit]
    field_simp
  rw [hrewrite, abs_mul, abs_of_pos (inv_pos.2 hV)]
  have hfin : (volume.real (Metric.ball x (r k)))⁻¹ *
      |∫ z in Metric.ball x (r k), (f z - f x) ∂volume| ≤ eps / 2 := by
    have := mul_le_mul_of_nonneg_left habs (inv_pos.2 hV).le
    rw [← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul] at this
    exact this
  linarith

end

end Algsuperdiff.Section5.Support
