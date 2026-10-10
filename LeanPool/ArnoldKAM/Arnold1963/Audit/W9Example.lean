/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Main.GlobalCover
public import LeanPool.ArnoldKAM.Arnold1963.Audit.FundamentalExample
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
A one-dimensional cubic Hamiltonian on two separated domains near +1 and -1. Its Hessian
is nondegenerate on both branches, while their central frequencies agree. A nonconstant
perturbation exercises the global construction without global frequency injectivity.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W9Example
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- The cubic Hamiltonian whose frequency map agrees at the two branch centers. -/
def cubic (p : ComplexSpace 1) : ℂ := p 0 ^ 3 / 3

theorem cubic_analytic (p : ComplexSpace 1) : AnalyticAt ℂ cubic p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt p).pow 3
    |>.div analyticAt_const (by norm_num)

theorem cubic_fderiv (p : ComplexSpace 1) :
    fderiv ℂ cubic p = p 0 ^ 2 • ContinuousLinearMap.proj 0 := by
  let L : ComplexSpace 1 →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hd := ((L.hasFDerivAt (x := p)).pow 3).mul_const (3 : ℂ)⁻¹
  change HasFDerivAt (𝕜 := ℂ) cubic _ p at hd
  rw [hd.fderiv]
  ext v
  simp [L]
  ring

theorem cubic_frequency (p : ComplexSpace 1) :
    actionFrequency cubic p = fun _ => p 0 ^ 2 := by
  ext j
  simp [actionFrequency, cubic_fderiv, Fin.eq_zero j]

theorem cubic_second (p v w : ComplexSpace 1) :
    fderiv ℂ (fderiv ℂ cubic) p v w = 2 * p 0 * v 0 * w 0 := by
  let L : ComplexSpace 1 →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have he : fderiv ℂ cubic = fun p => p 0 ^ 2 • L := funext cubic_fderiv
  rw [he]
  have hd := ((L.hasFDerivAt (x := p)).pow 2).smul_const L
  change ((fderiv ℂ (fun p => L p ^ 2 • L) p) v) w = _
  rw [hd.fderiv]
  simp [L]

theorem cubic_hessian (p : ComplexSpace 1) : hessianDet cubic p = 2 * p 0 := by
  rw [hessianDet_eq_matrix (cubic_analytic p)]
  erw [Matrix.det_fin_one]
  simp [cubic_second]

/-- The one-dimensional real action vector with the specified value. -/
def center (a : ℝ) : RealSpace 1 := fun _ => a

/-- Two disjoint compact complex action balls around the two branch centers. -/
def ambient : Set (ComplexSpace 1) :=
  closedBall (complexify (center 1)) (1 / 4) ∪ closedBall (complexify (center (-1))) (1 / 4)

/-- The union of the corresponding open real action balls. -/
def realOpen : Set (RealSpace 1) :=
  ball (center 1) (1 / 4) ∪ ball (center (-1)) (1 / 4)

theorem ambient_conj : ConjInvariant ambient := by
  intro p hp
  change star p ∈ ambient
  rcases hp with hp | hp
  · apply Or.inl
    have hs : star (complexify (center 1)) = complexify (center 1) := conjVec_complexify _
    rw [mem_closedBall, ← hs, dist_star_star]
    exact hp
  · apply Or.inr
    have hs : star (complexify (center (-1))) = complexify (center (-1)) := conjVec_complexify _
    rw [mem_closedBall, ← hs, dist_star_star]
    exact hp

theorem realSlice_ambient : realSlice ambient =
    closedBall (center 1) (1 / 4) ∪ closedBall (center (-1)) (1 / 4) := by
  ext x
  simp only [realSlice, ambient, mem_preimage, mem_union, mem_closedBall,
    (isometry_complexify 1).dist_eq]

/-- The verified compact-domain and nondegeneracy hypotheses for the cubic example. -/
def cubicOriginalData : GlobalHamiltonianData 1 cubic ambient where
  dimension_pos := by norm_num
  compact := (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
  domain_conj := ambient_conj
  analytic := fun p _ => cubic_analytic p
  conj := by intro p _; simp [cubic, conjVec]
  realOpen := realOpen
  isOpen_realOpen := isOpen_ball.union isOpen_ball
  nonempty_realOpen := ⟨center 1, Or.inl (mem_ball_self (by norm_num))⟩
  closure_realOpen := by
    rw [realOpen, closure_union, closure_ball _ (by norm_num : (1 / 4 : ℝ) ≠ 0),
      closure_ball _ (by norm_num : (1 / 4 : ℝ) ≠ 0), realSlice_ambient]
  boundary_null := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ volume (frontier (ball (center 1) (1 / 4)) ∪
          frontier (ball (center (-1)) (1 / 4))) := measure_mono
        ((frontier_union_subset _ _).trans
          (union_subset_union inter_subset_left inter_subset_right))
      _ ≤ volume (frontier (ball (center 1) (1 / 4))) +
          volume (frontier (ball (center (-1)) (1 / 4))) := measure_union_le _ _
      _ = 0 := by rw [frontier_ball _ (by norm_num : (1 / 4 : ℝ) ≠ 0),
        frontier_ball _ (by norm_num : (1 / 4 : ℝ) ≠ 0),
        Measure.addHaar_sphere volume, Measure.addHaar_sphere volume, zero_add]
  complex_interior := by
    intro p hp
    have hb : complexify p ∈
        ball (complexify (center 1)) (1 / 4) ∪ ball (complexify (center (-1))) (1 / 4) := by
      simpa only [realOpen, mem_union, mem_ball, (isometry_complexify 1).dist_eq] using hp
    exact mem_interior.mpr ⟨_, union_subset_union ball_subset_closedBall ball_subset_closedBall,
      isOpen_ball.union isOpen_ball, hb⟩
  nondegenerate := by
    intro p hp
    rw [cubic_hessian]
    apply mul_ne_zero (by norm_num)
    intro he
    have hp0 : p 0 = 0 := by simpa only [complexify, Complex.ofReal_eq_zero] using he
    have hpzero : p = 0 := by ext j; simpa [Fin.eq_zero j] using hp0
    rw [hpzero] at hp
    change dist (0 : RealSpace 1) (fun _ => 1) < (1 / 4 : ℝ) ∨
      dist (0 : RealSpace 1) (fun _ => -1) < (1 / 4 : ℝ) at hp
    norm_num [dist_eq_norm, pi_norm_const] at hp

theorem frequency_not_injective : ¬ InjOn (actionFrequency cubic) ambient := by
  intro hi
  have he := hi (Or.inl (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 4)))
    (Or.inr (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 4)))
    (show actionFrequency cubic (complexify (center 1)) =
      actionFrequency cubic (complexify (center (-1))) by
        simp [cubic_frequency, center, complexify])
  have h0 := congrArg (fun p : ComplexSpace 1 => p 0) he
  norm_num [complexify, center] at h0

/-- A finite localization of the cubic example with width one and tolerance one half. -/
def localization : FiniteLocalization 1 cubic ambient 1 (1 / 2) :=
  Classical.choice (cubicOriginalData.exists_finiteLocalization (by norm_num) (by norm_num))

/-- The centered cosine perturbation restricted to the cubic example's ambient domain. -/
def perturbation : AnalyticPhaseFunction 1 ambient 1 :=
  (examplePerturbation 1 localization.threshold).restrict (subset_univ _) le_rfl ambient_conj

theorem perturbation_bound : perturbation.uniformNorm ≤ localization.threshold :=
  ((examplePerturbation 1 localization.threshold).uniformNorm_restrict_le _ _ _).trans
    (examplePerturbation_bound 1 localization.threshold_pos)

theorem nonconstant_on_initial_phase :
    ∃ z ∈ phaseDomain ambient 1, ∃ w ∈ phaseDomain ambient 1,
      perturbation.toFun z ≠ perturbation.toFun w := by
  refine ⟨(complexify (center 1), complexify (0 : RealSpace 1)),
    ⟨Or.inl (mem_closedBall_self (by norm_num)), complexify_mem_angleStrip _ _⟩,
    (complexify (center 1), complexify (fun _ : Fin 1 => Real.pi)),
    ⟨Or.inl (mem_closedBall_self (by norm_num)), complexify_mem_angleStrip _ _⟩, ?_⟩
  exact examplePerturbation_nonconstant 1 localization.threshold_pos (complexify (center 1))

theorem actual_bad_volume : volume (localization.badSet perturbation perturbation_bound) <
    ENNReal.ofReal (1 / 2 : ℝ) * volume localization.phase :=
  localization.badSet_volume_lt cubicOriginalData.compact perturbation perturbation_bound

theorem actual_good_volume_pos :
    0 < volume (localization.goodSet perturbation perturbation_bound) :=
  localization.goodSet_volume_pos perturbation perturbation_bound

end KamProject.Arnold1963.Audit.W9Example
