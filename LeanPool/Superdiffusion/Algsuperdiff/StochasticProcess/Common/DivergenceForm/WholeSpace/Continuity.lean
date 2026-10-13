/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Tail
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.RealResolvent
public import LeanPool.HighContrastHomogenization.Support.Sobolev.FiniteLpCoordinate

/-!
# Continuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Continuity of the analytic minimal resolvent

For square-integrable bounded data, the local Dirichlet resolvents have a
common interior Hölder modulus on each fixed ball.  Their monotone pointwise
supremum therefore has the same modulus.  Applying this argument to the
positive and negative parts gives continuity of the real minimal resolvent.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

omit [NeZero d] in
/-- The cubic exhaustion is monotone at arbitrary indices. -/
theorem wholeSpaceCube_mono {m n : ℕ} (hmn : m ≤ n) :
    wholeSpaceCube d m ⊆ wholeSpaceCube d n := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih => exact ih.trans (wholeSpaceCube_subset_succ d n)

omit [NeZero d] in
/-- Every fixed Euclidean ball is eventually contained in the cubic
exhaustion. -/
theorem exists_euclideanBall_subset_wholeSpaceCube (x : Vec d) {r : ℝ}
    (hr : 0 < r) : ∃ m, euclideanBall x r ⊆ wholeSpaceCube d m := by
  let C : ℝ := ∑ i, |x i| + r
  obtain ⟨m, hm⟩ := exists_nat_gt C
  refine ⟨m + 1, fun y hy => mem_wholeSpaceCube_iff.mpr fun i => ?_⟩
  have hcoord : |x i| ≤ ∑ j, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hyr : euclideanNorm (y - x) < r :=
    Decay.euclideanNorm_sub_lt_of_mem_euclideanBall hr.le hy
  have hycoord : |y i - x i| < r :=
    (HCPolySupport.abs_coordinate_le_euclideanNorm (y - x) i).trans_lt hyr
  have hyabs : |y i| < C := by
    have htri : |y i| ≤ |y i - x i| + |x i| := by
      calc
        |y i| = |(y i - x i) + x i| := by rw [sub_add_cancel]
        _ ≤ |y i - x i| + |x i| := abs_add_le _ _
    dsimp only [C]
    linarith only [htri, hycoord, hcoord]
  have hpowNat : m + 1 < 3 ^ (m + 1) := Nat.lt_pow_self (by norm_num)
  have hpow : C < (3 : ℝ) ^ (m + 1) := by
    have hm' : C < (m : ℝ) := hm
    have hcast : (m : ℝ) < (3 : ℝ) ^ (m + 1) := by
      exact_mod_cast (Nat.lt_trans (Nat.lt_succ_self m) hpowNat)
    exact hm'.trans hcast
  exact abs_lt.mp (hyabs.trans hpow)

omit [NeZero d] in
/-- Restricting a globally square-integrable bounded datum to one exhaustion
cube does not increase its `L²` norm. -/
theorem norm_cubeDatum_le {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (hfLp : MemLp f 2 volume) (m : ℕ) :
    ‖boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (hf.comp measurable_subtype_coe) (fun y => hfD y)‖ ≤
      (eLpNorm f 2 volume).toReal := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y => hfD y)
  have hFae : (fun y => F y) =ᵐ[volumeMeasureOn (wholeSpaceCube d m)] f := by
    filter_upwards [boundedMeasurableToScalarL2_coeFn hU
        (hf.comp measurable_subtype_coe) (fun y => hfD y),
      ae_restrict_mem hU.isOpen.measurableSet] with y hFy hy
    rw [hFy, domainExtension_of_mem hy]
    rfl
  change ‖F‖ ≤ _
  rw [Lp.norm_def, eLpNorm_congr_ae hFae]
  exact ENNReal.toReal_mono hfLp.eLpNorm_lt_top.ne
    (eLpNorm_mono_measure f (Measure.restrict_le_self))

omit [NeZero d] in
/-- A common Hölder bound on a pointwise bounded-above family is inherited by
its pointwise supremum. -/
theorem euclideanHolderBoundOn_iSup {W : Set (Vec d)} {alpha K : ℝ}
    {rep : ℕ → Vec d → ℝ}
    (hbdd : ∀ x ∈ W, BddAbove (Set.range fun n => rep n x))
    (h : ∀ n, EuclideanHolderBoundOn W alpha K (rep n)) :
    EuclideanHolderBoundOn W alpha K (fun x => ⨆ n, rep n x) := by
  have hone : ∀ x ∈ W, ∀ y ∈ W,
      (⨆ n, rep n x) - (⨆ n, rep n y) ≤
        K * euclideanNorm (x - y) ^ alpha := by
    intro x hx y hy
    have hle : ∀ n, rep n x ≤
        (⨆ m, rep m y) + K * euclideanNorm (x - y) ^ alpha := by
      intro n
      have h1 : rep n y ≤ ⨆ m, rep m y := le_ciSup (hbdd y hy) n
      have h2 := h n x hx y hy
      have h3 : rep n x - rep n y ≤
          K * euclideanNorm (x - y) ^ alpha := (le_abs_self _).trans h2
      linarith only [h1, h3]
    have := ciSup_le hle
    linarith only [this]
  intro x hx y hy
  have hxy := hone x hx y hy
  have hyx := hone y hy x hx
  have hsymm : euclideanNorm (y - x) = euclideanNorm (x - y) := by
    rw [show y - x = -(x - y) by ring, euclideanNorm_neg]
  rw [hsymm] at hyx
  rw [abs_le]
  exact ⟨by linarith only [hyx], hxy⟩

/-- Shifting the index of a bounded-above monotone real sequence does not
change its supremum. -/
theorem ciSup_nat_add_of_monotone {u : ℕ → ℝ} (hu : Monotone u)
    (hbdd : BddAbove (Set.range u)) (N : ℕ) :
    (⨆ k, u (k + N)) = ⨆ m, u m := by
  have hbddShift : BddAbove (Set.range fun k => u (k + N)) :=
    hbdd.mono (Set.range_comp_subset_range _ _)
  apply le_antisymm
  · exact ciSup_le fun k => le_ciSup hbdd (k + N)
  · refine ciSup_le fun m => ?_
    exact (hu (Nat.le_add_right m N)).trans (le_ciSup hbddShift m)

/-- The positive minimal resolvent preserves pointwise order. -/
theorem analyticMinimalResolvent_mono (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hfg : ∀ x, f x ≤ g x) (x : Vec d) :
    A.analyticMinimalResolvent mu f hf hfD x ≤
      A.analyticMinimalResolvent mu g hg hgE x := by
  unfold analyticMinimalResolvent
  exact iSup_mono fun m => ENNReal.ofReal_le_ofReal
    (A.analyticCubeResolvent_mono mu hf hg hfD hgE hfg m x)

/-- Nonnegative scalar multiplication commutes with the real value of the
positive minimal resolvent. -/
theorem toReal_analyticMinimalResolvent_smul (mu : PositiveShift) {c : ℝ}
    (hc : 0 ≤ c) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    (A.analyticMinimalResolvent mu (fun y => c * f y) (hf.const_smul c)
        (D := c * D) (fun y => by
          rw [abs_mul, abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left (hfD y) hc) x).toReal =
      c * (A.analyticMinimalResolvent mu f hf hfD x).toReal := by
  let hcf : ∀ y, |c * f y| ≤ c * D := fun y => by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hfD y) hc
  have htcf := A.tendsto_analyticCubeResolvent mu (hf.const_smul c)
    (fun y => mul_nonneg hc (hf0 y)) (mul_nonneg hc hD) hcf x
  have htf := (A.tendsto_analyticCubeResolvent mu hf hf0 hD hfD x).const_mul c
  apply tendsto_nhds_unique htcf
  apply htf.congr'
  filter_upwards with m
  exact A.analyticCubeResolvent_smul mu c hf hfD
    (fun y => by simpa only [abs_of_nonneg hc] using hcf y) m x |>.symm

/-- The real minimal resolvent is uniformly stable in the supremum norm,
with the sharp maximum-principle constant. -/
theorem abs_analyticMinimalResolventReal_sub_le (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E eps : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E)
    (hclose : ∀ x, |f x - g x| ≤ eps) (x : Vec d) :
    |A.analyticMinimalResolventReal mu f hf hfD x -
        A.analyticMinimalResolventReal mu g hg hgE x| ≤
      eps / (mu : ℝ) := by
  have hneg : ∀ y, |-g y| ≤ E := by
    intro y
    simpa only [abs_neg] using hgE y
  have hsum : ∀ y, |f y + -g y| ≤ D + E := by
    intro y
    exact (abs_add_le (f y) (-g y)).trans
      (add_le_add (hfD y) (hneg y))
  have hadd := A.analyticMinimalResolventReal_add mu hf hg.neg hfD hneg x
  have hsmul := A.analyticMinimalResolventReal_smul mu (-1) hg hgE x
  have hsmul' : A.analyticMinimalResolventReal mu (fun y ↦ -g y) hg.neg hneg x =
      -A.analyticMinimalResolventReal mu g hg hgE x := by
    simpa only [neg_mul, one_mul, abs_neg, abs_one] using hsmul
  have hsumEq :
      A.analyticMinimalResolventReal mu (fun y ↦ f y + -g y)
          (hf.add hg.neg) hsum x =
        A.analyticMinimalResolventReal mu (fun y ↦ f y - g y)
          (hf.sub hg) hclose x := by
    symm
    apply A.analyticMinimalResolventReal_bound_irrel mu (hf.sub hg) hclose
  have hstep : A.analyticMinimalResolventReal mu f hf hfD x -
      A.analyticMinimalResolventReal mu g hg hgE x =
      A.analyticMinimalResolventReal mu (fun y ↦ f y + -g y)
          (hf.add hg.neg) hsum x := by
    rw [sub_eq_add_neg, ← hsmul']
    exact hadd.symm
  calc
    |A.analyticMinimalResolventReal mu f hf hfD x -
        A.analyticMinimalResolventReal mu g hg hgE x| =
      |A.analyticMinimalResolventReal mu (fun y ↦ f y + -g y)
          (hf.add hg.neg) hsum x| := congrArg abs hstep
    _ = |A.analyticMinimalResolventReal mu (fun y ↦ f y - g y)
          (hf.sub hg) hclose x| := congrArg abs hsumEq
    _ ≤ eps / (mu : ℝ) :=
      A.abs_analyticMinimalResolventReal_le mu (hf.sub hg) hclose x

omit [NeZero d] in
private theorem matrixWeak_const_smul
    {W : Set (Vec d)} {c : ℝ} {a : CoeffField d}
    {u : H1Function W} {g : Vec d → ℝ}
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a W u g 0) :
    IsMatrixDivFormWeakSolutionZerothOrderOn
      (fun x ↦ c • a x) W u (fun x ↦ c * g x) 0 := by
  intro phi
  have h := hu phi
  have hl : (∫ x in W, vecDot (matVecMul (c • a x) (u.grad x))
      (phi.toH1Function.grad x) ∂volume) =
      c * ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
        (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    simp [smul_matVecMul, vecDot_smul_left]
  have hr : (∫ x in W, (c * g x) * phi.toH1Function.toFun x ∂volume) =
      c * ∫ x in W, g x * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [hl, hr]
  simpa only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero]
    using congrArg (c * ·) h

omit [NeZero d] in
private theorem scalarLInfSizeOn_const_mul
    {W : Set (Vec d)} {c : ℝ} {g : Vec d → ℝ} :
    scalarLInfSizeOn W (fun x ↦ c * g x) =
      |c| * scalarLInfSizeOn W g := by
  unfold scalarLInfSizeOn
  have heq : (fun x ↦ c * g x) = c • g := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [heq, eLpNorm_const_smul]
  rw [ENNReal.toReal_mul]
  rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg c)]

/-- At every point, a tail of the cubic exhaustion has one common local
`C^{0,1/2}` modulus.  The radius is obtained by freezing the continuous skew
part at that point; its size is unrestricted. -/
theorem exists_holderBound_cubeResolvent_tail (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (hfLp : MemLp f 2 volume) (x : Vec d) :
    ∃ r > 0, ∃ N K, ∀ k,
      EuclideanHolderBoundOn (euclideanBall x r) (1 / 2 : ℝ) K
        (A.analyticCubeResolvent mu f hf hfD (k + N)) := by
  let delta : ℝ := smallContrastThreshold d (1 / 2 : ℝ)
  have hdelta : 0 < delta := by
    unfold delta smallContrastThreshold
    positivity
  obtain ⟨R, hR, -, hsmall, hEllFrozen⟩ :=
    exists_ball_coefficientIdentityDistanceLE_normalizedFrozenCoeff
      isOpen_univ A.hnu A.hsymm A.hskewContinuous (Set.mem_univ x) hdelta
  obtain ⟨N, hBN⟩ := exists_euclideanBall_subset_wholeSpaceCube x hR
  let K : ℝ := smallContrastZerothSchauderConstant d *
    (R ^ (1 - (1 / 2 : ℝ) - (d : ℝ) / 2) *
        ((min (mu : ℝ) A.nu)⁻¹ *
          (eLpNorm f 2 volume).toReal) +
      R ^ (2 - (1 / 2 : ℝ)) * (A.nu⁻¹ * (2 * D)))
  refine ⟨R / 2, half_pos hR, N, K, fun k ↦ ?_⟩
  let m := k + N
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y ↦ hfD y)
  have hNm : N ≤ m := Nat.le_add_left N k
  have hBm : euclideanBall x R ⊆ wholeSpaceCube d m :=
    hBN.trans (wholeSpaceCube_mono hNm)
  have hFM : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m), |F y| ≤ D := by
    simpa only [F, hU, abs_of_nonneg hD] using
      abs_boundedMeasurableToScalarL2_le hU
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
  obtain ⟨z, g, hzvalue, hgmem, hgsize, hgrad, hzeq⟩ :=
    exists_interior_equation_alphaShifted_with_gradient A.a hU mu.property
      A.hnu (A.cubeEllipticity m) F hD hFM
      (isOpen_euclideanBall x R) hBm
  have hk : matTranspose (A.a x - A.nu • (1 : Mat d)) =
      -(A.a x - A.nu • (1 : Mat d)) :=
    sub_scalar_one_isSkew_of_symmPart_eq (A.hsymm x)
  have hfrozen : IsMatrixDivFormWeakSolutionZerothOrderOn
      (fun y ↦ A.a y - (A.a x - A.nu • (1 : Mat d)))
      (euclideanBall x R) z g 0 :=
    (isMatrixDivFormWeakSolutionZerothOrderOn_sub_skew_const_iff hk).2 hzeq
  have hnormalized : IsMatrixDivFormWeakSolutionZerothOrderOn
      (normalizedFrozenCoeff A.nu A.a x) (euclideanBall x R) z
      (fun y ↦ A.nu⁻¹ * g y) 0 := by
    simpa only [normalizedFrozenCoeff] using!
      matrixWeak_const_smul (c := A.nu⁻¹) hfrozen
  have hgscaled : MemScalarLInfOn (euclideanBall x R)
      (fun y ↦ A.nu⁻¹ * g y) := by
    have := hgmem.const_smul A.nu⁻¹
    simpa only [Pi.smul_apply, smul_eq_mul] using! this
  classical
  let aLocal : CoeffField d := fun y i j ↦
    if y ∈ euclideanBall x R then normalizedFrozenCoeff A.nu A.a x y i j else 0
  have hmeas : Measurable aLocal := by
    simpa only [aLocal] using! hEllFrozen.1
  have hsmallLocal : CoefficientIdentityDistanceLE
      (euclideanBall x R) aLocal delta := by
    filter_upwards [hsmall,
      ae_restrict_mem (isOpen_euclideanBall x R).measurableSet] with y hy hyB
    simpa only [aLocal, hyB, ite_true] using hy
  have hnormalizedLocal : IsMatrixDivFormWeakSolutionZerothOrderOn
      aLocal (euclideanBall x R) z (fun y ↦ A.nu⁻¹ * g y) 0 := by
    intro phi
    have h := hnormalized phi
    have hlhs :
        (∫ y in euclideanBall x R, vecDot (matVecMul (aLocal y) (z.grad y))
            (phi.toH1Function.grad y) ∂volume) =
          ∫ y in euclideanBall x R, vecDot
            (matVecMul (normalizedFrozenCoeff A.nu A.a x y) (z.grad y))
            (phi.toH1Function.grad y) ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (isOpen_euclideanBall x R).measurableSet]
        with y hy
      simp only [aLocal, hy, ite_true]
    rw [hlhs]
    exact h
  obtain ⟨v, hvcont, hvae, hvholder⟩ :=
    schauder_holder_euclideanBall_zerothOrder x hR A.hd
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1)
      hdelta.le le_rfl hmeas hsmallLocal hnormalizedLocal hgscaled
  have hanalytic := A.analyticCubeResolvent_ae mu hf hfD m
  have hhalf : euclideanBall x (R / 2) ⊆ wholeSpaceCube d m :=
    (euclideanBall_subset_euclideanBall (by positivity)
      (by linarith only [hR])).trans hBm
  have heq : Set.EqOn v (A.analyticCubeResolvent mu f hf hfD m)
      (euclideanBall x (R / 2)) := by
    refine eqOn_of_continuousOn_of_ae_eq (isOpen_euclideanBall x (R / 2))
      hvcont ((A.continuousOn_analyticCubeResolvent mu hf hfD m).mono hhalf) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (euclideanBall_subset_euclideanBall (by positivity)
          (by linarith only [hR])) hvae,
      ae_restrict_of_ae_restrict_of_subset
        (euclideanBall_subset_euclideanBall (by positivity)
          (by linarith only [hR])) hzvalue,
      ae_restrict_of_ae_restrict_of_subset hhalf hanalytic] with y hv hz ha
    rw [hv, hz, ha]
  have hnorm : ‖F‖ ≤ (eLpNorm f 2 volume).toReal := by
    simpa only [F, hU] using norm_cubeDatum_le hf hfD hfLp m
  have hgrad' : vectorLpSizeOn (euclideanBall x R) 2 z.grad ≤
      (min (mu : ℝ) A.nu)⁻¹ *
        (eLpNorm f 2 volume).toReal :=
    hgrad.trans (mul_le_mul_of_nonneg_left hnorm
      (inv_nonneg.mpr (le_min mu.property.le A.hnu.le)))
  have hgsize' : scalarLInfSizeOn (euclideanBall x R)
      (fun y ↦ A.nu⁻¹ * g y) ≤ A.nu⁻¹ * (2 * D) := by
    rw [scalarLInfSizeOn_const_mul, abs_of_pos (inv_pos.2 A.hnu)]
    exact mul_le_mul_of_nonneg_left hgsize (inv_nonneg.2 A.hnu.le)
  have hK : smallContrastZerothSchauderConstant d *
      (R ^ (1 - (1 / 2 : ℝ) - (d : ℝ) / 2) *
          vectorLpSizeOn (euclideanBall x R) 2 z.grad +
        R ^ (2 - (1 / 2 : ℝ)) *
          scalarLInfSizeOn (euclideanBall x R) (fun y ↦ A.nu⁻¹ * g y)) ≤ K := by
    unfold K
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
      (smallContrastZerothSchauderConstant_nonneg d)
    · exact mul_le_mul_of_nonneg_left hgrad' (Real.rpow_nonneg hR.le _)
    · exact mul_le_mul_of_nonneg_left hgsize' (Real.rpow_nonneg hR.le _)
  intro y hy z' hz'
  rw [← heq hy, ← heq hz']
  exact (hvholder y hy z' hz').trans
    (mul_le_mul_of_nonneg_right hK
      (Real.rpow_nonneg (euclideanNorm_nonneg _) _))

/-- For nonnegative globally square-integrable data, the real value of the
minimal resolvent has a local Hölder bound at every point. -/
theorem locally_holder_analyticMinimalResolvent (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (hfLp : MemLp f 2 volume) (x : Vec d) :
    ∃ r > 0, ∃ K, EuclideanHolderBoundOn (euclideanBall x r) (1 / 2 : ℝ) K
      (fun y => (A.analyticMinimalResolvent mu f hf hfD y).toReal) := by
  obtain ⟨r, hr, N, K, htail⟩ :=
    A.exists_holderBound_cubeResolvent_tail mu hf hD hfD hfLp x
  refine ⟨r, hr, K, ?_⟩
  have hbdd' : ∀ y ∈ euclideanBall x r,
      BddAbove (Set.range fun k ↦
        A.analyticCubeResolvent mu f hf hfD (k + N) y) := by
    intro y _
    refine ⟨D / (mu : ℝ), ?_⟩
    rintro z ⟨k, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le mu hf hD hfD (k + N) y)
  have hsup := euclideanHolderBoundOn_iSup hbdd' htail
  have hshift : (fun y => ⨆ k,
      A.analyticCubeResolvent mu f hf hfD (k + N) y) =
      fun y => ⨆ m, A.analyticCubeResolvent mu f hf hfD m y := by
    funext y
    exact ciSup_nat_add_of_monotone
      (A.monotone_analyticCubeResolvent mu hf hf0 hfD y)
      (by
        refine ⟨D / (mu : ℝ), ?_⟩
        rintro z ⟨m, rfl⟩
        exact (le_abs_self _).trans
          (A.abs_analyticCubeResolvent_le mu hf hD hfD m y)) N
  have hreal : (fun y => ⨆ m,
      A.analyticCubeResolvent mu f hf hfD m y) =
      fun y => (A.analyticMinimalResolvent mu f hf hfD y).toReal := by
    funext y
    have ht := A.tendsto_analyticCubeResolvent mu hf hf0 hD hfD y
    exact tendsto_nhds_unique (tendsto_atTop_ciSup (A.monotone_analyticCubeResolvent
      mu hf hf0 hfD y) (by
        refine ⟨D / (mu : ℝ), ?_⟩
        rintro z ⟨m, rfl⟩
        exact (le_abs_self _).trans
          (A.abs_analyticCubeResolvent_le mu hf hD hfD m y))) ht
  simpa only [hshift, hreal] using hsup

/-- The real analytic minimal resolvent is continuous for every bounded
measurable datum which is globally square-integrable. -/
theorem continuous_analyticMinimalResolventReal_of_memLp (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (hfLp : MemLp f 2 volume) :
    Continuous (A.analyticMinimalResolventReal mu f hf hfD) := by
  let fp : Vec d → ℝ := analyticPositivePart f
  let fn : Vec d → ℝ := analyticPositivePart fun y => -f y
  have hfpmeas : Measurable fp := measurable_analyticPositivePart hf
  have hfnmeas : Measurable fn := measurable_analyticPositivePart hf.neg
  have hfp0 : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfn0 : ∀ x, 0 ≤ fn x := fun x => le_max_right _ _
  have hfpD : ∀ x, |fp x| ≤ D := by
    intro x
    have hpart : 0 ≤ fp x := hfp0 x
    rw [abs_of_nonneg hpart]
    exact max_le ((le_abs_self (f x)).trans (hfD x)) hD
  have hfnD : ∀ x, |fn x| ≤ D := by
    intro x
    have hpart : 0 ≤ fn x := hfn0 x
    rw [abs_of_nonneg hpart]
    exact max_le ((le_abs_self (-f x)).trans (by simpa using hfD x)) hD
  have hfpLp : MemLp fp 2 volume := by
    refine hfLp.mono hfpmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hfp0 x)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hfnLp : MemLp fn 2 volume := by
    refine hfLp.mono hfnmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hfn0 x)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨rp, hrp, Kp, hp⟩ := A.locally_holder_analyticMinimalResolvent mu hfpmeas
    hfp0 hD hfpD hfpLp x
  obtain ⟨rn, hrn, Kn, hn⟩ := A.locally_holder_analyticMinimalResolvent mu hfnmeas
    hfn0 hD hfnD hfnLp x
  have hxp : x ∈ euclideanBall x rp := center_mem_euclideanBall x hrp
  have hxn : x ∈ euclideanBall x rn := center_mem_euclideanBall x hrn
  have hpcont := continuousOn_of_euclideanHolderBoundOn
    (by norm_num : (0 : ℝ) < 1 / 2) hp
  have hncont := continuousOn_of_euclideanHolderBoundOn
    (by norm_num : (0 : ℝ) < 1 / 2) hn
  change ContinuousAt (fun y =>
    (A.analyticMinimalResolvent mu fp hfpmeas hfpD y).toReal -
      (A.analyticMinimalResolvent mu fn hfnmeas hfnD y).toReal) x
  exact (hpcont.continuousAt ((isOpen_euclideanBall x rp).mem_nhds hxp)).sub
    (hncont.continuousAt ((isOpen_euclideanBall x rn).mem_nhds hxn))

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
