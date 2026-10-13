/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableResolvent
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorHolderConstant

/-!
# BoundedMeasurableLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Continuity of the interior representative of the resolvent along uniformly
bounded pointwise convergent data.
-/

/-!
# Bounded pointwise limits of the analytic resolvent

The analytic side of the comparison between the process resolvent and the
resolvent of the divergence-form operator has to be continuous along
uniformly bounded pointwise convergent data, at **every** point of the domain.

That does not follow from the interior Hölder estimate alone, because the
`L^∞` part of its data size does not tend to zero.  What is used instead is
the mean-plus-oscillation bound

`|w x₀| ≤ |⨍_{B ρ} w| + K ρ ^ alpha`,

with `K` the Hölder constant of the interior estimate, uniform along the
sequence, and with the mean controlled by the `L²` norm through Cauchy–Schwarz:
`|⨍_{B ρ} w| ≤ ‖w‖_{L²} / √(volume (B ρ))`.  Letting the index go to infinity
at fixed `ρ` and then `ρ → 0` gives the convergence.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-! ## `L²` convergence from uniformly bounded pointwise convergence -/

/-- On a bounded domain, uniformly bounded almost everywhere pointwise
convergence implies convergence in `L²`. -/
theorem tendsto_norm_scalarL2_sub_of_bounded_ae_tendsto
    (hU : IsOpenBoundedConvexDomain U) {F : ℕ → ScalarL2 U} {G : ScalarL2 U}
    {C : ℝ} (hbd : ∀ᵐ x ∂volumeMeasureOn U, ∀ k, |F k x - G x| ≤ C)
    (hpt : ∀ᵐ x ∂volumeMeasureOn U,
      Tendsto (fun k => F k x) atTop (nhds (G x))) :
    Tendsto (fun k => ‖F k - G‖) atTop (nhds 0) := by
  let := hU.isFiniteMeasure_restrict_volume
  have hsq : ∀ k, ‖F k - G‖ ^ 2 =
      ∫ x, (F k x - G x) ^ 2 ∂volumeMeasureOn U := by
    intro k
    have hinner : ‖F k - G‖ ^ 2 = inner ℝ (F k - G) (F k - G) :=
      (real_inner_self_eq_norm_sq (F k - G)).symm
    rw [hinner, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (F k) G] with x hx
    rw [hx]
    simp [pow_two]
  have hzero : Tendsto (fun k => ∫ x, (F k x - G x) ^ 2 ∂volumeMeasureOn U)
      atTop (nhds 0) := by
    have hmeas : ∀ k, AEStronglyMeasurable
        (fun x => (F k x - G x) ^ 2) (volumeMeasureOn U) := fun k =>
      (((Lp.aestronglyMeasurable (F k)).sub (Lp.aestronglyMeasurable G)).pow 2)
    have hbound : ∀ k, ∀ᵐ x ∂volumeMeasureOn U,
        ‖(F k x - G x) ^ 2‖ ≤ C ^ 2 := by
      intro k
      filter_upwards [hbd] with x hx
      have h := hx k
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hlim : ∀ᵐ x ∂volumeMeasureOn U,
        Tendsto (fun k => (F k x - G x) ^ 2) atTop (nhds 0) := by
      filter_upwards [hpt] with x hx
      have hsub : Tendsto (fun k => F k x - G x) atTop (nhds 0) := by
        simpa using hx.sub (tendsto_const_nhds (x := (G : Vec d → ℝ) x))
      simpa using hsub.pow 2
    have := tendsto_integral_of_dominated_convergence (fun _ => C ^ 2) hmeas
      (integrable_const _) hbound hlim
    simpa using this
  have hcomp : Tendsto
      (fun k => Real.sqrt (∫ x, (F k x - G x) ^ 2 ∂volumeMeasureOn U))
      atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hzero
    simpa [Function.comp_def] using this
  have heq : (fun k => Real.sqrt (∫ x, (F k x - G x) ^ 2 ∂volumeMeasureOn U)) =
      fun k => ‖F k - G‖ := by
    funext k
    rw [← hsq k, Real.sqrt_sq (norm_nonneg _)]
  rwa [heq] at hcomp

/-! ## The mean-plus-oscillation bound -/

private theorem abs_average_sub_const_le_of_ae {mu : Measure (Vec d)}
    [IsFiniteMeasure mu] (hmu : mu ≠ 0) {f : Vec d → ℝ} (hf : Integrable f mu)
    {c C : ℝ} (hC : ∀ᵐ y ∂mu, |f y - c| ≤ C) :
    |(⨍ y, f y ∂mu) - c| ≤ C := by
  have : NeZero mu := ⟨hmu⟩
  have huniv : mu Set.univ ≠ 0 := by
    simpa [Measure.measure_univ_eq_zero] using hmu
  have hpos : 0 < mu.real Set.univ := by
    rw [Measure.real]
    exact ENNReal.toReal_pos huniv (measure_ne_top mu Set.univ)
  have hconst : (⨍ _y : Vec d, c ∂mu) = c := average_const mu c
  have hsub : (⨍ y, f y ∂mu) - c = ⨍ y, (f y - c) ∂mu := by
    conv_lhs => rw [← hconst]
    rw [average_eq, average_eq, average_eq, ← smul_sub,
      ← integral_sub hf (integrable_const c)]
  have hbd : ‖∫ y, (f y - c) ∂mu‖ ≤ C * mu.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hC] with y hy
    simpa using hy
  rw [hsub, average_eq, smul_eq_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc
    (mu.real Set.univ)⁻¹ * |∫ y, (f y - c) ∂mu|
        ≤ (mu.real Set.univ)⁻¹ * (C * mu.real Set.univ) :=
          mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hpos.le)
    _ = C := by field_simp

/-- Cauchy–Schwarz: the integral of an `L²` class over a subset of the domain
is controlled by its norm times the square root of the volume. -/
theorem abs_setIntegral_le_norm_mul_sqrt
    {B : Set (Vec d)} (hB : MeasurableSet B) (hBU : B ⊆ U)
    (hBtop : volume B ≠ ⊤) (G : ScalarL2 U) :
    |∫ y in B, G y ∂volume| ≤ ‖G‖ * Real.sqrt (volume B).toReal := by
  have hmeasB : volumeMeasureOn U B = volume B := by
    rw [Measure.restrict_apply hB, Set.inter_eq_self_of_subset_left hBU]
  have hne : volumeMeasureOn U B ≠ ⊤ := by rw [hmeasB]; exact hBtop
  set chi : ScalarL2 U := indicatorConstLp 2 hB hne (1 : ℝ) with hchi
  have hnormchi : ‖chi‖ = Real.sqrt (volume B).toReal := by
    rw [hchi, norm_indicatorConstLp (by norm_num) (by norm_num)]
    rw [Measure.real, hmeasB, Real.sqrt_eq_rpow]
    simp
  have hinner : inner ℝ G chi = ∫ y in B, G y ∂volume := by
    rw [L2.inner_def]
    have hfun : ∫ x, (inner ℝ (G x) (chi x) : ℝ) ∂volumeMeasureOn U =
        ∫ x, B.indicator (fun y => (G : Vec d → ℝ) y) x ∂volumeMeasureOn U := by
      refine integral_congr_ae ?_
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hB)
        (hμs := hne) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hxB : x ∈ B
      · simp [hxB]
      · simp [hxB]
    rw [hfun, integral_indicator hB, Measure.restrict_restrict hB,
      Set.inter_eq_self_of_subset_left hBU]
  rw [← hinner]
  calc |inner ℝ G chi| ≤ ‖G‖ * ‖chi‖ := abs_real_inner_le_norm G chi
    _ = ‖G‖ * Real.sqrt (volume B).toReal := by rw [hnormchi]

/-- Mean-plus-oscillation bound: a function continuous on the domain,
representing an `L²` class and Hölder on a ball, is controlled at the centre
of that ball by the `L²` norm and the Hölder constant. -/
theorem abs_representative_le_of_holder (G : ScalarL2 U)
    {w : Vec d → ℝ} (hwae : w =ᵐ[volumeMeasureOn U] G)
    {x₀ : Vec d} {rho K alpha : ℝ} (hrho : 0 < rho) (hK : 0 ≤ K)
    (halpha : 0 ≤ alpha) (hball : euclideanBall x₀ rho ⊆ U)
    (hholder : EuclideanHolderBoundOn (euclideanBall x₀ rho) alpha K w) :
    |w x₀| ≤ ‖G‖ / Real.sqrt (volume (euclideanBall x₀ rho)).toReal +
      K * rho ^ alpha := by
  set B : Set (Vec d) := euclideanBall x₀ rho with hBdef
  have hBopen : IsOpen B := isOpen_euclideanBall x₀ rho
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hBne : B.Nonempty := ⟨x₀, center_mem_euclideanBall x₀ hrho⟩
  have hBfin : IsFiniteMeasure (volume.restrict B) :=
    HCPolySupport.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall x₀ rho
  have hBtop : volume B ≠ ⊤ := by
    have hlt := hBfin.measure_univ_lt_top
    rw [Measure.restrict_apply_univ] at hlt
    exact hlt.ne
  have hBpos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos (hBopen.measure_pos volume hBne).ne' hBtop
  have hsqrtpos : 0 < Real.sqrt (volume B).toReal := Real.sqrt_pos.2 hBpos
  have haeB : w =ᵐ[volume.restrict B] (G : Vec d → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hball hwae
  have hmemB : MemLp w 2 (volume.restrict B) :=
    ((Lp.memLp G).mono_measure (Measure.restrict_mono hball le_rfl)).ae_eq
      haeB.symm
  have hintB : Integrable w (volume.restrict B) :=
    hmemB.integrable (by norm_num)
  have hnezero : volume.restrict B ≠ 0 := by
    intro hzero
    have hval : (volume.restrict B) B = 0 := by rw [hzero]; rfl
    rw [Measure.restrict_apply_self] at hval
    exact (hBopen.measure_pos volume hBne).ne' hval
  have hosc : |(⨍ y in B, w y ∂volume) - w x₀| ≤ K * rho ^ alpha := by
    refine abs_average_sub_const_le_of_ae hnezero hintB ?_
    filter_upwards [ae_restrict_mem hBmeas] with y hy
    refine (hholder y hy x₀ (center_mem_euclideanBall x₀ hrho)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    have hy' : euclideanSqDist y x₀ < rho ^ 2 := hy
    have hsq : euclideanNorm (y - x₀) ^ 2 ≤ rho ^ 2 := by
      rw [euclideanNorm_sq]
      exact le_of_lt hy'
    have hle : euclideanNorm (y - x₀) ≤ rho := by
      have hs := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (euclideanNorm_nonneg _), Real.sqrt_sq hrho.le] at hs
    exact Real.rpow_le_rpow (euclideanNorm_nonneg _) hle halpha
  have hmean : |⨍ y in B, w y ∂volume| ≤
      ‖G‖ / Real.sqrt (volume B).toReal := by
    have hcongr : ∫ y in B, w y ∂volume = ∫ y in B, (G : Vec d → ℝ) y ∂volume :=
      integral_congr_ae haeB
    have hcs := abs_setIntegral_le_norm_mul_sqrt hBmeas hball hBtop G
    have hsq : Real.sqrt (volume B).toReal * Real.sqrt (volume B).toReal =
        (volume B).toReal := Real.mul_self_sqrt hBpos.le
    rw [setAverage_eq, smul_eq_mul, abs_mul, measureReal_def, hcongr,
      abs_of_nonneg (inv_nonneg.mpr hBpos.le)]
    calc ((volume B).toReal)⁻¹ * |∫ y in B, (G : Vec d → ℝ) y ∂volume|
        ≤ ((volume B).toReal)⁻¹ * (‖G‖ * Real.sqrt (volume B).toReal) :=
          mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hBpos.le)
      _ = ‖G‖ / Real.sqrt (volume B).toReal := by
          have harith : ∀ t g : ℝ, 0 < t → (t * t)⁻¹ * (g * t) = g / t := by
            intro t g ht
            field_simp
          have h := harith (Real.sqrt (volume B).toReal) ‖G‖ hsqrtpos
          rw [hsq] at h
          exact h
  have hsplit : |w x₀| ≤ |⨍ y in B, w y ∂volume| +
      |(⨍ y in B, w y ∂volume) - w x₀| := by
    have hrewrite : w x₀ =
        (⨍ y in B, w y ∂volume) + -((⨍ y in B, w y ∂volume) - w x₀) := by ring
    calc |w x₀| = |(⨍ y in B, w y ∂volume) +
            -((⨍ y in B, w y ∂volume) - w x₀)| := by rw [← hrewrite]
      _ ≤ |⨍ y in B, w y ∂volume| + |-((⨍ y in B, w y ∂volume) - w x₀)| :=
          abs_add_le _ _
      _ = |⨍ y in B, w y ∂volume| + |(⨍ y in B, w y ∂volume) - w x₀| := by
          rw [abs_neg]
  exact hsplit.trans (add_le_add hmean hosc)

/-! ## The interior estimate for bounded data -/

/-- The interior equation for the `α`-shifted problem together with the bounds
on its data. -/
theorem exists_interior_equation_alphaShifted_with_gradient
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (F : ScalarL2 U) {M : ℝ} (hM : 0 ≤ M)
    (hFM : ∀ᵐ x ∂volumeMeasureOn U, |F x| ≤ M)
    {W : Set (Vec d)} (hW : IsOpen W) (hWU : W ⊆ U) :
    ∃ z : H1Function W, ∃ g : Vec d → ℝ,
      z.toFun =ᵐ[volume.restrict W] alphaShiftedResolvent a hα hlam hEll F ∧
      MemScalarLInfOn W g ∧
      scalarLInfSizeOn W g ≤ 2 * M ∧
      vectorLpSizeOn W 2 z.grad ≤ (min α lam)⁻¹ * ‖F‖ ∧
      IsMatrixDivFormWeakSolutionZerothOrderOn a W z g 0  := by
  have hq : IsBoundedNonnegativePotential U (fun _ => (0 : ℝ)) 0 :=
    isBoundedNonnegativePotential_zero U
  set u : ZeroTraceSobolev U := alphaShiftedSolution a hα hlam hEll F with hudef
  have hu : IsPotentialWeakSolution a α (fun _ => (0 : ℝ)) U u F := by
    have h := potentialSolution_isPotentialWeakSolution a hα hlam hEll
      (fun _ => (0 : ℝ)) hq F
    rwa [potentialSolution_zero_potential a hα hlam hEll hq F] at h
  obtain ⟨w, hwvalue, hwgrad⟩ := ZeroTraceSobolev.exists_h10Function hU u
  have hgvalue : (fun x => interiorScalarSource α (fun _ => (0 : ℝ)) hq F u x)
      =ᵐ[volume.restrict W]
      fun x => F x - α * ZeroTraceSobolev.toL2 u x -
        (0 : ℝ) * ZeroTraceSobolev.toL2 u x :=
    ae_restrict_of_ae_restrict_of_subset hWU
      (interiorScalarSource_coeFn α (fun _ => (0 : ℝ)) hq F u)
  have habs : ∀ᵐ x ∂volumeMeasureOn U,
      |α * ZeroTraceSobolev.toL2 u x| ≤ M :=
    abs_alpha_mul_alphaShiftedResolvent_le_ae a hU hα hlam hEll F M hM hFM
  have hbound : ∀ᵐ x ∂volume.restrict W,
      |interiorScalarSource α (fun _ => (0 : ℝ)) hq F u x| ≤ 2 * M := by
    filter_upwards [hgvalue,
      ae_restrict_of_ae_restrict_of_subset hWU hFM,
      ae_restrict_of_ae_restrict_of_subset hWU habs] with x hg hf hau
    rw [hg, zero_mul, sub_zero]
    have hrewrite : F x - α * ZeroTraceSobolev.toL2 u x =
        F x + -(α * ZeroTraceSobolev.toL2 u x) := by ring
    rw [hrewrite]
    calc |F x + -(α * ZeroTraceSobolev.toL2 u x)|
        ≤ |F x| + |-(α * ZeroTraceSobolev.toL2 u x)| := abs_add_le _ _
      _ = |F x| + |α * ZeroTraceSobolev.toL2 u x| := by rw [abs_neg]
      _ ≤ M + M := add_le_add hf hau
      _ = 2 * M := by ring
  have hmeas : AEStronglyMeasurable
      (fun x => interiorScalarSource α (fun _ => (0 : ℝ)) hq F u x)
      (volume.restrict W) :=
    (Lp.aestronglyMeasurable
      (interiorScalarSource α (fun _ => (0 : ℝ)) hq F u)).mono_measure
      (Measure.restrict_mono hWU le_rfl)
  obtain ⟨hmem, hsize⟩ := memScalarLInfOn_of_ae_bound
    (by positivity) hmeas hbound
  refine ⟨w.toH1Function.restrict hW hWU,
    fun x => interiorScalarSource α (fun _ => (0 : ℝ)) hq F u x,
    ?_, hmem, hsize, ?_, ?_⟩
  · have hres : ZeroTraceSobolev.toL2 u = alphaShiftedResolvent a hα hlam hEll F :=
      rfl
    rw [← hres]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWU
      w.toH1Function.coeFn_toScalarL2] with x hx
    rw [← hwvalue]
    exact hx.symm
  · have hgrad := vectorLpSizeOn_grad_le_norm_gradToHilbertVectorL2
      (U := U) hWU w.toH1Function
    rw [hwgrad] at hgrad
    exact hgrad.trans ((ZeroTraceSobolev.norm_gradient_le u).trans
      (norm_alphaShiftedSolution_apply_le a hα hlam hEll F))
  · exact isMatrixDivFormWeakSolutionZerothOrderOn_restrict hU.isOpen hW hWU
      (isMatrixDivFormWeakSolutionZerothOrderOn_domain_of_isPotentialWeakSolution
        a (fun _ => (0 : ℝ)) hq F hu w hwgrad)

theorem penalizationInteriorHolderConstant_mono_gradient (d : ℕ)
    (alpha : ℝ) {r : ℝ} (hr : 0 ≤ r) (M : ℝ) {G G' : ℝ} (h : G ≤ G') :
    penalizationInteriorHolderConstant d alpha r G M ≤
      penalizationInteriorHolderConstant d alpha r G' M  := by
  have h2r : (0 : ℝ) ≤ 2 * r := by linarith only [hr]
  unfold penalizationInteriorHolderConstant
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg h2r _)) le_rfl)
    (smallContrastZerothSchauderConstant_nonneg d)

/-! ## Continuity of the interior representative along bounded limits -/

theorem penalizationInteriorHolderConstant_nonneg (d : ℕ)
    (alpha : ℝ) {r G M : ℝ} (hr : 0 ≤ r) (hG : 0 ≤ G) (hM : 0 ≤ M) :
    0 ≤ penalizationInteriorHolderConstant d alpha r G M  := by
  have h2r : (0 : ℝ) ≤ 2 * r := by linarith only [hr]
  unfold penalizationInteriorHolderConstant
  have h1 : (0 : ℝ) ≤ (2 * r) ^ (1 - alpha - (d : ℝ) / 2) * G :=
    mul_nonneg (Real.rpow_nonneg h2r _) hG
  have h2 : (0 : ℝ) ≤ (2 * r) ^ (2 - alpha) * (2 * M) :=
    mul_nonneg (Real.rpow_nonneg h2r _) (by linarith only [hM])
  exact mul_nonneg (smallContrastZerothSchauderConstant_nonneg d)
    (by linarith only [h1, h2])

/-! ## The quantitative interior witness -/

open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing in
/-- **The freezing route to the quantitative witness.**  For a coefficient with
symmetric part `nu • 1` and continuous skew part of arbitrary size, the frozen
radius at a point serves every bounded datum, and the constant is the same
Schauder constant with the forcing budget scaled by `nu⁻¹`. -/
theorem hasLocalHolderShiftedResolvents_continuousCoeff [NeZero d] (hd : 2 ≤ d)
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {nu : ℝ} (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) U)
    {lam Lam : ℝ} (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a) :
    HasLocalHolderShiftedResolvents a hlam hEll (1 / 2 : ℝ) nu⁻¹ := by
  refine ⟨hasContinuousShiftedResolvents_continuousCoeff hd a hU hnu hsymm hcont
    hlam hEll, ?_⟩
  intro mu hmu x hx M hM
  obtain ⟨s, hs, hsU, hbound⟩ :=
    exists_frozenRadius_holder_of_continuousCoeff hd hU.isOpen hnu hsymm hcont hx
  have hsub : euclideanBall x (s / 2) ⊆ euclideanBall x s :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith only [hs])
  refine ⟨s / 2, half_pos hs, hsub.trans hsU, ?_⟩
  intro f hfM v hvcont hvae
  obtain ⟨z, g, hzvalue, hgmem, hgsize, hgradsize, hzeq⟩ :=
    exists_interior_equation_alphaShifted_with_gradient a hU hmu hlam hEll f hM
      hfM (isOpen_euclideanBall x s) hsU
  obtain ⟨y0, hy0cont, hy0ae, hy0holder⟩ :=
    hbound ((min mu lam)⁻¹ * ‖f‖) M z g hgmem hgsize hgradsize hzeq
  have heq : Set.EqOn v y0 (euclideanBall x (s / 2)) := by
    refine eqOn_of_continuousOn_of_ae_eq (isOpen_euclideanBall x (s / 2))
      hvcont hy0cont ?_
    filter_upwards [hvae, ae_restrict_of_ae_restrict_of_subset hsub hy0ae,
      ae_restrict_of_ae_restrict_of_subset hsub hzvalue] with p h1 h2 h3
    rw [h1, h2, h3]
  intro p hp q hq
  rw [heq hp, heq hq]
  exact hy0holder p hp q hq

/-- **The analytic side is continuous along uniformly bounded `L²`-convergent
data, at every point of the domain.**  The `L²` norm controls the mean of the
difference over a small ball and the quantitative interior witness controls its
oscillation there, with a constant that stays bounded along the sequence. -/
theorem tendsto_representative_of_tendsto_norm_reg
    (a : CoeffField d) {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {alpha B : ℝ} (halpha0 : 0 < alpha) (hB : 0 ≤ B)
    (hReg : HasLocalHolderShiftedResolvents a hlam hEll alpha B)
    {F : ℕ → ScalarL2 U} {Fl : ScalarL2 U} {M : ℝ} (hM : 0 ≤ M)
    (hFM : ∀ k, ∀ᵐ y ∂volumeMeasureOn U, |F k y - Fl y| ≤ M)
    (hL2 : Tendsto (fun k => ‖F k - Fl‖) atTop (nhds 0))
    {wk : ℕ → Vec d → ℝ} {w : Vec d → ℝ}
    (hwkcont : ∀ k, ContinuousOn (wk k) U)
    (hwkae : ∀ k, wk k =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a hα hlam hEll (F k))
    (hwcont : ContinuousOn w U)
    (hwae : w =ᵐ[volumeMeasureOn U] alphaShiftedResolvent a hα hlam hEll Fl)
    {x : Vec d} (hx : x ∈ U) :
    Tendsto (fun k => wk k x) atTop (nhds (w x))  := by
  have hBM : (0 : ℝ) ≤ B * M := mul_nonneg hB hM
  obtain ⟨r, hr, hballr, hbound⟩ := hReg.2 hα x hx hM
  have hFdiff : ∀ k, ∀ᵐ y ∂volumeMeasureOn U, |(F k - Fl) y| ≤ M := by
    intro k
    filter_upwards [hFM k, Lp.coeFn_sub (F k) Fl] with y hbd hsub
    rw [hsub, Pi.sub_apply]
    exact hbd
  have hDae : ∀ k, (fun y => wk k y - w y) =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a hα hlam hEll (F k - Fl) := by
    intro k
    have hlin : alphaShiftedResolvent a hα hlam hEll (F k - Fl) =
        alphaShiftedResolvent a hα hlam hEll (F k) -
          alphaShiftedResolvent a hα hlam hEll Fl := by
      rw [map_sub]
    rw [hlin]
    filter_upwards [hwkae k, hwae,
      Lp.coeFn_sub (alphaShiftedResolvent a hα hlam hEll (F k))
        (alphaShiftedResolvent a hα hlam hEll Fl)] with y h1 h2 h3
    rw [h1, h2, h3, Pi.sub_apply]
  have hholder : ∀ k, EuclideanHolderBoundOn (euclideanBall x r) alpha
      (penalizationInteriorHolderConstant d alpha r
        ((min α lam)⁻¹ * ‖F k - Fl‖) (B * M)) (fun y => wk k y - w y) := by
    intro k
    exact hbound (F k - Fl) (hFdiff k) (fun y => wk k y - w y)
      (((hwkcont k).mono hballr).sub (hwcont.mono hballr))
      (ae_restrict_of_ae_restrict_of_subset hballr (hDae k))
  -- the quantitative bound
  have hquant : ∀ (k : ℕ) (rho : ℝ), 0 < rho → rho < r →
      |wk k x - w x| ≤
        (α⁻¹ * ‖F k - Fl‖) /
            Real.sqrt (volume (euclideanBall x rho)).toReal +
          penalizationInteriorHolderConstant d alpha r
            ((min α lam)⁻¹ * ‖F k - Fl‖) (B * M) * rho ^ alpha := by
    intro k rho hrho hrhor
    have hsub : euclideanBall x rho ⊆ euclideanBall x r :=
      euclideanBall_subset_euclideanBall hrho.le hrhor
    have hK : 0 ≤ penalizationInteriorHolderConstant d alpha r
        ((min α lam)⁻¹ * ‖F k - Fl‖) (B * M) :=
      penalizationInteriorHolderConstant_nonneg d alpha hr.le
        (mul_nonneg (inv_nonneg.mpr (le_min hα.le hlam.le)) (norm_nonneg _)) hBM
    have hh : EuclideanHolderBoundOn (euclideanBall x rho) alpha
        (penalizationInteriorHolderConstant d alpha r
          ((min α lam)⁻¹ * ‖F k - Fl‖) (B * M)) (fun y => wk k y - w y) :=
      fun y hy z hz => hholder k y (hsub hy) z (hsub hz)
    have hbase := abs_representative_le_of_holder
      (alphaShiftedResolvent a hα hlam hEll (F k - Fl)) (hDae k) hrho hK
      halpha0.le (hsub.trans hballr) hh
    refine hbase.trans (add_le_add ?_ le_rfl)
    have hnorm : ‖alphaShiftedResolvent a hα hlam hEll (F k - Fl)‖ ≤
        α⁻¹ * ‖F k - Fl‖ :=
      norm_alphaShiftedResolvent_apply_le a hα hlam hEll (F k - Fl)
    have hsqrtnn : (0 : ℝ) ≤
        Real.sqrt (volume (euclideanBall x rho)).toReal := Real.sqrt_nonneg _
    exact div_le_div_of_nonneg_right hnorm hsqrtnn
  -- the epsilon argument
  rw [Metric.tendsto_atTop]
  intro eps heps
  set Kbar : ℝ := penalizationInteriorHolderConstant d alpha r
    ((min α lam)⁻¹ * 1) (B * M) with hKbar
  have hKbar0 : 0 ≤ Kbar :=
    penalizationInteriorHolderConstant_nonneg d alpha hr.le
      (by positivity) hBM
  set t : ℝ := ((eps / 2) / (Kbar + 1)) ^ (alpha⁻¹) with htdef
  have htpos : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  set rho : ℝ := min (r / 2) t with hrhodef
  have hrho0 : 0 < rho := lt_min (by linarith only [hr]) htpos
  have hrhor : rho < r := lt_of_le_of_lt (min_le_left _ _) (by linarith only [hr])
  have hrhoK : Kbar * rho ^ alpha < eps / 2 := by
    have hrt : rho ≤ t := min_le_right _ _
    have hpow : rho ^ alpha ≤ (eps / 2) / (Kbar + 1) := by
      have h := Real.rpow_le_rpow hrho0.le hrt halpha0.le
      rwa [htdef, Real.rpow_inv_rpow (by positivity) halpha0.ne'] at h
    have hstep : Kbar * rho ^ alpha ≤ Kbar * ((eps / 2) / (Kbar + 1)) :=
      mul_le_mul_of_nonneg_left hpow hKbar0
    refine hstep.trans_lt ?_
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith only [heps, hKbar0]
  set c : ℝ := Real.sqrt (volume (euclideanBall x rho)).toReal with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    refine Real.sqrt_pos.2 (ENNReal.toReal_pos ?_ ?_)
    · exact ((isOpen_euclideanBall x rho).measure_pos volume
        ⟨x, center_mem_euclideanBall x hrho0⟩).ne'
    · have := HCPolySupport.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall
        x rho
      have hlt := (inferInstance :
        IsFiniteMeasure (volume.restrict (euclideanBall x rho))).measure_univ_lt_top
      rw [Measure.restrict_apply_univ] at hlt
      exact hlt.ne
  rw [Metric.tendsto_atTop] at hL2
  obtain ⟨N, hN⟩ := hL2 (min 1 (eps / 2 * c * α)) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hsmall := hN k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hsmall
  have hle1 : ‖F k - Fl‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hsmall (min_le_left _ _))
  have hlt2 : ‖F k - Fl‖ < eps / 2 * c * α :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hmean : (α⁻¹ * ‖F k - Fl‖) / c < eps / 2 := by
    rw [div_lt_iff₀ hcpos]
    have hinv : α⁻¹ * ‖F k - Fl‖ < α⁻¹ * (eps / 2 * c * α) :=
      mul_lt_mul_of_pos_left hlt2 (inv_pos.mpr hα)
    have hsimp : α⁻¹ * (eps / 2 * c * α) = eps / 2 * c := by
      field_simp
    rw [hsimp] at hinv
    exact hinv
  have hosc : penalizationInteriorHolderConstant d alpha r
      ((min α lam)⁻¹ * ‖F k - Fl‖) (B * M) * rho ^ alpha < eps / 2 := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg hrho0.le _)) hrhoK
    exact penalizationInteriorHolderConstant_mono_gradient d alpha hr.le (B * M)
      (mul_le_mul_of_nonneg_left hle1 (inv_nonneg.mpr (le_min hα.le hlam.le)))
  have hfinal := hquant k rho hrho0 hrhor
  rw [Real.dist_eq]
  rw [← hcdef] at hfinal
  linarith only [hfinal, hmean, hosc]

open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing in
/-- **The freezing instance of the headline.**  For a coefficient whose
symmetric part is the scalar field `nu • 1` and whose skew part is continuous of
arbitrary size, the analytic side is continuous along uniformly bounded
`L²`-convergent data at every point of the domain, with no contrast
hypothesis. -/
theorem tendsto_representative_of_tendsto_norm_freezing [NeZero d]
    (hd : 2 ≤ d) (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {nu : ℝ} (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {F : ℕ → ScalarL2 U} {Fl : ScalarL2 U} {M : ℝ} (hM : 0 ≤ M)
    (hFM : ∀ k, ∀ᵐ y ∂volumeMeasureOn U, |F k y - Fl y| ≤ M)
    (hL2 : Tendsto (fun k => ‖F k - Fl‖) atTop (nhds 0))
    {wk : ℕ → Vec d → ℝ} {w : Vec d → ℝ}
    (hwkcont : ∀ k, ContinuousOn (wk k) U)
    (hwkae : ∀ k, wk k =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a hα hlam hEll (F k))
    (hwcont : ContinuousOn w U)
    (hwae : w =ᵐ[volumeMeasureOn U] alphaShiftedResolvent a hα hlam hEll Fl)
    {x : Vec d} (hx : x ∈ U) :
    Tendsto (fun k => wk k x) atTop (nhds (w x)) :=
  tendsto_representative_of_tendsto_norm_reg a hα hlam hEll (by norm_num)
    (inv_nonneg.mpr hnu.le)
    (hasLocalHolderShiftedResolvents_continuousCoeff hd a hU hnu hsymm hcont
      hlam hEll)
    hM hFM hL2 hwkcont hwkae hwcont hwae hx

end

end DivergenceFormProcess.Form
