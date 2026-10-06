/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLiouvilleForward
public import LeanPool.HighContrastHomogenization.Analytic.ClosureH1a
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SolutionIntegrability
public import LeanPool.HighContrastHomogenization.Support.Probability.LocalEllipticitySlices
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleCubeRestriction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Restricting a Liouville-class solution to a finite centered cube

The frozen Liouville carrier is a whole-space value-gradient pair rather than
an `H1Function`.  Its growth limit nevertheless forces finite `L²` value norm
on arbitrarily large balls.  Together with the local weighted Sobolev class,
this realizes the exact representatives as a finite centered-cube solution.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set _root_.Filter
open scoped ENNReal Topology

noncomputable section

/-- A weak equation restricts to a smaller set.  Compact support makes the two
set integrals equal to the same whole-space integral. -/
theorem IsWeakSolutionOn.mono
    {d : ℕ} {b : CoeffField d} {U V : Set (Vec d)} {F : Vec d → Vec d}
    (hUV : U ⊆ V) (h : IsWeakSolutionOn b V F) :
    IsWeakSolutionOn b U F := by
  intro phi hphi
  have hphiV : IsLocalTest V phi :=
    ⟨hphi.contDiff, hphi.hasCompactSupport, hphi.tsupport_subset.trans hUV⟩
  obtain ⟨hint, hzero⟩ := h phi hphiV
  let f : Vec d → ℝ := fun x =>
    vecDot (smoothGrad phi x) (matVecMul (b x) (F x))
  have hfzero : ∀ x, x ∉ U → f x = 0 := by
    intro x hx
    have hxnot : x ∉ tsupport phi := fun hmem => hx (hphi.tsupport_subset hmem)
    simp only [f, smoothGrad_eq_zero_of_notMem_tsupport hxnot,
      vecDot_zero_left]
  refine ⟨hint.mono_set hUV, ?_⟩
  have hUint : ∫ x in U, f x ∂volume = ∫ x, f x ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hfzero
  have hVzero : ∀ x, x ∉ V → f x = 0 := fun x hx => hfzero x (fun hxU => hx (hUV hxU))
  have hVint : ∫ x in V, f x ∂volume = ∫ x, f x ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hVzero
  change ∫ x in U, f x ∂volume = 0
  calc
    ∫ x in U, f x ∂volume = ∫ x, f x ∂volume := hUint
    _ = ∫ x in V, f x ∂volume := hVint.symm
    _ = 0 := hzero

/-- The frozen sublinear limit cannot hide an infinite normalized value norm
at every large positive radius: the scalar prefactor is then positive and
finite, while the product tends to zero. -/
theorem exists_large_radius_normalizedL2Norm_ne_top_of_liouvilleGrowth
    {d : ℕ} {v : Vec d → ℝ} {theta R : ℝ}
    (hgrowth : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) v)
      atTop (nhds 0)) :
    ∃ r : ℝ, R < r ∧ 0 < r ∧ normalizedL2Norm (euclideanBall d r) v ≠ ⊤ := by
  have hfinite : ∀ᶠ r : ℝ in atTop,
      ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) v ≠ ⊤ :=
    hgrowth.eventually_ne ENNReal.zero_ne_top
  have hevent : ∀ᶠ r : ℝ in atTop,
      R < r ∧ 0 < r ∧ normalizedL2Norm (euclideanBall d r) v ≠ ⊤ := by
    filter_upwards [eventually_gt_atTop R, eventually_gt_atTop 0, hfinite]
      with r hR hr hprod
    refine ⟨hR, hr, ?_⟩
    intro htop
    have hfactor : ENNReal.ofReal (r ^ (-(1 + theta))) ≠ 0 := by
      exact ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos hr _)
    rw [htop, ENNReal.mul_top hfactor] at hprod
    exact hprod rfl
  exact hevent.exists

/-- Finite frozen normalized norm on a positive finite-volume set gives the
ordinary local `L²` membership used by `H1Function`. -/
theorem memLp_volumeRestrict_of_normalizedL2Norm_ne_top
    {d : ℕ} {V : Set (Vec d)} {v : Vec d → ℝ}
    (hvmeas : AEStronglyMeasurable v volume)
    (hVzero : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    (hnorm : normalizedL2Norm V v ≠ ⊤) :
    MemLp v 2 (volume.restrict V) := by
  have hmeasNorm : AEStronglyMeasurable v (volumeNormalizedMeasure V) := by
    unfold volumeNormalizedMeasure
    exact AEStronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous
      hvmeas.restrict
  have hmemNorm : MemLp v 2 (volumeNormalizedMeasure V) := by
    rw [memLp_iff, ← normalizedL2Norm_eq_eLpNorm_volumeNormalizedMeasure V v hmeasNorm]
    exact lt_top_iff_ne_top.2 hnorm
  have hscaled := hmemNorm.smul_measure hVtop
  simpa only [volumeNormalizedMeasure, smul_smul,
    ENNReal.mul_inv_cancel hVzero hVtop, one_smul] using hscaled

/-- Every open triadic cube is contained in some positive-radius centered
Euclidean ball. -/
theorem exists_pos_euclideanBall_superset_openCubeSet
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    ∃ R : ℝ, 0 < R ∧ openCubeSet Q ⊆ euclideanBall d R := by
  obtain ⟨rho, hrho, hcube⟩ :=
    (isBounded_cubeSet Q).subset_ball_lt 0 (0 : Vec d)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  let R : ℝ := Real.sqrt d * rho
  have hR : 0 < R := mul_pos (Real.sqrt_pos.2 hdreal) hrho
  refine ⟨R, hR, fun x hx => ?_⟩
  have hxmetric : x ∈ Metric.ball (0 : Vec d) rho :=
    hcube (openCubeSet_subset_cubeSet Q hx)
  have hnorm := vecNormSq_sub_lt_of_mem_metricBall (NeZero.pos d) hxmetric
  have hRsq : (d : ℝ) * rho ^ 2 = R ^ 2 := by
    dsimp only [R]
    rw [mul_pow, Real.sq_sqrt hdreal.le]
  simpa only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero, hRsq]
    using hnorm

/-- The measurable value representative in the frozen growth condition is in
normalized `L²` on every origin cube. -/
theorem memLp_normalizedCubeMeasure_of_liouvilleGrowth
    {d : ℕ} [NeZero d] {theta : ℝ} {v : Vec d → ℝ}
    (hvmeas : AEStronglyMeasurable v volume)
    (hgrowth : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) v)
      atTop (nhds 0)) (q : ℕ) :
    MemLp v 2 (normalizedCubeMeasure (originCube d (q : ℤ))) := by
  let Q : TriadicCube d := originCube d (q : ℤ)
  obtain ⟨R, hR, hsub⟩ := exists_pos_euclideanBall_superset_openCubeSet Q
  obtain ⟨r, hrR, hr, hnorm⟩ :=
    exists_large_radius_normalizedL2Norm_ne_top_of_liouvilleGrowth
      (R := R) hgrowth
  have hsub' : openCubeSet Q ⊆ euclideanBall d r := hsub.trans (by
    intro x hx
    have hxnorm : vecNormSq x < R ^ 2 := by
      simpa only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero]
        using hx
    have hsq : R ^ 2 < r ^ 2 := pow_lt_pow_left₀ hrR hR.le (by norm_num)
    simpa only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero]
      using hxnorm.trans hsq)
  have hballZero : volume (euclideanBall d r) ≠ 0 :=
    (ENNReal.toReal_ne_zero.mp
      (Book.Ch01.volume_euclideanBall_toReal_ne_zero (0 : Vec d) hr)).1
  have hballTop : volume (euclideanBall d r) ≠ ⊤ :=
    Book.Ch01.volume_euclideanBall_ne_top (0 : Vec d) r
  have hvBall : MemLp v 2 (volume.restrict (euclideanBall d r)) :=
    memLp_volumeRestrict_of_normalizedL2Norm_ne_top hvmeas
      hballZero hballTop hnorm
  have hvOpen : MemLp v 2 (volume.restrict (openCubeSet Q)) :=
    hvBall.mono_measure (Measure.restrict_mono_set volume hsub')
  have hvCube : MemLp v 2 (cubeMeasure Q) := by
    simpa only [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
      using hvOpen
  have hscaled := hvCube.smul_measure
    (c := ENNReal.ofReal ((cubeVolume Q)⁻¹)) ENNReal.ofReal_ne_top
  simpa only [normalizedCubeMeasure] using hscaled

/-- The gradient representative of a local Sobolev-class pair is an honest
vector-valued `L²` field on every open centered cube, with the ellipticity pair
of a ball containing the cube. -/
theorem memVectorL2_grad_openCubeSet_of_memH1sLoc
    {d : ℕ} [NeZero d] {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemH1sLoc b v Dv) (Q : TriadicCube d) :
    MemVectorL2 (openCubeSet Q) Dv := by
  obtain ⟨R, hR, hsub⟩ :=
    exists_pos_euclideanBall_superset_openCubeSet Q
  have hsqBall := integrableOn_vecNormSq_grad_of_memH1sLoc_class hb hv hR
  have hsq : IntegrableOn (fun x => vecNormSq (Dv x))
      (openCubeSet Q) volume :=
    hsqBall.mono_set hsub
  have hcoord : ∀ i, MemScalarL2 (openCubeSet Q) (fun x => Dv x i) := by
    intro i
    have hmeas :=
      aestronglyMeasurable_grad_of_memH1sLoc hv (openCubeSet Q) i
    apply (memLp_two_iff_integrable_sq hmeas).2
    refine hsq.mono' (hmeas.pow 2) ?_
    filter_upwards with x
    have hi : 0 ≤ Dv x i ^ 2 := sq_nonneg _
    have hvec : 0 ≤ vecNormSq (Dv x) := vecNormSq_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hi, abs_of_nonneg hvec] using
      sq_apply_le_vecNormSq (Dv x) i
  simpa only [MemVectorL2, volumeMeasureOn] using
    (MemLp.of_eval hcoord : MemLp Dv 2 (volumeMeasureOn (openCubeSet Q)))

/-- A member of the exact frozen Liouville class restricts to a public finite
cube solution, preserving both supplied representatives pointwise. -/
theorem exists_cubeSolution_eq_representatives_of_memLiouvilleClass
    {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
    {b : CoeffField d} {theta : ℝ}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemLiouvilleClass b theta v Dv)
    (hcoeff : (a.coeffOn (originCube d m)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))] b) :
    ∃ u : Book.Ch03.CubeSolution (originCube d m) a,
      u.toH1.toFun = v ∧ u.toH1.grad = Dv := by
  let Q : TriadicCube d := originCube d m
  obtain ⟨R, hR, hQball⟩ :=
    exists_pos_euclideanBall_superset_openCubeSet Q
  obtain ⟨r, hrR, hr, hnorm⟩ :=
    exists_large_radius_normalizedL2Norm_ne_top_of_liouvilleGrowth
      (R := R) hv.2.2
  have hQsub : openCubeSet Q ⊆ euclideanBall d r :=
    hQball.trans (by
      intro x hx
      have hxnorm : vecNormSq x < R ^ 2 := by
        simpa only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero]
          using hx
      have hsq : R ^ 2 < r ^ 2 := pow_lt_pow_left₀ hrR hR.le (by norm_num)
      simpa only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero]
        using hxnorm.trans hsq)
  have hballZero : volume (euclideanBall d r) ≠ 0 :=
    (ENNReal.toReal_ne_zero.mp
      (Book.Ch01.volume_euclideanBall_toReal_ne_zero (0 : Vec d) hr)).1
  have hballTop : volume (euclideanBall d r) ≠ ⊤ :=
    (isOpenBoundedConvexDomain_euclideanBallAt (0 : Vec d) hr).volume_lt_top.ne
  have hvBall : MemLp v 2 (volume.restrict (euclideanBall d r)) :=
    memLp_volumeRestrict_of_normalizedL2Norm_ne_top hv.1.1.1
      hballZero hballTop hnorm
  have hvCube : MemScalarL2 (openCubeSet Q) v :=
    hvBall.mono_measure (Measure.restrict_mono_set volume hQsub)
  have hDvCube : MemVectorL2 (openCubeSet Q) Dv :=
    memVectorL2_grad_openCubeSet_of_memH1sLoc hb hv.1 Q
  have hweakGrad : HasWeakGradientOn (openCubeSet Q) v Dv := by
    exact (hv.1.2 r hr).1.restrict (isOpen_openCubeSet Q) hQsub
  let uH1 : H1Function (openCubeSet Q) :=
    { toFun := v
      grad := Dv
      memL2 := hvCube
      gradMemL2 := by
        intro i
        simpa only [MemVectorL2, volumeMeasureOn] using hDvCube.eval i
      hasWeakGradient := hweakGrad }
  have hweakB : IsWeakSolutionOn b (openCubeSet Q) Dv :=
    hv.2.1.mono (Set.subset_univ _)
  have hweakA : IsWeakSolutionOn
      (a.coeffOn Q).toCoeffField (openCubeSet Q) Dv :=
    hweakB.congr_ae hcoeff.symm _root_.Filter.EventuallyEq.rfl
  have haeEll : IsAEEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (openCubeSet Q) (a.coeffOn Q).toCoeffField := by
    refine ⟨measurableSet_openCubeSet Q, ?_, ?_⟩
    · intro i j
      simpa only [Book.Ch02.cubeDomain_coe] using
        (a.coeffOn Q).aeStronglyMeasurable i j
    · simpa only [Book.Ch02.cubeDomain_coe] using (a.coeffOn Q).aeElliptic
  have hflux : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (Dv x)) :=
    haeEll.memVectorL2_matVecMul hDvCube
  have hsolenoidal : IsSolenoidalOn (openCubeSet Q)
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (Dv x)) := by
    apply IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2
      hflux (isOpen_openCubeSet Q)
    intro psi hsmooth hcompact hsupport
    have htest : IsLocalTest (openCubeSet Q) psi :=
      ⟨hsmooth, hcompact, hsupport⟩
    have hzero := (hweakA psi htest).2
    change ∫ x in openCubeSet Q,
      vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (Dv x))
        (smoothGrad psi x) ∂volume = 0
    simpa only [vecDot_comm] using hzero
  let u : Book.Ch03.CubeSolution Q a :=
    { toH1 := uH1
      isHarmonic := ⟨uH1.isPotentialOn, hsolenoidal⟩ }
  exact ⟨u, rfl, rfl⟩

end

end HighContrast
end HCPolySupport
