/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalFormResolvent
public import LeanPool.FastDynamo.Operator.RieszEigenvalueLocalization
public import LeanPool.FastDynamo.Local.SeedParameters

/-!
# The isolating contour `Γ` around the seed eigenvalue `λ_*`

This module is the Lean form of the choice of the contour in §2.3 of the paper (the paragraph
after the analytic Fredholm argument):

> Applying this conclusion to `w = V⁰`, we fix a positively oriented circle `Γ` whose closed
> interior `𝒢` lies in `{re z > 0}` and whose interior contains `λ_*` and no other spectral
> point of `A_{V⁰}`.

`FastDynamo/Local/HorizontalModeIsolation.lean` provides the punctured ball of invertible
parameters around any point of the open right half plane, and
`FastDynamo/Local/HorizontalFormResolvent.lean` turns invertibility of the shifted form
operator into an `L² → H¹` resolvent.  Here those two are combined into one bundle
`HorizontalIsolation`, carrying

* a radius `r ≤ re λ_* / 4` whose *doubled* ball still lies in the half plane and contains no
  spectral point except possibly `λ_*` (the bound `r ≤ re λ_* / 4` is a choice of the
  formalisation; the paper only requires `𝒢 ⊂ {re z > 0}`);
* the contour `Γ = SpectralCircle` centred at `λ_*` with that radius, so that
  `g_* = Γ.growthFloor = re λ_* - r ≥ (3/4) re λ_* > 0` (`eq:spectral-gap`) and
  `𝒢 = Γ.closedRegion ⊆ {re z > 0}`;
* the resolvent on the punctured ball, hence on `Γ` itself;
* the Riesz projection `P⁰ = (2πi)^{-1}∮_Γ(z-A_w)^{-1}dz`, proved idempotent (annular
  holomorphy), of finite rank (the resolvent differs from the free one by a compact operator,
  and the free one is holomorphic inside `Γ`), nonzero, and fixing the eigenvector.  The
  finite rank goes beyond §2.3 of the paper, which asserts only that the spectrum of `A_w` in
  the open right half plane consists of isolated eigenvalues.

The eigenpair at `λ_*` enters only as a hypothesis here; it is supplied by
`Local/HorizontalModeEigenpair.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

namespace HorizontalMode

open HorizontalWeakForm PonomarenkoFreeOmegaInterface

/-- The closed unit disk has finite planar Lebesgue measure. -/
theorem volume_unitDisk_ne_top : volume wholePlaneUnitDisk ≠ (∞ : ℝ≥0∞) := by
  have hcompact : IsCompact wholePlaneUnitDisk := by
    rw [wholePlaneUnitDisk]
    exact isCompact_closedBall 0 1
  exact hcompact.measure_lt_top.ne

/-- The axial coordinate of the seed velocity vanishes off the closed unit disk. -/
theorem horizontalModeVelocity_axial_ae_zero (N Omega : ℝ) :
    ∀ᵐ x ∂volume, x ∉ wholePlaneUnitDisk →
      wholePlaneCoordLInf 2 (horizontalModeVelocity N Omega) x = 0 :=
  horizontalModeVelocity_coord_ae_zero_off_unitDisk N Omega 2

/-- The transverse coordinates of the seed velocity vanish off the closed unit disk. -/
theorem horizontalModeVelocity_transverse_ae_zero (N Omega : ℝ) :
    ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ wholePlaneUnitDisk →
      wholePlaneCoordLInf j.castSucc (horizontalModeVelocity N Omega) x = 0 :=
  fun j => horizontalModeVelocity_coord_ae_zero_off_unitDisk N Omega j.castSucc

end HorizontalMode

namespace HorizontalWeakForm

/-! ## Isolation data -/

/-- **Isolating data for a spectral point of `A_w`.**  The doubled ball `B(λ, 2r)` lies in the
open right half plane and contains no spectral point of `A_w` except possibly `λ` itself, and
the radius obeys `r ≤ re λ / 4`, a normalisation chosen by the formalisation. -/
structure HorizontalIsolation (N : ℝ) (w : WholePlaneC3LInf) (lam : ℂ) where
  /-- The radius of the isolating contour. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- The constraint `r ≤ re λ_* / 4`, which yields `g_* ≥ (3/4) re λ_*`. -/
  radius_le : radius ≤ lam.re / 4
  re_pos : 0 < lam.re
  /-- The doubled ball stays inside the open right half plane. -/
  ball_subset : Metric.ball lam (2 * radius) ⊆ {z : ℂ | 0 < z.re}
  /-- The doubled ball is free of spectral points other than `λ`. -/
  punctured : ∀ z ∈ Metric.ball lam (2 * radius), z ≠ lam →
    (horizontalPencilForm N w z).IsInvertible

/-- **Existence of isolating data.**  Analytic Fredholm discreteness supplies an isolating
radius around every parameter of the open right half plane; shrinking it to `re λ / 4` gives
the contour constraint `r ≤ re λ / 4`. -/
theorem nonempty_horizontalIsolation
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (N : ℝ) (w : WholePlaneC3LInf)
    (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0)
    {lam : ℂ} (hlam : 0 < lam.re) :
    Nonempty (HorizontalIsolation N w lam) := by
  obtain ⟨rho, hrho, hsub, hpunct⟩ :=
    exists_punctured_ball_isInvertible_horizontalPencilForm s hs hsm N w hw3 hw hlam
  refine ⟨{ radius := min (rho / 4) (lam.re / 4)
            radius_pos := lt_min (by linarith) (by linarith)
            radius_le := min_le_right _ _
            re_pos := hlam
            ball_subset := ?_
            punctured := ?_ }⟩
  · refine subset_trans (Metric.ball_subset_ball ?_) hsub
    have h : min (rho / 4) (lam.re / 4) ≤ rho / 4 := min_le_left _ _
    linarith
  · intro z hz hne
    refine hpunct z ?_ hne
    refine Metric.ball_subset_ball ?_ hz
    have h : min (rho / 4) (lam.re / 4) ≤ rho / 4 := min_le_left _ _
    linarith

namespace HorizontalIsolation

variable {N : ℝ} {w : WholePlaneC3LInf} {lam : ℂ}

/-! ### The contour -/

/-- The positively oriented isolating circle `Γ` centred at the spectral point. -/
def contour (iso : HorizontalIsolation N w lam) : SpectralCircle :=
  { center := lam, radius := iso.radius, radius_pos := iso.radius_pos }

/-- The contour is centred at the spectral point. -/
@[simp] theorem contour_center (iso : HorizontalIsolation N w lam) :
    iso.contour.center = lam := rfl

/-- The contour has the isolating radius. -/
@[simp] theorem contour_radius (iso : HorizontalIsolation N w lam) :
    iso.contour.radius = iso.radius := rfl

/-- The closed interior `𝒢` is the closed disc of radius `r` about `λ`. -/
theorem contour_closedRegion (iso : HorizontalIsolation N w lam) :
    iso.contour.closedRegion = Metric.closedBall lam iso.radius := rfl

/-- The growth floor `g_* = min_{𝒢} re ζ` of `eq:spectral-gap` is `re λ - r`. -/
theorem growthFloor_eq (iso : HorizontalIsolation N w lam) :
    iso.contour.growthFloor = lam.re - iso.radius := rfl

/-- The lower bound `g_* ≥ (3/4) re λ_*` (`eq:spectral-gap` in quantitative form; the paper
only needs `g_* > 0`). -/
theorem growthFloor_ge (iso : HorizontalIsolation N w lam) :
    3 / 4 * lam.re ≤ iso.contour.growthFloor := by
  have h := iso.radius_le
  rw [growthFloor_eq]
  linarith

/-- `g_* > 0`: this is `eq:spectral-gap`. -/
theorem growthFloor_pos (iso : HorizontalIsolation N w lam) :
    0 < iso.contour.growthFloor := by
  have h := iso.growthFloor_ge
  have hre := iso.re_pos
  linarith

/-- The closed interior `𝒢` lies in the open right half plane. -/
theorem closedRegion_re_pos (iso : HorizontalIsolation N w lam) {z : ℂ}
    (hz : z ∈ iso.contour.closedRegion) : 0 < z.re :=
  iso.contour.closedRegion_re_pos iso.growthFloor_pos hz

/-- The closed interior sits inside the doubled ball. -/
theorem closedRegion_subset_ball (iso : HorizontalIsolation N w lam) :
    iso.contour.closedRegion ⊆ Metric.ball lam (2 * iso.radius) := by
  rw [contour_closedRegion]
  refine Metric.closedBall_subset_ball ?_
  have h := iso.radius_pos
  linarith

/-! ### The resolvent on the punctured ball and on `Γ` -/

/-- The punctured doubled ball, an open set of resolvent parameters. -/
def puncturedSet (iso : HorizontalIsolation N w lam) : Set ℂ :=
  Metric.ball lam (2 * iso.radius) \ {lam}

/-- The punctured doubled ball is open. -/
theorem isOpen_puncturedSet (iso : HorizontalIsolation N w lam) :
    IsOpen iso.puncturedSet :=
  Metric.isOpen_ball.sdiff isClosed_singleton

/-- Every parameter of the punctured ball has positive real part. -/
theorem puncturedSet_re_pos (iso : HorizontalIsolation N w lam) :
    ∀ z ∈ iso.puncturedSet, 0 < z.re :=
  fun _ hz => iso.ball_subset hz.1

/-- The shifted form operator is invertible on the punctured ball. -/
theorem puncturedSet_isInvertible (iso : HorizontalIsolation N w lam) :
    ∀ z ∈ iso.puncturedSet, (horizontalPencilForm N w z).IsInvertible :=
  fun _ hz => iso.punctured _ hz.1 (by simpa using hz.2)

/-- The chosen `L² → D(A_w)` resolvent on the punctured ball. -/
def resolvent (iso : HorizontalIsolation N w lam) :
    HasResolventOn (horizontalFormOperator N w) iso.puncturedSet :=
  horizontalHasResolventOn N w iso.puncturedSet iso.puncturedSet_re_pos
    iso.puncturedSet_isInvertible

/-- The state resolvent on the punctured ball is `j ∘ 𝔸_w(z)⁻¹ ∘ pivot`. -/
theorem resolvent_stateResolvent (iso : HorizontalIsolation N w lam) {z : ℂ}
    (hz : z ∈ iso.puncturedSet) :
    iso.resolvent.stateResolvent z =
      (wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z) :=
  horizontalHasResolventOn_stateResolvent N w iso.puncturedSet _ _ hz

/-- The contour lies in the punctured ball, hence in the resolvent set of `A_w`. -/
theorem sphere_subset_puncturedSet (iso : HorizontalIsolation N w lam) :
    Metric.sphere lam iso.radius ⊆ iso.puncturedSet := by
  intro z hz
  have hdist : dist z lam = iso.radius := Metric.mem_sphere.mp hz
  refine ⟨Metric.mem_ball.mpr ?_, ?_⟩
  · rw [hdist]
    have h := iso.radius_pos
    linarith
  · intro hmem
    rw [Set.mem_singleton_iff.mp hmem, dist_self] at hdist
    exact absurd hdist.symm (ne_of_gt iso.radius_pos)

/-- The chosen resolvent restricted to the contour. -/
def contourResolvent (iso : HorizontalIsolation N w lam) :
    HasResolventOn (horizontalFormOperator N w) (Metric.sphere lam iso.radius) :=
  iso.resolvent.mono iso.sphere_subset_puncturedSet

/-! ### The Riesz projection -/

/-- The Riesz projection `P⁰ = (2πi)^{-1}∮_Γ(z-A_w)^{-1}dz`. -/
def projection (iso : HorizontalIsolation N w lam) : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2 :=
  iso.contourResolvent.rieszProjection

/-- The closed annulus between the half-radius and the contour lies in the punctured ball. -/
theorem annulus_subset_puncturedSet (iso : HorizontalIsolation N w lam) :
    Metric.closedBall lam iso.radius \ Metric.ball lam (iso.radius / 2) ⊆
      iso.puncturedSet := by
  rintro z ⟨hzc, hzb⟩
  have hle : dist z lam ≤ iso.radius := Metric.mem_closedBall.mp hzc
  have hge : iso.radius / 2 ≤ dist z lam := not_lt.mp (fun h => hzb (Metric.mem_ball.mpr h))
  have hpos : 0 < iso.radius := iso.radius_pos
  refine ⟨Metric.mem_ball.mpr (by linarith), ?_⟩
  intro hmem
  rw [Set.mem_singleton_iff.mp hmem, dist_self] at hge
  linarith

/-- **The Riesz projection is idempotent.**  Holomorphy of the resolvent on the punctured
ball makes the contour operator independent of the radius, and the double-contour exchange
of `FastDynamo/Operator/RieszProjectionCalculus.lean` then gives idempotence. -/
theorem isIdempotentElem_projection (iso : HorizontalIsolation N w lam) :
    IsIdempotentElem iso.projection :=
  iso.resolvent.rieszProjection_outer_isIdempotentElem_of_isOpen_common_resolvent
    (by linarith [iso.radius_pos] : (0 : ℝ) < iso.radius / 2)
    (by linarith [iso.radius_pos] : iso.radius / 2 < iso.radius)
    iso.isOpen_puncturedSet iso.annulus_subset_puncturedSet

/-- The closed interior lies in the open right half plane, in subset form. -/
theorem closedBall_subset_rePos (iso : HorizontalIsolation N w lam) :
    Metric.closedBall lam iso.radius ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  exact iso.closedRegion_re_pos hz

/-- **The Riesz projection has finite rank.**  On the contour the state resolvent of `A_w`
differs from the free one by a compact operator, and the free one is holomorphic on the closed
interior, so its contour integral vanishes; `FastDynamo/Operator/FredholmIsolation.lean` then
makes `P⁰` a compact idempotent.  This is stronger than what §2.3 of the paper asserts
(isolated eigenvalues, with no multiplicity claim). -/
theorem finiteDimensional_projection_range
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0)
    (iso : HorizontalIsolation N w lam) :
    FiniteDimensional ℂ iso.projection.toLinearMap.range := by
  have hFcont : ContinuousOn (horizontalFreeStateResolvent N)
      (Metric.sphere lam iso.radius) := by
    intro z hz
    have hzre : 0 < z.re :=
      iso.closedBall_subset_rePos (Metric.sphere_subset_closedBall hz)
    exact ((analyticAt_horizontalFreeStateResolvent N hzre).continuousAt).continuousWithinAt
  have hcompact : ∀ z ∈ Metric.sphere lam iso.radius,
      IsCompactOperator (iso.contourResolvent.stateResolvent z -
        horizontalFreeStateResolvent N z) := by
    intro z hz
    have hzp : z ∈ iso.puncturedSet := iso.sphere_subset_puncturedSet hz
    have heq : iso.contourResolvent.stateResolvent z =
        (wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z) :=
      iso.resolvent_stateResolvent hzp
    rw [heq]
    exact isCompactOperator_horizontalStateResolvent_sub_free s hs hsm N w hw3 hw
      (iso.puncturedSet_re_pos z hzp) (iso.puncturedSet_isInvertible z hzp)
  have hFint : circleIntegral (horizontalFreeStateResolvent N) lam iso.radius = 0 :=
    circleIntegral_horizontalFreeStateResolvent_eq_zero N iso.radius_pos.le
      iso.closedBall_subset_rePos
  exact iso.contourResolvent.finiteDimensional_rieszProjection_range_of_compact_difference
    iso.radius_pos.le (horizontalFreeStateResolvent N) hFcont hcompact hFint
    iso.isIdempotentElem_projection

/-! ### The eigenvector -/

/-- **`P⁰b = b`.**  The Riesz projection fixes the eigenvector of `A_w` at the enclosed
eigenvalue, because the scalar Cauchy kernel has winding number one there. -/
theorem projection_apply_eigenvector (iso : HorizontalIsolation N w lam)
    (u : HorizontalFormDomain N w)
    (heig : (horizontalFormOperator N w).IsEigenpair lam u) :
    iso.projection (wholePlaneH1Embedding C2 u.1.1) =
      wholePlaneH1Embedding C2 u.1.1 :=
  iso.contourResolvent.rieszProjection_apply_of_isEigenpair_mem_ball heig
    (Metric.mem_ball_self iso.radius_pos)

/-- **`P⁰ ≠ 0`.**  The spectrum inside `Γ` is nonempty. -/
theorem projection_ne_zero (iso : HorizontalIsolation N w lam)
    (u : HorizontalFormDomain N w)
    (heig : (horizontalFormOperator N w).IsEigenpair lam u) :
    iso.projection ≠ 0 := by
  intro hzero
  have hfix := iso.projection_apply_eigenvector u heig
  rw [hzero] at hfix
  exact heig.1 hfix.symm

/-! ### The enclosed spectrum -/

/-- **`𝒢` meets the spectrum only at `λ`.** -/
theorem closedRegion_inter_spectrum_subset (iso : HorizontalIsolation N w lam) :
    iso.contour.closedRegion ∩ horizontalSpectrum N w ⊆ {lam} := by
  rintro z ⟨hzG, hzspec⟩
  by_contra hne
  exact hzspec.2 (iso.punctured z (iso.closedRegion_subset_ball hzG)
    (by simpa using hne))

/-- With an eigenpair at `λ`, the closed interior `𝒢` meets the spectrum exactly at `λ`. -/
theorem closedRegion_inter_spectrum (iso : HorizontalIsolation N w lam)
    (u : HorizontalFormDomain N w)
    (heig : (horizontalFormOperator N w).IsEigenpair lam u) :
    iso.contour.closedRegion ∩ horizontalSpectrum N w = {lam} := by
  refine Set.Subset.antisymm iso.closedRegion_inter_spectrum_subset ?_
  rintro z hz
  rw [Set.mem_singleton_iff.mp hz]
  exact ⟨Metric.mem_closedBall_self iso.radius_pos.le,
    mem_horizontalSpectrum_of_isEigenpair N w iso.re_pos u heig⟩

end HorizontalIsolation

end HorizontalWeakForm

namespace HorizontalMode

open HorizontalWeakForm PonomarenkoFreeOmegaInterface

/-! ## The seed instance -/

/-- **Isolating data at the certified seed.**  For the free-`Ω` jump flow `V⁰` of
`eq:jump-flow` and the certified eigenvalue `λ_* = κ² - N²`, an isolating contour exists.  No
eigenpair hypothesis is needed for this: only `re λ_* > 0`, carried by the certificate. -/
theorem nonempty_horizontalIsolation_modeVelocity {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) :
    Nonempty (HorizontalIsolation N (horizontalModeVelocity N Omega)
      (horizontalEigenvalue N kappa)) :=
  nonempty_horizontalIsolation wholePlaneUnitDisk measurableSet_wholePlaneUnitDisk
    volume_unitDisk_ne_top N (horizontalModeVelocity N Omega)
    (horizontalModeVelocity_axial_ae_zero N Omega)
    (horizontalModeVelocity_transverse_ae_zero N Omega)
    (re_ponomarenkoLocalEigenvalue_pos hd)

/-- A chosen isolating contour at the certified seed. -/
def modeIsolation {N Omega : ℝ} {kappa : ℂ} (hd : CertifiedInterfaceData N Omega kappa) :
    HorizontalIsolation N (horizontalModeVelocity N Omega) (horizontalEigenvalue N kappa) :=
  Classical.choice (nonempty_horizontalIsolation_modeVelocity hd)

/-- **The seed contour.**  Granting the weak eigenvalue identity of `lem:jump-horizontal-mode`,
the certified mode is an eigenvector inside the contour: the Riesz projection is a nonzero
finite-rank projection fixing it, the closed interior meets the spectrum exactly at `λ_*`, and
the growth floor obeys `g_* ≥ (3/4) re λ_* > 0`. -/
theorem modeIsolation_spec {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) (hweak : HorizontalModeWeakIdentity hd) :
    ∃ u : HorizontalFormDomain N (horizontalModeVelocity N Omega),
      u.1.1 = horizontalMode hd ∧
        (modeIsolation hd).projection
            (wholePlaneH1Embedding C2 (horizontalMode hd)) =
          wholePlaneH1Embedding C2 (horizontalMode hd) ∧
        (modeIsolation hd).projection ≠ 0 ∧
        (modeIsolation hd).contour.closedRegion ∩
            horizontalSpectrum N (horizontalModeVelocity N Omega) =
          {horizontalEigenvalue N kappa} := by
  obtain ⟨u, hu, heig⟩ := horizontalMode_isEigenpair hd hweak
  refine ⟨u, hu, ?_, (modeIsolation hd).projection_ne_zero u heig, ?_⟩
  · have h := (modeIsolation hd).projection_apply_eigenvector u heig
    rw [hu] at h
    exact h
  · exact (modeIsolation hd).closedRegion_inter_spectrum u heig

end HorizontalMode

end

end FastDynamo
