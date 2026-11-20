/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalFormCompactness
public import LeanPool.FastDynamo.Local.HorizontalModeWeakIdentity

/-!
# Global analytic-Fredholm isolation for the horizontal form operator

This module is the Lean form, for the two-component horizontal operator, of the analytic
Fredholm paragraph of §2.3 of the paper ("Spectral isolation and regularisation"):

> The analytic Fredholm theorem implies that `𝔸_w(z)` is invertible except at a discrete set
> of points in the open right half-plane. [...] Hence the spectrum of `A_w` in the open right
> half-plane consists of isolated eigenvalues.

`FastDynamo/Local/HorizontalFormCompactness.lean` supplies the local half of that argument:
the factorisation `𝔸_w(z) = F_z(1 - K(z))` with `K(z)` compact and holomorphic on
`{re z > 0}`, an invertible base point at the Gårding shift, and a scalar reduction on a ball
around every parameter.  This file does the *global* bookkeeping, in three steps.

* A generic continuation lemma for `AnalyticFredholm.LocalScalarReductionCover`: a cover of a
  connected open domain by local scalar reductions, together with one invertible parameter,
  makes the invertible locus **codiscrete**, not merely dense.  Density is
  `LocalScalarReductionCover.subset_closure_invertibleSet_inter` of
  `FastDynamo/Operator/AnalyticFredholmContinuation.lean`; codiscreteness needs the local
  isolated-zero theorem on each patch, applied at an invertible point that the density
  statement itself provides.
* The connectedness of `{z : ℂ | 0 < re z}`, by convexity.
* The support hypotheses of the compactness layer for the free-`Ω` jump velocity `V⁰`.

The conclusion, `isDiscrete_horizontalSpectrum` and
`exists_punctured_ball_isInvertible_horizontalPencilForm`, is the exact input of the contour
construction in `FastDynamo/Local/HorizontalModeContour.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace AnalyticFredholm

namespace LocalScalarReductionCover

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {F : ℂ → (X →L[ℂ] X)} {U : Set ℂ}

omit [CompleteSpace X] in
/-- **Codiscreteness of the invertible locus.**  On a connected domain covered by local scalar
reductions and containing one invertible parameter, the noninvertible parameters have no
accumulation point in the domain.  This strengthens
`LocalScalarReductionCover.subset_closure_invertibleSet_inter`, which only gives density, and
is the global form of the analytic Fredholm theorem used in §2.3 of the paper. -/
theorem invertibleSet_mem_codiscreteWithin
    (atlas : LocalScalarReductionCover F U) (hU : IsConnected U)
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀ : (F z₀).IsInvertible) :
    invertibleSet F ∈ codiscreteWithin U := by
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hzU
  have hzV : z ∈ atlas.patch z hzU := atlas.mem_patch z hzU
  have hVopen : IsOpen (atlas.patch z hzU) := atlas.patch_isOpen z hzU
  obtain ⟨y, hyV, hy⟩ := atlas.exists_invertible_on_isOpen hU hz₀U hz₀ hVopen
    ⟨z, hzV⟩ (atlas.patch_subset z hzU)
  have hcod := (atlas.reduction z hzU).eventually_isInvertible_of_mem
    (atlas.patch_isConnected z hzU) hyV hy hzV
  have hVnhds : atlas.patch z hzU ∈ 𝓝[≠] z :=
    nhdsWithin_le_nhds (hVopen.mem_nhds hzV)
  filter_upwards [hcod, hVnhds] with y hy' hyV'
  exact Or.inl (hy'.resolve_right (by simpa using hyV'))

omit [CompleteSpace X] in
/-- The noninvertible parameters form a discrete subset of the connected domain. -/
theorem isDiscrete_noninvertibleSet_inter
    (atlas : LocalScalarReductionCover F U) (hU : IsConnected U)
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀ : (F z₀).IsInvertible) :
    IsDiscrete (noninvertibleSet F ∩ U) := by
  apply isDiscrete_of_codiscreteWithin
  simpa [noninvertibleSet] using
    atlas.invertibleSet_mem_codiscreteWithin hU hz₀U hz₀

omit [CompleteSpace X] in
/-- **Isolation in positive-radius form.**  Every parameter of the connected open domain has a
punctured ball, still inside the domain, consisting entirely of invertible parameters. -/
theorem exists_punctured_ball_isInvertible
    (atlas : LocalScalarReductionCover F U) (hU : IsConnected U) (hUopen : IsOpen U)
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀ : (F z₀).IsInvertible)
    {z : ℂ} (hzU : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∀ y ∈ Metric.ball z r, y ≠ z → (F y).IsInvertible := by
  have hcod := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp
    (atlas.invertibleSet_mem_codiscreteWithin hU hz₀U hz₀) z hzU
  have hUevent : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hUopen.mem_nhds hzU)
  have hinv : invertibleSet F ∈ 𝓝[≠] z := by
    filter_upwards [hcod, hUevent] with y hy hyU
    exact hy.resolve_right (by simpa using hyU)
  obtain ⟨W, hW, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hinv
  obtain ⟨r, hr, hrW⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hW (hUopen.mem_nhds hzU))
  refine ⟨r, hr, fun y hy => (hrW hy).2, fun y hy hne => ?_⟩
  exact hWsub ⟨(hrW hy).1, by simpa using hne⟩

section CompactHilbert

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Discreteness of the noninvertible locus of an analytic compact pencil. -/
theorem compactPencil_isDiscrete_noninvertibleSet_inter
    {K : ℂ → (H →L[ℂ] H)} {U : Set ℂ}
    (hUopen : IsOpen U) (hU : IsConnected U)
    (hKanalytic : AnalyticOnNhd ℂ K U)
    (hKcompact : ∀ z ∈ U, IsCompactOperator (K z))
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀ : (compactPencil K z₀).IsInvertible) :
    IsDiscrete (noninvertibleSet (compactPencil K) ∩ U) :=
  (compactPencilCover K U hUopen hKanalytic hKcompact).isDiscrete_noninvertibleSet_inter
    hU hz₀U hz₀

/-- Punctured-ball isolation for an analytic compact pencil. -/
theorem compactPencil_exists_punctured_ball_isInvertible
    {K : ℂ → (H →L[ℂ] H)} {U : Set ℂ}
    (hUopen : IsOpen U) (hU : IsConnected U)
    (hKanalytic : AnalyticOnNhd ℂ K U)
    (hKcompact : ∀ z ∈ U, IsCompactOperator (K z))
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀ : (compactPencil K z₀).IsInvertible)
    {z : ℂ} (hzU : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∀ y ∈ Metric.ball z r, y ≠ z → (compactPencil K y).IsInvertible :=
  (compactPencilCover K U hUopen hKanalytic hKcompact).exists_punctured_ball_isInvertible
    hU hUopen hz₀U hz₀ hzU

end CompactHilbert

end LocalScalarReductionCover

end AnalyticFredholm

/-! ## The open right half plane is connected -/

/-- The open right half plane is convex, being a linear half space. -/
theorem convex_rePos : Convex ℝ {z : ℂ | 0 < z.re} :=
  _root_.convex_halfSpace_re_gt 0

/-- The open right half plane is connected.  This is the missing hypothesis of every
analytic-Fredholm continuation theorem applied below. -/
theorem isConnected_rePos : IsConnected {z : ℂ | 0 < z.re} :=
  ⟨⟨1, by norm_num⟩, convex_rePos.isPreconnected⟩

namespace HorizontalMode

open HorizontalWeakForm PonomarenkoFreeOmegaInterface

/-! ## The free-`Ω` jump velocity is supported in the closed unit disk -/

/-- Every scalar coordinate of the free-`Ω` jump velocity vanishes almost everywhere outside
the closed unit disk.  This discharges the support hypotheses of
`FastDynamo/Local/HorizontalFormCompactness.lean` for the seed flow `V⁰`. -/
theorem horizontalJumpVelocityLInf_coord_ae_zero_off_unitDisk
    (Omega U : ℝ) (i : Fin 3) :
    ∀ᵐ y ∂volume, y ∉ wholePlaneUnitDisk →
      wholePlaneCoordLInf i (horizontalJumpVelocityLInf Omega U) y = 0 := by
  have hcoord :
      (wholePlaneCoordLInf i (horizontalJumpVelocityLInf Omega U) : WholePlane → ℂ) =ᵐ[volume]
        fun y ↦ (EuclideanSpace.proj i)
          ((horizontalJumpVelocityLInf Omega U : WholePlane → C3) y) := by
    simpa only [wholePlaneCoordLInf] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := ∞) (μ := (volume : Measure WholePlane)) (horizontalJumpVelocityLInf Omega U)
  have hjump := horizontalJumpVelocityLInf_coe_ae Omega U
  filter_upwards [hcoord, hjump] with y hcoord_y hjump_y
  intro hy
  have hnorm : 1 < ‖y‖ := by
    by_contra hle
    exact hy (by simpa [wholePlaneUnitDisk, mem_closedBall, dist_zero_right] using not_lt.mp hle)
  rw [hcoord_y, hjump_y, horizontalJumpVelocity_of_one_lt_norm Omega U hnorm]
  simp

/-- The seed velocity `V⁰ = 1_{r<1}(Ω r e_θ + U e₃)` of `eq:jump-flow` vanishes almost
everywhere outside the closed unit disk, coordinate by coordinate. -/
theorem horizontalModeVelocity_coord_ae_zero_off_unitDisk (N Omega : ℝ) (i : Fin 3) :
    ∀ᵐ y ∂volume, y ∉ wholePlaneUnitDisk →
      wholePlaneCoordLInf i (horizontalModeVelocity N Omega) y = 0 :=
  horizontalJumpVelocityLInf_coord_ae_zero_off_unitDisk Omega (jumpAxialSpeed N Omega) i

end HorizontalMode

namespace HorizontalWeakForm

/-! ## The spectrum of `A_w` in the open right half plane -/

/-- The set of parameters of the open right half plane at which the shifted form operator
`𝔸_w(z) = F_z + K_w` fails to be an isomorphism `V → V*`.  By
`horizontalFormOperator_exists_iff` these are exactly the spectral points of `A_w` there
(analytic Fredholm paragraph of §2.3). -/
def horizontalSpectrum (N : ℝ) (w : WholePlaneC3LInf) : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ ¬ (horizontalPencilForm N w z).IsInvertible}

/-- The horizontal spectrum is the noninvertible locus of the compact pencil `1 - K(z)`,
intersected with the open right half plane.  This is the translation performed by
`horizontalPencilForm_isInvertible_iff`. -/
theorem horizontalSpectrum_eq_noninvertibleSet (N : ℝ) (w : WholePlaneC3LInf) :
    horizontalSpectrum N w =
      AnalyticFredholm.noninvertibleSet
          (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w)) ∩
        {z : ℂ | 0 < z.re} := by
  ext z
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨?_, hz⟩
    intro hinv
    exact hnot ((horizontalPencilForm_isInvertible_iff N w hz).mpr hinv)
  · rintro ⟨hnot, hz⟩
    refine ⟨hz, ?_⟩
    intro hinv
    exact hnot ((horizontalPencilForm_isInvertible_iff N w hz).mp hinv)

section Supported

variable (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
  (N : ℝ) (w : WholePlaneC3LInf)
  (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
  (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0)

include hs hsm hw3 hw

/-- **Global analytic-Fredholm discreteness.**  For a velocity supported in a set of finite
measure, the spectral points of `𝔸_w` in the open right half plane form a discrete set.  This
is the conclusion of the analytic Fredholm theorem in §2.3 of the paper. -/
theorem isDiscrete_horizontalSpectrum : IsDiscrete (horizontalSpectrum N w) := by
  have hz₀ : (horizontalGardingShift N w : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simpa using horizontalGardingShift_pos N w
  rw [horizontalSpectrum_eq_noninvertibleSet]
  exact AnalyticFredholm.LocalScalarReductionCover.compactPencil_isDiscrete_noninvertibleSet_inter
    isOpen_rePos isConnected_rePos (analyticOnNhd_horizontalFredholmKernel N w)
    (fun z _ => isCompactOperator_horizontalFredholmKernel_of_ae_zero_off s hs hsm N w hw3 hw z)
    hz₀ (compactPencil_isInvertible_gardingShift N w)

/-- **Isolation.**  Every parameter of the open right half plane has a punctured ball, still
inside the half plane, on which `𝔸_w(z)` is an isomorphism `V → V*`. -/
theorem exists_punctured_ball_isInvertible_horizontalPencilForm
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ {z : ℂ | 0 < z.re} ∧
      ∀ z ∈ Metric.ball z₀ r, z ≠ z₀ → (horizontalPencilForm N w z).IsInvertible := by
  have hbase : (horizontalGardingShift N w : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simpa using horizontalGardingShift_pos N w
  obtain ⟨r, hr, hsub, hpunct⟩ :=
    AnalyticFredholm.LocalScalarReductionCover.compactPencil_exists_punctured_ball_isInvertible
      isOpen_rePos isConnected_rePos (analyticOnNhd_horizontalFredholmKernel N w)
      (fun z _ => isCompactOperator_horizontalFredholmKernel_of_ae_zero_off s hs hsm N w hw3 hw z)
      hbase (compactPencil_isInvertible_gardingShift N w) (z := z₀) hz₀
  refine ⟨r, hr, hsub, fun z hz hne => ?_⟩
  exact (horizontalPencilForm_isInvertible_iff N w (hsub hz)).mpr (hpunct z hz hne)

end Supported

/-! ## Eigenvalues are spectral points -/

/-- An eigenvector of `A_w` makes the shifted form operator singular at its eigenvalue: the
first graph coordinate is a nonzero null vector of `𝔸_w(λ)`. -/
theorem horizontalPencilForm_apply_eq_zero_of_isEigenpair
    (N : ℝ) (w : WholePlaneC3LInf) (lambda : ℂ) (u : HorizontalFormDomain N w)
    (heig : (horizontalFormOperator N w).IsEigenpair lambda u) :
    horizontalPencilForm N w lambda u.1.1 = 0 := by
  refine ContinuousLinearMap.ext fun phi => ?_
  have hrel := horizontalFormDomain_relation N w u phi
  have hsnd : u.1.2 = -(lambda • wholePlaneH1Embedding C2 u.1.1) := by
    have h := heig.2
    change -u.1.2 = lambda • wholePlaneH1Embedding C2 u.1.1 at h
    linear_combination (norm := module) -h
  have h1 := horizontalPencilForm_apply N w lambda u.1.1 phi
  have h2 : inner ℂ (wholePlaneH1Embedding C2 phi) u.1.2 =
      -(lambda * inner ℂ (wholePlaneH1Embedding C2 phi)
        (wholePlaneH1Embedding C2 u.1.1)) := by
    rw [hsnd, inner_neg_right, inner_smul_right]
  calc horizontalPencilForm N w lambda u.1.1 phi
      = horizontalWeakForm N w u.1.1 phi +
          lambda * inner ℂ (wholePlaneH1Embedding C2 phi)
            (wholePlaneH1Embedding C2 u.1.1) := h1
    _ = inner ℂ (wholePlaneH1Embedding C2 phi) u.1.2 +
          lambda * inner ℂ (wholePlaneH1Embedding C2 phi)
            (wholePlaneH1Embedding C2 u.1.1) := by rw [hrel]
    _ = 0 := by linear_combination h2

/-- An eigenvalue of `A_w` with positive real part belongs to the horizontal spectrum.  This
is the converse half of the paper's identification of the spectrum in the open right half
plane with the eigenvalues of `A_w` (analytic Fredholm paragraph of §2.3). -/
theorem mem_horizontalSpectrum_of_isEigenpair
    (N : ℝ) (w : WholePlaneC3LInf) {lambda : ℂ} (hlam : 0 < lambda.re)
    (u : HorizontalFormDomain N w)
    (heig : (horizontalFormOperator N w).IsEigenpair lambda u) :
    lambda ∈ horizontalSpectrum N w := by
  refine ⟨hlam, fun hinv => ?_⟩
  have hzero := horizontalPencilForm_apply_eq_zero_of_isEigenpair N w lambda u heig
  obtain ⟨e, he⟩ := hinv
  have hb : u.1.1 = 0 := by
    have h1 : e u.1.1 = 0 := by
      rw [show e u.1.1 = horizontalPencilForm N w lambda u.1.1 from
        congrArg (fun T : WholePlaneC2H1 →L[ℂ] ComplexAntiDual WholePlaneC2H1 => T u.1.1) he]
      exact hzero
    have := congrArg e.symm h1
    simpa using this
  exact heig.1 (by rw [horizontalFormOperator_embedding_apply, hb, map_zero])

end HorizontalWeakForm

end

end FastDynamo
