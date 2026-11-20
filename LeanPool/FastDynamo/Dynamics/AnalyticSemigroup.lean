/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.SemigroupRestriction
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Analytic semigroups

A strongly continuous semigroup `S` on a complex Banach space is *analytic of angle
`δ ∈ (0, π/2]`* if it extends to a holomorphic operator-valued map on the open sector
`Σ_δ = {z ≠ 0, |arg z| < δ}` that obeys the semigroup law there and is strongly continuous
at `0` in every smaller sector (Engel–Nagel, *One-Parameter Semigroups for Linear Evolution
Equations*, Definition II.4.5).  This is the notion of analyticity in the paper's
Lemma A.1 (`lem:semigroup-spectral-growth`).

* `openSector δ` is the sector `Σ_δ`.
* `AnalyticExtension S δ` bundles an extension `toFun : ℂ → X →L[ℂ] X` with the four
  properties of the definition: agreement with `S` on `[0, ∞)`, the semigroup law on
  `Σ_δ`, holomorphy on `Σ_δ` in the operator norm, and strong continuity at `0` within
  each `Σ_δ'`, `δ' < δ`.
* `IsAnalyticSemigroup S δ` says `0 < δ ≤ π/2` and an analytic extension of angle `δ`
  exists.
* `isOpen_openSector`, `isPreconnected_openSector`: for `δ ≤ π` the sector is open and
  preconnected (it is the polar image of `(0, ∞) × (-δ, δ)`).
* `IsAnalyticSemigroup.restrict`: on a Hilbert space, an analytic semigroup restricts to an
  analytic semigroup of the same angle on every closed invariant subspace `W`.  The identity
  theorem shows that the extension maps `W` into itself on the sector
  (`AnalyticExtension.apply_mem`); the restricted extension is the extension compressed by the
  orthogonal projection onto `W`.
-/

@[expose] public section

namespace FastDynamo

open Filter Topology

universe u

/-- The open sector `Σ_δ = {z ∈ ℂ | z ≠ 0, |arg z| < δ}` of half-opening `δ` around the
positive real axis. -/
def openSector (δ : ℝ) : Set ℂ := {z : ℂ | z ≠ 0 ∧ |Complex.arg z| < δ}

/-- A holomorphic extension of a strongly continuous semigroup `S` to the open sector
`openSector δ`, in the sense of Engel–Nagel, Definition II.4.5: an operator-valued map that
agrees with `S` on `[0, ∞)`, obeys the semigroup law on the sector, is holomorphic there in
the operator norm, and converges strongly to the identity at `0` within every smaller
sector. -/
structure AnalyticExtension {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (S : StronglyContinuousSemigroup X) (δ : ℝ) where
  /-- The extended operator family. -/
  toFun : ℂ → X →L[ℂ] X
  /-- Agreement with the semigroup at nonnegative real times. -/
  toFun_ofReal : ∀ t : NNReal, toFun ((t : ℝ) : ℂ) = S t
  /-- The semigroup law on the sector. -/
  toFun_add : ∀ z ∈ openSector δ, ∀ w ∈ openSector δ,
    toFun (z + w) = (toFun z).comp (toFun w)
  /-- Holomorphy on the sector, in the operator norm. -/
  differentiableOn : DifferentiableOn ℂ toFun (openSector δ)
  /-- Strong continuity at `0` within every smaller sector. -/
  tendsto_zero : ∀ δ' : ℝ, 0 < δ' → δ' < δ → ∀ x : X,
    Tendsto (fun z ↦ toFun z x) (𝓝[openSector δ'] 0) (𝓝 x)

/-- A strongly continuous semigroup is *analytic of angle `δ`* if `0 < δ ≤ π/2` and it has
a holomorphic extension to `openSector δ` (Engel–Nagel, Definition II.4.5). -/
def IsAnalyticSemigroup {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (S : StronglyContinuousSemigroup X) (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ Real.pi / 2 ∧ Nonempty (AnalyticExtension S δ)

/-- For `δ ≤ π` the sector `openSector δ` is open: it is the preimage of `(-δ, δ)` under
`Complex.arg` inside the slit plane, where `arg` is continuous. -/
theorem isOpen_openSector {δ : ℝ} (hδ : δ ≤ Real.pi) : IsOpen (openSector δ) := by
  have hcont : ContinuousOn Complex.arg Complex.slitPlane := fun z hz ↦
    (Complex.continuousAt_arg hz).continuousWithinAt
  have heq : openSector δ = Complex.slitPlane ∩ Complex.arg ⁻¹' Set.Ioo (-δ) δ := by
    ext z
    simp only [openSector, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioo, Complex.mem_slitPlane_iff_arg, abs_lt]
    constructor
    · rintro ⟨hz, h1, h2⟩
      exact ⟨⟨by linarith, hz⟩, h1, h2⟩
    · rintro ⟨⟨_, hz⟩, h1, h2⟩
      exact ⟨hz, h1, h2⟩
  rw [heq]
  exact hcont.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo

/-- For `δ ≤ π` the sector `openSector δ` is preconnected: it is the image of the
connected set `(0, ∞) × (-δ, δ)` under the polar parametrisation `(r, θ) ↦ r e^{iθ}`. -/
theorem isPreconnected_openSector {δ : ℝ} (hδ : δ ≤ Real.pi) :
    IsPreconnected (openSector δ) := by
  have heq : openSector δ = (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) ''
      (Set.Ioi 0 ×ˢ Set.Ioo (-δ) δ) := by
    ext z
    simp only [openSector, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
      Set.mem_Ioo, Prod.exists]
    constructor
    · rintro ⟨hz, hlt⟩
      exact ⟨‖z‖, Complex.arg z, ⟨norm_pos_iff.mpr hz, (abs_lt.mp hlt)⟩,
        Complex.norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨r, θ, ⟨hr, h1, h2⟩, rfl⟩
      refine ⟨mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _), ?_⟩
      have hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
      have harg : Complex.arg (Complex.exp (θ * Complex.I)) = θ := by
        rw [Complex.exp_mul_I]
        exact Complex.arg_cos_add_sin_mul_I hθ
      rw [Complex.arg_real_mul _ hr, harg, abs_lt]
      exact ⟨h1, h2⟩
  rw [heq]
  refine (isPreconnected_Ioi.prod isPreconnected_Ioo).image _ ?_
  exact (Continuous.continuousOn (by fun_prop))

/-- `1` lies in every sector of positive angle. -/
theorem one_mem_openSector {δ : ℝ} (hδ : 0 < δ) : (1 : ℂ) ∈ openSector δ :=
  ⟨one_ne_zero, by simpa using hδ⟩

/-- An analytic extension maps a closed subspace that the semigroup leaves invariant into
itself at every point of its sector.  For `x ∈ W`, the map `z ↦ (1 - P_W) (T z x)`, with
`P_W` the orthogonal projection onto `W`, is holomorphic on the preconnected sector and
vanishes on the positive real axis, so it vanishes identically by the identity theorem. -/
theorem AnalyticExtension.apply_mem {X : Type u}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {S : StronglyContinuousSemigroup X} {δ : ℝ} (T : AnalyticExtension S δ)
    (hδ0 : 0 < δ) (hδ : δ ≤ Real.pi) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (hinv : ∀ (t : NNReal) (x : X), x ∈ W → S t x ∈ W) {z : ℂ} (hz : z ∈ openSector δ)
    {x : X} (hx : x ∈ W) : T.toFun z x ∈ W := by
  have : CompleteSpace W := hW.completeSpace_coe
  set f : ℂ → X := fun w ↦ T.toFun w x - W.starProjection (T.toFun w x) with hf
  have hdiff : DifferentiableOn ℂ f (openSector δ) := by
    have happ : DifferentiableOn ℂ (fun w ↦ T.toFun w x) (openSector δ) :=
      fun w hw ↦ DifferentiableAt.comp_differentiableWithinAt w
        (ContinuousLinearMap.apply ℂ X x).differentiableAt (T.differentiableOn w hw)
    exact happ.sub ((W.starProjection).differentiable.comp_differentiableOn happ)
  have hzero : ∀ t : ℝ, 0 < t → f t = 0 := by
    intro t ht
    have h := T.toFun_ofReal (Real.toNNReal t)
    rw [Real.coe_toNNReal t ht.le] at h
    simp only [hf, h]
    rw [Submodule.starProjection_eq_self_iff.mpr (hinv _ x hx), sub_self]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = 0 := by
    have hlim : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Complex.ofReal_eq_one] using (ne_of_gt ht)
    have hev : ∀ᶠ t : ℝ in 𝓝[>] 1, f t = 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hzero t (lt_trans one_pos ht)
    exact hlim.frequently hev.frequently
  have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (hdiff.analyticOnNhd (isOpen_openSector hδ)) (isPreconnected_openSector hδ)
    (one_mem_openSector hδ0) hfreq hz
  have hfz : T.toFun z x = W.starProjection (T.toFun z x) := sub_eq_zero.mp hall
  rw [hfz]
  exact Submodule.coe_mem _

/-- **Restriction of an analytic semigroup.**  An analytic semigroup of angle `δ` on a
Hilbert space restricts, on a closed subspace `W` that it leaves invariant, to an analytic
semigroup of the same angle.  The extension of the restriction is
`z ↦ P_W ∘ T z ∘ ι_W`, with `P_W` the orthogonal projection onto `W`; on the sector and on
`[0, ∞)` the extension maps `W` into itself (`AnalyticExtension.apply_mem`), so `P_W` acts
there as the identity. -/
theorem IsAnalyticSemigroup.restrict {X : Type u}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {S : StronglyContinuousSemigroup X} {δ : ℝ} (hS : IsAnalyticSemigroup S δ)
    (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (hinv : ∀ (t : NNReal) (x : X), x ∈ W → S t x ∈ W) :
    IsAnalyticSemigroup (S.restrict W hinv) δ := by
  obtain ⟨hδ0, hδ, ⟨T⟩⟩ := hS
  have : CompleteSpace W := hW.completeSpace_coe
  have hπ : δ ≤ Real.pi := hδ.trans (by linarith [Real.pi_pos])
  have hmem : ∀ z ∈ openSector δ, ∀ x : W, T.toFun z x ∈ W := fun z hz x ↦
    T.apply_mem hδ0 hπ W hW hinv hz x.2
  have hproj : ∀ z ∈ openSector δ, ∀ x : W,
      ((W.orthogonalProjectionOnto (T.toFun z x) : W) : X) = T.toFun z x := fun z hz x ↦ by
    rw [← Submodule.starProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr (hmem z hz x)]
  refine ⟨hδ0, hδ, ⟨⟨fun z ↦
    (W.orthogonalProjectionOnto).comp ((T.toFun z).comp W.subtypeL), ?_, ?_, ?_, ?_⟩⟩⟩
  · intro t
    ext x
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, T.toFun_ofReal,
      StronglyContinuousSemigroup.restrict_apply]
    rw [← Submodule.starProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr (hinv t x x.2)]
  · intro z hz w hw
    ext x
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, T.toFun_add z hz w hw]
    rw [hproj w hw x]
  · exact (differentiableOn_const _).clm_comp
      (T.differentiableOn.clm_comp (differentiableOn_const _))
  · intro δ' hδ'0 hδ' x
    rw [tendsto_subtype_rng]
    refine (T.tendsto_zero δ' hδ'0 hδ' x).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ∈ openSector δ := ⟨hz.1, hz.2.trans hδ'⟩
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact (hproj z hz' x).symm

end FastDynamo
