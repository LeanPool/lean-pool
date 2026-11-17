/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Graph.CoareaJacobian
public import LeanPool.KLS.FunctionalInequalities.Analysis.LocalInverse
public import LeanPool.KLS.FunctionalInequalities.Analysis.Graph.OpenIntegral
public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Graph.Area

/-! # Codimension-`m` charts for a family of regular levels

The regular case of the codimension-`m` coarea formula needs the fibres of `u : V → W` near a
regular point to be, **simultaneously for all nearby levels**, graphs of one `C¹` map over a fixed
parameter space, with the level itself as a parameter.  This module builds that family.  It is the
codimension-`m` analogue of `RegularChart.lean`, whose scalar chart is
`x ↦ graphRetract ι x + u x • e`.

The chart here maps into a **product**, `Φ x = (ιᵀ x, u x) : H × W`, so no identification of the
normal factor with the ambient space is needed.  Its derivative at a regular point is the
continuous linear equivalence `flattenVectorEquiv`, whose inverse is written down explicitly —
`(y, w) ↦ ι y + κ (Q⁻¹ w)` with `Q = L ∘ κ` — rather than obtained from a dimension count.
Mathlib's
inverse function theorem, through the repository's `exists_contDiffOn_localInverse`, then gives a
`C¹` chart with a `C¹` inverse, and the splitting turns the inverse into a graph:

`D.symm (y, t) = ι y + κ (ψ (y, t))` and `u (D.symm (y, t)) = t`.

`exists_levelGraphFamily` packages this with a globally `C¹` representative `ψ` of the height, an
open parameter domain `Ω` and the open neighbourhood `N` it parametrizes bijectively.  Combined with
the fibre Jacobian identity of `Graph/CoareaJacobian.lean` and the area formula
`hausdorffNormalized_image_vectorGraphMap` of
`Analysis/Vector/Graph/Area.lean`, this is everything the local
coarea equality needs except the fibrewise `m`-dimensional change of variables.

**No coarea formula is proved here**, and no integration is performed.  There is no regularity
hypothesis outside `O`: the chart is built from the local `C¹` representative
`exists_contDiff_eqOn_ball`, exactly as in the scalar file.
-/

@[expose] public section

noncomputable section

open Module Set MeasureTheory
open scoped RealInnerProductSpace ContDiff ENNReal

namespace FunctionalInequalities.Analysis

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-! ### The flattening equivalence -/

omit [FiniteDimensional ℝ V] in
/-- The normal factor is carried isomorphically onto the target by `Q = L ∘ κ`.  At a regular point
this is the statement that `L` restricted to the orthogonal complement of its kernel is invertible,
which is where the codimension `finrank K = finrank W` comes from. -/
def normalEquiv {κ : K →ₗᵢ[ℝ] V} {L : V →L[ℝ] W}
    (hQ : Function.Bijective (L ∘L κ.toContinuousLinearMap)) : K ≃L[ℝ] W :=
  ContinuousLinearEquiv.ofBijective (L ∘L κ.toContinuousLinearMap)
    (LinearMap.ker_eq_bot.2 hQ.1) (LinearMap.range_eq_top.2 hQ.2)

omit [FiniteDimensional ℝ V] in
@[simp] theorem normalEquiv_apply {κ : K →ₗᵢ[ℝ] V} {L : V →L[ℝ] W}
    (hQ : Function.Bijective (L ∘L κ.toContinuousLinearMap)) (z : K) :
    normalEquiv hQ z = L (κ z) := rfl

omit [FiniteDimensional ℝ W] in
/-- The flattening operator `x ↦ (ιᵀ x, L x)`. -/
def flattenVectorCLM (ι : H →ₗᵢ[ℝ] V) (L : V →L[ℝ] W) : V →L[ℝ] H × W :=
  (graphProj ι).prod L

omit [FiniteDimensional ℝ W] in
@[simp] theorem flattenVectorCLM_apply (ι : H →ₗᵢ[ℝ] V) (L : V →L[ℝ] W) (x : V) :
    flattenVectorCLM ι L x = (graphProj ι x, L x) := rfl

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ V] in
/-- The explicit inverse of the flattening operator, `(y, w) ↦ ι y + κ (Q⁻¹ w)`. -/
def unflattenVectorCLM (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) {L : V →L[ℝ] W}
    (hQ : Function.Bijective (L ∘L κ.toContinuousLinearMap)) : (H × W) →L[ℝ] V :=
  ι.toContinuousLinearMap ∘L (ContinuousLinearMap.fst ℝ H W)
    + κ.toContinuousLinearMap ∘L ((normalEquiv hQ).symm : W →L[ℝ] K)
        ∘L (ContinuousLinearMap.snd ℝ H W)

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ V] in
@[simp] theorem unflattenVectorCLM_apply (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) {L : V →L[ℝ] W}
    (hQ : Function.Bijective (L ∘L κ.toContinuousLinearMap)) (p : H × W) :
    unflattenVectorCLM ι κ hQ p = ι p.1 + κ ((normalEquiv hQ).symm p.2) := rfl

/-- **The derivative of the chart at a regular point is a linear equivalence.**  The hypotheses are
that the parameter factor is the kernel direction, `L ∘ ι = 0`, and that the normal factor is
carried isomorphically onto the target.  The inverse is explicit, so no dimension count is used. -/
def flattenVectorEquiv {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V} (hs : IsVectorGraphSplitting ι κ)
    {L : V →L[ℝ] W} (hker : L ∘L ι.toContinuousLinearMap = 0)
    (hQ : Function.Bijective (L ∘L κ.toContinuousLinearMap)) : V ≃L[ℝ] H × W :=
  ContinuousLinearEquiv.equivOfInverse (flattenVectorCLM ι L) (unflattenVectorCLM ι κ hQ)
    (by
      intro v
      have hsplit := hs.split v
      have hzero : L (ι (graphProj ι v)) = 0 := by
        have h := congrArg (fun T : H →L[ℝ] W => T (graphProj ι v)) hker
        simpa using h
      have hL : L v = L (κ (graphProj κ v)) := by
        conv_lhs => rw [← hsplit]
        rw [map_add, hzero, zero_add]
      have hz : (normalEquiv hQ).symm (L v) = graphProj κ v := by
        rw [hL, ← normalEquiv_apply hQ, ContinuousLinearEquiv.symm_apply_apply]
      simpa [hz] using hsplit)
    (by
      rintro ⟨y, w⟩
      have h1 : graphProj ι (ι y + κ ((normalEquiv hQ).symm w)) = y := hs.proj_left _ _
      have h2 : L (ι y + κ ((normalEquiv hQ).symm w)) = w := by
        have hzero : L (ι y) = 0 := by
          have h := congrArg (fun T : H →L[ℝ] W => T y) hker
          simpa using h
        rw [map_add, hzero, zero_add, ← normalEquiv_apply hQ,
          ContinuousLinearEquiv.apply_symm_apply]
      simp only [unflattenVectorCLM_apply, flattenVectorCLM_apply]
      rw [h1, h2])

theorem coe_flattenVectorEquiv {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) {L : V →L[ℝ] W}
    (hker : L ∘L ι.toContinuousLinearMap = 0)
    (hQ : Function.Bijective (L ∘L κ.toContinuousLinearMap)) :
    (flattenVectorEquiv hs hker hQ : V →L[ℝ] H × W) = flattenVectorCLM ι L := rfl

/-! ### The chart -/

section FlatteningChart

omit [FiniteDimensional ℝ W]
/-- The chart that flattens every nearby level of `u`: the parameter component is the tangential
retraction, the normal component is the value of `u`. -/
def flattenVectorChart (ι : H →ₗᵢ[ℝ] V) (u : V → W) : V → H × W :=
  fun x => (graphProj ι x, u x)

theorem contDiffOn_flattenVectorChart (ι : H →ₗᵢ[ℝ] V) {u : V → W} {O : Set V}
    (hu : ContDiffOn ℝ 1 u O) : ContDiffOn ℝ 1 (flattenVectorChart ι u) O :=
  (graphProj ι).contDiff.contDiffOn.prodMk hu

theorem hasFDerivAt_flattenVectorChart (ι : H →ₗᵢ[ℝ] V) {u : V → W} {x : V}
    (hu : DifferentiableAt ℝ u x) :
    HasFDerivAt (flattenVectorChart ι u) ((graphProj ι).prod (fderiv ℝ u x)) x :=
  (graphProj ι).hasFDerivAt.prodMk hu.hasFDerivAt

end FlatteningChart

/-- **A chart flattening every nearby level, with a `C¹` inverse on its whole target.**  The
codimension-`m` analogue of `exists_regularChart`; no regularity outside `O` is used or asserted. -/
theorem exists_vectorRegularChart {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hker : fderiv ℝ u x₀ ∘L ι.toContinuousLinearMap = 0)
    (hQ : Function.Bijective (fderiv ℝ u x₀ ∘L κ.toContinuousLinearMap)) :
    ∃ D : OpenPartialHomeomorph V (H × W),
      (∀ x, D x = (graphProj ι x, u x)) ∧ x₀ ∈ D.source ∧ D.source ⊆ O ∧
      ContDiffOn ℝ 1 D D.source ∧ ContDiffOn ℝ 1 D.symm D.target := by
  have hΦ : ContDiffOn ℝ 1 (flattenVectorChart ι u) O := contDiffOn_flattenVectorChart ι hu
  have hd : HasFDerivAt (flattenVectorChart ι u)
      (flattenVectorEquiv hs hker hQ : V →L[ℝ] H × W) x₀ := by
    rw [coe_flattenVectorEquiv]
    exact hasFDerivAt_flattenVectorChart ι
      ((hu.contDiffAt (hO.mem_nhds hx₀)).differentiableAt one_ne_zero)
  obtain ⟨D, hD, hxD, hDO, hDC, hIC⟩ := exists_contDiffOn_localInverse hO hΦ hx₀ hd
  exact ⟨D, fun x => congrFun hD x, hxD, hDO, hDC, hIC⟩

/-! ### The inverse chart is a family of graphs -/

section LevelHeight

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ W]
/-- The height of the inverse chart: its normal coordinate, as a function of the parameter and the
level jointly. -/
def vectorLevelHeight (κ : K →ₗᵢ[ℝ] V) (D : OpenPartialHomeomorph V (H × W)) (p : H × W) : K :=
  graphProj κ (D.symm p)

theorem contDiffOn_vectorLevelHeight (κ : K →ₗᵢ[ℝ] V) {D : OpenPartialHomeomorph V (H × W)}
    (hD : ContDiffOn ℝ 1 D.symm D.target) :
    ContDiffOn ℝ 1 (vectorLevelHeight κ D) D.target :=
  (graphProj κ).contDiff.comp_contDiffOn hD

end LevelHeight

omit [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] in
/-- **The inverse chart is precisely a graph at each level, and that graph attains the level.**
Both conclusions hold on one joint open parameter domain, which is what a family of fibres needs. -/
theorem vectorLevelChart_inverse {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) {D : OpenPartialHomeomorph V (H × W)} {u : V → W}
    (hD : ∀ x, D x = (graphProj ι x, u x)) {p : H × W} (hp : p ∈ D.target) :
    D.symm p = ι p.1 + κ (vectorLevelHeight κ D p) ∧ u (D.symm p) = p.2 := by
  have h := D.right_inv hp
  rw [hD] at h
  refine ⟨?_, congrArg Prod.snd h⟩
  have h1 : graphProj ι (D.symm p) = p.1 := congrArg Prod.fst h
  have h2 := hs.split (D.symm p)
  rw [h1] at h2
  exact h2.symm

/-! ### The level-graph family -/

/-- **The codimension-`m` local level-graph family.**  Near a point where the parameter factor is
the kernel direction of the differential and the normal factor is carried onto the target, the
fibres of `u` are simultaneously the graphs of one **globally `C¹`** map `ψ` over an open joint
domain `Ω` of parameter and level, and the graph map is a bijection of `Ω` onto an open
neighbourhood `N ⊆ O` of the point.  This is the codimension-`m` analogue of the chart half of
`exists_coarea_neighborhood`; **no integration and no coarea formula is involved**. -/
theorem exists_levelGraphFamily {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hker : fderiv ℝ u x₀ ∘L ι.toContinuousLinearMap = 0)
    (hQ : Function.Bijective (fderiv ℝ u x₀ ∘L κ.toContinuousLinearMap)) :
    ∃ (Ω : Set (H × W)) (ψ : H × W → K) (N : Set V),
      IsOpen Ω ∧ ContDiff ℝ 1 ψ ∧ IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      (∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2) ∧
      (fun p : H × W => ι p.1 + κ (ψ p)) '' Ω = N ∧
      Set.InjOn (fun p : H × W => ι p.1 + κ (ψ p)) Ω := by
  obtain ⟨D, hD, hxD, hDO, hDC, hIC⟩ := exists_vectorRegularChart hs hO hu hx₀ hker hQ
  set p₀ : H × W := D x₀ with hp₀def
  have hp₀ : p₀ ∈ D.target := D.map_source hxD
  obtain ⟨r, ψ, hr, hrT, hψ, hψeq⟩ :=
    exists_contDiff_eqOn_ball D.open_target (contDiffOn_vectorLevelHeight κ hIC) hp₀
  set Ω : Set (H × W) := Metric.ball p₀ r with hΩdef
  have hΩopen : IsOpen Ω := Metric.isOpen_ball
  have hinv : ∀ p ∈ Ω, ι p.1 + κ (ψ p) = D.symm p := by
    intro p hp
    rw [hψeq hp]
    exact ((vectorLevelChart_inverse hs hD (hrT hp)).1).symm
  have hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2 := by
    intro p hp
    rw [hinv p hp]
    exact (vectorLevelChart_inverse hs hD (hrT hp)).2
  set N : Set V := D.source ∩ D ⁻¹' Ω with hNdef
  refine ⟨Ω, ψ, N, hΩopen, hψ, D.isOpen_inter_preimage hΩopen,
    ⟨hxD, Metric.mem_ball_self hr⟩, fun x hx => hDO hx.1, hlevel, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      change ι p.1 + κ (ψ p) ∈ N
      rw [hinv p hp]
      exact ⟨D.map_target (hrT hp), by simp only [Set.mem_preimage, D.right_inv (hrT hp)]; exact hp⟩
    · intro hx
      refine ⟨D x, hx.2, ?_⟩
      change ι (D x).1 + κ (ψ (D x)) = x
      rw [hinv (D x) hx.2, D.left_inv hx.1]
  · intro p hp q hq hpq
    replace hpq : ι p.1 + κ (ψ p) = ι q.1 + κ (ψ q) := hpq
    rw [hinv p hp, hinv q hq] at hpq
    have h := congrArg D hpq
    rwa [D.right_inv (hrT hp), D.right_inv (hrT hq)] at h

/-! ### The hypotheses hold at every regular point -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The kernel of the differential is a parameter direction. -/
theorem comp_ker_subtypeₗᵢ_eq_zero (L : V →L[ℝ] W) :
    L ∘L (LinearMap.ker (L : V →ₗ[ℝ] W)).subtypeₗᵢ.toContinuousLinearMap = 0 := by
  refine ContinuousLinearMap.ext fun y => ?_
  simp

omit [FiniteDimensional ℝ W] in
/-- **At a regular point the orthogonal complement of the kernel is carried onto the target.**
Injectivity is the triviality of `ker L ⊓ (ker L)ᗮ`; surjectivity uses the orthogonal splitting. -/
theorem bijective_comp_orthogonal_subtypeₗᵢ (L : V →L[ℝ] W)
    (hL : Function.Surjective (L : V →ₗ[ℝ] W)) :
    Function.Bijective
      (L ∘L ((LinearMap.ker (L : V →ₗ[ℝ] W))ᗮ).subtypeₗᵢ.toContinuousLinearMap) := by
  set P : Submodule ℝ V := LinearMap.ker (L : V →ₗ[ℝ] W) with hP
  have hs := isVectorGraphSplitting_orthogonal P
  have hzero := comp_ker_subtypeₗᵢ_eq_zero L
  constructor
  · intro z z' h
    simp only [ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap] at h
    have hker : ((z : V) - (z' : V)) ∈ P := by
      simp only [hP, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub]
      simpa using sub_eq_zero.2 h
    have hperp : ((z : V) - (z' : V)) ∈ (Pᗮ : Submodule ℝ V) := sub_mem z.2 z'.2
    have : ((z : V) - (z' : V)) ∈ P ⊓ (Pᗮ : Submodule ℝ V) := ⟨hker, hperp⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext (sub_eq_zero.1 this)
  · intro w
    obtain ⟨v, rfl⟩ := hL w
    refine ⟨graphProj (Pᗮ).subtypeₗᵢ v, ?_⟩
    have hsplit := hs.split v
    have h0 : L (P.subtypeₗᵢ (graphProj P.subtypeₗᵢ v)) = 0 := by
      have h := congrArg (fun T : P →L[ℝ] W => T (graphProj P.subtypeₗᵢ v)) hzero
      simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        zero_apply] at h
      exact h
    have hv := congrArg (fun x : V => L x) hsplit
    simp only [map_add, h0, zero_add] at hv
    simpa using hv

/-- **The level-graph family at a regular point.**  Only `coareaJacobian (fderiv ℝ u x₀) ≠ 0` is
assumed: the parameter space is the kernel of the differential, the normal factor its orthogonal
complement, and the codimension `finrank Pᗮ = finrank W` is automatic.  There is **no** finiteness,
boundedness or regular-value hypothesis. -/
theorem exists_levelGraphFamily_of_coareaJacobian_ne_zero {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hreg : coareaJacobian (fderiv ℝ u x₀) ≠ 0) :
    ∃ (P : Submodule ℝ V) (Ω : Set (P × W)) (ψ : P × W → (Pᗮ : Submodule ℝ V)) (N : Set V),
      IsVectorGraphSplitting P.subtypeₗᵢ (Pᗮ).subtypeₗᵢ ∧
      finrank ℝ (Pᗮ : Submodule ℝ V) = finrank ℝ W ∧
      IsOpen Ω ∧ ContDiff ℝ 1 ψ ∧ IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      (∀ p ∈ Ω, u (P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) = p.2) ∧
      (fun p : P × W => P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) '' Ω = N ∧
      Set.InjOn (fun p : P × W => P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) Ω := by
  have hsurj : Function.Surjective ((fderiv ℝ u x₀ : V →ₗ[ℝ] W)) :=
    (coareaJacobian_ne_zero_iff (fderiv ℝ u x₀)).1 hreg
  refine ⟨LinearMap.ker ((fderiv ℝ u x₀ : V →ₗ[ℝ] W)), ?_⟩
  obtain ⟨Ω, ψ, N, hΩ, hψ, hN, hxN, hNO, hlevel, himg, hinj⟩ :=
    exists_levelGraphFamily (isVectorGraphSplitting_orthogonal _) hO hu hx₀
      (comp_ker_subtypeₗᵢ_eq_zero (fderiv ℝ u x₀))
      (bijective_comp_orthogonal_subtypeₗᵢ (fderiv ℝ u x₀) hsurj)
  exact ⟨Ω, ψ, N, isVectorGraphSplitting_orthogonal _,
    finrank_orthogonal_ker_eq (fderiv ℝ u x₀) hsurj, hΩ, hψ, hN, hxN, hNO, hlevel, himg, hinj⟩

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ K] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] in
/-- **The fibres of the family are graphs.**  The slice of the parametrized neighbourhood at level
`t` is exactly the graph of `y ↦ ψ (y, t)` over the parameter slice — the set whose measure the
normalized area formula `hausdorffNormalized_image_vectorGraphMap` computes. -/
theorem slice_eq_image_vectorGraphMap {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V} {u : V → W}
    {Ω : Set (H × W)} {ψ : H × W → K} {N : Set V}
    (himg : (fun p : H × W => ι p.1 + κ (ψ p)) '' Ω = N)
    (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2) (t : W) :
    N ∩ {x : V | u x = t} = vectorGraphMap ι κ (fun y => ψ (y, t)) '' {y : H | (y, t) ∈ Ω} := by
  ext x
  constructor
  · rintro ⟨hxN, hxt⟩
    rw [← himg] at hxN
    obtain ⟨⟨y, s⟩, hp, rfl⟩ := hxN
    have hs : s = t := by
      have := hlevel (y, s) hp
      simp only at this
      rw [← this]
      exact hxt
    subst hs
    exact ⟨y, hp, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← himg]
      exact ⟨(y, t), hy, rfl⟩
    · exact hlevel (y, t) hy

omit [FiniteDimensional ℝ W] in
/-- **The measure of a fibre of the chart.**  The slice at level `t` is a graph, so the proved
normalized area formula `hausdorffNormalized_image_vectorGraphMap` computes its normalized
`(n - m)`-dimensional measure as a Lebesgue integral of the graph area density over the parameter
slice.  This is the inner integral of the
codimension-`m` coarea formula **with weight one**; the weighted form, which the general statement
needs, is **not** proved — it is the codimension-`m` analogue of `setLIntegral_image_graphMap`. -/
theorem hausdorffNormalized_slice_of_levelGraphFamily [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace V] [BorelSpace V] {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) {u : V → W} {Ω : Set (H × W)} (hΩ : IsOpen Ω)
    {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ) {N : Set V}
    (himg : (fun p : H × W => ι p.1 + κ (ψ p)) '' Ω = N)
    (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2) (t : W) :
    KLS.hausdorffNormalized V (finrank ℝ H) (N ∩ {x : V | u x = t})
      = ∫⁻ y in {y : H | (y, t) ∈ Ω}, ENNReal.ofReal (LinearMap.normDet
          ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, t)) y) : H →ₗ[ℝ] V)))
          ∂(volume : Measure H) := by
  have hslice : MeasurableSet {y : H | (y, t) ∈ Ω} :=
    (hΩ.preimage (continuous_id.prodMk continuous_const)).measurableSet
  rw [slice_eq_image_vectorGraphMap himg hlevel t]
  exact hausdorffNormalized_image_vectorGraphMap ι κ hs.perp
    (hψ.comp (contDiff_id.prodMk contDiff_const)) hslice

/-! ### The chart feeds the fibre Jacobian identity -/

/-- **The two densities match at every point of the chart.**  The level family produced above
satisfies exactly the hypotheses of `normDet_fderiv_mul_coareaJacobian`, so on the chart domain the
ambient coarea density and the graph area density of the normalized area formula agree.  This is
the interface the local coarea equality will consume; **it is not that equality**, which still
needs the fibrewise `m`-dimensional change of variables. -/
theorem normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) (hdim : finrank ℝ K = finrank ℝ W)
    {u : V → W} {O : Set V} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    {Ω : Set (H × W)} (hΩ : IsOpen Ω) {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ)
    (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2)
    (hmem : ∀ p ∈ Ω, ι p.1 + κ (ψ p) ∈ O) {y₀ : H} {t₀ : W} (hp : (y₀, t₀) ∈ Ω) :
    LinearMap.normDet ((fderiv ℝ (fun t => ψ (y₀, t)) t₀ : W →ₗ[ℝ] K))
        * coareaJacobian (fderiv ℝ u (ι y₀ + κ (ψ (y₀, t₀))))
      = LinearMap.normDet
          ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, t₀)) y₀) : H →ₗ[ℝ] V)) :=
  normDet_fderiv_mul_coareaJacobian hs hdim hΩ hψ.contDiffOn hlevel hp
    ((hu.contDiffAt (hO.mem_nhds (hmem _ hp))).differentiableAt one_ne_zero)

end FunctionalInequalities.Analysis
