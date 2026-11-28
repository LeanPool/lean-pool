/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.RellichCompactness
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.Algebra.Module.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev spaces on open sets as Hilbert spaces

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω ⊆ V` open and `s` real. Mathlib's Sobolev space `H^s(V) = H^{s,2}(V, ℂ)` is a Hilbert space;
the Sobolev spaces on `Ω` are built inside it, as in Chandler-Wilde, Hewett and Moiola (§3.1)
and McLean (Chapter 3), and are Hilbert spaces as well.

* **Vanishing on `Ω`**: `Rd.vanishOn s Ω` is the closed subspace of the `U ∈ H^s(V)` with
  `U(φ) = 0` for every test function `φ` of `Ω` (evaluation `Rd.besselEvalCLM` is continuous);
  for `s = 1` it consists of the `U` vanishing almost everywhere on `Ω`
  (`Rd.mem_vanishOn_one_iff`).
* **`H^s(Ω)`**: `Rd.RestrictionSpace s Ω` is the orthogonal complement of `Rd.vanishOn s Ω`,
  with the restriction `Rd.restrictProj`, the orthogonal projection. It is isometric to the
  quotient `H^s(V) ⧸ vanishOn s Ω` (`Rd.quotientEquivRestrictionSpace`), so its norm is the
  minimum of the norms of the extensions.
* **`H^1(Ω)` in `L_2(Ω)`**: `Rd.restrictL2` is injective, has norm at most `1`, and is compact
  for bounded `Ω` (Rellich's theorem, `Rd.isCompactOperator_restrictL2`); `U|_Ω = u` whenever
  `U ∈ H^1(V)` agrees with `u ∈ H^1(Ω)` on `Ω` (`Rd.restrictProj_eq_of_ae_eq`).
* **Weak derivatives**: the `L_2` function of `U ∈ H^1(V)` lies in `W^1_2(V)` and in `W^1_2(Ω)`
  for every open `Ω` (`Rd.memSobolev_toL2`, `Rd.memWeakSobolev_toL2`), every function of
  `W^1_2(V)` is one (`Rd.exists_toL2_eq_of_memSobolev`), with
  `‖U‖² = ‖U‖_2² + (2π)⁻² ∑_i ‖∂_{e_i} U‖_2²` (`Rd.sq_norm_eq_of_hasWeakLineDeriv`), so
  `‖U‖ ≤ ‖U‖_2 + ∑_i ‖∂_{e_i} U‖_2` (`Rd.norm_le_norm_toL2_add_sum`); the weak derivative
  `∂_v` is a bounded operator `H^1(V) → L_2(V)` of norm at most `2π ‖v‖` (`Rd.weakDerivL2`,
  `Rd.norm_weakDerivL2_le`); the weak derivatives of an element vanishing on `Ω` vanish on `Ω`.
  For `u ∈ H^1(Ω)`, the `L_2(Ω)` norm of `u` and `(2π)⁻¹` times the `L_2(Ω)` norm of its weak
  gradient are bounded by the norm of `H^1(Ω)`:
  `‖u|_Ω‖_2² + (2π)⁻² ∑_i ‖(∂_{e_i} u)|_Ω‖_2² ≤ ‖u‖²` (`Rd.sq_norm_restr_add_sum_le`,
  `Rd.sq_norm_restrictL2_add_sum_le`).
* **Schwartz functions are dense**: the Schwartz functions form a dense subspace of every
  `H^s(V)` (`Rd.ofSchwartz`, a continuous linear map, `Rd.denseRange_ofSchwartz`), and so do the
  compactly supported ones (`Rd.dense_ofSchwartz_hasCompactSupport`).
* **Differences in `H^1(V)`**: `‖Δ_v ι U‖_2 ≤ 2π ‖v‖ ‖U‖` (`Rd.norm_fwdDiffL2_toL2_le`), first
  for Schwartz functions, then by density; hence `ω_r(ι U, 2^(-k))_2 ≤ 2^(r-1) 2π 2^(-k) ‖U‖`
  for `r ≥ 1` (`Rd.lpModulus_toL2_le`).
* **`HTilde^s(Ω)` and `H^s_0(Ω)`**: every test function of `Ω` lies in every `H^s(V)` (`Rd.ofTest`),
  and every Schwartz function with compact support in `Ω` lies in the span of the test functions
  (`Rd.ofSchwartz_mem_testSpan`).
  `Rd.tildeSpace s Ω` is the closure of the test functions of `Ω` in `H^s(V)`,
  `Rd.zeroBoundarySpace s Ω` the closure of their restrictions in `H^s(Ω)`. For `s = 1` and every
  open `Ω`, restriction is an isometry of `HTilde^1(Ω)` onto `H^1_0(Ω)`
  (`Rd.tildeEquivZeroBoundary`),
  and inside `H^1(V)` the two are the same subspace (`Rd.tildeSpace_one_le_orthogonal`,
  `Rd.coe_tildeEquivZeroBoundary_symm_apply`); the elements of `HTilde^1(Ω)` vanish outside `Ω`
  (`Rd.toL2_ae_eq_zero_of_mem_tildeSpace`). On the whole space, `HTilde^s(V) = H^s(V)`
  (`Rd.tildeSpace_top`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal SchwartzMap Real BesselPotentialSpace Distributions LineDeriv
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Evaluation at a Schwartz function -/

/-- **Evaluation at a Schwartz function is a bounded functional on `H^s(V)`**: for a Schwartz
function `φ`, the map `U ↦ U(φ)`, which evaluates the tempered distribution of `U ∈ H^s(V)` at
`φ`, as a continuous linear functional. It is the composition `U ↦ J_s U ∈ L_2(V)`,
`g ↦ J_{-s} g ∈ 𝓢'(V, ℂ)`, and evaluation at `φ`, all continuous
(Mathlib's `PointwiseConvergenceCLM.evalCLM`). -/
noncomputable def besselEvalCLM (s : ℝ) (φ : 𝓢(V, ℂ)) : H^{s}(V) →L[ℂ] ℂ :=
  PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ ∘L besselPotential V ℂ (-s) ∘L
    Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2 ∘L
    (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).toLinearIsometry.toContinuousLinearMap

/-- `besselEvalCLM s φ U = U(φ)`, the tempered distribution of `U` evaluated at `φ`, since
`J_{-s}(J_s U) = U` (Mathlib's `BesselPotentialSpace.besselPotential_neg_toLp_eq`). -/
@[simp]
theorem besselEvalCLM_apply (s : ℝ) (φ : 𝓢(V, ℂ)) (U : H^{s}(V)) :
    besselEvalCLM s φ U = U.toDistr φ := by
  simp only [besselEvalCLM, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    BesselPotentialSpace.toLpₗᵢ_apply, Lp.toTemperedDistributionCLM_apply,
    BesselPotentialSpace.besselPotential_neg_toLp_eq, PointwiseConvergenceCLM.evalCLM_apply]
  -- `U φ = U φ`: Mathlib's `evalCLM_apply` applies `U` through another coercion to functions
  rfl

/-- For every Schwartz function `φ`, `U ↦ U(φ)` is continuous on `H^s(V)`. -/
theorem continuous_toDistr_apply (s : ℝ) (φ : 𝓢(V, ℂ)) :
    Continuous fun U : H^{s}(V) => U.toDistr φ :=
  (besselEvalCLM s φ).continuous.congr fun U => besselEvalCLM_apply s φ U

/-! ### Distributions vanishing on `Ω` -/

/-- **The elements of `H^s(V)` vanishing on `Ω`**: the `U ∈ H^s(V)` whose tempered distribution
vanishes on every real test function of the open set `Ω`, `U(φ) = 0` for all `φ ∈ 𝓓(Ω)`
(`Rd.mem_vanishOn_iff`). It is a closed subspace (`Rd.isClosed_vanishOn`); for `s = 1` it
consists of the `U` that vanish almost everywhere on `Ω` (`Rd.mem_vanishOn_one_iff`). -/
noncomputable def vanishOn (s : ℝ) (Ω : Opens V) : Submodule ℂ H^{s}(V) :=
  ⨅ φ : 𝓓(Ω, ℝ), (besselEvalCLM s (testSchwartz φ)).ker

/-- `U` vanishes on `Ω` iff `U(φ) = 0` for every real test function `φ` of `Ω`. -/
theorem mem_vanishOn_iff {s : ℝ} {Ω : Opens V} (U : H^{s}(V)) :
    U ∈ vanishOn s Ω ↔ ∀ φ : 𝓓(Ω, ℝ), U.toDistr (testSchwartz φ) = 0 := by
  simp [vanishOn, Submodule.mem_iInf]

/-- The elements of `H^s(V)` vanishing on `Ω` form a closed subspace: an intersection of kernels
of the continuous functionals `U ↦ U(φ)` (Mathlib's `ContinuousLinearMap.isClosed_ker`). -/
theorem isClosed_vanishOn (s : ℝ) (Ω : Opens V) : IsClosed (vanishOn s Ω : Set H^{s}(V)) := by
  rw [vanishOn, Submodule.coe_iInf]
  exact isClosed_iInter fun φ => ContinuousLinearMap.isClosed_ker _

/-- The subspace `Rd.vanishOn s Ω` is complete, as a closed subspace of the complete space
`H^s(V)`; hence it has an orthogonal projection. -/
instance completeSpace_vanishOn (s : ℝ) (Ω : Opens V) : CompleteSpace (vanishOn s Ω) :=
  (isClosed_vanishOn s Ω).completeSpace_coe

/-- For `U ∈ H^1(V)` and a real test function `φ` of `Ω`, `U(φ) = ∫ φ · U`, the integral of `φ`
against the `L_2` function of `U` (`Rd.toTemperedDistribution_toL2`). -/
theorem toDistr_testSchwartz_eq_integral {Ω : Opens V} (U : H^{1}(V)) (φ : 𝓓(Ω, ℝ)) :
    U.toDistr (testSchwartz φ) = ∫ x, ((φ x : ℝ) : ℂ) * toL2 U x := by
  rw [← toTemperedDistribution_toL2, Lp.toTemperedDistribution_apply]
  simp [smul_eq_mul]

/-- **Vanishing on `Ω` for `s = 1`**: `U ∈ H^1(V)` vanishes on the open set `Ω` iff its `L_2`
function vanishes almost everywhere on `Ω`. `⇐`: the integrand `φ · U` vanishes almost
everywhere; `⇒`: a locally integrable function on `Ω` with vanishing integrals against all
smooth compactly supported real functions in `Ω` vanishes almost everywhere on `Ω` (Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem mem_vanishOn_one_iff {Ω : Opens V} (U : H^{1}(V)) :
    U ∈ vanishOn 1 Ω ↔ (toL2 U : V → ℂ) =ᵐ[volume.restrict (Ω : Set V)] 0 := by
  rw [mem_vanishOn_iff, Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  constructor
  · intro hU
    refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((Lp.memLp (toL2 U)).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      fun g hg hgc hgs => ?_
    have h := hU ⟨g, hg, hgc, hgs⟩
    rw [toDistr_testSchwartz_eq_integral] at h
    simpa [Complex.real_smul] using h
  · intro hU φ
    rw [toDistr_testSchwartz_eq_integral]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hU] with x hx
    by_cases hxΩ : x ∈ (Ω : Set V)
    · simp [hx hxΩ]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hxΩ (φ.tsupport_subset h)]

/-- For `s = 1`, `U` vanishes on `Ω` iff the restriction to `L_2(Ω)` of the `L_2` function of
`U` is zero. -/
theorem mem_vanishOn_one_iff_restrict_eq_zero {Ω : Opens V} (U : H^{1}(V)) :
    U ∈ vanishOn 1 Ω ↔ LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) (toL2 U) = 0 := by
  rw [mem_vanishOn_one_iff, Lp.eq_zero_iff_ae_eq_zero]
  constructor <;> intro h
  · exact (LpToLpRestrictCLM_coeFn ℂ _ _).trans h
  · exact (LpToLpRestrictCLM_coeFn ℂ _ _).symm.trans h

/-- For `s = 1`, the elements vanishing on `Ω` form the kernel of `U ↦ U|_Ω`, the restriction of
the `L_2` function of `U` to `L_2(Ω)`. -/
theorem vanishOn_one_eq_ker (Ω : Opens V) :
    vanishOn 1 Ω = (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) ∘L toL2).ker := by
  ext U
  rw [mem_vanishOn_one_iff_restrict_eq_zero, LinearMap.mem_ker]
  rfl

/-! ### The restriction space `H^s(Ω)` -/

/-- **The Sobolev space `H^s(Ω)`** on an open set `Ω`, for every real `s`, as a Hilbert space:
the orthogonal complement in `H^s(V)` of the elements vanishing on `Ω`. It is isometric to the
quotient of `H^s(V)` by them (`Rd.quotientEquivRestrictionSpace`), so its norm is the infimum
of the norms of all extensions (`Rd.norm_restrictProj_le_of_mem`,
`Rd.exists_norm_restrictProj_eq`); this is the space `H^s(Ω)` of Chandler-Wilde, Hewett and
Moiola (§3.1.4) and of McLean (Chapter 3). -/
abbrev RestrictionSpace (s : ℝ) (Ω : Opens V) := ↥(vanishOn s Ω)ᗮ

/-- **Restriction to `Ω`**: the orthogonal projection of `H^s(V)` onto `H^s(Ω)`, an operator of
norm at most `1` whose kernel is `Rd.vanishOn s Ω` (`Rd.restrictProj_eq_zero_iff`). -/
noncomputable def restrictProj (s : ℝ) (Ω : Opens V) : H^{s}(V) →L[ℂ] RestrictionSpace s Ω :=
  (vanishOn s Ω)ᗮ.orthogonalProjectionOnto

variable {s : ℝ} {Ω : Opens V}

/-- The restriction has norm at most `1`: `‖U|_Ω‖ ≤ ‖U‖`. -/
theorem norm_restrictProj_apply_le (U : H^{s}(V)) : ‖restrictProj s Ω U‖ ≤ ‖U‖ :=
  Submodule.norm_orthogonalProjectionOnto_apply_le _ U

/-- The kernel of the restriction consists of the elements vanishing on `Ω` (Mathlib's
`Submodule.orthogonalProjectionOnto_eq_zero_iff`, `Submodule.orthogonal_orthogonal`). -/
theorem restrictProj_eq_zero_iff (U : H^{s}(V)) : restrictProj s Ω U = 0 ↔ U ∈ vanishOn s Ω := by
  rw [restrictProj, Submodule.orthogonalProjectionOnto_eq_zero_iff,
    Submodule.orthogonal_orthogonal]

/-- The restriction is the identity on `H^s(Ω)`. -/
@[simp]
theorem restrictProj_coe (u : RestrictionSpace s Ω) : restrictProj s Ω (u : H^{s}(V)) = u :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self u

/-- Every element of `H^s(Ω)` is the restriction of an element of `H^s(V)`. -/
theorem restrictProj_surjective : Function.Surjective (restrictProj s Ω) :=
  fun u => ⟨u, restrictProj_coe u⟩

/-- `U` and its restriction differ by an element vanishing on `Ω`. -/
theorem sub_restrictProj_mem (U : H^{s}(V)) :
    U - (restrictProj s Ω U : H^{s}(V)) ∈ vanishOn s Ω := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (vanishOn s Ω)ᗮ) U
  rwa [Submodule.orthogonal_orthogonal] at h

/-- **`H^s(Ω)` as a quotient**: `H^s(V) ⧸ vanishOn s Ω` is isometrically isomorphic to
`H^s(Ω)`. This holds by the definition of `H^s(Ω)` as an orthogonal complement (Mathlib's
`Submodule.quotientEquivOrthogonal`). -/
noncomputable def quotientEquivRestrictionSpace (s : ℝ) (Ω : Opens V) :
    (H^{s}(V) ⧸ vanishOn s Ω) ≃ₗᵢ[ℂ] RestrictionSpace s Ω :=
  Submodule.quotientEquivOrthogonal _

/-- The class of `U` corresponds to the restriction of `U`. -/
theorem quotientEquivRestrictionSpace_mk (U : H^{s}(V)) :
    quotientEquivRestrictionSpace s Ω (Submodule.Quotient.mk U) = restrictProj s Ω U := by
  have h : (Submodule.Quotient.mk U : H^{s}(V) ⧸ vanishOn s Ω) =
      Submodule.Quotient.mk (restrictProj s Ω U : H^{s}(V)) :=
    (Submodule.Quotient.eq _).2 (sub_restrictProj_mem U)
  rw [quotientEquivRestrictionSpace, h,
    Submodule.quotientEquivOrthogonal_mk _ _ (restrictProj s Ω U).2]

/-- **The norm of `H^s(Ω)` is at most that of every extension**: `‖U|_Ω‖ ≤ ‖U + W‖` for every
`W` vanishing on `Ω` (Mathlib's `Submodule.Quotient.norm_mk_le`). -/
theorem norm_restrictProj_le_of_mem (U : H^{s}(V)) {W : H^{s}(V)} (hW : W ∈ vanishOn s Ω) :
    ‖restrictProj s Ω U‖ ≤ ‖U + W‖ := by
  have h : (Submodule.Quotient.mk U : H^{s}(V) ⧸ vanishOn s Ω) = Submodule.Quotient.mk (U + W) :=
    (Submodule.Quotient.eq _).2 (by simpa using neg_mem hW)
  rw [← quotientEquivRestrictionSpace_mk, LinearIsometryEquiv.norm_map, h]
  exact Submodule.Quotient.norm_mk_le _ _

/-- **The infimum is attained**: for every `U ∈ H^s(V)` some `W` vanishing on `Ω` has
`‖U|_Ω‖ = ‖U + W‖`, namely `W = U|_Ω - U`. -/
theorem exists_norm_restrictProj_eq (U : H^{s}(V)) :
    ∃ W ∈ vanishOn s Ω, ‖restrictProj s Ω U‖ = ‖U + W‖ :=
  ⟨(restrictProj s Ω U : H^{s}(V)) - U, by simpa using neg_mem (sub_restrictProj_mem U),
    by simp⟩

/-! ### Restriction to `L_2(Ω)` and Rellich's theorem -/

variable (Ω) in
/-- **`H^1(Ω)` in `L_2(Ω)`**: the bounded operator `u ↦ u|_Ω` from `H^1(Ω)` to `L_2(Ω)`, the
restriction of the `L_2` function of `u ∈ H^1(V)` to `Ω`. It is injective
(`Rd.restrictL2_injective`), has norm at most `1` (`Rd.norm_restrictL2_apply_le`), and is compact
for bounded `Ω` (`Rd.isCompactOperator_restrictL2`). -/
noncomputable def restrictL2 : RestrictionSpace 1 Ω →L[ℂ] Lp ℂ 2 (volume.restrict (Ω : Set V)) :=
  (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) ∘L toL2) ∘L (vanishOn 1 Ω)ᗮ.subtypeL

/-- `restrictL2 Ω u` is the restriction to `Ω` of the `L_2` function of `u`. -/
theorem restrictL2_apply (u : RestrictionSpace 1 Ω) :
    restrictL2 Ω u = LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) (toL2 (u : H^{1}(V))) :=
  rfl

/-- **`u|_Ω = f|_Ω` as an equation of functions**: for `u ∈ H^1(Ω)` and `f ∈ L_2(V)`,
`restrictL2 Ω u` is the restriction of `f` to `Ω` iff the `L_2` function of `u` equals `f` almost
everywhere on `Ω` (Mathlib's `LpToLpRestrictCLM_coeFn`). -/
theorem restrictL2_eq_iff_ae_eq (u : RestrictionSpace 1 Ω) (f : Lp ℂ 2 (volume : Measure V)) :
    restrictL2 Ω u = LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) f ↔
      (toL2 (u : H^{1}(V)) : V → ℂ) =ᵐ[volume.restrict (Ω : Set V)] f := by
  rw [restrictL2_apply, Lp.ext_iff]
  exact ⟨fun h => (LpToLpRestrictCLM_coeFn ℂ _ _).symm.trans
      (h.trans (LpToLpRestrictCLM_coeFn ℂ _ _)),
    fun h => (LpToLpRestrictCLM_coeFn ℂ _ _).trans
      (h.trans (LpToLpRestrictCLM_coeFn ℂ _ _).symm)⟩

/-- **An element of `H^1(Ω)` is determined by its values on `Ω`**: `u ↦ u|_Ω` is injective,
since its kernel lies in `vanishOn 1 Ω ⊓ (vanishOn 1 Ω)ᗮ = ⊥`
(`Rd.mem_vanishOn_one_iff_restrict_eq_zero`, Mathlib's
`Submodule.inf_orthogonal_eq_bot`). -/
theorem restrictL2_injective : Function.Injective (restrictL2 Ω) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  have h1 : (u : H^{1}(V)) ∈ vanishOn 1 Ω := (mem_vanishOn_one_iff_restrict_eq_zero _).2 hu
  have h2 : (u : H^{1}(V)) ∈ vanishOn 1 Ω ⊓ (vanishOn 1 Ω)ᗮ := ⟨h1, u.2⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
  exact Subtype.ext h2

/-- `‖u|_Ω‖_{L_2(Ω)} ≤ ‖u‖_{H^1(Ω)}` (`Rd.norm_toL2_le` and Mathlib's
`norm_Lp_toLp_restrict_le`). -/
theorem norm_restrictL2_apply_le (u : RestrictionSpace 1 Ω) : ‖restrictL2 Ω u‖ ≤ ‖u‖ :=
  (norm_Lp_toLp_restrict_le _ _).trans (norm_toL2_le _)

/-- The restriction to `L_2(Ω)` of `U|_Ω ∈ H^1(Ω)` is the restriction of the `L_2` function of
`U`, because `U - U|_Ω` vanishes on `Ω` (`Rd.sub_restrictProj_mem`). -/
theorem restrictL2_restrictProj (U : H^{1}(V)) :
    restrictL2 Ω (restrictProj 1 Ω U) = LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) (toL2 U) := by
  have h := (mem_vanishOn_one_iff_restrict_eq_zero _).1 (sub_restrictProj_mem (s := 1) (Ω := Ω) U)
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

/-- **The restriction of an element that agrees with `u` on `Ω`**: if `U ∈ H^1(V)` and
`u ∈ H^1(Ω)` agree almost everywhere on `Ω`, then `U|_Ω = u`, since both have the restriction
`(ι U)|_Ω` in `L_2(Ω)` (`Rd.restrictL2_restrictProj`, `Rd.restrictL2_eq_iff_ae_eq`) and
`u ↦ u|_Ω` is injective (`Rd.restrictL2_injective`). -/
theorem restrictProj_eq_of_ae_eq {U : H^{1}(V)} {u : RestrictionSpace 1 Ω}
    (h : (toL2 U : V → ℂ) =ᵐ[volume.restrict (Ω : Set V)] toL2 (u : H^{1}(V))) :
    restrictProj 1 Ω U = u :=
  restrictL2_injective ((restrictL2_restrictProj U).trans
    ((restrictL2_eq_iff_ae_eq u (toL2 U)).2 h.symm).symm)

/-- **Rellich's theorem for `H^1(Ω)`**: for every bounded open set `Ω ⊆ V`, the embedding
`H^1(Ω) → L_2(Ω)` is a compact operator. For the restriction space `H^1(Ω)`, this is the
compactness that Assumption F of Hiptmair, Pauly and Schulz asks for; on bounded Lipschitz
domains the restriction space is the weak-derivative space by the extension theorem. The proof
is Rellich's theorem for `H^1(V)` (`Rd.isCompactOperator_restr_toL2`) composed with the
bounded inclusion of `H^1(Ω)` into `H^1(V)` (Mathlib's `IsCompactOperator.comp_clm`). -/
theorem isCompactOperator_restrictL2 (hΩ : Bornology.IsBounded (Ω : Set V)) :
    IsCompactOperator (restrictL2 Ω) :=
  (isCompactOperator_restr_toL2 hΩ).comp_clm _

/-! ### Weak derivatives of `H^1(V)` functions -/

/-- **`H^1(V) ⊆ W^1_2(V)`**: the `L_2` function of every `U ∈ H^1(V)` lies in the Sobolev space
`W^1_2(V)` of weak derivatives (`Rd.memSobolev_one_iff`). -/
theorem memSobolev_toL2 (U : H^{1}(V)) : MemSobolev 1 (toL2 U) := by
  rw [memSobolev_one_iff, toTemperedDistribution_toL2]
  exact U.memSobolev_toDistr

/-- **`W^1_2(V)` functions are elements of `H^1(V)`**: for `f ∈ L_2(V)` with `f ∈ W^1_2(V)` there
is `U ∈ H^1(V)` whose `L_2` function is `f` (`Rd.memSobolev_one_iff`, `Rd.toL2_eq_of_toDistr_eq`);
the converse of `Rd.memSobolev_toL2`. -/
theorem exists_toL2_eq_of_memSobolev {f : Lp ℂ 2 (volume : Measure V)} (hf : MemSobolev 1 f) :
    ∃ U : H^{1}(V), toL2 U = f :=
  ⟨_, toL2_eq_of_toDistr_eq ((memSobolev_one_iff f).1 hf).toBesselPotentialSpace
    (TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr _).symm⟩

variable (Ω) in
/-- **`H^1(V) ⊆ W^1_2(Ω)`**: for every open `Ω`, the `L_2` function of `U ∈ H^1(V)` lies in the
Sobolev space `W^1_2(Ω)` of weak derivatives on `Ω` (`Rd.memSobolev_toL2`, restricted by
`Rd.MemWeakSobolev.mono_set`); in particular so does every `u ∈ H^1(Ω)`. -/
theorem memWeakSobolev_toL2 (U : H^{1}(V)) : MemWeakSobolev Ω 1 2 (toL2 U) :=
  MemWeakSobolev.mono_set (memSobolev_toL2 U) le_top

/-- For `U ∈ H^1(V)` and every direction `v`, the `L_2` function of `U` has a weak derivative
`∂_v` on `V` in `L_2(V)`. -/
theorem exists_hasWeakLineDeriv_toL2 (U : H^{1}(V)) (v : V) :
    ∃ g : Lp ℂ 2 (volume : Measure V), HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (toL2 U) g := by
  obtain ⟨g, hg⟩ := (memSobolev_iff_tempered _).1 (memSobolev_toL2 U) 1 le_rfl fun _ => v
  exact ⟨g, hasWeakLineDeriv_top_iff.2 hg⟩

/-- **The weak derivatives of `H^1(V)` are bounded**: if `g ∈ L_2(V)` is the weak derivative
`∂_v` on `V` of the `L_2` function of `U ∈ H^1(V)`, then `‖g‖_2 ≤ 2π ‖v‖ ‖U‖`
(`Rd.enorm_le_of_hasWeakLineDeriv` with `J_1 f = U`). -/
theorem norm_le_of_hasWeakLineDeriv_toL2 {v : V} {U : H^{1}(V)}
    {g : Lp ℂ 2 (volume : Measure V)} (h : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (toL2 U) g) :
    ‖g‖ ≤ 2 * π * ‖v‖ * ‖U‖ := by
  have hfh : besselPotential V ℂ 1 ((toL2 U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (U.toLp : 𝓢'(V, ℂ)) := by
    rw [toTemperedDistribution_toL2]
    exact U.bessel_toDistr_eq_toLp
  have he := enorm_le_of_hasWeakLineDeriv h hfh
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity),
    BesselPotentialSpace.norm_toLp_eq] at he
  exact he

/-- The weak derivative `∂_v` of the `L_2` functions of `H^1(V)` as a linear map: `U` goes to the
weak derivative chosen in `Rd.exists_hasWeakLineDeriv_toL2`, which is linear in `U` because weak
derivatives on `V` are unique classes (`Rd.HasWeakLineDeriv.eq_of_top`). -/
noncomputable def weakDerivL2Linear (v : V) : H^{1}(V) →ₗ[ℂ] Lp ℂ 2 (volume : Measure V) where
  toFun U := (exists_hasWeakLineDeriv_toL2 U v).choose
  map_add' U W := by
    refine HasWeakLineDeriv.eq_of_top (exists_hasWeakLineDeriv_toL2 (U + W) v).choose_spec ?_
    refine ((exists_hasWeakLineDeriv_toL2 U v).choose_spec.add
      (exists_hasWeakLineDeriv_toL2 W v).choose_spec).congr_ae ?_ ?_
    · rw [map_add]
      exact ae_restrict_of_ae (Lp.coeFn_add _ _).symm
    · exact ae_restrict_of_ae (Lp.coeFn_add _ _).symm
  map_smul' c U := by
    refine HasWeakLineDeriv.eq_of_top (exists_hasWeakLineDeriv_toL2 (c • U) v).choose_spec ?_
    refine ((exists_hasWeakLineDeriv_toL2 U v).choose_spec.smul c).congr_ae ?_ ?_
    · rw [map_smul]
      exact ae_restrict_of_ae (Lp.coeFn_smul _ _).symm
    · exact ae_restrict_of_ae (Lp.coeFn_smul _ _).symm

/-- `weakDerivL2Linear v U` is the weak derivative `∂_v` of the `L_2` function of `U`. -/
theorem hasWeakLineDeriv_weakDerivL2Linear (v : V) (U : H^{1}(V)) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (toL2 U) (weakDerivL2Linear v U) :=
  (exists_hasWeakLineDeriv_toL2 U v).choose_spec

/-- **The weak derivative `∂_v` as an operator** `H^1(V) → L_2(V)`, of norm at most `2π ‖v‖`
(`Rd.norm_le_of_hasWeakLineDeriv_toL2`): `∂_v U` is the weak derivative on `V` of the `L_2`
function of `U` (`Rd.hasWeakLineDeriv_weakDerivL2`). -/
noncomputable def weakDerivL2 (v : V) : H^{1}(V) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  (weakDerivL2Linear v).mkContinuous (2 * π * ‖v‖) fun U =>
    norm_le_of_hasWeakLineDeriv_toL2 (hasWeakLineDeriv_weakDerivL2Linear v U)

/-- **The operator norm of the weak derivative**: `‖∂_v‖ ≤ 2π ‖v‖` as an operator
`H^1(V) → L_2(V)` (Mathlib's `LinearMap.mkContinuous_norm_le`). -/
theorem norm_weakDerivL2_le (v : V) : ‖weakDerivL2 v‖ ≤ 2 * π * ‖v‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- `weakDerivL2 v U` is the weak derivative `∂_v` on `V` of the `L_2` function of `U`. -/
theorem hasWeakLineDeriv_weakDerivL2 (v : V) (U : H^{1}(V)) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (toL2 U) (weakDerivL2 v U) :=
  hasWeakLineDeriv_weakDerivL2Linear v U

/-- Every weak derivative `g ∈ L_2(V)` of the `L_2` function of `U` along `v` is
`weakDerivL2 v U`. -/
theorem weakDerivL2_eq {v : V} {U : H^{1}(V)} {g : Lp ℂ 2 (volume : Measure V)}
    (h : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (toL2 U) g) : weakDerivL2 v U = g :=
  (hasWeakLineDeriv_weakDerivL2 v U).eq_of_top h

/-- **The `H^1(V)` norm by the weak gradient, in `ℝ`**: let `(e_i)` be an orthonormal basis of
`V`, `f` the `L_2` function of `U ∈ H^1(V)`, and `g_i ∈ L_2(V)` the weak derivatives
`∂_{e_i} f` on `V`. Then `‖U‖² = ‖f‖_2² + (2π)⁻² ∑_i ‖g_i‖_2²`
(`Rd.sq_norm_besselPotential_one_eq` with `J_1 f = U`). -/
theorem sq_norm_eq_of_hasWeakLineDeriv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (U : H^{1}(V)) {g : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) (toL2 U) (g i)) :
    ‖U‖ ^ 2 = ‖toL2 U‖ ^ 2 + (2 * π)⁻¹ ^ 2 * ∑ i, ‖g i‖ ^ 2 := by
  have hfh : besselPotential V ℂ 1 ((toL2 U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (U.toLp : 𝓢'(V, ℂ)) := by
    rw [toTemperedDistribution_toL2]
    exact U.bessel_toDistr_eq_toLp
  have hreal := sq_norm_besselPotential_one_eq b hg hfh
  rw [BesselPotentialSpace.norm_toLp_eq] at hreal
  have hpi : (2 * π) ^ 2 ≠ 0 := by positivity
  rw [inv_pow]
  field_simp
  linarith

/-- **The norm of `H^1(V)` by `W^1_2(V)` norms**: for an orthonormal basis `(e_i)` of `V` and
`U ∈ H^1(V)` whose `L_2` function has the weak derivatives `G_i = ∂_{e_i}` on `V`,
`‖U‖ ≤ ‖U‖_2 + ∑_i ‖G_i‖_2`, since `‖U‖² = ‖U‖_2² + (2π)⁻² ∑_i ‖G_i‖_2²`
(`Rd.sq_norm_eq_of_hasWeakLineDeriv`). -/
theorem norm_le_norm_toL2_add_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (U : H^{1}(V)) {G : ι → Lp ℂ 2 (volume : Measure V)}
    (hG : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) (toL2 U) (G i)) :
    ‖U‖ ≤ ‖toL2 U‖ + ∑ i, ‖G i‖ := by
  have h := sq_norm_eq_of_hasWeakLineDeriv b U hG
  have hπ : (2 * π)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi]))
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) fun i _ => norm_nonneg (G i)
  have h0 : 0 ≤ ∑ i, ‖G i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hsum : 0 ≤ ∑ i, ‖G i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine (pow_le_pow_iff_left₀ (norm_nonneg U) (by positivity) two_ne_zero).1 ?_
  rw [h]
  nlinarith [norm_nonneg (toL2 U)]

/-- **The weak gradient on `Ω` is bounded by the `H^1(Ω)` norm**: let `(e_i)` be an orthonormal
basis of `V`, `u ∈ H^1(Ω)`, and `g_i ∈ L_2(V)` the weak derivatives `∂_{e_i}` on `V` of the `L_2`
function of `u`. Then `‖u|_Ω‖_2² + (2π)⁻² ∑_i ‖g_i|_Ω‖_2² ≤ ‖u‖_{H^1(Ω)}²`, since the left side
without the restrictions is `‖u‖²` (`Rd.sq_norm_eq_of_hasWeakLineDeriv`). For the unweighted
`W^1_2(Ω)` norm the constant is `2π`. -/
theorem sq_norm_restr_add_sum_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (u : RestrictionSpace 1 Ω) {g : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) (toL2 (u : H^{1}(V))) (g i)) :
    ‖restrictL2 Ω u‖ ^ 2 + (2 * π)⁻¹ ^ 2 *
      ∑ i, ‖LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) (g i)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [show ‖u‖ = ‖(u : H^{1}(V))‖ from rfl, sq_norm_eq_of_hasWeakLineDeriv b _ hg]
  gcongr with i
  · exact norm_Lp_toLp_restrict_le _ _
  · exact norm_Lp_toLp_restrict_le _ _

/-- **The weak gradient on `Ω` is bounded by the `H^1(Ω)` norm, with weak derivatives on `Ω`**:
let `(e_i)` be an orthonormal basis of `V`, `u ∈ H^1(Ω)`, and `g_i ∈ L_2(Ω)` weak derivatives
`∂_{e_i}` on `Ω` of the `L_2` function of `u`. Then `‖u|_Ω‖_2² + (2π)⁻² ∑_i ‖g_i‖_2² ≤ ‖u‖²`:
the `g_i` agree almost everywhere on `Ω` with the weak derivatives on `V`
(`Rd.HasWeakLineDeriv.unique`), and `Rd.sq_norm_restr_add_sum_le` applies. -/
theorem sq_norm_restrictL2_add_sum_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (u : RestrictionSpace 1 Ω) {g : ι → Lp ℂ 2 (volume.restrict (Ω : Set V))}
    (hg : ∀ i, HasWeakLineDeriv Ω (fun _ : Fin 1 => b i) (toL2 (u : H^{1}(V))) (g i)) :
    ‖restrictL2 Ω u‖ ^ 2 + (2 * π)⁻¹ ^ 2 * ∑ i, ‖g i‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  choose G hG using fun i => exists_hasWeakLineDeriv_toL2 (u : H^{1}(V)) (b i)
  have hGg : ∀ i, LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) (G i) = g i := fun i =>
    Lp.ext ((LpToLpRestrictCLM_coeFn ℂ _ _).trans (((hG i).mono le_top).unique (hg i)))
  simpa only [hGg] using sq_norm_restr_add_sum_le b u hG

/-- **Weak derivatives of an element vanishing on `Ω`**: for `W ∈ H^1(V)` vanishing on `Ω`, every
weak derivative on `V` of the `L_2` function of `W` vanishes almost everywhere on `Ω`. -/
theorem weakDeriv_ae_zero_of_mem_vanishOn {W : H^{1}(V)} (hW : W ∈ vanishOn 1 Ω) {k : ℕ}
    {v : Fin k → V} {g : V → ℂ} (hg : HasWeakLineDeriv ⊤ v (toL2 W) g) :
    g =ᵐ[volume.restrict (Ω : Set V)] 0 :=
  hg.ae_eq_zero_of_ae_eq_zero le_top ((mem_vanishOn_one_iff W).1 hW)

/-! ### Test functions, `HTilde^s(Ω)` and `H^s_0(Ω)` -/

variable (s) in
/-- **A test function as an element of `H^s(V)`**: a real test function `φ` of `Ω`, as the
complex Schwartz function `Rd.testSchwartz φ`, lies in every `H^s(V)` (Mathlib's
`SchwartzMap.memSobolev`). -/
noncomputable def ofTest (φ : 𝓓(Ω, ℝ)) : H^{s}(V) :=
  ((testSchwartz φ).memSobolev (s := s) (p := 2)).toBesselPotentialSpace

/-- The tempered distribution of `ofTest s φ` is the Schwartz function `φ`. -/
@[simp]
theorem toDistr_ofTest (φ : 𝓓(Ω, ℝ)) :
    (ofTest s φ).toDistr = (testSchwartz φ : 𝓢'(V, ℂ)) :=
  TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr _

/-- **A test function in `H^1(V)` as an `L_2` function**: the `L_2` function of `ofTest 1 φ` is
`φ` almost everywhere (`Rd.toL2_eq_of_toDistr_eq`). -/
theorem toL2_ofTest_ae (φ : 𝓓(Ω, ℝ)) :
    (toL2 (ofTest 1 φ) : V → ℂ) =ᵐ[volume] testSchwartz φ := by
  rw [toL2_eq_of_toDistr_eq _ (f := (testSchwartz φ).toLp 2 (volume : Measure V))
    (by rw [Lp.toTemperedDistribution_toLp_eq]; exact (toDistr_ofTest φ).symm)]
  exact (testSchwartz φ).coeFn_toLp 2 volume

variable (s Ω) in
/-- **The test functions of `Ω` in `H^s(V)`**: the complex linear span of the `ofTest s φ`,
`φ` a real test function of `Ω`. -/
noncomputable def testSpan : Submodule ℂ H^{s}(V) :=
  Submodule.span ℂ (Set.range (ofTest s : 𝓓(Ω, ℝ) → H^{s}(V)))

variable (s Ω) in
/-- **The space `HTilde^s(Ω)`** of Chandler-Wilde, Hewett and Moiola: the closure in `H^s(V)` of the
test functions of `Ω`, a Hilbert space. -/
noncomputable def tildeSpace : Submodule ℂ H^{s}(V) :=
  (testSpan s Ω).topologicalClosure

variable (s Ω) in
/-- `HTilde^s(Ω)` is closed in `H^s(V)`. -/
theorem isClosed_tildeSpace : IsClosed (tildeSpace s Ω : Set H^{s}(V)) :=
  Submodule.isClosed_topologicalClosure _

/-- `HTilde^s(Ω)` is complete, as a closed subspace of `H^s(V)`. -/
instance completeSpace_tildeSpace (s : ℝ) (Ω : Opens V) : CompleteSpace (tildeSpace s Ω) :=
  (isClosed_tildeSpace s Ω).completeSpace_coe

/-! ### Schwartz functions are dense in `H^s(V)` -/

variable (s) in
/-- **Schwartz functions in `H^s(V)`, continuously**: `w ↦ w ∈ H^s(V)` as a continuous linear
map from the Schwartz space: `w` is the element of `H^s(V)` whose Bessel potential `J_s w ∈ L_2(V)`
(Mathlib's `BesselPotentialSpace.toLp`) is the Schwartz function `Rd.besselSchwartz s w`
(`Rd.toDistr_ofSchwartz`). -/
noncomputable def ofSchwartz : 𝓢(V, ℂ) →L[ℂ] H^{s}(V) :=
  (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).symm.toLinearIsometry.toContinuousLinearMap ∘L
    SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L besselSchwartz s

variable (s) in
/-- The tempered distribution of `ofSchwartz s w` is the Schwartz function `w`, since
`J_{-s} J_s = J_0 = id` (Mathlib's `TemperedDistribution.besselPotential_besselPotential_apply`). -/
@[simp]
theorem toDistr_ofSchwartz (w : 𝓢(V, ℂ)) : (ofSchwartz s w).toDistr = (w : 𝓢'(V, ℂ)) := by
  simp only [ofSchwartz, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    BesselPotentialSpace.toLpₗᵢ_symm_apply, SchwartzMap.toLpCLM_apply]
  rw [Lp.toTemperedDistribution_toLp_eq, ← besselPotential_schwartz]
  have h := TemperedDistribution.besselPotential_besselPotential_apply (E := V) (F := ℂ) s (-s)
    (w : 𝓢'(V, ℂ))
  rw [show s + -s = 0 by ring, TemperedDistribution.besselPotential_zero] at h
  exact h

variable (s) in
/-- `ofSchwartz s w` is the element of `H^s(V)` given by Mathlib's `SchwartzMap.memSobolev`. -/
theorem ofSchwartz_eq (w : 𝓢(V, ℂ)) :
    ofSchwartz s w = (w.memSobolev (s := s) (p := 2)).toBesselPotentialSpace :=
  BesselPotentialSpace.ext (by simp)

variable (s) in
/-- A test function of `Ω` in `H^s(V)` is its Schwartz function: `ofTest s φ = ofSchwartz s φ`. -/
theorem ofTest_eq_ofSchwartz (φ : 𝓓(Ω, ℝ)) : ofTest s φ = ofSchwartz s (testSchwartz φ) :=
  BesselPotentialSpace.ext (by simp)

/-- The `L_2` function of a Schwartz function `w` in `H^1(V)` is `w`
(`Rd.toL2_eq_of_toDistr_eq`). -/
theorem toL2_ofSchwartz (w : 𝓢(V, ℂ)) : toL2 (ofSchwartz 1 w) = w.toLp 2 :=
  toL2_eq_of_toDistr_eq _ (by rw [Lp.toTemperedDistribution_toLp_eq, toDistr_ofSchwartz])

/-- **The weak derivative of a Schwartz function in `H^1(V)`** is its classical derivative:
`∂_v (ofSchwartz 1 w) = ∂_v w` in `L_2(V)` (`Rd.hasWeakLineDeriv_schwartz`). -/
theorem weakDerivL2_ofSchwartz (v : V) (w : 𝓢(V, ℂ)) :
    weakDerivL2 v (ofSchwartz 1 w) = (∂_{v} w).toLp 2 := by
  refine weakDerivL2_eq ?_
  have h := hasWeakLineDeriv_schwartz ⊤ w (fun _ : Fin 1 => v)
  rw [LineDeriv.iteratedLineDerivOp_one] at h
  refine h.congr_ae ?_ ?_
  · rw [volume_restrict_top, toL2_ofSchwartz]
    exact (w.coeFn_toLp 2 volume).symm
  · rw [volume_restrict_top]
    exact ((∂_{v} w).coeFn_toLp 2 volume).symm

variable (s) in
/-- **The Schwartz functions are dense in `H^s(V)`**, for every real `s`: `J_s` is an isometry of
`H^s(V)` onto `L_2(V)` (Mathlib's `BesselPotentialSpace.toLpₗᵢ`), it maps the Schwartz functions
onto the Schwartz functions (`Rd.besselSchwartz_besselSchwartz_neg`), and these are dense in
`L_2(V)` (Mathlib's `SchwartzMap.denseRange_toLpCLM`). -/
theorem denseRange_ofSchwartz : DenseRange (ofSchwartz (V := V) s) := by
  have hJ : Function.Surjective (besselSchwartz (V := V) s) :=
    fun w => ⟨_, besselSchwartz_besselSchwartz_neg s w⟩
  have h1 : DenseRange fun w : 𝓢(V, ℂ) =>
      SchwartzMap.toLpCLM ℂ ℂ 2 volume (besselSchwartz s w) :=
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := (volume : Measure V)) two_ne_top).comp
      hJ.denseRange (SchwartzMap.toLpCLM ℂ ℂ 2 volume).continuous
  exact (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).symm.surjective.denseRange.comp h1
    (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).symm.continuous

variable (s) in
/-- **Compactly supported Schwartz functions are dense in `H^s(V)`**, for every real `s`: the
cut-offs `χ_n w` of a Schwartz function converge to `w` in the Schwartz space
(`Rd.tendsto_cutoffMul`), hence in `H^s(V)`, and the Schwartz functions are dense
(`Rd.denseRange_ofSchwartz`). -/
theorem dense_ofSchwartz_hasCompactSupport :
    Dense (ofSchwartz (V := V) s '' {w | HasCompactSupport w}) := by
  refine dense_closure.1 ((denseRange_ofSchwartz s).mono ?_)
  rintro _ ⟨w, rfl⟩
  exact mem_closure_of_tendsto (((ofSchwartz s).continuous.tendsto w).comp (tendsto_cutoffMul w))
    (Eventually.of_forall fun n => ⟨_, hasCompactSupport_cutoffMul n w, rfl⟩)

variable (s) in
/-- **Compactly supported Schwartz functions in `Ω` lie in the span of the test functions**: a
Schwartz function `w` with compact support in the open set `Ω` is `Re w + i Im w` with real test
functions of `Ω` (`Rd.exists_testSchwartz_eq_of_tsupport_subset`), so `w ∈ testSpan s Ω` for every
real `s`. -/
theorem ofSchwartz_mem_testSpan {w : 𝓢(V, ℂ)} (hw : HasCompactSupport w)
    (hwΩ : tsupport w ⊆ Ω) : ofSchwartz s w ∈ testSpan s Ω := by
  obtain ⟨a, b, rfl⟩ := exists_testSchwartz_eq_of_tsupport_subset w hw hwΩ
  rw [map_add, map_smul, ← ofTest_eq_ofSchwartz, ← ofTest_eq_ofSchwartz]
  exact (testSpan s Ω).add_mem (Submodule.subset_span ⟨a, rfl⟩)
    ((testSpan s Ω).smul_mem _ (Submodule.subset_span ⟨b, rfl⟩))

variable (s) in
/-- **`HTilde^s(V) = H^s(V)`**: on the whole space, the test functions are dense in `H^s(V)` for
every
real `s`, since the compactly supported Schwartz functions are dense
(`Rd.dense_ofSchwartz_hasCompactSupport`) and lie in the span of the test functions
(`Rd.ofSchwartz_mem_testSpan`). -/
theorem tildeSpace_top : tildeSpace s (⊤ : Opens V) = ⊤ := by
  rw [tildeSpace, ← Submodule.dense_iff_topologicalClosure_eq_top]
  refine (dense_ofSchwartz_hasCompactSupport s).mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ofSchwartz_mem_testSpan s hw (by simp)

/-! ### Differences in `H^1(V)` -/

/-- **Differences in `H^1(V)`**: `‖Δ_v ι U‖_2 ≤ 2π ‖v‖ ‖U‖` for every `U ∈ H^1(V)`, with the
difference operator `Δ_v` on `L_2(V)` (`Rd.fwdDiffL2`). For a Schwartz function `G` this is
`‖Δ_v G‖_2 ≤ ‖∂_v G‖_2 ≤ 2π ‖v‖ ‖G‖_{H^1}` (`Rd.enorm_fwdDiffL2_toLp_le`,
`Rd.norm_weakDerivL2_le`); both sides are continuous in `U`, and the Schwartz functions are dense
in `H^1(V)` (`Rd.denseRange_ofSchwartz`). -/
theorem norm_fwdDiffL2_toL2_le (v : V) (U : H^{1}(V)) :
    ‖fwdDiffL2 V v (toL2 U)‖ ≤ 2 * π * ‖v‖ * ‖U‖ := by
  refine DenseRange.induction_on (denseRange_ofSchwartz (V := V) 1) U
    (isClosed_le ((fwdDiffL2 V v).continuous.comp toL2.continuous).norm
      (continuous_const.mul continuous_norm)) fun w => ?_
  have h1 : ‖fwdDiffL2 V v (toL2 (ofSchwartz 1 w))‖ ≤ ‖(∂_{v} w : 𝓢(V, ℂ)).toLp 2‖ := by
    rw [toL2_ofSchwartz, ← toReal_eNorm, ← toReal_eNorm]
    exact ENNReal.toReal_mono eNorm_ne_top (enorm_fwdDiffL2_toLp_le v w)
  have h2 : ‖(∂_{v} w : 𝓢(V, ℂ)).toLp 2‖ ≤ 2 * π * ‖v‖ * ‖ofSchwartz 1 w‖ := by
    rw [← weakDerivL2_ofSchwartz]
    exact ((weakDerivL2 v).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_weakDerivL2_le v) (norm_nonneg _))
  exact h1.trans h2

/-- **The first-order modulus in `H^1(V)`**: `ω_1(ι U, 2^(-k))_2 ≤ 2π 2^(-k) ‖U‖` for every
`U ∈ H^1(V)` (`Rd.norm_fwdDiffL2_toL2_le`, and `ENNReal.ofReal_one_div_two_pow_pow` for the
scale `2^(-k)`). -/
theorem lpModulus_one_toL2_le (U : H^{1}(V)) (k : ℕ) :
    lpModulus 2 1 (toL2 U) k ≤
      ENNReal.ofReal (2 * π) * ENNReal.dyadicWeight (-1) k * ‖U‖ₑ := by
  have hk : ENNReal.ofReal (1 / 2 ^ k) = ENNReal.dyadicWeight (-1) k := by
    simpa using ENNReal.ofReal_one_div_two_pow_pow k 1
  refine iSup₂_le fun h hh => ?_
  rw [Function.iterate_one, ← enorm_fwdDiffL2, ← ofReal_norm, ← ofReal_norm,
    ← hk, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((norm_fwdDiffL2_toL2_le h U).trans ?_)
  gcongr

/-- **The modulus of an `H^1(V)` function**: for every order `r ≥ 1`,
`ω_r(ι U, 2^(-k))_2 ≤ 2^(r-1) 2π 2^(-k) ‖U‖` for `U ∈ H^1(V)`
(`Rd.lpModulus_one_toL2_le` and `ω_{1+l} ≤ 2^l ω_1`, `Rd.lpModulus_add_order_le`). -/
theorem lpModulus_toL2_le {r : ℕ} (hr : 1 ≤ r) (U : H^{1}(V)) (k : ℕ) :
    lpModulus 2 r (toL2 U) k ≤
      2 ^ (r - 1) * ENNReal.ofReal (2 * π) * ENNReal.dyadicWeight (-1) k * ‖U‖ₑ := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_sub_cancel_left, mul_assoc, mul_assoc, ← mul_assoc (ENNReal.ofReal (2 * π))]
  exact (lpModulus_add_order_le 1 l (toL2 U) k).trans
    (mul_le_mul' le_rfl (lpModulus_one_toL2_le U k))

variable (s Ω) in
/-- **The space `H^s_0(Ω)`**: the closure in `H^s(Ω)` of the restrictions of the test functions
of `Ω`, a Hilbert space. -/
noncomputable def zeroBoundarySpace : Submodule ℂ (RestrictionSpace s Ω) :=
  ((testSpan s Ω).map (restrictProj s Ω : H^{s}(V) →ₗ[ℂ] RestrictionSpace s Ω)).topologicalClosure

variable (s Ω) in
/-- `H^s_0(Ω)` is closed in `H^s(Ω)`. -/
theorem isClosed_zeroBoundarySpace :
    IsClosed (zeroBoundarySpace s Ω : Set (RestrictionSpace s Ω)) :=
  Submodule.isClosed_topologicalClosure _

/-- `H^s_0(Ω)` is complete, as a closed subspace of `H^s(Ω)`. -/
instance completeSpace_zeroBoundarySpace (s : ℝ) (Ω : Opens V) :
    CompleteSpace (zeroBoundarySpace s Ω) :=
  (isClosed_zeroBoundarySpace s Ω).completeSpace_coe

variable (s Ω) in
/-- **From `HTilde^s(Ω)` to `H^s(Ω)`**: the restriction of the elements of `HTilde^s(Ω)` to `Ω`, an
operator of norm at most `1` with values in `H^s_0(Ω)` (`Rd.range_tildeToRestrictionL_le`). -/
noncomputable def tildeToRestrictionL : tildeSpace s Ω →L[ℂ] RestrictionSpace s Ω :=
  restrictProj s Ω ∘L (tildeSpace s Ω).subtypeL

/-- The restriction maps `HTilde^s(Ω)` into `H^s_0(Ω)`, by continuity of the restriction (Mathlib's
`map_mem_closure`). -/
theorem range_tildeToRestrictionL_le :
    (tildeToRestrictionL s Ω).range ≤ zeroBoundarySpace s Ω := by
  rintro _ ⟨U, rfl⟩
  change restrictProj s Ω (U : H^{s}(V)) ∈ _
  have hU : (U : H^{s}(V)) ∈ closure (testSpan s Ω : Set H^{s}(V)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact U.2
  rw [← SetLike.mem_coe, zeroBoundarySpace, Submodule.topologicalClosure_coe]
  exact map_mem_closure (restrictProj s Ω).continuous hU fun W hW => Submodule.mem_map_of_mem hW

/-- `H^s_0(Ω)` is the closure of the image of `HTilde^s(Ω)` under the restriction. -/
theorem closure_range_tildeToRestrictionL :
    (tildeToRestrictionL s Ω).range.topologicalClosure = zeroBoundarySpace s Ω := by
  refine le_antisymm (Submodule.topologicalClosure_minimal _ range_tildeToRestrictionL_le
    (isClosed_zeroBoundarySpace s Ω)) (Submodule.topologicalClosure_mono ?_)
  rintro _ ⟨U, hU, rfl⟩
  exact ⟨⟨U, Submodule.le_topologicalClosure _ hU⟩, rfl⟩

/-- **The elements of the span of the test functions are Schwartz functions supported in `Ω`**:
every `U ∈ testSpan s Ω` is the tempered distribution of a Schwartz function `w` whose closed
support lies in `Ω`. -/
theorem exists_schwartz_of_mem_testSpan {U : H^{s}(V)} (hU : U ∈ testSpan s Ω) :
    ∃ w : 𝓢(V, ℂ), tsupport w ⊆ Ω ∧ U.toDistr = (w : 𝓢'(V, ℂ)) := by
  induction hU using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ⟨testSchwartz φ, (tsupport_comp_subset Complex.ofReal_zero φ).trans φ.tsupport_subset,
      toDistr_ofTest φ⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, hxw⟩ := hx
    obtain ⟨w', hw', hyw⟩ := hy
    exact ⟨w + w', (tsupport_add _ _).trans (Set.union_subset hw hw'), by
      rw [BesselPotentialSpace.toDistr_add, hxw, hyw, map_add]⟩
  | smul c x _ hx =>
    obtain ⟨w, hw, hxw⟩ := hx
    have hs : tsupport (c • w : 𝓢(V, ℂ)) ⊆ tsupport w := by
      rw [FunLike.coe_smul]
      exact tsupport_smul_subset_right (fun _ : V => c) w
    exact ⟨c • w, hs.trans hw, by rw [BesselPotentialSpace.toDistr_smul, hxw, map_smul]⟩

/-- **Elements of the span of the test functions vanish near the complement of `Ω`**: for
`U ∈ testSpan 1 Ω`, the `L_2` function of `U` vanishes almost everywhere on an open set
containing `V \ Ω`, the complement of the closed support of its Schwartz function. -/
theorem exists_opens_toL2_ae_eq_zero {U : H^{1}(V)} (hU : U ∈ testSpan 1 Ω) :
    ∃ O : Opens V, (Ω : Set V)ᶜ ⊆ O ∧ (toL2 U : V → ℂ) =ᵐ[volume.restrict (O : Set V)] 0 := by
  obtain ⟨w, hw, hUw⟩ := exists_schwartz_of_mem_testSpan hU
  have h : toL2 U = w.toLp 2 (volume : Measure V) :=
    toL2_eq_of_toDistr_eq U (by rw [Lp.toTemperedDistribution_toLp_eq]; exact hUw.symm)
  refine ⟨⟨(tsupport w)ᶜ, (isClosed_tsupport w).isOpen_compl⟩, Set.compl_subset_compl.2 hw, ?_⟩
  rw [h]
  filter_upwards [ae_restrict_of_ae (w.coeFn_toLp 2 volume),
    ae_restrict_mem (isClosed_tsupport w).isOpen_compl.measurableSet] with x hx hxO
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport hxO

/-- **The elements of `HTilde^1(Ω)` vanish outside `Ω`**: for every open `Ω` and `U ∈
HTilde^1(Ω)`, the
`L_2` function of `U` vanishes almost everywhere outside `Ω`. The `U` with this property form the
kernel of `U ↦ (ι U)|_{V \ Ω}`, a closed subspace containing the test functions of `Ω`
(`Rd.exists_opens_toL2_ae_eq_zero`). -/
theorem toL2_ae_eq_zero_of_mem_tildeSpace {Ω : Opens V} {U : H^{1}(V)}
    (hU : U ∈ tildeSpace 1 Ω) : ∀ᵐ x ∂volume, x ∉ (Ω : Set V) → toL2 U x = 0 := by
  have hker : tildeSpace 1 Ω ≤
      (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V)ᶜ ∘L toL2).ker := by
    refine Submodule.topologicalClosure_minimal _ (fun W hW => ?_)
      (ContinuousLinearMap.isClosed_ker _)
    obtain ⟨O, hO, hWO⟩ := exists_opens_toL2_ae_eq_zero hW
    rw [LinearMap.mem_ker]
    change LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V)ᶜ (toL2 W) = 0
    rw [Lp.eq_zero_iff_ae_eq_zero]
    exact (LpToLpRestrictCLM_coeFn ℂ _ _).trans (ae_restrict_of_ae_restrict_of_subset hO hWO)
  have h := hker hU
  rw [LinearMap.mem_ker] at h
  change LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V)ᶜ (toL2 U) = 0 at h
  rw [Lp.eq_zero_iff_ae_eq_zero] at h
  have h' := (LpToLpRestrictCLM_coeFn ℂ _ _).symm.trans h
  rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet.compl] at h'
  exact h'

/-- **Functions with disjoint supports**: in every `L_p(μ)` with values in a normed group, if
`a` vanishes almost everywhere outside a measurable set `S` and `b` vanishes almost everywhere on
`S`, then `‖a‖_p ≤ ‖a + b‖_p`, since `|a + b| ≥ |a|` almost everywhere (Mathlib's
`Lp.norm_le_norm_of_ae_le`). -/
theorem norm_le_norm_add_of_ae_eq_zero {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {S : Set α} (hS : MeasurableSet S) {a b : Lp E p μ}
    (ha : (a : α → E) =ᵐ[μ.restrict Sᶜ] 0) (hb : (b : α → E) =ᵐ[μ.restrict S] 0) :
    ‖a‖ ≤ ‖a + b‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [(ae_restrict_iff' hS.compl).1 ha, (ae_restrict_iff' hS).1 hb,
    Lp.coeFn_add a b] with x hax hbx hx
  rw [hx, Pi.add_apply]
  by_cases hxS : x ∈ S
  · simp [hbx hxS]
  · simp [hax hxS]

/-- **The `H^1(V)` norm of a test function of `Ω` is at most that of its sum with a function
vanishing on `Ω`**: for `U ∈ testSpan 1 Ω` and `W` vanishing on `Ω`, `‖U‖ ≤ ‖U + W‖`. With an
orthonormal basis `(e_i)`, `‖U‖² = ‖U‖_2² + (2π)⁻² ∑_i ‖∂_{e_i} U‖_2²`
(`Rd.sq_norm_eq_of_hasWeakLineDeriv`), and the same for `U + W`. `U` and its weak gradient vanish
near `V \ Ω` (`Rd.exists_opens_toL2_ae_eq_zero`), `W` and its weak gradient vanish on `Ω`
(`Rd.mem_vanishOn_one_iff`, `Rd.weakDeriv_ae_zero_of_mem_vanishOn`), so each `L_2` norm grows
(`Rd.norm_le_norm_add_of_ae_eq_zero`). -/
theorem norm_le_norm_add_of_mem_testSpan {U W : H^{1}(V)} (hU : U ∈ testSpan 1 Ω)
    (hW : W ∈ vanishOn 1 Ω) : ‖U‖ ≤ ‖U + W‖ := by
  obtain ⟨O, hO, hUO⟩ := exists_opens_toL2_ae_eq_zero hU
  let b := stdOrthonormalBasis ℝ V
  choose gU hgU using fun i => exists_hasWeakLineDeriv_toL2 U (b i)
  choose gW hgW using fun i => exists_hasWeakLineDeriv_toL2 W (b i)
  have hUW : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) (toL2 (U + W))
      ((gU i + gW i : Lp ℂ 2 (volume : Measure V)) : V → ℂ) :=
    fun i => ((hgU i).add (hgW i)).congr_ae
      (by rw [volume_restrict_top, map_add]; exact (Lp.coeFn_add _ _).symm)
      (by rw [volume_restrict_top]; exact (Lp.coeFn_add _ _).symm)
  have h1 : ‖toL2 U‖ ≤ ‖toL2 (U + W)‖ := by
    rw [map_add]
    exact norm_le_norm_add_of_ae_eq_zero Ω.isOpen.measurableSet
      (ae_restrict_of_ae_restrict_of_subset hO hUO) ((mem_vanishOn_one_iff W).1 hW)
  have h2 : ∀ i, ‖gU i‖ ≤ ‖gU i + gW i‖ := fun i =>
    norm_le_norm_add_of_ae_eq_zero Ω.isOpen.measurableSet
      (ae_restrict_of_ae_restrict_of_subset hO ((hgU i).ae_eq_zero_of_ae_eq_zero le_top hUO))
      (weakDeriv_ae_zero_of_mem_vanishOn hW (hgW i))
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), sq_norm_eq_of_hasWeakLineDeriv b U hgU,
    sq_norm_eq_of_hasWeakLineDeriv b (U + W) hUW]
  gcongr with i
  exact h2 i

/-- **Restriction preserves the norm of test functions**: for `U ∈ testSpan 1 Ω`,
`‖U|_Ω‖_{H^1(Ω)} = ‖U‖_{H^1(V)}`. The norm of `U|_Ω` is `‖U + W‖` for some `W` vanishing on `Ω`
(`Rd.exists_norm_restrictProj_eq`), which is at least `‖U‖`
(`Rd.norm_le_norm_add_of_mem_testSpan`). -/
theorem norm_restrictProj_of_mem_testSpan {U : H^{1}(V)} (hU : U ∈ testSpan 1 Ω) :
    ‖restrictProj 1 Ω U‖ = ‖U‖ := by
  refine le_antisymm (norm_restrictProj_apply_le U) ?_
  obtain ⟨W, hW, h⟩ := exists_norm_restrictProj_eq (Ω := Ω) U
  rw [h]
  exact norm_le_norm_add_of_mem_testSpan hU hW

/-- **Restriction is isometric on `HTilde^1(Ω)`**: for `U ∈ HTilde^1(Ω)`, `‖U|_Ω‖ = ‖U‖`, by
continuity
from the test functions (`Rd.norm_restrictProj_of_mem_testSpan`). -/
theorem norm_restrictProj_of_mem_tildeSpace {U : H^{1}(V)} (hU : U ∈ tildeSpace 1 Ω) :
    ‖restrictProj 1 Ω U‖ = ‖U‖ := by
  have hc : IsClosed {U : H^{1}(V) | ‖restrictProj 1 Ω U‖ = ‖U‖} :=
    isClosed_eq (continuous_norm.comp (restrictProj 1 Ω).continuous) continuous_norm
  refine closure_minimal (fun U hU => norm_restrictProj_of_mem_testSpan hU) hc ?_
  rw [← Submodule.topologicalClosure_coe]
  exact hU

variable (Ω) in
/-- **Restriction as an isometry of `HTilde^1(Ω)` into `H^1(Ω)`**: for every open set `Ω`, the
restriction `HTilde^1(Ω) → H^1(Ω)` as a linear isometry (`Rd.norm_restrictProj_of_mem_tildeSpace`),
the case `s = 1` of `HTilde^s(Ω) = H^s_0(Ω)`. -/
noncomputable def tildeToRestriction : tildeSpace 1 Ω →ₗᵢ[ℂ] RestrictionSpace 1 Ω where
  toLinearMap := (tildeToRestrictionL 1 Ω).toLinearMap
  norm_map' U := norm_restrictProj_of_mem_tildeSpace U.2

/-- `tildeToRestriction Ω U` is the restriction of `U` to `Ω`. -/
theorem tildeToRestriction_apply (U : tildeSpace 1 Ω) :
    tildeToRestriction Ω U = restrictProj 1 Ω U :=
  rfl

/-- **The image of `HTilde^1(Ω)` is `H^1_0(Ω)`**: the range of the isometry `tildeToRestriction` is
closed, since `HTilde^1(Ω)` is complete (Mathlib's `Isometry.isClosedEmbedding`), and its closure is
`H^1_0(Ω)` (`Rd.closure_range_tildeToRestrictionL`). -/
theorem range_tildeToRestriction :
    (tildeToRestriction Ω).toLinearMap.range = zeroBoundarySpace 1 Ω := by
  have hc : IsClosed ((tildeToRestriction Ω).toLinearMap.range : Set (RestrictionSpace 1 Ω)) :=
    (tildeToRestriction Ω).isometry.isClosedEmbedding.isClosed_range
  rw [← closure_range_tildeToRestrictionL]
  exact (IsClosed.submodule_topologicalClosure_eq hc).symm

variable (Ω) in
/-- **`HTilde^1(Ω) ≅ H^1_0(Ω)` isometrically, for every open set `Ω`**: the identity
`HTilde^s(Ω) = H^s_0(Ω)` at `s = 1`, with equal norms. McLean (Theorem 3.33) proves
`HTilde^s(Ω) = H^s_0(Ω)` on Lipschitz domains for `s ≥ 0` with `s - 1/2 ∉ ℤ`, in particular for
`s = 1`, up to equivalence of norms; for `s = 1` restriction is an isometry of `HTilde^1(Ω)` onto
`H^1_0(Ω)` for every open `Ω` (`Rd.tildeToRestriction`, `Rd.range_tildeToRestriction`, Mathlib's
`LinearIsometry.equivRange`). -/
noncomputable def tildeEquivZeroBoundary : tildeSpace 1 Ω ≃ₗᵢ[ℂ] zeroBoundarySpace 1 Ω :=
  (tildeToRestriction Ω).equivRange.trans (LinearIsometryEquiv.ofEq _ _ range_tildeToRestriction)

/-- `tildeEquivZeroBoundary Ω U` is the restriction of `U` to `Ω`. -/
theorem coe_tildeEquivZeroBoundary_apply (U : tildeSpace 1 Ω) :
    (tildeEquivZeroBoundary Ω U : RestrictionSpace 1 Ω) = restrictProj 1 Ω U :=
  rfl

/-- **`HTilde^1(Ω)` lies in `H^1(Ω)`**: every element of `HTilde^1(Ω)` is orthogonal to the elements
vanishing on `Ω`. Restriction is the orthogonal projection onto `H^1(Ω)` and keeps the norm of
`U ∈ HTilde^1(Ω)` (`Rd.norm_restrictProj_of_mem_tildeSpace`), and a vector whose orthogonal
projection has the same norm lies in the subspace (Mathlib's
`Submodule.mem_iff_norm_starProjection`). -/
theorem tildeSpace_one_le_orthogonal : tildeSpace 1 Ω ≤ (vanishOn 1 Ω)ᗮ := fun U hU =>
  ((vanishOn 1 Ω)ᗮ.mem_iff_norm_starProjection U).2 (norm_restrictProj_of_mem_tildeSpace hU)

/-- **The element of `HTilde^1(Ω)` with restriction `u ∈ H^1_0(Ω)` is `u` itself**: inside `H^1(V)`,
`HTilde^1(Ω)` and `H^1_0(Ω)` are the same subspace, and the inverse of `Rd.tildeEquivZeroBoundary`
is the identity (`Rd.tildeSpace_one_le_orthogonal`, `Rd.restrictProj_coe`). -/
theorem coe_tildeEquivZeroBoundary_symm_apply (u : zeroBoundarySpace 1 Ω) :
    (((tildeEquivZeroBoundary Ω).symm u : tildeSpace 1 Ω) : H^{1}(V)) =
      ((u : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  have h := congrArg (fun v : zeroBoundarySpace 1 Ω => ((v : RestrictionSpace 1 Ω) : H^{1}(V)))
    ((tildeEquivZeroBoundary Ω).apply_symm_apply u)
  have h' := restrictProj_coe (⟨_, tildeSpace_one_le_orthogonal
    ((tildeEquivZeroBoundary Ω).symm u).2⟩ : RestrictionSpace 1 Ω)
  simp only [coe_tildeEquivZeroBoundary_apply] at h
  rw [← h]
  exact (congrArg Subtype.val h').symm

end Rd
