/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Sobolev.LipschitzDomainGreen
public import LeanPool.FunctionSpaces.Domains.Sobolev.SobolevDuality
public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.ConvolutionAdjoint
public import LeanPool.FunctionSpaces.Rd.Atoms.SmoothAtoms

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The kernel of the trace

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner product
space `V`, such as `ℝ^d`, with Lebesgue measure, `H^1(Ω)` the Hilbert space of restrictions of
`H^1(V)`, `HTilde^1(Ω)` the closure of the test functions of `Ω` in `H^1(V)` and `H^1_0(Ω)` the
closure of their restrictions in `H^1(Ω)`.

* **Mollification in `H^1(V)`**: convergence of the `L_2` functions and of their weak
  derivatives gives convergence in `H^1(V)` (`Rd.tendsto_of_tendsto_toL2`), so the mollified
  `η_c ⋆ U` converge to `U` in `H^1(V)` as `c → ∞` (`Rd.tendsto_of_toL2_eq_convLp`). Mollifying a
  function that vanishes outside a compact set `S` gives Schwartz functions supported in
  `supp η_c + S` (`Rd.exists_schwartz_eq_conv`), hence elements of `HTilde^1(Ω)` when these sets lie
  in `Ω` (`Rd.mem_tildeSpace_of_dilate`, `Rd.mem_tildeSpace_of_isCompact`); the mollifiers are
  normalised bump functions (`Rd.bumpMollifier`).
* **`HTilde^1(Ω)` by supports**: for `U ∈ H^1(V)` vanishing outside an open set `Ω`, the zero
  extension of `U|_Ω` is `U` (`Rd.indicatorLp_toL2_restrictProj`), and on a bounded Lipschitz
  domain every `U ∈ H^1(V)` vanishing outside `Ω` lies in `HTilde^1(Ω)`
  (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`). The
  pieces of `U` near the boundary are pushed into `Ω` by a mollifier supported in the cone of the
  chart (`Rd.LipschitzGraph.coneMollifier`,
  `Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart`).
* **`ker γ = H^1_0(Ω)`** (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`, McLean,
  Theorem 3.40): `u ∈ H^1(Ω)` has zero trace iff its zero extension lies in `H^1(V)`
  (`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_iff_mem_traceKer`), iff the zero extension
  lies in `HTilde^1(Ω)`, iff `u ∈ H^1_0(Ω)`.
* **The quotient and the duals**: `H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)` isometrically
  (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`); its content is
  `ker γ = H^1_0(Ω)`, and the isometry holds by the definition of `H^{1/2}(Γ)` as the orthogonal
  complement of `ker γ`. Further `HTilde^1(Ω) ≅ ker γ`
  (`Rd.BoundedLipschitzDomain.tildeEquivTraceKer`) and `(ker γ)^* ≅ H^{-1}(Ω)`
  (`Rd.BoundedLipschitzDomain.dualTraceKerEquiv`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace LineDeriv Pointwise

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Mollification in `H^1(V)` -/

/-- **Convergence in `H^1(V)`** from the convergence of the `L_2` functions and of all their weak
derivatives in `L_2(V)`: `‖W - U‖ ≤ ‖ι W - ι U‖_2 + ∑_i ‖∂_{e_i} W - ∂_{e_i} U‖_2` for an
orthonormal basis `(e_i)` (`Rd.norm_le_norm_toL2_add_sum`). -/
theorem tendsto_of_tendsto_toL2 {ι : Type*} {l : Filter ι} {W : ι → H^{1}(V)} {U : H^{1}(V)}
    (h0 : Tendsto (fun i => toL2 (W i)) l (𝓝 (toL2 U)))
    (h1 : ∀ v : V, Tendsto (fun i => weakDerivL2 v (W i)) l (𝓝 (weakDerivL2 v U))) :
    Tendsto W l (𝓝 U) := by
  let b := stdOrthonormalBasis ℝ V
  rw [tendsto_iff_norm_sub_tendsto_zero] at h0 ⊢
  have h2 := h0.add (tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_iff_norm_sub_tendsto_zero.1 (h1 (b i)))
  simp only [Finset.sum_const_zero, add_zero] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) h2
  refine (norm_le_norm_toL2_add_sum b (W i - U)
    (G := fun k => weakDerivL2 (b k) (W i) - weakDerivL2 (b k) U) fun k => ?_).trans_eq (by
      rw [map_sub])
  rw [← map_sub]
  exact hasWeakLineDeriv_weakDerivL2 _ _

/-- **Mollification converges in `H^1(V)`**: let `η` be a Schwartz function with `∫ η = 1`,
`c_i ≠ 0` dilation factors with `c_i → ∞`, `η_c(x) = c^n η(c x)`, and `U ∈ H^1(V)`. If
`W_i ∈ H^1(V)` has the `L_2` function `η_{c_i} ⋆ ι U`, then `W_i → U` in `H^1(V)`. The weak
derivatives of `η_{c_i} ⋆ ι U` are `η_{c_i} ⋆ ∂_v U` (`Rd.hasWeakLineDeriv_convLp`), and
approximate identities converge in `L_2(V)` (`Rd.tendsto_convLp_dilate`). -/
theorem tendsto_of_toL2_eq_convLp {η : 𝓢(V, ℂ)} (h1 : ∫ x, η x = 1) {ι : Type*} {l : Filter ι}
    {c : ι → ℝ} (hc : ∀ i, c i ≠ 0) (hcl : Tendsto c l atTop) (U : H^{1}(V))
    {W : ι → H^{1}(V)}
    (hW : ∀ i, toL2 (W i) = convLp two_ne_top (integrable_dilate η.integrable (hc i)) (toL2 U)) :
    Tendsto W l (𝓝 U) := by
  refine tendsto_of_tendsto_toL2 ?_ fun v => ?_
  · simp_rw [hW]
    exact tendsto_convLp_dilate two_ne_top η.integrable h1 hc hcl _
  · have hd : ∀ i, weakDerivL2 v (W i) =
        convLp two_ne_top (integrable_dilate η.integrable (hc i)) (weakDerivL2 v U) := fun i =>
      weakDerivL2_eq (by
        rw [hW i]
        exact hasWeakLineDeriv_convLp two_ne_top two_ne_top (schwartzDilate (c i) (hc i) η) _
          (coe_schwartzDilate _ _ _) (hasWeakLineDeriv_weakDerivL2 v U))
    simp_rw [hd]
    exact tendsto_convLp_dilate two_ne_top η.integrable h1 hc hcl _

/-! ### Smooth functions supported in `Ω` -/

/-- **Smoothing a function that vanishes outside a compact set**: for a smooth kernel `K` with
compact support and a locally integrable `f` vanishing outside a compact set `S`, `K ⋆ f` is a
Schwartz function with compact support in `supp K + S` (Mathlib's
`HasCompactSupport.contDiff_convolution_left`, `HasCompactSupport.convolution`,
`support_convolution_subset`). -/
theorem exists_schwartz_eq_conv {K f : V → ℂ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K)
    (hKc : HasCompactSupport K)
    (hf : LocallyIntegrable f volume) {S : Set V} (hS : IsCompact S) (hfS : ∀ x ∉ S, f x = 0) :
    ∃ w : 𝓢(V, ℂ), (w : V → ℂ) = conv K f volume ∧ HasCompactSupport w ∧
      tsupport w ⊆ tsupport K + S := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro hS hfS
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (conv K f volume) := contDiff_conv hK hKc hf
  have hcs : HasCompactSupport (conv K f volume) :=
    hKc.convolution (ContinuousLinearMap.mul ℂ ℂ) hfc
  exact ⟨hcs.toSchwartzMap hsm, rfl, hcs, closure_minimal ((support_convolution_subset _).trans
    (add_subset_add (subset_tsupport K) (Function.support_subset_iff'.2 hfS)))
    (hKc.isCompact.add hS).isClosed⟩

/-- **Mollified functions in `HTilde^1(Ω)`**: let `Ω` be open, `U ∈ H^1(V)` vanishing almost
everywhere
outside a compact set `S`, and `η` a smooth function with compact support and `∫ η = 1`. If
`supp η_{2^n} + S ⊆ Ω` for all large `n`, then `U ∈ HTilde^1(Ω)`: the functions `η_{2^n} ⋆ ι U` are
Schwartz functions with compact support in `Ω` (`Rd.exists_schwartz_eq_conv`), hence in the span
of the test functions (`Rd.ofSchwartz_mem_testSpan`), and they converge to `U` in `H^1(V)`
(`Rd.tendsto_of_toL2_eq_convLp`). -/
theorem mem_tildeSpace_of_dilate {Ω : Opens V} {U : H^{1}(V)} {S : Set V} (hS : IsCompact S)
    (hUS : ∀ᵐ x ∂volume, x ∉ S → toL2 U x = 0) {η : V → ℂ}
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hηc : HasCompactSupport η) (hη1 : ∫ x, η x = 1)
    (hΩ : ∀ᶠ n : ℕ in atTop, tsupport (dilate ((2 : ℝ) ^ n) η) + S ⊆ Ω) :
    U ∈ tildeSpace 1 Ω := by
  have hGae : S.indicator (toL2 U : V → ℂ) =ᵐ[volume] toL2 U := by
    filter_upwards [hUS] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS, hx hxS]
  have hloc : LocallyIntegrable (S.indicator (toL2 U : V → ℂ)) volume :=
    ((Lp.memLp (toL2 U)).locallyIntegrable (by norm_num)).indicator hS.isClosed.measurableSet
  have hc : ∀ n : ℕ, (2 : ℝ) ^ n ≠ 0 := fun n => by positivity
  choose w hw hwc hws using fun n : ℕ => exists_schwartz_eq_conv (contDiff_dilate hη _)
    (hasCompactSupport_dilate hηc (hc n)) hloc hS fun x hx => indicator_of_notMem hx _
  have hW : ∀ n, toL2 (ofSchwartz 1 (w n)) = convLp two_ne_top
      (integrable_dilate (hηc.toSchwartzMap hη).integrable (hc n)) (toL2 U) := fun n => by
    rw [toL2_ofSchwartz]
    refine Lp.ext ?_
    filter_upwards [(w n).coeFn_toLp 2 volume, convLp_apply_ae two_ne_top
      (integrable_dilate (hηc.toSchwartzMap hη).integrable (hc n)) (toL2 U)] with x h1 h2
    rw [h1, h2, hw n, conv_congr_ae hGae]
    rfl
  have ht := tendsto_of_toL2_eq_convLp (η := hηc.toSchwartzMap hη) hη1 hc
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) U hW
  rw [tildeSpace, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto ht (hΩ.mono fun n hn =>
    ofSchwartz_mem_testSpan 1 (hwc n) ((hws n).trans hn))

/-- **Mollified functions with compact support in `Ω`**: for an open set `Ω`, every `U ∈ H^1(V)`
vanishing almost everywhere outside a compact subset `S` of `Ω` lies in `HTilde^1(Ω)`. Some
thickening `S_δ` lies in `Ω` (Mathlib's `IsCompact.exists_thickening_subset_open`), and for the
mollifier of the standard bump `Rd.stdBumpBase`, supported in `closedBall(0, 1)`, eventually
`supp η_{2^n} + S ⊆ S_δ` (`Rd.eventually_tsupport_dilate_add_subset_thickening`,
`Rd.mem_tildeSpace_of_dilate`). -/
theorem mem_tildeSpace_of_isCompact {Ω : Opens V} {U : H^{1}(V)} {S : Set V} (hS : IsCompact S)
    (hSΩ : S ⊆ Ω) (hUS : ∀ᵐ x ∂volume, x ∉ S → toL2 U x = 0) : U ∈ tildeSpace 1 Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hS.exists_thickening_subset_open Ω.isOpen hSΩ
  refine mem_tildeSpace_of_dilate hS hUS (contDiff_bumpMollifier (stdBumpBase (V := V)))
    (hasCompactSupport_bumpMollifier _) (integral_bumpMollifier _) ?_
  exact (eventually_tsupport_dilate_add_subset_thickening (tsupport_bumpMollifier_subset _) hδ
    S).mono fun n hn => hn.trans hδΩ

/-! ### Mollifiers supported in the cone of a Lipschitz graph -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The bump function of the cone mollifier: centre `e/4`, radii `ρ/4` and `ρ/2` for the cone
radius `ρ = 1/(8(M + 1))`. -/
noncomputable def coneMollifierBase : ContDiffBump ((1 / 4 : ℝ) • Ω.e) :=
  ⟨Ω.coneRadius / 4, Ω.coneRadius / 2, by have := Ω.coneRadius_pos; positivity,
    by have := Ω.coneRadius_pos; linarith⟩

/-- **The cone mollifier**: a smooth function with integral `1` and compact support in the open
cone `K` of the graph and in `closedBall(0, 1/2)`
(`Rd.LipschitzGraph.tsupport_coneMollifier_subset`), the
mollifier of the bump `Rd.LipschitzGraph.coneMollifierBase`. Convolution with its dilates moves
the closure of the graph domain into the domain (`Rd.LipschitzGraph.add_mem_of_mem_closure`). -/
noncomputable def coneMollifier : V → ℂ := bumpMollifier Ω.coneMollifierBase

/-- The cone mollifier is supported in the open cone and in `closedBall(0, 1/2)`: its closed
support is
`closedBall(e/4, ρ/2) ⊆ B(e/4, ρ) ⊆ K` (`Rd.LipschitzGraph.ball_subset_cone`), and
`‖e/4‖ + ρ/2 ≤ 1/2`. -/
theorem tsupport_coneMollifier_subset :
    tsupport Ω.coneMollifier ⊆ Ω.cone ∩ closedBall 0 (1 / 2) := by
  intro z hz
  have h := tsupport_bumpMollifier_subset Ω.coneMollifierBase hz
  have hρ := Ω.coneRadius_pos
  have hρ8 := Ω.coneRadius_le
  have hr : Ω.coneMollifierBase.rOut = Ω.coneRadius / 2 := rfl
  rw [hr] at h
  refine ⟨Ω.ball_subset_cone (closedBall_subset_ball (by linarith) h), ?_⟩
  rw [mem_closedBall, dist_eq_norm] at h
  have he : ‖(1 / 4 : ℝ) • Ω.e‖ = 1 / 4 := by
    rw [norm_smul, Ω.norm_e, mul_one, Real.norm_of_nonneg (by norm_num)]
  have hz' : ‖z‖ ≤ ‖z - (1 / 4 : ℝ) • Ω.e‖ + ‖(1 / 4 : ℝ) • Ω.e‖ := by
    have := norm_add_le (z - (1 / 4 : ℝ) • Ω.e) ((1 / 4 : ℝ) • Ω.e)
    rwa [sub_add_cancel] at this
  rw [mem_closedBall_zero_iff]
  linarith

end LipschitzGraph

/-! ### `HTilde^1(Ω)` by supports -/

/-- **The zero extension of the restriction**: for an open `Ω` and `U ∈ H^1(V)` vanishing almost
everywhere outside `Ω`, the zero extension of the `L_2` function of `U|_Ω ∈ H^1(Ω)` is `ι U`, since
`U|_Ω = U` almost everywhere on `Ω` (`Rd.sub_restrictProj_mem`, `Rd.mem_vanishOn_one_iff`). -/
theorem indicatorLp_toL2_restrictProj {Ω : Opens V} {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ (Ω : Set V) → toL2 U x = 0) :
    indicatorLp Ω.isOpen.measurableSet (toL2 (restrictProj 1 Ω U : H^{1}(V))) = toL2 U := by
  have h := (mem_vanishOn_one_iff _).1 (sub_restrictProj_mem (s := 1) (Ω := Ω) U)
  rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet] at h
  refine Lp.ext ?_
  filter_upwards [indicatorLp_apply_ae Ω.isOpen.measurableSet
    (toL2 (restrictProj 1 Ω U : H^{1}(V))), h, hU,
    Lp.coeFn_sub (toL2 U) (toL2 (restrictProj 1 Ω U : H^{1}(V)))] with x h1 h2 h3 h4
  rw [h1]
  by_cases hx : x ∈ (Ω : Set V)
  · have h5 := h2 hx
    rw [map_sub, h4, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h5
    rw [indicator_of_mem hx, h5]
  · rw [indicator_of_notMem hx, h3 hx]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The local lemma: chart pieces of functions vanishing outside `Ω` lie in `HTilde^1(Ω)`**: let
`U ∈ H^1(V)` vanish almost everywhere outside `Ω`, and let `ζ` be a continuous bounded real
function with closed support in the boundary ball `B_j`. Every `W ∈ H^1(V)` with `ι W = ζ ι U`
lies in `HTilde^1(Ω)`. `W` vanishes outside the compact set `S = ΩBar_j ∩ supp ζ`, since `Ω ∩
B_j` is
the graph domain `Ω_j` inside `B_j`; the cone mollifier of the chart moves `S` into `Ω_j`
(`Rd.LipschitzGraph.add_mem_of_mem_closure`, `Rd.LipschitzGraph.mem_cone_of_mem_tsupport_dilate`),
and its small dilates keep it inside `B_j`
(`Rd.eventually_tsupport_dilate_add_subset_thickening`, `Rd.mem_tildeSpace_of_dilate`). -/
theorem mem_tildeSpace_of_mulLp_chart (j : Fin Ω.N) {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0) {ζ : V → ℝ}
    (hζ : tsupport ζ ⊆ ball (Ω.center j) (Ω.radius j)) {C : ℝ}
    (hc : Continuous fun x => (ζ x : ℂ)) (hC : ∀ x, ‖(ζ x : ℂ)‖ ≤ C) {W : H^{1}(V)}
    (hW : toL2 W = mulLp hc hC (toL2 U)) : W ∈ tildeSpace 1 Ω.toOpens := by
  have hB := Ω.inter_ball_eq j le_rfl
  have hK : IsCompact (tsupport ζ) :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hζ)
  have hS : IsCompact (closure (Ω.graph j).domain ∩ tsupport ζ) := hK.inter_left isClosed_closure
  have hWS : ∀ᵐ x ∂volume, x ∉ closure (Ω.graph j).domain ∩ tsupport ζ → toL2 W x = 0 := by
    rw [hW]
    filter_upwards [mulLp_apply_ae hc hC (toL2 U), hU] with x h1 h2 hxS
    rw [h1]
    by_cases hxK : x ∈ tsupport ζ
    · have hxΩ : x ∉ Ω.carrier := fun hxΩ =>
        hxS ⟨subset_closure ((Set.ext_iff.1 hB x).1 ⟨hxΩ, hζ hxK⟩).1, hxK⟩
      rw [h2 hxΩ, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hxK, Complex.ofReal_zero, zero_mul]
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_thickening_subset_open isOpen_ball hζ
  have hη := (Ω.graph j).tsupport_coneMollifier_subset
  refine mem_tildeSpace_of_dilate (η := (Ω.graph j).coneMollifier) hS hWS
    (contDiff_bumpMollifier _) (hasCompactSupport_bumpMollifier _) (integral_bumpMollifier _) ?_
  filter_upwards [eventually_tsupport_dilate_add_subset_thickening (hη.trans inter_subset_right)
    hδ (closure (Ω.graph j).domain ∩ tsupport ζ)] with n hn
  rintro _ ⟨z, hz, y, hy, rfl⟩
  have hzK := (Ω.graph j).mem_cone_of_mem_tsupport_dilate (hη.trans inter_subset_left)
    (by positivity) hz
  have hzyB : z + y ∈ ball (Ω.center j) (Ω.radius j) :=
    hδB (thickening_subset_of_subset δ inter_subset_right (hn ⟨z, hz, y, hy, rfl⟩))
  have hzyD : z + y ∈ (Ω.graph j).domain := by
    rw [add_comm]
    exact (Ω.graph j).add_mem_of_mem_closure hy.1 hzK
  rw [Ω.coe_toOpens]
  exact ((Set.ext_iff.1 hB (z + y)).2 ⟨hzyD, hzyB⟩).1

/-- **The decomposition of a function vanishing outside `Ω`**: if `χ + ∑_j ψ_j = 1` on `Ω`,
`U ∈ H^1(V)` vanishes almost everywhere outside `Ω`, the `L_2` functions of `W_j` are `ψ_j ι U`
and that of `W_0` is `χ ι U`, then `U = ∑_j W_j + W_0` in `H^1(V)`: on `Ω` this is
`Rd.BoundedLipschitzDomain.toL2_ae_eq_sum_add`, outside `Ω` both sides vanish, and `ι` is
injective (`Rd.toL2_injective`). -/
theorem eq_sum_add_of_ae_eq_zero (ψ : Ω.BoundaryPartition) {χ : V → ℝ}
    (hχ1 : ∀ x ∈ Ω.carrier, χ x + ∑ j, ψ.toFun j x = 1) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0)
    {Wj : Fin Ω.N → H^{1}(V)} (hWj : ∀ j, toL2 (Wj j) = ψ.localize j (toL2 U))
    {W0 : H^{1}(V)} (hW0 : toL2 W0 = mulLp hc hC (toL2 U)) : U = ∑ j, Wj j + W0 := by
  refine toL2_injective (Lp.ext ?_)
  have hΩ := (ae_restrict_iff' Ω.measurableSet).1 (toL2_ae_eq_sum_add ψ hχ1 hc hC U hWj hW0)
  have h0 : (toL2 W0 : V → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) * toL2 U x := by
    rw [hW0]
    exact mulLp_apply_ae hc hC _
  have hloc : ∀ᵐ x ∂(volume : Measure V), ∀ j,
      (toL2 (Wj j) : V → ℂ) x = ψ.toComplex j x * toL2 U x := ae_all_iff.2 fun j => by
    rw [hWj j]
    exact mulLp_apply_ae _ _ _
  filter_upwards [hΩ, hU, hloc, h0, Lp.coeFn_add (∑ j, toL2 (Wj j)) (toL2 W0),
    Lp.coeFn_fun_finsetSum Finset.univ fun j => toL2 (Wj j)] with x h1 h2 h3 h4 h5 h6
  by_cases hx : x ∈ Ω.carrier
  · exact h1 hx
  · rw [map_add, map_sum, h5, Pi.add_apply, h6, h4, h2 hx]
    simp only [h3, h2 hx, mul_zero, Finset.sum_const_zero, add_zero]

/-- **Functions vanishing outside `Ω` lie in `HTilde^1(Ω)`**: on a bounded Lipschitz domain, every
`U ∈ H^1(V)` whose `L_2` function vanishes almost everywhere outside `Ω` lies in the closure of the
test functions of `Ω`. With a resolution of unity `ψ` equal to one near `Γ`
(`Rd.BoundedLipschitzDomain.exists_boundaryPartition_nhds`) and the interior cut-off `χ`
(`Rd.BoundedLipschitzDomain.exists_interior_cutoff`), `U = ∑_j ψ_j U + χ U`
(`Rd.BoundedLipschitzDomain.eq_sum_add_of_ae_eq_zero`); the chart pieces lie in `HTilde^1(Ω)` by the
cone mollifiers (`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart`), the interior piece
since it vanishes outside a compact subset of `Ω` (`Rd.mem_tildeSpace_of_isCompact`). -/
theorem mem_tildeSpace_of_ae_eq_zero {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0) : U ∈ tildeSpace 1 Ω.toOpens := by
  obtain ⟨ψ, -, -, hψ⟩ := Ω.exists_boundaryPartition_nhds
  obtain ⟨χ, hχ, hcs, hχΩ, hχ1⟩ := exists_interior_cutoff ψ hψ
  have hc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hcs.comp_left Complex.ofReal_zero)
  choose Wj hWj using fun j => ψ.exists_toL2_eq_localize j U
  obtain ⟨W0, hW0⟩ := exists_toL2_eq_mulLp hχ hcs hc hC U
  rw [Ω.eq_sum_add_of_ae_eq_zero ψ hχ1 hc hC hU hWj hW0]
  refine add_mem (Submodule.sum_mem _ fun j _ =>
    Ω.mem_tildeSpace_of_mulLp_chart j hU (ψ.tsupport_subset j) _ _ (hWj j)) ?_
  refine mem_tildeSpace_of_isCompact hcs.isCompact (by rw [Ω.coe_toOpens]; exact hχΩ) ?_
  rw [hW0]
  filter_upwards [mulLp_apply_ae hc hC (toL2 U)] with x hx hxS
  rw [hx, image_eq_zero_of_notMem_tsupport hxS, Complex.ofReal_zero, zero_mul]

/-- **`HTilde^1(Ω)` is the space of `H^1(V)` functions vanishing outside `Ω`**: on a bounded
Lipschitz
domain, `U ∈ H^1(V)` lies in `HTilde^1(Ω)` iff its `L_2` function vanishes almost everywhere outside
`Ω` (`Rd.toL2_ae_eq_zero_of_mem_tildeSpace`,
`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_ae_eq_zero`). Since `Γ` is a null set
(`Rd.BoundedLipschitzDomain.volume_frontier`), this is `HTilde^s(Ω) = H^s_{ΩBar}` of McLean
(Theorem 3.29) for `s = 1`. -/
theorem mem_tildeSpace_iff (U : H^{1}(V)) :
    U ∈ tildeSpace 1 Ω.toOpens ↔ ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0 :=
  ⟨toL2_ae_eq_zero_of_mem_tildeSpace, Ω.mem_tildeSpace_of_ae_eq_zero⟩

/-! ### `ker γ = H^1_0(Ω)` -/

/-- **`H^1_0(Ω) ⊆ ker γ`**: every element of `H^1_0(Ω)` is the restriction `U|_Ω` of some
`U ∈ HTilde^1(Ω)` (`Rd.range_tildeToRestriction`); `U` vanishes outside `Ω`
(`Rd.toL2_ae_eq_zero_of_mem_tildeSpace`), so the zero extension of `U|_Ω` is `ι U ∈ W^1_2(V)`
(`Rd.indicatorLp_toL2_restrictProj`), and its trace vanishes
(`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_iff_mem_traceKer`). -/
theorem zeroBoundarySpace_le_traceKer : zeroBoundarySpace 1 Ω.toOpens ≤ Ω.traceKer := by
  intro u hu
  rw [← range_tildeToRestriction] at hu
  obtain ⟨U, rfl⟩ := hu
  rw [← Ω.memSobolev_indicatorLp_iff_mem_traceKer]
  have h := indicatorLp_toL2_restrictProj (toL2_ae_eq_zero_of_mem_tildeSpace U.2)
  change MemSobolev 1 (indicatorLp Ω.toOpens.isOpen.measurableSet
    (toL2 (restrictProj 1 Ω.toOpens U : H^{1}(V))))
  rw [h]
  exact memSobolev_toL2 _

/-- **`ker γ ⊆ H^1_0(Ω)`**: for `u` in the trace kernel, the zero extension `1_Ω ι u` is the `L_2`
function of some `U ∈ H^1(V)` (`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_of_mem_traceKer`,
`Rd.exists_toL2_eq_of_memSobolev`). `U` vanishes outside `Ω`, so `U ∈ HTilde^1(Ω)`
(`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_ae_eq_zero`), and `u = U|_Ω`
(`Rd.restrictProj_eq_of_ae_eq`) lies in `H^1_0(Ω)` (`Rd.range_tildeToRestriction`). -/
theorem traceKer_le_zeroBoundarySpace : Ω.traceKer ≤ zeroBoundarySpace 1 Ω.toOpens := by
  intro u hu
  obtain ⟨U, hU⟩ := exists_toL2_eq_of_memSobolev (Ω.memSobolev_indicatorLp_of_mem_traceKer hu)
  have hUae : (toL2 U : V → ℂ) =ᵐ[volume] Ω.carrier.indicator (toL2 (u : H^{1}(V))) := by
    rw [hU]
    exact indicatorLp_apply_ae _ _
  have hU0 : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0 := by
    filter_upwards [hUae] with x hx hxΩ
    rw [hx, indicator_of_notMem hxΩ]
  have hUu : (toL2 U : V → ℂ) =ᵐ[volume.restrict (Ω.toOpens : Set V)] toL2 (u : H^{1}(V)) := by
    rw [Ω.coe_toOpens]
    filter_upwards [ae_restrict_of_ae hUae, ae_restrict_mem Ω.measurableSet] with x hx hxΩ
    rw [hx, indicator_of_mem hxΩ]
  rw [← restrictProj_eq_of_ae_eq hUu, ← range_tildeToRestriction]
  exact ⟨⟨U, Ω.mem_tildeSpace_of_ae_eq_zero hU0⟩, rfl⟩

/-- **`ker γ = H^1_0(Ω)`** on a bounded Lipschitz domain (McLean, Theorem 3.40; Hiptmair, Pauly
and Schulz cite it for `ker γ = H^1_0(Ω)`): the elements of `H^1(Ω)` whose chart traces all vanish,
equivalently whose boundary trace vanishes almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff`), are exactly the limits in `H^1(Ω)` of test
functions of `Ω` (`Rd.BoundedLipschitzDomain.zeroBoundarySpace_le_traceKer`,
`Rd.BoundedLipschitzDomain.traceKer_le_zeroBoundarySpace`). -/
theorem traceKer_eq_zeroBoundarySpace : Ω.traceKer = zeroBoundarySpace 1 Ω.toOpens :=
  le_antisymm Ω.traceKer_le_zeroBoundarySpace Ω.zeroBoundarySpace_le_traceKer

/-! ### The quotient and the duals -/

/-- **`H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)` isometrically**: the quotient of `H^1(Ω)` by `H^1_0(Ω)`,
with the quotient norm, is isometrically isomorphic to the trace space, the orthogonal complement
of `ker γ = H^1_0(Ω)` (Mathlib's `Submodule.quotientEquivOrthogonal`,
`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`); the class of `u` corresponds to `γ u`
(`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace_mk`). The content is
`ker γ = H^1_0(Ω)`; the isometry holds by the definition of the trace space as the orthogonal
complement of `ker γ`. This is the trace space of Hiptmair, Pauly and Schulz for `k = 0`; its norm
is equivalent to the Sobolev–Slobodeckij norm of the classical `H^{1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`). -/
noncomputable def quotientZeroBoundaryEquivTraceSpace :
    (Ω.SobolevOne ⧸ zeroBoundarySpace 1 Ω.toOpens) ≃ₗᵢ[ℂ] Ω.TraceSpace :=
  (Submodule.quotientEquivOrthogonal (zeroBoundarySpace 1 Ω.toOpens)).trans
    (LinearIsometryEquiv.ofEq _ _ (by rw [Ω.traceKer_eq_zeroBoundarySpace]))

/-- The class of `u` modulo `H^1_0(Ω)` corresponds to the trace `γ u`. -/
theorem quotientZeroBoundaryEquivTraceSpace_mk (u : Ω.SobolevOne) :
    Ω.quotientZeroBoundaryEquivTraceSpace (Submodule.Quotient.mk u) = Ω.trace u := by
  have hK := Ω.traceKer_eq_zeroBoundarySpace
  have hx : (Ω.trace u : Ω.SobolevOne) ∈ (zeroBoundarySpace 1 Ω.toOpens)ᗮ := by
    rw [← hK]
    exact (Ω.trace u).2
  have hm : u - Ω.extend (Ω.trace u) ∈ zeroBoundarySpace 1 Ω.toOpens := by
    rw [← hK]
    exact Ω.sub_extend_trace_mem u
  have h : (Submodule.Quotient.mk u : Ω.SobolevOne ⧸ zeroBoundarySpace 1 Ω.toOpens) =
      Submodule.Quotient.mk (Ω.trace u : Ω.SobolevOne) := (Submodule.Quotient.eq _).2 hm
  rw [quotientZeroBoundaryEquivTraceSpace, LinearIsometryEquiv.trans_apply, h,
    Submodule.quotientEquivOrthogonal_mk _ _ hx]
  rfl

/-- **`HTilde^1(Ω) ≅ ker γ` isometrically**: restriction is an isometry of `HTilde^1(Ω)` onto
`H^1_0(Ω) = ker γ` (`Rd.tildeEquivZeroBoundary`,
`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`). -/
noncomputable def tildeEquivTraceKer : tildeSpace 1 Ω.toOpens ≃ₗᵢ[ℂ] Ω.traceKer :=
  (tildeEquivZeroBoundary Ω.toOpens).trans
    (LinearIsometryEquiv.ofEq _ _ Ω.traceKer_eq_zeroBoundarySpace.symm)

/-- `tildeEquivTraceKer Ω U` is the restriction of `U` to `Ω`. -/
theorem coe_tildeEquivTraceKer_apply (U : tildeSpace 1 Ω.toOpens) :
    (Ω.tildeEquivTraceKer U : Ω.SobolevOne) = restrictProj 1 Ω.toOpens U :=
  rfl

/-- **The element of `HTilde^1(Ω)` with restriction `u ∈ ker γ` is `u` itself**, read in `H^1(V)`
(`Rd.coe_tildeEquivZeroBoundary_symm_apply`). -/
theorem coe_tildeEquivTraceKer_symm_apply (u : Ω.traceKer) :
    ((Ω.tildeEquivTraceKer.symm u : tildeSpace 1 Ω.toOpens) : H^{1}(V)) =
      ((u : Ω.SobolevOne) : H^{1}(V)) := by
  rw [tildeEquivTraceKer, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.ofEq_symm,
    coe_tildeEquivZeroBoundary_symm_apply, LinearIsometryEquiv.coe_ofEq_apply]

/-- **The dual of `ker γ` is `H^{-1}(Ω)`**: every bounded functional `ℓ` on the trace kernel is
`u ↦ [W, u]` for exactly one `W ∈ H^{-1}(Ω)`, with `‖W‖ = ‖ℓ‖`
(`Rd.BoundedLipschitzDomain.dualTraceKerEquiv_apply`,
`Rd.BoundedLipschitzDomain.dualTraceKerEquiv_eq_iff`); Riesz on `ker γ`, the isometry
`Rd.BoundedLipschitzDomain.tildeEquivTraceKer` and the duality `HTilde^1(Ω) ≅ H^{-1}(Ω)`
(`Rd.tildeEquivRestriction`), as for `Rd.dualZeroBoundaryEquiv`. -/
noncomputable def dualTraceKerEquiv :
    StrongDual ℂ Ω.traceKer ≃ₗᵢ⋆[ℂ] RestrictionSpace (-1) Ω.toOpens :=
  (InnerProductSpace.toDual ℂ Ω.traceKer).symm.trans
    (Ω.tildeEquivTraceKer.symm.trans (tildeEquivRestriction 1 Ω.toOpens))

/-- **`ℓ` is the pairing with `dualTraceKerEquiv Ω ℓ`**: `ℓ(u) = [W, u]` for
`W = dualTraceKerEquiv Ω ℓ` and every `u ∈ ker γ`, read as an element of `H^1(V)`. -/
theorem dualTraceKerEquiv_apply (ℓ : StrongDual ℂ Ω.traceKer) (u : Ω.traceKer) :
    ℓ u = pairing 1 (Ω.dualTraceKerEquiv ℓ : H^{-1}(V)) ((u : Ω.SobolevOne) : H^{1}(V)) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := Ω.traceKer) (x := u) (y := ℓ)
  rw [← h, ← LinearIsometryEquiv.inner_map_map Ω.tildeEquivTraceKer.symm,
    Submodule.coe_inner, dualTraceKerEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, coe_tildeEquivRestriction_apply, pairing_besselShift,
    Ω.coe_tildeEquivTraceKer_symm_apply u]

/-- The functional of `W ∈ H^{-1}(Ω)` on `ker γ` is `u ↦ [W, u]`. -/
theorem dualTraceKerEquiv_symm_apply (W : RestrictionSpace (-1) Ω.toOpens) (u : Ω.traceKer) :
    Ω.dualTraceKerEquiv.symm W u =
      pairing 1 (W : H^{-1}(V)) ((u : Ω.SobolevOne) : H^{1}(V)) := by
  rw [dualTraceKerEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualTraceKerEquiv Ω ℓ = W` iff
`ℓ(u) = [W, u]` for every `u ∈ ker γ`. -/
theorem dualTraceKerEquiv_eq_iff (ℓ : StrongDual ℂ Ω.traceKer)
    (W : RestrictionSpace (-1) Ω.toOpens) :
    Ω.dualTraceKerEquiv ℓ = W ↔ ∀ u : Ω.traceKer,
      ℓ u = pairing 1 (W : H^{-1}(V)) ((u : Ω.SobolevOne) : H^{1}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualTraceKerEquiv_symm_apply]

end BoundedLipschitzDomain

end Rd
