/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Sobolev.LipschitzGraphGreen
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeLeibniz

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Green's formula on bounded Lipschitz domains

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner product
space `V`, such as `ℝ^d`, with the boundary balls `B_j`, the Lipschitz graph domains `Ω_j` over the
hyperplanes `H_j`, the graph maps `γ_j`, the traces `Tr_j`, the normal weights
`n^j_v = ⟪∇φ_j, v⟫ - ⟪v, e_j⟫`, the surface measure `σ` and the outward unit normal `ν`.

* **Integration by parts in `H^1(V)`**: `∫_V (∂_v U) W + U ∂_v W = 0` for `U, W ∈ H^1(V)`
  (`Rd.integral_weakDeriv_mul_add_eq_zero`), by density of the Schwartz functions, and likewise
  for `f, g ∈ W^1_2(V)` (`Rd.integral_mul_add_eq_zero_of_hasWeakLineDeriv`).
* **Green's formula in chart form** (`Rd.BoundedLipschitzDomain.setIntegral_green_of_nhds`): for a
  resolution of unity `ψ` equal to one near `Γ`
  (`Rd.BoundedLipschitzDomain.exists_boundaryPartition_nhds`),
  `∫_Ω (∂_v U) W + U ∂_v W = ∑_j ∫_{H_j} ψ_j(γ_j x') Tr_j U Tr_j W n^j_v dx'`. The pieces `ψ_j W`
  give Green's formula on the graph domains, and the interior piece `χ W` with the smooth
  `χ = 1_Ω (1 - ∑_j ψ_j)` of compact support in `Ω`
  (`Rd.BoundedLipschitzDomain.exists_interior_cutoff`) integrates to zero.
* **The unit normal** (`Rd.BoundedLipschitzDomain.normal_ae_eq_normalAt`): on every ball `B_j`,
  `ν = ν_j ∘ P_j` `σ`-almost everywhere, so `‖ν‖ = 1` and `ν` points out of `Ω` almost everywhere
  (`Rd.BoundedLipschitzDomain.norm_normal_ae`, `Rd.BoundedLipschitzDomain.inner_normal_neg_ae`).
  Gauss–Green for `C^1` functions in two charts gives the same boundary integrals, and test
  functions on `H_j` are restrictions of test functions on `V`
  (`Rd.LipschitzGraph.exists_contDiff_comp_graphMap_eq`).
* **Green's formula** (`Rd.BoundedLipschitzDomain.setIntegral_green_surface`,
  `Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne`):
  `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ u · γ w ⟪v, ν⟫ dσ` for `u, w ∈ H^1(Ω)`, also with weak
  derivatives on `Ω`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne_of_hasWeakLineDeriv`), and in chart
  form for every resolution of unity (`Rd.BoundedLipschitzDomain.setIntegral_green`).
* **The zero extension** (`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_iff_mem_traceKer`): for
  `u ∈ H^1(Ω)`, `1_Ω u ∈ W^1_2(V)` iff the trace of `u` vanishes, and then
  `∂_v (1_Ω u) = 1_Ω ∂_v u`. One direction is Green's formula without boundary term, the other
  compares the traces from both sides of each graph, with the lower graph domain
  `{x : ⟪x, e⟫ < φ(x)}` (`Rd.LipschitzGraph.lower`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Topology Set
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace LineDeriv

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Integration by parts in `H^1(V)` -/

/-- **The weak derivatives of `H^1(V)` are local**: if the `L_2` function of `U ∈ H^1(V)`
vanishes almost everywhere on an open set `O`, so does its weak derivative `∂_v U`
(`Rd.HasWeakLineDeriv.ae_eq_zero_of_ae_eq_zero`). -/
theorem weakDerivL2_ae_eq_zero_of_ae_eq_zero {O : Set V} (hO : IsOpen O) (v : V)
    {U : H^{1}(V)} (hU : (toL2 U : V → ℂ) =ᵐ[volume.restrict O] 0) :
    (weakDerivL2 v U : V → ℂ) =ᵐ[volume.restrict O] 0 :=
  (hasWeakLineDeriv_weakDerivL2 v U).ae_eq_zero_of_ae_eq_zero (O := ⟨O, hO⟩) le_top hU

/-- **Weak derivatives of functions that agree on an open set agree there**: if the `L_2`
functions of `U, W ∈ H^1(V)` agree almost everywhere on an open set `O`, so do `∂_v U` and
`∂_v W` (`Rd.weakDerivL2_ae_eq_zero_of_ae_eq_zero` for `U - W`). -/
theorem weakDerivL2_ae_eq_of_ae_eq {O : Set V} (hO : IsOpen O) (v : V) {U W : H^{1}(V)}
    (h : (toL2 U : V → ℂ) =ᵐ[volume.restrict O] toL2 W) :
    (weakDerivL2 v U : V → ℂ) =ᵐ[volume.restrict O] weakDerivL2 v W := by
  have h0 := weakDerivL2_ae_eq_zero_of_ae_eq_zero hO v (U := U - W) (by
    filter_upwards [h, ae_restrict_of_ae (Lp.coeFn_sub (toL2 U) (toL2 W))] with x hx hs
    rw [map_sub, hs, Pi.sub_apply, hx, sub_self, Pi.zero_apply])
  filter_upwards [h0, ae_restrict_of_ae (Lp.coeFn_sub (weakDerivL2 v U) (weakDerivL2 v W))]
    with x hx hs
  rw [map_sub, hs, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx
  exact hx

/-- The integrand `(∂_v U) W + U ∂_v W` of Green's formula is integrable for `U, W ∈ H^1(V)`, a
sum of products of `L_2` functions. -/
theorem integrable_weakDeriv_mul_add (v : V) (U W : H^{1}(V)) :
    Integrable fun x => weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x :=
  ((Lp.memLp _).integrable_mul (Lp.memLp _)).add ((Lp.memLp _).integrable_mul (Lp.memLp _))

/-- **Green's integrand is linear in the second function**: for a measurable set `s` and a finite
family `W_i ∈ H^1(V)`, `∫_s (∂_v U) ∑_i W_i + U ∂_v ∑_i W_i` is the sum of the integrals
(`Rd.setIntegral_weakDeriv_mul_add_eq`). -/
theorem setIntegral_weakDeriv_mul_add_sum {s : Set V} (hs : MeasurableSet s) (v : V)
    (U : H^{1}(V)) {ι : Type*} (t : Finset ι) (W : ι → H^{1}(V)) :
    ∫ x in s, weakDerivL2 v U x * toL2 (∑ i ∈ t, W i) x +
        toL2 U x * weakDerivL2 v (∑ i ∈ t, W i) x =
      ∑ i ∈ t, ∫ x in s, weakDerivL2 v U x * toL2 (W i) x + toL2 U x * weakDerivL2 v (W i) x := by
  rw [setIntegral_weakDeriv_mul_add_eq hs]
  simp only [setIntegral_weakDeriv_mul_add_eq hs, map_sum, Finset.sum_add_distrib]

/-- **Green's integrand is additive in the second function**: for a measurable set `s`,
`∫_s (∂_v U)(W₁ + W₂) + U ∂_v (W₁ + W₂)` is the sum of the two integrals
(`Rd.setIntegral_weakDeriv_mul_add_eq`). -/
theorem setIntegral_weakDeriv_mul_add_add {s : Set V} (hs : MeasurableSet s) (v : V)
    (U W₁ W₂ : H^{1}(V)) :
    ∫ x in s, weakDerivL2 v U x * toL2 (W₁ + W₂) x + toL2 U x * weakDerivL2 v (W₁ + W₂) x =
      (∫ x in s, weakDerivL2 v U x * toL2 W₁ x + toL2 U x * weakDerivL2 v W₁ x) +
        ∫ x in s, weakDerivL2 v U x * toL2 W₂ x + toL2 U x * weakDerivL2 v W₂ x := by
  rw [setIntegral_weakDeriv_mul_add_eq hs, setIntegral_weakDeriv_mul_add_eq hs,
    setIntegral_weakDeriv_mul_add_eq hs, map_add, map_add, map_add, map_add]
  ring

/-- The left side of Green's formula on `V`, `(U, W) ↦ ∫ (∂_v U) W + U ∂_v W`, is continuous on
`H^1(V) × H^1(V)` (`Rd.continuous_setIntegral_weakDeriv_mul_add` on `s = V`). -/
theorem continuous_integral_weakDeriv_mul_add (v : V) : Continuous fun p : H^{1}(V) × H^{1}(V) =>
    ∫ x, weakDerivL2 v p.1 x * toL2 p.2 x + toL2 p.1 x * weakDerivL2 v p.2 x := by
  simpa only [Measure.restrict_univ] using
    continuous_setIntegral_weakDeriv_mul_add (V := V) MeasurableSet.univ v

/-- **Integration by parts for Schwartz functions**: `∫ (∂_v w₁) w₂ + w₁ ∂_v w₂ = 0` for Schwartz
functions `w₁, w₂` (Mathlib's `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left`). -/
theorem integral_lineDerivOp_mul_add_eq_zero (v : V) (w₁ w₂ : 𝓢(V, ℂ)) :
    ∫ x, (∂_{v} w₁) x * w₂ x + w₁ x * (∂_{v} w₂) x = 0 := by
  have i1 : Integrable fun x => (∂_{v} w₁) x * w₂ x :=
    ((∂_{v} w₁).memLp 2 volume).integrable_mul (w₂.memLp 2 volume)
  have i2 : Integrable fun x => w₁ x * (∂_{v} w₂) x :=
    (w₁.memLp 2 volume).integrable_mul ((∂_{v} w₂).memLp 2 volume)
  rw [integral_add i1 i2, SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left w₁ w₂ v,
    add_neg_cancel]

/-- **Integration by parts in `H^1(V)`**: for `U, W ∈ H^1(V)` and every direction `v`,
`∫ (∂_v U) W + U ∂_v W = 0`. Both sides are continuous on `H^1(V) × H^1(V)`
(`Rd.continuous_integral_weakDeriv_mul_add`) and the identity holds for Schwartz functions
(`Rd.integral_lineDerivOp_mul_add_eq_zero`), which are dense (`Rd.denseRange_ofSchwartz`). -/
theorem integral_weakDeriv_mul_add_eq_zero (v : V) (U W : H^{1}(V)) :
    ∫ x, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x = 0 := by
  refine (denseRange_ofSchwartz (V := V) 1).induction_on₂
    (p := fun U W : H^{1}(V) =>
      ∫ x, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x = 0)
    (isClosed_eq (continuous_integral_weakDeriv_mul_add v) continuous_const) (fun w₁ w₂ => ?_) U W
  rw [← integral_lineDerivOp_mul_add_eq_zero v w₁ w₂]
  refine integral_congr_ae ?_
  rw [weakDerivL2_ofSchwartz, weakDerivL2_ofSchwartz, toL2_ofSchwartz, toL2_ofSchwartz]
  filter_upwards [(∂_{v} w₁).coeFn_toLp 2 volume, (∂_{v} w₂).coeFn_toLp 2 volume,
    w₁.coeFn_toLp 2 volume, w₂.coeFn_toLp 2 volume] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **Integration by parts for `W^1_2(V)` functions**: for `f, g ∈ L_2(V)` with
`f, g ∈ W^1_2(V)`, every direction `v` and the weak derivatives `f_v = ∂_v f`, `g_v = ∂_v g` in
`L_2(V)`, `∫ f_v g + f g_v = 0`. Here `f = ι U`, `g = ι W` for `U, W ∈ H^1(V)`
(`Rd.exists_toL2_eq_of_memSobolev`), so this is `Rd.integral_weakDeriv_mul_add_eq_zero`. -/
theorem integral_mul_add_eq_zero_of_hasWeakLineDeriv (f g : Lp ℂ 2 (volume : Measure V))
    (hf : MemSobolev 1 f) (hg : MemSobolev 1 g) (v : V) {fv gv : Lp ℂ 2 (volume : Measure V)}
    (hfv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) f fv)
    (hgv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) g gv) :
    ∫ x, fv x * g x + f x * gv x = 0 := by
  obtain ⟨U, rfl⟩ := exists_toL2_eq_of_memSobolev hf
  obtain ⟨W, rfl⟩ := exists_toL2_eq_of_memSobolev hg
  rw [← weakDerivL2_eq hfv, ← weakDerivL2_eq hgv]
  exact integral_weakDeriv_mul_add_eq_zero v U W

/-! ### Localisation -/

/-- **Sets that agree inside `B`**: if `s ∩ B = t ∩ B` and `F` vanishes almost everywhere outside
`B`, then `∫_s F = ∫_t F`. -/
theorem setIntegral_eq_of_inter_eq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s t B : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ B = t ∩ B) {F : α → E} (hF : ∀ᵐ x ∂μ, x ∉ B → F x = 0) :
    ∫ x in s, F x ∂μ = ∫ x in t, F x ∂μ := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  by_cases hB : x ∈ B
  · have hst : x ∈ s ↔ x ∈ t := by simpa [hB] using Set.ext_iff.1 h x
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs, indicator_of_mem (hst.1 hxs)]
    · rw [indicator_of_notMem hxs, indicator_of_notMem (fun h' => hxs (hst.2 h'))]
  · rw [indicator_apply_eq_zero.2 fun _ => hx hB, indicator_apply_eq_zero.2 fun _ => hx hB]

/-- **Testing a zero extension**: for a measurable `s ⊆ V`, `F ∈ L_p(V)`, a real function `φ` and
a function `h` equal to `φ` almost everywhere, `∫_V φ · 1_s F = ∫_s F h`. -/
theorem integral_smul_indicatorLp_eq_setIntegral_mul {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set V}
    (hs : MeasurableSet s)
    (F : Lp ℂ p (volume : Measure V)) {φ : V → ℝ} {h : V → ℂ}
    (hh : h =ᵐ[volume] fun x => (φ x : ℂ)) :
    ∫ x, φ x • (indicatorLp hs F : V → ℂ) x = ∫ x in s, F x * h x := by
  rw [← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorLp_apply_ae hs F, hh] with x h1 h2
  rw [h1]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx, h2, Complex.real_smul]
    ring
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]

/-- **Smooth multipliers keep `H^1(V)`**: for a smooth real `χ` with compact support and
`W ∈ H^1(V)` there is `W' ∈ H^1(V)` whose `L_2` function is `χ ι W` (`Rd.MemSobolev.mulLp`). -/
theorem exists_toL2_eq_mulLp {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hcs : HasCompactSupport χ) {C : ℝ} (hc : Continuous fun x => (χ x : ℂ))
    (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) (W : H^{1}(V)) :
    ∃ W' : H^{1}(V), toL2 W' = mulLp hc hC (toL2 W) :=
  exists_toL2_eq_of_memSobolev ((memSobolev_toL2 W).mulLp hχ hcs hc hC)

/-- **Green's integrand of a product vanishes outside the multiplier**: if the `L_2` function of
`W' ∈ H^1(V)` is `χ ι W` for a continuous bounded `χ`, then `(∂_v U) W' + U ∂_v W' = 0` almost
everywhere outside the closed support of `χ` (`Rd.weakDerivL2_ae_eq_zero_of_ae_eq_zero`). -/
theorem ae_weakDeriv_mul_add_eq_zero_of_mulLp {χ : V → ℝ} {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) {W W' : H^{1}(V)}
    (hW' : toL2 W' = mulLp hc hC (toL2 W)) (v : V) (U : H^{1}(V)) :
    ∀ᵐ x ∂volume, x ∉ tsupport χ →
      weakDerivL2 v U x * toL2 W' x + toL2 U x * weakDerivL2 v W' x = 0 := by
  have hO : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
  have h0 : (toL2 W' : V → ℂ) =ᵐ[volume.restrict (tsupport χ)ᶜ] 0 := by
    rw [hW']
    filter_upwards [ae_restrict_of_ae (mulLp_apply_ae hc hC (toL2 W)),
      ae_restrict_mem hO.measurableSet] with x hx hxO
    rw [hx, image_eq_zero_of_notMem_tsupport hxO, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  have h1 := weakDerivL2_ae_eq_zero_of_ae_eq_zero hO v h0
  rw [EventuallyEq, ae_restrict_iff' hO.measurableSet] at h0 h1
  filter_upwards [h0, h1] with x hx0 hx1 hx
  rw [hx0 hx, hx1 hx]
  simp only [Pi.zero_apply, mul_zero, add_zero]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Line derivatives vanish outside the closed support**: `∂_v g(x) = 0` for `x ∉ tsupport g`,
since `g` vanishes on a neighbourhood of `x`. -/
theorem lineDeriv_eq_zero_of_notMem_tsupport {g : V → ℂ} {x : V} (hx : x ∉ tsupport g) (v : V) :
    lineDeriv ℝ g x v = 0 := by
  rw [((notMem_tsupport_iff_eventuallyEq).1 hx).lineDeriv_eq]
  simp [lineDeriv]

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-! ### Test functions on the hyperplane as restrictions -/

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Test functions on the hyperplane are restrictions to the graph**: for an open `W ⊆ V` and a
smooth `φ : H → ℝ` with compact support in `γ⁻¹(W)` there is a smooth `g : V → ℝ` with compact
support in `W` and `g ∘ γ = φ`, namely `g(x) = φ(Px) χ(x)` for a smooth `χ` with support in the
bounded open set `W ∩ {dist(·, γ(supp φ)) < 1}` equal to `1` near the compact set `γ(supp φ)`
(`Rd.exists_smooth_partition_nhds`). -/
theorem exists_contDiff_comp_graphMap_eq {W : Set V} (hW : IsOpen W) {φ : Ω.hyperplane → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφW : tsupport φ ⊆ Ω.graphMap ⁻¹' W) :
    ∃ g : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ W ∧ ∀ x', g (Ω.graphMap x') = φ x' := by
  have hK : IsCompact (Ω.graphMap '' tsupport φ) := hφc.isCompact.image Ω.continuous_graphMap
  obtain ⟨χ, hχ, hχW, hχ1, -, -⟩ := exists_smooth_partition_nhds (ι := Unit) hK
    (fun _ => W ∩ thickening 1 (Ω.graphMap '' tsupport φ)) (fun _ => hW.inter isOpen_thickening)
    (by
      rintro _ ⟨x', hx', rfl⟩
      exact mem_iUnion.2 ⟨(), hφW hx', self_subset_thickening one_pos _ ⟨x', hx', rfl⟩⟩)
  have hχc : HasCompactSupport (χ ()) :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      (hK.isBounded.thickening.subset ((hχW ()).trans inter_subset_right))
  refine ⟨fun x => φ (Ω.proj x) * χ () x, (hφ.comp Ω.proj.contDiff).mul (hχ ()),
    hχc.mul_left, tsupport_mul_subset_right.trans ((hχW ()).trans inter_subset_left),
    fun x' => ?_⟩
  simp only [Ω.proj_graphMap]
  by_cases hx : x' ∈ tsupport φ
  · have h1 := hχ1.self_of_nhdsSet _ ⟨x', hx, rfl⟩
    rw [Fintype.sum_unique] at h1
    rw [show (default : Unit) = () from rfl] at h1
    rw [h1, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-! ### The graph domain below the graph -/

/-- **The lower graph domain** `{x : ⟪x, e⟫ < φ(x)}` below the graph of `φ`, as a Lipschitz graph
domain with the direction `-e` and the function `-φ`; it has the same graph
(`Rd.LipschitzGraph.lower_graphMap_proj_graphMap`) and lies in the complement of `Ω`
(`Rd.LipschitzGraph.notMem_domain_of_mem_lower_domain`). -/
def lower : LipschitzGraph V where
  e := -Ω.e
  norm_e := by rw [norm_neg, Ω.norm_e]
  M := Ω.M
  M_nonneg := Ω.M_nonneg
  phi x := -Ω.phi x
  lipschitz x y := by
    rw [show -Ω.phi x - -Ω.phi y = Ω.phi y - Ω.phi x by ring, norm_sub_rev]
    exact Ω.lipschitz y x
  const x t := by rw [smul_neg, ← neg_smul, Ω.const]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The lower graph domain is `{x : ⟪x, e⟫ < φ(x)}`. -/
theorem mem_lower_domain_iff (x : V) : x ∈ Ω.lower.domain ↔ inner ℝ x Ω.e < Ω.phi x := by
  change -Ω.phi x < inner ℝ x (-Ω.e) ↔ _
  rw [inner_neg_right, neg_lt_neg_iff]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The lower graph domain lies in the complement of `Ω`. -/
theorem notMem_domain_of_mem_lower_domain {x : V} (hx : x ∈ Ω.lower.domain) :
    x ∉ Ω.domain := fun h => lt_asymm h ((Ω.mem_lower_domain_iff x).1 hx)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The two domains have the same graph**: every point `γ(x')` of the graph of `Ω` is the point
`γ_-(P_- γ(x'))` of the graph of the lower domain. -/
theorem lower_graphMap_proj_graphMap (x' : Ω.hyperplane) :
    Ω.lower.graphMap (Ω.lower.proj (Ω.graphMap x')) = Ω.graphMap x' := by
  rw [Ω.lower.graphMap_proj_eq_iff]
  change inner ℝ (Ω.graphMap x') (-Ω.e) = -Ω.phi (Ω.graphMap x')
  rw [inner_neg_right, Ω.inner_graphMap, Ω.phi_graphMap]

/-- **The traces from above and from below agree**: for `U ∈ H^1(V)`, the trace of `U` on the
graph from `Ω` and from the lower domain agree, `Tr U(x') = Tr_- U(P_- γ(x'))` for almost every
`x' ∈ H` (`Rd.LipschitzGraph.trace_ae_eq_trace_comp`). -/
theorem traceH1_ae_eq_traceH1_lower (U : H^{1}(V)) :
    ∀ᵐ x' ∂(volume : Measure Ω.hyperplane),
      Ω.traceH1 U x' = Ω.lower.traceH1 U (Ω.lower.proj (Ω.graphMap x')) := by
  filter_upwards [Ω.trace_ae_eq_trace_comp Ω.lower two_ne_top one_le_two (s := 1 / 2)
    (by norm_num) (by norm_num) one_le_two (modNorm_toL2_lt_top U)] with x' hx'
  exact hx' (Ω.lower_graphMap_proj_graphMap x')

/-- **Functions vanishing below the graph have zero trace**: if `U ∈ H^1(V)` vanishes almost
everywhere on the part of the lower domain inside an open set `O`, then `Tr U(x') = 0` for almost
every `x'` with `γ(x') ∈ O`: the trace from below vanishes there
(`Rd.LipschitzGraph.trace_ae_eq_zero_of_ae_eq_zero`) and equals the trace from above
(`Rd.LipschitzGraph.traceH1_ae_eq_traceH1_lower`, with the null sets carried over by
`Rd.LipschitzGraph.ae_proj_graphMap`). -/
theorem traceH1_ae_eq_zero_of_lower {U : H^{1}(V)} {O : Set V} (hO : IsOpen O)
    (hU : ∀ᵐ x ∂(volume : Measure V), x ∈ Ω.lower.domain → x ∈ O → toL2 U x = 0) :
    ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), Ω.graphMap x' ∈ O → Ω.traceH1 U x' = 0 := by
  have h0 := Ω.lower.trace_ae_eq_zero_of_ae_eq_zero two_ne_top 2 (s := 1 / 2) (by norm_num)
    one_le_two (Ω.lower.intrinsicNorm_toL2_lt_top U) hO hU
  filter_upwards [Ω.traceH1_ae_eq_traceH1_lower U, Ω.ae_proj_graphMap Ω.lower h0] with x' h1 h2 hx'
  rw [h1]
  exact h2 (Ω.lower_graphMap_proj_graphMap x') (by rw [Ω.lower_graphMap_proj_graphMap]; exact hx')

end LipschitzGraph

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-! ### The interior cut-off -/

variable {Ω}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The interior remainder vanishes near the complement**: if `∑_j ψ_j = 1` on a neighbourhood
of `Γ`, the function `1_Ω (1 - ∑_j ψ_j)` vanishes on a neighbourhood of every point outside `Ω`. -/
theorem indicator_one_sub_sum_eventuallyEq_zero (ψ : Ω.BoundaryPartition)
    (hψ : ∀ᶠ y in 𝓝ˢ (frontier Ω.carrier), ∑ j, ψ.toFun j y = 1) {x : V} (hx : x ∉ Ω.carrier) :
    Ω.carrier.indicator (fun y => 1 - ∑ j, ψ.toFun j y) =ᶠ[𝓝 x] 0 := by
  by_cases hc : x ∈ closure Ω.carrier
  · have hf : x ∈ frontier Ω.carrier := ⟨hc, by rwa [Ω.isOpen.interior_eq]⟩
    filter_upwards [hψ.filter_mono (nhds_le_nhdsSet hf)] with y hy
    by_cases hyΩ : y ∈ Ω.carrier
    · rw [indicator_of_mem hyΩ, hy, sub_self, Pi.zero_apply]
    · rw [indicator_of_notMem hyΩ, Pi.zero_apply]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    rw [indicator_of_notMem (fun h => hy (subset_closure h)), Pi.zero_apply]

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The interior cut-off**: if `∑_j ψ_j = 1` on a neighbourhood of `Γ`, there is a smooth real
`χ` with compact support in `Ω` and `χ + ∑_j ψ_j = 1` on `Ω`, namely `χ = 1_Ω (1 - ∑_j ψ_j)`,
smooth because it vanishes near every point outside `Ω`
(`Rd.BoundedLipschitzDomain.indicator_one_sub_sum_eventuallyEq_zero`). -/
theorem exists_interior_cutoff (ψ : Ω.BoundaryPartition)
    (hψ : ∀ᶠ y in 𝓝ˢ (frontier Ω.carrier), ∑ j, ψ.toFun j y = 1) :
    ∃ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ω.carrier ∧ ∀ x ∈ Ω.carrier, χ x + ∑ j, ψ.toFun j x = 1 := by
  set χ := Ω.carrier.indicator (fun y => 1 - ∑ j, ψ.toFun j y)
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => 1 - ∑ j, ψ.toFun j y) :=
    contDiff_const.sub (ContDiff.sum fun j _ => ψ.contDiff j)
  have hts : tsupport χ ⊆ Ω.carrier := fun x hx => by
    by_contra h
    exact (notMem_tsupport_iff_eventuallyEq.2
      (indicator_one_sub_sum_eventuallyEq_zero ψ hψ h)) hx
  refine ⟨χ, contDiff_iff_contDiffAt.2 fun x => ?_, isCompact_of_isClosed_isBounded
    (isClosed_tsupport _) (Ω.isBounded.subset hts), hts, fun x hx => ?_⟩
  · by_cases hx : x ∈ Ω.carrier
    · exact hsm.contDiffAt.congr_of_eventuallyEq (eventually_of_mem (Ω.isOpen.mem_nhds hx)
        fun y hy => indicator_of_mem hy _)
    · exact contDiff_zero_fun.contDiffAt.congr_of_eventuallyEq
        (indicator_one_sub_sum_eventuallyEq_zero ψ hψ hx)
  · simp only [χ, indicator_of_mem hx]
    ring

/-- **Localised `H^1(V)` functions**: for every resolution of unity `ψ`, every chart `j` and
`W ∈ H^1(V)` there is `W' ∈ H^1(V)` whose `L_2` function is `ψ_j ι W`
(`Rd.exists_toL2_eq_mulLp`). -/
theorem BoundaryPartition.exists_toL2_eq_localize (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (W : H^{1}(V)) : ∃ W' : H^{1}(V), toL2 W' = ψ.localize j (toL2 W) :=
  exists_toL2_eq_mulLp (ψ.contDiff j) (ψ.hasCompactSupport j) _ _ W

/-! ### Green's formula in chart form -/

/-- **The chart pieces of Green's formula**: if the `L_2` function of `W' ∈ H^1(V)` is `ψ_j ι W`,
then `∫_Ω (∂_v U) W' + U ∂_v W' = ∫_{H_j} ψ_j(γ_j x') Tr_j U Tr_j W n^j_v dx'`. The integrand
vanishes outside `B_j`, where `Ω` agrees with the graph domain `Ω_j`, so this is Green's formula
on `Ω_j` (`Rd.LipschitzGraph.setIntegral_green_besselPotentialSpace`) with
`Tr_j (ψ_j W) = (ψ_j ∘ γ_j) Tr_j W` (`Rd.LipschitzGraph.trace_mulLp_ae`). -/
theorem setIntegral_weakDeriv_mul_add_localize (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (U : H^{1}(V)) {W W' : H^{1}(V)} (hW' : toL2 W' = ψ.localize j (toL2 W)) (v : V) :
    ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 W' x + toL2 U x * weakDerivL2 v W' x =
      ∫ x', ψ.toComplex j ((Ω.graph j).graphMap x') * (Ω.graph j).traceH1 U x' *
        (Ω.graph j).traceH1 W x' * ((Ω.graph j).normalWeight v x' : ℂ) := by
  have hz := ae_weakDeriv_mul_add_eq_zero_of_mulLp (χ := ψ.toFun j)
    (ψ.contDiff_toComplex j).continuous (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j)) hW'
    v U
  have hB : Ω.carrier ∩ ball (Ω.center j) (Ω.radius j) =
      (Ω.graph j).domain ∩ ball (Ω.center j) (Ω.radius j) := Ω.inter_ball_eq j le_rfl
  rw [setIntegral_eq_of_inter_eq Ω.measurableSet (Ω.graph j).measurableSet_domain hB
    (hz.mono fun x hx hxB => hx fun h => hxB (ψ.tsupport_subset j h)),
    (Ω.graph j).setIntegral_green_besselPotentialSpace U W' v]
  refine integral_congr_ae ?_
  have htr := (Ω.graph j).trace_mulLp_ae two_ne_top one_le_two (s := 1 / 2) (by norm_num)
    (by norm_num) one_le_two (ψ.contDiff_toComplex j) (ψ.derivBound_spec j)
    (modNorm_toL2_lt_top W)
  filter_upwards [htr] with x' hx'
  rw [(Ω.graph j).traceH1_apply W', hW', BoundaryPartition.localize, hx',
    (Ω.graph j).traceH1_apply W]
  ring

/-- **The interior piece of Green's formula vanishes**: if the `L_2` function of `W' ∈ H^1(V)` is
`χ ι W` for a continuous bounded `χ` with closed support in `Ω`, then
`∫_Ω (∂_v U) W' + U ∂_v W' = ∫_V (∂_v U) W' + U ∂_v W' = 0`
(`Rd.integral_weakDeriv_mul_add_eq_zero`). -/
theorem setIntegral_weakDeriv_mul_add_mulLp_eq_zero {χ : V → ℝ} (hχΩ : tsupport χ ⊆ Ω.carrier)
    {C : ℝ} (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) (U : H^{1}(V))
    {W W' : H^{1}(V)} (hW' : toL2 W' = mulLp hc hC (toL2 W)) (v : V) :
    ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 W' x + toL2 U x * weakDerivL2 v W' x = 0 := by
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero ((ae_weakDeriv_mul_add_eq_zero_of_mulLp hc hC
    hW' v U).mono fun x hx hxΩ => hx fun h => hxΩ (hχΩ h))]
  exact integral_weakDeriv_mul_add_eq_zero v U W'

/-- **The decomposition on `Ω`**: if `χ + ∑_j ψ_j = 1` on `Ω`, the `L_2` functions of `W_j` are
`ψ_j ι W` and that of `W_0` is `χ ι W`, then `ι W = ι (∑_j W_j + W_0)` almost everywhere on
`Ω`. -/
theorem toL2_ae_eq_sum_add (ψ : Ω.BoundaryPartition) {χ : V → ℝ}
    (hχ1 : ∀ x ∈ Ω.carrier, χ x + ∑ j, ψ.toFun j x = 1) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) (W : H^{1}(V))
    {Wj : Fin Ω.N → H^{1}(V)} (hWj : ∀ j, toL2 (Wj j) = ψ.localize j (toL2 W))
    {W0 : H^{1}(V)} (hW0 : toL2 W0 = mulLp hc hC (toL2 W)) :
    (toL2 W : V → ℂ) =ᵐ[volume.restrict Ω.carrier] toL2 (∑ j, Wj j + W0) := by
  have h0 : (toL2 W0 : V → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) * toL2 W x := by
    rw [hW0]
    exact mulLp_apply_ae hc hC _
  have hloc : ∀ᵐ x ∂(volume : Measure V), ∀ j,
      (toL2 (Wj j) : V → ℂ) x = ψ.toComplex j x * toL2 W x := ae_all_iff.2 fun j => by
    rw [hWj j]
    exact mulLp_apply_ae _ _ _
  filter_upwards [ae_restrict_mem Ω.measurableSet, ae_restrict_of_ae hloc,
    ae_restrict_of_ae (Lp.coeFn_add (∑ j, toL2 (Wj j)) (toL2 W0)),
    ae_restrict_of_ae (Lp.coeFn_fun_finsetSum Finset.univ fun j => toL2 (Wj j)),
    ae_restrict_of_ae h0] with x hx h1 h2 h3 h4
  rw [map_add, map_sum, h2, Pi.add_apply, h3, h4]
  simp only [h1]
  rw [← Finset.sum_mul, ← add_mul]
  have h5 : ∑ j, ψ.toComplex j x + (χ x : ℂ) = 1 := by
    simp only [BoundaryPartition.toComplex]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_add, add_comm, hχ1 x hx, Complex.ofReal_one]
  rw [h5, one_mul]

/-- **Green's formula on a bounded Lipschitz domain, chart form, for a resolution of unity equal
to one near the boundary**: if `∑_j ψ_j = 1` on a neighbourhood of `Γ`, then for all
`U, W ∈ H^1(V)` and every direction `v`,
`∫_Ω (∂_v U) W + U ∂_v W = ∑_j ∫_{H_j} ψ_j(γ_j x') Tr_j U Tr_j W n^j_v dx'`. Split
`W = ∑_j ψ_j W + χ W` on `Ω` with the interior cut-off `χ`
(`Rd.BoundedLipschitzDomain.exists_interior_cutoff`): the chart pieces are Green's formula on the
graph domains (`Rd.BoundedLipschitzDomain.setIntegral_weakDeriv_mul_add_localize`), and the
interior piece vanishes
(`Rd.BoundedLipschitzDomain.setIntegral_weakDeriv_mul_add_mulLp_eq_zero`). -/
theorem setIntegral_green_of_nhds (ψ : Ω.BoundaryPartition)
    (hψ : ∀ᶠ y in 𝓝ˢ (frontier Ω.carrier), ∑ j, ψ.toFun j y = 1) (U W : H^{1}(V)) (v : V) :
    ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
      ∑ j, ∫ x', ψ.toComplex j ((Ω.graph j).graphMap x') * (Ω.graph j).traceH1 U x' *
        (Ω.graph j).traceH1 W x' * ((Ω.graph j).normalWeight v x' : ℂ) := by
  obtain ⟨χ, hχ, hcs, hχΩ, hχ1⟩ := exists_interior_cutoff ψ hψ
  have hc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hcs.comp_left Complex.ofReal_zero)
  choose Wj hWj using fun j => ψ.exists_toL2_eq_localize j W
  obtain ⟨W0, hW0⟩ := exists_toL2_eq_mulLp hχ hcs hc hC W
  have hae := toL2_ae_eq_sum_add ψ hχ1 hc hC W hWj hW0
  have hint : ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
      ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 (∑ j, Wj j + W0) x +
        toL2 U x * weakDerivL2 v (∑ j, Wj j + W0) x := by
    refine integral_congr_ae ?_
    filter_upwards [hae, weakDerivL2_ae_eq_of_ae_eq Ω.isOpen v hae] with x h1 h2
    rw [h1, h2]
  rw [hint, setIntegral_weakDeriv_mul_add_add Ω.measurableSet,
    setIntegral_weakDeriv_mul_add_sum Ω.measurableSet,
    setIntegral_weakDeriv_mul_add_mulLp_eq_zero hχΩ hc hC U hW0, add_zero]
  exact Finset.sum_congr rfl fun j _ => setIntegral_weakDeriv_mul_add_localize ψ j U (hWj j) v

/-! ### The unit normal is the chart normal -/

variable (Ω)

/-- **Gauss–Green on `Ω` in one chart**: for a `C^1` function `g` with compact support in the
boundary ball `B_j` and every direction `v`, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν_j ∘ P_j⟫ dσ`. Inside `B_j`
the domain is the graph domain `Ω_j`, so this is Gauss–Green on `Ω_j`
(`Rd.LipschitzGraph.setIntegral_lineDeriv_eq_normal`) with the surface measure in the chart
(`Rd.BoundedLipschitzDomain.integral_surfaceMeasure_of_support`). -/
theorem setIntegral_lineDeriv_eq_chart (j : Fin Ω.N) {g : V → ℂ} (hg : ContDiff ℝ 1 g)
    (hgB : tsupport g ⊆ ball (Ω.center j) (Ω.radius j)) (v : V) :
    ∫ x in Ω.carrier, lineDeriv ℝ g x v = ∫ y, g y *
      (inner ℝ v ((Ω.graph j).normalAt ((Ω.graph j).proj y)) : ℂ) ∂Ω.surfaceMeasure := by
  have hgc : HasCompactSupport g :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport g) (isBounded_ball.subset hgB)
  rw [setIntegral_eq_of_inter_eq Ω.measurableSet (Ω.graph j).measurableSet_domain
    (Ω.inter_ball_eq j le_rfl) (ae_of_all _ fun x hx =>
      lineDeriv_eq_zero_of_notMem_tsupport (fun h => hx (hgB h)) v),
    (Ω.graph j).setIntegral_lineDeriv_eq_normal hg hgc v,
    Ω.integral_surfaceMeasure_of_support j _ fun y hy =>
      hgB (subset_tsupport _ (left_ne_zero_of_mul hy))]
  simp only [LipschitzGraph.proj_graphMap]

/-- For a continuous `g` with compact support, `y ↦ g(y) ⟪v, ν_j(P_j y)⟫` is integrable with
respect to the finite surface measure: it is bounded and measurable. -/
theorem integrable_mul_inner_normalAt (j : Fin Ω.N) {g : V → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (v : V) :
    Integrable (fun y => g y * (inner ℝ v ((Ω.graph j).normalAt ((Ω.graph j).proj y)) : ℂ))
      Ω.surfaceMeasure := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hm : Measurable fun y => (inner ℝ v ((Ω.graph j).normalAt ((Ω.graph j).proj y)) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_const.inner
      ((Ω.graph j).measurable_normalAt.comp (Ω.graph j).proj.continuous.measurable))
  refine Integrable.of_bound (hg.aestronglyMeasurable.mul hm.aestronglyMeasurable) (C * ‖v‖)
    (ae_of_all _ fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul (hC y) ((abs_real_inner_le_norm _ _).trans ?_) (abs_nonneg _)
    ((norm_nonneg _).trans (hC y))
  rw [(Ω.graph j).norm_normalAt, mul_one]

/-- **The chart normals give the same boundary integrals**: for a `C^1` function `g` with compact
support in `B_j ∩ B_k` and every `v`, `∫_Γ g ⟪v, ν_j ∘ P_j - ν_k ∘ P_k⟫ dσ = 0`, since both
chart integrals are `∫_Ω ∂_v g` (`Rd.BoundedLipschitzDomain.setIntegral_lineDeriv_eq_chart`). -/
theorem integral_mul_inner_normalAt_sub_eq_zero (j k : Fin Ω.N) {g : V → ℂ}
    (hg : ContDiff ℝ 1 g)
    (hgB : tsupport g ⊆ ball (Ω.center j) (Ω.radius j) ∩ ball (Ω.center k) (Ω.radius k))
    (v : V) :
    ∫ y, g y * (inner ℝ v ((Ω.graph j).normalAt ((Ω.graph j).proj y) -
      (Ω.graph k).normalAt ((Ω.graph k).proj y)) : ℂ) ∂Ω.surfaceMeasure = 0 := by
  have hgc : HasCompactSupport g := isCompact_of_isClosed_isBounded (isClosed_tsupport g)
    (isBounded_ball.subset (hgB.trans inter_subset_left))
  have hj := Ω.setIntegral_lineDeriv_eq_chart j hg (hgB.trans inter_subset_left) v
  have hk := Ω.setIntegral_lineDeriv_eq_chart k hg (hgB.trans inter_subset_right) v
  simp only [inner_sub_right, Complex.ofReal_sub, mul_sub]
  rw [integral_sub (Ω.integrable_mul_inner_normalAt j hg.continuous hgc v)
    (Ω.integrable_mul_inner_normalAt k hg.continuous hgc v), ← hj, ← hk, sub_self]

/-- **The chart identity in the chart**: for a `C^1` function `g` with compact support in
`B_j ∩ B_k` and every `v`,
`∫_{H_j} g(γ_j x') ⟪v, ν_j(x') - ν_k(P_k γ_j x')⟫ √(1 + ‖∇φ_j(x')‖²) dx' = 0`
(`Rd.BoundedLipschitzDomain.integral_mul_inner_normalAt_sub_eq_zero` and the surface measure in the
chart). -/
theorem integral_graphMap_mul_inner_normalAt_sub_eq_zero (j k : Fin Ω.N) {g : V → ℂ}
    (hg : ContDiff ℝ 1 g)
    (hgB : tsupport g ⊆ ball (Ω.center j) (Ω.radius j) ∩ ball (Ω.center k) (Ω.radius k))
    (v : V) :
    ∫ x', g ((Ω.graph j).graphMap x') * ((inner ℝ v ((Ω.graph j).normalAt x' -
      (Ω.graph k).normalAt ((Ω.graph k).proj ((Ω.graph j).graphMap x'))) *
        (Ω.graph j).gram x' : ℝ) : ℂ) = 0 := by
  rw [← Ω.integral_mul_inner_normalAt_sub_eq_zero j k hg hgB v,
    Ω.integral_surfaceMeasure_of_support j _ fun y hy =>
      (hgB (subset_tsupport _ (left_ne_zero_of_mul hy))).1]
  refine integral_congr_ae (ae_of_all _ fun x' => ?_)
  simp only [LipschitzGraph.proj_graphMap, Complex.ofReal_mul]
  ring

/-- The density `x' ↦ ⟪v, ν_j(x') - ν_k(P_k γ_j x')⟫ √(1 + ‖∇φ_j(x')‖²)` is locally integrable on
`H_j`: it is measurable and bounded by `2 ‖v‖ √(1 + M_j²)`. -/
theorem locallyIntegrable_inner_normalAt_sub_mul_gram (j k : Fin Ω.N) (v : V) :
    LocallyIntegrable (fun x' => inner ℝ v ((Ω.graph j).normalAt x' -
      (Ω.graph k).normalAt ((Ω.graph k).proj ((Ω.graph j).graphMap x'))) * (Ω.graph j).gram x')
      (volume : Measure (Ω.graph j).hyperplane) := by
  have hm : Measurable fun x' => inner ℝ v ((Ω.graph j).normalAt x' -
      (Ω.graph k).normalAt ((Ω.graph k).proj ((Ω.graph j).graphMap x'))) * (Ω.graph j).gram x' :=
    (measurable_const.inner ((Ω.graph j).measurable_normalAt.sub
      ((Ω.graph k).measurable_normalAt.comp ((Ω.graph k).proj.continuous.comp
        (Ω.graph j).continuous_graphMap).measurable))).mul (Ω.graph j).measurable_gram
  refine (memLp_top_of_bound hm.aestronglyMeasurable (‖v‖ * 2 * √(1 + (Ω.graph j).M ^ 2))
    (ae_of_all _ fun x' => ?_)).locallyIntegrable le_top
  have hn : ‖(Ω.graph j).normalAt x' -
      (Ω.graph k).normalAt ((Ω.graph k).proj ((Ω.graph j).graphMap x'))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [(Ω.graph j).norm_normalAt, (Ω.graph k).norm_normalAt]
    norm_num
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg ((Ω.graph j).gram_pos x').le]
  exact mul_le_mul ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn
    (norm_nonneg _))) ((Ω.graph j).gram_le x') ((Ω.graph j).gram_pos x').le (by positivity)

/-- **The chart normals agree on the overlaps, in the chart**: for almost every `x' ∈ H_j` with
`γ_j(x') ∈ B_j ∩ B_k`, `ν_j(x') = ν_k(P_k γ_j x')`. The density
`⟪v, ν_j - ν_k ∘ P_k ∘ γ_j⟫ √(1 + ‖∇φ_j‖²)` integrates to zero against every test function `φ` on
the open set `γ_j⁻¹(B_j ∩ B_k)`, which is `g ∘ γ_j` for a test function `g` with support in
`B_j ∩ B_k` (`Rd.LipschitzGraph.exists_contDiff_comp_graphMap_eq`,
`Rd.BoundedLipschitzDomain.integral_graphMap_mul_inner_normalAt_sub_eq_zero`); so it vanishes
almost everywhere there (Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), for each
vector `v` of an orthonormal basis. -/
theorem normalAt_graphMap_ae_eq (j k : Fin Ω.N) :
    ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
      (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j) ∩ ball (Ω.center k) (Ω.radius k) →
        (Ω.graph j).normalAt x' =
          (Ω.graph k).normalAt ((Ω.graph k).proj ((Ω.graph j).graphMap x')) := by
  set W := ball (Ω.center j) (Ω.radius j) ∩ ball (Ω.center k) (Ω.radius k)
  have hW : IsOpen W := isOpen_ball.inter isOpen_ball
  have hO : IsOpen ((Ω.graph j).graphMap ⁻¹' W) := hW.preimage (Ω.graph j).continuous_graphMap
  set b := stdOrthonormalBasis ℝ V
  have hi : ∀ i, ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
      x' ∈ (Ω.graph j).graphMap ⁻¹' W → inner ℝ (b i) ((Ω.graph j).normalAt x' -
        (Ω.graph k).normalAt ((Ω.graph k).proj ((Ω.graph j).graphMap x'))) *
          (Ω.graph j).gram x' = 0 := fun i =>
    hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Ω.locallyIntegrable_inner_normalAt_sub_mul_gram j k (b i)).locallyIntegrableOn _)
      fun φ hφ hφc hφO => by
        obtain ⟨g, hg, -, hgW, hgφ⟩ := (Ω.graph j).exists_contDiff_comp_graphMap_eq hW hφ hφc hφO
        have h := Ω.integral_graphMap_mul_inner_normalAt_sub_eq_zero j k (g := fun y => (g y : ℂ))
          ((Complex.ofRealCLM.contDiff.comp hg).of_le (by exact_mod_cast le_top))
          ((tsupport_comp_subset Complex.ofReal_zero g).trans hgW) (b i)
        simp only [hgφ, ← Complex.ofReal_mul] at h
        rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h
        simpa only [smul_eq_mul] using h
  filter_upwards [ae_all_iff.2 hi] with x' hx' hxW
  rw [← sub_eq_zero, ← b.sum_repr' ((Ω.graph j).normalAt x' -
    (Ω.graph k).normalAt ((Ω.graph k).proj ((Ω.graph j).graphMap x')))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(mul_eq_zero.1 (hx' i hxW)).resolve_right ((Ω.graph j).gram_pos x').ne', zero_smul]

/-- **The chart normals agree on the overlaps**: for `σ`-almost every `y ∈ B_j ∩ B_k`,
`ν_j(P_j y) = ν_k(P_k y)` (`Rd.BoundedLipschitzDomain.normalAt_graphMap_ae_eq` and the null sets
of `σ` in the chart, `Rd.BoundedLipschitzDomain.ae_surfaceMeasure_ball_iff`). -/
theorem normalAt_proj_ae_eq (j k : Fin Ω.N) :
    ∀ᵐ y ∂Ω.surfaceMeasure, y ∈ ball (Ω.center j) (Ω.radius j) →
      y ∈ ball (Ω.center k) (Ω.radius k) →
        (Ω.graph j).normalAt ((Ω.graph j).proj y) = (Ω.graph k).normalAt ((Ω.graph k).proj y) := by
  refine (Ω.ae_surfaceMeasure_ball_iff j).2 ?_
  filter_upwards [Ω.normalAt_graphMap_ae_eq j k] with x' hx' hj hk
  rw [LipschitzGraph.proj_graphMap]
  exact hx' ⟨hj, hk⟩

/-- **The unit normal is the chart normal**: for every chart `j` and `σ`-almost every `y ∈ B_j`,
`ν(y) = ν_j(P_j y)`. On `Γ`, `ν(y) = ∑_k ψ_k(y) ν_k(P_k y)` is a combination with weights
summing to `1` of chart normals that all agree with `ν_j(P_j y)`
(`Rd.BoundedLipschitzDomain.normalAt_proj_ae_eq`). -/
theorem normal_ae_eq_normalAt (j : Fin Ω.N) :
    ∀ᵐ y ∂Ω.surfaceMeasure, y ∈ ball (Ω.center j) (Ω.radius j) →
      Ω.normal y = (Ω.graph j).normalAt ((Ω.graph j).proj y) := by
  filter_upwards [ae_all_iff.2 fun k => Ω.normalAt_proj_ae_eq j k, Ω.ae_mem_frontier]
    with y hy hΓ hj
  have hterm : ∀ k, Ω.boundaryPartition.toFun k y • (Ω.graph k).normalAt ((Ω.graph k).proj y) =
      Ω.boundaryPartition.toFun k y • (Ω.graph j).normalAt ((Ω.graph j).proj y) := fun k => by
    by_cases h : Ω.boundaryPartition.toFun k y = 0
    · rw [h, zero_smul, zero_smul]
    · rw [hy k hj (Ω.boundaryPartition.mem_ball_of_ne_zero h)]
  rw [normal, Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_smul,
    Ω.boundaryPartition.sum_eq_one y hΓ, one_smul]

/-- **The unit normal is a unit vector**: `‖ν(y)‖ = 1` for `σ`-almost every `y`
(`Rd.BoundedLipschitzDomain.normal_ae_eq_normalAt`, `Rd.LipschitzGraph.norm_normalAt`). -/
theorem norm_normal_ae : ∀ᵐ y ∂Ω.surfaceMeasure, ‖Ω.normal y‖ = 1 := by
  filter_upwards [ae_all_iff.2 Ω.normal_ae_eq_normalAt, Ω.ae_mem_frontier] with y hy hΓ
  obtain ⟨j, hj⟩ := mem_iUnion.1 (Ω.frontier_subset hΓ)
  rw [hy j hj, (Ω.graph j).norm_normalAt]

/-- **The unit normal points out of `Ω`**: for every chart `j`, `σ`-almost every `y ∈ B_j` and
every `w` in the cone `K_j` of `Ω_j`, `⟪ν(y), w⟫ < 0`
(`Rd.LipschitzGraph.inner_normalAt_neg_of_mem_cone`). -/
theorem inner_normal_neg_ae (j : Fin Ω.N) :
    ∀ᵐ y ∂Ω.surfaceMeasure, y ∈ ball (Ω.center j) (Ω.radius j) →
      ∀ w ∈ (Ω.graph j).cone, inner ℝ (Ω.normal y) w < 0 := by
  filter_upwards [Ω.normal_ae_eq_normalAt j] with y hy hj w hw
  rw [hy hj]
  exact (Ω.graph j).inner_normalAt_neg_of_mem_cone _ hw

/-! ### Green's formula with the surface measure -/

/-- **The trace in `L_2(Γ)` in a chart**: for `U ∈ H^1(V)`, `(γ_{L_2} U)(γ_j x') = Tr_j U(x')` for
almost every `x' ∈ H_j` with `γ_j(x') ∈ B_j` (`Rd.BoundedLipschitzDomain.ambientTraceL2_apply_ae`,
`Rd.BoundedLipschitzDomain.boundaryTrace_graphMap`). -/
theorem ambientTraceL2_graphMap_ae (j : Fin Ω.N) (U : H^{1}(V)) :
    ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
      (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j) →
        Ω.ambientTraceL2 U ((Ω.graph j).graphMap x') = (Ω.graph j).traceH1 U x' := by
  filter_upwards [Ω.ae_graphMap_of_ae_surfaceMeasure j
    (Ω.ambientTraceL2_apply_ae Ω.boundaryPartition U),
    Ω.boundaryTrace_graphMap Ω.boundaryPartition two_ne_top one_le_two (s := 1 / 2) (by norm_num)
      (by norm_num) one_le_two (modNorm_toL2_lt_top U) j] with x' h1 h2 hj
  rw [h1 hj, h2 hj, (Ω.graph j).traceH1_apply]

/-- **The unit normal in a chart**: `ν(γ_j x') = ν_j(x')` for almost every `x' ∈ H_j` with
`γ_j(x') ∈ B_j` (`Rd.BoundedLipschitzDomain.normal_ae_eq_normalAt`). -/
theorem normal_graphMap_ae (j : Fin Ω.N) :
    ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
      (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j) →
        Ω.normal ((Ω.graph j).graphMap x') = (Ω.graph j).normalAt x' := by
  filter_upwards [(Ω.ae_surfaceMeasure_ball_iff j).1 (Ω.normal_ae_eq_normalAt j)] with x' hx' hj
  rw [hx' hj, LipschitzGraph.proj_graphMap]

/-- The boundary integrand `γ_{L_2} U · γ_{L_2} W ⟪v, ν⟫` of Green's formula is integrable with
respect to the surface measure: a product of two `L_2(Γ)` functions and a bounded one. -/
theorem integrable_ambientTraceL2_mul_inner_normal (U W : H^{1}(V)) (v : V) :
    Integrable (fun y => Ω.ambientTraceL2 U y * Ω.ambientTraceL2 W y *
      (inner ℝ v (Ω.normal y) : ℂ)) Ω.surfaceMeasure :=
  ((Lp.memLp _).integrable_mul (Lp.memLp _)).mul_bdd
    (Complex.measurable_ofReal.comp
      (measurable_const.inner Ω.measurable_normal)).aestronglyMeasurable
    (ae_of_all _ fun y => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (Ω.norm_normal_le y)))

/-- **The boundary integral of Green's formula in the charts**: for every resolution of unity `ψ`,
`U, W ∈ H^1(V)` and every direction `v`,
`∫_Γ γ_{L_2} U · γ_{L_2} W ⟪v, ν⟫ dσ = ∑_j ∫_{H_j} ψ_j(γ_j x') Tr_j U Tr_j W n^j_v dx'`, by the
surface measure in the charts (`Rd.BoundedLipschitzDomain.integral_surfaceMeasure`), the traces and
the normal in the charts, and `⟪v, ν_j⟫ √(1 + ‖∇φ_j‖²) = n^j_v`
(`Rd.LipschitzGraph.inner_normalAt_mul_gram`). -/
theorem integral_ambientTraceL2_mul_inner_normal_eq (ψ : Ω.BoundaryPartition) (U W : H^{1}(V))
    (v : V) :
    ∫ y, Ω.ambientTraceL2 U y * Ω.ambientTraceL2 W y * (inner ℝ v (Ω.normal y) : ℂ)
      ∂Ω.surfaceMeasure =
      ∑ j, ∫ x', ψ.toComplex j ((Ω.graph j).graphMap x') * (Ω.graph j).traceH1 U x' *
        (Ω.graph j).traceH1 W x' * ((Ω.graph j).normalWeight v x' : ℂ) := by
  rw [Ω.integral_surfaceMeasure ψ (Ω.integrable_ambientTraceL2_mul_inner_normal U W v)]
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
  filter_upwards [Ω.ambientTraceL2_graphMap_ae j U, Ω.ambientTraceL2_graphMap_ae j W,
    Ω.normal_graphMap_ae j] with x' h1 h2 h3
  by_cases hψ : ψ.toFun j ((Ω.graph j).graphMap x') = 0
  · simp only [ψ.toComplex_of_eq_zero hψ, zero_mul]
  · have hj := ψ.mem_ball_of_ne_zero hψ
    rw [h1 hj, h2 hj, h3 hj, ← (Ω.graph j).inner_normalAt_mul_gram, Complex.ofReal_mul]
    ring

/-- **Green's formula on a bounded Lipschitz domain** (Grisvard, Theorem 1.5.3.1): for all
`U, W ∈ H^1(V)` and every direction `v`,
`∫_Ω (∂_v U) W + U ∂_v W = ∫_Γ γ U · γ W ⟪v, ν⟫ dσ` with the traces `γ U, γ W ∈ L_2(Γ)`
(`Rd.BoundedLipschitzDomain.ambientTraceL2`), the outward unit normal `ν` and the surface measure
`σ`. The chart form for a resolution of unity equal to one near `Γ`
(`Rd.BoundedLipschitzDomain.setIntegral_green_of_nhds`) is the boundary integral in the charts
(`Rd.BoundedLipschitzDomain.integral_ambientTraceL2_mul_inner_normal_eq`). -/
theorem setIntegral_green_surface (U W : H^{1}(V)) (v : V) :
    ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
      ∫ y, Ω.ambientTraceL2 U y * Ω.ambientTraceL2 W y * (inner ℝ v (Ω.normal y) : ℂ)
        ∂Ω.surfaceMeasure := by
  obtain ⟨ψ, -, -, hψ⟩ := Ω.exists_boundaryPartition_nhds
  rw [setIntegral_green_of_nhds ψ hψ, Ω.integral_ambientTraceL2_mul_inner_normal_eq ψ]

/-- **Green's formula on `H^1(Ω)`**: for all `u, w ∈ H^1(Ω)` and every direction `v`,
`∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ u · γ w ⟪v, ν⟫ dσ` with the trace
`γ = Rd.BoundedLipschitzDomain.boundaryTraceL2 : H^1(Ω) → L_2(Γ)`; the left side uses the
representatives of `u, w` in `H^1(V)` (`Rd.BoundedLipschitzDomain.setIntegral_green_surface`,
`Rd.BoundedLipschitzDomain.boundaryTraceL2_eq_ambientTraceL2`). -/
theorem setIntegral_green_sobolevOne (u w : Ω.SobolevOne) (v : V) :
    ∫ x in Ω.carrier, weakDerivL2 v (u : H^{1}(V)) x * toL2 (w : H^{1}(V)) x +
        toL2 (u : H^{1}(V)) x * weakDerivL2 v (w : H^{1}(V)) x =
      ∫ y, Ω.boundaryTraceL2 u y * Ω.boundaryTraceL2 w y * (inner ℝ v (Ω.normal y) : ℂ)
        ∂Ω.surfaceMeasure := by
  rw [Ω.boundaryTraceL2_eq_ambientTraceL2, Ω.boundaryTraceL2_eq_ambientTraceL2]
  exact Ω.setIntegral_green_surface _ _ v

/-- **Green's formula on `H^1(Ω)` with weak derivatives on `Ω`**: for all `u, w ∈ H^1(Ω)`, every
direction `v` and weak derivatives `u_v = ∂_v u`, `w_v = ∂_v w` on `Ω`,
`∫_Ω u_v w + u w_v = ∫_Γ γ u · γ w ⟪v, ν⟫ dσ` with the trace `γ : H^1(Ω) → L_2(Γ)`. On `Ω`, `u_v`
and `w_v` agree almost everywhere with the weak derivatives on `V` of the representatives in
`H^1(V)` (`Rd.HasWeakLineDeriv.mono`, `Rd.HasWeakLineDeriv.unique`), so this is
`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne`. -/
theorem setIntegral_green_sobolevOne_of_hasWeakLineDeriv (u w : Ω.SobolevOne) (v : V)
    {uv wv : V → ℂ}
    (huv : HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => v) (toL2 (u : H^{1}(V))) uv)
    (hwv : HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => v) (toL2 (w : H^{1}(V))) wv) :
    ∫ x in Ω.carrier, uv x * toL2 (w : H^{1}(V)) x + toL2 (u : H^{1}(V)) x * wv x =
      ∫ y, Ω.boundaryTraceL2 u y * Ω.boundaryTraceL2 w y * (inner ℝ v (Ω.normal y) : ℂ)
        ∂Ω.surfaceMeasure := by
  rw [← Ω.setIntegral_green_sobolevOne u w v]
  have h1 := ((hasWeakLineDeriv_weakDerivL2 v (u : H^{1}(V))).mono le_top).unique huv
  have h2 := ((hasWeakLineDeriv_weakDerivL2 v (w : H^{1}(V))).mono le_top).unique hwv
  rw [Ω.coe_toOpens] at h1 h2
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

/-- **Green's formula in chart form**: for every resolution of unity `ψ` on the boundary, all
`U, W ∈ H^1(V)` and every direction `v`,
`∫_Ω (∂_v U) W + U ∂_v W = ∑_j ∫_{H_j} ψ_j(γ_j x') Tr_j U Tr_j W n^j_v dx'` with the traces `Tr_j`
of the graph domains and the normal weights `n^j_v = ⟪∇φ_j, v⟫ - ⟪v, e_j⟫`
(`Rd.BoundedLipschitzDomain.setIntegral_green_surface`,
`Rd.BoundedLipschitzDomain.integral_ambientTraceL2_mul_inner_normal_eq`). -/
theorem setIntegral_green_besselPotentialSpace (ψ : Ω.BoundaryPartition) (U W : H^{1}(V))
    (v : V) :
    ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
      ∑ j, ∫ x', ψ.toComplex j ((Ω.graph j).graphMap x') * (Ω.graph j).traceH1 U x' *
        (Ω.graph j).traceH1 W x' * ((Ω.graph j).normalWeight v x' : ℂ) := by
  rw [Ω.setIntegral_green_surface, Ω.integral_ambientTraceL2_mul_inner_normal_eq ψ]

/-- **Green's formula on a bounded Lipschitz domain, for `W^1_2(V)` functions**: for every
resolution of unity `ψ`, all `f, g ∈ L_2(V)` with `f, g ∈ W^1_2(V)`, every direction `v` and the
weak derivatives `f_v = ∂_v f`, `g_v = ∂_v g` in `L_2(V)`,
`∫_Ω f_v g + f g_v = ∑_j ∫_{H_j} ψ_j(γ_j x') Tr_j f Tr_j g n^j_v dx'`
(`Rd.BoundedLipschitzDomain.setIntegral_green_besselPotentialSpace`). -/
theorem setIntegral_green (ψ : Ω.BoundaryPartition) (f g : Lp ℂ 2 (volume : Measure V))
    (hf : MemSobolev 1 f) (hg : MemSobolev 1 g) (v : V) {fv gv : Lp ℂ 2 (volume : Measure V)}
    (hfv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) f fv)
    (hgv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) g gv) :
    ∫ x in Ω.carrier, fv x * g x + f x * gv x =
      ∑ j, ∫ x', ψ.toComplex j ((Ω.graph j).graphMap x') *
        (Ω.graph j).trace two_ne_top 2 f x' * (Ω.graph j).trace two_ne_top 2 g x' *
          ((Ω.graph j).normalWeight v x' : ℂ) := by
  obtain ⟨U, rfl⟩ := exists_toL2_eq_of_memSobolev hf
  obtain ⟨W, rfl⟩ := exists_toL2_eq_of_memSobolev hg
  rw [← weakDerivL2_eq hfv, ← weakDerivL2_eq hgv]
  exact Ω.setIntegral_green_besselPotentialSpace ψ U W v

/-! ### The zero extension of functions with vanishing trace -/

/-- **Functions with vanishing trace have no boundary term**: for `u` in the trace kernel,
`W ∈ H^1(V)` and every direction `v`, `∫_Ω (∂_v u) W + u ∂_v W = 0`
(`Rd.BoundedLipschitzDomain.setIntegral_green_surface`, `γ_{L_2} u = 0` by
`Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`). -/
theorem setIntegral_green_of_mem_traceKer {u : Ω.SobolevOne} (hu : u ∈ Ω.traceKer)
    (W : H^{1}(V)) (v : V) :
    ∫ x in Ω.carrier, weakDerivL2 v (u : H^{1}(V)) x * toL2 W x +
      toL2 (u : H^{1}(V)) x * weakDerivL2 v W x = 0 := by
  have h0 : Ω.ambientTraceL2 (u : H^{1}(V)) = 0 := by
    have hk : u ∈ (Ω.boundaryTraceL2).ker := by
      rw [Ω.ker_boundaryTraceL2]
      exact hu
    rw [← Ω.boundaryTraceL2_eq_ambientTraceL2]
    exact LinearMap.mem_ker.1 hk
  rw [Ω.setIntegral_green_surface, h0]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := Ω.surfaceMeasure)] with y hy
  rw [hy]
  simp

/-- **The weak derivatives of the zero extension**: for `u` in the trace kernel and every
direction `v`, the zero extension `1_Ω ∂_v u` of the weak derivative is the weak derivative of the
zero extension `1_Ω u` on `V`. Tested against `φ`, this is
`∫_Ω (∂_v u) φ = -∫_Ω u ∂_v φ`, Green's formula without boundary term
(`Rd.BoundedLipschitzDomain.setIntegral_green_of_mem_traceKer`). -/
theorem hasWeakLineDeriv_indicatorLp_of_mem_traceKer {u : Ω.SobolevOne} (hu : u ∈ Ω.traceKer)
    (v : V) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (indicatorLp Ω.measurableSet (toL2 (u : H^{1}(V))))
      (indicatorLp Ω.measurableSet (weakDerivL2 v (u : H^{1}(V)))) := by
  refine (hasWeakLineDeriv_iff_integral (locallyIntegrableOn_top_Lp _)
    (locallyIntegrableOn_top_Lp _)).2 fun φ => ?_
  obtain ⟨W, hWdef⟩ : ∃ W : H^{1}(V), W = ofSchwartz 1 (testSchwartz φ) := ⟨_, rfl⟩
  have hW : (toL2 W : V → ℂ) =ᵐ[volume] fun x => (φ x : ℂ) := by
    rw [hWdef, toL2_ofSchwartz]
    filter_upwards [(testSchwartz φ).coeFn_toLp 2 volume] with x hx
    rw [hx, testSchwartz_apply]
  have hdW : (weakDerivL2 v W : V → ℂ) =ᵐ[volume] fun x => ((∂_{v} φ) x : ℂ) := by
    rw [hWdef, weakDerivL2_ofSchwartz, lineDerivOp_testSchwartz]
    filter_upwards [(testSchwartz (∂_{v} φ)).coeFn_toLp 2 volume] with x hx
    rw [hx, testSchwartz_apply]
  have h0 := Ω.setIntegral_green_of_mem_traceKer hu W v
  have i1 : Integrable (fun x => weakDerivL2 v (u : H^{1}(V)) x * toL2 W x)
      (volume.restrict Ω.carrier) := ((Lp.memLp _).integrable_mul (Lp.memLp _)).restrict
  have i2 : Integrable (fun x => toL2 (u : H^{1}(V)) x * weakDerivL2 v W x)
      (volume.restrict Ω.carrier) := ((Lp.memLp _).integrable_mul (Lp.memLp _)).restrict
  rw [integral_add i1 i2, add_eq_zero_iff_eq_neg] at h0
  have e1 := integral_smul_indicatorLp_eq_setIntegral_mul Ω.measurableSet
    (weakDerivL2 v (u : H^{1}(V))) hW
  have e2 := integral_smul_indicatorLp_eq_setIntegral_mul Ω.measurableSet
    (toL2 (u : H^{1}(V))) hdW
  simp only [LineDeriv.iteratedLineDerivOp_one]
  rw [e1, e2, h0, pow_one, neg_one_smul]

/-- **The zero extension of a function with vanishing trace lies in `W^1_2(V)`**: for `u` in the
trace kernel, `1_Ω u ∈ W^1_2(V)`, with the weak derivatives `1_Ω ∂_v u`
(`Rd.BoundedLipschitzDomain.hasWeakLineDeriv_indicatorLp_of_mem_traceKer`,
`Rd.memSobolev_one_of_forall_hasWeakLineDeriv`). -/
theorem memSobolev_indicatorLp_of_mem_traceKer {u : Ω.SobolevOne} (hu : u ∈ Ω.traceKer) :
    MemSobolev 1 (indicatorLp Ω.measurableSet (toL2 (u : H^{1}(V)))) :=
  memSobolev_one_of_forall_hasWeakLineDeriv fun v =>
    ⟨_, Ω.hasWeakLineDeriv_indicatorLp_of_mem_traceKer hu v⟩

/-- **A function whose zero extension lies in `W^1_2(V)` has vanishing trace**: if
`1_Ω u ∈ W^1_2(V)` for `u ∈ H^1(Ω)`, then `u` lies in the trace kernel. In the chart `j`, the
trace of `u` is the trace of `F = 1_Ω u` (they agree on `Ω_j ∩ B_j`,
`Rd.LipschitzGraph.trace_ae_eq_of_ae_eq`), and `F` vanishes on the part of the lower domain in
`B_j`, which lies outside `Ω`, so its trace vanishes
(`Rd.LipschitzGraph.traceH1_ae_eq_zero_of_lower`). -/
theorem mem_traceKer_of_memSobolev_indicatorLp {u : Ω.SobolevOne}
    (hu : MemSobolev 1 (indicatorLp Ω.measurableSet (toL2 (u : H^{1}(V))))) : u ∈ Ω.traceKer := by
  obtain ⟨F, hF⟩ := exists_toL2_eq_of_memSobolev hu
  have hFe : (toL2 F : V → ℂ) =ᵐ[volume] Ω.carrier.indicator (toL2 (u : H^{1}(V))) := by
    rw [hF]
    exact indicatorLp_apply_ae _ _
  rw [Ω.mem_traceKer_iff Ω.boundaryPartition, EventuallyEq, Ω.eventually_aeBoundary_iff]
  intro j
  have hB := Ω.inter_ball_eq j le_rfl
  have h1 := (Ω.graph j).trace_ae_eq_of_ae_eq two_ne_top 2 (s := 1 / 2) (by norm_num) one_le_two
    ((Ω.graph j).intrinsicNorm_toL2_lt_top (u : H^{1}(V)))
    ((Ω.graph j).intrinsicNorm_toL2_lt_top F) isOpen_ball (by
      filter_upwards [hFe] with x hx hxd hxB
      have hxΩ : x ∈ Ω.carrier := ((Set.ext_iff.1 hB x).2 ⟨hxd, hxB⟩).1
      rw [hx, indicator_of_mem hxΩ])
  have h2 := (Ω.graph j).traceH1_ae_eq_zero_of_lower (U := F) isOpen_ball (by
    filter_upwards [hFe] with x hx hxd hxB
    have hxΩ : x ∉ Ω.carrier := fun h => (Ω.graph j).notMem_domain_of_mem_lower_domain hxd
      ((Set.ext_iff.1 hB x).1 ⟨h, hxB⟩).1
    rw [hx, indicator_of_notMem hxΩ])
  filter_upwards [h1, h2, Ω.boundaryTrace_graphMap Ω.boundaryPartition two_ne_top one_le_two
    (s := 1 / 2) (by norm_num) (by norm_num) one_le_two (modNorm_toL2_lt_top (u : H^{1}(V))) j]
    with x' a b c hj
  rw [c hj, a hj, Pi.zero_apply]
  exact b hj

/-- **Zero extension and vanishing trace**: for `u ∈ H^1(Ω)`, the zero extension `1_Ω u` lies in
`W^1_2(V)` iff `u` lies in the trace kernel, that is, iff its trace vanishes almost everywhere on
`Γ`
(`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_of_mem_traceKer`,
`Rd.BoundedLipschitzDomain.mem_traceKer_of_memSobolev_indicatorLp`). -/
theorem memSobolev_indicatorLp_iff_mem_traceKer (u : Ω.SobolevOne) :
    MemSobolev 1 (indicatorLp Ω.measurableSet (toL2 (u : H^{1}(V)))) ↔ u ∈ Ω.traceKer :=
  ⟨Ω.mem_traceKer_of_memSobolev_indicatorLp, Ω.memSobolev_indicatorLp_of_mem_traceKer⟩

end BoundedLipschitzDomain

end Rd
