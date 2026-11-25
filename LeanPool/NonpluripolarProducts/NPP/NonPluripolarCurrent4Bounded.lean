/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrent4CLN
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarClosedLocal
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrent2Multilinear
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentPlurifine

/-!
# Non-pluripolar products with bounded factors

Source: `chapter_npp.tex`, `prop:npp1` (3), second sentence ("if `q ≤ p`, and we only assume that
`φ₁, …, φ_q ∈ L^∞_loc(X)`, and that the non-pluripolar product `T := dd^c φ_{q+1} ∧ ⋯ ∧ dd^c φ_p`
is well-defined, then the non-pluripolar product `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p` is also well-defined,
and is equal to the Bedford–Taylor product `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_q ∧ T` as in
`rmk:extensionBT`"); Xia, *Foundations of pluripotential theory*,
`prop:nonpluripolar-bounded-factor-compatibility`.

On an open `U ⊆ ℂⁿ`:

* `tendsto_mulBorel_apply_of_tendsto` — `u_k T → u T` for bounded weights `u_k → u` on `U`;
* `mulBorel_ddcMul_eq_of_smooth`, `mulBorel_ddcMul_eq_of_mulBorel_eq` — **if `w S = w Θ` for a
  bounded psh weight `w ≥ 0`, then `w dd^c v ∧ S = w dd^c v ∧ Θ`** for every locally bounded psh
  `v` (smooth `v` by commutation with smooth forms, general `v` by the weighted decreasing
  continuity of Bedford–Taylor products with an arbitrary closed positive base);
* `mulBorel_ddcMul_indicator_eq_of_cutoffs` — the same for the indicators `1_{O_m}` of sets
  admitting psh cutoffs (FPT's functions `w_k`);
* **`nonPluripolarProduct_cons_bounded`** — FPT `prop:nonpluripolar-bounded-factor-compatibility`
  for one bounded factor: `⟨dd^c v ∧ dd^c φ₁ ∧ ⋯⟩` is well defined and equals the relative
  Bedford–Taylor product `dd^c v ∧ ⟨dd^c φ₁ ∧ ⋯⟩`;
* **`nonPluripolarProduct_append_bounded`** — `prop:npp1` (3), second sentence, locally: for
  locally bounded psh `v₁, …, v_q` and psh `φ_{q+1}, …, φ_p` with `T = ⟨⋀ dd^c φⱼ⟩` well
  defined, `⟨dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ dd^c φ_{q+1} ∧ ⋯⟩` is well defined and equals the relative
  Bedford–Taylor product `btProduct q r v T = dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ T`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity

variable {n : ℕ}

variable {U : Opens (ComplexModel n)}

/-! ### Convergence in the weight -/

/-- **Dominated convergence in the weight**: `u_k T → u T` (on every `(γ, φ)`) for measurable
weights bounded by `1` converging pointwise on `U`. -/
theorem tendsto_mulBorel_apply_of_tendsto {q : ℕ} {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {u : ℕ → (ComplexModel n) → ℝ} {u₀ : (ComplexModel n) → ℝ} (hum : ∀ k,
      Measurable (u k))
    (hu₀m : Measurable u₀) (hb : ∀ k x, |u k x| ≤ 1) (hb₀ : ∀ x, |u₀ x| ≤ 1)
    (hlim : ∀ x ∈ (U : Set (ComplexModel n)), Tendsto (fun k => u k x) atTop (𝓝 (u₀ x)))
      (γ : formSpan n q)
    (φ : 𝓓(U, ℝ)) : Tendsto (fun k => mulBorel T (u k) γ φ) atTop (𝓝 (mulBorel T u₀ γ φ)) := by
  apply tendsto_mulBorel_apply_of_ae_tendsto hT hum hu₀m hb hb₀ _ γ φ
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hT.traceMeasure_compl] with x hx
  exact hlim x (by simpa using hx)

/-! ### Transfer of weighted identities through `dd^c v ∧ ·` -/

variable {m : ℕ}

/-- **Smooth potentials**: if `w S = w Θ`, then `w dd^c g ∧ S = w dd^c g ∧ Θ` for `g` smooth on
`U` with semipositive Levi form (`dd^c g ∧ ·` is the wedge with a smooth form, which commutes
with multiplication by Borel weights). -/
theorem mulBorel_ddcMul_eq_of_smooth {S Θ : LocalProductCurrent n U (m + 1)} (hS : IsPositive S)
    (hSc : IsClosedCurrent S) (hΘ : IsPositive Θ) (hΘc : IsClosedCurrent Θ) {w : (ComplexModel n)
      → ℝ}
    (hwm : Measurable w) (hwb : IsLocallyBoundedOn w U) (hSΘ : mulBorel S w = mulBorel Θ w)
    {g : (ComplexModel n) → ℝ} (hg : ContDiffOn ℝ ∞ g U) (hgl : ∀ x ∈ U, ∀ v, 0 ≤ leviForm g x v) :
    mulBorel (ddcMul S g) w = mulBorel (ddcMul Θ g) w := by
  rw [ddcMul_eq_ddcWedge hS hSc hg, ddcMul_eq_ddcWedge hΘ hΘc hg, ddcWedge_eq_wedgeForm,
    ddcWedge_eq_wedgeForm, mulBorel_wedgeForm rfl hS _ (ddcForm_mem_spCone hg hgl) hwm hwb,
    mulBorel_wedgeForm rfl hΘ _ (ddcForm_mem_spCone hg hgl) hwm hwb, hSΘ]

/-- **Bounded potentials** (FPT, proof of `prop:nonpluripolar-bounded-factor-compatibility`, the
weighted form of `thm:bt-decreasing-continuity` with the constant weights `w`): if `w S = w Θ`
for a nonnegative locally bounded psh `w` (extended by `0` off `U`), then
`w dd^c v ∧ S = w dd^c v ∧ Θ` for every locally bounded psh `v`. -/
theorem mulBorel_ddcMul_eq_of_mulBorel_eq {S Θ : LocalProductCurrent n U (m + 1)}
    (hS : IsPositive S) (hSc : IsClosedCurrent S) (hΘ : IsPositive Θ) (hΘc : IsClosedCurrent Θ)
    {w : (ComplexModel n) → ℝ} (hw : IsLocallyBoundedPshOn U w)
    (hSΘ : mulBorel S ((U : Set (ComplexModel n)).indicator w) = mulBorel Θ ((U : Set
      (ComplexModel n)).indicator w))
    {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U v) :
    mulBorel (ddcMul S v) ((U : Set (ComplexModel n)).indicator w) =
      mulBorel (ddcMul Θ v) ((U : Set (ComplexModel n)).indicator w) := by
  have hWm := measurable_indicator_of_isLocallyBoundedPshOn hw
  have hWb := isLocallyBoundedOn_indicator hw
  apply LocalBedfordTaylorCalculus.eq_of_local
  intro x hx
  obtain ⟨A, hxA, hArc⟩ := BedfordTaylor.exists_relativelyCompact_ball (Ω := U) hx
  have hAU : A ≤ U := subset_closure.trans hArc.2
  refine ⟨A, hAU, hxA, ?_⟩
  have hSA := isPositive_restrict hS hAU
  have hΘA := isPositive_restrict hΘ hAU
  have hSAc := isClosedCurrent_restrict hSc hAU
  have hΘAc := isClosedCurrent_restrict hΘc hAU
  have hwA := isLocallyBoundedPshOn_mono hw hAU
  have hvA := isLocallyBoundedPshOn_mono hv hAU
  have hWAm := measurable_indicator_of_isLocallyBoundedPshOn hwA
  have hWAb := isLocallyBoundedOn_indicator hwA
  have hcongr : ∀ x ∈ A, (A : Set (ComplexModel n)).indicator w x = (U : Set (ComplexModel
    n)).indicator w x := fun x hx => by
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hAU hx)]
  -- reduce to `A`
  have hred : ∀ {T : LocalProductCurrent n U (m + 1)} (hT : IsPositive T) (hTc : IsClosedCurrent
    T),
      restrict hAU (mulBorel (ddcMul T v) ((U : Set (ComplexModel n)).indicator w)) =
        mulBorel (ddcMul (restrict hAU T) v) ((A : Set (ComplexModel n)).indicator w) := by
    intro T hT hTc
    rw [← mulBorel_restrict (isPositive_ddcMul hT hTc hv).1 hAU hWm hWb,
      ← ddcMul_restrict hT hAU hv]
    exact mulBorel_congr (isPositive_ddcMul (isPositive_restrict hT hAU)
      (isClosedCurrent_restrict hTc hAU) hvA).1 hWm (isLocallyBoundedOn_mono hWb hAU) hWAm hWAb
      fun x hx => (hcongr x hx).symm
  rw [hred hS hSc, hred hΘ hΘc]
  -- the identity of the weighted currents on `A`
  have hSΘA : mulBorel (restrict hAU S) ((A : Set (ComplexModel n)).indicator w) =
      mulBorel (restrict hAU Θ) ((A : Set (ComplexModel n)).indicator w) := by
    have h1 := congrArg (restrict hAU) hSΘ
    rw [← mulBorel_restrict hS hAU hWm hWb, ← mulBorel_restrict hΘ hAU hWm hWb] at h1
    rw [mulBorel_congr hSA hWAm hWAb hWm (isLocallyBoundedOn_mono hWb hAU) hcongr,
      mulBorel_congr hΘA hWAm hWAb hWm (isLocallyBoundedOn_mono hWb hAU) hcongr]
    exact h1
  -- smooth decreasing approximations of `v` on a relatively compact ball
  obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hv hArc
  have hfA : ∀ l, IsLocallyBoundedPshOn A (f l) := fun l =>
    isLocallyBoundedPshOn_of_isSmoothPshOn (hf.1 l)
  have hfl : ∀ l, ∀ x ∈ A, ∀ y, 0 ≤ leviForm (f l) x y := fun l x hx y =>
    leviForm_nonneg_of_posSemidef (((hf.1 l).1.contDiffAt (A.isOpen.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ((hf.1 l).2.2 x hx) y
  set u : ℕ → Fin 2 → (ComplexModel n) → ℝ := fun l => ![w, f l] with hu_def
  set u₀ : Fin 2 → (ComplexModel n) → ℝ := ![w, v] with hu₀_def
  have hu : ∀ l i, IsLocallyBoundedPshOn A (u l i) := fun l i => by
    fin_cases i
    · exact hwA
    · exact hfA l
  have hu₀ : ∀ i, IsLocallyBoundedPshOn A (u₀ i) := fun i => by
    fin_cases i
    · exact hwA
    · exact hvA
  have hanti : ∀ i, ∀ z ∈ (A : Set (ComplexModel n)), Antitone fun l => u l i z := fun i z hz => by
    fin_cases i
    · exact fun _ _ _ => le_rfl
    · exact hf.2.1 z hz
  have hlim : ∀ i, ∀ z ∈ (A : Set (ComplexModel n)), Tendsto (fun l => u l i z) atTop (𝓝 (u₀ i z))
    :=
    fun i z hz => by
      fin_cases i
      · exact tendsto_const_nhds
      · exact hf.2.2 z hz
  have hS' := weakTendsto_mulBorel_btProduct_of_antitone 1 m _ hSA hSAc u u₀ hu hu₀ hanti hlim
  have hΘ' := weakTendsto_mulBorel_btProduct_of_antitone 1 m _ hΘA hΘAc u u₀ hu hu₀ hanti hlim
  have hterm : ∀ l, mulBorel (ddcMul (restrict hAU S) (f l)) ((A : Set (ComplexModel n)).indicator
    w) =
      mulBorel (ddcMul (restrict hAU Θ) (f l)) ((A : Set (ComplexModel n)).indicator w) := fun l =>
    mulBorel_ddcMul_eq_of_smooth hSA hSAc hΘA hΘAc hWAm hWAb hSΘA (hf.1 l).1 (hfl l)
  ext γ φ
  refine tendsto_nhds_unique (hS' γ φ) ?_
  have e : (fun l => mulBorel (btProduct 1 m (Fin.tail (u l)) (restrict hAU S))
      ((A : Set (ComplexModel n)).indicator (u l 0)) γ φ) =
      fun l => mulBorel (btProduct 1 m (Fin.tail (u l)) (restrict hAU Θ))
        ((A : Set (ComplexModel n)).indicator (u l 0)) γ φ := by
    funext l
    exact congrArg (fun T : LocalProductCurrent n A m => T γ φ) (hterm l)
  rw [e]
  exact hΘ' γ φ

/-- **Transfer through psh cutoffs** (FPT, proof of
`prop:nonpluripolar-bounded-factor-compatibility`): let `1_{O_k} S = 1_{O_k} Θ_k` for closed
positive `S, Θ_k`, and let `w_k` be locally bounded psh cutoffs on `U` (`0 ≤ w_k ≤ 1`, `w_k = 0`
off `O_k`, `w_k → 1` on `⋃ O_k`).  If `1_{O_{m₀}} dd^c v ∧ Θ_k = 1_{O_{m₀}} dd^c v ∧ Θ_{m₀}` for
`k ≥ m₀`, then `1_{O_{m₀}} dd^c v ∧ S = 1_{O_{m₀}} dd^c v ∧ Θ_{m₀}`. -/
theorem mulBorel_ddcMul_indicator_eq_of_cutoffs {S : LocalProductCurrent n U (m + 1)}
    (hS : IsPositive S) (hSc : IsClosedCurrent S) {Θ : ℕ → LocalProductCurrent n U (m + 1)}
    (hΘ : ∀ k, IsPositive (Θ k)) (hΘc : ∀ k, IsClosedCurrent (Θ k)) {O : ℕ → Set (ComplexModel n)}
    (hOm : ∀ k, MeasurableSet (O k))
    (hSΘ : ∀ k, mulBorel S ((O k).indicator fun _ => (1 : ℝ)) =
      mulBorel (Θ k) ((O k).indicator fun _ => (1 : ℝ)))
    {w : ℕ → (ComplexModel n) → ℝ} (hw : ∀ k, IsLocallyBoundedPshOn U (w k))
    (hw01 : ∀ k, ∀ x ∈ (U : Set (ComplexModel n)), 0 ≤ w k x ∧ w k x ≤ 1)
    (hwO : ∀ k, ∀ x ∈ (U : Set (ComplexModel n)), x ∉ O k → w k x = 0)
    (hwlim : ∀ x ∈ (U : Set (ComplexModel n)), (∃ k, x ∈ O k) → Tendsto (fun k => w k x)
      atTop (𝓝 1))
    {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U v) {m₀ : ℕ}
    (hcons : ∀ k, m₀ ≤ k → mulBorel (ddcMul (Θ k) v) ((O m₀).indicator fun _ => (1 : ℝ)) =
      mulBorel (ddcMul (Θ m₀) v) ((O m₀).indicator fun _ => (1 : ℝ))) :
    mulBorel (ddcMul S v) ((O m₀).indicator fun _ => (1 : ℝ)) =
      mulBorel (ddcMul (Θ m₀) v) ((O m₀).indicator fun _ => (1 : ℝ)) := by
  set W : ℕ → (ComplexModel n) → ℝ := fun k => (U : Set (ComplexModel n)).indicator (w k)
    with hW_def
  have hWm : ∀ k, Measurable (W k) := fun k => measurable_indicator_of_isLocallyBoundedPshOn (hw k)
  have hWb : ∀ k, IsLocallyBoundedOn (W k) U := fun k => isLocallyBoundedOn_indicator (hw k)
  have hW0 : ∀ k x, 0 ≤ W k x := fun k x => by
    by_cases hx : x ∈ (U : Set (ComplexModel n))
    · simp only [hW_def, Set.indicator_of_mem hx]
      exact (hw01 k x hx).1
    · simp only [hW_def, Set.indicator_of_notMem hx, le_refl]
  have hW1 : ∀ k x, W k x ≤ 1 := fun k x => by
    by_cases hx : x ∈ (U : Set (ComplexModel n))
    · simp only [hW_def, Set.indicator_of_mem hx]
      exact (hw01 k x hx).2
    · simp only [hW_def, Set.indicator_of_notMem hx]
      exact zero_le_one
  set I : Set (ComplexModel n) → (ComplexModel n) → ℝ := fun A => A.indicator fun _ => (1 : ℝ)
    with hI_def
  have hIm : ∀ k, Measurable (I (O k)) := fun k => measurable_const.indicator (hOm k)
  have hIb : ∀ A, IsLocallyBoundedOn (I A) U := fun A => isLocallyBoundedOn_indicator_one A
  have hI0 : ∀ A x, 0 ≤ I A x := fun A x => by
    by_cases hx : x ∈ A <;> simp [hI_def, hx]
  have hR := fun {T : LocalProductCurrent n U (m + 1)} (hT : IsPositive T)
    (hTc : IsClosedCurrent T) => (isPositive_ddcMul hT hTc hv).1
  -- (a) `w_k S = w_k Θ_k`
  have hSΘW : ∀ k, mulBorel S (W k) = mulBorel (Θ k) (W k) := by
    intro k
    have e : W k = fun x => I (O k) x * W k x := by
      funext x
      by_cases hxO : x ∈ O k
      · simp [hI_def, hxO]
      · by_cases hxU : x ∈ (U : Set (ComplexModel n))
        · simp [hI_def, hxO, hW_def, Set.indicator_of_mem hxU, hwO k x hxU hxO]
        · simp [hI_def, hxO, hW_def, Set.indicator_of_notMem hxU]
    rw [e, ← mulBorel_mulBorel hS (hIm k) (hIb _) (hI0 _) (hWm k) (hWb k),
      ← mulBorel_mulBorel (hΘ k) (hIm k) (hIb _) (hI0 _) (hWm k) (hWb k)]
    exact congrArg (fun T => mulBorel T (W k)) (hSΘ k)
  -- (b) `w_k dd^c v ∧ S = w_k dd^c v ∧ Θ_k`
  have hRW : ∀ k, mulBorel (ddcMul S v) (W k) = mulBorel (ddcMul (Θ k) v) (W k) := fun k =>
    mulBorel_ddcMul_eq_of_mulBorel_eq hS hSc (hΘ k) (hΘc k) (hw k) (hSΘW k) hv
  -- (c) `w_k 1_{O_{m₀}} dd^c v ∧ S = w_k 1_{O_{m₀}} dd^c v ∧ Θ_{m₀}` for `k ≥ m₀`
  have hc : ∀ k, m₀ ≤ k → mulBorel (ddcMul S v) (fun x => W k x * I (O m₀) x) =
      mulBorel (ddcMul (Θ m₀) v) (fun x => W k x * I (O m₀) x) := by
    intro k hk
    have e : (fun x => W k x * I (O m₀) x) = fun x => I (O m₀) x * W k x :=
      funext fun x => mul_comm _ _
    rw [← mulBorel_mulBorel (hR hS hSc) (hWm k) (hWb k) (hW0 k) (hIm m₀) (hIb _), hRW k,
      mulBorel_mulBorel (hR (hΘ k) (hΘc k)) (hWm k) (hWb k) (hW0 k) (hIm m₀) (hIb _), e,
      ← mulBorel_mulBorel (hR (hΘ k) (hΘc k)) (hIm m₀) (hIb _) (hI0 _) (hWm k) (hWb k),
      hcons k hk,
      mulBorel_mulBorel (hR (hΘ m₀) (hΘc m₀)) (hIm m₀) (hIb _) (hI0 _) (hWm k) (hWb k)]
  -- (d) the limit `k → ∞`
  have hmeas : ∀ k, Measurable fun x => W k x * I (O m₀) x := fun k => (hWm k).mul (hIm m₀)
  have hbd : ∀ k x, |W k x * I (O m₀) x| ≤ 1 := fun k x => by
    rw [abs_mul, abs_of_nonneg (hW0 k x), abs_of_nonneg (hI0 _ x)]
    have h1 : I (O m₀) x ≤ 1 := by by_cases hx : x ∈ O m₀ <;> simp [hI_def, hx]
    nlinarith [hW0 k x, hW1 k x, hI0 (O m₀) x]
  have hbd₀ : ∀ x, |I (O m₀) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ O m₀ <;> simp [hI_def, hx]
  have hlim : ∀ x ∈ (U : Set (ComplexModel n)), Tendsto (fun k => W k x * I (O m₀) x) atTop
      (𝓝 (I (O m₀) x)) := by
    intro x hx
    by_cases hxO : x ∈ O m₀
    · have h := hwlim x hx ⟨m₀, hxO⟩
      simp only [hI_def, Set.indicator_of_mem hxO, mul_one, hW_def, Set.indicator_of_mem hx]
      exact h
    · simp only [hI_def, Set.indicator_of_notMem hxO, mul_zero]
      exact tendsto_const_nhds
  ext γ φ
  have h1 := tendsto_mulBorel_apply_of_tendsto (hR hS hSc) hmeas (hIm m₀) hbd hbd₀ hlim γ φ
  have h2 := tendsto_mulBorel_apply_of_tendsto (hR (hΘ m₀) (hΘc m₀)) hmeas (hIm m₀) hbd hbd₀
    hlim γ φ
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [eventually_ge_atTop m₀] with k hk
  exact (congrArg (fun T : LocalProductCurrent n U m => T γ φ) (hc k hk)).symm

/-! ### Helpers on truncations, base currents and null sets -/

theorem heq_oneCurrentOf {a b : ℕ} (ha : a = n) (hb : b = n) :
    HEq (oneCurrentOf (U := U) ha) (oneCurrentOf (U := U) hb) := by
  cases ha
  cases hb
  rfl

/-- `dd^c a ∧ dd^c u₁ ∧ ⋯ ∧ dd^c u_p = dd^c (a dd^c u₁ ∧ ⋯ ∧ dd^c u_p)`, on `[U]`. -/
theorem btProduct_cons_eq_ddcMul {r p' : ℕ} (hqp : r + (p' + 1) = n) (hqp' : r + 1 + p' = n)
    (a : (ComplexModel n) → ℝ) (u : Fin p' → (ComplexModel n) → ℝ) :
    btProduct (p' + 1) r (Fin.cons a u) (oneCurrentOf (U := U) hqp) =
      ddcMul (btProduct p' (r + 1) u (oneCurrentOf (U := U) hqp')) a := by
  rw [btProduct_succ_eq_ddcMul p' r _ _ _ (heq_oneCurrentOf hqp hqp'), Fin.tail_cons,
    Fin.cons_zero]

theorem truncationReal_coe (v : (ComplexModel n) → ℝ) (k : ℕ) (z : (ComplexModel n)) :
    truncationReal (fun z => (v z : EReal)) k z = max (v z) (-(k : ℝ)) := by
  simp only [truncationReal, truncation]
  rcases le_total (v z) (-(k : ℝ)) with h | h
  · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h), max_eq_right h, EReal.toReal_coe]
  · rw [max_eq_left (EReal.coe_le_coe_iff.mpr h), max_eq_left h, EReal.toReal_coe]

theorem neg_lt_truncationReal_iff {u : (ComplexModel n) → EReal} (hu : PlurisubharmonicOn u U)
    (k : ℕ) {z : (ComplexModel n)}
    (hz : z ∈ (U : Set (ComplexModel n))) :
    -(k : ℝ) < truncationReal u k z ↔ ((-(k : ℝ) : ℝ) : EReal) < u z := by
  have h := congrArg (z ∈ ·) (strictLocus_eq_truncationReal_superlevel hu (le_refl k))
  simp only [strictTruncationLocus, mem_ofPred_eq, eq_iff_iff] at h
  exact ⟨fun h' => (h.mpr ⟨hz, h'⟩).2, fun h' => (h.mp ⟨hz, h'⟩).2⟩

theorem truncationReal_eq_of_lt {u : (ComplexModel n) → EReal} (hu : PlurisubharmonicOn u U)
    {k l : ℕ}
    (hkl : k ≤ l) {z : (ComplexModel n)} (hz : z ∈ (U : Set (ComplexModel n))) (h : ((-(k : ℝ)
      : ℝ) : EReal) < u z) :
    truncationReal u l z = truncationReal u k z := by
  rw [← truncationReal_nested hu hkl hz, max_eq_left]
  have hl : ((-(k : ℝ) : ℝ) : EReal) < truncation u l z := lt_of_lt_of_le h (le_max_left _ _)
  rw [← coe_truncationReal hu l hz] at hl
  exact (EReal.coe_lt_coe_iff.mp hl).le

/-- A positive current multiplied by the indicator of a null set of its trace measure is `0`. -/
theorem mulBorel_indicator_eq_zero_of_null {q : ℕ} {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {A : Set (ComplexModel n)} (hA : MeasurableSet A) (h0 : hT.traceMeasure A
      = 0) :
    mulBorel T (A.indicator fun _ => (1 : ℝ)) = 0 := by
  ext γ φ
  rw [mulBorel_apply hT (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one A)]
  simp only [LinearMap.zero_apply, _root_.zero_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
  rw [Set.indicator_of_notMem hx, zero_mul, mul_zero, Pi.zero_apply]

/-- The trace measure of a positive current vanishes on a set `A` if `1_A T = 0`. -/
theorem traceMeasure_eq_zero_of_mulBorel_indicator_eq_zero {q : ℕ}
    {T : LocalProductCurrent n U q} (hT : IsPositive T) {A : Set (ComplexModel n)} (hA :
      MeasurableSet A)
    (h0 : mulBorel T (A.indicator fun _ => (1 : ℝ)) = 0) : hT.traceMeasure A = 0 := by
  have hP := isPositive_mulBorel_indicator hT hA
  have hz : hP.traceMeasure = 0 :=
    eq_of_forall_testFunction_integral_eq (U := U) hP.traceMeasure_compl (by simp)
      (fun K hK hKU => hP.traceMeasure_lt_top hK hKU) (fun _ _ _ => by simp) fun φ => by
        rw [hP.integral_traceMeasure, h0]
        simp
  rw [traceMeasure_mulBorel_indicator hT hA] at hz
  exact Measure.restrict_eq_zero.mp hz

/-! ### One bounded factor -/

variable {r p' : ℕ}

/-- **FPT `prop:nonpluripolar-bounded-factor-compatibility`, one bounded factor**: for psh
`φ₁, …, φ_{p'}` on `U` with `S = ⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_{p'}⟩` well defined and a locally bounded
psh `v`, the non-pluripolar product `⟨dd^c v ∧ dd^c φ₁ ∧ ⋯ ∧ dd^c φ_{p'}⟩` is well defined and
equals the relative Bedford–Taylor product `dd^c v ∧ S = dd^c (v S)`. -/
theorem nonPluripolarProduct_cons_bounded (hqp' : r + 1 + p' = n) (hqp : r + (p' + 1) = n)
    {φ : Fin p' → (ComplexModel n) → EReal} (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp' U φ) {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U v) :
    IsWellDefinedOn hqp U (Fin.cons (fun z => (v z : EReal)) φ) ∧
      nonPluripolarProduct hqp U (Fin.cons (fun z => (v z : EReal)) φ) =
        ddcMul (nonPluripolarProduct hqp' U φ) v := by
  set S := nonPluripolarProduct hqp' U φ with hS_def
  have hS : IsPositive S := isPositive_nonPluripolarProduct hqp' hφ hW
  have hSc : IsClosedCurrent S := isClosedAny_nonPluripolarProduct hqp' hφ hW
  set Θ : ℕ → LocalProductCurrent n U (r + 1) := truncatedBT hqp' U φ with hΘ_def
  have hΘ : ∀ k, IsPositive (Θ k) := fun k => (isPositive_truncatedBT hqp' hφ k).1
  have hΘc : ∀ k, IsClosedCurrent (Θ k) := fun k => (isPositive_truncatedBT hqp' hφ k).2
  set O := BedfordTaylorTopDegree.strictLocus U φ with hO_def
  have hOm : ∀ k, MeasurableSet (O k) := BedfordTaylorTopDegree.measurableSet_strictLocus hφ
  set ψ : Fin (p' + 1) → (ComplexModel n) → EReal := Fin.cons (fun z => (v z : EReal))
    φ with hψ_def
  have hψ : ∀ i, PlurisubharmonicOn (ψ i) U := fun i => Fin.cases hv.1 hφ i
  set Oψ := BedfordTaylorTopDegree.strictLocus U ψ with hOψ_def
  have hOψm : ∀ k, MeasurableSet (Oψ k) := BedfordTaylorTopDegree.measurableSet_strictLocus hψ
  have hR := (isPositive_ddcMul hS hSc hv).1
  have hRk : ∀ k, IsPositive (ddcMul (Θ k) v) := fun k => (isPositive_ddcMul (hΘ k) (hΘc k) hv).1
  have hIm : ∀ A : Set (ComplexModel n), MeasurableSet A → Measurable (A.indicator fun _ => (1 :
    ℝ)) :=
    fun A hA => measurable_const.indicator hA
  -- `dd^c a ∧ Θ_k` as a Bedford–Taylor product of `p' + 1` bounded functions
  have hE : ∀ (a : (ComplexModel n) → ℝ) (k : ℕ), btProduct (p' + 1) r
      (Fin.cons a fun i => truncationReal (φ i) k) (oneCurrentOf (U := U) hqp) =
        ddcMul (Θ k) a := fun a k => btProduct_cons_eq_ddcMul hqp hqp' a _
  -- consistency of `dd^c v ∧ Θ_k` on the strict loci (plurifine locality)
  have hcons : ∀ m₀ k, m₀ ≤ k → mulBorel (ddcMul (Θ k) v) ((O m₀).indicator fun _ => (1 : ℝ)) =
      mulBorel (ddcMul (Θ m₀) v) ((O m₀).indicator fun _ => (1 : ℝ)) := by
    intro m₀ k hk
    rw [← hE v k, ← hE v m₀]
    refine mulBorel_btProduct_eq_of_eqOn_plurifineOpen hqp (fun i => ?_) (fun i => ?_)
      (fun z hz => hz.1) (hOm m₀) (isOpen_plurifine_strictLocus hφ m₀) fun i => ?_
    · exact Fin.cases hv (fun j => truncationReal_isLocallyBoundedPshOn (hφ j) k) i
    · exact Fin.cases hv (fun j => truncationReal_isLocallyBoundedPshOn (hφ j) m₀) i
    · refine Fin.cases (fun z _ => rfl) (fun j z hz => ?_) i
      simp only [Fin.cons_succ]
      exact truncationReal_eq_of_lt (hφ j) hk hz.1 (hz.2 j)
  -- `1_{O_m} dd^c v ∧ S = 1_{O_m} dd^c v ∧ Θ_m`, through the psh cutoffs of the strict loci
  have hL : ∀ m₀, mulBorel (ddcMul S v) ((O m₀).indicator fun _ => (1 : ℝ)) =
      mulBorel (ddcMul (Θ m₀) v) ((O m₀).indicator fun _ => (1 : ℝ)) := by
    intro m₀
    apply LocalBedfordTaylorCalculus.eq_of_local
    intro x hx
    obtain ⟨V, hVU, hxV, w, -, hwpsh, hw01, hwO, hwlim⟩ :=
      hasPshCutoffs_strictLocus hφ {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    refine ⟨V, hVU, hxV (mem_singleton x), ?_⟩
    rw [← mulBorel_restrict hR hVU (hIm _ (hOm m₀)) (isLocallyBoundedOn_indicator_one _),
      ← mulBorel_restrict (hRk m₀) hVU (hIm _ (hOm m₀)) (isLocallyBoundedOn_indicator_one _),
      ← ddcMul_restrict hS hVU hv, ← ddcMul_restrict (hΘ m₀) hVU hv]
    refine mulBorel_ddcMul_indicator_eq_of_cutoffs (isPositive_restrict hS hVU)
      (isClosedCurrent_restrict hSc hVU) (Θ := fun k => restrict hVU (Θ k))
      (fun k => isPositive_restrict (hΘ k) hVU) (fun k => isClosedCurrent_restrict (hΘc k) hVU)
      hOm (fun k => ?_) hwpsh hw01 hwO hwlim (isLocallyBoundedPshOn_mono hv hVU) fun k hk => ?_
    · rw [mulBorel_restrict hS hVU (hIm _ (hOm k)) (isLocallyBoundedOn_indicator_one _),
        mulBorel_restrict (hΘ k) hVU (hIm _ (hOm k)) (isLocallyBoundedOn_indicator_one _),
        mulBorel_nonPluripolarProduct_strictLocus hqp' hφ hW k]
      rfl
    · rw [ddcMul_restrict (hΘ k) hVU hv, ddcMul_restrict (hΘ m₀) hVU hv,
        mulBorel_restrict (hRk k) hVU (hIm _ (hOm m₀)) (isLocallyBoundedOn_indicator_one _),
        mulBorel_restrict (hRk m₀) hVU (hIm _ (hOm m₀)) (isLocallyBoundedOn_indicator_one _),
        hcons m₀ k hk]
  -- the truncated products of `(v, φ₁, …)`
  have hT : ∀ k, mulBorel (truncatedBT hqp U ψ k) ((Oψ k).indicator fun _ => (1 : ℝ)) =
      mulBorel (ddcMul S v) ((Oψ k).indicator fun _ => (1 : ℝ)) := by
    intro k
    have hb : ∀ i, IsLocallyBoundedPshOn U
        ((Fin.cons v fun i => truncationReal (φ i) k : Fin (p' + 1) → (ComplexModel n) → ℝ) i)
          := fun i =>
      Fin.cases hv (fun j => truncationReal_isLocallyBoundedPshOn (hφ j) k) i
    have hmax : ∀ i, EqOn (fun z => truncationReal (ψ i) k z)
        (fun z => max ((Fin.cons v fun i => truncationReal (φ i) k : Fin (p' + 1)
          → (ComplexModel n) → ℝ) i z)
          (-(k : ℝ))) U := by
      intro i
      refine Fin.cases (fun z _ => ?_) (fun j z hz => ?_) i
      · simp only [hψ_def, Fin.cons_zero]
        exact truncationReal_coe v k z
      · simp only [hψ_def, Fin.cons_succ]
        exact (truncationReal_nested (hφ j) le_rfl hz).symm
    have h1 := BedfordTaylorTopDegree.mulBorel_btProduct_max_const hqp hb
      (fun i => truncationReal_isLocallyBoundedPshOn (hψ i) k) (-(k : ℝ)) hmax
    have hLset : {z | z ∈ U ∧ ∀ i, -(k : ℝ) <
        (Fin.cons v fun i => truncationReal (φ i) k : Fin (p' + 1) → (ComplexModel n) → ℝ)
          i z} = Oψ k := by
      ext z
      simp only [hOψ_def, BedfordTaylorTopDegree.strictLocus, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, hψ_def]
      constructor
      · rintro ⟨hz, h0, hs⟩
        exact ⟨hz, EReal.coe_lt_coe_iff.mpr h0, fun j => (neg_lt_truncationReal_iff (hφ j) k hz).mp
          (hs j)⟩
      · rintro ⟨hz, h0, hs⟩
        exact ⟨hz, EReal.coe_lt_coe_iff.mp h0, fun j => (neg_lt_truncationReal_iff (hφ j) k hz).mpr
          (hs j)⟩
    rw [hLset] at h1
    have hsub : Oψ k ⊆ O k := fun z hz => ⟨hz.1, fun j => hz.2 j.succ⟩
    change mulBorel (btProduct (p' + 1) r (fun i => truncationReal (ψ i) k)
      (oneCurrentOf (U := U) hqp)) _ = _
    rw [h1, hE v k, ← inter_eq_right.mpr hsub, ← mulBorel_indicator_indicator (hRk k) (hOm k)
      (hOψm k), ← hL k, mulBorel_indicator_indicator hR (hOm k) (hOψm k)]
  -- well-definedness: the truncated products are bounded by `dd^c v ∧ S`
  have hWψ : IsWellDefinedOn hqp U ψ := by
    rw [isWellDefinedOn_iff hqp hψ, (isTruncationFamily hqp hψ).hasLocallyFiniteMass_iff]
    intro K hK hKU
    refine lt_of_le_of_lt (iSup_le fun k => ?_) (hR.traceMeasure_lt_top hK hKU)
    have hP := isPositive_mulBorel_indicator ((isTruncationFamily hqp hψ).isPositive k) (hOψm k)
    have hP' := isPositive_mulBorel_indicator hR (hOψm k)
    calc ((isTruncationFamily hqp hψ).isPositive k).traceMeasure (K ∩ Oψ k)
        = hP.traceMeasure K := (traceMeasure_mulBorel_indicator_apply _ (hOψm k) hP
          hK.measurableSet).symm
      _ = hP'.traceMeasure K := by
          rw [IsPositive.traceMeasure_congr hP hP' (hT k)]
      _ = hR.traceMeasure (K ∩ Oψ k) :=
          traceMeasure_mulBorel_indicator_apply hR (hOψm k) hP' hK.measurableSet
      _ ≤ hR.traceMeasure K := measure_mono inter_subset_left
  -- `dd^c v ∧ S` vanishes off `⋃ₖ O_k(v, φ)`
  have hnull : hR.traceMeasure (⋃ k, Oψ k)ᶜ = 0 := by
    -- `S` vanishes off `⋃ₖ O_k(φ)`
    have hS0 : hS.traceMeasure (⋃ k, O k)ᶜ = 0 :=
      traceMeasure_eq_zero_of_mulBorel_indicator_eq_zero hS
        (MeasurableSet.iUnion hOm).compl (mulBorel_nonPluripolarProduct_compl hqp' hφ hW)
    -- the poles of the `φⱼ`
    have hpoles : ∀ j, hR.traceMeasure ({z | φ j z = ⊥} ∩ U) = 0 := by
      intro j
      refine measure_inter_eq_zero_of_local fun x hx => ?_
      obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
      refine ⟨ball x (ρ / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
      refine traceMeasure_poleSet_ddcMul_eq_zero hS hSc hv hρ hρU ((hφ j).mono hρU)
        (measure_mono_null (fun z hz => ?_) hS0)
      refine fun hz' => ?_
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz'
      have := hk.2 j
      rw [hz.1] at this
      exact not_lt_bot this
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hR.traceMeasure_compl
      (measure_iUnion_null hpoles))
    by_cases hzU : z ∈ (U : Set (ComplexModel n))
    · right
      by_contra hne
      simp only [mem_iUnion, not_exists, mem_inter_iff, mem_ofPred_eq, not_and] at hne
      have hfin : ∀ j, φ j z ≠ ⊥ := fun j h => hne j h hzU
      choose a ha using fun j => (⟨(φ j z).toReal, (EReal.coe_toReal
        ((hφ j z hzU).ne_top) (hfin j)).symm⟩ : ∃ a : ℝ, φ j z = a)
      obtain ⟨k, hk⟩ := exists_nat_gt (|v z| + ∑ j, |a j|)
      refine hz (mem_iUnion.mpr ⟨k, hzU, fun i => ?_⟩)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [hψ_def, Fin.cons_zero]
        refine EReal.coe_lt_coe_iff.mpr ?_
        have := neg_abs_le (v z)
        have h2 : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ => abs_nonneg _
        linarith
      · simp only [hψ_def, Fin.cons_succ, ha j]
        refine EReal.coe_lt_coe_iff.mpr ?_
        have := neg_abs_le (a j)
        have h2 : |a j| ≤ ∑ j, |a j| :=
          Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
        have h3 := abs_nonneg (v z)
        linarith
    · exact Or.inl hzU
  refine ⟨hWψ, (eq_nonPluripolarProduct_of_mulBorel hqp hψ hWψ hR (fun k => (hT k).symm)
    (mulBorel_indicator_eq_zero_of_null hR (MeasurableSet.iUnion hOψm).compl hnull)).symm⟩

/-! ### Several bounded factors -/

theorem nonPluripolarProduct_comp_cast {q p₁ p₂ : ℕ} (h : p₁ = p₂) (hqp₁ : q + p₁ = n)
    (hqp₂ : q + p₂ = n) (φ : Fin p₂ → (ComplexModel n) → EReal) :
    (IsWellDefinedOn hqp₁ U (φ ∘ Fin.cast h) ↔ IsWellDefinedOn hqp₂ U φ) ∧
      nonPluripolarProduct hqp₁ U (φ ∘ Fin.cast h) = nonPluripolarProduct hqp₂ U φ := by
  subst h
  exact ⟨Iff.rfl, rfl⟩

theorem isWellDefinedOn_congr_degree {a b p : ℕ} (h : a = b) (ha : a + p = n) (hb : b + p = n)
    (φ : Fin p → (ComplexModel n) → EReal) : IsWellDefinedOn ha U φ ↔ IsWellDefinedOn hb U φ := by
  subst h
  rfl

theorem heq_nonPluripolarProduct {a b p : ℕ} (h : a = b) (ha : a + p = n) (hb : b + p = n)
    (φ : Fin p → (ComplexModel n) → EReal) :
    HEq (nonPluripolarProduct ha U φ) (nonPluripolarProduct hb U φ) := by
  subst h
  rfl

/-- **`prop:npp1` (3), second sentence** (FPT `prop:nonpluripolar-bounded-factor-compatibility`),
on an open `U ⊆ ℂⁿ`: let `v₁, …, v_q` be locally bounded psh and `φ_{q+1}, …, φ_p` psh on `U`
with `T = ⟨dd^c φ_{q+1} ∧ ⋯ ∧ dd^c φ_p⟩` well defined.  Then the non-pluripolar product
`⟨dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ dd^c φ_{q+1} ∧ ⋯ ∧ dd^c φ_p⟩` of the concatenated tuple is well defined
and equals the relative Bedford–Taylor product `dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ T` (`btProduct q r v T`,
the recursion `dd^c(v₁ dd^c(v₂ ⋯ dd^c(v_q T)))` with base `T`). -/
theorem nonPluripolarProduct_append_bounded : ∀ (q : ℕ) {r p' : ℕ} (hqp' : r + q + p' = n)
    (hqp : r + (q + p') = n) {v : Fin q → (ComplexModel n) → ℝ} (_hv : ∀ i, IsLocallyBoundedPshOn
      U (v i))
    {φ : Fin p' → (ComplexModel n) → EReal} (_hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (_hW : IsWellDefinedOn hqp' U φ),
    IsWellDefinedOn hqp U (Fin.append (fun i z => (v i z : EReal)) φ) ∧
      nonPluripolarProduct hqp U (Fin.append (fun i z => (v i z : EReal)) φ) =
        btProduct q r v (nonPluripolarProduct hqp' U φ)
  | 0, r, p', hqp', hqp, v, _, φ, _, hW => by
    rw [Fin.append_left_nil _ φ rfl]
    have h := nonPluripolarProduct_comp_cast (U := U) (by rw [Nat.zero_add] : 0 + p' = p') hqp
      hqp' φ
    exact ⟨h.1.mpr hW, h.2⟩
  | q + 1, r, p', hqp', hqp, v, hv, φ, hφ, hW => by
    have e : (fun i z => (v i z : EReal)) =
        Fin.cons (fun z => (v 0 z : EReal)) (fun i z => (v i.succ z : EReal)) :=
      (Fin.cons_self_tail _).symm
    rw [e, Fin.append_cons]
    set ψ := Fin.append (fun (i : Fin q) z => (v i.succ z : EReal)) φ with hψ_def
    have h1 : r + 1 + q + p' = n := by omega
    have hW' : IsWellDefinedOn h1 U φ :=
      (isWellDefinedOn_congr_degree (by omega : r + (q + 1) = r + 1 + q) hqp' h1 φ).mp hW
    obtain ⟨hWψ, hψeq⟩ := nonPluripolarProduct_append_bounded q (r := r + 1) h1
      (by omega : r + 1 + (q + p') = n) (fun i => hv i.succ) hφ hW'
    have hψpsh : ∀ i, PlurisubharmonicOn (ψ i) U := by
      refine Fin.addCases (fun i => ?_) (fun j => ?_)
      · rw [hψ_def, Fin.append_left]
        exact (hv i.succ).1
      · rw [hψ_def, Fin.append_right]
        exact hφ j
    have h2 : r + (q + p' + 1) = n := by omega
    have hcore := nonPluripolarProduct_cons_bounded (by omega : r + 1 + (q + p') = n) h2
      hψpsh hWψ (hv 0)
    have hc := nonPluripolarProduct_comp_cast (U := U) (Nat.add_right_comm q 1 p') hqp h2
      (Fin.cons (fun z => (v 0 z : EReal)) ψ)
    refine ⟨hc.1.mpr hcore.1, ?_⟩
    rw [hc.2, hcore.2, hψeq]
    exact (btProduct_succ_eq_ddcMul q r v _ _
      (heq_nonPluripolarProduct (by omega : r + (q + 1) = r + 1 + q) hqp' h1 φ)).symm

end SGPT.NPP.NonPluripolarCurrent
