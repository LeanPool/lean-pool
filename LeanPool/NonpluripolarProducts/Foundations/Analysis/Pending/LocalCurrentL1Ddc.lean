/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullbackDdc

/-!
# `dd^c(u [1])` for a plurisubharmonic function `u ∈ L¹_loc`

Blueprint `ana:l1-psh-current`, `ana:l1-psh-ddc` (`blueprint/src/analytic.tex`; TN.5,
    toward `ana:volume-semicontinuity`,
route item 2: the local readings of `θ + dd^c u` for an UNBOUNDED `θ`-psh `u`).  Source: Demailly,
    *Complex analytic and
differential geometry* (`demailly-cadg`), Ch. I (4.17) (a (pluri)subharmonic `u ≢ -∞` on a
    connected open set is `L¹_loc`),
(5.8) (its complex Hessian is a positive measure) and Ch. III, 1.18 (`i d'd'' u` of a psh
    `u ∈ L¹_loc` is a closed positive
`(1,1)`-current); Boucksom 2002 (`bou02-volume`) uses these currents for arbitrary closed positive
    `T = θ + dd^c u`.

The library's `ddcMul (oneCurrent U) w = dd^c(w [1])` (`Pending.LocalBedfordTaylorProducts`)
    is the Bedford--Taylor product of a
LOCALLY BOUNDED psh `w` (a junk value otherwise).  Here, for `u : ℂⁿ → [-∞, ∞]`:

* `IsL1PshOn U u`: `u` is psh on `U` and nondegenerate (every point of `U` has points where
    `u ≠ -∞` arbitrarily close: the
  chart form of `FirstPass.LocallyNondegenerate`); `IsL1PshOn.locallyIntegrableOn` (`u ∈
    L¹_loc(U)`),
  `IsL1PshOn.ae_ne_bot` (`u > -∞` a.e. on `U`), `IsL1PshOn.mono`;
* `l1Current U u`, the current `u [1]` of bidimension `(n,n)`: `(u [1])(γ)(φ) = ⟨γ⟩ ∫ φ u dλ`
    (`l1Current_apply`), and
  `ddcL1 U u = dd^c(u [1])`; `l1Current_congr_ae`, `restrict_l1Current`, `restrict_ddcL1`;
* `weakTendsto_l1Current` (dominated convergence of the potentials gives weak convergence of the
    currents);
  `IsL1PshOn.weakTendsto_l1Current_truncation`: the truncations `max(u, -k)`
    (`FirstPass.MongeAmpere.truncationReal`, locally
  bounded psh, decreasing to `u`) give `max(u, -k) [1] → u [1]`, hence
    `dd^c(max(u,-k) [1]) → dd^c(u [1])`;
* **`l1Current_coe_eq_mulBorel`, `ddcL1_coe_eq_ddcMul`**: for `w` locally bounded psh,
    `w [1]` is TN3's `mulBorel [1] w`, so
  `dd^c(w [1])` is `ddcMul (oneCurrent U) w`;
* **`IsL1PshOn.isPositive_ddcL1`**: `dd^c(u [1])` is positive (limit of the positive
    `dd^c(max(u,-k) [1])`);
  `isClosedAny_ddcL1`: it is closed;
* `IsL1PshOn.comp`: `u ∘ τ` is again psh and nondegenerate for a biholomorphism `τ`;
* **`pullback_ddcL1`**: naturality, `τ^*(dd^c(u [1])) = dd^c((u ∘ τ) [1])` for `τ : A → B`
    biholomorphic (`pullback_ddcMul` of
  `Pending.LocalCurrentPullbackDdc` for each truncation, and the weak continuity of `τ^*`).

Sorry-free.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms TopDegreeDensity LocalProductCurrents
  LocalBedfordTaylorLocality LocalBedfordTaylorProducts LocalBedfordTaylorContinuity
    LocalBedfordTaylorForms
  LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor

/-! ### Nondegenerate psh functions are locally integrable and finite almost everywhere -/

section Nondegenerate

variable {n : ℕ}

/-- **A psh function in `L¹_loc`**: `u` is plurisubharmonic on `U` and no point of `U` has a
    neighbourhood on which
`u ≡ -∞` (the chart form of `FirstPass.LocallyNondegenerate`). -/
structure IsL1PshOn (U : Opens (ComplexModel n)) (u : ComplexModel n → EReal) : Prop where
  psh : PlurisubharmonicOn u U
  frequently_ne_bot : ∀ x ∈ U, ∃ᶠ y in 𝓝 x, u y ≠ ⊥

variable {U : Opens (ComplexModel n)} {u : ComplexModel n → EReal}

/-- Every point of `U` has an open neighbourhood on which `u` is finite a.e. and integrable. -/
theorem IsL1PshOn.subset_pshIntegrabilityLocus (hu : IsL1PshOn U u) :
    (U : Set (ComplexModel n)) ⊆ pshIntegrabilityLocus u volume := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  obtain ⟨a, ha, haB⟩ := ((hu.frequently_ne_bot x hx).and_eventually (Metric.ball_mem_nhds x
    hr)).exists
  exact (hu.psh.mono hball).subset_pshIntegrabilityLocus volume (convex_ball x r).isPreconnected
    ⟨a, haB, ha⟩
    (Metric.mem_ball_self hr)

/-- **`u ∈ L¹_loc(U)`.** -/
theorem IsL1PshOn.locallyIntegrableOn (hu : IsL1PshOn U u) :
    LocallyIntegrableOn (fun x => (u x).toReal) U volume := by
  intro x hx
  obtain ⟨V, hV, hxV, -, hI⟩ := hu.subset_pshIntegrabilityLocus hx
  exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), hI⟩

/-- **`u > -∞` almost everywhere on `U`.** -/
theorem IsL1PshOn.ae_ne_bot (hu : IsL1PshOn U u) :
    ∀ᵐ x ∂(volume.restrict (U : Set (ComplexModel n))), u x ≠ ⊥ := by
  rw [ae_restrict_iff' U.isOpen.measurableSet, ae_iff]
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨V, hV, hxV, hae, -⟩ := hu.subset_pshIntegrabilityLocus (Classical.not_imp.mp hx).1
  rw [ae_restrict_iff' hV.measurableSet, ae_iff] at hae
  refine ⟨_, inter_mem_nhdsWithin _ (hV.mem_nhds hxV), measure_mono_null (fun y hy => ?_) hae⟩
  exact fun h' => (Classical.not_imp.mp hy.1).2 (h' hy.2).2

/-- Restriction to an open subset. -/
theorem IsL1PshOn.mono (hu : IsL1PshOn U u) {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    : IsL1PshOn V u :=
  ⟨hu.psh.mono hVU, fun x hx => hu.frequently_ne_bot x (hVU hx)⟩

end Nondegenerate

/-! ### The current `u [1]` and `dd^c(u [1])` -/

section Current

variable {n : ℕ} {U : Opens (ComplexModel n)}

variable (U) in
/-- **The current `u [1]`** of bidimension `(n,n)` of a function `u ∈ L¹_loc(U)` with values in
    `[-∞, ∞]`:
`(u [1])(γ)(φ) = ⟨γ⟩ ∫ φ u dλ`; the junk value `0` when `u ∉ L¹_loc(U)`. -/
def l1Current (u : ComplexModel n → EReal) : LocalProductCurrent n U n :=
  open Classical in
  if h : LocallyIntegrableOn (fun x => (u x).toReal) U volume then
    LinearMap.smulRight (topDensityLM n ∘ₗ (formSpan n n).subtype) (regularDistribution volume _ h)
  else 0

theorem l1Current_apply {u : ComplexModel n → EReal} (h : LocallyIntegrableOn (fun x => (u
    x).toReal) U volume)
    (γ : formSpan n n) (φ : 𝓓(U, ℝ)) :
    l1Current U u γ φ = topDensity (γ : RealForm n (2 * n)) * ∫ x, φ x * (u x).toReal := by
  rw [l1Current, dite_eq_left h]
  simp [regularDistribution_apply]

/-- `u [1]` depends only on the class of `u` almost everywhere on `U`. -/
theorem l1Current_congr_ae {u v : ComplexModel n → EReal} (hu : LocallyIntegrableOn (fun x => (u
    x).toReal) U volume)
    (hv : LocallyIntegrableOn (fun x => (v x).toReal) U volume)
    (h : ∀ᵐ x ∂(volume.restrict (U : Set (ComplexModel n))), (u x).toReal = (v x).toReal) :
    l1Current U u = l1Current U v := by
  ext γ φ
  rw [l1Current_apply hu, l1Current_apply hv]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).mp h] with x hx
  by_cases hxU : x ∈ (U : Set (ComplexModel n))
  · rw [hx hxU]
  · simp [testFunction_eq_zero_of_notMem φ hxU]

/-- **Restriction**: `(u [1])|_V = u [1]` on `V ≤ U`. -/
theorem restrict_l1Current {u : ComplexModel n → EReal} {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    (hu : LocallyIntegrableOn (fun x => (u x).toReal) U volume) :
    LocalBedfordTaylorLocality.restrict hVU (l1Current U u) = l1Current V u := by
  ext γ φ
  rw [LocalBedfordTaylorLocality.restrict_apply, l1Current_apply hu, l1Current_apply (hu.mono_set
    hVU)]
  simp only [extTest_apply]

/-- A test function times a function in `L¹_loc(U)` is integrable. -/
theorem integrable_testFunction_mul {F : ComplexModel n → ℝ} (hF : LocallyIntegrableOn F U volume)
    (φ : 𝓓(U, ℝ)) :
    Integrable (fun x => φ x * F x) volume := by
  have hK : IntegrableOn (fun x => φ x * F x) (tsupport φ) volume :=
    (hF.integrableOn_compact_subset φ.tsupport_subset φ.hasCompactSupport).continuousOn_mul
      φ.continuous.continuousOn φ.hasCompactSupport
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).mp hK
  by_contra hxs
  exact hx (show φ x * F x = 0 by rw [image_eq_zero_of_notMem_tsupport hxs, zero_mul])

/-- **Dominated convergence of the potentials gives weak convergence of the currents**
    `f_k [1] → g [1]`. -/
theorem weakTendsto_l1Current {f : ℕ → ComplexModel n → EReal} {g : ComplexModel n → EReal}
    (hf : ∀ k, LocallyIntegrableOn (fun x => (f k x).toReal) U volume)
    (hg : LocallyIntegrableOn (fun x => (g x).toReal) U volume)
    {F : ComplexModel n → ℝ} (hF : LocallyIntegrableOn F U volume)
    (hbound : ∀ k, ∀ᵐ x ∂(volume.restrict (U : Set (ComplexModel n))), |(f k x).toReal| ≤ F x)
    (hlim : ∀ᵐ x ∂(volume.restrict (U : Set (ComplexModel n))),
      Tendsto (fun k => (f k x).toReal) atTop (𝓝 (g x).toReal)) :
    WeakTendsto (fun k => l1Current U (f k)) (l1Current U g) := by
  intro γ φ
  simp only [l1Current_apply (hf _), l1Current_apply hg]
  refine Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence (fun x => |φ x| * |F x|)
    (fun k => (integrable_testFunction_mul (hf k) φ).aestronglyMeasurable) ?_ (fun k => ?_) ?_)
  · exact (integrable_testFunction_mul hF φ).norm.congr (Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_mul])
  · filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).mp (hbound k)] with x hx
    by_cases hxU : x ∈ (U : Set (ComplexModel n))
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left ((hx hxU).trans (le_abs_self _)) (abs_nonneg _)
    · rw [testFunction_eq_zero_of_notMem φ hxU]
      simp
  · filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).mp hlim] with x hx
    by_cases hxU : x ∈ (U : Set (ComplexModel n))
    · exact (hx hxU).const_mul _
    · simp only [testFunction_eq_zero_of_notMem φ hxU, zero_mul]
      exact tendsto_const_nhds

/-- `|max(u, -k)| ≤ |u|` where `u` is finite. -/
theorem abs_truncationReal_le {u : ComplexModel n → EReal} (k : ℕ) {x : ComplexModel n} (hx : u x
    ≠ ⊥)
    (hx' : u x ≠ ⊤) : |truncationReal u k x| ≤ |(u x).toReal| := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = r := ⟨(u x).toReal, (EReal.coe_toReal hx' hx).symm⟩
  simp only [truncationReal, truncation, hr, EReal.toReal_coe]
  rcases le_total (-(k : ℝ)) r with h | h
  · rw [max_eq_left (EReal.coe_le_coe_iff.mpr h), EReal.toReal_coe]
  · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h), EReal.toReal_coe, abs_neg, Nat.abs_cast,
    abs_of_nonpos
      (h.trans (by simp))]
    linarith

/-- `max(u, -k) → u` where `u` is finite. -/
theorem tendsto_truncationReal {u : ComplexModel n → EReal} {x : ComplexModel n} (hx : u x ≠ ⊥)
    (hx' : u x ≠ ⊤) :
    Tendsto (fun k => truncationReal u k x) atTop (𝓝 (u x).toReal) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, u x = r := ⟨(u x).toReal, (EReal.coe_toReal hx' hx).symm⟩
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈-r⌉₊) fun k hk => ?_
  have h : -(k : ℝ) ≤ r := by
    have := (Nat.le_ceil (-r)).trans (Nat.cast_le.mpr hk)
    linarith
  simp only [truncationReal, truncation, hr, EReal.toReal_coe]
  rw [max_eq_left (EReal.coe_le_coe_iff.mpr h), EReal.toReal_coe]

/-- **The truncations**: `max(u, -k) [1] → u [1]` weakly. -/
theorem IsL1PshOn.weakTendsto_l1Current_truncation {u : ComplexModel n → EReal} (hu : IsL1PshOn U
    u) :
    WeakTendsto (fun k => l1Current U (fun x => (truncationReal u k x : EReal))) (l1Current U u)
      := by
  have hfin : ∀ᵐ x ∂(volume.restrict (U : Set (ComplexModel n))), u x ≠ ⊥ ∧ u x ≠ ⊤ := by
    filter_upwards [hu.ae_ne_bot, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
    exact ⟨hx, (hu.psh x hxU).ne_top⟩
  refine weakTendsto_l1Current (fun k => ?_) hu.locallyIntegrableOn hu.locallyIntegrableOn.norm
    (fun k => ?_) ?_
  · simpa only [EReal.toReal_coe] using
      locallyIntegrableOn_of_plurisubharmonicOn_real (truncationReal_isLocallyBoundedPshOn hu.psh
        k).1
  · filter_upwards [hfin] with x hx
    simpa only [EReal.toReal_coe, Real.norm_eq_abs] using abs_truncationReal_le k hx.1 hx.2
  · filter_upwards [hfin] with x hx
    simpa only [EReal.toReal_coe] using tendsto_truncationReal hx.1 hx.2

/-- **Agreement with the Bedford--Taylor current**: for `w` locally bounded psh,
    `w [1]` is `mulBorel [1] w` (TN3's
current of `w` times Lebesgue measure). -/
theorem l1Current_coe_eq_mulBorel {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn U w) :
    l1Current U (fun x => (w x : EReal)) = mulBorel (oneCurrent U) ((U : Set (ComplexModel
      n)).indicator w) := by
  ext γ φ
  set c : ℝ := topDensity (γ : RealForm n (2 * n)) with hc
  have hloc : IsLocalDensity (U := U) (volume.restrict (U : Set (ComplexModel n))) (fun _ => c) :=
    ⟨by rw [Measure.restrict_apply U.isOpen.measurableSet.compl, compl_inter_self, measure_empty],
      fun K hK _ => (Measure.restrict_apply_le _ K).trans_lt hK.measure_lt_top, measurable_const,
      fun K _ _ => ⟨|c|, fun _ _ => le_rfl⟩⟩
  have hrep : ∀ ψ : 𝓓(U, ℝ), oneCurrent U γ ψ = ∫ x, ψ x * c ∂(volume.restrict (U : Set
    (ComplexModel n))) := by
    intro ψ
    rw [oneCurrent_apply, integral_mul_const, setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => testFunction_eq_zero_of_notMem ψ hx, mul_comm]
  rw [mulBorel_apply_of_integral_eq isPositive_oneCurrent γ hloc hrep
    (measurable_indicator_of_isLocallyBoundedPshOn hw) (isLocallyBoundedOn_indicator hw) φ,
    l1Current_apply (by simpa only [EReal.toReal_coe] using
      locallyIntegrableOn_of_plurisubharmonicOn_real hw.1)]
  simp only [EReal.toReal_coe]
  rw [setIntegral_congr_fun U.isOpen.measurableSet (g := fun x => c * (φ x * w x)) fun x hx => by
      simp only [indicator_of_mem hx]; ring,
    integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [testFunction_eq_zero_of_notMem φ hx]]

end Current

section DDC

variable {m : ℕ}

/-- **`dd^c(u [1])`** for `u ∈ L¹_loc(U)` (`n = m + 1`), a current of bidimension `(m,m)`. -/
def ddcL1 (U : Opens (ComplexModel (m + 1))) (u : ComplexModel (m + 1) → EReal)
    : LocalProductCurrent (m + 1) U m :=
  ddc (l1Current U u)

/-- For `w` locally bounded psh, `dd^c(w [1])` is the Bedford--Taylor current
    `ddcMul (oneCurrent U) w`. -/
theorem ddcL1_coe_eq_ddcMul {U : Opens (ComplexModel (m + 1))} {w : ComplexModel (m + 1) → ℝ}
    (hw : IsLocallyBoundedPshOn U w) : ddcL1 U (fun x => (w x : EReal)) = ddcMul (oneCurrent U)
      w := by
  rw [ddcL1, ddcMul, l1Current_coe_eq_mulBorel hw]

/-- `dd^c(max(u, -k) [1]) → dd^c(u [1])` weakly. -/
theorem IsL1PshOn.weakTendsto_ddcMul_truncation {U : Opens (ComplexModel (m + 1))} {u :
    ComplexModel (m + 1) → EReal}
    (hu : IsL1PshOn U u) :
    WeakTendsto (fun k => ddcMul (oneCurrent U) (truncationReal u k)) (ddcL1 U u) := by
  have h := weakTendsto_ddc hu.weakTendsto_l1Current_truncation
  intro γ φ
  have e : ∀ k, ddcMul (oneCurrent U) (truncationReal u k) =
      ddc (l1Current U (fun x => (truncationReal u k x : EReal))) := fun k =>
    (ddcL1_coe_eq_ddcMul (truncationReal_isLocallyBoundedPshOn hu.psh k)).symm
  simp only [e]
  exact h γ φ

/-- **Positivity of `dd^c(u [1])`** for a psh `u ∈ L¹_loc(U)`. -/
theorem IsL1PshOn.isPositive_ddcL1 {U : Opens (ComplexModel (m + 1))} {u : ComplexModel (m + 1)
    → EReal}
    (hu : IsL1PshOn U u) : IsPositive (ddcL1 U u) :=
  isPositive_of_weakTendsto (fun k => isPositive_ddcMul_oneCurrent
    (truncationReal_isLocallyBoundedPshOn hu.psh k))
    hu.weakTendsto_ddcMul_truncation

/-- `dd^c(u [1])` is closed. -/
theorem isClosedAny_ddcL1 {U : Opens (ComplexModel (m + 1))} (u : ComplexModel (m + 1) → EReal) :
    IsClosedAny m (ddcL1 U u) := by
  cases m with
  | zero => trivial
  | succ k => exact isClosedCurrent_ddc _

/-- **Restriction**: `dd^c(u [1])|_V = dd^c(u [1])` on `V ≤ U`. -/
theorem restrict_ddcL1 {U V : Opens (ComplexModel (m + 1))} (hVU : V ≤ U) {u : ComplexModel (m +
    1) → EReal}
    (hu : LocallyIntegrableOn (fun x => (u x).toReal) U volume) :
    LocalBedfordTaylorLocality.restrict hVU (ddcL1 U u) = ddcL1 V u := by
  rw [ddcL1, ddcL1, ← ddc_restrict, restrict_l1Current hVU hu]

end DDC

/-! ### Naturality under biholomorphisms -/

section Naturality

variable {m : ℕ} {A B : Opens (ComplexModel (m + 1))} {τ σ : ComplexModel (m + 1)
    → ComplexModel (m + 1)}

/-- `u ∘ τ` is psh and nondegenerate on `A` when `u` is so on `B`. -/
theorem IsL1PshOn.comp (h : IsBiholomorphicPair A B τ σ) {u : ComplexModel (m + 1)
    → EReal} (hu : IsL1PshOn B u) :
    IsL1PshOn A (fun x => u (τ x)) where
  psh := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic A.isOpen (h.holo.differentiableOn
    (by simp))
    h.mapsTo hu.psh
  frequently_ne_bot x hx := by
    rw [Filter.frequently_iff]
    intro V hV
    have hσ : ContinuousAt σ (τ x) := h.holo_inv.continuousOn.continuousAt (B.isOpen.mem_nhds
      (h.mapsTo hx))
    have hpre : σ ⁻¹' (V ∩ A) ∈ 𝓝 (τ x) := by
      refine hσ.preimage_mem_nhds ?_
      rw [h.left_inv x hx]
      exact inter_mem hV (A.isOpen.mem_nhds hx)
    obtain ⟨y, hyV, hy⟩ := Filter.frequently_iff.mp (hu.frequently_ne_bot (τ x) (h.mapsTo hx))
      (inter_mem hpre (B.isOpen.mem_nhds (h.mapsTo hx)))
    refine ⟨σ y, hyV.1.1, ?_⟩
    rw [h.right_inv y hyV.2]
    exact hy

/-- **Naturality of `dd^c` for psh functions in `L¹_loc`**: `τ^*(dd^c(u [1])) = dd^c((u ∘ τ) [1])`
    for `τ : A → B`
biholomorphic. -/
theorem pullback_ddcL1 (h : IsBiholomorphicPair A B τ σ) {u : ComplexModel (m + 1)
    → EReal} (hu : IsL1PshOn B u) :
    pullback h hu.isPositive_ddcL1 = ddcL1 A (fun x => u (τ x)) := by
  ext γ φ
  have hw : ∀ k, IsLocallyBoundedPshOn B (truncationReal u k) := fun k =>
    truncationReal_isLocallyBoundedPshOn hu.psh k
  have h1 := weakTendsto_pullback h (fun k => isPositive_ddcMul_oneCurrent (hw k))
    hu.isPositive_ddcL1
    hu.weakTendsto_ddcMul_truncation γ φ
  simp only [pullback_ddcMul h (hw _)] at h1
  have h2 := (hu.comp h).weakTendsto_ddcMul_truncation γ φ
  exact tendsto_nhds_unique h1 h2

end Naturality

end SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
