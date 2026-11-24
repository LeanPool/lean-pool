/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorMass
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.MollifierApproximation

/-!
# Continuity of the recursive Bedford--Taylor product for continuous potentials

For the currents of `Pending.LocalProductCurrents` on an open `U ⊆ ℂⁿ`, weak convergence
`T_k → T` (`WeakTendsto`) means `T_k(γ)(φ) → T(γ)(φ)` for every constant form `γ` and every test
function `φ`.  This file proves `bt:continuous-convergence` (`demailly-cadg:III.3.6`):

* `isPositive_of_weakTendsto`, `isClosedAny_of_weakTendsto` — weak limits of positive (closed)
  currents are positive (closed); `weakTendsto_ddc` — `dd^c` is weakly continuous;
* `exists_traceMeasure_le_of_weakTendsto` — the trace masses of a weakly convergent sequence of
  positive currents are bounded on every compact subset of `U`;
* `exists_contDiff_abs_sub_le` — a function continuous on `U` is uniformly approximated on a
    compact
  subset of `U` by globally smooth functions (mollification);
* `weakTendsto_mulBorel` — **the multiplication argument**: if `S_k → S` weakly (positive) and
  `a_k → a` locally uniformly on `U` with `a` continuous, then `a_k S_k → a S` weakly;
* `weakTendsto_btProduct` — **continuity of the recursive product**: if `T_k → T` weakly
  (positive closed) and locally bounded PSH `u_j^k` converge locally uniformly on `U` to continuous
  `u_j`, then `B(u^k; T_k) → B(u; T)` weakly; `weakTendsto_mulBorel_btProduct` — the weighted form
  `u_1^k B(u_2^k, …; T_k) → u_1 B(u_2, …; T)`.

The limit potentials are only assumed continuous: the limit products are positive and closed as
    weak
limits (`isPositive_btProduct_of_weakTendsto`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorMass

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U : Opens (ComplexModel n)}

/-! ### Weak convergence of currents -/

section Weak

variable {q : ℕ}

/-- **Weak convergence** of currents of bidimension `(q,q)` on `U`: `T_k(γ)(φ) → T(γ)(φ)` for every
constant form `γ` and every test function `φ`. -/
def WeakTendsto (T : ℕ → LocalProductCurrent n U q) (T₀ : LocalProductCurrent n U q) : Prop :=
  ∀ (γ : formSpan n q) (φ : 𝓓(U, ℝ)), Tendsto (fun k => T k γ φ) atTop (𝓝 (T₀ γ φ))

/-- A weak limit of positive currents is positive. -/
theorem isPositive_of_weakTendsto {T : ℕ → LocalProductCurrent n U q}
    {T₀ : LocalProductCurrent n U q} (hT : ∀ k, IsPositive (T k)) (h : WeakTendsto T T₀) :
    IsPositive T₀ := by
  intro ι _ γ φ hγ
  have hlim : Tendsto (fun k => ∑ i, T k (γ i) (φ i)) atTop (𝓝 (∑ i, T₀ (γ i) (φ i))) :=
    tendsto_finsetSum _ fun i _ => h (γ i) (φ i)
  exact ge_of_tendsto' hlim fun k => hT k ι γ φ hγ

/-- A weak limit of closed currents is closed. -/
theorem isClosedCurrent_of_weakTendsto {T : ℕ → LocalProductCurrent n U (q + 1)}
    {T₀ : LocalProductCurrent n U (q + 1)} (hT : ∀ k, IsClosedCurrent (T k))
    (h : WeakTendsto T T₀) : IsClosedCurrent T₀ := by
  intro ℓ γ
  ext φ
  rw [_root_.sum_apply, _root_.zero_apply]
  simp only [dDist_apply, Finset.sum_neg_distrib, neg_eq_zero]
  have hlim : Tendsto (fun k => ∑ a, T k (wedgeLM q (isOneOne_testForm a ℓ) γ)
      (dTest (realBasis n a) φ)) atTop
      (𝓝 (∑ a, T₀ (wedgeLM q (isOneOne_testForm a ℓ) γ) (dTest (realBasis n a) φ))) :=
    tendsto_finsetSum _ fun a _ => h _ _
  have hzero : ∀ k, ∑ a, T k (wedgeLM q (isOneOne_testForm a ℓ) γ)
      (dTest (realBasis n a) φ) = 0 := fun k => (hT k).apply_eq_zero ℓ γ φ
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem isClosedAny_of_weakTendsto : ∀ {q : ℕ} {T : ℕ → LocalProductCurrent n U q}
    {T₀ : LocalProductCurrent n U q}, (∀ k, IsClosedAny q (T k)) → WeakTendsto T T₀ →
    IsClosedAny q T₀
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, hT, h => isClosedCurrent_of_weakTendsto hT h

/-- `dd^c` is weakly continuous. -/
theorem weakTendsto_ddc {T : ℕ → LocalProductCurrent n U (q + 1)}
    {T₀ : LocalProductCurrent n U (q + 1)} (h : WeakTendsto T T₀) :
    WeakTendsto (fun k => ddc (T k)) (ddc T₀) := fun γ φ => by
  simp only [ddc_apply_apply]
  exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => (h _ _).const_mul _

/-- **Uniform mass bounds**: the trace masses of a weakly convergent sequence of positive currents
are bounded on every compact subset of `U`. -/
theorem exists_traceMeasure_le_of_weakTendsto {T : ℕ → LocalProductCurrent n U q}
    {T₀ : LocalProductCurrent n U q} (hT : ∀ k, IsPositive (T k)) (h : WeakTendsto T T₀)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, ∀ k, ((hT k).traceMeasure K).toReal ≤ M := by
  obtain ⟨V, hVo, hKV, hVcl, hVc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨χ, hχ, hχ1, hχV, hχ01⟩ := exists_cutoff_unit hK hVo hKV
  have hχc : HasCompactSupport χ := hVc.of_isClosed_subset (isClosed_tsupport χ)
    (hχV.trans subset_closure)
  let χt : 𝓓(U, ℝ) := ⟨χ, hχ, hχc, hχV.trans (subset_closure.trans hVcl)⟩
  obtain ⟨B, hB⟩ := (h (kahlerPower n q) χt).bddAbove_range
  refine ⟨B, fun k => ?_⟩
  have hfin : (hT k).traceMeasure K < ⊤ := (hT k).traceMeasure_lt_top hK hKU
  have hint : Integrable (fun x => χ x) (hT k).traceMeasure := by
    have := (hT k).integrable_mul_of_bounded (w := fun _ => (1 : ℝ)) χt.continuous
      χt.hasCompactSupport χt.tsupport_subset aestronglyMeasurable_const ⟨1, fun _ _ => by simp⟩
    simp only [mul_one] at this
    exact this
  calc ((hT k).traceMeasure K).toReal = ∫ x in K, χ x ∂(hT k).traceMeasure := by
        rw [setIntegral_congr_fun hK.measurableSet (fun x hx => hχ1 x hx),
          setIntegral_const, smul_eq_mul, mul_one]
        rfl
    _ ≤ ∫ x, χ x ∂(hT k).traceMeasure :=
        setIntegral_le_integral hint (Eventually.of_forall fun x => (hχ01 x).1)
    _ = T k (kahlerPower n q) χt := (hT k).integral_traceMeasure χt
    _ ≤ B := hB ⟨k, rfl⟩

/-- The integral of `h f` for a density `f` bounded by `C` and `h` bounded by `B` and vanishing
off a compact `K ⊆ U`. -/
theorem abs_integral_mul_density_le {R : LocalProductCurrent n U q} (hR : IsPositive R)
    (γ : formSpan n q) {C : ℝ} (hC : ∀ᵐ x ∂hR.traceMeasure, |hR.density γ x| ≤ C)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {h : E → ℝ} {B : ℝ}
    (hB : ∀ x ∈ K, |h x| ≤ B) (hK0 : ∀ x ∉ K, h x = 0) :
    |∫ x, h x * hR.density γ x ∂hR.traceMeasure| ≤ B * C * (hR.traceMeasure K).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hK0 x hx, zero_mul]]
  have := norm_setIntegral_le_of_norm_le_const_ae (f := fun x => h x * hR.density γ x)
    (C := B * C) (hR.traceMeasure_lt_top hK hKU) (by
      rw [ae_restrict_iff' hK.measurableSet]
      filter_upwards [hC] with x hx hxK
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB x hxK) hx (abs_nonneg _) ((abs_nonneg _).trans (hB x hxK)))
  simpa [Real.norm_eq_abs, Measure.real] using this

end Weak

/-! ### Uniform smooth approximation -/

section Approximation

/-- **Uniform smooth approximation on compacts**: a function continuous on `U` is, on a compact
subset of `U`, uniformly within `ε` of a globally smooth function. -/
theorem exists_contDiff_abs_sub_le {a : E → ℝ} (ha : ContinuousOn a U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, |g x - a x| ≤ ε := by
  obtain ⟨V, hVo, hKV, hVcl, hVc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨χ, hχ, hχ1, hχV, -⟩ := exists_cutoff_unit hK hVo hKV
  set a' : E → ℝ := fun x => χ x * a x with ha'def
  have hχU : tsupport χ ⊆ U := hχV.trans (subset_closure.trans hVcl)
  have ha'c : Continuous a' := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ (U : Set E)
    · exact hχ.continuous.continuousAt.mul (ha.continuousAt (U.isOpen.mem_nhds hx))
    · have h0 : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hχU h)
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [h0] with y hy
      simp only [ha'def, hy, Pi.zero_apply, zero_mul]
  have ha'cs : HasCompactSupport a' :=
    hVc.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_mul_subset_left (f := χ) (g := a)).trans (hχV.trans subset_closure))
  have hunif := ha'cs.uniformContinuous_of_continuous ha'c
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hunif ε hε
  let φ : ContDiffBump (0 : E) := ⟨δ / 2, δ, by positivity, by linarith⟩
  refine ⟨mollify volume a' φ, contDiff_mollify volume ha'c.locallyIntegrable φ, fun x hx => ?_⟩
  have hdist : dist (mollify volume a' φ x) (a' x) ≤ ε := by
    rw [mollify_eq_convolution]
    refine ContDiffBump.dist_normed_convolution_le ha'c.aestronglyMeasurable fun y hy => ?_
    exact (hmod (Metric.mem_ball.mp hy)).le
  have hax : a' x = a x := by simp only [ha'def, hχ1 x hx, one_mul]
  rw [hax, Real.dist_eq] at hdist
  exact hdist

end Approximation

/-! ### The multiplication argument -/

section Multiplication

variable {q : ℕ}

/-- **The multiplication argument**: if positive currents `S_k → S` weakly and Borel functions
`a_k`, bounded on the compact subsets of `U`, converge locally uniformly on `U` to a function `a`
continuous on `U`, then `a_k S_k → a S` weakly. -/
theorem weakTendsto_mulBorel {S : ℕ → LocalProductCurrent n U q}
    {S₀ : LocalProductCurrent n U q} (hS : ∀ k, IsPositive (S k)) (hconv : WeakTendsto S S₀)
    {a : ℕ → E → ℝ} {a₀ : E → ℝ} (ha : ∀ k, Measurable (a k))
    (hab : ∀ k, IsLocallyBoundedOn (a k) U) (ha₀ : Measurable a₀) (ha₀c : ContinuousOn a₀ U)
    (hloc : TendstoLocallyUniformlyOn a a₀ atTop U) :
    WeakTendsto (fun k => mulBorel (S k) (a k)) (mulBorel S₀ a₀) := by
  have hS₀ := isPositive_of_weakTendsto hS hconv
  have ha₀b : IsLocallyBoundedOn a₀ U := fun K hK hKU => by
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (ha₀c.mono hKU)
    exact ⟨A, fun x hx => by simpa [Real.norm_eq_abs] using hA x hx⟩
  intro γ φ
  set K := tsupport φ with hKdef
  have hK : IsCompact K := φ.hasCompactSupport
  have hKU : K ⊆ U := φ.tsupport_subset
  have hφ0 : ∀ x ∉ K, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨C, hC0, h₁, h₂⟩ := exists_orderUnit γ.2
  obtain ⟨M, hM⟩ := exists_traceMeasure_le_of_weakTendsto hS hconv hK hKU
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, ∀ x, |φ x| ≤ Φ := by
    obtain ⟨Φ, hΦ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    exact ⟨Φ, fun x => by simpa [Real.norm_eq_abs] using hΦ x⟩
  have hΦ0 : 0 ≤ Φ := (abs_nonneg _).trans (hΦ 0)
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg.trans (hM 0)
  set σ₀ := (hS₀.traceMeasure K).toReal
  have hσ₀ : 0 ≤ σ₀ := ENNReal.toReal_nonneg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set L : ℝ := Φ * C * (M + σ₀) + 1 with hLdef
  have hL : 0 < L := by positivity
  set δ : ℝ := ε / (4 * L) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hg, hga⟩ := exists_contDiff_abs_sub_le ha₀c hK hKU hδ
  have hgb : IsLocallyBoundedOn g U := fun K' hK' _ => by
    obtain ⟨A, hA⟩ := hK'.exists_bound_of_continuousOn hg.continuous.continuousOn
    exact ⟨A, fun x hx => by simpa [Real.norm_eq_abs] using hA x hx⟩
  -- the middle term converges
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hconv γ (mulTest hg φ)) (ε / 4) (by positivity)
  -- the weights converge uniformly on `K`
  have hunif : TendstoUniformlyOn a a₀ atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen).mp hloc K hKU hK
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hunif δ hδ)
  refine ⟨max N₁ N₂, fun k hk => ?_⟩
  have hk₁ : N₁ ≤ k := le_of_max_le_left hk
  have hk₂ : N₂ ≤ k := le_of_max_le_right hk
  -- the three terms
  have hmid : |S k γ (mulTest hg φ) - S₀ γ (mulTest hg φ)| < ε / 4 := by
    simpa [Real.dist_eq] using hN₁ k hk₁
  have hrepk : S k γ (mulTest hg φ) = ∫ x, (φ x * g x) * (hS k).density γ x ∂(hS k).traceMeasure
    := by
    rw [(hS k).apply_eq_integral_density]
    rfl
  have hrep₀ : S₀ γ (mulTest hg φ) = ∫ x, (φ x * g x) * hS₀.density γ x ∂hS₀.traceMeasure := by
    rw [hS₀.apply_eq_integral_density]
    rfl
  have hintk : ∀ w : E → ℝ, Measurable w → IsLocallyBoundedOn w U →
      Integrable (fun x => (φ x * w x) * (hS k).density γ x) (hS k).traceMeasure :=
    fun w hw hwb => ((hS k).integrable_mul_density hw hwb γ φ).congr
      (Eventually.of_forall fun x => by simp only; ring)
  have hint₀ : ∀ w : E → ℝ, Measurable w → IsLocallyBoundedOn w U →
      Integrable (fun x => (φ x * w x) * hS₀.density γ x) hS₀.traceMeasure :=
    fun w hw hwb => (hS₀.integrable_mul_density hw hwb γ φ).congr
      (Eventually.of_forall fun x => by simp only; ring)
  have h1 : |mulBorel (S k) (a k) γ φ - S k γ (mulTest hg φ)| ≤ Φ * (2 * δ) * C * M := by
    rw [mulBorel_apply (hS k) (ha k) (hab k), hrepk]
    have e : ∫ x, φ x * (a k x * (hS k).density γ x) ∂(hS k).traceMeasure -
        ∫ x, (φ x * g x) * (hS k).density γ x ∂(hS k).traceMeasure =
        ∫ x, (φ x * (a k x - g x)) * (hS k).density γ x ∂(hS k).traceMeasure := by
      rw [← integral_sub (((hintk (a k) (ha k) (hab k))).congr
          (Eventually.of_forall fun x => by simp only; ring))
        (hintk g hg.continuous.measurable hgb)]
      congr 1
      funext x
      ring
    rw [e]
    refine (abs_integral_mul_density_le (hS k) γ
      (abs_density_le_of_orderUnit (hS k) γ h₁ h₂) hK hKU (B := Φ * (2 * δ)) (fun x hx => ?_)
      (fun x hx => by rw [hφ0 x hx, zero_mul])).trans ?_
    · rw [abs_mul]
      refine mul_le_mul (hΦ x) ?_ (abs_nonneg _) hΦ0
      have e1 := hN₂ k hk₂ x hx
      rw [Real.dist_eq] at e1
      have e2 := hga x hx
      calc |a k x - g x| = |(a k x - a₀ x) + (a₀ x - g x)| := by ring_nf
        _ ≤ |a k x - a₀ x| + |a₀ x - g x| := abs_add_le _ _
        _ ≤ δ + δ := by
            refine add_le_add ?_ ?_
            · rw [abs_sub_comm]; exact e1.le
            · rw [abs_sub_comm]; exact e2
        _ = 2 * δ := by ring
    · have := hM k
      have hpos : 0 ≤ Φ * (2 * δ) * C := by positivity
      exact mul_le_mul_of_nonneg_left this hpos
  have h3 : |S₀ γ (mulTest hg φ) - mulBorel S₀ a₀ γ φ| ≤ Φ * δ * C * σ₀ := by
    rw [mulBorel_apply hS₀ ha₀ ha₀b, hrep₀]
    have e : ∫ x, (φ x * g x) * hS₀.density γ x ∂hS₀.traceMeasure -
        ∫ x, φ x * (a₀ x * hS₀.density γ x) ∂hS₀.traceMeasure =
        ∫ x, (φ x * (g x - a₀ x)) * hS₀.density γ x ∂hS₀.traceMeasure := by
      rw [← integral_sub (hint₀ g hg.continuous.measurable hgb) ((hint₀ a₀ ha₀ ha₀b).congr
          (Eventually.of_forall fun x => by simp only; ring))]
      congr 1
      funext x
      ring
    rw [e]
    refine abs_integral_mul_density_le hS₀ γ (abs_density_le_of_orderUnit hS₀ γ h₁ h₂) hK hKU
      (B := Φ * δ) (fun x hx => ?_) (fun x hx => by rw [hφ0 x hx, zero_mul])
    rw [abs_mul]
    exact mul_le_mul (hΦ x) (hga x hx) (abs_nonneg _) hΦ0
  rw [Real.dist_eq]
  have htri : |mulBorel (S k) (a k) γ φ - mulBorel S₀ a₀ γ φ| ≤
      |mulBorel (S k) (a k) γ φ - S k γ (mulTest hg φ)| +
        |S k γ (mulTest hg φ) - S₀ γ (mulTest hg φ)| +
          |S₀ γ (mulTest hg φ) - mulBorel S₀ a₀ γ φ| := by
    have := abs_add_three (mulBorel (S k) (a k) γ φ - S k γ (mulTest hg φ))
      (S k γ (mulTest hg φ) - S₀ γ (mulTest hg φ)) (S₀ γ (mulTest hg φ) - mulBorel S₀ a₀ γ φ)
    ring_nf at this ⊢
    linarith
  have hsmall : Φ * (2 * δ) * C * M + Φ * δ * C * σ₀ ≤ ε / 2 := by
    have hδL : δ * L = ε / 4 := by
      rw [hδdef]; field_simp
    have : Φ * (2 * δ) * C * M + Φ * δ * C * σ₀ ≤ 2 * (δ * L) := by
      rw [hLdef]
      nlinarith [mul_nonneg (mul_nonneg hΦ0 hδ.le) hC0, mul_nonneg hδ.le hσ₀, hM0]
    linarith
  linarith

end Multiplication

/-! ### Continuity of the recursive product -/

section Recursion

/-- **Continuity of the recursive Bedford--Taylor product for continuous potentials**
(`bt:continuous-convergence`, `demailly-cadg:III.3.6`): if positive closed currents `T_k → T`
weakly and locally bounded PSH functions `u_j^k` converge locally uniformly on `U` to functions
`u_j` continuous on `U`, then `B(u^k; T_k) → B(u; T)` weakly. -/
theorem weakTendsto_btProduct : ∀ (q r : ℕ) (u : ℕ → Fin q → E → ℝ) (u₀ : Fin q → E → ℝ)
    (T : ℕ → LocalProductCurrent n U (r + q)) (T₀ : LocalProductCurrent n U (r + q)),
    (∀ k, IsPositive (T k)) → (∀ k, IsClosedAny (r + q) (T k)) → WeakTendsto T T₀ →
    (∀ k i, IsLocallyBoundedPshOn U (u k i)) → (∀ i, ContinuousOn (u₀ i) U) →
    (∀ i, TendstoLocallyUniformlyOn (fun k => u k i) (u₀ i) atTop U) →
    WeakTendsto (fun k => btProduct q r (u k) (T k)) (btProduct q r u₀ T₀)
  | 0, _, _, _, _, _, _, _, h, _, _, _ => h
  | q + 1, r, u, u₀, T, T₀, hT, hTc, h, hu, hu₀, hconv => by
    simp only [btProduct_succ]
    have hstep : WeakTendsto (fun k => ddcMul (T k) (u k (Fin.last q)))
        (ddcMul T₀ (u₀ (Fin.last q))) := by
      refine weakTendsto_ddc (weakTendsto_mulBorel hT h
        (fun k => measurable_indicator_of_isLocallyBoundedPshOn (hu k _))
        (fun k => isLocallyBoundedOn_indicator (hu k _))
        (LocalBedfordTaylorSmooth.measurable_indicator_of_continuousOn (hu₀ _))
        ((hu₀ (Fin.last q)).congr fun _x hx => Set.indicator_of_mem hx _) ?_)
      exact ((hconv (Fin.last q)).congr fun _k _x hx => (Set.indicator_of_mem hx
        _).symm).congr_right
        fun _x hx => (Set.indicator_of_mem hx _).symm
    exact weakTendsto_btProduct q r (fun k => Fin.init (u k)) (Fin.init u₀) _ _
      (fun k => (isPositive_ddcMul (hT k) (hTc k) (hu k _)).1)
      (fun k => (isPositive_ddcMul (hT k) (hTc k) (hu k _)).2) hstep
      (fun k i => hu k _) (fun i => hu₀ _) (fun i => hconv _)

/-- The limit product `B(u; T)` is positive and closed. -/
theorem isPositive_btProduct_of_weakTendsto (q r : ℕ) (u : ℕ → Fin q → E → ℝ)
    (u₀ : Fin q → E → ℝ) (T : ℕ → LocalProductCurrent n U (r + q))
    (T₀ : LocalProductCurrent n U (r + q)) (hT : ∀ k, IsPositive (T k))
    (hTc : ∀ k, IsClosedAny (r + q) (T k)) (h : WeakTendsto T T₀)
    (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i)) (hu₀ : ∀ i, ContinuousOn (u₀ i) U)
    (hconv : ∀ i, TendstoLocallyUniformlyOn (fun k => u k i) (u₀ i) atTop U) :
    IsPositive (btProduct q r u₀ T₀) ∧ IsClosedAny r (btProduct q r u₀ T₀) := by
  have hlim := weakTendsto_btProduct q r u u₀ T T₀ hT hTc h hu hu₀ hconv
  exact ⟨isPositive_of_weakTendsto (fun k => (isPositive_btProduct q r (u k) (T k) (hT k) (hTc k)
      (hu k)).1) hlim,
    isClosedAny_of_weakTendsto (fun k => (isPositive_btProduct q r (u k) (T k) (hT k) (hTc k)
      (hu k)).2) hlim⟩

/-- **The weighted form** (`bt:continuous-convergence`):
    `u_1^k B(u_2^k, …; T_k) → u_1 B(u_2, …; T)`
weakly, the weight `u_1` being extended by zero off `U`. -/
theorem weakTendsto_mulBorel_btProduct (q r : ℕ) (w : ℕ → E → ℝ) (w₀ : E → ℝ)
    (u : ℕ → Fin q → E → ℝ) (u₀ : Fin q → E → ℝ) (T : ℕ → LocalProductCurrent n U (r + q))
    (T₀ : LocalProductCurrent n U (r + q)) (hT : ∀ k, IsPositive (T k))
    (hTc : ∀ k, IsClosedAny (r + q) (T k)) (h : WeakTendsto T T₀)
    (hw : ∀ k, IsLocallyBoundedPshOn U (w k)) (hw₀ : ContinuousOn w₀ U)
    (hwconv : TendstoLocallyUniformlyOn w w₀ atTop U)
    (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i)) (hu₀ : ∀ i, ContinuousOn (u₀ i) U)
    (hconv : ∀ i, TendstoLocallyUniformlyOn (fun k => u k i) (u₀ i) atTop U) :
    WeakTendsto (fun k => mulBorel (btProduct q r (u k) (T k)) ((U : Set E).indicator (w k)))
      (mulBorel (btProduct q r u₀ T₀) ((U : Set E).indicator w₀)) :=
  weakTendsto_mulBorel (fun k => (isPositive_btProduct q r (u k) (T k) (hT k) (hTc k) (hu k)).1)
    (weakTendsto_btProduct q r u u₀ T T₀ hT hTc h hu hu₀ hconv)
    (fun k => measurable_indicator_of_isLocallyBoundedPshOn (hw k))
    (fun k => isLocallyBoundedOn_indicator (hw k))
    (LocalBedfordTaylorSmooth.measurable_indicator_of_continuousOn hw₀)
    (hw₀.congr fun _x hx => Set.indicator_of_mem hx _)
    ((hwconv.congr fun _k _x hx => (Set.indicator_of_mem hx _).symm).congr_right
      fun _x hx => (Set.indicator_of_mem hx _).symm)

end Recursion

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
