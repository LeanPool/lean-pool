/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Atoms.AtomComposition
public import LeanPool.FunctionSpaces.Analysis.Differences.DomainModuli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Invariance of Besov spaces under smooth changes of variables

Let `Ω` be a measurable convex set with nonempty interior and `T` a smooth change of variables with
a cut-off on `Ω` (`Rd.CutoffDiffeo`), acting by `T f = 1_{Ω ∩ U} (χ f) ∘ Φ`.

* `T` respects null sets on `Ω` (`Rd.CutoffDiffeo.apply_ae_eq`): `Ψ` is differentiable on the
  compact `K₀`, so it maps null sets to null sets (Mathlib's
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`).
* `T` is a bounded operator on `L_p` (`Rd.CutoffDiffeo.applyLp`), by the change of variables
  `x = Ψ(y)` on `K₀` (Mathlib's `lintegral_image_eq_lintegral_abs_det_fderiv_mul`):
  `∫ |T g|^p = ∫_{K₀} |det DΨ| |χ|^p |g|^p`.
* **Transport of smooth atoms** (`Rd.CutoffDiffeo.exists_transported_atoms`): the images of smooth
  atoms on `V` centred at the cell centres are regular atoms on `Ω` whose new centres `Ψ(y)`,
  `y ∈ K₀` near the old centre, have bounded overlap, because `Φ` is Lipschitz on `Ψ(K₀)`.
* **Invariance** (`Rd.CutoffDiffeo.modNormOn_applyLp_le`): for `1 ≤ p < ∞`, `0 < s < r` and
  `1 ≤ q ≤ ∞`,

  `‖1_Ω T F‖_p + ‖(2^(ks) ω_r(T F, 2^(-k), Ω)_p)_k‖_{ℓ_q}`
  `  ≤ C (‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q})`.

  Decompose `F` into smooth cell atoms of order `r`
  (`Rd.LocalMeansBump.atomic_decomposition_smooth`), transport them, and synthesise on `Ω`
  (`Rd.modNormOn_le_coeffNorm`).
* **The extension property** (`Rd.HasBesovExtension`): every function of finite intrinsic Besov
  quasi-norm on a measurable set (`Rd.modNormOn`) extends to `V` with a bound. It is the same for
  sets that agree up to a null set (`Rd.HasBesovExtension.congr_set`), and with it the order of
  the differences does not matter (`Rd.HasBesovExtension.modNormOn_order_le`).
* **Besov domains** (`Rd.BesovDomain`): convex closed sets with nonempty interior with the
  extension property (`Rd.BesovDomain.of_hasBesovExtension`, up to null sets
  `Rd.BesovDomain.of_ae_eq`). On a Besov domain the intrinsic quasi-norm is invariant
  (`Rd.CutoffDiffeo.modNormOn_applyLp_le_modNormOn`), and the order of the differences does not
  matter (`Rd.BesovDomain.modNormOn_order_le`); `V` itself is a Besov domain, and so are the
  closed half-space, the quadrant, closed balls of positive radius, the closed unit cube and the
  closures of nonempty bounded open convex sets (`FunctionSpaces.Domains.Lipschitz.HalfSpace`,
  `FunctionSpaces.Domains.Lipschitz.BesovDomains`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal NNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Linearity -/

namespace CutoffDiffeo

section Linear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Set V} (T : CutoffDiffeo Ω)

/-- `T (g₁ + g₂) = T g₁ + T g₂`. -/
theorem apply_add (g₁ g₂ : V → ℂ) : T.apply (g₁ + g₂) = T.apply g₁ + T.apply g₂ := by
  funext x
  by_cases hx : x ∈ Ω ∩ T.U
  · simp only [apply, Set.indicator_of_mem hx, Pi.add_apply, mul_add]
  · simp only [apply, Set.indicator_of_notMem hx, Pi.add_apply, add_zero]

/-- `T (c g) = c T g`. -/
theorem apply_smul (c : ℂ) (g : V → ℂ) : T.apply (c • g) = c • T.apply g := by
  funext x
  by_cases hx : x ∈ Ω ∩ T.U
  · simp only [apply, Set.indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [apply, Set.indicator_of_notMem hx, Pi.smul_apply, smul_zero]

/-- **`T` commutes with series** whose terms it kills where the coefficients change: if for every
`m` either `λ'_m = λ_m` or `T a_m = 0`, then `T (∑_m λ_m a_m) = ∑_m λ'_m T a_m`. -/
theorem apply_tsum {ι : Type*} (coef coef' : ι → ℂ) (a : ι → V → ℂ)
    (h : ∀ m, coef' m = coef m ∨ T.apply (a m) = 0) (x : V) :
    T.apply (fun y => ∑' m, coef m * a m y) x = ∑' m, coef' m * T.apply (a m) x := by
  by_cases hx : x ∈ Ω ∩ T.U
  · have e : ∀ m, T.apply (a m) x = T.chi (T.Phi x) * a m (T.Phi x) := fun m => by
      rw [apply, Set.indicator_of_mem hx]
    rw [apply, Set.indicator_of_mem hx, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rcases h m with h | h
    · rw [h, e]
      ring
    · have h' := congrFun h x
      rw [Pi.zero_apply, e] at h'
      rw [e, h', mul_zero]
      calc T.chi (T.Phi x) * (coef m * a m (T.Phi x)) = coef m * (T.chi (T.Phi x) * a m (T.Phi
        x)) := by
            ring
        _ = 0 := by rw [h', mul_zero]
  · rw [apply, Set.indicator_of_notMem hx]
    symm
    refine (tsum_congr fun m => ?_).trans tsum_zero
    rw [apply, Set.indicator_of_notMem hx, mul_zero]

end Linear

/-! ### Null sets and the change of variables -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Set V} (T : CutoffDiffeo Ω)

/-- **`T` respects null sets on `Ω`**: if `g₁ = g₂` almost everywhere on `Ω`, then
`T g₁ = T g₂` almost everywhere, since `Ψ` maps the null set `K₀ ∩ {g₁ ≠ g₂}` to a null set. -/
theorem apply_ae_eq {g₁ g₂ : V → ℂ} (h : ∀ᵐ y ∂volume, y ∈ Ω → g₁ y = g₂ y) :
    T.apply g₁ =ᵐ[volume] T.apply g₂ := by
  set N := {y | y ∈ Ω ∧ g₁ y ≠ g₂ y}
  have hN : volume N = 0 := by
    rw [ae_iff] at h
    exact measure_mono_null (fun y hy => fun h' => hy.2 (h' hy.1)) h
  have hΨN : volume (T.Psi '' (T.K0 ∩ N)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((T.contDiffOn_Psi.differentiableOn (by simp)).mono
        (inter_subset_left.trans T.K0_subset))
      (measure_mono_null inter_subset_right hN)
  refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hΨN)
  have hx' : T.apply g₁ x ≠ T.apply g₂ x := hx
  by_cases hxs : x ∈ Ω ∩ T.U
  · rw [apply, apply, Set.indicator_of_mem hxs, Set.indicator_of_mem hxs] at hx'
    have hΦK : T.Phi x ∈ T.K0 := by
      by_contra hΦK
      rw [T.chi_eq_zero _ (T.mapsTo_Phi hxs).1 hΦK, zero_mul, zero_mul] at hx'
      exact hx' rfl
    have hne : g₁ (T.Phi x) ≠ g₂ (T.Phi x) := fun he => hx' (by rw [he])
    exact ⟨T.Phi x, ⟨hΦK, (T.mapsTo_Phi hxs).1, hne⟩, T.left_inv x hxs⟩
  · rw [apply, apply, Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs] at hx'
    exact absurd rfl hx'

/-- `T g` is almost everywhere strongly measurable with `g`. -/
theorem aestronglyMeasurable_apply (hΩm : MeasurableSet Ω) {g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) : AEStronglyMeasurable (T.apply g) volume := by
  have hSm : MeasurableSet (Ω ∩ T.U) := hΩm.inter T.isOpen_U.measurableSet
  have h1 : AEStronglyMeasurable (T.apply hg.mk) volume := by
    refine (aestronglyMeasurable_indicator_iff hSm).2 ?_
    have hΦ : AEMeasurable T.Phi (volume.restrict (Ω ∩ T.U)) :=
      T.contDiffOn_Phi.continuousOn.aemeasurable hSm
    have hχ : ContinuousOn (fun x => T.chi (T.Phi x)) (Ω ∩ T.U) :=
      T.contDiffOn_chi.continuousOn.comp T.contDiffOn_Phi.continuousOn T.mapsTo_Phi
    exact (hχ.aestronglyMeasurable hSm).mul
      (hg.stronglyMeasurable_mk.aestronglyMeasurable.comp_aemeasurable hΦ)
  exact h1.congr (T.apply_ae_eq (hg.ae_eq_mk.mono fun y hy _ => hy.symm))

variable (hΩ : Convex ℝ Ω) (hint : (interior Ω).Nonempty)
include hΩ hint

omit hΩ hint in
/-- **The change of variables** `x = Ψ(y)`: for `e > 0`,
`∫ |T g|^e = ∫_{K₀} |det DΨ(y)| |χ(y)|^e |g(y)|^e dy`. -/
theorem lintegral_apply_eq (g : V → ℂ) {e : ℝ} (he : 0 < e) :
    ∫⁻ x, ‖T.apply g x‖ₑ ^ e = ∫⁻ y in T.K0,
      ENNReal.ofReal |(fderivWithin ℝ T.Psi (Ω ∩ T.U') y).det| * (‖T.chi y‖ₑ ^ e * ‖g y‖ₑ ^ e) := by
  have hderiv : ∀ y ∈ T.K0,
      HasFDerivWithinAt T.Psi (fderivWithin ℝ T.Psi (Ω ∩ T.U') y) T.K0 y := fun y hy =>
    ((T.contDiffOn_Psi.differentiableOn (by simp) y
      (T.K0_subset hy)).hasFDerivWithinAt).mono T.K0_subset
  have hinj : InjOn T.Psi T.K0 := fun y₁ h₁ y₂ h₂ h => by
    rw [← T.right_inv y₁ (T.K0_subset h₁), h, T.right_inv y₂ (T.K0_subset h₂)]
  rw [← setLIntegral_eq_of_support_subset (s := T.carrier) fun x hx => ?_]
  · rw [carrier, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      T.isCompact_K0.measurableSet hderiv hinj]
    refine setLIntegral_congr_fun T.isCompact_K0.measurableSet fun y hy => ?_
    rw [apply, Set.indicator_of_mem (T.mapsTo_Psi (T.K0_subset hy)), T.right_inv y (T.K0_subset hy),
      eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ he.le]
  · by_contra hxc
    exact hx (show ‖T.apply g x‖ₑ ^ e = 0 by
      rw [T.apply_eq_zero_of_notMem g hxc, eNorm_zero, ENNReal.zero_rpow_of_pos he])

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Jacobian of `Ψ` is bounded on `K₀`. -/
theorem exists_det_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ T.K0, |(fderivWithin ℝ T.Psi (Ω ∩ T.U') y).det| ≤ B := by
  obtain ⟨B, hB⟩ := T.isCompact_K0.exists_bound_of_continuousOn
    ((ContinuousLinearMap.continuous_det.comp_continuousOn
      (T.contDiffOn_Psi.continuousOn_fderivWithin (T.uniqueDiffOn_target hΩ hint)
        (by exact_mod_cast le_top))).mono T.K0_subset)
  exact ⟨max B 0, le_max_right _ _, fun y hy =>
    ((Real.norm_eq_abs _).symm.trans_le (hB y hy)).trans (le_max_left _ _)⟩

/-- **`T` is bounded on `L_p`**: `‖T g‖_p ≤ C ‖g‖_p` for `0 < p < ∞`. -/
theorem eLpNorm_apply_le (hΩm : MeasurableSet Ω) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, AEStronglyMeasurable g volume →
      eLpNorm (T.apply g) p volume ≤ C * eLpNorm g p volume := by
  obtain ⟨B, hB0, hB⟩ := T.exists_det_bound hΩ hint
  obtain ⟨M, hM0, hM⟩ := T.exists_iteratedFDerivWithin_chi_bound hΩ hint 0
  set e := p.toReal
  have he : 0 < e := ENNReal.toReal_pos hp0 hp
  set D := ENNReal.ofReal B * ENNReal.ofReal M ^ e
  have hD : D ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg he.le ENNReal.ofReal_ne_top)
  refine ⟨D ^ (1 / e), ENNReal.rpow_ne_top_of_nonneg (by positivity) hD, fun g hg => ?_⟩
  rw [← ENNReal.rpow_le_rpow_iff he, ENNReal.mul_rpow_of_nonneg _ _ he.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel he.ne', ENNReal.rpow_one,
    eLpNorm_rpow_eq (T.aestronglyMeasurable_apply hΩm hg) hp0 hp, eLpNorm_rpow_eq hg hp0 hp,
    T.lintegral_apply_eq g he]
  calc ∫⁻ y in T.K0, ENNReal.ofReal |(fderivWithin ℝ T.Psi (Ω ∩ T.U') y).det| *
        (‖T.chi y‖ₑ ^ e * ‖g y‖ₑ ^ e)
      ≤ ∫⁻ y in T.K0, D * ‖g y‖ₑ ^ e := by
        refine setLIntegral_mono' T.isCompact_K0.measurableSet fun y hy => ?_
        have hχ : ‖T.chi y‖ₑ ≤ ENNReal.ofReal M := by
          have := hM 0 le_rfl y (T.K0_subset hy)
          rw [norm_iteratedFDerivWithin_zero] at this
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal this
        rw [← mul_assoc]
        exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (hB y hy))
          (ENNReal.rpow_le_rpow hχ he.le)) le_rfl
    _ ≤ ∫⁻ y, D * ‖g y‖ₑ ^ e := setLIntegral_le_lintegral _ _
    _ = D * ∫⁻ y, ‖g y‖ₑ ^ e := lintegral_const_mul' _ _ hD

/-! ### `T` as an operator on `L_p` -/

variable (hΩm : MeasurableSet Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
include hΩm hp

/-- `T g ∈ L_p` for `g ∈ L_p`. -/
theorem memLp_apply {g : V → ℂ} (hg : MemLp g p volume) : MemLp (T.apply g) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨C, hC, hle⟩ := T.eLpNorm_apply_le hΩ hint hΩm hp0 hp
  exact (hle g hg.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top hC.lt_top hg)

/-- **The change of variables with a cut-off as a bounded operator on `L_p`**. -/
noncomputable def applyLp : Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  LinearMap.mkContinuous
    { toFun := fun g => (T.memLp_apply hΩ hint hΩm hp (Lp.memLp g)).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (T.memLp_apply hΩ hint hΩm hp (Lp.memLp (f + g)))
        have e2 := MemLp.coeFn_toLp (T.memLp_apply hΩ hint hΩm hp (Lp.memLp f))
        have e3 := MemLp.coeFn_toLp (T.memLp_apply hΩ hint hΩm hp (Lp.memLp g))
        have e5 := Lp.coeFn_add ((T.memLp_apply hΩ hint hΩm hp (Lp.memLp f)).toLp _)
          ((T.memLp_apply hΩ hint hΩm hp (Lp.memLp g)).toLp _)
        have e6 := T.apply_ae_eq ((Lp.coeFn_add f g).mono fun y hy _ => hy)
        filter_upwards [e1, e2, e3, e5, e6] with x h1 h2 h3 h5 h6
        rw [h1, h5, Pi.add_apply, h2, h3, h6, apply_add, Pi.add_apply]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (T.memLp_apply hΩ hint hΩm hp (Lp.memLp (c • f)))
        have e2 := MemLp.coeFn_toLp (T.memLp_apply hΩ hint hΩm hp (Lp.memLp f))
        have e4 := Lp.coeFn_smul c ((T.memLp_apply hΩ hint hΩm hp (Lp.memLp f)).toLp _)
        have e6 := T.apply_ae_eq ((Lp.coeFn_smul c f).mono fun y hy _ => hy)
        filter_upwards [e1, e2, e4, e6] with x h1 h2 h4 h6
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, h6, apply_smul, Pi.smul_apply] }
    (Classical.choose (T.eLpNorm_apply_le hΩ hint hΩm
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp)).toReal
    (fun g => by
      obtain ⟨hC, hle⟩ := Classical.choose_spec (T.eLpNorm_apply_le hΩ hint hΩm
        (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp)
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC (Lp.eLpNorm_ne_top g))
        (hle g (Lp.aestronglyMeasurable g)))

/-- The operator acts by `T`, almost everywhere. -/
theorem applyLp_ae (g : Lp ℂ p (volume : Measure V)) :
    T.applyLp hΩ hint hΩm hp g =ᵐ[volume] T.apply g :=
  MemLp.coeFn_toLp (T.memLp_apply hΩ hint hΩm hp (Lp.memLp g))

omit hp [Fact (1 ≤ p)] in
/-- **Transport of smooth atoms**: for smooth atoms on `V` of order `r ≥ 1`, radius factor `d` and
constant `A`, centred at the cell centres, there are `d'`, `C' < ∞` and `N` such that for all
coefficients `λ` the images `T a_{j,m}` are regular atoms on `Ω` of order and exponent `r` with
radius factor `d'`, constant `C'` and suitable centres, and coefficients `λ'` with `|λ'| ≤ |λ|`,
`λ' = λ` unless `T a_{j,m} = 0`, and at most `N` centres with `λ' ≠ 0` in each ball of radius
`(d' + r) 2^(-j)`. -/
theorem exists_transported_atoms {r : ℕ} (hr : 1 ≤ r) {d A : ℝ} (hd : 0 ≤ d) (hA : 0 ≤ A) :
    ∃ (d' : ℝ) (C' : ℝ≥0∞) (N : ℕ), C' ≠ ∞ ∧
      ∀ (a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ) (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ),
        (∀ j m, IsSmoothAtom Set.univ r d A j (cellCenter j m) (a j m)) →
        ∃ (c' : ℕ → (Fin (finrank ℝ V) → ℤ) → V) (coef' : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ),
          (∀ j x (S : Finset (Fin (finrank ℝ V) → ℤ)),
            (∀ m ∈ S, coef' j m ≠ 0 ∧ ‖x - c' j m‖ ≤ (d' + r) / 2 ^ j) → S.card ≤ N) ∧
          (∀ j m, IsRegularAtomOn Ω p r r d' C' j (c' j m) (T.apply (a j m))) ∧
          (∀ j m, ‖coef' j m‖ₑ ≤ ‖coef j m‖ₑ) ∧
          (∀ j m, coef' j m = coef j m ∨ T.apply (a j m) = 0) := by
  classical
  obtain ⟨L, A', hL, hA', hT⟩ := T.isSmoothAtom_apply hΩ hΩm hint r
  obtain ⟨LΦ, hLΦ⟩ := T.exists_lipschitzOnWith_Phi hΩ
  set d' := 2 * L * d
  have hd' : 0 ≤ d' := by positivity
  have hρ : 0 ≤ d' + r := by positivity
  refine ⟨d', ENNReal.ofReal (2 ^ r * (r : ℝ) ^ (r + 1) * (A' * A)) *
      (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d' ^ finrank ℝ V) * volume (ball (0 : V) 1))) ^
        (1 / p.toReal), ⌈(2 * (2 * LΦ * (d' + r) + d) + 2) ^ finrank ℝ V⌉₊,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne))),
    fun a coef ha => ?_⟩
  -- the cells that meet `K₀`, and a point of `K₀` near their centre
  set near : ℕ → (Fin (finrank ℝ V) → ℤ) → Prop :=
    fun j m => ∃ y ∈ T.K0, ‖y - cellCenter j m‖ ≤ d / 2 ^ j
  have hfar : ∀ j m, ¬ near j m → T.apply (a j m) = 0 := fun j m h => funext fun x =>
    T.apply_eq_zero_of_forall_far (ha j m).eq_zero
      (fun y hy => lt_of_not_ge fun hle => h ⟨y, hy, hle⟩) x
  refine ⟨fun j m => if h : near j m then T.Psi h.choose else 0,
    fun j m => if near j m then coef j m else 0, fun j x S hS => ?_, fun j m => ?_,
    fun j m => ?_, fun j m => ?_⟩
  · -- bounded overlap
    have hnear : ∀ m ∈ S, near j m := fun m hm => by
      by_contra h
      exact (hS m hm).1 (ite_eq_right h)
    refine card_le_of_lipschitz_centres hLΦ j hd hρ
      (z := fun m => if h : near j m then T.Psi h.choose else 0) x S fun m hm => ?_
    have hS' := (hS m hm).2
    dsimp only at hS' ⊢
    rw [dite_eq_left (hnear m hm)] at hS' ⊢
    obtain ⟨hy, hyc⟩ := (hnear m hm).choose_spec
    exact ⟨⟨_, hy, rfl⟩, by rwa [T.right_inv _ (T.K0_subset hy)], hS'⟩
  · -- the atoms
    by_cases h : near j m
    · dsimp only
      rw [dite_eq_left h]
      obtain ⟨hy, hyc⟩ := h.choose_spec
      exact isRegularAtomOn_of_isSmoothAtom hΩ hΩm hint hr le_rfl hd' (mul_nonneg hA' hA)
        (hT hA (ha j m) _ hy hyc)
    · rw [hfar j m h]
      exact isRegularAtomOn_of_isSmoothAtom hΩ hΩm hint hr le_rfl hd' (mul_nonneg hA' hA)
        (isSmoothAtom_zero Ω r d' (mul_nonneg hA' hA) j _)
  · dsimp only
    by_cases h : near j m
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, eNorm_zero]
      exact zero_le
  · by_cases h : near j m
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (hfar j m h)

/-- **Invariance under a smooth change of variables with a cut-off**: for `1 ≤ p < ∞`,
`0 < s < r` and `1 ≤ q ≤ ∞` there is `C < ∞` such that for all `F ∈ L_p(V)`
`‖1_Ω T F‖_p + ‖(2^(ks) ω_r(T F, 2^(-k), Ω)_p)_k‖_{ℓ_q} ≤
C (‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q})`. The smooth cell atoms of `F`
(`Rd.LocalMeansBump.atomic_decomposition_smooth`) are transported by `T`
(`Rd.CutoffDiffeo.exists_transported_atoms`) and synthesised on `Ω`
(`Rd.modNormOn_le_coeffNorm`). -/
theorem modNormOn_applyLp_le {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞}
    (hq : 1 ≤ q) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : Lp ℂ p (volume : Measure V),
      modNormOn hΩm r s q (T.applyLp hΩ hint hΩm hp F) ≤
        C * (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  have hp1 : 1 ≤ p := Fact.out
  set b := LocalMeansBump.std (V := V)
  obtain ⟨A, hA, hdec⟩ := b.atomic_decomposition_smooth hp r r
  have hd : 0 ≤ 2 * (r : ℝ) * b.radius + finrank ℝ V :=
    add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg r)) b.radius_nonneg)
      (Nat.cast_nonneg _)
  obtain ⟨d', C', N, hC', htr⟩ := T.exists_transported_atoms hΩ hint hΩm hr hd hA (p := p)
  refine ⟨atomSynthConst p N C' r s r * b.upperConst r s, ENNReal.mul_ne_top
    (atomSynthConst_ne_top hp1 N hC' r hs hsr) (b.upperConst_ne_top r s), fun F => ?_⟩
  obtain ⟨ha, hsum, hcoef⟩ := hdec F
  obtain ⟨c', coef', hN, ha', hle, hor⟩ :=
    htr _ (fun j => cellCoef p j (b.localMean hp r j F)) ha
  -- the transported level sums
  have hf : ∀ j, ∀ᵐ x ∂volume, T.applyLp hΩ hint hΩm hp
      (convLp hp (b.integrable_dual r j) (b.localMean hp r j F)) x =
        ∑' m, coef' j m * T.apply (cellAtom p (b.dual r j) j (b.localMean hp r j F) m) x :=
    fun j => by
      filter_upwards [T.applyLp_ae hΩ hint hΩm hp _,
        T.apply_ae_eq ((hsum j).mono fun y hy _ => hy)] with x h1 h2
      rw [h1, h2]
      exact T.apply_tsum _ _ _ (hor j) x
  have hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), T.applyLp hΩ hint hΩm hp
      (convLp hp (b.integrable_dual r j) (b.localMean hp r j F))) atTop
      (𝓝 (T.applyLp hΩ hint hΩm hp F)) := by
    have h := ((T.applyLp hΩ hint hΩm hp).continuous.tendsto F).comp
      (b.tendsto_sum_dual_localMean hp hr F)
    simpa only [Function.comp_def, map_sum] using h
  have hsyn := modNormOn_le_coeffNorm hp hΩm c' _ coef' hN ha' hf hF hs hsr hq
  rw [modNormOn, Lp.eNorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hΩm _)]
  refine hsyn.trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  calc coeffNorm p (finrank ℝ V) s q coef'
      ≤ coeffNorm p (finrank ℝ V) s q (fun j => cellCoef p j (b.localMean hp r j F)) :=
        ENNReal.lqNorm_mono fun j => mul_le_mul' le_rfl (levelNorm_mono p (hle j))
    _ = b.localMeansNorm hp r s q F := hcoef s q
    _ ≤ _ := b.localMeansNorm_le hp r s hq F

end CutoffDiffeo

/-! ### Global changes of variables -/

namespace CutoffDiffeo

section Global

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A **global change of variables with a cut-off**: a smooth bijection `Φ` of `V` with smooth
inverse `Ψ` and a smooth cut-off `χ` with compact support, as a change of variables on `V`. -/
noncomputable def global (Phi Psi : V → V) (hPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi) (hPsiPhi : ∀ x, Psi (Phi x) = x)
    (hPhiPsi : ∀ y, Phi (Psi y) = y) (chi : V → ℂ) (hchi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi)
    (hchic : HasCompactSupport chi) : CutoffDiffeo (Set.univ : Set V) where
  U := Set.univ
  U' := Set.univ
  isOpen_U := isOpen_univ
  isOpen_U' := isOpen_univ
  Phi := Phi
  Psi := Psi
  chi := chi
  K0 := tsupport chi
  contDiffOn_Phi := hPhi.contDiffOn
  contDiffOn_Psi := hPsi.contDiffOn
  contDiffOn_chi := hchi.contDiffOn
  mapsTo_Phi _ _ := ⟨Set.mem_univ _, Set.mem_univ _⟩
  mapsTo_Psi _ _ := ⟨Set.mem_univ _, Set.mem_univ _⟩
  left_inv x _ := hPsiPhi x
  right_inv y _ := hPhiPsi y
  isCompact_K0 := hchic
  K0_subset _ _ := ⟨Set.mem_univ _, Set.mem_univ _⟩
  chi_eq_zero _ _ hy := image_eq_zero_of_notMem_tsupport hy

/-- A global change of variables acts by `T f = (χ f) ∘ Φ`. -/
theorem global_apply (Phi Psi : V → V) (hPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi) (hPsiPhi : ∀ x, Psi (Phi x) = x)
    (hPhiPsi : ∀ y, Phi (Psi y) = y) (chi : V → ℂ) (hchi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi)
    (hchic : HasCompactSupport chi) (f : V → ℂ) (x : V) :
    (global Phi Psi hPhi hPsi hPsiPhi hPhiPsi chi hchi hchic).apply f x = chi (Phi x) * f (Phi
      x) := by
  rw [apply, Set.indicator_of_mem]
  · rfl
  · exact ⟨Set.mem_univ _, Set.mem_univ _⟩

end Global

end CutoffDiffeo

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The extension property -/

/-- The **extension property** of a measurable set `Ω`: for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞` there is `C < ∞` such that every `f ∈ L_p(V)` with
`N_Ω(f) = ‖1_Ω f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` (`Rd.modNormOn`) agrees on `Ω`
with some `F ∈ L_p(V)` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C N_Ω(f)`. -/
def HasBesovExtension {Ω : Set V} (hΩ : MeasurableSet Ω) : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ (r : ℕ) (s : ℝ), 0 < s → s < r →
    ∀ q : ℝ≥0∞, 1 ≤ q → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn hΩ r s q f < ∞ → ∃ F : Lp ℂ p (volume : Measure V),
        indicatorLp hΩ F = indicatorLp hΩ f ∧
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
          C * modNormOn hΩ r s q f

/-- **The extension property is the same for sets that agree up to a null set**: if `U` has it and
`U'` agrees with `U` up to a null set, then `U'` has it; the proof keeps the constant `C`, since
the cut-offs and the intrinsic quasi-norms on `U` and `U'` agree (`Rd.indicatorLp_congr_set`,
`Rd.modNormOn_congr_set`). -/
theorem HasBesovExtension.congr_set {U U' : Set V} {hU : MeasurableSet U} (hU' : MeasurableSet U')
    (hUU' : U =ᵐ[volume] U') (h : HasBesovExtension hU) : HasBesovExtension hU' := by
  intro p _ hp r s hs hsr q hq
  obtain ⟨C, hC, hext⟩ := h p hp r s hs hsr q hq
  refine ⟨C, hC, fun f hf => ?_⟩
  simp_rw [← modNormOn_congr_set hU hU' hUU', ← indicatorLp_congr_set hU hU' hUU'] at hf ⊢
  exact hext f hf

/-- **The order of the differences does not matter on a set with the extension property**: for
`0 < s < r` and `s < r'` there is `C < ∞` with `N_Ω(f; r') ≤ C N_Ω(f; r)` whenever
`N_Ω(f; r) < ∞`, where `N_Ω(f; r) = ‖1_Ω f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}`. Extend
`f` to `V`, change the order there (`Rd.modNorm_le_modNorm_of_lt`), and restrict. -/
theorem HasBesovExtension.modNormOn_order_le {Ω : Set V} {hΩ : MeasurableSet Ω}
    (h : HasBesovExtension hΩ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {r r' : ℕ} {s : ℝ}
    (hs : 0 < s) (hsr : s < r) (hsr' : s < r') {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn hΩ r s q f < ∞ → modNormOn hΩ r' s q f ≤ C * modNormOn hΩ r s q f := by
  obtain ⟨C₁, hC₁, hext⟩ := h p hp r s hs hsr q hq
  obtain ⟨C₂, hC₂, hord⟩ := modNorm_le_modNorm_of_lt (V := V) hp r hs.le hsr' hq
  refine ⟨C₂ * C₁, ENNReal.mul_ne_top hC₂ hC₁, fun f hf => ?_⟩
  obtain ⟨F, hFf, hFle⟩ := hext f hf
  rw [mul_assoc]
  exact (modNormOn_le_modNorm_of_indicatorLp hΩ r' s q hFf).trans
    ((hord F).trans (mul_le_mul' le_rfl hFle))

/-! ### Besov domains -/

/-- A **Besov domain**: a closed convex set with nonempty interior with the extension property
(`Rd.HasBesovExtension`): every function of finite intrinsic Besov quasi-norm agrees with a
function on `V` whose Besov quasi-norm is bounded by a constant times the intrinsic one, for
`1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`. The extension is a field of the class, so the class is a
hypothesis; its instances are `univ`, the closed half-space, the models of manifolds with and
without boundary and the quadrant model of manifolds with corners (`Rd.BesovDomain.univ`,
`Rd.BesovDomain.closedHalfSpace`, `Rd.BesovDomain.range_euclideanHalfSpace`,
`Rd.BesovDomain.range_of_boundaryless`, `Rd.BesovDomain.range_euclideanQuadrant`) and the closed
unit cube (`Rd.BesovDomain.closedUnitCube`). The closure of a Lipschitz graph domain with convex
graph function, of a nonempty convex bounded Lipschitz domain and of a nonempty bounded open
convex set is a Besov domain (`Rd.BesovDomain.closure_lipschitzGraph`,
`Rd.BesovDomain.closure_boundedLipschitzDomain`, `Rd.BesovDomain.closure_of_convex`), and so is
every closed ball of positive radius (`Rd.BesovDomain.closedBall`).
The class consists of closed convex sets; every Lipschitz graph domain and every bounded Lipschitz
domain, convex or not, has the extension property (`Rd.HasBesovExtension`,
`Rd.LipschitzGraph.hasBesovExtension`, `Rd.BoundedLipschitzDomain.hasBesovExtension`). -/
class BesovDomain (Ω : Set V) : Prop where
  convex : Convex ℝ Ω
  isClosed : IsClosed Ω
  interior_nonempty : (interior Ω).Nonempty
  exists_extension : HasBesovExtension isClosed.measurableSet

/-- **`V` is a Besov domain**, with the extension `F = f`. -/
instance BesovDomain.univ : BesovDomain (Set.univ : Set V) where
  convex := convex_univ
  isClosed := isClosed_univ
  interior_nonempty := by
    rw [interior_univ]
    exact Set.univ_nonempty
  exists_extension p _ _ r s _ _ q _ := ⟨1, ENNReal.one_ne_top, fun f _ =>
    ⟨f, rfl, by rw [one_mul, modNormOn_univ]⟩⟩

/-- **A closed convex set with nonempty interior and the extension property is a Besov
domain.** -/
theorem BesovDomain.of_hasBesovExtension {Ω : Set V} (hc : Convex ℝ Ω) (hcl : IsClosed Ω)
    (hint : (interior Ω).Nonempty) (h : HasBesovExtension hcl.measurableSet) : BesovDomain Ω :=
  ⟨hc, hcl, hint, h⟩

/-- **Besov domains up to null sets**: a closed convex set `Ω` with nonempty interior is a Besov
domain if it agrees up to a null set with a set `U` with the extension property
(`Rd.HasBesovExtension.congr_set`). -/
theorem BesovDomain.of_ae_eq {Ω U : Set V} (hc : Convex ℝ Ω) (hcl : IsClosed Ω)
    (hint : (interior Ω).Nonempty) {hU : MeasurableSet U} (h : HasBesovExtension hU)
    (hae : Ω =ᵐ[volume] U) : BesovDomain Ω :=
  of_hasBesovExtension hc hcl hint (h.congr_set hcl.measurableSet hae.symm)

namespace BesovDomain

variable (Ω : Set V) [BesovDomain Ω]

/-- A Besov domain is measurable. -/
theorem measurableSet : MeasurableSet Ω := (isClosed (Ω := Ω)).measurableSet

/-- **A Besov domain has the extension property.** -/
theorem hasBesovExtension : HasBesovExtension (measurableSet Ω) :=
  exists_extension (Ω := Ω)

variable {Ω} in
/-- **The order of the differences on a Besov domain does not matter**: for `0 < s < r` and
`s < r'` there is `C < ∞` with `N_Ω(f; r') ≤ C N_Ω(f; r)` whenever `N_Ω(f; r) < ∞`, where
`N_Ω(f; r) = ‖1_Ω f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}`
(`Rd.HasBesovExtension.modNormOn_order_le`). -/
theorem modNormOn_order_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {r r' : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r) (hsr' : s < r') {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn (measurableSet Ω) r s q f < ∞ →
      modNormOn (measurableSet Ω) r' s q f ≤ C * modNormOn (measurableSet Ω) r s q f :=
  (hasBesovExtension Ω).modNormOn_order_le hp hs hsr hsr' hq

end BesovDomain

namespace CutoffDiffeo

variable {Ω : Set V} [hB : BesovDomain Ω] (T : CutoffDiffeo Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (hp : p ≠ ∞)

/-- **`T` depends only on the values on `Ω`**: if `F = f` almost everywhere on `Ω`, then
`T F = T f` in `L_p`. -/
theorem applyLp_eq_of_indicatorLp_eq {F f : Lp ℂ p (volume : Measure V)}
    (hFf : indicatorLp (BesovDomain.measurableSet Ω) F =
      indicatorLp (BesovDomain.measurableSet Ω) f) :
    T.applyLp hB.convex hB.interior_nonempty (BesovDomain.measurableSet Ω) hp F =
      T.applyLp hB.convex hB.interior_nonempty (BesovDomain.measurableSet Ω) hp f := by
  have hae : ∀ᵐ y ∂volume, y ∈ Ω → F y = f y := by
    filter_upwards [indicatorLp_apply_ae (BesovDomain.measurableSet Ω) F,
      indicatorLp_apply_ae (BesovDomain.measurableSet Ω) f] with y h1 h2 hy
    rw [← Set.indicator_of_mem hy (F : V → ℂ), ← Set.indicator_of_mem hy (f : V → ℂ), ← h1, ← h2,
      hFf]
  refine Lp.ext ?_
  filter_upwards [T.applyLp_ae hB.convex hB.interior_nonempty (BesovDomain.measurableSet Ω) hp F,
    T.applyLp_ae hB.convex hB.interior_nonempty (BesovDomain.measurableSet Ω) hp f,
    T.apply_ae_eq hae] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **Invariance of the intrinsic Besov quasi-norm on a Besov domain** under a smooth change of
variables with a cut-off: for `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞` there is `C < ∞` with
`N_Ω(T f) ≤ C N_Ω(f)` for all `f` with `N_Ω(f) < ∞`, where
`N_Ω(f) = ‖1_Ω f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}`. Extend `f` to `V`
(`Rd.BesovDomain.exists_extension`) and apply `Rd.CutoffDiffeo.modNormOn_applyLp_le`. -/
theorem modNormOn_applyLp_le_modNormOn {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn (BesovDomain.measurableSet Ω) r s q f < ∞ →
      modNormOn (BesovDomain.measurableSet Ω) r s q
          (T.applyLp hB.convex hB.interior_nonempty (BesovDomain.measurableSet Ω) hp f) ≤
        C * modNormOn (BesovDomain.measurableSet Ω) r s q f := by
  obtain ⟨C₁, hC₁, hext⟩ := hB.exists_extension p hp r s hs hsr q hq
  obtain ⟨C₂, hC₂, hT⟩ := T.modNormOn_applyLp_le hB.convex hB.interior_nonempty
    (BesovDomain.measurableSet Ω) hp hr hs hsr hq
  refine ⟨C₂ * C₁, ENNReal.mul_ne_top hC₂ hC₁, fun f hf => ?_⟩
  obtain ⟨F, hFf, hFle⟩ := hext f hf
  rw [← T.applyLp_eq_of_indicatorLp_eq hp hFf, mul_assoc]
  exact (hT F).trans (mul_le_mul' le_rfl hFle)

end CutoffDiffeo

end Rd
