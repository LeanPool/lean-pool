/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Extension.LipschitzGraphBesov

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Local extensions

Rychkov's construction works locally. Let `b` be a bump for local means with kernels `k_j`, dual
kernels `η_j` and radius `R ≤ 1/2`, and let `U ⊆ W` and `U ⊆ T` be measurable sets such that

* `x - y ∈ W` for `x ∈ U` and `y` in the support of a dual kernel (`η_j ⋆` at points of `U` only
  sees `W`), and
* `W ⊆ T_{L h}` for the steps `h = -c^(-1) z`, `c ≥ 1`, `b(z) ≠ 0` (the averaged differences of
  the moment kernels at points of `W` stay in `T`).

Then for `f ∈ L_p(V)` with `‖f‖_{L_p(T)} + ‖(2^(ks) ω_L(f, 2^(-k), T)_p)_k‖_{ℓ_q} < ∞` (the
intrinsic quasi-norm `Rd.modNormOn` on `T`) and `0 < s < L`, the local extension
`F = ∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` (`Rd.LocalMeansBump.localExtension`) has a finite Besov
quasi-norm on `V` and `F = f` almost everywhere on `U` (`Rd.LocalMeansBump.exists_local_extension`);
its Besov quasi-norm is at most a constant of the bump (`Rd.LocalMeansBump.localExtConst`) times
that of `f` on `T` (`Rd.LocalMeansBump.exists_local_extension_le`). The local means on `W` are
bounded by the moduli on `T` (`Rd.LocalMeansBump.localNormOn_le`), by the moment kernel bound for
two sets (`Rd.eLpNorm_indicator_sub_convLp_momentKernel_le`).

Two kinds of patches satisfy the conditions:

* **boundary patches** of a Lipschitz graph domain `Ω`, `U = Ω ∩ B(c, ρ - 2ε)`,
  `W = Ω ∩ B(c, ρ - ε)`, `T = Ω ∩ B(c, ρ)`, for a bump supported in the reflected cone with
  `L R ≤ ε` (`Rd.LipschitzGraph.patch_support`, `Rd.LipschitzGraph.patch_step`);
* **interior patches** of an open set `O`, `U = {infDist(·, Oᶜ) > 2δ}`, `W = {infDist(·, Oᶜ) > δ}`,
  `T = O`, for any bump with `L R ≤ δ` (`Rd.interior_patch_support`, `Rd.interior_patch_step`);
  these sets lie in `O` (`Rd.setOf_lt_infDist_compl_subset`), and so does `x - y` for
  `δ < infDist(x, Oᶜ)` and `‖y‖ ≤ δ` (`Rd.sub_mem_of_lt_infDist_of_norm_le`).

Short steps `-y ∈ KBar`, `‖y‖ ≤ ε`, take `Ω ∩ B(c, ρ - ε)` into `Ω ∩ B(c, ρ)`
(`Rd.LipschitzGraph.sub_mem_patch_of_mem_closedCone`); this gives the support conditions of all
cone-supported kernels of small support.

Bumps of every radius come from rescaling (`Rd.LocalMeansBump.rescale`) and from the normalised
smooth bump centred at `0` (`Rd.LocalMeansBump.centered`). The cone bump of a Lipschitz graph
domain, rescaled, is supported in the reflected cone with a radius `R ≤ 1/2` and `a R ≤ ε`
(`Rd.LipschitzGraph.exists_coneBump_radius_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Bumps of every radius -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The **rescaled bump** `c^n b(c ·)`, of radius `R / c`. -/
noncomputable def rescale {c : ℝ} (hc : 0 < c) : LocalMeansBump V where
  toFun := Rd.dilate c b.toFun
  radius := b.radius / c
  radius_nonneg := div_nonneg b.radius_nonneg hc.le
  contDiff := contDiff_const.mul (b.contDiff.comp (contDiff_const_smul c))
  eq_zero z hz := by
    have hz' : b.radius < ‖c • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc.le]
      rwa [div_lt_iff₀ hc, mul_comm] at hz
    simp only [Rd.dilate, b.eq_zero _ hz', mul_zero]
  integral_eq_one := by rw [integral_dilate _ hc, b.integral_eq_one]

/-- The rescaled bump has radius `R / c`. -/
theorem rescale_radius {c : ℝ} (hc : 0 < c) : (b.rescale hc).radius = b.radius / c := rfl

/-- The dilated moment kernels vanish outside the ball of radius `L R`. -/
theorem scaled_eq_zero (L j : ℕ) {y : V} (hy : L * b.radius < ‖y‖) : b.scaled L j y = 0 := by
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have hy' : L * b.radius < ‖(2 : ℝ) ^ j • y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (L : ℝ) * b.radius < ‖y‖ := hy
      _ ≤ 2 ^ j * ‖y‖ := le_mul_of_one_le_left (norm_nonneg y) h1
  simp only [scaled, Rd.dilate, b.momentKernel_eq_zero L hy', mul_zero]

/-- The dual kernels vanish outside the ball of radius `L R`. -/
theorem dual_eq_zero (L j : ℕ) {y : V} (hy : L * b.radius < ‖y‖) : b.dual L j y = 0 := by
  cases j with
  | zero => exact b.scaled_eq_zero L 0 hy
  | succ j =>
    change b.scaled L (j + 1) y + b.scaled L j y = 0
    rw [b.scaled_eq_zero L _ hy, b.scaled_eq_zero L _ hy, add_zero]

/-- The local means kernels vanish outside the ball of radius `L R`. -/
theorem kernel_eq_zero (L j : ℕ) {y : V} (hy : L * b.radius < ‖y‖) : b.kernel L j y = 0 := by
  cases j with
  | zero => exact b.scaled_eq_zero L 0 hy
  | succ j =>
    change b.scaled L (j + 1) y - b.scaled L j y = 0
    rw [b.scaled_eq_zero L _ hy, b.scaled_eq_zero L _ hy, sub_zero]

end LocalMeansBump

/-! ### Kernels supported in the reflected cone -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- Rescaled bumps supported in `-K` are supported in `-K`. -/
theorem coneSupported_rescale {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun) {c : ℝ}
    (hc : 0 < c) : Ω.ConeSupported (b.rescale hc).toFun :=
  hb.dilate hc

/-- **Cone bumps of small radius**: for `a ≥ 0` and `ε > 0` the cone bump rescaled by
`1 + a / ε` is supported in `-K` and has a radius `R ≤ 1/2` with `a R ≤ ε`
(`Rd.LipschitzGraph.coneBump_radius`). -/
theorem exists_coneBump_radius_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ b : LocalMeansBump V, Ω.ConeSupported b.toFun ∧ b.radius ≤ 1 / 2 ∧ a * b.radius ≤ ε := by
  have hc : 0 < 1 + a / ε := by positivity
  refine ⟨Ω.coneBump.rescale hc, Ω.coneSupported_rescale Ω.coneSupported_coneBump hc, ?_, ?_⟩ <;>
    rw [LocalMeansBump.rescale_radius, Ω.coneBump_radius]
  · exact div_le_self (by norm_num) (le_add_of_nonneg_right (by positivity))
  · rw [← mul_div_assoc, div_le_iff₀ hc, mul_add, mul_one, mul_div_cancel₀ a hε.ne']
    linarith

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Short steps into the reflected closed cone stay in a patch**: if `x ∈ Ω ∩ B(c, ρ - ε)`,
`-y ∈ KBar` and `‖y‖ ≤ ε`, then `x - y ∈ Ω ∩ B(c, ρ)` (`Rd.LipschitzGraph.add_mem_of_mem_closedCone`
and the triangle inequality). -/
theorem sub_mem_patch_of_mem_closedCone {ε ρ : ℝ} {c x y : V}
    (hx : x ∈ Ω.domain ∩ ball c (ρ - ε)) (hy : -y ∈ Ω.closedCone) (hyR : ‖y‖ ≤ ε) :
    x - y ∈ Ω.domain ∩ ball c ρ := by
  obtain ⟨hxΩ, hxc⟩ := hx
  refine ⟨by simpa [sub_eq_add_neg] using Ω.add_mem_of_mem_closedCone hxΩ hy, ?_⟩
  rw [mem_ball] at hxc ⊢
  calc dist (x - y) c ≤ dist x c + ‖y‖ := by
        rw [dist_eq_norm, dist_eq_norm, sub_right_comm]
        exact norm_sub_le _ _
    _ < ρ - ε + ε := by linarith
    _ = ρ := by ring

/-- **Boundary patches, the support condition**: for a bump supported in `-K` with `L R ≤ ε`, the
dual kernels at points of `Ω ∩ B(c, ρ - 2ε)` only see `Ω ∩ B(c, ρ - ε)`
(`Rd.LipschitzGraph.sub_mem_patch_of_mem_closedCone`). -/
theorem patch_support {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun) {L : ℕ} {ε ρ : ℝ}
    {c : V} (hLR : L * b.radius ≤ ε) :
    ∀ x ∈ Ω.domain ∩ ball c (ρ - 2 * ε), ∀ j y, b.dual L j y ≠ 0 →
      x - y ∈ Ω.domain ∩ ball c (ρ - ε) := by
  intro x hx j y hy
  have hyR : ‖y‖ ≤ L * b.radius := not_lt.1 fun h => hy (b.dual_eq_zero L j h)
  rw [show ρ - 2 * ε = ρ - ε - ε by ring] at hx
  exact Ω.sub_mem_patch_of_mem_closedCone hx
    (Ω.cone_subset_closedCone (Ω.coneSupported_dual_of hb L j y hy)) (hyR.trans hLR)

/-- **Boundary patches, the step condition**: for a bump supported in `-K` with `L R ≤ ε`, the steps
`-c'^(-1) z`, `c' ≥ 1`, `b(z) ≠ 0`, take `Ω ∩ B(c, ρ - ε)` into `Ω ∩ B(c, ρ)`. -/
theorem patch_step {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun) {L : ℕ} {ε ρ : ℝ}
    {c : V} (hLR : L * b.radius ≤ ε) :
    ∀ c' : ℝ, 1 ≤ c' → ∀ z, b.toFun z ≠ 0 →
      Ω.domain ∩ ball c (ρ - ε) ⊆ stepSet (Ω.domain ∩ ball c ρ) L (-c'⁻¹ • z) := by
  intro c' hc' z hz x ⟨hxΩ, hxc⟩ l hl
  have hc0 : 0 < c' := zero_lt_one.trans_le hc'
  have hzK : -z ∈ Ω.cone := hb z hz
  have hzR : ‖z‖ ≤ b.radius := not_lt.1 fun h => hz (b.eq_zero z h)
  have hh : -c'⁻¹ • z = c'⁻¹ • -z := by rw [neg_smul, smul_neg]
  have hnorm : ‖(l : ℝ) • (-c'⁻¹ • z)‖ ≤ L * b.radius := by
    rw [norm_smul, norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hc0.le,
      Real.norm_of_nonneg (Nat.cast_nonneg l)]
    have hl' : (l : ℝ) ≤ L := by exact_mod_cast hl
    have hinv : c'⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc'
    calc (l : ℝ) * (c'⁻¹ * ‖z‖) ≤ L * (1 * b.radius) := by
          gcongr
      _ = L * b.radius := by ring
  refine ⟨?_, ?_⟩
  · rw [hh]
    exact Ω.add_nsmul_mem hxΩ (Ω.smul_mem_cone (inv_pos.2 hc0) hzK) l
  · rw [mem_ball] at hxc ⊢
    calc dist (x + (l : ℝ) • (-c'⁻¹ • z)) c ≤ dist x c + ‖(l : ℝ) • (-c'⁻¹ • z)‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ < ρ - ε + ε := by linarith
      _ = ρ := by ring

end LipschitzGraph

/-! ### Interior patches -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Points at distance more than `r ≥ 0` from the complement of `s` lie in `s`. -/
theorem setOf_lt_infDist_compl_subset (s : Set V) {r : ℝ} (hr : 0 ≤ r) :
    {x : V | r < infDist x sᶜ} ⊆ s := fun x hx => by
  by_contra h
  have h0 : infDist x sᶜ = 0 := infDist_zero_of_mem h
  simp only [Set.mem_ofPred_eq] at hx
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Interior patches, the support condition**: if the dual kernels vanish outside the ball of
radius `δ`, they see `{infDist(·, Oᶜ) > δ}` from points of `{infDist(·, Oᶜ) > 2δ}`. -/
theorem interior_patch_support (O : Set V) {k : V → ℂ} {δ : ℝ} (hk : ∀ y, k y ≠ 0 → ‖y‖ ≤ δ) :
    ∀ x ∈ {x : V | 2 * δ < infDist x Oᶜ}, ∀ y, k y ≠ 0 → x - y ∈ {x : V | δ < infDist x Oᶜ} := by
  intro x hx y hy
  have h := infDist_le_infDist_add_dist (s := Oᶜ) (x := x) (y := x - y)
  rw [dist_eq_norm, sub_sub_cancel] at h
  simp only [Set.mem_ofPred_eq] at hx ⊢
  linarith [hk y hy]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Inner patches, the support condition for kernels in a ball**: if `δ < infDist(x, Oᶜ)` and
`‖y‖ ≤ δ`, then `x - y ∈ O`, since `x - y` lies in the ball `B(x, infDist(x, Oᶜ)) ⊆ O`
(Mathlib's `Metric.ball_infDist_compl_subset`). -/
theorem sub_mem_of_lt_infDist_of_norm_le (O : Set V) {δ : ℝ} {x y : V}
    (hx : x ∈ {x : V | δ < infDist x Oᶜ}) (hy : ‖y‖ ≤ δ) : x - y ∈ O :=
  ball_infDist_compl_subset (by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact hy.trans_lt hx)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Interior patches, the step condition**: steps of length at most `δ / L` take
`{infDist(·, Oᶜ) > δ}` into `O_{L h}`. -/
theorem interior_patch_step (O : Set V) {L : ℕ} {δ : ℝ} {h : V} (hh : L * ‖h‖ ≤ δ) :
    {x : V | δ < infDist x Oᶜ} ⊆ stepSet O L h := by
  intro x hx l hl
  by_contra hmem
  have h1 : infDist x Oᶜ ≤ dist x (x + (l : ℝ) • h) := infDist_le_dist_of_mem hmem
  have hl' : (l : ℝ) ≤ L := by exact_mod_cast hl
  have h2 : dist x (x + (l : ℝ) • h) ≤ δ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg (Nat.cast_nonneg l)]
    exact (mul_le_mul_of_nonneg_right hl' (norm_nonneg h)).trans hh
  simp only [Set.mem_ofPred_eq] at hx
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The sets `{infDist(·, Oᶜ) > δ}` are measurable. -/
theorem measurableSet_infDist_gt (O : Set V) (δ : ℝ) :
    MeasurableSet {x : V | δ < infDist x Oᶜ} :=
  (isOpen_lt continuous_const (continuous_infDist_pt _)).measurableSet

/-! ### Local means and moduli on a set -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- `‖1_W (k_0 ⋆ f)‖_p ≤ ‖m‖_1 ‖f‖_p`. -/
theorem enorm_indicatorLp_localMean_zero_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖indicatorLp hW (b.localMean hp L 0 f)‖ₑ ≤
      eLpNorm (momentKernel b.toFun L) 1 volume * ‖f‖ₑ :=
  (enorm_indicatorLp_le hW _).trans (b.enorm_localMean_zero_le hp L f)

/-- **The local means on `W` are bounded by the moduli on `T`**:
`‖(2^(js) ‖1_W (k_j ⋆ f)‖_p)_j‖_{ℓ_q} ≤
(‖m‖_1 + 2 ‖g‖_1) (‖f‖_p + ‖(2^(js) ω_L(f, 2^(-j), T)_p)_j‖_{ℓ_q})`
(`ENNReal.lqNorm_dyadicWeight_le_of_head_of_succ_le`). -/
theorem localNormOn_le (hp : p ≠ ∞) {W T : Set V} (hW : MeasurableSet W) (L : ℕ) (s : ℝ)
    {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hstep : ∀ c : ℝ, 1 ≤ c → ∀ z, b.toFun z ≠ 0 → W ⊆ stepSet T L (-c⁻¹ • z))
    (hR : b.radius ≤ 1 / 2) (f : Lp ℂ p (volume : Measure V)) :
    b.localNormOn hp hW L s q f ≤
      (eLpNorm (momentKernel b.toFun L) 1 volume + 2 * ∫⁻ z, ‖b.toFun z‖ₑ) *
        (‖f‖ₑ + lqNorm q (fun j => dyadicWeight s j * lpModulusOn p T L f j)) :=
  ENNReal.lqNorm_dyadicWeight_le_of_head_of_succ_le hq s
    (fun j => ‖indicatorLp hW (b.localMean hp L j f)‖ₑ) (lpModulusOn p T L f)
    (b.enorm_indicatorLp_localMean_zero_le hp hW L f)
    fun j => b.enorm_indicatorLp_localMean_succ_le hp hW L j hstep hR f

/-- The **constant of the local extension** `C_b(L, s) (‖m‖_1 + 2 ‖g‖_1)`, for the moment kernel
`m` of the bump `g`: the constant of the synthesis estimate (`Rd.LocalMeansBump.synthConst`) times
that of `Rd.LocalMeansBump.localNormOn_le`. -/
noncomputable def localExtConst (L : ℕ) (s : ℝ) : ℝ≥0∞ :=
  b.synthConst L s * (eLpNorm (momentKernel b.toFun L) 1 volume + 2 * ∫⁻ z, ‖b.toFun z‖ₑ)

/-- The constant of the local extension is finite for `0 < s < L`. -/
theorem localExtConst_ne_top {L : ℕ} {s : ℝ} (hs : 0 < s) (hsL : s < L) :
    b.localExtConst L s ≠ ∞ :=
  ENNReal.mul_ne_top (b.synthConst_ne_top hs hsL) (b.momentConst_ne_top L)

/-- **The local extension theorem with a bound**: let `U ⊆ W`, `U ⊆ T` be measurable sets such
that the dual kernels at points of `U` only see `W` and the steps take `W` into `T`, and let the
bump have radius `R ≤ 1/2`. For `1 ≤ p < ∞`, `0 < s`, `1 ≤ q ≤ ∞` and `f` with
`N_T(f) = ‖f‖_{L_p(T)} + ‖(2^(ks) ω_L(f, 2^(-k), T)_p)_k‖_{ℓ_q} < ∞` there is `F` with
`F = f` almost everywhere on `U` and
`‖F‖_p + ‖(2^(ks) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C_b(L, s) (‖m‖_1 + 2 ‖g‖_1) N_T(f)`
(`Rd.LocalMeansBump.localExtConst`): the local extension of `1_T f`
(`Rd.LocalMeansBump.modNorm_localExtension_le`, `Rd.LocalMeansBump.localNormOn_le`). The constant
is finite for `s < L` (`Rd.LocalMeansBump.localExtConst_ne_top`); for `s ≥ L` the factor
`(1 - 2^(-(L - s)))⁻¹` of `Rd.LocalMeansBump.synthConst` is `∞`. -/
theorem exists_local_extension_le (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {U W T : Set V} (hU : MeasurableSet U)
    (hW : MeasurableSet W) (hT : MeasurableSet T) (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W)
    (hstep : ∀ c : ℝ, 1 ≤ c → ∀ z, b.toFun z ≠ 0 → W ⊆ stepSet T L (-c⁻¹ • z))
    (hR : b.radius ≤ 1 / 2) (f : Lp ℂ p (volume : Measure V))
    (hf : modNormOn hT L s q f < ∞) :
    ∃ F : Lp ℂ p (volume : Measure V),
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L F k) ≤
          b.localExtConst L s * modNormOn hT L s q f ∧
        indicatorLp hU F = indicatorLp hU f := by
  set f' := indicatorLp hT f
  have hae : T.indicator f' =ᵐ[volume] T.indicator f := by
    filter_upwards [indicatorLp_apply_ae hT f] with x hx
    by_cases hxT : x ∈ T
    · rw [Set.indicator_of_mem hxT, Set.indicator_of_mem hxT, hx, Set.indicator_of_mem hxT]
    · rw [Set.indicator_of_notMem hxT, Set.indicator_of_notMem hxT]
  have hmod : ∀ k, lpModulusOn p T L f' k = lpModulusOn p T L f k := fun k =>
    lpModulusOn_congr hae L k
  have hle : b.localNormOn hp hW L s q f' ≤
      (eLpNorm (momentKernel b.toFun L) 1 volume + 2 * ∫⁻ z, ‖b.toFun z‖ₑ) *
        (‖f'‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p T L f k)) := by
    have h := b.localNormOn_le hp hW L s hq hstep hR f'
    simp_rw [hmod] at h
    exact h
  have hfin : b.localNormOn hp hW L s q f' < ∞ :=
    hle.trans_lt (ENNReal.mul_lt_top (b.momentConst_ne_top L).lt_top hf)
  refine ⟨b.localExtension hp hW L f', (b.modNorm_localExtension_le hp hW L hs hq hfin).trans ?_,
    ?_⟩
  · rw [localExtConst, mul_assoc]
    exact mul_le_mul' le_rfl hle
  rw [b.indicatorLp_localExtension hp hL hU hW hUW hs hq hfin]
  refine Lp.ext ?_
  filter_upwards [indicatorLp_apply_ae hU f', indicatorLp_apply_ae hU f,
    indicatorLp_apply_ae hT f] with x h1 h2 h3
  rw [h1, h2]
  by_cases hxU : x ∈ U
  · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, h3, Set.indicator_of_mem (hUT hxU)]
  · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]

/-- **The local extension theorem**: let `U ⊆ W`, `U ⊆ T` be measurable sets such that the dual
kernels at points of `U` only see `W` and the steps take `W` into `T`, and let the bump have
radius `R ≤ 1/2`. For `1 ≤ p < ∞`, `0 < s < L`, `1 ≤ q ≤ ∞` and `f` with
`‖f‖_{L_p(T)} + ‖(2^(ks) ω_L(f, 2^(-k), T)_p)_k‖_{ℓ_q} < ∞` there is `F` with a finite Besov
quasi-norm by differences on `V` and `F = f` almost everywhere on `U`
(`Rd.LocalMeansBump.exists_local_extension_le`). -/
theorem exists_local_extension (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {U W T : Set V} (hU : MeasurableSet U)
    (hW : MeasurableSet W) (hT : MeasurableSet T) (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W)
    (hstep : ∀ c : ℝ, 1 ≤ c → ∀ z, b.toFun z ≠ 0 → W ⊆ stepSet T L (-c⁻¹ • z))
    (hR : b.radius ≤ 1 / 2) (f : Lp ℂ p (volume : Measure V))
    (hf : modNormOn hT L s q f < ∞) :
    ∃ F : Lp ℂ p (volume : Measure V),
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L F k) < ∞ ∧
        indicatorLp hU F = indicatorLp hU f := by
  obtain ⟨F, hF, hFf⟩ := b.exists_local_extension_le hp hL hs hq hU hW hT hUT hUW hstep hR f hf
  exact ⟨F, hF.trans_lt (ENNReal.mul_lt_top (b.localExtConst_ne_top hs hsL).lt_top hf), hFf⟩

end LocalMeansBump

end Rd
