/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import LeanPool.Triangular.Auto.Dissipation

/-!
# The Gaussian estimate on finite grids and its Euclidean limit

Derived from the corresponding part of the upstream triangular Hilbert form proof.

The lattice-norm convergence adapts `TwoCommuting/Auto/Sec6EuclideanCounting.lean`.
Joris Roos’s `lean-twocommuting` revision `33b69ccacc013c703a151421658187ea4d2029fb`
credits these Apache-2.0 Lean proofs to Claude.
-/

@[expose] public section

namespace Triangular.Auto

open MeasureTheory Filter Topology Matrix Real

open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section

/-- Translating one center changes the center-plane sum by exactly the translation. -/
lemma sum_shift (v : Fin 3) (q : Fin 2 → ℝ) (d : ℝ) :
    Function.update (planePt q) v (planePt q v + d) 0 +
      Function.update (planePt q) v (planePt q v + d) 1 +
      Function.update (planePt q) v (planePt q v + d) 2 = d := by
  fin_cases v <;> simp [planePt] <;> ring

lemma heatCost_aemeasurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {α : Fin 3 → ℝ}
    (hα1 : ∀ v, 1 ≤ α v) (hα2 : ∀ v, α v ≤ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    AEMeasurable (heatCost Hd α) ((volume.restrict (Set.Ioc a b)).prod volume) := by
  apply ENNReal.aemeasurable_of_tendsto
    (f := fun m z => ENNReal.ofReal (Hd.costDensity α (1 / ((m : ℝ) + 1)) z))
  · intro m
    exact (Hd.costDensity_integrable hh (by positivity) hα1 hα2 ha
      hab).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  · exact Eventually.of_forall fun z => heatCost_tendsto Hd α z (fun m => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- A bounded real diagonal matrix has the corresponding operator-norm bound. -/
lemma sq_smul_one_sub_rdiag_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℝ} {d : ℝ} (hf : ∀ i, |f i| ≤ d) :
    ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - rdiag f * rdiag f).PosSemidef := by
  have e : (d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - rdiag f * rdiag f =
      rdiag fun i => d ^ 2 - f i ^ 2 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [rdiag]; ring
    · simp [rdiag, hij]
  rw [e]
  refine rdiag_posSemidef fun i => ?_
  have := hf i
  nlinarith [abs_nonneg (f i), sq_abs (f i)]

/-- The center-integrated trace is controlled by the three energy densities. -/
theorem heatTrace_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {s : ℝ} (hs : 0 < s) :
    ‖((1 / s : ℝ) : ℂ) * ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ ≤
      ENNReal.ofReal (5 / 3 * constD * constA ^ 2) *
        ∑ v, ∫⁻ p, heatCost Hd (rateAt v) (s, p) := by
  obtain ⟨hcD, hD⟩ := constD_spec
  obtain ⟨hcA, hA⟩ := constA_spec
  set σB : Fin 3 → ℝ := fun _ => 11 / 10 * s
  have hσV : ∀ v k, 0 < Function.update σB v s k := fun v k => by
    simp only [σB, Function.update_apply]; split_ifs <;> positivity
  set Φ : Fin 3 → (Fin 3 → ℝ) → ℝ≥0∞ := fun v p =>
    matCost (Hd.T p (Function.update σB v s) v) (Hd.Ui p (Function.update σB v s) v)
  have hΦ : ∀ v, Measurable (Φ v) := fun v => Hd.measurable_rowCost _ (hσV v) v
  have htr : ∀ q : Fin 2 → ℝ, ‖Hd.baseTrace 3 (planePt q) s‖ₑ ≤
      ENNReal.ofReal (5 / 3 * constD) * ∑ v, ENNReal.ofReal (constA ^ 2 * s) *
        ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
          Φ v (Function.update (planePt q) v (planePt q v + d)) := by
    intro q
    set p := planePt q
    have hDh : ∀ v, (Hd.Dmat 3 v p s).IsHermitian := fun v => rdiag_isHermitian _
    have hDb : ∀ v, ((constD ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - Hd.Dmat 3 v p s *
        Hd.Dmat 3 v p s).PosSemidef := fun v =>
      sq_smul_one_sub_rdiag_psd fun i => hD 3 v s hs _
    have h05 := cyclic_trace_control (W0 := Hd.W p σB 0) (W1 := Hd.W p σB 1)
      (W2 := Hd.W p σB 2) (D0 := Hd.Dmat 3 0 p s) (D1 := Hd.Dmat 3 1 p s)
      (D2 := Hd.Dmat 3 2 p s) (hDh 0) (hDh 1) (hDh 2) hcD (hDb 0) (hDb 1) (hDb 2)
    rw [← ofReal_norm]
    refine h05.trans (mul_le_mul' le_rfl ?_)
    rw [Fin.sum_univ_three]
    have hv := fun v : Fin 3 => Hd.vertex_avg hh v (by norm_num [dexp]) (hA 3 v) p hs
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact hv 0
    · exact hv 1
    · exact hv 2
  have hI : ∀ v, AEMeasurable (fun q : Fin 2 → ℝ => ENNReal.ofReal (constA ^ 2 * s) *
      ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
        Φ v (Function.update (planePt q) v (planePt q v + d))) volume := by
    intro v
    refine (Measurable.lintegral_prod_right' (ν := (volume : Measure ℝ))
      (f := fun z : (Fin 2 → ℝ) × ℝ => ENNReal.ofReal (gaussian (1 / 10 * s) z.2) *
        Φ v (Function.update (planePt z.1) v (planePt z.1 v + z.2))) ?_).const_mul _
      |>.aemeasurable
    refine (ENNReal.measurable_ofReal.comp ((continuous_gaussian' _).measurable.comp
      measurable_snd)).mul ((hΦ v).comp ?_)
    have : Continuous fun z : (Fin 2 → ℝ) × ℝ =>
        Function.update (planePt z.1) v (planePt z.1 v + z.2) := by
      refine continuous_pi fun k => ?_
      by_cases hk : k = v
      · subst hk; simp only [Function.update_self]
        fin_cases k <;> dsimp [planePt] <;> fun_prop
      · simp only [Function.update_of_ne hk]
        fin_cases k <;> dsimp [planePt] <;> fun_prop
    exact this.measurable
  have hcv : ∀ v, ∫⁻ q : Fin 2 → ℝ, ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
      Φ v (Function.update (planePt q) v (planePt q v + d)) ≤
      ∫⁻ p, heatCost Hd (rateAt v) (s, p) := by
    intro v
    have hF : Measurable fun p : Fin 3 → ℝ =>
        ENNReal.ofReal (gaussian (1 / 10 * s) (p 0 + p 1 + p 2)) * Φ v p :=
      (ENNReal.measurable_ofReal.comp ((continuous_gaussian' _).measurable.comp
        (by fun_prop))).mul (hΦ v)
    have := lintegral_plane_shift v hF
    simp only [sum_shift] at this
    rw [this]
    refine lintegral_mono fun p => ?_
    simp only [heatCost, HeatData.Gm_eq, Φ]
    rw [sig_rateAt]
    refine mul_le_mul' le_rfl ?_
    exact Finset.single_le_sum (f := fun v' => matCost (Hd.T p
      (Function.update (fun _ => 11 / 10 * s) v s) v')
      (Hd.Ui p (Function.update (fun _ => 11 / 10 * s) v s) v'))
      (fun _ _ => zero_le) (Finset.mem_univ v)
  calc ‖((1 / s : ℝ) : ℂ) * ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ
      = ENNReal.ofReal (1 / s) * ‖∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ := by
        rw [eNorm_mul, ← ofReal_norm (((1 / s : ℝ) : ℂ)), Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ ENNReal.ofReal (1 / s) * ∫⁻ q : Fin 2 → ℝ, ‖Hd.baseTrace 3 (planePt q) s‖ₑ :=
        mul_le_mul' le_rfl (eNorm_integral_le_lintegral_eNorm _)
    _ ≤ ENNReal.ofReal (1 / s) * ∫⁻ q : Fin 2 → ℝ, ENNReal.ofReal (5 / 3 * constD) *
        ∑ v, ENNReal.ofReal (constA ^ 2 * s) * ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
          Φ v (Function.update (planePt q) v (planePt q v + d)) :=
        mul_le_mul' le_rfl (lintegral_mono htr)
    _ = ENNReal.ofReal (1 / s) * (ENNReal.ofReal (5 / 3 * constD) *
        ∑ v, ENNReal.ofReal (constA ^ 2 * s) * ∫⁻ q : Fin 2 → ℝ, ∫⁻ d,
          ENNReal.ofReal (gaussian (1 / 10 * s) d) *
            Φ v (Function.update (planePt q) v (planePt q v + d))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _
          fun v _ => hI v]
        congr 2
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (1 / s) * (ENNReal.ofReal (5 / 3 * constD) *
        ∑ v, ENNReal.ofReal (constA ^ 2 * s) * ∫⁻ p, heatCost Hd (rateAt v) (s, p)) := by
        gcongr with v
        exact hcv v
    _ = ENNReal.ofReal (5 / 3 * constD * constA ^ 2) * ∑ v, ∫⁻ p, heatCost Hd (rateAt v) (s, p) :=
        by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

lemma continuousOn_kernIntegrand (m : ℕ) (t : ℝ) :
    ContinuousOn (fun s => kernIntegrand m s t) (Set.Ioi 0) :=
  (continuousOn_kernIntegrand_joint m).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => hs)

/-- The finite Gaussian form in source coordinates. -/
def gridGaussianForm {ι : Type*} [Fintype ι] (Hd : HeatData ι) (a b : ℝ) : ℂ :=
  (Hd.h ^ 3 : ℂ) * ∑ i, ∑ j, ∑ k,
    Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
      (Kern 3 a b (Hd.u i + Hd.u j + Hd.u k) : ℂ)

lemma gridGaussianForm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    gridGaussianForm Hd a b =
      ∫ s in Set.Ioc a b, ((1 / s : ℝ) : ℂ) *
        ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s := by
  let F : ι → ι → ι → ℝ → ℂ := fun i j k s =>
    (Hd.h ^ 3 : ℂ) * (Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i) *
      (kernIntegrand 3 s (Hd.u i + Hd.u j + Hd.u k) : ℂ)
  have hint : ∀ i j k, IntegrableOn (F i j k) (Set.Ioc a b) := by
    intro i j k
    apply Integrable.const_mul
    exact (((continuousOn_kernIntegrand 3 _).mono
      ((Set.Icc_subset_Ioi_iff hab).mpr ha)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self).ofReal
  have hpt : ∀ s ∈ Set.Ioc a b,
      ((1 / s : ℝ) : ℂ) * (∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s) =
        ∑ i, ∑ j, ∑ k, F i j k s := by
    intro s hs
    rw [(Hd.integral_baseTrace hh.le (Or.inl rfl) (ha.trans hs.1)).2]
    simp only [F, Finset.mul_sum, kernIntegrand]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hint i j k]
  simp_rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint _ j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ _ k]
  simp only [gridGaussianForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [F, integral_const_mul]
  rw [integral_complex_ofReal, ← intervalIntegral.integral_of_le hab, ← Kern_eq]
  ring

/-- The constant in the grid form's bound by the sum of the three cubic energies. -/
def heatBoundConstant : ℝ :=
  (5 / 3 * constD * constA ^ 2) * 3 *
    (28 * (2 * Real.sqrt 2 * (1 + Real.sqrt (2 / Real.pi))))

lemma heatBoundConstant_nonneg : 0 ≤ heatBoundConstant := by
  have := constD_spec.1
  unfold heatBoundConstant
  positivity

/-- The fixed Gaussian scale interval is bounded by the initial cubic energy. -/
theorem gridGaussianForm_cubic_bound {ι : Type*} [Fintype ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {a b : ℝ} (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ‖gridGaussianForm Hd a b‖ ≤ heatBoundConstant * ∑ v, Hd.nCube v := by
  classical
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hα1 : ∀ v k, 1 ≤ rateAt v k := by
    intro v k
    rcases rateAt_cases v k with h | h <;> norm_num [h]
  have hα2 : ∀ v k, rateAt v k ≤ 2 := by
    intro v k
    rcases rateAt_cases v k with h | h <;> norm_num [h]
  have hm := fun v => heatCost_aemeasurable Hd hh (hα1 v) (hα2 v) ha0 hab
  let c := 5 / 3 * constD * constA ^ 2
  let B := 28 * (2 * Real.sqrt 2 * (1 + Real.sqrt (2 / Real.pi))) * ∑ v, Hd.nCube v
  have hc : 0 ≤ c := by have := constD_spec.1; dsimp [c]; positivity
  have hB : 0 ≤ B := by
    dsimp [B, HeatData.nCube]
    positivity
  have he : ∀ v, ∫⁻ z, heatCost Hd (rateAt v) z
      ∂((volume.restrict (Set.Ioc a b)).prod volume) ≤ ENNReal.ofReal B := fun v =>
    heatCost_interval_bound Hd hk hu hh (rateAt_cases v) (rateAt_sum v) ha hab
  have hb : ENNReal.ofReal ‖gridGaussianForm Hd a b‖ ≤
      ENNReal.ofReal c * ∑ _v : Fin 3, ENNReal.ofReal B := by
    rw [ofReal_norm, gridGaussianForm_eq Hd hh ha0 hab]
    refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
    calc
      ∫⁻ s in Set.Ioc a b,
          ‖((1 / s : ℝ) : ℂ) * ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ ≤
          ∫⁻ s in Set.Ioc a b, ENNReal.ofReal c *
            ∑ v, ∫⁻ p, heatCost Hd (rateAt v) (s, p) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact heatTrace_bound Hd hh (ha0.trans hs.1)
      _ = ENNReal.ofReal c * ∑ v, ∫⁻ z, heatCost Hd (rateAt v) z
          ∂((volume.restrict (Set.Ioc a b)).prod volume) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        · congr 1
          exact Finset.sum_congr rfl fun v _ => (lintegral_prod _ (hm v)).symm
        · intro v _
          exact (hm v).lintegral_prod_right'
      _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum fun v _ => he v)
  have heq : ENNReal.ofReal c * ∑ _v : Fin 3, ENNReal.ofReal B =
      ENNReal.ofReal (heatBoundConstant * ∑ v, Hd.nCube v) := by
    rw [Fin.sum_univ_three, ← ENNReal.ofReal_add hB hB,
      ← ENNReal.ofReal_add (add_nonneg hB hB) hB, ← ENNReal.ofReal_mul hc]
    congr 1
    dsimp [c, B, heatBoundConstant]
    ring
  rw [heq] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by
    apply mul_nonneg heatBoundConstant_nonneg
    exact Finset.sum_nonneg fun v _ => by dsimp [HeatData.nCube]; positivity)).mp hb

lemma nNorm_cube {ι : Type*} [Fintype ι] (h : ℝ) (A : Matrix ι ι ℂ) :
    nNorm h A ^ 3 = h ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 3 := by
  rw [nNorm, ← Real.rpow_natCast,
    ← Real.rpow_mul (mul_nonneg (sq_nonneg h) (by positivity))]
  norm_num

/-- Rescale each input edge matrix by its own complex scalar, leaving the grid fixed. -/
def scaleHeatData {ι : Type*} (Hd : HeatData ι) (c : Fin 3 → ℂ) : HeatData ι :=
  ⟨Hd.u, Hd.h, fun v => c v • Hd.A v⟩

lemma gridGaussianForm_scale {ι : Type*} [Fintype ι]
    (Hd : HeatData ι) (c : Fin 3 → ℂ) (a b : ℝ) :
    gridGaussianForm (scaleHeatData Hd c) a b =
      c 0 * c 1 * c 2 * gridGaussianForm Hd a b := by
  simp only [gridGaussianForm, scaleHeatData, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

lemma nCube_scale {ι : Type*} [Fintype ι]
    (Hd : HeatData ι) (c : Fin 3 → ℂ) (v : Fin 3) :
    (scaleHeatData Hd c).nCube v = ‖c v‖ ^ 3 * Hd.nCube v := by
  simp only [HeatData.nCube, scaleHeatData, Matrix.smul_apply, smul_eq_mul,
    norm_mul, mul_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Trilinearity converts the cubic energy estimate to a product of three L³ norms. -/
theorem gridGaussianForm_bound {ι : Type*} [Fintype ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {a b : ℝ} (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ‖gridGaussianForm Hd a b‖ ≤ 3 * heatBoundConstant *
      nNorm Hd.h (Hd.A 0) * nNorm Hd.h (Hd.A 1) * nNorm Hd.h (Hd.A 2) := by
  classical
  let N : Fin 3 → ℝ := fun v => nNorm Hd.h (Hd.A v)
  have hN0 : ∀ v, 0 ≤ N v := fun v => by dsimp [N, nNorm]; positivity
  by_cases hN : ∀ v, 0 < N v
  · let c : Fin 3 → ℂ := fun v => ((N v)⁻¹ : ℝ)
    let D := scaleHeatData Hd c
    have hD : ∀ v, D.nCube v = 1 := by
      intro v
      rw [show D.nCube v = ‖c v‖ ^ 3 * Hd.nCube v from nCube_scale Hd c v]
      have he : ‖c v‖ = (N v)⁻¹ := by
        simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hN v))]
      rw [he, show Hd.nCube v = N v ^ 3 from (nNorm_cube Hd.h (Hd.A v)).symm]
      field_simp [(hN v).ne']
    have hb := gridGaussianForm_cubic_bound D hk hu hh ha hab
    simp only [hD, Fin.sum_univ_three] at hb
    rw [gridGaussianForm_scale, norm_mul, norm_mul, norm_mul] at hb
    have hc : ∀ v, ‖c v‖ = (N v)⁻¹ := fun v => by
      simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hN v))]
    simp only [hc] at hb
    have hp : 0 < N 0 * N 1 * N 2 := mul_pos (mul_pos (hN 0) (hN 1)) (hN 2)
    have hb' : (N 0 * N 1 * N 2)⁻¹ * ‖gridGaussianForm Hd a b‖ ≤
        3 * heatBoundConstant := by
      simpa only [mul_inv, mul_comm heatBoundConstant 3, show (1 + 1 + 1 : ℝ) = 3 by norm_num]
        using hb
    calc
      ‖gridGaussianForm Hd a b‖ =
          (N 0 * N 1 * N 2) * ((N 0 * N 1 * N 2)⁻¹ * ‖gridGaussianForm Hd a b‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
      _ ≤ (N 0 * N 1 * N 2) * (3 * heatBoundConstant) :=
        mul_le_mul_of_nonneg_left hb' hp.le
      _ = _ := by dsimp [N]; ring
  · push Not at hN
    obtain ⟨v, hv⟩ := hN
    have hz : N v = 0 := le_antisymm hv (hN0 v)
    have hA : Hd.A v = 0 := eq_zero_of_nNorm_eq_zero hh hz
    have hg : gridGaussianForm Hd a b = 0 := by
      fin_cases v
      · change Hd.A 0 = 0 at hA
        simp [gridGaussianForm, hA]
      · change Hd.A 1 = 0 at hA
        simp [gridGaussianForm, hA]
      · change Hd.A 2 = 0 at hA
        simp [gridGaussianForm, hA]
    rw [hg, norm_zero]
    have hC := heatBoundConstant_nonneg
    change 0 ≤ 3 * heatBoundConstant * N 0 * N 1 * N 2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (hN0 0)) (hN0 1)) (hN0 2)

end

end Triangular.Auto

namespace Triangular.Auto

open MeasureTheory Filter Topology Matrix Real

open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section

lemma exists_fin_shift {R : ℕ} {w : ℤ} (h : |w| ≤ R) :
    ∃ i : Fin (2 * R + 1), (i : ℤ) - R = w := by
  have := neg_abs_le w
  have := le_abs_self w
  refine ⟨⟨(w + R).toNat, by omega⟩, ?_⟩
  change (((w + R).toNat : ℕ) : ℤ) - R = w
  omega

lemma sum_eq_tsum_of_injective {T E : Type*} [Fintype T] [NormedAddCommGroup E]
    {d : ℕ} (e : T → (Fin d → ℤ)) (he : Function.Injective e)
    (f : (Fin d → ℤ) → E) (hs : ∀ z, f z ≠ 0 → z ∈ Set.range e) :
    ∑ t, f (e t) = ∑' z, f z := by
  rw [← he.tsum_eq (fun z hz => hs z hz), tsum_fintype]

lemma int_bounds_of_ne_zero {F : ℝ × ℝ → ℂ} {ρ : ℝ}
    (hF : ∀ p, ρ < ‖p‖ → F p = 0) {N : ℕ} (hN : 0 < N)
    {a b : ℤ} (hp : F ((a : ℝ) / N, (b : ℝ) / N) ≠ 0) :
    (|a| : ℝ) ≤ ρ * N ∧ (|b| : ℝ) ≤ ρ * N := by
  have h : ‖((a : ℝ) / N, (b : ℝ) / N)‖ ≤ ρ :=
    not_lt.1 fun h => hp (hF _ h)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_div,
    abs_of_pos hN', div_le_iff₀ hN', Int.cast_abs] using h

/-- The three cyclic input factors paired with the Gaussian interval kernel. -/
def sourceGaussianIntegrand (F : Fin 3 → ℝ × ℝ → ℂ) (a b : ℝ)
    (x : Fin 3 → ℝ) : ℂ :=
  F 0 (x 0, x 1) * F 1 (x 1, x 2) * F 2 (x 2, x 0) *
    (Kern 3 a b (x 0 + x 1 + x 2) : ℂ)

theorem sourceGaussian_lattice_bound (F : Fin 3 → ℝ × ℝ → ℂ) {ρ : ℝ}
    (hF : ∀ v p, ρ < ‖p‖ → F v p = 0)
    {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : ((N : ℝ)⁻¹) ^ 2 ≤ a) (hab : a ≤ b) :
    ‖((N : ℝ)⁻¹) ^ 3 • ∑' z : Fin 3 → ℤ,
        sourceGaussianIntegrand F a b (fun i => (z i : ℝ) / N)‖ ≤
      3 * heatBoundConstant *
        ∏ v, (((N : ℝ)⁻¹) ^ 2 *
          ∑' z : Fin 2 → ℤ, ‖F v ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖ ^ 3) ^
            (1 / 3 : ℝ) := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  let R : ℕ := ⌈ρ * N⌉₊
  let kk : Fin (2 * R + 1) → ℤ := fun i => (i : ℤ) - R
  have hk : Function.Injective kk := by
    intro i j hij
    simp only [kk, sub_left_inj] at hij
    exact Fin.ext (by exact_mod_cast hij)
  have hfind : ∀ w : ℤ, (|w| : ℝ) ≤ ρ * N → ∃ i, kk i = w := by
    intro w hw
    exact exists_fin_shift (by exact_mod_cast hw.trans (Nat.le_ceil _))
  let u : Fin (2 * R + 1) → ℝ := fun i => (kk i : ℝ) / N
  let Hd : HeatData (Fin (2 * R + 1)) :=
    ⟨u, (N : ℝ)⁻¹, fun v i j => F v (u i, u j)⟩
  have hn (v : Fin 3) : nNorm Hd.h (Hd.A v) =
      (((N : ℝ)⁻¹) ^ 2 *
        ∑' z : Fin 2 → ℤ, ‖F v ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖ ^ 3) ^
          (1 / 3 : ℝ) := by
    let e : Fin (2 * R + 1) × Fin (2 * R + 1) → (Fin 2 → ℤ) :=
      fun t => ![kk t.1, kk t.2]
    have he : Function.Injective e := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ hij
      have h0 := congrFun hij 0
      have h1 := congrFun hij 1
      simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      rw [hk h0, hk h1]
    have hs : ∀ z : Fin 2 → ℤ,
        ‖F v ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖ ^ 3 ≠ 0 → z ∈ Set.range e := by
      intro z hz
      obtain ⟨b0, b1⟩ := int_bounds_of_ne_zero (hF v) hN
        (a := z 0) (b := z 1) (fun h => hz (by simp [h]))
      obtain ⟨i, hi⟩ := hfind (z 0) b0
      obtain ⟨j, hj⟩ := hfind (z 1) b1
      refine ⟨(i, j), ?_⟩
      funext l
      fin_cases l <;> simp [e, hi, hj]
    unfold nNorm
    rw [← sum_eq_tsum_of_injective e he _ hs, Fintype.sum_prod_type]
    rfl
  have hsum : gridGaussianForm Hd a b =
      ((N : ℝ)⁻¹) ^ 3 • ∑' z : Fin 3 → ℤ,
        sourceGaussianIntegrand F a b (fun i => (z i : ℝ) / N) := by
    let e : Fin (2 * R + 1) × Fin (2 * R + 1) × Fin (2 * R + 1) →
        (Fin 3 → ℤ) := fun t => ![kk t.1, kk t.2.1, kk t.2.2]
    have he : Function.Injective e := by
      rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hij
      have h0 := congrFun hij 0
      have h1 := congrFun hij 1
      have h2 := congrFun hij 2
      simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] at h0 h1 h2
      rw [hk h0, hk h1, hk h2]
    have hs : ∀ z, sourceGaussianIntegrand F a b
        (fun i => (z i : ℝ) / N) ≠ 0 → z ∈ Set.range e := by
      intro z hz
      have hp := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1
      obtain ⟨b0, b1⟩ := int_bounds_of_ne_zero (hF 0) hN
        (mul_ne_zero_iff.mp hp.1).1
      obtain ⟨_, b2⟩ := int_bounds_of_ne_zero (hF 1) hN
        (mul_ne_zero_iff.mp hp.1).2
      obtain ⟨i, hi⟩ := hfind (z 0) b0
      obtain ⟨j, hj⟩ := hfind (z 1) b1
      obtain ⟨k, hk'⟩ := hfind (z 2) b2
      refine ⟨(i, j, k), ?_⟩
      funext l
      fin_cases l <;> simp [e, hi, hj, hk']
    rw [← sum_eq_tsum_of_injective e he _ hs, Fintype.sum_prod_type,
      Fintype.sum_congr _ _ fun i => Fintype.sum_prod_type _]
    simp only [gridGaussianForm, sourceGaussianIntegrand, Hd, u, e,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Complex.real_smul, Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_pow]
  have h := gridGaussianForm_bound Hd hk (fun i => by dsimp [Hd, u]; ring)
    (inv_pos.mpr hN') ha hab
  rw [hsum, hn, hn, hn] at h
  simpa [Fin.prod_univ_succ, mul_assoc] using h

lemma exists_support_bound {f : ℝ × ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ ρ, 0 ≤ ρ ∧ ∀ p, ρ < ‖p‖ → f p = 0 := by
  obtain ⟨r, hr⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨max r 0, le_max_right _ _, fun p hp => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hr h
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left r 0]

lemma integral_fin2_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ × ℝ → E) :
    ∫ x : Fin 2 → ℝ, f (x 0, x 1) = ∫ p, f p :=
  (volume_preserving_finTwoArrow ℝ).integral_comp' (g := f)

lemma tendsto_lattice_norm_cube {Φ : ℝ × ℝ → ℂ} (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2 * ∑' z : Fin 2 → ℤ, ‖Φ ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖
      ^ 3) atTop (𝓝 (∫ p, ‖Φ p‖ ^ 3)) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨ρ, hρ, hΦ⟩ := exists_support_bound hs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h := lattice_sampling_dominated_convergence (d := 2)
    (fun x : Fin 2 → ℝ => ‖Φ (x 0, x 1)‖ ^ 3) ⟨C ^ 3, fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 3⟩
    ⟨ρ, fun x hx => by
      have : ρ < ‖(x 0, x 1)‖ := by
        by_contra hcon
        push Not at hcon
        rw [Prod.norm_def, max_le_iff] at hcon
        refine absurd hx (not_lt.2 ((pi_norm_le_iff_of_nonneg hρ).2 fun i => ?_))
        fin_cases i
        · exact hcon.1
        · exact hcon.2
      simp [hΦ _ this]⟩ ∅ (fun x _ => by fun_prop)
  rw [integral_fin2_eq (fun p => ‖Φ p‖ ^ 3)] at h
  simpa only [smul_eq_mul] using h

lemma sourceGaussian_continuous (F : Fin 3 → ℝ × ℝ → ℂ)
    (hF : ∀ v, Continuous (F v)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Continuous (sourceGaussianIntegrand F a b) := by
  have hK := continuous_Kern 3 ha hab
  unfold sourceGaussianIntegrand
  fun_prop

lemma sourceGaussian_support (F : Fin 3 → ℝ × ℝ → ℂ) {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hF : ∀ v p, ρ < ‖p‖ → F v p = 0)
    (x : Fin 3 → ℝ) (hx : ρ < ‖x‖) :
    sourceGaussianIntegrand F a b x = 0 := by
  by_cases h0 : F 0 (x 0, x 1) = 0
  · simp [sourceGaussianIntegrand, h0]
  by_cases h1 : F 1 (x 1, x 2) = 0
  · simp [sourceGaussianIntegrand, h1]
  have hp : ‖(x 0, x 1)‖ ≤ ρ := not_lt.1 fun h => h0 (hF 0 _ h)
  have hq : ‖(x 1, x 2)‖ ≤ ρ := not_lt.1 fun h => h1 (hF 1 _ h)
  rw [Prod.norm_def, max_le_iff] at hp hq
  have : ‖x‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ).2 (by
    intro i
    fin_cases i
    · exact hp.1
    · exact hp.2
    · exact hq.2)
  exact False.elim (not_lt_of_ge this hx)

theorem sourceGaussian_compact_bound (F : Fin 3 → ℝ × ℝ → ℂ)
    (hc : ∀ v, Continuous (F v)) (hs : ∀ v, HasCompactSupport (F v))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x, sourceGaussianIntegrand F a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (∫ p, ‖F v p‖ ^ 3) ^ (1 / 3 : ℝ) := by
  classical
  choose ρ hρ hF using fun v => exists_support_bound (hs v)
  let R := ∑ v, ρ v
  have hv (v : Fin 3) : ρ v ≤ R :=
    Finset.single_le_sum (fun i _ => hρ i) (Finset.mem_univ v)
  have hR : 0 ≤ R := Finset.sum_nonneg fun v _ => hρ v
  have hsupp : ∀ v p, R < ‖p‖ → F v p = 0 :=
    fun v p hp => hF v p ((hv v).trans_lt hp)
  have hcomp : HasCompactSupport (sourceGaussianIntegrand F a b) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ) R)
      (fun x hx => sourceGaussian_support F hR hsupp x (by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))
  have hcont := sourceGaussian_continuous F hc ha hab
  have hlim := lattice_sampling_dominated_convergence
    (sourceGaussianIntegrand F a b)
    (hcont.bounded_above_of_compact_support hcomp)
    ⟨R, sourceGaussian_support F hR hsupp⟩ ∅ (fun x _ => hcont.continuousAt)
  have hnorm (v : Fin 3) := (tendsto_lattice_norm_cube (hc v) (hs v)).rpow_const
    (p := 1 / 3) (Or.inr (by norm_num))
  have hprod := (tendsto_finsetProd Finset.univ (fun v _ => hnorm v)).const_mul
    (3 * heatBoundConstant)
  refine le_of_tendsto_of_tendsto hlim.norm hprod ?_
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using h.pow 2
  filter_upwards [eventually_gt_atTop 0, hzero.eventually (ge_mem_nhds ha)]
    with N hN hNa
  exact sourceGaussian_lattice_bound F hsupp hN hNa hab

/-- A radial cutoff equal to one on the ball of radius `n` and zero past radius `n + 1`. -/
def compactCutoff (n : ℕ) (p : ℝ × ℝ) : ℝ := max 0 (min 1 (n + 1 - ‖p‖))

lemma compactCutoff_bounds (n : ℕ) (p : ℝ × ℝ) :
    0 ≤ compactCutoff n p ∧ compactCutoff n p ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma compactCutoff_continuous (n : ℕ) : Continuous (compactCutoff n) := by
  unfold compactCutoff
  fun_prop

lemma compactCutoff_support (n : ℕ) : HasCompactSupport (compactCutoff n) := by
  refine HasCompactSupport.intro (isCompact_closedBall 0 (n + 1 : ℝ)) ?_
  intro p hp
  have h : (n : ℝ) + 1 < ‖p‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hp
  simp [compactCutoff, min_eq_right (by linarith : (n : ℝ) + 1 - ‖p‖ ≤ 1),
    max_eq_left (by linarith : (n : ℝ) + 1 - ‖p‖ ≤ 0)]

lemma compactCutoff_tendsto (p : ℝ × ℝ) :
    Tendsto (fun n => compactCutoff n p) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖p‖)]
    with n hn
  simp [compactCutoff, min_eq_left (by linarith : (1 : ℝ) ≤ n + 1 - ‖p‖)]

lemma toReal_eLpNorm_three {F : ℝ × ℝ → ℂ} (hF : MemLp F 3) :
    (eLpNorm F 3).toReal = (∫ p, ‖F p‖ ^ 3) ^ (1 / 3 : ℝ) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  norm_num

theorem sourceGaussian_bound (F : Fin 3 → ℝ × ℝ → ℂ)
    (hc : ∀ v, Continuous (F v)) (hL : ∀ v, MemLp (F v) 3)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hi : Integrable (sourceGaussianIntegrand F a b)) :
    ‖∫ x, sourceGaussianIntegrand F a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (eLpNorm (F v) 3).toReal := by
  let f (n : ℕ) (v : Fin 3) (p : ℝ × ℝ) : ℂ := compactCutoff n p * F v p
  have hfc (n : ℕ) (v : Fin 3) : Continuous (f n v) :=
    (Complex.continuous_ofReal.comp (compactCutoff_continuous n)).mul (hc v)
  have hfs (n : ℕ) (v : Fin 3) : HasCompactSupport (f n v) :=
    ((compactCutoff_support n).comp_left Complex.ofReal_zero).mul_right
  have hfn (n : ℕ) (v : Fin 3) (p : ℝ × ℝ) : ‖f n v p‖ ≤ ‖F v p‖ := by
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (compactCutoff_bounds n p).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (compactCutoff_bounds n p).2
  have hLp (n : ℕ) (v : Fin 3) :
      (eLpNorm (f n v) 3).toReal ≤ (eLpNorm (F v) 3).toReal :=
    ENNReal.toReal_mono (hL v).eLpNorm_ne_top (eLpNorm_mono (hfc n v).aestronglyMeasurable (hfn n
        v))
  have hfbound (n : ℕ) : ‖∫ x, sourceGaussianIntegrand (f n) a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (eLpNorm (F v) 3).toReal := by
    have h := sourceGaussian_compact_bound (f n) (hfc n) (hfs n) ha hab
    simp_rw [← toReal_eLpNorm_three ((hfc n _).memLp_of_hasCompactSupport (hfs n _))] at h
    refine h.trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) (fun v _ => hLp n v)) ?_)
    positivity [heatBoundConstant_nonneg]
  have hlim : Tendsto (fun n => ∫ x, sourceGaussianIntegrand (f n) a b x)
      atTop (𝓝 (∫ x, sourceGaussianIntegrand F a b x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖sourceGaussianIntegrand F a b x‖)
    · intro n
      exact (sourceGaussian_continuous (f n) (hfc n) ha hab).aestronglyMeasurable
    · exact hi.norm
    · intro n
      filter_upwards [] with x
      simp only [sourceGaussianIntegrand, norm_mul]
      gcongr <;> apply hfn
    · filter_upwards [] with x
      have hf (v : Fin 3) (p : ℝ × ℝ) :
          Tendsto (fun n => f n v p) atTop (𝓝 (F v p)) := by
        simpa [f] using
          ((Complex.continuous_ofReal.tendsto 1).comp (compactCutoff_tendsto p)).mul_const (F v p)
      exact (((hf 0 _).mul (hf 1 _)).mul (hf 2 _)).mul_const _
  exact le_of_tendsto' hlim.norm hfbound

end

end Triangular.Auto
