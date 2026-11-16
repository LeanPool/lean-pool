/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.WeakDerivative
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.Tilted
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.ZeroGradient
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# The kernel of the closed unit gradient of a tilted law

For a log-concave law `ν = m.tilted (-U)` with full-dimensional support and continuous potential
`U`, an element `h` of the domain of the closed unit gradient `Tbar` with `Tbar h = 0` has zero weak
gradient against Haar measure: `∫ h ∂_w φ dm = 0` for every `φ ∈ C_c^∞` and every direction `w`.
The proof passes to the limit in integration by parts along a smooth compactly supported graph
sequence (`exists_seq_smooth_tendsto_graph`). The change of measure `dm = Z e^{U} dν`, with
`Z = ∫ e^{-U} dm`, turns the Haar integrals into `L²(ν)` pairings with continuous compactly
supported weights. Elements of `L²(ν)` are locally integrable for `m`, because `e^{-U}` is bounded
below on compact sets. With `Energy.Euclidean.exists_ae_eq_const_of_integral_mul_fderiv_eq_zero`
this shows that `Tbar h = 0` forces `h` to be the constant `∫ h dν`
(`eq_const_mean_of_closedWeightedOperator_eq_zero`); the converse and the resulting identification
of `ker Tbar` with the constants are in `HeatSemigroup/SpectralGap/Curvature.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}


omit [InnerProductSpace ℝ V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Change of measure from Haar measure to the tilted law: with `Z = ∫ e^{-U} dm`,
`∫ F dm = ∫ Z e^{U} F dν` for every `F`. -/
theorem integral_eq_integral_mul_exp (hνU : (ν : Measure V) = m.tilted (-U)) (F : V → ℝ) :
    ∫ x, F x ∂m = ∫ x, ((∫ y, Real.exp (-U y) ∂m) * Real.exp (U x)) * F x ∂(ν : Measure V) := by
  have hInt : Integrable (fun x => Real.exp (-U x)) m := by
    by_contra hnot
    have ht : m.tilted (-U) = 0 := by
      apply tilted_of_not_integrable
      exact hnot
    have hzero : (ν : Measure V) Set.univ = 0 := by
      rw [hνU, ht]
      simp
    have hone : (ν : Measure V) Set.univ = 1 := by
      simp
    rw [hzero] at hone
    norm_num at hone
  have hZ : 0 < ∫ y, Real.exp (-U y) ∂m := by
    exact integral_exp_pos hInt
  rw [hνU, integral_tilted]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv]
  have hZ0 : (∫ y, Real.exp (-U y) ∂m) ≠ 0 := ne_of_gt hZ
  have hExp : Real.exp (-U x) * Real.exp (U x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    F x =
        F x * (Real.exp (-U x) * Real.exp (U x)) := by
          rw [hExp]
          ring
    _ =
        (Real.exp (-U x) * (∫ y, Real.exp (-U y) ∂m)⁻¹) *
          ((∫ y, Real.exp (-U y) ∂m) * Real.exp (U x) * F x) := by
            field_simp [hZ0]

omit [InnerProductSpace ℝ V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- On a compact set Haar measure is dominated by a finite multiple of the tilted law, because
the density `e^{-U}/Z` is bounded below there. -/
theorem restrict_le_smul_of_eq_tilted (hνU : (ν : Measure V) = m.tilted (-U)) (hU : Continuous U)
    {K : Set V} (hK : IsCompact K) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ m.restrict K ≤ c • (ν : Measure V) := by
  have hInt : Integrable (fun x => Real.exp (-U x)) m :=
    integrable_exp_neg_of_eq_tilted hνU
  let Z : ℝ := ∫ y, Real.exp (-U y) ∂m
  have hZ : 0 < Z := by
    dsimp [Z]
    rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hInt]
    simp [Function.support, (Real.exp_pos _).ne', Measure.measure_univ_pos, NeZero.ne m]
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ K, U x ≤ M := by
    by_cases hKne : K.Nonempty
    · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne hU.continuousOn
      exact ⟨U x, fun y hy => hmax hy⟩
    · exact ⟨0, fun x hx => (hKne ⟨x, hx⟩).elim⟩
  refine ⟨ENNReal.ofReal (Z * Real.exp M), ENNReal.ofReal_ne_top, ?_⟩
  refine Measure.le_intro fun s hs _ => ?_
  rw [Measure.restrict_apply hs, Measure.smul_apply, hνU, Measure.tilted,
    withDensity_apply _ hs, smul_eq_mul]
  calc
    m (s ∩ K) = ∫⁻ x in s ∩ K, 1 ∂m := by simp
    _ ≤ ∫⁻ x in s ∩ K,
        ENNReal.ofReal (Z * Real.exp M) *
          ENNReal.ofReal (Real.exp ((-U) x) / Z) ∂m := by
      refine setLIntegral_mono' (hs.inter hK.measurableSet) ?_
      intro x hx
      have hprod :
          (Z * Real.exp M) * (Real.exp ((-U) x) / Z) =
            Real.exp (M - U x) := by
        change (Z * Real.exp M) * (Real.exp (-U x) / Z) =
          Real.exp (M - U x)
        calc
          (Z * Real.exp M) * (Real.exp (-U x) / Z) =
              Real.exp M * Real.exp (-U x) := by
                field_simp [hZ0]
          _ = Real.exp (M + (-U x)) := by
                rw [← Real.exp_add]
          _ = Real.exp (M - U x) := by ring_nf
      calc
        (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp (M - U x)) := by
          rw [ENNReal.one_le_ofReal]
          exact (Real.one_le_exp_iff).2 (sub_nonneg.mpr (hM x hx.2))
        _ = ENNReal.ofReal (Z * Real.exp M) *
              ENNReal.ofReal (Real.exp ((-U) x) / Z) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact congrArg ENNReal.ofReal hprod.symm
    _ ≤ ∫⁻ x in s,
        ENNReal.ofReal (Z * Real.exp M) *
          ENNReal.ofReal (Real.exp ((-U) x) / Z) ∂m :=
      lintegral_mono_set Set.inter_subset_left
    _ = ENNReal.ofReal (Z * Real.exp M) *
        (∫⁻ x in s, ENNReal.ofReal (Real.exp ((-U) x) / Z) ∂m) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

omit [SecondCountableTopology V] in
/-- Every `L²(ν)` class is locally integrable for Haar measure. -/
theorem locallyIntegrable_coeFn (hνU : (ν : Measure V) = m.tilted (-U)) (hU : Continuous U)
    (f : Lp ℝ 2 (ν : Measure V)) : LocallyIntegrable (f : V → ℝ) m := by
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  obtain ⟨c, hc, hle⟩ := restrict_le_smul_of_eq_tilted m hνU hU hK
  have h1 : Integrable (f : V → ℝ) (ν : Measure V) :=
    (Lp.memLp f).integrable (by norm_num)
  exact (h1.smul_measure hc).mono_measure hle

/-- `L²(ν)` convergence gives convergence of Haar integrals against a continuous compactly
supported weight. -/
theorem tendsto_integral_mul_of_tendsto (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) {g : ℕ → V → ℝ} (hg : ∀ n, MemLp (g n) 2 (ν : Measure V))
    {f : Lp ℝ 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 f))
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ x, g n x * ψ x ∂m) atTop (𝓝 (∫ x, f x * ψ x ∂m)) := by
  let Z : ℝ := ∫ y, Real.exp (-U y) ∂m
  let Ψ : V → ℝ := fun x => (Z * Real.exp (U x)) * ψ x
  have hInt : Integrable (fun x => Real.exp (-U x)) m :=
    integrable_exp_neg_of_eq_tilted hνU
  have hΨcont : Continuous Ψ := by
    dsimp [Ψ]
    exact (continuous_const.mul (Real.continuous_exp.comp hU)).mul hψ
  have hsupport : Function.support Ψ ⊆ Function.support ψ := by
    intro x hx
    by_contra h
    have hψx : ψ x = 0 := by
      simpa [Function.mem_support] using h
    have hΨx : Ψ x = 0 := by
      simp [Ψ, hψx]
    exact hx hΨx
  have hΨc : HasCompactSupport Ψ := by
    exact hψc.mono hsupport
  have hΨ : MemLp Ψ 2 (ν : Measure V) :=
    hΨcont.memLp_of_hasCompactSupport hΨc
  have hpair :
      ∀ a : Lp ℝ 2 (ν : Measure V),
        (∫ x, (a : V → ℝ) x * Ψ x ∂(ν : Measure V)) =
          ⟪a, hΨ.toLp Ψ⟫ := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hΨ] with x hx
    rw [hx]
    exact mul_comm _ _
  have hseq :
      ∀ n, (∫ x, g n x * ψ x ∂m) =
        ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫ := by
    intro n
    calc
      ∫ x, g n x * ψ x ∂m =
          ∫ x, (Z * Real.exp (U x)) * (g n x * ψ x) ∂(ν : Measure V) := by
            simpa [Z] using
              (integral_eq_integral_mul_exp m hνU (fun x => g n x * ψ x))
      _ = ∫ x, ((hg n).toLp (g n) : V → ℝ) x * Ψ x ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [MemLp.coeFn_toLp (hg n)] with x hx
            dsimp [Ψ]
            rw [hx]
            ring
      _ = ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫ := hpair ((hg n).toLp (g n))
  have htarget :
      (∫ x, f x * ψ x ∂m) = ⟪f, hΨ.toLp Ψ⟫ := by
    calc
      ∫ x, f x * ψ x ∂m =
          ∫ x, (Z * Real.exp (U x)) * ((f : V → ℝ) x * ψ x) ∂(ν : Measure V) := by
            simpa [Z] using
              (integral_eq_integral_mul_exp m hνU
                (fun x => (f : V → ℝ) x * ψ x))
      _ = ∫ x, (f : V → ℝ) x * Ψ x ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [Ψ]
            ring
      _ = ⟪f, hΨ.toLp Ψ⟫ := hpair f
  have hinner :
      Tendsto
        (fun n => ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫)
        atTop (𝓝 ⟪f, hΨ.toLp Ψ⟫) :=
    hlim.inner tendsto_const_nhds
  rw [show (fun n => ∫ x, g n x * ψ x ∂m) =
      (fun n => ⟪(hg n).toLp (g n), hΨ.toLp Ψ⟫) from funext hseq]
  rw [show (∫ x, f x * ψ x ∂m) = ⟪f, hΨ.toLp Ψ⟫ from htarget]
  exact hinner

/-- The vector-valued version: `L²(ν; V)` convergence of fields gives convergence of
`∫ ψ ⟪G_n, w⟫ dm` for a continuous compactly supported weight `ψ` and a direction `w`. -/
theorem tendsto_integral_mul_inner_of_tendsto (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) {G : ℕ → V → V} (hG : ∀ n, MemLp (G n) 2 (ν : Measure V))
    {F : Lp V 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 F))
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (w : V) :
    Tendsto (fun n => ∫ x, ψ x * ⟪G n x, w⟫ ∂m) atTop (𝓝 (∫ x, ψ x * ⟪F x, w⟫ ∂m)) := by
  let Z : ℝ := ∫ y, Real.exp (-U y) ∂m
  let W : V → V := fun x => ((Z * Real.exp (U x)) * ψ x) • w
  have hWcont : Continuous W := by
    dsimp [W]
    fun_prop
  have hWsupport : Function.support W ⊆ Function.support ψ := by
    intro x hx
    by_contra h
    have hψx : ψ x = 0 := by
      simpa [Function.mem_support] using h
    have hWx : W x = 0 := by
      simp [W, hψx]
    exact hx hWx
  have hWc : HasCompactSupport W := by
    exact hψc.mono hWsupport
  have hW : MemLp W 2 (ν : Measure V) :=
    hWcont.memLp_of_hasCompactSupport hWc
  have hpair :
      ∀ a : Lp V 2 (ν : Measure V),
        (∫ x, ⟪(a : V → V) x, W x⟫ ∂(ν : Measure V)) =
          ⟪a, hW.toLp W⟫ := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hW] with x hx
    rw [hx]
  have hseq :
      ∀ n, (∫ x, ψ x * ⟪G n x, w⟫ ∂m) =
        ⟪(hG n).toLp (G n), hW.toLp W⟫ := by
    intro n
    calc
      ∫ x, ψ x * ⟪G n x, w⟫ ∂m =
          ∫ x, (Z * Real.exp (U x)) *
            (ψ x * ⟪G n x, w⟫) ∂(ν : Measure V) := by
              simpa [Z] using
                (integral_eq_integral_mul_exp m hνU
                  (fun x => ψ x * ⟪G n x, w⟫))
      _ = ∫ x, ⟪((hG n).toLp (G n) : V → V) x, W x⟫
            ∂(ν : Measure V) := by
              apply integral_congr_ae
              filter_upwards [MemLp.coeFn_toLp (hG n)] with x hx
              dsimp [W]
              rw [hx]
              simp only [inner_smul_right]
              ring
      _ = ⟪(hG n).toLp (G n), hW.toLp W⟫ :=
        hpair ((hG n).toLp (G n))
  have htarget :
      (∫ x, ψ x * ⟪F x, w⟫ ∂m) = ⟪F, hW.toLp W⟫ := by
    calc
      ∫ x, ψ x * ⟪F x, w⟫ ∂m =
          ∫ x, (Z * Real.exp (U x)) *
            (ψ x * ⟪(F : V → V) x, w⟫) ∂(ν : Measure V) := by
              simpa [Z] using
                (integral_eq_integral_mul_exp m hνU
                  (fun x => ψ x * ⟪(F : V → V) x, w⟫))
      _ = ∫ x, ⟪(F : V → V) x, W x⟫ ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [W]
            simp only [inner_smul_right]
            ring
      _ = ⟪F, hW.toLp W⟫ := hpair F
  have hinner :
      Tendsto
        (fun n => ⟪(hG n).toLp (G n), hW.toLp W⟫)
        atTop (𝓝 ⟪F, hW.toLp W⟫) :=
    hlim.inner tendsto_const_nhds
  rw [show (fun n => ∫ x, ψ x * ⟪G n x, w⟫ ∂m) =
      (fun n => ⟪(hG n).toLp (G n), hW.toLp W⟫) from funext hseq]
  rw [show (∫ x, ψ x * ⟪F x, w⟫ ∂m) = ⟪F, hW.toLp W⟫ from htarget]
  exact hinner

omit [SecondCountableTopology V] in
/-- Smooth integration by parts against a test: `∫ g ∂_w φ dm = -∫ φ ⟪∇g, w⟫ dm` for smooth `g`
and smooth compactly supported `φ`. -/
theorem integral_mul_fderiv_eq_neg_integral_mul_inner_gradient {g φ : V → ℝ}
    (hg : ContDiff ℝ ∞ g) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, g x * fderiv ℝ φ x w ∂m = -∫ x, φ x * ⟪gradient g x, w⟫ ∂m := by
  have hIBP :=
    Energy.Euclidean.integral_mul_fderiv_apply m hφ hφc hg w
  have hgrad :
      (∫ x, φ x * ⟪gradient g x, w⟫ ∂m) =
        ∫ x, φ x * fderiv ℝ g x w ∂m := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [inner_gradient_left]
  linarith

/-- **Weak gradient of an element of the closed domain**: for `h ∈ D(Tbar)`, smooth compactly
supported `φ` and every direction `w`, `∫ h ∂_w φ dm = -∫ φ ⟪Tbar h, w⟫ dm`. -/
theorem integral_mul_fderiv_eq_neg_integral_mul_inner (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m =
      -∫ x, φ x * ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
        Lp V 2 (ν : Measure V)) x, w⟫ ∂m := by
  obtain ⟨g, hg, hgc, h1, h2⟩ :=
    hν.exists_seq_smooth_tendsto_graph m
      (ContinuousLinearMap.id ℝ V) hi h
  have hψ : Continuous (fun x => fderiv ℝ φ x w) := by
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψc : HasCompactSupport (fun x => fderiv ℝ φ x w) := by
    exact hφc.fderiv_apply ℝ w
  have hL :
      Tendsto
        (fun n => ∫ x, g n x * fderiv ℝ φ x w ∂m)
        atTop
        (𝓝 (∫ x, (h : Lp ℝ 2 (ν : Measure V)) x *
          fderiv ℝ φ x w ∂m)) :=
    tendsto_integral_mul_of_tendsto m hνU hU
      (fun n => memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n))
      h1 hψ hψc
  let G : ℕ → V → V :=
    fun n => apply (ContinuousLinearMap.id ℝ V) (g n)
  have hG : ∀ n, MemLp (G n) 2 (ν : Measure V) := by
    intro n
    dsimp [G]
    exact
      (IsTest.of_contDiff_hasCompactSupport ν
        (ContinuousLinearMap.id ℝ V) (hg n) (hgc n)).memLp_apply
  have h2' :
      Tendsto
        (fun n => (hG n).toLp (G n))
        atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h)) := by
    simpa [G] using h2
  have hR :
      Tendsto
        (fun n => ∫ x, φ x * ⟪G n x, w⟫ ∂m)
        atTop
        (𝓝 (∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) :=
    tendsto_integral_mul_inner_of_tendsto m hνU hU hG h2'
      hφ.continuous hφc w
  have hneg :
      Tendsto
        (fun n => -(∫ x, φ x * ⟪G n x, w⟫ ∂m))
        atTop
        (𝓝 (-∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) :=
    hR.neg
  have heq :
      ∀ n, -(∫ x, φ x * ⟪G n x, w⟫ ∂m) =
        ∫ x, g n x * fderiv ℝ φ x w ∂m := by
    intro n
    simpa [G, Energy.WeightedGradient.apply_id] using
      (integral_mul_fderiv_eq_neg_integral_mul_inner_gradient
        m (hg n) hφ hφc w).symm
  have hL' :
      Tendsto
        (fun n => ∫ x, g n x * fderiv ℝ φ x w ∂m)
        atTop
        (𝓝 (-∫ x, φ x *
          ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h :
            Lp V 2 (ν : Measure V)) x, w⟫ ∂m)) := by
    exact hneg.congr heq
  exact tendsto_nhds_unique hL hL'

/-- **Zero closed gradient gives zero weak gradient**: if `Tbar h = 0`, then
`∫ h ∂_w φ dm = 0` for every `φ ∈ C_c^∞` and every `w`. -/
theorem integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : V) :
    ∫ x, (h : Lp ℝ 2 (ν : Measure V)) x * fderiv ℝ φ x w ∂m = 0 := by
  rw [integral_mul_fderiv_eq_neg_integral_mul_inner m hν hi hνU hU h hφ hφc w, h0,
    neg_eq_zero]
  have hInt : Integrable (fun x => Real.exp (-U x)) m :=
    integrable_exp_neg_of_eq_tilted hνU
  have hac : m ≪ (ν : Measure V) := by
    rw [hνU]
    exact absolutelyContinuous_tilted hInt
  apply integral_eq_zero_of_ae
  filter_upwards [
    hac.ae_le (Lp.coeFn_zero (E := V) (p := 2) (μ := (ν : Measure V)))
  ] with x _
  simp

/-- **The kernel of the closed unit gradient consists of constants**: if `Tbar h = 0`, then `h` is the
`L²(ν)` constant equal to its mean. -/
theorem eq_const_mean_of_closedWeightedOperator_eq_zero (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) :
    (h : Lp ℝ 2 (ν : Measure V)) = L2.const ν (L2.mean ν (h : Lp ℝ 2 (ν : Measure V))) := by
  obtain ⟨c, hc⟩ :=
    Energy.Euclidean.exists_ae_eq_const_of_integral_mul_fderiv_eq_zero m
      (locallyIntegrable_coeFn m hνU hU (h : Lp ℝ 2 (ν : Measure V)))
      (fun φ hφ hφc w =>
        integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero
          m hν hi hνU hU h h0 hφ hφc w)
  have hac : (ν : Measure V) ≪ m := by
    rw [hνU]
    exact tilted_absolutelyContinuous m (-U)
  have hae :
      (h : Lp ℝ 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] (fun _ : V => c) :=
    hac.ae_le hc
  have hconst :
      (L2.const ν c : Lp ℝ 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] (fun _ : V => c) :=
    L2.const_coeFn ν c
  have hL :
      (h : Lp ℝ 2 (ν : Measure V)) = L2.const ν c :=
    Lp.ext (hae.trans hconst.symm)
  rw [hL, L2.mean_const]

end FunctionalInequalities.KLS.LogConcave
