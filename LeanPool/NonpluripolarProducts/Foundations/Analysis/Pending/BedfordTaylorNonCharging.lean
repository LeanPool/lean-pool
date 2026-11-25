/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorCLN
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorExistence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BTTruncations
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PluripolarSets

/-!
# Bedford–Taylor limit measures do not charge pluripolar sets

Let `μ` be the weak limit of the mixed densities of decreasing smooth
plurisubharmonic approximations on an open set. Near a point, a local
pluripolar witness `ψ` is truncated at level `-k`; the Chern–Levine–Nirenberg
estimate with the truncated weight bounds the smooth densities of the open set
`{ψ < -k}` by `C / (S + k)` uniformly in the approximation index, where the
constant involves the `L¹` norm of `ψ` on a ball. Testing against continuous
functions increasing to the indicator of that open set transfers the bound to
`μ`. Letting `k → ∞` shows that `μ` does not charge the pole set near the point,
and a countable cover gives the global statement.

Source: Demailly, *Complex analytic and differential geometry*, III.3.11.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open MeasureLocality (integrable_of_tsupport_subset)

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- **Open sets.** A uniform bound on the smooth densities tested against
continuous functions below the indicator of an open set bounds the limit
measure of that set. -/
theorem measure_le_of_tendstoMixed_of_isOpen {U : Opens (ComplexModel n)}
    {F : Fin n → ℕ → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤) (hT : TendstoMixed U F μ)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOU : closure O ⊆ U) {B : ℝ}
    (hB : ∀ φ : ComplexModel n → ℝ, Continuous φ → (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
      (∀ z ∉ O, φ z = 0) → ∀ k, ∫ z, φ z * mixedDensity (fun i ↦ F i k) z ≤ B) :
    μ O ≤ ENNReal.ofReal B := by
  classical
  -- a monotone family of continuous functions increasing to the indicator of `O`
  obtain ⟨φ, hφc, hφ01, hφO, hφmono, hφlim⟩ : ∃ φ : ℕ → ComplexModel n → ℝ,
      (∀ j, Continuous (φ j)) ∧ (∀ j z, 0 ≤ φ j z ∧ φ j z ≤ 1) ∧ (∀ j, ∀ z ∉ O, φ j z = 0) ∧
      (∀ z, Monotone fun j ↦ φ j z) ∧
      (∀ z ∈ O, ∀ᶠ j in atTop, φ j z = 1) := by
    by_cases hne : (Oᶜ).Nonempty
    · refine ⟨fun j z ↦ min 1 (j * infDist z Oᶜ), fun j ↦ continuous_const.min
        (continuous_const.mul (continuous_infDist_pt _)), fun j z ↦ ⟨le_min zero_le_one
        (mul_nonneg j.cast_nonneg infDist_nonneg), min_le_left _ _⟩, fun j z hz ↦ ?_,
        fun z j l hjl ↦ min_le_min le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hjl)
          infDist_nonneg), fun z hz ↦ ?_⟩
      · simp [infDist_zero_of_mem (show z ∈ Oᶜ from hz)]
      · have hpos : 0 < infDist z Oᶜ :=
          (hO.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa using hz)
        obtain ⟨j, hj⟩ := exists_nat_gt (1 / infDist z Oᶜ)
        refine eventually_atTop.2 ⟨j, fun l hl ↦ min_eq_left ?_⟩
        have : 1 / infDist z Oᶜ ≤ l := hj.le.trans (by exact_mod_cast hl)
        rwa [div_le_iff₀ hpos] at this
    · have hOuniv : O = univ := by simpa [not_nonempty_iff_eq_empty] using hne
      exact ⟨fun _ _ ↦ 1, fun _ ↦ continuous_const, fun _ _ ↦ ⟨zero_le_one, le_rfl⟩,
        fun _ z hz ↦ absurd (hOuniv ▸ mem_univ z) hz, fun _ ↦ monotone_const,
        fun _ _ ↦ Eventually.of_forall fun _ ↦ rfl⟩
  have hsupp (j : ℕ) : tsupport (φ j) ⊆ closure O :=
    closure_mono fun z hz ↦ by_contra fun h ↦ hz (hφO j z h)
  have hcs (j : ℕ) : HasCompactSupport (φ j) := hOc.of_isClosed_subset (isClosed_tsupport _)
    (hsupp j)
  have hint (j : ℕ) : Integrable (φ j) μ :=
    integrable_of_tsupport_subset hμf (hφc j) (hcs j) ((hsupp j).trans hOU)
  have hle (j : ℕ) : ∫ z, φ j z ∂μ ≤ B :=
    le_of_tendsto' (hT (φ j) (hφc j) (hcs j) ((hsupp j).trans hOU)) fun k ↦
      hB (φ j) (hφc j) (hφ01 j) (hφO j) k
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (f := fun j z ↦ ENNReal.ofReal (φ j z)) (F := O.indicator 1)
    (fun j ↦ (hφc j).measurable.ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun z j l hjl ↦ ENNReal.ofReal_le_ofReal (hφmono z hjl))
    (Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ O
      · rw [indicator_of_mem hz]
        exact tendsto_const_nhds.congr' ((hφlim z hz).mono fun j hj ↦ by simp [hj])
      · rw [indicator_of_notMem hz]
        simp [hφO _ z hz])
  rw [lintegral_indicator_one hO.measurableSet] at hlim
  refine le_of_tendsto' hlim fun j ↦ ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hint j) (Eventually.of_forall fun z ↦ (hφ01 j z).1)]
  exact ENNReal.ofReal_le_ofReal (hle j)

theorem IsDecApprox.integrableOn_sub_mul {U : Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    {B : Set (ComplexModel n)} (hBm : MeasurableSet B) (hBc : IsCompact (closure B))
    (hBU : closure B ⊆ U) {D : ComplexModel n → ℝ} (hD : ContinuousOn D U) (S : ℝ) :
    IntegrableOn (fun z ↦ (S - w z) * D z) B := by
  exact (hG.weighted_sub_mul_limits hBm hBc hBU hD S).1

/-- **Local noncharging.** Near a point where the approximations live on a ball
of radius `3R`, the limit measure does not charge the pole set of a nontrivial
plurisubharmonic function defined on a preconnected neighborhood of that ball. -/
theorem measure_poleSet_inter_ball_eq_zero {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : ∀ i, IsDecApprox U (u i) (F i)) {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤) (hT : TendstoMixed U F μ)
    {z₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : closedBall z₀ (3 * R) ⊆ U)
    {V : Set (ComplexModel n)} {ψ : ComplexModel n → EReal} (hVc : IsPreconnected V)
    (hψ : PlurisubharmonicOn ψ V) (hne : ∃ a ∈ V, ψ a ≠ ⊥)
    (hbV : closedBall z₀ (3 * R) ⊆ V) :
    μ ({z | ψ z = ⊥} ∩ ball z₀ (R / 2)) = 0 := by
  classical
  set Ω' : Opens (ComplexModel n) := ⟨ball z₀ (3 * R), isOpen_ball⟩
  have hψ' : PlurisubharmonicOn ψ Ω' := fun x hx ↦ hψ x (hbV (ball_subset_closedBall hx))
  set U2 : Opens (ComplexModel n) := ⟨ball z₀ (5 * R / 2), isOpen_ball⟩
  have hU2rc : RelativelyCompactIn U2 Ω' :=
    ⟨(isCompact_closedBall z₀ _).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))⟩
  have hU2Ω' : U2 ≤ Ω' := subset_closure.trans hU2rc.2
  have hU2U : U2 ≤ U := fun z hz ↦ hball (ball_subset_closedBall (hU2Ω' hz))
  have h2U2 : closedBall z₀ (2 * R) ⊆ U2 := closedBall_subset_ball (by linarith)
  have hcb (r : ℝ) (hr : r ≤ 3 * R) : closedBall z₀ r ⊆ U :=
    (closedBall_subset_closedBall hr).trans hball
  -- uniform bound for the slots on the closed ball of radius `2R`
  choose Ci hCi using fun i ↦ (hF i).exists_abs_le (isCompact_closedBall z₀ (2 * R))
    (hcb _ (by linarith))
  set M := ∑ i, |Ci i| with hM_def
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hFM (i : Fin n) (k : ℕ) (z : ComplexModel n) (hz : z ∈ closedBall z₀ (2 * R)) :
      |F i k z| ≤ M :=
    (hCi i k z hz).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i ↦ |Ci i|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨C, hC0, hC⟩ := exists_cln_constant_weight z₀ hR hM0
  -- an upper bound for `ψ` and its integrability on the ball
  obtain ⟨S₀, hS₀, hψS₀⟩ := hψ'.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z₀ R) (closedBall_subset_ball (by linarith))
  set S : ℝ := S₀ + 1
  have hIψ : IntegrableOn (fun z ↦ (ψ z).toReal) (ball z₀ R) :=
    ((hψ.locallyIntegrableOn_toReal volume hVc hne).integrableOn_compact_subset
      ((closedBall_subset_closedBall (by linarith)).trans hbV)
      (isCompact_closedBall z₀ R)).mono_set ball_subset_closedBall
  have hfin : ∀ᵐ z ∂volume.restrict (ball z₀ R), ψ z ≠ ⊤ ∧ ψ z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset
      (ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hbV))
      (hψ.ae_finite volume hVc hne)
  set I := ∫ z in ball z₀ R, (S - (ψ z).toReal)
  have : IsFiniteMeasure (volume.restrict (ball z₀ R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hμk (k : ℕ) : μ ({z | ψ z = ⊥} ∩ ball z₀ (R / 2)) ≤
      ENNReal.ofReal (C * I / (S + k)) := by
    have hSk : 0 < S + k := by positivity
    set w := truncationReal ψ k with hw_def
    have hw : IsLocallyBoundedPshOn Ω' w := truncationReal_isLocallyBoundedPshOn hψ' k
    obtain ⟨G, hG0⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hw hU2rc
    have hG : IsDecApprox U2 w G := isDecApprox_of_isDecreasingApproximation hw hU2Ω' hG0
    have hwcoe (z : ComplexModel n) (hz : z ∈ Ω') : (w z : EReal) = truncation ψ k z :=
      coe_truncationReal hψ' k hz
    have hwS (z : ComplexModel n) (hz : z ∈ closedBall z₀ R) : w z < S := by
      have hzΩ : z ∈ Ω' := closedBall_subset_ball (by linarith) hz
      have : (w z : EReal) ≤ (S₀ : EReal) := by
        rw [hwcoe z hzΩ]
        exact max_le (hψS₀ z hz) (EReal.coe_le_coe_iff.mpr (by
          linarith [Nat.cast_nonneg (α := ℝ) k]))
      have := EReal.coe_le_coe_iff.mp this
      simp only [S]; linarith
    have hFs (l : ℕ) (i : Fin n) : IsSmoothPsdOn U2 (F i l) :=
      ⟨((hF i).1 l).1.mono hU2U, fun z hz ↦ ((hF i).1 l).2 z (hU2U hz)⟩
    have hcln (l : ℕ) := hC U2 (fun i ↦ F i l) w G S h2U2 (hFs l) (fun i ↦ hFM i l) hG hwS
    -- comparison of the weight integral with the integral of `ψ`
    have hwI : ∫ z in ball z₀ R, (S - w z) ≤ I := by
      have h1 : IntegrableOn (fun z ↦ S - w z) (ball z₀ R) := by
        simpa using hG.integrableOn_sub_mul isOpen_ball.measurableSet
          ((isCompact_closedBall z₀ R).of_isClosed_subset isClosed_closure
            closure_ball_subset_closedBall)
          (closure_ball_subset_closedBall.trans
            ((closedBall_subset_closedBall (by linarith)).trans h2U2))
          (continuousOn_const (c := (1 : ℝ))) S
      refine integral_mono_ae h1 ((integrable_const S).sub hIψ) ?_
      filter_upwards [hfin, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzb
      have hzΩ : z ∈ Ω' := ball_subset_ball (by linarith) hzb
      have : (ψ z).toReal ≤ w z := by
        change (ψ z).toReal ≤ (truncation ψ k z).toReal
        exact EReal.toReal_le_toReal (le_max_left _ _) hz.2 (truncation_ne_top hψ' k hzΩ)
      change S - w z ≤ S - (ψ z).toReal
      linarith
    -- the open set where `ψ < -k`
    set O := ball z₀ (R / 2) ∩ {z | ψ z < ((-(k : ℝ) : ℝ) : EReal)} with hO_def
    have hOo : IsOpen O := by
      refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
      have hzV : z ∈ V := hbV (ball_subset_closedBall
        (ball_subset_ball (by linarith) hz.1))
      exact inter_mem (isOpen_ball.mem_nhds hz.1)
        ((hψ z hzV).upperSemicontinuousAt _ hz.2)
    have hOcl : closure O ⊆ closedBall z₀ (R / 2) :=
      (closure_mono inter_subset_left).trans closure_ball_subset_closedBall
    have hOc : IsCompact (closure O) :=
      (isCompact_closedBall z₀ _).of_isClosed_subset isClosed_closure hOcl
    have hPO : {z | ψ z = ⊥} ∩ ball z₀ (R / 2) ⊆ O := fun z hz ↦
      ⟨hz.2, by simp only [mem_ofPred_eq, hz.1.out]; exact EReal.bot_lt_coe _⟩
    refine (measure_mono hPO).trans (measure_le_of_tendstoMixed_of_isOpen hμf hT hOo hOc
      (hOcl.trans (hcb _ (by linarith))) fun φ hφ hφ01 hφO l ↦ ?_)
    set D := mixedDensity (fun i ↦ F i l) with hD_def
    have hDc : ContinuousOn D U2 := continuousOn_mixedDensity fun i ↦ (hFs l i).1
    have hD0 (z : ComplexModel n) (hz : z ∈ U2) : 0 ≤ D z :=
      mixedDensity_nonneg fun i ↦ (hFs l i).2 z hz
    have hB2c : IsCompact (closure (ball z₀ (R / 2))) :=
      (isCompact_closedBall z₀ _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    have hB2U : closure (ball z₀ (R / 2)) ⊆ U2 :=
      closure_ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans
        h2U2)
    have hstep1 : ∫ z, φ z * D z = ∫ z in ball z₀ (R / 2), φ z * D z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
        rw [hφO z fun h ↦ hz h.1, zero_mul]).symm
    have hint1 : IntegrableOn (fun z ↦ φ z * D z) (ball z₀ (R / 2)) :=
      integrableOn_of_continuousOn_closure hB2c hB2U (hφ.continuousOn.mul hDc)
    have hint2 : IntegrableOn (fun z ↦ (S - w z) * D z / (S + k)) (ball z₀ (R / 2)) :=
      (hG.integrableOn_sub_mul isOpen_ball.measurableSet hB2c hB2U hDc S).div_const _
    have hstep2 : ∫ z in ball z₀ (R / 2), φ z * D z ≤
        ∫ z in ball z₀ (R / 2), (S - w z) * D z / (S + k) := by
      refine setIntegral_mono_on hint1 hint2 isOpen_ball.measurableSet fun z hz ↦ ?_
      have hzU2 : z ∈ U2 := h2U2 (closedBall_subset_closedBall (by linarith)
        (ball_subset_closedBall hz))
      have hDz := hD0 z hzU2
      by_cases hzO : z ∈ O
      · have hwz : w z = -(k : ℝ) := by
          change (truncation ψ k z).toReal = _
          rw [truncation, max_eq_right hzO.2.le, EReal.toReal_coe]
        rw [hwz, show (S - -(k : ℝ)) * D z / (S + k) = D z by field_simp; ring]
        exact mul_le_of_le_one_left hDz (hφ01 z).2
      · rw [hφO z hzO, zero_mul]
        have := hwS z (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))
        exact div_nonneg (mul_nonneg (by linarith) hDz) hSk.le
    rw [hstep1]
    refine hstep2.trans ?_
    rw [integral_div]
    refine div_le_div_of_nonneg_right ((hcln l).trans ?_) hSk.le
    exact mul_le_mul_of_nonneg_left hwI hC0
  have ht : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (C * I / (S + k))) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ ↦ C * I / (S + k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ S tendsto_natCast_atTop_atTop)
    simpa using ENNReal.tendsto_ofReal this
  exact le_antisymm (ge_of_tendsto' ht hμk) bot_le

/-- **Global noncharging.** A measure that is, near every point of `Ω`, the weak
limit of mixed densities of decreasing smooth approximations does not charge
locally pluripolar sets. -/
theorem doesNotChargePluripolarOn_of_forall_tendstoMixed {Ω : Opens (ComplexModel n)}
    {μ : Measure (ComplexModel n)}
    (h : ∀ x ∈ Ω, ∃ U : Opens (ComplexModel n), x ∈ U ∧
      ∃ (u : Fin n → ComplexModel n → ℝ) (F : Fin n → ℕ → ComplexModel n → ℝ),
        (∀ i, IsDecApprox U (u i) (F i)) ∧ (∀ K, IsCompact K → K ⊆ U → μ K < ⊤) ∧
          TendstoMixed U F μ) :
    DoesNotChargePluripolarOn μ (Ω : Set (ComplexModel n)) := by
  intro s hs
  have hloc (x : Ω) : ∃ W : Set (ComplexModel n), IsOpen W ∧ (x : ComplexModel n) ∈ W ∧
      μ (s ∩ W) = 0 := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨V, ψ, hVo, hxV, hVc, hψ, hne, hp⟩ := hs x hx
    obtain ⟨U, hxU, u, F, hF, hμf, hT⟩ := h x hx
    obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp (hVo.inter U.isOpen) x ⟨hxV, hxU⟩
    have hsub : closedBall x (3 * (r / 4)) ⊆ V ∩ U :=
      (closedBall_subset_ball (by linarith)).trans hrb
    refine ⟨ball x (r / 4 / 2), isOpen_ball, mem_ball_self (by positivity), ?_⟩
    have h0 := measure_poleSet_inter_ball_eq_zero hF hμf hT (by positivity : 0 < r / 4)
      (hsub.trans inter_subset_right) hVc hψ hne (hsub.trans inter_subset_left)
    refine measure_mono_null (fun z (hz : z ∈ s ∩ ball x (r / 4 / 2)) ↦
      (⟨hp z ?_ hz.1, hz.2⟩ : z ∈ {z | ψ z = ⊥} ∩ ball x (r / 4 / 2))) h0
    exact (hsub (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz.2))).1
  choose W hWo hxW hW0 using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  have hcover : s ∩ Ω ⊆ ⋃ i ∈ T, s ∩ W i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ mem_iUnion.2 ⟨⟨z, hz.2⟩, hxW _⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 this
    exact mem_iUnion₂.2 ⟨i, hi, hz.1, hzi⟩
  exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 fun i _ ↦ hW0 i)

theorem exists_relativelyCompact_ball {Ω : Opens (ComplexModel n)} {x : ComplexModel n}
    (hx : x ∈ Ω) : ∃ U : Opens (ComplexModel n), x ∈ U ∧ RelativelyCompactIn U Ω := by
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  exact ⟨⟨ball x (r / 2), isOpen_ball⟩, mem_ball_self (half_pos hr),
    (isCompact_closedBall x _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
    closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hr)).trans hrb)⟩

/-- **Mixed bounded Bedford–Taylor measures do not charge pluripolar sets.** -/
theorem IsLocalMixedBedfordTaylorMeasure.doesNotChargePluripolarOn
    {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ) :
    DoesNotChargePluripolarOn μ (Ω : Set (ComplexModel n)) := by
  refine doesNotChargePluripolarOn_of_forall_tendstoMixed fun x hx ↦ ?_
  obtain ⟨U, hxU, hU⟩ := exists_relativelyCompact_ball hx
  have hUΩ : U ≤ Ω := subset_closure.trans hU.2
  obtain ⟨F, hF, hlim⟩ := IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU
  exact ⟨U, hxU, v, F, hF.1, (fun K hK hKU ↦ hμ.2.2.1 K hK (hKU.trans hUΩ)), hlim⟩

/-- **Bounded Bedford–Taylor measures do not charge pluripolar sets.** -/
theorem IsLocalBedfordTaylorMeasure.doesNotChargePluripolarOn
    {Ω : Opens (ComplexModel n)} {v : ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalBedfordTaylorMeasure Ω v μ) :
    DoesNotChargePluripolarOn μ (Ω : Set (ComplexModel n)) := by
  refine doesNotChargePluripolarOn_of_forall_tendstoMixed fun x hx ↦ ?_
  obtain ⟨U, hxU, hU⟩ := exists_relativelyCompact_ball hx
  have hUΩ : U ≤ Ω := subset_closure.trans hU.2
  obtain ⟨F, hF, hlim⟩ := IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU
  exact ⟨U, hxU, fun _ ↦ v, F, hF.1, (fun K hK hKU ↦ hμ.2.2.1 K hK (hKU.trans hUΩ)), hlim⟩

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
