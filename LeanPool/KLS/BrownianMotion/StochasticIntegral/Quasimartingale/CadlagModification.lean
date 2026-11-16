/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified by kls-lean for the selected proved dependency closure; see formalization/vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: Lean/Mathlib v4.35.0 adaptations
-- (deprecated names; four proof bodies for the new MemLp/eLpNorm API); see vendor/port.patch.
module

public import LeanPool.KLS.BrownianMotion.Auxiliary.ConvergenceInMeasure
public import LeanPool.KLS.BrownianMotion.Auxiliary.Jensen
public import LeanPool.KLS.BrownianMotion.Auxiliary.LeftLimWithin
public import LeanPool.KLS.BrownianMotion.Continuity.LimitModification
public import LeanPool.KLS.BrownianMotion.StochasticIntegral.Cadlag
public import LeanPool.KLS.BrownianMotion.StochasticIntegral.Predictable
public import LeanPool.KLS.BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality
public import LeanPool.KLS.BrownianMotion.Auxiliary.Jensen
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Cadlag modification of quasimartingales

We build right-continuous and càdlàg modifications of real quasimartingales.

The construction is done in two steps. First, for a process `X` and an antitone family of events
`R d` on which the paths of `X` along a countable dense set of times have left and right limits
before `d` (`IsRegularityFamily`), we define processes `rightContModifOf R X` and
`cadlagModifOf R X` from the right limits of `X`, and we prove their regularity and measurability
properties. That part applies to processes with values in a normed group.
Then, for a real quasimartingale `X`, the events `regularitySet T X d`, defined with the upcrossings
of `X`, are almost sure and give the modifications `rightContModifReal X` and `cadlagModifReal X`.

See the file `CadlagModificationBanach` for martingales with values in a Banach space. -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

/-- A dense set contains points above any point which is not maximal. -/
lemma Dense.exists_gt_of_not_isMax {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α]
    {s : Set α} (hs : Dense s) {a : α} (ha : ¬ IsMax a) :
    ∃ b ∈ s, a < b :=
  hs.exists_mem_open isOpen_Ioi (not_isMax_iff.1 ha)

/-- A dense set contains points in `Ioo a b` for `a < b`, if `a` is not isolated on the right.
Version of `Dense.exists_between` for an order which may not be densely ordered. -/
lemma Dense.exists_between_of_nhdsGT_neBot {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α]
    {s : Set α} (hs : Dense s) {a b : α} [(𝓝[>] a).NeBot] (hab : a < b) :
    ∃ c ∈ s, a < c ∧ c < b :=
  hs.exists_mem_open isOpen_Ioo (Filter.nonempty_of_mem (Ioo_mem_nhdsGT hab))

/-- A maximal element is isolated on the right. -/
lemma IsMax.nhdsGT_eq_bot {α : Type*} [Preorder α] [TopologicalSpace α] {a : α} (ha : IsMax a) :
    𝓝[>] a = ⊥ :=
  ha.Ioi_eq ▸ nhdsWithin_empty a

/-- A point which is not isolated on the right is not maximal. -/
lemma not_isMax_of_nhdsGT_neBot {α : Type*} [Preorder α] [TopologicalSpace α] {a : α}
    [h : (𝓝[>] a).NeBot] : ¬ IsMax a :=
  fun ha ↦ h.ne ha.nhdsGT_eq_bot

/- The three stability helpers below use the proved upstream bodies from
BrownianMotion/StochasticIntegral/UniformIntegrable.lean at a7ad7af. They are private
to this consumer, so the unrelated optional-sampling and limit-process placeholders
from that module are outside the selected dependency closure. -/
section UniformIntegrableStability

variable {ι κ Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

private lemma MeasureTheory.UniformIntegrable.add [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : UniformIntegrable X p μ) (hY : UniformIntegrable Y p μ) :
    UniformIntegrable (X + Y) p μ := by
  refine ⟨hX.1.add hY.1 hp, ?_⟩
  obtain ⟨C_X, hC_X⟩ := hX.2
  obtain ⟨C_Y, hC_Y⟩ := hY.2
  exact ⟨C_X + C_Y, fun i ↦
    le_trans (eLpNorm_add_le hp) (add_le_add (hC_X i) (hC_Y i))⟩

private lemma MeasureTheory.uniformIntegrable_of_dominated [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : ι → Ω → E} {Y : κ → Ω → F} {p : ℝ≥0∞}
    (hY : UniformIntegrable Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∃ j, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ ‖Y j ω‖) :
    UniformIntegrable X p μ := by
  refine ⟨?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hY.1
    · intro ε
      exact zero_le
    · intro ε
      refine iSup_le fun i ↦ iSup_le fun s ↦ iSup_le fun hs ↦ ?_
      obtain ⟨j, hj⟩ := hX i
      exact (eLpNorm_mono_ae (mX i).restrict (ae_restrict_of_ae hj)).trans
        (le_iSup_of_le j (le_iSup_of_le s (le_iSup_of_le hs le_rfl)))
  · obtain ⟨C, hC⟩ := hY.2
    exact ⟨C, fun i ↦
      let ⟨j, hj⟩ := hX i
      le_trans (eLpNorm_mono_ae (mX i) hj) (hC j)⟩

private lemma MeasureTheory.UniformIntegrable.norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (hY : UniformIntegrable X p μ) :
    UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := by
  refine uniformIntegrable_of_dominated hY ?_ (fun i ↦ ⟨i, by simp⟩)
  exact fun i ↦ (UniformIntegrable.aestronglyMeasurable hY i).norm

end UniformIntegrableStability

section UniformIntegrableAux

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Vitali**: if a uniformly integrable sequence converges almost everywhere, then its integrals
on any set converge to the integral of the limit. -/
lemma MeasureTheory.UniformIntegrable.tendsto_setIntegral [IsFiniteMeasure μ]
    {f : ℕ → Ω → E} {g : Ω → E} (hUI : UniformIntegrable f 1 μ)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω))) (A : Set Ω) :
    Tendsto (fun n ↦ ∫ ω in A, f n ω ∂μ) atTop (𝓝 (∫ ω in A, g ω ∂μ)) := by
  have hg : MemLp g 1 μ := hUI.memLp_of_ae_tendsto hfg
  refine tendsto_setIntegral_of_L1' g
    (.of_forall fun n ↦ memLp_one_iff_integrable.1 (hUI.memLp n)) ?_ A
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hUI.aestronglyMeasurable hg
    hUI.unifIntegrable hfg

/-- The integrals of the truncations `f ⊔ (-k)` of an integrable function `f` converge to the
integral of `f`. -/
lemma MeasureTheory.Integrable.tendsto_setIntegral_sup_neg_natCast {f : Ω → ℝ}
    (hf : Integrable f μ) (A : Set Ω) :
    Tendsto (fun k : ℕ ↦ ∫ ω in A, f ω ⊔ (-(k : ℝ)) ∂μ) atTop (𝓝 (∫ ω in A, f ω ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω ↦ |f ω|)
    (fun k ↦ (hf.aestronglyMeasurable.sup aestronglyMeasurable_const).restrict)
    hf.abs.restrict (fun k ↦ .of_forall fun ω ↦ ?_) (.of_forall fun ω ↦ ?_)
  · rw [Real.norm_eq_abs, abs_le]
    refine ⟨(neg_abs_le _).trans le_sup_left, sup_le (le_abs_self _) ?_⟩
    exact (neg_nonpos.2 (Nat.cast_nonneg k)).trans (abs_nonneg _)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈-f ω⌉₊] with k hk
    rw [eq_comm, sup_eq_left, neg_le]
    exact (Nat.le_ceil _).trans (mod_cast hk)

/-- A family of functions which is bounded from below by a constant and such that each function is
bounded from above by a conditional expectation of a fixed integrable function is uniformly
integrable. -/
lemma MeasureTheory.uniformIntegrable_of_le_condExp [IsFiniteMeasure μ] {κ : Type*}
    {f : κ → Ω → ℝ} {g : Ω → ℝ} {c : ℝ} {m : κ → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ)
    (hg : Integrable g μ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hcf : ∀ i, ∀ᵐ ω ∂μ, c ≤ f i ω) (hfg : ∀ i, f i ≤ᵐ[μ] μ[g | m i]) :
    UniformIntegrable f 1 μ := by
  have hUI : UniformIntegrable ((fun _ _ ↦ |c|) + fun i ω ↦ ‖(μ[g | m i]) ω‖) 1 μ :=
    (uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const |c|)).add le_rfl
      (hg.uniformIntegrable_condExp hm).norm
  refine uniformIntegrable_of_dominated hUI hf fun i ↦ ⟨i, ?_⟩
  filter_upwards [hcf i, hfg i] with ω h1 h2
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (a := |c| + _) (by positivity), abs_le]
  constructor
  · linarith [neg_abs_le c, abs_nonneg ((μ[g | m i]) ω)]
  · linarith [le_abs_self ((μ[g | m i]) ω), abs_nonneg c]

/-- `L¹` bound for a submartingale on an interval. -/
lemma MeasureTheory.Submartingale.integral_abs_le {ι : Type*} [Preorder ι]
    {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : Submartingale X 𝓕 μ) {t s u : ι} (hts : t ≤ s) (hsu : s ≤ u) :
    ∫ ω, |X s ω| ∂μ ≤ 2 * ∫ ω, X u ω ⊔ 0 ∂μ - ∫ ω, X t ω ∂μ := by
  have hZ : Submartingale (fun s ω ↦ X s ω ⊔ 0) 𝓕 μ :=
    hX.sup (martingale_const 𝓕 μ 0).submartingale
  have h_eq : ∫ ω, |X s ω| ∂μ = 2 * ∫ ω, X s ω ⊔ 0 ∂μ - ∫ ω, X s ω ∂μ := by
    rw [← integral_const_mul, ← integral_sub ((hZ.integrable s).const_mul 2) (hX.integrable s)]
    congr with ω
    rcases le_total 0 (X s ω) with h | h
    · rw [abs_of_nonneg h, sup_of_le_left h]
      ring
    · rw [abs_of_nonpos h, sup_of_le_right h]
      ring
  have h1 := hZ.setIntegral_le hsu MeasurableSet.univ
  have h2 := hX.setIntegral_le hts MeasurableSet.univ
  simp only [Measure.restrict_univ] at h1 h2
  linarith

end UniformIntegrableAux

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}

section RegularitySet

variable {X : ι → Ω → ℝ}

/-- In this set, the process is bounded and has finitely many upcrossings (of any interval) in `T`
before time `d` -/
def regularitySet (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  {ω | (∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r) ∧
    (∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1)}

lemma regularitySet_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySet T X d₂ ⊆ regularitySet T X d₁ := by
  intro ω hω
  simp only [regularitySet, Set.mem_ofPred_eq] at hω ⊢
  constructor
  · intro q r hqr
    have hω' :=  hω.1 q r hqr
    refine fun h_mem ↦ hω' ?_
    exact infiniteAlt_mono'' hd h_mem
  · obtain ⟨M, hM⟩ := hω.2
    refine ⟨M, fun s hs ↦ ?_⟩
    specialize hM s (by grind)
    grind

section OrderBot

variable [OrderBot ι]

lemma ae_mem_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) (hdT : d ∈ T) :
    ∀ᵐ ω ∂μ, ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT, ae_exists_bound'' hX hT d] with ω hω1 hω2
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2⟩

lemma ae_mem_all_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T T' : Set ι} (hT : T.Countable) (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT', ae_exists_bound hX hT hT'] with ω hω1 hω2 d hdT
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2 d hdT⟩

lemma measurableSet_altSet (hX : IsRealQuasimartingale 𝓕 X μ)
    (d : ι) (F : Finset ι) (hF : ∀ i ∈ F, i ≤ d) {q r : ℚ} (_hqr : q < r) (m : ℕ) :
    MeasurableSet[𝓕 d] (altSet X F q r m) := by
  have hXmeas : ∀ s ∈ F, Measurable[𝓕 d] (X s) := fun s hs ↦
    (hX.adapted s).mono (𝓕.mono (hF s hs)) le_rfl
  have hset : altSet X F (q : ℝ) (r : ℝ) m
      = ⋃ g ∈ Fintype.piFinset (fun _ : Fin (2 * m) ↦ F),
          {ω | (∀ (i : Fin (2 * m)) (h : (i : ℕ) + 1 < 2 * m), g i < g ⟨(i : ℕ) + 1, h⟩)
            ∧ (∀ i : Fin m, X (g ⟨2 * (i : ℕ), by omega⟩) ω ≤ (q : ℝ))
            ∧ (∀ i : Fin m, (r : ℝ) ≤ X (g ⟨2 * (i : ℕ) + 1, by omega⟩) ω)} := by
    ext ω
    simp only [altSet, Set.mem_ofPred_eq, Set.mem_iUnion, Fintype.mem_piFinset, exists_prop]
    constructor
    · rintro ⟨c, hc1, hc2, hc3, hc4⟩
      exact ⟨fun i ↦ c (i : ℕ), fun i ↦ hc2 (i : ℕ) i.2,
        fun i h ↦ hc1 (i : ℕ) h, fun i ↦ hc3 (i : ℕ) i.2, fun i ↦ hc4 (i : ℕ) i.2⟩
    · rintro ⟨g, hgF, hg1, hg3, hg4⟩
      refine ⟨fun k ↦ if h : k < 2 * m then g ⟨k, h⟩ else ⊥, by grind, by grind, ?_, ?_⟩
      · intro i hi
        have h2i : 2 * i < 2 * m := by lia
        simp only [dite_eq_left h2i]
        exact hg3 ⟨i, hi⟩
      · intro i hi
        have h2i : 2 * i + 1 < 2 * m := by lia
        simp only [dite_eq_left h2i]
        exact hg4 ⟨i, hi⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun g hg ↦ ?_
  have hgF : ∀ i, g i ∈ F := Fintype.mem_piFinset.mp hg
  -- Split off the (measure-space independent) monotonicity condition, then recognise the event
  -- as a finite intersection of measurable half-lines `{X s ≤ q}` and `{r ≤ X s}`, `s ∈ F`.
  rw [Set.ofPred_and]
  refine (MeasurableSet.const _).inter ?_
  rw [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i ↦ ?_) (MeasurableSet.iInter fun i ↦ ?_)
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ), by lia⟩) measurableSet_Iic
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ) + 1, by lia⟩) measurableSet_Ici

lemma measurableSet_infiniteAlt (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) {q r : ℚ} (hqr : q < r) :
    MeasurableSet[𝓕 d] (infiniteAlt T d X q r) := by
  unfold infiniteAlt
  refine MeasurableSet.iInter fun m ↦ MeasurableSet.biUnion ?_ fun F ↦ ?_
  · refine countable_setOf_finset_coe_subset ?_
    exact hT.mono (by grind)
  · intro hF
    refine measurableSet_altSet hX d F ?_ hqr m
    simp only [Set.subset_inter_iff, Set.mem_ofPred_eq] at hF
    intro i hi
    exact hF.2 hi

lemma measurableSet_regularitySet (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySet T X d) := by
  suffices MeasurableSet[𝓕 d]
        ((⋂ (q : ℚ) (r : ℚ) (hqr : q < r), {ω | ω ∉ infiniteAlt T d X q r}) ∩
        (⋃ M : ℕ, ⋂ s ∈ T ∩ Set.Iic d, {ω | |X s ω| ≤ M + 1})) by
      convert this
      ext ω
      simp [regularitySet]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun p ↦ MeasurableSet.iInter fun q ↦ ?_
    by_cases hpq : p < q
    · simp only [hpq, Set.iInter_true]
      refine MeasurableSet.compl ?_
      exact measurableSet_infiniteAlt hX hT d hpq
    · simp [hpq]
  · refine MeasurableSet.iUnion fun M ↦ MeasurableSet.biInter (hT.mono (by grind)) fun s hs ↦ ?_
    refine measurableSet_le ?_ (by fun_prop)
    simp only [Set.mem_inter_iff, Set.mem_Iic] at hs
    refine Measurable.mono ?_ (𝓕.mono hs.2) le_rfl
    simp_rw [← Real.norm_eq_abs]
    exact (hX.stronglyAdapted s).norm.measurable

end OrderBot

variable [TopologicalSpace ι] [OrderTopology ι]

lemma right_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxd : x < d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_ofPred_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    convert hω.2
    simp
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_right hxd hfa hfb
  · refine ⟨((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind

lemma left_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxle : x ≤ d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_ofPred_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    convert hω.2
    simp
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_left hxle hfa hfb
  · refine ⟨(M : ℝ) + 1, ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind

end RegularitySet

/-! ### Regularity families

A regularity family for a process `X` along a set of times `T` is an antitone family of events
`R d` such that on `R d`, the path of `X` along `T` has left and right limits at all times
before `d`. The main example is `regularitySet T X` for a real process `X`.

From such a family we define the events `regularitySetRight T R d`, on which the paths are regular
up to a time slightly after `d`. These are the events used to define the modifications of `X`. -/

section RegularityFamily

variable [TopologicalSpace ι] {T : Set ι} {R : ι → Set Ω} {d : ι} {ω : Ω}

/-- The set of `ω` that belong to some `R s`, for `s ∈ T` with `s > d` or for `s ≥ d` isolated on
the right (`𝓝[>] s = ⊥`: `s` is maximal or has a successor). Here `R` is an antitone family of
sets, for example `regularitySet T X` for a real process `X`.

If `d` is not isolated on the right and `T` is dense, this is the set of `ω` that belong to
`R s` for some `s ∈ T` with `s > d` (see `regularitySetRight_eq_biUnion_gt`).
If `d` is isolated on the right, this is `R d` (see `regularitySetRight_of_nhdsGT_eq_bot`). -/
def regularitySetRight (T : Set ι) (R : ι → Set Ω) (d : ι) : Set Ω :=
  ⋃ s ∈ (T ∩ Set.Ioi d) ∪ ({s | 𝓝[>] s = ⊥} ∩ Set.Ici d), R s

lemma mem_regularitySetRight_iff :
    ω ∈ regularitySetRight T R d
      ↔ ∃ s, ((s ∈ T ∧ d < s) ∨ (𝓝[>] s = ⊥ ∧ d ≤ s)) ∧ ω ∈ R s := by
  simp [regularitySetRight]

lemma regularitySetRight_of_nhdsGT_eq_bot (hR : Antitone R) (hd : 𝓝[>] d = ⊥) :
    regularitySetRight T R d = R d := by
  ext ω
  rw [mem_regularitySetRight_iff]
  refine ⟨fun ⟨s, hs, hω⟩ ↦ ?_, fun hω ↦ ⟨d, .inr ⟨hd, le_rfl⟩, hω⟩⟩
  rcases hs with ⟨-, hds⟩ | ⟨-, hds⟩
  · exact hR hds.le hω
  · exact hR hds hω

lemma regularitySetRight_eq_biUnion_lt (hR : Antitone R) {t : ι} [hd : (𝓝[>] d).NeBot]
    (hdt : d < t) (hT : ∀ s, d < s → ∃ u ∈ T, d < u ∧ u ≤ s) :
    regularitySetRight T R d = ⋃ d' ∈ T ∩ Set.Ioc d t, R d' := by
  ext ω
  simp only [mem_regularitySetRight_iff, Set.mem_inter_iff, Set.mem_iUnion, exists_prop,
    Set.mem_Ioc]
  refine ⟨fun ⟨i, hi, hωi⟩ ↦ ?_, fun ⟨i, ⟨hiT, hdi, hit⟩, hωi⟩ ↦ ⟨i, .inl ⟨hiT, hdi⟩, hωi⟩⟩
  -- `d` is not isolated on the right, hence `d < i` in both cases
  have hdi : d < i := by
    rcases hi with ⟨-, hdi⟩ | ⟨hi, hdi⟩
    · exact hdi
    · exact lt_of_le_of_ne hdi fun h ↦ hd.ne (h ▸ hi)
  obtain ⟨u, huT, hdu, hu⟩ := hT (min i t) (lt_min hdi hdt)
  exact ⟨u, ⟨huT, hdu, hu.trans (min_le_right _ _)⟩, hR (hu.trans (min_le_left _ _)) hωi⟩

lemma regularitySetRight_eq_biUnion_gt (hR : Antitone R) [hd : (𝓝[>] d).NeBot]
    (hT : ∀ s, d < s → ∃ u ∈ T, d < u ∧ u ≤ s) :
    regularitySetRight T R d = ⋃ d' ∈ T ∩ Set.Ioi d, R d' := by
  ext ω
  simp only [mem_regularitySetRight_iff, Set.mem_inter_iff, Set.mem_iUnion, exists_prop,
    Set.mem_Ioi]
  refine ⟨fun ⟨i, hi, hωi⟩ ↦ ?_, fun ⟨i, hi, hωi⟩ ↦ ⟨i, .inl hi, hωi⟩⟩
  rcases hi with hi | ⟨hi, hdi⟩
  · exact ⟨i, hi, hωi⟩
  · obtain ⟨u, huT, hdu, hu⟩ := hT i (lt_of_le_of_ne hdi fun h ↦ hd.ne (h ▸ hi))
    exact ⟨u, ⟨huT, hdu⟩, hR hu hωi⟩

lemma regularitySetRight_anti {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySetRight T R d₂ ⊆ regularitySetRight T R d₁ := by
  intro ω hω
  rw [mem_regularitySetRight_iff] at hω ⊢
  obtain ⟨s, hs, hω⟩ := hω
  exact ⟨s, hs.imp (fun h ↦ ⟨h.1, hd.trans_lt h.2⟩) (fun h ↦ ⟨h.1, hd.trans h.2⟩), hω⟩

/-- If almost surely `ω` belongs to `R d` for all `d ∈ T` and all `d` isolated on the right, then
almost surely `ω` belongs to all the sets `regularitySetRight T R d`. -/
lemma ae_mem_regularitySetRight
    (hR : ∀ᵐ ω ∂μ, ∀ d ∈ T ∪ {s | 𝓝[>] s = ⊥}, ω ∈ R d)
    (hTcof : ∀ x, ¬ IsMax x → ∃ s ∈ T, x < s) :
    ∀ᵐ ω ∂μ, ∀ d, ω ∈ regularitySetRight T R d := by
  filter_upwards [hR] with ω hω d
  rw [mem_regularitySetRight_iff]
  by_cases hd : 𝓝[>] d = ⊥
  · exact ⟨d, .inr ⟨hd, le_rfl⟩, hω d (.inr hd)⟩
  · obtain ⟨s, hs, hsd⟩ := hTcof d fun hd' ↦ hd hd'.nhdsGT_eq_bot
    exact ⟨s, .inl ⟨hs, hsd⟩, hω s (.inl hs)⟩

variable [OrderTopology ι]

/-- For a right-continuous filtration and a time `t` that is not isolated on the right, a set that
is `𝓕 s`-measurable for every `s > t` is already `𝓕 t`-measurable, since `𝓕 t = ⨅ s > t, 𝓕 s`. -/
lemma measurableSet_of_forall_gt [𝓕.IsRightContinuous]
    {t : ι} [(𝓝[>] t).NeBot] {A : Set Ω}
    (h : ∀ s, t < s → MeasurableSet[𝓕 s] A) :
    MeasurableSet[𝓕 t] A := by
  have hrc : (𝓕 t : MeasurableSpace Ω) = ⨅ j > t, 𝓕 j := by
    have h1 := 𝓕.rightCont_eq_of_neBot_nhdsGT t
    rwa [Filtration.IsRightContinuous.eq] at h1
  rw [hrc, MeasurableSpace.measurableSet_iInf]
  intro j
  rw [MeasurableSpace.measurableSet_iInf]
  exact h j

lemma measurableSet_regularitySetRight [𝓕.IsRightContinuous] (hR : Antitone R)
    (hRm : ∀ d, MeasurableSet[𝓕 d] (R d)) (hT : T.Countable) (hTd : Dense T) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySetRight T R d) := by
  -- if `d` is isolated on the right, the set is `R d`
  rcases (𝓝[>] d).eq_or_neBot with hd | hd
  · rw [regularitySetRight_of_nhdsGT_eq_bot hR hd]
    exact hRm d
  refine measurableSet_of_forall_gt fun s hs ↦ ?_
  rw [regularitySetRight_eq_biUnion_lt hR hs]
  swap
  · intro u hu
    obtain ⟨z, hz1, hz2, hz3⟩ := hTd.exists_between_of_nhdsGT_neBot hu
    exact ⟨z, hz1, hz2, hz3.le⟩
  refine MeasurableSet.biUnion (hT.mono Set.inter_subset_left) fun t ht ↦ ?_
  exact 𝓕.mono ht.2.2 _ (hRm t)

lemma measurableSet_regularitySetRight' [SecondCountableTopology ι]
    (hRm : ∀ d, MeasurableSet (R d)) (hT : T.Countable) (d : ι) :
    MeasurableSet (regularitySetRight T R d) := by
  rw [regularitySetRight]
  refine MeasurableSet.biUnion ?_ fun t _ ↦ hRm t
  exact (hT.mono Set.inter_subset_left).union
    (countable_setOfPred_isolated_right.mono Set.inter_subset_left)

lemma eventually_mem_regularitySetRight_of_mem (hω : ω ∈ regularitySetRight T R d) :
    ∀ᶠ y in 𝓝[>] d, ω ∈ regularitySetRight T R y := by
  obtain ⟨s, hs, hω'⟩ := mem_regularitySetRight_iff.1 hω
  rcases hs with ⟨hsT, hds⟩ | ⟨hs, hds⟩
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds hds] with y hy hxy
    exact mem_regularitySetRight_iff.2 ⟨s, .inl ⟨hsT, hy⟩, hω'⟩
  · rcases hds.eq_or_lt with rfl | hds
    · -- `d` is isolated on the right
      simp [hs]
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [eventually_lt_nhds hds] with y hy hxy
      exact mem_regularitySetRight_iff.2 ⟨s, .inr ⟨hs, hy.le⟩, hω'⟩

variable {E : Type*} [TopologicalSpace E] {X : ι → Ω → E}

/-- An antitone family of events `R d` is a regularity family for a process `X` along a set of
times `T` if on `R d`, the path of `X` along `T` has right limits at all times before `d` and left
limits at all times up to `d`. -/
structure IsRegularityFamily (T : Set ι) (X : ι → Ω → E) (R : ι → Set Ω) : Prop where
  anti : Antitone R
  exists_tendsto_nhdsGT ⦃x d : ι⦄ ⦃ω : Ω⦄ (hxd : x < d) (hω : ω ∈ R d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l)
  exists_tendsto_nhdsLT ⦃x d : ι⦄ ⦃ω : Ω⦄ (hxd : x ≤ d) (hω : ω ∈ R d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l)

namespace IsRegularityFamily

variable (hR : IsRegularityFamily T X R) {y : ι}
include hR

omit [OrderTopology ι] in
lemma right_limit_of_mem_regularitySetRight (hω : ω ∈ regularitySetRight T R d) (hyd : y ≤ d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  by_cases hy : 𝓝[>] y = ⊥
  · exact ⟨X y ω, by simp [eq_bot_mono (nhdsWithin_mono _ Set.inter_subset_right) hy]⟩
  obtain ⟨s, hs, hω'⟩ := mem_regularitySetRight_iff.1 hω
  refine hR.exists_tendsto_nhdsGT ?_ hω'
  rcases hs with ⟨-, hds⟩ | ⟨hs, hds⟩
  · exact hyd.trans_lt hds
  · exact lt_of_le_of_ne (hyd.trans hds) fun h ↦ hy (h ▸ hs)

omit [OrderTopology ι] in
lemma left_limit_of_mem_regularitySetRight (hω : ω ∈ regularitySetRight T R d) (hyd : y ≤ d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  obtain ⟨s, hs, hω'⟩ := mem_regularitySetRight_iff.1 hω
  refine hR.exists_tendsto_nhdsLT ?_ hω'
  rcases hs with ⟨-, hds⟩ | ⟨-, hds⟩
  · exact hyd.trans hds.le
  · exact hyd.trans hds

lemma tendsto_nhdsGT_rightLimWithin (hω : ω ∈ regularitySetRight T R d) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Ioi d] d) (𝓝 (Function.rightLimWithin (X · ω) T d)) := by
  have h := hR.right_limit_of_mem_regularitySetRight hω le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_rightLimWithin_of_tendsto h

lemma tendsto_nhdsLT_leftLimWithin (hω : ω ∈ regularitySetRight T R d) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Iio d] d) (𝓝 (Function.leftLimWithin (X · ω) T d)) := by
  have h := hR.left_limit_of_mem_regularitySetRight hω le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_leftLimWithin_of_tendsto h

lemma continuousWithinAt_rightLimWithin [T3Space E] (hTd : Dense T)
    (hT : ∀ y, 𝓝[>] y = ⊥ → y ∈ T) (hω : ω ∈ regularitySetRight T R d) :
    ContinuousWithinAt (Function.rightLimWithin (X · ω) T) (Set.Ici d) d := by
  refine continuousWithinAt_rightLimWithin_Ici_of_dense hTd (.of_forall hT) ?_ ?_
  · rw [Set.inter_comm]
    exact hR.tendsto_nhdsGT_rightLimWithin hω
  · filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
    rw [Set.inter_comm]
    exact hR.tendsto_nhdsGT_rightLimWithin hy

end IsRegularityFamily

end RegularityFamily

variable [TopologicalSpace ι] [OrderTopology ι]

/-! ### Pathwise regularization

For a fixed path `h : ι → F` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`.

The regularization `r y` is the limit of `h` along `T` from the right of `y`, unless `y` is
isolated on the right, in which case `r y = h y` (hypothesis `hr'`) and we need `y ∈ T`. -/

section PathRegularization

variable {F : Type*} [TopologicalSpace F] [RegularSpace F] {T : Set ι} {h r : ι → F} {x : ι}

/-- The right-limit regularization inherits left limits of `h` along `T`. -/
lemma tendsto_rightLim_nhdsLT (hTd : Dense T) (hT : ∀ y, 𝓝[>] y = ⊥ → y ∈ T)
    (hr : ∀ᶠ y in 𝓝[<] x, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y)))
    (hr' : ∀ y, 𝓝[>] y = ⊥ → r y = h y) {L : F}
    (hL : Tendsto h (𝓝[T ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto r (𝓝[<] x) (𝓝 L) := by
  by_cases hex : ∃ u, u < x
  swap
  · have hempty : Set.Iio x = ∅ := Set.eq_empty_iff_forall_notMem.2
      (fun u hu ↦ hex ⟨u, hu⟩)
    rw [nhdsWithin, hempty, Filter.principal_empty, inf_bot_eq]
    exact tendsto_bot
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T, h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt hex).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hvx, hr] with y hy hr
  -- if `y` is isolated on the right, then `r y = h y` and `y ∈ T`
  rcases (𝓝[>] y).eq_or_neBot with hy' | hy'
  · rw [hr' y hy']
    exact hv hy (hT y hy')
  have hne := nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hTd y
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto hr ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hy.2] with s hs hsT
  exact hv ⟨hy.1.trans hs.1, hs.2⟩ hsT

/-- Along a strictly increasing sequence `u → x` from the left, the regularized values
`r (u k)` tend to the left limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_lt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y)))
    (hr' : ∀ y, 𝓝[>] y = ⊥ → r y = h y) {u : ℕ → ι} {L : F}
    (hux : ∀ k, u k < x) (hutend : Tendsto u atTop (𝓝 x))
    (huT' : ∀ k, 𝓝[>] (u k) = ⊥ → u k ∈ T')
    (hL : Tendsto h (𝓝[T' ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt ⟨u 0, hux 0⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Ioi v :=
    hutend (IsOpen.mem_nhds isOpen_Ioi hvx)
  filter_upwards [hevk] with k hk
  -- if `u k` is isolated on the right, then `r (u k) = h (u k)` and `u k ∈ T'`
  rcases (𝓝[>] (u k)).eq_or_neBot with hk' | hk'
  · rw [hr' _ hk']
    exact hv ⟨hk, hux k⟩ (huT' k hk')
  have hne := nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hTd (u k)
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT (hux k)] with s hs hsT
  exact hv ⟨hk.trans hs.1, hs.2⟩ (hTT' hsT)

/-- Along a strictly decreasing sequence `u → x` from the right, the regularized values
`r (u k)` tend to the right limit of `h` at `x` along `T' ⊇ T`. -/
lemma tendsto_rightLim_comp_of_gt (hTd : Dense T) {T' : Set ι} (hTT' : T ⊆ T')
    (hr : ∀ y, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y)))
    (hr' : ∀ y, 𝓝[>] y = ⊥ → r y = h y) {u : ℕ → ι} {L : F}
    (hux : ∀ k, x < u k) (hutend : Tendsto u atTop (𝓝 x))
    (huT' : ∀ k, 𝓝[>] (u k) = ⊥ → u k ∈ T')
    (hL : Tendsto h (𝓝[T' ∩ Set.Ioi x] x) (𝓝 L)) :
    Tendsto (fun k ↦ r (u k)) atTop (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[>] x ⊓ 𝓟 T', h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsGT_basis_of_exists_gt ⟨u 0, hux 0⟩).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  have hevk : ∀ᶠ k in atTop, u k ∈ Set.Iio v :=
    hutend (IsOpen.mem_nhds isOpen_Iio hvx)
  filter_upwards [hevk] with k hk
  -- if `u k` is isolated on the right, then `r (u k) = h (u k)` and `u k ∈ T'`
  rcases (𝓝[>] (u k)).eq_or_neBot with hk' | hk'
  · rw [hr' _ hk']
    exact hv ⟨hux k, hk⟩ (huT' k hk')
  have hne := nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hTd (u k)
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto (hr (u k)) ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hk] with s hs hsT
  exact hv ⟨(hux k).trans hs.1, hs.2⟩ (hTT' hsT)

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

/-- Any uncountable set in a second-countable linear order admits a sequence of its elements
converging to a point from the right. -/
lemma exists_seq_gt_tendsto_of_not_countable [SecondCountableTopology ι]
    {A : Set ι} (hA : ¬ A.Countable) :
    ∃ (p : ι) (u : ℕ → ι), (∀ k, u k ∈ A) ∧ (∀ k, p < u k) ∧
      Tendsto u atTop (𝓝 p) := by
  have h := countable_setOfPred_isolated_right_within (s := A)
  have hsub : ¬ A ⊆ {x | x ∈ A ∧ 𝓝[A ∩ Set.Ioi x] x = ⊥} := by
    intro hcon
    exact hA (h.mono hcon)
  rw [Set.not_subset] at hsub
  obtain ⟨p, hpA, hpiso⟩ := hsub
  simp only [Set.mem_ofPred_eq, not_and] at hpiso
  have : (𝓝[A ∩ Set.Ioi p] p).NeBot := ⟨hpiso hpA⟩
  obtain ⟨u, hu⟩ := exists_seq_tendsto (𝓝[A ∩ Set.Ioi p] p)
  simp only [tendsto_nhdsWithin_iff, Set.mem_inter_iff, Set.mem_Ioi, eventually_atTop] at hu
  obtain ⟨hu_tendsto, a, hu⟩ := hu
  refine ⟨p, fun k ↦ u (a + k), fun k ↦ (hu (a + k) (by grind)).1,
    fun k ↦ (hu (a + k) (by grind)).2, ?_⟩
  simp_rw [add_comm a]
  exact (tendsto_add_atTop_iff_nat a).mpr hu_tendsto

end Accumulation

open Function

section RealRegularity

variable {X : ι → Ω → ℝ} {T : Set ι}

/-- The events `regularitySet T X d` form a regularity family for the real process `X`. -/
lemma isRegularityFamily_regularitySet : IsRegularityFamily T X (regularitySet T X) :=
  ⟨fun _ _ hd ↦ regularitySet_anti hd,
    fun x d _ hxd hω ↦ right_limit_of_mem_regularitySet x d hxd hω,
    fun x d _ hxd hω ↦ left_limit_of_mem_regularitySet x d hxd hω⟩

variable [OrderBot ι]

/-- Almost surely, `ω` belongs to `regularitySet T X d` for all `d ∈ T` and all `d` isolated on
the right. -/
lemma ae_mem_all_regularitySet_union_nhdsGT_eq_bot [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T ∪ {s | 𝓝[>] s = ⊥}, ω ∈ regularitySet T X d :=
  ae_mem_all_regularitySet hX hT (hT.union countable_setOfPred_isolated_right)

lemma IsRealQuasimartingale.ae_mem_regularitySetRight [SecondCountableTopology ι]
    [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) (hTcof : ∀ x, ¬ IsMax x → ∃ s ∈ T, x < s) :
    ∀ᵐ ω ∂μ, ∀ d, ω ∈ regularitySetRight T (regularitySet T X) d :=
  ProbabilityTheory.ae_mem_regularitySetRight
    (ae_mem_all_regularitySet_union_nhdsGT_eq_bot hX hT) hTcof

lemma ae_right_limit [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) (hTcof : ∀ x, ¬ IsMax x → ∃ d ∈ T, x < d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  filter_upwards [hX.ae_mem_regularitySetRight hT hTcof] with ω hω x
  exact isRegularityFamily_regularitySet.right_limit_of_mem_regularitySetRight (hω x) le_rfl

lemma ae_left_limit [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (hTcof : ∀ x, ¬ IsMax x → ∃ d ∈ T, x ≤ d) :
    ∀ᵐ ω ∂μ, ∀ x, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  filter_upwards [ae_mem_all_regularitySet_union_nhdsGT_eq_bot hX hT] with ω hω
  intro x
  by_cases hx : IsMax x
  · exact left_limit_of_mem_regularitySet x x le_rfl (hω x (.inr hx.nhdsGT_eq_bot))
  · obtain ⟨d, hdT, hxle⟩ := hTcof x hx
    exact left_limit_of_mem_regularitySet x d hxle (hω d (.inl hdT))


/-- The set of points where the right limit along a countable dense set `T` disagrees with `X` is
countable. -/
lemma countable_not_rightLimWithin_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hTc : T.Countable) (hTd : Dense T) :
    {t | ¬ (fun ω ↦ rightLimWithin (X · ω) T t) =ᵐ[μ] X t}.Countable := by
  -- every dense set is cofinal among non-maximal elements
  have hcof : ∀ T : Set ι, Dense T → ∀ x : ι, ¬ IsMax x → ∃ d ∈ T, x < d :=
    fun T hTd x hx ↦ hTd.exists_gt_of_not_isMax hx
  -- the right-limit value along `T`, by choice
  let R T' x ω : ℝ := Function.rightLimWithin (X · ω) T' x
  have hRspec T' x ω (h : ∃ l, Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 l)) :
      Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 (R T' x ω)) := by
    rw [Set.inter_comm] at h ⊢
    exact tendsto_rightLimWithin_of_tendsto h
  -- Stage 1: a.e. one-sided limits along D₀
  have hae₀ := ae_right_limit hX hTc (hcof T hTd)
  -- Stage 2: measurable versions of `R D₀ x`
  have hRm : ∀ x : ι, ∃ g : Ω → ℝ, Measurable g ∧ g =ᵐ[μ] R T x := by
    intro x
    -- if `x` is isolated on the right, the right limit is `X x`
    rcases (𝓝[>] x).eq_or_neBot with hx | hx
    · refine ⟨X x, hX.measurable x, ae_of_all _ fun ω ↦ ?_⟩
      exact (rightLimWithin_eq_of_nhdsGT_eq_bot (X · ω) T hx).symm
    have hne : (𝓝[T ∩ Set.Ioi x] x).NeBot := by
      rw [Set.inter_comm]
      exact nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hTd x
    obtain ⟨v, hv⟩ := exists_seq_tendsto (𝓝[T ∩ Set.Ioi x] x)
    have haet : ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X (v j) ω) atTop (𝓝 (R T x ω)) := by
      filter_upwards [hae₀] with ω hω
      exact (hRspec T x ω (hω x)).comp hv
    obtain ⟨g, hgmeas, hgae⟩ := measurable_limit_of_tendsto_metrizable_ae
      (f := fun j ↦ X (v j)) (L := atTop) (fun j ↦ (hX.measurable (v j)).aemeasurable)
      (by filter_upwards [haet] with ω hω using ⟨_, hω⟩)
    refine ⟨g, hgmeas, ?_⟩
    filter_upwards [haet, hgae] with ω h1 h2
    exact tendsto_nhds_unique h2 h1
  choose Rm hRmMeas hRmae using hRm
  -- Stage 3: the set of points where `R D₀ x` and `X x` disagree is countable
  let Sset : Set ι := {x | ¬ R T x =ᵐ[μ] X x}
  change Sset.Countable
  by_contra hSunc
  set Sn : ℕ → Set ι := fun n ↦
    {x | ENNReal.ofReal (1 / (n + 1)) < μ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}} with hSn
  have hSsub : Sset ⊆ ⋃ n, Sn n := by
    intro x hx
    have hxm : ¬ Rm x =ᵐ[μ] X x := fun hcon ↦ hx ((hRmae x).symm.trans hcon)
    have hpos : μ {ω | Rm x ω ≠ X x ω} ≠ 0 := hxm
    have hBmono : Monotone (fun n : ℕ ↦ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}) := by
      intro n n' hnn' ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hω
      have : (n : ℝ) ≤ (n' : ℝ) := mod_cast hnn'
      gcongr
    have hBunion : {ω | Rm x ω ≠ X x ω} = ⋃ n : ℕ, {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hne
        have habs : 0 < |Rm x ω - X x ω| := abs_pos.2 (sub_ne_zero.2 hne)
        exact exists_nat_one_div_lt habs
      · rintro ⟨n, hn⟩ hcon
        rw [hcon, sub_self, abs_zero] at hn
        exact absurd hn (not_lt.2 (by positivity))
    have hexn : ∃ n₀ : ℕ, 0 < μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by
      by_contra! hcon
      simp only [nonpos_iff_eq_zero] at hcon
      refine hpos ?_
      rw [hBunion]
      refine le_antisymm ((measure_iUnion_le _).trans ?_) zero_le
      simp only [hcon, tsum_zero, Std.le_refl]
    obtain ⟨n₀, hn₀⟩ := hexn
    have hfin : μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} ≠ ⊤ := measure_ne_top μ _
    let ε : ℝ := (μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}).toReal
    have hεpos : 0 < ε := ENNReal.toReal_pos hn₀.ne' hfin
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hεpos
    let n := max n₀ n₁
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [hSn]
    have hsub2 : {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}
        ⊆ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} :=
      hBmono (le_max_left n₀ n₁)
    calc ENNReal.ofReal (1 / (n + 1))
        ≤ ENNReal.ofReal (1 / (n₁ + 1)) := by
          refine ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) ?_)
          gcongr
          exact mod_cast le_max_right n₀ n₁
      _ < ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.2 hn₁
      _ = μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by rw [ENNReal.ofReal_toReal hfin]
      _ ≤ μ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} := measure_mono hsub2
  have hexSn : ∃ n, ¬ (Sn n).Countable := by
    by_contra! hcon
    exact hSunc ((Set.countable_iUnion hcon).mono hSsub)
  obtain ⟨n, hSnunc⟩ := hexSn
  obtain ⟨p, u, huSn, hup, hutend⟩ := exists_seq_gt_tendsto_of_not_countable hSnunc
  set T' : Set ι := T ∪ (Set.range u ∪ {p}) with hT'
  have hT'c : T'.Countable :=
    hTc.union ((Set.countable_range u).union (Set.countable_singleton p))
  have hT'd : Dense T' := hTd.mono Set.subset_union_left
  have haediff : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Rm (u k) ω - X (u k) ω) atTop (𝓝 0) := by
    have hcnt : ∀ᵐ ω ∂μ, ∀ k, Rm (u k) ω = R T (u k) ω := ae_all_iff.2 fun k ↦ hRmae (u k)
    filter_upwards [hae₀, ae_right_limit hX hT'c (hcof T' hT'd), hcnt] with ω hω₀ hω' hkeq
    have hL' := hRspec T' p ω (hω' p)
    have hXu : Tendsto (fun k ↦ X (u k) ω) atTop (𝓝 (R T' p ω)) := by
      refine hL'.comp ?_
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hutend, Filter.Eventually.of_forall fun k ↦ by grind⟩
    have hRu : Tendsto (fun k ↦ R T (u k) ω) atTop (𝓝 (R T' p ω)) :=
      tendsto_rightLim_comp_of_gt hTd Set.subset_union_left
        (fun y ↦ hRspec T y ω (hω₀ y))
        (fun y hy ↦ rightLimWithin_eq_of_nhdsGT_eq_bot (X · ω) T hy) hup hutend
        (fun k _ ↦ .inr (.inl ⟨k, rfl⟩)) hL'
    have hsub := hRu.sub hXu
    rw [sub_self] at hsub
    refine Tendsto.congr (fun k ↦ ?_) hsub
    rw [hkeq k]
  have htim : TendstoInMeasure μ (fun k ω ↦ Rm (u k) ω - X (u k) ω) atTop
      (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun k ↦ ((hRmMeas (u k)).sub (hX.measurable (u k))).aestronglyMeasurable) ?_
    filter_upwards [haediff] with ω hω using hω
  have hcontra := htim (ENNReal.ofReal (1 / (n + 1 : ℝ)))
    (by rw [ENNReal.ofReal_pos]; positivity)
  have hev : ∀ᶠ k in atTop,
      μ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0}
        < ENNReal.ofReal (1 / (n + 1)) := by
    refine hcontra.eventually_lt_const ?_
    positivity
  obtain ⟨k, hk⟩ := hev.exists
  have hmem := huSn k
  rw [hSn, Set.mem_ofPred_eq] at hmem
  have hsub3 : {ω | 1 / (n + 1 : ℝ) < |Rm (u k) ω - X (u k) ω|}
      ⊆ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0} := by
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω ⊢
    rw [edist_dist, dist_zero_right, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hω.le
  exact lt_irrefl _ ((hmem.trans_le (measure_mono hsub3)).trans hk)

end RealRegularity

/-! ## Times used to define the modifications -/

section RegularityTimes

/-- A countable dense set of times which contains all the times that are isolated on the right
(the maximal element and the times which have a successor, if any). The modifications of a
quasimartingale are defined from the limits of the process along this set.

At a time `t` isolated on the right, the modification is `X t`: we need those times in the set
to ensure that the paths of the process restricted to the set, which have one-sided limits almost
surely, control these values. If `ι` is densely ordered without maximal element, this set is
`denseCountable ι`. -/
def regularityTimes (ι : Type*) [Preorder ι] [TopologicalSpace ι] [SecondCountableTopology ι] :
    Set ι :=
  denseCountable ι ∪ {t | 𝓝[>] t = ⊥}

omit [OrderTopology ι] in
lemma mem_regularityTimes_of_nhdsGT_eq_bot [SecondCountableTopology ι] {t : ι}
    (ht : 𝓝[>] t = ⊥) :
    t ∈ regularityTimes ι := .inr ht

omit [OrderTopology ι] in
lemma dense_regularityTimes [SecondCountableTopology ι] : Dense (regularityTimes ι) :=
  dense_denseCountable.mono Set.subset_union_left

lemma countable_regularityTimes [SecondCountableTopology ι] : (regularityTimes ι).Countable :=
  countable_denseCountable.union countable_setOfPred_isolated_right

end RegularityTimes

/-! ## Modifications defined from a regularity family

Let `X` be a process with values in a normed group and let `R` be a regularity family for `X`
along `regularityTimes ι`. We define two processes from the right limits of `X` along
`regularityTimes ι`.

`rightContModifOf R X` has the following properties:
* it is right-continuous, and has left limits at `t` on `regularitySetRight (regularityTimes ι) R t`
* if the filtration is right-continuous and the sets `R d` are `𝓕 d`-measurable, then it is
  strongly adapted.

`cadlagModifOf R X` has the following properties:
* it is càdlàg
* if the filtration is right-continuous and complete, the sets `R d` are `𝓕 d`-measurable and
  almost sure, then it is strongly adapted.

If the events `R d` are almost sure, the two processes are indistinguishable and are equal to
`X t` almost surely
* at all times `t` which are isolated on the right
* at all times `t` at which `X` is right-continuous in probability
* at all times if `X` is a martingale with respect to a right-continuous filtration.

These constructions are used for real quasimartingales below, with `R = regularitySet _ X`, and
for martingales with values in a Banach space. -/

section Measurability

variable {E : Type*} [NormedAddCommGroup E] {X : ι → Ω → E} {T : Set ι}

/-- For a right-continuous filtration and a time `t` that is not isolated on the right, a function
that is `𝓕 s`-strongly measurable for every `s > t` is `𝓕 t`-strongly measurable. -/
lemma stronglyMeasurable_of_forall_gt [𝓕.IsRightContinuous] {t : ι} [(𝓝[>] t).NeBot]
    {f : Ω → E} (h : ∀ s, t < s → StronglyMeasurable[𝓕 s] f) :
    StronglyMeasurable[𝓕 t] f := by
  borelize E
  obtain ⟨s, hs⟩ := not_isMax_iff.1 (not_isMax_of_nhdsGT_neBot (a := t))
  refine stronglyMeasurable_iff_measurable_separable.2
    ⟨fun B hB ↦ ?_, (h s hs).isSeparable_range⟩
  exact measurableSet_of_forall_gt fun s hs ↦ (h s hs).measurable hB

/-- The right limit of a process along `T` at time `t`, restricted to a measurable set on which
that limit exists, is strongly measurable with respect to a sigma-algebra `m` as soon as the process
is `m`-strongly measurable at all times of a right neighborhood of `t` in `T`. -/
lemma stronglyMeasurable_indicator_rightLimWithin [FirstCountableTopology ι]
    {m : MeasurableSpace Ω} {G : Set Ω} (hG : MeasurableSet[m] G) {t : ι} {S : Set ι}
    (hS : S ∈ 𝓝[T ∩ Set.Ioi t] t) (hXS : ∀ s ∈ S, StronglyMeasurable[m] (X s))
    (hXt : StronglyMeasurable[m] (X t))
    (hlim : ∀ ω ∈ G, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) :
    StronglyMeasurable[m] (G.indicator fun ω ↦ rightLimWithin (X · ω) T t) := by
  rcases (𝓝[T ∩ Set.Ioi t] t).eq_or_neBot with hbot | hne
  · -- if the right neighbourhood filter is trivial, the right limit is `X t`
    have heq : (fun ω ↦ rightLimWithin (X · ω) T t) = X t := by
      ext ω
      exact rightLimWithin_eq_of_eq_bot _ (by rwa [Set.inter_comm])
    rw [heq]
    exact hXt.indicator hG
  -- otherwise, the right limit is the limit along a sequence of times in `S`
  obtain ⟨v, hv⟩ := exists_seq_tendsto (𝓝[T ∩ Set.Ioi t] t)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hv.eventually hS)
  have hv' : Tendsto (fun n ↦ v (n + N)) atTop (𝓝[T ∩ Set.Ioi t] t) :=
    (tendsto_add_atTop_iff_nat N).2 hv
  refine stronglyMeasurable_of_tendsto atTop
    (fun n ↦ (hXS (v (n + N)) (hN _ (by lia))).indicator hG) (tendsto_pi_nhds.2 fun ω ↦ ?_)
  by_cases hω : ω ∈ G
  · simp only [Set.indicator_of_mem hω]
    have h := hlim ω hω
    rw [Set.inter_comm] at h
    have h' := tendsto_rightLimWithin_of_tendsto h
    rw [Set.inter_comm] at h'
    exact h'.comp hv'
  · simp only [Set.indicator_of_notMem hω]
    exact tendsto_const_nhds

end Measurability

section RightContModifOf

variable [SecondCountableTopology ι] {E : Type*} [NormedAddCommGroup E] {X : ι → Ω → E}
  {R : ι → Set Ω}

/-- The right-continuous modification of a process `X` with regularity family `R`, defined from
the right limits of `X` along the countable dense set `regularityTimes ι`. -/
noncomputable
def rightContModifOf (R : ι → Set Ω) (X : ι → Ω → E) (t : ι) (ω : Ω) : E :=
  open Classical in
  if ω ∈ regularitySetRight (regularityTimes ι) R t
    then rightLimWithin (X · ω) (regularityTimes ι) t else 0

omit [OrderTopology ι] in
lemma rightContModifOf_eq_indicator (R : ι → Set Ω) (X : ι → Ω → E) (t : ι) :
    rightContModifOf R X t = (regularitySetRight (regularityTimes ι) R t).indicator
      fun ω ↦ rightLimWithin (X · ω) (regularityTimes ι) t := by
  ext ω
  simp [rightContModifOf, Set.indicator]

omit [OrderTopology ι] in
lemma rightContModifOf_eq_zero {x : ι} {ω : Ω}
    (hω : ω ∉ regularitySetRight (regularityTimes ι) R x) :
    (rightContModifOf R X · ω) =ᶠ[𝓝[>] x] 0 := by
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  have hy' : ω ∉ regularitySetRight (regularityTimes ι) R y :=
    fun hω' ↦ hω (regularitySetRight_anti (le_of_lt hy) hω')
  simp [rightContModifOf, hy']

section Pathwise

variable (hR : IsRegularityFamily (regularityTimes ι) X R)
include hR

lemma tendsto_rightContModifOf_rightLimWithin {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (regularityTimes ι) R x) :
    Tendsto (rightContModifOf R X · ω) (𝓝[>] x)
      (𝓝 (rightLimWithin (X · ω) (regularityTimes ι) x)) := by
  classical
  rw [tendsto_congr' (f₂ := rightLimWithin (X · ω) (regularityTimes ι))]
  swap
  · filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
      using by simp [rightContModifOf, hy]
  suffices ContinuousWithinAt (rightLimWithin (X · ω) (regularityTimes ι)) (Set.Ici x) x by
    rwa [← continuousWithinAt_Ioi_iff_Ici] at this
  exact hR.continuousWithinAt_rightLimWithin dense_regularityTimes
    (fun _ ↦ mem_regularityTimes_of_nhdsGT_eq_bot) hω

lemma tendsto_rightContModifOf_leftLimWithin {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (regularityTimes ι) R x) :
    Tendsto (rightContModifOf R X · ω) (𝓝[<] x)
      (𝓝 (leftLimWithin (X · ω) (regularityTimes ι) x)) := by
  have h_mem y (hyx : y ≤ x) : ω ∈ regularitySetRight (regularityTimes ι) R y :=
    regularitySetRight_anti hyx hω
  classical
  rw [tendsto_congr' (f₂ := rightLimWithin (X · ω) (regularityTimes ι))]
  swap
  · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
    simp [rightContModifOf, h_mem y (le_of_lt hy)]
  refine tendsto_rightLim_nhdsLT dense_regularityTimes
    (fun _ ↦ mem_regularityTimes_of_nhdsGT_eq_bot) ?_
    (fun y hy ↦ rightLimWithin_eq_of_nhdsGT_eq_bot _ _ hy) (hR.tendsto_nhdsLT_leftLimWithin hω)
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  exact hR.tendsto_nhdsGT_rightLimWithin (h_mem y (le_of_lt hy))

/-- The paths of `rightContModifOf R X` are right-continuous. -/
lemma continuousWithinAt_rightContModifOf (x : ι) (ω : Ω) :
    ContinuousWithinAt (rightContModifOf R X · ω) (Set.Ioi x) x := by
  by_cases hω : ω ∈ regularitySetRight (regularityTimes ι) R x
  · have hYx : rightContModifOf R X x ω = rightLimWithin (X · ω) (regularityTimes ι) x := by
      simp only [rightContModifOf, ite_eq_left hω]
    rw [ContinuousWithinAt, hYx]
    exact tendsto_rightContModifOf_rightLimWithin hR hω
  · refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (rightContModifOf_eq_zero hω) ?_
    · fun_prop
    · simp [rightContModifOf, hω]

lemma stronglyMeasurable_rightContModifOf (hX : StronglyAdapted 𝓕 X)
    (hRm : ∀ d, MeasurableSet[𝓕 d] (R d)) (t : ι) :
    StronglyMeasurable (rightContModifOf R X t) := by
  rw [rightContModifOf_eq_indicator]
  exact stronglyMeasurable_indicator_rightLimWithin
    (measurableSet_regularitySetRight' (fun d ↦ 𝓕.le d _ (hRm d)) countable_regularityTimes t)
    Filter.univ_mem (fun s _ ↦ (hX s).mono (𝓕.le s)) ((hX t).mono (𝓕.le t))
    fun ω hω ↦ hR.right_limit_of_mem_regularitySetRight hω le_rfl

lemma stronglyAdapted_rightContModifOf [𝓕.IsRightContinuous] (hX : StronglyAdapted 𝓕 X)
    (hRm : ∀ d, MeasurableSet[𝓕 d] (R d)) :
    StronglyAdapted 𝓕 (rightContModifOf R X) := by
  intro t
  have hG s (hts : t ≤ s) : MeasurableSet[𝓕 s] (regularitySetRight (regularityTimes ι) R t) :=
    𝓕.mono hts _ (measurableSet_regularitySetRight hR.anti hRm countable_regularityTimes
      dense_regularityTimes t)
  have hlim ω (hω : ω ∈ regularitySetRight (regularityTimes ι) R t) :
      ∃ l, Tendsto (X · ω) (𝓝[regularityTimes ι ∩ Set.Ioi t] t) (𝓝 l) :=
    hR.right_limit_of_mem_regularitySetRight hω le_rfl
  rw [rightContModifOf_eq_indicator]
  rcases (𝓝[>] t).eq_or_neBot with ht | ht
  · -- if `t` is isolated on the right, the right limit is `X t`
    refine stronglyMeasurable_indicator_rightLimWithin (S := ∅) (hG t le_rfl) ?_ (by simp)
      (hX t) hlim
    simp [eq_bot_mono (nhdsWithin_mono _ Set.inter_subset_right) ht]
  -- otherwise, it suffices to show `𝓕 s`-measurability for every `s > t`
  refine stronglyMeasurable_of_forall_gt fun s hts ↦ ?_
  refine stronglyMeasurable_indicator_rightLimWithin (S := Set.Iio s) (hG s hts.le) ?_
    (fun u hu ↦ (hX u).mono (𝓕.mono (le_of_lt hu))) ((hX t).mono (𝓕.mono hts.le)) hlim
  exact nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hts)

end Pathwise

section AlmostSure

variable (hRae : ∀ᵐ ω ∂μ, ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t)
include hRae

omit [OrderTopology ι] in
lemma rightContModifOf_ae_eq_of_rightLimWithin_ae_eq {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (regularityTimes ι) t) =ᵐ[μ] X t) :
    rightContModifOf R X t =ᵐ[μ] X t := by
  filter_upwards [hRae, ht] with ω hω hωR
  simpa only [rightContModifOf, ite_eq_left (hω _)]

/-- At a time `t` which is isolated on the right, `rightContModifOf R X t` is a.e. equal to
`X t`. -/
lemma rightContModifOf_ae_eq_of_nhdsGT_eq_bot {t : ι} (ht : 𝓝[>] t = ⊥) :
    rightContModifOf R X t =ᵐ[μ] X t :=
  rightContModifOf_ae_eq_of_rightLimWithin_ae_eq hRae
    (ae_of_all _ fun _ ↦ rightLimWithin_eq_of_nhdsGT_eq_bot _ _ ht)

/-- If `t` is not isolated on the right, there is a sequence of times `w n ∈ (t, u]` tending to `t`
along which `X` converges almost surely to `rightContModifOf R X t`. -/
lemma exists_seq_tendsto_rightContModifOf (hR : IsRegularityFamily (regularityTimes ι) X R)
    {t u : ι} [(𝓝[>] t).NeBot] (htu : t < u) :
    ∃ w : ℕ → ι, (∀ n, t < w n) ∧ (∀ n, w n ≤ u) ∧ Tendsto w atTop (𝓝[>] t) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (w n) ω) atTop (𝓝 (rightContModifOf R X t ω)) := by
  let T := regularityTimes ι
  have hTd : Dense T := dense_regularityTimes
  have : (𝓝[Set.Ioi t ∩ T] t).NeBot := nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hTd t
  obtain ⟨w₀, hw₀⟩ := exists_seq_tendsto (𝓝[Set.Ioi t ∩ T] t)
  have h_ev : ∀ᶠ n in atTop, w₀ n ≤ u ∧ w₀ n ∈ Set.Ioi t ∩ T := by
    rw [tendsto_nhdsWithin_iff] at hw₀
    filter_upwards [hw₀.1.eventually (eventually_lt_nhds htu), hw₀.2] with n hn1 hn2
      using ⟨hn1.le, hn2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 h_ev
  have hw : Tendsto (fun n ↦ w₀ (n + N)) atTop (𝓝[T ∩ Set.Ioi t] t) := by
    rw [Set.inter_comm]
    exact (tendsto_add_atTop_iff_nat N).2 hw₀
  refine ⟨fun n ↦ w₀ (n + N), fun n ↦ (hN (n + N) (by lia)).2.1, fun n ↦ (hN (n + N) (by lia)).1,
    hw.mono_right (nhdsWithin_mono _ Set.inter_subset_right), ?_⟩
  filter_upwards [hRae] with ω hω
  have hYω : rightContModifOf R X t ω = rightLimWithin (X · ω) T t := by
    simp only [rightContModifOf, T, ite_eq_left (hω t)]
  rw [hYω]
  exact (hR.tendsto_nhdsGT_rightLimWithin (hω t)).comp hw

/-- At a time `t` at which `X` is right-continuous in probability, `rightContModifOf R X t` is a.e.
equal to `X t`. -/
lemma rightContModifOf_ae_eq_of_tendstoInMeasure [IsFiniteMeasure μ]
    (hR : IsRegularityFamily (regularityTimes ι) X R) (hX : StronglyAdapted 𝓕 X) (t : ι)
    (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModifOf R X t =ᵐ[μ] X t := by
  -- if `t` is isolated on the right, the right limit is `X t`
  rcases (𝓝[>] t).eq_or_neBot with ht | ht
  · exact rightContModifOf_ae_eq_of_nhdsGT_eq_bot hRae ht
  -- a sequence `w n > t` which tends to `t`, with `X (w n) → rightContModifOf R X t` a.e.
  obtain ⟨u, htu⟩ := not_isMax_iff.1 (not_isMax_of_nhdsGT_neBot (a := t))
  obtain ⟨w, -, -, hw, h_tendsto⟩ := exists_seq_tendsto_rightContModifOf hRae hR htu
  refine tendstoInMeasure_ae_unique ?_ (hXRC.comp hw)
  exact tendstoInMeasure_of_tendsto_ae
    (fun n ↦ ((hX (w n)).mono (𝓕.le _)).aestronglyMeasurable) h_tendsto

/-- The right-continuous modification of a martingale with respect to a right-continuous
filtration is a modification. -/
theorem _root_.MeasureTheory.Martingale.rightContModifOf_ae_eq [NormedSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure μ] [𝓕.IsRightContinuous] (hX : Martingale X 𝓕 μ)
    (hR : IsRegularityFamily (regularityTimes ι) X R) (hRm : ∀ d, MeasurableSet[𝓕 d] (R d))
    (t : ι) :
    rightContModifOf R X t =ᵐ[μ] X t := by
  -- if `t` is isolated on the right, the right limit is `X t`
  rcases (𝓝[>] t).eq_or_neBot with ht | ht
  · exact rightContModifOf_ae_eq_of_nhdsGT_eq_bot hRae ht
  -- a sequence `w n ∈ (t, u]` which tends to `t`, with `X (w n) → rightContModifOf R X t` a.e.
  obtain ⟨u, htu⟩ := not_isMax_iff.1 (not_isMax_of_nhdsGT_neBot (a := t))
  obtain ⟨w, htw, hwu, -, h_tendsto⟩ := exists_seq_tendsto_rightContModifOf hRae hR htu
  -- the sequence `X (w n)` is uniformly integrable, hence converges in `L¹`
  have hUI : UniformIntegrable (fun n ↦ X (w n)) 1 μ := by
    rw [uniformIntegrable_congr_ae (g := fun n ↦ μ[X u | 𝓕 (w n)])
      fun n ↦ (hX.2 (w n) u (hwu n)).symm]
    exact (hX.integrable u).uniformIntegrable_condExp' fun n ↦ 𝓕.le (w n)
  have hY_int : Integrable (rightContModifOf R X t) μ := hUI.integrable_of_ae_tendsto h_tendsto
  -- `rightContModifOf R X t` and `X t` are `𝓕 t`-measurable, with the same integrals on `𝓕 t`
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
    (fun _ _ _ ↦ hY_int.integrableOn) (fun _ _ _ ↦ (hX.integrable t).integrableOn)
    (fun A hA _ ↦ ?_)
    (stronglyAdapted_rightContModifOf hR hX.stronglyAdapted hRm t).aestronglyMeasurable
    (hX.stronglyAdapted t).aestronglyMeasurable
  refine tendsto_nhds_unique (hUI.tendsto_setIntegral h_tendsto A) ?_
  simp_rw [← hX.setIntegral_eq (htw _).le hA]
  exact tendsto_const_nhds

end AlmostSure

end RightContModifOf

section CadlagModifOf

variable [SecondCountableTopology ι] {E : Type*} [NormedAddCommGroup E] {X : ι → Ω → E}
  {R : ι → Set Ω}

/-- The càdlàg modification of a process `X` with regularity family `R`, defined from the right
limits of `X` along the countable dense set `regularityTimes ι`. -/
noncomputable
def cadlagModifOf (R : ι → Set Ω) (X : ι → Ω → E) (t : ι) (ω : Ω) : E :=
  open Classical in
  if ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t then rightContModifOf R X t ω else 0

omit [OrderTopology ι] in
lemma cadlagModifOf_ae_eq_rightContModifOf
    (hRae : ∀ᵐ ω ∂μ, ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t) :
    ∀ᵐ ω ∂μ, ∀ t, cadlagModifOf R X t ω = rightContModifOf R X t ω := by
  filter_upwards [hRae] with ω hω
  simp [cadlagModifOf, ite_eq_left hω]

omit [OrderTopology ι] in
lemma cadlagModifOf_ae_eq_of_rightContModifOf_ae_eq
    (hRae : ∀ᵐ ω ∂μ, ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t) {t : ι}
    (ht : rightContModifOf R X t =ᵐ[μ] X t) :
    cadlagModifOf R X t =ᵐ[μ] X t := by
  filter_upwards [cadlagModifOf_ae_eq_rightContModifOf (X := X) hRae, ht] with ω hω hωt
  rw [hω t, hωt]

lemma measurableSet_forall_mem_regularitySetRight (hRm : ∀ d, MeasurableSet (R d)) :
    MeasurableSet {ω | ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t} := by
  have : {ω | ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t}
      = ⋂ t ∈ regularityTimes ι, regularitySetRight (regularityTimes ι) R t := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h t _ ↦ h t, fun h t ↦ ?_⟩
    by_cases ht : IsMax t
    · exact h t (mem_regularityTimes_of_nhdsGT_eq_bot ht.nhdsGT_eq_bot)
    obtain ⟨t', ht'T, htt'⟩ := dense_regularityTimes.exists_gt_of_not_isMax ht
    exact regularitySetRight_anti htt'.le (h t' ht'T)
  rw [this]
  exact MeasurableSet.biInter countable_regularityTimes
    fun t _ ↦ measurableSet_regularitySetRight' hRm countable_regularityTimes t

variable (hR : IsRegularityFamily (regularityTimes ι) X R)
include hR

lemma continuousWithinAt_cadlagModifOf (x : ι) (ω : Ω) :
    ContinuousWithinAt (cadlagModifOf R X · ω) (Set.Ioi x) x := by
  unfold cadlagModifOf
  split_ifs with hω
  · exact continuousWithinAt_rightContModifOf hR x ω
  · fun_prop

lemma exists_tendsto_nhdsLT_cadlagModifOf (x : ι) (ω : Ω) :
    ∃ l, Tendsto (cadlagModifOf R X · ω) (𝓝[<] x) (𝓝 l) := by
  unfold cadlagModifOf
  split_ifs with hω
  · exact ⟨leftLimWithin (X · ω) (regularityTimes ι) x,
      tendsto_rightContModifOf_leftLimWithin hR (hω x)⟩
  · exact ⟨0, tendsto_const_nhds⟩

/-- The paths of `cadlagModifOf R X` are càdlàg. -/
theorem isCadlag_cadlagModifOf (ω : Ω) : IsCadlag (cadlagModifOf R X · ω) :=
  ⟨fun x ↦ continuousWithinAt_cadlagModifOf hR x ω,
    fun x ↦ exists_tendsto_nhdsLT_cadlagModifOf hR x ω⟩

lemma stronglyMeasurable_cadlagModifOf (hX : StronglyAdapted 𝓕 X)
    (hRm : ∀ d, MeasurableSet[𝓕 d] (R d)) (t : ι) :
    StronglyMeasurable (cadlagModifOf R X t) :=
  StronglyMeasurable.ite (measurableSet_forall_mem_regularitySetRight fun d ↦ 𝓕.le d _ (hRm d))
    (stronglyMeasurable_rightContModifOf hR hX hRm t) stronglyMeasurable_const

lemma stronglyAdapted_cadlagModifOf [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    (hX : StronglyAdapted 𝓕 X) (hRm : ∀ d, MeasurableSet[𝓕 d] (R d))
    (hRae : ∀ᵐ ω ∂μ, ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t) :
    StronglyAdapted 𝓕 (cadlagModifOf R X) := by
  refine fun i ↦ StronglyMeasurable.ite ?_ (stronglyAdapted_rightContModifOf hR hX hRm i)
    stronglyMeasurable_const
  rw [← MeasurableSet.compl_iff]
  refine Filtration.IsComplete.measurableSet_of_null ?_ i (μ := μ)
  rwa [ae_iff] at hRae

end CadlagModifOf

/-! ## Right-continuous modification of a quasimartingale

For a real quasimartingale `X` we define a process `rightContModifReal X` with the following
properties:
* `rightContModifReal X` is right-continuous
* `rightContModifReal X` has left limits almost everywhere
* for all `t` outside a countable set, `rightContModifReal X t =ᵐ[μ] X t`
* if `t` is isolated on the right (for example if `t` is a maximal element of `ι` or has a
  successor), then `rightContModifReal X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `rightContModifReal X` is a modification of `X`.
* if the filtration is right-continuous, then `rightContModifReal X` is adapted.

Note that if `X` is not right-continuous in probability, we can still obtain a modification by
changing the value of `rightContModifReal X` on a countable set of times, with the drawback that the
right-continuity then holds only outside that countable set.

-/

section RightContModif

variable [SecondCountableTopology ι] {X : ι → Ω → ℝ}

/-- The right-continuous modification of a real quasimartingale, defined from the right limits
along the countable dense set `regularityTimes ι`. -/
noncomputable
def rightContModifReal (X : ι → Ω → ℝ) : ι → Ω → ℝ :=
  rightContModifOf (regularitySet (regularityTimes ι) X) X

lemma continuousWithinAt_rightContModifReal (x : ι) (ω : Ω) :
    ContinuousWithinAt (rightContModifReal X · ω) (Set.Ioi x) x :=
  continuousWithinAt_rightContModifOf isRegularityFamily_regularitySet x ω

variable [OrderBot ι]

lemma measurable_rightContModifReal (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (rightContModifReal X t) :=
  (stronglyMeasurable_rightContModifOf isRegularityFamily_regularitySet hX.stronglyAdapted
    (measurableSet_regularitySet hX countable_regularityTimes) t).measurable

lemma stronglyAdapted_rightContModifReal [𝓕.IsRightContinuous] (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (rightContModifReal X) :=
  stronglyAdapted_rightContModifOf isRegularityFamily_regularitySet hX.stronglyAdapted
    (measurableSet_regularitySet hX countable_regularityTimes)

lemma adapted_rightContModifReal [𝓕.IsRightContinuous] (hX : IsRealQuasimartingale 𝓕 X μ) :
    Adapted 𝓕 (rightContModifReal X) :=
  fun t ↦ (stronglyAdapted_rightContModifReal hX t).measurable

variable [IsFiniteMeasure μ]

/-- Almost surely, `ω` belongs to all the events used to define the modifications of a real
quasimartingale. -/
lemma IsRealQuasimartingale.ae_mem_regularitySetRight_regularityTimes
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    ∀ᵐ ω ∂μ, ∀ t,
      ω ∈ regularitySetRight (regularityTimes ι) (regularitySet (regularityTimes ι) X) t :=
  hX.ae_mem_regularitySetRight countable_regularityTimes
    fun _ ↦ dense_regularityTimes.exists_gt_of_not_isMax

lemma rightContModifReal_ae_eq_of_rightLimWithin_ae_eq (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (regularityTimes ι) t) =ᵐ[μ] X t) :
    rightContModifReal X t =ᵐ[μ] X t :=
  rightContModifOf_ae_eq_of_rightLimWithin_ae_eq hX.ae_mem_regularitySetRight_regularityTimes ht

/-- At a time `t` which is isolated on the right, the right-continuous modification is a.e. equal
to `X t`. -/
lemma rightContModifReal_ae_eq_of_nhdsGT_eq_bot (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : 𝓝[>] t = ⊥) :
    rightContModifReal X t =ᵐ[μ] X t :=
  rightContModifOf_ae_eq_of_nhdsGT_eq_bot hX.ae_mem_regularitySetRight_regularityTimes ht

/-- At a maximal time `t`, the right-continuous modification is a.e. equal to `X t`. -/
lemma rightContModifReal_ae_eq_of_isMax (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι} (ht : IsMax t) :
    rightContModifReal X t =ᵐ[μ] X t :=
  rightContModifReal_ae_eq_of_nhdsGT_eq_bot hX ht.nhdsGT_eq_bot

/-- The set of points where the right modification of a real quasimartingale along
a countable dense set `T` disagrees with `X` is countable. -/
lemma countable_not_rightContModifReal_ae_eq (hX : IsRealQuasimartingale 𝓕 X μ) :
    {t | ¬ rightContModifReal X t =ᵐ[μ] X t}.Countable := by
  refine (countable_not_rightLimWithin_ae_eq hX countable_regularityTimes
    dense_regularityTimes).mono fun t ht ↦ ?_
  exact fun hcon ↦ ht (rightContModifReal_ae_eq_of_rightLimWithin_ae_eq hX hcon)

lemma rightContModifReal_ae_eq_of_tendstoInMeasure (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModifReal X t =ᵐ[μ] X t :=
  rightContModifOf_ae_eq_of_tendstoInMeasure hX.ae_mem_regularitySetRight_regularityTimes
    isRegularityFamily_regularitySet hX.stronglyAdapted t hXRC

end RightContModif

/-! ## Càdlàg modification of a quasimartingale

For a real quasimartingale `X` we define a process `cadlagModifReal X` with the following
properties:
* `cadlagModifReal X` is càdlàg
* for all `t` outside a countable set, `cadlagModifReal X t =ᵐ[μ] X t`
* if `t` is isolated on the right (for example if `t` is a maximal element of `ι` or has a
  successor), then `cadlagModifReal X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `cadlagModifReal X` is a modification of `X`.
* if the filtration is right-continuous and complete, then `cadlagModifReal X` is adapted.

TODO: if `t ↦ μ[X t]` is right-continuous (in particular if `X` is a martingale),
then `cadlagModifReal X` is a modification of `X` without the assumption that `X`
is right-continuous in probability.

-/

section CadlagModif

variable [SecondCountableTopology ι] {X : ι → Ω → ℝ}

/-- The càdlàg modification of a real quasimartingale, defined from the right limits
along the countable dense set `regularityTimes ι`. -/
noncomputable
def cadlagModifReal (X : ι → Ω → ℝ) : ι → Ω → ℝ :=
  cadlagModifOf (regularitySet (regularityTimes ι) X) X

lemma continuousWithinAt_cadlagModifReal (x : ι) (ω : Ω) :
    ContinuousWithinAt (cadlagModifReal X · ω) (Set.Ioi x) x :=
  continuousWithinAt_cadlagModifOf isRegularityFamily_regularitySet x ω

lemma exists_tendsto_nhdsLT_cadlagModifReal (x : ι) (ω : Ω) :
    ∃ l, Tendsto (cadlagModifReal X · ω) (𝓝[<] x) (𝓝 l) :=
  exists_tendsto_nhdsLT_cadlagModifOf isRegularityFamily_regularitySet x ω

theorem isCadlag_cadlagModifReal (ω : Ω) : IsCadlag (cadlagModifReal X · ω) :=
  isCadlag_cadlagModifOf isRegularityFamily_regularitySet ω

variable [OrderBot ι]

lemma measurable_cadlagModifReal (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (cadlagModifReal X t) :=
  (stronglyMeasurable_cadlagModifOf isRegularityFamily_regularitySet hX.stronglyAdapted
    (measurableSet_regularitySet hX countable_regularityTimes) t).measurable

variable [IsFiniteMeasure μ]

lemma cadlagModifReal_ae_eq_rightContModifReal (hX : IsRealQuasimartingale 𝓕 X μ) :
    ∀ᵐ ω ∂μ, ∀ t, cadlagModifReal X t ω = rightContModifReal X t ω :=
  cadlagModifOf_ae_eq_rightContModifOf hX.ae_mem_regularitySetRight_regularityTimes

lemma cadlagModifReal_ae_eq_of_rightContModifReal_ae_eq (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : rightContModifReal X t =ᵐ[μ] X t) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  cadlagModifOf_ae_eq_of_rightContModifOf_ae_eq hX.ae_mem_regularitySetRight_regularityTimes ht

lemma cadlagModifReal_ae_eq_of_rightLimWithin_ae_eq (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (regularityTimes ι) t) =ᵐ[μ] X t) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  cadlagModifReal_ae_eq_of_rightContModifReal_ae_eq hX
    (rightContModifReal_ae_eq_of_rightLimWithin_ae_eq hX ht)

/-- At a time `t` which is isolated on the right, the càdlàg modification is a.e. equal to
`X t`. -/
lemma cadlagModifReal_ae_eq_of_nhdsGT_eq_bot (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : 𝓝[>] t = ⊥) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  cadlagModifReal_ae_eq_of_rightContModifReal_ae_eq hX
    (rightContModifReal_ae_eq_of_nhdsGT_eq_bot hX ht)

/-- At a maximal time `t`, the càdlàg modification is a.e. equal to `X t`. -/
lemma cadlagModifReal_ae_eq_of_isMax (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι} (ht : IsMax t) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  cadlagModifReal_ae_eq_of_nhdsGT_eq_bot hX ht.nhdsGT_eq_bot

/-- The set of points where the cadlag modification of a real quasimartingale along
a countable dense set `T` disagrees with `X` is countable. -/
lemma countable_not_cadlagModifReal_ae_eq (hX : IsRealQuasimartingale 𝓕 X μ) :
    {t | ¬ cadlagModifReal X t =ᵐ[μ] X t}.Countable :=
  (countable_not_rightContModifReal_ae_eq hX).mono fun _ ht hcon ↦
    ht (cadlagModifReal_ae_eq_of_rightContModifReal_ae_eq hX hcon)

lemma cadlagModifReal_ae_eq_of_tendstoInMeasure (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  cadlagModifReal_ae_eq_of_rightContModifReal_ae_eq hX
    (rightContModifReal_ae_eq_of_tendstoInMeasure hX t hXRC)

lemma stronglyAdapted_cadlagModifReal [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (cadlagModifReal X) :=
  stronglyAdapted_cadlagModifOf isRegularityFamily_regularitySet hX.stronglyAdapted
    (measurableSet_regularitySet hX countable_regularityTimes)
    hX.ae_mem_regularitySetRight_regularityTimes

lemma adapted_cadlagModifReal [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    Adapted 𝓕 (cadlagModifReal X) :=
  fun t ↦ (stronglyAdapted_cadlagModifReal hX t).measurable

end CadlagModif

lemma _root_.MeasureTheory.Martingale.integral_eq [SigmaFiniteFiltration μ 𝓕] {X : ι → Ω → ℝ}
    (hX : Martingale X 𝓕 μ) (i j : ι) : ∫ ω, X i ω ∂μ = ∫ ω, X j ω ∂μ := by
  wlog hij : i ≤ j
  · exact (this hX j i (by grind)).symm
  conv_rhs => rw [← integral_condExp (𝓕.le i)]
  refine integral_congr_ae ?_
  filter_upwards [hX.2 i j hij] with _ heq using heq.symm

section Modification

variable [SecondCountableTopology ι] [OrderBot ι] [IsFiniteMeasure μ] {X : ι → Ω → ℝ}

/-- If `t` is not isolated on the right, there is a sequence of times `w n ∈ (t, u]` tending to `t`
along which a quasimartingale `X` converges almost surely to `rightContModifReal X t`. -/
lemma exists_seq_tendsto_rightContModifReal (hX : IsRealQuasimartingale 𝓕 X μ) {t u : ι}
    [(𝓝[>] t).NeBot] (htu : t < u) :
    ∃ w : ℕ → ι, (∀ n, t < w n) ∧ (∀ n, w n ≤ u) ∧ Tendsto w atTop (𝓝[>] t) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (w n) ω) atTop (𝓝 (rightContModifReal X t ω)) :=
  exists_seq_tendsto_rightContModifOf hX.ae_mem_regularitySetRight_regularityTimes
    isRegularityFamily_regularitySet htu

/-- The right-continuous modification of a martingale with respect to a right-continuous
filtration is a modification. -/
theorem _root_.MeasureTheory.Martingale.rightContModifReal_ae_eq [𝓕.IsRightContinuous]
    (hX : Martingale X 𝓕 μ) (t : ι) :
    rightContModifReal X t =ᵐ[μ] X t :=
  hX.rightContModifOf_ae_eq hX.isRealQuasimartingale.ae_mem_regularitySetRight_regularityTimes
    isRegularityFamily_regularitySet
    (measurableSet_regularitySet hX.isRealQuasimartingale countable_regularityTimes) t

/-- The càdlàg modification of a martingale with respect to a right-continuous filtration is a
modification. -/
theorem _root_.MeasureTheory.Martingale.cadlagModifReal_ae_eq [𝓕.IsRightContinuous]
    (hX : Martingale X 𝓕 μ) (t : ι) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  cadlagModifReal_ae_eq_of_rightContModifReal_ae_eq hX.isRealQuasimartingale
    (hX.rightContModifReal_ae_eq t)

/-- The right-continuous modification of a submartingale with respect to a right-continuous
filtration is a modification at the times where the expectation is right-continuous. -/
theorem _root_.MeasureTheory.Submartingale.rightContModifReal_ae_eq [𝓕.IsRightContinuous]
    (hX : Submartingale X 𝓕 μ) (t : ι)
    (hXRC : Tendsto (fun s ↦ μ[X s]) (𝓝[>] t) (𝓝 (μ[X t]))) :
    rightContModifReal X t =ᵐ[μ] X t := by
  have hXq : IsRealQuasimartingale 𝓕 X μ := hX.isRealQuasimartingale
  -- if `t` is isolated on the right, the right limit is `X t`
  rcases (𝓝[>] t).eq_or_neBot with ht | ht
  · exact rightContModifReal_ae_eq_of_nhdsGT_eq_bot hXq ht
  -- a sequence `w n ∈ (t, u]` which tends to `t`, with `X (w n) → Y := rightContModifReal X t` a.e.
  obtain ⟨u, htu⟩ := not_isMax_iff.1 (not_isMax_of_nhdsGT_neBot (a := t))
  obtain ⟨w, htw, hwu, hw, h_tendsto⟩ := exists_seq_tendsto_rightContModifReal hXq htu
  set Y := rightContModifReal X t
  -- `Y` is integrable, by Fatou's lemma
  have hY_int : Integrable Y μ := by
    refine memLp_one_iff_integrable.1 ?_
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n ↦ (hX.integrable (w n)).aestronglyMeasurable) Y
      (measurable_rightContModifReal hXq t).aestronglyMeasurable h_tendsto).trans_lt ?_
    have h_le n : eLpNorm (X (w n)) 1 μ
        ≤ ENNReal.ofReal (2 * ∫ ω, X u ω ⊔ 0 ∂μ - ∫ ω, X t ω ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm (hX.integrable _).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable _)]
      exact ENNReal.ofReal_le_ofReal (hX.integral_abs_le (htw n).le (hwu n))
    refine (liminf_le_liminf (.of_forall h_le)).trans_lt ?_
    simp
  -- the truncated processes `X ⊔ c` are submartingales, uniformly integrable along `w`
  have hZ (c : ℝ) : Submartingale (fun s ω ↦ X s ω ⊔ c) 𝓕 μ :=
    hX.sup (martingale_const 𝓕 μ c).submartingale
  have hZ_UI (c : ℝ) : UniformIntegrable (fun n ω ↦ X (w n) ω ⊔ c) 1 μ :=
    uniformIntegrable_of_le_condExp (fun n ↦ 𝓕.le (w n)) ((hZ c).integrable u)
      (fun n ↦ ((hZ c).integrable (w n)).aestronglyMeasurable)
      (fun n ↦ .of_forall fun ω ↦ le_sup_right) (fun n ↦ (hZ c).2.1 (w n) u (hwu n))
  have hZ_lim (c : ℝ) (A : Set Ω) : Tendsto (fun n ↦ ∫ ω in A, X (w n) ω ⊔ c ∂μ) atTop
      (𝓝 (∫ ω in A, Y ω ⊔ c ∂μ)) := by
    refine (hZ_UI c).tendsto_setIntegral ?_ A
    filter_upwards [h_tendsto] with ω hω using hω.sup_nhds tendsto_const_nhds
  -- `∫_A X t ≤ ∫_A Y` for `A ∈ 𝓕 t`: true for the truncated processes, then let `c → -∞`
  have h_le (A : Set Ω) (hA : MeasurableSet[𝓕 t] A) :
      ∫ ω in A, X t ω ∂μ ≤ ∫ ω in A, Y ω ∂μ := by
    refine le_of_tendsto_of_tendsto' ((hX.integrable t).tendsto_setIntegral_sup_neg_natCast A)
      (hY_int.tendsto_setIntegral_sup_neg_natCast A) fun k ↦ ?_
    exact ge_of_tendsto' (hZ_lim _ A) fun n ↦ (hZ _).setIntegral_le (htw n).le hA
  -- `∫ Y ≤ ∫ X (w n₀)` for all `n₀`, by the same argument, hence `∫ Y ≤ ∫ X t`
  have h_ge : ∫ ω, Y ω ∂μ ≤ ∫ ω, X t ω ∂μ := by
    refine ge_of_tendsto' (hXRC.comp hw) fun n₀ ↦ ?_
    have h1 := hY_int.tendsto_setIntegral_sup_neg_natCast Set.univ
    have h2 := (hX.integrable (w n₀)).tendsto_setIntegral_sup_neg_natCast Set.univ
    simp only [Measure.restrict_univ] at h1 h2
    refine le_of_tendsto_of_tendsto' h1 h2 fun k ↦ ?_
    have h3 := hZ_lim (-(k : ℝ)) Set.univ
    simp only [Measure.restrict_univ] at h3
    have h_ev : ∀ᶠ n in atTop, w n < w n₀ :=
      (hw.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (htw n₀))
    refine le_of_tendsto h3 ?_
    filter_upwards [h_ev] with n hn
    simpa using (hZ (-(k : ℝ))).setIntegral_le hn.le MeasurableSet.univ
  -- `Y` and `X t` are `𝓕 t`-measurable and have the same integrals on `𝓕 t`
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
    (fun _ _ _ ↦ hY_int.integrableOn) (fun _ _ _ ↦ (hX.integrable t).integrableOn)
    (fun A hA _ ↦ le_antisymm ?_ (h_le A hA))
    (adapted_rightContModifReal hXq t).stronglyMeasurable.aestronglyMeasurable
    (hX.stronglyAdapted t).aestronglyMeasurable
  have h1 := integral_add_compl (𝓕.le t A hA) hY_int
  have h2 := integral_add_compl (𝓕.le t A hA) (hX.integrable t)
  have h3 := h_le Aᶜ hA.compl
  linarith

/-- The càdlàg modification of a submartingale with respect to a right-continuous filtration is a
modification at the times where the expectation is right-continuous. -/
theorem _root_.MeasureTheory.Submartingale.cadlagModifReal_ae_eq [𝓕.IsRightContinuous]
    (hX : Submartingale X 𝓕 μ) (t : ι)
    (hXRC : Tendsto (fun s ↦ μ[X s]) (𝓝[>] t) (𝓝 (μ[X t]))) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  cadlagModifReal_ae_eq_of_rightContModifReal_ae_eq hX.isRealQuasimartingale
    (hX.rightContModifReal_ae_eq t hXRC)

end Modification

end ProbabilityTheory
