/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerSmoothPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerBoundedTruncation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotMonotoneMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ChartPartition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothCutoff
public import LeanPool.NonpluripolarProducts.Foundations.FiniteTuple

/-!
# Reducing the BEGZ patch-mass estimate to bounded potentials

`Pending.GlobalNonPluripolarKahler` carries the BEGZ uniform compact
truncation-mass estimate `patch_uniformCompactTruncationMass`, the one interface
on which `Pending.GlobalNonPluripolar` — itself sorry-free — depends, and it is
about *unbounded* `θ`-PSH potentials.  This module removes the unboundedness from it: the estimate
follows from the single statement

  `HasUniformBoundedGlobalMass η` — the total masses of the global mixed
  measures of *bounded* `η`-PSH tuples are bounded by one finite constant,

applied to finitely many enlarged backgrounds `η = θ + Cω`.  Mathematically
that constant is the cohomological intersection number `∫ η₁ ∧ ⋯ ∧ ηₙ`, and
proving the statement is the remaining integration-by-parts problem; nothing
here assumes it.

The reduction is the standard one, arranged so that no plurifine locality with
a nonconstant truncation level is needed.  Around a point of the patch domain
choose a chart-smooth `ψ i` agreeing with the patch potential `P.potential i`;
then

  `max (u i) (-k - ψ i)`

is a *global* bounded `(θ i + Cω)`-PSH potential whose corrected patch
potential is exactly `max (P.corrected i, -k) + Cσ`, the level-`k` truncation
of the patch data plus a fixed smooth PSH function.  Slot monotonicity absorbs
the `Cσ`, so the level-`k` truncation mass on a compact set is at most the
total mass of a bounded global measure, uniformly in `k`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.UniformBoundedGlobalMass

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open MixedNonPluripolar MixedMongeAmpere GlobalNonPluripolar BoundedGlobalProduct

noncomputable section

variable {n : ℕ}

/-! ### Locality of the uniform compact mass condition -/

/-- **The uniform compact truncation-mass condition is local.** A neighbourhood
of every point carrying one finite bound, uniform in the truncation level, is
enough: a compact subset is covered by finitely many of them. -/
theorem hasUniformCompactMixedTruncationMass_of_local {Ω : Opens (ComplexModel n)}
    {w : Fin n → ComplexModel n → EReal} (hw : ∀ i, PlurisubharmonicOn (w i) Ω)
    (hloc : ∀ z ∈ Ω, ∃ L : Set (ComplexModel n), L ∈ 𝓝 z ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k, mixedTruncationMeasure Ω w hw k L ≤ C) :
    HasUniformCompactMixedTruncationMass Ω w hw := by
  classical
  intro K hK hKΩ
  choose! L hL C hCtop hCbound using hloc
  obtain ⟨t, htK, htcover⟩ := hK.elim_nhds_subcover L fun z hz => hL z (hKΩ hz)
  refine ⟨∑ z ∈ t, C z, ?_, fun k => ?_⟩
  · exact ENNReal.sum_lt_top.mpr fun z hz => hCtop z (hKΩ (htK z hz))
  · calc mixedTruncationMeasure Ω w hw k K
        ≤ mixedTruncationMeasure Ω w hw k (⋃ z ∈ t, L z) := measure_mono htcover
      _ ≤ ∑ z ∈ t, mixedTruncationMeasure Ω w hw k (L z) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ z ∈ t, C z :=
          Finset.sum_le_sum fun z hz => hCbound z (hKΩ (htK z hz)) k

/-! ### Smooth PSD from smooth PSH -/

/-- A smooth plurisubharmonic function has positive semidefinite complex
Hessian: the quadratic form of the Hessian is the Levi form. -/
theorem isSmoothPsdOn_of_plurisubharmonicOn {U : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hp : PlurisubharmonicOn (fun z => (f z : EReal)) U) :
    BedfordTaylor.IsSmoothPsdOn U f := by
  refine ⟨hf, fun z hz => ?_⟩
  have hf2 : ContDiffAt ℝ 2 f z :=
    ((hf z hz).contDiffAt (U.isOpen.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (complexHessian_isHermitian hf2) fun x => ?_
  rw [complexHessian_dotProduct_mulVec_eq_leviForm hf2 x]
  exact_mod_cast leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hf hp hz _

/-! ### Adding one smooth PSD function to every slot -/

/-- The tuple with the smooth increment added in the slots of index below `m`. -/
def addPrefix (v : Fin n → ComplexModel n → ℝ) (s : ComplexModel n → ℝ) (m : ℕ) :
    Fin n → ComplexModel n → ℝ :=
  fun i => if (i : ℕ) < m then (fun z => v i z + s z) else v i

theorem addPrefix_zero (v : Fin n → ComplexModel n → ℝ) (s : ComplexModel n → ℝ) :
    addPrefix v s 0 = v :=
  FiniteTuple.replacePrefix_zero v (fun i z ↦ v i z + s z)

theorem addPrefix_full (v : Fin n → ComplexModel n → ℝ) (s : ComplexModel n → ℝ) :
    addPrefix v s n = fun i z => v i z + s z :=
  FiniteTuple.replacePrefix_full v (fun i z ↦ v i z + s z)

theorem addPrefix_succ (v : Fin n → ComplexModel n → ℝ) (s : ComplexModel n → ℝ)
    {m : ℕ} (hm : m < n) :
    addPrefix v s (m + 1) =
      Function.update (addPrefix v s m) ⟨m, hm⟩
        (fun z => addPrefix v s m ⟨m, hm⟩ z + s z) := by
  have hslot : addPrefix v s m ⟨m, hm⟩ = v ⟨m, hm⟩ := by simp [addPrefix]
  rw [hslot]
  exact FiniteTuple.replacePrefix_succ v (fun i z ↦ v i z + s z) hm

theorem isLocallyBoundedMixedPshOn_addPrefix {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} {s : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedMixedPshOn Ω v)
    (hvs : IsLocallyBoundedMixedPshOn Ω fun i z => v i z + s z) (m : ℕ) :
    IsLocallyBoundedMixedPshOn Ω (addPrefix v s m) := by
  intro i
  by_cases h : (i : ℕ) < m
  · simpa only [addPrefix, ite_eq_left h] using hvs i
  · simpa only [addPrefix, ite_eq_right h] using hv i

/-- **Slot monotonicity in every slot at once.** Adding one smooth positive
semidefinite function to each slot does not decrease the bounded mixed
Bedford–Taylor measure of a compact subset of the domain. -/
theorem canonicalMixedBedfordTaylorMeasure_le_add_smoothPsd {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} {s : ComplexModel n → ℝ}
    (hs : BedfordTaylor.IsSmoothPsdOn Ω s) (hv : IsLocallyBoundedMixedPshOn Ω v)
    (hvs : IsLocallyBoundedMixedPshOn Ω fun i z => v i z + s z)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (ComplexModel n))) :
    canonicalMixedBedfordTaylorMeasure Ω v hv K ≤
      canonicalMixedBedfordTaylorMeasure Ω (fun i z => v i z + s z) hvs K := by
  classical
  have h : ∀ m : ℕ, IsLocallyBoundedMixedPshOn Ω (addPrefix v s m) :=
    fun m => isLocallyBoundedMixedPshOn_addPrefix hv hvs m
  have key : ∀ m : ℕ, m ≤ n →
      canonicalMixedBedfordTaylorMeasure Ω (addPrefix v s 0) (h 0) K ≤
        canonicalMixedBedfordTaylorMeasure Ω (addPrefix v s m) (h m) K := by
    intro m
    induction m with
    | zero => intro _; exact le_rfl
    | succ m ih =>
      intro hm
      refine (ih (Nat.le_of_succ_le hm)).trans ?_
      have hmn : m < n := hm
      have hstep := BedfordTaylor.IsBTLimit.measure_le_add_smoothPsd
        (BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
          (canonicalMixedBedfordTaylorMeasure_spec Ω (addPrefix v s m) (h m)))
        (⟨m, hmn⟩ : Fin n) hs
        (ν := canonicalMixedBedfordTaylorMeasure Ω (addPrefix v s (m + 1)) (h (m + 1)))
        ?_ hK hKΩ
      · exact hstep
      · rw [← addPrefix_succ v s hmn]
        exact BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
          (canonicalMixedBedfordTaylorMeasure_spec Ω (addPrefix v s (m + 1)) (h (m + 1)))
  have h0 : canonicalMixedBedfordTaylorMeasure Ω (addPrefix v s 0) (h 0) =
      canonicalMixedBedfordTaylorMeasure Ω v hv :=
    canonicalMixedBedfordTaylorMeasure_eq (h 0)
      (IsLocalMixedBedfordTaylorMeasure.congr
        (canonicalMixedBedfordTaylorMeasure_spec Ω v hv)
        fun i z _ => by rw [addPrefix_zero])
  have hn : canonicalMixedBedfordTaylorMeasure Ω (addPrefix v s n) (h n) =
      canonicalMixedBedfordTaylorMeasure Ω (fun i z => v i z + s z) hvs :=
    canonicalMixedBedfordTaylorMeasure_eq (h n)
      (IsLocalMixedBedfordTaylorMeasure.congr
        (canonicalMixedBedfordTaylorMeasure_spec Ω (fun i z => v i z + s z) hvs)
        fun i z _ => by rw [addPrefix_full])
  have := key n le_rfl
  rwa [h0, hn] at this

/-! ### Extending a local potential to a chart-smooth function -/

/-- A smooth function on an open set, cut off by a test function supported
there, extends smoothly by zero. -/
theorem contDiff_cutoff_extend {Ω : Opens (ComplexModel n)} {β p : ComplexModel n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβΩ : tsupport β ⊆ (Ω : Set (ComplexModel n)))
    (hp : ContDiffOn ℝ ∞ p Ω) :
    ContDiff ℝ ∞ ((Ω : Set (ComplexModel n)).indicator fun z => β z * p z) := by
  have heq : (Ω : Set (ComplexModel n)).indicator (fun z => β z * p z) =
      fun z => β z * p z := by
    funext z
    by_cases hz : z ∈ (Ω : Set (ComplexModel n))
    · exact indicator_of_mem hz _
    · have hzs : z ∉ tsupport β := fun h ↦ hz (hβΩ h)
      rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hzs, zero_mul]
  rw [heq]
  simpa only [smul_eq_mul] using
    SmoothCutoff.contDiff_smul_of_tsupport_subset Ω.isOpen hβ hβΩ hp

/-- Local boundedness and plurisubharmonicity survive adding a smooth
plurisubharmonic function. -/
theorem isLocallyBoundedPshOn_add_smooth {Ω : Opens (ComplexModel n)}
    {f s : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f)
    (hsC : ContDiffOn ℝ ∞ s Ω) (hspsh : PlurisubharmonicOn (fun z => (s z : EReal)) Ω) :
    IsLocallyBoundedPshOn Ω fun z => f z + s z := by
  refine ⟨?_, ?_⟩
  · have h := hf.1.add hspsh
    have hfun : (fun z => ((f z + s z : ℝ) : EReal)) =
        fun z => ((f z : ℝ) : EReal) + ((s z : ℝ) : EReal) := by
      funext z
      exact EReal.coe_add _ _
    rw [hfun]
    exact h
  · intro z hz
    obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen z hz
    have hcb : Metric.closedBall z (r / 2) ⊆ (Ω : Set (ComplexModel n)) :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨D, hD⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
      (hsC.continuousOn.mono hcb)
    refine ⟨V ⊓ ⟨Metric.ball z (r / 2), Metric.isOpen_ball⟩,
      ⟨hzV, Metric.mem_ball_self (by linarith)⟩, fun w hw => hVΩ hw.1, C + D, fun w hw => ?_⟩
    have h1 : |f w| ≤ C := hC w hw.1
    have h2 : |s w| ≤ D := by
      simpa [Real.norm_eq_abs] using hD w (Metric.ball_subset_closedBall hw.2)
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Extending a patch potential to a chart-smooth function -/

/-- **A smooth local potential is the restriction of a chart-smooth function.**
On the half ball the patch potential is literally the chart expression of a
globally chart-smooth, globally bounded function on `M`. -/
theorem exists_chartSmooth_eq_on_ball {e : ComplexChart n M} {W : Opens (ComplexModel n)}
    (hW : (W : Set (ComplexModel n)) ⊆ e.val.target) {p : ComplexModel n → ℝ}
    (hp : ContDiffOn ℝ ∞ p W) {z₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball z₀ r ⊆ (W : Set (ComplexModel n))) :
    ∃ ψ : M → ℝ, ChartSmooth (n := n) ψ ∧ (∃ Q : ℝ, ∀ x, |ψ x| ≤ Q) ∧
      ∀ z ∈ Metric.ball z₀ (r / 2), ψ (e.val.symm z) = p z := by
  classical
  have hcb : Metric.closedBall z₀ (r / 2) ⊆ Metric.ball z₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := (⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ : Opens (ComplexModel n)))
    (K := Metric.closedBall z₀ (r / 2)) (isCompact_closedBall _ _) hcb
  set q : ComplexModel n → ℝ :=
    (W : Set (ComplexModel n)).indicator (fun z => (χ : ComplexModel n → ℝ) z * p z)
    with hq_def
  have hχt : tsupport (χ : ComplexModel n → ℝ) ⊆ Metric.ball z₀ r := χ.tsupport_subset
  have hq : ContDiff ℝ ∞ q := contDiff_cutoff_extend χ.contDiff (hχt.trans hball) hp
  have hqsupp : tsupport q ⊆ tsupport (χ : ComplexModel n → ℝ) := by
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro z hz
    by_contra hzc
    refine hz ?_
    by_cases hzW : z ∈ (W : Set (ComplexModel n))
    · rw [hq_def, indicator_of_mem hzW, image_eq_zero_of_notMem_tsupport hzc, zero_mul]
    · rw [hq_def, indicator_of_notMem hzW]
  have hqc : IsCompact (tsupport q) :=
    χ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport q) hqsupp
  have hqtar : tsupport q ⊆ e.val.target := hqsupp.trans ((hχt.trans hball).trans hW)
  refine ⟨ChartPartition.chartExtend e q,
    ChartPartition.chartSmooth_chartExtend e hq hqc hqtar, ?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := hqc.exists_bound_of_continuousOn hq.continuous.continuousOn
    refine ⟨max Q 0, fun x => ?_⟩
    by_cases hx : x ∈ e.val.source
    · rw [ChartPartition.chartExtend_of_mem hx]
      by_cases hz : e.val x ∈ tsupport q
      · exact le_trans (by simpa [Real.norm_eq_abs] using hQ _ hz) (le_max_left _ _)
      · rw [image_eq_zero_of_notMem_tsupport hz]
        simp
    · rw [ChartPartition.chartExtend_of_notMem hx]
      simp
  · intro z hz
    have hzball : z ∈ Metric.ball z₀ r :=
      Metric.ball_subset_ball (by linarith) hz
    have hzW : z ∈ (W : Set (ComplexModel n)) := hball hzball
    have hztar : z ∈ e.val.target := hW hzW
    have hsrc : e.val.symm z ∈ e.val.source := e.val.map_target hztar
    have hχz : (χ : ComplexModel n → ℝ) z = 1 :=
      hχ1.self_of_nhdsSet z (Metric.ball_subset_closedBall hz)
    rw [ChartPartition.chartExtend_of_mem hsrc, e.val.right_inv hztar, hq_def,
      indicator_of_mem hzW, hχz, one_mul]

/-! ### The reduction -/

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Uniform finiteness of the bounded global masses.**  One finite constant
bounds the total masses of the global mixed non-pluripolar measures of *all*
bounded `θ`-PSH tuples.  Mathematically that constant is the cohomological
intersection number of the backgrounds; proving the statement is the remaining
integration-by-parts problem and nothing here assumes it. -/
def HasUniformBoundedGlobalMass (θ : Fin n → ClosedRealOneOneForm n M) : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (v : Fin n → M → EReal)
    (hv : ∀ i, ThetaPlurisubharmonic (θ i).val (v i)),
      (∀ i, IsBoundedPotential (v i)) → globalMixedMeasure θ v hv univ ≤ C

variable {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

section NonemptyCase

variable [Nonempty M]

/-- **The local step of the reduction.**  Near every point of a patch domain the
level-`k` truncation masses of a compact neighbourhood are bounded by one finite
constant, uniformly in `k`. -/
theorem exists_local_uniform_truncation_bound (omega : KahlerBackground n M)
    (hmass : ∀ η : Fin n → ClosedRealOneOneForm n M, HasUniformBoundedGlobalMass η)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (P : Patch θ u)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ P.domain) :
    ∃ L : Set (ComplexModel n), L ∈ 𝓝 z₀ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k, mixedTruncationMeasure P.domain P.corrected P.plurisubharmonic k L ≤ C := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp P.domain.isOpen z₀ hz₀
  -- chart-smooth global extensions of the patch potentials
  have hex : ∀ i, ∃ ψ : M → ℝ, ChartSmooth (n := n) ψ ∧ (∃ Q : ℝ, ∀ x, |ψ x| ≤ Q) ∧
      ∀ z ∈ Metric.ball z₀ (r / 2), ψ (P.chart.val.symm z) = P.potential i z := fun i =>
    exists_chartSmooth_eq_on_ball P.domain_le_target (P.localPotential i).2.2.1 hr hball
  choose ψ hψsm hψbd hψeq using hex
  -- one constant making every enlarged background semipositive and every `-ψ i` quasi-PSH
  obtain ⟨C, hCpos, hCsemi, hCpsh⟩ :=
    SmoothDDCForm.exists_pos_thetaPlurisubharmonic_smooth omega θ (fun i x => -ψ i x)
      fun i e => (hψsm i e).neg
  have hCω : ((C • omega.form : ClosedRealOneOneForm n M)).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive hCpos.le
  -- a local potential of `C ω` near `z₀`
  obtain ⟨Wτ, τ, hz₀Wτ, hτ, hτpsh0⟩ :=
    (LocalPotentials.thetaPlurisubharmonic_zero_iff (C • omega.form)).mpr hCω
      P.chart z₀ (P.domain_le_target hz₀)
  have hτpsh : PlurisubharmonicOn (fun y => ((τ y : ℝ) : EReal)) Wτ := by
    have h := hτpsh0
    simpa [chartFunction] using h
  set V : Opens (ComplexModel n) :=
    ⟨Metric.ball z₀ (r / 2) ∩ Wτ, Metric.isOpen_ball.inter hτ.1⟩ with hVdef
  have hz₀V : z₀ ∈ V := ⟨Metric.mem_ball_self (by linarith), hz₀Wτ⟩
  have hVball : (V : Set (ComplexModel n)) ⊆ Metric.ball z₀ (r / 2) := fun z hz => hz.1
  have hVτ : (V : Set (ComplexModel n)) ⊆ Wτ := fun z hz => hz.2
  have hVdom : (V : Set (ComplexModel n)) ⊆ (P.domain : Set (ComplexModel n)) :=
    fun z hz => hball (Metric.ball_subset_ball (by linarith) hz.1)
  obtain ⟨ρ, hρ, hρball⟩ := Metric.isOpen_iff.mp V.isOpen z₀ hz₀V
  refine ⟨Metric.closedBall z₀ (ρ / 2), Metric.closedBall_mem_nhds z₀ (by linarith), ?_⟩
  set L : Set (ComplexModel n) := Metric.closedBall z₀ (ρ / 2) with hLdef
  have hLc : IsCompact L := isCompact_closedBall _ _
  have hLV : L ⊆ (V : Set (ComplexModel n)) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρball
  -- the enlarged backgrounds and the global bounded truncations
  set η : Fin n → ClosedRealOneOneForm n M := fun i => θ i + C • omega.form with hηdef
  set w : ℕ → Fin n → M → EReal :=
    fun k i x => Max.max (u i x) (((-(k : ℝ) - ψ i x : ℝ)) : EReal) with hwdef
  have hupsh : ∀ i, ThetaPlurisubharmonic (η i).val (u i) := fun i =>
    LocalPotentials.thetaPlurisubharmonic_add_of_semipositive (hu i) hCω
  have hgpsh : ∀ (k : ℕ) (i : Fin n),
      ThetaPlurisubharmonic (η i).val fun x => ((-(k : ℝ) - ψ i x : ℝ) : EReal) := by
    intro k i
    have h := FirstPass.GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const
      (hCpsh i) (k : ℝ)
    have hfun : (fun x : M => ((-(k : ℝ) - ψ i x : ℝ) : EReal)) =
        fun x : M => (((-ψ i x : ℝ)) : EReal) - ((k : ℝ) : EReal) := by
      funext x
      rw [← EReal.coe_sub]
      congr 1
      ring
    rw [hfun]
    exact h
  have hwpsh : ∀ k i, ThetaPlurisubharmonic (η i).val (w k i) := fun k i =>
    ThetaPlurisubharmonic.max (hupsh i) (hgpsh k i)
  have hwbd : ∀ k i, IsBoundedPotential (w k i) := by
    intro k i
    obtain ⟨Q, hQ⟩ := hψbd i
    obtain ⟨Cu, hCu⟩ := FirstPass.ThetaPlurisubharmonic.exists_global_upper_bound (hu i)
    refine ⟨-(k : ℝ) - Q, Max.max Cu (-(k : ℝ) + Q), fun x => ⟨?_, ?_⟩⟩
    · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (le_max_right (u i x) _)
      have h := abs_le.mp (hQ x)
      linarith [h.2]
    · refine max_le ((hCu x).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
        (EReal.coe_le_coe_iff.mpr ?_)
      have h := abs_le.mp (hQ x)
      have : -(k : ℝ) - ψ i x ≤ -(k : ℝ) + Q := by linarith [h.1]
      exact this.trans (le_max_right _ _)
  obtain ⟨Cm, hCmtop, hCm⟩ := hmass η
  refine ⟨Cm, hCmtop, fun k => ?_⟩
  -- the smooth PSH increment on `V`
  have hτV : IsSmoothLocalPotential (C • omega.form).val P.chart V τ :=
    hτ.mono V.isOpen hVτ
  have hτpshV : PlurisubharmonicOn (fun y => ((τ y : ℝ) : EReal)) V := hτpsh.mono hVτ
  have hτCV : ContDiffOn ℝ ∞ τ V := hτ.2.2.1.mono hVτ
  have hτpsd : BedfordTaylor.IsSmoothPsdOn V τ :=
    isSmoothPsdOn_of_plurisubharmonicOn hτCV hτpshV
  -- the sub-patch carrying the level-`k` data
  have hpot : ∀ i, IsSmoothLocalPotential (η i).val P.chart V
      fun z => P.potential i z + τ z := fun i =>
    FirstPass.LocalPotentials.localPotential_add
      ((P.localPotential i).mono V.isOpen hVdom) hτV
  have hkey : ∀ (i : Fin n), ∀ z ∈ (V : Set (ComplexModel n)),
      chartFunction (w k i) P.chart z + ((P.potential i z + τ z : ℝ) : EReal) =
        Max.max (P.corrected i z + ((τ z : ℝ) : EReal))
          ((((-(k : ℝ) + τ z : ℝ)) : EReal)) := by
    intro i z hz
    have hψz : ψ i (P.chart.val.symm z) = P.potential i z := hψeq i z (hVball hz)
    change Max.max (u i (P.chart.val.symm z))
        (((-(k : ℝ) - ψ i (P.chart.val.symm z) : ℝ)) : EReal) +
        ((P.potential i z + τ z : ℝ) : EReal) = _
    rw [hψz, ← max_add_add_right]
    congr 1
    · change chartFunction (u i) P.chart z + ((P.potential i z + τ z : ℝ) : EReal) = _
      rw [EReal.coe_add, ← add_assoc]
      rfl
    · rw [← EReal.coe_add]
      congr 1
      ring
  have hplur : ∀ i, PlurisubharmonicOn
      (fun z => chartFunction (w k i) P.chart z + ((P.potential i z + τ z : ℝ) : EReal)) V := by
    intro i
    have hcorr : PlurisubharmonicOn (fun z => P.corrected i z + ((τ z : ℝ) : EReal)) V :=
      ((P.plurisubharmonic i).mono hVdom).add hτpshV
    have hconstpsh : PlurisubharmonicOn
        (fun _ : ComplexModel n => (((-(k : ℝ) : ℝ)) : EReal)) V := fun x _ =>
      plurisubharmonicAt_const _ (EReal.coe_ne_top _) x
    have hconst : PlurisubharmonicOn (fun z => (((-(k : ℝ) + τ z : ℝ)) : EReal)) V := by
      have hfun : (fun z => (((-(k : ℝ) + τ z : ℝ)) : EReal)) =
          fun z => (((-(k : ℝ) : ℝ)) : EReal) + ((τ z : ℝ) : EReal) := by
        funext z
        exact EReal.coe_add _ _
      rw [hfun]
      exact hconstpsh.add hτpshV
    intro x hx
    refine ((hcorr.max hconst) x hx).congr ?_
    filter_upwards [V.isOpen.mem_nhds hx] with y hy
    exact (hkey i y hy).symm
  set Q : Patch η (w k) :=
    { chart := P.chart
      domain := V
      domain_le_target := hVdom.trans P.domain_le_target
      potential := fun i z => P.potential i z + τ z
      localPotential := hpot
      plurisubharmonic := hplur } with hQdef
  -- the corrected real tuple of the sub-patch is the level-`k` truncation plus `τ`
  have hcorrReal : ∀ i, EqOn (correctedReal Q i)
      (fun z => mixedTruncationReal P.corrected k i z + τ z) V := by
    intro i z hz
    have hne : P.corrected i z ≠ ⊤ := ((P.plurisubharmonic i) z (hVdom hz)).ne_top
    have hQz : Q.corrected i z =
        Max.max (P.corrected i z) ((((-(k : ℝ)) : ℝ) : EReal)) + ((τ z : ℝ) : EReal) := by
      have h := hkey i z hz
      rw [show Q.corrected i z =
        chartFunction (w k i) P.chart z + ((P.potential i z + τ z : ℝ) : EReal) from rfl, h,
        show (((-(k : ℝ) + τ z : ℝ)) : EReal) =
          (((-(k : ℝ) : ℝ)) : EReal) + ((τ z : ℝ) : EReal) from EReal.coe_add _ _]
      exact max_add_add_right _ _ _
    have hmaxne : Max.max (P.corrected i z) ((((-(k : ℝ)) : ℝ) : EReal)) ≠ ⊤ :=
      ne_of_lt (max_lt (lt_top_iff_ne_top.mpr hne) (EReal.coe_lt_top _))
    have hmaxnb : Max.max (P.corrected i z) ((((-(k : ℝ)) : ℝ) : EReal)) ≠ ⊥ :=
      ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (le_max_right _ _))
    change (Q.corrected i z).toReal = _
    rw [hQz, EReal.toReal_add hmaxne hmaxnb (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
    rfl
  -- the measure chain
  have hPV : ∀ i, PlurisubharmonicOn (P.corrected i) V := fun i =>
    (P.plurisubharmonic i).mono hVdom
  have htruncV : IsLocallyBoundedMixedPshOn V (mixedTruncationReal P.corrected k) :=
    mixedTruncationReal_isLocallyBounded hPV k
  have hsum : IsLocallyBoundedMixedPshOn V
      (fun i z => mixedTruncationReal P.corrected k i z + τ z) := fun i =>
    isLocallyBoundedPshOn_add_smooth (htruncV i) hτCV hτpshV
  have hQbd : IsLocallyBoundedMixedPshOn V (correctedReal Q) :=
    correctedReal_isLocallyBoundedMixedPshOn (hwbd k) Q
  have hstep1 : mixedTruncationMeasure P.domain P.corrected P.plurisubharmonic k L =
      mixedTruncationMeasure V P.corrected hPV k L := by
    have hloc := mixedTruncationMeasure_open_locality (Ω := P.domain) (U := V)
      (u := P.corrected) (v := P.corrected) hVdom P.plurisubharmonic hPV
      (fun _ _ _ => rfl) k
    have h2 : mixedTruncationMeasure V P.corrected hPV k L =
        (mixedTruncationMeasure P.domain P.corrected P.plurisubharmonic k).restrict
          (V : Set (ComplexModel n)) L := by rw [hloc]
    rw [h2, Measure.restrict_apply hLc.measurableSet]
    congr 1
    exact (inter_eq_self_of_subset_left hLV).symm
  have hstep2 : mixedTruncationMeasure V P.corrected hPV k L ≤
      canonicalMixedBedfordTaylorMeasure V (mixedTruncationReal P.corrected k) htruncV L := by
    exact Measure.le_iff'.mp Measure.restrict_le_self _
  have hstep3 := canonicalMixedBedfordTaylorMeasure_le_add_smoothPsd hτpsd htruncV hsum hLc hLV
  have hstep4 : canonicalMixedBedfordTaylorMeasure V
      (fun i z => mixedTruncationReal P.corrected k i z + τ z) hsum =
      canonicalMixedBedfordTaylorMeasure V (correctedReal Q) hQbd :=
    canonicalMixedBedfordTaylorMeasure_eq hsum
      (IsLocalMixedBedfordTaylorMeasure.congr
        (canonicalMixedBedfordTaylorMeasure_spec V (correctedReal Q) hQbd)
        fun i => hcorrReal i)
  have hstep5 : canonicalMixedBedfordTaylorMeasure V (correctedReal Q) hQbd L ≤
      globalMixedMeasure η (w k) (hwpsh k) univ := by
    have hpush := globalMixedMeasure_restrict_patch_eq_canonical (hwpsh k) (hwbd k) Q
    have hsub : L ⊆ (V : Set (ComplexModel n)) ∩
        P.chart.val.symm ⁻¹' (P.chart.val.symm '' L) := fun z hz =>
      ⟨hLV hz, mem_image_of_mem _ hz⟩
    calc canonicalMixedBedfordTaylorMeasure V (correctedReal Q) hQbd L
        ≤ canonicalMixedBedfordTaylorMeasure V (correctedReal Q) hQbd
            ((V : Set (ComplexModel n)) ∩
              P.chart.val.symm ⁻¹' (P.chart.val.symm '' L)) := measure_mono hsub
      _ = Q.pushMeasure (canonicalMixedBedfordTaylorMeasure V (correctedReal Q) hQbd)
            (P.chart.val.symm '' L) := (Patch.pushMeasure_apply Q _ _).symm
      _ = (globalMixedMeasure η (w k) (hwpsh k)).restrict (Q.source : Set M)
            (P.chart.val.symm '' L) := by rw [hpush]
      _ ≤ globalMixedMeasure η (w k) (hwpsh k) univ := by
          refine le_trans (Measure.le_iff'.mp Measure.restrict_le_self _) ?_
          exact measure_mono (subset_univ _)
  calc mixedTruncationMeasure P.domain P.corrected P.plurisubharmonic k L
      = mixedTruncationMeasure V P.corrected hPV k L := hstep1
    _ ≤ canonicalMixedBedfordTaylorMeasure V (mixedTruncationReal P.corrected k) htruncV L :=
        hstep2
    _ ≤ canonicalMixedBedfordTaylorMeasure V
          (fun i z => mixedTruncationReal P.corrected k i z + τ z) hsum L := hstep3
    _ = canonicalMixedBedfordTaylorMeasure V (correctedReal Q) hQbd L := by rw [hstep4]
    _ ≤ globalMixedMeasure η (w k) (hwpsh k) univ := hstep5
    _ ≤ Cm := hCm (w k) (hwpsh k) (hwbd k)

end NonemptyCase

/-- **The BEGZ patch-mass condition, reduced to bounded potentials.**  Granting
that the total masses of the bounded global mixed measures are uniformly finite
in every tuple of backgrounds, the uniform compact truncation-mass condition
holds for every raw theta-PSH tuple on a compact Kähler manifold. -/
theorem hasPatchTruncationMass_of_uniformBoundedGlobalMass (omega : KahlerBackground n M)
    (hmass : ∀ η : Fin n → ClosedRealOneOneForm n M, HasUniformBoundedGlobalMass η)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    HasPatchTruncationMass θ u := by
  intro P
  refine hasUniformCompactMixedTruncationMass_of_local P.plurisubharmonic fun z hz => ?_
  cases isEmpty_or_nonempty M with
  | inl hM => exact (hM.false (P.chart.val.symm z)).elim
  | inr hM => exact exists_local_uniform_truncation_bound omega hmass hu P hz

end

end SGPT.Foundations.Analysis.Pending.UniformBoundedGlobalMass
