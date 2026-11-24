/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IncreasingPshBallSubmean

/-!
# Bounded potentials do not charge negligible sets (step C4b of I-0510)

Let `v_j` be an increasing sequence of uniformly bounded `θ`-PSH potentials on a compact complex
manifold, `V = sup_j v_j` and `V^*` its upper semicontinuous regularization (assumed `θ`-PSH).
Then for every bounded `θ`-PSH potential `w`, the non-pluripolar measure `(θ + ddᶜw)ⁿ` does not
charge the *negligible set* `{V < V^*}` (`diagonalPotentialMeasure_negligible_eq_zero`).

This is the measure half of Bedford--Taylor's theorem "negligible sets are pluripolar"
(Bedford--Taylor 1982, Thm 7.1; Błocki's lecture notes, §2.2).  In a chart the measure is the
Bedford--Taylor measure `μ` of the corrected potential of `w`, and the corrected potentials of
the `v_j` form an increasing approximation of that of `V^*` (they converge to it Lebesgue-almost
everywhere: `ae_uscRegularization_iSup_eq_on_ball`).  The Bedford--Taylor convergence theorem
for increasing sequences with a fixed measure and increasing weights
(`BedfordTaylor.incWClaim_all`, Cegrell's proof) gives `∫ χ (VTilde^* - vTilde_k) dμ → 0`.
Markov's inequality gives `μ{vTilde_k + δ ≤ VTilde^* ∀ k} = 0` (`measure_inter_gap_eq_zero`).
A finite chart cover finishes the proof.
-/

@[expose] public section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.NegligibleSetNotCharged

noncomputable section

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {n : ℕ}

/-! ## The local statement -/

/-- **Local form.** If `vTilde_k` increasingly approximates the locally bounded psh `VTilde` on `D`
and `μ` is the Bedford--Taylor measure of a locally bounded psh `wTilde` on `D`, then for every
compact `K ⊆ D` and `δ > 0`, `μ (K ∩ {z | ∀ k, vTilde_k z + δ ≤ VTilde z}) = 0`. -/
theorem measure_inter_gap_eq_zero {D : TopologicalSpace.Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w) {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit D (fun _ => w) μ) {V : ComplexModel n → ℝ} (hV : IsLocallyBoundedPshOn D V)
    {v : ℕ → ComplexModel n → ℝ} (hv : IsIncApprox D V v) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKD : K ⊆ D) {δ : ℝ} (hδ : 0 < δ) :
    μ (K ∩ {z | ∀ k, v k z + δ ≤ V z}) = 0 := by
  classical
  obtain ⟨χ, hχK, hχc, hχD, hχ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK D.isOpen hKD
  have hχcs : HasCompactSupport χ := hχc
  have hμf : ∀ K', IsCompact K' → K' ⊆ D → μ K' < ⊤ := fun K' hK' hK'D => hμ.2.1 K' hK' hK'D
  have hadm : IsIncAdmissible n D (fun _ => w) (fun _ _ => w) :=
    ⟨fun _ => hw, fun _ => isIncApprox_const hw, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  have hconv := incWClaim_all D (fun _ => w) (fun _ _ => w) (fun _ => μ) μ hadm (fun _ => hμ) hμ
    V v hV hv χ χ.continuous hχcs hχD
  -- the gap integrals tend to `0`
  have hint : ∀ f : ComplexModel n → ℝ, IsLocallyBoundedPshOn D f →
      Integrable (fun z => χ z * f z) μ := fun f hf =>
    integrable_test_mul_of_isLocallyBoundedPshOn hf hμf χ.continuous hχcs hχD
  have hgap : Tendsto (fun k => ∫ z, χ z * (V z - v k z) ∂μ) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∫ z, χ z * V z ∂μ)).sub hconv
    rw [sub_self] at h
    refine h.congr fun k => ?_
    rw [← integral_sub (hint V hV) (hint (v k) (hv.1 k))]
    congr 1
    funext z
    ring
  -- Markov's inequality, uniformly in `k`
  have hnonneg : ∀ k z, 0 ≤ χ z * (V z - v k z) := by
    intro k z
    by_cases hz : z ∈ (D : Set (ComplexModel n))
    · exact mul_nonneg (hχ01 z).1 (sub_nonneg.mpr (hv.2.2.1 k z hz))
    · have : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hχD h)
      rw [this, zero_mul]
  have hsub : ∀ k, K ∩ {z | ∀ k, v k z + δ ≤ V z} ⊆ {z | δ ≤ χ z * (V z - v k z)} := by
    intro k z hz
    have h1 : χ z = 1 := hχK hz.1
    change δ ≤ χ z * (V z - v k z)
    rw [h1, one_mul]
    linarith [hz.2 k]
  have hbound : ∀ k, δ * (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal ≤
      ∫ z, χ z * (V z - v k z) ∂μ := by
    intro k
    have hI : Integrable (fun z => χ z * (V z - v k z)) μ := by
      have := (hint V hV).sub (hint (v k) (hv.1 k))
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply]
      ring
    have hfinK : μ {z | δ ≤ χ z * (V z - v k z)} ≠ ⊤ := by
      refine ne_top_of_le_ne_top (hμf _ hχc hχD).ne (measure_mono fun z hz => ?_)
      by_contra hzt
      have : χ z = 0 := image_eq_zero_of_notMem_tsupport hzt
      have hz' : δ ≤ χ z * (V z - v k z) := hz
      rw [this, zero_mul] at hz'
      linarith
    calc δ * (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal
        ≤ δ * (μ {z | δ ≤ χ z * (V z - v k z)}).toReal := by
          gcongr
          exact hsub k
      _ ≤ ∫ z, χ z * (V z - v k z) ∂μ :=
          mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (hnonneg k)) hI δ
  have hle0 : δ * (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal ≤ 0 :=
    ge_of_tendsto hgap (Eventually.of_forall hbound)
  have htoReal : (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal = 0 := by
    refine le_antisymm ?_ ENNReal.toReal_nonneg
    by_contra h
    push Not at h
    have := mul_pos hδ h
    linarith
  have hfin : μ (K ∩ {z | ∀ k, v k z + δ ≤ V z}) ≠ ⊤ :=
    ne_top_of_le_ne_top (hμf K hK hKD).ne (measure_mono inter_subset_left)
  exact (ENNReal.toReal_eq_zero_iff _).mp htoReal |>.resolve_right hfin

/-! ## The global statement -/

/-- Adding a real constant commutes with suprema in `EReal`. -/
theorem iSup_add_coe {ι : Sort*} (a : ι → EReal) (r : ℝ) :
    (⨆ i, a i) + (r : EReal) = ⨆ i, (a i + (r : EReal)) := by
  refine Monotone.map_iSup_of_continuousAt (f := fun x : EReal => x + (r : EReal)) ?_
    (fun x y h => add_le_add h le_rfl) (by simp)
  exact ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2)
    (f := fun x : EReal => (x, (r : EReal))) (x := ⨆ i, a i)
    (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot r)) (Or.inr (EReal.coe_ne_top r)))
    (continuous_id.prodMk continuous_const).continuousAt

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

open BoundedGlobalProduct ThetaCapacityChart ThetaCapacityChartLocal PatchLocalBoundedMeasure

/-- **Bounded potentials do not charge negligible sets.**  For an increasing sequence of
uniformly bounded `θ`-PSH potentials `v_j` whose regularized supremum `V^*` is `θ`-PSH, and every
bounded `θ`-PSH potential `w`, `(θ + ddᶜw)ⁿ {sup_j v_j < V^*} = 0`. -/
theorem diagonalPotentialMeasure_negligible_eq_zero {θ : ClosedRealOneOneForm n M}
    {w : M → EReal} (hw : IsThetaPshPotential θ.val w) (hwb : IsBoundedPotential w)
    {v : ℕ → M → EReal} (hv : ∀ j, IsThetaPshPotential θ.val (v j)) {a b : ℝ}
    (hvb : ∀ j x, (a : EReal) ≤ v j x ∧ v j x ≤ (b : EReal)) (hmono : Monotone v)
    (hV : IsThetaPshPotential θ.val (uscRegularization (⨆ j, v j))) :
    diagonalPotentialMeasure θ w hw
      {x | (⨆ j, v j) x < uscRegularization (⨆ j, v j) x} = 0 := by
  classical
  set Vs : M → EReal := uscRegularization (⨆ j, v j) with hVsdef
  set N : Set M := {x | (⨆ j, v j) x < Vs x} with hNdef
  have hsupv : ∀ x, (⨆ j, v j) x = ⨆ j, v j x := fun x => iSup_apply
  have hVle : ∀ x, Vs x ≤ (b : EReal) := fun x =>
    uscRegularization_le (g := fun _ => (b : EReal)) upperSemicontinuous_const
      (fun y => by rw [hsupv]; exact iSup_le fun j => (hvb j y).2) x
  have hle_sup : ∀ j x, v j x ≤ (⨆ j, v j) x := fun j x => by
    rw [hsupv]; exact le_iSup (fun j => v j x) j
  have hsup_le : ∀ x, (⨆ j, v j) x ≤ Vs x := fun x => le_uscRegularization _ x
  have hVge : ∀ x, (a : EReal) ≤ Vs x := fun x =>
    (hvb 0 x).1.trans ((hle_sup 0 x).trans (hsup_le x))
  obtain ⟨aw, bw, hwbd⟩ := hwb
  have hloc : ∀ x : M, ∃ Nx : Set M, IsOpen Nx ∧ x ∈ Nx ∧
      diagonalPotentialMeasure θ w hw (N ∩ Nx) = 0 := by
    intro x
    set e : ComplexChart n M := complexChartAt (n := n) x with he
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    set z₀ : ComplexModel n := e.val x with hz₀def
    have hz : z₀ ∈ e.val.target := e.val.map_source hx
    obtain ⟨W, ρ, hz₀W, hρ, -⟩ := hw.1 e z₀ hz
    have hopen : IsOpen (W ∩ e.val.target) := hρ.1.inter e.val.open_target
    obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hopen z₀ ⟨hz₀W, hz⟩
    set r : ℝ := r₀ / 4 with hrdef
    have hr : 0 < r := by positivity
    have h2 : closedBall z₀ (2 * r) ⊆ W ∩ e.val.target :=
      (closedBall_subset_ball (by linarith)).trans hball
    set D : TopologicalSpace.Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩ with hDdef
    have hDsub : (D : Set (ComplexModel n)) ⊆ closedBall z₀ (2 * r) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    have hD : (D : Set (ComplexModel n)) ⊆ e.val.target := fun y hy => (h2 (hDsub hy)).2
    have hρD : IsSmoothLocalPotential θ.val e D ρ :=
      hρ.mono isOpen_ball fun y hy => (h2 (hDsub hy)).1
    obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall z₀ (2 * r)).exists_bound_of_continuousOn
      (hρ.2.2.1.continuousOn.mono fun y hy => (h2 hy).1)
    set L : ℝ := max L₀ 0 with hLdef
    have hL : ∀ y ∈ closedBall z₀ (2 * r), |ρ y| ≤ L := fun y hy =>
      (hL₀ y hy).trans (le_max_left _ _)
    have hLD : ∀ y ∈ (D : Set (ComplexModel n)), |ρ y| ≤ L := fun y hy => hL y (hDsub hy)
    have hρcont : ∀ y ∈ (D : Set (ComplexModel n)), ContinuousAt ρ y := fun y hy =>
      (hρ.2.2.1.continuousOn.continuousAt (hρ.1.mem_nhds (h2 (hDsub hy)).1))
    -- the corrected chart functions
    set wt := correctedChartReal w e ρ with hwtdef
    have hwt : IsLocallyBoundedPshOn D wt :=
      correctedChartReal_isLocallyBoundedPshOn_of_boundedOn hw.1 hρD
        (fun y _ => hwbd (e.val.symm y)) hLD
    set vt : ℕ → ComplexModel n → ℝ := fun k => correctedChartReal (v k) e ρ with hvtdef
    have hvt : ∀ k, IsLocallyBoundedPshOn D (vt k) := fun k =>
      correctedChartReal_isLocallyBoundedPshOn_of_boundedOn (hv k).1 hρD
        (fun y _ => hvb k (e.val.symm y)) hLD
    set Vt := correctedChartReal Vs e ρ with hVtdef
    have hVt : IsLocallyBoundedPshOn D Vt :=
      correctedChartReal_isLocallyBoundedPshOn_of_boundedOn hV.1 hρD
        (fun y _ => ⟨hVge (e.val.symm y), hVle (e.val.symm y)⟩) hLD
    -- finiteness of the values
    have hvfin : ∀ k y, v k y ≠ ⊤ ∧ v k y ≠ ⊥ := fun k y =>
      ⟨ne_top_of_le_ne_top (EReal.coe_ne_top b) (hvb k y).2,
        ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hvb k y).1⟩
    have hVfin : ∀ y, Vs y ≠ ⊤ ∧ Vs y ≠ ⊥ := fun y =>
      ⟨ne_top_of_le_ne_top (EReal.coe_ne_top b) (hVle y),
        ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hVge y)⟩
    -- the increasing approximation
    have hae : ∀ᵐ z ∂(volume : Measure (ComplexModel n)), z ∈ (D : Set (ComplexModel n)) →
        Tendsto (fun k => vt k z) atTop (𝓝 (Vt z)) := by
      set c : ℕ → ComplexModel n → EReal :=
        fun k y => chartFunction (v k) e y + (ρ y : EReal) with hcdef
      have hcpsh : ∀ k, DiscPshOn (c k) (ball z₀ (2 * r)) := fun k =>
        PlurisubharmonicOn.discPshOn
          ((ThetaPlurisubharmonic.corrected_plurisubharmonicOn (hv k).1 e hρ).mono
            fun y hy => (h2 (ball_subset_closedBall hy)).1)
      have hcmono : ∀ y ∈ ball z₀ (2 * r), Monotone fun k => c k y := fun y _ k l hkl =>
        add_le_add (hmono hkl _) le_rfl
      have hcC : ∀ k, ∀ y ∈ ball z₀ (2 * r), c k y ≤ ((b + L : ℝ) : EReal) := by
        intro k y hy
        rw [EReal.coe_add]
        exact add_le_add (hvb k (e.val.symm y)).2
          (EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hL y (ball_subset_closedBall hy))))
      have h := SGPT.Foundations.Analysis.ae_uscRegularization_iSup_eq_on_ball hcpsh hcmono
        volume z₀ (S := 2 * r) (by positivity) subset_rfl hcC
      filter_upwards [h] with z hz hzD
      have hzball : z ∈ ball z₀ (2 * r / 2) := by
        rw [mul_div_cancel_left₀ r two_ne_zero]; exact hzD
      have heq := hz hzball
      have hfun : (fun y => ⨆ k, c k y) =
          fun y => chartFunction (⨆ j, v j) e y + (ρ y : EReal) := by
        funext y
        simp only [hcdef, chartFunction, hsupv]
        exact (iSup_add_coe _ _).symm
      rw [hfun, uscRegularization_add_coe_continuousAt_apply _ (hρcont z hzD),
        uscRegularization_chartFunction_apply _ e (hD hzD)] at heq
      have htend : Tendsto (fun k => c k z) atTop (𝓝 (⨆ k, c k z)) :=
        tendsto_atTop_iSup (hcmono z (ball_subset_ball (by linarith) hzD))
      rw [← heq] at htend
      have hlimfin : chartFunction Vs e z + (ρ z : EReal) ≠ ⊤ ∧
          chartFunction Vs e z + (ρ z : EReal) ≠ ⊥ := by
        obtain ⟨h1, h2'⟩ := hVfin (e.val.symm z)
        exact ⟨EReal.add_ne_top h1 (EReal.coe_ne_top _),
          EReal.add_ne_bot_iff.mpr ⟨h2', EReal.coe_ne_bot _⟩⟩
      have hreal := (EReal.tendsto_toReal hlimfin.1 hlimfin.2).comp htend
      have hVtz : (chartFunction Vs e z + (ρ z : EReal)).toReal = Vt z := by
        obtain ⟨h1, h2'⟩ := hVfin (e.val.symm z)
        simp only [chartFunction]
        rw [EReal.toReal_add h1 h2' (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
        rfl
      rw [hVtz] at hreal
      refine hreal.congr fun k => ?_
      obtain ⟨h1, h2'⟩ := hvfin k (e.val.symm z)
      simp only [Function.comp_apply, hcdef, chartFunction]
      rw [EReal.toReal_add h1 h2' (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
      rfl
    have hinc : IsIncApprox D Vt vt := by
      refine ⟨hvt, fun z _ k l hkl => ?_, fun k z _ => ?_, hae⟩
      · obtain ⟨h1, h2'⟩ := hvfin k (e.val.symm z)
        obtain ⟨h3, h4⟩ := hvfin l (e.val.symm z)
        change (v k (e.val.symm z)).toReal + ρ z ≤ (v l (e.val.symm z)).toReal + ρ z
        exact add_le_add (EReal.toReal_le_toReal (hmono hkl _) h2' h3) le_rfl
      · obtain ⟨h1, h2'⟩ := hvfin k (e.val.symm z)
        obtain ⟨h3, h4⟩ := hVfin (e.val.symm z)
        change (v k (e.val.symm z)).toReal + ρ z ≤ (Vs (e.val.symm z)).toReal + ρ z
        exact add_le_add (EReal.toReal_le_toReal
          ((hle_sup k _).trans (hsup_le _)) h2' h3) le_rfl
    -- the local measure
    have hμ := isBTLimit_canonicalBedfordTaylorMeasure hwt
    have hKD : closedBall z₀ (r / 2) ⊆ (D : Set (ComplexModel n)) :=
      closedBall_subset_ball (by linarith)
    have hzero : ∀ m : ℕ, Pending.MongeAmpere.canonicalBedfordTaylorMeasure D wt hwt
        (closedBall z₀ (r / 2) ∩ {z | ∀ k, vt k z + 1 / ((m : ℝ) + 1) ≤ Vt z}) = 0 :=
      fun m => measure_inter_gap_eq_zero hwt hμ hVt hinc (isCompact_closedBall _ _) hKD
        (by positivity)
    refine ⟨e.val.source ∩ e.val ⁻¹' ball z₀ (r / 2), e.val.isOpen_inter_preimage isOpen_ball,
      ⟨hx, mem_ball_self (by positivity)⟩, ?_⟩
    have hE : N ∩ (e.val.source ∩ e.val ⁻¹' ball z₀ (r / 2)) ⊆
        ((diagSlotChart θ e D hD ρ hρD).source : Set M) := fun y hy =>
      ⟨hy.2.1, ball_subset_ball (by linarith) hy.2.2⟩
    have hb : IsBoundedPotentialOn w ((diagSlotChart θ e D hD ρ hρD).source : Set M) :=
      ⟨aw, bw, fun y _ => hwbd y⟩
    rw [DiagonalMeasureDecreasingPortmanteau.diagonalPotentialMeasure_eq_canonical hw hb hwt hE]
    refine measure_mono_null ?_ (measure_iUnion_null hzero)
    rintro _ ⟨y, ⟨hyN, hys, hyb⟩, rfl⟩
    have hyN' : (⨆ j, v j) y < Vs y := hyN
    have hsfin : (⨆ j, v j) y ≠ ⊤ ∧ (⨆ j, v j) y ≠ ⊥ :=
      ⟨ne_top_of_le_ne_top (hVfin y).1 (hsup_le y),
        ne_bot_of_le_ne_bot (hvfin 0 y).2 (hle_sup 0 y)⟩
    have hlt : ((⨆ j, v j) y).toReal < (Vs y).toReal := by
      have h := hyN'
      rw [← EReal.coe_toReal hsfin.1 hsfin.2, ← EReal.coe_toReal (hVfin y).1 (hVfin y).2] at h
      exact EReal.coe_lt_coe_iff.mp h
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    refine mem_iUnion.mpr ⟨m, ball_subset_closedBall hyb, fun k => ?_⟩
    have hinv : e.val.symm (e.val y) = y := e.val.left_inv hys
    change (v k (e.val.symm (e.val y))).toReal + ρ (e.val y) + 1 / ((m : ℝ) + 1) ≤
      (Vs (e.val.symm (e.val y))).toReal + ρ (e.val y)
    rw [hinv]
    have hk : (v k y).toReal ≤ ((⨆ j, v j) y).toReal :=
      EReal.toReal_le_toReal (hle_sup k y) (hvfin k y).2 hsfin.1
    linarith
  choose Nx hNo hxN hN0 using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover Nx hNo
    (fun x _ => mem_iUnion.mpr ⟨x, hxN x⟩)
  refine measure_mono_null (fun y hy => ?_)
    ((measure_biUnion_null_iff t.countable_toSet).mpr fun x _ => hN0 x)
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  exact mem_iUnion₂.mpr ⟨x, hxt, hy, hyx⟩

end

end SGPT.Foundations.Analysis.Pending.NegligibleSetNotCharged
