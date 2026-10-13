/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEventAtBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.AdjointInjection
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.GoodEventAggregation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.HomogenizationInput
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.WaveSizesZeroth

/-!
# LocalizationAssemblyCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the per-`(l,z)` core of the localization assembly

It carries the two scalar inputs named (i) and the per-`(l,z)` composed switch
endpoints they close; the `l`-sum, the `z`-average and the five-term display
live in the sibling `Provider/Localization/LocalizationAssembly.lean`.

## What is here

1. **The loading ball of the breakdown legs** (§1).  The proved
   `Breakdown.breakdownLegA_le_of_paired_bound` says that a bound on `J(R,
   σ^{-1/2}v, σ^{1/2}v; a)` over the ball `|v|² ≤ 2` bounds the leg.  The
   converse is what the assembly needs — the leg is an admissible *majorant* of
   every paired loading in that ball — and it holds because the primal frame
   map `e ↦ e₁ - e₂` maps the doubled unit sphere ONTO the ball
   (`exists_frameLegAVec_eq`).  This is the exact statement that lets the
   deep-response comparator of the printed first two terms be the SAME carrier
   `breakdownLegA / breakdownLegB` that the printed left-hand side uses, at
   `(a_{l-h}, σ_{l-h})` instead of `(a_m, σ_m)`.

2. **The scalar input** (§2) (i):

3. For one grid cube `R` of the printed tiling, on one probability-one event
   and uniformly in the cube,

   ```text
   legA(R; a_m, σ_m)
     ≤ 24 · legA(R; a_{l-h}, σ_{l-h})
       + 8·Cinj(Ccg) · c⋆⁻¹ γ · waveSizeW2(m,h,R)²
       + Cs·48Ccg · switchRemainder γ E h j
   ```

   with `l = R.scale = m - j`.  The three summands are the printed first, third
   and fifth terms of `e.localization.mathcalE.estimate` before the
   `z`-average and the `l`-sum.

## Fidelity and constants

* The deep comparator of the printed display is `max_{|e|=1} J(z + □_l, ·, ·;
  a_{l-h})`; the carrier here is `breakdownLegA R (a_{l-h}) (isotropic
  σ_{l-h})`, which is twice that maximum by quadratic homogeneity — exactly the
  convention the proved `e.mathcal.E.breakdown` already uses on the printed
  left-hand side.  In the per-`(l,z)` display of §3 the same doubling
  does sit on both sides; in the sibling module's display it does NOT, because
  there the left-hand side is `𝓔²`, which carries no doubling, and
  `legScaleAverage` is degree-one homogeneous.  Its provenance is `8` (the
  proved `SwitchNormalization.breakdownLeg{A,B}_le_of_shom_switch` at the `ρ =
  4` window) times `3` (the printed injection factor).  Nothing downstream is
  sharp in it (`e.what.homogenization.gives` absorbs it into its own `C`).
* No `min`/`3^{2γΔ}` reshaping happens here: the remainder is emitted through
  the proved cross-file seam
  `AggregationRemainder.switchRemainder_eq_of_int_gap` ((iii)), never
  re-derived.

## The scale gate on `m0` (-bin statement change)

The landmark premise carried by every declaration below is `mStarStar M < m0`,
**not** the printed `m0 in (mstar, infty) cap Z`.  Nothing else moved: the
premise is forwarded verbatim to the proved producers consumed here, no proof
step here consumes it, and no frozen statement changes.
-/

namespace Algsuperdiff.Section3.Provider.Localization

open _root_.MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. The loading ball of the breakdown legs

`Breakdown.frameLegAVec e = e₁ - e₂` and `Breakdown.frameLegBVec e = e₁ + e₂`
send the doubled unit sphere `|e| = 1` into the loading ball `|v|² ≤ 2` (the
proved `vecNormSq_frameLeg{A,B}Vec_le`).  They are also ONTO it: given `v` with
`|v|² ≤ 2`, the pair `(v/2 + u, ∓ v/2 + u)` with `|u|² = (2-|v|²)/4` is a
doubled unit direction with the prescribed image, by the parallelogram
identity.  A single coordinate spike supplies `u`, which is where `[NeZero d]`
enters. -/

/-- **The primal frame map is onto the loading ball.**  Every `v` of squared
length at most `2` is the primal frame combination `e₁ - e₂` of a doubled unit
direction. -/
theorem exists_frameLegAVec_eq [NeZero d] {v : Vec d} (hv : vecNormSq v ≤ 2) :
    ∃ e : FullBlockVec d, Ch02.fullBlockVecNormSq e = 1 ∧ frameLegAVec e = v := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set t : ℝ := Real.sqrt ((2 - vecNormSq v) / 4) with ht
  set u : Vec d := Pi.single ⟨0, hd⟩ t with hu
  have ht2 : t ^ 2 = (2 - vecNormSq v) / 4 := by
    rw [ht, Real.sq_sqrt (by linarith)]
  have hun : vecNormSq u = t ^ 2 := by
    simp [hu, vecNormSq, vecDot, Pi.single_apply, Finset.sum_ite_eq', pow_two]
  refine ⟨Sum.elim (fun i => (2 : ℝ)⁻¹ * v i + u i)
    (fun i => -((2 : ℝ)⁻¹ * v i) + u i), ?_, ?_⟩
  · rw [ErrorComparison.fullBlockVecNormSq_eq_add]
    have h1 : (fun i : Fin d => (Sum.elim (fun i => (2 : ℝ)⁻¹ * v i + u i)
        (fun i => -((2 : ℝ)⁻¹ * v i) + u i) : FullBlockVec d) (Sum.inl i)) =
        fun i => (2 : ℝ)⁻¹ * v i + u i := rfl
    have h2 : (fun i : Fin d => (Sum.elim (fun i => (2 : ℝ)⁻¹ * v i + u i)
        (fun i => -((2 : ℝ)⁻¹ * v i) + u i) : FullBlockVec d) (Sum.inr i)) =
        fun i => -((2 : ℝ)⁻¹ * v i) + u i := rfl
    rw [h1, h2]
    have hexp : ∀ i : Fin d,
        ((2 : ℝ)⁻¹ * v i + u i) * ((2 : ℝ)⁻¹ * v i + u i) +
            (-((2 : ℝ)⁻¹ * v i) + u i) * (-((2 : ℝ)⁻¹ * v i) + u i) =
          (2 : ℝ)⁻¹ * (v i * v i) + 2 * (u i * u i) := by
      intro i; ring
    have hsplit : vecNormSq (fun i => (2 : ℝ)⁻¹ * v i + u i) +
        vecNormSq (fun i => -((2 : ℝ)⁻¹ * v i) + u i) =
        (2 : ℝ)⁻¹ * vecNormSq v + 2 * vecNormSq u := by
      simp only [vecNormSq, vecDot, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hexp i
    rw [hsplit, hun, ht2]
    ring
  · funext i
    show ((2 : ℝ)⁻¹ * v i + u i) - (-((2 : ℝ)⁻¹ * v i) + u i) = v i
    ring

/-- **The adjoint frame map is onto the loading ball.** -/
theorem exists_frameLegBVec_eq [NeZero d] {v : Vec d} (hv : vecNormSq v ≤ 2) :
    ∃ e : FullBlockVec d, Ch02.fullBlockVecNormSq e = 1 ∧ frameLegBVec e = v := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set t : ℝ := Real.sqrt ((2 - vecNormSq v) / 4) with ht
  set u : Vec d := Pi.single ⟨0, hd⟩ t with hu
  have ht2 : t ^ 2 = (2 - vecNormSq v) / 4 := by
    rw [ht, Real.sq_sqrt (by linarith)]
  have hun : vecNormSq u = t ^ 2 := by
    simp [hu, vecNormSq, vecDot, Pi.single_apply, Finset.sum_ite_eq', pow_two]
  refine ⟨Sum.elim (fun i => (2 : ℝ)⁻¹ * v i + u i)
    (fun i => (2 : ℝ)⁻¹ * v i - u i), ?_, ?_⟩
  · rw [ErrorComparison.fullBlockVecNormSq_eq_add]
    have h1 : (fun i : Fin d => (Sum.elim (fun i => (2 : ℝ)⁻¹ * v i + u i)
        (fun i => (2 : ℝ)⁻¹ * v i - u i) : FullBlockVec d) (Sum.inl i)) =
        fun i => (2 : ℝ)⁻¹ * v i + u i := rfl
    have h2 : (fun i : Fin d => (Sum.elim (fun i => (2 : ℝ)⁻¹ * v i + u i)
        (fun i => (2 : ℝ)⁻¹ * v i - u i) : FullBlockVec d) (Sum.inr i)) =
        fun i => (2 : ℝ)⁻¹ * v i - u i := rfl
    rw [h1, h2]
    have hexp : ∀ i : Fin d,
        ((2 : ℝ)⁻¹ * v i + u i) * ((2 : ℝ)⁻¹ * v i + u i) +
            ((2 : ℝ)⁻¹ * v i - u i) * ((2 : ℝ)⁻¹ * v i - u i) =
          (2 : ℝ)⁻¹ * (v i * v i) + 2 * (u i * u i) := by
      intro i; ring
    have hsplit : vecNormSq (fun i => (2 : ℝ)⁻¹ * v i + u i) +
        vecNormSq (fun i => (2 : ℝ)⁻¹ * v i - u i) =
        (2 : ℝ)⁻¹ * vecNormSq v + 2 * vecNormSq u := by
      simp only [vecNormSq, vecDot, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hexp i
    rw [hsplit, hun, ht2]
    ring
  · funext i
    show ((2 : ℝ)⁻¹ * v i + u i) + ((2 : ℝ)⁻¹ * v i - u i) = v i
    ring

/-- **The primal leg majorizes every paired loading of the ball.**  The exact
converse of the proved `Breakdown.breakdownLegA_le_of_paired_bound`: on a
descendant cube the leg at the isotropic comparator is an upper bound for `J(R,
σ^{-1/2}v, σ^{1/2}v; a)` at every `v` with `|v|² ≤ 2`. -/
theorem responseJ_paired_le_breakdownLegA [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar)
    (hR : R ∈ descendantsAtScale Q k) {v : Vec d} (hv : vecNormSq v ≤ 2) :
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R)
        (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤
      breakdownLegA R a (Observable.isotropicComparatorMatrix sigma) := by
  obtain ⟨e, he, hev⟩ := exists_frameLegAVec_eq hv
  have hbdd := breakdownLegAValueSet_bddAbove (Q := Q) (k := k) a
    (Observable.isotropicComparatorMatrix sigma) hR
  rw [breakdownLegAValueSet_isotropic_eq] at hbdd
  rw [breakdownLegA, breakdownLegAValueSet_isotropic_eq]
  exact le_csSup hbdd ⟨e, he, by rw [hev]⟩

/-- **The adjoint leg majorizes every paired loading of the ball.** -/
theorem responseJ_paired_le_breakdownLegB [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar)
    (hR : R ∈ descendantsAtScale Q k) {v : Vec d} (hv : vecNormSq v ≤ 2) :
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R).transpose
        (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤
      breakdownLegB R a (Observable.isotropicComparatorMatrix sigma) := by
  obtain ⟨e, he, hev⟩ := exists_frameLegBVec_eq hv
  have hbdd := breakdownLegBValueSet_bddAbove (Q := Q) (k := k) a
    (Observable.isotropicComparatorMatrix sigma) hR
  rw [breakdownLegBValueSet_isotropic_eq] at hbdd
  rw [breakdownLegB, breakdownLegBValueSet_isotropic_eq]
  exact le_csSup hbdd ⟨e, he, by rw [hev]⟩

/-- **The wave-gauge bound at the fixed sample** ((i), second item).

The priced wave remainder of the `J`-injection display carries `3^{4l - 2γl} ·
underlineW2Gauge(R, k_L - k_{l-h})²`.

Deterministic, sample by sample; no measure and no Orlicz datum occurs. -/
theorem injection_waveLeg_le_waveSizeW2_sq (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 ≤ Ccg) (R : TriadicCube d) (h : ℕ) (L : ℤ) (omega : ShellSeq d) :
    324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
          ((Disorder.cstar M)⁻¹ * M.gamma *
            (3 : ℝ) ^ (4 * (R.scale : ℝ) - 2 * M.gamma * (R.scale : ℝ))) *
          underlineW2Gauge R (shellIncrement omega (R.scale - (h : ℤ)) L) ^ 2 ≤
      324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
          ((Disorder.cstar M)⁻¹ * M.gamma) *
        MultiscaleEstimate.waveSizeW2 M L h R omega ^ 2 := by
  have hbase := three_zpow_mul_underlineW2Gauge_sq_le_waveGaugeW2_sq R L h omega
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hresp : (0 : ℝ) ≤ responseSensitivityConst d :=
    (responseSensitivityConst_pos M.shellPrefix.dimension).le
  have hpre : (0 : ℝ) ≤ 324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
      ((Disorder.cstar M)⁻¹ * M.gamma) := by positivity
  have hfac : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * M.gamma) * (R.scale : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsplit : (3 : ℝ) ^ (4 * (R.scale : ℝ) - 2 * M.gamma * (R.scale : ℝ)) =
      (3 : ℝ) ^ (-(2 * M.gamma) * (R.scale : ℝ)) * (3 : ℝ) ^ (4 * R.scale) := by
    rw [show (4 : ℝ) * (R.scale : ℝ) - 2 * M.gamma * (R.scale : ℝ) =
        -(2 * M.gamma) * (R.scale : ℝ) + (((4 * R.scale : ℤ)) : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_intCast]
  have hw2 : MultiscaleEstimate.waveSizeW2 M L h R omega ^ 2 =
      (3 : ℝ) ^ (-(2 * M.gamma) * (R.scale : ℝ)) *
        MultiscaleEstimate.waveGaugeW2 L h R omega ^ 2 := by
    rw [MultiscaleEstimate.waveSizeW2, mul_pow,
      ← Real.rpow_natCast ((3 : ℝ) ^ (-M.gamma * ((R.scale : ℤ) : ℝ))) 2,
      ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hstep : (3 : ℝ) ^ (4 * (R.scale : ℝ) - 2 * M.gamma * (R.scale : ℝ)) *
      underlineW2Gauge R (shellIncrement omega (R.scale - (h : ℤ)) L) ^ 2 ≤
      MultiscaleEstimate.waveSizeW2 M L h R omega ^ 2 := by
    rw [hsplit, hw2, mul_assoc]
    exact mul_le_mul_of_nonneg_left hbase hfac
  calc 324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
        ((Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (4 * (R.scale : ℝ) - 2 * M.gamma * (R.scale : ℝ))) *
        underlineW2Gauge R (shellIncrement omega (R.scale - (h : ℤ)) L) ^ 2
      = (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma)) *
          ((3 : ℝ) ^ (4 * (R.scale : ℝ) - 2 * M.gamma * (R.scale : ℝ)) *
            underlineW2Gauge R (shellIncrement omega (R.scale - (h : ℤ)) L) ^ 2) := by
        ring
    _ ≤ (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma)) *
          MultiscaleEstimate.waveSizeW2 M L h R omega ^ 2 :=
        mul_le_mul_of_nonneg_left hstep hpre

/-! ## 3. The per-`(l,z)` composed switch endpoints

All three ingredients are made first (one null set for every triadic cube, gap
and coefficient scale), because the `z`-aggregation fixes the sample and then
ranges over the grid. -/

/-- The `#lambda`-gate on ONE null set, uniformly in the cube and the two
scales.  `TriadicCube d` and `ℤ` are countable, so this is
`LambdaGateChain.lambda_gate_chain` plus three `ae_all_iff` rewrites; the three
scale premises are discharged by case analysis (off them the conclusion is
vacuous). -/
private theorem lambda_gate_chain_forall_cubes (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
            ∀ (Q : TriadicCube d) (n L : ℤ), n ≤ L → n ≤ Q.scale → n ≤ m0 →
              omega ∈ goodLocalEvent M Ccg Q n →
                (Annealed.sigmaBar M n : ℝ) *
                    (Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2)
                      (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ ≤
                  48 * Ccg := by
  obtain ⟨C, hC0, hmain⟩ := lambda_gate_chain d
  refine ⟨C, hC0, ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE Ccg hCcg
  rw [MeasureTheory.ae_all_iff]
  intro Q
  rw [MeasureTheory.ae_all_iff]
  intro n
  rw [MeasureTheory.ae_all_iff]
  intro L
  by_cases hnL : n ≤ L
  · by_cases hnQ : n ≤ Q.scale
    · by_cases hnm0 : n ≤ m0
      · filter_upwards
          [hmain M m0 E hm0 hstate hCE hgammaE Ccg hCcg Q n L hnL hnQ hnm0]
          with omega homega
        exact fun _ _ _ => homega
      · exact Filter.Eventually.of_forall fun _ _ _ h => absurd h hnm0
    · exact Filter.Eventually.of_forall fun _ _ h _ => absurd h hnQ
  · exact Filter.Eventually.of_forall fun _ h _ _ => absurd h hnL

/-- The T priced injection display on ONE null set, uniformly in the cube, the gap,
the coefficient scale and the load.  The adjoint twin of
`GoodEventAggregation.responseJ_injection_priced_ae_forall_cubes_and_loads`,
obtained from the primal one by the proved `(J3)` transfer
`AdjointInjection.responseJ_transpose_injection_priced_forall_loads_of_primal`
and the same three `ae_all_iff` rewrites.  No constant changes. -/
private theorem responseJ_transpose_injection_priced_ae_forall_cubes_and_loads (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
            ∀ (Q : TriadicCube d) (hgap : ℕ) (L : ℤ),
              Q.scale - (hgap : ℤ) ≤ L → Q.scale - (hgap : ℤ) ≤ m0 →
              M.gamma * (hgap : ℝ) ≤ 1 →
                omega ∈ goodLocalEvent M Ccg Q (Q.scale - (hgap : ℤ)) →
                  ∀ v : Vec d, vecNormSq v ≤ 2 →
                    Ch02.responseJ (Ch02.cubeDomain Q)
                        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn
                          Q).transpose
                        (Observable.inverseSqrtLoad
                          (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                        (Observable.sqrtLoad
                          (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) ≤
                      3 * Ch02.responseJ (Ch02.cubeDomain Q)
                          ((coefficientCutoffTriadicCoeffFamily M
                            (Q.scale - (hgap : ℤ)) omega).coeffOn Q).transpose
                          (Observable.inverseSqrtLoad
                            (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                          (Observable.sqrtLoad
                            (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) +
                        324 * responseSensitivityConst d *
                          (16 * Ccg + 8 * Ccg ^ 2) *
                          ((Disorder.cstar M)⁻¹ * M.gamma *
                            (3 : ℝ) ^ (4 * (Q.scale : ℝ) -
                              2 * M.gamma * (Q.scale : ℝ))) *
                          underlineW2Gauge Q
                            (shellIncrement omega.1 (Q.scale - (hgap : ℤ)) L) ^ 2 := by
  obtain ⟨C, hC0, hprim⟩ := responseJ_injection_priced_ae_forall_loads d
  refine ⟨C, hC0, ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE Ccg hCcg
  rw [MeasureTheory.ae_all_iff]
  intro Q
  rw [MeasureTheory.ae_all_iff]
  intro hgap
  rw [MeasureTheory.ae_all_iff]
  intro L
  by_cases hnL : Q.scale - (hgap : ℤ) ≤ L
  · by_cases hnm0 : Q.scale - (hgap : ℤ) ≤ m0
    · by_cases hgh : M.gamma * (hgap : ℝ) ≤ 1
      · filter_upwards
          [responseJ_transpose_injection_priced_forall_loads_of_primal M Ccg Q hgap L
            hnL (hprim M m0 E hm0 hstate hCE hgammaE Ccg hCcg Q hgap L hnL hnm0 hgh)]
          with omega homega
        exact fun _ _ _ => homega
      · exact Filter.Eventually.of_forall fun _ _ _ h => absurd h hgh
    · exact Filter.Eventually.of_forall fun _ _ h _ => absurd h hnm0
  · exact Filter.Eventually.of_forall fun _ h _ _ => absurd h hnL

/-- The `#J`-smallness carrier of the injection display, identified with the honest
coefficient family at the translated sample. -/
private theorem carrier_bridge [NeZero d] (M : ABKModel d) (Q : TriadicCube d)
    {n L : ℤ} (hnL : n ≤ L) (omega : CutoffSample d) (p q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain (originCube d 0))
        (perturbCoeffOn (Ch02.cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M Q n omega)
          (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1) p q =
      Ch02.responseJ (Ch02.cubeDomain (originCube d Q.scale))
        ((coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample (triadicCubeShift Q) omega)).coeffOn
            (originCube d Q.scale)) p q := by
  rw [responseJ_perturbCoeffOn_unitRescaledCutoffCoeff M Q hnL omega p q,
    ← responseJ_cutoffFamily_eq_unitRescaledCutoffCoeff M L Q p q omega,
    responseJ_cutoffFamily_eq_originCube_translate M L Q p q omega]

/-- **The composed primal per-`(l,z)` endpoint.**

For the multiscale root's own regime, one gap `h` with `γ h ≤ 1` and one
working scale `m ≤ m0`: on ONE probability-one event, simultaneously for every
depth `j` and every grid cube `R` of the printed tiling at scale `l = m - j`, on
the manuscript's own good event `𝒬(l, l-h, z)`,

```text
legA(R; a_m, σ_m) ≤ 24 · legA(R; a_{l-h}, σ_{l-h})
                    + 8·Cinj(Ccg)·c⋆⁻¹γ · waveSizeW2(m,h,R)²
                    + Cs·48Ccg · switchRemainder γ E h j .
```

The three summands are, before the `z`-average and the `l`-sum, the printed
first, third and fifth terms of `e.localization.mathcalE.estimate`.  The `24`
is `8` (the proved switch endpoint at the `ρ = 4` window) times `3` (the
printed injection factor); measured at the printed `max_{|e|=1}` carrier this
is a factor-`4` loss against the printed `6` in a dimension-free numeral,
chartered by [C]'s own text and disclosed in the module header.

A, inherited: `0 < Ccg` and the good-event membership. -/
theorem breakdownLegA_le_deep_wave_remainder_ae (d : ℕ) [NeZero d] :
    ∃ Cs Cg Ci : ℝ, 0 < Cs ∧ 0 < Cg ∧ 0 < Ci ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Cg * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Ci * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ (m : ℤ), m ≤ m0 →
            ∀ (hgap : ℕ), M.gamma * (hgap : ℝ) ≤ 1 →
              ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
                ∀ (j : ℕ) (R : TriadicCube d),
                  R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)) →
                    omega ∈ goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)) →
                      breakdownLegA R (coefficientCutoffTriadicCoeffFamily M m omega)
                          (Observable.isotropicComparatorMatrix
                            (Annealed.sigmaBar M m)) ≤
                        24 * breakdownLegA R
                            (coefficientCutoffTriadicCoeffFamily M
                              (R.scale - (hgap : ℤ)) omega)
                            (Observable.isotropicComparatorMatrix
                              (Annealed.sigmaBar M (R.scale - (hgap : ℤ)))) +
                          8 * (324 * responseSensitivityConst d *
                              (16 * Ccg + 8 * Ccg ^ 2) *
                              ((Disorder.cstar M)⁻¹ * M.gamma)) *
                            MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 +
                          Cs * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j := by
  obtain ⟨Cs, hCs0, hsw⟩ := breakdownLegA_le_of_shom_switch d
  obtain ⟨Cg, hCg0, hchain⟩ := lambda_gate_chain_forall_cubes d
  obtain ⟨Ci, hCi0, hinj⟩ := responseJ_injection_priced_ae_forall_cubes_and_loads d
  refine ⟨Cs, Cg, Ci, hCs0, hCg0, hCi0, ?_⟩
  intro M m0 E hm0 hstate hCEs hCEg hCEi hgammaE Ccg hCcg m hmm0 hgap hgh
  filter_upwards
    [hchain M m0 E hm0 hstate hCEg hgammaE Ccg hCcg,
     hinj M m0 E hm0 hstate hCEi hgammaE Ccg hCcg]
    with omega hgateall hstepall j R hR homega
  have hscale : R.scale = m - (j : ℤ) :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hjm : m - (j : ℤ) ≤ m := by omega
  have hnR : R.scale - (hgap : ℤ) ≤ R.scale := by omega
  have hnm : R.scale - (hgap : ℤ) ≤ m := by omega
  have hnm0 : R.scale - (hgap : ℤ) ≤ m0 := le_trans hnm hmm0
  have hsign : (0 : ℝ) ≤ ((Annealed.sigmaBar M (R.scale - (hgap : ℤ)) : ℝ)) :=
    (Annealed.sigmaBar M (R.scale - (hgap : ℤ))).2.le
  -- the gate at the switch endpoint's own carrier
  have hgate : (Annealed.sigmaBar M (R.scale - (hgap : ℤ)) : ℝ) *
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse
        (Ch02.cubeDomain (originCube d R.scale))
        ((coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
            (originCube d R.scale))) ≤ 48 * Ccg := by
    refine sigmaStarInv_gate_of_lambdaGate (originCube d R.scale)
      (coefficientCutoffTriadicCoeffFamily M m
        (translateCutoffSample (triadicCubeShift R) omega))
      (s := 1 / 8) (q := 2) hsign (by norm_num) (by norm_num) ?_
    rw [← lambdaSq_cutoff_translateCutoffSample M m R (1 / 8)
      (Ch02.MultiscaleExponent.finite 2) omega]
    exact hgateall R (R.scale - (hgap : ℤ)) m hnm hnR hnm0 homega
  -- the deep bound at the switch endpoint's own carrier
  have hstep := hstepall R hgap m hnm hnm0 hgh homega
  have hdeep : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Ch02.responseJ (Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M m
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale))
          (Observable.inverseSqrtLoad
            (Annealed.sigmaBar M (R.scale - (hgap : ℤ))) v)
          (Observable.sqrtLoad
            (Annealed.sigmaBar M (R.scale - (hgap : ℤ))) v) ≤
        3 * breakdownLegA R
            (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
            (Observable.isotropicComparatorMatrix
              (Annealed.sigmaBar M (R.scale - (hgap : ℤ)))) +
          (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
              ((Disorder.cstar M)⁻¹ * M.gamma)) *
            MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 := by
    intro v hv
    rw [← carrier_bridge M R hnm omega]
    have h1 := hstep v hv
    have h2 := responseJ_paired_le_breakdownLegA
      (Q := originCube d m) (k := m - (j : ℤ))
      (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
      (Annealed.sigmaBar M (R.scale - (hgap : ℤ))) hR hv
    have h3 := injection_waveLeg_le_waveSizeW2_sq M hCcg.le R hgap m omega.1
    linarith
  have hc0 : (0 : ℝ) ≤
      3 * breakdownLegA R
          (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (R.scale - (hgap : ℤ)))) +
        (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma)) *
          MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 := by
    have hleg := breakdownLegA_nonneg R
      (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (R.scale - (hgap : ℤ))))
    have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have hcstar : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
    have hresp : (0 : ℝ) ≤ responseSensitivityConst d :=
      (responseSensitivityConst_pos M.shellPrefix.dimension).le
    have hwave : (0 : ℝ) ≤
        (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma)) *
          MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 := by
      have : (0 : ℝ) ≤ 324 * responseSensitivityConst d *
          (16 * Ccg + 8 * Ccg ^ 2) * ((Disorder.cstar M)⁻¹ * M.gamma) := by
        have := hCcg.le
        positivity
      positivity
    linarith
  have hmain := hsw M m0 E hm0 hstate hCEs hgammaE m (R.scale - (hgap : ℤ))
    hnm hmm0 m R omega (48 * Ccg) _ hc0 hgate hdeep
  have hrem : Cs * (48 * Ccg) *
        min 1 (M.gamma ^ 2 * ((m : ℝ) - ((R.scale - (hgap : ℤ) : ℤ) : ℝ)) ^ 2) *
        (3 : ℝ) ^ (2 * (M.gamma *
          ((m : ℝ) - ((R.scale - (hgap : ℤ) : ℤ) : ℝ)))) +
      Cs * (48 * Ccg) * ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
        (3 : ℝ) ^ (2 * (M.gamma *
          ((m : ℝ) - ((R.scale - (hgap : ℤ) : ℤ) : ℝ))))
      = Cs * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j := by
    rw [hscale]
    exact switchRemainder_eq_of_int_gap Cs (48 * Ccg) M.gamma (E : ℝ) m hgap j
  linarith [hmain, hrem]

/-- **The composed adjoint per-`(l,z)` endpoint.**  The `(J3)` mirror of
`breakdownLegA_le_deep_wave_remainder_ae`: same regime list, same gap window,
same constants `24 / 8·Cinj / Cs·48Ccg`, every carrier transposed.  The gate is
the SAME printed `lambda`-gate (`SwitchNormalization.sigmaStarInv_transpose_gate_of_lambdaGate`
is an adjoint invariance, not a second estimate), and the deep and wave terms
come from the transposed injection endpoint of `AdjointInjection`. -/
theorem breakdownLegB_le_deep_wave_remainder_ae (d : ℕ) [NeZero d] :
    ∃ Cs Cg Ci : ℝ, 0 < Cs ∧ 0 < Cg ∧ 0 < Ci ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Cg * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Ci * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ (m : ℤ), m ≤ m0 →
            ∀ (hgap : ℕ), M.gamma * (hgap : ℝ) ≤ 1 →
              ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
                ∀ (j : ℕ) (R : TriadicCube d),
                  R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)) →
                    omega ∈ goodLocalEvent M Ccg R (R.scale - (hgap : ℤ)) →
                      breakdownLegB R (coefficientCutoffTriadicCoeffFamily M m omega)
                          (Observable.isotropicComparatorMatrix
                            (Annealed.sigmaBar M m)) ≤
                        24 * breakdownLegB R
                            (coefficientCutoffTriadicCoeffFamily M
                              (R.scale - (hgap : ℤ)) omega)
                            (Observable.isotropicComparatorMatrix
                              (Annealed.sigmaBar M (R.scale - (hgap : ℤ)))) +
                          8 * (324 * responseSensitivityConst d *
                              (16 * Ccg + 8 * Ccg ^ 2) *
                              ((Disorder.cstar M)⁻¹ * M.gamma)) *
                            MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 +
                          Cs * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j := by
  obtain ⟨Cs, hCs0, hsw⟩ := breakdownLegB_le_of_shom_switch d
  obtain ⟨Cg, hCg0, hchain⟩ := lambda_gate_chain_forall_cubes d
  obtain ⟨Ci, hCi0, hinj⟩ :=
    responseJ_transpose_injection_priced_ae_forall_cubes_and_loads d
  refine ⟨Cs, Cg, Ci, hCs0, hCg0, hCi0, ?_⟩
  intro M m0 E hm0 hstate hCEs hCEg hCEi hgammaE Ccg hCcg m hmm0 hgap hgh
  filter_upwards
    [hchain M m0 E hm0 hstate hCEg hgammaE Ccg hCcg,
     hinj M m0 E hm0 hstate hCEi hgammaE Ccg hCcg]
    with omega hgateall hstepall j R hR homega
  have hscale : R.scale = m - (j : ℤ) :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hnR : R.scale - (hgap : ℤ) ≤ R.scale := by omega
  have hnm : R.scale - (hgap : ℤ) ≤ m := by omega
  have hnm0 : R.scale - (hgap : ℤ) ≤ m0 := le_trans hnm hmm0
  have hsign : (0 : ℝ) ≤ ((Annealed.sigmaBar M (R.scale - (hgap : ℤ)) : ℝ)) :=
    (Annealed.sigmaBar M (R.scale - (hgap : ℤ))).2.le
  have hgate : (Annealed.sigmaBar M (R.scale - (hgap : ℤ)) : ℝ) *
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse
        (Ch02.cubeDomain (originCube d R.scale))
        ((coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
            (originCube d R.scale)).transpose) ≤ 48 * Ccg := by
    refine sigmaStarInv_transpose_gate_of_lambdaGate (originCube d R.scale)
      (coefficientCutoffTriadicCoeffFamily M m
        (translateCutoffSample (triadicCubeShift R) omega))
      (s := 1 / 8) (q := 2) hsign (by norm_num) (by norm_num) ?_
    rw [← lambdaSq_cutoff_translateCutoffSample M m R (1 / 8)
      (Ch02.MultiscaleExponent.finite 2) omega]
    exact hgateall R (R.scale - (hgap : ℤ)) m hnm hnR hnm0 homega
  have hstep := hstepall R hgap m hnm hnm0 hgh homega
  have hdeep : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Ch02.responseJ (Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M m
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale)).transpose
          (Observable.inverseSqrtLoad
            (Annealed.sigmaBar M (R.scale - (hgap : ℤ))) v)
          (Observable.sqrtLoad
            (Annealed.sigmaBar M (R.scale - (hgap : ℤ))) v) ≤
        3 * breakdownLegB R
            (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
            (Observable.isotropicComparatorMatrix
              (Annealed.sigmaBar M (R.scale - (hgap : ℤ)))) +
          (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
              ((Disorder.cstar M)⁻¹ * M.gamma)) *
            MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 := by
    intro v hv
    rw [← responseJ_cutoffFamily_transpose_eq_originCube_translate M m R _ _ omega]
    have h1 := hstep v hv
    have h2 := responseJ_paired_le_breakdownLegB
      (Q := originCube d m) (k := m - (j : ℤ))
      (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
      (Annealed.sigmaBar M (R.scale - (hgap : ℤ))) hR hv
    have h3 := injection_waveLeg_le_waveSizeW2_sq M hCcg.le R hgap m omega.1
    linarith
  have hc0 : (0 : ℝ) ≤
      3 * breakdownLegB R
          (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (R.scale - (hgap : ℤ)))) +
        (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma)) *
          MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 := by
    have hleg := breakdownLegB_nonneg R
      (coefficientCutoffTriadicCoeffFamily M (R.scale - (hgap : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (R.scale - (hgap : ℤ))))
    have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have hcstar : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
    have hresp : (0 : ℝ) ≤ responseSensitivityConst d :=
      (responseSensitivityConst_pos M.shellPrefix.dimension).le
    have hwave : (0 : ℝ) ≤
        (324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
            ((Disorder.cstar M)⁻¹ * M.gamma)) *
          MultiscaleEstimate.waveSizeW2 M m hgap R omega.1 ^ 2 := by
      have : (0 : ℝ) ≤ 324 * responseSensitivityConst d *
          (16 * Ccg + 8 * Ccg ^ 2) * ((Disorder.cstar M)⁻¹ * M.gamma) := by
        have := hCcg.le
        positivity
      positivity
    linarith
  have hmain := hsw M m0 E hm0 hstate hCEs hgammaE m (R.scale - (hgap : ℤ))
    hnm hmm0 m R omega (48 * Ccg) _ hc0 hgate hdeep
  have hrem : Cs * (48 * Ccg) *
        min 1 (M.gamma ^ 2 * ((m : ℝ) - ((R.scale - (hgap : ℤ) : ℤ) : ℝ)) ^ 2) *
        (3 : ℝ) ^ (2 * (M.gamma *
          ((m : ℝ) - ((R.scale - (hgap : ℤ) : ℤ) : ℝ)))) +
      Cs * (48 * Ccg) * ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
        (3 : ℝ) ^ (2 * (M.gamma *
          ((m : ℝ) - ((R.scale - (hgap : ℤ) : ℤ) : ℝ))))
      = Cs * (48 * Ccg) * switchRemainder M.gamma (E : ℝ) hgap j := by
    rw [hscale]
    exact switchRemainder_eq_of_int_gap Cs (48 * Ccg) M.gamma (E : ℝ) m hgap j
  linarith [hmain, hrem]

end

end Algsuperdiff.Section3.Provider.Localization
