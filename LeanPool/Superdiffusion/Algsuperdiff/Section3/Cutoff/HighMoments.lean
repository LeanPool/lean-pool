/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Carrier
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations

/-!
# HighMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Higher moments of the genuine cutoff local envelope

The lower-infinite cutoff itself is defined only on `CutoffSample`.  This
module follows the same rule for its local control: the displayed series is
used only on that carrier, where `LowerTailGood` supplies its summability.
In particular, this is not a totalized control on arbitrary shell sequences.

The upper ellipticity lane must control the full nonsymmetric coefficient
matrix.  Thus its random envelope is built from the skew cutoff, not confused
with the deterministic lower energy constant `nu`.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The actual lower-tail local control on the public convergence carrier.
Its value is the nonnegative series of the literal local controls of all
shells `j_(m-r)`. -/
def cutoffLocalControl (ell m : ℤ) (omega : CutoffSample d) : ℝ :=
  ∑' r : ℕ, localCubeControl ell (omega.1 (m - (r : ℤ)))

/-- The cutoff local-control series is nonnegative. -/
theorem cutoffLocalControl_nonneg (ell m : ℤ) (omega : CutoffSample d) :
    0 ≤ cutoffLocalControl ell m omega := by
  apply tsum_nonneg
  intro r
  exact localCubeControl_nonneg _ _

/-- The defining local-control series is summable at every point of the
public cutoff carrier. -/
theorem summable_cutoffLocalControl (ell m : ℤ) (omega : CutoffSample d) :
    Summable (fun r : ℕ => localCubeControl ell (omega.1 (m - (r : ℤ))) ) :=
  lowerTailGood_summable omega.2 ell m

/-- Internal quantitative scale for the literal zero-shell local control.
It records the finite lattice entropy at a cube scale and is not a new
normalization of any source-facing object. -/
def localCubeControlGammaScale (d : ℕ) (q : ℤ) : ℝ :=
  Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3)) *
    Real.sqrt (1 + max (q : ℝ) 0)

private theorem one_le_localCubeControlGammaBase (d : ℕ) :
    1 ≤ Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3)) := by
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have harg : 0 ≤ 3 * (1 + (d : ℝ) * Real.log 3) := by positivity
  have hsquare : (Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3))) ^ 2 =
      3 * (1 + (d : ℝ) * Real.log 3) := Real.sq_sqrt harg
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3)) :=
    Real.sqrt_nonneg _
  nlinarith

/-- The zero-shell local control has an explicit `Γ₂` moment witness.  The
only scale dependence is the square root of the number of unit descendants;
no independence between translated controls is assumed. -/
theorem hasGammaMomentGrowthWith_localCubeControl_zero (M : ABKModel d) (q : ℤ) :
    IndependentSums.HasGammaMomentGrowthWith
      (ShellField.zeroShellLaw M.P).toMeasure 2 (localCubeControl q)
      (IndependentSums.gammaMomentConst 2 * localCubeControlGammaScale d q) := by
  let C : ℝ := Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3))
  have hCpos : 0 < C := by
    dsimp [C]
    apply Real.sqrt_pos.2
    have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hscale_pos : 0 < localCubeControlGammaScale d q := by
    unfold localCubeControlGammaScale
    apply mul_pos hCpos
    apply Real.sqrt_pos.2
    have : (0 : ℝ) ≤ max (q : ℝ) 0 := le_max_right _ _
    linarith
  have htail_unit : IndependentSums.IsBigOWith
      (ShellField.zeroShellLaw M.P).toMeasure (IndependentSums.gammaSigma 2)
      ShellField.unitCubeValueNorm 1 := by
    exact Algsuperdiff.Probability.isBigOWith_gammaSigma_two_of_gaussian_tail
      (by simpa only [one_mul, ← Real.rpow_natCast] using!
        zeroShell_unitCubeValueNorm_gaussian_tail M)
  have htail : IndependentSums.IsBigOWith
      (ShellField.zeroShellLaw M.P).toMeasure (IndependentSums.gammaSigma 2)
      (localCubeControl q) (localCubeControlGammaScale d q) := by
    rcases le_total q 0 with hq | hq
    · apply (htail_unit.of_le (fun j => by
          simpa only [localCubeControl_zero_eq_unitCubeValueNorm] using
            localCubeControl_le_localCubeControl_zero q hq j)).mono_scale
      unfold localCubeControlGammaScale
      rw [max_eq_right (by exact_mod_cast hq)]
      simpa only [add_zero, Real.sqrt_one, mul_one] using one_le_localCubeControlGammaBase d
    · rcases lt_or_eq_of_le hq with hqpos | rfl
      swap
      · have hscale : 1 ≤ localCubeControlGammaScale d 0 := by
          unfold localCubeControlGammaScale
          norm_num only [Int.cast_zero, max_self, add_zero, Real.sqrt_one, mul_one]
          exact one_le_localCubeControlGammaBase d
        have hzero : localCubeControl (d := d) 0 = ShellField.unitCubeValueNorm (d := d) := by
          funext j
          exact localCubeControl_zero_eq_unitCubeValueNorm j
        simpa only [hzero] using
          htail_unit.mono_scale hscale
      have hq0 : 0 ≤ q := by omega
      let S := descendantsAtScale (originCube d q) 0
      let hS : S.Nonempty := descendantsAtScale_nonempty (originCube d q) hq0
      have hcard : S.card = (3 ^ d) ^ q.toNat := by
        simpa only [S] using card_originCubeUnitControlMax_lattice (d := d) q hq0
      have hqNat : 1 ≤ q.toNat := by
        omega
      have hbase : 2 ≤ 3 ^ d := by
        calc
          2 ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ d := pow_le_pow_right' (by norm_num) M.shellPrefix.dimension
      have hcard_two : 2 ≤ S.card := by
        rw [hcard]
        calc
          2 ≤ (3 ^ d) ^ 1 := by simpa using hbase
          _ ≤ (3 ^ d) ^ q.toNat := pow_le_pow_right' (by omega) hqNat
      let X : TriadicCube d → ShellField d → ℝ :=
        fun R => translatedUnitCubeControl (triadicCubeShift R)
      have htail_X : ∀ R ∈ S, IndependentSums.IsBigOWith
          (ShellField.zeroShellLaw M.P).toMeasure (IndependentSums.gammaSigma 2)
          (X R) 1 := by
        intro R _
        exact Algsuperdiff.Probability.isBigOWith_gammaSigma_two_of_gaussian_tail
          (by simpa only [one_mul, ← Real.rpow_natCast, X] using!
            zeroShell_translatedUnitCubeControl_gaussian_tail M (triadicCubeShift R))
      have htail_max : IndependentSums.IsBigOWith
          (ShellField.zeroShellLaw M.P).toMeasure (IndependentSums.gammaSigma 2)
          (originCubeUnitControlMax q hq0)
          ((3 * Real.log (S.card : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
        simpa only [originCubeUnitControlMax, S, X, hS, mul_one] using!
          IndependentSums.isBigOWith_gammaSigma_finset_sup'
            (μ := (ShellField.zeroShellLaw M.P).toMeasure) S hS
            (X := X) (A := 1) (σ := 2) (by norm_num) hcard_two htail_X
      apply (htail_max.of_le (fun j =>
        localCubeControl_le_originCubeUnitControlMax q hq0 j)).mono_scale
      have hmax : max 1 (Real.log (S.card : ℝ)) ≤
          (1 + (d : ℝ) * Real.log 3) * (1 + q.toNat) := by
        rw [hcard]
        exact Algsuperdiff.Probability.max_log_three_pow_le d q.toNat
      have hlog : 0 ≤ Real.log (S.card : ℝ) := by
        have hcard_real : (1 : ℝ) ≤ S.card := by
          have htwo : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard_two
          linarith
        exact Real.log_nonneg hcard_real
      have hsqrt : Real.sqrt (3 * Real.log (S.card : ℝ)) ≤
          Real.sqrt (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q.toNat))) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) hmax) (by norm_num)
      have hsplit : Real.sqrt (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q.toNat))) =
          C * Real.sqrt (1 + q.toNat) := by
        have hbase_nonneg : 0 ≤ 3 * (1 + (d : ℝ) * Real.log 3) := by
          have hlog' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          positivity
        dsimp [C]
        rw [show 3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q.toNat)) =
          (3 * (1 + (d : ℝ) * Real.log 3)) * (1 + q.toNat) by ring,
          Real.sqrt_mul hbase_nonneg]
      rw [show ((3 * Real.log (S.card : ℝ)) ^ ((2 : ℝ)⁻¹)) =
          Real.sqrt (3 * Real.log (S.card : ℝ)) by
        rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]]
      calc
        Real.sqrt (3 * Real.log (S.card : ℝ)) ≤
            Real.sqrt (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + q.toNat))) := hsqrt
        _ = C * Real.sqrt (1 + q.toNat) := hsplit
        _ = localCubeControlGammaScale d q := by
          unfold localCubeControlGammaScale
          have hqcast : (q.toNat : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          rw [hqcast, max_eq_left (by exact_mod_cast hq0)]
  simpa only [localCubeControlGammaScale] using
    IndependentSums.hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
      (μ := (ShellField.zeroShellLaw M.P).toMeasure)
      (Y := localCubeControl q) (σ := 2) (K := localCubeControlGammaScale d q)
      (by norm_num) hscale_pos (fun j => localCubeControl_nonneg q j)
      (measurable_localCubeControl q).aemeasurable htail

/-- Transport a one-sided stretched-exponential estimate through an exact
push-forward identity.  This is stated locally because the cutoff carrier is
a subtype with a deliberately nontrivial induced law. -/
private theorem isBigOWith_gammaSigma_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    {σ A : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hX : Measurable X) (hY : Measurable Y)
    (hmap : Measure.map X μ = Measure.map Y μ')
    (hYtail : IndependentSums.IsBigOWith μ' (IndependentSums.gammaSigma σ) Y A) :
    IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma σ) X A := by
  rw [IndependentSums.isBigOWith_gammaSigma_iff] at hYtail ⊢
  intro t ht
  let E : Set ℝ := {x | A * t < x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_id
  calc
    μ.real {omega | A * t < X omega} = (Measure.map X μ).real E := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := μ) hX.aemeasurable hE)
      simpa only [E, Set.preimage_ofPred_eq] using! h.symm
    _ = (Measure.map Y μ').real E := by rw [hmap]
    _ = μ'.real {omega | A * t < Y omega} := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := μ') hY.aemeasurable hE)
      simpa only [E, Set.preimage_ofPred_eq] using! h
    _ ≤ Real.exp (-(t ^ σ)) := hYtail ht

/-- Countable `Γ_σ` aggregation for an everywhere convergent family.  The
proof passes uniform finite-sum tails to the exact pointwise sum by Fatou;
it requires no independence between the summands. -/
private theorem isBigO_gammaSigma_tsum_of_hasSum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {σ : ℝ} {S : Ω → ℝ}
    (hσ : 0 < σ) (ha : ∀ k, 0 < a k) (hasum : Summable a)
    (hX : ∀ k, IndependentSums.IsBigO μ (IndependentSums.gammaSigma σ) (X k) (a k))
    (hXm : ∀ k, Measurable (X k))
    (hS : ∀ omega, HasSum (fun k => X k omega) (S omega)) :
    IndependentSums.IsBigO μ (IndependentSums.gammaSigma σ) S
      (IndependentSums.gammaTriangleConst σ * ∑' k, a k) := by
  let A : ℝ := IndependentSums.gammaTriangleConst σ * ∑' k, a k
  have htriangle_pos : 0 < IndependentSums.gammaTriangleConst σ :=
    IndependentSums.gammaTriangleConst_pos
  have hsum_pos : 0 < ∑' k, a k :=
    hasum.tsum_pos (fun k => (ha k).le) 0 (ha 0)
  have hApos : 0 < A := mul_pos htriangle_pos hsum_pos
  let P : ℕ → Ω → ℝ := fun N omega => ∑ k ∈ Finset.range N, X k omega
  have hPmeas : ∀ N, Measurable (P N) := fun N =>
    Finset.measurable_sum (Finset.range N) (fun k _ => hXm k)
  have hSmeas : Measurable S :=
    measurable_of_tendsto_metrizable hPmeas
      (tendsto_pi_nhds.2 fun omega => (hS omega).tendsto_sum_nat)
  have hpartial : ∀ N, 1 ≤ N → ∀ ⦃t : ℝ⦄, 1 ≤ t →
      μ.real (IndependentSums.absTailEvent (P N) (A * t)) ≤
        Real.exp (-(t ^ σ)) := by
    intro N hN t ht
    have hne : (Finset.range N).Nonempty := by
      rw [Finset.nonempty_range_iff]
      omega
    have hfinite : IndependentSums.IsBigO μ (IndependentSums.gammaSigma σ)
        (fun omega => ∑ k ∈ Finset.range N, X k omega)
        (IndependentSums.gammaTriangleConst σ * ∑ k ∈ Finset.range N, a k) :=
      IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma (μ := μ)
        (s := Finset.range N) (X := X) (a := a) (σ := σ) hσ hne
        (fun i _ => ha i) (fun i _ => hX i) (fun i _ => hXm i)
    have hscale : IndependentSums.gammaTriangleConst σ * ∑ k ∈ Finset.range N, a k ≤ A := by
      dsimp [A]
      exact mul_le_mul_of_nonneg_left
        (hasum.sum_le_tsum (Finset.range N) (fun i _ => (ha i).le)) htriangle_pos.le
    exact (IndependentSums.isBigO_gammaSigma_iff.mp (hfinite.mono_scale hscale)) ht
  rw [IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  let c : ℝ := A * t
  have hcpos : 0 < c := mul_pos hApos (lt_of_lt_of_le zero_lt_one ht)
  let E : ℕ → Set Ω := fun N => IndependentSums.absTailEvent (P N) c
  have hEmeas : ∀ N, MeasurableSet (E N) := fun N =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hPmeas N))
  let f : ℕ → Ω → ℝ≥0∞ := fun N => (E N).indicator (fun _ => 1)
  have hfmeas : ∀ N, Measurable (f N) := fun N =>
    measurable_const.indicator (hEmeas N)
  have hdom : ∀ omega, (IndependentSums.absTailEvent S c).indicator
      (fun _ => (1 : ℝ≥0∞)) omega ≤ Filter.liminf (fun N => f N omega) Filter.atTop := by
    intro omega
    by_cases hmem : omega ∈ IndependentSums.absTailEvent S c
    · rw [Set.indicator_of_mem hmem]
      have hlt : c < |S omega| := IndependentSums.mem_absTailEvent.mp hmem
      have htend : Filter.Tendsto (fun N => |P N omega|) Filter.atTop (nhds (|S omega|)) :=
        ((hS omega).tendsto_sum_nat).abs
      have hEventually : ∀ᶠ N in Filter.atTop, f N omega = 1 := by
        have hgt : ∀ᶠ N in Filter.atTop, c < |P N omega| :=
          htend.eventually (eventually_gt_nhds hlt)
        filter_upwards [hgt] with N hN
        exact Set.indicator_of_mem (IndependentSums.mem_absTailEvent.mpr hN) _
      calc
        (1 : ℝ≥0∞) = Filter.liminf (fun _ : ℕ => (1 : ℝ≥0∞)) Filter.atTop :=
          (Filter.liminf_const 1).symm
        _ ≤ Filter.liminf (fun N => f N omega) Filter.atTop := by
          refine Filter.liminf_le_liminf ?_
          filter_upwards [hEventually] with N hN
          exact le_of_eq hN.symm
    · rw [Set.indicator_of_notMem hmem]
      exact zero_le
  have hmeasure : μ (IndependentSums.absTailEvent S c) ≤
      Filter.liminf (fun N => μ (E N)) Filter.atTop := by
    calc
      μ (IndependentSums.absTailEvent S c) = ∫⁻ omega,
          (IndependentSums.absTailEvent S c).indicator (fun _ => (1 : ℝ≥0∞)) omega ∂μ := by
        simpa only [one_mul] using!
          (lintegral_indicator_const
            (μ := μ) (measurableSet_lt measurable_const
              (continuous_abs.measurable.comp hSmeas)) (1 : ℝ≥0∞)).symm
      _ ≤ ∫⁻ omega, Filter.liminf (fun N => f N omega) Filter.atTop ∂μ :=
        lintegral_mono hdom
      _ ≤ Filter.liminf (fun N => ∫⁻ omega, f N omega ∂μ) Filter.atTop :=
        lintegral_liminf_le hfmeas
      _ = Filter.liminf (fun N => μ (E N)) Filter.atTop := by
        refine congrArg (fun g => Filter.liminf g Filter.atTop) ?_
        funext N
        simpa only [f, one_mul] using
          (lintegral_indicator_const (μ := μ) (hEmeas N) (1 : ℝ≥0∞))
  have hEbound : ∀ N, μ (E N) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have hEzero : E 0 = ∅ := by
        ext omega
        simp only [E, P, IndependentSums.absTailEvent, IndependentSums.upperTailEvent,
          Finset.range_zero, Finset.sum_empty, abs_zero, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_lt]
        exact hcpos.le
      rw [hEzero]
      simp
    · have hbound := hpartial N hN ht
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E N))]
      exact ENNReal.ofReal_le_ofReal hbound
  have hlim : Filter.liminf (fun N => μ (E N)) Filter.atTop ≤
      ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    calc
      Filter.liminf (fun N => μ (E N)) Filter.atTop ≤
          Filter.liminf (fun _ : ℕ => ENNReal.ofReal (Real.exp (-(t ^ σ)))) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hEbound)
      _ = ENNReal.ofReal (Real.exp (-(t ^ σ))) := Filter.liminf_const _
  have hbound := hmeasure.trans hlim
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
    ENNReal.ofReal_ne_top).mpr hbound
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal

/-- The deterministic `Γ₂` budget for one lower shell.  It is the earlier
expectation majorant with the harmless tail-to-moment factor displayed, so its
summability follows from the already-verified geometric majorant. -/
def cutoffGammaMajorant (d : ℕ) (gamma : ℝ) (m ell : ℤ) (r : ℕ) : ℝ :=
  Real.exp 1 * expectedCubeMajorant d gamma m ell r

theorem cutoffGammaMajorant_pos (d : ℕ) (gamma : ℝ) (m ell : ℤ) (r : ℕ) :
    0 < cutoffGammaMajorant d gamma m ell r := by
  unfold cutoffGammaMajorant expectedCubeMajorant cubeMajorant
  apply mul_pos (Real.exp_pos _)
  apply mul_pos (gaussianMaximumDimConst_pos d)
  apply mul_pos
  · apply Real.sqrt_pos.2
    have : (0 : ℝ) ≤ max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0 := le_max_right _ _
    linarith
  · exact Real.rpow_pos_of_pos (by norm_num) _

theorem summable_cutoffGammaMajorant {gamma : ℝ} (hgamma : 0 < gamma)
    (m ell : ℤ) : Summable (cutoffGammaMajorant d gamma m ell) := by
  unfold cutoffGammaMajorant
  exact (summable_expectedCubeMajorant hgamma m ell).mul_left _

/-- A single lower shell has the explicit `Γ₂` tail budget matching the
summable deterministic majorant.  This transports only the literal marginal
scaling law, and uses no cross-shell independence. -/
theorem isBigOWith_gammaSigma_localCubeControl_lowerShell (M : ABKModel d)
    (m ell : ℤ) (r : ℕ) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega => localCubeControl ell (omega (m - r)))
      (cutoffGammaMajorant d M.gamma m ell r) := by
  let n : ℤ := m - r
  let q : ℤ := ell - n
  let b : ℝ := Real.rpow 3 (M.gamma * (n : ℝ))
  let f : ShellSeq d → ℝ := fun omega => localCubeControl ell (omega n)
  let g : ShellField d → ℝ := fun j => b * localCubeControl q j
  have hbpos : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hMpos : 0 < IndependentSums.gammaMomentConst 2 * localCubeControlGammaScale d q := by
    apply mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
    unfold localCubeControlGammaScale
    apply mul_pos
    · apply Real.sqrt_pos.2
      have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      positivity
    · apply Real.sqrt_pos.2
      have : (0 : ℝ) ≤ max (q : ℝ) 0 := le_max_right _ _
      linarith
  have hzero : IndependentSums.IsBigOWith
      (ShellField.zeroShellLaw M.P).toMeasure (IndependentSums.gammaSigma 2)
      (localCubeControl q)
      (Real.exp 1 * (IndependentSums.gammaMomentConst 2 * localCubeControlGammaScale d q)) :=
    IndependentSums.isBigOWith_gammaSigma_of_hasGammaMomentGrowthWith_of_nonneg
      (μ := (ShellField.zeroShellLaw M.P).toMeasure) (σ := 2) (by norm_num) hMpos
      (fun j => localCubeControl_nonneg q j)
      (hasGammaMomentGrowthWith_localCubeControl_zero M q)
  have hscaled : IndependentSums.IsBigOWith
      (ShellField.zeroShellLaw M.P).toMeasure (IndependentSums.gammaSigma 2) g
      (b * (Real.exp 1 * (IndependentSums.gammaMomentConst 2 * localCubeControlGammaScale d q))) := by
    simpa only [g] using hzero.const_mul hbpos.le
  have hf : Measurable f :=
    (measurable_localCubeControl ell).comp (measurable_pi_apply n)
  have hg : Measurable g := measurable_const.mul (measurable_localCubeControl q)
  have hmap : Measure.map f M.P.toMeasure =
      Measure.map g (ShellField.zeroShellLaw M.P).toMeasure := by
    simpa only [f, g, b, q] using map_localCubeControl_shell_eq_zero M ell n
  have htransport := isBigOWith_gammaSigma_of_map_eq hf hg hmap hscaled
  have hscale : b * (Real.exp 1 *
      (IndependentSums.gammaMomentConst 2 * localCubeControlGammaScale d q)) =
      cutoffGammaMajorant d M.gamma m ell r := by
    have hn : (n : ℝ) = (m : ℝ) - (r : ℝ) := by
      dsimp [n]
      push_cast
      ring
    have hq : (q : ℝ) = (ell : ℝ) - ((m : ℝ) - (r : ℝ)) := by
      dsimp [q, n]
      push_cast
      ring
    unfold cutoffGammaMajorant expectedCubeMajorant cubeMajorant
    unfold localCubeControlGammaScale gaussianMaximumDimConst
    dsimp only [b, q]
    rw [hn, hq]
    ring
  simpa only [f, n, hscale] using htransport

/-- The same individual-shell estimate on the genuine lower-tail sample
carrier.  The subtype law is used only through its exact push-forward to the
canonical shell law. -/
private theorem isBigOWith_gammaSigma_cutoffSample_lowerShell (M : ABKModel d)
    (m ell : ℤ) (r : ℕ) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : CutoffSample d => localCubeControl ell (omega.1 (m - r)))
      (cutoffGammaMajorant d M.gamma m ell r) := by
  let f : ShellSeq d → ℝ := fun omega => localCubeControl ell (omega (m - r))
  let F : CutoffSample d → ℝ := fun omega => localCubeControl ell (omega.1 (m - r))
  have hf : Measurable f :=
    (measurable_localCubeControl ell).comp (measurable_pi_apply (m - r))
  have hF : Measurable F := hf.comp
    (MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).measurable
  have hmap : Measure.map F (cutoffSampleLaw M).toMeasure = Measure.map f M.P.toMeasure := by
    calc
      Measure.map F (cutoffSampleLaw M).toMeasure =
          Measure.map f (Measure.map Subtype.val (cutoffSampleLaw M).toMeasure) := by
        simpa only [F, f, Function.comp_apply] using!
          (Measure.map_map hf
            (MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).measurable).symm
      _ = Measure.map f M.P.toMeasure := by rw [map_cutoffSampleLaw_val]
  exact isBigOWith_gammaSigma_of_map_eq hF hf hmap
    (isBigOWith_gammaSigma_localCubeControl_lowerShell M m ell r)

/-- The actual lower-infinite cutoff local control has a scale-summable
`Γ₂` bound on its public convergence carrier.  This is a countable triangle
over its literal lower shells; it assumes neither shell independence nor a
totalized cutoff outside `CutoffSample`. -/
theorem isBigO_gammaSigma_cutoffLocalControl (M : ABKModel d) (ell m : ℤ) :
    IndependentSums.IsBigO (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2) (cutoffLocalControl ell m)
      (IndependentSums.gammaTriangleConst 2 *
        ∑' r : ℕ, cutoffGammaMajorant d M.gamma m ell r) := by
  let X : ℕ → CutoffSample d → ℝ := fun r omega =>
    localCubeControl ell (omega.1 (m - r))
  let a : ℕ → ℝ := cutoffGammaMajorant d M.gamma m ell
  have ha : ∀ r, 0 < a r := fun r => cutoffGammaMajorant_pos d M.gamma m ell r
  have hasum : Summable a := summable_cutoffGammaMajorant M.shellPrefix.gamma_pos m ell
  have hXm : ∀ r, Measurable (X r) := fun r =>
    (measurable_localCubeControl ell).comp
      ((measurable_pi_apply (m - r)).comp
        (MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).measurable)
  have hX : ∀ r, IndependentSums.IsBigO (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2) (X r) (a r) := by
    intro r
    have hnonneg : ∀ omega, 0 ≤ X r omega := fun omega =>
      localCubeControl_nonneg ell (omega.1 (m - r))
    show IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2) (fun omega => |X r omega|) (a r)
    simpa only [abs_of_nonneg (hnonneg _)] using
      isBigOWith_gammaSigma_cutoffSample_lowerShell M m ell r
  have hsum : ∀ omega, HasSum (fun r => X r omega) (cutoffLocalControl ell m omega) := by
    intro omega
    simpa only [X] using! (summable_cutoffLocalControl ell m omega).hasSum
  simpa only [a] using isBigO_gammaSigma_tsum_of_hasSum
    (μ := (cutoffSampleLaw M).toMeasure) (X := X) (a := a) (S := cutoffLocalControl ell m)
    (σ := 2) (by norm_num) ha hasum hX hXm hsum

/-- Measurability of the genuine cutoff local envelope follows from its
everywhere-convergent partial sums on `CutoffSample`. -/
theorem measurable_cutoffLocalControl (ell m : ℤ) :
    Measurable (cutoffLocalControl (d := d) ell m) := by
  let X : ℕ → CutoffSample d → ℝ := fun r omega =>
    localCubeControl ell (omega.1 (m - r))
  have hXm : ∀ r, Measurable (X r) := fun r =>
    (measurable_localCubeControl ell).comp
      ((measurable_pi_apply (m - r)).comp
        (MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).measurable)
  have hsum : ∀ omega, HasSum (fun r => X r omega) (cutoffLocalControl ell m omega) := by
    intro omega
    simpa only [X] using! (summable_cutoffLocalControl ell m omega).hasSum
  exact measurable_of_tendsto_metrizable
    (fun N => Finset.measurable_sum (Finset.range N) (fun r _ => hXm r))
    (tendsto_pi_nhds.2 fun omega => (hsum omega).tendsto_sum_nat)

/-- Witness-level `Γ₂` moment aggregation for the actual lower cutoff.  The
explicit scale is the summable lower-shell budget multiplied only by
CoarseGraining's documented finite-triangle and tail-to-moment constants. -/
theorem hasGammaMomentGrowthWith_cutoffLocalControl (M : ABKModel d) (ell m : ℤ) :
    IndependentSums.HasGammaMomentGrowthWith (cutoffSampleLaw M).toMeasure 2
      (cutoffLocalControl ell m)
      (IndependentSums.gammaMomentConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          ∑' r : ℕ, cutoffGammaMajorant d M.gamma m ell r)) := by
  let a : ℕ → ℝ := cutoffGammaMajorant d M.gamma m ell
  have ha : ∀ r, 0 < a r := fun r => cutoffGammaMajorant_pos d M.gamma m ell r
  have hasum : Summable a := summable_cutoffGammaMajorant M.shellPrefix.gamma_pos m ell
  have hscale_pos : 0 < IndependentSums.gammaTriangleConst 2 * ∑' r, a r := by
    apply mul_pos IndependentSums.gammaTriangleConst_pos
    exact hasum.tsum_pos (fun r => (ha r).le) 0 (ha 0)
  simpa only [a] using
    IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := (cutoffSampleLaw M).toMeasure) (X := cutoffLocalControl ell m) (σ := 2)
      (K := IndependentSums.gammaTriangleConst 2 * ∑' r, a r)
      (by norm_num) hscale_pos (measurable_cutoffLocalControl ell m).aemeasurable
      (isBigO_gammaSigma_cutoffLocalControl M ell m)

end

end Algsuperdiff.Section3.Cutoff
