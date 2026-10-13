/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenCloserMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationOscillationBridge

/-!
# GammaTenEnvelopeInputGrid

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Besov envelope of Step 2, produced on the whole mesh at once

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`.

## The two obstructions this module removes

`Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput` asks for a
family `Bg` of nonnegative sample functions, **one per mesh cell**, that dominates
every finite-depth positive `q = 2` Besov seminorm of the localized field on
that cell almost surely, lies in `L^4`, and whose **grid** fourth-moment root
is below `cgamma^{15}`.  Two things stand between it and the proved machinery.

1. `Closure.GammaTenEnvelope.exists_besovEnvelope_of_integral_pow_four_le`
   produces an envelope from a **per-cell** fourth-moment bound, but the
   oscillation input of Step 2 is a **grid average**: reading a grid average at
   one cell costs the factor `3^{jd}` and destroys the threshold.  The fix is
   not to read the grid average at a cell at all: the envelope device is run
   simultaneously at every cell of the grid, and the fourth moments are
   compared only after the grid average has been taken.

2. The device needs the family it envelopes to be measurable in the sample, and
   the finite-depth Besov seminorm of the localized field is not known to be.
   The fix is to envelope a **majorant** instead: `oscMajorant`, built from the
   oscillation cells of `e.nablaw.oscillations` through
   `LocalizationFluctuationOscillationBridge.cubeBesovPositiveVectorDepthAverage_le_descendantsAverage_sq`.
   It dominates every finite-depth seminorm, is monotone in the depth cutoff,
   and its measurability and integrability reduce to those of
   `meshOscillationCell`, which are proved.

## What is proved

* `sq_sum_le_sum_two_pow_mul_sq` --- the weighted Cauchy--Schwarz step
  `(sum_i a_i)^2 <= sum_i 2^{i+1} a_i^2`, the elementary replacement for
  Minkowski that the grid average tolerates.
* `sq_descendantsAverage_le` --- Jensen for the descendant average.
* `exists_grid_pathwise_envelope_of_monotone` --- **the grid device**: a
  monotone, measurable, nonnegative family indexed by the grid, whose grid
  average of fourth moments is bounded by a single `C` uniformly in the cutoff,
  admits a measurable pathwise envelope, cell by cell, in `L^4`, with the same
  grid average of fourth moments.
* `oscMajorant`, `oscMajorant_nonneg`, `monotone_oscMajorant`,
  `measurable_oscMajorant` --- the majorant and its three elementary properties.
* `cubeBesovPositiveVectorPartialSeminormTwo_le_oscMajorant` --- the domination,
  the only place the oscillation bridge is used.
* `pow_four_oscMajorant_le` --- **the pointwise fourth-power bound**: weighted
  Cauchy--Schwarz over depths, then Jensen inside each depth, leaving a
  weighted sum over depths of descendant averages of the fourth powers of the
  oscillation cells.
* `integrable_descendantsAverage`, `integral_descendantsAverage`,
  `cubeFamilyAverage_finsetSum` --- the commutations of the sample integral,
  the descendant average and the grid average that carry that pointwise bound
  to the grid average of the fourth moment of the majorant.
* `sum_two_pow_mul_rpow_pow_four_geometric_le` --- the geometric summation of
  the resulting weighted sum.

The fold at a grid family and the composite envelope itself are one step
downstream, in `Closure.GammaTenInteriorFamily`
(`cubeFamilyAverage_integral_pow_four_oscMajorant_le_family` and
`exists_besovEnvelope_of_family_depth_oscillation`), whose per-depth input is
read at the sub-family the consumer actually uses.

## Binders

Measurability and fourth-power integrability of the oscillation cells in the
sample, the `L^2` membership of the field on the mesh cells' descendants, and
the per-depth grid fourth-moment bounds.  The first three are the standing
integrability of the quantities being formed and are conditional A obligations
of this module; the last is `e.lower.bound.oscillations` read at every depth of
the tower.  No smallness gate, no geometry beyond the triadic mesh, and nothing
about the corrector or the coefficient field occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`, `e.nablaw.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]

/-! ## Two elementary inequalities -/

/-- **Weighted Cauchy--Schwarz with summable weights.**  The square of a finite
sum is below the sum of its squares weighted by `2^{i+1}`; the weights are
summable, which is the only property used.  This is the elementary replacement
for Minkowski in `L^2` that survives the grid average unchanged. -/
theorem sq_sum_le_sum_two_pow_mul_sq (n : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, a i) ^ (2 : ℕ) ≤
      ∑ i ∈ Finset.range n, (2 : ℝ) ^ (i + 1) * a i ^ (2 : ℕ) := by
  classical
  have hpos : ∀ i : ℕ, (0 : ℝ) < (2 : ℝ) ^ (i + 1) := fun i => by positivity
  set f : ℕ → ℝ := fun i => (Real.sqrt ((2 : ℝ) ^ (i + 1)))⁻¹ with hf
  set g : ℕ → ℝ := fun i => Real.sqrt ((2 : ℝ) ^ (i + 1)) * a i with hg
  have hfg : ∀ i : ℕ, f i * g i = a i := by
    intro i
    have hs : (0 : ℝ) < Real.sqrt ((2 : ℝ) ^ (i + 1)) := Real.sqrt_pos.2 (hpos i)
    show (Real.sqrt ((2 : ℝ) ^ (i + 1)))⁻¹ * (Real.sqrt ((2 : ℝ) ^ (i + 1)) * a i) = a i
    exact inv_mul_cancel_left₀ (ne_of_gt hs) (a i)
  have hfsq : ∀ i : ℕ, f i ^ (2 : ℕ) = ((2 : ℝ) ^ (i + 1))⁻¹ := by
    intro i
    rw [hf]
    simp only [inv_pow]
    rw [Real.sq_sqrt (hpos i).le]
  have hgsq : ∀ i : ℕ, g i ^ (2 : ℕ) = (2 : ℝ) ^ (i + 1) * a i ^ (2 : ℕ) := by
    intro i
    rw [hg, mul_pow, Real.sq_sqrt (hpos i).le]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) f g
  simp only [hfg, hfsq, hgsq] at hcs
  have hgeom : ∑ i ∈ Finset.range n, ((2 : ℝ) ^ (i + 1))⁻¹ ≤ 1 := by
    have hrw : ∀ i : ℕ, ((2 : ℝ) ^ (i + 1))⁻¹ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i := by
      intro i
      have hhalf : ((1 : ℝ) / 2) ^ i = ((2 : ℝ) ^ i)⁻¹ := by rw [one_div, inv_pow]
      rw [pow_succ, mul_inv, hhalf]
      ring
    calc ∑ i ∈ Finset.range n, ((2 : ℝ) ^ (i + 1))⁻¹
        = (1 / 2 : ℝ) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => hrw i
      _ ≤ (1 / 2 : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (by norm_num)
      _ = 1 := by norm_num
  have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, (2 : ℝ) ^ (i + 1) * a i ^ (2 : ℕ) :=
    Finset.sum_nonneg fun i _ => by positivity
  calc (∑ i ∈ Finset.range n, a i) ^ (2 : ℕ)
      ≤ (∑ i ∈ Finset.range n, ((2 : ℝ) ^ (i + 1))⁻¹) *
          ∑ i ∈ Finset.range n, (2 : ℝ) ^ (i + 1) * a i ^ (2 : ℕ) := hcs
    _ ≤ 1 * ∑ i ∈ Finset.range n, (2 : ℝ) ^ (i + 1) * a i ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hgeom hnn
    _ = ∑ i ∈ Finset.range n, (2 : ℝ) ^ (i + 1) * a i ^ (2 : ℕ) := one_mul _

/-- **Jensen for the descendant average.**  Unconditional. -/
theorem sq_descendantsAverage_le (R : TriadicCube d) (i : ℕ) (F : TriadicCube d → ℝ) :
    (descendantsAverage R i F) ^ (2 : ℕ) ≤
      descendantsAverage R i (fun R' => F R' ^ (2 : ℕ)) := by
  classical
  have hne : (descendantsAtDepth R i).Nonempty := descendantsAtDepth_nonempty R i
  have hcard : (0 : ℝ) < ((descendantsAtDepth R i).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hcheb : (∑ R' ∈ descendantsAtDepth R i, F R') ^ 2 ≤
      ((descendantsAtDepth R i).card : ℝ) * ∑ R' ∈ descendantsAtDepth R i, F R' ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hL : (descendantsAverage R i F) ^ (2 : ℕ) =
      (((descendantsAtDepth R i).card : ℝ))⁻¹ ^ 2 *
        (∑ R' ∈ descendantsAtDepth R i, F R') ^ 2 := by
    unfold descendantsAverage
    ring
  have hR : descendantsAverage R i (fun R' => F R' ^ (2 : ℕ)) =
      (((descendantsAtDepth R i).card : ℝ))⁻¹ *
        ∑ R' ∈ descendantsAtDepth R i, F R' ^ 2 := rfl
  rw [hL, hR]
  have hstep := mul_le_mul_of_nonneg_left hcheb
    (by positivity : (0 : ℝ) ≤ (((descendantsAtDepth R i).card : ℝ))⁻¹ ^ 2)
  refine hstep.trans_eq ?_
  field_simp

/-! ## The grid envelope device -/

/-- **A monotone family indexed by the grid, with a uniform grid fourth moment,
has a pathwise envelope carrying the same grid fourth moment.**

The grid version of
`Closure.GammaTenEnvelope.exists_pathwise_envelope_of_monotone`.  The point is
that the fourth moments are compared only **after** the grid average: no cell
of the grid ever sees the grid average, so the `3^{jd}` of a per-cell reading
never appears.  Monotone convergence is run inside the finite sum over the
grid by `ENNReal.finsetSum_iSup_of_monotone`.

on measurability, nonnegativity and monotonicity of the family, on the standing
integrability `hint` of the moments being formed, and on the uniform grid bound
`hbdd`. -/
theorem exists_grid_pathwise_envelope_of_monotone (mu : Measure Omega)
    (I : Finset (TriadicCube d)) (u : ℕ → TriadicCube d → Omega → ℝ)
    (hmeas : ∀ (N : ℕ), ∀ R ∈ I, Measurable (u N R))
    (hnn : ∀ (N : ℕ) (R : TriadicCube d) (w : Omega), 0 ≤ u N R w)
    (hmono : ∀ (R : TriadicCube d) (w : Omega), Monotone fun N => u N R w)
    (hint : ∀ N : ℕ, ∀ R ∈ I, Integrable (fun w => u N R w ^ (4 : ℕ)) mu)
    {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ N : ℕ, cubeFamilyAverage I (fun R => ∫ w, u N R w ^ (4 : ℕ) ∂mu) ≤ C) :
    ∃ B : TriadicCube d → Omega → ℝ,
      (∀ R w, 0 ≤ B R w) ∧ (∀ R ∈ I, Measurable (B R)) ∧
      (∀ R ∈ I, ∀ᵐ w ∂mu, ∀ N : ℕ, u N R w ≤ B R w) ∧
      (∀ R ∈ I, MemLp (B R) 4 mu) ∧
      cubeFamilyAverage I (fun R => ∫ w, B R w ^ (4 : ℕ) ∂mu) ≤ C := by
  classical
  set V : TriadicCube d → Omega → ℝ≥0∞ :=
    fun R w => ⨆ N, ENNReal.ofReal (u N R w ^ (4 : ℕ)) with hVdef
  set L : ℕ → TriadicCube d → ℝ≥0∞ :=
    fun N R => ∫⁻ w, ENNReal.ofReal (u N R w ^ (4 : ℕ)) ∂mu with hLdef
  have hVmeas : ∀ R ∈ I, Measurable (V R) := fun R hR =>
    Measurable.iSup fun N => ENNReal.measurable_ofReal.comp ((hmeas N R hR).pow_const 4)
  have hLmono : ∀ R, Monotone fun N => L N R := by
    intro R i j hij
    refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ (hnn i R w) (hmono R w hij) 4
  have hVL : ∀ R ∈ I, (∫⁻ w, V R w ∂mu) = ⨆ N, L N R := by
    intro R hR
    rw [hVdef, hLdef]
    exact lintegral_iSup
      (fun N => ENNReal.measurable_ofReal.comp ((hmeas N R hR).pow_const 4))
      (fun i j hij w => ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (hnn i R w) (hmono R w hij) 4))
  have hLofReal : ∀ N : ℕ, ∀ R ∈ I,
      L N R = ENNReal.ofReal (∫ w, u N R w ^ (4 : ℕ) ∂mu) := by
    intro N R hR
    rw [hLdef]
    exact (ofReal_integral_eq_lintegral_ofReal (hint N R hR)
      (Filter.Eventually.of_forall fun w => by positivity)).symm
  have hsumle : ∀ N : ℕ, ∑ R ∈ I, L N R ≤ ENNReal.ofReal ((I.card : ℝ) * C) := by
    intro N
    have hnnint : ∀ R ∈ I, (0 : ℝ) ≤ ∫ w, u N R w ^ (4 : ℕ) ∂mu :=
      fun R _ => integral_nonneg fun w => by positivity
    have hsum : ∑ R ∈ I, (∫ w, u N R w ^ (4 : ℕ) ∂mu) ≤ (I.card : ℝ) * C := by
      have h := hbdd N
      unfold cubeFamilyAverage at h
      rcases Nat.eq_zero_or_pos I.card with hcard | hcard
      · rw [Finset.card_eq_zero.mp hcard]
        simp only [Finset.sum_empty]
        positivity
      · have hcardR : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcard
        have hmul := mul_le_mul_of_nonneg_left h hcardR.le
        rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcardR), one_mul] at hmul
    calc ∑ R ∈ I, L N R = ∑ R ∈ I, ENNReal.ofReal (∫ w, u N R w ^ (4 : ℕ) ∂mu) :=
          Finset.sum_congr rfl fun R hR => hLofReal N R hR
      _ = ENNReal.ofReal (∑ R ∈ I, ∫ w, u N R w ^ (4 : ℕ) ∂mu) :=
          (ENNReal.ofReal_sum_of_nonneg hnnint).symm
      _ ≤ ENNReal.ofReal ((I.card : ℝ) * C) := ENNReal.ofReal_le_ofReal hsum
  have hbig : ∑ R ∈ I, (∫⁻ w, V R w ∂mu) ≤ ENNReal.ofReal ((I.card : ℝ) * C) := by
    have hswap : ∑ R ∈ I, (∫⁻ w, V R w ∂mu) = ⨆ N : ℕ, ∑ R ∈ I, L N R := by
      rw [Finset.sum_congr rfl hVL]
      exact ENNReal.finsetSum_iSup_of_monotone (fun R => hLmono R)
    rw [hswap]
    exact iSup_le hsumle
  have hVfin : ∀ R ∈ I, (∫⁻ w, V R w ∂mu) ≠ ⊤ := by
    intro R hR
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ hbig)
    exact Finset.single_le_sum (f := fun S => ∫⁻ w, V S w ∂mu) (fun S _ => zero_le) hR
  have hfin : ∀ R ∈ I, ∀ᵐ w ∂mu, V R w ≠ ⊤ := by
    intro R hR
    filter_upwards [ae_lt_top (hVmeas R hR) (hVfin R hR)] with w hw
    exact ne_of_lt hw
  have hdom : ∀ R ∈ I, ∀ᵐ w ∂mu, ∀ N : ℕ, u N R w ≤ envelopeSup (fun N => u N R) w := by
    intro R hR
    filter_upwards [hfin R hR] with w hw
    exact fun N => le_envelopeSup_of_ne_top hw (fun N => hnn N R w) N
  have hpt : ∀ R ∈ I, ∀ᵐ w ∂mu,
      ENNReal.ofReal (envelopeSup (fun N => u N R) w ^ (4 : ℕ)) = V R w := by
    intro R hR
    filter_upwards [hfin R hR] with w hw
    rw [pow_envelopeSup (fun N => u N R) w, ENNReal.ofReal_toReal hw]
  have hBpow : ∀ R ∈ I,
      ∫ w, envelopeSup (fun N => u N R) w ^ (4 : ℕ) ∂mu = (∫⁻ w, V R w ∂mu).toReal := by
    intro R hR
    have hBnn : 0 ≤ᵐ[mu] fun w => envelopeSup (fun N => u N R) w ^ (4 : ℕ) :=
      Filter.Eventually.of_forall fun w => by positivity
    have hBmeas : AEStronglyMeasurable
        (fun w => envelopeSup (fun N => u N R) w ^ (4 : ℕ)) mu :=
      ((measurable_envelopeSup (fun N => hmeas N R hR)).pow_const 4).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae hBnn hBmeas, lintegral_congr_ae (hpt R hR)]
  have hBint : ∀ R ∈ I,
      Integrable (fun w => envelopeSup (fun N => u N R) w ^ (4 : ℕ)) mu := by
    intro R hR
    refine ⟨((measurable_envelopeSup (fun N => hmeas N R hR)).pow_const
      4).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w => by positivity),
      lintegral_congr_ae (hpt R hR)]
    exact lt_of_le_of_ne le_top (hVfin R hR)
  refine ⟨fun R => envelopeSup (fun N => u N R), fun R w => envelopeSup_nonneg _ w,
    fun R hR => measurable_envelopeSup (fun N => hmeas N R hR), hdom, ?_, ?_⟩
  · intro R hR
    exact memLp_four_of_integrable_pow_four (fun w => envelopeSup_nonneg _ w)
      ((measurable_envelopeSup (fun N => hmeas N R hR)).aestronglyMeasurable) (hBint R hR)
  · rcases Nat.eq_zero_or_pos I.card with hcard | hcard
    · have hIempty : I = ∅ := Finset.card_eq_zero.mp hcard
      simp only [hIempty, cubeFamilyAverage, Finset.sum_empty, mul_zero]
      exact hC
    · have hcardR : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcard
      have hsumeq : ∑ R ∈ I, (∫ w, envelopeSup (fun N => u N R) w ^ (4 : ℕ) ∂mu) =
          (∑ R ∈ I, (∫⁻ w, V R w ∂mu)).toReal := by
        rw [ENNReal.toReal_sum hVfin]
        exact Finset.sum_congr rfl hBpow
      have hle : (∑ R ∈ I, (∫⁻ w, V R w ∂mu)).toReal ≤ (I.card : ℝ) * C := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbig
        rwa [ENNReal.toReal_ofReal (by positivity)] at h
      unfold cubeFamilyAverage
      rw [hsumeq]
      calc ((I.card : ℝ))⁻¹ * (∑ R ∈ I, (∫⁻ w, V R w ∂mu)).toReal
          ≤ ((I.card : ℝ))⁻¹ * ((I.card : ℝ) * C) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = C := by field_simp

/-! ## The oscillation majorant -/

/-- The square of the majorant: the Besov tower's own weights applied to the
descendant averages of the **squared oscillation cells** of
`e.nablaw.oscillations`, at the scales `base - i`. -/
def oscMajorantSq (base : ℤ) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (R : TriadicCube d) : ℝ :=
  ∑ i ∈ Finset.range (N + 1),
    (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (2 : ℕ) *
      descendantsAverage R i (fun R' => meshOscillationCell (base - (i : ℤ)) u R' ^ (2 : ℕ))

/-- **The oscillation majorant of the finite-depth positive `q = 2` Besov
seminorm.**  It dominates the seminorm by the oscillation bridge, is monotone in
the depth cutoff, and is measurable in the sample as soon as the oscillation
cells are. -/
def oscMajorant (base : ℤ) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (R : TriadicCube d) : ℝ :=
  Real.sqrt (oscMajorantSq base s N u R)

theorem oscMajorantSq_nonneg (base : ℤ) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (R : TriadicCube d) : 0 ≤ oscMajorantSq base s N u R := by
  refine Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) ?_
  exact descendantsAverage_nonneg R i _ fun R' _ => by positivity

theorem oscMajorant_nonneg (base : ℤ) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (R : TriadicCube d) : 0 ≤ oscMajorant base s N u R := Real.sqrt_nonneg _

theorem monotone_oscMajorant (base : ℤ) (s : ℝ) (u : Vec d → Vec d) (R : TriadicCube d) :
    Monotone fun N => oscMajorant base s N u R := by
  intro i j hij
  refine Real.sqrt_le_sqrt ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => ?_
  · exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk) (Nat.succ_le_succ hij))
  · exact mul_nonneg (by positivity)
      (descendantsAverage_nonneg R k _ fun R' _ => by positivity)

/-- Measurability of the majorant in the sample, from measurability of the
oscillation cells alone. -/
theorem measurable_oscMajorant (base : ℤ) (s : ℝ) (N : ℕ) (R : TriadicCube d)
    (U : Omega → Vec d → Vec d)
    (hcell : ∀ i ∈ Finset.range (N + 1), ∀ R' ∈ descendantsAtDepth R i,
      Measurable fun w => meshOscillationCell (base - (i : ℤ)) (U w) R') :
    Measurable fun w => oscMajorant base s N (U w) R := by
  classical
  have hsq : Measurable fun w => oscMajorantSq base s N (U w) R := by
    refine Finset.measurable_sum _ fun i hi => ?_
    have hinner : Measurable fun w =>
        ∑ R' ∈ descendantsAtDepth R i,
          meshOscillationCell (base - (i : ℤ)) (U w) R' ^ (2 : ℕ) :=
      Finset.measurable_sum _ fun R' hR' => ((hcell i hi R' hR').pow_const 2)
    exact (hinner.const_mul _).const_mul _
  exact hsq.sqrt

/-- **The majorant dominates the finite-depth positive `q = 2` Besov seminorm.**

This is the only place `LocalizationFluctuationOscillationBridge` is used: the
depth-`i` term of the tower on `R` is at most the depth-`i` descendant average of
the squared oscillation cells at scale `R.scale - i`.

on the `L^2` memberships on the descendants, the standing integrability of the
quantities being formed. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_le_oscMajorant
    (R : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (hu : ∀ i ∈ Finset.range (N + 1), ∀ R' ∈ descendantsAtDepth R i,
      MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R')) :
    cubeBesovPositiveVectorPartialSeminormTwo R s N u ≤ oscMajorant R.scale s N u R := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo oscMajorant oscMajorantSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => ?_)
  rw [sq_cubeBesovPositiveVectorDepthSeminorm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact cubeBesovPositiveVectorDepthAverage_le_descendantsAverage_sq R u i (hu i hi)

/-- The pointwise fourth-power bound: weighted Cauchy--Schwarz over depths
followed by Jensen inside each depth.  Unconditional. -/
theorem pow_four_oscMajorant_le (base : ℤ) (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (R : TriadicCube d) :
    oscMajorant base s N u R ^ (4 : ℕ) ≤
      ∑ i ∈ Finset.range (N + 1),
        (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) *
          descendantsAverage R i
            (fun R' => meshOscillationCell (base - (i : ℤ)) u R' ^ (4 : ℕ)) := by
  classical
  have hXnn : 0 ≤ oscMajorantSq base s N u R := oscMajorantSq_nonneg base s N u R
  have hpow : oscMajorant base s N u R ^ (4 : ℕ) =
      (oscMajorantSq base s N u R) ^ (2 : ℕ) := by
    unfold oscMajorant
    have h2 : Real.sqrt (oscMajorantSq base s N u R) ^ (2 : ℕ) =
        oscMajorantSq base s N u R := Real.sq_sqrt hXnn
    calc Real.sqrt (oscMajorantSq base s N u R) ^ (4 : ℕ)
        = (Real.sqrt (oscMajorantSq base s N u R) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (oscMajorantSq base s N u R) ^ (2 : ℕ) := by rw [h2]
  rw [hpow]
  refine le_trans (sq_sum_le_sum_two_pow_mul_sq (N + 1)
    (fun i => (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (2 : ℕ) *
      descendantsAverage R i
        (fun R' => meshOscillationCell (base - (i : ℤ)) u R' ^ (2 : ℕ))))
    (Finset.sum_le_sum fun i _ => ?_)
  have hA := sq_descendantsAverage_le R i
    (fun R' => meshOscillationCell (base - (i : ℤ)) u R' ^ (2 : ℕ))
  have hAeq : descendantsAverage R i
      (fun R' => (meshOscillationCell (base - (i : ℤ)) u R' ^ (2 : ℕ)) ^ (2 : ℕ)) =
      descendantsAverage R i
        (fun R' => meshOscillationCell (base - (i : ℤ)) u R' ^ (4 : ℕ)) := by
    refine congrArg (descendantsAverage R i) (funext fun R' => ?_)
    ring
  rw [hAeq] at hA
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) := by
    positivity
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hA hc)
  ring

/-! ## Bookkeeping for the descendant average -/

theorem integrable_descendantsAverage (mu : Measure Omega) (R : TriadicCube d) (i : ℕ)
    (f : TriadicCube d → Omega → ℝ)
    (hf : ∀ R' ∈ descendantsAtDepth R i, Integrable (f R') mu) :
    Integrable (fun w => descendantsAverage R i (fun R' => f R' w)) mu := by
  classical
  have hrw : (fun w => descendantsAverage R i (fun R' => f R' w)) =
      fun w => ((descendantsAtDepth R i).card : ℝ)⁻¹ *
        ∑ R' ∈ descendantsAtDepth R i, f R' w := rfl
  rw [hrw]
  exact (integrable_finsetSum _ hf).const_mul _

theorem integral_descendantsAverage (mu : Measure Omega) (R : TriadicCube d) (i : ℕ)
    (f : TriadicCube d → Omega → ℝ)
    (hf : ∀ R' ∈ descendantsAtDepth R i, Integrable (f R') mu) :
    ∫ w, descendantsAverage R i (fun R' => f R' w) ∂mu =
      descendantsAverage R i (fun R' => ∫ w, f R' w ∂mu) := by
  classical
  have hrw : (fun w => descendantsAverage R i (fun R' => f R' w)) =
      fun w => ((descendantsAtDepth R i).card : ℝ)⁻¹ *
        ∑ R' ∈ descendantsAtDepth R i, f R' w := rfl
  rw [hrw, integral_const_mul, integral_finsetSum _ hf]
  rfl

theorem cubeFamilyAverage_finsetSum (I : Finset (TriadicCube d)) {iota : Type*}
    (s : Finset iota) (F : iota → TriadicCube d → ℝ) :
    cubeFamilyAverage I (fun R => ∑ i ∈ s, F i R) =
      ∑ i ∈ s, cubeFamilyAverage I (F i) := by
  classical
  unfold cubeFamilyAverage
  rw [Finset.sum_comm, Finset.mul_sum]

/-! ## The geometric summation of the fold -/

theorem rpow_three_pow_four_eq (s : ℝ) (i : ℕ) :
    (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) = (Real.rpow (3 : ℝ) (4 * s)) ^ i := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  show ((3 : ℝ) ^ (s * (i : ℝ))) ^ (4 : ℕ) = ((3 : ℝ) ^ (4 * s)) ^ i
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (s * (i : ℝ))) 4, ← Real.rpow_mul h3,
    ← Real.rpow_natCast ((3 : ℝ) ^ (4 * s)) i, ← Real.rpow_mul h3]
  congr 1
  push_cast
  ring

/-- **The fold is summable at a geometric per-depth input.**  If the depth-`i`
grid fourth moment of the oscillation cells is below `A r^i`, and the ratio
`2 . 3^{4 s} r` is below `1/2`, then the weighted sum of the fold is below `4 A`
uniformly in the depth cutoff.  At the closure's own exponent
`s = gammaTenBesovExponent = 1/2` the factor `3^{4 s}` is `9`, so the gate reads
`18 r <= 1/2`, i.e. `r <= 1/36`; the display's own per-depth ratio is `3^{-4}`
once the fourth moment is taken, which is well inside it. -/
theorem sum_two_pow_mul_rpow_pow_four_geometric_le {s A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r)
    (D : ℕ → ℝ) (hD : ∀ i : ℕ, D i ≤ A * r ^ i)
    (hq : 2 * Real.rpow (3 : ℝ) (4 * s) * r ≤ 1 / 2) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1),
      (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) * D i ≤ 4 * A := by
  classical
  set q : ℝ := 2 * Real.rpow (3 : ℝ) (4 * s) * r with hqdef
  have hq0 : (0 : ℝ) ≤ q := by
    rw [hqdef]
    have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (4 * s) := Real.rpow_nonneg (by norm_num) _
    positivity
  have hterm : ∀ i ∈ Finset.range (N + 1),
      (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) * D i ≤
        2 * A * q ^ i := by
    intro i _
    rw [rpow_three_pow_four_eq]
    have hfac : (0 : ℝ) ≤ (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (4 * s)) ^ i := by
      have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (4 * s) := Real.rpow_nonneg (by norm_num) _
      positivity
    refine le_trans (mul_le_mul_of_nonneg_left (hD i) hfac) (le_of_eq ?_)
    rw [hqdef, mul_pow, mul_pow, pow_succ]
    ring
  calc ∑ i ∈ Finset.range (N + 1),
        (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) * D i
      ≤ ∑ i ∈ Finset.range (N + 1), 2 * A * q ^ i := Finset.sum_le_sum hterm
    _ = 2 * A * ∑ i ∈ Finset.range (N + 1), q ^ i := by rw [Finset.mul_sum]
    _ ≤ 2 * A * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hq0 hq i) ?_
        simpa using sum_geometric_two_le (N + 1)
    _ = 4 * A := by ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
