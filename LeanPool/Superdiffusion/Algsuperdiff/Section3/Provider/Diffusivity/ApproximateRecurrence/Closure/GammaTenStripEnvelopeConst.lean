/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripEnvelope

/-!
# GammaTenStripEnvelopeConst

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior-mesh Besov envelope with the depth input carrying a constant

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`, `e.nablaw.oscillations`.

## The gap this module fills

The interior route of `Closure.GammaTenStripEnvelope` reads the per-depth input
at exactly `cgamma^{16} (1+i) 3^{-i}` and returns the grid fourth-moment root
at exactly `cgamma^{15}`, at one and the same `cgamma`.  Both numbers are
rigid, and the consumer of the envelope does not read the depth endpoints at
those numbers:

* the Besov tower the closure's `hosc` is stated at is the tower of the
  **gauged** `bfF_z`, which by
`cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_potential`
  and `..._flux` is a fixed *scalar multiple* of the tower of the raw field; and
* the flux leg's raw field is `neumannFluxField = grad w_N + streamForcing`,
  whose oscillation cell exceeds that of `grad w_N` by the forcing term of
  `Closure.GammaTenInteriorMinkowski.meshOscillationCell_neumannFluxField_le`,
  again a bounded multiple.

Neither multiple can be pushed through the proved statement: rescaling `cgamma`
moves premise and conclusion together (a factor `A >= 1` in the premise costs
`A^{15/16}` in the conclusion, in the wrong direction), so the summation has to
be re-run with the constant carried.  That is all this module does.

## What is proved

* `sum_depth_fold_const_le` --- the depth fold of the interior route with the
  constant `A` carried: a per-depth input `2 (A cgamma^{16} (1+i) 3^{-i})^4`
  folds to `200 A^4 cgamma^{64}`, uniformly in the depth cutoff.  The interior
  route's own fold closes with the numerical step
  `200 cgamma^{64} <= cgamma^{60}`; here that step is **omitted** rather than
  applied, so that the caller chooses the budget.
* `exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const` --- the
  envelope itself: from a per-depth grid fourth-moment root below
  `A cgamma^{16} (1+i) 3^{-i}` and the explicit budget premise
  `200 A^4 cgamma^{64} <= c^4`, a nonnegative sample family `B`, in `L^4` at
  every cell of `interiorMesoCubeGrid d K n outer`, dominating every finite-depth
  positive `q = 2` Besov seminorm of `U` at exponent `gammaTenBesovExponent`
  almost surely, whose grid fourth-moment root is below `c`.

At `A = 1`, `c = cgamma^{15}` and `0 < cgamma <= 1/4` the budget premise reduces
to `200 cgamma^{64} <= cgamma^{60}`, so the interior route's own endpoint is the
special case; nothing is weakened.

## Binders

Those of the proved composite --- the scale bookkeeping `K = n + p`, `outer + 1
= n + g`, `g <= p`, `n <= outer`, the boundary gate `d 3^{g-p} <= 1/2`, the
three cellwise typing binders and the per-depth input --- with the quarter
bound on `cgamma` and its positivity **removed** (the fold no longer performs a
numerical step in `cgamma`) and the two numerical parameters `A`, `c` added,
the second nonnegative and tied to the first by `hbudget`.  Nothing about the
corrector, the coefficient field or the sample space occurs: `U` is an
arbitrary sample-indexed field and `mu` an arbitrary measure.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`, `e.nablaw.oscillations`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]

/-! ## The depth fold with a constant carried -/

/-- **The depth fold of the interior route, with the constant `A` carried.**

The interior route's own fold stops at `cgamma^{60}`, because it applies its
closing numerical step in `cgamma`; here the fold is left at
`200 A^4 cgamma^{64}`, which is what a caller with a constant in the per-depth
input needs.  Unconditional beyond `hD`. -/
theorem sum_depth_fold_const_le {gamma A : ℝ} (D : ℕ → ℝ)
    (hD : ∀ i : ℕ, D i ≤ 2 * (A * (gamma ^ (16 : ℕ) *
      ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))))) ^ (4 : ℕ)) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1),
      (2 : ℝ) ^ (i + 1) *
        (Real.rpow (3 : ℝ) (gammaTenBesovExponent * (i : ℝ))) ^ (4 : ℕ) * D i ≤
      200 * A ^ (4 : ℕ) * gamma ^ (64 : ℕ) := by
  have hA0 : (0 : ℝ) ≤ 50 * A ^ (4 : ℕ) * gamma ^ (64 : ℕ) := by positivity
  have hr0 : (0 : ℝ) ≤ (1 : ℝ) / 36 := by norm_num
  have hDle : ∀ i : ℕ,
      D i ≤ (50 * A ^ (4 : ℕ) * gamma ^ (64 : ℕ)) * ((1 : ℝ) / 36) ^ i := by
    intro i
    refine (hD i).trans ?_
    have hfac : (A * (gamma ^ (16 : ℕ) *
        ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))))) ^ (4 : ℕ) =
        A ^ (4 : ℕ) * gamma ^ (64 : ℕ) *
          ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) ^ (4 : ℕ) := by
      ring
    rw [hfac]
    have hg64 : (0 : ℝ) ≤ A ^ (4 : ℕ) * gamma ^ (64 : ℕ) := by positivity
    have hstep := depth_decay_pow_four_le i
    calc 2 * (A ^ (4 : ℕ) * gamma ^ (64 : ℕ) *
          ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) ^ (4 : ℕ))
        ≤ 2 * (A ^ (4 : ℕ) * gamma ^ (64 : ℕ) * (25 * ((1 : ℝ) / 36) ^ i)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hstep hg64
      _ = (50 * A ^ (4 : ℕ) * gamma ^ (64 : ℕ)) * ((1 : ℝ) / 36) ^ i := by ring
  have hgate : 2 * Real.rpow (3 : ℝ) (4 * gammaTenBesovExponent) * ((1 : ℝ) / 36) ≤
      1 / 2 := by
    have hexp : (4 : ℝ) * gammaTenBesovExponent = 2 := by
      rw [gammaTenBesovExponent]; norm_num
    have h9 : Real.rpow (3 : ℝ) (2 : ℝ) = 9 := by
      have hstep : (3 : ℝ) ^ (2 : ℝ) = (3 : ℝ) ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hval : (3 : ℝ) ^ (2 : ℝ) = 9 := by rw [hstep]; norm_num
      exact hval
    rw [hexp, h9]
    norm_num
  have hsum := sum_two_pow_mul_rpow_pow_four_geometric_le
    (s := gammaTenBesovExponent) hA0 hr0 D hDle hgate N
  refine hsum.trans (le_of_eq ?_)
  ring

/-! ## The composite -/

/-- **The Besov envelope of Step 2 on the interior mesh, from a depth input
carrying a constant.**

The mirror of
`Closure.GammaTenStripEnvelope.exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot`
whose per-depth input is `A cgamma^{16} (1+i) 3^{-i}` and whose conclusion is
the caller's own budget `c`, the two being tied by the explicit numerical
premise `hbudget : 200 A^4 cgamma^{64} <= c^4`.

on the scale bookkeeping, the boundary gate `hsmall`, the budget premise, the
three cellwise typing binders and `hdepth`. -/
theorem exists_besovEnvelope_interiorMesoCubeGrid_of_depth_gridRoot_const
    (mu : Measure Omega) {K n outer : ℤ} {p g : ℕ}
    (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (hno : n ≤ outer)
    (hsmall : (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2)
    (U : Omega → Vec d → Vec d) {gamma A c : ℝ} (hc0 : 0 ≤ c)
    (hbudget : 200 * A ^ (4 : ℕ) * gamma ^ (64 : ℕ) ≤ c ^ (4 : ℕ))
    (hmeascell : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      Measurable fun w => meshOscillationCell (n - (i : ℤ)) (U w) R')
    (hintcell : ∀ i : ℕ, ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      Integrable (fun w => meshOscillationCell (n - (i : ℤ)) (U w) R' ^ (4 : ℕ)) mu)
    (hmem2 : ∀ (w : Omega) (i : ℕ),
      ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1),
      MemLp (U w) (2 : ℝ≥0∞) (normalizedCubeMeasure R'))
    (hdepth : ∀ i : ℕ,
      gridFourthMomentRoot mu (interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1))
          (fun R' w => meshOscillationCell (n - (i : ℤ)) (U w) R') ≤
        A * (gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))))) :
    ∃ B : TriadicCube d → Omega → ℝ,
      (∀ R w, 0 ≤ B R w) ∧
      (∀ R ∈ interiorMesoCubeGrid d K n outer, MemLp (B R) 4 mu) ∧
      gridFourthMomentRoot mu (interiorMesoCubeGrid d K n outer) B ≤ c ∧
      (∀ R ∈ interiorMesoCubeGrid d K n outer, ∀ᵐ w ∂mu, ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N (U w) ≤
          B R w) := by
  classical
  have hnK : n ≤ K := by omega
  have hrefine : ∀ (i : ℕ), ∀ R ∈ interiorMesoCubeGrid d K n outer,
      ∀ R' ∈ descendantsAtDepth R i,
        R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1) :=
    fun i R hR R' hR' => mem_interiorMesoCubeGrid_of_mem_descendantsAtDepth hnK hno hR hR'
  set D : ℕ → ℝ := fun i =>
    2 * (A * (gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))))) ^ (4 : ℕ)
    with hD
  have hDbound : ∀ i : ℕ,
      cubeFamilyAverage (interiorMesoCubeGrid d K n outer) (fun R => descendantsAverage R i
        (fun R' => ∫ w, meshOscillationCell (n - (i : ℤ)) (U w) R' ^ (4 : ℕ) ∂mu)) ≤
      D i := by
    intro i
    refine le_trans (cubeFamilyAverage_descendantsAverage_interiorMesoCubeGrid_le d i hK
      houter hgp hno hsmall _ ?_) ?_
    · intro R' _
      exact integral_nonneg fun w => by positivity
    · rw [hD]
      exact mul_le_mul_of_nonneg_left
        (cubeFamilyAverage_pow_four_le_of_gridFourthMomentRoot_le mu _ _ (hdepth i))
        (by norm_num)
  have hC0 : (0 : ℝ) ≤ c ^ (4 : ℕ) := by positivity
  obtain ⟨B, hB0, hBmem, hBgrid, hBdom⟩ :=
    exists_besovEnvelope_of_family_depth_oscillation mu
      (interiorMesoCubeGrid d K n outer) n gammaTenBesovExponent U
      (fun R hR => scale_eq_of_mem_mesoCubeGrid (interiorMesoCubeGrid_subset hR))
      (fun i R hR R' hR' => hmeascell i R' (hrefine i R hR R' hR'))
      (fun i R hR R' hR' => hintcell i R' (hrefine i R hR R' hR'))
      (fun w i R hR R' hR' => hmem2 w i R' (hrefine i R hR R' hR'))
      D hDbound hC0
      (fun N => le_trans (sum_depth_fold_const_le D (fun i => le_of_eq rfl) N) hbudget)
  refine ⟨B, hB0, hBmem, ?_, hBdom⟩
  have hmom : gridFourthMoment mu (interiorMesoCubeGrid d K n outer) B ≤ c ^ (4 : ℕ) := by
    change cubeFamilyAverage _ (fun R => ∫ w, B R w ^ (4 : ℝ) ∂mu) ≤ _
    have hcongr : (fun R => ∫ w, B R w ^ (4 : ℝ) ∂mu) =
        fun R => ∫ w, B R w ^ (4 : ℕ) ∂mu := by
      funext R
      exact integral_congr_ae (Filter.Eventually.of_forall fun w => rpow_four_eq_pow_four _)
    rw [hcongr]
    exact hBgrid
  exact gridFourthMomentRoot_le_of_le mu _ B hc0 hmom

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
