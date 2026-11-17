/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityMarkApprox

/-!
# Step (finite-sum) predictable integrands

The compensated integral of a finite family of simple predictable integrands, its martingale
property and square-integrability on the natural filtration, together with the covariance
identities for compensated masses of disjoint and of nested space-time sets that underlie the
`L²` isometry.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Step (finite-sum) predictable integrands

The mark-discretised approximant is rank-`>1` in the mark, so it is a finite
`ℝ`-combination of `SimplePredictable` pieces rather than a single one. Its
compensated integral is the sum of the pieces' integrals, and (being a sum of the
per-piece martingales) it is again a martingale on the natural filtration. -/

/-- The compensated integral of a **finite family** of simple predictable
integrands: `∑ⱼ ∫ φⱼ dÑ`. -/
noncomputable def stepIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ j, simpleIntegral N (Φ j) t ω

/-- The step integral vanishes at time `0` (each piece does). -/
lemma stepIntegral_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T) (ω : Ω) :
    stepIntegral N Φ 0 ω = 0 := by
  simp [stepIntegral, simpleIntegral_zero]

/-- A finite family of adapted simple predictables integrates to a martingale on the
natural filtration (the finite sum of the per-piece compensated martingales). -/
lemma martingale_stepIntegral_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T)
    (h_adapt : ∀ j : Fin k, ∀ i : Fin (Φ j).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((Φ j).partition i.castSucc))
        ((Φ j).ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => stepIntegral N Φ t)
      ℱ P := by
  have hfun : (fun t : ℝ => stepIntegral N Φ t)
      = ∑ j : Fin k, (fun t : ℝ => simpleIntegral N (Φ j) t) := by
    funext t ω
    simp only [stepIntegral, Finset.sum_apply]
  rw [hfun]
  have hmart : ∀ s : Finset (Fin k),
      MeasureTheory.Martingale (∑ j ∈ s, fun t : ℝ => simpleIntegral N (Φ j) t)
        ℱ P := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        exact MeasureTheory.martingale_zero ℝ _ P
    | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (martingale_simpleIntegral_compensated N ℱ hℱ (Φ j) (h_adapt j)).add ih
  exact hmart Finset.univ

/-- A finite family of simple predictables integrates to an `L²` function at the
horizon `T` (finite sum of the per-piece `L²` integrals). -/
lemma stepIntegral_memLp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T)
    (h_adapt : ∀ j : Fin k, ∀ i : Fin (Φ j).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((Φ j).partition i.castSucc)) ((Φ j).ξ i)) :
    MeasureTheory.MemLp (fun ω => stepIntegral N Φ T ω) 2 P :=
  MeasureTheory.memLp_finsetSum Finset.univ
    (fun j _ => simpleIntegral_memLp_compensated N ℱ hℱ hT (Φ j) (h_adapt j))

/-- **Disjoint compensated increments are uncorrelated.** For measurable `B, B'`
with finite reference intensity and `Disjoint B B'`, the compensated values
`Ñ(B), Ñ(B')` are independent (Poisson disjoint independence) and mean-zero, so
`E[Ñ(B)·Ñ(B')] = 0`. The bilinear building block for the step-integral isometry.
(The two-set family is indexed by `ULift (Fin 2)` to match the structure-field
universe of `independent_disjoint`.) -/
lemma compensated_cross_disjoint_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hdisj : Disjoint B B') :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P = 0 := by
  -- index the pair by `ULift (Fin 2)` (universe of `independent_disjoint`'s `ι`).
  set G : ULift (Fin 2) → Set (ℝ × E) := fun i => ![B, B'] i.down with hG
  have hmeas : ∀ i, MeasurableSet (G i) := by
    rintro ⟨i⟩; fin_cases i <;> first | exact hB | exact hB'
  have hpair : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    rintro ⟨i⟩ ⟨j⟩ hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hdisj | exact hdisj.symm
  -- `N(·,B)` and `N(·,B')` are independent.
  have hidx : ProbabilityTheory.IndepFun (fun ω => N.N ω B) (fun ω => N.N ω B') P := by
    have h01 : (ULift.up (0 : Fin 2)) ≠ ULift.up (1 : Fin 2) := by
      simp
    have h := (N.independent_disjoint G hmeas hpair).indepFun h01
    simpa [hG] using h
  -- `Ñ(B) = (·.toReal − ν̂(B).toReal) ∘ N(·,B)`, so independence is preserved.
  have hcompeq : (fun ω => N.compensated B ω)
      = (fun x : ℝ≥0∞ => x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
        ∘ (fun ω => N.N ω B) := by funext ω; rfl
  have hcompeq' : (fun ω => N.compensated B' ω)
      = (fun x : ℝ≥0∞ => x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B').toReal)
        ∘ (fun ω => N.N ω B') := by funext ω; rfl
  have hindep : ProbabilityTheory.IndepFun
      (fun ω => N.compensated B ω) (fun ω => N.compensated B' ω) P := by
    rw [hcompeq, hcompeq']
    exact hidx.comp (ENNReal.measurable_toReal.sub_const _)
      (ENNReal.measurable_toReal.sub_const _)
  have hasm : MeasureTheory.AEStronglyMeasurable (fun ω => N.compensated B ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB)).sub_const _).aestronglyMeasurable
  have hasm' : MeasureTheory.AEStronglyMeasurable (fun ω => N.compensated B' ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB')).sub_const _).aestronglyMeasurable
  rw [hindep.integral_fun_mul_eq_mul_integral hasm hasm',
    compensated_mean_zero N hB hfin, zero_mul]

/-- **Second moment of a difference of disjoint compensated increments.** For
measurable disjoint `C, D` with finite intensity,
`E[(Ñ(C) − Ñ(D))²] = ν̂(C).toReal + ν̂(D).toReal` — the cross term drops out by
`compensated_cross_disjoint_zero`, the squares by `compensated_second_moment`.
This is the two-piece isometry for the disjoint-support step-integral route. -/
lemma compensated_diff_sq_disjoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {C D : Set (ℝ × E)} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤)
    (hDf : LevyStochCalc.Poisson.referenceIntensity ν D ≠ ⊤)
    (hdisj : Disjoint C D) :
    ∫ ω, (N.compensated C ω - N.compensated D ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν C).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal := by
  have hCsq := compensated_sq_integrable N hC hCf
  have hDsq := compensated_sq_integrable N hD hDf
  have hCD := compensated_cross_integrable N hC hD hCf hDf
  have h2UV : MeasureTheory.Integrable
      (fun ω => 2 * (N.compensated C ω * N.compensated D ω)) P := hCD.const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => (N.compensated C ω) ^ 2 - 2 * (N.compensated C ω * N.compensated D ω)) P :=
    hCsq.sub h2UV
  have hpt : (fun ω => (N.compensated C ω - N.compensated D ω) ^ 2)
      = (fun ω => (N.compensated C ω) ^ 2
          - 2 * (N.compensated C ω * N.compensated D ω) + (N.compensated D ω) ^ 2) := by
    funext ω; ring
  rw [hpt,
    MeasureTheory.integral_add hmid hDsq,
    MeasureTheory.integral_sub hCsq h2UV,
    MeasureTheory.integral_const_mul,
    compensated_cross_disjoint_zero N hC hD hCf hdisj,
    compensated_second_moment N hC hCf, compensated_second_moment N hD hDf]
  ring

/-- **Compensated additivity over `inter`/`diff`** (a.e.). For measurable `B` with
finite intensity and measurable `C`, `Ñ(B) = Ñ(B ∩ C) + Ñ(B ∖ C)` a.e. (where the
`ℕ`-valued count `N(·,B)` is finite). Measure additivity (`measure_inter_add_diff`)
in `toReal`. -/
lemma compensated_inter_add_diff_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    (fun ω => N.compensated B ω)
      =ᵐ[P] (fun ω => N.compensated (B ∩ C) ω + N.compensated (B \ C) ω) := by
  filter_upwards [N.integer_valued hB hfin] with ω hω
  obtain ⟨n, hn⟩ := hω
  have hBfin : N.N ω B ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
  have hint_ne : N.N ω (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.inter_subset_left)
  have hdiff_ne : N.N ω (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.sdiff_subset)
  have hrefint : LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hrefdiff : LevyStochCalc.Poisson.referenceIntensity ν (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
  rw [show N.N ω B = N.N ω (B ∩ C) + N.N ω (B \ C) from
        (measure_inter_add_sdiff (μ := N.N ω) B hC).symm,
      show LevyStochCalc.Poisson.referenceIntensity ν B
          = LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C)
            + LevyStochCalc.Poisson.referenceIntensity ν (B \ C) from
        (measure_inter_add_sdiff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B hC).symm,
      ENNReal.toReal_add hint_ne hdiff_ne, ENNReal.toReal_add hrefint hrefdiff]
  ring

/-- **Polarisation expansion** of the squared difference: for measurable `B, B'`
with finite intensity, `E[(Ñ(B) − Ñ(B'))²] = ν̂(B).toReal − 2·E[Ñ(B)Ñ(B')] + ν̂(B').toReal`
(squares via `compensated_second_moment`, cross term left symbolic). -/
lemma compensated_diff_sq_expand
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hfin' : LevyStochCalc.Poisson.referenceIntensity ν B' ≠ ⊤) :
    ∫ ω, (N.compensated B ω - N.compensated B' ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal
        - 2 * (∫ ω, N.compensated B ω * N.compensated B' ω ∂P)
        + (LevyStochCalc.Poisson.referenceIntensity ν B').toReal := by
  have hBsq := compensated_sq_integrable N hB hfin
  have hB'sq := compensated_sq_integrable N hB' hfin'
  have hBB' := compensated_cross_integrable N hB hB' hfin hfin'
  have h2 : MeasureTheory.Integrable
      (fun ω => 2 * (N.compensated B ω * N.compensated B' ω)) P := hBB'.const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => (N.compensated B ω) ^ 2 - 2 * (N.compensated B ω * N.compensated B' ω)) P :=
    hBsq.sub h2
  have hpt : (fun ω => (N.compensated B ω - N.compensated B' ω) ^ 2)
      = (fun ω => (N.compensated B ω) ^ 2
          - 2 * (N.compensated B ω * N.compensated B' ω) + (N.compensated B' ω) ^ 2) := by
    funext ω; ring
  rw [hpt, MeasureTheory.integral_add hmid hB'sq,
    MeasureTheory.integral_sub hBsq h2, MeasureTheory.integral_const_mul,
    compensated_second_moment N hB hfin, compensated_second_moment N hB' hfin']

/-- **Bilinear covariance of compensated increments.** For measurable `B, B'` with
finite intensity, `E[Ñ(B)·Ñ(B')] = ν̂(B ∩ B').toReal` — the full polarisation of
`compensated_second_moment`, construction-agnostic (no disjointness). Combines the
`Ñ(B)−Ñ(B') =ᵃᵉ Ñ(B∖B')−Ñ(B'∖B)` decomposition (`compensated_inter_add_diff_ae`),
the disjoint two-piece value (`compensated_diff_sq_disjoint`), the polarisation
expansion (`compensated_diff_sq_expand`), and intensity inclusion–exclusion. -/
lemma compensated_cross_covariance
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hfin' : LevyStochCalc.Poisson.referenceIntensity ν B' ≠ ⊤) :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal := by
  set C := B \ B' with hCdef
  set D := B' \ B with hDdef
  have hCmeas : MeasurableSet C := hB.diff hB'
  have hDmeas : MeasurableSet D := hB'.diff hB
  have hdisj : Disjoint C D := disjoint_sdiff_sdiff
  have hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  have hDf : LevyStochCalc.Poisson.referenceIntensity ν D ≠ ⊤ :=
    ne_top_of_le_ne_top hfin' (measure_mono Set.sdiff_subset)
  have hrefint : LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B') ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  -- a.e. `Ñ(B) − Ñ(B') = Ñ(C) − Ñ(D)`.
  have hsub_ae : (fun ω => N.compensated B ω - N.compensated B' ω)
      =ᵐ[P] (fun ω => N.compensated C ω - N.compensated D ω) := by
    filter_upwards [compensated_inter_add_diff_ae N hB hB' hfin,
      compensated_inter_add_diff_ae N hB' hB hfin'] with ω h1 h2
    rw [h1, h2, Set.inter_comm B' B]; ring
  have hsq_ae : (fun ω => (N.compensated B ω - N.compensated B' ω) ^ 2)
      =ᵐ[P] (fun ω => (N.compensated C ω - N.compensated D ω) ^ 2) :=
    hsub_ae.mono (fun ω h => by
      change (N.compensated B ω - N.compensated B' ω) ^ 2
        = (N.compensated C ω - N.compensated D ω) ^ 2
      rw [show N.compensated B ω - N.compensated B' ω
            = N.compensated C ω - N.compensated D ω from h])
  have hsq_eq : ∫ ω, (N.compensated B ω - N.compensated B' ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν C).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal :=
    (MeasureTheory.integral_congr_ae hsq_ae).trans
      (compensated_diff_sq_disjoint N hCmeas hDmeas hCf hDf hdisj)
  have hexp := compensated_diff_sq_expand N hB hB' hfin hfin'
  -- intensity inclusion–exclusion (in `toReal`).
  have hrefB : (LevyStochCalc.Poisson.referenceIntensity ν B).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν C).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν B
          = LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')
            + LevyStochCalc.Poisson.referenceIntensity ν C from
        (measure_inter_add_sdiff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B hB').symm,
      ENNReal.toReal_add hrefint hCf]
  have hrefB' : (LevyStochCalc.Poisson.referenceIntensity ν B').toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν B'
          = LevyStochCalc.Poisson.referenceIntensity ν (B' ∩ B)
            + LevyStochCalc.Poisson.referenceIntensity ν D from
        (measure_inter_add_sdiff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B' hB).symm,
      Set.inter_comm B' B, ENNReal.toReal_add hrefint hDf]
  rw [hexp] at hsq_eq
  linarith [hsq_eq, hrefB, hrefB']

end LevyStochCalc.Poisson.Compensated
