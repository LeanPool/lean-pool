/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonCompensatedIsometryAdapted

/-!
# The compensated Poisson random measure is an orthogonal martingale measure

The diagonal second moment `𝔼[Ñ(B)²] = ν̂(B)` (`compensated_integral_sq`) is the `C = D` case of the
full **covariance** of the compensated Poisson random measure:

  `𝔼[Ñ(C)·Ñ(D)] = ν̂(C ∩ D)`   for measurable finite-intensity `C, D`.

`Ñ` is thus an *orthogonal martingale measure* with (deterministic) intensity `ν̂`: increments on
disjoint regions are uncorrelated, and the covariance of general increments is the intensity of
their overlap. The proof decomposes `C = (C∩D) ⊔ (C\D)` and `D = (C∩D) ⊔ (D\C)` into three disjoint
pieces whose counts are independent (the independent-scattering field `indep_of_disjoint_region`);
the three disjoint cross-pairs vanish (`integral_mul_compensated_eq_zero`) and the diagonal
`𝔼[Ñ(C∩D)²]` is `ν̂(C∩D)`.

This covariance is the bilinear core the compensated-integral isometry is built on (the jump
analogue of `WienerIntegralL2.covariance_increment_aux`), and the first rung of the Itô–Lévy
integral *operator* (the CLM over the characterised predictable `L²`).

## Provenance

Built on our own `PoissonRandomMeasure` / `PoissonCompensatedIsometryAdapted` (PRM field shape
consulted from `cgarryZA/LevyStochCalc`, Apache-2.0, cited — a rendering of Applebaum 2009 Def.
2.3.1; the proofs are ours). Reference: Applebaum, *Lévy Processes and Stochastic Calculus*, CUP
2009, Thm 4.2.3.

## Main results

* `ae_count_ne_top`: the count `N(·, B)` is almost surely finite when `ν̂ B ≠ ⊤`.
* `compensated_add_of_disjoint`: `Ñ(X ∪ Y) = Ñ(X) + Ñ(Y)` almost surely for disjoint
  finite-intensity `X`, `Y`.
* `compensated_mul_compensated_disjoint`: `𝔼[Ñ(X)·Ñ(Y)] = 0` for disjoint measurable `X`, `Y`
  with `Y` of finite intensity.
* `compensated_covariance`: `𝔼[Ñ(C)·Ñ(D)] = ν̂(C ∩ D)` for measurable finite-intensity `C`, `D`.
* `integral_adapted_bilinear_future`: for `φ` integrable and adapted at `s`, and `C`, `D` in the
  region after `s`, `𝔼[φ·Ñ(C)·Ñ(D)] = 𝔼[φ]·ν̂(C ∩ D)`.
* `integral_bilinear_pairing`: for bounded `φa` adapted at `sa ≤ sb` and `φb` adapted at `sb`,
  `𝔼[φa Ñ((sa, ta] × Aa) · φb Ñ((sb, tb] × Ab)] = 𝔼[φa φb]·ν̂` of the box intersection.

## References

* [Applebaum (2009)][Applebaum2009], Thm 4.2.3
* [*cgarryZA/LevyStochCalc*][LevyStochCalc], cited axiom #6

## Tags

compensated Poisson random measure, orthogonal martingale measure, covariance of Poisson counts,
Lévy process, independent scattering, MSC 60G55, MSC 60G51, MSC 60H05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **Counts are a.e. finite** on finite-intensity sets: `N(·, B)` has law `Poisson(ν̂ B)`, which is
supported on `ℕ ⊂ ℝ≥0∞`, so `⊤` is a null value. -/
theorem ae_count_ne_top (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, N.N ω B ≠ ⊤ := by
  rw [ae_iff]
  have hset : {ω | ¬ N.N ω B ≠ ⊤} = (fun ω => N.N ω B) ⁻¹' {⊤} := by
    ext ω; simp [Set.mem_preimage]
  rw [hset, ← Measure.map_apply (N.measurable_eval hB) (measurableSet_singleton ⊤),
    N.poisson_law hB hfin]
  change poissonMeasureENN (referenceIntensity ν B).toNNReal {⊤} = 0
  unfold poissonMeasureENN
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton ⊤),
    show (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' {(⊤ : ℝ≥0∞)} = ∅ from by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact ENNReal.natCast_ne_top n]
  exact measure_empty

/-- **Additivity of the compensated increment** on disjoint finite-intensity sets:
`Ñ(X ∪ Y) = Ñ(X) + Ñ(Y)` a.e. (count additivity + a.e. finiteness). -/
theorem compensated_add_of_disjoint (N : PoissonRandomMeasure P ν) {X Y : Set (ℝ × E)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hdisj : Disjoint X Y)
    (hXfin : referenceIntensity ν X ≠ ⊤) (hYfin : referenceIntensity ν Y ≠ ⊤) :
    ∀ᵐ ω ∂P, N.compensated (X ∪ Y) ω = N.compensated X ω + N.compensated Y ω := by
  filter_upwards [ae_count_ne_top N hX hXfin, ae_count_ne_top N hY hYfin] with ω hXω hYω
  simp only [PoissonRandomMeasure.compensated]
  rw [measure_union hdisj hY, ENNReal.toReal_add hXω hYω,
    show referenceIntensity ν (X ∪ Y) = referenceIntensity ν X + referenceIntensity ν Y from
      measure_union hdisj hY, ENNReal.toReal_add hXfin hYfin]
  ring

/-- **Uncorrelated on disjoint regions**: `𝔼[Ñ(X)·Ñ(Y)] = 0` for disjoint measurable `X, Y` (finite
`Y`). `Ñ(X)` lives on the region disjoint from `Y`, so `Ñ(X) ⟂ Ñ(Y)`; `Ñ(Y)` is mean-zero. -/
theorem compensated_mul_compensated_disjoint (N : PoissonRandomMeasure P ν) {X Y : Set (ℝ × E)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hdisj : Disjoint X Y)
    (hYfin : referenceIntensity ν Y ≠ ⊤) :
    ∫ ω, N.compensated X ω * N.compensated Y ω ∂P = 0 := by
  refine integral_mul_compensated_eq_zero N hY hYfin ?_
  change Measurable[N.regionSigma Y] fun ω => (N.N ω X).toReal - (referenceIntensity ν X).toReal
  have hc : Measurable[N.regionSigma Y] fun ω => N.N ω X :=
    (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le X ⟨hdisj, hX⟩ le_rfl) le_rfl
  exact hc.ennreal_toReal.sub measurable_const

/-- **The covariance of the compensated Poisson random measure**: `𝔼[Ñ(C)·Ñ(D)] = ν̂(C ∩ D)`. `Ñ` is
an orthogonal martingale measure with intensity `ν̂`. Decompose into the three disjoint pieces
`C∩D`, `C\D`, `D\C`; the three cross-pairs vanish and the diagonal `𝔼[Ñ(C∩D)²]` is `ν̂(C∩D)`. -/
theorem compensated_covariance (N : PoissonRandomMeasure P ν) {C D : Set (ℝ × E)}
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤) :
    ∫ ω, N.compensated C ω * N.compensated D ω ∂P = (referenceIntensity ν (C ∩ D)).toReal := by
  have hIms : MeasurableSet (C ∩ D) := hC.inter hD
  have hC'ms : MeasurableSet (C \ D) := hC.diff hD
  have hD'ms : MeasurableSet (D \ C) := hD.diff hC
  have hIfin : referenceIntensity ν (C ∩ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.inter_subset_left)
  have hC'fin : referenceIntensity ν (C \ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.sdiff_subset)
  have hD'fin : referenceIntensity ν (D \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hIC' : Disjoint (C ∩ D) (C \ D) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.2
  have hID' : Disjoint (C ∩ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  have hC'D' : Disjoint (C \ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  -- a.e. decompositions of the two increments
  have hdC : ∀ᵐ ω ∂P, N.compensated C ω
      = N.compensated (C ∩ D) ω + N.compensated (C \ D) ω := by
    have h := compensated_add_of_disjoint N hIms hC'ms hIC' hIfin hC'fin
    rwa [Set.inter_union_sdiff] at h
  have hdD : ∀ᵐ ω ∂P, N.compensated D ω
      = N.compensated (C ∩ D) ω + N.compensated (D \ C) ω := by
    have h := compensated_add_of_disjoint N hIms hD'ms hID' hIfin hD'fin
    rwa [show (C ∩ D) ∪ (D \ C) =
        D from by rw [Set.inter_comm]; exact Set.inter_union_sdiff D C] at h
  -- L² membership ⇒ integrability of every cross product
  have hL2 : ∀ {S : Set (ℝ × E)}, MeasurableSet S → referenceIntensity ν S ≠ ⊤ →
      MemLp (N.compensated S) 2 P := fun hS hSf => memLp_compensated N hS hSf
  -- expand the product into the four pieces
  have hprod : ∀ᵐ ω ∂P, N.compensated C ω * N.compensated D ω
      = (N.compensated (C ∩ D) ω) ^ 2
        + N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
        + N.compensated (C \ D) ω * N.compensated (C ∩ D) ω
        + N.compensated (C \ D) ω * N.compensated (D \ C) ω := by
    filter_upwards [hdC, hdD] with ω hCω hDω
    rw [hCω, hDω]; ring
  rw [integral_congr_ae hprod]
  have hi1 : Integrable (fun ω => (N.compensated (C ∩ D) ω) ^ 2) P :=
    (hL2 hIms hIfin).integrable_sq
  have hi2 : Integrable (fun ω => N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P :=
    (hL2 hIms hIfin).integrable_mul (hL2 hD'ms hD'fin)
  have hi3 : Integrable (fun ω => N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P :=
    (hL2 hC'ms hC'fin).integrable_mul (hL2 hIms hIfin)
  have hi4 : Integrable (fun ω => N.compensated (C \ D) ω * N.compensated (D \ C) ω) P :=
    (hL2 hC'ms hC'fin).integrable_mul (hL2 hD'ms hD'fin)
  have hf12 : Integrable (fun ω => (N.compensated (C ∩ D) ω) ^ 2
      + N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P := hi1.add hi2
  have hf123 : Integrable (fun ω => (N.compensated (C ∩ D) ω) ^ 2
      + N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
      + N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P := hf12.add hi3
  rw [integral_add hf123 hi4, integral_add hf12 hi3,
    integral_add hi1 hi2, compensated_integral_sq N hIms hIfin,
    compensated_mul_compensated_disjoint N hIms hD'ms hID' hD'fin,
    compensated_mul_compensated_disjoint N hC'ms hIms hIC'.symm hIfin,
    compensated_mul_compensated_disjoint N hC'ms hD'ms hC'D' hD'fin]
  ring

/-! ### Weighted future pairings — the bilinear rung

The covariance above is the `φ ≡ 1` case of a **weighted** future pairing
`𝔼[φ · Ñ(C) · Ñ(D)] = 𝔼[φ] · ν̂(C ∩ D)` for `φ` adapted at a time `s` before both `C, D`
(`C, D ⊆ (s, ∞) × E`). It is the jump analogue of `ItoIsometryAdapted.rect_increment_pairing`
(Brownian rectangles — cited, not reused): the past-adapted weight factors out of every future
increment, and the increment covariance supplies `ν̂(C ∩ D)`. From it, splitting a box at the later
of two start times gives the **overlapping-box bilinear pairing** the Itô–Lévy isometry sums over.

All of it rests on the *single-increment* field `indep_of_disjoint_region` — no past-vs-future
`σ`-algebra independence is assumed. Integrability of the triple products is bought by the same
independence (a past-adapted factor is `⟂` any future increment it multiplies). -/

/-- The past `σ`-algebra `pastFiltration s` sits inside the disjoint-region `σ`-algebra of any
set lying strictly after `s` (`D ⊆ (s, ∞) × E`) — the generalisation of
`pastFiltration_le_regionSigma` from a future box to an arbitrary future set. -/
private lemma pastFiltration_le_regionSigma_sub (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hD : D ⊆ Set.Ioi s ×ˢ Set.univ) :
    N.pastFiltration s ≤ N.regionSigma D := by
  refine iSup₂_le fun C hC => le_iSup₂_of_le C ⟨?_, hC.2⟩ le_rfl
  refine Set.disjoint_of_subset hC.1 hD (Set.disjoint_left.mpr ?_)
  rintro ⟨x, e⟩ hx hxD
  exact absurd (Set.mem_Iic.mp (Set.mem_prod.mp hx).1)
    (not_le.mpr (Set.mem_Ioi.mp (Set.mem_prod.mp hxD).1))

/-- A compensated increment on `p` is measurable for the disjoint-region `σ`-algebra of any set `q`
disjoint from `p`. -/
private lemma compensated_measurable_regionSigma (N : PoissonRandomMeasure P ν)
    {p q : Set (ℝ × E)} (hpq : Disjoint p q) (hpms : MeasurableSet p) :
    Measurable[N.regionSigma q] (N.compensated p) := by
  change Measurable[N.regionSigma q] fun ω => (N.N ω p).toReal - (referenceIntensity ν p).toReal
  have hc : Measurable[N.regionSigma q] fun ω => N.N ω p :=
    (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le p ⟨hpq, hpms⟩ le_rfl) le_rfl
  exact hc.ennreal_toReal.sub measurable_const

/-- **Past-adapted `⟂` future compensated increment (general future set).** For `φ` adapted at `s`
and `D ⊆ (s, ∞) × E`, `φ ⟂ Ñ(D)`. The set-level version of `adapted_indepFun_compensated`. -/
private lemma adapted_indepFun_compensated_sub (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hDms : MeasurableSet D) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    {φ : Ω → ℝ} (hφ : Measurable[N.pastFiltration s] φ) :
    IndepFun φ (N.compensated D) P := by
  have hfield : Indep (N.regionSigma D)
      (MeasurableSpace.comap (fun ω => N.N ω D) inferInstance) P :=
    N.indep_of_disjoint_region hDms
  have hφ_le : MeasurableSpace.comap φ inferInstance ≤ N.regionSigma D :=
    le_trans (measurable_iff_comap_le.mp hφ)
      (pastFiltration_le_regionSigma_sub N hDsub)
  have hraw : IndepFun φ (fun ω => N.N ω D) P :=
    (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_left hfield hφ_le)
  have hcomp := hraw.comp (φ := (id : ℝ → ℝ))
    (ψ := fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν D).toReal)
    measurable_id (by fun_prop)
  simp only [Function.comp_def, id_eq] at hcomp
  exact hcomp

/-- **Weighted diagonal energy (general future set).** For `φ` adapted at `s`, integrable, and
`D ⊆ (s, ∞) × E`, `𝔼[φ · Ñ(D)²] = 𝔼[φ] · ν̂(D)`: `φ ⟂ Ñ(D)²` and `𝔼[Ñ(D)²] = ν̂(D)`. -/
private lemma integral_adapted_mul_compensated_sq_sub (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hDms : MeasurableSet D) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    (hDfin : referenceIntensity ν D ≠ ⊤) {φ : Ω → ℝ} (hφ : Measurable[N.pastFiltration s] φ)
    (hφint : Integrable φ P) :
    ∫ ω, φ ω * (N.compensated D ω) ^ 2 ∂P = (∫ ω, φ ω ∂P) * (referenceIntensity ν D).toReal := by
  rw [(adapted_indepFun_compensated_sub N hDms hDsub hφ).integral_mul_sq
      hφint.aestronglyMeasurable (memLp_compensated N hDms hDfin).aestronglyMeasurable,
    compensated_integral_sq N hDms hDfin]

/-- **The weighted future bilinear pairing** — the covariance carrying a past-adapted weight. For
`φ` adapted at `s` and integrable, and `C, D ⊆ (s, ∞) × E` measurable finite-intensity,

  `𝔼[φ · Ñ(C) · Ñ(D)] = 𝔼[φ] · ν̂(C ∩ D)`.

This is `compensated_covariance` with a weight (`φ ≡ 1` recovers it). Decompose `C, D` into the
three disjoint pieces `C∩D`, `C\D`, `D\C` (all still after `s`); the weighted product expands into
the diagonal `φ · Ñ(C∩D)²` plus three cross pieces `φ · Ñ(p) · Ñ(q)` with `p, q` disjoint. Each
cross piece pairs to zero (`integral_mul_compensated_eq_zero`, the weighted factor `φ · Ñ(p)` being
`regionSigma q`-measurable); the diagonal is `𝔼[φ] · ν̂(C∩D)`
(`integral_adapted_mul_compensated_sq_sub`). Every product is integrable because a past-adapted
factor is independent of the future increment it multiplies. -/
theorem integral_adapted_bilinear_future (N : PoissonRandomMeasure P ν) {s : ℝ}
    {C D : Set (ℝ × E)} (hCms : MeasurableSet C) (hDms : MeasurableSet D)
    (hCsub : C ⊆ Set.Ioi s ×ˢ Set.univ) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤)
    {φ : Ω → ℝ} (hφ : Measurable[N.pastFiltration s] φ) (hφint : Integrable φ P) :
    ∫ ω, φ ω * N.compensated C ω * N.compensated D ω ∂P
      = (∫ ω, φ ω ∂P) * (referenceIntensity ν (C ∩ D)).toReal := by
  -- the three disjoint pieces, all still strictly after `s`
  have hIms : MeasurableSet (C ∩ D) := hCms.inter hDms
  have hC'ms : MeasurableSet (C \ D) := hCms.diff hDms
  have hD'ms : MeasurableSet (D \ C) := hDms.diff hCms
  have hIsub : C ∩ D ⊆ Set.Ioi s ×ˢ Set.univ := Set.inter_subset_left.trans hCsub
  have hC'sub : C \ D ⊆ Set.Ioi s ×ˢ Set.univ := Set.sdiff_subset.trans hCsub
  have hD'sub : D \ C ⊆ Set.Ioi s ×ˢ Set.univ := Set.sdiff_subset.trans hDsub
  have hIfin : referenceIntensity ν (C ∩ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.inter_subset_left)
  have hC'fin : referenceIntensity ν (C \ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.sdiff_subset)
  have hD'fin : referenceIntensity ν (D \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hIC' : Disjoint (C ∩ D) (C \ D) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.2
  have hID' : Disjoint (C ∩ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  have hC'D' : Disjoint (C \ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  -- a.e. decompositions of the two increments
  have hdC : ∀ᵐ ω ∂P, N.compensated C ω
      = N.compensated (C ∩ D) ω + N.compensated (C \ D) ω := by
    have h := compensated_add_of_disjoint N hIms hC'ms hIC' hIfin hC'fin
    rwa [Set.inter_union_sdiff] at h
  have hdD : ∀ᵐ ω ∂P, N.compensated D ω
      = N.compensated (C ∩ D) ω + N.compensated (D \ C) ω := by
    have h := compensated_add_of_disjoint N hIms hD'ms hID' hIfin hD'fin
    rwa [show (C ∩ D) ∪ (D \ C) = D from by
      rw [Set.inter_comm]; exact Set.inter_union_sdiff D C] at h
  -- reusable measurability / integrability shorthands
  have hφreg : ∀ {q : Set (ℝ × E)}, q ⊆ Set.Ioi s ×ˢ Set.univ → Measurable[N.regionSigma q] φ :=
    fun hq => hφ.mono
      (pastFiltration_le_regionSigma_sub N hq) le_rfl
  have hÑint : ∀ {p : Set (ℝ × E)}, MeasurableSet p → referenceIntensity ν p ≠ ⊤ →
      Integrable (N.compensated p) P :=
    fun hp hpf => (memLp_compensated N hp hpf).integrable (by norm_num)
  have hφÑint : ∀ {p : Set (ℝ × E)}, MeasurableSet p → p ⊆ Set.Ioi s ×ˢ Set.univ →
      referenceIntensity ν p ≠ ⊤ → Integrable (fun ω => φ ω * N.compensated p ω) P :=
    fun hp hps hpf =>
      (adapted_indepFun_compensated_sub N hp hps hφ).integrable_mul hφint (hÑint hp hpf)
  -- independence of a weighted disjoint increment from a fresh increment
  have hindep_cross : ∀ {p q : Set (ℝ × E)}, Disjoint p q → MeasurableSet p →
      q ⊆ Set.Ioi s ×ˢ Set.univ → MeasurableSet q →
      IndepFun (fun ω => φ ω * N.compensated p ω) (N.compensated q) P := by
    intro p q hpq hpms hqsub hqms
    have hX : Measurable[N.regionSigma q] (fun ω => φ ω * N.compensated p ω) :=
      (hφreg hqsub).mul (compensated_measurable_regionSigma N hpq hpms)
    have hfield : Indep (N.regionSigma q)
        (MeasurableSpace.comap (fun ω => N.N ω q) inferInstance) P :=
            N.indep_of_disjoint_region hqms
    have hraw : IndepFun (fun ω => φ ω * N.compensated p ω) (fun ω => N.N ω q) P :=
      (IndepFun_iff_Indep _ _ _).mpr
        (indep_of_indep_of_le_left hfield (measurable_iff_comap_le.mp hX))
    have hc := hraw.comp (φ := (id : ℝ → ℝ))
      (ψ := fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν q).toReal) measurable_id (by fun_prop)
    simp only [Function.comp_def, id_eq] at hc
    exact hc
  -- expand the weighted product into diagonal + three cross pieces
  have hprod : ∀ᵐ ω ∂P, φ ω * N.compensated C ω * N.compensated D ω
      = φ ω * (N.compensated (C ∩ D) ω) ^ 2
        + φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
        + φ ω * N.compensated (C \ D) ω * N.compensated (C ∩ D) ω
        + φ ω * N.compensated (C \ D) ω * N.compensated (D \ C) ω := by
    filter_upwards [hdC, hdD] with ω hCω hDω
    rw [hCω, hDω]; ring
  rw [integral_congr_ae hprod]
  -- integrabilities of the four pieces
  have hindepI2 := (adapted_indepFun_compensated_sub N hIms hIsub hφ).comp
    (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2) measurable_id (by fun_prop)
  simp only [Function.comp_def, id_eq] at hindepI2
  have hi1 : Integrable (fun ω => φ ω * (N.compensated (C ∩ D) ω) ^ 2) P :=
    hindepI2.integrable_mul hφint ((memLp_compensated N hIms hIfin).integrable_sq)
  have hi2 : Integrable
      (fun ω => φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P :=
    (hindep_cross hID' hIms hD'sub hD'ms).integrable_mul
      (hφÑint hIms hIsub hIfin) (hÑint hD'ms hD'fin)
  have hi3 : Integrable
      (fun ω => φ ω * N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P :=
    (hindep_cross hIC'.symm hC'ms hIsub hIms).integrable_mul
      (hφÑint hC'ms hC'sub hC'fin) (hÑint hIms hIfin)
  have hi4 : Integrable
      (fun ω => φ ω * N.compensated (C \ D) ω * N.compensated (D \ C) ω) P :=
    (hindep_cross hC'D' hC'ms hD'sub hD'ms).integrable_mul
      (hφÑint hC'ms hC'sub hC'fin) (hÑint hD'ms hD'fin)
  have hf12 : Integrable (fun ω => φ ω * (N.compensated (C ∩ D) ω) ^ 2
      + φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P := hi1.add hi2
  have hf123 : Integrable (fun ω => φ ω * (N.compensated (C ∩ D) ω) ^ 2
      + φ ω * N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
      + φ ω * N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P := hf12.add hi3
  -- the three cross pieces vanish; the diagonal is `𝔼[φ]·ν̂(C∩D)`
  have hX2 : Measurable[N.regionSigma (D \ C)] (fun ω => φ ω * N.compensated (C ∩ D) ω) :=
    (hφreg hD'sub).mul (compensated_measurable_regionSigma N hID' hIms)
  have hX3 : Measurable[N.regionSigma (C ∩ D)] (fun ω => φ ω * N.compensated (C \ D) ω) :=
    (hφreg hIsub).mul (compensated_measurable_regionSigma N hIC'.symm hC'ms)
  have hX4 : Measurable[N.regionSigma (D \ C)] (fun ω => φ ω * N.compensated (C \ D) ω) :=
    (hφreg hD'sub).mul (compensated_measurable_regionSigma N hC'D' hC'ms)
  rw [integral_add hf123 hi4, integral_add hf12 hi3, integral_add hi1 hi2,
    integral_adapted_mul_compensated_sq_sub N hIms hIsub hIfin hφ hφint,
    integral_mul_compensated_eq_zero N hD'ms hD'fin hX2,
    integral_mul_compensated_eq_zero N hIms hIfin hX3,
    integral_mul_compensated_eq_zero N hD'ms hD'fin hX4]
  ring

/-- **The overlapping-box bilinear pairing** — the Itô–Lévy inner-product core. For coefficients
`φa` adapted at `sa`, `φb` adapted at `sb` with `sa ≤ sb`, both bounded,

  `𝔼[(φa · Ñ(boxa)) · (φb · Ñ(boxb))] = 𝔼[φa · φb] · ν̂(boxa ∩ boxb)`,

with `boxa = (sa, ta] × Aa`, `boxb = (sb, tb] × Ab`. The jump analogue of
`ItoIsometryAdapted.rect_increment_pairing` (Brownian rectangles — cited, not reused). Split `boxa`
in time at the later start `sb`: the past part `(-∞, sb]` pairs to zero against the future increment
`Ñ(boxb)` (`integral_mul_compensated_eq_zero`); the future part `(sb, ∞)` starts at `sb` alongside
`boxb`, so the weighted future pairing `integral_adapted_bilinear_future` supplies
`𝔼[φa φb] · ν̂(futPart ∩ boxb)`, and `futPart ∩ boxb = boxa ∩ boxb`. -/
theorem integral_bilinear_pairing (N : PoissonRandomMeasure P ν)
    {sa ta sb tb : ℝ} (hab : sa ≤ sb)
    {Aa Ab : Set E} (hAa : MeasurableSet Aa) (hAb : MeasurableSet Ab)
    (hAafin : ν Aa ≠ ⊤) (hAbfin : ν Ab ≠ ⊤)
    {φa φb : Ω → ℝ} {Ca Cb : ℝ}
    (hφa : Measurable[N.pastFiltration sa] φa) (hφb : Measurable[N.pastFiltration sb] φb)
    (hφaB : ∀ ω, |φa ω| ≤ Ca) (hφbB : ∀ ω, |φb ω| ≤ Cb) :
    ∫ ω, (φa ω * N.compensated (Set.Ioc sa ta ×ˢ Aa) ω)
          * (φb ω * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) ∂P
      = (∫ ω, φa ω * φb ω ∂P)
          * (referenceIntensity ν ((Set.Ioc sa ta ×ˢ Aa) ∩ (Set.Ioc sb tb ×ˢ Ab))).toReal := by
  -- measurability of the boxes and the past / future half-planes at `sb`
  have hboxams : MeasurableSet (Set.Ioc sa ta ×ˢ Aa) := measurableSet_Ioc.prod hAa
  have hboxbms : MeasurableSet (Set.Ioc sb tb ×ˢ Ab) := measurableSet_Ioc.prod hAb
  have hIicms : MeasurableSet (Set.Iic sb ×ˢ (Set.univ : Set E)) :=
    measurableSet_Iic.prod MeasurableSet.univ
  have hIoims : MeasurableSet (Set.Ioi sb ×ˢ (Set.univ : Set E)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hpastms : MeasurableSet (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) :=
    hboxams.inter hIicms
  have hfutms : MeasurableSet (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) :=
    hboxams.inter hIoims
  -- finiteness (the halves are subsets of `boxa`)
  have hboxafin : referenceIntensity ν (Set.Ioc sa ta ×ˢ Aa) ≠ ⊤ :=
    referenceIntensity_box_ne_top hAafin
  have hboxbfin : referenceIntensity ν (Set.Ioc sb tb ×ˢ Ab) ≠ ⊤ :=
    referenceIntensity_box_ne_top hAbfin
  have hpastfin : referenceIntensity ν (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hboxafin (measure_mono Set.inter_subset_left)
  have hfutfin : referenceIntensity ν (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hboxafin (measure_mono Set.inter_subset_left)
  -- geometry: `boxb ⊆` future, past `⟂` future, past `∪` future `= boxa`,
  -- `futPart ∩ boxb = boxa ∩ boxb`
  have hIicIoi : Disjoint (Set.Iic sb ×ˢ (Set.univ : Set E)) (Set.Ioi sb ×ˢ Set.univ) :=
    Set.disjoint_left.mpr fun ⟨x, e⟩ hx hxD =>
      absurd (Set.mem_Iic.mp (Set.mem_prod.mp hx).1)
        (not_le.mpr (Set.mem_Ioi.mp (Set.mem_prod.mp hxD).1))
  have hboxbsub : Set.Ioc sb tb ×ˢ Ab ⊆ Set.Ioi sb ×ˢ Set.univ :=
    Set.prod_mono Set.Ioc_subset_Ioi_self (Set.subset_univ _)
  have hfutsub : Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ) ⊆ Set.Ioi sb ×ˢ Set.univ :=
    Set.inter_subset_right
  have hpastdisjb : Disjoint (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ))
      (Set.Ioc sb tb ×ˢ Ab) :=
    Set.disjoint_of_subset Set.inter_subset_right hboxbsub hIicIoi
  have hdisj_pf : Disjoint (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ))
      (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) :=
    Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right hIicIoi
  have hunion : (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ))
      ∪ (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) = Set.Ioc sa ta ×ˢ Aa := by
    rw [← Set.inter_union_distrib_left, ← Set.union_prod, Set.Iic_union_Ioi,
      Set.univ_prod_univ, Set.inter_univ]
  have hfutinter : (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ∩ (Set.Ioc sb tb ×ˢ Ab)
      = (Set.Ioc sa ta ×ˢ Aa) ∩ (Set.Ioc sb tb ×ˢ Ab) := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hboxbsub]
  -- the weight `φa · φb` is adapted at `sb`, bounded, hence integrable
  have hφ : Measurable[N.pastFiltration sb] (fun ω => φa ω * φb ω) :=
    (hφa.mono (N.pastFiltration.mono hab) le_rfl).mul hφb
  have hbound : ∀ ω, ‖φa ω * φb ω‖ ≤ Ca * Cb := fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hφaB ω) (hφbB ω) (abs_nonneg _) ((abs_nonneg _).trans (hφaB ω))
  have hφint : Integrable (fun ω => φa ω * φb ω) P :=
    (memLp_top_of_bound (hφ.mono (N.pastFiltration.le sb) le_rfl).aestronglyMeasurable (Ca * Cb)
        (ae_of_all _ hbound)).integrable
      le_top
  -- `Ñ(boxa) = Ñ(pastPart) + Ñ(futPart)` a.e.
  have hdecomp : ∀ᵐ ω ∂P, N.compensated (Set.Ioc sa ta ×ˢ Aa) ω
      = N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω
        + N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ω := by
    have h := compensated_add_of_disjoint N hpastms hfutms hdisj_pf hpastfin hfutfin
    rwa [hunion] at h
  -- split the integrand: past term (⟶ 0) + future term (⟶ master pairing)
  have hprod : ∀ᵐ ω ∂P,
      (φa ω * N.compensated (Set.Ioc sa ta ×ˢ Aa) ω)
        * (φb ω * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω)
      = φa ω * φb ω * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω
          * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω
        + φa ω * φb ω * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ω
          * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω := by
    filter_upwards [hdecomp] with ω hω
    rw [hω]; ring
  rw [integral_congr_ae hprod]
  -- integrabilities: bounded weight × (`L²`-increment) × (`L²`-increment)
  have hint_past : Integrable (fun ω => φa ω * φb ω
      * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω
      * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) P :=
    (((memLp_compensated N hpastms hpastfin).integrable_mul
        (memLp_compensated N hboxbms hboxbfin)).bdd_mul
        (hφ.mono (N.pastFiltration.le sb) le_rfl).aestronglyMeasurable (ae_of_all _ hbound)).congr
      (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)
  have hint_fut : Integrable (fun ω => φa ω * φb ω
      * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Ioi sb ×ˢ Set.univ)) ω
      * N.compensated (Set.Ioc sb tb ×ˢ Ab) ω) P :=
    (((memLp_compensated N hfutms hfutfin).integrable_mul
        (memLp_compensated N hboxbms hboxbfin)).bdd_mul
        (hφ.mono (N.pastFiltration.le sb) le_rfl).aestronglyMeasurable (ae_of_all _ hbound)).congr
      (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)
  rw [integral_add hint_past hint_fut]
  -- past term vanishes (weighted past-region factor `⟂` fresh future increment)
  have hXpast : Measurable[N.regionSigma (Set.Ioc sb tb ×ˢ Ab)]
      (fun ω => φa ω * φb ω
        * N.compensated (Set.Ioc sa ta ×ˢ Aa ∩ (Set.Iic sb ×ˢ Set.univ)) ω) :=
    (hφ.mono
      (pastFiltration_le_regionSigma_sub N hboxbsub) le_rfl).mul
      (compensated_measurable_regionSigma N hpastdisjb hpastms)
  rw [integral_mul_compensated_eq_zero N hboxbms hboxbfin hXpast, zero_add,
    integral_adapted_bilinear_future N hfutms hboxbms hfutsub hboxbsub hfutfin hboxbfin hφ hφint,
    hfutinter]

end MathFin
