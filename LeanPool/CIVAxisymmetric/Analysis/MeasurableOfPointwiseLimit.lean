/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
Real-analysis glue for `CIV.IsAdmissibleDrift`'s and `CIV.IsLocallyBoundedOn`'s own measurability
clauses: a pointwise (respectively a.e.-pointwise) limit of measurable, respectively
almost-everywhere strongly measurable, functions is again measurable, respectively almost-everywhere
strongly measurable.
-/

public section

open MeasureTheory Set Filter
open scoped NNReal Topology
open CKN

noncomputable section

namespace CIV



theorem continuous_measurable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {f : α → β} (hf : Continuous f) : Measurable f :=
  hf.measurable

theorem measurable_of_forall_tendsto {m : ℕ} {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    {Bn : ℕ → Vec m × ℝ → β} {B : Vec m × ℝ → β}
    (hBn : ∀ n, Measurable (Bn n))
    (hconv : ∀ z, Tendsto (fun n => Bn n z) atTop (nhds (B z))) :
    Measurable B :=
  measurable_of_tendsto_metrizable' atTop hBn (tendsto_pi_nhds.mpr hconv)

theorem measurable_pair_of_isAdmissibleDrift_of_forall_tendsto {m : ℕ}
    {Bn : ℕ → Vec m × ℝ → Vec m} {B : Vec m × ℝ → Vec m}
    {divBn : ℕ → Vec m × ℝ → ℝ} {divB : Vec m × ℝ → ℝ}
    (hBn : ∀ n, Measurable (Bn n)) (hdivBn : ∀ n, Measurable (divBn n))
    (hconvB : ∀ z, Tendsto (fun n => Bn n z) atTop (nhds (B z)))
    (hconvDiv : ∀ z, Tendsto (fun n => divBn n z) atTop (nhds (divB z))) :
    Measurable B ∧ Measurable divB :=
  ⟨measurable_of_forall_tendsto hBn hconvB, measurable_of_forall_tendsto hdivBn hconvDiv⟩

theorem aestronglyMeasurable_of_forall_ae_tendsto {m : ℕ} {μ : Measure (Vec m × ℝ)}
    {qn : ℕ → Vec m × ℝ → ℝ} {q : Vec m × ℝ → ℝ}
    (hqn : ∀ n, AEStronglyMeasurable (qn n) μ)
    (hconv : ∀ᵐ z ∂μ, Tendsto (fun n => qn n z) atTop (nhds (q z))) :
    AEStronglyMeasurable q μ :=
  aestronglyMeasurable_of_tendsto_ae atTop hqn hconv

theorem aestronglyMeasurable_isLocallyBoundedOn_of_forall_ae_tendsto {m : ℕ} {I : Set ℝ}
    {qn : ℕ → Vec m × ℝ → ℝ} {q : Vec m × ℝ → ℝ}
    (hqn : ∀ n, AEStronglyMeasurable (qn n) (volume.restrict (univ ×ˢ I)))
    (hconv : ∀ᵐ z ∂(volume.restrict (univ ×ˢ I)),
      Tendsto (fun n => qn n z) atTop (nhds (q z))) :
    AEStronglyMeasurable q (volume.restrict (univ ×ˢ I)) :=
  aestronglyMeasurable_of_forall_ae_tendsto hqn hconv

end CIV
