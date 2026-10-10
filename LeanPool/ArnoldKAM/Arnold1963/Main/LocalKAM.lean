/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Tori.Embedding
public import LeanPool.ArnoldKAM.Arnold1963.Tori.Parameterization

/-!
Local analytic invariant tori and the physical measure decomposition within one initial
frequency chart, obtained from the actual infinite iteration.
-/

@[expose] public section
noncomputable section
open Set Function MeasureTheory Topology
open scoped NNReal ENNReal
namespace KamProject.Arnold1963
open Iteration
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- The initial real action-angle phase set of a local iteration. -/
def localPhase : Set (RealPhaseSpace n) := realSlice h.domain ×ˢ univ
/-- The image of the limiting action domain and real torus under the limiting transformation. -/
def localF1 : Set (RealPhaseSpace n) :=
  h.torusLimitMap b '' (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))
/-- The complement of the local good set inside the initial local phase set. -/
def localF2 : Set (RealPhaseSpace n) := h.localPhase \ h.localF1 b

theorem localF1_subset : h.localF1 b ⊆ h.localPhase := (h.torusLimitMap_maps b).image_subset

theorem localF1_eq_union : h.localF1 b =
    ⋃ p ∈ realSlice (h.limitDomain b), h.invariantTorus b p := by
  ext z
  constructor
  · rintro ⟨⟨p, q⟩, hpq, rfl⟩
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hpq.1, ⟨(p, q), ⟨rfl, mem_univ _⟩, rfl⟩⟩⟩
  · intro hz
    rcases mem_iUnion.mp hz with ⟨p, hz⟩
    rcases mem_iUnion.mp hz with ⟨hp, x, hx, rfl⟩
    exact ⟨x, ⟨(show x.1 = p from hx.1) ▸ hp, mem_univ _⟩, rfl⟩

theorem localF1_compact : IsCompact (h.localF1 b) := h.torusLimitMap_image_compact b

theorem local_partition : h.localF1 b ∪ h.localF2 b = h.localPhase ∧
    Disjoint (h.localF1 b) (h.localF2 b) := by
  constructor
  · ext z
    have hs := h.localF1_subset b (a := z)
    change (z ∈ h.localF1 b ∨ z ∈ h.localPhase ∧ z ∉ h.localF1 b) ↔ z ∈ h.localPhase
    tauto
  · exact disjoint_sdiff_right

theorem localPhase_volume_finite : volume h.localPhase ≠ ⊤ := by
  rw [localPhase, torus_phase_volume]
  exact ENNReal.mul_ne_top h.volume_finite (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem localF2_volume_lt : volume (h.localF2 b) < ENNReal.ofReal κ * volume h.localPhase := by
  have hfin := h.localPhase_volume_finite
  have hF1fin := ne_top_of_le_ne_top hfin (measure_mono (h.localF1_subset b))
  have hefin : ENNReal.ofReal κ * volume h.localPhase ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hh := ENNReal.add_lt_add_right hefin (h.torusLimitMap_volume_gt b)
  change ENNReal.ofReal (1 - κ) * volume h.localPhase +
    ENNReal.ofReal κ * volume h.localPhase <
    volume (h.localF1 b) + ENNReal.ofReal κ * volume h.localPhase at hh
  rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.mpr b.fraction_lt_one.le)
    b.fraction_pos.le, sub_add_cancel, ENNReal.ofReal_one, one_mul] at hh
  exact measure_sdiff_lt_of_lt_add (h.localF1_compact b).isClosed.measurableSet.nullMeasurableSet
    (h.localF1_subset b) hF1fin hh

/-- The invariant torus associated with a complex frequency via its real action label. -/
def frequencyTorus (ω : ComplexSpace n) : Set (RealPhaseSpace n) :=
  h.invariantTorus b (h.realFrequencyLabel b ω)

theorem localF1_eq_frequency_union : h.localF1 b =
    ⋃ ω ∈ h.retainedRealFrequencies b, h.frequencyTorus b ω := by
  rw [h.localF1_eq_union b]
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨p, hp, hz⟩
    refine ⟨h.limitFrequency b (complexify p), ⟨complexify p, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
    simpa only [frequencyTorus, realFrequencyLabel, h.frequencyLabel_left b hp,
      realPart_complexify] using hz
  · rintro ⟨ω, hω, hz⟩
    exact ⟨h.realFrequencyLabel b ω, (h.realFrequencyLabel_spec b hω).1, hz⟩

theorem frequencyTorus_disjoint {ω ω' : ComplexSpace n}
    (hω : ω ∈ h.retainedRealFrequencies b) (hω' : ω' ∈ h.retainedRealFrequencies b)
    (hne : ω ≠ ω') : Disjoint (h.frequencyTorus b ω) (h.frequencyTorus b ω') := by
  have hs := h.realFrequencyLabel_spec b hω
  have hs' := h.realFrequencyLabel_spec b hω'
  apply h.invariantTorus_disjoint b hs.1 hs'.1
  intro he
  apply hne
  rw [← hs.2.1, ← hs'.2.1, he]

theorem frequency_orbit {ω : ComplexSpace n} (hω : ω ∈ h.retainedRealFrequencies b)
    (q : RealSpace n) :
    (∀ t : ℝ, h.orbit b (h.realFrequencyLabel b ω) q t =
      h.frequencyParameterization b ω (complexify q + (t : ℂ) • ω)) ∧
    (∀ t : ℝ, HasDerivAt (h.orbit b (h.realFrequencyLabel b ω) q)
      (h.vectorField b 0 (h.orbit b (h.realFrequencyLabel b ω) q t)) t) ∧
    (∀ t : ℝ, torusProjection (realPartPhase (h.orbit b (h.realFrequencyLabel b ω) q t)) ∈
      h.frequencyTorus b ω) ∧
    (∀ k : FourierIndex n, k ≠ 0 → indexPairing k ω ≠ 0) := by
  have hs := h.realFrequencyLabel_spec b hω
  refine ⟨?_, h.orbit_hasDerivAt b hs.1 q, h.orbit_mem_torus_image b hs.1 q, ?_⟩
  · intro t
    unfold orbit frequencyParameterization
    rw [hs.2.1, hs.2.2]
  · intro k hk
    simpa only [hs.2.1] using h.limitFrequency_no_integer_relation b hs.1 k hk

end Iteration.InitialData

/-- The local KAM conclusion, including nonempty limiting domains and disjoint embedded tori. -/
structure LocalKAMResult {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0}
    {κ D : ℝ} (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
    (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D) : Prop where
  nonempty : (realSlice (h.limitDomain b)).Nonempty
  frequency_injective : InjOn (h.limitFrequency b) (h.limitDomain b)
  embedding : ∀ p ∈ realSlice (h.limitDomain b), IsClosedEmbedding (h.torusEmbedding b p)
  analytic_lift : ∀ p ∈ h.limitDomain b,
    AnalyticOnNhd ℂ (fun q => h.limitMap b (p, q)) (InitialData.commonAngleStrip n ρ₀)
  immersion : ∀ p ∈ h.limitDomain b, ∀ q ∈ angleStrip n (ρ₀ / 6),
    Injective (fderiv ℂ (fun q => h.limitMap b (p, q)) q)
  angle_bijective : ∀ p ∈ realSlice (h.limitDomain b), Bijective (h.torusAngleMap b p)
  inverse_analytic : ∀ p ∈ realSlice (h.limitDomain b), ∀ Q : RealSpace n,
    AnalyticAt ℂ (h.complexAngleInverse b (complexify p)) (complexify Q)
  corrections_small : ∀ p ∈ h.limitDomain b, ∀ q ∈ InitialData.commonAngleStrip n ρ₀,
    ‖h.actionCorrection b p q‖ < κ ∧ ‖h.angleCorrection b p q‖ < κ
  disjoint : ∀ p ∈ realSlice (h.limitDomain b), ∀ p' ∈ realSlice (h.limitDomain b), p ≠ p' →
    Disjoint (h.invariantTorus b p) (h.invariantTorus b p')
  invariant_orbits : ∀ p ∈ realSlice (h.limitDomain b), ∀ q : RealSpace n, ∀ t : ℝ,
    HasDerivAt (h.orbit b p q) (h.vectorField b 0 (h.orbit b p q t)) t ∧
    torusProjection (realPartPhase (h.orbit b p q t)) ∈ h.invariantTorus b p
  nonresonance : ∀ p ∈ h.limitDomain b, ∀ k : FourierIndex n, k ≠ 0 →
    indexPairing k (h.limitFrequency b p) ≠ 0
  union_eq : h.localF1 b = ⋃ ω ∈ h.retainedRealFrequencies b, h.frequencyTorus b ω
  compact : IsCompact (h.localF1 b)
  partition : h.localF1 b ∪ h.localF2 b = h.localPhase ∧ Disjoint (h.localF1 b) (h.localF2 b)
  large_measure : ENNReal.ofReal (1 - κ) * volume h.localPhase < volume (h.localF1 b)
  small_complement : volume (h.localF2 b) < ENNReal.ofReal κ * volume h.localPhase

theorem localKAM {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
    (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
    (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D) : LocalKAMResult b h where
  nonempty := h.limit_realSlice_nonempty b
  frequency_injective := h.limitFrequency_injOn b
  embedding := fun _ hp => h.torusEmbedding_isClosedEmbedding b hp
  analytic_lift := fun _ hp => h.limitMap_angle_analytic b hp
  immersion := fun _ hp _ hq => h.torusLift_derivative_injective b hp hq
  angle_bijective := fun _ hp => h.torusAngleMap_bijective b hp
  inverse_analytic := fun _ hp Q => h.complexAngleInverse_analytic_at_real b hp Q
  corrections_small := fun _ hp _ hq => h.torusCorrections_small b hp hq
  disjoint := fun _ hp _ hp' he => h.invariantTorus_disjoint b hp hp' he
  invariant_orbits := fun _ hp q t =>
    ⟨h.orbit_hasDerivAt b hp q t, h.orbit_mem_torus_image b hp q t⟩
  nonresonance := fun _ hp k hk => h.limitFrequency_no_integer_relation b hp k hk
  union_eq := h.localF1_eq_frequency_union b
  compact := h.localF1_compact b
  partition := h.local_partition b
  large_measure := h.torusLimitMap_volume_gt b
  small_complement := h.localF2_volume_lt b

end KamProject.Arnold1963
