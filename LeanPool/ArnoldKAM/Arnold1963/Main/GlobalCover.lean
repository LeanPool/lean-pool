/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Main.FiniteLocalization
public import LeanPool.ArnoldKAM.Arnold1963.Measure.FiniteCover

/-!
The union of actual local KAM outputs and a strict global bad-set measure bound. Local
frequency labels retain their chart branches; cross-chart disjointness is proved separately.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

namespace FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ ambient ρ κ)

/-- The initial real action-angle phase set over the ambient action domain. -/
def phase (_L : FiniteLocalization n H₀ ambient ρ κ) : Set (RealPhaseSpace n) :=
  realSlice ambient ×ˢ univ

/-- The union of good sets constructed by the finitely many local iterations. -/
def goodSet (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold) :
    Set (RealPhaseSpace n) := ⋃ c : L.patches, (L.data f hf c).localF1 (L.parameters c)

/-- The complement of the global good set inside the initial real phase set. -/
def badSet (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold) :
    Set (RealPhaseSpace n) := L.phase \ L.goodSet f hf

theorem localPhase_subset (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) (c : L.patches) :
    (L.data f hf c).localPhase ⊆ L.phase := by
  intro z hz
  exact ⟨c.val.subset hz.1, hz.2⟩

theorem goodSet_subset (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold) :
    L.goodSet f hf ⊆ L.phase := by
  intro z hz
  obtain ⟨c, hc⟩ := mem_iUnion.mp hz
  exact L.localPhase_subset f hf c ((L.data f hf c).localF1_subset (L.parameters c) hc)

theorem goodSet_compact (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) : IsCompact (L.goodSet f hf) :=
  isCompact_iUnion fun c => (L.data f hf c).localF1_compact (L.parameters c)

theorem badSet_measurable (hG : IsCompact ambient) (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) : MeasurableSet (L.badSet f hf) :=
  ((isCompact_realSlice hG).isClosed.measurableSet.prod MeasurableSet.univ).diff
    (L.goodSet_compact f hf).isClosed.measurableSet

theorem partition (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold) :
    L.goodSet f hf ∪ L.badSet f hf = L.phase ∧ Disjoint (L.goodSet f hf) (L.badSet f hf) := by
  refine ⟨union_sdiff_cancel (L.goodSet_subset f hf), disjoint_sdiff_right⟩

theorem phase_volume_finite (hG : IsCompact ambient) : volume L.phase ≠ ⊤ := by
  rw [phase, torus_phase_volume]
  have hfin : realVolume ambient ≠ ⊤ := by
    change volume (realSlice ambient) ≠ ⊤
    exact (isCompact_realSlice hG).measure_ne_top
  exact ENNReal.mul_ne_top hfin
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem phase_cover (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold) :
    volume (L.phase \ ⋃ c : L.patches, (L.data f hf c).localPhase) <
      ENNReal.ofReal L.coverError * volume L.phase := by
  classical
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi) ^ n
  have hC : C ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'
  have hCt : C ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hprod (U : Set (RealSpace n)) :
      volume (U ×ˢ (univ : Set (RealTorus n))) = volume U * C := by
    change (volume.prod volume) _ = _
    rw [Measure.prod_prod]
    congr 1
    change (Measure.pi fun _ : Fin n => (volume : Measure (AddCircle (2 * Real.pi)))) univ = _
    simp [C, Measure.pi_univ, AddCircle.measure_univ]
  have hs : L.phase \ ⋃ c : L.patches, (L.data f hf c).localPhase =
      (realSlice ambient \ ⋃ c ∈ L.patches, realSlice c.domain) ×ˢ (univ : Set (RealTorus n)) := by
    ext z
    simp [phase, Iteration.InitialData.localPhase, data, HamiltonianPatch.initialData]
  rw [hs, hprod, phase, hprod, ← mul_assoc]
  simpa only [mul_comm C] using ENNReal.mul_lt_mul_right hC hCt L.cover

theorem badSet_volume_lt (hG : IsCompact ambient) (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) :
    volume (L.badSet f hf) < ENNReal.ofReal κ * volume L.phase := by
  apply measure_complement_finite_union_lt volume L.phase
    (fun c : L.patches => (L.data f hf c).localPhase)
    (fun c => (L.data f hf c).localF1 (L.parameters c))
    L.coverError_pos.le L.fraction_pos.le (L.phase_volume_finite hG) (L.phase_cover f hf)
  · intro c
    exact ((L.data f hf c).localF2_volume_lt (L.parameters c)).le.trans
      (mul_le_mul' le_rfl (measure_mono (L.localPhase_subset f hf c)))
  · simpa using L.budget

theorem goodSet_eq_tori (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) :
    L.goodSet f hf = ⋃ c : L.patches,
      ⋃ ω ∈ (L.data f hf c).retainedRealFrequencies (L.parameters c),
      (L.data f hf c).frequencyTorus (L.parameters c) ω := by
  unfold goodSet
  congr 1
  funext c
  exact (L.data f hf c).localF1_eq_frequency_union (L.parameters c)

theorem goodSet_volume_pos (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) : 0 < volume (L.goodSet f hf) := by
  obtain ⟨c, hc⟩ := L.patches_nonempty
  let j : L.patches := ⟨c, hc⟩
  exact (lt_of_le_of_lt zero_le (L.local_result f hf j).large_measure).trans_le
    (measure_mono (subset_iUnion (fun c => (L.data f hf c).localF1 (L.parameters c)) j))

theorem corrections_small (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) (c : L.patches) {p q : ComplexSpace n}
    (hp : p ∈ (L.data f hf c).limitDomain (L.parameters c))
    (hq : q ∈ Iteration.InitialData.commonAngleStrip n L.width) :
    ‖(L.data f hf c).actionCorrection (L.parameters c) p q‖ < κ ∧
      ‖(L.data f hf c).angleCorrection (L.parameters c) p q‖ < κ := by
  have hh := (L.local_result f hf c).corrections_small p hp q hq
  exact ⟨hh.1.trans_le L.fraction_le, hh.2.trans_le L.fraction_le⟩

theorem orbit_original (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)
    (c : L.patches) {p : RealSpace n}
    (hp : p ∈ realSlice ((L.data f hf c).limitDomain (L.parameters c)))
    (q : RealSpace n) (t : ℝ) :
    HasDerivAt ((L.data f hf c).orbit (L.parameters c) p q)
      (hamiltonianVectorField (fun z => H₀ z.1 + f.toFun z)
        ((L.data f hf c).orbit (L.parameters c) p q t)) t :=
  (L.data f hf c).orbit_hasDerivAt (L.parameters c) hp q t

theorem orbit_mem_goodSet (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) (c : L.patches) {p : RealSpace n}
    (hp : p ∈ realSlice ((L.data f hf c).limitDomain (L.parameters c)))
    (q : RealSpace n) (t : ℝ) :
    torusProjection (realPartPhase ((L.data f hf c).orbit (L.parameters c) p q t)) ∈
      L.goodSet f hf := by
  apply mem_iUnion.mpr
  refine ⟨c, ?_⟩
  rw [(L.data f hf c).localF1_eq_union (L.parameters c)]
  exact mem_iUnion₂.mpr ⟨p, hp, (L.data f hf c).orbit_mem_torus_image (L.parameters c) hp q t⟩

theorem exists_global_orbit (f : AnalyticPhaseFunction n ambient ρ)
    (hf : f.uniformNorm ≤ L.threshold) {z : RealPhaseSpace n} (hz : z ∈ L.goodSet f hf) :
    ∃ γ : ℝ → ComplexPhaseSpace n,
      torusProjection (realPartPhase (γ 0)) = z ∧
      (∀ t, HasDerivAt γ (hamiltonianVectorField (fun w => H₀ w.1 + f.toFun w) (γ t)) t) ∧
      (∀ t, complexifyPhase (realPartPhase (γ t)) = γ t) ∧
      (∀ t, torusProjection (realPartPhase (γ t)) ∈ L.goodSet f hf) := by
  obtain ⟨c, x, hx, rfl⟩ := mem_iUnion.mp hz
  let q := (torusRepresentative x).2
  refine ⟨(L.data f hf c).orbit (L.parameters c) x.1 q, ?_,
    L.orbit_original f hf c hx.1 q,
    (L.data f hf c).orbit_real_value (L.parameters c) hx.1 q,
    L.orbit_mem_goodSet f hf c hx.1 q⟩
  rw [(L.data f hf c).orbit_initial (L.parameters c)]
  rfl

end FiniteLocalization

theorem global_kam_cover {n : ℕ} {H₀ : ComplexSpace n → ℂ}
    {ambient : Set (ComplexSpace n)} (h : GlobalHamiltonianData n H₀ ambient)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ L : FiniteLocalization n H₀ ambient ρ κ,
      ∀ f : AnalyticPhaseFunction n ambient ρ, ∀ hf : f.uniformNorm ≤ L.threshold,
        IsCompact (L.goodSet f hf) ∧
        L.goodSet f hf ∪ L.badSet f hf = L.phase ∧
        Disjoint (L.goodSet f hf) (L.badSet f hf) ∧
        volume (L.badSet f hf) < ENNReal.ofReal κ * volume L.phase ∧
        0 < volume (L.goodSet f hf) ∧
        ∀ c : L.patches, LocalKAMResult (L.parameters c) (L.data f hf c) := by
  obtain ⟨L⟩ := h.exists_finiteLocalization hρ hκ
  exact ⟨L, fun f hf => ⟨L.goodSet_compact f hf, (L.partition f hf).1,
    (L.partition f hf).2, L.badSet_volume_lt h.compact f hf, L.goodSet_volume_pos f hf,
    L.local_result f hf⟩⟩

end KamProject.Arnold1963
