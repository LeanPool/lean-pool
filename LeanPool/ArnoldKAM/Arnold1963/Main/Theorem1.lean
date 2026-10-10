/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Main.TorusResult
public import LeanPool.ArnoldKAM.Arnold1963.Tori.CrossChart

/-!
Analytic Hamiltonian KAM on the compact domains specified by GlobalHamiltonianData. A common
positive threshold precedes the perturbation. The actual local constructions and cross-chart
orbit-closure argument produce a pairwise disjoint family with a strict measure-loss bound.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963
local instance theorem1PeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- The global KAM partition, measure bounds, realized tori and all-time Hamiltonian
trajectories. -/
structure Theorem1Result (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (G : Set (ComplexSpace n)) (ρ : ℝ≥0) (κ : ℝ)
    (f : AnalyticPhaseFunction n G ρ) where
  /-- The positive output width on which every realized torus lift is analytic. -/
  width : ℝ≥0
  width_pos : 0 < width
  width_le : width ≤ ρ
  /-- The compact positive-measure set covered by the realized invariant tori. -/
  goodSet : Set (RealPhaseSpace n)
  /-- The measurable exceptional set complementary to the good set in the initial phase domain. -/
  badSet : Set (RealPhaseSpace n)
  /-- The family of pairwise disjoint realized invariant tori. -/
  tori : Set (Set (RealPhaseSpace n))
  good_compact : IsCompact goodSet
  good_measurable : MeasurableSet goodSet
  bad_measurable : MeasurableSet badSet
  partition : goodSet ∪ badSet = realSlice G ×ˢ (univ : Set (RealTorus n))
  disjoint_partition : Disjoint goodSet badSet
  good_volume_pos : 0 < volume goodSet
  good_nonempty : goodSet.Nonempty
  good_large : ENNReal.ofReal (1 - κ) *
    volume (realSlice G ×ˢ (univ : Set (RealTorus n))) < volume goodSet
  bad_small : volume badSet < ENNReal.ofReal κ *
    volume (realSlice G ×ˢ (univ : Set (RealTorus n)))
  union_eq : goodSet = ⋃₀ tori
  pairwise_disjoint : tori.Pairwise Disjoint
  realization : ∀ T ∈ tori, Nonempty (KAMTorus n H₀ f.toFun G width κ T)
  global_orbits : ∀ z ∈ goodSet, ∃ γ : ℝ → ComplexPhaseSpace n,
    torusProjection (realPartPhase (γ 0)) = z ∧
    (∀ t, HasDerivAt γ (hamiltonianVectorField (fun w => H₀ w.1 + f.toFun w) (γ t)) t) ∧
    (∀ t, complexifyPhase (realPartPhase (γ t)) = γ t) ∧
    (∀ t, torusProjection (realPartPhase (γ t)) ∈ goodSet)

namespace FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ G ρ κ)

theorem goodSet_volume_gt (hG : IsCompact G) (f : AnalyticPhaseFunction n G ρ)
    (hf : f.uniformNorm ≤ L.threshold) :
    ENNReal.ofReal (1 - κ) * volume L.phase < volume (L.goodSet f hf) := by
  by_cases hκ : κ < 1
  · have hκ0 : 0 ≤ κ := (L.fraction_pos.trans_le L.fraction_le).le
    have hV := L.phase_volume_finite hG
    have hK := ne_top_of_le_ne_top hV (measure_mono (L.goodSet_subset f hf))
    have hκV : ENNReal.ofReal κ * volume L.phase ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV
    have he : ENNReal.ofReal (1 - κ) * volume L.phase +
        ENNReal.ofReal κ * volume L.phase = volume L.phase := by
      rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.mpr hκ.le) hκ0,
        sub_add_cancel, ENNReal.ofReal_one, one_mul]
    have hm := measure_union (μ := volume) (L.partition f hf).2 (L.badSet_measurable hG f hf)
    rw [(L.partition f hf).1] at hm
    apply (ENNReal.add_lt_add_iff_right hκV).mp
    rw [he]
    calc
      volume L.phase = volume (L.goodSet f hf) + volume (L.badSet f hf) := hm
      _ < volume (L.goodSet f hf) + ENNReal.ofReal κ * volume L.phase :=
        ENNReal.add_lt_add_left hK (L.badSet_volume_lt hG f hf)
  · rw [ENNReal.ofReal_of_nonpos (by linarith : 1 - κ ≤ 0), zero_mul]
    exact L.goodSet_volume_pos f hf

/-- The global KAM result assembled from a finite localization and a small perturbation. -/
def theorem1Result (hG : IsCompact G) (f : AnalyticPhaseFunction n G ρ)
    (hf : f.uniformNorm ≤ L.threshold) : Theorem1Result n H₀ G ρ κ f where
  width := L.width / 6
  width_pos := div_pos L.width_pos (by norm_num)
  width_le := (div_le_self (zero_le : 0 ≤ L.width) (by norm_num : (1 : ℝ≥0) ≤ 6)).trans
    L.width_le
  goodSet := L.goodSet f hf
  badSet := L.badSet f hf
  tori := L.tori f hf
  good_compact := L.goodSet_compact f hf
  good_measurable := (L.goodSet_compact f hf).isClosed.measurableSet
  bad_measurable := L.badSet_measurable hG f hf
  partition := (L.partition f hf).1
  disjoint_partition := (L.partition f hf).2
  good_volume_pos := L.goodSet_volume_pos f hf
  good_nonempty := nonempty_of_measure_ne_zero (L.goodSet_volume_pos f hf).ne'
  good_large := L.goodSet_volume_gt hG f hf
  bad_small := L.badSet_volume_lt hG f hf
  union_eq := L.goodSet_eq_sUnion_tori f hf
  pairwise_disjoint := L.tori_pairwise_disjoint f hf
  realization := by
    rintro T ⟨c, p, hp, rfl⟩
    exact ⟨L.torusResult f hf c hp⟩
  global_orbits := fun _ hz => L.exists_global_orbit f hf hz

end FiniteLocalization

theorem theorem1 {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction n G ρ,
      f.uniformNorm ≤ M → Nonempty (Theorem1Result n H₀ G ρ κ f) := by
  obtain ⟨L⟩ := h.exists_finiteLocalization hρ hκ
  exact ⟨L.threshold, L.threshold_pos, fun f hf => ⟨L.theorem1Result h.compact f hf⟩⟩

theorem theorem1_of_pointwise {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction n G ρ,
      (∀ z ∈ phaseDomain G ρ, ‖f.toFun z‖ < M) → Nonempty (Theorem1Result n H₀ G ρ κ f) := by
  obtain ⟨M, hM, hmain⟩ := theorem1 h hρ hκ
  refine ⟨M, hM, fun f hf => hmain f ?_⟩
  exact f.norm_le_iff.mpr ⟨hM.le, fun z hz => (hf z hz).le⟩

end KamProject.Arnold1963
