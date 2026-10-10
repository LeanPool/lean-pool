/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Convergence.Composition
public import LeanPool.ArnoldKAM.Arnold1963.Convergence.SequenceLimit

/-!
Uniform convergence of actual cumulative transformations on their common domain, with
periodicity, real compatibility, and displacement estimates.
-/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- The telescoping limit of the cumulative phase transformations. -/
def limitMap : ComplexPhaseSpace n → ComplexPhaseSpace n :=
  Convergence.sequenceLimit (h.cumulative b)

theorem cumulative_uniform : TendstoUniformlyOn (h.cumulative b) (h.limitMap b) atTop
    (h.limitPhase b) :=
  Convergence.sequenceLimit_tendstoUniformlyOn b.weighted_beta_summable
    (fun s _ hx => h.cumulative_increment b s (h.limitPhase_subset b (s + 1) hx))

theorem limitMap_tail {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b) (s : ℕ) :
    ‖h.limitMap b z - h.cumulative b s z‖ ≤
      ∑' j, (2 : ℝ) ^ (j + s) * beta δ₁ (j + s) :=
  Convergence.sequenceLimit_tail_le b.weighted_beta_summable
    (fun j => h.cumulative_increment b j (h.limitPhase_subset b (j + 1) hz)) s

theorem limitMap_displacement {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b) :
    ‖h.limitMap b z - z‖ < 2 * (beta δ₁ 0 : ℝ) := by
  have hh := h.limitMap_tail b hz 0
  simp only [Nat.add_zero, cumulative] at hh
  exact hh.trans_lt b.weighted_beta_tsum_lt

theorem limitMap_continuous : ContinuousOn (h.limitMap b) (h.limitPhase b) :=
  (h.cumulative_uniform b).continuousOn (Filter.Eventually.frequently
    (Filter.Eventually.of_forall fun s =>
      (h.cumulative_analytic b s).continuousOn.mono (h.limitPhase_subset b s)))

theorem limitMap_maps : MapsTo (h.limitMap b) (h.limitPhase b) (h.phase b 0) := by
  intro z hz
  exact (h.phase_closed b 0).mem_of_tendsto ((h.cumulative_uniform b).tendsto_at hz)
    (Filter.Eventually.of_forall fun s => h.cumulative_maps b s (h.limitPhase_subset b s hz))

theorem limitMap_periodic {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b)
    (k : FourierIndex n) : h.limitMap b (phaseShift k z) = phaseShift k (h.limitMap b z) := by
  have hs := (h.cumulative_uniform b).tendsto_at (h.limitPhase_shift b hz k)
  have ht := ((h.cumulative_uniform b).tendsto_at hz).add_const (0, angleShift k)
  apply tendsto_nhds_unique hs
  convert ht using 1
  · funext s
    exact (h.cumulative_periodic b s z (h.limitPhase_subset b s hz) k).trans
      (phaseShift_eq_add k _)
  · rw [phaseShift_eq_add]

theorem limitMap_real {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b) :
    h.limitMap b (conjPhase z) = conjPhase (h.limitMap b z) := by
  have hs := (h.cumulative_uniform b).tendsto_at (h.limitPhase_conj b hz)
  have ht := ((h.cumulative_uniform b).tendsto_at hz).star
  apply tendsto_nhds_unique hs
  convert ht using 1
  · funext s
    simpa only [conjPhase_eq_star] using h.cumulative_real b s z (h.limitPhase_subset b s hz)
  · rw [conjPhase_eq_star]

theorem limitMap_real_value {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) :
    complexifyPhase (realPartPhase (h.limitMap b (complexifyPhase x))) =
      h.limitMap b (complexifyPhase x) := by
  apply complexifyPhase_realPartPhase_of_conj
  have hz : complexifyPhase x ∈ h.limitPhase b :=
    h.commonPhase_subset b ⟨hx, complexify_mem_angleStrip _ _⟩
  simpa only [conjPhase_complexifyPhase] using (h.limitMap_real b hz).symm

end KamProject.Arnold1963.Iteration.InitialData
