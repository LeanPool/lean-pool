/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Measure.RealSymplectic
public import LeanPool.ArnoldKAM.Arnold1963.Measure.PeriodicProjection
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingTorus

/-!
Physical quotient volume for finite cumulative transformations, using their injectivity.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration.InitialData
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- The cumulative phase transformation restricted to unwrapped real coordinates. -/
def realCumulative (s : ℕ) : RealPhaseCover n → RealPhaseCover n :=
  realPhaseRestriction (h.cumulative b s)

theorem real_mem_phase (s : ℕ) {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) : complexifyPhase x ∈ h.phase b s :=
  h.limitPhase_subset b s (h.commonPhase_subset b ⟨hx, complexify_mem_angleStrip _ _⟩)

theorem realCumulative_continuous (s : ℕ) : ContinuousOn (h.realCumulative b s)
    (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealSpace n))) := by
  intro x hx
  have hd := hasFDerivAt_realPhaseRestriction
    (h.cumulative_analytic b s _ (h.real_mem_phase b s hx.1)).differentiableAt
  exact hd.continuousAt.continuousWithinAt

theorem realCumulative_injOn (s : ℕ) : InjOn (h.realCumulative b s)
    (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealSpace n))) := by
  intro x hx y hy he
  have hh := congrArg complexifyPhase he
  change complexifyPhase (realPhaseRestriction (h.cumulative b s) x) =
    complexifyPhase (realPhaseRestriction (h.cumulative b s) y) at hh
  rw [h.cumulative_realPhase_value b s (h.real_mem_phase b s hx.1),
    h.cumulative_realPhase_value b s (h.real_mem_phase b s hy.1)] at hh
  simpa using congrArg realPartPhase
    (h.cumulative_injOn b s (h.real_mem_phase b s hx.1) (h.real_mem_phase b s hy.1) hh)

theorem realCumulative_shift (s : ℕ) {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) (k : FourierIndex n) :
    h.realCumulative b s (realPhaseShift k x) = realPhaseShift k (h.realCumulative b s x) := by
  change realPartPhase (h.cumulative b s (complexifyPhase (realPhaseShift k x))) = _
  rw [complexifyPhase_shift, h.cumulative_periodic b s _ (h.real_mem_phase b s hx) k]
  exact realPartPhase_shift k _

/-- The limiting real action domain paired with a half-open fundamental angle cell. -/
def retainedCell : Set (RealPhaseCover n) :=
  realSlice (h.limitDomain b) ×ˢ realAngleCell n (2 * Real.pi)

theorem retainedCell_measurable : MeasurableSet (h.retainedCell b) :=
  (measurableSet_realSlice_of_isCompact (h.limit_compact b)).prod
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)

theorem realCumulative_image_projection_injOn (s : ℕ) :
    InjOn torusProjection (h.realCumulative b s '' h.retainedCell b) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
  obtain ⟨k, hk⟩ := (torusProjection_eq_iff _ _).mp he
  rw [← h.realCumulative_shift b s hy.1 k] at hk
  have hxy : x = realPhaseShift k y := h.realCumulative_injOn b s ⟨hx.1, mem_univ _⟩
    (show realPhaseShift k y ∈ realSlice (h.limitDomain b) ×ˢ univ from ⟨hy.1, mem_univ _⟩) hk
  have hproj : torusProjection x = torusProjection y := by
    rw [hxy, torusProjection_shift]
  have heq := torusProjection_injOn_cell ⟨mem_univ _, hx.2⟩ ⟨mem_univ _, hy.2⟩ hproj
  rw [heq]

theorem cumulative_torus_volume (s : ℕ) :
    volume ((torusProjection ∘ h.realCumulative b s) '' h.retainedCell b) =
      volume (h.retainedCell b) := by
  have hsub : h.retainedCell b ⊆ realSlice (h.limitDomain b) ×ˢ (univ : Set (RealSpace n)) :=
    fun _ hx => ⟨hx.1, mem_univ _⟩
  rw [image_comp, torusProjection_volume
    ((h.retainedCell_measurable b).image_of_continuousOn_injOn
      ((h.realCumulative_continuous b s).mono hsub) ((h.realCumulative_injOn b s).mono hsub))
    (h.realCumulative_image_projection_injOn b s)]
  exact h.cumulative_real_volume b s (h.retainedCell_measurable b) (fun _ hx => hx.1)

end KamProject.Arnold1963.Iteration.InitialData
