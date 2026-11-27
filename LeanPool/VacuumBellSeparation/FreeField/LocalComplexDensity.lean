/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LocalComplexAnnihilator
public import LeanPool.VacuumBellSeparation.FreeField.ComplexSource

/-!
# Dense complex range of actual local source completions

The scalar positive-energy and spatial Fourier argument proved that every
physical complex annihilator of a positive-radius ball is zero. Hilbert-space
orthogonal complementation now yields density of the constructed complex source
map for every region containing such a ball.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped InnerProductSpace

theorem complexSourceMap_denseRange_of_contains_ball {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : Metric.ball x₀ R ⊆ U) :
    DenseRange (complexSourceMap hm U) := by
  let K : Submodule ℂ (Lp ℂ 2 (oneParticleMeasure m)) := (complexSourceMap hm U).range
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff (Kᗮ)).mpr
    intro ψ hψ
    apply eq_zero_of_local_timeZero_complex_annihilator hm hR x₀ ψ
    intro u hu
    apply (K.mem_orthogonal' ψ).mp hψ
    let u' : SourceTestSpace hm U := ⟨u, localizedTimeZeroSources_mono hU hu⟩
    exact ⟨Gaussian.HilbertComplexification.ofReal (u' : SourceHilbert hm U),
      complexSourceMap_ofReal_test hm U u'⟩
  have hK : K.topologicalClosure = ⊤ := K.topologicalClosure_eq_top_iff.mpr horth
  rw [denseRange_iff_closure_range]
  change (K.topologicalClosure : Set (Lp ℂ 2 (oneParticleMeasure m))) = univ
  rw [hK]
  rfl

theorem complexSourceMap_denseRange_of_open {m : ℝ} (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U) (hne : U.Nonempty) :
    DenseRange (complexSourceMap hm U) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  exact complexSourceMap_denseRange_of_contains_ball hm hR x₀ U hball

theorem complexSourceMap_denseRange_ball {m R : ℝ} (hm : 0 < m) (hR : 0 < R)
    (x₀ : EuclideanSpace ℝ (Fin 3)) :
    DenseRange (complexSourceMap hm (Metric.ball x₀ R)) :=
  complexSourceMap_denseRange_of_contains_ball hm hR x₀ _ Subset.rfl

end VacuumBellSeparation
