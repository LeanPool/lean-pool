/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingSymmetry

/-!
Uniqueness on a fixed source yields conjugation compatibility and angle equivariance.
-/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963
namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ r : ℝ≥0} {M : ℝ}
  (S : AnalyticPhaseFunction n G ρ) (d : GeneratingData S.toFun G (angleStrip n ρ) r M)

include S

theorem conj_generatingTarget {y : ComplexPhaseSpace n}
    (hy : y ∈ generatingTarget G (angleStrip n ρ) r) :
    conjPhase y ∈ generatingTarget G (angleStrip n ρ) r := by
  constructor
  · exact star_mem_erosion S.domain_conj hy.1
  · apply star_mem_erosion (fun q hq => ?_) hy.2
    apply (mem_angleStrip_iff _ _).2
    intro j
    simpa using (mem_angleStrip_iff _ _).1 hq j

omit S in
theorem shift_generatingTarget {y : ComplexPhaseSpace n}
    (hy : y ∈ generatingTarget G (angleStrip n ρ) r) (k : FourierIndex n) :
    phaseShift k y ∈ generatingTarget G (angleStrip n ρ) r :=
  ⟨hy.1, add_mem_erosion (fun q => add_angleShift_mem_iff q k ρ) hy.2⟩

theorem conj_generatingSource {x : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G (angleStrip n ρ) r) :
    conjPhase x ∈ generatingSource G (angleStrip n ρ) r :=
  star_mem_erosion (fun _ hz => conj_mem_phaseDomain S.domain_conj hz) hx

omit S in
theorem shift_generatingSource {x : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G (angleStrip n ρ) r) (k : FourierIndex n) :
    phaseShift k x ∈ generatingSource G (angleStrip n ρ) r := by
  rw [phaseShift_eq_add]
  exact add_mem_erosion (fun z => by
    simpa only [phaseShift_eq_add, phaseDomain] using
      phaseShift_mem_phaseDomain (G := G) (ρ := ρ) k z) hx

include d

theorem gradients_conj_on_source {x : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G (angleStrip n ρ) r) :
    pGradient S.toFun (conjPhase x) = conjVec (pGradient S.toFun x) ∧
      qGradient S.toFun (conjPhase x) = conjVec (qGradient S.toFun x) := by
  exact gradients_conj (S.analytic _ (erosion_subset _ _ hx)) S.conj_compatible
    (mem_of_superset (closedBall_mem_nhds _ (show (0 : ℝ) < r from d.radius_pos))
      (S.conj_generatingSource hx))

theorem input_conj {x : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G (angleStrip n ρ) r) :
    generatingInput S.toFun (conjPhase x) = conjPhase (generatingInput S.toFun x) := by
  have hg := (S.gradients_conj_on_source d hx).1
  change ((conjPhase x).1, (conjPhase x).2 + pGradient S.toFun (conjPhase x)) =
    conjPhase (x.1, x.2 + pGradient S.toFun x)
  rw [hg]
  ext j <;> simp [conjPhase]

theorem output_conj {x : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G (angleStrip n ρ) r) :
    generatingOutput S.toFun (conjPhase x) = conjPhase (generatingOutput S.toFun x) := by
  have hg := (S.gradients_conj_on_source d hx).2
  change ((conjPhase x).1 + qGradient S.toFun (conjPhase x), (conjPhase x).2) =
    conjPhase (x.1 + qGradient S.toFun x, x.2)
  rw [hg]
  ext j <;> simp [conjPhase]

theorem input_shift {x : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G (angleStrip n ρ) r) (k : FourierIndex n) :
    generatingInput S.toFun (phaseShift k x) = phaseShift k (generatingInput S.toFun x) := by
  have hg := (gradients_periodic S d.radius_pos hx k).1
  change (x.1, x.2 + angleShift k + pGradient S.toFun (phaseShift k x)) =
    (x.1, (x.2 + pGradient S.toFun x) + angleShift k)
  rw [hg]
  congr 1
  abel

theorem output_shift {x : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G (angleStrip n ρ) r) (k : FourierIndex n) :
    generatingOutput S.toFun (phaseShift k x) = phaseShift k (generatingOutput S.toFun x) := by
  have hg := (gradients_periodic S d.radius_pos hx k).2
  change (x.1 + qGradient S.toFun (phaseShift k x), x.2 + angleShift k) =
    (x.1 + qGradient S.toFun x, x.2 + angleShift k)
  rw [hg]

theorem generatingInverse_conj {y : ComplexPhaseSpace n}
    (hy : y ∈ generatingTarget G (angleStrip n ρ) r) :
    generatingInverse S.toFun G (angleStrip n ρ) r (conjPhase y) =
      conjPhase (generatingInverse S.toFun G (angleStrip n ρ) r y) := by
  apply d.input_injOn (d.inverse_mem (S.conj_generatingTarget hy))
    (S.conj_generatingSource (d.inverse_mem hy))
  rw [(d.inverse_spec (S.conj_generatingTarget hy)).2.1,
    S.input_conj d (d.inverse_mem hy), (d.inverse_spec hy).2.1]

theorem generatingTransform_conj {y : ComplexPhaseSpace n}
    (hy : y ∈ generatingTarget G (angleStrip n ρ) r) :
    generatingTransform S.toFun G (angleStrip n ρ) r (conjPhase y) =
      conjPhase (generatingTransform S.toFun G (angleStrip n ρ) r y) := by
  unfold generatingTransform
  simp only [Function.comp_apply, S.generatingInverse_conj d hy]
  exact S.output_conj d (d.inverse_mem hy)

theorem generatingInverse_shift {y : ComplexPhaseSpace n}
    (hy : y ∈ generatingTarget G (angleStrip n ρ) r) (k : FourierIndex n) :
    generatingInverse S.toFun G (angleStrip n ρ) r (phaseShift k y) =
      phaseShift k (generatingInverse S.toFun G (angleStrip n ρ) r y) := by
  apply d.input_injOn (d.inverse_mem (shift_generatingTarget hy k))
    (shift_generatingSource (d.inverse_mem hy) k)
  rw [(d.inverse_spec (shift_generatingTarget hy k)).2.1,
    S.input_shift d (d.inverse_mem hy) k, (d.inverse_spec hy).2.1]

theorem generatingTransform_shift {y : ComplexPhaseSpace n}
    (hy : y ∈ generatingTarget G (angleStrip n ρ) r) (k : FourierIndex n) :
    generatingTransform S.toFun G (angleStrip n ρ) r (phaseShift k y) =
      phaseShift k (generatingTransform S.toFun G (angleStrip n ρ) r y) := by
  unfold generatingTransform
  simp only [Function.comp_apply, S.generatingInverse_shift d hy k]
  exact S.output_shift d (d.inverse_mem hy) k

end AnalyticPhaseFunction
end KamProject.Arnold1963
