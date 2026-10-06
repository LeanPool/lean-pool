/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.EssL5UniqueInputs
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionBundle
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionContraction

/-!
# Clauses of the short-time solution

Clauses of `prop:pv-local-solution` for the Duhamel fixed point: besides being
a finite-energy weak solution in `L⁵` of the slab, it lies in `L⁴` of the slab,
its pressure is the canonical pressure `P[U ⊗ U]` of `def:riesz-pressure` (cut
off to the slab), and that pressure lies in `L² ∩ L^{5/2}` of the slab.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Duhamel fixed point of `prop:pv-local-solution` is a finite-energy weak
solution whose pressure is the canonical pressure `P[U ⊗ U]` cut off to the
slab. -/
theorem pvLocalClauses_bundle {a : Vec3 → Vec3} (ha : IsInJ a)
    {σ : ℝ} (hσ : 0 < σ) {U : ParabolicPoint → Vec3}
    (hU5 : MemLp U (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (hU4 : MemLp U (ENNReal.ofReal 4)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (hfix : ∀ z : ParabolicPoint, z.2 ≠ 0 → U z = pvLocalMap a σ U z)
    (hinit : ∀ x : Vec3, U (x, 0) = a x) :
    ∃ DU : ParabolicPoint → Fin 3 → Vec3,
      IsSerrinWeakSolution σ a U DU (pvSlabPressure σ U) :=
  pvLocal_canonical_bundle ha hσ hU5 hU4 hfix hinit

/-- The short-time solution of `prop:pv-local-solution`, with its `L⁴` bound and
its pressure: for every divergence-free datum in `L² ∩ L³` there are `σ > 0`
and a finite-energy weak solution on `ℝ³ × (0, σ)` in `L⁵ ∩ L⁴` of the slab,
whose pressure is the canonical pressure `P[U ⊗ U]` cut off to the slab and
lies in `L² ∩ L^{5/2}` of the slab. -/
theorem pvLocalSolution_clauses {a : Vec3 → Vec3} (ha : IsInJ a)
    (ha3 : MemLp a (ENNReal.ofReal (3 : ℝ)) volume) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ U : ParabolicPoint → Vec3, ∃ DU : ParabolicPoint → Fin 3 → Vec3,
      IsSerrinWeakSolution σ a U DU (pvSlabPressure σ U) ∧
      MemLp U (ENNReal.ofReal 5)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) ∧
      MemLp U (ENNReal.ofReal 4)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) ∧
      MemLp (pvSlabPressure σ U) (ENNReal.ofReal 2) volume ∧
      MemLp (pvSlabPressure σ U) (ENNReal.ofReal (5 / 2)) volume := by
  have ha3' : MemLp a 3 volume := by
    have e3 : ENNReal.ofReal (3 : ℝ) = 3 := by simp
    rw [e3] at ha3
    exact ha3
  obtain ⟨σ, hσ, U, hU5, hU4, hfix, hinit⟩ := pvLocal_fixedPoint ha.1 ha3'
  obtain ⟨DU, hU⟩ := pvLocalClauses_bundle ha hσ hU5 hU4 hfix hinit
  have hT52 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal (5 / 2)) volume :=
    fun i j => (pvSlabTensor_memLp_both hU5 hU4 i j).1
  have hT2 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume :=
    fun i j => (pvSlabTensor_memLp_both hU5 hU4 i j).2
  exact ⟨σ, hσ, U, DU, hU, hU5, hU4, pvSlabPressure_memLp (by norm_num) hT2 hT2,
    pvSlabPressure_memLp (by norm_num) hT2 hT52⟩

end ESS

end
