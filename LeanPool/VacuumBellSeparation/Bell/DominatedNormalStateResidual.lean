/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.DominatedStateResidual
public import LeanPool.VacuumBellSeparation.Bell.NormalStateMixtures

/-! Normality of an actual positive residual, for arbitrary directed positive
suprema. No GNS representation or normal-state density is postulated. -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite.HC00

open Filter
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem stateFunctional_real_tendsto_of_normal (M : VonNeumannAlgebra H)
    (φ : StateSpace M) (hn : IsNormalFunctional M φ.1)
    {s : Set M.toStarSubalgebra} (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ X ∈ s, 0 ≤ X) {X : M.toStarSubalgebra} (hX : IsLUB s X) :
    Tendsto (fun i : s => (φ.1 i.1).re) atTop (𝓝 (φ.1 X).re) := by
  obtain ⟨p, hp1, he⟩ := φ.2
  have hn' : IsNormalFunctional M p := by
    simpa only [IsNormalFunctional, he] using hn
  simpa only [he] using positiveFunctional_real_tendsto_of_normal M p hn' hs hd hp hX

theorem dominatedStateResidual_isNormal (M : VonNeumannAlgebra H)
    (ω φ : StateSpace M) (hnω : IsNormalFunctional M ω.1)
    (hnφ : IsNormalFunctional M φ.1) {t : ℝ} (ht1 : t < 1)
    (hdom : ∀ T : M.toStarSubalgebra, 0 ≤ T → t • φ.1 T ≤ ω.1 T) :
    IsNormalFunctional M (dominatedStateResidual M ω φ t) := by
  intro s hs hd hp X hX
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  have hlim : Tendsto (fun i : s => (dominatedStateResidual M ω φ t i.1).re) atTop
      (𝓝 (dominatedStateResidual M ω φ t X).re) := by
    simpa only [dominatedStateResidual, smul_apply,
      sub_apply, Complex.smul_re, Complex.sub_re, smul_eq_mul] using
      ((stateFunctional_real_tendsto_of_normal M ω hnω hs hd hp hX).sub
        ((stateFunctional_real_tendsto_of_normal M φ hnφ hs hd hp hX).const_mul t)).const_mul
          (1 - t)⁻¹
  obtain ⟨p, hp1, he⟩ := dominatedStateResidual_isState M ω φ ht1 hdom
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    have hle : (p Y).re ≤ (p X).re :=
      (Complex.le_def.mp (p.monotone' (hX.1 hY))).1
    rw [he Y, he X] at hle
    exact hle
  · intro r hr
    exact le_of_tendsto hlim (Eventually.of_forall fun i : s => hr ⟨i.1, i.2, rfl⟩)

theorem jointBellCorrelation_maximal_normal_of_dominated (A B : VonNeumannAlgebra H)
    (hcomm : Commuting A B) (ω φ : NormalStateSpace (jointAlgebra A B))
    (hmax : jointBellCorrelation A B ω.1 = Real.sqrt 2)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hdom : ∀ T : (jointAlgebra A B).toStarSubalgebra,
      0 ≤ T → t • φ.1 T ≤ ω.1 T) :
    jointBellCorrelation A B φ.1 = Real.sqrt 2 :=
  jointBellCorrelation_maximal_of_dominated A B hcomm ⟨ω.1, ω.2.1⟩ ⟨φ.1, φ.2.1⟩
    hmax ht ht1 hdom

end VacuumBellSeparation.Bipartite.HC00
