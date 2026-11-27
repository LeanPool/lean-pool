/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DirectedStrongLimit
public import LeanPool.VacuumBellSeparation.Bell.StrongClosure
public import LeanPool.VacuumBellSeparation.Bell.BipartiteNormalStateDefs

/-!
# Normality of actual vector functionals on concrete von Neumann algebras

Every nonempty directed positive set with a least upper bound is used as
its own index set. The bounded strong limit lies in the original VNA by
the double-commutant closure theorem, and equals that least upper bound.
The resulting normality is order-normality for arbitrary directed sets.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open ContinuousLinearMap Filter
open scoped Topology InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An internal positive directed supremum is the genuine strong limit. -/
theorem strong_tendsto_of_isLUB_positive (M : VonNeumannAlgebra H)
    {s : Set M.toStarSubalgebra} (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ T ∈ s, 0 ≤ T) {X : M.toStarSubalgebra} (hX : IsLUB s X)
    (x : H) :
    Tendsto (fun i : s => (i.1 : H →L[ℂ] H) x) atTop
      (𝓝 ((X : H →L[ℂ] H) x)) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hdir.isDirectedOrder
  let A : s → H →L[ℂ] H := fun i => i.1
  have hmono : Monotone A := fun _ _ h => h
  have hApos (i : s) : 0 ≤ A i := hpos i.1 i.2
  have hAbound (i : s) : A i ≤ (X : H →L[ℂ] H) := hX.1 i.2
  obtain ⟨B, hB, _, hsup⟩ := Gaussian.exists_strongLimit_of_monotone_nonneg_bounded
    A hmono hApos (X : H →L[ℂ] H) hAbound
  have hBM : B ∈ M := mem_vonNeumannAlgebra_of_strong_tendsto M
    (Filter.Eventually.of_forall fun i : s => i.1.2) hB
  have heq : B = (X : H →L[ℂ] H) := by
    apply le_antisymm
    · exact hsup.2 (by rintro _ ⟨i, rfl⟩; exact hAbound i)
    · have hXB : X ≤ (⟨B, hBM⟩ : M.toStarSubalgebra) := hX.2 (by
        intro Y hY
        exact hsup.1 ⟨⟨Y, hY⟩, rfl⟩)
      exact hXB
  simpa only [heq] using hB x

/-- Vector functionals preserve all positive directed suprema, not only sequential limits. -/
theorem vectorFunctional_isNormal (M : VonNeumannAlgebra H) (Ω : H) :
    IsNormalFunctional M (vectorFunctional M Ω) := by
  intro s hs hdir hpos X hX
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hdir.isDirectedOrder
  have ht : Tendsto (fun i : s => (vectorFunctional M Ω i.1).re) atTop
      (𝓝 ((vectorFunctional M Ω X).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner (strong_tendsto_of_isLUB_positive M hs hdir hpos hX Ω))
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    have h := (ContinuousLinearMap.le_def.mp
      (show (Y : H →L[ℂ] H) ≤ (X : H →L[ℂ] H) from hX.1 hY)).re_inner_nonneg_right Ω
    simpa [vectorFunctional, inner_sub_right, sub_nonneg] using h
  · intro r hr
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall fun i : s => hr ⟨i.1, i.2, rfl⟩

/-- The actual positive complex-linear map underlying the vector functional. -/
def vectorPositiveLinearMap (M : VonNeumannAlgebra H) (Ω : H) :
    M.toStarSubalgebra →ₚ[ℂ] ℂ where
  toFun := vectorFunctional M Ω
  map_add' X Y := inner_add_right Ω ((X : H →L[ℂ] H) Ω) ((Y : H →L[ℂ] H) Ω)
  map_smul' c X := by simp [vectorFunctional]
  monotone' := by
    intro X Y hXY
    apply sub_nonneg.mp
    have h := (ContinuousLinearMap.le_def.mp
      (show (X : H →L[ℂ] H) ≤ (Y : H →L[ℂ] H) from hXY)).inner_nonneg_right Ω
    simpa only [vectorFunctional, sub_apply, inner_sub_right] using h

/-- A unit vector induces a normal state on the actual original joint/local algebra. -/
theorem vectorFunctional_isNormalState (M : VonNeumannAlgebra H) (Ω : H)
    (hΩ : ‖Ω‖ = 1) : IsNormalStateFunctional M (vectorFunctional M Ω) := by
  refine ⟨⟨vectorPositiveLinearMap M Ω, ?_, fun _ => rfl⟩,
    vectorFunctional_isNormal M Ω⟩
  change inner ℂ Ω ((1 : H →L[ℂ] H) Ω) = 1
  simp [inner_self_eq_norm_sq_to_K, hΩ]

end VacuumBellSeparation.Bipartite
