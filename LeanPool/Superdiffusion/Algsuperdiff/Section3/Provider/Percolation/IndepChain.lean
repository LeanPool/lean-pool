/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.ClusterEvent

/-!
# IndepChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Mutual independence from the two-set finite-range hypothesis

ABK26, assumes finite-range independence in a *two-set* form: for each `L ∈ ℕ`
and disjoint `𝒵, 𝒵' ⊆ ℤ^d` at distance greater than `3 ^ L`, the families
`{B_{L'}(z) : z ∈ 𝒵, L' ∈ [0,L]}` and `{B_{L'}(z) : z ∈ 𝒵', L' ∈ [0,L]}` are
independent. Every concentration inequality, however, consumes *mutual*
independence of a whole family, `ProbabilityTheory.iIndepFun`.

This module supplies the bridge. For a family of sites `{z i}` that is pairwise
separated at range `3 ^ L`, the singleton `{z a}` and the union of the remaining
sites are separated, so the two-set hypothesis applies to that pair; iterating
along a `Finset` gives the full product formula defining
`ProbabilityTheory.iIndep`. It is the chain induction of the percolation bound,
run here for an identity rather than for an inequality.

Mathlib's route to `iIndep` from π-systems, `ProbabilityTheory.iIndepSets.iIndep`,
is not usable here: it takes as input the *full* family product formula on
generating π-systems, which is precisely what has to be produced. The chain
induction below is therefore proved directly from `ProbabilityTheory.iIndep_iff`.

## Main results

* `Algsuperdiff.Section3.Provider.Percolation.iIndepFun_of_measurable_siteSigma`:
  random variables measurable with respect to the localised σ-algebras of a
  pairwise-separated family of sites are mutually independent, in the
  hypothesis format the concentration inequality consumes.

## References

* ABK26, Lemma `l.percolation.bound.general`, hypothesis (ii).
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}


/-- The chain induction: the product formula for a `Finset` of
pairwise-separated sites. -/
private theorem meas_biInter_eq_prod [IsProbabilityMeasure μ] {ι : Type*}
    {B : ℕ → (Fin d → ℤ) → Set Ω} {L : ℕ} {z : ι → Fin d → ℤ}
    (hindep : ∀ S S' : Set (Fin d → ℤ), (∀ u ∈ S, ∀ v ∈ S', 3 ^ L < latDist u v) →
      Indep (siteSigma B S L) (siteSigma B S' L) μ)
    (hsep : ∀ i j : ι, i ≠ j → 3 ^ L < latDist (z i) (z j)) :
    ∀ (s : Finset ι) (f : ι → Set Ω),
      (∀ i, i ∈ s → MeasurableSet[siteSigma B ({z i} : Set (Fin d → ℤ)) L] (f i)) →
      μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | insert a s ha ih =>
      intro f hf
      have hA : MeasurableSet[siteSigma B ({z a} : Set (Fin d → ℤ)) L] (f a) :=
        hf a (Finset.mem_insert_self a s)
      have hC : MeasurableSet[siteSigma B
          (⋃ i ∈ (s : Set ι), ({z i} : Set (Fin d → ℤ))) L] (⋂ i ∈ s, f i) := by
        refine Finset.measurableSet_biInter s fun i hi => ?_
        refine siteSigma_mono B (fun u hu => ?_) L _
          (hf i (Finset.mem_insert_of_mem hi))
        exact Set.mem_biUnion (Finset.mem_coe.mpr hi) hu
      have hsep' : ∀ u ∈ ({z a} : Set (Fin d → ℤ)),
          ∀ v ∈ (⋃ i ∈ (s : Set ι), ({z i} : Set (Fin d → ℤ))),
          3 ^ L < latDist u v := by
        intro u hu v hv
        obtain ⟨i, hi, hv⟩ := Set.mem_iUnion₂.mp hv
        rw [Set.mem_singleton_iff] at hu hv
        subst hu
        subst hv
        refine hsep a i ?_
        rintro rfl
        exact ha (Finset.mem_coe.mp hi)
      have hprod := (Indep_iff _ _ μ).mp (hindep _ _ hsep') _ _ hA hC
      rw [Finset.set_biInter_insert, hprod, Finset.prod_insert ha,
        ih f fun i hi => hf i (Finset.mem_insert_of_mem hi)]


/-- **The `iIndepFun` form.** Random variables that are measurable with respect
to the localised σ-algebras of a pairwise-separated family of sites are mutually
independent. This is the hypothesis format consumed by the ABK26 concentration
inequality. -/
theorem iIndepFun_of_measurable_siteSigma [IsProbabilityMeasure μ] {ι : Type*}
    {B : ℕ → (Fin d → ℤ) → Set Ω} {L : ℕ} {z : ι → Fin d → ℤ} {X : ι → Ω → ℝ}
    (hindep : ∀ S S' : Set (Fin d → ℤ), (∀ u ∈ S, ∀ v ∈ S', 3 ^ L < latDist u v) →
      Indep (siteSigma B S L) (siteSigma B S' L) μ)
    (hsep : ∀ i j : ι, i ≠ j → 3 ^ L < latDist (z i) (z j))
    (hX : ∀ i, Measurable[siteSigma B ({z i} : Set (Fin d → ℤ)) L] (X i)) :
    iIndepFun X μ := by
  refine (iIndepFun_iff_iIndep _ X μ).mpr ?_
  rw [iIndep_iff]
  intro s f hf
  exact meas_biInter_eq_prod hindep hsep s f fun i hi => (hX i).comap_le _ (hf i hi)

end Algsuperdiff.Section3.Provider.Percolation
