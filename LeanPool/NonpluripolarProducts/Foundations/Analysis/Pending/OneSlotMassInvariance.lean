/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.UniformBoundedGlobalMass

/-!
# One-slot mass invariance is the whole remaining obligation

`Pending.UniformBoundedGlobalMass` reduces the BEGZ patch-mass estimate to
`HasUniformBoundedGlobalMass η`: one finite constant bounds the total masses of
the global mixed measures of all *bounded* `η`-PSH tuples.  This module reduces
that in turn to the single integration-by-parts statement

  **one-slot mass invariance** — replacing the potential in one slot by another
  bounded one does not change the total mass,

which is the compact form of `∫ ddᶜ(a - b) ∧ T = 0`.  Two reductions are
involved and both are elementary:

* changing all `n` slots one at a time shows that *any two* bounded `η`-PSH
  tuples have the same total mass;
* if there is no bounded `η`-PSH tuple at all the uniform bound holds vacuously
  with constant `0`, and otherwise the common mass of one such tuple is the
  constant, finite because bounded tuples already have finite mass
  (`Pending.BoundedGlobalProduct`).

So after this module the only unproved statement between the project and the
BEGZ finite-mass theorem is one-slot mass invariance for bounded potentials.
No truncation level, no `⊥` value and no strict locus occurs in it.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.UniformBoundedGlobalMass

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

omit [BorelSpace M] in
/-- Equal tuples have equal global mixed measures; the regularity proof is
irrelevant by construction. -/
theorem globalMixedMeasure_congr_tuple {η : Fin n → ClosedRealOneOneForm n M}
    {a b : Fin n → M → EReal} (e : a = b)
    (ha : ∀ i, ThetaPlurisubharmonic (η i).val (a i))
    (hb : ∀ i, ThetaPlurisubharmonic (η i).val (b i)) :
    globalMixedMeasure η a ha = globalMixedMeasure η b hb := by
  subst e
  rfl

/-- **One-slot mass invariance for bounded potentials.** Replacing the potential
of one slot by another bounded `η`-PSH potential leaves the total mass of the
global mixed measure unchanged.  In coordinates this is
`∫ ddᶜ(a - b) ∧ T = 0`; globally it is the compact integration-by-parts
identity.  It is *not* proved here. -/
def HasOneSlotMassInvariance (η : Fin n → ClosedRealOneOneForm n M) : Prop :=
  ∀ (v : Fin n → M → EReal) (i₀ : Fin n) (a : M → EReal)
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i))
    (hva : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update v i₀ a i)),
    (∀ i, IsBoundedPotential (v i)) → IsBoundedPotential a →
      globalMixedMeasure η (Function.update v i₀ a) hva univ =
        globalMixedMeasure η v hv univ

variable {η : Fin n → ClosedRealOneOneForm n M}

/-- The tuple agreeing with `v'` in the slots of index below `m`, and with `v`
elsewhere. -/
def swapPrefix (v v' : Fin n → M → EReal) (m : ℕ) : Fin n → M → EReal :=
  fun i => if (i : ℕ) < m then v' i else v i

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
theorem swapPrefix_zero (v v' : Fin n → M → EReal) : swapPrefix v v' 0 = v := by
  funext i
  simp [swapPrefix]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
theorem swapPrefix_full (v v' : Fin n → M → EReal) : swapPrefix v v' n = v' := by
  funext i
  simp [swapPrefix, i.isLt]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
theorem swapPrefix_succ (v v' : Fin n → M → EReal) {m : ℕ} (hm : m < n) :
    swapPrefix v v' (m + 1) =
      Function.update (swapPrefix v v' m) ⟨m, hm⟩ (v' ⟨m, hm⟩) := by
  classical
  funext i
  by_cases h : i = ⟨m, hm⟩
  · subst h
    simp [swapPrefix]
  · have hne : (i : ℕ) ≠ m := fun hc => h (Fin.ext hc)
    have hiff : ((i : ℕ) < m + 1) = ((i : ℕ) < m) := by
      simp only [Nat.lt_succ_iff_lt_or_eq, hne, or_false]
    simp [swapPrefix, Function.update_of_ne h, hiff]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem thetaPlurisubharmonic_swapPrefix {v v' : Fin n → M → EReal}
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i))
    (hv' : ∀ i, ThetaPlurisubharmonic (η i).val (v' i)) (m : ℕ) (i : Fin n) :
    ThetaPlurisubharmonic (η i).val (swapPrefix v v' m i) := by
  by_cases h : (i : ℕ) < m
  · simpa only [swapPrefix, ite_eq_left h] using hv' i
  · simpa only [swapPrefix, ite_eq_right h] using hv i

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
theorem isBoundedPotential_swapPrefix {v v' : Fin n → M → EReal}
    (hb : ∀ i, IsBoundedPotential (v i)) (hb' : ∀ i, IsBoundedPotential (v' i))
    (m : ℕ) (i : Fin n) : IsBoundedPotential (swapPrefix v v' m i) := by
  by_cases h : (i : ℕ) < m
  · simpa only [swapPrefix, ite_eq_left h] using hb' i
  · simpa only [swapPrefix, ite_eq_right h] using hb i

omit [BorelSpace M] in
/-- **All bounded tuples have the same total mass**, granted one-slot
invariance: change the slots one at a time. -/
theorem globalMixedMeasure_univ_eq_of_bounded (h : HasOneSlotMassInvariance η)
    {v v' : Fin n → M → EReal}
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i))
    (hv' : ∀ i, ThetaPlurisubharmonic (η i).val (v' i))
    (hb : ∀ i, IsBoundedPotential (v i)) (hb' : ∀ i, IsBoundedPotential (v' i)) :
    globalMixedMeasure η v hv univ = globalMixedMeasure η v' hv' univ := by
  classical
  have hpsh : ∀ m, ∀ i, ThetaPlurisubharmonic (η i).val (swapPrefix v v' m i) :=
    fun m => thetaPlurisubharmonic_swapPrefix hv hv' m
  have hbd : ∀ m, ∀ i, IsBoundedPotential (swapPrefix v v' m i) :=
    fun m => isBoundedPotential_swapPrefix hb hb' m
  have key : ∀ m : ℕ, m ≤ n →
      globalMixedMeasure η (swapPrefix v v' m) (hpsh m) univ =
        globalMixedMeasure η v hv univ := by
    intro m
    induction m with
    | zero =>
      intro _
      exact congrArg (fun μ : Measure M => μ univ)
        (globalMixedMeasure_congr_tuple (swapPrefix_zero v v') (hpsh 0) hv)
    | succ m ih =>
      intro hm
      have hmn : m < n := hm
      have hupd : ∀ i, ThetaPlurisubharmonic (η i).val
          (Function.update (swapPrefix v v' m) (⟨m, hmn⟩ : Fin n) (v' ⟨m, hmn⟩) i) := by
        rw [← swapPrefix_succ v v' hmn]
        exact hpsh (m + 1)
      calc globalMixedMeasure η (swapPrefix v v' (m + 1)) (hpsh (m + 1)) univ
          = globalMixedMeasure η
              (Function.update (swapPrefix v v' m) (⟨m, hmn⟩ : Fin n) (v' ⟨m, hmn⟩))
              hupd univ :=
            congrArg (fun μ : Measure M => μ univ)
              (globalMixedMeasure_congr_tuple (swapPrefix_succ v v' hmn)
                (hpsh (m + 1)) hupd)
        _ = globalMixedMeasure η (swapPrefix v v' m) (hpsh m) univ :=
            h (swapPrefix v v' m) ⟨m, hmn⟩ (v' ⟨m, hmn⟩) (hpsh m) hupd (hbd m) (hb' _)
        _ = globalMixedMeasure η v hv univ := ih (Nat.le_of_succ_le hm)
  have hn := key n le_rfl
  have hfull : globalMixedMeasure η (swapPrefix v v' n) (hpsh n) univ =
      globalMixedMeasure η v' hv' univ :=
    congrArg (fun μ : Measure M => μ univ)
      (globalMixedMeasure_congr_tuple (swapPrefix_full v v') (hpsh n) hv')
  rw [← hn]
  exact hfull

/-- **The uniform bounded-mass statement follows from one-slot invariance.**
If no bounded `η`-PSH tuple exists the bound is vacuous; otherwise every bounded
tuple has the same, finite, total mass. -/
theorem hasUniformBoundedGlobalMass_of_oneSlot (h : HasOneSlotMassInvariance η) :
    HasUniformBoundedGlobalMass η := by
  classical
  by_cases hex : ∃ (v : Fin n → M → EReal)
      (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i)), ∀ i, IsBoundedPotential (v i)
  · obtain ⟨v₀, hv₀, hb₀⟩ := hex
    refine ⟨globalMixedMeasure η v₀ hv₀ univ,
      globalMixedMeasure_apply_lt_top_of_bounded hv₀ hb₀ univ, fun v hv hb => ?_⟩
    exact le_of_eq (globalMixedMeasure_univ_eq_of_bounded h hv hv₀ hb hb₀)
  · exact ⟨0, by simp, fun v hv hb => absurd ⟨v, hv, hb⟩ hex⟩

end

end SGPT.Foundations.Analysis.Pending.UniformBoundedGlobalMass
