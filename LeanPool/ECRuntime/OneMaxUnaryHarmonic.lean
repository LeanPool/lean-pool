/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.OneMax
public import LeanPool.ECRuntime.StaticUnaryUnbiasedMutation

/-!
A singleton-only OneMax runtime bound for static unary-unbiased mutation
laws with positive singleton probability. The harmonic fitness-level
certificate requires no radius-moment hypothesis.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-- The singleton improving masks are a subevent of all strict OneMax
improvements. We use the original mask measure, not a conditioned law. -/
private theorem oneMaxUnary_progress_mass_lower_bound
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (x : BitString n) :
    (oneMaxPotential x : Real) * (law.oneBitMass / (n : Real)) ≤
      finiteEventMass law.weight (fun mask : MutationMask n =>
        oneMaxPotential (selectedAfterMask oneMaxReal x mask) < oneMaxPotential x) := by
  have hmass :
      (∑ mask ∈ singleZeroMasks x, law.weight mask) =
        law.singleZeroFlipWeight x := by
    unfold singleZeroMasks zeroSingletonMasks singleZeroFlipWeight
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Finset.singleton_injective hij
  calc
    (oneMaxPotential x : Real) * (law.oneBitMass / (n : Real)) =
        law.singleZeroFlipWeight x := by
          simpa [oneMaxPotential] using (law.singleZeroFlipWeight_eq hn x).symm
    _ = ∑ mask ∈ singleZeroMasks x, law.weight mask := hmass.symm
    _ ≤ finiteEventMass law.weight (fun mask : MutationMask n =>
          oneMaxPotential (selectedAfterMask oneMaxReal x mask) <
            oneMaxPotential x) := by
      apply sum_le_finiteEventMass_of_subset
      · exact law.weight_nonneg
      · intro mask hm
        rcases Finset.mem_image.mp hm with ⟨i, hi, himask⟩
        subst mask
        exact oneMaxPotential_selected_single_zero_flip_lt x i
          ((mem_zeroPositions x i).mp hi)

/-- The existing harmonic fitness-level certificate specialized to the
singleton mass `p_1` of an arbitrary static unary-unbiased operator. -/
theorem oneMaxUnary_harmonic_finiteHorizon
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hn : 0 < n) (hp : 0 < law.oneBitMass) :
    HasUniformFiniteHorizonRuntimeBound
      (law.transition oneMaxReal)
      (oneMaxTarget n)
      (harmonicLevelRuntime (law.oneBitMass / (n : Real)) oneMaxPotential) := by
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hgeneric := harmonicFitnessLevel_finiteHorizonBound
    (w := fun (_x : BitString n) (mask : MutationMask n) => law.weight mask)
    (step := selectedAfterMask oneMaxReal)
    (V := oneMaxPotential)
    (rate := law.oneBitMass / (n : Real))
    (hrate := div_pos hp hnreal)
    (hw := fun _x mask => law.weight_nonneg mask)
    (hsum := fun _x => law.weight_sum)
    (hmono := fun x mask => oneMaxPotential_selectedAfterMask_le x mask)
    (hprogress := fun x _hx => oneMaxUnary_progress_mass_lower_bound law hn x)
  -- The two target descriptions are extensionally equal, but their
  -- `DecidablePred` instances differ.  Use the certified congruence lemma
  -- instead of relying on `simpa` to identify dependent instances.
  intro t x
  have htarget : oneMaxTarget n =
      potentialTarget (oneMaxPotential (n := n)) := by rfl
  have hcongr := finiteHorizonRuntime_congr_target
    (law.transition oneMaxReal) (oneMaxTarget n)
    (potentialTarget (oneMaxPotential (n := n))) htarget t x
  calc
    finiteHorizonRuntime (law.transition oneMaxReal) (oneMaxTarget n) t x =
        finiteHorizonRuntime (law.transition oneMaxReal)
          (potentialTarget (oneMaxPotential (n := n))) t x := hcongr
    _ ≤ harmonicLevelRuntime (law.oneBitMass / (n : Real)) oneMaxPotential x :=
      hgeneric t x

/-- Unrestricted iteration-count bound: E[T] ≤ n H_{zeroCount(x)} / p_1.
The initial evaluation is not included in T. -/
theorem oneMaxUnary_runtimeSup_le_harmonic
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hn : 0 < n) (hp : 0 < law.oneBitMass) (x : BitString n) :
    runtimeSup (law.transition oneMaxReal) (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (((n : Real) / law.oneBitMass) * harmonicReal (zeroCount x)) := by
  have hcert := runtimeSup_le_of_uniform_bound
    (law.transition oneMaxReal) (oneMaxTarget n)
    (harmonicLevelRuntime (law.oneBitMass / (n : Real)) oneMaxPotential)
    (law.oneMaxUnary_harmonic_finiteHorizon hn hp) x
  have hcoeff : (law.oneBitMass / (n : Real))⁻¹ =
      (n : Real) / law.oneBitMass := by
    rw [inv_div]
  simpa only [harmonicLevelRuntime, oneMaxPotential, hcoeff] using hcert

end StaticUnaryUnbiasedMutation
end ECRuntime
