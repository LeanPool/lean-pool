/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioOperator
public import LeanPool.VacuumBellSeparation.FreeField.PartialOperatorComposition

/-!
# The full domain and action of the square of a bounded ratio

For commuting A,B with A²+B²=2I, the actual maximal square of L(Ax)=Bx
has domain range A² and sends A²x to B²x. This is a domain theorem,
not a formal cancellation of an unbounded inverse.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A B : E →L[ℂ] E) (hA : Function.Injective A)
variable (hc : Commute A B) (hsq : A * A + B * B = 2)

include hc hsq in
omit [CompleteSpace E] in
theorem boundedRatio_square_mem_domain (x : E) :
    x ∈ (partialComp (boundedRatio A B hA) (boundedRatio A B hA)).domain ↔
      ∃ z, A (A z) = x := by
  rw [partialComp_domain]
  constructor
  · rintro ⟨hx, hLx⟩
    obtain ⟨u, hu, hBu⟩ := boundedRatio_representation A B hA ⟨x, hx⟩
    obtain ⟨v, hv⟩ := hLx
    have heq : A v = B u := hv.trans hBu.symm
    let w := (1 / 2 : ℂ) • (A u + B v)
    have hw : A w = u := by
      have hcomm : A (B v) = B (A v) :=
        congrArg (fun Q : E →L[ℂ] E => Q v) hc.eq
      have hsum : A (A u) + B (B u) = (2 : ℂ) • u := by
        simpa only [add_apply, mul_apply_eq_comp, ofNat_apply, two_smul] using
          congrArg (fun Q : E →L[ℂ] E => Q u) hsq
      rw [show A w = (1 / 2 : ℂ) • (A (A u) + A (B v)) by simp [w], hcomm, heq, hsum]
      norm_num [smul_smul]
    exact ⟨w, by rw [hw, hu]⟩
  · rintro ⟨z, rfl⟩
    refine ⟨⟨A z, rfl⟩, ?_⟩
    rw [boundedRatio_apply_range]
    exact ⟨B z, congrArg (fun Q : E →L[ℂ] E => Q z) hc.eq⟩

include hc in
omit [CompleteSpace E] in
/-- The square's value at every point of its proved maximal domain. -/
theorem boundedRatio_square_apply (z : E)
    (hx : A (A z) ∈ (partialComp (boundedRatio A B hA) (boundedRatio A B hA)).domain) :
    partialComp (boundedRatio A B hA) (boundedRatio A B hA) ⟨A (A z), hx⟩ = B (B z) := by
  have hval : boundedRatio A B hA ⟨A (A z), ⟨A z, rfl⟩⟩ = A (B z) := by
    rw [boundedRatio_apply_range]
    exact congrArg (fun Q : E →L[ℂ] E => Q z) hc.eq.symm
  have hy : boundedRatio A B hA ⟨A (A z), ⟨A z, rfl⟩⟩ ∈ (boundedRatio A B hA).domain :=
    ⟨B z, hval.symm⟩
  rw [partialComp_apply _ _ ⟨A (A z), hx⟩ ⟨A z, rfl⟩ hy]
  have hsub : (⟨boundedRatio A B hA ⟨A (A z), ⟨A z, rfl⟩⟩, hy⟩ :
      (boundedRatio A B hA).domain) = ⟨A (B z), ⟨B z, rfl⟩⟩ := Subtype.ext hval
  rw [hsub, boundedRatio_apply_range]

include hc hsq in
omit [CompleteSpace E] in
theorem boundedRatio_square_eq :
    partialComp (boundedRatio A B hA) (boundedRatio A B hA) =
      boundedRatio (A * A) (B * B) (hA.comp hA) := by
  apply LinearPMap.ext
  · ext x
    exact boundedRatio_square_mem_domain A B hA hc hsq x
  · intro x hx hy
    obtain ⟨z, hz⟩ := (boundedRatio_square_mem_domain A B hA hc hsq x).mp hx
    subst x
    exact (boundedRatio_square_apply A B hA hc z hx).trans
      (boundedRatio_apply_range (A * A) (B * B) (hA.comp hA) z).symm

end VacuumBellSeparation
