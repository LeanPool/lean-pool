/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Constructions

/-!
# Scattered spaces and products of quasi-sober spaces

An arbitrary product of quasi-sober spaces is quasi-sober: the generic point of an irreducible
closed set `S` has for coordinates the generic points of the closures of the projections of `S`.
The file also defines scattered spaces (every nonempty subset has a relatively isolated point)
and proves they are `T0` and quasi-sober.

## Main definitions

* `Scattered`

## Main statements

* `Scattered.t0Space`, `Scattered.quasiSober`
* `quasiSober_pi`: an arbitrary product of quasi-sober spaces is quasi-sober.
-/

@[expose] public section

open Set Function

/-- Every nonempty subset has a relatively isolated point. -/
def Scattered (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ A : Set X, A.Nonempty → ∃ x ∈ A, ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ A, y ∈ W → y = x

section Scattered

variable {Z : Type*} [TopologicalSpace Z]

/-- A scattered space is `T0`. -/
theorem Scattered.t0Space (h : Scattered Z) : T0Space Z := by
  refine (t0Space_iff_inseparable _).2 fun x y hxy => ?_
  obtain ⟨z, hz | hz, W, hW, hzW, hiso⟩ := h {x, y} (insert_nonempty _ _) <;> subst hz
  · exact (hiso y (by simp) ((inseparable_iff_forall_isOpen.1 hxy W hW).1 hzW)).symm
  · exact hiso x (by simp) ((inseparable_iff_forall_isOpen.1 hxy W hW).2 hzW)

/-- An isolated point of an irreducible closed set is its generic point. -/
theorem Scattered.quasiSober (h : Scattered Z) : QuasiSober Z where
  sober {S} hS hc := by
    obtain ⟨x, hx, W, hW, hxW, hiso⟩ := h S hS.nonempty
    refine ⟨x, (closure_minimal (singleton_subset_iff.2 hx) hc).antisymm fun y hy => ?_⟩
    rw [← specializes_iff_mem_closure, specializes_iff_forall_open]
    intro V hV hyV
    obtain ⟨z, hzS, hzW, hzV⟩ := hS.2 W V hW hV ⟨x, hx, hxW⟩ ⟨y, hy, hyV⟩
    exact hiso z hzS hzW ▸ hzV

end Scattered

/-- An arbitrary product of quasi-sober spaces is quasi-sober: the generic point of an
irreducible closed `S` has for coordinates the generic points of the closures of the
projections of `S`. -/
instance quasiSober_pi {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [∀ i, QuasiSober (π i)] : QuasiSober (∀ i, π i) where
  sober {S} hS hc := by
    classical
    have hi i : IsIrreducible (eval i '' S) := hS.image _ (continuous_apply i).continuousOn
    set x : ∀ i, π i := fun i => (hi i).genericPoint
    have hx i : closure {x i} = closure (eval i '' S) := (hi i).genericPoint_closure_eq
    have hxS : x ∈ S := by
      rw [← hc.closure_eq, mem_closure_iff]
      intro o ho hxo
      obtain ⟨I, u, hu, hIo⟩ := isOpen_pi_iff.1 ho x hxo
      suffices (S ∩ (I : Set ι).pi u).Nonempty from
        let ⟨y, hyS, hyI⟩ := this; ⟨y, hIo hyI, hyS⟩
      clear hIo
      induction I using Finset.induction_on with
      | empty => simpa using hS.nonempty
      | insert a I ha ih =>
        rw [Finset.coe_insert, insert_pi]
        have hua := hu a (Finset.mem_insert_self _ _)
        obtain ⟨_, hy, y, hyS, rfl⟩ :=
          mem_closure_iff.1 (hx a ▸ subset_closure rfl : x a ∈ closure (eval a '' S)) _ hua.1 hua.2
        exact hS.2 _ _ (hua.1.preimage (continuous_apply a))
          (isOpen_set_pi I.finite_toSet fun b hb => (hu b (Finset.mem_insert_of_mem hb)).1)
          ⟨y, hyS, hy⟩ (ih fun b hb => hu b (Finset.mem_insert_of_mem hb))
    refine ⟨x, (closure_minimal (singleton_subset_iff.2 hxS) hc).antisymm fun y hy => ?_⟩
    rw [← specializes_iff_mem_closure, specializes_pi]
    exact fun i => specializes_iff_mem_closure.2 (hx i ▸ subset_closure (mem_image_of_mem _ hy))
