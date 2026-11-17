/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/Category.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.Recurrence
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Category
-/


@[expose] public section

namespace OAI

open Set Filter Topology

namespace TuringRigidity

theorem measurable_continuousOn_residual {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (f : X → Y) (hf : Measurable f) :
    ∃ D : Set X, D ∈ residual X ∧ ContinuousOn f D := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis Y
  have hm : ∀ n : ℕ, MeasurableSet (f ⁻¹' b n) :=
    fun n => hf ((hb.isOpen (mem_range_self n)).measurableSet)
  choose V hVo hVeq using fun n => (hm n).residualEq_isOpen
  let D : Set X := {x | ∀ n : ℕ, f x ∈ b n ↔ x ∈ V n}
  have hD : D ∈ residual X := by
    apply eventually_countable_forall.mpr
    intro n
    exact Filter.eventuallyEqSet_iff.mp (hVeq n)
  refine ⟨D, hD, hb.continuousOn_iff.mpr ?_⟩
  rintro s ⟨n, rfl⟩
  refine ⟨V n, hVo n, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hd⟩
    exact ⟨(hd n).mp hx, hd⟩
  · rintro ⟨hx, hd⟩
    exact ⟨(hd n).mpr hx, hd⟩

def forwardShift (s a : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1 + s, p.2 - p.1 + a)
  invFun p := (p.1 - s, p.2 + (p.1 - s) - a)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun :=
    (continuous_fst.add continuous_const).prodMk
      ((continuous_snd.sub continuous_fst).add continuous_const)
  continuous_invFun :=
    (continuous_fst.sub continuous_const).prodMk
      ((continuous_snd.add (continuous_fst.sub continuous_const)).sub continuous_const)

def backwardShift (s : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.2 + s, p.1 - p.2)
  invFun p := (p.2 + (p.1 - s), p.1 - s)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun :=
    (continuous_snd.add continuous_const).prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun :=
    (continuous_snd.add (continuous_fst.sub continuous_const)).prodMk
      (continuous_fst.sub continuous_const)

def goodPairs (t : ℝ) (D : Set ℝ) (E : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∀ s ∈ rationalSpan t,
    p.1 + s ∈ D ∧ (∀ a ∈ rationalSpan t, (p.1+s, p.2-p.1+a) ∈ E) ∧
      (p.2+s, p.1-p.2) ∈ E}

theorem goodPairs_residual (t : ℝ) (D : Set ℝ) (E : Set (ℝ × ℝ))
    (hD : D ∈ residual ℝ) (hE : E ∈ residual (ℝ × ℝ)) :
    goodPairs t D E ∈ residual (ℝ × ℝ) := by
  have : Countable (rationalSpan t) := (rationalSpan_countable t).to_subtype
  have hcoord (s : ℝ) : {p : ℝ × ℝ | p.1 + s ∈ D} ∈ residual (ℝ × ℝ) := by
    exact tendsto_residual_of_isOpenMap
      (continuous_fst.add continuous_const)
      ((Homeomorph.addRight s).isOpenMap.comp isOpenMap_fst) hD
  have hforward (s a : ℝ) :
      {p : ℝ × ℝ | (p.1+s,p.2-p.1+a) ∈ E} ∈ residual (ℝ × ℝ) := by
    exact tendsto_residual_of_isOpenMap
      (forwardShift s a).continuous (forwardShift s a).isOpenMap hE
  have hbackward (s : ℝ) :
      {p : ℝ × ℝ | (p.2+s,p.1-p.2) ∈ E} ∈ residual (ℝ × ℝ) := by
    exact tendsto_residual_of_isOpenMap
      (backwardShift s).continuous (backwardShift s).isOpenMap hE
  have h : ∀ᶠ p in residual (ℝ × ℝ), ∀ s : rationalSpan t,
      p.1+s.val ∈ D ∧
      (∀ a : rationalSpan t, (p.1+s.val,p.2-p.1+a.val) ∈ E) ∧
      (p.2+s.val,p.1-p.2) ∈ E := by
    apply eventually_countable_forall.mpr
    intro s
    exact Filter.Eventually.and (hcoord s.val)
      (Filter.Eventually.and (eventually_countable_forall.mpr
        (fun a => hforward s.val a.val)) (hbackward s.val))
  filter_upwards [h] with p hp
  intro s hs
  exact ⟨(hp ⟨s,hs⟩).1, fun a ha => (hp ⟨s,hs⟩).2.1 ⟨a,ha⟩, (hp ⟨s,hs⟩).2.2⟩

end TuringRigidity

end OAI
