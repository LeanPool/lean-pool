/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/DegreeCoverage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BinaryCut
public import LeanPool.TuringConeRigidity.Computability.BinaryRecovery
public import LeanPool.TuringConeRigidity.Representation.Assembly

/-!
# Degree Coverage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
namespace BinarySeries

theorem value_eq_series (B : Oracle) :
    value B = ∑' n, (bit B n : ℝ) * (2^(n+1) : ℝ)⁻¹ := rfl

theorem irrational_of_noncomputable (B : Oracle) (h : ¬ Reduces B (fun _ => false)) :
    Irrational (value B) := by
  intro ⟨q,hq⟩
  apply h
  have hr := set_reduces_cut B (mixed_of_noncomputable B h)
  rw [←hq] at hr
  exact reduces_trans hr (rational_cut_reduces q _)

theorem rational_series_reduces (B A : Oracle) (q : ℚ) (hq : (q : ℝ) = value B) :
    Reduces B A := by
  by_contra h
  have hn : ¬ Reduces B (fun _ => false) := by
    intro hh
    exact h (reduces_trans hh (eventually_constant_reduces (fun _ => false) A false 0 (by simp)))
  exact irrational_of_noncomputable B hn ⟨q,hq⟩

theorem noncomputable_series (B : Oracle) (h : ¬ Reduces B (fun _ => false)) :
    Irrational (value B) ∧ 0 < value B ∧ value B < 1 ∧
      Reduces (cut (value B)) B ∧ Reduces B (cut (value B)) := by
  have hm := mixed_of_noncomputable B h
  have hi := irrational_of_noncomputable B h
  refine ⟨hi,positive B ?_,lt_one B ?_,cut_reduces B hi,set_reduces_cut B hm⟩
  · obtain ⟨n,_,hn⟩ := (hm 0).1
    exact ⟨n,hn⟩
  · obtain ⟨n,_,hn⟩ := (hm 0).2
    exact ⟨n,hn⟩
end BinarySeries

theorem irrational_degree_coverage : IrrationalDegreeCoverage := by
  intro a ha
  obtain ⟨B,rfl⟩ := degree_surjective a
  have hn : ¬ Reduces B (fun _ => false) := by
    intro h
    exact ha (le_antisymm h bot_le)
  obtain ⟨hi,h0,h1,hforward,hback⟩ := BinarySeries.noncomputable_series B hn
  exact ⟨BinarySeries.value B,hi,h0,h1,(degree_eq_iff _ _).mpr ⟨hforward,hback⟩⟩

end TuringRigidity

end OAI
