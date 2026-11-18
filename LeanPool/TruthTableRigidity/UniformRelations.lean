/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import LeanPool.TruthTableRigidity.Degrees
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import LeanPool.TruthTableRigidity.ShiftStep

/-! # Continuous oracle operations and uniformization of the three relations -/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-! ### Continuity of the group operations -/

/-- 2-adic addition, as a map of oracles. -/
def zaddO (G H : Oracle) : Oracle := (Z2.of G + Z2.of H : Z2)

/-- 2-adic negation, as a map of oracles. -/
def znegO (G : Oracle) : Oracle := (-Z2.of G : Z2)

theorem continuous_ojoin : Continuous fun p : Oracle × Oracle => ojoin p.1 p.2 := by
  apply continuous_pi
  intro n
  by_cases h : n % 2 = 0
  · simp only [ojoin_apply, h, ite_true]
    exact (continuous_apply _).comp continuous_fst
  · simp only [ojoin_apply, h, ite_false]
    exact (continuous_apply _).comp continuous_snd

theorem continuous_zaddO : Continuous fun p : Oracle × Oracle => zaddO p.1 p.2 :=
  (isTTFunctional_addHalves.continuous.comp continuous_ojoin).congr fun p => by
    simp [Function.comp, zaddO]

theorem continuous_znegO : Continuous znegO := isTTFunctional_neg.continuous

/-! ### The reductions (1) -/

theorem red_plus (G H : Z2) : TTReducible (G + H : Z2) (ojoin G H) := by
  change TTReducible (Z2.of G + Z2.of H : Z2) (ojoin G H)
  simpa only [evens_ojoin, odds_ojoin] using
    ttReducible_of_isTTFunctional isTTFunctional_addHalves (ojoin G H)

theorem red_minus (G H : Z2) : TTReducible G (ojoin (G + H : Z2) (-H : Z2)) := by
  have := ttReducible_of_isTTFunctional isTTFunctional_addHalves (ojoin (G + H : Z2) (-H : Z2))
  simp only [evens_ojoin, odds_ojoin] at this
  have e : (Z2.of (G + H) + Z2.of (-H) : Z2) = G := by
    change (G + H) + -H = G; abel
  rwa [e] at this

theorem shift_cons (b : Bool) (X : Oracle) : shift (cons b X) = X := by
  funext n; simp [shift, cons]

theorem red_half (G H : Z2) : TTReducible (G + H : Z2) (ojoin G (G + (H + H) : Z2)) := by
  have := ttReducible_of_isTTFunctional (isTTFunctional_shift.comp isTTFunctional_addHalves)
    (ojoin G (G + (H + H) : Z2))
  simp only [Function.comp, evens_ojoin, odds_ojoin] at this
  have e : shift (Z2.of G + Z2.of (G + (H + H)) : Z2) = (G + H : Z2) := by
    have : (Z2.of G + Z2.of (G + (H + H)) : Z2) = (G + H) + (G + H) := by
      change G + (G + (H + H)) = (G + H) + (G + H); abel
    rw [this, Z2.add_self, shift_cons]
  rwa [e] at this

/-! ### Uniform relations on an open set -/

/-- Uniformize the addition, subtraction and halving reductions on one open set. The
five evaluations of `F` need only be continuous on the given dense `Gδ` set. -/
theorem uniformize_relations {F : Oracle → Oracle} {E U : Set (Oracle × Oracle)}
    (hEG : IsGδ E) (hEd : Dense E) (hU : IsOpen U) (hne : U.Nonempty)
    (hfst : ContinuousOn (fun p : Oracle × Oracle => F p.1) E)
    (hsnd : ContinuousOn (fun p : Oracle × Oracle => F p.2) E)
    (hadd : ContinuousOn (fun p : Oracle × Oracle => F (zaddO p.1 p.2)) E)
    (hneg : ContinuousOn (fun p : Oracle × Oracle => F (znegO p.2)) E)
    (hdouble : ContinuousOn (fun p : Oracle × Oracle => F (zaddO p.1 (zaddO p.2 p.2))) E)
    (hmono : ∀ A B, TTReducible A B → TTReducible (F A) (F B))
    (hjoin : ∀ A B, TTReducible (F (ojoin A B)) (ojoin (F A) (F B))) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧
      ∃ Φp Φm Φh : Oracle → Oracle, IsTTFunctional Φp ∧ IsTTFunctional Φm ∧
        IsTTFunctional Φh ∧ ∀ p ∈ E, p ∈ V → Relations F Φp Φm Φh p.1 p.2 := by
  have continuousOn_join {φ ψ : Oracle × Oracle → Oracle}
      (hφ : ContinuousOn φ E) (hψ : ContinuousOn ψ E) :
      ContinuousOn (fun p => ojoin (φ p) (ψ p)) E :=
    continuous_ojoin.comp_continuousOn (hφ.prodMk hψ)
  obtain ⟨V₁, hV₁U, hV₁, hV₁ne, Φp, hp, hRp⟩ := uniformization_on hEG hEd hU hne hadd
    (continuousOn_join hfst hsnd) (fun p _ _ =>
      (hmono _ _ (red_plus p.1 p.2)).trans (hjoin _ _))
  obtain ⟨V₂, hV₂V₁, hV₂, hV₂ne, Φm, hm, hRm⟩ := uniformization_on hEG hEd hV₁ hV₁ne hfst
    (continuousOn_join hadd hneg) (fun p _ _ =>
      (hmono _ _ (red_minus p.1 p.2)).trans (hjoin _ _))
  obtain ⟨V₃, hV₃V₂, hV₃, hV₃ne, Φh, hh, hRh⟩ := uniformization_on hEG hEd hV₂ hV₂ne hadd
    (continuousOn_join hfst hdouble) (fun p _ _ =>
      (hmono _ _ (red_half p.1 p.2)).trans (hjoin _ _))
  exact ⟨V₃, hV₃V₂.trans (hV₂V₁.trans hV₁U), hV₃, hV₃ne, Φp, Φm, Φh, hp, hm, hh,
    fun p hpE hpV => ⟨hRp p hpE (hV₂V₁ (hV₃V₂ hpV)), hRm p hpE (hV₃V₂ hpV), hRh p hpE hpV⟩⟩

end TT
