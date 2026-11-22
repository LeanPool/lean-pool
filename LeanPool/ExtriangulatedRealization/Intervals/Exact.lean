/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Maps
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The interval sequences `0 → A i → P i → Y → 0`

Exactness in the functor category `Rep k I` is checked pointwise; we record this as a general
lemma and deduce that `0 → A i → P i → Y → 0` is short exact (the rows of (2.1)).
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

/-- A short complex in a functor category into an abelian category is exact if it is exact
after every evaluation. -/
lemma ShortComplex.exact_of_evaluation {J : Type*} [Category J] {C : Type*} [Category C]
    [Abelian C] (S : ShortComplex (J ⥤ C)) (h : ∀ j, (S.map ((evaluation J C).obj j)).Exact) :
    S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ (fun j => ?_)
  exact ((ShortComplex.exact_iff_isZero_homology _).mp (h j)).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- An element of an interval representation at a point of the support. -/
lemma intervalRep_eq_const {U : Set (WithBot I)} [U.OrdConnected] {t : WithBot I} (ht : t ∈ U)
    (f : (intervalRep U : Rep k I).obj t) : f = fun _ => f ⟨(), ht⟩ := by
  funext x
  rfl

open Classical in
/-- The interval sequence `A i → P i → Y`. -/
noncomputable def intervalSeq (i : I) : ShortComplex (Rep k I) :=
  ShortComplex.mk (bMap i) (cMap i) (bMap_comp_cMap i)

open Classical in
lemma intervalSeq_shortExact (i : I) : (intervalSeq (k := k) i).ShortExact where
  exact := by
    apply ShortComplex.exact_of_evaluation
    intro t
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    by_cases htA : t ∈ (A i).support
    · refine ⟨fun _ => x₂ ⟨(), htA.2⟩, ?_⟩
      funext x
      change (if h : t ∈ (A i).support then x₂ ⟨(), htA.2⟩ else 0) = x₂ x
      rw [dite_eq_left htA]
    · refine ⟨0, ?_⟩
      rw [map_zero]
      funext x
      have htb : t = ⊥ := by
        by_contra hne
        exact htA ⟨bot_lt_iff_ne_bot.mpr hne, x.2⟩
      subst htb
      have h0 := congrFun hx₂ ⟨(), mem_Y.mpr rfl⟩
      change (if h : (⊥ : WithBot I) ∈ (P i).support then x₂ ⟨(), h⟩ else 0) = 0 at h0
      rw [dite_eq_left x.2] at h0
      exact h0.symm
  mono_f := by
    rw [NatTrans.mono_iff_mono_app]
    intro t
    rw [ModuleCat.mono_iff_injective]
    intro f g hfg
    funext x
    have h := congrFun hfg ⟨(), x.2.2⟩
    change (if h : t ∈ (A i).support then f ⟨(), h⟩ else 0) =
      (if h : t ∈ (A i).support then g ⟨(), h⟩ else 0) at h
    rw [dite_eq_left x.2, dite_eq_left x.2] at h
    exact h
  epi_g := by
    rw [NatTrans.epi_iff_epi_app]
    intro t
    rw [ModuleCat.epi_iff_surjective]
    intro y
    by_cases ht : t ∈ (Y (I := I)).support
    · have htP : t ∈ (P i).support := by
        rw [mem_Y.mp ht]
        exact (bot_le : (⊥ : WithBot I) ≤ i)
      refine ⟨fun _ => y ⟨(), ht⟩, ?_⟩
      funext x
      change (if h : t ∈ (P i).support then y ⟨(), ht⟩ else 0) = y x
      rw [dite_eq_left htP]
    · refine ⟨0, ?_⟩
      funext x
      exact absurd x.2 ht

end ExtriangulatedRealization
