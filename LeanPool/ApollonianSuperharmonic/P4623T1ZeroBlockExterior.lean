/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3161T1AggregateComplementConnectivity

-- [TABLET NODE: P4623T1ZeroBlockExterior]

/-!
# P4623T1ZeroBlockExterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4623T1ZeroBlockExterior :
    let K : Finset PeriodicSubtileIndex :=
      {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
        ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
    ∀ S : Finset PeriodicSubtileIndex,
      (S = K ∨ ∃ d ∈ K, S = K.erase d) →
      ∀ a ∉ S, ∀ b ∉ S,
        Relation.ReflTransGen
          (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∉ S ∧ y ∉ S) a b := by
-- BODY
  classical
  dsimp only
  let K : Finset PeriodicSubtileIndex :=
    {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
      ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}
  have memK (a : PeriodicSubtileIndex) :
      a ∈ K ↔ (a.first, a.second) ∈ ({(0, 0)} : Finset (Int × Int)) := by
    rcases a with ⟨l, m, n⟩
    cases l <;> simp [K, PeriodicSubtileIndex.mk.injEq]
  have outside (a b : PeriodicSubtileIndex) (ha : a ∉ K) (hb : b ∉ K) :
      Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∉ K ∧ y ∉ K) a b := by
    exact Relation.ReflTransGen.mono
      (fun x y e ↦ ⟨e.1, fun h ↦ e.2.1 ((memK x).mp h),
        fun h ↦ e.2.2 ((memK y).mp h)⟩) a b
      (P3161T1AggregateComplementConnectivity
        {(0, 0), (1, 0), (0, -1)} {(0, 0)} (by decide)
        (by decide) a b (fun h ↦ ha ((memK a).mpr h))
        (fun h ↦ hb ((memK b).mpr h)))
  have attachment (d : PeriodicSubtileIndex) (hd : d ∈ K) :
      ∃ e, e ∉ K ∧ AllowedSubtileIncidence d e := by
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨.B, 0, 1⟩, by decide, .AB01 0 0⟩
    · exact ⟨⟨.D, -1, -1⟩, by decide, by
        simpa using AllowedSubtileIncidence.BDm1m1 0 0⟩
    · exact ⟨⟨.D, -1, 0⟩, by decide, by
        simpa using AllowedSubtileIncidence.CDm10 0 0⟩
    · exact ⟨⟨.F, 1, 0⟩, by decide, .DF10 0 0⟩
    · exact ⟨⟨.C, 1, 0⟩, by decide, (AllowedSubtileIncidence.CEm10 1 0).symm⟩
    · exact ⟨⟨.B, 0, 1⟩, by decide, (AllowedSubtileIncidence.BF0m1 0 1).symm⟩
  intro S hS
  rcases hS with rfl | ⟨d, hd, rfl⟩
  · intro a ha b hb
    exact outside a b ha hb
  · let R := fun x y ↦ AllowedSubtileIncidence x y ∧
        x ∉ K.erase d ∧ y ∉ K.erase d
    have lift {a b} (h : Relation.ReflTransGen
        (fun x y ↦ AllowedSubtileIncidence x y ∧ x ∉ K ∧ y ∉ K) a b) :
        Relation.ReflTransGen R a b :=
      Relation.ReflTransGen.mono
        (fun x y e ↦ ⟨e.1, fun h ↦ e.2.1 (Finset.mem_of_mem_erase h),
          fun h ↦ e.2.2 (Finset.mem_of_mem_erase h)⟩) a b h
    have attach (a : PeriodicSubtileIndex) (ha : a ∉ K.erase d) :
        ∃ e, e ∉ K ∧ Relation.ReflTransGen R a e := by
      by_cases h : a ∈ K
      · have had : a = d := by
          by_contra hne
          exact ha (Finset.mem_erase.mpr ⟨hne, h⟩)
        subst a
        obtain ⟨e, he, hde⟩ := attachment d hd
        exact ⟨e, he, .single ⟨hde, ha,
          fun h ↦ he (Finset.mem_of_mem_erase h)⟩⟩
      · exact ⟨a, h, .refl⟩
    intro a ha b hb
    obtain ⟨a', ha', hpa⟩ := attach a ha
    obtain ⟨b', hb', hpb⟩ := attach b hb
    have reverse : Relation.ReflTransGen R b' b := by
      clear hb'
      induction hpb with
      | refl => exact .refl
      | tail _ e ih => exact (Relation.ReflTransGen.single ⟨e.1.symm, e.2.2, e.2.1⟩).trans ih
    exact hpa.trans ((lift (outside a' b' ha' hb')).trans reverse)

end ApollonianSuperharmonic

end
