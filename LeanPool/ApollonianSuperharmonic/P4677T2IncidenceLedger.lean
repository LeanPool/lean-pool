/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Int.Interval


-- [TABLET NODE: P4677T2IncidenceLedger]

/-!
# P4677T2IncidenceLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4677T2IncidenceLedger :
    (∀ a b, AllowedSubtileIncidence a b ↔ AllowedSubtileIncidence b a) ∧
    (∀ a, ¬ AllowedSubtileIncidence a a) ∧
    (∀ a, Set.Finite {b | AllowedSubtileIncidence a b}) ∧
    (∀ f, Function.Injective (SixSubtileFaceVertices f)) ∧
    (∀ f i j, i ≠ j →
      AllowedSubtileIncidence (SixSubtileFaceVertices f i)
        (SixSubtileFaceVertices f j)) ∧
    (∀ a b, AllowedSubtileIncidence a b →
      ∃ f g : PeriodicSubtileFaceIndex, f ≠ g ∧
        ((∃ i, SixSubtileFaceVertices f i = a) ∧
          (∃ i, SixSubtileFaceVertices f i = b)) ∧
        ((∃ i, SixSubtileFaceVertices g i = a) ∧
          (∃ i, SixSubtileFaceVertices g i = b)) ∧
        ∀ h : PeriodicSubtileFaceIndex,
          ((∃ i, SixSubtileFaceVertices h i = a) ∧
            (∃ i, SixSubtileFaceVertices h i = b)) → h = f ∨ h = g) := by
-- BODY
  classical
  let forward (a b : PeriodicSubtileIndex) : Prop :=
    match a.label, b.label with
    | .A, .B => (b.first = a.first ∧ b.second = a.second) ∨
        (b.first = a.first ∧ b.second = a.second + 1) ∨
        (b.first = a.first + 1 ∧ b.second = a.second + 1)
    | .A, .C => (b.first = a.first ∧ b.second = a.second) ∨
        (b.first = a.first + 1 ∧ b.second = a.second + 1)
    | .A, .D => b.first = a.first ∧ b.second = a.second
    | .A, .E => b.first = a.first ∧ b.second = a.second + 1
    | .A, .F => b.first = a.first ∧ b.second = a.second
    | .B, .C => b.first = a.first ∧ b.second = a.second
    | .B, .D => (b.first = a.first ∧ b.second = a.second) ∨
        (b.first = a.first - 1 ∧ b.second = a.second - 1)
    | .B, .E => b.first = a.first ∧ b.second = a.second
    | .B, .F => b.first = a.first ∧ b.second = a.second - 1
    | .C, .D => b.first = a.first - 1 ∧ b.second = a.second
    | .C, .E => b.first = a.first - 1 ∧ b.second = a.second
    | .C, .F => b.first = a.first ∧ b.second = a.second
    | .D, .E => b.first = a.first ∧ b.second = a.second
    | .D, .F => b.first = a.first + 1 ∧ b.second = a.second
    | _, _ => False
  have normal {a b} (h : AllowedSubtileIncidence a b) :
      forward a b ∨ forward b a := by
    induction h with
    | symm _ ih => exact ih.symm
    | _ => simp [forward]
  have positive (a b : PeriodicSubtileIndex) (h : forward a b) :
      AllowedSubtileIncidence a b := by
    rcases a with ⟨al, m, n⟩
    rcases b with ⟨bl, p, q⟩
    cases al <;> cases bl <;> simp only [forward] at h
    all_goals repeat' (rcases h with h | h)
    all_goals first
      | (convert AllowedSubtileIncidence.AB m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.AB01 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.AB11 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.AC m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.AC11 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.AD m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.AE01 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.AF m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.BC m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.BDm1m1 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.BD m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.BE m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.BF0m1 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.CDm10 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.CEm10 m n using 1 <;> simp
          [PeriodicSubtileIndex.mk.injEq] <;> omega)
      | (convert AllowedSubtileIncidence.CF m n using 1 <;> simp [PeriodicSubtileIndex.mk.injEq]
          <;> omega)
      | (convert AllowedSubtileIncidence.DE m n using 1;
          simp [PeriodicSubtileIndex.mk.injEq]; omega)
      | (convert AllowedSubtileIncidence.DF10 m n using 1; simp
          [PeriodicSubtileIndex.mk.injEq]; omega)
  have normal_iff (a b) : AllowedSubtileIncidence a b ↔ forward a b ∨ forward b a :=
    ⟨normal, fun h => h.elim (positive a b) (fun h => .symm (positive b a h))⟩
  refine ⟨fun a b => ⟨AllowedSubtileIncidence.symm, AllowedSubtileIncidence.symm⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a h
    have hn := normal h
    rcases a with ⟨l, m, n⟩
    cases l <;> simp [forward] at hn
  · intro a
    let labels : Finset SixSubtileLabel := {.A, .B, .C, .D, .E, .F}
    let box := ((labels.product (Finset.Icc (a.first - 1) (a.first + 1))).product
      (Finset.Icc (a.second - 1) (a.second + 1))).image
        (fun p => (⟨p.1.1, p.1.2, p.2⟩ : PeriodicSubtileIndex))
    apply box.finite_toSet.subset
    intro b hb
    have hn := normal hb
    have bounds : a.first - 1 ≤ b.first ∧ b.first ≤ a.first + 1 ∧
        a.second - 1 ≤ b.second ∧ b.second ≤ a.second + 1 := by
      rcases a with ⟨al, m, n⟩
      rcases b with ⟨bl, p, q⟩
      cases al <;> cases bl <;> simp [forward] at hn ⊢ <;> omega
    apply Finset.mem_image.mpr
    refine ⟨((b.label, b.first), b.second), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_Icc.mpr ⟨bounds.1, bounds.2.1⟩⟩,
        Finset.mem_Icc.mpr bounds.2.2⟩
      cases b.label <;> simp [labels]
    · cases b; rfl
  · intro f i j hij
    rcases f with ⟨l, m, n⟩
    cases l <;> fin_cases i <;> fin_cases j <;>
      simp [SixSubtileFaceVertices, PeriodicSubtileIndex.mk.injEq] at hij ⊢
  · intro f i j hij
    rcases f with ⟨l, m, n⟩
    cases l <;> fin_cases i <;> fin_cases j <;> try contradiction
    all_goals rw [normal_iff]
    all_goals simp [SixSubtileFaceVertices, forward]
  · intro a b hab
    have occurs (f : PeriodicSubtileFaceIndex) (a : PeriodicSubtileIndex) :
        (∃ i, SixSubtileFaceVertices f i = a) ↔
          SixSubtileFaceVertices f 0 = a ∨
          SixSubtileFaceVertices f 1 = a ∨ SixSubtileFaceVertices f 2 = a := by
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
      · rintro (h | h | h)
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
    induction hab
    case symm a b hab ih =>
      obtain ⟨f, g, hfg, hf, hg, hu⟩ := ih
      exact ⟨f, g, hfg, ⟨hf.2, hf.1⟩, ⟨hg.2, hg.1⟩,
        fun h hh => hu h ⟨hh.2, hh.1⟩⟩
    case' AB m n => refine ⟨⟨.I1, m, n⟩, ⟨.I2, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' AB01 m n => refine ⟨⟨.J1, m, n⟩, ⟨.J2, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' AB11 m n => refine ⟨⟨.J3, m, n⟩, ⟨.J4, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' AC m n => refine ⟨⟨.I1, m, n⟩, ⟨.I3, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' AC11 m n => refine ⟨⟨.J3, m, n⟩, ⟨.J5, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' AD m n => refine ⟨⟨.I2, m, n⟩, ⟨.J4, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' AE01 m n => refine ⟨⟨.J1, m, n⟩, ⟨.J5, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' AF m n => refine ⟨⟨.I3, m, n⟩, ⟨.J2, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' BC m n => refine ⟨⟨.I1, m, n⟩, ⟨.J3, m - 1, n - 1⟩, ?_, ?_, ?_, ?_⟩
    case' BDm1m1 m n => refine ⟨⟨.J4, m - 1, n - 1⟩, ⟨.J6, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' BD m n => refine ⟨⟨.I2, m, n⟩, ⟨.I4, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' BE m n => refine ⟨⟨.I4, m, n⟩, ⟨.J1, m, n - 1⟩, ?_, ?_, ?_, ?_⟩
    case' BF0m1 m n => refine ⟨⟨.J2, m, n - 1⟩, ⟨.J6, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' CDm10 m n => refine ⟨⟨.J7, m, n⟩, ⟨.J8, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' CEm10 m n => refine ⟨⟨.J5, m - 1, n - 1⟩, ⟨.J7, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' CF m n => refine ⟨⟨.I3, m, n⟩, ⟨.J8, m, n⟩, ?_, ?_, ?_, ?_⟩
    case' DE m n => refine ⟨⟨.I4, m, n⟩, ⟨.J7, m + 1, n⟩, ?_, ?_, ?_, ?_⟩
    case' DF10 m n => refine ⟨⟨.J6, m + 1, n + 1⟩, ⟨.J8, m + 1, n⟩, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (solve | (try simp only [occurs]); simp [SixSubtileFaceVertices,
          PeriodicSubtileIndex.mk.injEq, PeriodicSubtileFaceIndex.mk.injEq])
      | (intro h hh
         simp only [occurs] at hh
         rcases h with ⟨hl, p, q⟩
         cases hl <;>
           simp [SixSubtileFaceVertices,
             PeriodicSubtileIndex.mk.injEq, PeriodicSubtileFaceIndex.mk.injEq] at hh ⊢ <;>
           omega)

end ApollonianSuperharmonic

end
