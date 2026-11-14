/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P3889T1TwoRaySectorDecomposition
public import LeanPool.ApollonianSuperharmonic.P3934T1LocalSide
public import Mathlib.Analysis.Normed.Module.Convex

-- [TABLET NODE: P3934T1SectorContinuation]

/-!
# P3934T1SectorContinuation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SectorContinuationGeometry

private theorem hdet_cases :
    ∀ (u : Real × Real), ∀ (v : Real × Real), (‖u‖ = 1) → ((‖v‖ = 1) → ((u ≠ v) → (
    let det :
        (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    (u.1 ≠ 0 ∨ u.2 ≠ 0) → (det u v ≠ 0 ∨ v = -u)))) := by
  classical
  intro u v hu hv huv det hcoord
  by_cases hd : det u v ≠ 0
  · exact Or.inl hd
  · right
    have hdet0 : u.1 * v.2 - u.2 * v.1 = 0 := by
      simpa [det] using hd
    have hscalar : ∃ k : Real, v = k • u := by
      rcases hcoord with h1 | h2
      · refine ⟨v.1 / u.1, ?_⟩
        apply Prod.ext
        · simp [div_eq_mul_inv, h1]
        · dsimp
          field_simp
          nlinarith [hdet0]
      · refine ⟨v.2 / u.2, ?_⟩
        apply Prod.ext
        · dsimp
          field_simp [h2]
          nlinarith [hdet0]
        · simp [div_eq_mul_inv, h2]
    obtain ⟨k, hk⟩ := hscalar
    have hkabs : |k| = 1 := by
      have hvnorm := hv
      rw [hk, norm_smul, Real.norm_eq_abs, hu] at hvnorm
      nlinarith
    have hk2 : k ^ 2 = 1 := by nlinarith [sq_abs k]
    have hfactor : (k - 1) * (k + 1) = 0 := by nlinarith [hk2]
    rcases mul_eq_zero.mp hfactor with hkone | hkminus
    · have hkone' : k = 1 := by linarith
      have huv' : v = u := by rw [hk, hkone']; simp
      exact False.elim (huv huv'.symm)
    · have hkminus' : k = -1 := by linarith
      rw [hk, hkminus']
      simp

private theorem hrep :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) →
        (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    (0 < d') → (
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    (∀ (y : Real × Real), d' • y = B (x + y) • a + A (x + y) • b) → (∀ (p : Real × Real), p - x =
        (B p / d') • a + (A p / d') • b)) := by
  classical
  intro x u v det d a b d' hdpos A B hdetid p
  have hy := hdetid (p - x)
  have hy' : d' • (p - x) = B p • a + A p • b := by simpa using hy
  have hd' : d' ≠ 0 := ne_of_gt hdpos
  have hmul := congrArg (fun y : Real × Real => d'⁻¹ • y) hy'
  calc
    p - x = d'⁻¹ • (d' • (p - x)) := by simp [smul_smul, hd']
    _ = d'⁻¹ • (B p • a + A p • b) := hmul
    _ = (B p / d') • a + (A p / d') • b := by
      simp [smul_add, smul_smul, div_eq_mul_inv, mul_comm]

private theorem hRayShape :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) →
        (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    (0 < d') → (
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) → ((∀ (t : Real), A (x + t • a) = 0) → ((∀ (t : Real), B
        (x + t • a) = t * d') → ((∀ (t : Real), A (x + t • b) = t * d') → ((∀ (t : Real), B (x +
        t • b) = 0) → (
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    ∀ (p : Real × Real), (p ∈ Rays) → ((A p = 0 ∧ 0 ≤ B p) ∨ (B p = 0 ∧ 0 ≤ A
            p)))))))) := by
  classical
  intro x u v det d a b d' hdpos A B horder hAa hBa hAb hBb Rays p hp
  change p ∈ {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
    {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v} at hp
  rcases hp with hp | hp
  · rcases hp with ⟨t, ht, rfl⟩
    rcases horder with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
    · have h1 : A (x + t • u) = 0 := by simpa [haEq] using hAa t
      have h2 : B (x + t • u) = t * d' := by simpa [haEq] using hBa t
      left
      exact ⟨h1, by rw [h2]; exact mul_nonneg ht (le_of_lt hdpos)⟩
    · have h1 : B (x + t • u) = 0 := by simpa [hbEq] using hBb t
      have h2 : A (x + t • u) = t * d' := by simpa [hbEq] using hAb t
      right
      exact ⟨h1, by rw [h2]; exact mul_nonneg ht (le_of_lt hdpos)⟩
  · rcases hp with ⟨t, ht, rfl⟩
    rcases horder with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
    · have h1 : B (x + t • v) = 0 := by simpa [hbEq] using hBb t
      have h2 : A (x + t • v) = t * d' := by simpa [hbEq] using hAb t
      right
      exact ⟨h1, by rw [h2]; exact mul_nonneg ht (le_of_lt hdpos)⟩
    · have h1 : A (x + t • v) = 0 := by simpa [haEq] using hAa t
      have h2 : B (x + t • v) = t * d' := by simpa [haEq] using hBa t
      left
      exact ⟨h1, by rw [h2]; exact mul_nonneg ht (le_of_lt hdpos)⟩

private theorem hEsubsetAt411 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    (0 < d') → (
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (∀ (k : Real), (0 ≤ k) → (x + k • a ∈ ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪ {p | ∃ t :
        Real, 0 ≤ t ∧ p = x + t • v}))) → ((∀ (k : Real), (0 ≤ k) → (x + k • b ∈ ({p | ∃ t :
        Real, 0 ≤ t ∧ p = x + t • u} ∪ {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}))) → ((∀ (p : Real
        × Real), (A p = 0) → (p = x + (B p / d') • a)) → ((∀ (p : Real × Real), (B p = 0) → (p =
        x + (A p / d') • b)) → (
    E.left ∪ E.right ⊆ C₁ ∪ C₂))))) := by
  classical
  intro x r u v E det d a b d' hdpos A B C₁ C D C₂ haRay hbRay hAzero hBzero
  let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
  intro p hp
  have hpout : p ∈ Metric.ball x r \ Rays := by
    rw [E.cover] at hp
    simpa [Rays] using hp
  rcases hpout with ⟨hpball, hnotray⟩
  by_cases hAneg : A p < 0
  · exact Or.inr (Or.inl ⟨hpball, hAneg⟩)
  · by_cases hBneg : B p < 0
    · exact Or.inr (Or.inr ⟨hpball, hBneg⟩)
    · have hAnonneg : 0 ≤ A p := le_of_not_gt hAneg
      have hBnonneg : 0 ≤ B p := le_of_not_gt hBneg
      by_cases hA0 : A p = 0
      · have hkray : 0 ≤ B p / d' := div_nonneg hBnonneg (le_of_lt hdpos)
        have hray := haRay (B p / d') hkray
        rw [← hAzero p hA0] at hray
        exact (hnotray hray).elim
      · by_cases hB0 : B p = 0
        · have hkray : 0 ≤ A p / d' := div_nonneg hAnonneg (le_of_lt hdpos)
          have hray := hbRay (A p / d') hkray
          rw [← hBzero p hB0] at hray
          exact (hnotray hray).elim
        · have hApos : 0 < A p := lt_of_le_of_ne hAnonneg (Ne.symm hA0)
          have hBpos : 0 < B p := lt_of_le_of_ne hBnonneg (Ne.symm hB0)
          exact Or.inl ⟨⟨hpball, hApos⟩, hBpos⟩

private theorem hdisAt436 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    Disjoint C₁ C₂ := by
  classical
  intro x r u v det d a b A B C₁ C D C₂
  apply Set.disjoint_left.mpr
  intro p hp₁ hp₂
  have hpA : 0 < A p := hp₁.1.2
  have hpB : 0 < B p := hp₁.2
  rcases hp₂ with hpC | hpD
  · rcases hpC with ⟨_, hpC⟩
    exact (not_lt_of_ge (le_of_lt hpA)) hpC
  · rcases hpD with ⟨_, hpD⟩
    exact (not_lt_of_ge (le_of_lt hpB)) hpD

private theorem classify :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (IsOpen C₁) → ((IsOpen C₂) → ((Disjoint C₁ C₂) → (∀ (S : Set (Real × Real)), (IsConnected S)
        → ((S ⊆ C₁ ∪ C₂) → (S ⊆ C₁ ∨ S ⊆ C₂))))) := by
  classical
  intro x r u v det d a b A B C₁ C D C₂ hC₁open hC₂open hdis S hS hsub
  by_cases hm : (S ∩ C₁).Nonempty
  · left
    exact hS.isPreconnected.subset_left_of_subset_union
      hC₁open hC₂open hdis hsub hm
  · right
    intro p hp
    rcases hsub hp with hp₁ | hp₂
    · exact (hm ⟨p, hp, hp₁⟩).elim
    · exact hp₂

private theorem hC₂off :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (∀ (p : Real × Real), (p ∈ Rays) → ((A p = 0 ∧ 0 ≤ B p) ∨ (B p = 0 ∧ 0 ≤ A p))) → (C₂ ⊆
        Metric.ball x r \ Rays) := by
  classical
  intro x r u v det d a b A B C D C₂ Rays hRayShape p hp
  rcases hp with hpC | hpD
  · rcases hpC with ⟨hpball, hAneg⟩
    change A p < 0 at hAneg
    refine ⟨hpball, ?_⟩
    intro hpr
    have hz := hRayShape p hpr
    rcases hz with ⟨hA0, _⟩ | ⟨hB0, hApos⟩
    · exact (ne_of_lt hAneg) hA0
    · exact (not_lt_of_ge hApos) hAneg
  · rcases hpD with ⟨hpball, hBneg⟩
    change B p < 0 at hBneg
    refine ⟨hpball, ?_⟩
    intro hpr
    have hz := hRayShape p hpr
    rcases hz with ⟨hA0, hBnonneg⟩ | ⟨hB0, _⟩
    · exact (not_lt_of_ge hBnonneg) hBneg
    · exact (ne_of_lt hBneg) hB0

private theorem horderComponentsAt496 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    let qpos : Real × Real := x + (r / 4) • (a + b)
    let qneg : Real × Real := x - (r / 4) • (a + b)
    (Disjoint C₁ C₂) → ((qpos ∈ E.left ∪ E.right) → ((qneg ∈ E.left ∪ E.right) → ((qpos ∈ C₁) →
        ((qneg ∈ C₂) → ((E.left ⊆ C₁ ∨ E.left ⊆ C₂) → ((E.right ⊆ C₁ ∨ E.right ⊆ C₂) → ((E.left ⊆
        C₁ ∧ E.right ⊆ C₂) ∨ (E.left ⊆ C₂ ∧ E.right ⊆ C₁)))))))) := by
  classical
  intro x r u v E det d a b A B C₁ C D C₂ qpos qneg hdis hqposE hqnegE hqposC₁ hqnegC₂ hleftCases
      hrightCases
  rcases hleftCases with hL₁ | hL₂
  · rcases hrightCases with hR₁ | hR₂
    · rcases hqnegE with hqL | hqR
      · exact False.elim ((Set.disjoint_left.mp hdis (hL₁ hqL) hqnegC₂).elim)
      · exact False.elim ((Set.disjoint_left.mp hdis (hR₁ hqR) hqnegC₂).elim)
    · exact Or.inl ⟨hL₁, hR₂⟩
  · rcases hrightCases with hR₁ | hR₂
    · exact Or.inr ⟨hL₂, hR₁⟩
    · rcases hqposE with hqL | hqR
      · exact False.elim ((Set.disjoint_left.mp hdis hqposC₁ (hL₂ hqL)).elim)
      · exact False.elim ((Set.disjoint_left.mp hdis hqposC₁ (hR₂ hqR)).elim)

private theorem hcomponentEqAt509 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (Disjoint C₁ C₂) → ((C₁ ⊆ Metric.ball x r \ Rays) → ((C₂ ⊆ Metric.ball x r \ Rays) →
        (((E.left ⊆ C₁ ∧ E.right ⊆ C₂) ∨ (E.left ⊆ C₂ ∧ E.right ⊆ C₁)) → ((E.left = C₁ ∧ E.right
        = C₂) ∨ (E.left = C₂ ∧ E.right = C₁))))) := by
  classical
  intro x r u v E det d a b A B C₁ C D C₂ Rays hdis hC₁off hC₂off horderComponents
  rcases horderComponents with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · left
    constructor
    · apply Set.Subset.antisymm hL
      intro p hp
      have hpE : p ∈ E.left ∪ E.right := by rw [E.cover]; exact hC₁off hp
      exact hpE.elim (fun hpL => hpL) fun hpR =>
        (Set.disjoint_left.mp hdis hp (hR hpR)).elim
    · apply Set.Subset.antisymm hR
      intro p hp
      have hpE : p ∈ E.left ∪ E.right := by rw [E.cover]; exact hC₂off hp
      exact hpE.elim (fun hpL =>
        (Set.disjoint_left.mp hdis (hL hpL) hp).elim) fun hpR => hpR
  · right
    constructor
    · apply Set.Subset.antisymm hL
      intro p hp
      have hpE : p ∈ E.left ∪ E.right := by rw [E.cover]; exact hC₂off hp
      exact hpE.elim (fun hpL => hpL) fun hpR =>
        (Set.disjoint_left.mp hdis (hR hpR) hp).elim
    · apply Set.Subset.antisymm hR
      intro p hp
      have hpE : p ∈ E.left ∪ E.right := by rw [E.cover]; exact hC₁off hp
      exact hpE.elim (fun hpL =>
        (Set.disjoint_left.mp hdis hp (hL hpL)).elim) fun hpR => hpR

private theorem sampleA :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    (0 < d') → ((‖a‖ = 1) → (
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (Continuous B) → ((∀ (t : Real), B (x + t • a) = t * d') → (∀ (t : Real), ∀ (δ : Real), (0 <
        t) → ((0 < δ) → ((Metric.ball (x + t • a) δ ⊆ Metric.ball x r) → (∃ qpos' qneg', qpos' ∈
        Metric.ball (x + t • a) δ ∧
        qneg' ∈ Metric.ball (x + t • a) δ ∧ qpos' ∈ C₁ ∧ qneg' ∈ C₂ ∧
        0 < det a (qpos' - (x + t • a)) ∧
        det a (qneg' - (x + t • a)) < 0))))))) := by
  classical
  intro x r u v det d a b d' hdpos ha A B C₁ C D C₂ hBcont hBa t δ ht hδ hball
  let z := x + t • a
  have hBz : 0 < B z := by rw [show B z = t * d' by simpa [z] using hBa t]; exact mul_pos ht hdpos
  have hWopen : IsOpen {q : Real × Real | 0 < B q} := isOpen_Ioi.preimage hBcont
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds hBz)
  let ε := min δ η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ η; linarith
  have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
  let j : Real × Real := (-a.2, a.1)
  have hjnorm : ‖j‖ = 1 := by
    dsimp [j]
    simpa [Prod.norm_def, Real.norm_eq_abs, max_comm] using ha
  have haNe : a ≠ (0, 0) := by
    intro h
    rw [h] at ha
    norm_num at ha
  have hsq : 0 < a.1 ^ 2 + a.2 ^ 2 := by
    by_contra h
    have hle : a.1 ^ 2 + a.2 ^ 2 ≤ 0 := le_of_not_gt h
    have h1sq : a.1 ^ 2 = 0 := by nlinarith only [hle, sq_nonneg a.2]
    have h2sq : a.2 ^ 2 = 0 := by nlinarith only [hle, sq_nonneg a.1]
    have h1 : a.1 = 0 := by nlinarith only [h1sq]
    have h2 : a.2 = 0 := by nlinarith only [h2sq]
    exact haNe (Prod.ext h1 h2)
  let qplus' := z + ε • j
  let qminus' := z - ε • j
  have hqplusBall : qplus' ∈ Metric.ball z δ := by
    change dist qplus' z < δ
    rw [dist_eq_norm]
    have heq : qplus' - z = ε • j := by simp [qplus']
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hjnorm]
    simpa using hεδ
  have hqminusBall : qminus' ∈ Metric.ball z δ := by
    change dist qminus' z < δ
    rw [dist_eq_norm]
    have heq : qminus' - z = -(ε • j) := by simp [qminus', sub_eq_add_neg]
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hjnorm]
    simpa using hεδ
  have hqplusB : 0 < B qplus' := hηsub (by
    change dist qplus' z < η
    rw [dist_eq_norm]
    have heq : qplus' - z = ε • j := by simp [qplus']
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hjnorm]
    simpa using hεη)
  have hAplus : A qplus' = ε * (a.1 ^ 2 + a.2 ^ 2) := by
    dsimp [A, qplus', z, j, det]
    ring
  have hAminus : A qminus' = -(ε * (a.1 ^ 2 + a.2 ^ 2)) := by
    dsimp [A, qminus', z, j, det]
    ring
  have hshift (q : Real × Real) : A q = det a (q - z) := by
    dsimp [A, z, det]
    ring
  have hdetplus : 0 < det a (qplus' - z) := by
    rw [← hshift, hAplus]
    exact mul_pos hε hsq
  have hdetminus : det a (qminus' - z) < 0 := by
    rw [← hshift, hAminus]
    exact neg_neg_of_pos (mul_pos hε hsq)
  have hqplusX : qplus' ∈ Metric.ball x r := hball hqplusBall
  have hqminusX : qminus' ∈ Metric.ball x r := hball hqminusBall
  have hAplusPos : 0 < A qplus' := by rw [hAplus]; exact mul_pos hε hsq
  have hAminusNeg : A qminus' < 0 := by rw [hAminus]; exact neg_neg_of_pos (mul_pos hε hsq)
  exact ⟨qplus', qminus', hqplusBall, hqminusBall,
    ⟨⟨hqplusX, hAplusPos⟩, hqplusB⟩,
    Or.inl ⟨hqminusX, hAminusNeg⟩, hdetplus, hdetminus⟩

private theorem sampleB :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    (0 < d') → ((‖b‖ = 1) → (
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (Continuous A) → ((∀ (t : Real), A (x + t • b) = t * d') → (∀ (t : Real), ∀ (δ : Real), (0 <
        t) → ((0 < δ) → ((Metric.ball (x + t • b) δ ⊆ Metric.ball x r) → (∃ qpos' qneg', qpos' ∈
        Metric.ball (x + t • b) δ ∧
        qneg' ∈ Metric.ball (x + t • b) δ ∧ qpos' ∈ C₂ ∧ qneg' ∈ C₁ ∧
        0 < det b (qpos' - (x + t • b)) ∧
        det b (qneg' - (x + t • b)) < 0))))))) := by
  classical
  intro x r u v det d a b d' hdpos hb A B C₁ C D C₂ hAcont hAb t δ ht hδ hball
  let z := x + t • b
  have hAz : 0 < A z := by rw [show A z = t * d' by simpa [z] using hAb t]; exact mul_pos ht hdpos
  have hWopen : IsOpen {q : Real × Real | 0 < A q} := isOpen_Ioi.preimage hAcont
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds hAz)
  let ε := min δ η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ η; linarith
  have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
  let j : Real × Real := (-b.2, b.1)
  have hjnorm : ‖j‖ = 1 := by
    dsimp [j]
    simpa [Prod.norm_def, Real.norm_eq_abs, max_comm] using hb
  have hbNe : b ≠ (0, 0) := by
    intro h
    rw [h] at hb
    norm_num at hb
  have hsq : 0 < b.1 ^ 2 + b.2 ^ 2 := by
    by_contra h
    have hle : b.1 ^ 2 + b.2 ^ 2 ≤ 0 := le_of_not_gt h
    have h1sq : b.1 ^ 2 = 0 := by nlinarith only [hle, sq_nonneg b.2]
    have h2sq : b.2 ^ 2 = 0 := by nlinarith only [hle, sq_nonneg b.1]
    have h1 : b.1 = 0 := by nlinarith only [h1sq]
    have h2 : b.2 = 0 := by nlinarith only [h2sq]
    exact hbNe (Prod.ext h1 h2)
  let qplus' := z + ε • j
  let qminus' := z - ε • j
  have hqplusBall : qplus' ∈ Metric.ball z δ := by
    change dist qplus' z < δ
    rw [dist_eq_norm]
    have heq : qplus' - z = ε • j := by simp [qplus']
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hjnorm]
    simpa using hεδ
  have hqminusBall : qminus' ∈ Metric.ball z δ := by
    change dist qminus' z < δ
    rw [dist_eq_norm]
    have heq : qminus' - z = -(ε • j) := by simp [qminus', sub_eq_add_neg]
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hjnorm]
    simpa using hεδ
  have hqminusA : 0 < A qminus' := hηsub (by
    change dist qminus' z < η
    rw [dist_eq_norm]
    have heq : qminus' - z = -(ε • j) := by simp [qminus', sub_eq_add_neg]
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hjnorm]
    simpa using hεη)
  have hBplus : B qplus' = -(ε * (b.1 ^ 2 + b.2 ^ 2)) := by
    dsimp [B, qplus', z, j, det]
    ring
  have hBminus : B qminus' = ε * (b.1 ^ 2 + b.2 ^ 2) := by
    dsimp [B, qminus', z, j, det]
    ring
  have hshift (q : Real × Real) : B q = -det b (q - z) := by
    dsimp [B, z, det]
    ring
  have hdetplus : 0 < det b (qplus' - z) := by
    have heq : det b (qplus' - z) = -B qplus' := by linarith [hshift qplus']
    rw [heq, hBplus]
    nlinarith [mul_pos hε hsq]
  have hdetminus : det b (qminus' - z) < 0 := by
    have heq : det b (qminus' - z) = -B qminus' := by linarith [hshift qminus']
    rw [heq, hBminus]
    exact neg_neg_of_pos (mul_pos hε hsq)
  have hqplusX : qplus' ∈ Metric.ball x r := hball hqplusBall
  have hqminusX : qminus' ∈ Metric.ball x r := hball hqminusBall
  have hBplusNeg : B qplus' < 0 := by rw [hBplus]; exact neg_neg_of_pos (mul_pos hε hsq)
  have hBminusPos : 0 < B qminus' := by rw [hBminus]; exact mul_pos hε hsq
  exact ⟨qplus', qminus', hqplusBall, hqminusBall,
    Or.inr ⟨hqplusX, hBplusNeg⟩,
    ⟨⟨hqminusX, hqminusA⟩, hBminusPos⟩, hdetplus, hdetminus⟩

private theorem aLocalC₁ :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (∀ (t : Real), ∀ (δ : Real), (0 < t) → ((0 < δ) → ((Metric.ball (x + t • a) δ ⊆ Metric.ball x
        r) → (∃ qpos' qneg', qpos' ∈ Metric.ball (x + t • a) δ ∧ qneg' ∈ Metric.ball (x + t • a)
        δ ∧ qpos' ∈ C₁ ∧ qneg' ∈ C₂ ∧ 0 < det a (qpos' - (x + t • a)) ∧ det a (qneg' - (x + t •
        a)) < 0)))) → ((a = u ∨ a = v) → (∀ (t : Real), (0 < t) → ((t < r) → ((E.left = C₁) →
        (P3934T1LocalSide E.left (x + t • a) a true ∧
        P3934T1LocalSide E.right (x + t • a) a false))))) := by
  classical
  intro x r u v E det d a b A B C₁ C D C₂ sampleA haRayEq t ht htr hL
  obtain ⟨δ, hδ, hball, hcases⟩ := E.sides a haRayEq t ht htr
  obtain ⟨qp, qn, hqpδ, hqnδ, hqpC₁, hqnC₂, hqpdet, hqndet⟩ :=
    sampleA t δ ht hδ hball
  rcases hcases with ⟨hLp, hRn⟩ | ⟨hRp, hLn⟩
  · exact ⟨⟨δ, hδ, hLp⟩, ⟨δ, hδ, hRn⟩⟩
  · have hqleft : qp ∈ E.left ∩ Metric.ball (x + t • a) δ := by
      constructor
      · rw [hL]
        exact hqpC₁
      · exact hqpδ
    rw [hLn] at hqleft
    rcases hqleft with ⟨_, hbad⟩
    exact False.elim ((not_lt_of_ge (le_of_lt hqpdet)) hbad)

private theorem aLocalC₂ :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (∀ (t : Real), ∀ (δ : Real), (0 < t) → ((0 < δ) → ((Metric.ball (x + t • a) δ ⊆ Metric.ball x
        r) → (∃ qpos' qneg', qpos' ∈ Metric.ball (x + t • a) δ ∧ qneg' ∈ Metric.ball (x + t • a)
        δ ∧ qpos' ∈ C₁ ∧ qneg' ∈ C₂ ∧ 0 < det a (qpos' - (x + t • a)) ∧ det a (qneg' - (x + t •
        a)) < 0)))) → ((a = u ∨ a = v) → (∀ (t : Real), (0 < t) → ((t < r) → ((E.left = C₂) →
        (P3934T1LocalSide E.left (x + t • a) a false ∧
        P3934T1LocalSide E.right (x + t • a) a true))))) := by
  classical
  intro x r u v E det d a b A B C₁ C D C₂ sampleA haRayEq t ht htr hL
  obtain ⟨δ, hδ, hball, hcases⟩ := E.sides a haRayEq t ht htr
  obtain ⟨qp, qn, hqpδ, hqnδ, hqpC₁, hqnC₂, hqpdet, hqndet⟩ :=
    sampleA t δ ht hδ hball
  rcases hcases with ⟨hLp, hRn⟩ | ⟨hRp, hLn⟩
  · have hqleft : qn ∈ E.left ∩ Metric.ball (x + t • a) δ := by
      constructor
      · rw [hL]
        exact hqnC₂
      · exact hqnδ
    rw [hLp] at hqleft
    rcases hqleft with ⟨_, hbad⟩
    exact False.elim ((not_lt_of_ge (le_of_lt hqndet)) hbad)
  · exact ⟨⟨δ, hδ, hLn⟩, ⟨δ, hδ, hRp⟩⟩

private theorem bLocalC₁ :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (∀ (t : Real), ∀ (δ : Real), (0 < t) → ((0 < δ) → ((Metric.ball (x + t • b) δ ⊆ Metric.ball x
        r) → (∃ qpos' qneg', qpos' ∈ Metric.ball (x + t • b) δ ∧ qneg' ∈ Metric.ball (x + t • b)
        δ ∧ qpos' ∈ C₂ ∧ qneg' ∈ C₁ ∧ 0 < det b (qpos' - (x + t • b)) ∧ det b (qneg' - (x + t •
        b)) < 0)))) → ((b = u ∨ b = v) → (∀ (t : Real), (0 < t) → ((t < r) → ((E.left = C₁) →
        (P3934T1LocalSide E.left (x + t • b) b false ∧
        P3934T1LocalSide E.right (x + t • b) b true))))) := by
  classical
  intro x r u v E det d a b A B C₁ C D C₂ sampleB hbRayEq t ht htr hL
  obtain ⟨δ, hδ, hball, hcases⟩ := E.sides b hbRayEq t ht htr
  obtain ⟨qp, qn, hqpδ, hqnδ, hqpC₂, hqnC₁, hqpdet, hqndet⟩ :=
    sampleB t δ ht hδ hball
  rcases hcases with ⟨hLp, hRn⟩ | ⟨hRp, hLn⟩
  · have hqleft : qn ∈ E.left ∩ Metric.ball (x + t • b) δ := by
      constructor
      · rw [hL]
        exact hqnC₁
      · exact hqnδ
    rw [hLp] at hqleft
    rcases hqleft with ⟨_, hbad⟩
    exact False.elim ((not_lt_of_ge (le_of_lt hqndet)) hbad)
  · exact ⟨⟨δ, hδ, hLn⟩, ⟨δ, hδ, hRp⟩⟩

private theorem bLocalC₂ :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (∀ (t : Real), ∀ (δ : Real), (0 < t) → ((0 < δ) → ((Metric.ball (x + t • b) δ ⊆ Metric.ball x
        r) → (∃ qpos' qneg', qpos' ∈ Metric.ball (x + t • b) δ ∧ qneg' ∈ Metric.ball (x + t • b)
        δ ∧ qpos' ∈ C₂ ∧ qneg' ∈ C₁ ∧ 0 < det b (qpos' - (x + t • b)) ∧ det b (qneg' - (x + t •
        b)) < 0)))) → ((b = u ∨ b = v) → (∀ (t : Real), (0 < t) → ((t < r) → ((E.left = C₂) →
        (P3934T1LocalSide E.left (x + t • b) b true ∧
        P3934T1LocalSide E.right (x + t • b) b false))))) := by
  classical
  intro x r u v E det d a b A B C₁ C D C₂ sampleB hbRayEq t ht htr hL
  obtain ⟨δ, hδ, hball, hcases⟩ := E.sides b hbRayEq t ht htr
  obtain ⟨qp, qn, hqpδ, hqnδ, hqpC₂, hqnC₁, hqpdet, hqndet⟩ :=
    sampleB t δ ht hδ hball
  rcases hcases with ⟨hLp, hRn⟩ | ⟨hRp, hLn⟩
  · exact ⟨⟨δ, hδ, hLp⟩, ⟨δ, hδ, hRn⟩⟩
  · have hqleft : qp ∈ E.left ∩ Metric.ball (x + t • b) δ := by
      constructor
      · rw [hL]
        exact hqpC₂
      · exact hqpδ
    rw [hLn] at hqleft
    rcases hqleft with ⟨_, hbad⟩
    exact False.elim ((not_lt_of_ge (le_of_lt hqpdet)) hbad)

private theorem flipSide :
    ∀ (U : Set (Real × Real)), ∀ (z : Real × Real), ∀ (w : Real × Real), ∀ (e : Bool),
        (P3934T1LocalSide U z w e) → (P3934T1LocalSide U z (-w) (!e)) := by
  classical
  intro U z w e h
  rcases h with ⟨ρ, hρ, heq⟩
  dsimp [P3934T1LocalSide] at heq ⊢
  let f := fun q : Real × Real =>
    w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1)
  let g := fun q : Real × Real =>
    (-w).1 * (q.2 - z.2) - (-w).2 * (q.1 - z.1)
  have hfg (q : Real × Real) : g q = -f q := by
    dsimp [f, g]
    simp
    ring
  cases e with
  | false =>
    refine ⟨ρ, hρ, ?_⟩
    calc
      U ∩ Metric.ball z ρ = {q | q ∈ Metric.ball z ρ ∧ f q < 0} := by
        simpa [f] using heq
      _ = {q | q ∈ Metric.ball z ρ ∧ 0 < g q} := by
        ext q
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hb, hf⟩
          exact ⟨hb, by rw [hfg]; linarith⟩
        · rintro ⟨hb, hg⟩
          exact ⟨hb, by rw [hfg] at hg; linarith⟩
  | true =>
    refine ⟨ρ, hρ, ?_⟩
    calc
      U ∩ Metric.ball z ρ = {q | q ∈ Metric.ball z ρ ∧ 0 < f q} := by
        simpa [f] using heq
      _ = {q | q ∈ Metric.ball z ρ ∧ g q < 0} := by
        ext q
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hb, hf⟩
          exact ⟨hb, by rw [hfg]; linarith⟩
        · rintro ⟨hb, hg⟩
          exact ⟨hb, by rw [hfg] at hg; linarith⟩

private theorem hform :
    (by
      classical
      exact
        ∀ (x u v : ℝ × ℝ),
          let det := fun (a b : ℝ × ℝ) => a.1 * b.2 - a.2 * b.1;
          v = -u →
            let A := fun (p : ℝ × ℝ) => det u (p - x);
            ∀ (w : ℝ × ℝ),
              w = u ∨ w = v →
                ∀ (t : ℝ) (q : ℝ × ℝ),
                  -u.1 * (q.2 - (x.2 + t * w.2)) - -u.2 * (q.1 - (x.1 + t * w.1)) = -A q) := by
  classical
  intro x u v det hvneg A w hw t q
  rcases hw with rfl | hwv
  · dsimp [A, det]
    ring
  · rw [hwv, hvneg]
    dsimp [A, det]
    ring

private theorem hlocalP :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    (∀ (w : Real × Real), (w = u ∨ w = v) → (∀ (t : Real), ∀ (q : Real × Real), -u.1 * (q.2 -
        (x.2 + t * w.2)) - -u.2 * (q.1 - (x.1 + t * w.1)) = -A q)) → ((∀ (t : Real), (t < r) → (0
        < r - t)) → ((∀ (w : Real × Real), (‖w‖ = 1) → (∀ (t : Real), (0 < t) → ((t < r) →
        (Metric.ball (x + t • w) (r - t) ⊆ Metric.ball x r)))) → (∀ (w : Real × Real), (w = u ∨ w
        = v) → ((‖w‖ = 1) → (∀ (t : Real), (0 < t) → ((t < r) → (P3934T1LocalSide P (x + t • w)
        (-u) false))))))) := by
  classical
  intro x r u v det A P hform hdelta hball w hw hwNorm t ht htr
  refine ⟨r - t, hdelta t htr, ?_⟩
  dsimp [P]
  ext q
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hbx, hA⟩, hq⟩
    exact ⟨hq, by rw [hform w hw t q]; linarith⟩
  · rintro ⟨hq, hformq⟩
    exact ⟨⟨hball w hwNorm t ht htr hq, by
      rw [hform w hw t q] at hformq
      linarith⟩, hq⟩

private theorem hlocalN :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (∀ (w : Real × Real), (w = u ∨ w = v) → (∀ (t : Real), ∀ (q : Real × Real), -u.1 * (q.2 -
        (x.2 + t * w.2)) - -u.2 * (q.1 - (x.1 + t * w.1)) = -A q)) → ((∀ (t : Real), (t < r) → (0
        < r - t)) → ((∀ (w : Real × Real), (‖w‖ = 1) → (∀ (t : Real), (0 < t) → ((t < r) →
        (Metric.ball (x + t • w) (r - t) ⊆ Metric.ball x r)))) → (∀ (w : Real × Real), (w = u ∨ w
        = v) → ((‖w‖ = 1) → (∀ (t : Real), (0 < t) → ((t < r) → (P3934T1LocalSide N (x + t • w)
        (-u) true))))))) := by
  classical
  intro x r u v det A N hform hdelta hball w hw hwNorm t ht htr
  refine ⟨r - t, hdelta t htr, ?_⟩
  dsimp [N]
  ext q
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hbx, hA⟩, hq⟩
    exact ⟨hq, by rw [hform w hw t q]; linarith⟩
  · rintro ⟨hq, hformq⟩
    exact ⟨⟨hball w hwNorm t ht htr hq, by
      rw [hform w hw t q] at hformq
      linarith⟩, hq⟩

private theorem hcol :
    ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    (u.1 ≠ 0 ∨ u.2 ≠ 0) → (∀ (y : Real × Real), (det u y = 0) → (∃ k : Real, y = k • u)) := by
  classical
  intro u det hcoord y hy
  rcases hcoord with h1 | h2
  · refine ⟨y.1 / u.1, ?_⟩
    apply Prod.ext
    · simp [div_eq_mul_inv, h1]
    · have hy' : u.1 * y.2 - u.2 * y.1 = 0 := by simpa [det] using hy
      dsimp
      field_simp
      nlinarith only [hy']
  · refine ⟨y.2 / u.2, ?_⟩
    apply Prod.ext
    · have hy' : u.1 * y.2 - u.2 * y.1 = 0 := by simpa [det] using hy
      dsimp
      field_simp [h2]
      nlinarith only [hy']
    · simp [div_eq_mul_inv, h2]

private theorem hzeroRay :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) →
        (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    (v = -u) → (
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (∀ (y : Real × Real), (det u y = 0) → (∃ k : Real, y = k • u)) → (∀ (p : Real × Real), (A p =
        0) → (p ∈ Rays))) := by
  classical
  intro x u v det hvneg A Rays hcol p hp
  have hy : det u (p - x) = 0 := by simpa [A] using hp
  obtain ⟨k, hk⟩ := hcol (p - x) hy
  have hpEq : p = x + k • u := by
    calc
      p = x + (p - x) := by simp
      _ = x + k • u := by rw [hk]
  by_cases hk0 : 0 ≤ k
  · exact Or.inl ⟨k, hk0, hpEq⟩
  · have hkneg : k < 0 := lt_of_not_ge hk0
    have hmul : (-k) • v = k • u := by rw [hvneg]; simp
    have hpEq' : p = x + (-k) • v := by rw [hpEq, ← hmul]
    exact Or.inr ⟨-k, le_of_lt (neg_pos.mpr hkneg), hpEq'⟩

private theorem hPoff :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (∀ (p : Real × Real), (p ∈ Rays) → (A p = 0)) → (P ⊆ Metric.ball x r \ Rays) := by
  classical
  intro x r u v det A P Rays hRayAzero p hp
  change p ∈ Metric.ball x r ∧ 0 < A p at hp
  change p ∈ Metric.ball x r ∧ p ∉ Rays
  refine ⟨hp.1, ?_⟩
  intro hpr
  have hzero := hRayAzero p hpr
  have hpA : 0 < A p := hp.2
  rw [hzero] at hpA
  exact (lt_irrefl 0) hpA

private theorem hNoff :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (∀ (p : Real × Real), (p ∈ Rays) → (A p = 0)) → (N ⊆ Metric.ball x r \ Rays) := by
  classical
  intro x r u v det A N Rays hRayAzero p hp
  change p ∈ Metric.ball x r ∧ A p < 0 at hp
  change p ∈ Metric.ball x r ∧ p ∉ Rays
  refine ⟨hp.1, ?_⟩
  intro hpr
  have hzero := hRayAzero p hpr
  have hpA : A p < 0 := hp.2
  rw [hzero] at hpA
  exact (lt_irrefl 0) hpA

private theorem hEsubsetAt1063 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (∀ (p : Real × Real), (A p = 0) → (p ∈ Rays)) → (E.left ∪ E.right ⊆ P ∪ N) := by
  classical
  intro x r u v E det A P N Rays hzeroRay p hp
  change p ∈ P ∨ p ∈ N
  have hpout : p ∈ Metric.ball x r \ Rays := by
    rw [← E.cover]
    exact hp
  rcases hpout with ⟨hpball, hnotray⟩
  by_cases hAneg : A p < 0
  · right
    change p ∈ Metric.ball x r ∧ A p < 0
    exact ⟨hpball, hAneg⟩
  · by_cases hA0 : A p = 0
    · exact False.elim (hnotray (hzeroRay p hA0))
    · left
      change p ∈ Metric.ball x r ∧ 0 < A p
      exact ⟨hpball,
        lt_of_le_of_ne (le_of_not_gt hAneg) (Ne.symm hA0)⟩

private theorem horderComponentsAt1092 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (IsOpen P) → ((IsOpen N) → (
    let j : Real × Real := (-u.2, u.1)
    let qpos : Real × Real := x + (r / 4) • j
    let qneg : Real × Real := x - (r / 4) • j
    (Disjoint P N) → ((E.left ∪ E.right ⊆ P ∪ N) → ((qpos ∈ E.left ∪ E.right) → ((qneg ∈ E.left ∪
        E.right) → ((qpos ∈ P) → ((qneg ∈ N) → ((E.left ⊆ P ∧ E.right ⊆ N) ∨ (E.left ⊆ N ∧
        E.right ⊆ P))))))))) := by
  classical
  intro x r u v E det A P N hPopen hNopen j qpos qneg hdis hEsubset hqposE hqnegE hqposP hqnegN
  rcases hqposE with hqL | hqR
  · have hL : E.left ⊆ P := by
      exact E.left_connected.isPreconnected.subset_left_of_subset_union
        hPopen hNopen hdis (fun p hp => hEsubset (Or.inl hp))
        ⟨qpos, hqL, hqposP⟩
    have hqnegR : qneg ∈ E.right := by
      rcases hqnegE with hqnegL | hqnegR
      · exact (Set.disjoint_left.mp hdis (hL hqnegL) hqnegN).elim
      · exact hqnegR
    have hR : E.right ⊆ N := by
      exact E.right_connected.isPreconnected.subset_right_of_subset_union
        hPopen hNopen hdis (fun p hp => hEsubset (Or.inr hp))
        ⟨qneg, hqnegR, hqnegN⟩
    exact Or.inl ⟨hL, hR⟩
  · have hR : E.right ⊆ P := by
      exact E.right_connected.isPreconnected.subset_left_of_subset_union
        hPopen hNopen hdis (fun p hp => hEsubset (Or.inr hp))
        ⟨qpos, hqR, hqposP⟩
    have hqnegL : qneg ∈ E.left := by
      rcases hqnegE with hqnegL | hqnegR
      · exact hqnegL
      · exact (Set.disjoint_left.mp hdis (hR hqnegR) hqnegN).elim
    have hL : E.left ⊆ N := by
      exact E.left_connected.isPreconnected.subset_right_of_subset_union
        hPopen hNopen hdis (fun p hp => hEsubset (Or.inl hp))
        ⟨qneg, hqnegL, hqnegN⟩
    exact Or.inr ⟨hL, hR⟩

private theorem hEqPN :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (Disjoint P N) → (
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (P ⊆ Metric.ball x r \ Rays) → ((N ⊆ Metric.ball x r \ Rays) → ((E.left ⊆ P) → ((E.right ⊆ N)
        → (E.left = P ∧ E.right = N))))) := by
  classical
  intro x r u v E det A P N hdis Rays hPoff hNoff hL hR
  constructor
  · apply Set.Subset.antisymm hL
    intro p hp
    have hpE : p ∈ E.left ∪ E.right := by
      rw [E.cover]
      exact hPoff hp
    exact hpE.elim (fun h => h) fun h =>
      (Set.disjoint_left.mp hdis hp (hR h)).elim
  · apply Set.Subset.antisymm hR
    intro p hp
    have hpE : p ∈ E.left ∪ E.right := by
      rw [E.cover]
      exact hNoff hp
    exact hpE.elim (fun h =>
      (Set.disjoint_left.mp hdis (hL h) hp).elim) fun h => h

private theorem hEqNP :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) →
        Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (Disjoint P N) → (
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (P ⊆ Metric.ball x r \ Rays) → ((N ⊆ Metric.ball x r \ Rays) → ((E.left ⊆ N) → ((E.right ⊆ P)
        → (E.left = N ∧ E.right = P))))) := by
  classical
  intro x r u v E det A P N hdis Rays hPoff hNoff hL hR
  constructor
  · apply Set.Subset.antisymm hL
    intro p hp
    have hpE : p ∈ E.left ∪ E.right := by
      rw [E.cover]
      exact hNoff hp
    exact hpE.elim (fun h => h) fun h =>
      (Set.disjoint_left.mp hdis (hR h) hp).elim
  · apply Set.Subset.antisymm hR
    intro p hp
    have hpE : p ∈ E.left ∪ E.right := by
      rw [E.cover]
      exact hPoff hp
    exact hpE.elim (fun h =>
      (Set.disjoint_left.mp hdis hp (hL h)).elim) fun h => h

end SectorContinuationGeometry

namespace SectorContinuationFacts

private theorem hu_ne :
    ∀ (u : Real × Real), (‖u‖ = 1) → (u ≠ (0, 0)) := by
  classical
  intro u hu h
  rw [h] at hu
  norm_num at hu

private theorem hcoord :
    ∀ (u : Real × Real), (u ≠ (0, 0)) → (u.1 ≠ 0 ∨ u.2 ≠ 0) := by
  classical
  intro u hu_ne
  by_contra h
  push Not at h
  exact hu_ne (Prod.ext h.1 h.2)

private theorem hdpos :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    (d ≠ 0) → (
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    0 < d') := by
  classical
  intro u v det d hd a b d'
  by_cases hpos : 0 < d
  · simp [d', a, b, hpos, d, det]
  · have hneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
    have hrev : det v u = -d := by dsimp [d, det]; ring
    simp only [d', a, b, ite_eq_right hpos]
    rw [hrev]
    linarith

private theorem hdetid :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    ∀ (y : Real × Real), d' • y = B (x + y) • a + A (x + y) • b := by
  classical
  intro x u v det d a b d' A B y
  apply Prod.ext <;> simp [A, B, d', det, smul_eq_mul] <;> ring

private theorem hAcontAt1316 :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let A : (Real × Real) → Real := fun p => det a (p - x)
    Continuous A := by
  classical
  intro x u v det d a A
  dsimp [A, det]
  fun_prop

private theorem hBcont :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let b : Real × Real := if 0 < d then v else u
    let B : (Real × Real) → Real := fun p => det (p - x) b
    Continuous B := by
  classical
  intro x u v det d b B
  dsimp [B, det]
  fun_prop

private theorem hC₁open :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    (Continuous A) → ((Continuous B) → (IsOpen C₁)) := by
  classical
  intro x r u v det d a b A B C₁ hAcont hBcont
  dsimp [C₁]
  exact (Metric.isOpen_ball.inter (isOpen_Ioi.preimage hAcont)).inter
    (isOpen_Ioi.preimage hBcont)

private theorem hCopen :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (Continuous A) → (IsOpen C) := by
  classical
  intro x r u v det d a A C hAcont
  dsimp [C]
  exact Metric.isOpen_ball.inter (isOpen_Iio.preimage hAcont)

private theorem hDopen :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let b : Real × Real := if 0 < d then v else u
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    (Continuous B) → (IsOpen D) := by
  classical
  intro x r u v det d b B D hBcont
  dsimp [D]
  exact Metric.isOpen_ball.inter (isOpen_Iio.preimage hBcont)

private theorem hC₂open :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let C₂ : Set (Real × Real) := C ∪ D
    (IsOpen C) → ((IsOpen D) → (IsOpen C₂)) := by
  classical
  intro x r u v det d a b A B C D C₂ hCopen hDopen
  dsimp [C₂]
  exact hCopen.union hDopen

private theorem hsumNorm :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    (‖a‖ = 1) → ((‖b‖ = 1) → (‖a + b‖ ≤ 2)) := by
  classical
  intro u v det d a b ha hb
  calc
    ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ = 2 := by rw [ha, hb]; norm_num

private theorem hqposballAt1344 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), (0 < r) → (
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    (‖a + b‖ ≤ 2) → ((0 < r / 4) → (
    let qpos : Real × Real := x + (r / 4) • (a + b)
    qpos ∈ Metric.ball x r))) := by
  classical
  intro x r u v hr det d a b hsumNorm hr4 qpos
  change dist qpos x < r
  rw [dist_eq_norm]
  have hbound : ‖(r / 4) • (a + b)‖ ≤ r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr4]
    nlinarith [hsumNorm]
  have hdiff : qpos - x = (r / 4) • (a + b) := by simp [qpos]
  rw [hdiff]
  linarith

private theorem hAqposAt1353 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let qpos : Real × Real := x + (r / 4) • (a + b)
    A qpos = (r / 4) * d' := by
  classical
  intro x r u v det d a b d' A qpos
  dsimp [A, qpos, det, d']
  ring

private theorem hBqpos :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let qpos : Real × Real := x + (r / 4) • (a + b)
    B qpos = (r / 4) * d' := by
  classical
  intro x r u v det d a b d' B qpos
  dsimp [B, qpos, det, d']
  ring

private theorem hqnegbAt1364 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), (0 < r) → (
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    (‖a + b‖ ≤ 2) → ((0 < r / 4) → (
    let qneg : Real × Real := x - (r / 4) • (a + b)
    qneg ∈ Metric.ball x r))) := by
  classical
  intro x r u v hr det d a b hsumNorm hr4 qneg
  change dist qneg x < r
  rw [dist_eq_norm]
  have hbound : ‖(r / 4) • (a + b)‖ ≤ r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr4]
    nlinarith [hsumNorm]
  have hdiff : qneg - x = -((r / 4) • (a + b)) := by simp [qneg, sub_eq_add_neg]
  rw [hdiff, norm_neg]
  linarith

private theorem hAqnegAt1373 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let qneg : Real × Real := x - (r / 4) • (a + b)
    A qneg = -(r / 4) * d' := by
  classical
  intro x r u v det d a b d' A qneg
  dsimp [A, qneg, det, d']
  ring

private theorem hqnegAAt1379 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let qpos : Real × Real := x + (r / 4) • (a + b)
    (A qpos = (r / 4) * d') → ((0 < A qpos) → (
    let qneg : Real × Real := x - (r / 4) • (a + b)
    (A qneg = -(r / 4) * d') → (A qneg < 0))) := by
  classical
  intro x r u v det d a b d' A qpos hAqpos hqposA qneg hAqneg
  rw [hAqneg]
  nlinarith [hqposA]

private theorem horder :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  classical
  intro u v det d a b
  by_cases hpos : 0 < d
  · left
    constructor <;> simp [a, b, hpos]
  · right
    constructor <;> simp [a, b, hpos]

private theorem haRay :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) → (∀ (k : Real), (0 ≤ k) → (x + k • a ∈ ({p | ∃ t : Real,
        0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}))) := by
  classical
  intro x u v det d a b horder k hk
  rcases horder with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
  · rw [haEq]
    exact Or.inl ⟨k, hk, rfl⟩
  · rw [haEq]
    exact Or.inr ⟨k, hk, rfl⟩

private theorem hbRay :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) → (∀ (k : Real), (0 ≤ k) → (x + k • b ∈ ({p | ∃ t : Real,
        0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}))) := by
  classical
  intro x u v det d a b horder k hk
  rcases horder with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
  · rw [hbEq]
    exact Or.inr ⟨k, hk, rfl⟩
  · rw [hbEq]
    exact Or.inl ⟨k, hk, rfl⟩

private theorem hAa :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let A : (Real × Real) → Real := fun p => det a (p - x)
    ∀ (t : Real), A (x + t • a) = 0 := by
  classical
  intro x u v det d a A t
  dsimp [A, det]
  ring

private theorem hBa :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let B : (Real × Real) → Real := fun p => det (p - x) b
    ∀ (t : Real), B (x + t • a) = t * d' := by
  classical
  intro x u v det d a b d' B t
  dsimp [B, det, d']
  ring

private theorem hAb :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let A : (Real × Real) → Real := fun p => det a (p - x)
    ∀ (t : Real), A (x + t • b) = t * d' := by
  classical
  intro x u v det d a b d' A t
  dsimp [A, det, d']
  ring

private theorem hBb :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let b : Real × Real := if 0 < d then v else u
    let B : (Real × Real) → Real := fun p => det (p - x) b
    ∀ (t : Real), B (x + t • b) = 0 := by
  classical
  intro x u v det d b B t
  dsimp [B, det]
  ring

private theorem hAzero :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    (∀ (p : ℝ × ℝ), p - x = (B p / d') • a + (A p / d') • b) → (∀ (p : Real × Real), (A p = 0) →
        (p = x + (B p / d') • a)) := by
  classical
  intro x u v det d a b d' A B hrep p hAp
  calc
    p = x + (p - x) := by simp
    _ = x + ((B p / d') • a + (A p / d') • b) := by rw [hrep]
    _ = x + (B p / d') • a := by rw [hAp]; simp

private theorem hBzero :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let d' := det a b
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    (∀ (p : ℝ × ℝ), p - x = (B p / d') • a + (A p / d') • b) → (∀ (p : Real × Real), (B p = 0) →
        (p = x + (A p / d') • b)) := by
  classical
  intro x u v det d a b d' A B hrep p hBp
  calc
    p = x + (p - x) := by simp
    _ = x + ((B p / d') • a + (A p / d') • b) := by rw [hrep]
    _ = x + (A p / d') • b := by rw [hBp]; simp

private theorem hC₁off :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (∀ p ∈ Rays, A p = (0 : ℝ) ∧ (0 : ℝ) ≤ B p ∨ B p = (0 : ℝ) ∧ (0 : ℝ) ≤ A p) → (C₁ ⊆
        Metric.ball x r \ Rays) := by
  classical
  intro x r u v det d a b A B C₁ Rays hRayShape p hp
  refine ⟨hp.1.1, ?_⟩
  intro hpr
  have hz := hRayShape p hpr
  rcases hz with ⟨hA0, _⟩ | ⟨hB0, _⟩
  · exact (ne_of_gt hp.1.2) hA0
  · exact (ne_of_gt hp.2) hB0

private theorem hqposEAt1461 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) b
    let C₁ : Set (Real × Real) :=
      Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let qpos : Real × Real := x + (r / 4) • (a + b)
    (qpos ∈ Metric.ball x r) → ((0 < A qpos) → ((0 < B qpos) → (
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (C₁ ⊆ Metric.ball x r \ Rays) → (qpos ∈ E.left ∪ E.right)))) := by
  classical
  intro x r u v E det d a b A B C₁ qpos hqposball hqposA hqposB Rays hC₁off
  rw [E.cover]
  exact hC₁off ⟨⟨hqposball, hqposA⟩, hqposB⟩

private theorem hqnegEAt1464 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    let A : (Real × Real) → Real := fun p => det a (p - x)
    let qneg : Real × Real := x - (r / 4) • (a + b)
    (qneg ∈ Metric.ball x r) → ((A qneg < 0) → ((Metric.ball x r ∩ {p : ℝ × ℝ | (fun (p : ℝ × ℝ)
        => (fun (a b : ℝ × ℝ) => a.1 * b.2 - a.2 * b.1) (if (0 : ℝ) < (fun (a b : ℝ × ℝ) => a.1 *
        b.2 - a.2 * b.1) u v then u else v) (p - x)) p < (0 : ℝ)} ∪ Metric.ball x r ∩ {p : ℝ × ℝ
        | (fun (p : ℝ × ℝ) => (fun (a b : ℝ × ℝ) => a.1 * b.2 - a.2 * b.1) (p - x) (if (0 : ℝ) <
        (fun (a b : ℝ × ℝ) => a.1 * b.2 - a.2 * b.1) u v then v else u)) p < (0 : ℝ)} ⊆
        Metric.ball x r \ ({p : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p = x + t • u} ∪ {p : ℝ × ℝ | ∃
        (t : ℝ), (0 : ℝ) ≤ t ∧ p = x + t • v})) → (qneg ∈ E.left ∪ E.right))) := by
  classical
  intro x r u v E det d a b A qneg hqnegb hqnegA hC₂off
  rw [E.cover]
  exact hC₂off (Or.inl ⟨hqnegb, hqnegA⟩)

private theorem haRayEq :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) → (a = u ∨ a = v) := by
  classical
  intro u v det d a b horder
  rcases horder with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
  · exact Or.inl haEq
  · exact Or.inr haEq

private theorem hbRayEq :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let d := det u v
    let a : Real × Real := if 0 < d then u else v
    let b : Real × Real := if 0 < d then v else u
    ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) → (b = u ∨ b = v) := by
  classical
  intro u v det d a b horder
  rcases horder with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
  · exact Or.inr hbEq
  · exact Or.inl hbEq

private theorem hdist :
    ∀ (x : Real × Real), ∀ (w : Real × Real), (‖w‖ = 1) → (∀ (t : Real), (0 < t) → (dist (x + t •
        w) x = t)) := by
  classical
  intro x w hw t ht
  rw [dist_eq_norm]
  have hsub : x + t • w - x = t • w := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hw]
  ring

private theorem hball :
    ∀ (x : Real × Real),
      ∀ (r : Real),
        (∀ (w : Real × Real), ‖w‖ = 1 → ∀ (t : Real), 0 < t → dist (x + t • w) x = t) →
          ∀ (w : Real × Real),
            ‖w‖ = 1 →
              ∀ (t : Real), 0 < t → Metric.ball (x + t • w) (r - t) ⊆ Metric.ball x r := by
  classical
  intro x r hdist w hw t ht
  apply Metric.ball_subset_ball'
  rw [hdist w hw t ht]
  exact le_of_eq (sub_add_cancel r t)

private theorem hAcontAt1604 :
    ∀ (x : Real × Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    Continuous A := by
  classical
  intro x u det A
  dsimp [A, det]
  fun_prop

private theorem hPopen :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    (Continuous A) → (IsOpen P) := by
  classical
  intro x r u det A P hAcont
  dsimp [P]
  exact Metric.isOpen_ball.inter (isOpen_Ioi.preimage hAcont)

private theorem hNopen :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (Continuous A) → (IsOpen N) := by
  classical
  intro x r u det A N hAcont
  dsimp [N]
  exact Metric.isOpen_ball.inter (isOpen_Iio.preimage hAcont)

private theorem hsqpos :
    ∀ (u : Real × Real), (u ≠ (0, 0)) → (0 < u.1 ^ 2 + u.2 ^ 2) := by
  classical
  intro u hu0
  by_contra h
  have hle : u.1 ^ 2 + u.2 ^ 2 ≤ 0 := le_of_not_gt h
  have h1sq : u.1 ^ 2 = 0 := by nlinarith only [hle, sq_nonneg u.2]
  have h2sq : u.2 ^ 2 = 0 := by nlinarith only [hle, sq_nonneg u.1]
  have h1 : u.1 = 0 := by nlinarith only [h1sq]
  have h2 : u.2 = 0 := by nlinarith only [h2sq]
  exact hu0 (Prod.ext h1 h2)

private theorem hjnorm :
    ∀ (u : Real × Real), (‖u‖ = 1) → (
    let j : Real × Real := (-u.2, u.1)
    ‖j‖ = 1) := by
  classical
  intro u hu j
  dsimp [j]
  simpa [Prod.norm_def, Real.norm_eq_abs, max_comm] using hu

private theorem hqposballAt1653 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), (0 < r) → (
    let j : Real × Real := (-u.2, u.1)
    (‖j‖ = 1) → ((0 < r / 4) → (
    let qpos : Real × Real := x + (r / 4) • j
    qpos ∈ Metric.ball x r))) := by
  classical
  intro x r u hr j hjnorm hr4 qpos
  change dist qpos x < r
  rw [dist_eq_norm]
  have heq : qpos - x = (r / 4) • j := by simp [qpos]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr4, hjnorm]
  nlinarith only [hr]

private theorem hqnegbAt1659 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), (0 < r) → (
    let j : Real × Real := (-u.2, u.1)
    (‖j‖ = 1) → ((0 < r / 4) → (
    let qneg : Real × Real := x - (r / 4) • j
    qneg ∈ Metric.ball x r))) := by
  classical
  intro x r u hr j hjnorm hr4 qneg
  change dist qneg x < r
  rw [dist_eq_norm]
  have heq : qneg - x = -((r / 4) • j) := by simp [qneg, sub_eq_add_neg]
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hr4, hjnorm]
  nlinarith only [hr]

private theorem hAqposAt1665 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let j : Real × Real := (-u.2, u.1)
    let qpos : Real × Real := x + (r / 4) • j
    A qpos = (r / 4) * (u.1 ^ 2 + u.2 ^ 2) := by
  classical
  intro x r u det A j qpos
  dsimp [A, qpos, j, det]
  ring

private theorem hAqnegAt1668 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let j : Real × Real := (-u.2, u.1)
    let qneg : Real × Real := x - (r / 4) • j
    A qneg = -(r / 4) * (u.1 ^ 2 + u.2 ^ 2) := by
  classical
  intro x r u det A j qneg
  dsimp [A, qneg, j, det]
  ring

private theorem hqnegAAt1672 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    (0 < u.1 ^ 2 + u.2 ^ 2) → (
    let j : Real × Real := (-u.2, u.1)
    (0 < r / 4) → (
    let qneg : Real × Real := x - (r / 4) • j
    (A qneg = -(r / 4) * (u.1 ^ 2 + u.2 ^ 2)) → (A qneg < 0))) := by
  classical
  intro x r u det A hsqpos j hr4 qneg hAqneg
  rw [hAqneg]
  nlinarith only [mul_pos hr4 hsqpos]

private theorem hdisAt1679 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    Disjoint P N := by
  classical
  intro x r u det A P N
  apply Set.disjoint_left.mpr
  intro p hp hn
  have hpA : 0 < A p := hp.2
  have hnA : A p < 0 := hn.2
  exact (not_lt_of_ge (le_of_lt hpA)) hnA

private theorem hAonU :
    ∀ (x : Real × Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    ∀ (t : Real), A (x + t • u) = 0 := by
  classical
  intro x u det A t
  dsimp [A, det]
  simp
  ring

private theorem hAonV :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    (v = -u) → (
    let A : (Real × Real) → Real := fun p => det u (p - x)
    ∀ (t : Real), A (x + t • v) = 0) := by
  classical
  intro x u v det hvneg A t
  rw [hvneg]
  dsimp [A, det]
  simp
  ring

private theorem hRayAzero :
    ∀ (x : Real × Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let Rays : Set (Real × Real) :=
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
    (∀ (t : Real), A (x + t • u) = 0) → ((∀ (t : Real), A (x + t • v) = 0) → (∀ (p : Real ×
        Real), (p ∈ Rays) → (A p = 0))) := by
  classical
  intro x u v det A Rays hAonU hAonV p hp
  change (∃ t : Real, 0 ≤ t ∧ p = x + t • u) ∨
    (∃ t : Real, 0 ≤ t ∧ p = x + t • v) at hp
  rcases hp with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · exact hAonU t
  · exact hAonV t

private theorem hPtoE :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    (Metric.ball x r ∩ {p : ℝ × ℝ | (0 : ℝ) < (fun (p : ℝ × ℝ) => (fun (a b : ℝ × ℝ) => a.1 * b.2
        - a.2 * b.1) u (p - x)) p} ⊆ Metric.ball x r \ ({p : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p =
        x + t • u} ∪ {p : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p = x + t • v})) → (P ⊆ E.left ∪
        E.right) := by
  classical
  intro x r u v E det A P hPoff p hp
  exact E.cover.symm ▸ hPoff hp

private theorem hNtoE :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (Metric.ball x r ∩ {p : ℝ × ℝ | (fun (p : ℝ × ℝ) => (fun (a b : ℝ × ℝ) => a.1 * b.2 - a.2 *
        b.1) u (p - x)) p < (0 : ℝ)} ⊆ Metric.ball x r \ ({p : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p
        = x + t • u} ∪ {p : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p = x + t • v})) → (N ⊆ E.left ∪
        E.right) := by
  classical
  intro x r u v E det A N hNoff p hp
  exact E.cover.symm ▸ hNoff hp

private theorem hcomponentEq :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), ∀ (E :
        P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (E.left ⊆ P ∧ E.right ⊆ N ∨ E.left ⊆ N ∧ E.right ⊆ P) → ((E.left ⊆ P → E.right ⊆ N → E.left =
        P ∧ E.right = N) → ((E.left ⊆ N → E.right ⊆ P → E.left = N ∧ E.right = P) → ((E.left = P
        ∧ E.right = N) ∨ (E.left = N ∧ E.right = P)))) := by
  classical
  intro x r u v E det A P N horderComponents hEqPN hEqNP
  apply Or.elim horderComponents
  · rintro ⟨hL, hR⟩
    exact Or.inl (hEqPN hL hR)
  · rintro ⟨hL, hR⟩
    exact Or.inr (hEqNP hL hR)

end SectorContinuationFacts

namespace SectorContinuationCases

private theorem nondegenerateContinuation :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), (0 < r) → ((‖u‖
        = 1) → ((‖v‖ = 1) → (∀ (E : P3889T1TwoRaySectorDecomposition x r u v),
    let det : (Real × Real) → (Real × Real) → Real :=
      fun a b => a.1 * b.2 - a.2 * b.1
    (det u v ≠ 0) → (∃ e : Bool, ∀ t : Real, 0 < t → t < r →
      P3934T1LocalSide E.left (x + t • u) (-u) e ∧
      P3934T1LocalSide E.left (x + t • v) v e ∧
      P3934T1LocalSide E.right (x + t • u) (-u) (!e) ∧
      P3934T1LocalSide E.right (x + t • v) v (!e))))) := by
  classical
  intro x r u v hr hu hv E det hnonzero
  let d := det u v
  have hd : d ≠ 0 := hnonzero
  let a : Real × Real := if 0 < d then u else v
  let b : Real × Real := if 0 < d then v else u
  let d' := det a b
  have hdpos := SectorContinuationFacts.hdpos u v hd
  have ha : ‖a‖ = 1 := by dsimp [a]; split_ifs <;> assumption
  have hb : ‖b‖ = 1 := by dsimp [b]; split_ifs <;> assumption
  let A : (Real × Real) → Real := fun p => det a (p - x)
  let B : (Real × Real) → Real := fun p => det (p - x) b
  have hdetid (y : Real × Real) := SectorContinuationFacts.hdetid x u v y
  have hrep (p : Real × Real) :
  p - x = (B p / d') • a + (A p / d') • b := SectorContinuationGeometry.hrep x u v hdpos
      hdetid p
  let C₁ : Set (Real × Real) :=
    Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
  let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
  let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
  let C₂ : Set (Real × Real) := C ∪ D
  have hAcont := SectorContinuationFacts.hAcontAt1316 x u v
  have hBcont := SectorContinuationFacts.hBcont x u v
  have hC₁open := SectorContinuationFacts.hC₁open x r u v hAcont hBcont
  have hCopen := SectorContinuationFacts.hCopen x r u v hAcont
  have hDopen := SectorContinuationFacts.hDopen x r u v hBcont
  have hC₂open := SectorContinuationFacts.hC₂open x r u v hCopen hDopen
  have hsumNorm := SectorContinuationFacts.hsumNorm u v ha hb
  have hr4 : 0 < r / 4 := by positivity
  let qpos : Real × Real := x + (r / 4) • (a + b)
  have hqposball := SectorContinuationFacts.hqposballAt1344 x r u v hr
      hsumNorm hr4
  have hAqpos : A qpos = (r / 4) * d' := SectorContinuationFacts.hAqposAt1353 x r u v
  have hBqpos : B qpos = (r / 4) * d' := SectorContinuationFacts.hBqpos x r u v
  have hqposA : 0 < A qpos := by rw [hAqpos]; positivity
  have hqposB : 0 < B qpos := by rw [hBqpos]; positivity
  let qneg : Real × Real := x - (r / 4) • (a + b)
  have hqnegb := SectorContinuationFacts.hqnegbAt1364 x r u v hr
      hsumNorm hr4
  have hAqneg := SectorContinuationFacts.hAqnegAt1373 x r u v
  have hqnegA := SectorContinuationFacts.hqnegAAt1379 x r u v hAqpos hqposA hAqneg
  have horder := SectorContinuationFacts.horder u v
  have haRay (k : Real) (hk : 0 ≤ k) := SectorContinuationFacts.haRay x u v horder k hk
  have hbRay (k : Real) (hk : 0 ≤ k) := SectorContinuationFacts.hbRay x u v horder k hk
  have hAa (t : Real) := SectorContinuationFacts.hAa x u v t
  have hBa (t : Real) := SectorContinuationFacts.hBa x u v t
  have hAb (t : Real) := SectorContinuationFacts.hAb x u v t
  have hBb (t : Real) := SectorContinuationFacts.hBb x u v t
  have hAzero (p : Real × Real) (hAp : A p = 0) := SectorContinuationFacts.hAzero x u v hrep p hAp
  have hBzero (p : Real × Real) (hBp : B p = 0) := SectorContinuationFacts.hBzero x u v hrep p hBp
  let Rays : Set (Real × Real) :=
    {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
  have hRayShape (p : Real × Real) (hp : p ∈ Rays) :
  (A p = 0 ∧ 0 ≤ B p) ∨ (B p = 0 ∧ 0 ≤ A p) := SectorContinuationGeometry.hRayShape x u v
      hdpos horder hAa hBa hAb hBb p hp
  have hEsubset := SectorContinuationGeometry.hEsubsetAt411 x r
      u v E hdpos haRay hbRay hAzero hBzero
  have hdis := SectorContinuationGeometry.hdisAt436 x r u v
  have classify (S : Set (Real × Real)) (hS : IsConnected S)
  (hsub : S ⊆ C₁ ∪ C₂) : S ⊆ C₁ ∨ S ⊆ C₂ := SectorContinuationGeometry.classify x r u v
      hC₁open hC₂open hdis S hS hsub
  have hC₁off := SectorContinuationFacts.hC₁off x r u v hRayShape
  have hC₂off := SectorContinuationGeometry.hC₂off x r u v
      hRayShape
  have hqposE := SectorContinuationFacts.hqposEAt1461 x r u v E
      hqposball hqposA hqposB hC₁off
  have hqnegE := SectorContinuationFacts.hqnegEAt1464 x r u v E
      hqnegb hqnegA hC₂off
  have hqposC₁ : qpos ∈ C₁ := ⟨⟨hqposball, hqposA⟩, hqposB⟩
  have hqnegC₂ : qneg ∈ C₂ := Or.inl ⟨hqnegb, hqnegA⟩
  have hleftCases := classify E.left E.left_connected
    (fun p hp => hEsubset (Or.inl hp))
  have hrightCases := classify E.right E.right_connected
    (fun p hp => hEsubset (Or.inr hp))
  have horderComponents :
  (E.left ⊆ C₁ ∧ E.right ⊆ C₂) ∨ (E.left ⊆ C₂ ∧ E.right ⊆ C₁) :=
      SectorContinuationGeometry.horderComponentsAt496 x r u v E hdis hqposE hqnegE hqposC₁
      hqnegC₂ hleftCases hrightCases
  have hcomponentEq :
  (E.left = C₁ ∧ E.right = C₂) ∨ (E.left = C₂ ∧ E.right = C₁) :=
      SectorContinuationGeometry.hcomponentEqAt509 x r u v E hdis hC₁off hC₂off horderComponents
  have sampleA (t δ : Real) (ht : 0 < t) (hδ : 0 < δ)
  (hball : Metric.ball (x + t • a) δ ⊆ Metric.ball x r) :
  ∃ qpos' qneg', qpos' ∈ Metric.ball (x + t • a) δ ∧
    qneg' ∈ Metric.ball (x + t • a) δ ∧ qpos' ∈ C₁ ∧ qneg' ∈ C₂ ∧
    0 < det a (qpos' - (x + t • a)) ∧
    det a (qneg' - (x + t • a)) < 0 := SectorContinuationGeometry.sampleA x r u v hdpos ha
        hBcont hBa t δ ht hδ hball
  have sampleB (t δ : Real) (ht : 0 < t) (hδ : 0 < δ)
  (hball : Metric.ball (x + t • b) δ ⊆ Metric.ball x r) :
  ∃ qpos' qneg', qpos' ∈ Metric.ball (x + t • b) δ ∧
    qneg' ∈ Metric.ball (x + t • b) δ ∧ qpos' ∈ C₂ ∧ qneg' ∈ C₁ ∧
    0 < det b (qpos' - (x + t • b)) ∧
    det b (qneg' - (x + t • b)) < 0 := SectorContinuationGeometry.sampleB x r u v hdpos hb
        hAcont hAb t δ ht hδ hball
  have haRayEq := SectorContinuationFacts.haRayEq u v horder
  have hbRayEq := SectorContinuationFacts.hbRayEq u v horder
  have aLocalC₁ (t : Real) (ht : 0 < t) (htr : t < r)
  (hL : E.left = C₁) :
  P3934T1LocalSide E.left (x + t • a) a true ∧
    P3934T1LocalSide E.right (x + t • a) a false := SectorContinuationGeometry.aLocalC₁ x r
        u v E sampleA haRayEq t ht htr hL
  have aLocalC₂ (t : Real) (ht : 0 < t) (htr : t < r)
  (hL : E.left = C₂) :
  P3934T1LocalSide E.left (x + t • a) a false ∧
    P3934T1LocalSide E.right (x + t • a) a true := SectorContinuationGeometry.aLocalC₂ x r
        u v E sampleA haRayEq t ht htr hL
  have bLocalC₁ (t : Real) (ht : 0 < t) (htr : t < r)
  (hL : E.left = C₁) :
  P3934T1LocalSide E.left (x + t • b) b false ∧
    P3934T1LocalSide E.right (x + t • b) b true := SectorContinuationGeometry.bLocalC₁ x r
        u v E sampleB hbRayEq t ht htr hL
  have bLocalC₂ (t : Real) (ht : 0 < t) (htr : t < r)
  (hL : E.left = C₂) :
  P3934T1LocalSide E.left (x + t • b) b true ∧
    P3934T1LocalSide E.right (x + t • b) b false := SectorContinuationGeometry.bLocalC₂ x r
        u v E sampleB hbRayEq t ht htr hL
  have flipSide (U : Set (Real × Real)) (z w : Real × Real) (e : Bool)
  (h : P3934T1LocalSide U z w e) :
  P3934T1LocalSide U z (-w) (!e) := SectorContinuationGeometry.flipSide U z w e h
  rcases hcomponentEq with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · by_cases hpos : 0 < d
    · have haEq : a = u := by simp [a, hpos]
      have hbEq : b = v := by simp [b, hpos]
      refine ⟨false, ?_⟩
      intro t ht htr
      have ⟨hLa, hRa⟩ := aLocalC₁ t ht htr hL
      have ⟨hLb, hRb⟩ := bLocalC₁ t ht htr hL
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [haEq] using flipSide E.left (x + t • a) a true hLa
      · simpa [hbEq] using hLb
      · simpa [haEq] using flipSide E.right (x + t • a) a false hRa
      · simpa [hbEq] using hRb
    · have hneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
      have haEq : a = v := by simp [a, hpos]
      have hbEq : b = u := by simp [b, hpos]
      refine ⟨true, ?_⟩
      intro t ht htr
      have ⟨hLa, hRa⟩ := aLocalC₁ t ht htr hL
      have ⟨hLb, hRb⟩ := bLocalC₁ t ht htr hL
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hbEq] using flipSide E.left (x + t • b) b false hLb
      · simpa [haEq] using hLa
      · simpa [hbEq] using flipSide E.right (x + t • b) b true hRb
      · simpa [haEq] using hRa
  · by_cases hpos : 0 < d
    · have haEq : a = u := by simp [a, hpos]
      have hbEq : b = v := by simp [b, hpos]
      refine ⟨true, ?_⟩
      intro t ht htr
      have ⟨hLa, hRa⟩ := aLocalC₂ t ht htr hL
      have ⟨hLb, hRb⟩ := bLocalC₂ t ht htr hL
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [haEq] using flipSide E.left (x + t • a) a false hLa
      · simpa [hbEq] using hLb
      · simpa [haEq] using flipSide E.right (x + t • a) a true hRa
      · simpa [hbEq] using hRb
    · have hneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
      have haEq : a = v := by simp [a, hpos]
      have hbEq : b = u := by simp [b, hpos]
      refine ⟨false, ?_⟩
      intro t ht htr
      have ⟨hLa, hRa⟩ := aLocalC₂ t ht htr hL
      have ⟨hLb, hRb⟩ := bLocalC₂ t ht htr hL
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hbEq] using flipSide E.left (x + t • b) b true hLb
      · simpa [haEq] using hLa
      · simpa [hbEq] using flipSide E.right (x + t • b) b false hRb
      · simpa [haEq] using hRa

private theorem oppositeContinuation :
    ∀ (x : Real × Real),
      ∀ (r : Real),
        ∀ (u : Real × Real),
          ∀ (v : Real × Real),
            0 < r →
              ‖u‖ = 1 →
                ‖v‖ = 1 →
                  ∀ (E : P3889T1TwoRaySectorDecomposition x r u v),
                    u ≠ ((0 : ℝ), (0 : ℝ)) →
                      u.1 ≠ (0 : ℝ) ∨ u.2 ≠ (0 : ℝ) →
                        v = -u →
                          ∃ e : Bool,
                            ∀ t : Real,
                            0 < t →
                            t < r →
                            P3934T1LocalSide E.left (x + t • u) (-u) e ∧
                            P3934T1LocalSide E.left (x + t • v) v e ∧
                            P3934T1LocalSide E.right (x + t • u) (-u) !e ∧
                            P3934T1LocalSide E.right (x + t • v) v !e := by
  classical
  intro x r u v hr hu hv E hu_ne hcoord hvneg
  let det : (Real × Real) → (Real × Real) → Real :=
    fun a b => a.1 * b.2 - a.2 * b.1
  let A : (Real × Real) → Real := fun p => det u (p - x)
  let P : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
  let N : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
  have hform (w : Real × Real) (hw : w = u ∨ w = v)
  (t : Real) (q : Real × Real) :
  -u.1 * (q.2 - (x.2 + t * w.2)) -
    -u.2 * (q.1 - (x.1 + t * w.1)) = -A q := SectorContinuationGeometry.hform x u v hvneg w hw t q
  have hdist (w : Real × Real) (hw : ‖w‖ = 1) (t : Real)
    (ht : 0 < t) := SectorContinuationFacts.hdist x w hw t ht
  have hdelta (t : Real) (htr : t < r) : 0 < r - t := by
    exact sub_pos.mpr htr
  have hball (w : Real × Real) (hw : ‖w‖ = 1) (t : Real)
    (ht : 0 < t) (htr : t < r) := SectorContinuationFacts.hball x r
        hdist w hw t ht
  have hlocalP (w : Real × Real) (hw : w = u ∨ w = v)
  (hwNorm : ‖w‖ = 1) (t : Real) (ht : 0 < t) (htr : t < r) :
  P3934T1LocalSide P (x + t • w) (-u) false := SectorContinuationGeometry.hlocalP x r u v
      hform hdelta hball w hw hwNorm t ht htr
  have hlocalN (w : Real × Real) (hw : w = u ∨ w = v)
  (hwNorm : ‖w‖ = 1) (t : Real) (ht : 0 < t) (htr : t < r) :
  P3934T1LocalSide N (x + t • w) (-u) true := SectorContinuationGeometry.hlocalN x r u v
      hform hdelta hball w hw hwNorm t ht htr
  have hAcont := SectorContinuationFacts.hAcontAt1604 x u
  have hPopen := SectorContinuationFacts.hPopen x r u hAcont
  have hNopen := SectorContinuationFacts.hNopen x r u hAcont
  have hu0 : u ≠ (0, 0) := hu_ne
  have hsqpos := SectorContinuationFacts.hsqpos u hu0
  let j : Real × Real := (-u.2, u.1)
  have hjnorm := SectorContinuationFacts.hjnorm u hu
  have hr4 : 0 < r / 4 := by positivity
  let qpos : Real × Real := x + (r / 4) • j
  let qneg : Real × Real := x - (r / 4) • j
  have hqposball := SectorContinuationFacts.hqposballAt1653 x r u hr
      hjnorm hr4
  have hqnegb := SectorContinuationFacts.hqnegbAt1659 x r u hr hjnorm hr4
  have hAqpos : A qpos = (r / 4) * (u.1 ^ 2 + u.2 ^ 2) := SectorContinuationFacts.hAqposAt1665
      x r u
  have hAqneg := SectorContinuationFacts.hAqnegAt1668
      x r u
  have hqposA : 0 < A qpos := by rw [hAqpos]; exact mul_pos hr4 hsqpos
  have hqnegA := SectorContinuationFacts.hqnegAAt1672 x r u hsqpos hr4 hAqneg
  have hdis := SectorContinuationFacts.hdisAt1679 x r u
  let Rays : Set (Real × Real) :=
    {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}
  have hcol (y : Real × Real) (hy : det u y = 0) :
  ∃ k : Real, y = k • u := SectorContinuationGeometry.hcol u hcoord y hy
  have hzeroRay (p : Real × Real) (hp : A p = 0) := SectorContinuationGeometry.hzeroRay x u v
      hvneg hcol p hp
  have hAonU (t : Real) := SectorContinuationFacts.hAonU x u t
  have hAonV (t : Real) := SectorContinuationFacts.hAonV x u v hvneg t
  have hRayAzero (p : Real × Real) (hp : p ∈ Rays) := SectorContinuationFacts.hRayAzero x u v
      hAonU hAonV p hp
  have hPoff := SectorContinuationGeometry.hPoff x r u v hRayAzero
  have hNoff := SectorContinuationGeometry.hNoff x r u v hRayAzero
  have hEsubset := SectorContinuationGeometry.hEsubsetAt1063 x r u
      v E hzeroRay
  have hPtoE := SectorContinuationFacts.hPtoE x r u v E hPoff
  have hNtoE := SectorContinuationFacts.hNtoE x r u v E hNoff
  have hqposE : qpos ∈ E.left ∪ E.right := by
    exact hPtoE ⟨hqposball, hqposA⟩
  have hqnegE : qneg ∈ E.left ∪ E.right := by
    exact hNtoE ⟨hqnegb, hqnegA⟩
  have hqposP : qpos ∈ P := ⟨hqposball, hqposA⟩
  have hqnegN : qneg ∈ N := ⟨hqnegb, hqnegA⟩
  have horderComponents :
  (E.left ⊆ P ∧ E.right ⊆ N) ∨ (E.left ⊆ N ∧ E.right ⊆ P) :=
      SectorContinuationGeometry.horderComponentsAt1092 x r u v E hPopen hNopen hdis hEsubset
      hqposE hqnegE hqposP hqnegN
  have hEqPN (hL : E.left ⊆ P) (hR : E.right ⊆ N) :
  E.left = P ∧ E.right = N := SectorContinuationGeometry.hEqPN x r u v E hdis hPoff hNoff hL hR
  have hEqNP (hL : E.left ⊆ N) (hR : E.right ⊆ P) :
  E.left = N ∧ E.right = P := SectorContinuationGeometry.hEqNP x r u v E hdis hPoff hNoff hL hR
  have hcomponentEq := SectorContinuationFacts.hcomponentEq x r u v E horderComponents hEqPN hEqNP
  rcases hcomponentEq with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · refine ⟨false, ?_⟩
    intro t ht htr
    have huSide := hlocalP u (Or.inl rfl) hu t ht htr
    have hvSide := hlocalP v (Or.inr rfl) hv t ht htr
    have huSideN := hlocalN u (Or.inl rfl) hu t ht htr
    have hvSideN := hlocalN v (Or.inr rfl) hv t ht htr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hL]
      exact huSide
    · rw [hL]
      rw [← hvneg] at hvSide
      exact hvSide
    · rw [hR]
      exact huSideN
    · rw [hR]
      rw [← hvneg] at hvSideN
      exact hvSideN
  · refine ⟨true, ?_⟩
    intro t ht htr
    have huSide := hlocalN u (Or.inl rfl) hu t ht htr
    have hvSide := hlocalN v (Or.inr rfl) hv t ht htr
    have huSideP := hlocalP u (Or.inl rfl) hu t ht htr
    have hvSideP := hlocalP v (Or.inr rfl) hv t ht htr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hL]
      exact huSide
    · rw [hL]
      rw [← hvneg] at hvSide
      exact hvSide
    · rw [hR]
      exact huSideP
    · rw [hR]
      rw [← hvneg] at hvSideP
      exact hvSideP

end SectorContinuationCases

theorem P3934T1SectorContinuation (x : Real × Real) (r : Real)
    (u v : Real × Real) (hr : 0 < r) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : u ≠ v) (E : P3889T1TwoRaySectorDecomposition x r u v) :
    ∃ e : Bool, ∀ t : Real, 0 < t → t < r →
      P3934T1LocalSide E.left (x + t • u) (-u) e ∧
      P3934T1LocalSide E.left (x + t • v) v e ∧
      P3934T1LocalSide E.right (x + t • u) (-u) (!e) ∧
      P3934T1LocalSide E.right (x + t • v) v (!e) := by
-- BODY
  let det : (Real × Real) → (Real × Real) → Real :=
    fun a b => a.1 * b.2 - a.2 * b.1
  have hu_ne := SectorContinuationFacts.hu_ne u hu
  have hcoord := SectorContinuationFacts.hcoord u hu_ne
  have hdet_cases := SectorContinuationGeometry.hdet_cases u v hu hv huv
      hcoord
  have nondegenerateContinuation (hnonzero : det u v ≠ 0) :
      ∃ e : Bool, ∀ t : Real, 0 < t → t < r →
      P3934T1LocalSide E.left (x + t • u) (-u) e ∧
      P3934T1LocalSide E.left (x + t • v) v e ∧
      P3934T1LocalSide E.right (x + t • u) (-u) (!e) ∧
      P3934T1LocalSide E.right (x + t • v) v (!e) :=
          SectorContinuationCases.nondegenerateContinuation x r u v hr hu hv E hnonzero
  have oppositeContinuation (hvneg : v = -u) :
      ∃ e : Bool, ∀ t : Real, 0 < t → t < r →
      P3934T1LocalSide E.left (x + t • u) (-u) e ∧
      P3934T1LocalSide E.left (x + t • v) v e ∧
      P3934T1LocalSide E.right (x + t • u) (-u) (!e) ∧
      P3934T1LocalSide E.right (x + t • v) v (!e) :=
          SectorContinuationCases.oppositeContinuation x r u v hr hu hv E hu_ne hcoord hvneg
  exact hdet_cases.elim nondegenerateContinuation oppositeContinuation

end ApollonianSuperharmonic

end
