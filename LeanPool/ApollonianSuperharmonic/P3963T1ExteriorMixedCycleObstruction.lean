/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndexAdjacentCell
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycleSubgraphDegreeTwo

-- [TABLET NODE: P3963T1ExteriorMixedCycleObstruction]

/-!
# P3963T1ExteriorMixedCycleObstruction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ExteriorMixedCycleProof

private theorem hadj :
    ∀ (p : List GaussianInt), ((4 : ℕ) ≤ p.length) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt),
        ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ →
        FourNeighborAdjacent a b) → (∀ a, ∀ b, (a, b) ∈ p.zip p.tail → FourNeighborAdjacent a b))
            := by
  classical
  intro p hlen hsteps a b hab
  rw [List.mem_iff_getElem] at hab
  rcases hab with ⟨i, hi, hab⟩
  have hi' : i < p.tail.length := by simpa [List.length_zip] using hi
  have hip : i + 1 < p.length := by
    simp only [List.length_tail] at hi'
    omega
  rw [List.getElem_zip, List.getElem_tail] at hab
  injection hab with ha hb
  have hdecomp : p = p.take i ++ p[i] :: p[i + 1] :: p.drop (i + 2) := by
    calc
      p = p.take i ++ p.drop i := (List.take_append_drop i p).symm
      _ = p.take i ++ p[i] :: p.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
      _ = p.take i ++ p[i] :: p[i + 1] :: p.drop (i + 2) := by
        rw [List.drop_eq_getElem_cons hip]
  have hs := hsteps (p[i]) (p[i + 1]) (p.take i) (p.drop (i + 2)) hdecomp
  simpa [ha, hb] using hs

private theorem incident :
    ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    ∀ (T : ProtoTile), ∀ (g : Finset GaussianInt), x ∈ g → g ∈ FootprintEdges T → ∃ q ∈ T.cells,
        q = c0 ∨ q = c1 ∨ q = c2 ∨ q = c3 := by
  classical
  intro x c0 c1 c2 c3 T g hxg hg
  simp only [FootprintEdges, Set.mem_ofPred_eq] at hg
  rcases hg with ⟨z, hz, hshape⟩
  rcases hshape with hshape | hshape | hshape | hshape
  · have hxg' : x = z ∨ x = z + 1 := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · subst z
      exact ⟨x, hz, Or.inl (by simp [c0])⟩
    · have hzEq : z = x - 1 := by
        calc
          z = (z + 1) - 1 := by ring
          _ = x - 1 := by rw [← h]
      rw [hzEq] at hz
      exact ⟨x - 1, hz, Or.inr (Or.inl (by simp [c1]))⟩
  · have hxg' : x = z ∨ x = z + ⟨0, 1⟩ := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · subst z
      exact ⟨x, hz, Or.inl (by simp [c0])⟩
    · have hzEq : z = x - ⟨0, 1⟩ := by
        calc
          z = (z + ⟨0, 1⟩) - ⟨0, 1⟩ := by ring
          _ = x - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      exact ⟨x - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr (by simp [c3])))⟩
  · have hxg' : x = z + 1 ∨ x = z + 1 + ⟨0, 1⟩ := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · have hzEq : z = x - 1 := by
        calc
          z = (z + 1) - 1 := by ring
          _ = x - 1 := by rw [← h]
      rw [hzEq] at hz
      exact ⟨x - 1, hz, Or.inr (Or.inl (by simp [c1]))⟩
    · have hzEq : z = x - 1 - ⟨0, 1⟩ := by
        calc
          z = (z + 1 + ⟨0, 1⟩) - 1 - ⟨0, 1⟩ := by ring
          _ = x - 1 - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      exact ⟨x - 1 - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inl (by simp [c2])))⟩
  · have hxg' : x = z + ⟨0, 1⟩ ∨ x = z + 1 + ⟨0, 1⟩ := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · have hzEq : z = x - ⟨0, 1⟩ := by
        calc
          z = (z + ⟨0, 1⟩) - ⟨0, 1⟩ := by ring
          _ = x - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      exact ⟨x - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr (by simp [c3])))⟩
    · have hzEq : z = x - 1 - ⟨0, 1⟩ := by
        calc
          z = (z + 1 + ⟨0, 1⟩) - 1 - ⟨0, 1⟩ := by ring
          _ = x - 1 - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      exact ⟨x - 1 - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inl (by simp [c2])))⟩

private theorem hpattern :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∃ q ∈ U.cells, q = c0 ∨ q = c1 ∨ q = c2 ∨ q = c3) → ((∃ q ∈ V.cells, q = c0 ∨ q = c1 ∨ q =
        c2 ∨ q = c3) → ((¬ (c0 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c0 ∈ V.cells)) →
        ((¬ (c1 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c2 ∈
        U.cells ∧ c3 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c0 ∈
        V.cells)) → ((¬ (c0 ∈ U.cells ∧ c3 ∈ V.cells)) → ((¬ (c0 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬
        (c1 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧
        c3 ∈ V.cells)) → ((c0 ∈ U.cells ∧ c2 ∈ V.cells) ∨ (c2 ∈ U.cells ∧ c0 ∈ V.cells) ∨ (c1 ∈
        U.cells ∧ c3 ∈ V.cells) ∨ (c3 ∈ U.cells ∧ c1 ∈ V.cells))))))))))))))) := by
  classical
  intro U V x c0 c1 c2 c3 hOccU hOccV no01 no10 no12 no21 no23 no32 no30 no03 noSame0 noSame1
      noSame2 noSame3
  obtain ⟨a, haU, haCase⟩ := hOccU
  obtain ⟨b, hbV, hbCase⟩ := hOccV
  rcases haCase with ha0 | ha1 | ha2 | ha3 <;>
    rcases hbCase with hb0 | hb1 | hb2 | hb3
  all_goals
    subst a
    subst b
    first
    | exact False.elim (noSame0 ⟨haU, hbV⟩)
    | exact False.elim (noSame1 ⟨haU, hbV⟩)
    | exact False.elim (noSame2 ⟨haU, hbV⟩)
    | exact False.elim (noSame3 ⟨haU, hbV⟩)
    | exact False.elim (no01 ⟨haU, hbV⟩)
    | exact False.elim (no10 ⟨haU, hbV⟩)
    | exact False.elim (no12 ⟨haU, hbV⟩)
    | exact False.elim (no21 ⟨haU, hbV⟩)
    | exact False.elim (no23 ⟨haU, hbV⟩)
    | exact False.elim (no32 ⟨haU, hbV⟩)
    | exact False.elim (no30 ⟨haU, hbV⟩)
    | exact False.elim (no03 ⟨haU, hbV⟩)
    | exact Or.inl ⟨haU, hbV⟩
    | exact Or.inr (Or.inl ⟨haU, hbV⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨haU, hbV⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨haU, hbV⟩))

private theorem hExteriorPair :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (¬ (c0 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧
        c2 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c3 ∈ V.cells))
        → ((¬ (c3 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c0 ∈
        U.cells ∧ c3 ∈ V.cells)) → (((c0 ∈ U.cells ∧ c2 ∈ V.cells) ∨ (c2 ∈ U.cells ∧ c0 ∈
        V.cells) ∨ (c1 ∈ U.cells ∧ c3 ∈ V.cells) ∨ (c3 ∈ U.cells ∧ c1 ∈ V.cells)) → ((∀ (q :
            GaussianInt), (q ∉ U.cells) → ((q ∉ V.cells) → (q ∈ (↑(U.cells ∪ V.cells) : Set
        GaussianInt)ᶜ))) → ((c1 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧ c3 ∈ (↑(U.cells ∪
        V.cells) : Set GaussianInt)ᶜ) ∨ (c0 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧ c2 ∈
        (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ))))))))))) := by
  classical
  intro U V x c0 c1 c2 c3 no01 no10 no12 no21 no23 no32 no30 no03 hpattern inExterior
  rcases hpattern with ⟨hu0, hv2⟩ | ⟨hu2, hv0⟩ | ⟨hu1, hv3⟩ | ⟨hu3, hv1⟩
  · left
    constructor
    · apply inExterior
      · intro h; exact no12 ⟨h, hv2⟩
      · intro h; exact no01 ⟨hu0, h⟩
    · apply inExterior
      · intro h; exact no32 ⟨h, hv2⟩
      · intro h; exact no03 ⟨hu0, h⟩
  · left
    constructor
    · apply inExterior
      · intro h; exact no10 ⟨h, hv0⟩
      · intro h; exact no21 ⟨hu2, h⟩
    · apply inExterior
      · intro h; exact no30 ⟨h, hv0⟩
      · intro h; exact no23 ⟨hu2, h⟩
  · right
    constructor
    · apply inExterior
      · intro h; exact no03 ⟨h, hv3⟩
      · intro h; exact no10 ⟨hu1, h⟩
    · apply inExterior
      · intro h; exact no23 ⟨h, hv3⟩
      · intro h; exact no12 ⟨hu1, h⟩
  · right
    constructor
    · apply inExterior
      · intro h; exact no01 ⟨h, hv1⟩
      · intro h; exact no30 ⟨hu3, h⟩
    · apply inExterior
      · intro h; exact no21 ⟨h, hv1⟩
      · intro h; exact no32 ⟨hu3, h⟩

private theorem adjNe :
    ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, FourNeighborAdjacent a b → a ≠ b := by
  classical
  intro a b hab heq
  subst b
  rcases hab with h | h | h | h
  · have hr := congrArg Zsqrtd.re h
    simp at hr
  · have hr := congrArg Zsqrtd.re h
    simp at hr
    omega
  · have hi := congrArg Zsqrtd.im h
    simp at hi
  · have hi := congrArg Zsqrtd.im h
    simp at hi
    omega

private theorem pairCases :
    ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d : GaussianInt), ({a, b} :
        Finset GaussianInt) = {c, d} → c ≠ d → a = c ∧ b = d ∨ a = d ∧ b = c := by
  classical
  intro a b c d hpair hcd
  have ha : a = c ∨ a = d := by
    have hmem : a ∈ ({c, d} : Finset GaussianInt) := by rw [← hpair]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hb : b = c ∨ b = d := by
    have hmem : b ∈ ({c, d} : Finset GaussianInt) := by rw [← hpair]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases ha with hac | had
  · subst a
    rcases hb with hbc | hbd
    · subst b
      have hmem : d ∈ ({c, d} : Finset GaussianInt) := by simp
      rw [← hpair] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact False.elim (hcd h.symm)
      · exact False.elim (hcd h.symm)
    · subst b
      exact Or.inl ⟨rfl, rfl⟩
  · subst a
    rcases hb with hbc | hbd
    · subst b
      exact Or.inr ⟨rfl, rfl⟩
    · subst b
      have hmem : c ∈ ({c, d} : Finset GaussianInt) := by simp
      rw [← hpair] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact False.elim (hcd h)
      · exact False.elim (hcd h)

private theorem adjacentMemZip :
    ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), ∀ (a : GaussianInt), ∀ (b :
        GaussianInt), (a, b) ∈ (l₁ ++ a :: b :: l₂).zip (l₁ ++ a :: b :: l₂).tail := by
  classical
  intro l₁ l₂ a b
  induction l₁ with
  | nil => simp
  | cons z l ih =>
      cases l with
      | nil => simp
      | cons z' l =>
          simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
            List.mem_cons]
          exact Or.inr ih

private theorem supportedRay :
    ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d : GaussianInt), (a = c)
        → ((b = d) → (({a, b} : Finset GaussianInt) = {c, d}))) → (∀ (T : ProtoTile), ∀ (g :
            Finset GaussianInt), x ∈ g → g ∈ FootprintEdges T → ∃ q ∈ T.cells, q = c0 ∧ (g = {x,
        x + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ g = {x, x + (1 : GaussianInt)}) ∨ q = c1 ∧ (g = {x,
        x + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ g = {x - (1 : GaussianInt), x}) ∨ q = c2 ∧ (g =
        {x - (1 : GaussianInt), x} ∨ g = {x - ⟨(0 : ℤ), (1 : ℤ)⟩, x}) ∨ q = c3 ∧ (g =
        {x - ⟨(0 : ℤ), (1 : ℤ)⟩, x} ∨ g = {x, x + (1 : GaussianInt)})) := by
  classical
  intro x c0 c1 c2 c3 pairEq T g hxg hg
  simp only [FootprintEdges, Set.mem_ofPred_eq] at hg
  rcases hg with ⟨z, hz, hshape⟩
  rcases hshape with hshape | hshape | hshape | hshape
  · have hxg' : x = z ∨ x = z + 1 := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · subst z
      refine ⟨x, hz, Or.inl ⟨by simp [c0], Or.inr ?_⟩⟩
      exact hshape
    · have hzEq : z = x - 1 := by
        calc
          z = (z + 1) - 1 := by ring
          _ = x - 1 := by rw [← h]
      rw [hzEq] at hz
      refine ⟨x - 1, hz, Or.inr (Or.inl ?_)⟩
      refine ⟨by simp [c1], Or.inr ?_⟩
      calc
        g = {z, z + 1} := hshape
        _ = {x - 1, x} := pairEq z (z + 1) (x - 1) x hzEq (by rw [hzEq]; ring)
  · have hxg' : x = z ∨ x = z + ⟨0, 1⟩ := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · subst z
      refine ⟨x, hz, Or.inl ⟨by simp [c0], Or.inl ?_⟩⟩
      exact hshape
    · have hzEq : z = x - ⟨0, 1⟩ := by
        calc
          z = (z + ⟨0, 1⟩) - ⟨0, 1⟩ := by ring
          _ = x - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      refine ⟨x - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ?_))⟩
      refine ⟨by simp [c3], Or.inl ?_⟩
      calc
        g = {z, z + ⟨0, 1⟩} := hshape
        _ = {x - ⟨0, 1⟩, x} := pairEq z (z + ⟨0, 1⟩)
          (x - ⟨0, 1⟩) x hzEq (by rw [hzEq]; ring)
  · have hxg' : x = z + 1 ∨ x = z + 1 + ⟨0, 1⟩ := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · have hzEq : z = x - 1 := by
        calc
          z = (z + 1) - 1 := by ring
          _ = x - 1 := by rw [← h]
      rw [hzEq] at hz
      refine ⟨x - 1, hz, Or.inr (Or.inl ⟨by simp [c1], Or.inl ?_⟩)⟩
      calc
        g = {z + 1, z + 1 + ⟨0, 1⟩} := hshape
        _ = {x, x + ⟨0, 1⟩} := pairEq (z + 1) (z + 1 + ⟨0, 1⟩)
          x (x + ⟨0, 1⟩) (by rw [hzEq]; ring) (by rw [hzEq]; ring)
    · have hzEq : z = x - 1 - ⟨0, 1⟩ := by
        calc
          z = (z + 1 + ⟨0, 1⟩) - 1 - ⟨0, 1⟩ := by ring
          _ = x - 1 - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      refine ⟨x - 1 - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inl ⟨by simp [c2], Or.inr ?_⟩))⟩
      calc
        g = {z + 1, z + 1 + ⟨0, 1⟩} := hshape
        _ = {x - ⟨0, 1⟩, x} := pairEq (z + 1) (z + 1 + ⟨0, 1⟩)
          (x - ⟨0, 1⟩) x (by rw [hzEq]; ring) (by rw [hzEq]; ring)
  · have hxg' : x = z + ⟨0, 1⟩ ∨ x = z + 1 + ⟨0, 1⟩ := by simpa [hshape] using hxg
    rcases hxg' with h | h
    · have hzEq : z = x - ⟨0, 1⟩ := by
        calc
          z = (z + ⟨0, 1⟩) - ⟨0, 1⟩ := by ring
          _ = x - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      refine ⟨x - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ⟨by simp [c3], Or.inr ?_⟩))⟩
      calc
        g = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} := hshape
        _ = {x, x + 1} := pairEq (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩)
          x (x + 1) (by rw [hzEq]; ring) (by rw [hzEq]; ring)
    · have hzEq : z = x - 1 - ⟨0, 1⟩ := by
        calc
          z = (z + 1 + ⟨0, 1⟩) - 1 - ⟨0, 1⟩ := by ring
          _ = x - 1 - ⟨0, 1⟩ := by rw [← h]
      rw [hzEq] at hz
      refine ⟨x - 1 - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inl ⟨by simp [c2], Or.inl ?_⟩))⟩
      calc
        g = {z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} := hshape
        _ = {x - 1, x} := pairEq (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩)
          (x - 1) x (by rw [hzEq]; ring) (by rw [hzEq]; ring)

private theorem cyclicPair :
    ∀ (F : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), (p.head? = some u) → ((p.getLast? = some v) → ((FourNeighborAdjacent v u) →
        ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
        GaussianInt), p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) → ((∀ (e : Finset
        GaussianInt), e ∈ F ↔ e = {v, u} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((
    let cyclicEdges := p.zip p.tail ++ [(v, u)];
    ∀ (q : LatticeCell), ((q + (1 : LatticeCell), q
        + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉ cyclicEdges ∧ (q + (1 : LatticeCell) + ⟨(0 :
        ℤ), (1 : ℤ)⟩, q + (1 : LatticeCell)) ∉ cyclicEdges → GridRayCrossingIndex (q + (1 :
        LatticeCell)) p = GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell), q + (1 :
        LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈ cyclicEdges ∨ (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1
        : ℤ)⟩, q + (1 : LatticeCell)) ∈ cyclicEdges → (GridRayCrossingIndex (q + (1 :
        LatticeCell)) p - GridRayCrossingIndex q p).natAbs = (1 : ℕ)) ∧ ((q + (1 : LatticeCell) +
        ⟨(0 : ℤ), (1 : ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉ cyclicEdges ∧ (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q +
        (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉ cyclicEdges → GridRayCrossingIndex (q + ⟨(0 :
        ℤ), (1 : ℤ)⟩) p = GridRayCrossingIndex q p) ∧ ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 :
        ℤ)⟩, q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈ cyclicEdges ∨ (q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 :
        LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈ cyclicEdges → (GridRayCrossingIndex (q + ⟨(0 : ℤ),
        (1 : ℤ)⟩) p - GridRayCrossingIndex q p).natAbs = (1 : ℕ))) → ((∀ (g : Finset
        GaussianInt), (g ∈ F) → (g = {v, u} ∨ ∃ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ g = {a, b}))
        → ((∀ {a : GaussianInt}, ∀ {b : GaussianInt}, (FourNeighborAdjacent a b) → (a ≠ b)) → ((∀
            (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d : GaussianInt), (({a,
        b} : Finset GaussianInt) = {c, d}) → ((c ≠ d) → ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))) →
        ((∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (a, b) ∈ (l₁ ++ a :: b :: l₂).zip (l₁ ++ a :: b :: l₂).tail) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), {a, b} ∈ F → (a, b) ∈ p.zip p.tail ++ [(v, u)] ∨ (b,
        a) ∈ p.zip p.tail ++ [(v, u)])))))))))) := by
  classical
  intro F p u v hhead hlast hclose hsteps hedges hcross hcycleEdge adjNe pairCases adjacentMemZip
      a b hab
  rcases hcycleEdge {a, b} hab with hclosing | ⟨c, d, l₁, l₂, hdecomp, hpair⟩
  · have hmatch := pairCases a b v u hclosing (adjNe hclose)
    rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      simp
    · right
      simp
  · have hstep := hsteps c d l₁ l₂ hdecomp
    have hmatch := pairCases a b c d hpair (adjNe hstep)
    have hmem : (c, d) ∈ p.zip p.tail := by
      rw [hdecomp]
      exact adjacentMemZip l₁ l₂ c d
    rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (List.mem_append.mpr (Or.inl hmem))
    · exact Or.inr (List.mem_append.mpr (Or.inl hmem))

private theorem edgeEndpointInW :
    ∀ (W : Set GaussianInt), ∀ (F : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), ∀ (u :
        GaussianInt), ∀ (v : GaussianInt), (∀ (g : Finset GaussianInt), (g ∈ F) → (g = {v, u} ∨ ∃
        a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ g = {a, b})) → ((u ∈ p) → ((v ∈ p) → ((∀ (z :
            GaussianInt), (z ∈ p) → (z ∈ W)) → (∀ g ∈ F, ∀ z ∈ g, z ∈ W)))) := by
  classical
  intro W F p u v hcycleEdge huMem hvMem vertexInW g hg z hz
  rcases hcycleEdge g hg with hclosing | ⟨a, b, l₁, l₂, hdecomp, hpair⟩
  · have hz' : z ∈ ({v, u} : Finset GaussianInt) := by rw [← hclosing]; exact hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with hzv | hzu
    · subst z; exact vertexInW v hvMem
    · subst z; exact vertexInW u huMem
  · have hz' : z ∈ ({a, b} : Finset GaussianInt) := by rw [← hpair]; exact hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with hza | hzb
    · apply vertexInW
      subst z
      rw [hdecomp]
      simp
    · apply vertexInW
      subst z
      rw [hdecomp]
      simp

private theorem noThreeNeighbors :
    ∀ (W : Set GaussianInt), ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (p : List
        GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt), (p.Nodup) → (((4 : ℕ) ≤ p.length)
        → ((p.head? = some u) → ((p.getLast? = some v) → ((W = (↑p.toFinset : Set GaussianInt)) →
        ((FourNeighborAdjacent v u) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List
        GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a
        b) → ((∀ (e : Finset GaussianInt), e ∈ F ↔ e = {v, u} ∨ ∃ (a : GaussianInt) (b :
        GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e
        = {a, b}) → ((∀ (g : Finset GaussianInt), (g ∈ F) → (∀ (z : GaussianInt), (z ∈ g) → (z ∈
        W))) → ((W.Finite) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), {x,
        a} ∈ F → {x, b} ∈ F → {x, c} ∈ F → x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
        False)))))))))) := by
  classical
  intro W F x p u v hnodup hlen hhead hlast hvertices hclose hsteps hedges edgeEndpointInW
      hWfinite a b c hab hbc hcc hxa hxb hxc hab' hac' hbc'
  let E : Set (Finset GaussianInt) := F
  let X : Set GaussianInt :=
    {z | ∃ edge ∈ E, z ∈ edge}
  have hXsubset : X ⊆ W := by
    intro z hz
    rcases hz with ⟨edge, hedge, hze⟩
    exact edgeEndpointInW edge hedge z hze
  let : Finite (Subtype X) := (hWfinite.subset hXsubset).to_subtype
  have hEsub : E ⊆ F := by intro edge hedge; exact hedge
  have hcycle' : SimpleGridCycle W F := by
    exact ⟨p, u, v, hnodup, hlen, hhead, hlast, hvertices,
      hclose, hsteps, hedges⟩
  have hdegree := SimpleGridCycleSubgraphDegreeTwo X W E F hcycle'
    hXsubset hEsub
  let G : SimpleGraph X := SimpleGraph.fromRel fun s t =>
    ({s.1, t.1} : Finset GaussianInt) ∈ E
  have hxX : x ∈ X := ⟨{x, a}, hab, by simp⟩
  let xX : X := ⟨x, hxX⟩
  have haX : a ∈ X := ⟨{x, a}, hab, by simp⟩
  have hbX : b ∈ X := ⟨{x, b}, hbc, by simp⟩
  have hcX : c ∈ X := ⟨{x, c}, hcc, by simp⟩
  let aX : X := ⟨a, haX⟩
  let bX : X := ⟨b, hbX⟩
  let cX : X := ⟨c, hcX⟩
  have hdegreeX : Set.ncard (G.neighborSet xX) ≤ 2 := by
    exact hdegree xX
  have hmemA : aX ∈ G.neighborSet xX := by
    rw [SimpleGraph.mem_neighborSet]
    apply (SimpleGraph.fromRel_adj _ _ _).mpr
    refine ⟨?_, Or.inl ?_⟩
    · intro h
      exact hxa (congrArg Subtype.val h)
    · change ({x, a} : Finset GaussianInt) ∈ E
      exact hab
  have hmemB : bX ∈ G.neighborSet xX := by
    rw [SimpleGraph.mem_neighborSet]
    apply (SimpleGraph.fromRel_adj _ _ _).mpr
    refine ⟨?_, Or.inl ?_⟩
    · intro h
      exact hxb (congrArg Subtype.val h)
    · change ({x, b} : Finset GaussianInt) ∈ E
      exact hbc
  have hmemC : cX ∈ G.neighborSet xX := by
    rw [SimpleGraph.mem_neighborSet]
    apply (SimpleGraph.fromRel_adj _ _ _).mpr
    refine ⟨?_, Or.inl ?_⟩
    · intro h
      exact hxc (congrArg Subtype.val h)
    · change ({x, c} : Finset GaussianInt) ∈ E
      exact hcc
  have habX : aX ≠ bX := by
    intro h
    exact hab' (congrArg Subtype.val h)
  have hacX : aX ≠ cX := by
    intro h
    exact hac' (congrArg Subtype.val h)
  have hbcX : bX ≠ cX := by
    intro h
    exact hbc' (congrArg Subtype.val h)
  let S : Finset X := {aX, bX, cX}
  have hSsubset : (S : Set X) ⊆ G.neighborSet xX := by
    intro z hz
    have hz' : z = aX ∨ z = bX ∨ z = cX := by
      simpa [S, Finset.mem_insert, Finset.mem_singleton] using hz
    rcases hz' with rfl | rfl | rfl
    · exact hmemA
    · exact hmemB
    · exact hmemC
  have hScard : (S : Set X).ncard = 3 := by
    rw [Set.ncard_coe_finset]
    simp [S, habX, hacX, hbcX]
  have hfiniteX : Finite (Subtype X) := (hWfinite.subset hXsubset).to_subtype
  let : Finite (Subtype X) := hfiniteX
  have hle : (S : Set X).ncard ≤ (G.neighborSet xX).ncard :=
    Set.ncard_mono (α := Subtype X) hSsubset
  rw [hScard] at hle
  omega

private theorem exteriorNoTile :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ, q ∉
        U.cells ∧ q ∉ V.cells := by
  classical
  intro U V q hq
  have hn : q ∉ (↑(U.cells ∪ V.cells) : Set GaussianInt) := by simpa using hq
  constructor
  · intro hqU
    apply hn
    change q ∈ (U.cells ∪ V.cells : Finset GaussianInt)
    exact Finset.mem_union.mpr (Or.inl hqU)
  · intro hqV
    apply hn
    change q ∈ (U.cells ∪ V.cells : Finset GaussianInt)
    exact Finset.mem_union.mpr (Or.inr hqV)

private theorem rayAt0 :
    ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → (∃ q ∈
        T.cells, (q = c0 ∧ (g = {x, x + ⟨0, 1⟩} ∨ g = {x, x + 1})) ∨ (q = c1 ∧ (g = {x, x + ⟨0,
        1⟩} ∨ g = {x - 1, x})) ∨ (q = c2 ∧ (g = {x - 1, x} ∨ g = {x - ⟨0, 1⟩, x})) ∨ (q = c3 ∧ (g
        = {x - ⟨0, 1⟩, x} ∨ g = {x, x + 1}))))) → (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt),
            x ∈ g → g ∈ FootprintEdges T → c1 ∉ T.cells → c2 ∉ T.cells → c3 ∉ T.cells → g = {x,
        x + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ g = {x, x + (1 : GaussianInt)}) := by
  classical
  intro x c0 c1 c2 c3 supportedRay T g hxg hg h1 h2 h3
  rcases supportedRay T g hxg hg with ⟨q, hq, hcase⟩
  rcases hcase with ⟨hq0, hr⟩ | ⟨hq1, hr⟩ | ⟨hq2, hr⟩ | ⟨hq3, hr⟩
  · exact hr
  · exact False.elim (h1 (by rw [← hq1]; exact hq))
  · exact False.elim (h2 (by rw [← hq2]; exact hq))
  · exact False.elim (h3 (by rw [← hq3]; exact hq))

private theorem rayAt1 :
    ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → (∃ q ∈
        T.cells, (q = c0 ∧ (g = {x, x + ⟨0, 1⟩} ∨ g = {x, x + 1})) ∨ (q = c1 ∧ (g = {x, x + ⟨0,
        1⟩} ∨ g = {x - 1, x})) ∨ (q = c2 ∧ (g = {x - 1, x} ∨ g = {x - ⟨0, 1⟩, x})) ∨ (q = c3 ∧ (g
        = {x - ⟨0, 1⟩, x} ∨ g = {x, x + 1}))))) → (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt),
            x ∈ g → g ∈ FootprintEdges T → c0 ∉ T.cells → c2 ∉ T.cells → c3 ∉ T.cells → g = {x,
        x + ⟨(0 : ℤ), (1 : ℤ)⟩} ∨ g = {x - (1 : GaussianInt), x}) := by
  classical
  intro x c0 c1 c2 c3 supportedRay T g hxg hg h0 h2 h3
  rcases supportedRay T g hxg hg with ⟨q, hq, hcase⟩
  rcases hcase with ⟨hq0, hr⟩ | ⟨hq1, hr⟩ | ⟨hq2, hr⟩ | ⟨hq3, hr⟩
  · exact False.elim (h0 (by rw [← hq0]; exact hq))
  · exact hr
  · exact False.elim (h2 (by rw [← hq2]; exact hq))
  · exact False.elim (h3 (by rw [← hq3]; exact hq))

private theorem rayAt2 :
    ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → (∃ q ∈
        T.cells, (q = c0 ∧ (g = {x, x + ⟨0, 1⟩} ∨ g = {x, x + 1})) ∨ (q = c1 ∧ (g = {x, x + ⟨0,
        1⟩} ∨ g = {x - 1, x})) ∨ (q = c2 ∧ (g = {x - 1, x} ∨ g = {x - ⟨0, 1⟩, x})) ∨ (q = c3 ∧ (g
        = {x - ⟨0, 1⟩, x} ∨ g = {x, x + 1}))))) → (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt),
            x ∈ g → g ∈ FootprintEdges T → c0 ∉ T.cells → c1 ∉ T.cells → c3 ∉ T.cells → g =
        {x - (1 : GaussianInt), x} ∨ g = {x - ⟨(0 : ℤ), (1 : ℤ)⟩, x}) := by
  classical
  intro x c0 c1 c2 c3 supportedRay T g hxg hg h0 h1 h3
  rcases supportedRay T g hxg hg with ⟨q, hq, hcase⟩
  rcases hcase with ⟨hq0, hr⟩ | ⟨hq1, hr⟩ | ⟨hq2, hr⟩ | ⟨hq3, hr⟩
  · exact False.elim (h0 (by rw [← hq0]; exact hq))
  · exact False.elim (h1 (by rw [← hq1]; exact hq))
  · exact hr
  · exact False.elim (h3 (by rw [← hq3]; exact hq))

private theorem rayAt3 :
    ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → (∃ q ∈
        T.cells, (q = c0 ∧ (g = {x, x + ⟨0, 1⟩} ∨ g = {x, x + 1})) ∨ (q = c1 ∧ (g = {x, x + ⟨0,
        1⟩} ∨ g = {x - 1, x})) ∨ (q = c2 ∧ (g = {x - 1, x} ∨ g = {x - ⟨0, 1⟩, x})) ∨ (q = c3 ∧ (g
        = {x - ⟨0, 1⟩, x} ∨ g = {x, x + 1}))))) → (∀ (T : ProtoTile), ∀ (g : Finset GaussianInt),
            x ∈ g → g ∈ FootprintEdges T → c0 ∉ T.cells → c1 ∉ T.cells → c2 ∉ T.cells → g =
        {x - ⟨(0 : ℤ), (1 : ℤ)⟩, x} ∨ g = {x, x + (1 : GaussianInt)}) := by
  classical
  intro x c0 c1 c2 c3 supportedRay T g hxg hg h0 h1 h2
  rcases supportedRay T g hxg hg with ⟨q, hq, hcase⟩
  rcases hcase with ⟨hq0, hr⟩ | ⟨hq1, hr⟩ | ⟨hq2, hr⟩ | ⟨hq3, hr⟩
  · exact False.elim (h0 (by rw [← hq0]; exact hq))
  · exact False.elim (h1 (by rw [← hq1]; exact hq))
  · exact False.elim (h2 (by rw [← hq2]; exact hq))
  · exact hr

private theorem hsectorRay :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt), ∀ (e : Finset GaussianInt), ∀ (f :
        Finset GaussianInt), (x ∈ e) → ((x ∈ f) → ((e ∈ FootprintEdges U) → ((f ∈ FootprintEdges
        V) → (
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (¬ (c0 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧
        c2 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c3 ∈ V.cells))
        → ((¬ (c3 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c0 ∈
        U.cells ∧ c3 ∈ V.cells)) → ((¬ (c0 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c1 ∈
        V.cells)) → ((¬ (c2 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c3 ∈ V.cells)) →
        (((c0 ∈ U.cells ∧ c2 ∈ V.cells) ∨ (c2 ∈ U.cells ∧ c0 ∈ V.cells) ∨ (c1 ∈ U.cells ∧ c3 ∈
        V.cells) ∨ (c3 ∈ U.cells ∧ c1 ∈ V.cells)) → ((∀ (T : ProtoTile), ∀ (g : Finset
        GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → ((c1 ∉ T.cells) → ((c2 ∉ T.cells) →
        ((c3 ∉ T.cells) → (g = {x, x + ⟨0, 1⟩} ∨ g = {x, x + 1})))))) → ((∀ (T : ProtoTile), ∀ (g
            : Finset GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → ((c0 ∉ T.cells) → ((c2 ∉
        T.cells) → ((c3 ∉ T.cells) → (g = {x, x + ⟨0, 1⟩} ∨ g = {x - 1, x})))))) → ((∀ (T :
            ProtoTile), ∀ (g : Finset GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → ((c0 ∉
        T.cells) → ((c1 ∉ T.cells) → ((c3 ∉ T.cells) → (g = {x - 1, x} ∨ g = {x - ⟨0, 1⟩,
        x})))))) → ((∀ (T : ProtoTile), ∀ (g : Finset GaussianInt), (x ∈ g) → ((g ∈
        FootprintEdges T) → ((c0 ∉ T.cells) → ((c1 ∉ T.cells) → ((c2 ∉ T.cells) → (g = {x - ⟨0,
        1⟩, x} ∨ g = {x, x + 1})))))) → ((c0 ∈ U.cells ∧ c2 ∈ V.cells ∧ (e = {x, x + ⟨0, 1⟩} ∨ e
        = {x, x + 1}) ∧ (f = {x - ⟨0, 1⟩, x} ∨ f = {x - 1, x})) ∨ (c2 ∈ U.cells ∧ c0 ∈ V.cells ∧
        (e = {x - 1, x} ∨ e = {x - ⟨0, 1⟩, x}) ∧ (f = {x, x + ⟨0, 1⟩} ∨ f = {x, x + 1})) ∨ (c1 ∈
        U.cells ∧ c3 ∈ V.cells ∧ (e = {x, x + ⟨0, 1⟩} ∨ e = {x - 1, x}) ∧ (f = {x - ⟨0, 1⟩, x} ∨
        f = {x, x + 1})) ∨ (c3 ∈ U.cells ∧ c1 ∈ V.cells ∧ (e = {x - ⟨0, 1⟩, x} ∨ e = {x, x + 1})
        ∧ (f = {x, x + ⟨0, 1⟩} ∨ f = {x - 1, x}))))))))))))))))))))))) := by
  classical
  intro U V x e f hxe hxf hUedge hVedge c0 c1 c2 c3 no01 no10 no12 no21 no23 no32 no30 no03
      noSame0 noSame1 noSame2 noSame3 hpattern rayAt0 rayAt1 rayAt2 rayAt3
  rcases hpattern with hpat | hpat | hpat | hpat
  · rcases hpat with ⟨hU0, hV2⟩
    have hU1 : c1 ∉ U.cells := by intro h; exact no12 ⟨h, hV2⟩
    have hU2 : c2 ∉ U.cells := by intro h; exact noSame2 ⟨h, hV2⟩
    have hU3 : c3 ∉ U.cells := by intro h; exact no32 ⟨h, hV2⟩
    have hV0 : c0 ∉ V.cells := by intro h; exact noSame0 ⟨hU0, h⟩
    have hV1 : c1 ∉ V.cells := by intro h; exact no01 ⟨hU0, h⟩
    have hV3 : c3 ∉ V.cells := by intro h; exact no03 ⟨hU0, h⟩
    refine Or.inl ⟨hU0, hV2, ?_, ?_⟩
    · exact rayAt0 U e hxe hUedge hU1 hU2 hU3
    · exact (rayAt2 V f hxf hVedge hV0 hV1 hV3).symm
  · rcases hpat with ⟨hU2, hV0⟩
    have hU0 : c0 ∉ U.cells := by intro h; exact noSame0 ⟨h, hV0⟩
    have hU1 : c1 ∉ U.cells := by intro h; exact no10 ⟨h, hV0⟩
    have hU3 : c3 ∉ U.cells := by intro h; exact no30 ⟨h, hV0⟩
    have hV1 : c1 ∉ V.cells := by intro h; exact no21 ⟨hU2, h⟩
    have hV2 : c2 ∉ V.cells := by intro h; exact noSame2 ⟨hU2, h⟩
    have hV3 : c3 ∉ V.cells := by intro h; exact no23 ⟨hU2, h⟩
    refine Or.inr (Or.inl ⟨hU2, hV0, ?_, ?_⟩)
    · exact rayAt2 U e hxe hUedge hU0 hU1 hU3
    · exact rayAt0 V f hxf hVedge hV1 hV2 hV3
  · rcases hpat with ⟨hU1, hV3⟩
    have hU0 : c0 ∉ U.cells := by intro h; exact no03 ⟨h, hV3⟩
    have hU2 : c2 ∉ U.cells := by intro h; exact no23 ⟨h, hV3⟩
    have hU3 : c3 ∉ U.cells := by intro h; exact noSame3 ⟨h, hV3⟩
    have hV0 : c0 ∉ V.cells := by intro h; exact no10 ⟨hU1, h⟩
    have hV1 : c1 ∉ V.cells := by intro h; exact noSame1 ⟨hU1, h⟩
    have hV2 : c2 ∉ V.cells := by intro h; exact no12 ⟨hU1, h⟩
    refine Or.inr (Or.inr (Or.inl ⟨hU1, hV3, ?_, ?_⟩))
    · exact rayAt1 U e hxe hUedge hU0 hU2 hU3
    · exact rayAt3 V f hxf hVedge hV0 hV1 hV2
  · rcases hpat with ⟨hU3, hV1⟩
    have hU0 : c0 ∉ U.cells := by intro h; exact no01 ⟨h, hV1⟩
    have hU1 : c1 ∉ U.cells := by intro h; exact noSame1 ⟨h, hV1⟩
    have hU2 : c2 ∉ U.cells := by intro h; exact no21 ⟨h, hV1⟩
    have hV0 : c0 ∉ V.cells := by intro h; exact no30 ⟨hU3, h⟩
    have hV2 : c2 ∉ V.cells := by intro h; exact no32 ⟨hU3, h⟩
    have hV3 : c3 ∉ V.cells := by intro h; exact noSame3 ⟨hU3, h⟩
    refine Or.inr (Or.inr (Or.inr ⟨hU3, hV1, ?_, ?_⟩))
    · exact rayAt3 U e hxe hUedge hU0 hU1 hU2
    · exact rayAt1 V f hxf hVedge hV0 hV2 hV3

private theorem noExtra :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt),
        ∀ (e : Finset GaussianInt), ∀ (f : Finset GaussianInt), (e ∈ F ∩ FootprintEdges U) → ((f
        ∈ F ∩ FootprintEdges V) → (
    let dir : Fin 4 → GaussianInt := fun i =>
      match i.val with
      | 0 => x + ⟨0, 1⟩
      | 1 => x + 1
      | 2 => x - ⟨0, 1⟩
      | _ => x - 1
    (∀ (i : Fin 4), ∀ (j : Fin 4), ∀ (k : Fin 4), (i ≠ j) → ((i ≠ k) → ((j ≠ k) → ((({x, dir i} :
        Finset GaussianInt) ∈ F) → ((({x, dir j} : Finset GaussianInt) ∈ F) → ((({x, dir k} :
        Finset GaussianInt) ∈ F) → (False))))))) → (∀ g ∈ F, ∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 :
        ℕ)), ∀ (k : Fin (4 : ℕ)), i ≠ j → i ≠ k → j ≠ k → e = {x, dir i} ∨ e = {dir i, x} → f =
        {x, dir j} ∨ f = {dir j, x} → g = {x, dir k} ∨ g = {dir k, x} → False))) := by
  classical
  intro U V F x e f he hf dir noThreeDir g hg i j k hij hik hjk hea hfb hgc
  have ha : ({x, dir i} : Finset GaussianInt) ∈ F := by
    rcases hea with h | h
    · rw [h.symm]; exact he.1
    · have h' : ({x, dir i} : Finset GaussianInt) = e := by
        rw [Finset.pair_comm]
        exact h.symm
      rw [h']
      exact he.1
  have hb : ({x, dir j} : Finset GaussianInt) ∈ F := by
    rcases hfb with h | h
    · rw [h.symm]; exact hf.1
    · have h' : ({x, dir j} : Finset GaussianInt) = f := by
        rw [Finset.pair_comm]
        exact h.symm
      rw [h']
      exact hf.1
  have hc : ({x, dir k} : Finset GaussianInt) ∈ F := by
    rcases hgc with h | h
    · rw [h.symm]; exact hg
    · have h' : ({x, dir k} : Finset GaussianInt) = g := by
        rw [Finset.pair_comm]
        exact h.symm
      rw [h']
      exact hg
  exact noThreeDir i j k hij hik hjk ha hb hc

private theorem cyclicToEdge :
    ∀ (F : Set (Finset GaussianInt)),
      ∀ (p : List GaussianInt),
        ∀ (u : GaussianInt),
          ∀ (v : GaussianInt),
            (4 : ℕ) ≤ p.length →
              p.head? = some u →
                p.getLast? = some v →
                  (∀ (e : Finset GaussianInt),
                      e ∈ F ↔
                        e = { v, u } ∨
                          ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂
                            : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = { a, b }) →
                    (let cyclicEdges := p.zip p.tail ++ [(v, u)];
                      ∀ (q : LatticeCell),
                        ((q + (1 : LatticeCell),
                            q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
                            cyclicEdges ∧
                            (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩,
                            q + (1 : LatticeCell)) ∉
                            cyclicEdges →
                            GridRayCrossingIndex (q + (1 : LatticeCell)) p =
                            GridRayCrossingIndex q p) ∧
                          ((q + (1 : LatticeCell),
                            q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                            cyclicEdges ∨
                            (q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩,
                            q + (1 : LatticeCell)) ∈
                            cyclicEdges →
                            (GridRayCrossingIndex (q + (1 : LatticeCell)) p -
                            GridRayCrossingIndex q p).natAbs =
                            (1 : ℕ)) ∧
                            ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩,
                            q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
                            cyclicEdges ∧
                            (q + ⟨(0 : ℤ), (1 : ℤ)⟩,
                            q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∉
                            cyclicEdges →
                            GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) p =
                            GridRayCrossingIndex q p) ∧
                            ((q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩,
                            q + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                            cyclicEdges ∨
                            (q + ⟨(0 : ℤ), (1 : ℤ)⟩,
                            q + (1 : LatticeCell) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∈
                            cyclicEdges →
                            (GridRayCrossingIndex (q + ⟨(0 : ℤ), (1 : ℤ)⟩) p -
                            GridRayCrossingIndex q p).natAbs =
                            (1 : ℕ))) →
                      (∀ (g : Finset GaussianInt),
                          g ∈ F →
                            g = { v, u } ∨
                            ∃ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ g = { a, b }) →
                        ∀ (a : GaussianInt),
                          ∀ (b : GaussianInt),
                            (a, b) ∈ p.zip p.tail ++ [(v, u)] → { a, b } ∈ F := by
  classical
  intro F p u v hlen hhead hlast hedges hcross hcycleEdge a b hab
  rcases List.mem_append.mp hab with h | h
  · rw [List.mem_iff_getElem] at h
    rcases h with ⟨i, hi, hpair⟩
    have hi' : i + 1 < p.length := by
      simp [List.length_zip] at hi
      omega
    rw [List.getElem_zip, List.getElem_tail] at hpair
    injection hpair with ha hb
    let l₁ := p.take i
    let l₂ := p.drop (i + 2)
    have hdecomp : p = l₁ ++ p[i] :: p[i + 1] :: l₂ := by
      dsimp [l₁, l₂]
      calc
        p = p.take i ++ p.drop i := (List.take_append_drop i p).symm
        _ = p.take i ++ p[i] :: p.drop (i + 1) := by
          rw [List.drop_eq_getElem_cons (by omega)]
        _ = p.take i ++ p[i] :: p[i + 1] :: p.drop (i + 2) := by
          rw [List.drop_eq_getElem_cons hi']
    subst a
    subst b
    exact (hedges _).mpr (Or.inr ⟨p[i], p[i + 1], l₁, l₂, hdecomp, rfl⟩)
  · simp only [List.mem_singleton] at h
    rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    exact (hedges _).mpr (Or.inl rfl)

private theorem exterior13A :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (¬ (c0 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧
        c2 ∈ V.cells)) → ((¬ (c0 ∈ U.cells ∧ c3 ∈ V.cells)) → ((∀ (q : GaussianInt), (q ∉
        U.cells) → ((q ∉ V.cells) → (q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ))) → (c0 ∈
        U.cells → c2 ∈ V.cells → c1 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧ c3 ∈ (↑(U.cells
        ∪ V.cells) : Set GaussianInt)ᶜ))))) := by
  classical
  intro U V x c0 c1 c2 c3 no01 no12 no32 no03 inExterior hu0 hv2
  constructor
  · apply inExterior
    · intro h; exact no12 ⟨h, hv2⟩
    · intro h; exact no01 ⟨hu0, h⟩
  · apply inExterior
    · intro h; exact no32 ⟨h, hv2⟩
    · intro h; exact no03 ⟨hu0, h⟩

private theorem exterior13B :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (¬ (c1 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧
        c3 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c0 ∈ V.cells)) → ((∀ (q : GaussianInt), (q ∉
        U.cells) → ((q ∉ V.cells) → (q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ))) → (c2 ∈
        U.cells → c0 ∈ V.cells → c1 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧ c3 ∈ (↑(U.cells
        ∪ V.cells) : Set GaussianInt)ᶜ))))) := by
  classical
  intro U V x c0 c1 c2 c3 no10 no21 no23 no30 inExterior hu2 hv0
  constructor
  · apply inExterior
    · intro h; exact no10 ⟨h, hv0⟩
    · intro h; exact no21 ⟨hu2, h⟩
  · apply inExterior
    · intro h; exact no30 ⟨h, hv0⟩
    · intro h; exact no23 ⟨hu2, h⟩

private theorem exterior02A :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (¬ (c1 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧
        c3 ∈ V.cells)) → ((¬ (c0 ∈ U.cells ∧ c3 ∈ V.cells)) → ((∀ (q : GaussianInt), (q ∉
        U.cells) → ((q ∉ V.cells) → (q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ))) → (c1 ∈
        U.cells → c3 ∈ V.cells → c0 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧ c2 ∈ (↑(U.cells
        ∪ V.cells) : Set GaussianInt)ᶜ))))) := by
  classical
  intro U V x c0 c1 c2 c3 no10 no12 no23 no03 inExterior hu1 hv3
  constructor
  · apply inExterior
    · intro h; exact no03 ⟨h, hv3⟩
    · intro h; exact no10 ⟨hu1, h⟩
  · apply inExterior
    · intro h; exact no23 ⟨h, hv3⟩
    · intro h; exact no12 ⟨hu1, h⟩

private theorem exterior02B :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (¬ (c0 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧
        c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c0 ∈ V.cells)) → ((∀ (q : GaussianInt), (q ∉
        U.cells) → ((q ∉ V.cells) → (q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ))) → (c3 ∈
        U.cells → c1 ∈ V.cells → c0 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧ c2 ∈ (↑(U.cells
        ∪ V.cells) : Set GaussianInt)ᶜ))))) := by
  classical
  intro U V x c0 c1 c2 c3 no01 no21 no32 no30 inExterior hu3 hv1
  constructor
  · apply inExterior
    · intro h; exact no01 ⟨h, hv1⟩
    · intro h; exact no30 ⟨hu3, h⟩
  · apply inExterior
    · intro h; exact no21 ⟨h, hv1⟩
    · intro h; exact no32 ⟨hu3, h⟩

private theorem hEeqAt936 :
    ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (p : List GaussianInt), ∀ (u :
        GaussianInt), ∀ (v : GaussianInt),
    let c0 : GaussianInt := x
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), ((a, b) ∈ p.zip p.tail ++ [(v, u)]) → (({a, b} :
        Finset GaussianInt) ∈ F)) → (
    let I : GaussianInt → Int := fun q => GridRayCrossingIndex q p
    (∀ (q : GaussianInt), ((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧ (q + ⟨0, 1⟩,
        q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)]) → (GridRayCrossingIndex (q + ⟨0, 1⟩) p =
        GridRayCrossingIndex q p)) → ((c3 + ⟨0, 1⟩ = x) → ((({x, x + 1} : Finset GaussianInt) ∉
        F) → (I c0 = I c3)))) := by
  classical
  intro F x p u v c0 c3 cyclicToEdge I crossNorthEq c3i hEabsent
  have hnc :
      (c3 + 1 + ⟨0, 1⟩, c3 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
      (c3 + ⟨0, 1⟩, c3 + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] := by
    constructor
    · intro h
      apply hEabsent
      convert cyclicToEdge _ _ h using 1; simp [c3, Finset.pair_comm]; ring
    · intro h
      apply hEabsent
      convert cyclicToEdge _ _ h using 1; simp [c3, Finset.pair_comm]; ring
  have h := crossNorthEq c3 hnc
  simpa [I, c0, c3, c3i] using h

private theorem hNeqAt966 :
    ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (p : List GaussianInt), ∀ (u :
        GaussianInt), ∀ (v : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), ((a, b) ∈ p.zip p.tail ++ [(v, u)]) → (({a, b} :
        Finset GaussianInt) ∈ F)) → (
    let I : GaussianInt → Int := fun q => GridRayCrossingIndex q p
    (∀ (q : GaussianInt), ((q + 1, q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧ (q + 1 + ⟨0, 1⟩,
        q + 1) ∉ p.zip p.tail ++ [(v, u)]) → (GridRayCrossingIndex (q + 1) p =
        GridRayCrossingIndex q p)) → ((c1 + 1 = x) → ((({x, x + ⟨0, 1⟩} : Finset GaussianInt) ∉
        F) → (I c0 = I c1)))) := by
  classical
  intro F x p u v c0 c1 cyclicToEdge I crossEastEq c1add hNabsent
  have hnc :
      (c1 + 1, c1 + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
      (c1 + 1 + ⟨0, 1⟩, c1 + 1) ∉ p.zip p.tail ++ [(v, u)] := by
    constructor
    · intro h
      apply hNabsent
      convert cyclicToEdge _ _ h using 1; simp [c1, Finset.pair_comm]
    · intro h
      apply hNabsent
      convert cyclicToEdge _ _ h using 1; simp [c1, Finset.pair_comm]
  have h := crossEastEq c1 hnc
  simpa [I, c0, c1, c1add] using h

private theorem hSeqAt999 :
    ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (p : List GaussianInt), ∀ (u :
        GaussianInt), ∀ (v : GaussianInt),
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), ((a, b) ∈ p.zip p.tail ++ [(v, u)]) → (({a, b} :
        Finset GaussianInt) ∈ F)) → (
    let I : GaussianInt → Int := fun q => GridRayCrossingIndex q p
    (∀ (q : GaussianInt), ((q + 1, q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧ (q + 1 + ⟨0, 1⟩,
        q + 1) ∉ p.zip p.tail ++ [(v, u)]) → (GridRayCrossingIndex (q + 1) p =
        GridRayCrossingIndex q p)) → ((c2 + 1 = x - ⟨0, 1⟩) → ((({x - ⟨0, 1⟩, x} : Finset
        GaussianInt) ∉ F) → (I c3 = I c2)))) := by
  classical
  intro F x p u v c2 c3 cyclicToEdge I crossEastEq c2add hSabsent
  have c2addi : c2 + 1 + ⟨0, 1⟩ = x := by dsimp [c2]; ring
  have hnc :
      (c2 + 1, c2 + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
      (c2 + 1 + ⟨0, 1⟩, c2 + 1) ∉ p.zip p.tail ++ [(v, u)] := by
    constructor
    · intro h
      apply hSabsent
      convert cyclicToEdge _ _ h using 1; simp [c2]; ring
    · intro h
      apply hSabsent
      simpa [c2, c2add, c2addi, Finset.pair_comm] using cyclicToEdge _ _ h
  have h := crossEastEq c2 hnc
  simpa [I, c2, c3, c2add] using h

private theorem hWeqAt1029 :
    ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (p : List GaussianInt), ∀ (u :
        GaussianInt), ∀ (v : GaussianInt),
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), ((a, b) ∈ p.zip p.tail ++ [(v, u)]) → (({a, b} :
        Finset GaussianInt) ∈ F)) → (
    let I : GaussianInt → Int := fun q => GridRayCrossingIndex q p
    (∀ (q : GaussianInt), ((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧ (q + ⟨0, 1⟩,
        q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)]) → (GridRayCrossingIndex (q + ⟨0, 1⟩) p =
        GridRayCrossingIndex q p)) → ((c2 + 1 + ⟨0, 1⟩ = x) → ((c2 + ⟨0, 1⟩ = x - 1) → ((({x - 1,
        x} : Finset GaussianInt) ∉ F) → (I c1 = I c2))))) := by
  classical
  intro F x p u v c1 c2 cyclicToEdge I crossNorthEq c2addi c2i hWabsent
  have hnc :
      (c2 + 1 + ⟨0, 1⟩, c2 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
      (c2 + ⟨0, 1⟩, c2 + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] := by
    constructor
    · intro h
      apply hWabsent
      simpa [c2, c2addi, c2i, Finset.pair_comm] using cyclicToEdge _ _ h
    · intro h
      apply hWabsent
      convert cyclicToEdge _ _ h using 1; simp [c2]; ring
  have h := crossNorthEq c2 hnc
  simpa [I, c1, c2, c2i] using h

private abbrev hNeqAt1093 := ApollonianSuperharmonic.ExteriorMixedCycleProof.hNeqAt966

private theorem verticalSupport :
    (∀ (a : GaussianInt),
        ∀ (b : GaussianInt),
          ∀ (c : GaussianInt),
            ∀ (d : GaussianInt),
              ({ a, b } : Finset GaussianInt) = { c, d } →
                c ≠ d → a = c ∧ b = d ∨ a = d ∧ b = c) →
      ∀ (T : ProtoTile),
        ∀ (q : GaussianInt),
          {q, q + ⟨(0 : ℤ), (1 : ℤ)⟩} ∈ FootprintEdges T →
            q ∈ T.cells ∨ q - (1 : GaussianInt) ∈ T.cells := by
  classical
  intro pairCases T q h
  rw [FootprintEdges] at h
  simp only [Set.mem_ofPred_eq] at h
  rcases h with ⟨z, hz, hshape⟩
  have hqd : q ≠ q + ⟨0, 1⟩ := by
    intro heq
    have hi := congrArg Zsqrtd.im heq
    simp at hi
  rcases hshape with hbot | hleft | hright | htop
  · rcases pairCases z (z + 1) q (q + ⟨0, 1⟩) hbot.symm hqd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst z
      have hi := congrArg Zsqrtd.im h₂
      simp at hi
    · subst z
      have hi := congrArg Zsqrtd.im h₂
      simp at hi
  · rcases pairCases z (z + ⟨0, 1⟩) q (q + ⟨0, 1⟩) hleft.symm hqd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst z
      exact Or.inl hz
    · subst z
      have hi := congrArg Zsqrtd.im h₂
      simp at hi; omega
  · rcases pairCases (z + 1) (z + 1 + ⟨0, 1⟩) q (q + ⟨0, 1⟩) hright.symm hqd with ⟨h₁, h₂⟩ | ⟨h₁,
      h₂⟩
    · have hzeq : z = q - 1 := by calc
        z = (z + 1) - 1 := by ring
        _ = q - 1 := by rw [h₁]
      rw [hzeq] at hz
      exact Or.inr hz
    · have hi₁ := congrArg Zsqrtd.im h₁
      have hi₂ := congrArg Zsqrtd.im h₂
      have hr₁ := congrArg Zsqrtd.re h₁
      have hr₂ := congrArg Zsqrtd.re h₂
      simp at hi₁ hi₂; omega
  · rcases pairCases (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) q (q + ⟨0, 1⟩) htop.symm hqd with ⟨h₁, h₂⟩ |
      ⟨h₁, h₂⟩
    · have hr₁ := congrArg Zsqrtd.re h₁
      have hr₂ := congrArg Zsqrtd.re h₂
      simp at hr₁ hr₂; omega
    · have hr₁ := congrArg Zsqrtd.re h₁
      have hr₂ := congrArg Zsqrtd.re h₂
      simp at hr₁ hr₂; omega

private theorem horizontalSupport :
    (∀ (a : GaussianInt),
        ∀ (b : GaussianInt),
          ∀ (c : GaussianInt),
            ∀ (d : GaussianInt),
              ({ a, b } : Finset GaussianInt) = { c, d } →
                c ≠ d → a = c ∧ b = d ∨ a = d ∧ b = c) →
      ∀ (T : ProtoTile),
        ∀ (q : GaussianInt),
          {q, q + (1 : GaussianInt)} ∈ FootprintEdges T →
            q ∈ T.cells ∨ q - ⟨(0 : ℤ), (1 : ℤ)⟩ ∈ T.cells := by
  classical
  intro pairCases T q h
  rw [FootprintEdges] at h
  simp only [Set.mem_ofPred_eq] at h
  rcases h with ⟨z, hz, hshape⟩
  have hqd : q ≠ q + 1 := by
    intro heq
    have hr := congrArg Zsqrtd.re heq
    simp at hr
  rcases hshape with hbot | hleft | hright | htop
  · rcases pairCases z (z + 1) q (q + 1) hbot.symm hqd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst z
      exact Or.inl hz
    · subst z
      have hr := congrArg Zsqrtd.re h₂
      simp at hr; omega
  · rcases pairCases z (z + ⟨0, 1⟩) q (q + 1) hleft.symm hqd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst z
      have hi := congrArg Zsqrtd.im h₂
      simp at hi
    · subst z
      have hi := congrArg Zsqrtd.im h₂
      simp at hi
  · rcases pairCases (z + 1) (z + 1 + ⟨0, 1⟩) q (q + 1) hright.symm hqd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hi₁ := congrArg Zsqrtd.im h₁
      have hi₂ := congrArg Zsqrtd.im h₂
      have hr₁ := congrArg Zsqrtd.re h₁
      have hr₂ := congrArg Zsqrtd.re h₂
      simp at hi₁ hi₂ hr₁ hr₂; omega
    · have hi₁ := congrArg Zsqrtd.im h₁
      have hi₂ := congrArg Zsqrtd.im h₂
      simp at hi₁ hi₂; omega
  · rcases pairCases (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) q (q + 1) htop.symm hqd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hzeq : z = q - ⟨0, 1⟩ := by calc
        z = (z + ⟨0, 1⟩) - ⟨0, 1⟩ := by ring
        _ = q - ⟨0, 1⟩ := by rw [h₁]
      rw [hzeq] at hz
      exact Or.inr hz
    · have hr₁ := congrArg Zsqrtd.re h₁
      have hr₂ := congrArg Zsqrtd.re h₂
      simp at hr₁ hr₂; omega

private theorem verticalNoF :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (F : Set (Finset GaussianInt)), (F ⊆ FootprintEdges U
        ∪ FootprintEdges V) → ((∀ (q : GaussianInt), (q ∈ (↑(U.cells ∪ V.cells) : Set
        GaussianInt)ᶜ) → (q ∉ U.cells ∧ q ∉ V.cells)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt),
            (({q, q + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T) → (q ∈ T.cells ∨ q - 1 ∈
        T.cells)) → (∀ q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ, q - (1 : GaussianInt) ∈
        (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ → {q, q + ⟨(0 : ℤ), (1 : ℤ)⟩} ∉ F))) := by
  classical
  intro U V F hsubset exteriorNoTile verticalSupport q hq hq' hF
  rcases hsubset hF with hU | hV
  · rcases verticalSupport U q hU with hqU | hqU'
    · exact (exteriorNoTile q hq).1 hqU
    · exact (exteriorNoTile (q - 1) hq').1 hqU'
  · rcases verticalSupport V q hV with hqV | hqV'
    · exact (exteriorNoTile q hq).2 hqV
    · exact (exteriorNoTile (q - 1) hq').2 hqV'

private theorem horizontalNoF :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (F : Set (Finset GaussianInt)), (F ⊆ FootprintEdges U
        ∪ FootprintEdges V) → ((∀ (q : GaussianInt), (q ∈ (↑(U.cells ∪ V.cells) : Set
        GaussianInt)ᶜ) → (q ∉ U.cells ∧ q ∉ V.cells)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt),
            (({q, q + 1} : Finset GaussianInt) ∈ FootprintEdges T) → (q ∈ T.cells ∨ q - ⟨0, 1⟩ ∈
        T.cells)) → (∀ q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ, q - ⟨(0 : ℤ), (1 : ℤ)⟩ ∈
        (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ → {q, q + (1 : GaussianInt)} ∉ F))) := by
  classical
  intro U V F hsubset exteriorNoTile horizontalSupport q hq hq' hF
  rcases hsubset hF with hU | hV
  · rcases horizontalSupport U q hU with hqU | hqU'
    · exact (exteriorNoTile q hq).1 hqU
    · exact (exteriorNoTile (q - ⟨0, 1⟩) hq').1 hqU'
  · rcases horizontalSupport V q hV with hqV | hqV'
    · exact (exteriorNoTile q hq).2 hqV
    · exact (exteriorNoTile (q - ⟨0, 1⟩) hq').2 hqV'


end ExteriorMixedCycleProof

namespace ExteriorCycleDetails

private theorem indexAdjacentExterior :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (F : Set (Finset GaussianInt)), ∀ (p : List
        GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt), (∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ((a, b) ∈ p.zip p.tail ++ [(v, u)]) → (({a, b} : Finset GaussianInt) ∈
            F)) → (
    let I : GaussianInt → Int := fun q => GridRayCrossingIndex q p
    (∀ (q : GaussianInt), ((q + 1, q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧ (q + 1 + ⟨0, 1⟩,
        q + 1) ∉ p.zip p.tail ++ [(v, u)]) → (GridRayCrossingIndex (q + 1) p =
        GridRayCrossingIndex q p)) → ((∀ (q : GaussianInt), ((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ p.zip
        p.tail ++ [(v, u)] ∧ (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)]) →
        (GridRayCrossingIndex (q + ⟨0, 1⟩) p = GridRayCrossingIndex q p)) → ((∀ (q :
            GaussianInt), (q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ) → ((q - 1 ∈ (↑(U.cells ∪
        V.cells) : Set GaussianInt)ᶜ) → (({q, q + ⟨0, 1⟩} : Finset GaussianInt) ∉ F))) → ((∀ (q :
            GaussianInt), (q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ) → ((q - ⟨0, 1⟩ ∈
            (↑(U.cells
        ∪ V.cells) : Set GaussianInt)ᶜ) → (({q, q + 1} : Finset GaussianInt) ∉ F))) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), a ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ → b ∈
        (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ → FourNeighborAdjacent a b → I a = I b))))) := by
  classical
  intro U V F p u v cyclicToEdge I crossEastEq crossNorthEq verticalNoF horizontalNoF a b ha hb hab
  rcases hab with hab | hab | hab | hab
  · subst b
    have hn := verticalNoF (a + 1) hb (by simpa using ha)
    have hnc :
        (a + 1, a + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
        (a + 1 + ⟨0, 1⟩, a + 1) ∉ p.zip p.tail ++ [(v, u)] := by
      constructor
      · intro h
        exact hn (by convert cyclicToEdge _ _ h using 1  )
      · intro h
        exact hn (by convert cyclicToEdge _ _ h using 1; simp [Finset.pair_comm] )
    have h := crossEastEq a hnc
    simpa only [I] using h.symm
  · have hb' : b + 1 = a := by rw [hab]; ring
    subst b
    have hn := verticalNoF a ha (by simpa using hb)
    have hnc :
        (a - 1 + 1, a - 1 + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
        (a - 1 + 1 + ⟨0, 1⟩, a - 1 + 1) ∉ p.zip p.tail ++ [(v, u)] := by
      constructor
      · intro h
        have h' : (a, a + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] := by
          convert h using 1; congr 1 <;> ring
        exact hn (cyclicToEdge _ _ h')
      · intro h
        exact hn (by convert cyclicToEdge _ _ h using 1; simp [Finset.pair_comm] )
    have h := crossEastEq (a - 1) hnc
    have hq : a - 1 + 1 = a := by ring
    change GridRayCrossingIndex ((a - 1) + 1) p = GridRayCrossingIndex (a - 1) p at h
    rw [hq] at h
    simpa only [I] using h
  · subst b
    have hn := horizontalNoF (a + ⟨0, 1⟩) hb (by simpa using ha)
    have hnc :
        (a + 1 + ⟨0, 1⟩, a + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
        (a + ⟨0, 1⟩, a + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] := by
      constructor
      · intro h
        exact hn (by convert cyclicToEdge _ _ h using 1; simp [Finset.pair_comm]; ring)
      · intro h
        exact hn (by convert cyclicToEdge _ _ h using 1; simp [Finset.pair_comm]; ring)
    have h := crossNorthEq a hnc
    simpa only [I] using h.symm
  · have hbCell : a - ⟨0, 1⟩ ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ := by
      rw [← hab]
      exact hb
    have hn := horizontalNoF a ha hbCell
    have hnc :
        (a + 1, a) ∉ p.zip p.tail ++ [(v, u)] ∧
        (a, a + 1) ∉ p.zip p.tail ++ [(v, u)] := by
      constructor
      · intro h
        exact hn (by convert cyclicToEdge _ _ h using 1; simp [Finset.pair_comm] )
      · intro h
        exact hn (by convert cyclicToEdge _ _ h using 1  )
    have hnc' :
        (b + 1 + ⟨0, 1⟩, b + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
        (b + ⟨0, 1⟩, b + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] := by
      convert hnc using 1 <;> rw [hab] <;> simp <;> ring
    have h := crossNorthEq b hnc'
    have hq : b + ⟨0, 1⟩ = a := by rw [hab]; ring
    change GridRayCrossingIndex (b + ⟨0, 1⟩) p = GridRayCrossingIndex b p at h
    rw [hq] at h
    simpa only [I] using h

private theorem walkConst :
    ∀ (S : Set GaussianInt), ∀ (J : GaussianInt → ℤ), (∀ (a : GaussianInt), ∀ (b : GaussianInt),
        a ∈ S → b ∈ S → FourNeighborAdjacent a b → J a = J b) → ∀ (walk : List GaussianInt), ∀
        (start : GaussianInt), ∀ (finish : GaussianInt), walk.head? = some start → walk.getLast?
        = some finish → (∀ z ∈ walk, z ∈ S) → (∀ (a : LatticeCell), ∀ (b : LatticeCell), ∀ (l₁ :
            List LatticeCell), ∀ (l₂ : List LatticeCell), walk = l₁ ++ a :: b :: l₂ →
        FourNeighborAdjacent a b) → J start = J finish := by
  classical
  intro S J step walk
  induction walk with
  | nil =>
      intro start finish hh
      simp at hh
  | cons a tail ih =>
      intro start finish hh hl hv hs
      have hstart : start = a := by
        have h' : a = start := by simpa using hh
        exact h'.symm
      cases tail with
      | nil =>
          simp at hh hl
          subst start
          subst finish
          rfl
      | cons b rest =>
          have hab : FourNeighborAdjacent a b := hs a b [] rest (by simp)
          have htailLast : (b :: rest).getLast? = some finish := by simpa using hl
          have htailVerts : ∀ z ∈ b :: rest, z ∈ S := by
            intro z hz
            exact hv z (by simp [hz])
          have htailSteps : ∀ c d l₁ l₂,
              b :: rest = l₁ ++ c :: d :: l₂ → FourNeighborAdjacent c d := by
            intro c d l₁ l₂ hdec
            have hdec' : a :: b :: rest = (a :: l₁) ++ c :: d :: l₂ := by
              simpa using congrArg (List.cons a) hdec
            exact hs c d (a :: l₁) l₂ hdec'
          have hfirst := step a b (hv a (by simp)) (hv b (by simp)) hab
          have htail := ih b finish rfl htailLast htailVerts htailSteps
          subst start
          exact hfirst.trans htail

end ExteriorCycleDetails

namespace ExteriorIndexCases

private theorem hmixed :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (F : Set (Finset GaussianInt)), ∀ (e : Finset GaussianInt), ∀ (f : Finset GaussianInt),
        (e ∈ F ∩ FootprintEdges U) → ((f ∈ F ∩ FootprintEdges V) → (e ≠ f))) := by
  classical
  intro U V hedge F e f he hf hef
  apply hedge
  exact ⟨e, ⟨he.2, by simpa [hef] using hf.2⟩⟩

private theorem pairEq :
    ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d : GaussianInt), a = c → b
        = d → ({a, b} : Finset GaussianInt) = {c, d} := by
  classical
  intro a b c d ha hb
  subst c
  subst d
  rfl

private theorem edgeLeft :
    ∀ (T : ProtoTile), ∀ q ∈ T.cells, {q, q + ⟨(0 : ℤ), (1 : ℤ)⟩} ∈ FootprintEdges T := by
  classical
  intro T q hq
  rw [FootprintEdges]
  exact ⟨q, hq, Or.inr (Or.inl rfl)⟩

private theorem edgeBottom :
    ∀ (T : ProtoTile), ∀ q ∈ T.cells, {q, q + (1 : GaussianInt)} ∈ FootprintEdges T := by
  classical
  intro T q hq
  rw [FootprintEdges]
  exact ⟨q, hq, Or.inl rfl⟩

private theorem edgeRight :
    ∀ (T : ProtoTile), ∀ q ∈ T.cells, {q + (1 : GaussianInt), q + (1 : GaussianInt) + ⟨(0 : ℤ),
        (1 : ℤ)⟩} ∈ FootprintEdges T := by
  classical
  intro T q hq
  rw [FootprintEdges]
  exact ⟨q, hq, Or.inr (Or.inr (Or.inl rfl))⟩

private theorem edgeTop :
    ∀ (T : ProtoTile), ∀ q ∈ T.cells, {q + ⟨(0 : ℤ), (1 : ℤ)⟩, q + (1 : GaussianInt) + ⟨(0 : ℤ),
        (1 : ℤ)⟩} ∈ FootprintEdges T := by
  classical
  intro T q hq
  rw [FootprintEdges]
  exact ⟨q, hq, Or.inr (Or.inr (Or.inr rfl))⟩

private theorem no01 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + ⟨0, 1⟩} : Finset
        GaussianInt) ∈ FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈
        T.cells) → (({q + 1, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c0
        ∈ U.cells ∧ c1 ∈ V.cells)))) := by
  classical
  intro U V hedge x c0 c1 edgeLeft edgeRight
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x, x + ⟨0, 1⟩}, ⟨by simpa [c0] using edgeLeft U c0 hu,
    by simpa [c1] using edgeRight V c1 hv⟩⟩

private theorem no10 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + ⟨0, 1⟩} : Finset
        GaussianInt) ∈ FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈
        T.cells) → (({q + 1, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c1
        ∈ U.cells ∧ c0 ∈ V.cells)))) := by
  classical
  intro U V hedge x c0 c1 edgeLeft edgeRight
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x, x + ⟨0, 1⟩}, ⟨by simpa [c1] using edgeRight U c1 hu,
    by simpa [c0] using edgeLeft V c0 hv⟩⟩

private theorem no12 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + 1} : Finset GaussianInt) ∈
        FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q + ⟨0,
        1⟩, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c1 ∈ U.cells ∧ c2 ∈
        V.cells)))) := by
  classical
  intro U V hedge x c1 c2 edgeBottom edgeTop
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x - 1, x}, ⟨by simpa [c1] using edgeBottom U c1 hu,
    by convert edgeTop V c2 hv using 1; simp [c2]; ring⟩⟩

private theorem no21 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + 1} : Finset GaussianInt) ∈
        FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q + ⟨0,
        1⟩, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c2 ∈ U.cells ∧ c1 ∈
        V.cells)))) := by
  classical
  intro U V hedge x c1 c2 edgeBottom edgeTop
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x - 1, x}, ⟨by convert edgeTop U c2 hu using 1; simp [c2]; ring,
    by simpa [c1] using edgeBottom V c1 hv⟩⟩

private theorem no23 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + ⟨0, 1⟩} : Finset
        GaussianInt) ∈ FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈
        T.cells) → (({q + 1, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c2
        ∈ U.cells ∧ c3 ∈ V.cells)))) := by
  classical
  intro U V hedge x c2 c3 edgeLeft edgeRight
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x - ⟨0, 1⟩, x}, ⟨by convert edgeRight U c2 hu using 1; simp [c2]; ring,
    by simpa [c3] using edgeLeft V c3 hv⟩⟩

private theorem no32 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + ⟨0, 1⟩} : Finset
        GaussianInt) ∈ FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈
        T.cells) → (({q + 1, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c3
        ∈ U.cells ∧ c2 ∈ V.cells)))) := by
  classical
  intro U V hedge x c2 c3 edgeLeft edgeRight
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x - ⟨0, 1⟩, x}, ⟨by simpa [c3] using edgeLeft U c3 hu,
    by convert edgeRight V c2 hv using 1; simp [c2]; ring⟩⟩

private theorem no30 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c0 : GaussianInt := x
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + 1} : Finset GaussianInt) ∈
        FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q + ⟨0,
        1⟩, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c3 ∈ U.cells ∧ c0 ∈
        V.cells)))) := by
  classical
  intro U V hedge x c0 c3 edgeBottom edgeTop
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x, x + 1}, ⟨by convert edgeTop U c3 hu using 1; simp [c3]; ring,
    by simpa [c0] using edgeBottom V c0 hv⟩⟩

private theorem no03 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), (¬(FootprintEdges U ∩ FootprintEdges V).Nonempty) → (∀
        (x : GaussianInt),
    let c0 : GaussianInt := x
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q, q + 1} : Finset GaussianInt) ∈
        FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (q : GaussianInt), (q ∈ T.cells) → (({q + ⟨0,
        1⟩, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T)) → (¬ (c0 ∈ U.cells ∧ c3 ∈
        V.cells)))) := by
  classical
  intro U V hedge x c0 c3 edgeBottom edgeTop
  rintro ⟨hu, hv⟩
  apply hedge
  exact ⟨{x, x + 1}, ⟨by simpa [c0] using edgeBottom U c0 hu,
    by convert edgeTop V c3 hv using 1; simp [c3]; ring⟩⟩

private theorem noSame0 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c0 : GaussianInt := x
    (∀ (q : GaussianInt), (q ∈ U.cells) → ((q ∈ V.cells) → (False))) → (¬ (c0 ∈ U.cells ∧ c0 ∈
        V.cells)) := by
  classical
  intro U V x c0 hcellDisjoint
  rintro ⟨hu, hv⟩
  exact hcellDisjoint c0 hu hv

private theorem noSame1 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c1 : GaussianInt := x - 1
    (∀ (q : GaussianInt), (q ∈ U.cells) → ((q ∈ V.cells) → (False))) → (¬ (c1 ∈ U.cells ∧ c1 ∈
        V.cells)) := by
  classical
  intro U V x c1 hcellDisjoint
  rintro ⟨hu, hv⟩
  exact hcellDisjoint c1 hu hv

private theorem noSame2 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    (∀ (q : GaussianInt), (q ∈ U.cells) → ((q ∈ V.cells) → (False))) → (¬ (c2 ∈ U.cells ∧ c2 ∈
        V.cells)) := by
  classical
  intro U V x c2 hcellDisjoint
  rintro ⟨hu, hv⟩
  exact hcellDisjoint c2 hu hv

private theorem noSame3 :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt),
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (∀ (q : GaussianInt), (q ∈ U.cells) → ((q ∈ V.cells) → (False))) → (¬ (c3 ∈ U.cells ∧ c3 ∈
        V.cells)) := by
  classical
  intro U V x c3 hcellDisjoint
  rintro ⟨hu, hv⟩
  exact hcellDisjoint c3 hu hv

private theorem inExterior :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ q ∉ U.cells, q ∉ V.cells → q ∈ (↑(U.cells ∪ V.cells)
        : Set GaussianInt)ᶜ := by
  classical
  intro U V q hu hv
  change q ∉ U.cells ∪ V.cells
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact hu h
  · exact hv h

private theorem hpne :
    ∀ (p : List GaussianInt), ((4 : ℕ) ≤ p.length) → (p ≠ []) := by
  classical
  intro p hlen h
  simp [h] at hlen

private theorem huMem :
    (by
      classical
      exact
        ∀ (p : List GaussianInt) (u : GaussianInt), p.head? = some u → u ∈ p) := by
  classical
  intro p u hhead
  rcases (List.head?_eq_some_iff.mp hhead) with ⟨l, rfl⟩
  simp

private theorem hvMem :
    (by
      classical
      exact
        ∀ (p : List GaussianInt) (v : GaussianInt), p.getLast? = some v → v ∈ p) := by
  classical
  intro p v hlast
  rcases (List.getLast?_eq_some_iff.mp hlast) with ⟨l, rfl⟩
  simp

private theorem vertexInW :
    ∀ (W : Set GaussianInt), ∀ (p : List GaussianInt), (W = (↑p.toFinset : Set GaussianInt)) → (∀
        z ∈ p, z ∈ W) := by
  classical
  intro W p hvertices z hz
  rw [hvertices]
  change z ∈ p.toFinset
  exact List.mem_toFinset.mpr hz

private theorem hWfinite :
    ∀ (W : Set GaussianInt), ∀ (p : List GaussianInt), (W = (↑p.toFinset : Set GaussianInt)) →
        (W.Finite) := by
  classical
  intro W p hvertices
  rw [hvertices]
  exact Finset.finite_toSet _

private def directionOffset : Fin 4 → GaussianInt :=
  ![⟨0, 1⟩, 1, -⟨0, 1⟩, -1]

private theorem dirInj :
    ∀ (x : GaussianInt),
      let dir : Fin 4 → GaussianInt := fun i =>
        match i.val with
        | 0 => x + ⟨0, 1⟩
        | 1 => x + 1
        | 2 => x - ⟨0, 1⟩
        | _ => x - 1
      Function.Injective dir := by
  classical
  intro x dir
  have hdir : dir = fun j => x + directionOffset j := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact sub_eq_add_neg x _
    · exact sub_eq_add_neg x _
  have hinjective : Function.Injective directionOffset := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
    | rfl
    | norm_num [directionOffset, Zsqrtd.ext_iff] at h
  intro i j hij
  rw [hdir] at hij
  exact hinjective (add_left_cancel hij)

private theorem dirNeX :
    ∀ (x : GaussianInt),
      let dir : Fin 4 → GaussianInt := fun i =>
        match i.val with
        | 0 => x + ⟨0, 1⟩
        | 1 => x + 1
        | 2 => x - ⟨0, 1⟩
        | _ => x - 1
      ∀ (i : Fin (4 : ℕ)), x ≠ dir i := by
  classical
  intro x dir
  have hdir : dir = fun j => x + directionOffset j := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact sub_eq_add_neg x _
    · exact sub_eq_add_neg x _
  have hnonzero : ∀ j, directionOffset j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num [directionOffset, Zsqrtd.ext_iff]
  intro i hi
  rw [hdir] at hi
  exact hnonzero i (add_left_cancel ((add_zero x).trans hi)).symm

private theorem noThreeDir :
    ∀ (W : Set GaussianInt), ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (p : List
        GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt), (p.Nodup) → (((4 : ℕ) ≤ p.length)
        → ((p.head? = some u) → ((p.getLast? = some v) → ((W = (↑p.toFinset : Set GaussianInt)) →
        ((FourNeighborAdjacent v u) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List
        GaussianInt), ∀ (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a
        b) → ((∀ (e : Finset GaussianInt), e ∈ F ↔ e = {v, u} ∨ ∃ (a : GaussianInt) (b :
        GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e
        = {a, b}) → ((∀ (g : Finset GaussianInt), (g ∈ F) → (g = {v, u} ∨ ∃ a b l₁ l₂, p = l₁ ++
        a :: b :: l₂ ∧ g = {a, b})) → ((u ∈ p) → ((v ∈ p) → ((∀ (z : GaussianInt), (z ∈ p) → (z ∈
        W)) → ((W.Finite) → (
    let dir : Fin 4 → GaussianInt := fun i =>
      match i.val with
      | 0 => x + ⟨0, 1⟩
      | 1 => x + 1
      | 2 => x - ⟨0, 1⟩
      | _ => x - 1
    (Function.Injective dir) → ((∀ (i : Fin 4), x ≠ dir i) → (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4
        : ℕ)), ∀ (k : Fin (4 : ℕ)), i ≠ j → i ≠ k → j ≠ k → {x, dir i} ∈ F → {x, dir j} ∈ F → {x,
        dir k} ∈ F → False))))))))))))))) := by
  classical
  intro W F x p u v hnodup hlen hhead hlast hvertices hclose hsteps hedges hcycleEdge huMem hvMem
      vertexInW hWfinite dir dirInj dirNeX i j k hij hik hjk ha hb hc
  apply (ExteriorMixedCycleProof.noThreeNeighbors W F x p u v hnodup hlen hhead hlast hvertices
      hclose hsteps hedges (ExteriorMixedCycleProof.edgeEndpointInW W F p u v hcycleEdge huMem
      hvMem vertexInW) hWfinite) (dir i) (dir j) (dir k) ha hb hc
    (dirNeX i) (dirNeX j) (dirNeX k)
    (fun h => hij (dirInj h)) (fun h => hik (dirInj h))
    (fun h => hjk (dirInj h))

private theorem hindexDiff :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (F : Set (Finset GaussianInt)), ∀ (x : GaussianInt),
        ∀ (e : Finset GaussianInt), ∀ (f : Finset GaussianInt), (x ∈ e) → ((x ∈ f) → ((e ∈ F ∩
        FootprintEdges U) → (∀ (p : List GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt),
        (e ∈ FootprintEdges U) → ((f ∈ FootprintEdges V) → (
    let c0 : GaussianInt := x
    let c1 : GaussianInt := x - 1
    let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
    let c3 : GaussianInt := x - ⟨0, 1⟩
    (¬ (c0 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧
        c2 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c1 ∈ V.cells)) → ((¬ (c2 ∈ U.cells ∧ c3 ∈ V.cells))
        → ((¬ (c3 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c0 ∈
        U.cells ∧ c3 ∈ V.cells)) → ((¬ (c0 ∈ U.cells ∧ c0 ∈ V.cells)) → ((¬ (c1 ∈ U.cells ∧ c1 ∈
        V.cells)) → ((¬ (c2 ∈ U.cells ∧ c2 ∈ V.cells)) → ((¬ (c3 ∈ U.cells ∧ c3 ∈ V.cells)) →
        (((c0 ∈ U.cells ∧ c2 ∈ V.cells) ∨ (c2 ∈ U.cells ∧ c0 ∈ V.cells) ∨ (c1 ∈ U.cells ∧ c3 ∈
        V.cells) ∨ (c3 ∈ U.cells ∧ c1 ∈ V.cells)) → ((∀ (q : GaussianInt), (q ∉ U.cells) → ((q ∉
        V.cells) → (q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ))) → ((∀ (T : ProtoTile), ∀ (g
        : Finset GaussianInt), (x ∈ g) → ((g ∈ FootprintEdges T) → (∃ q ∈ T.cells, (q = c0 ∧ (g =
        {x, x + ⟨0, 1⟩} ∨ g = {x, x + 1})) ∨ (q = c1 ∧ (g = {x, x + ⟨0, 1⟩} ∨ g = {x - 1, x})) ∨
        (q = c2 ∧ (g = {x - 1, x} ∨ g = {x - ⟨0, 1⟩, x})) ∨ (q = c3 ∧ (g = {x - ⟨0, 1⟩, x} ∨ g =
        {x, x + 1}))))) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, b} : Finset
        GaussianInt) ∈ F) → ((a, b) ∈ (p.zip p.tail) ++ [(v, u)] ∨ (b, a) ∈ (p.zip p.tail) ++
        [(v, u)])) → (
    let dir : Fin 4 → GaussianInt := fun i =>
      match i.val with
      | 0 => x + ⟨0, 1⟩
      | 1 => x + 1
      | 2 => x - ⟨0, 1⟩
      | _ => x - 1
    (∀ (g : Finset GaussianInt), (g ∈ F) → (∀ (i : Fin 4), ∀ (j : Fin 4), ∀ (k : Fin 4), (i ≠ j)
        → ((i ≠ k) → ((j ≠ k) → ((e = {x, dir i} ∨ e = {dir i, x}) → ((f = {x, dir j} ∨ f =
        {dir j, x}) → ((g = {x, dir k} ∨ g = {dir k, x}) → (False)))))))) → ((∀ (a :
        GaussianInt), ∀ (b : GaussianInt), ((a, b) ∈ p.zip p.tail ++ [(v, u)]) → (({a, b} :
        Finset GaussianInt) ∈ F)) → (
    let I : GaussianInt → Int := fun q => GridRayCrossingIndex q p
    (∀ (q : GaussianInt), ((q + 1, q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧ (q + 1 + ⟨0, 1⟩,
        q + 1) ∉ p.zip p.tail ++ [(v, u)]) → (GridRayCrossingIndex (q + 1) p =
        GridRayCrossingIndex q p)) → ((∀ (q : GaussianInt), ((q + 1, q + 1 + ⟨0, 1⟩) ∈ p.zip
        p.tail ++ [(v, u)] ∨ (q + 1 + ⟨0, 1⟩, q + 1) ∈ p.zip p.tail ++ [(v, u)]) →
        ((GridRayCrossingIndex (q + 1) p - GridRayCrossingIndex q p).natAbs = 1)) → ((∀ (q :
        GaussianInt), ((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧ (q + ⟨0, 1⟩, q +
        1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)]) → (GridRayCrossingIndex (q + ⟨0, 1⟩) p =
        GridRayCrossingIndex q p)) → ((∀ (q : GaussianInt), ((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∈ p.zip
        p.tail ++ [(v, u)] ∨ (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)]) →
        ((GridRayCrossingIndex (q + ⟨0, 1⟩) p - GridRayCrossingIndex q p).natAbs = 1)) → ((c1 + 1
        = x) → ((c2 + 1 = x - ⟨0, 1⟩) → ((c2 + 1 + ⟨0, 1⟩ = x) → ((c2 + ⟨0, 1⟩ = x - 1) → ((c3 +
        ⟨0, 1⟩ = x) → ((c3 + 1 + ⟨0, 1⟩ = x + 1) → (((c1 ∈ (↑(U.cells ∪ V.cells) : Set
        GaussianInt)ᶜ ∧ c3 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ) ∧ (I c1 - I c3).natAbs =
        1) ∨ ((c0 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧ c2 ∈ (↑(U.cells ∪ V.cells) : Set
        GaussianInt)ᶜ) ∧ (I c0 - I c2).natAbs = 1)))))))))))))))))))))))))))))))))) := by
  classical
  intro U V F x e f hxe hxf he p u v hUedge hVedge c0 c1 c2 c3 no01 no10 no12 no21 no23 no32 no30
      no03 noSame0 noSame1 noSame2 noSame3 hpattern inExterior supportedRay cyclicPair dir
      noExtra cyclicToEdge I crossEastEq crossEastJump crossNorthEq crossNorthJump c1add c2add
      c2addi c2i c3i c3addi
  let nDir : Fin 4 := 0
  let eDir : Fin 4 := 1
  let sDir : Fin 4 := 2
  let wDir : Fin 4 := 3
  have c1addi : c1 + 1 + ⟨0, 1⟩ = x + ⟨0, 1⟩ := by dsimp [c1]; ring
  rcases (ExteriorMixedCycleProof.hsectorRay U V x e f hxe hxf hUedge hVedge no01 no10 no12 no21
      no23 no32 no30 no03 noSame0 noSame1 noSame2 noSame3 hpattern
      (ExteriorMixedCycleProof.rayAt0 x supportedRay) (ExteriorMixedCycleProof.rayAt1 x
      supportedRay) (ExteriorMixedCycleProof.rayAt2 x supportedRay)
      (ExteriorMixedCycleProof.rayAt3 x supportedRay)) with h0 | h1 | h2 | h3
  · rcases h0 with ⟨hu0, hv2, heRay, hfRay⟩
    have hexterior := (ExteriorMixedCycleProof.exterior13A U V x no01 no12 no32 no03 inExterior)
        hu0 hv2
    rcases heRay with heN | heE
    · have hEabsent : ({x, x + 1} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfS | hfW
        · exact noExtra _ hg nDir sDir eDir (by decide) (by decide) (by decide)
            (Or.inl heN) (Or.inr hfS) (Or.inl rfl)
        · exact noExtra _ hg nDir wDir eDir (by decide) (by decide) (by decide)
            (Or.inl heN) (Or.inr hfW) (Or.inl rfl)
      have hNcyc := cyclicPair x (x + ⟨0, 1⟩) (by simpa [heN] using he.1)
      have hNjump : (I c0 - I c1).natAbs = 1 := by
        have hc : (c1 + 1, c1 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c1 + 1 + ⟨0, 1⟩, c1 + 1) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c1, c1add, c1addi] using hNcyc
        have h := crossEastJump c1 hc
        simpa [I, c0, c1, c1add] using h
      have hEeq : I c0 = I c3 := ExteriorMixedCycleProof.hEeqAt936 F x p u v cyclicToEdge
          crossNorthEq c3i hEabsent
      have hneg : I c1 - I c3 = -(I c0 - I c1) := by rw [hEeq]; ring
      refine Or.inl ⟨hexterior, ?_⟩
      rw [hneg, Int.natAbs_neg, hNjump]
    · have hNabsent : ({x, x + ⟨0, 1⟩} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfS | hfW
        · exact noExtra _ hg eDir sDir nDir (by decide) (by decide) (by decide)
            (Or.inl heE) (Or.inr hfS) (Or.inl rfl)
        · exact noExtra _ hg eDir wDir nDir (by decide) (by decide) (by decide)
            (Or.inl heE) (Or.inr hfW) (Or.inl rfl)
      have hEcyc := cyclicPair x (x + 1) (by simpa [heE] using he.1)
      have hEjump : (I c0 - I c3).natAbs = 1 := by
        have hc : (c3 + 1 + ⟨0, 1⟩, c3 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c3 + ⟨0, 1⟩, c3 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c3, c3i, c3addi] using Or.symm hEcyc
        have h := crossNorthJump c3 hc
        simpa [I, c0, c3, c3i] using h
      have hNeq : I c0 = I c1 := ExteriorMixedCycleProof.hNeqAt966 F x p u v cyclicToEdge
          crossEastEq c1add hNabsent
      refine Or.inl ⟨hexterior, ?_⟩
      rw [← hNeq]
      exact hEjump
  · rcases h1 with ⟨hu2, hv0, heRay, hfRay⟩
    have hexterior := (ExteriorMixedCycleProof.exterior13B U V x no10 no21 no23 no30 inExterior)
        hu2 hv0
    rcases heRay with heW | heS
    · have hSabsent : ({x - ⟨0, 1⟩, x} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfN | hfE
        · exact noExtra _ hg wDir nDir sDir (by decide) (by decide) (by decide)
            (Or.inr heW) (Or.inl hfN) (Or.inr rfl)
        · exact noExtra _ hg wDir eDir sDir (by decide) (by decide) (by decide)
            (Or.inr heW) (Or.inl hfE) (Or.inr rfl)
      have hWcyc := cyclicPair (x - 1) x (by simpa [heW] using he.1)
      have hWjump : (I c1 - I c2).natAbs = 1 := by
        have hc : (c2 + 1 + ⟨0, 1⟩, c2 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c2 + ⟨0, 1⟩, c2 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c2, c2addi, c2i] using Or.symm hWcyc
        have h := crossNorthJump c2 hc
        simpa [I, c1, c2, c2i] using h
      have hSeq : I c3 = I c2 := ExteriorMixedCycleProof.hSeqAt999 F x p u v cyclicToEdge
          crossEastEq c2add hSabsent
      refine Or.inl ⟨hexterior, ?_⟩
      rw [hSeq]
      exact hWjump
    · have hWabsent : ({x - 1, x} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfN | hfE
        · exact noExtra _ hg sDir nDir wDir (by decide) (by decide) (by decide)
            (Or.inr heS) (Or.inl hfN) (Or.inr rfl)
        · exact noExtra _ hg sDir eDir wDir (by decide) (by decide) (by decide)
            (Or.inr heS) (Or.inl hfE) (Or.inr rfl)
      have hScyc := cyclicPair (x - ⟨0, 1⟩) x (by simpa [heS] using he.1)
      have hSjump : (I c3 - I c2).natAbs = 1 := by
        have hc : (c2 + 1, c2 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c2 + 1 + ⟨0, 1⟩, c2 + 1) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c2, c2add] using hScyc
        have h := crossEastJump c2 hc
        simpa [I, c2, c3, c2add] using h
      have hWeq : I c1 = I c2 := ExteriorMixedCycleProof.hWeqAt1029 F x p u v cyclicToEdge
          crossNorthEq c2addi c2i hWabsent
      have hneg : I c1 - I c3 = -(I c3 - I c2) := by rw [hWeq]; ring
      refine Or.inl ⟨hexterior, ?_⟩
      rw [hneg, Int.natAbs_neg, hSjump]
  · rcases h2 with ⟨hu1, hv3, heRay, hfRay⟩
    have hexterior := (ExteriorMixedCycleProof.exterior02A U V x no10 no12 no23 no03 inExterior)
        hu1 hv3
    rcases heRay with heN | heW
    · have hWabsent : ({x - 1, x} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfS | hfE
        · exact noExtra _ hg nDir sDir wDir (by decide) (by decide) (by decide)
            (Or.inl heN) (Or.inr hfS) (Or.inr rfl)
        · exact noExtra _ hg nDir eDir wDir (by decide) (by decide) (by decide)
            (Or.inl heN) (Or.inl hfE) (Or.inr rfl)
      have hNcyc := cyclicPair x (x + ⟨0, 1⟩) (by simpa [heN] using he.1)
      have hNjump : (I c0 - I c1).natAbs = 1 := by
        have hc : (c1 + 1, c1 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c1 + 1 + ⟨0, 1⟩, c1 + 1) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c1, c1add, c1addi] using hNcyc
        have h := crossEastJump c1 hc
        simpa [I, c0, c1, c1add] using h
      have hWeq : I c1 = I c2 := ExteriorMixedCycleProof.hWeqAt1029 F x p u v cyclicToEdge
          crossNorthEq c2addi c2i hWabsent
      refine Or.inr ⟨hexterior, ?_⟩
      have hneg : I c0 - I c2 = I c0 - I c1 := by rw [hWeq]
      rw [hneg]
      exact hNjump
    · have hNabsent : ({x, x + ⟨0, 1⟩} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfS | hfE
        · exact noExtra _ hg wDir sDir nDir (by decide) (by decide) (by decide)
            (Or.inr heW) (Or.inr hfS) (Or.inl rfl)
        · exact noExtra _ hg wDir eDir nDir (by decide) (by decide) (by decide)
            (Or.inr heW) (Or.inl hfE) (Or.inl rfl)
      have hWcyc := cyclicPair (x - 1) x (by simpa [heW] using he.1)
      have hWjump : (I c1 - I c2).natAbs = 1 := by
        have hc : (c2 + 1 + ⟨0, 1⟩, c2 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c2 + ⟨0, 1⟩, c2 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c2, c2addi, c2i] using Or.symm hWcyc
        have h := crossNorthJump c2 hc
        simpa [I, c1, c2, c2i] using h
      have hNeq : I c0 = I c1 := ExteriorMixedCycleProof.hNeqAt1093 F x p u v cyclicToEdge
          crossEastEq c1add hNabsent
      refine Or.inr ⟨hexterior, ?_⟩
      have hEq : I c0 - I c2 = I c1 - I c2 := by rw [hNeq]
      rw [hEq]
      exact hWjump
  · rcases h3 with ⟨hu3, hv1, heRay, hfRay⟩
    have hexterior := (ExteriorMixedCycleProof.exterior02B U V x no01 no21 no32 no30 inExterior)
        hu3 hv1
    rcases heRay with heS | heE
    · have hEabsent : ({x, x + 1} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfN | hfW
        · exact noExtra _ hg sDir nDir eDir (by decide) (by decide) (by decide)
            (Or.inr heS) (Or.inl hfN) (Or.inl rfl)
        · exact noExtra _ hg sDir wDir eDir (by decide) (by decide) (by decide)
            (Or.inr heS) (Or.inr hfW) (Or.inl rfl)
      have hScyc := cyclicPair (x - ⟨0, 1⟩) x (by simpa [heS] using he.1)
      have hSjump : (I c3 - I c2).natAbs = 1 := by
        have hc : (c2 + 1, c2 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c2 + 1 + ⟨0, 1⟩, c2 + 1) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c2, c2add] using hScyc
        have h := crossEastJump c2 hc
        simpa [I, c2, c3, c2add] using h
      have hEeq : I c0 = I c3 := ExteriorMixedCycleProof.hEeqAt936 F x p u v cyclicToEdge
          crossNorthEq c3i hEabsent
      refine Or.inr ⟨hexterior, ?_⟩
      have hEq : I c0 - I c2 = I c3 - I c2 := by rw [hEeq]
      rw [hEq]
      exact hSjump
    · have hSabsent : ({x - ⟨0, 1⟩, x} : Finset GaussianInt) ∉ F := by
        intro hg
        rcases hfRay with hfN | hfW
        · exact noExtra _ hg eDir nDir sDir (by decide) (by decide) (by decide)
            (Or.inl heE) (Or.inl hfN) (Or.inr rfl)
        · exact noExtra _ hg eDir wDir sDir (by decide) (by decide) (by decide)
            (Or.inl heE) (Or.inr hfW) (Or.inr rfl)
      have hEcyc := cyclicPair x (x + 1) (by simpa [heE] using he.1)
      have hEjump : (I c0 - I c3).natAbs = 1 := by
        have hc : (c3 + 1 + ⟨0, 1⟩, c3 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
            (c3 + ⟨0, 1⟩, c3 + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] := by
          simpa [c3, c3i, c3addi] using Or.symm hEcyc
        have h := crossNorthJump c3 hc
        simpa [I, c0, c3, c3i] using h
      have hSeq : I c3 = I c2 := ExteriorMixedCycleProof.hSeqAt999 F x p u v cyclicToEdge
          crossEastEq c2add hSabsent
      refine Or.inr ⟨hexterior, ?_⟩
      have hEq : I c0 - I c2 = I c0 - I c3 := by rw [hSeq]
      rw [hEq]
      exact hEjump

end ExteriorIndexCases

theorem P3963T1ExteriorMixedCycleObstruction
    (U V : ProtoTile)
    (hdisjoint : Disjoint U.cells V.cells)
    (hedge : ¬ (FootprintEdges U ∩ FootprintEdges V).Nonempty)
    (houtside : FourNeighborConnected
      ((↑(U.cells ∪ V.cells) : Set LatticeCell)ᶜ))
    (W : Set GaussianInt) (F : Set (Finset GaussianInt))
    (hcycle : SimpleGridCycle W F)
    (hsubset : F ⊆ FootprintEdges U ∪ FootprintEdges V)
    (x : GaussianInt) (e f : Finset GaussianInt)
    (hxe : x ∈ e) (hxf : x ∈ f)
    (he : e ∈ F ∩ FootprintEdges U)
    (hf : f ∈ F ∩ FootprintEdges V) : False := by
-- BODY
  rcases hcycle with ⟨p, u, v, hnodup, hlen, hhead, hlast, hvertices,
    hclose, hsteps, hedges⟩
  have hlen3 : 3 ≤ p.length := by omega
  have hcross := GridRayCrossingIndexAdjacentCell p u v hhead hlast hnodup
    hlen3 (ExteriorMixedCycleProof.hadj p hlen hsteps) hclose
  have hUedge : e ∈ FootprintEdges U := he.2
  have hVedge : f ∈ FootprintEdges V := hf.2
  have hcycleEdge (g : Finset GaussianInt) (hg : g ∈ F) :
      g = {v, u} ∨ ∃ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ g = {a, b} :=
    (hedges g).mp hg
  let c0 : GaussianInt := x
  let c1 : GaussianInt := x - 1
  let c2 : GaussianInt := x - 1 - ⟨0, 1⟩
  let c3 : GaussianInt := x - ⟨0, 1⟩
  have pairEq (a b c d : GaussianInt) (ha : a = c) (hb : b = d) :
      ({a, b} : Finset GaussianInt) = {c, d} := ExteriorIndexCases.pairEq a b c d ha hb
  have incident (T : ProtoTile) (g : Finset GaussianInt)
      (hxg : x ∈ g) (hg : g ∈ FootprintEdges T) :
      ∃ q ∈ T.cells, q = c0 ∨ q = c1 ∨ q = c2 ∨ q = c3 := ExteriorMixedCycleProof.incident x T g
          hxg hg
  have hOccU := incident U e hxe hUedge
  have hOccV := incident V f hxf hVedge
  have edgeLeft (T : ProtoTile) (q : GaussianInt) (hq : q ∈ T.cells) :
      ({q, q + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T := ExteriorIndexCases.edgeLeft T
          q hq
  have edgeBottom (T : ProtoTile) (q : GaussianInt) (hq : q ∈ T.cells) :
      ({q, q + 1} : Finset GaussianInt) ∈ FootprintEdges T := ExteriorIndexCases.edgeBottom T q hq
  have edgeRight (T : ProtoTile) (q : GaussianInt) (hq : q ∈ T.cells) :
      ({q + 1, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T :=
          ExteriorIndexCases.edgeRight T q hq
  have edgeTop (T : ProtoTile) (q : GaussianInt) (hq : q ∈ T.cells) :
      ({q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T :=
          ExteriorIndexCases.edgeTop T q hq
  have no01 : ¬ (c0 ∈ U.cells ∧ c1 ∈ V.cells) := ExteriorIndexCases.no01 U V hedge x edgeLeft
      edgeRight
  have no10 : ¬ (c1 ∈ U.cells ∧ c0 ∈ V.cells) := ExteriorIndexCases.no10 U V hedge x edgeLeft
      edgeRight
  have no12 : ¬ (c1 ∈ U.cells ∧ c2 ∈ V.cells) := ExteriorIndexCases.no12 U V hedge x edgeBottom
      edgeTop
  have no21 : ¬ (c2 ∈ U.cells ∧ c1 ∈ V.cells) := ExteriorIndexCases.no21 U V hedge x edgeBottom
      edgeTop
  have no23 : ¬ (c2 ∈ U.cells ∧ c3 ∈ V.cells) := ExteriorIndexCases.no23 U V hedge x edgeLeft
      edgeRight
  have no32 : ¬ (c3 ∈ U.cells ∧ c2 ∈ V.cells) := ExteriorIndexCases.no32 U V hedge x edgeLeft
      edgeRight
  have no30 : ¬ (c3 ∈ U.cells ∧ c0 ∈ V.cells) := ExteriorIndexCases.no30 U V hedge x edgeBottom
      edgeTop
  have no03 : ¬ (c0 ∈ U.cells ∧ c3 ∈ V.cells) := ExteriorIndexCases.no03 U V hedge x edgeBottom
      edgeTop
  have hcellDisjoint (q : GaussianInt) (hu : q ∈ U.cells)
      (hv : q ∈ V.cells) : False := (Finset.disjoint_left.mp hdisjoint) hu hv
  have noSame0 : ¬ (c0 ∈ U.cells ∧ c0 ∈ V.cells) := ExteriorIndexCases.noSame0 U V x hcellDisjoint
  have noSame1 : ¬ (c1 ∈ U.cells ∧ c1 ∈ V.cells) := ExteriorIndexCases.noSame1 U V x hcellDisjoint
  have noSame2 : ¬ (c2 ∈ U.cells ∧ c2 ∈ V.cells) := ExteriorIndexCases.noSame2 U V x hcellDisjoint
  have noSame3 : ¬ (c3 ∈ U.cells ∧ c3 ∈ V.cells) := ExteriorIndexCases.noSame3 U V x hcellDisjoint
  have hpattern :
      (c0 ∈ U.cells ∧ c2 ∈ V.cells) ∨ (c2 ∈ U.cells ∧ c0 ∈ V.cells) ∨
      (c1 ∈ U.cells ∧ c3 ∈ V.cells) ∨ (c3 ∈ U.cells ∧ c1 ∈ V.cells) :=
          ExteriorMixedCycleProof.hpattern U V x hOccU hOccV no01 no10 no12 no21 no23 no32 no30
          no03 noSame0 noSame1 noSame2 noSame3
  have inExterior (q : GaussianInt) (hu : q ∉ U.cells)
      (hv : q ∉ V.cells) : q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ :=
          ExteriorIndexCases.inExterior U V q hu hv
  have pairCases (a b c d : GaussianInt)
      (hpair : ({a, b} : Finset GaussianInt) = {c, d}) (hcd : c ≠ d) :
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := ExteriorMixedCycleProof.pairCases a b c d hpair hcd
  have supportedRay (T : ProtoTile) (g : Finset GaussianInt)
      (hxg : x ∈ g) (hg : g ∈ FootprintEdges T) :
      ∃ q ∈ T.cells,
        (q = c0 ∧ (g = {x, x + ⟨0, 1⟩} ∨ g = {x, x + 1})) ∨
        (q = c1 ∧ (g = {x, x + ⟨0, 1⟩} ∨ g = {x - 1, x})) ∨
        (q = c2 ∧ (g = {x - 1, x} ∨ g = {x - ⟨0, 1⟩, x})) ∨
        (q = c3 ∧ (g = {x - ⟨0, 1⟩, x} ∨ g = {x, x + 1})) := ExteriorMixedCycleProof.supportedRay
            x pairEq T g hxg hg
  have cyclicPair (a b : GaussianInt) (hab : ({a, b} : Finset GaussianInt) ∈ F) :
      (a, b) ∈ (p.zip p.tail) ++ [(v, u)] ∨
      (b, a) ∈ (p.zip p.tail) ++ [(v, u)] := ExteriorMixedCycleProof.cyclicPair F p u v hhead
          hlast hclose hsteps hedges hcross hcycleEdge (ExteriorMixedCycleProof.adjNe)
              pairCases (ExteriorMixedCycleProof.adjacentMemZip) a b hab
  have huMem : u ∈ p := ExteriorIndexCases.huMem p u hhead
  have hvMem : v ∈ p := ExteriorIndexCases.hvMem p v hlast
  have vertexInW (z : GaussianInt) (hz : z ∈ p) : z ∈ W := ExteriorIndexCases.vertexInW W p
      hvertices z hz
  have hWfinite : W.Finite := ExteriorIndexCases.hWfinite W p hvertices
  have exteriorNoTile (q : GaussianInt)
      (hq : q ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ) :
      q ∉ U.cells ∧ q ∉ V.cells := ExteriorMixedCycleProof.exteriorNoTile U V q hq
  let dir : Fin 4 → GaussianInt := fun i =>
    match i.val with
    | 0 => x + ⟨0, 1⟩
    | 1 => x + 1
    | 2 => x - ⟨0, 1⟩
    | _ => x - 1
  have dirInj : Function.Injective dir := ExteriorIndexCases.dirInj x
  have dirNeX (i : Fin 4) : x ≠ dir i := ExteriorIndexCases.dirNeX x i
  have noThreeDir (i j k : Fin 4)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (ha : ({x, dir i} : Finset GaussianInt) ∈ F)
      (hb : ({x, dir j} : Finset GaussianInt) ∈ F)
      (hc : ({x, dir k} : Finset GaussianInt) ∈ F) : False := ExteriorIndexCases.noThreeDir W F x
          p u v hnodup hlen hhead hlast hvertices hclose hsteps hedges hcycleEdge huMem hvMem
          vertexInW hWfinite dirInj dirNeX i j k hij hik hjk ha hb hc
  have noExtra (g : Finset GaussianInt) (hg : g ∈ F)
      (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hea : e = {x, dir i} ∨ e = {dir i, x})
      (hfb : f = {x, dir j} ∨ f = {dir j, x})
      (hgc : g = {x, dir k} ∨ g = {dir k, x}) : False := ExteriorMixedCycleProof.noExtra U V F x
          e f he hf noThreeDir g hg i j k hij hik hjk hea hfb hgc
  have cyclicToEdge (a b : GaussianInt)
      (hab : (a, b) ∈ p.zip p.tail ++ [(v, u)]) :
      ({a, b} : Finset GaussianInt) ∈ F := ExteriorMixedCycleProof.cyclicToEdge F p u v hlen
          hhead hlast hedges hcross hcycleEdge a b hab
  let I : GaussianInt → Int := fun q => GridRayCrossingIndex q p
  have crossEastEq (q : GaussianInt)
      (hnc : (q + 1, q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
        (q + 1 + ⟨0, 1⟩, q + 1) ∉ p.zip p.tail ++ [(v, u)]) :
      GridRayCrossingIndex (q + 1) p = GridRayCrossingIndex q p :=
    (hcross q).1 hnc
  have crossEastJump (q : GaussianInt)
      (hcyc : (q + 1, q + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
        (q + 1 + ⟨0, 1⟩, q + 1) ∈ p.zip p.tail ++ [(v, u)]) :
      (GridRayCrossingIndex (q + 1) p - GridRayCrossingIndex q p).natAbs = 1 :=
    (hcross q).2.1 hcyc
  have crossNorthEq (q : GaussianInt)
      (hnc : (q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)] ∧
        (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∉ p.zip p.tail ++ [(v, u)]) :
      GridRayCrossingIndex (q + ⟨0, 1⟩) p = GridRayCrossingIndex q p :=
    (hcross q).2.2.1 hnc
  have crossNorthJump (q : GaussianInt)
      (hcyc : (q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)] ∨
        (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∈ p.zip p.tail ++ [(v, u)]) :
      (GridRayCrossingIndex (q + ⟨0, 1⟩) p - GridRayCrossingIndex q p).natAbs = 1 :=
    (hcross q).2.2.2 hcyc
  have c1add : c1 + 1 = x := by dsimp [c1]; ring
  have c2add : c2 + 1 = x - ⟨0, 1⟩ := by dsimp [c2]; ring
  have c2addi : c2 + 1 + ⟨0, 1⟩ = x := by dsimp [c2]; ring
  have c2i : c2 + ⟨0, 1⟩ = x - 1 := by dsimp [c2]; ring
  have c3i : c3 + ⟨0, 1⟩ = x := by dsimp [c3]; ring
  have c3addi : c3 + 1 + ⟨0, 1⟩ = x + 1 := by dsimp [c3]; ring
  have hindexDiff :
      ((c1 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧
        c3 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ) ∧
          (I c1 - I c3).natAbs = 1) ∨
        ((c0 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ ∧
          c2 ∈ (↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ) ∧
            (I c0 - I c2).natAbs = 1) := ExteriorIndexCases.hindexDiff U V F x e f hxe hxf he p u
                v hUedge hVedge no01 no10 no12 no21 no23 no32 no30 no03 noSame0 noSame1 noSame2
                noSame3 hpattern inExterior supportedRay cyclicPair noExtra cyclicToEdge
                crossEastEq crossEastJump crossNorthEq crossNorthJump c1add c2add c2addi c2i c3i
                c3addi
  have walkConstExterior := (ExteriorCycleDetails.walkConst)
    ((↑(U.cells ∪ V.cells) : Set GaussianInt)ᶜ) I (ExteriorCycleDetails.indexAdjacentExterior U V
        F p u v cyclicToEdge crossEastEq crossNorthEq (ExteriorMixedCycleProof.verticalNoF U V F
        hsubset exteriorNoTile (ExteriorMixedCycleProof.verticalSupport pairCases))
        (ExteriorMixedCycleProof.horizontalNoF U V F hsubset exteriorNoTile
        (ExteriorMixedCycleProof.horizontalSupport pairCases)))
  rcases hindexDiff with ⟨⟨ha, hb⟩, hd⟩ | ⟨⟨ha, hb⟩, hd⟩
  · rcases houtside.2 c1 ha c3 hb with ⟨walk, hh, hl, hv, hs⟩
    have hsame := walkConstExterior walk c1 c3 hh hl hv hs
    rw [hsame] at hd
    norm_num at hd
  · rcases houtside.2 c0 ha c2 hb with ⟨walk, hh, hl, hv, hs⟩
    have hsame := walkConstExterior walk c0 c2 hh hl hv hs
    rw [hsame] at hd
    norm_num at hd

end ApollonianSuperharmonic

end
