/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndex
public import LeanPool.ApollonianSuperharmonic.GridStepLogLiftDelta

/-!
# GridRayCrossingIndexZeroOfEdgeLifts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

noncomputable section

-- [TABLET NODE: GridRayCrossingIndexZeroOfEdgeLifts]
theorem GridRayCrossingIndexZeroOfEdgeLifts
    (q : LatticeCell) (p : List GaussianInt) (x y : GaussianInt)
    (F : GaussianInt → ℂ)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (hadj : ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b)
    (hclose : FourNeighborAdjacent y x)
    (hlift : ∀ a b : GaussianInt,
      ((∃ l₁ l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂) ∨
        (a = y ∧ b = x)) →
      ∃ L : Set.Icc (0 : Real) 1 → ℂ,
        Continuous L ∧ L ⟨0, by norm_num⟩ = F a ∧ L ⟨1, by norm_num⟩ = F b ∧
        ∀ t, Complex.exp (L t) =
          (1 - (t : Real)) * ((a : ℂ) - GridCellCenter q) +
            (t : Real) * ((b : ℂ) - GridCellCenter q)) :
    GridRayCrossingIndex q p = 0 := by
-- BODY
  let step : GaussianInt → GaussianInt → Int := fun a b ↦
    if b = a + ⟨0, 1⟩ ∧ a.im = q.im ∧ a.re ≤ q.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = q.im ∧ a.re ≤ q.re then -1
    else 0
  let C : ℂ := 2 * Real.pi * Complex.I
  have hstep (a b : GaussianInt)
      (hoccur : (∃ l₁ l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂) ∨
        (a = y ∧ b = x))
      (hab : FourNeighborAdjacent a b) :
      F b - F a =
        Complex.log ((b : ℂ) - GridCellCenter q) -
          Complex.log ((a : ℂ) - GridCellCenter q) - C * step a b := by
    rcases hlift a b hoccur with ⟨L, hL, hL0, hL1, hexp⟩
    have h := GridStepLogLiftDelta q a b hab L hL hexp
    rw [hL0, hL1] at h
    exact h
  have chain : ∀ (l : List GaussianInt),
      (∃ pre, p = pre ++ l) →
      ∀ a b, l.head? = some a → l.getLast? = some b →
      F b - F a =
        Complex.log ((b : ℂ) - GridCellCenter q) -
          Complex.log ((a : ℂ) - GridCellCenter q) -
          C * (List.zipWith step l l.tail).sum := by
    intro l hsuffix
    induction l with
    | nil => simp
    | cons a l ih =>
        cases l with
        | nil =>
            intro u v hu hv
            simp at hu hv
            subst u
            subst v
            simp
        | cons b l =>
            intro u v hu hv
            simp only [List.head?_cons, Option.some.injEq] at hu
            subst u
            have hbhead : (b :: l).head? = some b := rfl
            have hsuffix' : ∃ pre, p = pre ++ (b :: l) := by
              rcases hsuffix with ⟨pre, hpre⟩
              refine ⟨pre ++ [a], ?_⟩
              rw [hpre]
              simp [List.append_assoc]
            have hchain := ih hsuffix' b v hbhead hv
            have hoccur : ∃ l₁ l₂ : List GaussianInt,
                p = l₁ ++ a :: b :: l₂ := by
              rcases hsuffix with ⟨pre, hpre⟩
              exact ⟨pre, l, hpre⟩
            have hab := hadj a b hoccur.choose hoccur.choose_spec.choose
              hoccur.choose_spec.choose_spec
            have habstep := hstep a b (Or.inl hoccur) hab
            simp only [List.tail_cons, List.zipWith_cons_cons, List.sum_cons]
            simp only [List.tail_cons] at hchain
            rw [Int.cast_add]
            linear_combination hchain + habstep
  have hpsuffix : ∃ pre, p = pre ++ p := ⟨[], by simp⟩
  have hchain := chain p hpsuffix x y hhead hlast
  have hcloseStep := hstep y x (Or.inr ⟨rfl, rfl⟩) hclose
  have htel : (F y - F x) + (F x - F y) =
      (Complex.log ((y : ℂ) - GridCellCenter q) -
          Complex.log ((x : ℂ) - GridCellCenter q) -
          C * ((List.zipWith step p p.tail).sum : ℂ)) +
        (Complex.log ((x : ℂ) - GridCellCenter q) -
          Complex.log ((y : ℂ) - GridCellCenter q) -
          C * (step y x : ℂ)) :=
    congrArg₂ (fun u v : ℂ ↦ u + v) hchain hcloseStep
  have hsum : C * ((List.zipWith step p p.tail).sum + step y x) = 0 := by
    have hz : C * ((List.zipWith step p p.tail).sum : ℂ) +
        C * (step y x : ℂ) = 0 := by
      have hl : (F y - F x) + (F x - F y) = 0 := by ring
      have hr :
          (Complex.log ((y : ℂ) - GridCellCenter q) -
              Complex.log ((x : ℂ) - GridCellCenter q) -
              C * ((List.zipWith step p p.tail).sum : ℂ)) +
            (Complex.log ((x : ℂ) - GridCellCenter q) -
              Complex.log ((y : ℂ) - GridCellCenter q) -
              C * (step y x : ℂ)) =
            -(C * ((List.zipWith step p p.tail).sum : ℂ) +
              C * (step y x : ℂ)) := by ring
      rw [hl, hr] at htel
      exact neg_eq_zero.mp htel.symm
    rw [mul_add]
    exact hz
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hcast' : ((List.zipWith step p p.tail).sum : ℂ) +
      (step y x : ℂ) = 0 := by
    exact (mul_eq_zero.mp hsum).resolve_left hC
  have hcast : (((List.zipWith step p p.tail).sum + step y x : Int) : ℂ) = 0 := by
    simpa only [Int.cast_add, Int.cast_zero] using hcast'
  have hint : (List.zipWith step p p.tail).sum + step y x = 0 := by
    exact_mod_cast hcast
  rw [GridRayCrossingIndex]
  dsimp only
  rw [hlast, hhead]
  exact hint

end

end ApollonianSuperharmonic

end
