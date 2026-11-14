/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.GaussianLatticeFiniteness
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.IntegerSuperharmonicRepresentative
public import LeanPool.ApollonianSuperharmonic.P5691T1PosDefQuadraticLowerBound

-- [TABLET NODE: PositiveDefiniteRepresentativeGap]

/-!
# PositiveDefiniteRepresentativeGap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PositiveDefiniteRepresentativeGap
    (A : Matrix (Fin 2) (Fin 2) Real) (C : BandCircle)
    (g h : IntegerLatticeFunction)
    (hg : IntegerSuperharmonicRepresentative A g)
    (hh : IntegerSuperharmonicRepresentative (CircleMatrix C) h)
    (hgap : (A - CircleMatrix C).PosDef) :
    (forall M : Real, exists R : Real, forall x : GaussianInt,
      R <= (x.re : Real) ^ 2 + (x.im : Real) ^ 2 ->
        M <= (g x : Real) - (h x : Real)) /\
    (exists c : Int, forall x : GaussianInt, h x <= g x + c) := by
-- BODY
  rcases hg with ⟨hAs, hQg, hglap⟩
  rcases hh with ⟨hCs, hQh, hhlap⟩
  let D := A - CircleMatrix C
  obtain ⟨k, hk, hlower⟩ := P5691T1PosDefQuadraticLowerBound D hgap
  have hqdiff (x : GaussianInt) :
      LatticeQuadraticForm A x - LatticeQuadraticForm (CircleMatrix C) x =
        LatticeQuadraticForm D x := by
    simp [D, LatticeQuadraticForm, Matrix.sub_mulVec]
    ring
  have hdiv : ∀ M : ℝ, ∃ R : ℝ, ∀ x : GaussianInt,
      R ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 →
        M ≤ (g x : ℝ) - (h x : ℝ) := by
    intro M
    have he : 0 < k / 4 := by linarith
    obtain ⟨Rg, hRg⟩ := hQg (k / 4) he
    obtain ⟨Rh, hRh⟩ := hQh (k / 4) he
    refine ⟨max Rg (max Rh (2 * M / k)), ?_⟩
    intro x hx
    have hxg := hRg x (le_trans (le_max_left _ _) hx)
    have hxh := hRh x (le_trans
      (le_trans (le_max_left Rh (2 * M / k))
        (le_max_right Rg (max Rh (2 * M / k)))) hx)
    have hq := hlower x
    have hmain : k / 2 * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) ≤
        (g x : ℝ) - (h x : ℝ) := by
      have hgl : -(k / 4 * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2)) ≤
          (g x : ℝ) - LatticeQuadraticForm A x :=
        neg_le_of_abs_le hxg
      have hhu : (h x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x ≤
          k / 4 * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) :=
        le_of_abs_le hxh
      rw [show (g x : ℝ) - (h x : ℝ) =
          (LatticeQuadraticForm A x - LatticeQuadraticForm (CircleMatrix C) x) +
            ((g x : ℝ) - LatticeQuadraticForm A x) -
            ((h x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x) by ring]
      rw [hqdiff]
      linarith
    have hxR : 2 * M / k ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 :=
      le_trans (le_trans (le_max_right Rh (2 * M / k))
        (le_max_right Rg (max Rh (2 * M / k)))) hx
    have hxR' : 2 * M ≤ k * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) :=
      by simpa [mul_comm] using (div_le_iff₀ hk).mp hxR
    nlinarith [hmain, hxR']
  refine ⟨hdiv, ?_⟩
  obtain ⟨R0, hR0⟩ := hdiv 0
  let S : Set GaussianInt := {x | (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 < R0}
  have hS : S.Finite := gaussianLatticeDisk_finite R0
  let V : Set ℤ := insert 0 ((fun x : GaussianInt => h x - g x) '' S)
  have hVfin : V.Finite := by
    dsimp [V]
    exact Set.Finite.insert 0 (hS.image _)
  have hVne : V.Nonempty := by
    exact ⟨0, Set.mem_insert 0 _⟩
  obtain ⟨c, hcV, hc⟩ := Set.exists_max_image V id hVfin hVne
  refine ⟨c, ?_⟩
  intro x
  by_cases hxin : x ∈ S
  · have hm : h x - g x ∈ V := by
      apply Set.mem_insert_iff.mpr
      right
      exact ⟨x, hxin, rfl⟩
    have hle : h x - g x ≤ c := by
      simpa using hc (h x - g x) hm
    linarith
  · have hlarge : R0 ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 := by
      dsimp [S] at hxin
      exact le_of_not_gt hxin
    have hnon : (0 : ℝ) ≤ (g x : ℝ) - (h x : ℝ) := hR0 x hlarge
    have hnon' : h x ≤ g x := by
      exact_mod_cast (show (h x : ℝ) ≤ (g x : ℝ) by linarith)
    have hc0 : (0 : ℤ) ≤ c := by
      have := hc 0 (Set.mem_insert 0 _)
      simpa using this
    linarith

end ApollonianSuperharmonic

end
