/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeQuadraticForm
public import Mathlib.LinearAlgebra.Matrix.PosDef

-- [TABLET NODE: P5691T1PosDefQuadraticLowerBound]

/-!
# P5691T1PosDefQuadraticLowerBound

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5691T1PosDefQuadraticLowerBound
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hgap : D.PosDef) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : GaussianInt,
      k * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) ≤ LatticeQuadraticForm D x := by
-- BODY
  let a : ℝ := D 0 0
  let b : ℝ := D 0 1
  let d : ℝ := D 1 1
  have hDs : D.IsHermitian := hgap.isHermitian
  have hDsym : D.IsSymm := by
    exact Matrix.isHermitian_iff_isSymm.mp hDs
  have ha : 0 < a := by
    have hp := hgap.dotProduct_mulVec_pos (x := ![(1 : ℝ), 0]) (by
      intro hz
      have := congr_fun hz 0
      simp at this)
    simpa [a, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hp
  have hpos (u v : ℝ) (hne : ![u, v] ≠ 0) :
      0 < a * u ^ 2 + 2 * b * u * v + d * v ^ 2 := by
    have hp := hgap.dotProduct_mulVec_pos (x := ![u, v]) hne
    have hs := hDsym.apply 0 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs] at hp
    dsimp [a, b, d]
    nlinarith [hp]
  have hdet : 0 < a * d - b ^ 2 := by
    have hp := hpos (-b) a (by
      intro hz
      have hz0 := congr_fun hz 0
      have hz1 := congr_fun hz 1
      simp [ha.ne'] at hz0 hz1
      )
    nlinarith
  have had : 0 < a + d := by
    have hd : 0 < d := by
      have hp := hgap.dotProduct_mulVec_pos (x := ![(0 : ℝ), 1]) (by
        intro hz
        have := congr_fun hz 1
        simp at this)
      simpa [d, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hp
    linarith
  have hquad (x : GaussianInt) :
      LatticeQuadraticForm D x =
        (1 / 2 : ℝ) * (a * (x.re : ℝ)^2 +
          2 * b * (x.re : ℝ) * (x.im : ℝ) + d * (x.im : ℝ)^2) := by
    have hs := hDsym.apply 0 1
    simp [LatticeQuadraticForm, a, b, d, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, -GaussianInt.intCast_re, -GaussianInt.intCast_im,
      hs]
    ring_nf
  have hlower (x : GaussianInt) :
      LatticeQuadraticForm D x ≥
        (a * d - b ^ 2) / (2 * (a + d)) *
          ((x.re : ℝ)^2 + (x.im : ℝ)^2) := by
    rw [hquad]
    have hs1 : 0 ≤ (a * (x.re : ℝ) + b * (x.im : ℝ)) ^ 2 := sq_nonneg _
    have hs2 : 0 ≤ (b * (x.re : ℝ) + d * (x.im : ℝ)) ^ 2 := sq_nonneg _
    field_simp
    nlinarith
  let k : ℝ := (a * d - b ^ 2) / (2 * (a + d))
  have hk : 0 < k := by
    dsimp [k]
    exact div_pos hdet (mul_pos (by norm_num) had)
  exact ⟨k, hk, hlower⟩

end ApollonianSuperharmonic

end
