/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.SignSquareProduct
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Combination

-- [TABLET NODE: P4953T1TriangleSections]

/-!
# P4953T1TriangleSections

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TriangleSections

private noncomputable def u (A : ℂ) := A.im

private noncomputable def w (x : ℂ) := x.im

private noncomputable def v (B : ℂ) := B.im

private noncomputable def d (A : ℂ) (B : ℂ) : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im)
    / (B.im - A.im)

private noncomputable def e (A : ℂ) (x : ℂ) : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im)
    / (x.im - A.im)

private noncomputable def f (x : ℂ) (B : ℂ) : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im)
    / (B.im - x.im)

private noncomputable def δ (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) := σ * ((d A B) (w x) - x.re)

private theorem huw (A : ℂ) (x : ℂ) (hAx : A.im < x.im) : (u A) < (w x) := by
  classical
  let u := A.im
  let w := x.im
  change (u < w)
  exact hAx

private theorem hwv (x : ℂ) (B : ℂ) (hxB : x.im < B.im) : (w x) < (v B) := by
  classical
  let w := x.im
  let v := B.im
  change (w < v)
  exact hxB

private theorem huv (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) : (u A) < (v
    B) := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  have huw : u < w := huw A x hAx
  have hwv : w < v := hwv x B hxB
  change (u < v)
  exact lt_trans huw hwv

private theorem hδ (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im
    - A.im) / (B.im - A.im) - x.re)) : 0 < (δ σ A x B) := by
  classical
  let w := x.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let δ := σ * (d w - x.re)
  change (0 < δ)
  simpa [δ, d] using hgap

private theorem hden₀ (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) : B.im -
    A.im ≠ 0 := by
  classical
  let u := A.im
  let v := B.im
  have huv : u < v := huv A x B hAx hxB
  exact ne_of_gt (sub_pos.mpr huv)

private theorem hden₁ (A : ℂ) (x : ℂ) (hAx : A.im < x.im) : x.im - A.im ≠ 0 := by
  classical
  let u := A.im
  let w := x.im
  have huw : u < w := huw A x hAx
  exact ne_of_gt (sub_pos.mpr huw)

private abbrev hden₂ := ApollonianSuperharmonic.TriangleSections.hden₁

private noncomputable def pts (A : ℂ) (x : ℂ) (B : ℂ) : Fin 3 → ℂ := ![x, A, B]

private theorem hdet (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (A.re -
    x.re) * (B.im - x.im) -
      (B.re - x.re) * (A.im - x.im) ≠ 0 := by
  classical
  let w := x.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let δ := σ * (d w - x.re)
  have hδ : 0 < δ := hδ σ A x B hgap
  have hden₀ : B.im - A.im ≠ 0 := hden₀ A x B hAx hxB
  have hEq : (A.re - x.re) * (B.im - x.im) -
      (B.re - x.re) * (A.im - x.im) = (B.im - A.im) * (d w - x.re) := by
    dsimp [d]
    field_simp
    ring
  rw [hEq]
  intro hz
  have hz' : (B.im - A.im) * (d w - x.re) = 0 := hz
  have hdw : d w - x.re = 0 := (mul_eq_zero.mp hz').resolve_left hden₀
  have : δ = 0 := by
    simp [δ, hdw]
  exact (ne_of_gt hδ) this

private theorem hind (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) :
    AffineIndependent ℝ (pts A x B) := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hdet : (A.re - x.re) * (B.im - x.im) -
      (B.re - x.re) * (A.im - x.im) ≠ 0 := hdet σ A x B hAx hxB hgap
  change (AffineIndependent ℝ pts)
  apply (affineIndependent_iff_of_fintype ℝ pts).mpr
  intro c hc hsum i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hc] at hsum
  have hc' : c 0 + c 1 + c 2 = 0 := by
    simpa [Fin.sum_univ_succ, ← add_assoc] using hc
  have hr : c 0 * x.re + c 1 * A.re + c 2 * B.re = 0 := by
    simpa [Fin.sum_univ_succ, pts, ← add_assoc, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im] using congrArg Complex.re hsum
  have hi' : c 0 * x.im + c 1 * A.im + c 2 * B.im = 0 := by
    simpa [Fin.sum_univ_succ, pts, ← add_assoc, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im] using congrArg Complex.im hsum
  have hr' : c 1 * (A.re - x.re) + c 2 * (B.re - x.re) = 0 := by
    linear_combination hr - x.re * hc'
  have hi'' : c 1 * (A.im - x.im) + c 2 * (B.im - x.im) = 0 := by
    linear_combination hi' - x.im * hc'
  have hc1 : c 1 = 0 := by
    apply (mul_eq_zero.mp (show c 1 * ((A.re - x.re) * (B.im - x.im) -
        (B.re - x.re) * (A.im - x.im)) = 0 by
      linear_combination (B.im - x.im) * hr' - (B.re - x.re) * hi'')).resolve_right hdet
  have hc2 : c 2 = 0 := by
    apply (mul_eq_zero.mp (show c 2 * ((A.re - x.re) * (B.im - x.im) -
        (B.re - x.re) * (A.im - x.im)) = 0 by
      linear_combination (A.re - x.re) * hi'' - (A.im - x.im) * hr')).resolve_right hdet
  have hc0 : c 0 = 0 := by linarith [hc']
  fin_cases i <;> simp [hc0, hc1, hc2]

private theorem hspan (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : affineSpan ℝ
    (Set.range (pts A x B)) = ⊤ := by
  classical
  let : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  change (affineSpan ℝ (Set.range pts) = ⊤)
  apply hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  have hfin : Module.finrank ℝ ℂ = 2 := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI]
    simp
  simp [hfin]

private noncomputable def b (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im <
    B.im) (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) :
    AffineBasis (Fin 3) ℝ ℂ := ⟨(pts A x B), (hind σ A x B hAx hxB hgap), (hspan σ A x B hAx hxB
    hgap)⟩

private theorem hrange (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : Set.range (b
    σ A x B hAx hxB hgap) = ({x, A, B} : Set ℂ) := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  change (Set.range b = ({x, A, B} : Set ℂ))
  rw [show (b : Fin 3 → ℂ) = ![x, A, B] from rfl]
  ext z
  simp []
  tauto

private noncomputable def T (A : ℂ) (x : ℂ) (B : ℂ) : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)

private theorem hmem (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : ∀ z, z ∈ (T
    A x B) ↔ ∀ i, 0 ≤ (b σ A x B hAx hxB hgap).coord i z := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hrange : Set.range b = ({x, A, B} : Set ℂ) := hrange σ A x B hAx hxB hgap
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  change (∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z)
  intro z
  change z ∈ convexHull ℝ ({x, A, B} : Set ℂ) ↔ _
  rw [← hrange, b.convexHull_eq_nonneg_coord]
  simp

private theorem hcoord_sum (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im <
    B.im) (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ)
    : (b σ A x B hAx hxB hgap).coord 0 z + (b σ A x B hAx hxB hgap).coord 1 z + (b σ A x B hAx
    hxB hgap).coord 2 z = 1 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  change (b.coord 0 z + b.coord 1 z + b.coord 2 z = 1)
  simpa only [Fin.sum_univ_three] using b.sum_coord_apply_eq_one z

private theorem hcoord_point (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im <
    B.im) (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      ((b σ A x B hAx hxB hgap).coord 0 z) • x + ((b σ A x B hAx hxB hgap).coord 1 z) • A + ((b σ
          A x B hAx hxB hgap).coord 2 z) • B = z := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  change ((b.coord 0 z) • x + (b.coord 1 z) • A + (b.coord 2 z) • B = z)
  have hb0 : b 0 = x := rfl
  have hb1 : b 1 = A := rfl
  have hb2 : b 2 = B := rfl
  simpa only [Fin.sum_univ_three, hb0, hb1, hb2, add_assoc] using
    b.linear_combination_coord_eq_self z

private theorem hcoord_re (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      z.re = (b σ A x B hAx hxB hgap).coord 0 z * x.re + (b σ A x B hAx hxB hgap).coord 1 z *
          A.re + (b σ A x B hAx hxB hgap).coord 2 z * B.re := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hcoord_point (z : ℂ) :
      (b.coord 0 z) • x + (b.coord 1 z) • A + (b.coord 2 z) • B = z := hcoord_point σ A x B hAx
          hxB hgap z
  change (z.re = b.coord 0 z * x.re + b.coord 1 z * A.re + b.coord 2 z * B.re)
  have hz := congrArg Complex.re (hcoord_point z)
  simpa [Complex.smul_re, add_assoc] using hz.symm

private theorem hcoord_im (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      z.im = (b σ A x B hAx hxB hgap).coord 0 z * x.im + (b σ A x B hAx hxB hgap).coord 1 z *
          A.im + (b σ A x B hAx hxB hgap).coord 2 z * B.im := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hcoord_point (z : ℂ) :
      (b.coord 0 z) • x + (b.coord 1 z) • A + (b.coord 2 z) • B = z := hcoord_point σ A x B hAx
          hxB hgap z
  change (z.im = b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im)
  have hz := congrArg Complex.im (hcoord_point z)
  simpa [Complex.smul_im, add_assoc] using hz.symm

private theorem hg0 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) (hgap
    : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) : σ * ((d A
    B) z.im - z.re) = (δ σ A x B) * (b σ A x B hAx hxB hgap).coord 0 z := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let δ := σ * (d w - x.re)
  have hden₀ : B.im - A.im ≠ 0 := hden₀ A x B hAx hxB
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hcoord_sum (z : ℂ) : b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 := hcoord_sum σ A x B hAx
      hxB hgap z
  have hcoord_re (z : ℂ) :
      z.re = b.coord 0 z * x.re + b.coord 1 z * A.re + b.coord 2 z * B.re := hcoord_re σ A x B
          hAx hxB hgap z
  have hcoord_im (z : ℂ) :
      z.im = b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im := hcoord_im σ A x B
          hAx hxB hgap z
  change (σ * (d z.im - z.re) = δ * b.coord 0 z)
  rw [hcoord_re z, hcoord_im z]
  dsimp [δ, d]
  field_simp [u, w, v, hden₀]
  linear_combination hcoord_sum z *
    (-σ * (A.re * (B.im - A.im) - (B.re - A.re) * A.im))

private theorem hδnum (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) :
    (δ σ A x B) * ((v B) - (u A)) =
      σ * (A.re * ((v B) - (u A)) + (B.re - A.re) * ((w x) - (u A)) - ((v B) - (u A)) * x.re) := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let δ := σ * (d w - x.re)
  have hden₀ : B.im - A.im ≠ 0 := hden₀ A x B hAx hxB
  change (δ * (v - u) =
      σ * (A.re * (v - u) + (B.re - A.re) * (w - u) - (v - u) * x.re))
  dsimp [δ, d, u, w, v]
  field_simp [hden₀]

private theorem hmul1 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      ((w x) - (u A)) * (σ * (z.re - (e A x) z.im)) =
        (b σ A x B hAx hxB hgap).coord 2 z * ((δ σ A x B) * ((v B) - (u A))) := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let e : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
  let δ := σ * (d w - x.re)
  have hden₁ : x.im - A.im ≠ 0 := hden₁ A x hAx
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hcoord_sum (z : ℂ) : b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 := hcoord_sum σ A x B hAx
      hxB hgap z
  have hcoord_re (z : ℂ) :
      z.re = b.coord 0 z * x.re + b.coord 1 z * A.re + b.coord 2 z * B.re := hcoord_re σ A x B
          hAx hxB hgap z
  have hcoord_im (z : ℂ) :
      z.im = b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im := hcoord_im σ A x B
          hAx hxB hgap z
  have hδnum : δ * (v - u) =
      σ * (A.re * (v - u) + (B.re - A.re) * (w - u) - (v - u) * x.re) := hδnum σ A x B hAx hxB
  change ((w - u) * (σ * (z.re - e z.im)) =
        b.coord 2 z * (δ * (v - u)))
  rw [hcoord_re z, hcoord_im z, hδnum]
  dsimp [e, u, w, v]
  field_simp [hden₁]
  linear_combination hcoord_sum z *
    (σ * (A.re * (x.im - A.im) - (x.re - A.re) * A.im))

private theorem hg1 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) (hgap
    : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      σ * (z.re - (e A x) z.im) =
        (δ σ A x B) * (((v B) - (u A)) / ((w x) - (u A))) * (b σ A x B hAx hxB hgap).coord 2 z := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let e : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
  let δ := σ * (d w - x.re)
  have huw : u < w := huw A x hAx
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hmul1 (z : ℂ) :
      (w - u) * (σ * (z.re - e z.im)) =
        b.coord 2 z * (δ * (v - u)) := hmul1 σ A x B hAx hxB hgap z
  change (σ * (z.re - e z.im) =
        δ * ((v - u) / (w - u)) * b.coord 2 z)
  calc
    σ * (z.re - e z.im) =
        ((w - u) * (σ * (z.re - e z.im))) / (w - u) := by
          field_simp [ne_of_gt (sub_pos.mpr huw)]
    _ = (b.coord 2 z * (δ * (v - u))) / (w - u) := by rw [hmul1]
    _ = δ * ((v - u) / (w - u)) * b.coord 2 z := by ring

private theorem hmul2 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      ((v B) - (w x)) * (σ * (z.re - (f x B) z.im)) =
        (b σ A x B hAx hxB hgap).coord 1 z * ((δ σ A x B) * ((v B) - (u A))) := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let f : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
  let δ := σ * (d w - x.re)
  have hden₂ : B.im - x.im ≠ 0 := hden₂ x B hxB
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hcoord_sum (z : ℂ) : b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 := hcoord_sum σ A x B hAx
      hxB hgap z
  have hcoord_re (z : ℂ) :
      z.re = b.coord 0 z * x.re + b.coord 1 z * A.re + b.coord 2 z * B.re := hcoord_re σ A x B
          hAx hxB hgap z
  have hcoord_im (z : ℂ) :
      z.im = b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im := hcoord_im σ A x B
          hAx hxB hgap z
  have hδnum : δ * (v - u) =
      σ * (A.re * (v - u) + (B.re - A.re) * (w - u) - (v - u) * x.re) := hδnum σ A x B hAx hxB
  change ((v - w) * (σ * (z.re - f z.im)) =
        b.coord 1 z * (δ * (v - u)))
  rw [hcoord_re z, hcoord_im z, hδnum]
  dsimp [f, u, w, v]
  field_simp [hden₂]
  linear_combination hcoord_sum z *
    (σ * (x.re * (B.im - x.im) - (B.re - x.re) * x.im))

private theorem hg2 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) (hgap
    : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      σ * (z.re - (f x B) z.im) =
        (δ σ A x B) * (((v B) - (u A)) / ((v B) - (w x))) * (b σ A x B hAx hxB hgap).coord 1 z := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let f : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
  let δ := σ * (d w - x.re)
  have hwv : w < v := hwv x B hxB
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hmul2 (z : ℂ) :
      (v - w) * (σ * (z.re - f z.im)) =
        b.coord 1 z * (δ * (v - u)) := hmul2 σ A x B hAx hxB hgap z
  change (σ * (z.re - f z.im) =
        δ * ((v - u) / (v - w)) * b.coord 1 z)
  calc
    σ * (z.re - f z.im) =
        ((v - w) * (σ * (z.re - f z.im))) / (v - w) := by
          field_simp [ne_of_gt (sub_pos.mpr hwv)]
    _ = (b.coord 1 z * (δ * (v - u))) / (v - w) := by rw [hmul2]
    _ = δ * ((v - u) / (v - w)) * b.coord 1 z := by ring

private theorem hfac1 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : 0 < (δ σ A x
    B) * (((v B) - (u A)) / ((w x) - (u A))) := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let δ := σ * (d w - x.re)
  have huw : u < w := huw A x hAx
  have huv : u < v := huv A x B hAx hxB
  have hδ : 0 < δ := hδ σ A x B hgap
  change (0 < δ * ((v - u) / (w - u)))
  exact mul_pos hδ (div_pos (sub_pos.mpr huv) (sub_pos.mpr huw))

private theorem hfac2 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : 0 < (δ σ A x
    B) * (((v B) - (u A)) / ((v B) - (w x))) := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let δ := σ * (d w - x.re)
  have hwv : w < v := hwv x B hxB
  have huv : u < v := huv A x B hAx hxB
  have hδ : 0 < δ := hδ σ A x B hgap
  change (0 < δ * ((v - u) / (v - w)))
  exact mul_pos hδ (div_pos (sub_pos.mpr huv) (sub_pos.mpr hwv))

private theorem hperturb (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) (i :
    Fin 3) (hz : (b σ A x B hAx hxB hgap).coord i z = 0)
      (ε : ℝ) (hε : 0 < ε) : ∃ y : ℂ, dist y z < ε ∧ y ∉ (T A x B) := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hmem : ∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z := hmem σ A x B hAx hxB hgap
  change (∃ y : ℂ, dist y z < ε ∧ y ∉ T)
  let t := ε / (‖z - b i‖ + 1)
  have ht : 0 < t := div_pos hε (by positivity)
  let y := AffineMap.lineMap (b i) z (1 + t)
  change b.coord i z = 0 at hz
  have hcoord : b.coord i y = -t := by
    dsimp [y]
    rw [(b.coord i).apply_lineMap, b.coord_apply_eq i, hz]
    simp [AffineMap.lineMap_apply_ring]
  have hdist : dist y z < ε := by
    rw [dist_eq_norm]
    have hy : y - z = (t : ℝ) • (z - b i) := by
      change AffineMap.lineMap (b i) z (1 + t) - z = t • (z - b i)
      rw [AffineMap.lineMap_apply_module']
      module
    rw [hy]
    have hnorm : ‖(t : ℝ) • (z - b i)‖ = |t| * ‖z - b i‖ := by
      change ‖(t : ℂ) * (z - b i)‖ = _
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_of_pos ht]
    calc
      (ε / (‖z - b i‖ + 1)) * ‖z - b i‖ <
          (ε / (‖z - b i‖ + 1)) * (‖z - b i‖ + 1) := by
        apply mul_lt_mul_of_pos_left _ (div_pos hε (by positivity))
        linarith [norm_nonneg (z - b i)]
      _ = ε := by field_simp
  have hnotmem : y ∉ T := by
    intro hy
    have hcoords := (hmem y).mp hy
    have hneg := hcoords i
    rw [hcoord] at hneg
    linarith
  exact ⟨y, hdist, hnotmem⟩

private theorem hRecont (x : ℂ) : Continuous Complex.re := by
  classical
  let w := x.im
  rw [Metric.continuous_iff]
  intro z ε hε
  refine ⟨ε, hε, ?_⟩
  intro w hw
  have hb : dist (w.re) (z.re) ≤ dist w z := by
    rw [Real.dist_eq, ← Complex.sub_re, dist_eq_norm]
    exact Complex.abs_re_le_norm (w - z)
  exact lt_of_le_of_lt hb hw

private theorem hImcont (x : ℂ) : Continuous Complex.im := by
  classical
  let w := x.im
  rw [Metric.continuous_iff]
  intro z ε hε
  refine ⟨ε, hε, ?_⟩
  intro w hw
  have hb : dist (w.im) (z.im) ≤ dist w z := by
    rw [Real.dist_eq, ← Complex.sub_im, dist_eq_norm]
    exact Complex.abs_im_le_norm (w - z)
  exact lt_of_le_of_lt hb hw

private theorem hcont0 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) : Continuous (fun z : ℂ => σ * ((d A B)
    z.im - z.re)) := by
  classical
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  have hRecont : Continuous Complex.re := hRecont x
  have hImcont : Continuous Complex.im := hImcont x
  change (Continuous (fun z : ℂ => σ * (d z.im - z.re)))
  dsimp [d]
  have himSub : Continuous (fun z : ℂ => z.im - A.im) :=
    hImcont.sub continuous_const
  have hterm : Continuous (fun z : ℂ =>
      (B.re - A.re) * (z.im - A.im) / (B.im - A.im)) :=
    (continuous_const.mul himSub).div_const _
  exact continuous_const.mul ((continuous_const.add hterm).sub hRecont)

private theorem hcont1 (σ : ℝ) (A : ℂ) (x : ℂ) : Continuous (fun z : ℂ => σ * (z.re - (e A x)
    z.im)) := by
  classical
  let e : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
  have hRecont : Continuous Complex.re := hRecont x
  have hImcont : Continuous Complex.im := hImcont x
  change (Continuous (fun z : ℂ => σ * (z.re - e z.im)))
  dsimp [e]
  have himSub : Continuous (fun z : ℂ => z.im - A.im) :=
    hImcont.sub continuous_const
  have hterm : Continuous (fun z : ℂ =>
      (x.re - A.re) * (z.im - A.im) / (x.im - A.im)) :=
    (continuous_const.mul himSub).div_const _
  exact continuous_const.mul (hRecont.sub (continuous_const.add hterm))

private theorem hcont2 (σ : ℝ) (x : ℂ) (B : ℂ) : Continuous (fun z : ℂ => σ * (z.re - (f x B)
    z.im)) := by
  classical
  let f : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
  have hRecont : Continuous Complex.re := hRecont x
  have hImcont : Continuous Complex.im := hImcont x
  change (Continuous (fun z : ℂ => σ * (z.re - f z.im)))
  dsimp [f]
  have himSub : Continuous (fun z : ℂ => z.im - x.im) :=
    hImcont.sub continuous_const
  have hterm : Continuous (fun z : ℂ =>
      (B.re - x.re) * (z.im - x.im) / (B.im - x.im)) :=
    (continuous_const.mul himSub).div_const _
  exact continuous_const.mul (hRecont.sub (continuous_const.add hterm))

private theorem hT_eq (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (T A x B) =
    {z | 0 ≤ σ * ((d A B) z.im - z.re) ∧
      0 ≤ σ * (z.re - (e A x) z.im) ∧ 0 ≤ σ * (z.re - (f x B) z.im)} := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let e : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
  let f : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
  let δ := σ * (d w - x.re)
  have hδ : 0 < δ := hδ σ A x B hgap
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hmem : ∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z := hmem σ A x B hAx hxB hgap
  have hg0 (z : ℂ) : σ * (d z.im - z.re) = δ * b.coord 0 z := hg0 σ A x B hAx hxB hgap z
  have hg1 (z : ℂ) :
      σ * (z.re - e z.im) =
        δ * ((v - u) / (w - u)) * b.coord 2 z := hg1 σ A x B hAx hxB hgap z
  have hg2 (z : ℂ) :
      σ * (z.re - f z.im) =
        δ * ((v - u) / (v - w)) * b.coord 1 z := hg2 σ A x B hAx hxB hgap z
  have hfac1 : 0 < δ * ((v - u) / (w - u)) := hfac1 σ A x B hAx hxB hgap
  have hfac2 : 0 < δ * ((v - u) / (v - w)) := hfac2 σ A x B hAx hxB hgap
  change (T = {z | 0 ≤ σ * (d z.im - z.re) ∧
      0 ≤ σ * (z.re - e z.im) ∧ 0 ≤ σ * (z.re - f z.im)})
  ext z
  rw [hmem z]
  constructor
  · intro hc
    exact ⟨by simpa only [hg0] using mul_nonneg hδ.le (hc 0),
      by simpa only [hg1] using mul_nonneg hfac1.le (hc 2),
      by simpa only [hg2] using mul_nonneg hfac2.le (hc 1)⟩
  · rintro ⟨hz0, hz1, hz2⟩ i
    fin_cases i
    · change 0 ≤ b.coord 0 z
      exact (mul_nonneg_iff_of_pos_left hδ).mp (by rw [← hg0 z]; exact hz0)
    · change 0 ≤ b.coord 1 z
      exact (mul_nonneg_iff_of_pos_left hfac2).mp (by rw [← hg2 z]; exact hz2)
    · change 0 ≤ b.coord 2 z
      exact (mul_nonneg_iff_of_pos_left hfac1).mp (by rw [← hg1 z]; exact hz1)

private theorem hclosed (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : IsClosed (T
    A x B) := by
  classical
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let e : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
  let f : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hcont0 : Continuous (fun z : ℂ => σ * (d z.im - z.re)) := hcont0 σ A x B
  have hcont1 : Continuous (fun z : ℂ => σ * (z.re - e z.im)) := hcont1 σ A x
  have hcont2 : Continuous (fun z : ℂ => σ * (z.re - f z.im)) := hcont2 σ x B
  have hT_eq : T = {z | 0 ≤ σ * (d z.im - z.re) ∧
      0 ≤ σ * (z.re - e z.im) ∧ 0 ≤ σ * (z.re - f z.im)} := hT_eq σ A x B hAx hxB hgap
  change (IsClosed T)
  rw [hT_eq]
  exact (isClosed_Ici.preimage hcont0).inter
    ((isClosed_Ici.preimage hcont1).inter (isClosed_Ici.preimage hcont2))

private theorem hint (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : ∀ z, z ∈
    interior (T A x B) ↔ ∀ i, 0 < (b σ A x B hAx hxB hgap).coord i z := by
  classical
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let e : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
  let f : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
  let δ := σ * (d w - x.re)
  have hδ : 0 < δ := hδ σ A x B hgap
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hmem : ∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z := hmem σ A x B hAx hxB hgap
  have hg0 (z : ℂ) : σ * (d z.im - z.re) = δ * b.coord 0 z := hg0 σ A x B hAx hxB hgap z
  have hg1 (z : ℂ) :
      σ * (z.re - e z.im) =
        δ * ((v - u) / (w - u)) * b.coord 2 z := hg1 σ A x B hAx hxB hgap z
  have hg2 (z : ℂ) :
      σ * (z.re - f z.im) =
        δ * ((v - u) / (v - w)) * b.coord 1 z := hg2 σ A x B hAx hxB hgap z
  have hfac1 : 0 < δ * ((v - u) / (w - u)) := hfac1 σ A x B hAx hxB hgap
  have hfac2 : 0 < δ * ((v - u) / (v - w)) := hfac2 σ A x B hAx hxB hgap
  have hperturb (z : ℂ) (i : Fin 3) (hz : b.coord i z = 0)
      (ε : ℝ) (hε : 0 < ε) : ∃ y : ℂ, dist y z < ε ∧ y ∉ T := hperturb σ A x B hAx hxB hgap z i
          hz ε hε
  have hcont0 : Continuous (fun z : ℂ => σ * (d z.im - z.re)) := hcont0 σ A x B
  have hcont1 : Continuous (fun z : ℂ => σ * (z.re - e z.im)) := hcont1 σ A x
  have hcont2 : Continuous (fun z : ℂ => σ * (z.re - f z.im)) := hcont2 σ x B
  change (∀ z, z ∈ interior T ↔ ∀ i, 0 < b.coord i z)
  intro z
  constructor
  · intro hz i
    have hcoords := (hmem z).mp (interior_subset hz)
    fin_cases i
    · rcases lt_or_eq_of_le (hcoords 0) with hpos | heq
      · exact hpos
      · rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz) with ⟨r, hr, hsub⟩
        obtain ⟨y, hyd, hyT⟩ := hperturb z 0 heq.symm r hr
        exact False.elim (hyT (interior_subset (hsub (Metric.mem_ball.mpr hyd))))
    · rcases lt_or_eq_of_le (hcoords 1) with hpos | heq
      · exact hpos
      · rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz) with ⟨r, hr, hsub⟩
        obtain ⟨y, hyd, hyT⟩ := hperturb z 1 heq.symm r hr
        exact False.elim (hyT (interior_subset (hsub (Metric.mem_ball.mpr hyd))))
    · rcases lt_or_eq_of_le (hcoords 2) with hpos | heq
      · exact hpos
      · rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz) with ⟨r, hr, hsub⟩
        obtain ⟨y, hyd, hyT⟩ := hperturb z 2 heq.symm r hr
        exact False.elim (hyT (interior_subset (hsub (Metric.mem_ball.mpr hyd))))
  · intro hc
    let U : Set ℂ := {z | 0 < σ * (d z.im - z.re)} ∩
      {z | 0 < σ * (z.re - e z.im)} ∩ {z | 0 < σ * (z.re - f z.im)}
    have hUopen : IsOpen U := by
      change IsOpen ((fun z : ℂ => σ * (d z.im - z.re)) ⁻¹' Set.Ioi 0 ∩
        (fun z : ℂ => σ * (z.re - e z.im)) ⁻¹' Set.Ioi 0 ∩
        (fun z : ℂ => σ * (z.re - f z.im)) ⁻¹' Set.Ioi 0)
      have hIoi : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
      exact ((hIoi.preimage hcont0).inter (hIoi.preimage hcont1)).inter
        (hIoi.preimage hcont2)
    have hUsub : U ⊆ T := by
      intro y hy
      rcases hy with ⟨⟨hy0, hy1⟩, hy2⟩
      change 0 < σ * (d y.im - y.re) at hy0
      change 0 < σ * (y.re - e y.im) at hy1
      change 0 < σ * (y.re - f y.im) at hy2
      apply (hmem y).2
      intro i
      fin_cases i
      · change 0 ≤ b.coord 0 y
        exact le_of_lt ((mul_pos_iff_of_pos_left hδ).mp (by rw [← hg0 y]; exact hy0))
      · change 0 ≤ b.coord 1 y
        exact le_of_lt ((mul_pos_iff_of_pos_left hfac2).mp (by rw [← hg2 y]; exact hy2))
      · change 0 ≤ b.coord 2 y
        exact le_of_lt ((mul_pos_iff_of_pos_left hfac1).mp (by rw [← hg1 y]; exact hy1))
    have hzU : z ∈ U := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change 0 < σ * (d z.im - z.re)
        rw [hg0 z]
        exact mul_pos hδ (hc 0)
      · change 0 < σ * (z.re - e z.im)
        rw [hg1 z]
        exact mul_pos hfac1 (hc 2)
      · change 0 < σ * (z.re - f z.im)
        rw [hg2 z]
        exact mul_pos hfac2 (hc 1)
    exact interior_maximal hUsub hUopen hzU

private theorem hb0 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) (hgap
    : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B hAx hxB
    hgap) 0 = x := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  change (b 0 = x)
  exact rfl

private theorem hb1 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) (hgap
    : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B hAx hxB
    hgap) 1 = A := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  change (b 1 = A)
  exact rfl

private theorem hb2 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im) (hgap
    : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B hAx hxB
    hgap) 2 = B := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  change (b 2 = B)
  exact rfl

private theorem hcoord01 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 0 A = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb1 : b 1 = A := hb1 σ A x B hAx hxB hgap
  change (b.coord 0 A = 0)
  rw [← hb1]
  exact b.coord_apply_ne (by decide)

private theorem hcoord02 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 0 B = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb2 : b 2 = B := hb2 σ A x B hAx hxB hgap
  change (b.coord 0 B = 0)
  rw [← hb2]
  exact b.coord_apply_ne (by decide)

private theorem hcoord11 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 1 A = 1 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb1 : b 1 = A := hb1 σ A x B hAx hxB hgap
  change (b.coord 1 A = 1)
  rw [← hb1]
  exact b.coord_apply_eq 1

private theorem hcoord12 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 1 B = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb2 : b 2 = B := hb2 σ A x B hAx hxB hgap
  change (b.coord 1 B = 0)
  rw [← hb2]
  exact b.coord_apply_ne (by decide)

private theorem hcoord20 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 2 A = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb1 : b 1 = A := hb1 σ A x B hAx hxB hgap
  change (b.coord 2 A = 0)
  rw [← hb1]
  exact b.coord_apply_ne (by decide)

private theorem hcoord22 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 2 B = 1 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb2 : b 2 = B := hb2 σ A x B hAx hxB hgap
  change (b.coord 2 B = 1)
  rw [← hb2]
  exact b.coord_apply_eq 2

private theorem hcoord00 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 0 x = 1 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb0 : b 0 = x := hb0 σ A x B hAx hxB hgap
  change (b.coord 0 x = 1)
  rw [← hb0]
  exact b.coord_apply_eq 0

private theorem hcoord10 (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 1 x = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb0 : b 0 = x := hb0 σ A x B hAx hxB hgap
  change (b.coord 1 x = 0)
  rw [← hb0]
  exact b.coord_apply_ne (by decide)

private theorem hcoord20x (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) : (b σ A x B
    hAx hxB hgap).coord 2 x = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  have hb0 : b 0 = x := hb0 σ A x B hAx hxB hgap
  change (b.coord 2 x = 0)
  rw [← hb0]
  exact b.coord_apply_ne (by decide)

private theorem hfaceAB (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      z ∈ segment ℝ A B ↔ z ∈ (T A x B) ∧ (b σ A x B hAx hxB hgap).coord 0 z = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hmem : ∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z := hmem σ A x B hAx hxB hgap
  have hcoord_sum (z : ℂ) : b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 := hcoord_sum σ A x B hAx
      hxB hgap z
  have hb1 : b 1 = A := hb1 σ A x B hAx hxB hgap
  have hb2 : b 2 = B := hb2 σ A x B hAx hxB hgap
  have hcoord01 : b.coord 0 A = 0 := hcoord01 σ A x B hAx hxB hgap
  have hcoord02 : b.coord 0 B = 0 := hcoord02 σ A x B hAx hxB hgap
  have hcoord11 : b.coord 1 A = 1 := hcoord11 σ A x B hAx hxB hgap
  have hcoord12 : b.coord 1 B = 0 := hcoord12 σ A x B hAx hxB hgap
  have hcoord20 : b.coord 2 A = 0 := hcoord20 σ A x B hAx hxB hgap
  have hcoord22 : b.coord 2 B = 1 := hcoord22 σ A x B hAx hxB hgap
  change (z ∈ segment ℝ A B ↔ z ∈ T ∧ b.coord 0 z = 0)
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    constructor
    · apply (hmem _).2
      intro i
      fin_cases i
      · change 0 ≤ b.coord 0 (AffineMap.lineMap A B t)
        rw [(b.coord 0).apply_lineMap, hcoord01, hcoord02]
        simp []
      · change 0 ≤ b.coord 1 (AffineMap.lineMap A B t)
        rw [(b.coord 1).apply_lineMap, hcoord11, hcoord12]
        simp [AffineMap.lineMap_apply_ring]
        linarith [ht.2]
      · change 0 ≤ b.coord 2 (AffineMap.lineMap A B t)
        rw [(b.coord 2).apply_lineMap, hcoord20, hcoord22]
        simp only [AffineMap.lineMap_apply_ring, mul_zero, mul_one, zero_add]
        exact ht.1
    · change b.coord 0 (AffineMap.lineMap A B t) = 0
      rw [(b.coord 0).apply_lineMap, hcoord01, hcoord02]
      simp []
  · rintro ⟨hz, hz0⟩
    have hcn := (hmem z).mp hz
    have hsum := hcoord_sum z
    rw [← hb1, ← hb2, segment_eq_image_lineMap]
    refine ⟨b.coord 2 z, ⟨hcn 2, ?_⟩, ?_⟩
    · linarith [hsum, hz0, hcn 1]
    · apply b.ext_elem
      intro i
      fin_cases i
      · change b.coord 0 (AffineMap.lineMap A B (b.coord 2 z)) = b.coord 0 z
        rw [(b.coord 0).apply_lineMap, hcoord01, hcoord02]
        simp [hz0]
      · change b.coord 1 (AffineMap.lineMap A B (b.coord 2 z)) = b.coord 1 z
        rw [(b.coord 1).apply_lineMap, hcoord11, hcoord12]
        simp [AffineMap.lineMap_apply_ring]
        linarith [hsum, hz0]
      · change b.coord 2 (AffineMap.lineMap A B (b.coord 2 z)) = b.coord 2 z
        rw [(b.coord 2).apply_lineMap, hcoord20, hcoord22]
        simp [AffineMap.lineMap_apply_ring]

private theorem hfacexB (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      z ∈ segment ℝ x B ↔ z ∈ (T A x B) ∧ (b σ A x B hAx hxB hgap).coord 1 z = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hmem : ∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z := hmem σ A x B hAx hxB hgap
  have hcoord_sum (z : ℂ) : b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 := hcoord_sum σ A x B hAx
      hxB hgap z
  have hcoord02 : b.coord 0 B = 0 := hcoord02 σ A x B hAx hxB hgap
  have hcoord12 : b.coord 1 B = 0 := hcoord12 σ A x B hAx hxB hgap
  have hcoord22 : b.coord 2 B = 1 := hcoord22 σ A x B hAx hxB hgap
  have hcoord00 : b.coord 0 x = 1 := hcoord00 σ A x B hAx hxB hgap
  have hcoord10 : b.coord 1 x = 0 := hcoord10 σ A x B hAx hxB hgap
  have hcoord20x : b.coord 2 x = 0 := hcoord20x σ A x B hAx hxB hgap
  change (z ∈ segment ℝ x B ↔ z ∈ T ∧ b.coord 1 z = 0)
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    constructor
    · apply (hmem _).2
      intro i
      fin_cases i
      · change 0 ≤ b.coord 0 (AffineMap.lineMap x B t)
        rw [(b.coord 0).apply_lineMap, hcoord00, hcoord02]
        simp [AffineMap.lineMap_apply_ring]
        linarith [ht.2]
      · change 0 ≤ b.coord 1 (AffineMap.lineMap x B t)
        rw [(b.coord 1).apply_lineMap, hcoord10, hcoord12]
        simp []
      · change 0 ≤ b.coord 2 (AffineMap.lineMap x B t)
        rw [(b.coord 2).apply_lineMap, hcoord20x, hcoord22]
        simp only [AffineMap.lineMap_apply_ring, mul_zero, mul_one, zero_add]
        exact ht.1
    · change b.coord 1 (AffineMap.lineMap x B t) = 0
      rw [(b.coord 1).apply_lineMap, hcoord10, hcoord12]
      simp []
  · rintro ⟨hz, hz1⟩
    have hcn := (hmem z).mp hz
    have hsum := hcoord_sum z
    rw [segment_eq_image_lineMap]
    refine ⟨b.coord 2 z, ⟨hcn 2, ?_⟩, ?_⟩
    · linarith [hsum, hz1, hcn 0]
    · apply b.ext_elem
      intro i
      fin_cases i
      · change b.coord 0 (AffineMap.lineMap x B (b.coord 2 z)) = b.coord 0 z
        rw [(b.coord 0).apply_lineMap, hcoord00, hcoord02]
        simp [AffineMap.lineMap_apply_ring]
        linarith [hsum, hz1]
      · change b.coord 1 (AffineMap.lineMap x B (b.coord 2 z)) = b.coord 1 z
        rw [(b.coord 1).apply_lineMap, hcoord10, hcoord12]
        simp [hz1]
      · change b.coord 2 (AffineMap.lineMap x B (b.coord 2 z)) = b.coord 2 z
        rw [(b.coord 2).apply_lineMap, hcoord20x, hcoord22]
        simp [AffineMap.lineMap_apply_ring]

private theorem hfacexA (σ : ℝ) (A : ℂ) (x : ℂ) (B : ℂ) (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) * (x.im - A.im) / (B.im - A.im) - x.re)) (z : ℂ) :
      z ∈ segment ℝ x A ↔ z ∈ (T A x B) ∧ (b σ A x B hAx hxB hgap).coord 2 z = 0 := by
  classical
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hmem : ∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z := hmem σ A x B hAx hxB hgap
  have hcoord_sum (z : ℂ) : b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 := hcoord_sum σ A x B hAx
      hxB hgap z
  have hcoord01 : b.coord 0 A = 0 := hcoord01 σ A x B hAx hxB hgap
  have hcoord11 : b.coord 1 A = 1 := hcoord11 σ A x B hAx hxB hgap
  have hcoord20 : b.coord 2 A = 0 := hcoord20 σ A x B hAx hxB hgap
  have hcoord00 : b.coord 0 x = 1 := hcoord00 σ A x B hAx hxB hgap
  have hcoord10 : b.coord 1 x = 0 := hcoord10 σ A x B hAx hxB hgap
  have hcoord20x : b.coord 2 x = 0 := hcoord20x σ A x B hAx hxB hgap
  change (z ∈ segment ℝ x A ↔ z ∈ T ∧ b.coord 2 z = 0)
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    constructor
    · apply (hmem _).2
      intro i
      fin_cases i
      · change 0 ≤ b.coord 0 (AffineMap.lineMap x A t)
        rw [(b.coord 0).apply_lineMap, hcoord00, hcoord01]
        simp [AffineMap.lineMap_apply_ring]
        linarith [ht.2]
      · change 0 ≤ b.coord 1 (AffineMap.lineMap x A t)
        rw [(b.coord 1).apply_lineMap, hcoord10, hcoord11]
        simp only [AffineMap.lineMap_apply_ring, mul_zero, mul_one, zero_add]
        exact ht.1
      · change 0 ≤ b.coord 2 (AffineMap.lineMap x A t)
        rw [(b.coord 2).apply_lineMap, hcoord20x, hcoord20]
        simp []
    · change b.coord 2 (AffineMap.lineMap x A t) = 0
      rw [(b.coord 2).apply_lineMap, hcoord20x, hcoord20]
      simp []
  · rintro ⟨hz, hz2⟩
    have hcn := (hmem z).mp hz
    have hsum := hcoord_sum z
    rw [segment_eq_image_lineMap]
    refine ⟨b.coord 1 z, ⟨hcn 1, ?_⟩, ?_⟩
    · linarith [hsum, hz2, hcn 0]
    · apply b.ext_elem
      intro i
      fin_cases i
      · change b.coord 0 (AffineMap.lineMap x A (b.coord 1 z)) = b.coord 0 z
        rw [(b.coord 0).apply_lineMap, hcoord00, hcoord01]
        simp [AffineMap.lineMap_apply_ring]
        linarith [hsum, hz2]
      · change b.coord 1 (AffineMap.lineMap x A (b.coord 1 z)) = b.coord 1 z
        rw [(b.coord 1).apply_lineMap, hcoord10, hcoord11]
        simp [AffineMap.lineMap_apply_ring]
      · change b.coord 2 (AffineMap.lineMap x A (b.coord 1 z)) = b.coord 2 z
        rw [(b.coord 2).apply_lineMap, hcoord20x, hcoord20]
        simp [hz2]

end TriangleSections

theorem P4953T1TriangleSections (σ : ℝ) (A x B : ℂ)
    (hAx : A.im < x.im) (hxB : x.im < B.im)
    (hgap : 0 < σ * (A.re + (B.re - A.re) *
      (x.im - A.im) / (B.im - A.im) - x.re)) :
    let d (y : ℝ) := A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
    let e (y : ℝ) := A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
    let f (y : ℝ) := x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
    let T := convexHull ℝ ({x, A, B} : Set ℂ)
    (∀ z, z ∈ interior T ↔ 0 < σ * (d z.im - z.re) ∧
      0 < σ * (z.re - e z.im) ∧ 0 < σ * (z.re - f z.im)) ∧
    (∀ z, A.im ≤ z.im → z.im ≤ x.im →
      (z ∈ T ↔ 0 ≤ σ * (z.re - e z.im) ∧ 0 ≤ σ * (d z.im - z.re))) ∧
    (∀ z, x.im ≤ z.im → z.im ≤ B.im →
      (z ∈ T ↔ 0 ≤ σ * (z.re - f z.im) ∧ 0 ≤ σ * (d z.im - z.re))) ∧
    frontier T = segment ℝ x A ∪ segment ℝ x B ∪ segment ℝ A B := by
-- BODY
  classical
  dsimp only
  let u := A.im
  let w := x.im
  let v := B.im
  let d : ℝ → ℝ := fun y => A.re + (B.re - A.re) * (y - A.im) / (B.im - A.im)
  let e : ℝ → ℝ := fun y => A.re + (x.re - A.re) * (y - A.im) / (x.im - A.im)
  let f : ℝ → ℝ := fun y => x.re + (B.re - x.re) * (y - x.im) / (B.im - x.im)
  let δ := σ * (d w - x.re)
  have huw : u < w := TriangleSections.huw A x hAx
  have hwv : w < v := TriangleSections.hwv x B hxB
  have hδ : 0 < δ := TriangleSections.hδ σ A x B hgap
  let pts : Fin 3 → ℂ := ![x, A, B]
  have hind : AffineIndependent ℝ pts := TriangleSections.hind σ A x B hAx hxB hgap
  have hspan : affineSpan ℝ (Set.range pts) = ⊤ := TriangleSections.hspan σ A x B hAx hxB hgap
  let b : AffineBasis (Fin 3) ℝ ℂ := ⟨pts, hind, hspan⟩
  let T : Set ℂ := convexHull ℝ ({x, A, B} : Set ℂ)
  have hmem : ∀ z, z ∈ T ↔ ∀ i, 0 ≤ b.coord i z := TriangleSections.hmem σ A x B hAx hxB hgap
  have hcoord_sum (z : ℂ) : b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 :=
      TriangleSections.hcoord_sum σ A x B hAx hxB hgap z
  have hcoord_im (z : ℂ) :
      z.im = b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im :=
          TriangleSections.hcoord_im σ A x B hAx hxB hgap z
  have hg0 (z : ℂ) : σ * (d z.im - z.re) = δ * b.coord 0 z := TriangleSections.hg0 σ A x B hAx
      hxB hgap z
  have hg1 (z : ℂ) :
      σ * (z.re - e z.im) =
        δ * ((v - u) / (w - u)) * b.coord 2 z := TriangleSections.hg1 σ A x B hAx hxB hgap z
  have hg2 (z : ℂ) :
      σ * (z.re - f z.im) =
        δ * ((v - u) / (v - w)) * b.coord 1 z := TriangleSections.hg2 σ A x B hAx hxB hgap z
  have hfac1 : 0 < δ * ((v - u) / (w - u)) := TriangleSections.hfac1 σ A x B hAx hxB hgap
  have hfac2 : 0 < δ * ((v - u) / (v - w)) := TriangleSections.hfac2 σ A x B hAx hxB hgap
  have hclosed : IsClosed T := TriangleSections.hclosed σ A x B hAx hxB hgap
  have hint : ∀ z, z ∈ interior T ↔ ∀ i, 0 < b.coord i z := TriangleSections.hint σ A x B hAx hxB
      hgap
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    rw [hint z]
    constructor
    · intro hc
      refine ⟨?_, ?_, ?_⟩
      · rw [hg0 z]
        exact mul_pos hδ (hc 0)
      · rw [hg1 z]
        exact mul_pos hfac1 (hc 2)
      · rw [hg2 z]
        exact mul_pos hfac2 (hc 1)
    · rintro ⟨hz0, hz1, hz2⟩
      intro i
      fin_cases i
      · have hh := hz0
        change 0 < σ * (d z.im - z.re) at hh
        have hp : 0 < δ * b.coord 0 z := by rw [← hg0 z]; exact hh
        exact (mul_pos_iff_of_pos_left hδ).mp hp
      · have hh := hz2
        change 0 < σ * (z.re - f z.im) at hh
        have hp : 0 < δ * ((v - u) / (v - w)) * b.coord 1 z := by
          rw [← hg2 z]
          exact hh
        exact (mul_pos_iff_of_pos_left hfac2).mp (by simpa [hfac2] using hp)
      · have hh := hz1
        change 0 < σ * (z.re - e z.im) at hh
        have hp : 0 < δ * ((v - u) / (w - u)) * b.coord 2 z := by
          rw [← hg1 z]
          exact hh
        exact (mul_pos_iff_of_pos_left hfac1).mp (by simpa [hfac1] using hp)
  · intro z hlow hhigh
    rw [hmem z]
    constructor
    · intro hc
      refine ⟨?_, ?_⟩
      · change 0 ≤ σ * (z.re - e z.im)
        rw [hg1 z]
        exact mul_nonneg hfac1.le (hc 2)
      · change 0 ≤ σ * (d z.im - z.re)
        rw [hg0 z]
        exact mul_nonneg hδ.le (hc 0)
    · rintro ⟨hz1, hz0⟩
      have hc0 : 0 ≤ b.coord 0 z :=
        (mul_nonneg_iff_of_pos_left hδ).mp (by
          have hh := hz0
          change 0 ≤ σ * (d z.im - z.re) at hh
          have hp : 0 ≤ δ * b.coord 0 z := by rw [← hg0 z]; exact hh
          exact hp)
      have hc2 : 0 ≤ b.coord 2 z :=
        (mul_nonneg_iff_of_pos_left hfac1).mp (by
          have hh := hz1
          change 0 ≤ σ * (z.re - e z.im) at hh
          have hp : 0 ≤ δ * ((v - u) / (w - u)) * b.coord 2 z := by
            rw [← hg1 z]
            exact hh
          simpa [hfac1] using hp)
      have hheight : x.im - z.im =
          b.coord 1 z * (x.im - A.im) - b.coord 2 z * (B.im - x.im) := by
        rw [hcoord_im z]
        calc
          x.im - (b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im) =
              x.im * (b.coord 0 z + b.coord 1 z + b.coord 2 z) -
                (b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im) := by
                  rw [hcoord_sum z]
                  ring
          _ = b.coord 1 z * (x.im - A.im) -
              b.coord 2 z * (B.im - x.im) := by ring
      have hprod : 0 ≤ b.coord 1 z * (w - u) := by
        nlinarith [hheight, hhigh, hc2, sub_nonneg.mpr (le_of_lt hwv)]
      have hc1 : 0 ≤ b.coord 1 z :=
        (mul_nonneg_iff_of_pos_right (sub_pos.mpr huw)).mp hprod
      intro i
      fin_cases i
      · exact hc0
      · exact hc1
      · exact hc2
  · intro z hlow hhigh
    rw [hmem z]
    constructor
    · intro hc
      refine ⟨?_, ?_⟩
      · change 0 ≤ σ * (z.re - f z.im)
        rw [hg2 z]
        exact mul_nonneg hfac2.le (hc 1)
      · change 0 ≤ σ * (d z.im - z.re)
        rw [hg0 z]
        exact mul_nonneg hδ.le (hc 0)
    · rintro ⟨hz2, hz0⟩
      have hc0 : 0 ≤ b.coord 0 z :=
        (mul_nonneg_iff_of_pos_left hδ).mp (by
          have hh := hz0
          change 0 ≤ σ * (d z.im - z.re) at hh
          have hp : 0 ≤ δ * b.coord 0 z := by rw [← hg0 z]; exact hh
          exact hp)
      have hc1 : 0 ≤ b.coord 1 z :=
        (mul_nonneg_iff_of_pos_left hfac2).mp (by
          have hh := hz2
          change 0 ≤ σ * (z.re - f z.im) at hh
          have hp : 0 ≤ δ * ((v - u) / (v - w)) * b.coord 1 z := by
            rw [← hg2 z]
            exact hh
          simpa [hfac2] using hp)
      have hheight : z.im - x.im =
          b.coord 2 z * (B.im - x.im) - b.coord 1 z * (x.im - A.im) := by
        rw [hcoord_im z]
        calc
          (b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im) -
              x.im =
              (b.coord 0 z * x.im + b.coord 1 z * A.im + b.coord 2 z * B.im) -
              x.im * (b.coord 0 z + b.coord 1 z + b.coord 2 z) := by
                rw [hcoord_sum z]
                ring
          _ = b.coord 2 z * (B.im - x.im) -
              b.coord 1 z * (x.im - A.im) := by ring
      have hprod : 0 ≤ b.coord 2 z * (v - w) := by
        nlinarith [hheight, hlow, hc1, sub_nonneg.mpr (le_of_lt huw)]
      have hc2 : 0 ≤ b.coord 2 z :=
        (mul_nonneg_iff_of_pos_right (sub_pos.mpr hwv)).mp hprod
      intro i
      fin_cases i
      · exact hc0
      · exact hc1
      · exact hc2
  have hfaceAB (z : ℂ) :
      z ∈ segment ℝ A B ↔ z ∈ T ∧ b.coord 0 z = 0 := TriangleSections.hfaceAB σ A x B hAx hxB hgap z
  have hfacexB (z : ℂ) :
      z ∈ segment ℝ x B ↔ z ∈ T ∧ b.coord 1 z = 0 := TriangleSections.hfacexB σ A x B hAx hxB hgap z
  have hfacexA (z : ℂ) :
      z ∈ segment ℝ x A ↔ z ∈ T ∧ b.coord 2 z = 0 := TriangleSections.hfacexA σ A x B hAx hxB hgap z
  rw [hclosed.frontier_eq]
  ext z
  constructor
  · rintro ⟨hzT, hzNoInt⟩
    have hcoords := (hmem z).mp hzT
    have hzero : ∃ i, b.coord i z = 0 := by
      by_contra hn
      have hstrict : ∀ i, 0 < b.coord i z := by
        intro i
        apply lt_of_le_of_ne (hcoords i)
        intro hEq
        exact hn ⟨i, hEq.symm⟩
      exact hzNoInt ((hint z).mpr hstrict)
    rcases hzero with ⟨i, hi⟩
    fin_cases i
    · exact Or.inr ((hfaceAB z).2 ⟨hzT, hi⟩)
    · exact Or.inl (Or.inr ((hfacexB z).2 ⟨hzT, hi⟩))
    · exact Or.inl (Or.inl ((hfacexA z).2 ⟨hzT, hi⟩))
  · intro hz
    rcases hz with hzRest | hzAB
    · rcases hzRest with hzA | hzB
      · have h := (hfacexA z).1 hzA
        refine ⟨h.1, ?_⟩
        intro hzInt
        exact (ne_of_gt ((hint z).mp hzInt 2)) h.2
      · have h := (hfacexB z).1 hzB
        refine ⟨h.1, ?_⟩
        intro hzInt
        exact (ne_of_gt ((hint z).mp hzInt 1)) h.2
    · have h := (hfaceAB z).1 hzAB
      refine ⟨h.1, ?_⟩
      intro hzInt
      exact (ne_of_gt ((hint z).mp hzInt 0)) h.2

end ApollonianSuperharmonic

end
