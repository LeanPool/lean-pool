/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TilingLatticeBasis
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Convex.Topology

-- [TABLET NODE: P4812T1LatticeCoordinates]

/-!
# P4812T1LatticeCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4812T1LatticeCoordinates (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hC : q 0 = C.1.1) :
    ∃ k : (Int × Int) ≃+ TilingLattice C,
      (∀ x, (k x : GaussianInt) =
        (x.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (x.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) ∧
      ∃ H : (Real × Real) ≃ₜ (Real × Real), ∀ p,
        H p = (p.1 + p.2 / 2) • GaussianRealPoint (BandVectors.1 (q 1) (q 0)) +
          p.2 • GaussianRealPoint (BandVectors.1 (q 2) (q 0)) := by
-- BODY
  classical
  let a := BandVectors.1 (q 1) (q 0)
  let b := BandVectors.1 (q 2) (q 0)
  obtain ⟨ha, hb, hcoords, _⟩ := TilingLatticeBasis C q hq hC
  let f : (Int × Int) →+ TilingLattice C := {
    toFun := fun x => ⟨(x.1 : GaussianInt) * a + (x.2 : GaussianInt) * b, by
      simpa [Int.cast_smul_eq_zsmul] using
        (TilingLattice C).add_mem ((TilingLattice C).zsmul_mem ha x.1)
          ((TilingLattice C).zsmul_mem hb x.2)⟩
    map_zero' := by apply Subtype.ext; simp
    map_add' := by
      intro x y
      apply Subtype.ext
      change ((x.1 + y.1 : Int) : GaussianInt) * a +
        ((x.2 + y.2 : Int) : GaussianInt) * b =
        ((x.1 : GaussianInt) * a + (x.2 : GaussianInt) * b) +
          ((y.1 : GaussianInt) * a + (y.2 : GaussianInt) * b)
      simp only [Int.cast_add]
      ring }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨z, hz, huniq⟩ := hcoords (f x)
      have hx : x = z := huniq x rfl
      have hy : y = z := huniq y (congrArg Subtype.val hxy.symm)
      exact hx.trans hy.symm
    · intro w
      obtain ⟨x, hx, _⟩ := hcoords w
      exact ⟨x, Subtype.ext hx⟩
  let k : (Int × Int) ≃+ TilingLattice C := AddEquiv.ofBijective f hf
  have hinj : Function.Injective (fun x : Int × Int =>
      (x.1 : GaussianInt) * a + (x.2 : GaussianInt) * b) := by
    intro x y h
    exact hf.1 (Subtype.ext h)
  have hd : a.re * b.im - a.im * b.re ≠ 0 := by
    intro hd
    have h1 : (b.re, -a.re) = ((0, 0) : Int × Int) := by
      apply hinj
      apply Zsqrtd.ext <;>
        simp <;> nlinarith
    have h2 : (b.im, -a.im) = ((0, 0) : Int × Int) := by
      apply hinj
      apply Zsqrtd.ext <;>
        simp <;> nlinarith
    have ha0 : a = 0 := by
      apply Zsqrtd.ext
      · have := congrArg Prod.snd h1; simpa using neg_eq_zero.mp this
      · have := congrArg Prod.snd h2; simpa using neg_eq_zero.mp this
    have he : ((1, 0) : Int × Int) = (0, 0) :=
      hinj (by simp [ha0])
    norm_num at he
  let d : Real := (a.re : Real) * b.im - (a.im : Real) * b.re
  have hdR : d ≠ 0 := by dsimp [d]; exact_mod_cast hd
  let H : (Real × Real) ≃ₜ (Real × Real) := {
    toFun := fun p =>
      ((p.1 + p.2 / 2) * a.re + p.2 * b.re,
        (p.1 + p.2 / 2) * a.im + p.2 * b.im)
    invFun := fun p =>
      (((b.im : Real) * p.1 - b.re * p.2) / d -
          (((a.re : Real) * p.2 - a.im * p.1) / d) / 2,
        ((a.re : Real) * p.2 - a.im * p.1) / d)
    left_inv := by
      intro p
      apply Prod.ext <;> dsimp <;> field_simp <;> ring
    right_inv := by
      intro p
      apply Prod.ext <;> dsimp <;> field_simp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  refine ⟨k, fun _ => rfl, H, ?_⟩
  intro p
  rfl

end ApollonianSuperharmonic

end
