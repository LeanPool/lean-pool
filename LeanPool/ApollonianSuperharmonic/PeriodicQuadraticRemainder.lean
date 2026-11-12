/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeQuadraticForm
public import LeanPool.ApollonianSuperharmonic.TilingLatticeBasis
public import LeanPool.ApollonianSuperharmonic.TilingLatticeCocycleExtension

-- [TABLET NODE: PeriodicQuadraticRemainder]

/-!
# PeriodicQuadraticRemainder

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PeriodicQuadraticRemainder (C : BandCircle)
    (g : IntegerLatticeFunction)
    (hcocycle : ∀ v, v ∈ TilingLattice C → ∃ a : GaussianInt,
      Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
        ![(a.re : ℝ), (a.im : ℝ)] ∧
      ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v) :
    ∃ b : ℝ × ℝ, ∀ v, v ∈ TilingLattice C → ∀ x,
      (g (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
          (b.1 * (x + v).re + b.2 * (x + v).im) =
        (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
          (b.1 * x.re + b.2 * x.im) := by
-- BODY
  classical
  let Q : GaussianInt → ℝ := fun z => LatticeQuadraticForm (CircleMatrix C) z
  let d : GaussianInt → ℝ := fun z => (g z : ℝ) - Q z
  have shift : ∀ x v : GaussianInt,
      Q (x + v) = Q x + x.re * (Matrix.mulVec (CircleMatrix C)
        ![(v.re : ℝ), (v.im : ℝ)] 0) +
        x.im * (Matrix.mulVec (CircleMatrix C)
        ![(v.re : ℝ), (v.im : ℝ)] 1) + Q v := by
    intro x v
    dsimp [Q, LatticeQuadraticForm]
    simp [CircleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.vecCons, Matrix.vecEmpty, Fin.cons, Fin.cases, Fin.induction,
      Fin.induction.go, -GaussianInt.intCast_re, -GaussianInt.intCast_im]
    ring_nf
  have delta_add : ∀ x v, v ∈ TilingLattice C → d (x + v) = d x + d v := by
    intro x v hv
    obtain ⟨a, ha, hg⟩ := hcocycle v hv
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    dsimp at h0 h1
    dsimp [d]
    rw [hg x, shift x v]
    simp only [sub_eq_add_neg]
    rw [h0, h1]
    norm_num
    ring
  have delta_zero : d 0 = 0 := by
    have hz := delta_add 0 0 (TilingLattice C).zero_mem
    simpa using hz
  have delta_neg : ∀ v, v ∈ TilingLattice C → d (-v) = -d v := by
    intro v hv
    have h := delta_add (-v) v hv
    have hmem : -v ∈ TilingLattice C := (TilingLattice C).neg_mem hv
    have hzero : -v + v = 0 := by simp
    rw [hzero, delta_zero] at h
    linarith
  let deltaHom : TilingLattice C →+ ℝ :=
    { toFun := fun v => d v
      map_zero' := delta_zero
      map_add' := by
        intro u v
        exact delta_add u v v.property }
  have basis : ∃ u v : GaussianInt, u ∈ TilingLattice C ∧
      v ∈ TilingLattice C ∧
      ∀ w : TilingLattice C, ∃! mn : Int × Int,
        (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v = (w : GaussianInt) := by
    by_cases hc : C.1.1.1 = 1
    · refine ⟨1, ⟨0, 1⟩, ?_, ?_, ?_⟩
      · simp [TilingLattice, hc]
      · simp [TilingLattice, hc]
      · intro w
        refine ⟨((w : GaussianInt).re, (w : GaussianInt).im), ?_, ?_⟩
        · ext <;> simp
        · intro mn hm
          have hr := congrArg (fun z : GaussianInt => z.re) hm
          have hi := congrArg (fun z : GaussianInt => z.im) hm
          simp? at hr hi
          exact Prod.ext (by exact_mod_cast hr) (by exact_mod_cast hi)
    · have hpos := C.2
      have hgt : 1 < C.1.1.1 := by omega
      obtain ⟨q, T, h, g0, hq, hC, hrest⟩ :=
        PositiveCurvatureGeneratorCocycles C hgt
      obtain ⟨hu, hv, hcoord, hleft, hright, hlast⟩ :=
        TilingLatticeBasis C q hq hC
      exact ⟨BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0), hu, hv,
        hcoord⟩
  obtain ⟨u, v, hu, hv, hcoord⟩ := basis
  let det : ℤ := u.re * v.im - u.im * v.re
  have det_ne : det ≠ 0 := by
    intro hd
    dsimp [det] at hd
    have hu0 : u ≠ 0 := by
      intro hz
      obtain ⟨mn, hm, hmu⟩ := hcoord ⟨0, (TilingLattice C).zero_mem⟩
      have hzero : (0 : Int × Int) = mn := hmu (0, 0) (by simp [hz])
      have hone : (1, 0) = mn := hmu (1, 0) (by simp [hz])
      have hh := congrArg Prod.fst (hone.trans hzero.symm)
      norm_num at hh
    have hv0 : v ≠ 0 := by
      intro hz
      obtain ⟨mn, hm, hmu⟩ := hcoord ⟨0, (TilingLattice C).zero_mem⟩
      have hzero : (0 : Int × Int) = mn := hmu (0, 0) (by simp [hz])
      have hone : (0, 1) = mn := hmu (0, 1) (by simp [hz])
      have hh := congrArg Prod.snd (hone.trans hzero.symm)
      norm_num at hh
    by_cases hreal : v.re = 0 ∧ u.re = 0
    · have himag : v.im ≠ 0 ∨ u.im ≠ 0 := by
        by_cases hvim : v.im = 0
        · right
          intro huim
          apply hu0
          ext <;> simp [huim, hreal.2]
        · exact Or.inl hvim
      rcases himag with hvim | huim
      · let mn : Int × Int := (v.im, -u.im)
        have hz : (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v = 0 := by
          ext <;> simp [mn, hreal.1, hreal.2]
          ring
        obtain ⟨mp, hp, hmp⟩ := hcoord ⟨0, (TilingLattice C).zero_mem⟩
        have heq : mn = mp := hmp mn hz
        have hz0 : (0 : Int × Int) = mp := hmp (0, 0) (by simp)
        have hmzero : mn = (0, 0) := heq.trans hz0.symm
        have : (mn.1 : Int) = 0 := by simpa using congrArg Prod.fst hmzero
        exact hvim this
      · let mn : Int × Int := (v.im, -u.im)
        have hz : (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v = 0 := by
          ext <;> simp [mn, hreal.1, hreal.2]
          ring
        obtain ⟨mp, hp, hmp⟩ := hcoord ⟨0, (TilingLattice C).zero_mem⟩
        have heq : mn = mp := hmp mn hz
        have hz0 : (0 : Int × Int) = mp := hmp (0, 0) (by simp)
        have hmzero : mn = (0, 0) := heq.trans hz0.symm
        have hsecond : (mn.2 : Int) = 0 := by simpa using congrArg Prod.snd hmzero
        dsimp [mn] at hsecond
        exact huim (by linarith [hsecond])
    · let mn : Int × Int := (v.re, -u.re)
      have hz : (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v = 0 := by
        ext <;> simp [mn]
        · ring
        · nlinarith [hd]
      obtain ⟨mp, hp, hmp⟩ := hcoord ⟨0, (TilingLattice C).zero_mem⟩
      have heq : mn = mp := hmp mn hz
      have hz0 : (0 : Int × Int) = mp := hmp (0, 0) (by simp)
      have hmzero : mn = (0, 0) := heq.trans hz0.symm
      have hfirst : (mn.1 : Int) = 0 := by simpa using congrArg Prod.fst hmzero
      have hsecond : (mn.2 : Int) = 0 := by simpa using congrArg Prod.snd hmzero
      apply hreal
      constructor
      · exact hfirst
      · linarith
  let b : ℝ × ℝ :=
    ((d u * (v.im : ℝ) - d v * (u.im : ℝ)) / (det : ℝ),
      ((u.re : ℝ) * d v - (v.re : ℝ) * d u) / (det : ℝ))
  have coordinate_value : ∀ w : TilingLattice C,
      d (w : GaussianInt) =
        b.1 * (w : GaussianInt).re + b.2 * (w : GaussianInt).im := by
    intro w
    obtain ⟨mn, hm, hmu⟩ := hcoord w
    have hlinear : d ((mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v) =
        (mn.1 : ℝ) * d u + (mn.2 : ℝ) * d v := by
      have hu' : (⟨u, hu⟩ : TilingLattice C) =
          (⟨u, hu⟩ : TilingLattice C) := rfl
      have hv' : (⟨v, hv⟩ : TilingLattice C) =
          (⟨v, hv⟩ : TilingLattice C) := rfl
      have hm1 := deltaHom.map_zsmul mn.1 (⟨u, hu⟩ : TilingLattice C)
      have hm2 := deltaHom.map_zsmul mn.2 (⟨v, hv⟩ : TilingLattice C)
      have hadd := deltaHom.map_add
        (mn.1 • (⟨u, hu⟩ : TilingLattice C))
        (mn.2 • (⟨v, hv⟩ : TilingLattice C))
      dsimp [deltaHom, d] at hm1 hm2 hadd ⊢
      rw [hm1, hm2] at hadd
      simpa [smul_eq_mul, zsmul_eq_mul, Int.cast_ofNat, Int.cast_neg,
        add_comm, add_left_comm, add_assoc] using hadd
    have hlinear' : d (w : GaussianInt) =
        (mn.1 : ℝ) * d u + (mn.2 : ℝ) * d v := by
      calc
        d (w : GaussianInt) =
            d ((mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v) :=
          congrArg d hm.symm
        _ = _ := hlinear
    rw [hlinear']
    dsimp [b]
    have hdetreal : (det : ℝ) ≠ 0 := by exact_mod_cast det_ne
    have hr := congrArg (fun z : GaussianInt => z.re) hm
    have hi := congrArg (fun z : GaussianInt => z.im) hm
    simp at hr hi
    field_simp [hdetreal]
    have hrr : (mn.1 : ℝ) * (u.re : ℝ) + (mn.2 : ℝ) * (v.re : ℝ) =
        (w : GaussianInt).re := by exact_mod_cast hr
    have hir : (mn.1 : ℝ) * (u.im : ℝ) + (mn.2 : ℝ) * (v.im : ℝ) =
        (w : GaussianInt).im := by exact_mod_cast hi
    rw [← hrr, ← hir]
    dsimp [det]
    push_cast
    ring_nf
  refine ⟨b, ?_⟩
  intro w hw x
  have hdw := coordinate_value ⟨w, hw⟩
  change d w = b.1 * (w.re : ℝ) + b.2 * (w.im : ℝ) at hdw
  have hdx := delta_add x w hw
  have hcorrected : d (x + w) -
      (b.1 * (x + w).re + b.2 * (x + w).im) =
      d x - (b.1 * x.re + b.2 * x.im) := by
    rw [hdx, show (x + w).re = x.re + w.re by simp,
      show (x + w).im = x.im + w.im by simp]
    rw [Int.cast_add, Int.cast_add]
    have haddb : b.1 * ((x.re : ℝ) + (w.re : ℝ)) +
        b.2 * ((x.im : ℝ) + (w.im : ℝ)) =
        (b.1 * x.re + b.2 * x.im) +
          (b.1 * (w.re : ℝ) + b.2 * (w.im : ℝ)) := by ring
    rw [haddb, ← hdw]
    ring
  simpa [d, Q] using hcorrected

end ApollonianSuperharmonic

end
