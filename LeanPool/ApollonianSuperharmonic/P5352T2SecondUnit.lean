/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5416T1SecondUnitGeometry
public import LeanPool.ApollonianSuperharmonic.P5416T1DiamondAxialDifferences
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: P5352T2SecondUnit]

/-!
# P5352T2SecondUnit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5352T2SecondUnit (K : DiamondParameter) (hk : 1 < K.1)
    (s : Fin 4) (f : IntegerLatticeFunction) (B : Int) (z : GaussianInt) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk 2
    let M := (P5352T2PlacementData K.1 1).2 s
    (∀ y, y ∈ FootprintVertices A.1 → f y = A.2.1 y) →
    (∀ y, y - M.1 ∈ FootprintVertices D.1 →
      f y = D.2.1 (y - M.1) + M.2.1.re*y.re + M.2.1.im*y.im + B) →
    z ∈ FootprintVertices A.1 → z - M.1 ∈ FootprintVertices D.1 →
    (∀ y, y = z ∨ y = z + 1 ∨ y = z - 1 ∨
          y = z + ⟨0, 1⟩ ∨ y = z - ⟨0, 1⟩ →
      y ∈ FootprintVertices A.1 ∨ y - M.1 ∈ FootprintVertices D.1) →
    (z - M.2.2 ∈ FootprintVertices A.1 → FourNeighborLaplacian f z = 0) ∧
    (z - M.2.2 ∉ FootprintVertices A.1 → FourNeighborLaplacian f z = 1) := by
-- BODY
  classical
  let k : Int := K.1
  have hk2 : 2 ≤ k := by dsimp [k]; omega
  let C (p q : Int) : Prop :=
    0 ≤ q ∧ q ≤ 2*k ∧ -k ≤ p ∧ p ≤ k ∧
      -q-1 ≤ p ∧ p ≤ q+1 ∧ -(2*k-q+1) ≤ p ∧ p ≤ 2*k-q+1
  let U (p q : Int) : Prop := 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1
  have cmem (x : GaussianInt) :
      x ∈ FootprintVertices (DiamondTile K.1) ↔ C x.re x.im :=
    (P5352T2DomainRows K x).1
  have umem (x : GaussianInt) :
      x ∈ FootprintVertices (P5352T2Sources K hk 2).1 ↔ U x.re x.im := by
    simp only [P5352T2Sources, Matrix.cons_val_two]
    simp [FootprintVertices]
    simp only [Zsqrtd.ext_iff, Zsqrtd.re_zero, Zsqrtd.im_zero,
      Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_add, Zsqrtd.im_add]
    dsimp [U]
    omega
  dsimp only
  intro hA hP hzA hzP hcov
  change ∀ y, y ∈ FootprintVertices (DiamondTile K.1) →
    f y = DiamondOdometer K y at hA
  have child (p q : Int) (h : C p q) :
      f ⟨p,q⟩ = P4207T1DiamondFormula ⟨p,q⟩ := by as_aux_lemma =>
    rw [hA _ ((cmem _).mpr h)]
    exact (P5352T2DomainRows K _).2 ((cmem _).mpr h)
  obtain ⟨center, marked⟩ := P5416T1SecondUnitGeometry K hk s z hzA hzP hcov
  let d := ((P5352T2PlacementData K.1 1).2 s).1
  let a := ((P5352T2PlacementData K.1 1).2 s).2.1
  have parent (p q : Int) (h : U (p-d.re) (q-d.im)) :
      f ⟨p,q⟩ = a.re*p + a.im*q + B := by as_aux_lemma =>
    have hh := hP ⟨p,q⟩ ((umem _).mpr h)
    change f ⟨p,q⟩ = (if (⟨p,q⟩ : GaussianInt)-d = 1+⟨0,1⟩ then (0 : Int) else 0) +
      a.re*p + a.im*q + B at hh
    simpa only [ite_self, zero_add] using hh
  have lap (p q : Int) : FourNeighborLaplacian f ⟨p,q⟩ =
      (f ⟨p+1,q⟩ - f ⟨p,q⟩) + (f ⟨p-1,q⟩ - f ⟨p,q⟩) +
      (f ⟨p,q+1⟩ - f ⟨p,q⟩) + (f ⟨p,q-1⟩ - f ⟨p,q⟩) := by as_aux_lemma =>
    rw [FourNeighborLaplacian,
      show (⟨p,q⟩ : GaussianInt)+1 = ⟨p+1,q⟩ by ext <;> simp,
      show (⟨p,q⟩ : GaussianInt)-1 = ⟨p-1,q⟩ by ext <;> simp,
      show (⟨p,q⟩ : GaussianInt)+⟨0,1⟩ = ⟨p,q+1⟩ by ext <;> simp,
      show (⟨p,q⟩ : GaussianInt)-⟨0,1⟩ = ⟨p,q-1⟩ by ext <;> simp]
    ring
  clear hA hP hzA hzP hcov umem
  fin_cases s
  · as_aux_lemma =>
    change z = ⟨-k,k⟩ at center
    subst z
    norm_num [Fin.ext_iff] at marked
    change ∀ p q, U (p-(-k-1)) (q-(k-1)) →
      f ⟨p,q⟩ = 0*p + (-k)*q + B at parent
    have hdiffW := parent (-k-1) k (by dsimp [U]; omega)
    have hdiffZ := parent (-k) k (by dsimp [U]; omega)
    have hw : f ⟨-k-1,k⟩ - f ⟨-k,k⟩ = 0 := by
      omega
    clear hdiffW hdiffZ parent
    have he := child (1-k) k (by dsimp [C]; omega)
    have hn := child (-k) (k+1) (by dsimp [C]; omega)
    have hs := child (-k) (k-1) (by dsimp [C]; omega)
    have hc := child (-k) k (by dsimp [C]; omega)
    have hl : FourNeighborLaplacian f ⟨-k,k⟩ = 1 := by
      rw [lap, show -k+1 = 1-k by ring]
      have hleft := (P5416T1DiamondAxialDifferences k hk2).1
      omega
    exact ⟨fun h => False.elim (marked h), fun _ => hl⟩
  · as_aux_lemma =>
    change z = ⟨0,0⟩ at center
    subst z
    norm_num [Fin.ext_iff] at marked
    change ∀ p q, U (p-0) (q-(-1)) →
      f ⟨p,q⟩ = 0*p + 0*q + B at parent
    have hdiffS := parent 0 (-1) (by dsimp [U]; omega)
    have hdiffZ := parent 0 0 (by dsimp [U]; omega)
    have hs : f ⟨0,-1⟩ - f ⟨0,0⟩ = 0 := by
      omega
    clear hdiffS hdiffZ parent
    have he := child 1 0 (by dsimp [C]; omega)
    have hw := child (-1) 0 (by dsimp [C]; omega)
    have hn := child 0 1 (by dsimp [C]; omega)
    have hc := child 0 0 (by dsimp [C]; omega)
    have hl : FourNeighborLaplacian f ⟨0,0⟩ = 0 := by
      rw [lap]
      norm_num only [zero_add, zero_sub]
      have hbottom := (P5416T1DiamondAxialDifferences k hk2).2.1
      omega
    exact ⟨fun _ => hl, fun h => False.elim (h marked)⟩
  · as_aux_lemma =>
    change z = ⟨k,k⟩ at center
    subst z
    norm_num [Fin.ext_iff] at marked
    change ∀ p q, U (p-k) (q-k) →
      f ⟨p,q⟩ = k*p + 0*q + B at parent
    have hdiffE := parent (k+1) k (by dsimp [U]; omega)
    have hdiffZ := parent k k (by dsimp [U]; omega)
    have he : f ⟨k+1,k⟩ - f ⟨k,k⟩ = k := by
      nlinarith only [hdiffE, hdiffZ]
    clear hdiffE hdiffZ parent
    have hw := child (k-1) k (by dsimp [C]; omega)
    have hn := child k (k+1) (by dsimp [C]; omega)
    have hs := child k (k-1) (by dsimp [C]; omega)
    have hc := child k k (by dsimp [C]; omega)
    have hl : FourNeighborLaplacian f ⟨k,k⟩ = 1 := by
      rw [lap]
      have hright := (P5416T1DiamondAxialDifferences k hk2).2.2.1
      omega
    exact ⟨fun h => False.elim (marked h), fun _ => hl⟩
  · as_aux_lemma =>
    change z = ⟨0,2*k⟩ at center
    subst z
    norm_num [Fin.ext_iff] at marked
    change ∀ p q, U (p-(-1)) (q-2*k) →
      f ⟨p,q⟩ = k*p + (-k)*q + B at parent
    have hdiffN := parent 0 (2*k+1) (by dsimp [U]; omega)
    have hdiffZ := parent 0 (2*k) (by dsimp [U]; omega)
    have hn : f ⟨0,2*k+1⟩ - f ⟨0,2*k⟩ = -k := by
      nlinarith only [hdiffN, hdiffZ]
    clear hdiffN hdiffZ parent
    have he := child 1 (2*k) (by dsimp [C]; omega)
    have hw := child (-1) (2*k) (by dsimp [C]; omega)
    have hs := child 0 (2*k-1) (by dsimp [C]; omega)
    have hc := child 0 (2*k) (by dsimp [C]; omega)
    have hl : FourNeighborLaplacian f ⟨0,2*k⟩ = 0 := by
      rw [lap]
      norm_num only [zero_add, zero_sub]
      have htop := (P5416T1DiamondAxialDifferences k hk2).2.2.2
      omega
    exact ⟨fun _ => hl, fun h => False.elim (h marked)⟩

end ApollonianSuperharmonic

end
