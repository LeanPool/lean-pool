/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5596T1CommonExtensionTransport
public import LeanPool.ApollonianSuperharmonic.P5332T1LiteralNormalization
public import LeanPool.ApollonianSuperharmonic.FordLaplacianTable
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacentPackingSymmetryTransport

-- [TABLET NODE: P5596T1LineParent]

/-!
# P5596T1LineParent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5596T1LineParent
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (i : Fin 3) (e : Bool) (hzero : (q i.succ).1 = 0)
    (T U : ProtoTile) (h k : PartialOdometer) (p p' : ℝ × ℝ)
    (g : IntegerLatticeFunction) (x : GaussianInt)
    (hT : TileOdometer (q 0) T h) (hU : TileOdometer (q 0) U k)
    (hp : PartialOdometerSlope h = some p)
    (hp' : PartialOdometerSlope k = some p')
    (hc : TileCentroid U - TileCentroid T =
      (if e = true then (1 : ℝ) else -1) •
        GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (hr : p'.1 - p.1 = (if e = true then (1 : ℝ) else -1) *
      (BandVectors.2 (q i.succ) (q 0)).re)
    (hi : p'.2 - p.2 = (if e = true then (1 : ℝ) else -1) *
      (BandVectors.2 (q i.succ) (q 0)).im)
    (hg : GlobalOdometerExtends g h) (kg : GlobalOdometerExtends g k)
    (hx : x ∈ h.domain) (kx : x ∈ k.domain)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h.domain ∨ y ∈ k.domain) :
    FourNeighborLaplacian g x = 1 := by
-- BODY
  have fordLineStar (P : FordFareyParameter) (e : Bool)
      (T U : ProtoTile) (h k : PartialOdometer) (p p' : ℝ × ℝ)
      (g : IntegerLatticeFunction) (x : GaussianInt)
      (hT : TileOdometer (FordCircleCoordinate P.p P.q) T h)
      (hU : TileOdometer (FordCircleCoordinate P.p P.q) U k)
      (hp : PartialOdometerSlope h = some p)
      (hp' : PartialOdometerSlope k = some p')
      (hc : TileCentroid U - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint ⟨0, -(P.q : Int)⟩)
      (hr : p'.1 - p.1 = (if e = true then (1 : ℝ) else -1) * (-P.p : Int))
      (hi : p'.2 - p.2 = 0)
      (hg : GlobalOdometerExtends g h) (kg : GlobalOdometerExtends g k)
      (hx : x ∈ h.domain) (kx : x ∈ k.domain)
      (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h.domain ∨ y ∈ k.domain) :
      FourNeighborLaplacian g x = 1 := by
    obtain ⟨u, d, a, B, f, hd, hd', _, _, _, hcent, hslope, hslope', hv, hv', hlap⟩ :=
      P5332T1LiteralNormalization P P T U h k p p' g hT hU hp hp' hg kg
    have dr : d.re = 0 := by
      have hh := congrArg Prod.fst hc
      rw [hcent] at hh
      change (↑P.q - ↑P.q) / 2 + (d.re : ℝ) =
        (if e = true then (1 : ℝ) else -1) * ((0 : Int) : ℝ) at hh
      simp only [sub_self, zero_div, zero_add, Int.cast_zero, mul_zero] at hh
      exact_mod_cast hh
    have di : d.im = if e = true then -(P.q : Int) else (P.q : Int) := by
      have hh := congrArg Prod.snd hc
      rw [hcent] at hh
      change (↑P.q - ↑P.q) / 2 + (d.im : ℝ) =
        (if e = true then (1 : ℝ) else -1) * (-(P.q : Int) : Int) at hh
      cases e <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        sub_self, zero_div, zero_add, Int.cast_neg, neg_mul, one_mul, neg_neg] at hh ⊢ <;>
        exact_mod_cast hh
    have ar : a.re = if e = true then -P.p else P.p := by
      rw [hslope] at hr
      cases e <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        sub_self, zero_div, zero_add, Int.cast_neg, neg_mul, one_mul, neg_neg] at hr ⊢ <;>
        exact_mod_cast hr
    have ai : a.im = 0 := by
      rw [hslope'] at hi
      simp only [sub_self, zero_div, zero_add] at hi
      exact_mod_cast hi
    have hneg (y : GaussianInt) :
        FordOdometer P (y + ⟨0, -(P.q : Int)⟩) = FordOdometer P y - P.p*y.re :=
      (Classical.choose_spec FordOdometerFamilyExistsUnique).1.2.2.1 P y
    have cocycle (y : GaussianInt) :
        FordOdometer P (y-d) + a.re*y.re + a.im*y.im = FordOdometer P y := by
      cases e
      · have deq : d = ⟨0, (P.q : Int)⟩ := by
          ext <;> simp_all
        have heq : y-d = y+⟨0, -(P.q : Int)⟩ := by
          rw [deq]
          ext <;> simp [sub_eq_add_neg]
        rw [heq, hneg, ar, ai]
        simp
      · have deq : d = ⟨0, -(P.q : Int)⟩ := by
          ext <;> simp_all
        have hh := hneg (y-d)
        have heq : y-d+⟨0, -(P.q : Int)⟩ = y := by rw [← deq]; abel
        rw [heq] at hh
        rw [ar, ai]
        simp only [ite_true, Zsqrtd.re_sub, dr, sub_zero] at hh ⊢
        linear_combination -hh
    have hB : B = 0 := by
      have h1 := hv (x-u) ((hd x).mp hx)
      have h2 := hv' (x-u) ((hd' x).mp kx)
      have h3 := cocycle (x-u)
      omega
    have values (y : GaussianInt)
        (hy : y = x ∨ y = x+1 ∨ y = x-1 ∨ y = x+⟨0,1⟩ ∨ y = x-⟨0,1⟩) :
        f (y-u) = FordOdometer P (y-u) := by
      rcases hstar y hy with hh | hk
      · exact hv (y-u) ((hd y).mp hh)
      · rw [hv' (y-u) ((hd' y).mp hk), hB, add_zero]
        exact cocycle (y-u)
    have hboundary : x-u ∈ LatticeVertexBoundary (FordVertexDomain P.q) := by
      have h1 := (hd x).mp hx
      have h2 := (hd' x).mp kx
      have hq := P.q_pos
      change 0 ≤ (x-u).re ∧ (x-u).re ≤ (P.q : Int) ∧
        0 ≤ (x-u).im ∧ (x-u).im ≤ (P.q : Int) at h1
      change 0 ≤ (x-u-d).re ∧ (x-u-d).re ≤ (P.q : Int) ∧
        0 ≤ (x-u-d).im ∧ (x-u-d).im ≤ (P.q : Int) at h2
      change 0 ≤ (x-u).re-d.re ∧ (x-u).re-d.re ≤ (P.q : Int) ∧
        0 ≤ (x-u).im-d.im ∧ (x-u).im-d.im ≤ (P.q : Int) at h2
      rw [dr] at h2
      refine ⟨h1, ?_⟩
      cases e
      · have heq : (x-u).im = (P.q : Int) := by
          simp only [Bool.false_eq_true, ite_false] at di
          omega
        refine ⟨x-u+⟨0,1⟩, ?_, ?_, ?_⟩
        · change ¬ (0 ≤ (x-u).re + 0 ∧ (x-u).re + 0 ≤ (P.q : Int) ∧
            0 ≤ (x-u).im + 1 ∧ (x-u).im + 1 ≤ (P.q : Int))
          omega
        · simp
        · simp
      · have heq : (x-u).im = 0 := by simp only [ite_true] at di; omega
        refine ⟨x-u-⟨0,1⟩, ?_, ?_, ?_⟩
        · simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub]
          simp only [Zsqrtd.im_sub] at heq
          omega
        · simp
        · simp
    rw [hlap x]
    have htable := (FordLaplacianTable P).2.1 (x-u) hboundary
    unfold FourNeighborLaplacian at htable ⊢
    have eq1 : x-u+1 = x+1-u := by abel
    have eq2 : x-u-1 = x-1-u := by abel
    have eq3 : x-u+⟨0,1⟩ = x+⟨0,1⟩-u := by abel
    have eq4 : x-u-⟨0,1⟩ = x-⟨0,1⟩-u := by abel
    rw [eq1, eq2, eq3, eq4] at htable ⊢
    rw [values x (Or.inl rfl), values (x+1) (Or.inr (Or.inl rfl)),
      values (x-1) (Or.inr (Or.inr (Or.inl rfl))),
      values (x+⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      values (x-⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
    exact htable
  obtain ⟨a, s, P, hP, hrev, _, hline, hford⟩ :=
    FordRegimeConverse q hq ⟨i.succ, hzero⟩
  have hindex : i = a+2 :=
    (ProperBandCurvatureStructure q hq).2.2 i (a+2) hzero hline
  let r : Fin 4 → CircleCoordinates :=
    ![q 0, q a.succ, q (a+1).succ, q (a+2).succ]
  have hr0 : r 0 = q 0 := rfl
  have hr3 : r (2 : Fin 3).succ = q i.succ := by rw [hindex]; rfl
  have hproper : ProperBandQuadruple r := by
    fin_cases a
    · convert hq using 1; (try funext j; fin_cases j) <;> rfl
    · refine ⟨?_, ?_⟩
      · exact SemiProperQuadruple.rotate hq.1
      · intro j
        fin_cases j
        · exact hq.2 1
        · exact hq.2 2
        · exact hq.2 0
    · refine ⟨?_, ?_⟩
      · exact SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1)
      · intro j
        fin_cases j
        · exact hq.2 2
        · exact hq.2 0
        · exact hq.2 1
  obtain ⟨negative, v, v', _, hTn, hUn, hpn, hp'n, hcn, hrn, hin, _⟩ :=
    LeftLatticeAdjacentPackingSymmetryTransport s r hproper 2 e T U h k p p'
      (by simpa only [hr0] using hT) (by simpa only [hr0] using hU) hp hp'
      (by simpa only [hr0, hr3] using hc)
      (by simpa only [hr0, hr3] using hr)
      (by simpa only [hr0, hr3] using hi)
  obtain ⟨g', hg', kg', hlap, hxn, kxn, hstarn⟩ :=
    P5596T1CommonExtensionTransport s g h k x hg kg hx kx hstar
  obtain ⟨_, _, _, hvline, _, _, haline, _, _⟩ :=
    (FordCoordinateConfiguration P).2 hP
  have hzeroN : FourNeighborLaplacian g' (BandPackingSymmetryVectorAction s x) = 1 := by
    apply fordLineStar P (xor e negative)
      (BandPackingSymmetryTileAction s T) (BandPackingSymmetryTileAction s U)
      (BandPackingSymmetryPartialOdometerAction s h)
      (BandPackingSymmetryPartialOdometerAction s k) v v' g'
      (BandPackingSymmetryVectorAction s x)
    · simpa only [show BandPackingSymmetryQuadrupleAction s r = FordRecursiveQuadruple P
        from hford, FordRecursiveQuadruple, Matrix.cons_val_zero] using hTn
    · simpa only [show BandPackingSymmetryQuadrupleAction s r = FordRecursiveQuadruple P
        from hford, FordRecursiveQuadruple, Matrix.cons_val_zero] using hUn
    · exact hpn
    · exact hp'n
    · simpa only [hrev, Bool.false_eq_true, ite_false,
        show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
        show BandPackingSymmetryQuadrupleAction s r = FordRecursiveQuadruple P from hford,
        hvline] using hcn
    · simpa only [hrev, Bool.false_eq_true, ite_false,
        show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
        show BandPackingSymmetryQuadrupleAction s r = FordRecursiveQuadruple P from hford,
        haline] using hrn
    · simpa only [hrev, Bool.false_eq_true, ite_false,
        show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
        show BandPackingSymmetryQuadrupleAction s r = FordRecursiveQuadruple P from hford,
        haline, Int.cast_zero, mul_zero] using hin
    · exact hg'
    · exact kg'
    · exact hxn
    · exact kxn
    · exact hstarn
  exact hlap ▸ hzeroN

end ApollonianSuperharmonic

end
