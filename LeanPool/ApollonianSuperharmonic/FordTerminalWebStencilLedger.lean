/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1LiteralNormalization
public import LeanPool.ApollonianSuperharmonic.P5332T1VectorPlacements
public import LeanPool.ApollonianSuperharmonic.P5332T1RightFirstValues
public import LeanPool.ApollonianSuperharmonic.P5332T1RightSecondValues
public import LeanPool.ApollonianSuperharmonic.P5332T1RightHorizontalValues
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent1Rotation0Values
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent1Rotation1Values
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent1Rotation2Values
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent1Rotation3Values
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent2Rotation0Values
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent2Rotation1Values
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent2Rotation2Values
public import LeanPool.ApollonianSuperharmonic.P5332T1Parent2Rotation3Values
public import LeanPool.ApollonianSuperharmonic.P5332T1RightRounding
public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRounding

-- [TABLET NODE: FordTerminalWebStencilLedger]

/-!
# FordTerminalWebStencilLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordTerminalStencilGeometry

private theorem lapValues :
    (by
      classical
      exact
        ∀ (f : IntegerLatticeFunction), ∀ (z : GaussianInt), ∀ (V : Fin 5 → Int), (∀ k : Fin 5,
            f (z + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k)) = V k) →
                (FourNeighborLaplacian f z = V 1 + V 2 + V 3 + V 4 - 4 * V 0) ) := by
  classical
  intro f z V hV
  unfold FourNeighborLaplacian
  rw [show f (z + 1) = V 1 by simpa using hV 1,
    show f (z - 1) = V 2 by simpa [sub_eq_add_neg] using hV 2,
    show f (z + ⟨0, 1⟩) = V 3 by simpa using hV 3,
    show f (z - ⟨0, 1⟩) = V 4 by simpa [sub_eq_add_neg] using hV 4,
    show f z = V 0 by simpa using hV 0]

private theorem positive :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → ((
        let q := FordRecursiveQuadruple P
        (∀ j : Fin 3,
          BandVectors.1 (q 0) (q j.succ) = (P5332T1RightRows P j 0).displacement ∧
          BandVectors.2 (q 0) (q j.succ) = (P5332T1RightRows P j 0).linear) ∧
        ∀ (j : Fin 2), ∀ (k : Fin 4),
        let i : Fin 3 := ⟨j.val, by omega⟩
          let R := P5332T1ParentRows P j k 0
          (1 / 2 : ℝ) • GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ k.val *
                (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) =
            (((((![P.q₁, P.q₂] j : Nat) : ℝ) - P.q) / 2 + R.displacement.re),
             ((((![P.q₁, P.q₂] j : Nat) : ℝ) - P.q) / 2 + R.displacement.im)) ∧
          (1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ k.val *
                (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))) =
            (((((![P.p₁, P.p₂] j : Int) : ℝ) - P.p) / 2 + R.linear.re),
             ((((![P.p₁, P.p₂] j : Int) : ℝ) - P.p) / 2 + R.linear.im)) ∧
          (⟨0, 1⟩ : GaussianInt) ^ k.val *
            (if Even k.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)) = R.companion) → ((∀ (f :
                  IntegerLatticeFunction), ∀ (z : GaussianInt), ∀ (V : Fin 5 → Int), (∀ k : Fin
                  5, f (z + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k)) = V k) →
                  (FourNeighborLaplacian f z = V 1 + V 2 + V 3 + V 4 - 4 * V 0)) → (∀ (i : Fin
                  3), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
                      PartialOdometer), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), ∀ (g :
                      IntegerLatticeFunction), ∀ (x : GaussianInt), TileOdometer
                  (FordRecursiveQuadruple P 0) T h → TileOdometer (FordRecursiveQuadruple P 0) T'
                  h' → PartialOdometerSlope h = some p → PartialOdometerSlope h' = some p' →
                  TileCentroid T' - TileCentroid T = GaussianRealPoint (BandVectors.1
                  (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)) → p'.1 - p.1 =
                  (BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P
                  i.succ)).re → p'.2 - p.2 = (BandVectors.2 (FordRecursiveQuadruple P 0)
                  (FordRecursiveQuadruple P i.succ)).im → GlobalOdometerExtends g h →
                  GlobalOdometerExtends g h' → x ∈ h.domain → x ∈ h'.domain → (∀ y, y = x ∨ y = x
                  + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ h.domain ∨ y ∈
                  h'.domain) → ((∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨ z = x - 1 - ⟨0, 1⟩ → z
                  ∈ T.cells ∨ z ∈ T'.cells) → FourNeighborLaplacian g x = 1) ∧ (¬ (∀ z, z = x ∨ z
                  = x - 1 ∨ z = x - ⟨0, 1⟩ ∨ z = x - 1 - ⟨0, 1⟩ → z ∈ T.cells ∨ z ∈ T'.cells) →
                  FourNeighborLaplacian g x = 0))))) := by
  classical
  intro P hq vectors lapValues i T U h k p p' g x hT hU hp hp' hc ha hb he he' hx hx' hstar
  obtain ⟨u, d, a, B, f, hdom, hdom', hcell, hcell', hfoot,
    hcent, hslope, hslope', hbase, hother, hlap⟩ :=
    P5332T1LiteralNormalization P P T U h k p p' g hT hU hp hp' he he'
  rw [(vectors.1 i).1] at hc
  rw [(vectors.1 i).2] at ha hb
  simp only [sub_self, zero_div, zero_add] at hcent hslope hslope'
  have hd : d = (P5332T1RightRows P i 0).displacement := by
    apply Zsqrtd.ext
    · have hh := congrArg Prod.fst (hcent.symm.trans hc)
      dsimp only [GaussianRealPoint] at hh
      exact_mod_cast hh
    · have hh := congrArg Prod.snd (hcent.symm.trans hc)
      dsimp only [GaussianRealPoint] at hh
      exact_mod_cast hh
  have ha' : a = (P5332T1RightRows P i 0).linear := by
    apply Zsqrtd.ext
    · exact_mod_cast hslope.symm.trans ha
    · exact_mod_cast hslope'.symm.trans hb
  subst d
  subst a
  have hstar' : ∀ l : Fin 5,
      x-u + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l) ∈ FordVertexDomain P.q ∨
      x-u + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l) -
        (P5332T1RightRows P i 0).displacement ∈ FordVertexDomain P.q := by
    intro l
    have hh := hstar (x + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l))
      (by fin_cases l <;> simp [sub_eq_add_neg])
    simpa [hdom, hdom', sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh
  have source : ∃ t : Int, 0 ≤ t ∧
      t ≤ ((![P.q₂,P.q₁,P.q] i : Nat) : Int) ∧
      (∀ l : Fin 5, f (x-u + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l)) =
        (P5332T1RightRows P i t).values l) ∧
      ((∀ z, z = x-u ∨ z = x-u-1 ∨ z = x-u-⟨0,1⟩ ∨ z = x-u-1-⟨0,1⟩ →
        z ∈ (FordTile P.q).cells ∨
        z - (P5332T1RightRows P i 0).displacement ∈ (FordTile P.q).cells) ↔
        0 < t ∧ t < ((![P.q₂,P.q₁,P.q] i : Nat) : Int)) := by
    fin_cases i
    · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1RightFirstValues P hq f B
        (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
      exact ⟨t, ht, ht', hv, hh⟩
    · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1RightSecondValues P hq f B
        (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
      exact ⟨t, ht, ht', hv, hh⟩
    · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1RightHorizontalValues P hq f B
        (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
      exact ⟨t, ht, ht', hv, hh⟩
  obtain ⟨t, ht, ht', hv, hh⟩ := source
  have celltest : (∀ z, z = x ∨ z = x-1 ∨ z = x-⟨0,1⟩ ∨ z = x-1-⟨0,1⟩ →
      z ∈ T.cells ∨ z ∈ U.cells) ↔
      (∀ z, z = x-u ∨ z = x-u-1 ∨ z = x-u-⟨0,1⟩ ∨ z = x-u-1-⟨0,1⟩ →
        z ∈ (FordTile P.q).cells ∨
        z - (P5332T1RightRows P i 0).displacement ∈ (FordTile P.q).cells) := by
    constructor
    · intro H z hz
      have hz' : z+u = x ∨ z+u = x-1 ∨ z+u = x-⟨0,1⟩ ∨ z+u = x-1-⟨0,1⟩ := by
        rcases hz with rfl | rfl | rfl | rfl <;>
          simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      simpa [hcell, hcell', sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
        using H (z+u) hz'
    · intro H z hz
      have hz' : z-u = x-u ∨ z-u = x-u-1 ∨ z-u = x-u-⟨0,1⟩ ∨ z-u = x-u-1-⟨0,1⟩ := by
        rcases hz with rfl | rfl | rfl | rfl <;>
          simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      simpa [hcell, hcell'] using H (z-u) hz'
  have hg : FourNeighborLaplacian g x =
      if 0 < t ∧ t < ((![P.q₂,P.q₁,P.q] i : Nat) : Int) then 1 else 0 := by
    rw [hlap x, lapValues f (x-u) _ hv]
    exact P5332T1RightRounding P hq i t ht ht'
  constructor
  · intro H
    rw [hg, ite_eq_left (hh.mp (celltest.mp H))]
  · intro H
    rw [hg, ite_eq_right (fun h => H (celltest.mpr (hh.mpr h)))]

private theorem hc' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (T : ProtoTile), ∀ (U : ProtoTile),
            (TileCentroid U - TileCentroid T = (if false = true then (1 : ℝ) else (-1 : ℝ)) •
            GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P i.succ))) → (TileCentroid T - TileCentroid U =
            GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple
            P i.succ))) ) := by
  classical
  intro P i T U hc
  simpa using congrArg Neg.neg hc

private theorem ha'At320 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), (p'.1 -
            p.1 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ)).re :
            ℝ)) → (p.1 - p'.1 = (BandVectors.2 (FordRecursiveQuadruple P 0)
            (FordRecursiveQuadruple P i.succ)).re) ) := by
  classical
  intro P i p p' ha
  change p'.1 - p.1 = -1 * _ at ha
  linarith

private theorem hb' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), (p'.2 -
            p.2 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ)).im :
            ℝ)) → (p.2 - p'.2 = (BandVectors.2 (FordRecursiveQuadruple P 0)
            (FordRecursiveQuadruple P i.succ)).im) ) := by
  classical
  intro P i p p' hb
  change p'.2 - p.2 = -1 * _ at hb
  linarith

private theorem hs :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), (∀ (y :
            GaussianInt), y = x ∨ y = x + (1 : GaussianInt) ∨ y = x - (1 : GaussianInt) ∨ y = x +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈
            h.domain ∨ y ∈ k.domain) → (∀ y, y = x ∨ y = x+1 ∨ y = x-1 ∨ y = x+⟨0,1⟩ ∨ y =
            x-⟨0,1⟩ → y ∈ k.domain ∨ y ∈ h.domain) ) := by
  classical
  intro h k x hstar y hy
  exact (hstar y hy).symm

private theorem hiAt337 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin (3 : ℕ)),
            ∀ (s : Fin (4 : ℕ)),
              ∀ (p : ℝ × ℝ),
                ∀ (p' : ℝ × ℝ),
                  (0 : ℤ) < (FordRecursiveQuadruple P i.succ).1 →
                    p'.1 - p.1 =
                        ((1 / 2 : ℝ) •
                            GaussianRealPoint
                              ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) *
                                (BandVectors.2 (FordRecursiveQuadruple P i.succ)
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) +
                                BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                (FordRecursiveQuadruple P i.succ)))).1 →
                      p'.2 - p.2 =
                          ((1 / 2 : ℝ) •
                              GaussianRealPoint
                                ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) *
                                (BandVectors.2 (FordRecursiveQuadruple P i.succ)
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) +
                                BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                (FordRecursiveQuadruple P i.succ)))).2 →
                        i.val < 2
    ) := by
  classical
  intro P i s p p' hpos ha hb
  by_contra hn
  have hi : i = 2 := Fin.ext (by omega)
  subst i
  change (0 : Int) < 0 at hpos
  omega

private theorem hdAt363 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T : ProtoTile),
            ∀ (U : ProtoTile), (TileCentroid U - TileCentroid T = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1
            (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) +
            BandVectors.1 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P
            i.succ)))) → (∀ (hi : i.val < 2),
        let j : Fin 2 := ⟨i.val, hi⟩
        ∀ (A : FordFareyParameter), (A.q = ![P.q₁, P.q₂] j) → (∀ (d : GaussianInt), (TileCentroid
            U - TileCentroid T = (((↑A.q : ℝ) - (↑P.q : ℝ)) / (2 : ℝ) + (↑d.re : ℝ), ((↑A.q : ℝ)
            - (↑P.q : ℝ)) / (2 : ℝ) + (↑d.im : ℝ))) → (((1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (FordRecursiveQuadruple P
            i.succ) (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) + BandVectors.1
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ))) =
            (((↑(![P.q₁, P.q₂] j) : ℝ) - (↑P.q : ℝ)) / (2 : ℝ) + (↑(P5332T1ParentRows P j s (0
            : ℤ)).displacement.re : ℝ), ((↑(![P.q₁, P.q₂] j) : ℝ) - (↑P.q : ℝ)) / (2 : ℝ) +
            (↑(P5332T1ParentRows P j s (0 : ℤ)).displacement.im : ℝ)) ∧ (1 / 2 : ℝ) •
            GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2
            (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) +
            BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P
            i.succ))) = (((↑(![P.p₁, P.p₂] j) : ℝ) - (↑P.p : ℝ)) / (2 : ℝ) +
            (↑(P5332T1ParentRows P j s (0 : ℤ)).linear.re : ℝ), ((↑(![P.p₁, P.p₂] j) : ℝ) -
            (↑P.p : ℝ)) / (2 : ℝ) + (↑(P5332T1ParentRows P j s (0 : ℤ)).linear.im : ℝ)) ∧ ((⟨(0
            : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ) else
            BandVectors.1 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P (0 : Fin (4
            : ℕ)))) = (P5332T1ParentRows P j s (0 : ℤ)).companion) → (d = (P5332T1ParentRows
            P j s 0).displacement)))) ) := by
  classical
  intro P i s T U hc hi j A hAq d hcent vv
  apply Zsqrtd.ext
  · have hn := congrArg Prod.fst hcent
    have hv := congrArg Prod.fst (hc.trans vv.1)
    rw [hAq] at hn
    dsimp at hn hv
    exact_mod_cast (show (d.re : ℝ) = (P5332T1ParentRows P j s 0).displacement.re by linarith)
  · have hn := congrArg Prod.snd hcent
    have hv := congrArg Prod.snd (hc.trans vv.1)
    rw [hAq] at hn
    dsimp at hn hv
    exact_mod_cast (show (d.im : ℝ) = (P5332T1ParentRows P j s 0).displacement.im by linarith)

private theorem ha'At375 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (p : ℝ × ℝ), ∀
            (p' : ℝ × ℝ), (p'.1 - p.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (FordRecursiveQuadruple P i.succ)
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) + BandVectors.2 (FordRecursiveQuadruple
            P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ)))).1) → ((p'.2 - p.2 = ((1 / 2
            : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) *
            (BandVectors.2 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P (0 : Fin
            (4 : ℕ))) + BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P i.succ)))).2) → (∀ (hi : i.val < 2),
        let j : Fin 2 := ⟨i.val, hi⟩
        ∀ (A : FordFareyParameter), (A.p = ![P.p₁, P.p₂] j) → (∀ (a : GaussianInt), (p'.1 - p.1 =
            ((↑A.p : ℝ) - (↑P.p : ℝ)) / (2 : ℝ) + (↑a.re : ℝ)) → ((p'.2 - p.2 = ((↑A.p : ℝ) -
            (↑P.p : ℝ)) / (2 : ℝ) + (↑a.im : ℝ)) → (((1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (FordRecursiveQuadruple P i.succ)
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) + BandVectors.1 (FordRecursiveQuadruple
            P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ))) = (((↑(![P.q₁, P.q₂] j) : ℝ)
            - (↑P.q : ℝ)) / (2 : ℝ) + (↑(P5332T1ParentRows P j s (0 : ℤ)).displacement.re : ℝ),
            ((↑(![P.q₁, P.q₂] j) : ℝ) - (↑P.q : ℝ)) / (2 : ℝ) + (↑(P5332T1ParentRows P j s (0 :
            ℤ)).displacement.im : ℝ)) ∧ (1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (FordRecursiveQuadruple P i.succ)
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) + BandVectors.2 (FordRecursiveQuadruple
            P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ))) = (((↑(![P.p₁, P.p₂] j) : ℝ)
            - (↑P.p : ℝ)) / (2 : ℝ) + (↑(P5332T1ParentRows P j s (0 : ℤ)).linear.re : ℝ),
            ((↑(![P.p₁, P.p₂] j) : ℝ) - (↑P.p : ℝ)) / (2 : ℝ) + (↑(P5332T1ParentRows P j s (0 :
            ℤ)).linear.im : ℝ)) ∧ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s :
            ℕ) then BandVectors.1 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P i.succ) else BandVectors.1 (FordRecursiveQuadruple P
            i.succ) (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))) = (P5332T1ParentRows P j s (0
            : ℤ)).companion) → (a = (P5332T1ParentRows P j s 0).linear)))))) ) := by
  classical
  intro P i s p p' ha hb hi j A hAp a hslope hslope' vv
  have hvr := congrArg Prod.fst vv.2.1
  have hvi := congrArg Prod.snd vv.2.1
  rw [hAp] at hslope hslope'
  dsimp at hvr hvi ha hb
  apply Zsqrtd.ext
  · exact_mod_cast (show (a.re : ℝ) = (P5332T1ParentRows P j s 0).linear.re by linarith)
  · exact_mod_cast (show (a.im : ℝ) = (P5332T1ParentRows P j s 0).linear.im by linarith)

private theorem hstar'At385 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), (∀ (y : GaussianInt),
            y = x ∨ y = x + (1 : GaussianInt) ∨ y = x - (1 : GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈ h.domain ∨ y
            ∈ k.domain) → (∀ (hi : i.val < 2),
        let j : Fin 2 := ⟨i.val, hi⟩
        ∀ (A : FordFareyParameter), ∀ (u : GaussianInt), (∀ (x : GaussianInt), x ∈ h.domain ↔ x -
            u ∈ FordVertexDomain P.q) → ((∀ (x : GaussianInt), x ∈ k.domain ↔ x - u -
            (P5332T1ParentRows P j s (0 : ℤ)).displacement ∈ FordVertexDomain A.q) → (∀ l : Fin
            5, x-u + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l) ∈ FordVertexDomain P.q ∨ x-u +
            (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l) - (P5332T1ParentRows P j s
            0).displacement ∈ FordVertexDomain A.q))) ) := by
  classical
  intro P i s h k x hstar hi j A u hdom hdom' l
  have hh := hstar (x + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l))
    (by fin_cases l <;> simp [sub_eq_add_neg])
  simpa [hdom, hdom', sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh

private theorem sourceAt395 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (1 : ℕ) < P.q →
            ∀ (i : Fin (3 : ℕ)),
              ∀ (s : Fin (4 : ℕ)),
                ∀ (h : PartialOdometer),
                  ∀ (k : PartialOdometer),
                    ∀ (p : ℝ × ℝ),
                      ∀ (p' : ℝ × ℝ),
                        ∀ (x : GaussianInt),
                          p'.1 - p.1 =
                              ((1 / 2 : ℝ) •
                                GaussianRealPoint
                                ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) *
                                (BandVectors.2 (FordRecursiveQuadruple P i.succ)
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) +
                                BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                (FordRecursiveQuadruple P i.succ)))).1 →
                            p'.2 - p.2 =
                                ((1 / 2 : ℝ) •
                                GaussianRealPoint
                                ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) *
                                (BandVectors.2 (FordRecursiveQuadruple P i.succ)
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) +
                                BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                (FordRecursiveQuadruple P i.succ)))).2 →
                              x ∈ h.domain →
                                x ∈ k.domain →
                                ∀ (j : Fin (2 : ℕ)),
                                ∀ (A : FordFareyParameter),
                                A.p = ![P.p₁, P.p₂] j →
                                A.q = ![P.q₁, P.q₂] j →
                                ∀ (u : GaussianInt),
                                ∀ (B : ℤ),
                                ∀ (f : IntegerLatticeFunction),
                                (∀ (x : GaussianInt),
                                x ∈ h.domain ↔ x - u ∈ FordVertexDomain P.q) →
                                (∀ y ∈ FordVertexDomain P.q, f y = FordOdometer P y) →
                                (∀ (x : GaussianInt),
                                x ∈ k.domain ↔
                                x - u - (P5332T1ParentRows P j s (0 : ℤ)).displacement ∈
                                FordVertexDomain A.q) →
                                p'.1 - p.1 =
                                ((↑A.p : ℝ) - (↑P.p : ℝ)) / (2 : ℝ) +
                                (↑(P5332T1ParentRows P j s (0 : ℤ)).linear.re : ℝ) →
                                p'.2 - p.2 =
                                ((↑A.p : ℝ) - (↑P.p : ℝ)) / (2 : ℝ) +
                                (↑(P5332T1ParentRows P j s (0 : ℤ)).linear.im : ℝ) →
                                (∀ (y : GaussianInt),
                                y - (P5332T1ParentRows P j s (0 : ℤ)).displacement ∈
                                FordVertexDomain A.q →
                                f y =
                                FordOdometer A
                                (y - (P5332T1ParentRows P j s (0 : ℤ)).displacement) +
                                (P5332T1ParentRows P j s (0 : ℤ)).linear.re * y.re +
                                (P5332T1ParentRows P j s (0 : ℤ)).linear.im * y.im +
                                B) →
                                (∀ (l : Fin (5 : ℕ)),
                                x - u +
                                ![(0 : ℤ√(-1 : ℤ)), (1 : ℤ√(-1 : ℤ)), (-1 : ℤ√(-1 : ℤ)),
                                (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt),
                                -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)]
                                l ∈
                                FordVertexDomain P.q ∨
                                x - u +
                                ![(0 : ℤ√(-1 : ℤ)), (1 : ℤ√(-1 : ℤ)), (-1 : ℤ√(-1 : ℤ)),
                                (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt),
                                -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)]
                                l -
                                (P5332T1ParentRows P j s (0 : ℤ)).displacement ∈
                                FordVertexDomain A.q) →
                                ∃ t : Int,
                                0 ≤ t ∧
                                t < ((![P.q₁, P.q₂] j : Nat) : Int) ∧
                                (∀ l : Fin 5,
                                f
                                (x - u + ![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) =
                                (P5332T1ParentRows P j s t).values l) ∧
                                (x - u - (P5332T1ParentRows P j s 0).companion ∈
                                FordVertexDomain P.q ↔
                                t = 0 ∧ Even (s.val + j.val))
    ) := by
  classical
  intro P hq i s h k p p' x ha hb hx hx' j A hAp hAq u B f hdom hbase hdom' hslope hslope'
      hother hstar'
  fin_cases j <;> fin_cases s
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent1Rotation0Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent1Rotation1Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent1Rotation2Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent1Rotation3Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent2Rotation0Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent2Rotation1Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent2Rotation2Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩
  · obtain ⟨t, ht, ht', _, _, hv, hh⟩ := P5332T1Parent2Rotation3Values P A hq hAp hAq
      f B (x-u) hbase hother ((hdom x).mp hx) ((hdom' x).mp hx') hstar'
    exact ⟨t, ht, ht', hv, hh⟩

private theorem hgAt426 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → ((∀ (f : IntegerLatticeFunction), ∀ (z :
            GaussianInt), ∀ (V : Fin 5 → Int), (∀ k : Fin 5, f (z + (![0, 1, -1, (⟨0, 1⟩ :
            GaussianInt), -⟨0, 1⟩] k)) = V k) → (FourNeighborLaplacian f z = V 1 + V 2 + V 3 + V
            4 - 4 * V 0)) → (∀ (s : Fin (4 : ℕ)), ∀ (g : IntegerLatticeFunction), ∀ (x :
            GaussianInt), ∀ (j : Fin (2 : ℕ)), ∀ (u : GaussianInt), ∀ (f :
            IntegerLatticeFunction), (∀ (x : GaussianInt), FourNeighborLaplacian g x =
            FourNeighborLaplacian f (x - u)) → (∀ (t : ℤ), ((0 : ℤ) ≤ t) → ((t < (↑(![P.q₁, P.q₂]
            j) : ℤ)) → ((∀ (l : Fin (5 : ℕ)), f (x - u + ![(0 : ℤ√(-1 : ℤ)), (1 : ℤ√(-1 : ℤ)),
            (-1 : ℤ√(-1 : ℤ)), (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)] l) = (P5332T1ParentRows P j s t).values l) → (FourNeighborLaplacian g
            x = if t = 0 ∧ Even (s.val+j.val) then 0 else 1)))))) ) := by
  classical
  intro P hq lapValues s g x j u f hlap t ht ht' hv
  rw [hlap x, lapValues f (x-u) _ hv]
  exact P5332T1ParentRounding P hq j s t ht ht'

end FordTerminalStencilGeometry

theorem FordTerminalWebStencilLedger (P : FordFareyParameter) (hq : 1 < P.q) :
    let q := FordRecursiveQuadruple P
    (∀ (i : Fin 3) (e : Bool) (T T' : ProtoTile)
        (h h' : PartialOdometer) (p p' : ℝ × ℝ)
        (g : IntegerLatticeFunction) (x : GaussianInt),
      TileOdometer (q 0) T h → TileOdometer (q 0) T' h' →
      PartialOdometerSlope h = some p →
      PartialOdometerSlope h' = some p' →
      TileCentroid T' - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) →
      p'.1 - p.1 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q 0) (q i.succ)).re →
      p'.2 - p.2 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q 0) (q i.succ)).im →
      OdometerCompatibility h h' →
      GlobalOdometerExtends g h → GlobalOdometerExtends g h' →
      x ∈ h.domain → x ∈ h'.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h.domain ∨ y ∈ h'.domain) →
      ((∀ s, s = x ∨ s = x - 1 ∨ s = x - ⟨0, 1⟩ ∨
            s = x - 1 - ⟨0, 1⟩ → s ∈ T.cells ∨ s ∈ T'.cells) →
          FourNeighborLaplacian g x = 1) ∧
      (¬ (∀ s, s = x ∨ s = x - 1 ∨ s = x - ⟨0, 1⟩ ∨
            s = x - 1 - ⟨0, 1⟩ → s ∈ T.cells ∨ s ∈ T'.cells) →
          FourNeighborLaplacian g x = 0)) ∧
    ∀ (i : Fin 3) (s : Fin 4) (T₀ Tᵢ : ProtoTile)
        (h₀ hᵢ : PartialOdometer) (p₀ pᵢ : ℝ × ℝ)
        (g : IntegerLatticeFunction) (x : GaussianInt),
      0 < (q i.succ).1 →
      TileOdometer (q 0) T₀ h₀ → TileOdometer (q i.succ) Tᵢ hᵢ →
      PartialOdometerSlope h₀ = some p₀ →
      PartialOdometerSlope hᵢ = some pᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
             BandVectors.1 (q 0) (q i.succ))) →
      pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).1 →
      pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).2 →
      OdometerCompatibility h₀ hᵢ →
      GlobalOdometerExtends g h₀ → GlobalOdometerExtends g hᵢ →
      x ∈ h₀.domain → x ∈ hᵢ.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h₀.domain ∨ y ∈ hᵢ.domain) →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0))
      let UR := TileTranslation T₀ uR
      (x ∈ FootprintVertices UR → FourNeighborLaplacian g x = 0) ∧
      (x ∉ FootprintVertices UR → FourNeighborLaplacian g x = 1) := by
-- BODY
  classical
  dsimp only
  have vectors :
    let q := FordRecursiveQuadruple P
    (∀ j : Fin 3,
      BandVectors.1 (q 0) (q j.succ) = (P5332T1RightRows P j 0).displacement ∧
      BandVectors.2 (q 0) (q j.succ) = (P5332T1RightRows P j 0).linear) ∧
    ∀ (j : Fin 2) (k : Fin 4),
      let i : Fin 3 := ⟨j.val, by omega⟩
      let R := P5332T1ParentRows P j k 0
      (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ k.val *
            (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) =
        (((((![P.q₁, P.q₂] j : Nat) : ℝ) - P.q) / 2 + R.displacement.re),
         ((((![P.q₁, P.q₂] j : Nat) : ℝ) - P.q) / 2 + R.displacement.im)) ∧
      (1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ k.val *
            (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))) =
        (((((![P.p₁, P.p₂] j : Int) : ℝ) - P.p) / 2 + R.linear.re),
         ((((![P.p₁, P.p₂] j : Int) : ℝ) - P.p) / 2 + R.linear.im)) ∧
      (⟨0, 1⟩ : GaussianInt) ^ k.val *
        (if Even k.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0)) = R.companion := P5332T1VectorPlacements P hq
  have lapValues (f : IntegerLatticeFunction) (z : GaussianInt) (V : Fin 5 → Int)
      (hV : ∀ k : Fin 5,
        f (z + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k)) = V k) :
      FourNeighborLaplacian f z = V 1 + V 2 + V 3 + V 4 - 4 * V 0 :=
          FordTerminalStencilGeometry.lapValues f z V hV
  have positive : ∀ (i : Fin 3) (T T' : ProtoTile)
      (h h' : PartialOdometer) (p p' : ℝ × ℝ)
      (g : IntegerLatticeFunction) (x : GaussianInt),
      TileOdometer (FordRecursiveQuadruple P 0) T h →
      TileOdometer (FordRecursiveQuadruple P 0) T' h' →
      PartialOdometerSlope h = some p → PartialOdometerSlope h' = some p' →
      TileCentroid T' - TileCentroid T =
        GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)) →
      p'.1 - p.1 = (BandVectors.2 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)).re →
      p'.2 - p.2 = (BandVectors.2 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)).im →
      GlobalOdometerExtends g h → GlobalOdometerExtends g h' →
      x ∈ h.domain → x ∈ h'.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h.domain ∨ y ∈ h'.domain) →
      ((∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
          z = x - 1 - ⟨0, 1⟩ → z ∈ T.cells ∨ z ∈ T'.cells) →
        FourNeighborLaplacian g x = 1) ∧
      (¬ (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
          z = x - 1 - ⟨0, 1⟩ → z ∈ T.cells ∨ z ∈ T'.cells) →
        FourNeighborLaplacian g x = 0) := FordTerminalStencilGeometry.positive P hq vectors
            lapValues
  constructor
  · intro i e T U h k p p' g x hT hU hp hp' hc ha hb _ he he' hx hx' hstar
    cases e
    · have hc' : TileCentroid T - TileCentroid U =
          GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P 0)
            (FordRecursiveQuadruple P i.succ)) := FordTerminalStencilGeometry.hc' P i T U hc
      have ha' : p.1 - p'.1 = (BandVectors.2 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)).re := FordTerminalStencilGeometry.ha'At320 P i p p' ha
      have hb' : p.2 - p'.2 = (BandVectors.2 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)).im := FordTerminalStencilGeometry.hb' P i p p' hb
      have hs : ∀ y, y = x ∨ y = x+1 ∨ y = x-1 ∨ y = x+⟨0,1⟩ ∨ y = x-⟨0,1⟩ →
          y ∈ k.domain ∨ y ∈ h.domain := FordTerminalStencilGeometry.hs h k x hstar
      simpa only [or_comm] using positive i U T k h p' p g x hU hT hp' hp
        hc' ha' hb' he' he hx' hx hs
    · exact positive i T U h k p p' g x hT hU hp hp'
        (by simpa using hc) (by simpa using ha) (by simpa using hb) he he' hx hx' hstar
  · intro i s T U h k p p' g x hpos hT hU hp hp' hc ha hb _ he he' hx hx' hstar
    have hi : i.val < 2 := FordTerminalStencilGeometry.hiAt337 P i s p p' hpos ha hb
    let j : Fin 2 := ⟨i.val, hi⟩
    have hij : (⟨j.val, by omega⟩ : Fin 3) = i := rfl
    obtain ⟨hqr, _, hqs, _, hredr, hreds, _⟩ := P5130T5ParentArithmetic P hq
    obtain ⟨A, hAp, hAq, hAc⟩ : ∃ A : FordFareyParameter,
        A.p = (![P.p₁,P.p₂] j : Int) ∧ A.q = (![P.q₁,P.q₂] j : Nat) ∧
        FordCircleCoordinate A.p A.q = FordRecursiveQuadruple P i.succ := by
      fin_cases i
      · obtain ⟨A, hA, _⟩ := FordFareyParentsExist P.p₁ P.q₁ hqr hredr
        exact ⟨A, hA.1, hA.2, by simp [FordRecursiveQuadruple, hA.1, hA.2, hqr.ne']⟩
      · obtain ⟨A, hA, _⟩ := FordFareyParentsExist P.p₂ P.q₂ hqs hreds
        exact ⟨A, hA.1, hA.2, by simp [FordRecursiveQuadruple, hA.1, hA.2]⟩
      · change 2 < 2 at hi
        omega
    obtain ⟨u, d, a, B, f, hdom, hdom', hcell, hcell', hfoot,
      hcent, hslope, hslope', hbase, hother, hlap⟩ :=
      P5332T1LiteralNormalization P A T U h k p p' g hT (by rw [hAc]; exact hU)
        hp hp' he he'
    have vv := vectors.2 j s
    dsimp only at vv
    rw [hij] at vv
    have hd : d = (P5332T1ParentRows P j s 0).displacement :=
        FordTerminalStencilGeometry.hdAt363 P i s T U hc hi A hAq d hcent vv
    have ha' : a = (P5332T1ParentRows P j s 0).linear := FordTerminalStencilGeometry.ha'At375 P
        i s p p' ha hb hi A hAp a hslope hslope' vv
    subst d
    subst a
    have hstar' : ∀ l : Fin 5,
        x-u + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l) ∈ FordVertexDomain P.q ∨
        x-u + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l) -
          (P5332T1ParentRows P j s 0).displacement ∈ FordVertexDomain A.q :=
              FordTerminalStencilGeometry.hstar'At385 P i s h k x hstar hi A u hdom hdom'
    clear hij
    clear_value j
    have source : ∃ t : Int, 0 ≤ t ∧ t < ((![P.q₁,P.q₂] j : Nat) : Int) ∧
        (∀ l : Fin 5, f (x-u + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l)) =
          (P5332T1ParentRows P j s t).values l) ∧
        (x-u - (P5332T1ParentRows P j s 0).companion ∈ FordVertexDomain P.q ↔
          t = 0 ∧ Even (s.val+j.val)) := FordTerminalStencilGeometry.sourceAt395 P hq i s h k
              p p' x ha hb hx hx' j A hAp hAq u B f hdom hbase hdom' hslope
              hslope' hother hstar'
    obtain ⟨t, ht, ht', hv, hh⟩ := source
    have hg : FourNeighborLaplacian g x =
        if t = 0 ∧ Even (s.val+j.val) then 0 else 1 := FordTerminalStencilGeometry.hgAt426 P hq
            lapValues s g x j u f hlap t ht ht' hv
    have mark : x ∈ FootprintVertices (TileTranslation T
        ((⟨0,1⟩ : GaussianInt)^s.val *
          (if Even s.val then BandVectors.1 (FordRecursiveQuadruple P 0)
              (FordRecursiveQuadruple P i.succ)
            else BandVectors.1 (FordRecursiveQuadruple P i.succ)
              (FordRecursiveQuadruple P 0)))) ↔ t = 0 ∧ Even (s.val+j.val) :=
by
      rw [hfoot, vv.2.2]
      exact hh
    constructor
    · intro hm
      rw [hg, ite_eq_left (mark.mp hm)]
    · intro hm
      rw [hg, ite_eq_right (fun h => hm (mark.mpr h))]

end ApollonianSuperharmonic

end
