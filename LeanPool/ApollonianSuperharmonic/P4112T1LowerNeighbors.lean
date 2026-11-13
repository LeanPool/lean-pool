/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordInteriorSquareCoordinates

public import LeanPool.ApollonianSuperharmonic.P4112T1PathGeometry

/-!
# P4112T1LowerNeighbors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic


-- [TABLET NODE: P4112T1LowerNeighbors]
namespace LowerNeighborGeometry

private theorem hq1pos :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((2 : ℕ) < P.q) → (0 < P.q₁)
    ) := by
  classical
  intro P hP
  by_contra h
  have hz : P.q₁ = 0 := by omega
  have hd := P.det₁
  rw [hz] at hd
  simp only [Nat.cast_zero, zero_mul] at hd
  by_cases hp : P.p₁ ≤ 0
  · have hqnonneg : 0 ≤ (P.q : Int) := by omega
    have : P.p₁ * (P.q : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hqnonneg
    omega
  · have hp' : 1 ≤ P.p₁ := by omega
    nlinarith

private theorem hneq :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((2 : ℕ) < P.q) → ((0 < P.q₁) → ((P.p₁ * (P.q₂ : Int) - (P.q₁
            : Int) * P.p₂ = 1) → ((P.q = P.q₁ + P.q₂) → (P.q₁ ≠ P.q₂))))
    ) := by
  classical
  intro P hP hq1pos hcross hsum heq
  have hm : (P.q₁ : Int) * (P.p₁ - P.p₂) = 1 := by
    rw [heq] at hcross
    nlinarith [hcross]
  have hd : (P.q₁ : Int) ∣ 1 := ⟨P.p₁ - P.p₂, hm.symm⟩
  have hu : (P.q₁ : Int) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le P.q₁)) hd
  omega

private abbrev squareCoordinates := ApollonianSuperharmonic.FordInteriorSquareCoordinates.membership

private theorem d_on_path :
    (by
      classical
      exact ∀ (P : FordFareyParameter), (2 < P.q) →
        let B := P4062T1RemainderPaths P
        let d : GaussianInt → Nat := fun x =>
          let a := @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _)
            (B 0).2 (B 1).2
          (x.re - a.re).natAbs + (x.im - a.im).natAbs
        ∀ (j : Fin 2) (z : GaussianInt), z ∈ (B j).1 →
          d z = (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs
    ) := by
  classical
  intro P hP B d j z hz
  have hgeom := P4112T1PathGeometry P hP
  fin_cases j
  · change z ∈ (P4062T1RemainderPaths P 0).1 at hz
    simp [d, B, hz]
  · change z ∈ (P4062T1RemainderPaths P 1).1 at hz
    have hdisj := hgeom.2.1
    have hnot : z ∉ (B 0).1 := by
      intro hz0
      exact Finset.disjoint_left.mp hdisj hz0 hz
    simp [d, B, hnot]

private theorem neighbor_filter :
    (by
      classical
      exact
        ∀ (S : Finset GaussianInt), ∀ (x : GaussianInt), ∀ (ρ : GaussianInt → ℕ), ({y ∈ S |
            FourNeighborAdjacent y x ∧ ρ y < ρ x} : Finset GaussianInt) = ({y ∈
            {x + (1 : GaussianInt), x - (1 : GaussianInt), x + ⟨(0 : ℤ), (1 : ℤ)⟩, x - ⟨(0 : ℤ),
            (1 : ℤ)⟩} | y ∈ S ∧ ρ y < ρ x} : Finset GaussianInt)
    ) := by
  classical
  intro S x ρ
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, hadj, hdist⟩
    refine ⟨?_, ⟨hy, hdist⟩⟩
    rcases hadj with h | h | h | h
    · right; left
      rw [h]
      simp
    · left
      rw [h]
      simp
    · right; right; right
      rw [h]
      simp
    · right; right; left
      rw [h]
      simp
  · rintro ⟨hycan, ⟨hy, hdist⟩⟩
    refine ⟨hy, ?_, hdist⟩
    rcases hycan with hy | hy | hy | hy <;> subst y <;>
      simp [FourNeighborAdjacent]

private theorem count_eq :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let d : GaussianInt → Nat := fun x =>
          let a := @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _)
              (B 0).2 (B 1).2
          (x.re-a.re).natAbs + (x.im-a.im).natAbs
        (∀ (j : Fin 2), ∀ (z : GaussianInt), (z ∈ (B j).1) → (d z = (z.re-(B j).2.re).natAbs +
            (z.im-(B j).2.im).natAbs)) → ((∀ (S : Finset GaussianInt), ∀ (x : GaussianInt), ∀ (ρ
            : GaussianInt → Nat), S.filter (fun y => FourNeighborAdjacent y x ∧ ρ y < ρ x) =
            ({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ S
            ∧ ρ y < ρ x)) → (
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (j : Fin (2 : ℕ)), ∀ x ∈ (B j).1, ({y ∈ (B j).1 | FourNeighborAdjacent y x ∧ d y < d x}
            : Finset GaussianInt).card = ({y ∈ {x + (1 : GaussianInt), x - (1 : GaussianInt),
            x + ⟨(0 : ℤ), (1 : ℤ)⟩, x - ⟨(0 : ℤ), (1 : ℤ)⟩} | y ∈ (B j).1 ∧ rootDist j y <
            rootDist j x} : Finset GaussianInt).card))
    ) := by
  classical
  intro P B d d_on_path neighbor_filter rootDist j x hx
  have hcongr :
      (B j).1.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x) =
        (B j).1.filter (fun y => FourNeighborAdjacent y x ∧
          rootDist j y < rootDist j x) := by
    apply Finset.filter_congr
    intro y hy
    rw [d_on_path j y hy, d_on_path j x hx]
  rw [hcongr, neighbor_filter]

private theorem root_candidate_empty :
    (by
      classical
      exact
        ∀ (S : Finset GaussianInt),
          ∀ (ρ : GaussianInt → ℕ),
            ∀ (x : GaussianInt),
              ρ x = (0 : ℕ) →
                ({y ∈
                        {x + (1 : GaussianInt), x - (1 : GaussianInt),
                          x + ⟨(0 : ℤ), (1 : ℤ)⟩, x - ⟨(0 : ℤ), (1 : ℤ)⟩} |
                      y ∈ S ∧ ρ y < ρ x} :
                    Finset GaussianInt) =
                  ∅
    ) := by
  classical
  intro S ρ x hz
  ext y
  simp only [Finset.mem_filter, Finset.notMem_empty]
  constructor
  · rintro ⟨_, _, hlt⟩
    rw [hz] at hlt
    omega
  · intro h
    contradiction

private theorem hpredAt281 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (z :
            GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q : Int)-1 ∧ 1 ≤
            z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (P.q₂ < P.q₁) → ((x.re = (↑P.q₁ :
            ℤ) ∧ x.im ≤ (↑P.q₂ : ℤ)) → ((x.re = (P.q₁ : Int)) → ((1 ≤ x.im) → ((x.im < (P.q₂ :
            Int)) → (x + ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ :
            Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))))))))))
    ) := by
  classical
  intro P hq1pos hsum squareCoordinates x horder harm hr hlo hhi
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x + ⟨0, 1⟩)).mpr
    simp only [Zsqrtd.re_add, Zsqrtd.im_add]
    norm_num
    constructor <;> omega
  · left
    constructor
    · simp [Zsqrtd.re_add, hr]
    · simp [Zsqrtd.im_add]
      omega

private theorem hpredDistAt295 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), ((B (0 : Fin (2 : ℕ))).2 = ⟨(↑P.q₁ : ℤ), (↑P.q₂ : ℤ)⟩) → ((x.re =
            (P.q₁ : Int)) → ((x.im < (P.q₂ : Int)) → (rootDist 0 (x + ⟨0, 1⟩) < rootDist 0 x)))
    ) := by
  classical
  intro P B rootDist x hb0root hr hhi
  have ha : 0 ≤ (P.q₂ : Int) - (x.im + 1) := by omega
  have hab : (P.q₂ : Int) - (x.im + 1) < (P.q₂ : Int) - x.im := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hrev1 : x.im + 1 - (P.q₂ : Int) = -((P.q₂ : Int) - (x.im + 1)) := by omega
  have hrev2 : x.im - (P.q₂ : Int) = -((P.q₂ : Int) - x.im) := by omega
  simp only [rootDist, hb0root, Zsqrtd.re_add, Zsqrtd.im_add, hr]
  simp only [Int.add_zero, sub_self, Int.natAbs_zero, zero_add]
  rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
  exact hn

private theorem hnotRightAt305 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.re = (P.q₁ : Int)) → ((x.im < (P.q₂ :
            Int)) → (x + 1 ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int)
            ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))))
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_add, hr] at hz
  · simp [Zsqrtd.im_add] at hz
    omega

private theorem hnotLeftAt315 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.re = (P.q₁ : Int)) → ((x.im < (P.q₂ :
            Int)) → (x - 1 ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int)
            ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))))
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_sub, hr] at hz
  · simp [Zsqrtd.im_sub] at hz
    omega

private theorem hnotPredAt325 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), ((B (0 : Fin (2 : ℕ))).2 = ⟨(↑P.q₁ : ℤ), (↑P.q₂ : ℤ)⟩) → ((x.re =
            (P.q₁ : Int)) → ((x.im < (P.q₂ : Int)) → (¬ rootDist 0 (x - ⟨0, 1⟩) < rootDist 0 x)))
    ) := by
  classical
  intro P B rootDist x hb0root hr hhi
  have ha : 0 ≤ (P.q₂ : Int) - x.im := by omega
  have hab : (P.q₂ : Int) - x.im < (P.q₂ : Int) - (x.im - 1) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hn' : rootDist 0 x < rootDist 0 (x - ⟨0, 1⟩) := by
    have hrev1 : x.im - (P.q₂ : Int) = -((P.q₂ : Int) - x.im) := by omega
    have hrev2 : x.im - 1 - (P.q₂ : Int) =
        -((P.q₂ : Int) - (x.im - 1)) := by omega
    simp only [rootDist, hb0root, Zsqrtd.re_sub, Zsqrtd.im_sub, hr]
    simp only [Int.sub_zero, sub_self, Int.natAbs_zero, zero_add]
    rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
    exact hn
  omega

private theorem hsetAt338 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x + ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re =
            (P.q₁ : Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))) →
            ((rootDist 0 (x + ⟨0, 1⟩) < rootDist 0 x) → ((x + 1 ∉ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ :
            Int) ∧ (P.q₁ : Int) ≤ z.re))) → ((x - 1 ∉ (P4062T1InteriorSquare P.q).filter (fun z
            => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int)
            ≤ z.re))) → ((¬ rootDist 0 (x - ⟨0, 1⟩) < rootDist 0 x) → ((({x + 1, x - 1, x + ⟨0,
            1⟩, x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ :
            Int) ∧ (P.q₁ : Int) ≤ z.re)) ∧ rootDist 0 y < rootDist 0 x)) = {x + ⟨0, 1⟩})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotRight hnotLeft hnotPred
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · subst y
      exact (hnotRight (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotLeft (Finset.mem_filter.mpr hmem)).elim
    · exact hy
    · subst y
      exact (hnotPred hdist).elim
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

private theorem hpredAt376 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (z :
            GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q : Int)-1 ∧ 1 ≤
            z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (x.im = (↑P.q₂ : ℤ) ∧ (↑P.q₁ : ℤ)
            ≤ x.re) → ((x.im = (P.q₂ : Int)) → ((x.re < (P.q : Int)) → (((P.q₁ : Int) < x.re) →
            (x - 1 ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤
            (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re)))))))))
    ) := by
  classical
  intro P hq1pos hsum squareCoordinates x harm hr hhi hgt
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x - 1)).mpr
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
    norm_num
    constructor <;> omega
  · right
    constructor
    · simp [Zsqrtd.im_sub, hr]
    · simp [Zsqrtd.re_sub]
      omega

private theorem hnotRightAt398 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), ((B (0 : Fin (2 : ℕ))).2 = ⟨(↑P.q₁ : ℤ), (↑P.q₂ : ℤ)⟩) → ((x.im =
            (P.q₂ : Int)) → (((P.q₁ : Int) < x.re) → (¬ rootDist 0 (x + 1) < rootDist 0 x)))
    ) := by
  classical
  intro P B rootDist x hb0root hr hgt
  have ha : 0 ≤ x.re - (P.q₁ : Int) := by omega
  have hab : x.re - (P.q₁ : Int) < x.re + 1 - (P.q₁ : Int) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hn' : rootDist 0 x < rootDist 0 (x + 1) := by
    simp only [rootDist, hb0root, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, hr]
    simp only [Int.add_zero, sub_self,
      Int.natAbs_zero]
    exact hn
  omega

private theorem hnotUpAt409 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.im = (P.q₂ : Int)) → (((P.q₁ : Int) <
            x.re) → (x + ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ :
            Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))))
    ) := by
  classical
  intro P x hr hgt hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_add] at hz
    omega
  · simp [Zsqrtd.im_add, hr] at hz

private theorem hnotDownAt419 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.im = (P.q₂ : Int)) → (((P.q₁ : Int) <
            x.re) → (x - ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ :
            Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))))
    ) := by
  classical
  intro P x hr hgt hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_sub] at hz
    omega
  · simp [Zsqrtd.im_sub, hr] at hz

private theorem hsetAt429 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x - 1 ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re =
            (P.q₁ : Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))) →
            ((rootDist 0 (x - 1) < rootDist 0 x) → ((¬ rootDist 0 (x + 1) < rootDist 0 x) → ((x +
            ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤
            (P.q₂ : Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))) → ((x - ⟨0, 1⟩ ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₂ :
            Int)) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re))) → ((({x + 1, x - 1, x + ⟨0, 1⟩,
            x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₂ : Int)) ∨ (z.im = (P.q₂ :
            Int) ∧ (P.q₁ : Int) ≤ z.re)) ∧ rootDist 0 y < rootDist 0 x)) = {x - 1})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotRight hnotUp hnotDown
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · subst y
      exact (hnotRight hdist).elim
    · exact hy
    · subst y
      exact (hnotUp (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotDown (Finset.mem_filter.mpr hmem)).elim
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

private theorem hpredAt476 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (z :
            GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q : Int)-1 ∧ 1 ≤
            z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (P.q₁ < P.q₂) → ((x.re = (↑P.q₁ :
            ℤ) ∧ x.im ≤ (↑P.q₁ : ℤ)) → ((x.re = (P.q₁ : Int)) → ((1 ≤ x.im) → ((x.im < (P.q₁ :
            Int)) → (x + ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ :
            Int) ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)))))))))))
    ) := by
  classical
  intro P hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x + ⟨0, 1⟩)).mpr
    simp only [Zsqrtd.re_add, Zsqrtd.im_add]
    norm_num
    constructor <;> omega
  · left
    constructor
    · simp [Zsqrtd.re_add, hr]
    · simp [Zsqrtd.im_add]
      omega

private theorem hpredDistAt490 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          let B := P4062T1RemainderPaths P;
          let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
            (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
          ∀ (x : GaussianInt),
            (B (0 : Fin (2 : ℕ))).2 = ⟨(↑P.q₁ : ℤ), (↑P.q₁ : ℤ)⟩ →
              x.re = (P.q₁ : Int) →
                x.im < (P.q₁ : Int) → rootDist 0 (x + ⟨0, 1⟩) < rootDist 0 x
    ) := by
  classical
  intro P B rootDist x hb0root hr hhi
  have ha : 0 ≤ (P.q₁ : Int) - (x.im + 1) := by omega
  have hab : (P.q₁ : Int) - (x.im + 1) < (P.q₁ : Int) - x.im := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hrev1 : x.im + 1 - (P.q₁ : Int) = -((P.q₁ : Int) - (x.im + 1)) := by omega
  have hrev2 : x.im - (P.q₁ : Int) = -((P.q₁ : Int) - x.im) := by omega
  simp only [rootDist, hb0root, Zsqrtd.re_add, Zsqrtd.im_add,
    hr]
  simp only [Int.add_zero, sub_self, Int.natAbs_zero, zero_add]
  rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
  exact hn

private theorem hnotRightAt501 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (x : GaussianInt),
            x.re = (P.q₁ : Int) →
              x.im < (P.q₁ : Int) →
                x + 1 ∉
                  (P4062T1InteriorSquare P.q).filter fun z =>
                    z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int) ∨
                      z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_add, hr] at hz
  · simp [Zsqrtd.im_add] at hz
    omega

private theorem hnotLeftAt511 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (x : GaussianInt),
            x.re = (P.q₁ : Int) →
              x.im < (P.q₁ : Int) →
                x - 1 ∉
                  (P4062T1InteriorSquare P.q).filter fun z =>
                    z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int) ∨
                      z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_sub, hr] at hz
  · simp [Zsqrtd.im_sub] at hz
    omega

private theorem hnotPredAt521 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          let B := P4062T1RemainderPaths P;
          let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
            (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
          ∀ (x : GaussianInt),
            (B (0 : Fin (2 : ℕ))).2 = ⟨(↑P.q₁ : ℤ), (↑P.q₁ : ℤ)⟩ →
              x.re = (P.q₁ : Int) →
                x.im < (P.q₁ : Int) → ¬rootDist 0 (x - ⟨0, 1⟩) < rootDist 0 x
    ) := by
  classical
  intro P B rootDist x hb0root hr hhi
  have ha : 0 ≤ (P.q₁ : Int) - x.im := by omega
  have hab : (P.q₁ : Int) - x.im < (P.q₁ : Int) - (x.im - 1) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hrev1 : x.im - (P.q₁ : Int) = -((P.q₁ : Int) - x.im) := by omega
  have hrev2 : x.im - 1 - (P.q₁ : Int) =
      -((P.q₁ : Int) - (x.im - 1)) := by omega
  have hn' : rootDist 0 x < rootDist 0 (x - ⟨0, 1⟩) := by
    simp only [rootDist, hb0root, Zsqrtd.re_sub, Zsqrtd.im_sub,
      hr]
    simp only [Int.sub_zero, sub_self, Int.natAbs_zero, zero_add]
    rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
    exact hn
  omega

private theorem hsetAt535 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x + ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re =
            (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)))) →
            ((rootDist 0 (x + ⟨0, 1⟩) < rootDist 0 x) → ((x + 1 ∉ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ :
            Int) ∧ z.re ≤ (P.q₁ : Int)))) → ((x - 1 ∉ (P4062T1InteriorSquare P.q).filter (fun z
            => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁
            : Int)))) → ((¬ rootDist 0 (x - ⟨0, 1⟩) < rootDist 0 x) → ((({x + 1, x - 1, x + ⟨0,
            1⟩, x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ :
            Int) ∧ z.re ≤ (P.q₁ : Int))) ∧ rootDist 0 y < rootDist 0 x)) = {x + ⟨0, 1⟩})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotRight hnotLeft hnotPred
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · subst y
      exact (hnotRight (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotLeft (Finset.mem_filter.mpr hmem)).elim
    · exact hy
    · subst y
      exact (hnotPred hdist).elim
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

private theorem hpredAt570 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (z :
            GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q : Int)-1 ∧ 1 ≤
            z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (P.q₁ < P.q₂) → ((x.im = (↑P.q₁ :
            ℤ) ∧ x.re ≤ (↑P.q₁ : ℤ)) → ((x.im = (P.q₁ : Int)) → ((1 ≤ x.re) → ((x.re < (P.q₁ :
            Int)) → (x + 1 ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int)
            ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)))))))))))
    ) := by
  classical
  intro P hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x + 1)).mpr
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
    constructor <;> omega
  · right
    constructor
    · simp [Zsqrtd.im_add, hr]
    · simp [Zsqrtd.re_add, Zsqrtd.re_one]
      omega

private theorem hpredDistAt583 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          let B := P4062T1RemainderPaths P;
          let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
            (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
          ∀ (x : GaussianInt),
            (B (0 : Fin (2 : ℕ))).2 = ⟨(↑P.q₁ : ℤ), (↑P.q₁ : ℤ)⟩ →
              x.im = (P.q₁ : Int) →
                x.re < (P.q₁ : Int) → rootDist 0 (x + 1) < rootDist 0 x
    ) := by
  classical
  intro P B rootDist x hb0root hr hhi
  have ha : 0 ≤ (P.q₁ : Int) - (x.re + 1) := by omega
  have hab : (P.q₁ : Int) - (x.re + 1) < (P.q₁ : Int) - x.re := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hrev1 : x.re + 1 - (P.q₁ : Int) = -((P.q₁ : Int) - (x.re + 1)) := by omega
  have hrev2 : x.re - (P.q₁ : Int) = -((P.q₁ : Int) - x.re) := by omega
  simp only [rootDist, hb0root, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_one, Zsqrtd.im_one, hr]
  simp only [Int.add_zero, sub_self, Int.natAbs_zero]
  rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
  exact hn

private theorem hnotLeftAt594 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          let B := P4062T1RemainderPaths P;
          let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
            (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
          ∀ (x : GaussianInt),
            (B (0 : Fin (2 : ℕ))).2 = ⟨(↑P.q₁ : ℤ), (↑P.q₁ : ℤ)⟩ →
              x.im = (P.q₁ : Int) →
                x.re < (P.q₁ : Int) → ¬rootDist 0 (x - 1) < rootDist 0 x
    ) := by
  classical
  intro P B rootDist x hb0root hr hhi
  have ha : 0 ≤ (P.q₁ : Int) - x.re := by omega
  have hab : (P.q₁ : Int) - x.re < (P.q₁ : Int) - (x.re - 1) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hrev1 : x.re - (P.q₁ : Int) = -((P.q₁ : Int) - x.re) := by omega
  have hrev2 : x.re - 1 - (P.q₁ : Int) =
      -((P.q₁ : Int) - (x.re - 1)) := by omega
  have hn' : rootDist 0 x < rootDist 0 (x - 1) := by
    simp only [rootDist, hb0root, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_one, Zsqrtd.im_one, hr]
    simp only [Int.sub_zero, sub_self, Int.natAbs_zero]
    rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
    exact hn
  omega

private theorem hnotUpAt608 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (x : GaussianInt),
            x.im = (P.q₁ : Int) →
              x.re < (P.q₁ : Int) →
                x + ⟨0, 1⟩ ∉
                  (P4062T1InteriorSquare P.q).filter fun z =>
                    z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int) ∨
                      z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_add] at hz
    omega
  · simp [Zsqrtd.im_add, hr] at hz

private theorem hnotDownAt618 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (x : GaussianInt),
            x.im = (P.q₁ : Int) →
              x.re < (P.q₁ : Int) →
                x - ⟨0, 1⟩ ∉
                  (P4062T1InteriorSquare P.q).filter fun z =>
                    z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int) ∨
                      z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_sub] at hz
    omega
  · simp [Zsqrtd.im_sub, hr] at hz

private theorem hsetAt628 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x + 1 ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re =
            (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)))) →
            ((rootDist 0 (x + 1) < rootDist 0 x) → ((¬ rootDist 0 (x - 1) < rootDist 0 x) → ((x +
            ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤
            (P.q₁ : Int)) ∨ (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)))) → ((x - ⟨0, 1⟩ ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ :
            Int)) ∨ (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int)))) → ((({x + 1, x - 1, x + ⟨0, 1⟩,
            x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int)) ∨ (z.im = (P.q₁ :
            Int) ∧ z.re ≤ (P.q₁ : Int))) ∧ rootDist 0 y < rootDist 0 x)) = {x + 1})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotLeft hnotUp hnotDown
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · exact hy
    · subst y
      exact (hnotLeft hdist).elim
    · subst y
      exact (hnotUp (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotDown (Finset.mem_filter.mpr hmem)).elim
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

private theorem hpredAt680 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (z :
            GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q : Int)-1 ∧ 1 ≤
            z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (P.q₂ < P.q₁) → ((x.im = (↑P.q₁ :
            ℤ) ∧ x.re ≤ (↑P.q₂ : ℤ)) → ((x.im = (P.q₁ : Int)) → ((1 ≤ x.re) → ((x.re < (P.q₂ :
            Int)) → (x + 1 ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ : Int)
            ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))))))))))
    ) := by
  classical
  intro P hq1pos hsum squareCoordinates x horder harm hr hlo hhi
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x + 1)).mpr
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
    constructor <;> omega
  · left
    constructor
    · simp [Zsqrtd.im_add, hr]
    · simp [Zsqrtd.re_add, Zsqrtd.re_one]
      omega

private theorem hpredDistAt693 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), ((B (1 : Fin (2 : ℕ))).2 = ⟨(↑P.q₂ : ℤ), (↑P.q₁ : ℤ)⟩) → ((x.im =
            (P.q₁ : Int)) → ((x.re < (P.q₂ : Int)) → (rootDist 1 (x + 1) < rootDist 1 x)))
    ) := by
  classical
  intro P B rootDist x hb1root hr hhi
  have ha : 0 ≤ (P.q₂ : Int) - (x.re + 1) := by omega
  have hab : (P.q₂ : Int) - (x.re + 1) < (P.q₂ : Int) - x.re := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hrev1 : x.re + 1 - (P.q₂ : Int) = -((P.q₂ : Int) - (x.re + 1)) := by omega
  have hrev2 : x.re - (P.q₂ : Int) = -((P.q₂ : Int) - x.re) := by omega
  simp only [rootDist, hb1root, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_one, Zsqrtd.im_one, hr]
  simp only [Int.add_zero, sub_self, Int.natAbs_zero]
  rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
  exact hn

private theorem hnotLeftAt704 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), ((B (1 : Fin (2 : ℕ))).2 = ⟨(↑P.q₂ : ℤ), (↑P.q₁ : ℤ)⟩) → ((x.im =
            (P.q₁ : Int)) → ((x.re < (P.q₂ : Int)) → (¬ rootDist 1 (x - 1) < rootDist 1 x)))
    ) := by
  classical
  intro P B rootDist x hb1root hr hhi
  have ha : 0 ≤ (P.q₂ : Int) - x.re := by omega
  have hab : (P.q₂ : Int) - x.re < (P.q₂ : Int) - (x.re - 1) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hrev1 : x.re - (P.q₂ : Int) = -((P.q₂ : Int) - x.re) := by omega
  have hrev2 : x.re - 1 - (P.q₂ : Int) =
      -((P.q₂ : Int) - (x.re - 1)) := by omega
  have hn' : rootDist 1 x < rootDist 1 (x - 1) := by
    simp only [rootDist, hb1root, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_one, Zsqrtd.im_one, hr]
    simp only [Int.sub_zero, sub_self, Int.natAbs_zero]
    rw [hrev1, Int.natAbs_neg, hrev2, Int.natAbs_neg]
    exact hn
  omega

private theorem hnotUpAt718 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.im = (P.q₁ : Int)) → ((x.re < (P.q₂ :
            Int)) → (x + ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ :
            Int) ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))))
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.im_add, hr] at hz
  · simp [Zsqrtd.re_add] at hz
    omega

private theorem hnotDownAt728 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.im = (P.q₁ : Int)) → ((x.re < (P.q₂ :
            Int)) → (x - ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ :
            Int) ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))))
    ) := by
  classical
  intro P x hr hhi hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.im_sub, hr] at hz
  · simp [Zsqrtd.re_sub] at hz
    omega

private theorem hsetAt738 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x + 1 ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.im =
            (P.q₁ : Int) ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))) →
            ((rootDist 1 (x + 1) < rootDist 1 x) → ((¬ rootDist 1 (x - 1) < rootDist 1 x) → ((x +
            ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧ z.re ≤
            (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))) → ((x - ⟨0, 1⟩ ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₂ :
            Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))) → ((({x + 1, x - 1, x + ⟨0, 1⟩,
            x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ :
            Int) ∧ (P.q₁ : Int) ≤ z.im)) ∧ rootDist 1 y < rootDist 1 x)) = {x + 1})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotLeft hnotUp hnotDown
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · exact hy
    · subst y
      exact (hnotLeft hdist).elim
    · subst y
      exact (hnotUp (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotDown (Finset.mem_filter.mpr hmem)).elim
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

private theorem hpredAt775 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q : Nat), ∀ (z :
            GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q : Int)-1 ∧ 1 ≤
            z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (x.re = (↑P.q₂ : ℤ) ∧ (↑P.q₁ : ℤ)
            ≤ x.im) → ((x.re = (P.q₂ : Int)) → (((P.q₁ : Int) < x.im) → ((x.im < (P.q : Int)) →
            (x - ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧
            z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im)))))))))
    ) := by
  classical
  intro P hq1pos hsum squareCoordinates x harm hr hlo hhi
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x - ⟨0, 1⟩)).mpr
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
    norm_num
    constructor <;> omega
  · right
    constructor
    · simp [Zsqrtd.re_sub, hr]
    · simp [Zsqrtd.im_sub]
      omega

private theorem hnotUpAt797 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), ((B (1 : Fin (2 : ℕ))).2 = ⟨(↑P.q₂ : ℤ), (↑P.q₁ : ℤ)⟩) → ((x.re =
            (P.q₂ : Int)) → (((P.q₁ : Int) < x.im) → (¬ rootDist 1 (x + ⟨0, 1⟩) < rootDist 1 x)))
    ) := by
  classical
  intro P B rootDist x hb1root hr hlo
  have ha : 0 ≤ x.im - (P.q₁ : Int) := by omega
  have hab : x.im - (P.q₁ : Int) < x.im + 1 - (P.q₁ : Int) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hn' : rootDist 1 x < rootDist 1 (x + ⟨0, 1⟩) := by
    simp only [rootDist, hb1root, Zsqrtd.re_add, Zsqrtd.im_add, hr,
      ]
    simp only [Int.add_zero, sub_self, Int.natAbs_zero, zero_add]
    exact hn
  omega

private theorem hnotRightAt807 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.re = (↑P.q₂ : ℤ) ∧ (↑P.q₁ : ℤ) ≤
            x.im) → ((x.re = (P.q₂ : Int)) → (x + 1 ∉ (P4062T1InteriorSquare P.q).filter (fun z
            => (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int)
            ≤ z.im))))
    ) := by
  classical
  intro P x harm hr hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.im_add, hr] at hz
  · simp [Zsqrtd.re_add] at hz
    omega

private theorem hnotLeftAt817 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.re = (↑P.q₂ : ℤ) ∧ (↑P.q₁ : ℤ) ≤
            x.im) → ((x.re = (P.q₂ : Int)) → (((P.q₁ : Int) < x.im) → (x - 1 ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₂ :
            Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im)))))
    ) := by
  classical
  intro P x harm hr hlo hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.im_sub, hr] at hz
    omega
  · simp [Zsqrtd.re_sub] at hz
    omega

private theorem hsetAt828 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x - ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.im =
            (P.q₁ : Int) ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))) →
            ((rootDist 1 (x - ⟨0, 1⟩) < rootDist 1 x) → ((¬ rootDist 1 (x + ⟨0, 1⟩) < rootDist 1
            x) → ((x + 1 ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧
            z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))) → ((x - 1 ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₂ :
            Int)) ∨ (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im))) → ((({x + 1, x - 1, x + ⟨0, 1⟩,
            x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₂ : Int)) ∨ (z.re = (P.q₂ :
            Int) ∧ (P.q₁ : Int) ≤ z.im)) ∧ rootDist 1 y < rootDist 1 x)) = {x - ⟨0, 1⟩})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotUp hnotRight hnotLeft
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · subst y
      exact (hnotRight (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotLeft (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotUp hdist).elim
    · exact hy
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

private theorem hpredAt877 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((2 : ℕ) < P.q) → ((0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q
            : Nat), ∀ (z : GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q :
            Int)-1 ∧ 1 ≤ z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (P.q₁ < P.q₂) →
            ((x.re = (↑P.q₂ : ℤ) ∧ (↑P.q₂ : ℤ) ≤ x.im) → ((x.re = (P.q₂ : Int)) → (((P.q₂ : Int)
            < x.im) → ((x.im < (P.q : Int)) → (x - ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter
            (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂
            : Int) ≤ z.re)))))))))))
    ) := by
  classical
  intro P hP hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x - ⟨0, 1⟩)).mpr
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
    norm_num
    constructor <;> omega
  · left
    constructor
    · simp [Zsqrtd.re_sub, hr]
    · simp [Zsqrtd.im_sub]
      omega

private theorem hnotUpAt899 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          let B := P4062T1RemainderPaths P;
          let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
            (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
          ∀ (x : GaussianInt),
            (B (1 : Fin (2 : ℕ))).2 = ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩ →
              x.re = (P.q₂ : Int) →
                (P.q₂ : Int) < x.im → ¬rootDist 1 (x + ⟨0, 1⟩) < rootDist 1 x
    ) := by
  classical
  intro P B rootDist x hb1root hr hlo
  have ha : 0 ≤ x.im - (P.q₂ : Int) := by omega
  have hab : x.im - (P.q₂ : Int) < x.im + 1 - (P.q₂ : Int) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hn' : rootDist 1 x < rootDist 1 (x + ⟨0, 1⟩) := by
    simp only [rootDist, hb1root, Zsqrtd.re_add, Zsqrtd.im_add,
      hr]
    simp only [Int.add_zero, sub_self, Int.natAbs_zero, zero_add]
    exact hn
  omega

private theorem hnotRightAt909 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (x : GaussianInt),
            x.re = (P.q₂ : Int) →
              (P.q₂ : Int) < x.im →
                x + 1 ∉
                  (P4062T1InteriorSquare P.q).filter fun z =>
                    z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im ∨
                      z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re
    ) := by
  classical
  intro P x hr hlo hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_add, hr] at hz
  · simp [Zsqrtd.im_add] at hz
    omega

private theorem hnotLeftAt919 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (x : GaussianInt),
            x.re = (P.q₂ : Int) →
              (P.q₂ : Int) < x.im →
                x - 1 ∉
                  (P4062T1InteriorSquare P.q).filter fun z =>
                    z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im ∨
                      z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re
    ) := by
  classical
  intro P x hr hlo hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_sub, hr] at hz
  · simp [Zsqrtd.im_sub] at hz
    omega

private theorem hsetAt929 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x - ⟨0, 1⟩ ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re =
            (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re))) →
            ((rootDist 1 (x - ⟨0, 1⟩) < rootDist 1 x) → ((¬ rootDist 1 (x + ⟨0, 1⟩) < rootDist 1
            x) → ((x + 1 ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₂ : Int) ∧
            (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re))) → ((x - 1 ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤
            z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re))) → ((({x + 1, x - 1, x + ⟨0, 1⟩,
            x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ :
            Int) ∧ (P.q₂ : Int) ≤ z.re)) ∧ rootDist 1 y < rootDist 1 x)) = {x - ⟨0, 1⟩})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotUp hnotRight hnotLeft
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · subst y
      exact (hnotRight (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotLeft (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotUp hdist).elim
    · exact hy
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

private theorem hpredAt966 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((2 : ℕ) < P.q) → ((0 < P.q₁) → ((P.q = P.q₁ + P.q₂) → ((∀ (q
            : Nat), ∀ (z : GaussianInt), z ∈ P4062T1InteriorSquare q ↔ 1 ≤ z.re ∧ z.re ≤ (q :
            Int)-1 ∧ 1 ≤ z.im ∧ z.im ≤ (q : Int)-1) → (∀ (x : GaussianInt), (P.q₁ < P.q₂) →
            ((x.im = (↑P.q₂ : ℤ) ∧ (↑P.q₂ : ℤ) ≤ x.re) → ((x.im = (P.q₂ : Int)) → (((P.q₂ : Int)
            < x.re) → ((x.re < (P.q : Int)) → (x - 1 ∈ (P4062T1InteriorSquare P.q).filter (fun
            z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ :
            Int) ≤ z.re)))))))))))
    ) := by
  classical
  intro P hP hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
  apply Finset.mem_filter.mpr
  constructor
  · apply (squareCoordinates P.q (x - 1)).mpr
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
    constructor <;> omega
  · right
    constructor
    · simp [Zsqrtd.im_sub, hr]
    · simp [Zsqrtd.re_sub, Zsqrtd.re_one]
      omega

private theorem hnotRightAt987 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          let B := P4062T1RemainderPaths P;
          let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
            (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
          ∀ (x : GaussianInt),
            (B (1 : Fin (2 : ℕ))).2 = ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩ →
              x.im = (P.q₂ : Int) →
                (P.q₂ : Int) < x.re → ¬rootDist 1 (x + 1) < rootDist 1 x
    ) := by
  classical
  intro P B rootDist x hb1root hr hlo
  have ha : 0 ≤ x.re - (P.q₂ : Int) := by omega
  have hab : x.re - (P.q₂ : Int) < x.re + 1 - (P.q₂ : Int) := by omega
  have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
  have hn' : rootDist 1 x < rootDist 1 (x + 1) := by
    simp only [rootDist, hb1root, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, hr]
    simp only [Int.add_zero, sub_self, Int.natAbs_zero]
    exact hn
  omega

private theorem hnotUpAt997 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.im = (↑P.q₂ : ℤ) ∧ (↑P.q₂ : ℤ) ≤
            x.re) → ((x.im = (P.q₂ : Int)) → (((P.q₂ : Int) < x.re) → (x + ⟨0, 1⟩ ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤
            z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re)))))
    ) := by
  classical
  intro P x harm hr hlo hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_add, hr] at hz
    omega
  · simp [Zsqrtd.im_add] at hz
    omega

private theorem hnotDownAt1008 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.im = (↑P.q₂ : ℤ) ∧ (↑P.q₂ : ℤ) ≤
            x.re) → ((x.im = (P.q₂ : Int)) → (x - ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter
            (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂
            : Int) ≤ z.re))))
    ) := by
  classical
  intro P x harm hr hz
  simp only [Finset.mem_filter] at hz
  rcases hz with ⟨_, hz | hz⟩
  · simp [Zsqrtd.re_sub, hr] at hz
  · simp [Zsqrtd.im_sub] at hz
    omega

private theorem hsetAt1018 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let B := P4062T1RemainderPaths P
        let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
          (z.re-(B j).2.re).natAbs + (z.im-(B j).2.im).natAbs
        ∀ (x : GaussianInt), (x - 1 ∈ (P4062T1InteriorSquare P.q).filter (fun z => (z.re =
            (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re))) →
            ((rootDist 1 (x - 1) < rootDist 1 x) → ((¬ rootDist 1 (x + 1) < rootDist 1 x) → ((x +
            ⟨0, 1⟩ ∉ (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂
            : Int) ≤ z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re))) → ((x - ⟨0, 1⟩ ∉
            (P4062T1InteriorSquare P.q).filter (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤
            z.im) ∨ (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re))) → ((({x + 1, x - 1, x + ⟨0, 1⟩,
            x - ⟨0, 1⟩} : Finset GaussianInt).filter (fun y => y ∈ (P4062T1InteriorSquare
            P.q).filter (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨ (z.im = (P.q₂ :
            Int) ∧ (P.q₂ : Int) ≤ z.re)) ∧ rootDist 1 y < rootDist 1 x)) = {x - 1})))))
    ) := by
  classical
  intro P B rootDist x hpred hpredDist hnotRight hnotUp hnotDown
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy | hy | hy | hy, hmem, hdist⟩
    · subst y
      exact (hnotRight hdist).elim
    · exact hy
    · subst y
      exact (hnotUp (Finset.mem_filter.mpr hmem)).elim
    · subst y
      exact (hnotDown (Finset.mem_filter.mpr hmem)).elim
  · intro hy
    subst y
    exact ⟨by simp, Finset.mem_filter.mp hpred, hpredDist⟩

end LowerNeighborGeometry

namespace LowerOrderCases

private theorem firstPathAscendingCount :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (0 : ℕ) < P.q₁ →
            P.q = P.q₁ + P.q₂ →
              let B := P4062T1RemainderPaths P;
              let d : GaussianInt → Nat := fun x =>
                let a :=
                  @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _) (B 0).2
                    (B 1).2
                (x.re - a.re).natAbs + (x.im - a.im).natAbs;
              (∀ (q : ℕ),
                  ∀ (z : GaussianInt),
                    z ∈ P4062T1InteriorSquare q ↔
                      (1 : ℤ) ≤ z.re ∧
                        z.re ≤ (↑q : ℤ) - (1 : ℤ) ∧
                          (1 : ℤ) ≤ z.im ∧ z.im ≤ (↑q : ℤ) - (1 : ℤ)) →
                let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
                  (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
                (∀ (j : Fin 2),
                    ∀ (x : GaussianInt),
                      x ∈ (B j).1 →
                        ((B j).1.filter fun y =>
                              FourNeighborAdjacent y x ∧ d y < d x).card =
                          (({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} :
                                Finset GaussianInt).filter
                              fun y => y ∈ (B j).1 ∧ rootDist j y < rootDist j x).card) →
                  (∀ (S : Finset GaussianInt),
                      ∀ (ρ : GaussianInt → ℕ),
                        ∀ (x : GaussianInt),
                          ρ x = (0 : ℕ) →
                            ({y ∈
                                {x + (1 : GaussianInt), x - (1 : GaussianInt),
                                x + ⟨(0 : ℤ), (1 : ℤ)⟩, x - ⟨(0 : ℤ), (1 : ℤ)⟩} |
                                y ∈ S ∧ ρ y < ρ x} :
                                Finset GaussianInt) =
                              ∅) →
                    ∀ (x : GaussianInt),
                      x ∈ (B 0).1 →
                        P.q₂ < P.q₁ →
                          ((B (0 : Fin 2)).1.filter fun y =>
                                FourNeighborAdjacent y x ∧ d y < d x).card =
                            if x = (B (0 : Fin 2)).2 then 0 else 1
    ) := by
  classical
  intro P hq1pos hsum B d squareCoordinates rootDist count_eq root_candidate_empty x hxB horder
  have hb0 : (B 0).1 = (P4062T1InteriorSquare P.q).filter
      (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₂ : Int)) ∨
        (z.im = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.re)) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hb0root : (B 0).2 = (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hxOrig := hxB
  rw [hb0] at hxB
  simp only [Finset.mem_filter] at hxB
  rw [count_eq 0 x hxOrig, hb0]
  rcases hxB with ⟨hsq, harm | harm⟩
  · by_cases hroot : x = (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 0 (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb0root]
      rw [root_candidate_empty _ (rootDist 0) _ hzero]
      simp [hb0root]
    · have hr : x.re = (P.q₁ : Int) := harm.1
      have hlo : 1 ≤ x.im := (squareCoordinates P.q x).mp hsq |>.2.2.1
      have hhi : x.im < (P.q₂ : Int) := by
        have := harm.2
        by_contra hn
        have : (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) = x := by
          ext <;> simp [hr]; omega
        exact hroot this.symm
      have hpred := LowerNeighborGeometry.hpredAt281
                P hq1pos hsum squareCoordinates x horder harm hr hlo hhi
      have hpredDist := LowerNeighborGeometry.hpredDistAt295 P x hb0root hr hhi
      have hnotRight := LowerNeighborGeometry.hnotRightAt305 P x hr hhi
      have hnotLeft := LowerNeighborGeometry.hnotLeftAt315 P x hr hhi
      have hnotPred := LowerNeighborGeometry.hnotPredAt325 P x hb0root hr hhi
      have hset := LowerNeighborGeometry.hsetAt338 P x hpred hpredDist hnotRight hnotLeft
                    hnotPred
      rw [hset]
      simp [hb0root, hroot]
  · by_cases hroot : x = (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 0 (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb0root]
      rw [root_candidate_empty _ (rootDist 0) _ hzero]
      simp [hb0root]
    · have hr : x.im = (P.q₂ : Int) := harm.1
      have hlo : (P.q₁ : Int) ≤ x.re := harm.2
      have hhi : x.re < (P.q : Int) := by
        have hsquare := (squareCoordinates P.q x).mp hsq
        omega
      have hgt : (P.q₁ : Int) < x.re := by
        by_contra hn
        have : x = (⟨(P.q₁ : Int), (P.q₂ : Int)⟩ : GaussianInt) := by
          ext <;> simp [hr]; omega
        exact hroot this
      have hpred := LowerNeighborGeometry.hpredAt376
                P hq1pos hsum squareCoordinates x harm hr hhi hgt
      have hpredDist : rootDist 0 (x - 1) < rootDist 0 x := by
        have ha : 0 ≤ x.re - 1 - (P.q₁ : Int) := by omega
        have hab : x.re - 1 - (P.q₁ : Int) < x.re - (P.q₁ : Int) := by omega
        have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
        simp only [rootDist, hb0root, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_one, Zsqrtd.im_one, hr]
        simp only [Int.sub_zero, sub_self, Int.natAbs_zero]
        exact hn
      have hnotRight := LowerNeighborGeometry.hnotRightAt398 P x hb0root hr hgt
      have hnotUp := LowerNeighborGeometry.hnotUpAt409 P x hr hgt
      have hnotDown := LowerNeighborGeometry.hnotDownAt419 P x hr hgt
      have hset := LowerNeighborGeometry.hsetAt429 P
                    x hpred hpredDist hnotRight hnotUp hnotDown
      rw [hset]
      simp [hb0root, hroot]

private theorem firstPathDescendingCount :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (0 : ℕ) < P.q₁ →
            P.q = P.q₁ + P.q₂ →
              P.q₁ ≠ P.q₂ →
                let B := P4062T1RemainderPaths P;
                let d : GaussianInt → Nat := fun x =>
                  let a :=
                    @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _) (B 0).2
                      (B 1).2
                  (x.re - a.re).natAbs + (x.im - a.im).natAbs;
                (∀ (q : ℕ),
                    ∀ (z : GaussianInt),
                      z ∈ P4062T1InteriorSquare q ↔
                        (1 : ℤ) ≤ z.re ∧
                          z.re ≤ (↑q : ℤ) - (1 : ℤ) ∧
                            (1 : ℤ) ≤ z.im ∧ z.im ≤ (↑q : ℤ) - (1 : ℤ)) →
                  let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
                    (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
                  (∀ (j : Fin 2),
                      ∀ (x : GaussianInt),
                        x ∈ (B j).1 →
                          ((B j).1.filter fun y =>
                                FourNeighborAdjacent y x ∧ d y < d x).card =
                            (({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} :
                                Finset GaussianInt).filter
                                fun y =>
                                y ∈ (B j).1 ∧ rootDist j y < rootDist j x).card) →
                    (∀ (S : Finset GaussianInt),
                        ∀ (ρ : GaussianInt → ℕ),
                          ∀ (x : GaussianInt),
                            ρ x = (0 : ℕ) →
                              ({y ∈
                                {x + (1 : GaussianInt), x - (1 : GaussianInt),
                                x + ⟨(0 : ℤ), (1 : ℤ)⟩, x - ⟨(0 : ℤ), (1 : ℤ)⟩} |
                                y ∈ S ∧ ρ y < ρ x} :
                                Finset GaussianInt) =
                                ∅) →
                      ∀ (x : GaussianInt),
                        x ∈ (B 0).1 →
                          ¬P.q₂ < P.q₁ →
                            ((B (0 : Fin 2)).1.filter fun y =>
                                FourNeighborAdjacent y x ∧ d y < d x).card =
                              if x = (B (0 : Fin 2)).2 then 0 else 1
    ) := by
  classical
  intro P hq1pos hsum hneq B d squareCoordinates rootDist count_eq root_candidate_empty x hxB
      horder
  have horder' : P.q₁ < P.q₂ := by omega
  have hb0 : (B 0).1 = (P4062T1InteriorSquare P.q).filter
      (fun z => (z.re = (P.q₁ : Int) ∧ z.im ≤ (P.q₁ : Int)) ∨
        (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₁ : Int))) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hb0root : (B 0).2 = (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hxOrig := hxB
  rw [hb0] at hxB
  simp only [Finset.mem_filter] at hxB
  rw [count_eq 0 x hxOrig, hb0]
  rcases hxB with ⟨hsq, harm | harm⟩
  · by_cases hroot : x = (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 0 (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb0root]
      rw [root_candidate_empty _ (rootDist 0) _ hzero]
      simp [hb0root]
    · have hr : x.re = (P.q₁ : Int) := harm.1
      have hlo : 1 ≤ x.im := (squareCoordinates P.q x).mp hsq |>.2.2.1
      have hhi : x.im < (P.q₁ : Int) := by
        by_contra hn
        have : (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) = x := by
          ext <;> simp [hr]; omega
        exact hroot this.symm
      have hpred := LowerNeighborGeometry.hpredAt476
                P hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
      have hpredDist := LowerNeighborGeometry.hpredDistAt490 P x hb0root hr hhi
      have hnotRight := LowerNeighborGeometry.hnotRightAt501 P x hr hhi
      have hnotLeft := LowerNeighborGeometry.hnotLeftAt511 P x hr hhi
      have hnotPred := LowerNeighborGeometry.hnotPredAt521 P x hb0root hr hhi
      have hset := LowerNeighborGeometry.hsetAt535 P x hpred hpredDist hnotRight hnotLeft
                    hnotPred
      rw [hset]
      simp [hb0root, hroot]
  · by_cases hroot : x = (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 0 (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb0root]
      rw [root_candidate_empty _ (rootDist 0) _ hzero]
      simp [hb0root]
    · have hr : x.im = (P.q₁ : Int) := harm.1
      have hlo : 1 ≤ x.re := (squareCoordinates P.q x).mp hsq |>.1
      have hhi : x.re < (P.q₁ : Int) := by
        by_contra hn
        have : x = (⟨(P.q₁ : Int), (P.q₁ : Int)⟩ : GaussianInt) := by
          ext <;> simp [hr]; omega
        exact hroot this
      have hpred := LowerNeighborGeometry.hpredAt570
                P hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
      have hpredDist := LowerNeighborGeometry.hpredDistAt583 P x hb0root hr hhi
      have hnotLeft := LowerNeighborGeometry.hnotLeftAt594 P x hb0root hr hhi
      have hnotUp := LowerNeighborGeometry.hnotUpAt608 P x hr hhi
      have hnotDown := LowerNeighborGeometry.hnotDownAt618 P x hr hhi
      have hset := LowerNeighborGeometry.hsetAt628 P
                    x hpred hpredDist hnotLeft hnotUp hnotDown
      rw [hset]
      simp [hb0root, hroot]

private theorem secondPathAscendingCount :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (0 : ℕ) < P.q₁ →
            P.q = P.q₁ + P.q₂ →
              let B := P4062T1RemainderPaths P;
              let d : GaussianInt → Nat := fun x =>
                let a :=
                  @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _) (B 0).2
                    (B 1).2
                (x.re - a.re).natAbs + (x.im - a.im).natAbs;
              (∀ (q : ℕ),
                  ∀ (z : GaussianInt),
                    z ∈ P4062T1InteriorSquare q ↔
                      (1 : ℤ) ≤ z.re ∧
                        z.re ≤ (↑q : ℤ) - (1 : ℤ) ∧
                          (1 : ℤ) ≤ z.im ∧ z.im ≤ (↑q : ℤ) - (1 : ℤ)) →
                let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
                  (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
                (∀ (j : Fin 2),
                    ∀ (x : GaussianInt),
                      x ∈ (B j).1 →
                        ((B j).1.filter fun y =>
                              FourNeighborAdjacent y x ∧ d y < d x).card =
                          (({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} :
                                Finset GaussianInt).filter
                              fun y => y ∈ (B j).1 ∧ rootDist j y < rootDist j x).card) →
                  (∀ (S : Finset GaussianInt),
                      ∀ (ρ : GaussianInt → ℕ),
                        ∀ (x : GaussianInt),
                          ρ x = (0 : ℕ) →
                            ({y ∈
                                {x + (1 : GaussianInt), x - (1 : GaussianInt),
                                x + ⟨(0 : ℤ), (1 : ℤ)⟩, x - ⟨(0 : ℤ), (1 : ℤ)⟩} |
                                y ∈ S ∧ ρ y < ρ x} :
                                Finset GaussianInt) =
                              ∅) →
                    ∀ (x : GaussianInt),
                      x ∈ (B 1).1 →
                        P.q₂ < P.q₁ →
                          ((B (1 : Fin 2)).1.filter fun y =>
                                FourNeighborAdjacent y x ∧ d y < d x).card =
                            if x = (B (1 : Fin 2)).2 then 0 else 1
    ) := by
  classical
  intro P hq1pos hsum B d squareCoordinates rootDist count_eq root_candidate_empty x hxB horder
  have hb1 : (B 1).1 = (P4062T1InteriorSquare P.q).filter
      (fun z => (z.im = (P.q₁ : Int) ∧ z.re ≤ (P.q₂ : Int)) ∨
        (z.re = (P.q₂ : Int) ∧ (P.q₁ : Int) ≤ z.im)) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hb1root : (B 1).2 = (⟨(P.q₂ : Int), (P.q₁ : Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hxOrig := hxB
  rw [hb1] at hxB
  simp only [Finset.mem_filter] at hxB
  rw [count_eq 1 x hxOrig, hb1]
  rcases hxB with ⟨hsq, harm | harm⟩
  · by_cases hroot : x = (⟨(P.q₂ : Int), (P.q₁ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 1 (⟨(P.q₂ : Int), (P.q₁ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb1root]
      rw [root_candidate_empty _ (rootDist 1) _ hzero]
      simp [hb1root]
    · have hr : x.im = (P.q₁ : Int) := harm.1
      have hlo : 1 ≤ x.re := (squareCoordinates P.q x).mp hsq |>.1
      have hhi : x.re < (P.q₂ : Int) := by
        by_contra hn
        have : x = (⟨(P.q₂ : Int), (P.q₁ : Int)⟩ : GaussianInt) := by
          ext <;> simp [hr]; omega
        exact hroot this
      have hpred := LowerNeighborGeometry.hpredAt680
                P hq1pos hsum squareCoordinates x horder harm hr hlo hhi
      have hpredDist := LowerNeighborGeometry.hpredDistAt693 P x hb1root hr hhi
      have hnotLeft := LowerNeighborGeometry.hnotLeftAt704 P x hb1root hr hhi
      have hnotUp := LowerNeighborGeometry.hnotUpAt718 P x hr hhi
      have hnotDown := LowerNeighborGeometry.hnotDownAt728 P x hr hhi
      have hset := LowerNeighborGeometry.hsetAt738 P
                    x hpred hpredDist hnotLeft hnotUp hnotDown
      rw [hset]
      simp [hb1root, hroot]
  · by_cases hroot : x = (⟨(P.q₂ : Int), (P.q₁ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 1 (⟨(P.q₂ : Int), (P.q₁ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb1root]
      rw [root_candidate_empty _ (rootDist 1) _ hzero]
      simp [hb1root]
    · have hr : x.re = (P.q₂ : Int) := harm.1
      have hlo : (P.q₁ : Int) < x.im := by
        by_contra hn
        have : x = (⟨(P.q₂ : Int), (P.q₁ : Int)⟩ : GaussianInt) := by
          ext <;> simp [hr]; omega
        exact hroot this
      have hhi : x.im < (P.q : Int) := by
        have hsquare := (squareCoordinates P.q x).mp hsq
        omega
      have hpred := LowerNeighborGeometry.hpredAt775
                P hq1pos hsum squareCoordinates x harm hr hlo hhi
      have hpredDist : rootDist 1 (x - ⟨0, 1⟩) < rootDist 1 x := by
        have ha : 0 ≤ x.im - 1 - (P.q₁ : Int) := by omega
        have hab : x.im - 1 - (P.q₁ : Int) < x.im - (P.q₁ : Int) := by omega
        have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
        simp only [rootDist, hb1root, Zsqrtd.re_sub, Zsqrtd.im_sub, hr,
          ]
        simp only [Int.sub_zero, sub_self, Int.natAbs_zero, zero_add]
        exact hn
      have hnotUp := LowerNeighborGeometry.hnotUpAt797 P x hb1root hr hlo
      have hnotRight := LowerNeighborGeometry.hnotRightAt807 P x harm hr
      have hnotLeft := LowerNeighborGeometry.hnotLeftAt817 P x harm hr hlo
      have hset := LowerNeighborGeometry.hsetAt828 P x hpred hpredDist hnotUp hnotRight
                    hnotLeft
      rw [hset]
      simp [hb1root, hroot]

private theorem secondPathDescendingCount :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          (2 : ℕ) < P.q →
            (0 : ℕ) < P.q₁ →
              P.q = P.q₁ + P.q₂ →
                P.q₁ ≠ P.q₂ →
                  let B := P4062T1RemainderPaths P;
                  let d : GaussianInt → Nat := fun x =>
                    let a :=
                      @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _) (B 0).2
                        (B 1).2
                    (x.re - a.re).natAbs + (x.im - a.im).natAbs;
                  (∀ (q : ℕ),
                      ∀ (z : GaussianInt),
                        z ∈ P4062T1InteriorSquare q ↔
                          (1 : ℤ) ≤ z.re ∧
                            z.re ≤ (↑q : ℤ) - (1 : ℤ) ∧
                              (1 : ℤ) ≤ z.im ∧ z.im ≤ (↑q : ℤ) - (1 : ℤ)) →
                    let rootDist (j : Fin 2) (z : GaussianInt) : Nat :=
                      (z.re - (B j).2.re).natAbs + (z.im - (B j).2.im).natAbs;
                    (∀ (j : Fin 2),
                        ∀ (x : GaussianInt),
                          x ∈ (B j).1 →
                            ((B j).1.filter fun y =>
                                FourNeighborAdjacent y x ∧ d y < d x).card =
                              (({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} :
                                Finset GaussianInt).filter
                                fun y =>
                                y ∈ (B j).1 ∧ rootDist j y < rootDist j x).card) →
                      (∀ (S : Finset GaussianInt),
                          ∀ (ρ : GaussianInt → ℕ),
                            ∀ (x : GaussianInt),
                              ρ x = (0 : ℕ) →
                                ({y ∈
                                {x + (1 : GaussianInt), x - (1 : GaussianInt),
                                x + ⟨(0 : ℤ), (1 : ℤ)⟩, x - ⟨(0 : ℤ), (1 : ℤ)⟩} |
                                y ∈ S ∧ ρ y < ρ x} :
                                Finset GaussianInt) =
                                ∅) →
                        ∀ (x : GaussianInt),
                          x ∈ (B 1).1 →
                            ¬P.q₂ < P.q₁ →
                              ((B (1 : Fin 2)).1.filter fun y =>
                                FourNeighborAdjacent y x ∧ d y < d x).card =
                                if x = (B (1 : Fin 2)).2 then 0 else 1
    ) := by
  classical
  intro P hP hq1pos hsum hneq B d squareCoordinates rootDist count_eq root_candidate_empty x hxB
      horder
  have horder' : P.q₁ < P.q₂ := by omega
  have hb1 : (B 1).1 = (P4062T1InteriorSquare P.q).filter
      (fun z => (z.re = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.im) ∨
        (z.im = (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ z.re)) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hb1root : (B 1).2 = (⟨(P.q₂ : Int), (P.q₂ : Int)⟩ : GaussianInt) := by
    simp [B, P4062T1RemainderPaths, horder]
  have hxOrig := hxB
  rw [hb1] at hxB
  simp only [Finset.mem_filter] at hxB
  rw [count_eq 1 x hxOrig, hb1]
  rcases hxB with ⟨hsq, harm | harm⟩
  · by_cases hroot : x = (⟨(P.q₂ : Int), (P.q₂ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 1 (⟨(P.q₂ : Int), (P.q₂ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb1root]
      rw [root_candidate_empty _ (rootDist 1) _ hzero]
      simp [hb1root]
    · have hr : x.re = (P.q₂ : Int) := harm.1
      have hlo : (P.q₂ : Int) < x.im := by
        by_contra hn
        have : x = (⟨(P.q₂ : Int), (P.q₂ : Int)⟩ : GaussianInt) := by
          ext <;> simp [hr]; omega
        exact hroot this
      have hhi : x.im < (P.q : Int) := by
        have hsquare := (squareCoordinates P.q x).mp hsq
        omega
      have hpred := LowerNeighborGeometry.hpredAt877
                P hP hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
      have hpredDist : rootDist 1 (x - ⟨0, 1⟩) < rootDist 1 x := by
        have ha : 0 ≤ x.im - 1 - (P.q₂ : Int) := by omega
        have hab : x.im - 1 - (P.q₂ : Int) < x.im - (P.q₂ : Int) := by omega
        have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
        simp only [rootDist, hb1root, Zsqrtd.re_sub, Zsqrtd.im_sub,
          hr]
        simp only [Int.sub_zero, sub_self, Int.natAbs_zero, zero_add]
        exact hn
      have hnotUp := LowerNeighborGeometry.hnotUpAt899 P x hb1root hr hlo
      have hnotRight := LowerNeighborGeometry.hnotRightAt909 P x hr hlo
      have hnotLeft := LowerNeighborGeometry.hnotLeftAt919 P x hr hlo
      have hset := LowerNeighborGeometry.hsetAt929 P x hpred hpredDist hnotUp hnotRight
                    hnotLeft
      rw [hset]
      simp [hb1root, hroot]
  · by_cases hroot : x = (⟨(P.q₂ : Int), (P.q₂ : Int)⟩ : GaussianInt)
    · subst x
      have hzero : rootDist 1 (⟨(P.q₂ : Int), (P.q₂ : Int)⟩ : GaussianInt) = 0 := by
        simp [rootDist, hb1root]
      rw [root_candidate_empty _ (rootDist 1) _ hzero]
      simp [hb1root]
    · have hr : x.im = (P.q₂ : Int) := harm.1
      have hlo : (P.q₂ : Int) < x.re := by
        by_contra hn
        have : x = (⟨(P.q₂ : Int), (P.q₂ : Int)⟩ : GaussianInt) := by
          ext <;> simp [hr]; omega
        exact hroot this
      have hhi : x.re < (P.q : Int) := by
        have hsquare := (squareCoordinates P.q x).mp hsq
        omega
      have hpred := LowerNeighborGeometry.hpredAt966
                P hP hq1pos hsum squareCoordinates x horder' harm hr hlo hhi
      have hpredDist : rootDist 1 (x - 1) < rootDist 1 x := by
        have ha : 0 ≤ x.re - 1 - (P.q₂ : Int) := by omega
        have hab : x.re - 1 - (P.q₂ : Int) < x.re - (P.q₂ : Int) := by omega
        have hn := Int.natAbs_lt_natAbs_of_nonneg_of_lt ha hab
        simp only [rootDist, hb1root, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_one, Zsqrtd.im_one, hr]
        simp only [Int.sub_zero, sub_self, Int.natAbs_zero]
        exact hn
      have hnotRight := LowerNeighborGeometry.hnotRightAt987 P x hb1root hr hlo
      have hnotUp := LowerNeighborGeometry.hnotUpAt997 P x harm hr hlo
      have hnotDown := LowerNeighborGeometry.hnotDownAt1008 P x harm hr
      have hset := LowerNeighborGeometry.hsetAt1018 P
                    x hpred hpredDist hnotRight hnotUp hnotDown
      rw [hset]
      simp [hb1root, hroot]

end LowerOrderCases

theorem P4112T1LowerNeighbors (P : FordFareyParameter) (hP : 2 < P.q) :
    let B := P4062T1RemainderPaths P
    let d : GaussianInt → Nat := fun x =>
      let a := @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _)
        (B 0).2 (B 1).2
      (x.re-a.re).natAbs + (x.im-a.im).natAbs
    ∀ j, ∀ x ∈ (B j).1,
      (@Finset.filter GaussianInt (fun y => FourNeighborAdjacent y x ∧ d y < d x)
        (fun _ => Classical.propDecidable _) (B j).1).card =
        (if x = (B j).2 then 0 else 1) := by
-- BODY
  classical
  have hq1pos := LowerNeighborGeometry.hq1pos P hP
  have hcross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1 := by
    have h1 : P.p₁ * ((P.q₁ + P.q₂ : Nat) : Int) -
        (P.q₁ : Int) * (P.p₁ + P.p₂) = 1 := by
      simpa [P.sum_q, P.sum_p] using P.det₁
    norm_num [Nat.cast_add] at h1
    nlinarith [h1]
  have hsum : P.q = P.q₁ + P.q₂ := P.sum_q
  have hneq := LowerNeighborGeometry.hneq P hP hq1pos hcross hsum
  let B := P4062T1RemainderPaths P
  let d : GaussianInt → Nat := fun x =>
    let a := @ite GaussianInt (x ∈ (B 0).1) (Classical.propDecidable _)
        (B 0).2 (B 1).2
    (x.re-a.re).natAbs + (x.im-a.im).natAbs
  simp only []
  change ∀ j, ∀ x ∈ (B j).1,
    ((B j).1.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
      (if x = (B j).2 then 0 else 1)
  have squareCoordinates (q : Nat) (z : GaussianInt) := LowerNeighborGeometry.squareCoordinates q z
  have d_on_path (j : Fin 2) (z : GaussianInt) (hz : z ∈ (B j).1) :=
      LowerNeighborGeometry.d_on_path P hP j z hz
  have neighbor_filter (S : Finset GaussianInt) (x : GaussianInt)
      (ρ : GaussianInt → Nat) := LowerNeighborGeometry.neighbor_filter S x ρ
  have count_eq (j : Fin 2) (x : GaussianInt) (hx : x ∈ (B j).1) :=
      LowerNeighborGeometry.count_eq P d_on_path neighbor_filter j x hx
  have root_candidate_empty (S : Finset GaussianInt) (ρ : GaussianInt → Nat)
      (x : GaussianInt) (hz : ρ x = 0) := LowerNeighborGeometry.root_candidate_empty S ρ x hz
  intro j
  fin_cases j
  · intro x hx
    change ((B 0).1.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
      (if x = (B 0).2 then 0 else 1) at ⊢
    change x ∈ (P4062T1RemainderPaths P 0).1 at hx
    have hxB : x ∈ (B 0).1 := hx
    by_cases horder : P.q₂ < P.q₁
    · have firstPathAscendingCount :
        ((B (0 : Fin 2)).1.filter
          (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
          (if x = (B (0 : Fin 2)).2 then 0 else 1) := LowerOrderCases.firstPathAscendingCount P
              hq1pos hsum squareCoordinates count_eq root_candidate_empty x hxB horder
      exact firstPathAscendingCount
    · have firstPathDescendingCount :
        ((B (0 : Fin 2)).1.filter
          (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
          (if x = (B (0 : Fin 2)).2 then 0 else 1) := LowerOrderCases.firstPathDescendingCount P
              hq1pos hsum hneq squareCoordinates count_eq root_candidate_empty x hxB horder
      exact firstPathDescendingCount
  · intro x hx
    change ((B 1).1.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
      (if x = (B 1).2 then 0 else 1) at ⊢
    change x ∈ (P4062T1RemainderPaths P 1).1 at hx
    have hxB : x ∈ (B 1).1 := hx
    by_cases horder : P.q₂ < P.q₁
    · have secondPathAscendingCount :
        ((B (1 : Fin 2)).1.filter
          (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
          (if x = (B (1 : Fin 2)).2 then 0 else 1) := LowerOrderCases.secondPathAscendingCount P
              hq1pos hsum squareCoordinates count_eq root_candidate_empty x hxB horder
      exact secondPathAscendingCount
    · have secondPathDescendingCount :
        ((B (1 : Fin 2)).1.filter
          (fun y => FourNeighborAdjacent y x ∧ d y < d x)).card =
          (if x = (B (1 : Fin 2)).2 then 0 else 1) := LowerOrderCases.secondPathDescendingCount P
              hP hq1pos hsum hneq squareCoordinates count_eq root_candidate_empty x hxB horder
      exact secondPathDescendingCount
end ApollonianSuperharmonic

end
