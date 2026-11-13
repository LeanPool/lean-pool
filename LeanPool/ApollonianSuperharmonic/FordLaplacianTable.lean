/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordBoundaryMultiplicity
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import Mathlib.RingTheory.Int.Basic

-- [TABLET NODE: FordLaplacianTable]

/-!
# FordLaplacianTable

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordLaplacianProof

private theorem periodic :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    ∀ (v : GaussianInt), ∀ (a : ℤ), ∀ (b : ℤ), ∀ (c : ℤ), (∀ (x : GaussianInt), g (x + v) = g x +
        a * x.re + b * x.im + c) → ∀ (x : GaussianInt), FourNeighborLaplacian g (x + v) =
        FourNeighborLaplacian g x := by
  classical
  intro P g v a b c h x
  unfold FourNeighborLaplacian
  rw [show x + v + 1 = (x + 1) + v by abel,
    show x + v - 1 = (x - 1) + v by abel,
    show x + v + ⟨0, 1⟩ = (x + ⟨0, 1⟩) + v by abel,
    show x + v - ⟨0, 1⟩ = (x - ⟨0, 1⟩) + v by abel]
  rw [h, h, h, h, h]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub,
    Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  ring

private theorem boundaryValue :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (∀ (P : FordFareyParameter), ∀ x ∈ FordDoubledBoundary P.q, Classical.choose
        FordOdometerFamilyExistsUnique P x = IntegerCeilDiv (P.p * x.re * x.im) (↑P.q : ℤ) (by
        exact_mod_cast P.q_pos.ne')) → (∀ (r : ℤ), ∀ (s : ℤ), (0 : ℤ) ≤ r → r ≤ (↑P.q : ℤ) → (0 :
        ℤ) ≤ s → s ≤ (↑P.q : ℤ) → r ≤ (1 : ℤ) ∨ (↑P.q : ℤ) - (1 : ℤ) ≤ r ∨ s ≤ (1 : ℤ) ∨ (↑P.q :
        ℤ) - (1 : ℤ) ≤ s → g ⟨r, s⟩ = -(-(P.p * r * s) / (↑P.q : ℤ))) := by
  classical
  intro P g hbdy r s hr hr' hs hs' hedge
  apply hbdy P
  change (0 ≤ r ∧ r ≤ P.q ∧ 0 ≤ s ∧ s ≤ P.q) ∧
    ¬(2 ≤ r ∧ r ≤ (P.q : Int) - 2 ∧
      2 ≤ s ∧ s ≤ (P.q : Int) - 2)
  omega

private theorem below :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (∀ (P : FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
        FordOdometerFamilyExistsUnique P (x + ⟨(0 : ℤ), -(↑P.q : ℤ)⟩) = Classical.choose
        FordOdometerFamilyExistsUnique P x - P.p * x.re) → ((0 < (P.q : Int)) → ((∀ (n : Int), ∀
            (k : Int), -((-(k * (P.q : Int) - n)) / (P.q : Int)) = k - n / (P.q : Int)) → ((∀ (r
            : Int), ∀ (s : Int), (0 ≤ r) → ((r ≤ P.q) → ((0 ≤ s) → ((s ≤ P.q) → ((r ≤ 1 ∨ (P.q :
            Int) -
        1 ≤ r ∨ s ≤ 1 ∨ (P.q : Int) - 1 ≤ s) → (g ⟨r, s⟩ = -((-(P.p * r * s)) / (P.q :
        Int)))))))) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t ≤ (↑P.q : ℤ) → g ⟨t, (-1 : ℤ)⟩ = -(P.p * t /
        (↑P.q : ℤ)))))) := by
  classical
  intro P g hneg hq ceilShift boundaryValue t ht ht'
  have hd := hneg P ⟨t, (P.q : Int) - 1⟩
  change g _ = g _ - _ at hd
  have he : (⟨t, (P.q : Int) - 1⟩ : GaussianInt) +
      ⟨0, -(P.q : Int)⟩ = ⟨t, -1⟩ := by ext <;> simp; ring
  rw [he] at hd
  have hv := boundaryValue t ((P.q : Int) - 1) ht ht'
    (by omega) (by omega) (by omega)
  rw [hv] at hd
  rw [show P.p * t * ((P.q : Int) - 1) =
    (P.p * t) * (P.q : Int) - P.p * t by ring, ceilShift] at hd
  simpa using hd

private theorem left :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (∀ (P : FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
        FordOdometerFamilyExistsUnique P (x + ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩) = Classical.choose
        FordOdometerFamilyExistsUnique P x + P.p₁ * x.re + P.p * x.im + (↑P.q₁ : ℤ) * P.p) → ((∀
            (P : FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
        FordOdometerFamilyExistsUnique P (x + ⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩) = Classical.choose
        FordOdometerFamilyExistsUnique P x + P.p₂ * x.re - P.p * x.im - (↑P.q : ℤ) * P.p₂) → ((0
        < (P.q : Int)) → (((P.q : Int) ≠ 0) → (((P.q₁ : Int) < P.q) → ((∀ (n : Int), ∀ (k : Int),
            -((-(k * (P.q : Int) - n)) / (P.q : Int)) = k - n / (P.q : Int)) → ((∀ (r : Int), ∀
            (s : Int), (0 ≤ r) → ((r ≤ P.q) → ((0 ≤ s) → ((s ≤ P.q) → ((r ≤ 1 ∨ (P.q : Int) - 1 ≤
            r ∨ s ≤
        1 ∨ (P.q : Int) - 1 ≤ s) → (g ⟨r, s⟩ = -((-(P.p * r * s)) / (P.q : Int)))))))) → (∀ (t :
            ℤ), (0 : ℤ) ≤ t → t ≤ (↑P.q : ℤ) → g ⟨(-1 : ℤ), t⟩ = -((P.p * t - (1 : ℤ)) / (↑P.q :
        ℤ))))))))) := by
  classical
  intro P g hpos hneg₂ hq hqne ha ceilShift boundaryValue t ht ht'
  have hsum : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  by_cases htb : t ≤ P.q₂
  · have hd := hpos P ⟨-1, t⟩
    change g _ = g _ + _ + _ + _ at hd
    have he : (⟨-1, t⟩ : GaussianInt) +
        ⟨(P.q : Int), (P.q₁ : Int)⟩ =
        ⟨(P.q : Int) - 1, t + P.q₁⟩ := by ext <;> simp; ring
    rw [he] at hd
    have hv := boundaryValue ((P.q : Int) - 1) (t + P.q₁)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [hv] at hd
    rw [show P.p * ((P.q : Int) - 1) * (t + P.q₁) =
      (P.p * (t + P.q₁)) * (P.q : Int) - P.p * (t + P.q₁) by ring,
      ceilShift] at hd
    have hdet := P.det₁
    have he' : P.p * (t + P.q₁) =
        (P.p * t - 1) + P.p₁ * (P.q : Int) := by nlinarith only [hdet]
    rw [he', Int.add_mul_ediv_right _ _ hqne] at hd
    dsimp at hd
    linarith only [hd, hdet]
  · have hd := hneg₂ P ⟨(P.q : Int) - 1, t - P.q₂⟩
    change g _ = g _ + _ - _ - _ at hd
    have he : (⟨(P.q : Int) - 1, t - P.q₂⟩ : GaussianInt) +
        ⟨-(P.q : Int), (P.q₂ : Int)⟩ = ⟨-1, t⟩ := by
      ext <;> simp; ring
    rw [he] at hd
    have hv := boundaryValue ((P.q : Int) - 1) (t - P.q₂)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [hv] at hd
    rw [show P.p * ((P.q : Int) - 1) * (t - P.q₂) =
      (P.p * (t - P.q₂)) * (P.q : Int) - P.p * (t - P.q₂) by ring,
      ceilShift] at hd
    have hdet := P.det₂
    have he' : P.p * (t - P.q₂) =
        (P.p * t - 1) + (-P.p₂) * (P.q : Int) := by nlinarith only [hdet]
    rw [he', Int.add_mul_ediv_right _ _ hqne] at hd
    dsimp at hd
    linarith only [hd]

private theorem nondiv :
    ∀ (P : FordFareyParameter), ∀ (t : ℤ), (0 : ℤ) < t → t < (↑P.q : ℤ) → ¬(↑P.q : ℤ) ∣ P.p * t
        := by
  classical
  intro P t ht ht'
  rintro ⟨k, hk⟩
  have hdet := congrArg (fun z : Int => z * t) P.det₁
  have hk' := congrArg (fun z : Int => z * (P.q₁ : Int)) hk
  have hd : (P.q : Int) ∣ t := by
    refine ⟨P.p₁ * t - (P.q₁ : Int) * k, ?_⟩
    nlinarith only [hk', hdet]
  have := Int.le_of_dvd ht hd
  omega

private theorem roundInterior :
    ∀ (P : FordFareyParameter), (0 < (P.q : Int)) → (((P.q : Int) ≠ 0) → ((∀ (t : Int), (0 < t) →
        ((t < P.q) → (¬ (P.q : Int) ∣ P.p * t))) → (∀ (t : ℤ), (0 : ℤ) < t → t < (↑P.q : ℤ) →
        -(-(P.p * t) / (↑P.q : ℤ)) - P.p * t / (↑P.q : ℤ) = (1 : ℤ) ∧ (P.p * t - (1 : ℤ)) / (↑P.q
        : ℤ) = P.p * t / (↑P.q : ℤ)))) := by
  classical
  intro P hq hqne nondiv t ht ht'
  have hn := nondiv t ht ht'
  constructor
  · rw [Int.neg_ediv, ite_eq_right hn, Int.sign_eq_one_of_pos hq]
    ring
  · apply (Int.ediv_eq_iff_of_pos hq).mpr
    have hm := Int.emod_nonneg (P.p * t) hqne
    have hml := Int.emod_lt_of_pos (P.p * t) hq
    have hmn : P.p * t % (P.q : Int) ≠ 0 := by
      intro hh
      exact hn (Int.dvd_of_emod_eq_zero hh)
    have hmp : 1 ≤ P.p * t % (P.q : Int) := by omega
    have hd := Int.emod_add_mul_ediv (P.p * t) (P.q : Int)
    constructor <;> nlinarith only [hmp, hml, hd]

private theorem bottomLap :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (0 < (P.q : Int)) → ((∀ (t : Int), (0 ≤ t) → ((t ≤ P.q) → (g ⟨t, 0⟩ = 0 ∧ g ⟨0, t⟩ = 0 ∧ g
        ⟨t, 1⟩ = -((- (P.p * t)) / (P.q : Int)) ∧ g ⟨1, t⟩ = -((- (P.p * t)) / (P.q : Int))))) →
        ((∀ (t : Int), (0 ≤ t) → ((t ≤ P.q) → (g ⟨t, -1⟩ = -(P.p * t / (P.q : Int))))) → ((∀ (t :
            Int), (0 ≤ t) → ((t ≤ P.q) → (g ⟨-1, t⟩ = -((P.p * t - 1) / (P.q : Int))))) → ((∀ (r
            : Int), ∀ (s : Int), FourNeighborLaplacian g ⟨r, s⟩ = g ⟨r + 1, s⟩ + g ⟨r - 1, s⟩ + g
            ⟨r, s
        + 1⟩ + g ⟨r, s - 1⟩ - 4 * g ⟨r, s⟩) → ((∀ (t : Int), (0 < t) → ((t < P.q) → (-((- (P.p *
        t)) / (P.q : Int)) - P.p * t / (P.q : Int) = 1 ∧ (P.p * t - 1) / (P.q : Int) = P.p * t /
        (P.q : Int)))) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t < (↑P.q : ℤ) → FourNeighborLaplacian g ⟨t,
        (0 : ℤ)⟩ = (1 : ℤ))))))) := by
  classical
  intro P g hq axes below left lapCoord roundInterior t ht ht'
  rw [lapCoord]
  norm_num only
  by_cases hz : t = 0
  · subst t
    have h0 := axes 0 (by omega) (by omega)
    have h1 := axes 1 (by omega) (by omega)
    have hl := left 0 (by omega) (by omega)
    have hd := below 0 (by omega) (by omega)
    norm_num [Int.neg_one_ediv, Int.sign_eq_one_of_pos hq] at hl
    norm_num at h0 hd ⊢
    rw [h1.1, hl, h1.2.1, hd, h0.1]
    norm_num
  · have hm := axes (t - 1) (by omega) (by omega)
    have hp := axes (t + 1) (by omega) (by omega)
    have hc := axes t ht (by omega)
    rw [hp.1, hm.1, hc.2.2.1, below t ht (by omega), hc.1]
    have hh := (roundInterior t (by omega) ht').1
    linarith only [hh]

private theorem leftLap :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (0 < (P.q : Int)) → ((∀ (x : GaussianInt), FourNeighborLaplacian g (x + ⟨0, (P.q : Int)⟩) =
        FourNeighborLaplacian g x) → ((∀ (t : Int), (0 ≤ t) → ((t ≤ P.q) → (g ⟨t, 0⟩ = 0 ∧ g ⟨0,
        t⟩ = 0 ∧ g ⟨t, 1⟩ = -((- (P.p * t)) / (P.q : Int)) ∧ g ⟨1, t⟩ = -((- (P.p * t)) / (P.q :
        Int))))) → ((∀ (t : Int), (0 ≤ t) → ((t ≤ P.q) → (g ⟨-1, t⟩ = -((P.p * t - 1) / (P.q :
        Int))))) → ((∀ (r : Int), ∀ (s : Int), FourNeighborLaplacian g ⟨r, s⟩ = g ⟨r + 1, s⟩ + g
        ⟨r - 1, s⟩ + g ⟨r, s + 1⟩ + g ⟨r, s - 1⟩ - 4 * g ⟨r, s⟩) → ((∀ (t : Int), (0 < t) → ((t <
        P.q) → (-((- (P.p * t)) / (P.q : Int)) - P.p * t / (P.q : Int) = 1 ∧ (P.p * t - 1) / (P.q
        : Int) = P.p * t / (P.q : Int)))) → ((∀ (t : Int), (0 ≤ t) → ((t < P.q) →
        (FourNeighborLaplacian g ⟨t, 0⟩ = 1))) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t ≤ (↑P.q : ℤ) →
        FourNeighborLaplacian g ⟨(0 : ℤ), t⟩ = (1 : ℤ)))))))) := by
  classical
  intro P g hq periodUp axes left lapCoord roundInterior bottomLap t ht ht'
  by_cases hz : t = 0
  · subst t
    exact bottomLap 0 (by omega) hq
  by_cases htop : t = P.q
  · subst t
    have hp := periodUp ⟨0, 0⟩
    simpa using hp.trans (bottomLap 0 (by omega) hq)
  rw [lapCoord]
  norm_num only
  have hm := axes (t - 1) (by omega) (by omega)
  have hp := axes (t + 1) (by omega) (by omega)
  have hc := axes t ht ht'
  rw [hc.2.2.2, left t ht ht', hp.2.1, hm.2.1, hc.2.1]
  obtain ⟨hround, hfloor⟩ := roundInterior t (by omega) (by omega)
  rw [hfloor]
  linarith only [hround]

private theorem rightLap :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    ((P.q₁ : Int) < P.q) → ((∀ (x : GaussianInt), FourNeighborLaplacian g (x + ⟨(0 : ℤ), -(↑P.q :
        ℤ)⟩) = FourNeighborLaplacian g x) → ((∀ (x : GaussianInt), FourNeighborLaplacian g (x +
        ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩) = FourNeighborLaplacian g x) → ((∀ (t : Int), (0 ≤ t) → ((t ≤
        P.q) → (FourNeighborLaplacian g ⟨0, t⟩ = 1))) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t ≤ (↑P.q : ℤ)
        → FourNeighborLaplacian g ⟨(↑P.q : ℤ), t⟩ = (1 : ℤ))))) := by
  classical
  intro P g ha periodNeg periodPos leftLap t ht ht'
  have he : (⟨0, t - P.q₁⟩ : GaussianInt) +
      ⟨(P.q : Int), (P.q₁ : Int)⟩ = ⟨(P.q : Int), t⟩ := by
    ext <;> simp
  rw [← he, periodPos]
  by_cases hs : (P.q₁ : Int) ≤ t
  · exact leftLap (t - P.q₁) (by omega) (by omega)
  · have he' : (⟨0, t - P.q₁ + P.q⟩ : GaussianInt) +
        ⟨0, -(P.q : Int)⟩ = ⟨0, t - P.q₁⟩ := by ext <;> simp
    rw [← he', periodNeg]
    exact leftLap (t - P.q₁ + P.q) (by omega) (by omega)

private theorem ha0 :
    ∀ (P : FordFareyParameter),
      (1 : ℕ) < P.q →
        let a : Int := P.q₁
        let b : Int := P.q₂
        (P.q : Int) = a + b → 0 < a := by
  classical
  intro P hbig a b hsum
  let A := P.p₁
  by_contra h
  have haz : a = 0 := by omega
  have hd : (P.q : Int) ∣ 1 := by
    refine ⟨A, ?_⟩
    have hh := P.det₁
    change A * (P.q : Int) - a * P.p = 1 at hh
    rw [haz] at hh
    nlinarith only [hh]
  have := Int.le_of_dvd (by norm_num : (0 : Int) < 1) hd
  omega

private theorem parentValue :
    ((∀ (P : FordFareyParameter), ∀ x ∈ FordDoubledBoundary P.q,
        Classical.choose FordOdometerFamilyExistsUnique P x = IntegerCeilDiv (P.p * x.re * x.im)
        (↑P.q : ℤ) (by exact_mod_cast P.q_pos.ne')) → (
        (
    let cdiv (n d : Int) := -((-n) / d);
    (
        (∀ (R : FordFareyParameter), ∀ (r : ℤ), ∀ (s :
        ℤ), (0 : ℤ) ≤ r ∧ r ≤ (↑R.q : ℤ) ∧ (0 : ℤ) ≤ s ∧ s ≤ (↑R.q : ℤ) → r ≤ (1 : ℤ) ∨ (↑R.q :
        ℤ) - (1 : ℤ) ≤ r ∨ s ≤ (1 : ℤ) ∨ (↑R.q : ℤ) - (1 : ℤ) ≤ s → Classical.choose
        FordOdometerFamilyExistsUnique R ⟨r, s⟩ = cdiv (R.p * r * s) (↑R.q : ℤ)))))) := by
  classical
  intro hbdy cdiv R r s hrect hedge
  apply hbdy R
  change (0 ≤ r ∧ r ≤ R.q ∧ 0 ≤ s ∧ s ≤ R.q) ∧
    ¬(2 ≤ r ∧ r ≤ (R.q : Int) - 2 ∧
      2 ≤ s ∧ s ≤ (R.q : Int) - 2)
  omega

private theorem v1 :
    ∀ (P : FordFareyParameter),
      let g := FordOdometer P;
      let a : Int := P.q₁
      let b : Int := P.q₂
      let A := P.p₁
      let B := P.p₂
      let cdiv (n d : Int) := -(-n / d)
      (P.q : Int) = a + b →
        ∀ (P₁ : FordFareyParameter),
          P₁.p = A →
            P₁.q = P.q₁ →
              ∀ (P₂ : FordFareyParameter),
                P₂.q = P.q₂ →
                  (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)),
                      Classical.choose FordOdometerFamilyExistsUnique P x =
                        Classical.choose FordOdometerFamilyExistsUnique P₁
                            (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) +
                            P.p₂ * x.re +
                            P.p₂ * x.im -
                            P.p₂ * (↑P.q₂ : ℤ) +
                          (1 : ℤ)) →
                    (∀ (R : FordFareyParameter),
                        ∀ (r : Int),
                          ∀ (s : Int),
                            0 ≤ r ∧ r ≤ R.q ∧ 0 ≤ s ∧ s ≤ R.q →
                            r ≤ 1 ∨ (R.q : Int) - 1 ≤ r ∨ s ≤ 1 ∨ (R.q : Int) - 1 ≤ s →
                            Classical.choose FordOdometerFamilyExistsUnique R ⟨r, s⟩ =
                            cdiv (R.p * r * s) R.q) →
                      ∀ (r : ℤ),
                        ∀ (s : ℤ),
                          b ≤ r ∧ r ≤ (↑P.q : ℤ) ∧ b ≤ s ∧ s ≤ (↑P.q : ℤ) →
                            r - b ≤ (1 : ℤ) ∨
                            a - (1 : ℤ) ≤ r - b ∨ s - b ≤ (1 : ℤ) ∨ a - (1 : ℤ) ≤ s - b →
                            g ⟨r, s⟩ =
                            cdiv (A * (r - b) * (s - b)) a + B * r + B * s - B * b + (1 : ℤ) := by
  classical
  intro P g a b A B cdiv hsum P₁ hp₁ hq₁ P₂ hq₂ rec1 parentValue r s hrect hedge
  have hd := rec1 ⟨r, s⟩ (by change b ≤ r ∧ r ≤ P.q ∧ b ≤ s ∧ s ≤ P.q; exact hrect)
  have he : (⟨r, s⟩ : GaussianInt) - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ = ⟨r - b, s - b⟩ := rfl
  rw [he] at hd
  have hv := parentValue P₁ (r - b) (s - b)
    (by rw [hq₁]; change 0 ≤ r - b ∧ r - b ≤ a ∧ 0 ≤ s - b ∧ s - b ≤ a; omega)
    (by simpa [hq₁, a] using hedge)
  rw [hp₁, hq₁] at hv
  rw [hv] at hd
  exact hd

private theorem v2 :
    ∀ (P : FordFareyParameter),
      let g := FordOdometer P;
      let a : Int := P.q₁
      let b : Int := P.q₂
      let A := P.p₁
      let B := P.p₂
      let cdiv (n d : Int) := -(-n / d)
      (P.q : Int) = a + b →
        ∀ (P₁ : FordFareyParameter),
          P₁.q = P.q₁ →
            ∀ (P₂ : FordFareyParameter),
              P₂.p = B →
                P₂.q = P.q₂ →
                  (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)),
                      Classical.choose FordOdometerFamilyExistsUnique P x =
                        Classical.choose FordOdometerFamilyExistsUnique P₂
                            (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) +
                          P.p₁ * x.im) →
                    (∀ (R : FordFareyParameter),
                        ∀ (r : Int),
                          ∀ (s : Int),
                            0 ≤ r ∧ r ≤ R.q ∧ 0 ≤ s ∧ s ≤ R.q →
                            r ≤ 1 ∨ (R.q : Int) - 1 ≤ r ∨ s ≤ 1 ∨ (R.q : Int) - 1 ≤ s →
                            Classical.choose FordOdometerFamilyExistsUnique R ⟨r, s⟩ =
                            cdiv (R.p * r * s) R.q) →
                      ∀ (r : ℤ),
                        ∀ (s : ℤ),
                          a ≤ r ∧ r ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ s ∧ s ≤ b →
                            r - a ≤ (1 : ℤ) ∨
                            b - (1 : ℤ) ≤ r - a ∨ s ≤ (1 : ℤ) ∨ b - (1 : ℤ) ≤ s →
                            g ⟨r, s⟩ = cdiv (B * (r - a) * s) b + A * s := by
  classical
  intro P g a b A B cdiv hsum P₁ hq₁ P₂ hp₂ hq₂ rec2 parentValue r s hrect hedge
  have hd := rec2 ⟨r, s⟩ (by change a ≤ r ∧ r ≤ P.q ∧ 0 ≤ s ∧ s ≤ b; exact hrect)
  have he : (⟨r, s⟩ : GaussianInt) - ⟨(P.q₁ : Int), 0⟩ = ⟨r - a, s⟩ := by ext <;> simp [a]
  rw [he] at hd
  have hv := parentValue P₂ (r - a) s
    (by rw [hq₂]; change 0 ≤ r - a ∧ r - a ≤ b ∧ 0 ≤ s ∧ s ≤ b; omega)
    (by simpa [hq₂, b] using hedge)
  rw [hp₂, hq₂] at hv
  rw [hv] at hd
  exact hd

private theorem v3 :
    ∀ (P : FordFareyParameter),
      let g := FordOdometer P;
      let a : Int := P.q₁
      let b : Int := P.q₂
      let A := P.p₁
      let B := P.p₂
      let cdiv (n d : Int) := -(-n / d)
      (P.q : Int) = a + b →
        ∀ (P₁ : FordFareyParameter),
          P₁.q = P.q₁ →
            ∀ (P₂ : FordFareyParameter),
              P₂.p = B →
                P₂.q = P.q₂ →
                  (∀ x ∈ FordRecursiveVertexDomains P (3 : Fin (4 : ℕ)),
                      Classical.choose FordOdometerFamilyExistsUnique P x =
                        Classical.choose FordOdometerFamilyExistsUnique P₂
                            (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) +
                          P.p₁ * x.re) →
                    (∀ (R : FordFareyParameter),
                        ∀ (r : Int),
                          ∀ (s : Int),
                            0 ≤ r ∧ r ≤ R.q ∧ 0 ≤ s ∧ s ≤ R.q →
                            r ≤ 1 ∨ (R.q : Int) - 1 ≤ r ∨ s ≤ 1 ∨ (R.q : Int) - 1 ≤ s →
                            Classical.choose FordOdometerFamilyExistsUnique R ⟨r, s⟩ =
                            cdiv (R.p * r * s) R.q) →
                      ∀ (r : ℤ),
                        ∀ (s : ℤ),
                          (0 : ℤ) ≤ r ∧ r ≤ b ∧ a ≤ s ∧ s ≤ (↑P.q : ℤ) →
                            r ≤ (1 : ℤ) ∨
                            b - (1 : ℤ) ≤ r ∨ s - a ≤ (1 : ℤ) ∨ b - (1 : ℤ) ≤ s - a →
                            g ⟨r, s⟩ = cdiv (B * r * (s - a)) b + A * r := by
  classical
  intro P g a b A B cdiv hsum P₁ hq₁ P₂ hp₂ hq₂ rec3 parentValue r s hrect hedge
  have hd := rec3 ⟨r, s⟩ (by change 0 ≤ r ∧ r ≤ b ∧ a ≤ s ∧ s ≤ P.q; exact hrect)
  have he : (⟨r, s⟩ : GaussianInt) - ⟨0, (P.q₁ : Int)⟩ = ⟨r, s - a⟩ := by ext <;> simp [a]
  rw [he] at hd
  have hv := parentValue P₂ r (s - a)
    (by rw [hq₂]; change 0 ≤ r ∧ r ≤ b ∧ 0 ≤ s - a ∧ s - a ≤ b; omega)
    (by simpa [hq₂, b] using hedge)
  rw [hp₂, hq₂] at hv
  rw [hv] at hd
  exact hd

private theorem near0 :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P;
    (
    let a : Int := P.q₁;
    let A := P.p₁;
    let cdiv (n d : Int) := -((-n) / d);
    (0 < a) → (∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → (
        ((∀ (r :
        Int), ∀ (s : Int), (0 ≤ r ∧ r ≤ a ∧ 0 ≤ s ∧ s ≤ a) → ((r ≤ 1 ∨ a - 1 ≤ r ∨ s ≤ 1 ∨ a - 1
        ≤ s) → (g ⟨r, s⟩ = cdiv (A * r * s) a))) → ((∀ (d : Int), ∀ (n : Int), ∀ (k : Int), (d ≠
        0) → (cdiv (k * d - n) d = k - n / d)) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t ≤ a → g ⟨a - (1 :
        ℤ), t⟩ = A * t - A * t / a ∧ g ⟨t, a - (1 : ℤ)⟩ = A * t - A * t / a)))))) := by
  classical
  intro P g a A cdiv ha0 P₁ hq₁ v0 cminus t ht ht'
  have hl := v0 (a - 1) t (by omega) (by omega)
  have hv := v0 t (a - 1) (by omega) (by omega)
  rw [show A * (a - 1) * t = (A * t) * a - A * t by ring,
    cminus _ _ _ (ne_of_gt ha0)] at hl
  rw [show A * t * (a - 1) = (A * t) * a - A * t by ring,
    cminus _ _ _ (ne_of_gt ha0)] at hv
  exact ⟨hl, hv⟩

private theorem edge2 :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P;
    ((P.q₁ : Int) < P.q) → (
        (
    let a : Int := P.q₁;
    let b : Int := P.q₂;
    let A := P.p₁;
    let B := P.p₂;
    let cdiv (n d : Int) := -((-n) / d);
    ((P.q : Int) = a + b) → ((A * b - B * a = 1) → ((0 < b) → (∀ (P₁ : FordFareyParameter), (P₁.q
        = P.q₁) → (∀ (P₂ : FordFareyParameter), (P₂.q = P.q₂) → ((∀ (r : Int), ∀ (s : Int), (a ≤
        r ∧ r ≤ P.q ∧ 0 ≤ s ∧ s ≤ b) → ((r - a ≤ 1 ∨ b - 1 ≤ r - a ∨ s ≤ 1 ∨ b - 1 ≤ s) → (g ⟨r,
        s⟩ = cdiv (B * (r - a) * s) b + A * s))) → ((∀ (r : Int), ∀ (s : Int), (0 ≤ r ∧ r ≤ b ∧ a
        ≤ s ∧ s ≤ P.q) → ((r ≤ 1 ∨ b - 1 ≤ r ∨ s - a ≤ 1 ∨ b - 1 ≤ s - a) → (g ⟨r, s⟩ = cdiv (B *
        r * (s - a)) b + A * r))) → ((∀ (d : Int), ∀ (k : Int), (d ≠ 0) → (cdiv (k * d) d = k)) →
        (∀ (r : ℤ), a ≤ r → r ≤ (↑P.q : ℤ) → g ⟨r, b⟩ = B * r + (1 : ℤ) ∧ g ⟨b, r⟩ = B * r + (1 :
        ℤ))))))))))) := by
  classical
  intro P g ha a b A B cdiv hsum hdet hb P₁ hq₁ P₂ hq₂ v2 v3 cmul r ht ht'
  have hl := v2 r b (by omega) (by omega)
  have hv := v3 b r (by omega) (by omega)
  rw [cmul _ _ (ne_of_gt hb)] at hl
  rw [show B * b * (r - a) = (B * (r - a)) * b by ring,
    cmul _ _ (ne_of_gt hb)] at hv
  constructor
  · nlinarith only [hl, hdet]
  · nlinarith only [hv, hdet]

private theorem lowFormula :
    ∀ (P : FordFareyParameter),
      let g := FordOdometer P;
      (∀ (r : Int),
          ∀ (s : Int),
            FourNeighborLaplacian g ⟨r, s⟩ =
              g ⟨r + 1, s⟩ + g ⟨r - 1, s⟩ + g ⟨r, s + 1⟩ + g ⟨r, s - 1⟩ - 4 * g ⟨r, s⟩) →
        let a : Int := P.q₁;
        let b : Int := P.q₂;
        let A := P.p₁;
        let B := P.p₂;
        let cdiv (n d : Int) := -(-n / d);
        (∀ (t : Int), 0 ≤ t → t ≤ a → g ⟨a, t⟩ = A * t ∧ g ⟨t, a⟩ = A * t) →
          (∀ (t : Int),
              0 ≤ t →
                t ≤ a →
                  g ⟨a - 1, t⟩ = A * t - A * t / a ∧ g ⟨t, a - 1⟩ = A * t - A * t / a) →
            (∀ (t : Int),
                0 ≤ t →
                  t ≤ b →
                    g ⟨a + 1, t⟩ = cdiv (B * t) b + A * t ∧
                      g ⟨t, a + 1⟩ = cdiv (B * t) b + A * t) →
              ∀ (t : ℤ),
                (0 : ℤ) < t →
                  t < a →
                    t ≤ b →
                      FourNeighborLaplacian g ⟨a, t⟩ = cdiv (B * t) b - A * t / a ∧
                        FourNeighborLaplacian g ⟨t, a⟩ = cdiv (B * t) b - A * t / a := by
  classical
  intro P g lapCoord a b A B cdiv edge0 near0 outward t ht hta htb
  have hc := edge0 t (by omega) (by omega)
  have hm := edge0 (t - 1) (by omega) (by omega)
  have hp' := edge0 (t + 1) (by omega) (by omega)
  have hl := near0 t (by omega) (by omega)
  have ho := outward t (by omega) htb
  constructor
  · rw [lapCoord, ho.1, hl.1, hp'.1, hm.1, hc.1]
    ring
  · rw [lapCoord, hp'.2, hm.2, ho.2, hl.2, hc.2]
    ring

private theorem highFormula :
    ∀ (P : FordFareyParameter),
      let g := FordOdometer P;
      (∀ (r : Int),
          ∀ (s : Int),
            FourNeighborLaplacian g ⟨r, s⟩ =
              g ⟨r + 1, s⟩ + g ⟨r - 1, s⟩ + g ⟨r, s + 1⟩ + g ⟨r, s - 1⟩ -
                4 * g ⟨r, s⟩) →
        (let a : Int := P.q₁;
        let b : Int := P.q₂;
        let A := P.p₁;
        let B := P.p₂;
        let cdiv (n d : Int) := -((-n) / d);
        ((P.q : Int) = a + b) →
          ((A * b - B * a = 1) →
            ((0 < b) →
              ((0 < a) →
                (∀ (P₁ : FordFareyParameter),
                  (P₁.q = P.q₁) →
                    (∀ (P₂ : FordFareyParameter),
                      (P₂.q = P.q₂) →
                        ((∀ (d : Int),
                            ∀ (n : Int),
                              ∀ (k : Int),
                                (d ≠ 0) → (cdiv (k * d - n) d = k - n / d)) →
                          ((∀ (d : Int),
                              ∀ (n : Int),
                                ∀ (k : Int),
                                  (d ≠ 0) → (cdiv (k * d + n) d = k + cdiv n d)) →
                            ((∀ (r : Int),
                                (a ≤ r) →
                                  ((r ≤ P.q) →
                                    (g ⟨r, b⟩ = B * r + 1 ∧
                                      g ⟨b, r⟩ = B * r + 1))) →
                              ((∀ (r : Int),
                                  (b ≤ r) →
                                    ((r ≤ P.q) →
                                      (g ⟨r, b + 1⟩ =
                                          cdiv (A * (r - b)) a + B * r + B + 1 ∧
                                        g ⟨b + 1, r⟩ =
                                          cdiv (A * (r - b)) a + B * r + B + 1))) →
                                ((∀ (r : Int),
                                    (a ≤ r) →
                                      ((r ≤ P.q) →
                                        (g ⟨r, b - 1⟩ =
                                            cdiv (B * (r - a) * (b - 1)) b +
                                              A * (b - 1) ∧
                                          g ⟨b - 1, r⟩ =
                                            cdiv (B * (r - a) * (b - 1)) b +
                                              A * (b - 1)))) →
                                  (∀ (t : ℤ),
                                    (0 : ℤ) < t →
                                      t ≤ a →
                                        t < b →
                                          FourNeighborLaplacian g
                                                ⟨(↑P.q : ℤ) - t, b⟩ =
                                              cdiv (B * t) b - A * t / a ∧
                                            FourNeighborLaplacian g
                                                ⟨b, (↑P.q : ℤ) - t⟩ =
                                              cdiv (B * t) b - A * t / a)))))))))))) := by
  classical
  intro P g lapCoord a b A B cdiv hsum hdet hb ha0 P₁ hq₁ P₂ hq₂ cminus cplus edge2 near1 near2
      t ht hta htb
  have hc := edge2 ((P.q : Int) - t) (by omega) (by omega)
  have hm := edge2 ((P.q : Int) - t - 1) (by omega) (by omega)
  have hp' := edge2 ((P.q : Int) - t + 1) (by omega) (by omega)
  have hl := near2 ((P.q : Int) - t) (by omega) (by omega)
  have ho := near1 ((P.q : Int) - t) (by omega) (by omega)
  rw [show A * ((P.q : Int) - t - b) = A * a - A * t by rw [hsum]; ring,
    cminus _ _ _ (ne_of_gt ha0)] at ho
  rw [show B * ((P.q : Int) - t - a) * (b - 1) =
    (B * (b - t) - B) * b + B * t by rw [hsum]; ring,
    cplus _ _ _ (ne_of_gt hb)] at hl
  constructor
  · rw [lapCoord, hp'.1, hm.1, ho.1, hl.1, hc.1]
    rw [hsum]
    nlinarith only [hdet]
  · rw [lapCoord, ho.2, hl.2, hp'.2, hm.2, hc.2]
    rw [hsum]
    nlinarith only [hdet]

private theorem roundArm :
    ∀ (P : FordFareyParameter),
    let a : Int := P.q₁
    let b : Int := P.q₂
    let A := P.p₁
    let B := P.p₂
    let cdiv (n d : Int) := -((-n) / d)
    (A * b - B * a = 1) → ((0 < b) → ((0 < a) → (∀ (t : ℤ), (0 : ℤ) < t → t < a → t < b → cdiv (B
        * t) b - A * t / a = (1 : ℤ)))) := by
  classical
  intro P a b A B cdiv hdet hb ha0 t ht hta htb
  have hn : ¬ a ∣ A * t := by
    rintro ⟨k, hk⟩
    have hdt := congrArg (fun z : Int => z * t) hdet
    have hk' := congrArg (fun z : Int => z * b) hk
    have hdiv : a ∣ t := by
      refine ⟨b * k - B * t, ?_⟩
      nlinarith only [hk', hdt]
    have := Int.le_of_dvd ht hdiv
    omega
  let k := A * t / a
  have hm := Int.emod_nonneg (A * t) (ne_of_gt ha0)
  have hml := Int.emod_lt_of_pos (A * t) ha0
  have hmn : A * t % a ≠ 0 := fun h => hn (Int.dvd_of_emod_eq_zero h)
  have hmp : 1 ≤ A * t % a := by omega
  have hmu : A * t % a ≤ a - 1 := by omega
  have he := Int.emod_add_mul_ediv (A * t) a
  have hl : k * a + 1 ≤ A * t := by dsimp [k]; nlinarith only [he, hmp]
  have hu : A * t ≤ (k + 1) * a - 1 := by dsimp [k]; nlinarith only [he, hmu]
  have hdt := congrArg (fun z : Int => z * t) hdet
  have hlb := mul_le_mul_of_nonneg_right hl hb.le
  have hub := mul_le_mul_of_nonneg_right hu hb.le
  have hbl : k * b < B * t := by
    by_contra h
    have hc := mul_le_mul_of_nonneg_right (show B * t ≤ k * b by omega) ha0.le
    nlinarith only [hc, hlb, hdt, htb]
  have hbu : B * t < (k + 1) * b := by
    by_contra h
    have hc := mul_le_mul_of_nonneg_right (show (k + 1) * b ≤ B * t by omega) ha0.le
    nlinarith only [hc, hub, hdt, hb, ht]
  have hq' : (- (B * t)) / b = -k - 1 := by
    apply (Int.ediv_eq_iff_of_pos hb).mpr
    constructor <;> nlinarith only [hbl, hbu]
  dsimp [cdiv]
  rw [hq']
  dsimp [k]
  ring

private theorem rectBoundary :
    ∀ (l : ℤ), ∀ (r : ℤ), ∀ (d : ℤ), ∀ (u : ℤ), ∀ (z : GaussianInt), z ∈ LatticeVertexBoundary {w
        : GaussianInt | l ≤ w.re ∧ w.re ≤ r ∧ d ≤ w.im ∧ w.im ≤ u} ↔ (l ≤ z.re ∧ z.re ≤ r ∧ d ≤
        z.im ∧ z.im ≤ u) ∧ (z.re = l ∨ z.re = r ∨ z.im = d ∨ z.im = u) := by
  classical
  intro l r d u z
  constructor
  · rintro ⟨hz, y, hy, hyr, hyi⟩
    refine ⟨hz, ?_⟩
    change l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u at hz
    change ¬(l ≤ y.re ∧ y.re ≤ r ∧ d ≤ y.im ∧ y.im ≤ u) at hy
    omega
  · rintro ⟨hz, he⟩
    refine ⟨hz, ?_⟩
    rcases he with he | he | he | he
    · refine ⟨⟨z.re - 1, z.im⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re + 1, z.im⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re, z.im - 1⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re, z.im + 1⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega

private theorem count :
    ∀ (P : FordFareyParameter),
      ∀ (x : GaussianInt),
        let a : Int := P.q₁;
        let b : Int := P.q₂;
        (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) ↔
            x.re ≤ a ∧ x.im ≤ a ∧ (x.re = a ∨ x.im = a)) →
          (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) ↔
              b ≤ x.re ∧ b ≤ x.im ∧ (x.re = b ∨ x.im = b)) →
            (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) ↔
                a ≤ x.re ∧ x.im ≤ b ∧ (x.re = a ∨ x.im = b)) →
              (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) ↔
                  x.re ≤ b ∧ a ≤ x.im ∧ (x.re = b ∨ x.im = a)) →
                FordBoundaryMultiplicity P x =
                  (((if x.re ≤ a ∧ x.im ≤ a ∧ (x.re = a ∨ x.im = a) then 1 else 0) +
                        if b ≤ x.re ∧ b ≤ x.im ∧ (x.re = b ∨ x.im = b) then 1 else 0) +
                      if a ≤ x.re ∧ x.im ≤ b ∧ (x.re = a ∨ x.im = b) then 1 else 0) +
                    if x.re ≤ b ∧ a ≤ x.im ∧ (x.re = b ∨ x.im = a) then 1 else 0 := by
  classical
  intro P x a b b0 b1 b2 b3
  simp only [FordBoundaryMultiplicity, Finset.card_filter,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) then 1 else 0) +
    ((if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) then 1 else 0) +
    ((if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) then 1 else 0) +
    (if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) then 1 else 0))) = _
  simp only [b0, b1, b2, b3]
  omega

end FordLaplacianProof

namespace FordLaplacianDetails

private theorem periodUp :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (∀ (x : GaussianInt), FourNeighborLaplacian g (x + ⟨(0 : ℤ), -(↑P.q : ℤ)⟩) =
        FourNeighborLaplacian g x) → (∀ (x : GaussianInt), FourNeighborLaplacian g (x + ⟨(0 : ℤ),
        (↑P.q : ℤ)⟩) = FourNeighborLaplacian g x) := by
  classical
  intro P g periodNeg x
  have h := periodNeg (x + ⟨0, (P.q : Int)⟩)
  have he : x + ⟨0, (P.q : Int)⟩ + ⟨0, -(P.q : Int)⟩ = x := by
    ext <;> simp
  rw [he] at h
  exact h.symm

private theorem ceilShift :
    ∀ (P : FordFareyParameter), ((P.q : Int) ≠ 0) → (∀ (n : ℤ), ∀ (k : ℤ), -(-(k * (↑P.q : ℤ) -
        n) / (↑P.q : ℤ)) = k - n / (↑P.q : ℤ)) := by
  classical
  intro P hqne n k
  rw [show -(k * (P.q : Int) - n) = n + (-k) * (P.q : Int) by ring,
    Int.add_mul_ediv_right _ _ hqne]
  ring

private theorem axes :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (0 < (P.q : Int)) → ((∀ (r : Int), ∀ (s : Int), (0 ≤ r) → ((r ≤ P.q) → ((0 ≤ s) → ((s ≤ P.q)
        → ((r ≤ 1 ∨ (P.q : Int) - 1 ≤ r ∨ s ≤ 1 ∨ (P.q : Int) - 1 ≤ s) → (g ⟨r, s⟩ = -((-(P.p * r
        * s)) / (P.q : Int)))))))) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t ≤ (↑P.q : ℤ) → g ⟨t, (0 : ℤ)⟩ =
        (0 : ℤ) ∧ g ⟨(0 : ℤ), t⟩ = (0 : ℤ) ∧ g ⟨t, (1 : ℤ)⟩ = -(-(P.p * t) / (↑P.q : ℤ)) ∧ g ⟨(1
        : ℤ), t⟩ = -(-(P.p * t) / (↑P.q : ℤ)))) := by
  classical
  intro P g hq boundaryValue t ht ht'
  have h0 := boundaryValue t 0 ht ht' (by omega) (by omega) (by omega)
  have h1 := boundaryValue 0 t (by omega) (by omega) ht ht' (by omega)
  have h2 := boundaryValue t 1 ht ht' (by omega) (by omega) (by omega)
  have h3 := boundaryValue 1 t (by omega) (by omega) ht ht' (by omega)
  simpa using And.intro h0 (And.intro h1 (And.intro h2 h3))

private theorem lapCoord :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    ∀ (r : ℤ), ∀ (s : ℤ), FourNeighborLaplacian g ⟨r, s⟩ = g ⟨r + (1 : ℤ), s⟩ + g ⟨r - (1 : ℤ),
        s⟩ + g ⟨r, s + (1 : ℤ)⟩ + g ⟨r, s - (1 : ℤ)⟩ - (4 : ℤ) * g ⟨r, s⟩ := by
  classical
  intro P g r s
  unfold FourNeighborLaplacian
  rw [show (⟨r, s⟩ : GaussianInt) + 1 = ⟨r + 1, s⟩ by ext <;> simp,
    show (⟨r, s⟩ : GaussianInt) - 1 = ⟨r - 1, s⟩ by ext <;> simp,
    show (⟨r, s⟩ : GaussianInt) + ⟨0, 1⟩ = ⟨r, s + 1⟩ by ext <;> simp,
    show (⟨r, s⟩ : GaussianInt) - ⟨0, 1⟩ = ⟨r, s - 1⟩ by ext <;> simp]

private theorem bottomClosed :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    (0 < (P.q : Int)) → ((∀ (t : Int), (0 ≤ t) → ((t < P.q) → (FourNeighborLaplacian g ⟨t, 0⟩ =
        1))) → ((∀ (t : Int), (0 ≤ t) → ((t ≤ P.q) → (FourNeighborLaplacian g ⟨(P.q : Int), t⟩ =
        1))) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t ≤ (↑P.q : ℤ) → FourNeighborLaplacian g ⟨t, (0 : ℤ)⟩ =
        (1 : ℤ)))) := by
  classical
  intro P g hq bottomLap rightLap t ht ht'
  by_cases he : t = P.q
  · rw [he]
    exact rightLap 0 (by omega) (by omega)
  · exact bottomLap t ht (by omega)

private theorem hedge :
    ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x ∈ LatticeVertexBoundary (FordVertexDomain
        P.q)) → (((0 : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ)) →
        (x.re = 0 ∨ x.re = P.q ∨ x.im = 0 ∨ x.im = P.q)) := by
  classical
  intro P x hx hxrect
  obtain ⟨_, y, hy, hyr, hyi⟩ := hx
  change ¬(0 ≤ y.re ∧ y.re ≤ P.q ∧ 0 ≤ y.im ∧ y.im ≤ P.q) at hy
  omega

private theorem hsumAt824 :
    ∀ (P : FordFareyParameter),
    let a : Int := P.q₁
    let b : Int := P.q₂
    (P.q : Int) = a + b := by
  classical
  intro P a b
  dsimp [a, b]
  exact_mod_cast P.sum_q

private theorem hdetAt828 :
    ∀ (P : FordFareyParameter),
    let a : Int := P.q₁
    let b : Int := P.q₂
    let A := P.p₁
    let B := P.p₂
    ((P.q : Int) = a + b) → ((P.p = A + B) → (A * b - B * a = 1)) := by
  classical
  intro P a b A B hsum hp
  have hd := P.det₁
  change A * (P.q : Int) - a * P.p = 1 at hd
  rw [hsum, hp] at hd
  nlinarith only [hd]

private theorem hcop :
    ∀ (P : FordFareyParameter),
    let a : Int := P.q₁
    let b : Int := P.q₂
    let A := P.p₁
    let B := P.p₂
    (A * b - B * a = 1) → (Nat.Coprime P.q₁ A.natAbs ∧ Nat.Coprime P.q₂ B.natAbs) := by
  classical
  intro P a b A B hdet
  have h1 : IsCoprime (P.q₁ : Int) A := ⟨-B, b, by dsimp [a] at hdet; nlinarith only [hdet]⟩
  have h2 : IsCoprime (P.q₂ : Int) B := ⟨A, -a, by dsimp [b] at hdet; nlinarith only [hdet]⟩
  exact ⟨by simpa using Int.isCoprime_iff_nat_coprime.mp h1,
    by simpa using Int.isCoprime_iff_nat_coprime.mp h2⟩

private theorem v0 :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    let a : Int := P.q₁
    let A := P.p₁
    let cdiv (n d : Int) := -((-n) / d)
    ∀ (P₁ : FordFareyParameter), (P₁.p = A) → ((P₁.q = P.q₁) → ((∀ x ∈ FordRecursiveVertexDomains
        P (0 : Fin (4 : ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x =
        Classical.choose FordOdometerFamilyExistsUnique P₁ x) → ((∀ (R : FordFareyParameter), ∀
        (r : Int), ∀ (s : Int), (0 ≤ r ∧ r ≤ R.q ∧ 0 ≤ s ∧ s ≤ R.q) → ((r ≤ 1 ∨ (R.q : Int) - 1 ≤
        r ∨ s ≤ 1 ∨ (R.q : Int) - 1 ≤ s) → (Classical.choose FordOdometerFamilyExistsUnique R ⟨r,
        s⟩ = cdiv (R.p * r * s) R.q))) → (∀ (r : ℤ), ∀ (s : ℤ), (0 : ℤ) ≤ r ∧ r ≤ a ∧ (0 : ℤ) ≤ s
        ∧ s ≤ a → r ≤ (1 : ℤ) ∨ a - (1 : ℤ) ≤ r ∨ s ≤ (1 : ℤ) ∨ a - (1 : ℤ) ≤ s → g ⟨r, s⟩ = cdiv
        (A * r * s) a)))) := by
  classical
  intro P g a A cdiv P₁ hp₁ hq₁ rec0 parentValue r s hrect hedge
  have hd := rec0 ⟨r, s⟩ (by change 0 ≤ r ∧ r ≤ a ∧ 0 ≤ s ∧ s ≤ a; exact hrect)
  have hv := parentValue P₁ r s (by simpa [hq₁, a] using hrect)
    (by simpa [hq₁, a] using hedge)
  rw [hp₁, hq₁] at hv
  exact hd.trans hv

private theorem cminus :
    let cdiv (n d : Int) := -((-n) / d)
    ∀ (d : ℤ), ∀ (n : ℤ), ∀ (k : ℤ), d ≠ (0 : ℤ) → cdiv (k * d - n) d = k - n / d := by
  classical
  intro cdiv d n k hd
  dsimp [cdiv]
  rw [show -(k * d - n) = n + (-k) * d by ring, Int.add_mul_ediv_right _ _ hd]
  ring

private theorem cplus :
    let cdiv (n d : Int) := -((-n) / d)
    ∀ (d : ℤ), ∀ (n : ℤ), ∀ (k : ℤ), d ≠ (0 : ℤ) → cdiv (k * d + n) d = k + cdiv n d := by
  classical
  intro cdiv d n k hd
  dsimp [cdiv]
  rw [show -(k * d + n) = -n + (-k) * d by ring, Int.add_mul_ediv_right _ _ hd]
  ring

private theorem edge0 :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P;
    (
    let a : Int := P.q₁;
    let A := P.p₁;
    let cdiv (n d : Int) := -((-n) / d);
    (0 < a) → (∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → (
        ((∀ (r :
        Int), ∀ (s : Int), (0 ≤ r ∧ r ≤ a ∧ 0 ≤ s ∧ s ≤ a) → ((r ≤ 1 ∨ a - 1 ≤ r ∨ s ≤ 1 ∨ a - 1
        ≤ s) → (g ⟨r, s⟩ = cdiv (A * r * s) a))) → ((∀ (d : Int), ∀ (k : Int), (d ≠ 0) → (cdiv (k
        * d) d = k)) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t ≤ a → g ⟨a, t⟩ = A * t ∧ g ⟨t, a⟩ = A *
        t)))))) := by
  classical
  intro P g a A cdiv ha0 P₁ hq₁ v0 cmul t ht ht'
  have hl := v0 a t (by omega) (by omega)
  have hv := v0 t a (by omega) (by omega)
  rw [show A * a * t = (A * t) * a by ring, cmul _ _ (ne_of_gt ha0)] at hl
  rw [cmul _ _ (ne_of_gt ha0)] at hv
  exact ⟨hl, hv⟩

private theorem outward :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P;
    ((P.q₁ : Int) < P.q) → (
        (
    let a : Int := P.q₁;
    let b : Int := P.q₂;
    let A := P.p₁;
    let B := P.p₂;
    let cdiv (n d : Int) := -((-n) / d);
    ((P.q : Int) = a + b) → (
        (∀ (P₂ : FordFareyParameter), (P₂.q = P.q₂) →
        ((∀ (r : Int), ∀ (s : Int), (a ≤ r ∧ r ≤ P.q ∧ 0 ≤ s ∧ s ≤ b) → ((r - a ≤ 1 ∨ b - 1 ≤ r -
        a ∨ s ≤ 1 ∨ b - 1 ≤ s) → (g ⟨r, s⟩ = cdiv (B * (r - a) * s) b + A * s))) → ((∀ (r : Int),
        ∀ (s : Int), (0 ≤ r ∧ r ≤ b ∧ a ≤ s ∧ s ≤ P.q) → ((r ≤ 1 ∨ b - 1 ≤ r ∨ s - a ≤ 1 ∨ b - 1
        ≤ s - a) → (g ⟨r, s⟩ = cdiv (B * r * (s - a)) b + A * r))) → (∀ (t : ℤ), (0 : ℤ) ≤ t → t
        ≤ b → g ⟨a + (1 : ℤ), t⟩ = cdiv (B * t) b + A * t ∧ g ⟨t, a + (1 : ℤ)⟩ = cdiv (B * t) b +
        A * t))))))) := by
  classical
  intro P g ha a b A B cdiv hsum P₂ hq₂ v2 v3 t ht ht'
  have hl := v2 (a + 1) t (by omega) (by omega)
  have hv := v3 t (a + 1) (by omega) (by omega)
  simpa only [add_sub_cancel_left, mul_one] using And.intro hl hv

private theorem near2 :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P;
    ((P.q₁ : Int) < P.q) → (
        (
    let a : Int := P.q₁;
    let b : Int := P.q₂;
    let A := P.p₁;
    let B := P.p₂;
    let cdiv (n d : Int) := -((-n) / d);
    ((P.q : Int) = a + b) → (∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → (∀ (P₂ :
        FordFareyParameter), (P₂.q = P.q₂) → ((∀ (r : Int), ∀ (s : Int), (a ≤ r ∧ r ≤ P.q ∧ 0 ≤ s
        ∧ s ≤ b) → ((r - a ≤ 1 ∨ b - 1 ≤ r - a ∨ s ≤ 1 ∨ b - 1 ≤ s) → (g ⟨r, s⟩ = cdiv (B * (r -
        a) * s) b + A * s))) → ((∀ (r : Int), ∀ (s : Int), (0 ≤ r ∧ r ≤ b ∧ a ≤ s ∧ s ≤ P.q) →
        ((r ≤ 1 ∨ b - 1 ≤ r ∨ s - a ≤ 1 ∨ b - 1 ≤ s - a) → (g ⟨r, s⟩ = cdiv (B * r * (s - a)) b +
        A * r))) → (∀ (r : ℤ), a ≤ r → r ≤ (↑P.q : ℤ) → g ⟨r, b - (1 : ℤ)⟩ = cdiv (B * (r - a) *
        (b - (1 : ℤ))) b + A * (b - (1 : ℤ)) ∧ g ⟨b - (1 : ℤ), r⟩ = cdiv (B * (r - a) * (b - (1 :
        ℤ))) b + A * (b - (1 : ℤ))))))))) := by
  classical
  intro P g ha a b A B cdiv hsum P₁ hq₁ P₂ hq₂ v2 v3 r ht ht'
  have hl := v2 r (b - 1) (by omega) (by omega)
  have hv := v3 (b - 1) r (by omega) (by omega)
  rw [show B * (b - 1) * (r - a) = B * (r - a) * (b - 1) by ring] at hv
  exact ⟨hl, hv⟩

private theorem b0 :
    ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), ((1 : ℤ) ≤ x.re) → (((1 : ℤ) ≤ x.im) → (
    let a : Int := P.q₁;
    (0 < a) → (∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → (
        ((∀ (l :
        Int), ∀ (r : Int), ∀ (d : Int), ∀ (u : Int), ∀ (z : GaussianInt), z ∈
        LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤ r ∧ d ≤ w.im ∧ w.im ≤ u} ↔ (l
        ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u) ∧ (z.re = l ∨ z.re = r ∨ z.im = d ∨ z.im = u)) →
        (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) ↔ x.re ≤ a ∧ x.im ≤ a ∧ (x.re
        = a ∨ x.im = a))))))) := by
  classical
  intro P x hr hs a ha0 P₁ hq₁ rectBoundary
  change x ∈ LatticeVertexBoundary {z : GaussianInt |
    0 ≤ z.re ∧ z.re ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ a} ↔ _
  rw [rectBoundary]
  omega

private theorem b1 :
    ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (x.re ≤ (↑P.q : ℤ) - (1 : ℤ)) → ((x.im ≤
        (↑P.q : ℤ) - (1 : ℤ)) → (
    let a : Int := P.q₁
    let b : Int := P.q₂
    ((P.q : Int) = a + b) → (∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → (∀ (P₂ :
        FordFareyParameter), (P₂.q = P.q₂) → ((∀ (l : Int), ∀ (r : Int), ∀ (d : Int), ∀ (u :
        Int), ∀ (z : GaussianInt), z ∈ LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤
        r ∧ d ≤ w.im ∧ w.im ≤ u} ↔ (l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u) ∧ (z.re = l ∨ z.re
        = r ∨ z.im = d ∨ z.im = u)) → (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1)
        ↔ b ≤ x.re ∧ b ≤ x.im ∧ (x.re = b ∨ x.im = b))))))) := by
  classical
  intro P x hr' hs' a b hsum P₁ hq₁ P₂ hq₂ rectBoundary
  change x ∈ LatticeVertexBoundary {z : GaussianInt |
    b ≤ z.re ∧ z.re ≤ P.q ∧ b ≤ z.im ∧ z.im ≤ P.q} ↔ _
  rw [rectBoundary]
  omega

private theorem b2 :
    ∀ (P : FordFareyParameter),
        (∀ (x : GaussianInt), (x.re ≤ (↑P.q : ℤ) -
        (1 : ℤ)) → (((1 : ℤ) ≤ x.im) → (
    let a : Int := P.q₁;
    let b : Int := P.q₂;
    ((P.q : Int) = a + b) → (∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → (∀ (P₂ :
        FordFareyParameter), (P₂.q = P.q₂) → ((∀ (l : Int), ∀ (r : Int), ∀ (d : Int), ∀ (u :
        Int), ∀ (z : GaussianInt), z ∈ LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤
        r ∧ d ≤ w.im ∧ w.im ≤ u} ↔ (l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u) ∧ (z.re = l ∨ z.re
        = r ∨ z.im = d ∨ z.im = u)) → (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2)
        ↔ a ≤ x.re ∧ x.im ≤ b ∧ (x.re = a ∨ x.im = b)))))))) := by
  classical
  intro P x hr' hs a b hsum P₁ hq₁ P₂ hq₂ rectBoundary
  change x ∈ LatticeVertexBoundary {z : GaussianInt |
    a ≤ z.re ∧ z.re ≤ P.q ∧ 0 ≤ z.im ∧ z.im ≤ b} ↔ _
  rw [rectBoundary]
  omega

private theorem b3 :
    ∀ (P : FordFareyParameter), ((P.q₁ : Int) < P.q) → (∀ (x : GaussianInt), ((1 : ℤ) ≤ x.re) →
        ((x.im ≤ (↑P.q : ℤ) - (1 : ℤ)) → (
    let a : Int := P.q₁
    let b : Int := P.q₂
    ((P.q : Int) = a + b) → (∀ (P₁ : FordFareyParameter), (P₁.q = P.q₁) → (∀ (P₂ :
        FordFareyParameter), (P₂.q = P.q₂) → ((∀ (l : Int), ∀ (r : Int), ∀ (d : Int), ∀ (u :
        Int), ∀ (z : GaussianInt), z ∈ LatticeVertexBoundary {w : GaussianInt | l ≤ w.re ∧ w.re ≤
        r ∧ d ≤ w.im ∧ w.im ≤ u} ↔ (l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u) ∧ (z.re = l ∨ z.re
        = r ∨ z.im = d ∨ z.im = u)) → (x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3)
        ↔ x.re ≤ b ∧ a ≤ x.im ∧ (x.re = b ∨ x.im = a)))))))) := by
  classical
  intro P ha x hr hs' a b hsum P₁ hq₁ P₂ hq₂ rectBoundary
  change x ∈ LatticeVertexBoundary {z : GaussianInt |
    0 ≤ z.re ∧ z.re ≤ b ∧ a ≤ z.im ∧ z.im ≤ P.q} ↔ _
  rw [rectBoundary]
  omega

private theorem hcaseAt964 :
    ∀ (P : FordFareyParameter), ∀ (x : GaussianInt),
    let a : Int := P.q₁
    let b : Int := P.q₂
    (FordBoundaryMultiplicity P x = (if x.re ≤ a ∧ x.im ≤ a ∧ (x.re = a ∨ x.im = a) then 1 else
        0) + (if b ≤ x.re ∧ b ≤ x.im ∧ (x.re = b ∨ x.im = b) then 1 else 0) + (if a ≤ x.re ∧ x.im
        ≤ b ∧ (x.re = a ∨ x.im = b) then 1 else 0) + (if x.re ≤ b ∧ a ≤ x.im ∧ (x.re = b ∨ x.im =
        a) then 1 else 0)) → ((FordBoundaryMultiplicity P x = (2 : ℕ)) → ((x.re = a ∧ x.im < a ∧
        x.im < b) ∨ (x.im = a ∧ x.re < a ∧ x.re < b) ∨ (x.im = b ∧ a < x.re ∧ b < x.re) ∨ (x.re =
        b ∧ a < x.im ∧ b < x.im))) := by
  classical
  intro P x a b count hn
  split_ifs at count <;> omega

private theorem hcaseAt988 :
    ∀ (P : FordFareyParameter), ∀ (x : GaussianInt),
    let a : Int := P.q₁
    let b : Int := P.q₂
    (FordBoundaryMultiplicity P x = (if x.re ≤ a ∧ x.im ≤ a ∧ (x.re = a ∨ x.im = a) then 1 else
        0) + (if b ≤ x.re ∧ b ≤ x.im ∧ (x.re = b ∨ x.im = b) then 1 else 0) + (if a ≤ x.re ∧ x.im
        ≤ b ∧ (x.re = a ∨ x.im = b) then 1 else 0) + (if x.re ≤ b ∧ a ≤ x.im ∧ (x.re = b ∨ x.im =
        a) then 1 else 0)) → ((FordBoundaryMultiplicity P x = (3 : ℕ)) → ((b < a ∧ ((x.re = a ∧
        x.im = b) ∨ (x.re = b ∧ x.im = a))) ∨ (a < b ∧ ((x.re = a ∧ x.im = a) ∨ (x.re = b ∧ x.im
        = b))))) := by
  classical
  intro P x a b count hn
  split_ifs at count <;> omega

private theorem hfAt993 :
    ∀ (P : FordFareyParameter), ((P.q₁ : Int) < P.q) → (
        (
    let a : Int := P.q₁;
    let b : Int := P.q₂;
    let A := P.p₁;
    let B := P.p₂;
    ((P.q : Int) = a + b) → ((A * b - B * a = 1) → ((0 < a) → (∀ (P₁ : FordFareyParameter), (P₁.q
        = P.q₁) → (∀ (P₂ : FordFareyParameter), (P₂.q = P.q₂) → ((b < a) → (A * b / a = B))))))))
        := by
  classical
  intro P ha a b A B hsum hdet ha0 P₁ hq₁ P₂ hq₂ hab
  rw [show A * b = 1 + B * a by nlinarith only [hdet],
    Int.add_mul_ediv_right _ _ (ne_of_gt ha0)]
  rw [Int.ediv_eq_zero_of_lt (by norm_num) (by omega)]
  ring

private theorem hcAt1006 :
    ∀ (P : FordFareyParameter), ((P.q₁ : Int) < P.q) → (((1 : ℕ) < P.q) → (
        (
    let a : Int := P.q₁;
    let b : Int := P.q₂;
    let A := P.p₁;
    let B := P.p₂;
    let cdiv (n d : Int) := -((-n) / d);
    ((P.q : Int) = a + b) → ((A * b - B * a = 1) → ((0 < b) → (∀ (P₁ : FordFareyParameter), (P₁.q
        = P.q₁) → (∀ (P₂ : FordFareyParameter), (P₂.q = P.q₂) → ((∀ (d : Int), ∀ (n : Int), ∀ (k
        : Int), (d ≠ 0) → (cdiv (k * d - n) d = k - n / d)) → ((a < b) → (cdiv (B * a) b =
        A)))))))))) := by
  classical
  intro P ha hbig a b A B cdiv hsum hdet hb P₁ hq₁ P₂ hq₂ cminus hab
  rw [show B * a = A * b - 1 by nlinarith only [hdet], cminus _ _ _ (ne_of_gt hb),
    Int.ediv_eq_zero_of_lt (by norm_num) (by omega)]
  ring

private theorem hall :
    ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), (FordBoundaryMultiplicity P x = (4 : ℕ)) →
        (∀ i, x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)) := by
  classical
  intro P x hn
  change (Finset.univ.filter fun i : Fin 4 =>
    x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)).card = 4 at hn
  have hcard : (Finset.univ.filter fun i : Fin 4 =>
      x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)).card =
      (Finset.univ : Finset (Fin 4)).card := by simpa using hn
  exact fun i => Finset.card_filter_eq_iff.mp hcard i (Finset.mem_univ i)

private theorem hdAt1050 :
    ∀ (P : FordFareyParameter), ((P.q₁ : Int) = P.q₂) → (((P.q : Int) = P.q₁ + P.q₂) → ((P.p₁ *
        (↑P.q : ℤ) - (↑P.q₁ : ℤ) * P.p = (1 : ℤ)) → ((P.p = P.p₁ + P.p₂) → ((P.q₁ : Int) ∣ 1))))
        := by
  classical
  intro P he hsum hdet hp
  refine ⟨P.p₁ - P.p₂, ?_⟩
  rw [hsum, ← he, hp] at hdet
  nlinarith only [hdet]

private theorem hnum :
    ∀ (P : FordFareyParameter), (P.p₁ * (↑P.q : ℤ) - (↑P.q₁ : ℤ) * P.p = (1 : ℤ)) → (((P.q₁ :
        Int) = 1) → (((P.q : Int) = 2) → (P.p = P.p₁ * 2 - 1))) := by
  classical
  intro P hdet hqa hqq
  rw [hqq, hqa] at hdet
  norm_num at hdet
  linarith only [hdet]

private theorem hvR :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    ((P.q : Int) = 2) → ((g ⟨(2 : ℤ), (0 : ℤ)⟩ = (0 : ℤ) ∧ g ⟨(0 : ℤ), (2 : ℤ)⟩ = (0 : ℤ) ∧ g ⟨(2
        : ℤ), (1 : ℤ)⟩ = -(-(P.p * (2 : ℤ)) / (↑P.q : ℤ)) ∧ g ⟨(1 : ℤ), (2 : ℤ)⟩ = -(-(P.p * (2 :
        ℤ)) / (↑P.q : ℤ))) → (g ⟨2, 1⟩ = P.p)) := by
  classical
  intro P g hqq hv
  have hh := hv.2.2.1
  rw [hqq, show -(P.p * 2) = (-P.p) * 2 by ring,
    Int.mul_ediv_cancel _ (by norm_num : (2 : Int) ≠ 0), neg_neg] at hh
  exact hh

private theorem hvU :
    ∀ (P : FordFareyParameter),
    let g := FordOdometer P
    ((P.q : Int) = 2) → ((g ⟨(2 : ℤ), (0 : ℤ)⟩ = (0 : ℤ) ∧ g ⟨(0 : ℤ), (2 : ℤ)⟩ = (0 : ℤ) ∧ g ⟨(2
        : ℤ), (1 : ℤ)⟩ = -(-(P.p * (2 : ℤ)) / (↑P.q : ℤ)) ∧ g ⟨(1 : ℤ), (2 : ℤ)⟩ = -(-(P.p * (2 :
        ℤ)) / (↑P.q : ℤ))) → (g ⟨1, 2⟩ = P.p)) := by
  classical
  intro P g hqq hv
  have hh := hv.2.2.2
  rw [hqq, show -(P.p * 2) = (-P.p) * 2 by ring,
    Int.mul_ediv_cancel _ (by norm_num : (2 : Int) ≠ 0), neg_neg] at hh
  exact hh

end FordLaplacianDetails

namespace FordInteriorCase

private theorem interiorLaplacian :
    ∀ (P : FordFareyParameter), let g := FordOdometer P
    (∀ (P : FordFareyParameter), ∀ x ∈ FordDoubledBoundary P.q, Classical.choose
        FordOdometerFamilyExistsUnique P x = IntegerCeilDiv (P.p * x.re * x.im) (↑P.q : ℤ) (by
        exact_mod_cast P.q_pos.ne')) → ((∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter),
            ∀ (P₂ : FordFareyParameter), (1 : ℕ) < P.q → P₁.p = P.p₁ → P₁.q = P.q₁ → P₂.p = P.p₂ →
        P₂.q = P.q₂ → (∀ x ∈ FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)), Classical.choose
        FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique P₁
        x) ∧ (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)), Classical.choose
        FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique P₁
        (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (↑P.q₂ : ℤ) + (1 :
        ℤ)) ∧ (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)), Classical.choose
        FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique P₂
        (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) + P.p₁ * x.im) ∧ ∀ x ∈ FordRecursiveVertexDomains P (3 : Fin
        (4 : ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x = Classical.choose
        FordOdometerFamilyExistsUnique P₂ (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) + P.p₁ * x.re) → (((P.q₁ :
        Int) < P.q) → ((∀ (n : Int), ∀ (k : Int), -((-(k * (P.q : Int) - n)) / (P.q : Int)) = k -
        n / (P.q : Int)) → ((∀ (r : Int), ∀ (s : Int), (0 ≤ r) → ((r ≤ P.q) → ((0 ≤ s) → ((s ≤
            P.q) → ((r ≤ 1 ∨ (P.q : Int) - 1 ≤ r ∨ s ≤ 1 ∨ (P.q : Int) -
        1 ≤ s) → (g ⟨r, s⟩ = -((-(P.p * r * s)) / (P.q : Int)))))))) → ((∀ (t : Int), (0 ≤ t) →
            ((t ≤ P.q) → (g ⟨t, 0⟩ = 0 ∧ g ⟨0, t⟩ = 0 ∧ g ⟨t, 1⟩ = -((- (P.p * t)) / (P.q : Int))
        ∧ g ⟨1, t⟩ = -((- (P.p * t)) / (P.q : Int))))) → ((∀ (r : Int), ∀ (s : Int),
            FourNeighborLaplacian g ⟨r, s⟩ = g ⟨r + 1, s⟩ + g ⟨r - 1, s⟩ + g ⟨r, s + 1⟩ + g ⟨r, s -
        1⟩ - 4 * g ⟨r, s⟩) → ((1 < P.q) → (∀ (x : GaussianInt), (1 ≤ x.re) → ((x.re
        ≤ (P.q : Int) - 1) → ((1 ≤ x.im) → ((x.im ≤ (P.q : Int) - 1) → (
    let n := FordBoundaryMultiplicity P x;
    (n = 2 → FourNeighborLaplacian g x = 1) ∧
      (n = 3 → FourNeighborLaplacian g x = 0) ∧
      (n = 4 → FourNeighborLaplacian g x = -2))))))))))))) := by
  classical
  intro P g hbdy hrec ha ceilShift boundaryValue axes lapCoord hbig x hr hr' hs hs'
  dsimp
  let a : Int := P.q₁
  let b : Int := P.q₂
  let A := P.p₁
  let B := P.p₂
  let cdiv (n d : Int) := -((-n) / d)
  have hsum : (P.q : Int) = a + b := FordLaplacianDetails.hsumAt824 P
  have hp : P.p = A + B := P.sum_p
  have hdet : A * b - B * a = 1 := FordLaplacianDetails.hdetAt828 P hsum hp
  have hb : 0 < b := by dsimp [b]; exact_mod_cast P.q₂_pos
  have ha0 : 0 < a := FordLaplacianProof.ha0 P hbig hsum
  have hcop : Nat.Coprime P.q₁ A.natAbs ∧ Nat.Coprime P.q₂ B.natAbs :=
      FordLaplacianDetails.hcop P hdet
  obtain ⟨P₁, ⟨hp₁, hq₁⟩, _⟩ := FordFareyParentsExist A P.q₁ (by omega) hcop.1
  obtain ⟨P₂, ⟨hp₂, hq₂⟩, _⟩ := FordFareyParentsExist B P.q₂ P.q₂_pos hcop.2
  obtain ⟨rec0, rec1, rec2, rec3⟩ := hrec P P₁ P₂ hbig hp₁ hq₁ hp₂ hq₂
  have parentValue (R : FordFareyParameter) (r s : Int)
      (hrect : 0 ≤ r ∧ r ≤ R.q ∧ 0 ≤ s ∧ s ≤ R.q)
      (hedge : r ≤ 1 ∨ (R.q : Int) - 1 ≤ r ∨
        s ≤ 1 ∨ (R.q : Int) - 1 ≤ s) :
      Classical.choose FordOdometerFamilyExistsUnique R ⟨r, s⟩ =
        cdiv (R.p * r * s) R.q := FordLaplacianProof.parentValue hbdy R r s hrect hedge
  -- Use the literal restrictions on the four parent doubled boundaries.
  have v0 (r s : Int) (hrect : 0 ≤ r ∧ r ≤ a ∧ 0 ≤ s ∧ s ≤ a)
      (hedge : r ≤ 1 ∨ a - 1 ≤ r ∨ s ≤ 1 ∨ a - 1 ≤ s) :
      g ⟨r, s⟩ = cdiv (A * r * s) a := FordLaplacianDetails.v0 P P₁ hp₁ hq₁ rec0 parentValue r
          s hrect hedge
  have v2 (r s : Int) (hrect : a ≤ r ∧ r ≤ P.q ∧ 0 ≤ s ∧ s ≤ b)
      (hedge : r - a ≤ 1 ∨ b - 1 ≤ r - a ∨ s ≤ 1 ∨ b - 1 ≤ s) :
      g ⟨r, s⟩ = cdiv (B * (r - a) * s) b + A * s := FordLaplacianProof.v2 P hsum P₁ hq₁ P₂
          hp₂ hq₂ rec2 parentValue r s hrect hedge
  have v3 (r s : Int) (hrect : 0 ≤ r ∧ r ≤ b ∧ a ≤ s ∧ s ≤ P.q)
      (hedge : r ≤ 1 ∨ b - 1 ≤ r ∨ s - a ≤ 1 ∨ b - 1 ≤ s - a) :
      g ⟨r, s⟩ = cdiv (B * r * (s - a)) b + A * r := FordLaplacianProof.v3 P hsum P₁ hq₁ P₂
          hp₂ hq₂ rec3 parentValue r s hrect hedge
  have cminus (d n k : Int) (hd : d ≠ 0) : cdiv (k * d - n) d = k - n / d :=
      FordLaplacianDetails.cminus d n k hd
  have cmul (d k : Int) (hd : d ≠ 0) : cdiv (k * d) d = k := by
    simpa using cminus d 0 k hd
  have edge0 (t : Int) (ht : 0 ≤ t) (ht' : t ≤ a) :
      g ⟨a, t⟩ = A * t ∧ g ⟨t, a⟩ = A * t := FordLaplacianDetails.edge0 P ha0 P₁ hq₁ v0
          cmul t ht ht'
  have near0 (t : Int) (ht : 0 ≤ t) (ht' : t ≤ a) :
      g ⟨a - 1, t⟩ = A * t - A * t / a ∧
      g ⟨t, a - 1⟩ = A * t - A * t / a := FordLaplacianProof.near0 P ha0 P₁ hq₁ v0 cminus
          t ht ht'
  have outward (t : Int) (ht : 0 ≤ t) (ht' : t ≤ b) :
      g ⟨a + 1, t⟩ = cdiv (B * t) b + A * t ∧
      g ⟨t, a + 1⟩ = cdiv (B * t) b + A * t := FordLaplacianDetails.outward P ha hsum P₂
          hq₂ v2 v3 t ht ht'
  have lowFormula (t : Int) (ht : 0 < t) (hta : t < a) (htb : t ≤ b) :
      FourNeighborLaplacian g ⟨a, t⟩ = cdiv (B * t) b - A * t / a ∧
      FourNeighborLaplacian g ⟨t, a⟩ = cdiv (B * t) b - A * t / a :=
          FordLaplacianProof.lowFormula P lapCoord edge0 near0 outward t ht hta htb
  have highFormula (t : Int) (ht : 0 < t) (hta : t ≤ a) (htb : t < b) :
      FourNeighborLaplacian g ⟨(P.q : Int) - t, b⟩ = cdiv (B * t) b - A * t / a ∧
      FourNeighborLaplacian g ⟨b, (P.q : Int) - t⟩ = cdiv (B * t) b - A * t / a :=
          FordLaplacianProof.highFormula P lapCoord hsum hdet hb ha0 P₁ hq₁ P₂ hq₂ cminus
          (FordLaplacianDetails.cplus) (FordLaplacianProof.edge2 P ha hsum hdet hb P₁ hq₁ P₂
              hq₂ v2 v3 cmul) ((show
                  ∀ (r : ℤ), b ≤ r → r ≤ (↑P.q : ℤ) → g ⟨r, b + (1 : ℤ)⟩ =
                  cdiv (A * (r - b)) a + B * r + B + (1 : ℤ) ∧ g ⟨b + (1 : ℤ),
                  r⟩ = cdiv (A * (r - b)) a + B * r + B + (1 : ℤ)
                from by
                  classical
                  intro r ht ht'
                  have hl := ((FordLaplacianProof.v1 P hsum P₁ hp₁ hq₁ P₂ hq₂ rec1
                      parentValue)) r (b + 1) (by omega) (by omega)
                  have hv := ((FordLaplacianProof.v1 P hsum P₁ hp₁ hq₁ P₂ hq₂ rec1
                      parentValue)) (b + 1) r (by omega) (by omega)
                  change g ⟨r, b + 1⟩ = cdiv (A * (r - b) * (b + 1 - b)) a +
                    B * r + B * (b + 1) - B * b + 1 at hl
                  change g ⟨b + 1, r⟩ = cdiv (A * (b + 1 - b) * (r - b)) a +
                    B * (b + 1) + B * r - B * b + 1 at hv
                  simp only [add_sub_cancel_left, mul_one] at hl hv
                  constructor
                  · nlinarith only [hl]
                  · nlinarith only [hv]))
              (FordLaplacianDetails.near2 P ha hsum P₁ hq₁ P₂ hq₂ v2 v3) t ht hta htb
  have roundArm (t : Int) (ht : 0 < t) (hta : t < a) (htb : t < b) :
      cdiv (B * t) b - A * t / a = 1 := FordLaplacianProof.roundArm P hdet hb ha0 t ht hta htb
  have rectBoundary (l r d u : Int) (z : GaussianInt) :
      z ∈ LatticeVertexBoundary {w : GaussianInt |
        l ≤ w.re ∧ w.re ≤ r ∧ d ≤ w.im ∧ w.im ≤ u} ↔
      (l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u) ∧
        (z.re = l ∨ z.re = r ∨ z.im = d ∨ z.im = u) := FordLaplacianProof.rectBoundary l r d u z
  have count : FordBoundaryMultiplicity P x =
      (if x.re ≤ a ∧ x.im ≤ a ∧ (x.re = a ∨ x.im = a) then 1 else 0) +
      (if b ≤ x.re ∧ b ≤ x.im ∧ (x.re = b ∨ x.im = b) then 1 else 0) +
      (if a ≤ x.re ∧ x.im ≤ b ∧ (x.re = a ∨ x.im = b) then 1 else 0) +
      (if x.re ≤ b ∧ a ≤ x.im ∧ (x.re = b ∨ x.im = a) then 1 else 0) :=
          FordLaplacianProof.count P x (FordLaplacianDetails.b0 P x hr hs ha0 P₁ hq₁
              rectBoundary) (FordLaplacianDetails.b1 P x hr' hs' hsum P₁ hq₁ P₂ hq₂ rectBoundary)
              (FordLaplacianDetails.b2 P x hr' hs hsum P₁ hq₁ P₂ hq₂ rectBoundary)
              (FordLaplacianDetails.b3 P ha x hr hs' hsum P₁ hq₁ P₂ hq₂ rectBoundary)
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    have hcase : (x.re = a ∧ x.im < a ∧ x.im < b) ∨
        (x.im = a ∧ x.re < a ∧ x.re < b) ∨
        (x.im = b ∧ a < x.re ∧ b < x.re) ∨
        (x.re = b ∧ a < x.im ∧ b < x.im) := FordLaplacianDetails.hcaseAt964 P x count hn
    rcases hcase with h | h | h | h
    · have hx : x = ⟨a, x.im⟩ := by ext <;> simp [h.1]
      rw [hx]
      exact (lowFormula x.im (by omega) h.2.1 (by omega)).1.trans
        (roundArm x.im (by omega) h.2.1 h.2.2)
    · have hx : x = ⟨x.re, a⟩ := by ext <;> simp [h.1]
      rw [hx]
      exact (lowFormula x.re (by omega) h.2.1 (by omega)).2.trans
        (roundArm x.re (by omega) h.2.1 h.2.2)
    · have hx : x = ⟨(P.q : Int) - ((P.q : Int) - x.re), b⟩ := by ext <;> simp [h.1]
      rw [hx]
      exact (highFormula ((P.q : Int) - x.re) (by omega) (by omega) (by omega)).1.trans
        (roundArm ((P.q : Int) - x.re) (by omega) (by omega) (by omega))
    · have hx : x = ⟨b, (P.q : Int) - ((P.q : Int) - x.im)⟩ := by ext <;> simp [h.1]
      rw [hx]
      exact (highFormula ((P.q : Int) - x.im) (by omega) (by omega) (by omega)).2.trans
        (roundArm ((P.q : Int) - x.im) (by omega) (by omega) (by omega))
  · intro hn
    have hcase : (b < a ∧ ((x.re = a ∧ x.im = b) ∨ (x.re = b ∧ x.im = a))) ∨
        (a < b ∧ ((x.re = a ∧ x.im = a) ∨ (x.re = b ∧ x.im = b))) :=
            FordLaplacianDetails.hcaseAt988 P x count hn
    rcases hcase with ⟨hab, hcase⟩ | ⟨hab, hcase⟩
    · have hf : A * b / a = B := FordLaplacianDetails.hfAt993 P ha hsum hdet ha0 P₁ hq₁ P₂
        hq₂ hab
      have hc : cdiv (B * b) b = B := cmul b B (ne_of_gt hb)
      rcases hcase with h | h
      · have hx : x = ⟨a, b⟩ := by ext <;> simp [h.1, h.2]
        rw [hx, (lowFormula b hb hab le_rfl).1, hc, hf]
        ring
      · have hx : x = ⟨b, a⟩ := by ext <;> simp [h.1, h.2]
        rw [hx, (lowFormula b hb hab le_rfl).2, hc, hf]
        ring
    · have hc : cdiv (B * a) b = A := FordLaplacianDetails.hcAt1006 P ha hbig hsum hdet hb P₁
        hq₁ P₂ hq₂ cminus hab
      have hf : A * a / a = A := Int.mul_ediv_cancel _ (ne_of_gt ha0)
      rcases hcase with h | h
      · have hx : x = ⟨a, a⟩ := by ext <;> simp [h.1, h.2]
        have hv0 := edge0 a ha0.le le_rfl
        have hvm := near0 a ha0.le le_rfl
        have hvp := outward a ha0.le (by omega)
        rw [hc] at hvp
        rw [hf] at hvm
        rw [hx, lapCoord, hvp.1, hvm.1, hvp.2, hvm.2, hv0.1]
        ring
      · have hx : x = ⟨b, b⟩ := by ext <;> simp [h.1, h.2]
        have he : (P.q : Int) - a = b := by omega
        have hh := (highFormula a ha0 le_rfl hab).1
        rw [he, hc, hf] at hh
        rw [hx]
        simpa using hh
  · intro hn
    clear * - P g hn hr hr' hs hs' ceilShift boundaryValue axes lapCoord
    have hall : ∀ i, x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i) :=
        FordLaplacianDetails.hall P x hn
    have h0 := (hall 0).1
    have h1 := (hall 1).1
    have h2 := (hall 2).1
    have h3 := (hall 3).1
    change 0 ≤ x.re ∧ x.re ≤ P.q₁ ∧ 0 ≤ x.im ∧ x.im ≤ P.q₁ at h0
    change (P.q₂ : Int) ≤ x.re ∧ x.re ≤ P.q ∧
      (P.q₂ : Int) ≤ x.im ∧ x.im ≤ P.q at h1
    change (P.q₁ : Int) ≤ x.re ∧ x.re ≤ P.q ∧
      0 ≤ x.im ∧ x.im ≤ P.q₂ at h2
    change 0 ≤ x.re ∧ x.re ≤ P.q₂ ∧
      (P.q₁ : Int) ≤ x.im ∧ x.im ≤ P.q at h3
    have he : (P.q₁ : Int) = P.q₂ := by omega
    have hsum : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
    have hdet := P.det₁
    have hp := P.sum_p
    have hd : (P.q₁ : Int) ∣ 1 := FordLaplacianDetails.hdAt1050 P he hsum hdet hp
    have ha1 := Int.le_of_dvd (by norm_num : (0 : Int) < 1) hd
    have hqa : (P.q₁ : Int) = 1 := by omega
    have hqq : (P.q : Int) = 2 := by omega
    have hx : x = ⟨1, 1⟩ := by ext <;> dsimp <;> omega
    have hnum : P.p = P.p₁ * 2 - 1 := FordLaplacianDetails.hnum P hdet hqa hqq
    have hc := boundaryValue 1 1 (by omega) (by omega)
      (by omega) (by omega) (by omega)
    norm_num only [mul_one] at hc
    rw [hnum, hqq] at hc
    rw [neg_sub] at hc
    have hround := ceilShift 1 P.p₁
    rw [hqq] at hround
    norm_num at hround
    rw [hround] at hc
    have hv := axes 2 (by omega) (by omega)
    have hv0 := axes 1 (by omega) (by omega)
    have hvR : g ⟨2, 1⟩ = P.p := FordLaplacianDetails.hvR P hqq hv
    have hvU : g ⟨1, 2⟩ = P.p := FordLaplacianDetails.hvU P hqq hv
    rw [hx, lapCoord]
    norm_num only
    rw [hvR, hv0.2.1, hvU, hv0.1, hc]
    nlinarith only [hnum]

end FordInteriorCase

theorem FordLaplacianTable (P : FordFareyParameter) :
    (∀ x, FourNeighborLaplacian (FordOdometer P) x =
      FourNeighborLaplacian (FordOdometer P) (x + ⟨0, (P.q : Int)⟩) ∧
      FourNeighborLaplacian (FordOdometer P) x =
      FourNeighborLaplacian (FordOdometer P)
        (x + ⟨(P.q : Int), (P.q₁ : Int)⟩)) ∧
    (∀ x, x ∈ LatticeVertexBoundary (FordVertexDomain P.q) ->
      FourNeighborLaplacian (FordOdometer P) x = 1) ∧
    (1 < P.q -> ∀ x,
      1 <= x.re -> x.re <= (P.q : Int) - 1 ->
      1 <= x.im -> x.im <= (P.q : Int) - 1 ->
      let n := FordBoundaryMultiplicity P x;
      (n = 2 -> FourNeighborLaplacian (FordOdometer P) x = 1) ∧
      (n = 3 -> FourNeighborLaplacian (FordOdometer P) x = 0) ∧
      (n = 4 -> FourNeighborLaplacian (FordOdometer P) x = -2)) := by
-- BODY
  classical
  let g := FordOdometer P
  obtain ⟨hbase, hbdy, hneg, hpos, hneg₂, hrec⟩ :=
    (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  have hq : 0 < (P.q : Int) := by exact_mod_cast P.q_pos
  have hqne : (P.q : Int) ≠ 0 := ne_of_gt hq
  have ha : (P.q₁ : Int) < P.q := by exact_mod_cast P.q₁_lt
  have periodic (v : GaussianInt) (a b c : Int)
      (h : ∀ x, g (x + v) = g x + a * x.re + b * x.im + c) :
      ∀ x, FourNeighborLaplacian g (x + v) = FourNeighborLaplacian g x :=
          FordLaplacianProof.periodic P v a b c h
  have periodNeg := periodic ⟨0, -(P.q : Int)⟩ (-P.p) 0 0
    (by intro x; have h := hneg P x; change g _ = g _ - _ at h; nlinarith only [h])
  have periodPos := periodic ⟨(P.q : Int), (P.q₁ : Int)⟩
    P.p₁ P.p ((P.q₁ : Int) * P.p) (hpos P)
  have periodUp (x : GaussianInt) :
      FourNeighborLaplacian g (x + ⟨0, (P.q : Int)⟩) =
        FourNeighborLaplacian g x := FordLaplacianDetails.periodUp P periodNeg x
  have ceilShift (n k : Int) :
      -((-(k * (P.q : Int) - n)) / (P.q : Int)) = k - n / (P.q : Int) :=
          FordLaplacianDetails.ceilShift P hqne n k
  have boundaryValue (r s : Int)
      (hr : 0 ≤ r) (hr' : r ≤ P.q) (hs : 0 ≤ s) (hs' : s ≤ P.q)
      (hedge : r ≤ 1 ∨ (P.q : Int) - 1 ≤ r ∨
        s ≤ 1 ∨ (P.q : Int) - 1 ≤ s) :
      g ⟨r, s⟩ = -((-(P.p * r * s)) / (P.q : Int)) := FordLaplacianProof.boundaryValue P hbdy r s
          hr hr' hs hs' hedge
  have axes (t : Int) (ht : 0 ≤ t) (ht' : t ≤ P.q) :
      g ⟨t, 0⟩ = 0 ∧ g ⟨0, t⟩ = 0 ∧
      g ⟨t, 1⟩ = -((- (P.p * t)) / (P.q : Int)) ∧
      g ⟨1, t⟩ = -((- (P.p * t)) / (P.q : Int)) := FordLaplacianDetails.axes P hq boundaryValue t
          ht ht'
  -- The left neighbor has numerator p*t - 1, unlike the lower neighbor.
  have left (t : Int) (ht : 0 ≤ t) (ht' : t ≤ P.q) :
      g ⟨-1, t⟩ = -((P.p * t - 1) / (P.q : Int)) := FordLaplacianProof.left P hpos hneg₂ hq hqne
          ha ceilShift boundaryValue t ht ht'
  have lapCoord (r s : Int) : FourNeighborLaplacian g ⟨r, s⟩ =
      g ⟨r + 1, s⟩ + g ⟨r - 1, s⟩ +
      g ⟨r, s + 1⟩ + g ⟨r, s - 1⟩ - 4 * g ⟨r, s⟩ := FordLaplacianDetails.lapCoord P r s
  have roundInterior (t : Int) (ht : 0 < t) (ht' : t < P.q) :
      -((- (P.p * t)) / (P.q : Int)) - P.p * t / (P.q : Int) = 1 ∧
      (P.p * t - 1) / (P.q : Int) = P.p * t / (P.q : Int) := FordLaplacianProof.roundInterior P
          hq hqne (FordLaplacianProof.nondiv P) t ht ht'
  have bottomLap (t : Int) (ht : 0 ≤ t) (ht' : t < P.q) :
      FourNeighborLaplacian g ⟨t, 0⟩ = 1 := FordLaplacianProof.bottomLap P hq axes
          (FordLaplacianProof.below P hneg hq ceilShift boundaryValue) left
          lapCoord roundInterior t ht ht'
  have leftLap (t : Int) (ht : 0 ≤ t) (ht' : t ≤ P.q) :
      FourNeighborLaplacian g ⟨0, t⟩ = 1 := FordLaplacianProof.leftLap P hq periodUp axes left
          lapCoord roundInterior bottomLap t ht ht'
  have rightLap (t : Int) (ht : 0 ≤ t) (ht' : t ≤ P.q) :
      FourNeighborLaplacian g ⟨(P.q : Int), t⟩ = 1 := FordLaplacianProof.rightLap P ha periodNeg
          periodPos leftLap t ht ht'
  have bottomClosed (t : Int) (ht : 0 ≤ t) (ht' : t ≤ P.q) :
      FourNeighborLaplacian g ⟨t, 0⟩ = 1 := FordLaplacianDetails.bottomClosed P hq bottomLap
          rightLap t ht ht'
  have interiorLaplacian (hbig : 1 < P.q) (x : GaussianInt)
      (hr : 1 ≤ x.re) (hr' : x.re ≤ (P.q : Int) - 1)
      (hs : 1 ≤ x.im) (hs' : x.im ≤ (P.q : Int) - 1) :
      let n := FordBoundaryMultiplicity P x;
      (n = 2 → FourNeighborLaplacian g x = 1) ∧
      (n = 3 → FourNeighborLaplacian g x = 0) ∧
      (n = 4 → FourNeighborLaplacian g x = -2) := FordInteriorCase.interiorLaplacian P hbdy hrec
          ha ceilShift boundaryValue axes lapCoord hbig x hr hr' hs hs'
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨(periodUp x).symm, (periodPos x).symm⟩
  · intro x hx
    have hxrect := hx.1
    change 0 ≤ x.re ∧ x.re ≤ P.q ∧ 0 ≤ x.im ∧ x.im ≤ P.q at hxrect
    have hedge : x.re = 0 ∨ x.re = P.q ∨ x.im = 0 ∨ x.im = P.q := FordLaplacianDetails.hedge P x
        hx hxrect
    have hxcoord : x = ⟨x.re, x.im⟩ := by rfl
    rw [hxcoord]
    rcases hedge with hl | hr | hb | ht
    · rw [hl]
      exact leftLap x.im hxrect.2.2.1 hxrect.2.2.2
    · rw [hr]
      exact rightLap x.im hxrect.2.2.1 hxrect.2.2.2
    · rw [hb]
      exact bottomClosed x.re hxrect.1 hxrect.2.1
    · rw [ht]
      have he : (⟨x.re, 0⟩ : GaussianInt) +
          ⟨0, (P.q : Int)⟩ = ⟨x.re, (P.q : Int)⟩ := by ext <;> simp
      rw [← he, periodUp]
      exact bottomClosed x.re hxrect.1 hxrect.2.1
  · exact interiorLaplacian

end ApollonianSuperharmonic

end
