/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4062T1RecursiveInteriors
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import Mathlib.RingTheory.Int.Basic

-- [TABLET NODE: P4062T1ParentalRestriction]

/-!
# P4062T1ParentalRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ParentalRestrictionProof

private theorem squareCoordinates :
    ∀ (q : ℕ), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔ (1 : ℤ) ≤ x.re ∧ x.re ≤ (↑q :
        ℤ) - (1 : ℤ) ∧ (1 : ℤ) ≤ x.im ∧ x.im ≤ (↑q : ℤ) - (1 : ℤ) := by
  classical
  intro q x
  unfold P4062T1InteriorSquare
  constructor
  · intro hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2,
      (Finset.mem_Icc.mp hb).1, (Finset.mem_Icc.mp hb).2⟩
  · intro h
    exact Finset.mem_image.mpr ⟨(x.re, x.im),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩,
        Finset.mem_Icc.mpr h.2.2⟩, by cases x; rfl⟩

private theorem hparent₁pos :
    ∀ (P : FordFareyParameter), ((2 : ℕ) < P.q) → ((P.q = P.q₁ + P.q₂) → (1 < P.q → 0 < P.q₁)) := by
  classical
  intro P hP hsum hbig
  by_contra hn
  have hz : P.q₁ = 0 := by omega
  have hdvd : (P.q : Int) ∣ (1 : Int) := by
    refine ⟨P.p₁, ?_⟩
    have hdet := P.det₁
    rw [hz] at hdet
    have hmul : P.p₁ * (P.q : Int) = 1 := by simpa using hdet
    calc
      1 = P.p₁ * (P.q : Int) := hmul.symm
      _ = (P.q : Int) * P.p₁ := by ring
  have hqint : 1 < (P.q : Int) := by exact_mod_cast hbig
  have hle := Int.le_of_dvd (by norm_num : (0 : Int) < 1) hdvd
  omega

private theorem hparents :
    ∀ (P : FordFareyParameter), (1 < P.q → 0 < P.q₁) → ((Nat.Coprime P.q₁ P.p₁.natAbs ∧
        Nat.Coprime P.q₂ P.p₂.natAbs) → (1 < P.q → ∃ P₁ P₂ : FordFareyParameter, P₁.p = P.p₁ ∧
        P₁.q = P.q₁ ∧ P₂.p = P.p₂ ∧ P₂.q = P.q₂)) := by
  classical
  intro P hparent₁pos hcoparents hbig
  obtain ⟨P₁, ⟨hp₁, hq₁⟩, _⟩ :=
    FordFareyParentsExist P.p₁ P.q₁ (hparent₁pos hbig) hcoparents.1
  obtain ⟨P₂, ⟨hp₂, hq₂⟩, _⟩ :=
    FordFareyParentsExist P.p₂ P.q₂ P.q₂_pos hcoparents.2
  exact ⟨P₁, P₂, hp₁, hq₁, hp₂, hq₂⟩

private theorem hrecursive :
    ∀ (P : FordFareyParameter), (1 < P.q → ∃ P₁ P₂ : FordFareyParameter, P₁.p = P.p₁ ∧ P₁.q =
        P.q₁ ∧ P₂.p = P.p₂ ∧ P₂.q = P.q₂) → ((∀ (P : FordFareyParameter), ∀ (P₁ :
            FordFareyParameter), ∀ (P₂ : FordFareyParameter), (1 : ℕ) < P.q → P₁.p = P.p₁ → P₁.q =
        P.q₁ → P₂.p = P.p₂ → P₂.q = P.q₂ → (∀ x ∈ FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)),
        Classical.choose FordOdometerFamilyExistsUnique P x = Classical.choose
        FordOdometerFamilyExistsUnique P₁ x) ∧ (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 :
        ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x = Classical.choose
        FordOdometerFamilyExistsUnique P₁ (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) + P.p₂ * x.re + P.p₂ *
        x.im - P.p₂ * (↑P.q₂ : ℤ) + (1 : ℤ)) ∧ (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 :
        ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x = Classical.choose
        FordOdometerFamilyExistsUnique P₂ (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) + P.p₁ * x.im) ∧ ∀ x ∈
        FordRecursiveVertexDomains P (3 : Fin (4 : ℕ)), Classical.choose
        FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique P₂
        (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) + P.p₁ * x.re) → (1 < P.q → ∃ P₁ P₂ : FordFareyParameter,
        P₁.p = P.p₁ ∧ P₁.q = P.q₁ ∧ P₂.p = P.p₂ ∧ P₂.q = P.q₂ ∧ (∀ x, x ∈
        FordRecursiveVertexDomains P 0 → FordOdometer P x = FordOdometer P₁ x) ∧ (∀ x, x ∈
        FordRecursiveVertexDomains P 1 → FordOdometer P x = FordOdometer P₁ (x - ⟨(P.q₂ : Int),
        (P.q₂ : Int)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1) ∧ (∀ x, x ∈
        FordRecursiveVertexDomains P 2 → FordOdometer P x = FordOdometer P₂ (x - ⟨(P.q₁ : Int),
        0⟩) + P.p₁ * x.im) ∧ (∀ x, x ∈ FordRecursiveVertexDomains P 3 → FordOdometer P x =
        FordOdometer P₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re))) := by
  classical
  intro P hparents hrec hbig
  rcases hparents hbig with ⟨P₁, P₂, hp₁, hq₁, hp₂, hq₂⟩
  obtain ⟨rec₀, rec₁, rec₂, rec₃⟩ :=
    hrec P P₁ P₂ hbig hp₁ hq₁ hp₂ hq₂
  refine ⟨P₁, P₂, hp₁, hq₁, hp₂, hq₂, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simpa [FordOdometer] using rec₀ x hx
  · intro x hx
    simpa [FordOdometer] using rec₁ x hx
  · intro x hx
    simpa [FordOdometer] using rec₂ x hx
  · intro x hx
    simpa [FordOdometer] using rec₃ x hx

private theorem hlapAffine :
    ∀ (f : GaussianInt → ℤ), ∀ (f' : GaussianInt → ℤ), ∀ (x : GaussianInt), ∀ (t : GaussianInt),
        ∀ (A : ℤ), ∀ (B : ℤ), ∀ (C : ℤ), f x = f' (x - t) + A * x.re + B * x.im + C → f (x - (1 :
        GaussianInt)) = f' (x - t - (1 : GaussianInt)) + A * (x - (1 : GaussianInt)).re + B * (x
        - (1 : GaussianInt)).im + C → f (x + (1 : GaussianInt)) = f' (x - t + (1 : GaussianInt))
        + A * (x + (1 : GaussianInt)).re + B * (x + (1 : GaussianInt)).im + C → f (x - ⟨(0 : ℤ),
        (1 : ℤ)⟩) = f' (x - t - ⟨(0 : ℤ), (1 : ℤ)⟩) + A * (x - ⟨(0 : ℤ), (1 : ℤ)⟩).re + B * (x -
        ⟨(0 : ℤ), (1 : ℤ)⟩).im + C → f (x + ⟨(0 : ℤ), (1 : ℤ)⟩) = f' (x - t + ⟨(0 : ℤ), (1 : ℤ)⟩)
        + A * (x + ⟨(0 : ℤ), (1 : ℤ)⟩).re + B * (x + ⟨(0 : ℤ), (1 : ℤ)⟩).im + C →
        FourNeighborLaplacian f x = FourNeighborLaplacian f' (x - t) := by
  classical
  intro f f' x t A B C h0 hm hp hmi hpi
  rw [FourNeighborLaplacian, hm, hp, hmi, hpi, h0,
    FourNeighborLaplacian]
  rw [show x - t - 1 = (x - t) - 1 by abel,
    show x - t + 1 = (x - t) + 1 by abel,
    show x - t - ⟨0, 1⟩ = (x - t) - ⟨0, 1⟩ by rfl,
    show x - t + ⟨0, 1⟩ = (x - t) + ⟨0, 1⟩ by rfl]
  simp
  ring

private theorem hchild0Lap :
    ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), (FordFareyParameter) → ((P₁.q =
        P.q₁) → ((∀ x ∈ FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)), FordOdometer P x =
        FordOdometer P₁ x) → ((∀ (z : GaussianInt), (0 ≤ z.re) → ((z.re ≤ (P.q₁ : Int)) → ((0 ≤
        z.im) → ((z.im ≤ (P.q₁ : Int)) → (z ∈ FordRecursiveVertexDomains P 0))))) → (∀ (x :
            GaussianInt), (1 : ℤ) ≤ x.re → x.re ≤ (↑P.q₁ : ℤ) - (1 : ℤ) → (1 : ℤ) ≤ x.im → x.im ≤
        (↑P.q₁ : ℤ) - (1 : ℤ) → FourNeighborLaplacian (FordOdometer P) x = FourNeighborLaplacian
        (FordOdometer P₁) x)))) := by
  classical
  intro P P₁ P₂ hq₁ hrec₀ hrec0Member x hxr hxr' hxi hxi'
  have hmem :
      x ∈ FordRecursiveVertexDomains P 0 ∧
      x - 1 ∈ FordRecursiveVertexDomains P 0 ∧
      x + 1 ∈ FordRecursiveVertexDomains P 0 ∧
      x - ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 0 ∧
      x + ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hrec0Member x (by omega) (by omega) (by omega) (by omega)
    · apply hrec0Member (x - 1) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec0Member (x + 1) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec0Member (x - ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
          ] <;> omega
    · apply hrec0Member (x + ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add,
          ] <;> omega
  unfold FourNeighborLaplacian
  rw [hrec₀ x hmem.1, hrec₀ (x - 1) hmem.2.1,
    hrec₀ (x + 1) hmem.2.2.1,
    hrec₀ (x - ⟨0, 1⟩) hmem.2.2.2.1,
    hrec₀ (x + ⟨0, 1⟩) hmem.2.2.2.2]

private theorem hchild1Lap :
    ∀ (P : FordFareyParameter), (P.q = P.q₁ + P.q₂) → (∀ (P₁ : FordFareyParameter), ∀ (P₂ :
        FordFareyParameter), (P₁.q = P.q₁) → ((P₂.q = P.q₂) → ((∀ x ∈ FordRecursiveVertexDomains
        P (1 : Fin (4 : ℕ)), FordOdometer P x = FordOdometer P₁ (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩)
        + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (↑P.q₂ : ℤ) + (1 : ℤ)) → ((∀ (f : GaussianInt →
        Int), ∀ (f' : GaussianInt → Int), ∀ (x : GaussianInt), ∀ (t : GaussianInt), ∀ (A : Int),
            ∀ (B : Int), ∀ (C : Int), (f x = f' (x - t) + A * x.re + B * x.im + C) → ((f (x - 1)
            = f'
        ((x - t) - 1) + A * (x - 1).re + B * (x - 1).im + C) → ((f (x + 1) = f' ((x - t) + 1) + A
        * (x + 1).re + B * (x + 1).im + C) → ((f (x - ⟨0, 1⟩) = f' ((x - t) - ⟨0, 1⟩) + A * (x -
        ⟨0, 1⟩).re + B * (x - ⟨0, 1⟩).im + C) → ((f (x + ⟨0, 1⟩) = f' ((x - t) + ⟨0, 1⟩) + A * (x
        + ⟨0, 1⟩).re + B * (x + ⟨0, 1⟩).im + C) → (FourNeighborLaplacian f x =
        FourNeighborLaplacian f' (x - t))))))) → ((∀ (z : GaussianInt), ((P.q₂ : Int) ≤ z.re) →
        ((z.re ≤ (P.q : Int)) → (((P.q₂ : Int) ≤ z.im) → ((z.im ≤ (P.q : Int)) → (z ∈
        FordRecursiveVertexDomains P 1))))) → (∀ (x : GaussianInt), (↑P.q₂ : ℤ) + (1 : ℤ) ≤ x.re
        → x.re ≤ (↑P.q : ℤ) - (1 : ℤ) → (↑P.q₂ : ℤ) + (1 : ℤ) ≤ x.im → x.im ≤ (↑P.q : ℤ) - (1 :
        ℤ) → FourNeighborLaplacian (FordOdometer P) x = FourNeighborLaplacian (FordOdometer P₁)
        (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩))))))) := by
  classical
  intro P hsum P₁ P₂ hq₁ hq₂ hrec₁ hlapAffine hrec1Member x hxr hxr' hxi hxi'
  have hmem :
      x ∈ FordRecursiveVertexDomains P 1 ∧
      x - 1 ∈ FordRecursiveVertexDomains P 1 ∧
      x + 1 ∈ FordRecursiveVertexDomains P 1 ∧
      x - ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 1 ∧
      x + ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hrec1Member x (by omega) (by omega) (by omega) (by omega)
    · apply hrec1Member (x - 1) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec1Member (x + 1) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec1Member (x - ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
          ] <;> omega
    · apply hrec1Member (x + ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add,
          ] <;> omega
  apply hlapAffine (FordOdometer P) (FordOdometer P₁) x
    ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ P.p₂ P.p₂
    (-P.p₂ * (P.q₂ : Int) + 1)
  · convert hrec₁ x hmem.1 using 1; ring
  · convert hrec₁ (x - 1) hmem.2.1 using 1; ring
  · convert hrec₁ (x + 1) hmem.2.2.1 using 1; ring
  · convert hrec₁ (x - ⟨0, 1⟩) hmem.2.2.2.1 using 1; ring
  · convert hrec₁ (x + ⟨0, 1⟩) hmem.2.2.2.2 using 1; ring

private theorem hchild2Lap :
    ∀ (P : FordFareyParameter), (P.q = P.q₁ + P.q₂) → (∀ (P₁ : FordFareyParameter), ∀ (P₂ :
        FordFareyParameter), (P₁.q = P.q₁) → ((P₂.q = P.q₂) → ((∀ x ∈ FordRecursiveVertexDomains
        P (2 : Fin (4 : ℕ)), FordOdometer P x = FordOdometer P₂ (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) +
        P.p₁ * x.im) → ((∀ (f : GaussianInt → Int), ∀ (f' : GaussianInt → Int), ∀ (x :
            GaussianInt), ∀ (t : GaussianInt), ∀ (A : Int), ∀ (B : Int), ∀ (C : Int), (f x = f' (x -
        t) + A * x.re + B * x.im + C) → ((f (x - 1) = f' ((x - t) - 1) + A * (x - 1).re + B * (x
        - 1).im + C) → ((f (x + 1) = f' ((x - t) + 1) + A * (x + 1).re + B * (x + 1).im + C) →
        ((f (x - ⟨0, 1⟩) = f' ((x - t) - ⟨0, 1⟩) + A * (x - ⟨0, 1⟩).re + B * (x - ⟨0, 1⟩).im + C)
        → ((f (x + ⟨0, 1⟩) = f' ((x - t) + ⟨0, 1⟩) + A * (x + ⟨0, 1⟩).re + B * (x + ⟨0, 1⟩).im +
        C) → (FourNeighborLaplacian f x = FourNeighborLaplacian f' (x - t))))))) → ((∀ (z :
            GaussianInt), ((P.q₁ : Int) ≤ z.re) → ((z.re ≤ (P.q : Int)) → ((0 ≤ z.im) → ((z.im ≤
        (P.q₂ : Int)) → (z ∈ FordRecursiveVertexDomains P 2))))) → (∀ (x : GaussianInt), (↑P.q₁ :
        ℤ) + (1 : ℤ) ≤ x.re → x.re ≤ (↑P.q : ℤ) - (1 : ℤ) → (1 : ℤ) ≤ x.im → x.im ≤ (↑P.q₂ : ℤ) -
        (1 : ℤ) → FourNeighborLaplacian (FordOdometer P) x = FourNeighborLaplacian (FordOdometer
        P₂) (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩))))))) := by
  classical
  intro P hsum P₁ P₂ hq₁ hq₂ hrec₂ hlapAffine hrec2Member x hxr hxr' hxi hxi'
  have hmem :
      x ∈ FordRecursiveVertexDomains P 2 ∧
      x - 1 ∈ FordRecursiveVertexDomains P 2 ∧
      x + 1 ∈ FordRecursiveVertexDomains P 2 ∧
      x - ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 2 ∧
      x + ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hrec2Member x (by omega) (by omega) (by omega) (by omega)
    · apply hrec2Member (x - 1) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec2Member (x + 1) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec2Member (x - ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
          ] <;> omega
    · apply hrec2Member (x + ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add,
          ] <;> omega
  apply hlapAffine (FordOdometer P) (FordOdometer P₂) x
    ⟨(P.q₁ : Int), 0⟩ 0 P.p₁ 0
  · convert hrec₂ x hmem.1 using 1; ring
  · convert hrec₂ (x - 1) hmem.2.1 using 1; ring
  · convert hrec₂ (x + 1) hmem.2.2.1 using 1; ring
  · convert hrec₂ (x - ⟨0, 1⟩) hmem.2.2.2.1 using 1; ring
  · convert hrec₂ (x + ⟨0, 1⟩) hmem.2.2.2.2 using 1; ring

private theorem hchild3Lap :
    ∀ (P : FordFareyParameter), (P.q = P.q₁ + P.q₂) → (∀ (P₁ : FordFareyParameter), ∀ (P₂ :
        FordFareyParameter), (P₁.q = P.q₁) → ((P₂.q = P.q₂) → ((∀ x ∈ FordRecursiveVertexDomains
        P (3 : Fin (4 : ℕ)), FordOdometer P x = FordOdometer P₂ (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) +
        P.p₁ * x.re) → ((∀ (f : GaussianInt → Int), ∀ (f' : GaussianInt → Int), ∀ (x :
            GaussianInt), ∀ (t : GaussianInt), ∀ (A : Int), ∀ (B : Int), ∀ (C : Int), (f x = f' (x -
        t) + A * x.re + B * x.im + C) → ((f (x - 1) = f' ((x - t) - 1) + A * (x - 1).re + B * (x
        - 1).im + C) → ((f (x + 1) = f' ((x - t) + 1) + A * (x + 1).re + B * (x + 1).im + C) →
        ((f (x - ⟨0, 1⟩) = f' ((x - t) - ⟨0, 1⟩) + A * (x - ⟨0, 1⟩).re + B * (x - ⟨0, 1⟩).im + C)
        → ((f (x + ⟨0, 1⟩) = f' ((x - t) + ⟨0, 1⟩) + A * (x + ⟨0, 1⟩).re + B * (x + ⟨0, 1⟩).im +
        C) → (FourNeighborLaplacian f x = FourNeighborLaplacian f' (x - t))))))) → ((∀ (z :
            GaussianInt), (0 ≤ z.re) → ((z.re ≤ (P.q₂ : Int)) → (((P.q₁ : Int) ≤ z.im) → ((z.im ≤
        (P.q : Int)) → (z ∈ FordRecursiveVertexDomains P 3))))) → (∀ (x : GaussianInt), (1 : ℤ) ≤
        x.re → x.re ≤ (↑P.q₂ : ℤ) - (1 : ℤ) → (↑P.q₁ : ℤ) + (1 : ℤ) ≤ x.im → x.im ≤ (↑P.q : ℤ) -
        (1 : ℤ) → FourNeighborLaplacian (FordOdometer P) x = FourNeighborLaplacian (FordOdometer
        P₂) (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩))))))) := by
  classical
  intro P hsum P₁ P₂ hq₁ hq₂ hrec₃ hlapAffine hrec3Member x hxr hxr' hxi hxi'
  have hmem :
      x ∈ FordRecursiveVertexDomains P 3 ∧
      x - 1 ∈ FordRecursiveVertexDomains P 3 ∧
      x + 1 ∈ FordRecursiveVertexDomains P 3 ∧
      x - ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 3 ∧
      x + ⟨0, 1⟩ ∈ FordRecursiveVertexDomains P 3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hrec3Member x (by omega) (by omega) (by omega) (by omega)
    · apply hrec3Member (x - 1) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec3Member (x + 1) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one] <;> omega
    · apply hrec3Member (x - ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub,
          ] <;> omega
    · apply hrec3Member (x + ⟨0, 1⟩) <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add,
          ] <;> omega
  apply hlapAffine (FordOdometer P) (FordOdometer P₂) x
    ⟨0, (P.q₁ : Int)⟩ P.p₁ 0 0
  · convert hrec₃ x hmem.1 using 1; ring
  · convert hrec₃ (x - 1) hmem.2.1 using 1; ring
  · convert hrec₃ (x + 1) hmem.2.2.1 using 1; ring
  · convert hrec₃ (x - ⟨0, 1⟩) hmem.2.2.2.1 using 1; ring
  · convert hrec₃ (x + ⟨0, 1⟩) hmem.2.2.2.2 using 1; ring

end ParentalRestrictionProof

theorem P4062T1ParentalRestriction (P : FordFareyParameter)
    (hP : 2 < P.q) :
    ∃ P₁ P₂ : FordFareyParameter,
      P₁.p = P.p₁ ∧ P₁.q = P.q₁ ∧ P₂.p = P.p₂ ∧ P₂.q = P.q₂ ∧
      P₁.q < P.q ∧ P₂.q < P.q ∧ P.q₁ ≠ P.q₂ ∧
      ∀ i : Fin 4,
        let R := if i.val < 2 then P₁ else P₂
        let u : GaussianInt :=
          ![0, ⟨(P.q₂ : Int), (P.q₂ : Int)⟩,
            ⟨(P.q₁ : Int), 0⟩, ⟨0, (P.q₁ : Int)⟩] i
        P4062T1RecursiveInteriors P i =
          (P4062T1InteriorSquare R.q).image (fun x => x+u) ∧
        ∀ x ∈ P4062T1RecursiveInteriors P i,
          FourNeighborLaplacian (FordOdometer P) x =
            FourNeighborLaplacian (FordOdometer R) (x-u) := by
-- BODY
  classical
  have squareCoordinates (q : Nat) (x : GaussianInt) :
      x ∈ P4062T1InteriorSquare q ↔
        1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧
        1 ≤ x.im ∧ x.im ≤ (q : Int) - 1 := ParentalRestrictionProof.squareCoordinates q x
  have hqpos : 0 < P.q := P.q_pos
  have hsum : P.q = P.q₁ + P.q₂ := P.sum_q
  have hparent₁ : P.q₁ < P.q := P.q₁_lt
  have hcrossdet : P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 := by
    have hdet := P.det₁
    have hsumI : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
    rw [hsumI, P.sum_p] at hdet
    nlinarith only [hdet]
  have hparent₁pos : 1 < P.q → 0 < P.q₁ := ParentalRestrictionProof.hparent₁pos P hP hsum
  have hparent₂lt : 1 < P.q → P.q₂ < P.q := by
    intro hbig
    have hpos := hparent₁pos hbig
    omega
  have hcoparents :
      Nat.Coprime P.q₁ P.p₁.natAbs ∧ Nat.Coprime P.q₂ P.p₂.natAbs := by
    have h₁ : IsCoprime (P.q₁ : Int) P.p₁ :=
      ⟨-P.p₂, (P.q₂ : Int), by nlinarith only [hcrossdet]⟩
    have h₂ : IsCoprime (P.q₂ : Int) P.p₂ :=
      ⟨P.p₁, -(P.q₁ : Int), by nlinarith only [hcrossdet]⟩
    exact ⟨by simpa using Int.isCoprime_iff_nat_coprime.mp h₁,
      by simpa using Int.isCoprime_iff_nat_coprime.mp h₂⟩
  have hparents : 1 < P.q →
      ∃ P₁ P₂ : FordFareyParameter,
        P₁.p = P.p₁ ∧ P₁.q = P.q₁ ∧
        P₂.p = P.p₂ ∧ P₂.q = P.q₂ := ParentalRestrictionProof.hparents P hparent₁pos hcoparents
  obtain ⟨hbase, hbdy, hneg, hpos, hneg₂, hrec⟩ :=
    (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  have hrecursive : 1 < P.q →
      ∃ P₁ P₂ : FordFareyParameter,
        P₁.p = P.p₁ ∧ P₁.q = P.q₁ ∧
        P₂.p = P.p₂ ∧ P₂.q = P.q₂ ∧
        (∀ x, x ∈ FordRecursiveVertexDomains P 0 →
          FordOdometer P x = FordOdometer P₁ x) ∧
        (∀ x, x ∈ FordRecursiveVertexDomains P 1 →
          FordOdometer P x = FordOdometer P₁
            (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) +
              P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1) ∧
        (∀ x, x ∈ FordRecursiveVertexDomains P 2 →
          FordOdometer P x = FordOdometer P₂
            (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im) ∧
        (∀ x, x ∈ FordRecursiveVertexDomains P 3 →
          FordOdometer P x = FordOdometer P₂
            (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re) := ParentalRestrictionProof.hrecursive P
                hparents hrec
  have hbig : 1 < P.q := by omega
  rcases hrecursive hbig with
    ⟨P₁, P₂, hp₁, hq₁, hp₂, hq₂, hrec₀, hrec₁, hrec₂, hrec₃⟩
  have hlapAffine (f f' : GaussianInt → Int)
      (x t : GaussianInt) (A B C : Int)
      (h0 : f x = f' (x - t) + A * x.re + B * x.im + C)
      (hm : f (x - 1) = f' ((x - t) - 1) +
        A * (x - 1).re + B * (x - 1).im + C)
      (hp : f (x + 1) = f' ((x - t) + 1) +
        A * (x + 1).re + B * (x + 1).im + C)
      (hmi : f (x - ⟨0, 1⟩) = f' ((x - t) - ⟨0, 1⟩) +
        A * (x - ⟨0, 1⟩).re + B * (x - ⟨0, 1⟩).im + C)
      (hpi : f (x + ⟨0, 1⟩) = f' ((x - t) + ⟨0, 1⟩) +
        A * (x + ⟨0, 1⟩).re + B * (x + ⟨0, 1⟩).im + C) :
      FourNeighborLaplacian f x = FourNeighborLaplacian f' (x - t) :=
          ParentalRestrictionProof.hlapAffine f f' x t A B C h0 hm hp hmi hpi
  have hrec0Member (z : GaussianInt)
      (hzr : 0 ≤ z.re) (hzr' : z.re ≤ (P.q₁ : Int))
      (hzi : 0 ≤ z.im) (hzi' : z.im ≤ (P.q₁ : Int)) :
      z ∈ FordRecursiveVertexDomains P 0 := by
    change 0 ≤ z.re ∧ z.re ≤ (P.q₁ : Int) ∧
      0 ≤ z.im ∧ z.im ≤ (P.q₁ : Int)
    exact ⟨hzr, hzr', hzi, hzi'⟩
  have hchild0Lap (x : GaussianInt)
      (hxr : 1 ≤ x.re) (hxr' : x.re ≤ (P.q₁ : Int) - 1)
      (hxi : 1 ≤ x.im) (hxi' : x.im ≤ (P.q₁ : Int) - 1) :
      FourNeighborLaplacian (FordOdometer P) x =
        FourNeighborLaplacian (FordOdometer P₁) x := ParentalRestrictionProof.hchild0Lap P P₁ P₂
            hq₁ hrec₀ hrec0Member x hxr hxr' hxi hxi'
  have hrec1Member (z : GaussianInt)
      (hzr : (P.q₂ : Int) ≤ z.re) (hzr' : z.re ≤ (P.q : Int))
      (hzi : (P.q₂ : Int) ≤ z.im) (hzi' : z.im ≤ (P.q : Int)) :
      z ∈ FordRecursiveVertexDomains P 1 := by
    change (P.q₂ : Int) ≤ z.re ∧ z.re ≤ (P.q : Int) ∧
      (P.q₂ : Int) ≤ z.im ∧ z.im ≤ (P.q : Int)
    exact ⟨hzr, hzr', hzi, hzi'⟩
  have hchild1Lap (x : GaussianInt)
      (hxr : (P.q₂ : Int) + 1 ≤ x.re)
      (hxr' : x.re ≤ (P.q : Int) - 1)
      (hxi : (P.q₂ : Int) + 1 ≤ x.im)
      (hxi' : x.im ≤ (P.q : Int) - 1) :
      FourNeighborLaplacian (FordOdometer P) x =
        FourNeighborLaplacian (FordOdometer P₁)
          (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) := ParentalRestrictionProof.hchild1Lap P hsum P₁ P₂
              hq₁ hq₂ hrec₁ hlapAffine hrec1Member x hxr hxr' hxi hxi'
  have hrec2Member (z : GaussianInt)
      (hzr : (P.q₁ : Int) ≤ z.re) (hzr' : z.re ≤ (P.q : Int))
      (hzi : 0 ≤ z.im) (hzi' : z.im ≤ (P.q₂ : Int)) :
      z ∈ FordRecursiveVertexDomains P 2 := by
    change (P.q₁ : Int) ≤ z.re ∧ z.re ≤ (P.q : Int) ∧
      0 ≤ z.im ∧ z.im ≤ (P.q₂ : Int)
    exact ⟨hzr, hzr', hzi, hzi'⟩
  have hchild2Lap (x : GaussianInt)
      (hxr : (P.q₁ : Int) + 1 ≤ x.re)
      (hxr' : x.re ≤ (P.q : Int) - 1)
      (hxi : 1 ≤ x.im)
      (hxi' : x.im ≤ (P.q₂ : Int) - 1) :
      FourNeighborLaplacian (FordOdometer P) x =
        FourNeighborLaplacian (FordOdometer P₂)
          (x - ⟨(P.q₁ : Int), 0⟩) := ParentalRestrictionProof.hchild2Lap P hsum P₁ P₂ hq₁ hq₂
              hrec₂ hlapAffine hrec2Member x hxr hxr' hxi hxi'
  have hrec3Member (z : GaussianInt)
      (hzr : 0 ≤ z.re) (hzr' : z.re ≤ (P.q₂ : Int))
      (hzi : (P.q₁ : Int) ≤ z.im) (hzi' : z.im ≤ (P.q : Int)) :
      z ∈ FordRecursiveVertexDomains P 3 := by
    change 0 ≤ z.re ∧ z.re ≤ (P.q₂ : Int) ∧
      (P.q₁ : Int) ≤ z.im ∧ z.im ≤ (P.q : Int)
    exact ⟨hzr, hzr', hzi, hzi'⟩
  have hchild3Lap (x : GaussianInt)
      (hxr : 1 ≤ x.re) (hxr' : x.re ≤ (P.q₂ : Int) - 1)
      (hxi : (P.q₁ : Int) + 1 ≤ x.im)
      (hxi' : x.im ≤ (P.q : Int) - 1) :
      FourNeighborLaplacian (FordOdometer P) x =
        FourNeighborLaplacian (FordOdometer P₂)
          (x - ⟨0, (P.q₁ : Int)⟩) := ParentalRestrictionProof.hchild3Lap P hsum P₁ P₂ hq₁ hq₂
              hrec₃ hlapAffine hrec3Member x hxr hxr' hxi hxi'
  have hne : P.q₁ ≠ P.q₂ := by
    intro he
    have hd : (P.q₁ : Int) ∣ (1 : Int) := by
      refine ⟨P.p₁-P.p₂, ?_⟩
      rw [← he] at hcrossdet
      nlinarith only [hcrossdet]
    have hb := Int.le_of_dvd (by norm_num : (0 : Int) < 1) hd
    have hp := P.q₂_pos
    omega
  refine ⟨P₁, P₂, hp₁, hq₁, hp₂, hq₂, ?_, ?_, hne, ?_⟩
  · rw [hq₁]
    exact P.q₁_lt
  · rw [hq₂]
    exact hparent₂lt hbig
  · intro i
    fin_cases i
    · change P4062T1InteriorSquare P.q₁ =
          (P4062T1InteriorSquare P₁.q).image (fun x => x+0) ∧
        ∀ x ∈ P4062T1InteriorSquare P.q₁,
          FourNeighborLaplacian (FordOdometer P) x =
            FourNeighborLaplacian (FordOdometer P₁) (x-0)
      constructor
      · simp [hq₁]
      · intro x hx
        have hb := (squareCoordinates P.q₁ x).mp hx
        simpa using hchild0Lap x hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    · change (P4062T1InteriorSquare P.q₁).image
          (fun x => x+⟨(P.q₂ : Int), (P.q₂ : Int)⟩) =
          (P4062T1InteriorSquare P₁.q).image
            (fun x => x+⟨(P.q₂ : Int), (P.q₂ : Int)⟩) ∧ _
      constructor
      · rw [hq₁]
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        have hb := (squareCoordinates P.q₁ y).mp hy
        apply hchild1Lap
        all_goals simp only [Zsqrtd.re_add, Zsqrtd.im_add]
        all_goals omega
    · change (P4062T1InteriorSquare P.q₂).image
          (fun x => x+⟨(P.q₁ : Int), 0⟩) =
          (P4062T1InteriorSquare P₂.q).image
            (fun x => x+⟨(P.q₁ : Int), 0⟩) ∧ _
      constructor
      · rw [hq₂]
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        have hb := (squareCoordinates P.q₂ y).mp hy
        apply hchild2Lap
        all_goals simp only [Zsqrtd.re_add, Zsqrtd.im_add, add_zero]
        all_goals omega
    · change (P4062T1InteriorSquare P.q₂).image
          (fun x => x+⟨0, (P.q₁ : Int)⟩) =
          (P4062T1InteriorSquare P₂.q).image
            (fun x => x+⟨0, (P.q₁ : Int)⟩) ∧ _
      constructor
      · rw [hq₂]
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        have hb := (squareCoordinates P.q₂ y).mp hy
        apply hchild3Lap
        all_goals simp only [Zsqrtd.re_add, Zsqrtd.im_add, add_zero]
        all_goals omega

end ApollonianSuperharmonic

end
