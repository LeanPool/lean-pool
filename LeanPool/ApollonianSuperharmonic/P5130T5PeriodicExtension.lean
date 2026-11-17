/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.P4818T1AffineTransversalExtension

-- [TABLET NODE: P5130T5PeriodicExtension]

/-!
# P5130T5PeriodicExtension

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PeriodicExtensionConstruction

private noncomputable abbrev q (P : FordFareyParameter) : Int := by
  classical
  let q : Int := P.q
  exact q

private theorem hq (P : FordFareyParameter) : 0 < (q P) := by
  classical
  let q : Int := P.q
  change (0 < q)
  dsimp [q]; exact_mod_cast P.q_pos

private theorem hq₁lt (P : FordFareyParameter) : (P.q₁ : Int) < (q P) := by
  classical
  let q : Int := P.q
  change ((P.q₁ : Int) < q)
  change (P.q₁ : Int) < (P.q : Int)
  exact_mod_cast P.q₁_lt

private noncomputable abbrev H (P : FordFareyParameter) : Set GaussianInt := by
  classical
  let q : Int := P.q
  let H : Set GaussianInt := {z | 0 ≤ z.re ∧ z.re < q ∧ 0 ≤ z.im ∧ z.im < q}
  exact H

private noncomputable abbrev a (P : FordFareyParameter) : GaussianInt := by
  classical
  let q : Int := P.q
  let a : GaussianInt := ⟨0, -q⟩
  exact a

private noncomputable abbrev b (P : FordFareyParameter) : GaussianInt := by
  classical
  let q : Int := P.q
  let b : GaussianInt := ⟨q, P.q₁⟩
  exact b

private noncomputable abbrev α (P : FordFareyParameter) : GaussianInt →+ Int := by
  classical
  let α : GaussianInt →+ Int :=
    { toFun := fun x => -P.p * x.re
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  exact α

private noncomputable abbrev β (P : FordFareyParameter) : GaussianInt →+ Int := by
  classical
  let β : GaussianInt →+ Int :=
    { toFun := fun x => P.p₁ * x.re + P.p * x.im
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add]; ring }
  exact β

private theorem hcomm (P : FordFareyParameter) : (α P) (b P) = (β P) (a P) := by
  classical
  let q : Int := P.q
  let a : GaussianInt := ⟨0, -q⟩
  let b : GaussianInt := ⟨q, P.q₁⟩
  let α : GaussianInt →+ Int :=
    { toFun := fun x => -P.p * x.re
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  let β : GaussianInt →+ Int :=
    { toFun := fun x => P.p₁ * x.re + P.p * x.im
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add]; ring }
  change (α b = β a)
  simp [α, β, a, b]

private theorem hrep (P : FordFareyParameter) (hq : 0 < (q P)) (x : GaussianInt) : ∃! t :
    GaussianInt × (Int × Int),
      t.1 ∈ (H P) ∧ x = t.1 + t.2.1 • (a P) + t.2.2 • (b P) := by
  classical
  let q : Int := P.q
  let H : Set GaussianInt := {z | 0 ≤ z.re ∧ z.re < q ∧ 0 ≤ z.im ∧ z.im < q}
  let a : GaussianInt := ⟨0, -q⟩
  let b : GaussianInt := ⟨q, P.q₁⟩
  change (0 < q) at hq
  change (∃! t : GaussianInt × (Int × Int),
      t.1 ∈ H ∧ x = t.1 + t.2.1 • a + t.2.2 • b)
  let n : Int := x.re / q
  let u : Int := x.re % q
  let k : Int := (x.im - n * P.q₁) / q
  let v : Int := (x.im - n * P.q₁) % q
  let z : GaussianInt := ⟨u, v⟩
  have hu0 : 0 ≤ u := by dsimp [u]; exact Int.emod_nonneg _ (by omega)
  have hult : u < q := by dsimp [u]; exact Int.emod_lt_of_pos _ hq
  have hv0 : 0 ≤ v := by dsimp [v]; exact Int.emod_nonneg _ (by omega)
  have hvlt : v < q := by dsimp [v]; exact Int.emod_lt_of_pos _ hq
  have hre : x.re = u + n * q := by
    have hh := (Int.emod_add_mul_ediv x.re q).symm
    calc
      x.re = x.re % q + q * (x.re / q) := hh
      _ = u + n * q := by dsimp [u, n]; ring
  have him : x.im = v + k * q + n * P.q₁ := by
    have hh := Int.emod_add_mul_ediv (x.im - n * P.q₁) q
    change v + q * k = x.im - n * P.q₁ at hh
    nlinarith
  have hz : z ∈ H := by simp [H, z, hu0, hult, hv0, hvlt]
  have hx : x = z + (-k) • a + n • b := by
    apply Zsqrtd.ext <;> simp [z, a, b, zsmul_eq_mul, hre, him]
  refine ⟨(z, (-k, n)), ⟨hz, hx⟩, ?_⟩
  intro t ht
  rcases t with ⟨w, m, l⟩
  rcases ht with ⟨hw, hwt⟩
  change 0 ≤ w.re ∧ w.re < q ∧ 0 ≤ w.im ∧ w.im < q at hw
  rcases hw with ⟨hwr0, hwr1, hwi0, hwi1⟩
  have hwr : 0 ≤ w.re ∧ w.re < q := ⟨hwr0, hwr1⟩
  have hwi : 0 ≤ w.im ∧ w.im < q := ⟨hwi0, hwi1⟩
  have hwrep := congr_arg Zsqrtd.re hwt
  have himrep := congr_arg Zsqrtd.im hwt
  simp only [Int.reduceNeg, zsmul_eq_mul, Zsqrtd.smul_val, mul_zero, mul_neg, Zsqrtd.re_add,
      add_zero, Zsqrtd.im_add, a, b] at hwrep himrep
  have hdivr : x.re / q = l := by
    apply (Int.ediv_eq_iff_of_pos hq).2
    constructor <;> rw [hwrep] <;> nlinarith [hwr.1, hwr.2]
  have hmodr : x.re % q = w.re := by
    rw [hwrep, show w.re + l * q = w.re + q * l by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt hwr.1 hwr.2]
  have hn_eq : l = n := by
    dsimp [n]
    exact hdivr.symm
  subst l
  have hu_eq : w.re = u := by
    dsimp [u]
    exact hmodr.symm
  have hm_eq : m = -k := by
    have heq : x.im - n * P.q₁ = w.im + q * (-m) := by
      rw [himrep]
      ring
    have hd : (x.im - n * P.q₁) / q = -m := by
      apply (Int.ediv_eq_iff_of_pos hq).2
      constructor <;> rw [heq] <;> nlinarith [hwi.1, hwi.2]
    dsimp [k]
    linarith
  have hv_eq : w.im = v := by
    have heq : x.im - n * P.q₁ = w.im + q * (-m) := by
      rw [himrep]
      ring
    have hd : (x.im - n * P.q₁) % q = w.im := by
      rw [heq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hwi.1 hwi.2]
    dsimp [v]
    exact hd.symm
  subst m
  apply Prod.ext
  · apply Zsqrtd.ext <;> simp [z, hu_eq, hv_eq]
  · apply Prod.ext <;> simp [hn_eq]

private theorem ext (P : FordFareyParameter) (f : IntegerLatticeFunction) (hcomm : ((α P) :
    GaussianInt → ℤ) (b P) = ((β P) : GaussianInt → ℤ) (a P)) (hrep : ∀ (x : GaussianInt), ∃! t :
    GaussianInt × ℤ × ℤ, t.1 ∈ (H P) ∧ x = t.1 + t.2.1 • (a P) + t.2.2 • (b P)) : ∃ (g :
    IntegerLatticeFunction), (∀ h ∈ (H P), g h = f h) ∧ (∀ (x : GaussianInt), g (x + (a P)) = g x
    + ((α P) : GaussianInt → ℤ) x + 0) ∧ (∀ (x : GaussianInt), g (x + (b P)) = g x + ((β P) :
    GaussianInt → ℤ) x + (↑P.q₁ : ℤ) * P.p) ∧ (∀ h ∈ (H P), ∀ (m n : ℤ), g (h + m • (a P) + n •
    (b P)) = f h + m * (((α P) : GaussianInt → ℤ) h + 0) + m * (m - 1) / 2 * ((α P) : GaussianInt
    → ℤ) (a P) + n * (((β P) : GaussianInt → ℤ) h + (↑P.q₁ : ℤ) * P.p) + n * (n - 1) / 2 * ((β P)
    : GaussianInt → ℤ) (b P) + m * n * ((β P) : GaussianInt → ℤ) (a P)) ∧ ∀ (g' :
    IntegerLatticeFunction), (∀ (x : GaussianInt), g' (x + (a P)) = g' x + ((α P) : GaussianInt →
    ℤ) x + 0) → (∀ (x : GaussianInt), g' (x + (b P)) = g' x + ((β P) : GaussianInt → ℤ) x +
    (↑P.q₁ : ℤ) * P.p) → (∀ h ∈ (H P), g' h = f h) → g' = g := by
  classical
  let q : Int := P.q
  let H : Set GaussianInt := {z | 0 ≤ z.re ∧ z.re < q ∧ 0 ≤ z.im ∧ z.im < q}
  let a : GaussianInt := ⟨0, -q⟩
  let b : GaussianInt := ⟨q, P.q₁⟩
  let α : GaussianInt →+ Int :=
    { toFun := fun x => -P.p * x.re
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  let β : GaussianInt →+ Int :=
    { toFun := fun x => P.p₁ * x.re + P.p * x.im
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add]; ring }
  change ((α : GaussianInt → ℤ) b = (β : GaussianInt → ℤ) a) at hcomm
  change (∀ (x : GaussianInt), ∃! t : GaussianInt × ℤ × ℤ, t.1 ∈ H ∧ x = t.1 + t.2.1 • a + t.2.2
      • b) at hrep
  change (∃ (g : IntegerLatticeFunction), (∀ h ∈ H, g h = f h) ∧ (∀ (x : GaussianInt), g (x + a)
      = g x + (α : GaussianInt → ℤ) x + 0) ∧ (∀ (x : GaussianInt), g (x + b) = g x + (β :
      GaussianInt → ℤ) x + (↑P.q₁ : ℤ) * P.p) ∧ (∀ h ∈ H, ∀ (m n : ℤ), g (h + m • a + n • b) = f
      h + m * ((α : GaussianInt → ℤ) h + 0) + m * (m - 1) / 2 * (α : GaussianInt → ℤ) a + n * ((β
      : GaussianInt → ℤ) h + (↑P.q₁ : ℤ) * P.p) + n * (n - 1) / 2 * (β : GaussianInt → ℤ) b + m *
      n * (β : GaussianInt → ℤ) a) ∧ ∀ (g' : IntegerLatticeFunction), (∀ (x : GaussianInt), g' (x
      + a) = g' x + (α : GaussianInt → ℤ) x + 0) → (∀ (x : GaussianInt), g' (x + b) = g' x + (β :
      GaussianInt → ℤ) x + (↑P.q₁ : ℤ) * P.p) → (∀ h ∈ H, g' h = f h) → g' = g)
  exact P4818T1AffineTransversalExtension H a b α β 0 (P.q₁ * P.p) f hrep hcomm

private theorem fEdges (P : FordFareyParameter) (f : IntegerLatticeFunction) (hB : ∀ x ∈
    FordDoubledBoundary P.q, f x = IntegerCeilDiv (P.p * x.re * x.im) (↑P.q : ℤ) (by
        exact_mod_cast P.q_pos.ne')) (hq : 0 < (q
    P)) (r : Int) (hr0 : 0 ≤ r) (hrq : r ≤ (q P)) :
      f ⟨r, 0⟩ = 0 ∧ f ⟨0, r⟩ = 0 ∧
      f ⟨r, (q P)⟩ = P.p * r ∧ f ⟨(q P), r⟩ = P.p * r := by
  classical
  let q : Int := P.q
  change (0 < q) at hq
  change r ≤ q at hrq
  change (f ⟨r, 0⟩ = 0 ∧ f ⟨0, r⟩ = 0 ∧
      f ⟨r, q⟩ = P.p * r ∧ f ⟨q, r⟩ = P.p * r)
  have mbot : (⟨r, 0⟩ : GaussianInt) ∈ FordDoubledBoundary P.q := by
    change (0 ≤ r ∧ r ≤ q ∧ 0 ≤ (0:Int) ∧ (0:Int) ≤ q) ∧
      ¬(2 ≤ r ∧ r ≤ q - 2 ∧ 2 ≤ (0:Int) ∧ (0:Int) ≤ q - 2)
    constructor <;> omega
  have mleft : (⟨0, r⟩ : GaussianInt) ∈ FordDoubledBoundary P.q := by
    change (0 ≤ (0:Int) ∧ (0:Int) ≤ q ∧ 0 ≤ r ∧ r ≤ q) ∧
      ¬(2 ≤ (0:Int) ∧ (0:Int) ≤ q - 2 ∧ 2 ≤ r ∧ r ≤ q - 2)
    constructor <;> omega
  have mtop : (⟨r, q⟩ : GaussianInt) ∈ FordDoubledBoundary P.q := by
    change (0 ≤ r ∧ r ≤ q ∧ 0 ≤ q ∧ q ≤ q) ∧
      ¬(2 ≤ r ∧ r ≤ q - 2 ∧ 2 ≤ q ∧ q ≤ q - 2)
    constructor <;> omega
  have mright : (⟨q, r⟩ : GaussianInt) ∈ FordDoubledBoundary P.q := by
    change (0 ≤ q ∧ q ≤ q ∧ 0 ≤ r ∧ r ≤ q) ∧
      ¬(2 ≤ q ∧ q ≤ q - 2 ∧ 2 ≤ r ∧ r ≤ q - 2)
    constructor <;> omega
  have hcTop : IntegerCeilDiv (P.p * r * q) q (ne_of_gt hq) = P.p * r := by
    unfold IntegerCeilDiv
    have he : -(P.p * r * q) = q * (-(P.p * r)) := by ring
    rw [he, Int.mul_ediv_cancel_left _ (ne_of_gt hq)]
    simp
  have hcRight : IntegerCeilDiv (P.p * q * r) q (ne_of_gt hq) = P.p * r := by
    have hh : P.p * q * r = P.p * r * q := by ring
    rw [hh]
    exact hcTop
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [IntegerCeilDiv] using hB ⟨r, 0⟩ mbot
  · simpa [IntegerCeilDiv] using hB ⟨0, r⟩ mleft
  · exact (hB ⟨r, q⟩ mtop).trans hcTop
  · exact (hB ⟨q, r⟩ mright).trans hcRight

end PeriodicExtensionConstruction

theorem P5130T5PeriodicExtension (P : FordFareyParameter)
    (f : IntegerLatticeFunction)
    (hB : ∀ x ∈ FordDoubledBoundary P.q,
      f x = IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne')) :
    ∃! g : IntegerLatticeFunction,
      (∀ x ∈ FordVertexDomain P.q, g x = f x) ∧
      (∀ x, g (x + ⟨0, -(P.q : Int)⟩) = g x - P.p * x.re) ∧
      (∀ x, g (x + ⟨(P.q : Int), (P.q₁ : Int)⟩) =
        g x + P.p₁ * x.re + P.p * x.im + (P.q₁ : Int) * P.p) ∧
      (∀ x, g (x + ⟨-(P.q : Int), (P.q₂ : Int)⟩) =
        g x + P.p₂ * x.re - P.p * x.im - (P.q : Int) * P.p₂) := by
-- BODY
  classical
  let q : Int := P.q
  have hq : 0 < q := PeriodicExtensionConstruction.hq P
  have hq₁lt : (P.q₁ : Int) < q := PeriodicExtensionConstruction.hq₁lt P
  let H : Set GaussianInt := {z | 0 ≤ z.re ∧ z.re < q ∧ 0 ≤ z.im ∧ z.im < q}
  let a : GaussianInt := ⟨0, -q⟩
  let b : GaussianInt := ⟨q, P.q₁⟩
  let α : GaussianInt →+ Int :=
    { toFun := fun x => -P.p * x.re
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  let β : GaussianInt →+ Int :=
    { toFun := fun x => P.p₁ * x.re + P.p * x.im
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add]; ring }
  have hcomm : α b = β a := PeriodicExtensionConstruction.hcomm P
  have hrep (x : GaussianInt) : ∃! t : GaussianInt × (Int × Int),
      t.1 ∈ H ∧ x = t.1 + t.2.1 • a + t.2.2 • b := PeriodicExtensionConstruction.hrep P hq x
  have ext := PeriodicExtensionConstruction.ext P f hcomm hrep
  rcases ext with ⟨g, hH, ha, hb, _, huniq⟩
  have fEdges (r : Int) (hr0 : 0 ≤ r) (hrq : r ≤ q) :
      f ⟨r, 0⟩ = 0 ∧ f ⟨0, r⟩ = 0 ∧
      f ⟨r, q⟩ = P.p * r ∧ f ⟨q, r⟩ = P.p * r := PeriodicExtensionConstruction.fEdges P f hB hq r
          hr0 hrq
  refine ⟨g, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    change 0 ≤ x.re ∧ x.re ≤ q ∧ 0 ≤ x.im ∧ x.im ≤ q at hx
    rcases hx with ⟨hr0, hrq, hi0, hiq⟩
    by_cases hr : x.re = q
    · have hx : x = ⟨q, x.im⟩ := by apply Zsqrtd.ext <;> simp [hr]
      rw [hx]
      have hright := fEdges x.im hi0 hiq
      have gzero : g ⟨0, x.im - P.q₁⟩ = 0 := by
        by_cases hlow : 0 ≤ x.im - P.q₁
        · by_cases hhigh : x.im - P.q₁ < q
          · have hmem : (⟨0, x.im - P.q₁⟩ : GaussianInt) ∈ H := by
              simp [H]; omega
            rw [hH _ hmem]
            have hv := fEdges (x.im - P.q₁) hlow (by omega)
            exact hv.2.1
          · have heq : x.im - P.q₁ = q := by omega
            have hdown := ha ⟨0, q⟩
            have hzero : g ⟨0, 0⟩ = 0 := by
              rw [hH _ (by simp []; omega)]
              exact (fEdges 0 (by omega) (by omega)).2.1
            have hdown' : g ⟨0, 0⟩ = g ⟨0, q⟩ := by
              simpa [a, α, q] using hdown
            simpa [heq] using hdown'.symm.trans hzero
        · have hlow' : 0 ≤ x.im - P.q₁ + q ∧ x.im - P.q₁ + q < q := by omega
          have hmem : (⟨0, x.im - P.q₁ + q⟩ : GaussianInt) ∈ H := by
            simp [H]; omega
          have hadd := ha ⟨0, x.im - P.q₁ + q⟩
          have hshift : (⟨0, x.im - P.q₁ + q⟩ : GaussianInt) + a = ⟨0, x.im - P.q₁⟩ := by
            apply Zsqrtd.ext <;> simp [a, q]
          rw [hshift] at hadd
          have hbase : g ⟨0, x.im - P.q₁ + q⟩ = 0 := by
            rw [hH _ hmem]
            exact (fEdges (x.im - P.q₁ + q) hlow'.1 (le_of_lt hlow'.2)).2.1
          have ha0 : α ⟨0, x.im - P.q₁ + q⟩ = 0 := by simp [α]
          rw [ha0, hbase] at hadd
          exact hadd
      have hstep := hb ⟨0, x.im - P.q₁⟩
      have hcoords : (⟨0, x.im - P.q₁⟩ : GaussianInt) + b = ⟨q, x.im⟩ := by
        apply Zsqrtd.ext <;> simp [b, q]
      rw [hcoords] at hstep
      rw [hright.2.2.2]
      rw [hstep, gzero]
      simp []
      nlinarith
    · by_cases hi : x.im = q
      · have hx : x = ⟨x.re, q⟩ := by apply Zsqrtd.ext <;> simp [hi]
        rw [hx]
        have htop := fEdges x.re hr0 hrq
        have hbase : (⟨x.re, 0⟩ : GaussianInt) ∈ H := by simp [H]; omega
        have hdown := ha ⟨x.re, q⟩
        have hshift : (⟨x.re, q⟩ : GaussianInt) + a = ⟨x.re, 0⟩ := by
          apply Zsqrtd.ext <;> simp [a, q]
        rw [hshift] at hdown
        have haTop : α ⟨x.re, q⟩ = -P.p * x.re := by simp [α]
        rw [haTop, hH _ hbase, htop.1] at hdown
        rw [htop.2.2.1]
        linarith
      · have hmem : x ∈ H := by simp [H]; omega
        exact hH x hmem
  · intro x
    change g (x + a) = g x - P.p * x.re
    rw [ha x]
    simp []
    ring
  · intro x
    change g (x + b) = g x + P.p₁ * x.re + P.p * x.im + (P.q₁ : Int) * P.p
    rw [hb x]
    simp []
    ring
  · intro x
    let y : GaussianInt := x + ⟨-(P.q : Int), (P.q₂ : Int)⟩
    have hqs : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by exact_mod_cast P.sum_q
    have hrel : y + a + b = x := by
      apply Zsqrtd.ext
      · simp [y, a, b, q]
      · simp only [Int.reduceNeg, Zsqrtd.im_add, y, a, q, b]
        rw [hqs]
        ring
    have hstep : g x = g y + α y + β (y + a) + (P.q₁ : Int) * P.p := by
      calc
        g x = g (y + a + b) := by rw [hrel]
        _ = g (y + a) + β (y + a) + (P.q₁ : Int) * P.p := hb (y + a)
        _ = g y + α y + β (y + a) + (P.q₁ : Int) * P.p := by rw [ha y]; ring
    rw [hstep]
    simp only [Int.reduceNeg, neg_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Zsqrtd.re_add,
        add_zero, Zsqrtd.im_add, y, α, β, a, q]
    have hps : P.p = P.p₁ + P.p₂ := P.sum_p
    rw [hqs, hps]
    ring
  · intro g' hg'
    rcases hg' with ⟨hagree, ha', hb', _⟩
    have hga : ∀ x, g' (x + a) = g' x + α x + 0 := by
      intro x
      rw [ha' x]
      simp [α]
      ring
    have hgb : ∀ x, g' (x + b) = g' x + β x + P.q₁ * P.p := by
      intro x
      rw [hb' x]
      simp [β]
      ring
    apply huniq g' hga hgb
    intro h hh
    have hdom : h ∈ FordVertexDomain P.q := by
      change 0 ≤ h.re ∧ h.re ≤ (P.q : Int) ∧ 0 ≤ h.im ∧ h.im ≤ (P.q : Int)
      rcases hh with ⟨hr0, hr1, hi0, hi1⟩
      constructor <;> omega
    exact hagree h hdom

end ApollonianSuperharmonic

end
