/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4818T1HalfOpen
public import LeanPool.ApollonianSuperharmonic.P4818T1ClosedOverlaps
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

-- [TABLET NODE: P4818T1Representatives]

/-!
# P4818T1Representatives

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RepresentativesProof

private theorem hk :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    0 < k := by
  classical
  intro K k
  dsimp [k]; exact_mod_cast K.2

private theorem hmem :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (z : GaussianInt), z ∈ DiamondVertexDomains K false ↔
      -k ≤ z.re ∧ z.re ≤ k ∧ 0 ≤ z.im ∧ z.im ≤ 2 * k ∧
      z.re + z.im ≤ 2 * k + 1 ∧ -z.re + z.im ≤ 2 * k + 1 ∧
      z.re - z.im ≤ 1 ∧ -z.re - z.im ≤ 1 := by
  classical
  intro K k z
  have raw : z ∈ DiamondVertexDomains K false ↔
      z.re.natAbs ≤ K.1 ∧ (z.im - k).natAbs ≤ K.1 ∧
      z.re.natAbs + (z.im - k).natAbs ≤ K.1 + 1 := by
    change max z.re.natAbs (max (z.im - k).natAbs
      (z.re.natAbs + (z.im - k).natAbs - 1)) ≤ K.1 ↔ _
    simp only [max_le_iff, Nat.sub_le_iff_le_add]
  rw [raw]
  have h1 := Int.natCast_natAbs z.re
  have h2 := Int.natCast_natAbs (z.im - k)
  by_cases hr : 0 ≤ z.re <;> by_cases hi : 0 ≤ z.im - k
  · rw [abs_of_nonneg hr] at h1
    rw [abs_of_nonneg hi] at h2
    omega
  · rw [abs_of_nonneg hr] at h1
    rw [abs_of_neg (by omega : z.im - k < 0)] at h2
    omega
  · rw [abs_of_neg (by omega : z.re < 0)] at h1
    rw [abs_of_nonneg hi] at h2
    omega
  · rw [abs_of_neg (by omega : z.re < 0)] at h1
    rw [abs_of_neg (by omega : z.im - k < 0)] at h2
    omega

private theorem hHmem :
    ∀ (K : DiamondParameter), ∀ (z : GaussianInt), (z ∈ P4818T1HalfOpen K) → (z ∈
        DiamondVertexDomains K false) := by
  classical
  intro K z hz
  simpa [P4818T1HalfOpen] using hz.1

private theorem noA :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    (∀ (x : GaussianInt), x ∈ DiamondVertexDomains K false ∧ x + ⟨(0 : ℤ), (-2 : ℤ)
        * (↑(K.1 : ℕ) : ℤ)⟩ ∈ DiamondVertexDomains K false ↔ ∃ (r : ℤ), (-1 : ℤ) ≤ r ∧ r ≤ (1 :
        ℤ) ∧ x = ⟨r, (2 : ℤ) * (↑(K.1 : ℕ) : ℤ)⟩) → ((∀ (z : GaussianInt), (z ∈
        P4818T1HalfOpen K) → (z ∈ DiamondVertexDomains K false)) → (∀ (u : GaussianInt), ∀ (v :
        GaussianInt), (u ∈ P4818T1HalfOpen K) → ((v ∈ P4818T1HalfOpen K) → ((v = u + a) →
        (False))))) := by
  classical
  intro K k a hA hHmem u v hu hv hadd
  have hu' : u + a ∈ DiamondVertexDomains K false := by
    rw [← hadd]
    exact hHmem v hv
  have hov := (hA u).mp ⟨hHmem u hu, by simpa [a, k] using hu'⟩
  rcases hov with ⟨r, hr, hr', hru⟩
  have hbad := hu
  simp only [P4818T1HalfOpen] at hbad
  exact hbad.2.1 ⟨by simp [hru], by simpa [hru, k] using hr,
    by simpa [hru, k] using hr'⟩

private theorem noB :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let b : GaussianInt := ⟨k + 1, k⟩
    (∀ (x : GaussianInt), x ∈ DiamondVertexDomains K false ∧ x + ⟨(↑(K.1 : ℕ) : ℤ) + (1 :
        ℤ), (↑(K.1 : ℕ) : ℤ)⟩ ∈ DiamondVertexDomains K false ↔ (∃ (j : ℤ), (1 : ℤ) ≤ j ∧ j
        ≤ (↑(K.1 : ℕ) : ℤ) ∧ x = ⟨-j, j⟩) ∨ ∃ (j : ℤ), (0 : ℤ) ≤ j ∧ j < (↑(K.1 : ℕ)
        : ℤ) ∧ x = ⟨(-1 : ℤ) - j, j⟩) → ((∀ (z : GaussianInt), (z ∈
        P4818T1HalfOpen K) → (z ∈ DiamondVertexDomains K false)) → (∀ (u : GaussianInt), ∀ (v :
        GaussianInt), (u ∈ P4818T1HalfOpen K) → ((v ∈ P4818T1HalfOpen K) → ((v = u + b) →
        (False))))) := by
  classical
  intro K k b hB hHmem u v hu hv hadd
  have hu' : u + b ∈ DiamondVertexDomains K false := by
    rw [← hadd]
    exact hHmem v hv
  have hov := (hB u).mp ⟨hHmem u hu, by simpa [b, k] using hu'⟩
  rcases hov with (⟨j, hj, hjk, hsrc⟩ | ⟨j, hj, hjk, hsrc⟩)
  · have hdst : v = ⟨k + 1 - j, k + j⟩ := by
      rw [hadd, hsrc]; ext <;> simp [b, k] <;> ring
    have hbad := hv
    simp only [P4818T1HalfOpen] at hbad
    exact hbad.2.2.1 (Or.inl ⟨j, hj, hjk, by simpa [k] using hdst⟩)
  · have hdst : v = ⟨k - j, k + j⟩ := by
      rw [hadd, hsrc]; ext <;> simp [b, k] <;> ring
    have hbad := hv
    simp only [P4818T1HalfOpen] at hbad
    exact hbad.2.2.1 (Or.inr ⟨j, hj, hjk, by simpa [k] using hdst⟩)

private theorem noC :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let c : GaussianInt := ⟨-k - 1, k⟩
    (∀ (x : GaussianInt), x ∈ DiamondVertexDomains K false ∧ x + ⟨-(↑(K.1 : ℕ) : ℤ) - (1 :
        ℤ), (↑(K.1 : ℕ) : ℤ)⟩ ∈ DiamondVertexDomains K false ↔ ∃ (j : ℤ), (1 : ℤ) ≤ j ∧ j ≤
        (↑(K.1 : ℕ) : ℤ) ∧ (x = ⟨j, j - (1 : ℤ)⟩ ∨ x = ⟨j, j⟩)) → ((∀
        (z : GaussianInt), (z ∈ P4818T1HalfOpen K) → (z ∈ DiamondVertexDomains K false)) → (∀
        (u : GaussianInt), ∀ (v : GaussianInt), (u ∈ P4818T1HalfOpen K) → ((v ∈
        P4818T1HalfOpen K) → ((v = u + c) → (False))))) := by
  classical
  intro K k c hC hHmem u v hu hv hadd
  have hu' : u + c ∈ DiamondVertexDomains K false := by
    rw [← hadd]
    exact hHmem v hv
  have hov := (hC u).mp ⟨hHmem u hu, by simpa [c, k] using hu'⟩
  rcases hov with ⟨j, hj, hjk, (hsrc | hsrc)⟩
  · have hdst : v = ⟨j - k - 1, k + j - 1⟩ := by
      rw [hadd, hsrc]; ext <;> simp [c, k] <;> ring
    have hbad := hv
    simp only [P4818T1HalfOpen] at hbad
    exact hbad.2.2.2 (Or.inl ⟨j, hj, hjk, by simpa [k] using hdst⟩)
  · have hdst : v = ⟨j - k - 1, k + j⟩ := by
      rw [hadd, hsrc]; ext <;> simp [c, k] <;> ring
    have hbad := hv
    simp only [P4818T1HalfOpen] at hbad
    exact hbad.2.2.2 (Or.inr ⟨j, hj, hjk, by simpa [k] using hdst⟩)

private theorem hinj :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    let c : GaussianInt := ⟨-k - 1, k⟩
    (∀ (x : GaussianInt), ∀ (m : ℤ), ∀ (n : ℤ), x ∈ DiamondVertexDomains K false → x + m • ⟨(0 :
        ℤ), (-2 : ℤ) * (↑(K.1 : ℕ) : ℤ)⟩ + n • ⟨(↑(K.1 : ℕ) : ℤ) + (1 : ℤ), (↑(K.1 : ℕ) : ℤ)⟩ ∈
        DiamondVertexDomains K false → m = (0 : ℤ) ∧ n = (0 : ℤ) ∨ m =
        (1 : ℤ) ∧ n = (0 : ℤ) ∨ m = (-1 : ℤ) ∧ n = (0 : ℤ) ∨ m = (0 : ℤ) ∧ n = (1 : ℤ) ∨ m = (0 :
        ℤ) ∧ n = (-1 : ℤ) ∨ m = (1 : ℤ) ∧ n = (1 : ℤ) ∨ m = (-1 : ℤ) ∧ n = (-1 : ℤ)) → ((∀ (z :
        GaussianInt), (z ∈ P4818T1HalfOpen K) → (z ∈ DiamondVertexDomains K false)) → ((∀ (u :
        GaussianInt), ∀ (v : GaussianInt), (u ∈ P4818T1HalfOpen K) → ((v ∈ P4818T1HalfOpen K)
        → ((v = u + a) → (False)))) → ((∀ (u : GaussianInt), ∀ (v : GaussianInt), (u ∈
        P4818T1HalfOpen K) → ((v ∈ P4818T1HalfOpen K) → ((v = u + b) → (False)))) → ((∀ (u :
        GaussianInt), ∀ (v : GaussianInt), (u ∈ P4818T1HalfOpen K) → ((v ∈ P4818T1HalfOpen K)
        → ((v = u + c) → (False)))) → (∀ (h₁ : GaussianInt), ∀ (h₂ : GaussianInt), ∀ (m : Int), ∀
        (n : Int), h₁ ∈ P4818T1HalfOpen K → h₂ ∈ P4818T1HalfOpen K →
      h₂ = h₁ + m • a + n • b → m = 0 ∧ n = 0))))) := by
  classical
  intro K k a b c hcoeff hHmem noA noB noC h₁ h₂ m n hh₁ hh₂ heq
  have hcfs := hcoeff h₁ m n (hHmem h₁ hh₁) (by rw [heq.symm]; exact hHmem h₂ hh₂)
  rcases hcfs with hz | hz | hz | hz | hz | hz | hz
  · exact hz
  · rcases hz with ⟨rfl, rfl⟩
    exfalso
    apply noA h₁ h₂ hh₁ hh₂
    simpa [a, b] using heq
  · rcases hz with ⟨hm, hn⟩
    subst m; subst n
    exfalso
    have hadd : h₁ = h₂ + a := by rw [heq]; simp [a, b]
    exact noA h₂ h₁ hh₂ hh₁ hadd
  · rcases hz with ⟨hm, hn⟩
    subst m; subst n
    exfalso
    have hadd : h₂ = h₁ + b := by simpa [a, b] using heq
    exact noB h₁ h₂ hh₁ hh₂ hadd
  · rcases hz with ⟨hm, hn⟩
    subst m; subst n
    exfalso
    have hadd : h₁ = h₂ + b := by rw [heq]; simp [a, b]
    exact noB h₂ h₁ hh₂ hh₁ hadd
  · rcases hz with ⟨hm, hn⟩
    subst m; subst n
    exfalso
    have habc : a + b = -c := by ext <;> simp [a, b, c] <;> ring
    have hsum : a + b + c = 0 := by rw [habc]; simp
    have hsum' : a + (b + c) = 0 := by simpa [add_assoc] using hsum
    have hadd : h₁ = h₂ + c := by
      calc
        h₁ = h₁ + (a + (b + c)) := by rw [hsum']; simp
        _ = h₂ + c := by
          rw [heq]
          simp only [one_zsmul]
          abel
    exact noC h₂ h₁ hh₂ hh₁ hadd
  · rcases hz with ⟨hm, hn⟩
    subst m; subst n
    exfalso
    have habc : a + b = -c := by ext <;> simp [a, b, c] <;> ring
    have hadd : h₂ = h₁ + c := by
      calc
        h₂ = h₁ + (-a) + (-b) := by simpa [a, b] using heq
        _ = h₁ + c := by
          have hc : -a - b = c := by calc
            -a - b = -(a + b) := by abel
            _ = -(-c) := by rw [habc]
            _ = c := by simp
          calc
            h₁ + (-a) + (-b) = h₁ + (-a - b) := by abel
            _ = h₁ + c := by rw [hc]
    exact noC h₁ h₂ hh₁ hh₂ hadd

private theorem rectMem :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    (∀ (z : GaussianInt), z ∈ DiamondVertexDomains K false ↔ -k ≤ z.re ∧ z.re ≤ k ∧ 0 ≤ z.im ∧
        z.im ≤ 2 * k ∧ z.re + z.im ≤ 2 * k + 1 ∧ -z.re + z.im ≤ 2 * k + 1 ∧ z.re - z.im ≤ 1 ∧
        -z.re - z.im ≤ 1) → (∀ (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤ k) → ((0 ≤ v) → ((v < 2 *
        k) → ((⟨u, v⟩ : GaussianInt) ∈ DiamondVertexDomains K false ↔
        u + v ≤ 2 * k + 1 ∧ u - v ≤ 1))))) := by
  classical
  intro K k hmem u v hu0 huk hv0 hvk
  rw [hmem]
  simp only []
  constructor <;> intro hh <;> omega

private theorem inHalf :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (z : GaussianInt), (z ∈ DiamondVertexDomains K false) → ((¬ (z.im = 2 * k ∧ -1 ≤ z.re ∧
        z.re ≤ 1)) → ((¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨k + 1 - j, k + j⟩) ∨
        (∃ j : Int, 0 ≤ j ∧ j < k ∧ z = ⟨k - j, k + j⟩))) → ((¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z =
            ⟨j - k - 1, k + j - 1⟩) ∨
        (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨j - k - 1, k + j⟩))) → (z ∈ P4818T1HalfOpen K)))) := by
  classical
  intro K k z hz hnotA hnotB hnotC
  change z ∈ DiamondVertexDomains K false ∧ _ ∧ _ ∧ _
  exact ⟨hz, hnotA, hnotB, hnotC⟩

private theorem hr0 :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (x : GaussianInt),
    let r : Int := x.re % (k + 1)
    0 ≤ r := by
  classical
  intro K k x r
  dsimp [r]
  exact Int.emod_nonneg _ (by omega)

private theorem hrlt :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (x : GaussianInt),
    let r : Int := x.re % (k + 1)
    r < k + 1 := by
  classical
  intro K k x r
  have hk : 0 < k := RepresentativesProof.hk K
  dsimp [r]
  exact Int.emod_lt_of_pos _ (by omega)

private theorem hs0 :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (x : GaussianInt),
    let n : Int := x.re / (k + 1)
    let s : Int := (x.im - k * n) % (2 * k)
    0 ≤ s := by
  classical
  intro K k x n s
  have hk : 0 < k := RepresentativesProof.hk K
  dsimp [s]
  exact Int.emod_nonneg _ (by omega)

private theorem hslt :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (x : GaussianInt),
    let n : Int := x.re / (k + 1)
    let s : Int := (x.im - k * n) % (2 * k)
    s < 2 * k := by
  classical
  intro K k x n s
  have hk : 0 < k := RepresentativesProof.hk K
  dsimp [s]
  exact Int.emod_lt_of_pos _ (by omega)

private theorem hre :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (x : GaussianInt),
    let n : Int := x.re / (k + 1)
    let r : Int := x.re % (k + 1)
    x.re = r + n * (k + 1) := by
  classical
  intro K k x n r
  calc
    x.re = x.re % (k + 1) + (k + 1) * (x.re / (k + 1)) :=
      (Int.emod_add_mul_ediv x.re (k + 1)).symm
    _ = r + n * (k + 1) := by simp [r, n]; ring

private theorem him :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (x : GaussianInt),
    let n : Int := x.re / (k + 1)
    let q : Int := (x.im - k * n) / (2 * k)
    let s : Int := (x.im - k * n) % (2 * k)
    x.im = s + 2 * k * q + k * n := by
  classical
  intro K k x n q s
  have hq : s + 2 * k * q = x.im - k * n := by
    simpa [s, q] using Int.emod_add_mul_ediv (x.im - k * n) (2 * k)
  nlinarith

private theorem hxrep :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    ∀ (x : GaussianInt),
    let n : Int := x.re / (k + 1)
    let r : Int := x.re % (k + 1)
    let q : Int := (x.im - k * n) / (2 * k)
    let s : Int := (x.im - k * n) % (2 * k)
    (x.re = r + n * (k + 1)) → ((x.im = s + 2 * k * q + k * n) → (
    let h : GaussianInt := ⟨r, s⟩
    x = h + (-q) • a + n • b)) := by
  classical
  intro K k a b x n r q s hre him h
  ext
  · simp [h, a, b, zsmul_eq_mul, hre]
  · simp [h, a, b, zsmul_eq_mul, him]
    ring

private theorem hrectBounds :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    ∀ (x : GaussianInt),
    let n : Int := x.re / (k + 1)
    let r : Int := x.re % (k + 1)
    let q : Int := (x.im - k * n) / (2 * k)
    let s : Int := (x.im - k * n) % (2 * k)
    (0 ≤ r) → ((r < k + 1) → ((0 ≤ s) → ((s < 2 * k) → ((x.re = r + n * (k + 1)) → ((x.im = s + 2
        * k * q + k * n) → (0 ≤ r ∧ r ≤ k ∧ 0 ≤ s ∧ s < 2 * k)))))) := by
  classical
  intro K k x n r q s hr0 hrlt hs0 hslt hre him
  omega

private theorem hex :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    (∀ (x : GaussianInt), x ∈ DiamondVertexDomains K false ∧ x + ⟨(↑(K.1 : ℕ) : ℤ) + (1 :
        ℤ), (↑(K.1 : ℕ) : ℤ)⟩ ∈ DiamondVertexDomains K false ↔ (∃ (j : ℤ), (1 : ℤ) ≤ j ∧ j
        ≤ (↑(K.1 : ℕ) : ℤ) ∧ x = ⟨-j, j⟩) ∨ ∃ (j : ℤ), (0 : ℤ) ≤ j ∧ j < (↑(K.1 : ℕ)
        : ℤ) ∧ x = ⟨(-1 : ℤ) - j, j⟩) → ((∀ (z : GaussianInt), z ∈
        DiamondVertexDomains K false ↔ -k ≤ z.re ∧ z.re ≤ k ∧ 0 ≤ z.im ∧ z.im ≤ 2 * k ∧ z.re +
        z.im ≤ 2 * k + 1 ∧ -z.re + z.im ≤ 2 * k + 1 ∧ z.re - z.im ≤ 1 ∧ -z.re - z.im ≤ 1) → ((∀
        (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤ k) → ((0 ≤ v) → ((v < 2 * k) → ((⟨u, v⟩ :
        GaussianInt) ∈ DiamondVertexDomains K false ↔ u + v ≤ 2 * k + 1 ∧ u - v ≤ 1))))) → ((∀ (z
        : GaussianInt), (z ∈ DiamondVertexDomains K false) → ((¬ (z.im = 2 * k ∧ -1 ≤ z.re ∧ z.re
        ≤ 1)) → ((¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨k + 1 - j, k + j⟩) ∨ (∃ j : Int, 0 ≤ j ∧ j
        < k ∧ z = ⟨k - j, k + j⟩))) → ((¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨j - k - 1, k + j -
        1⟩) ∨ (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨j - k - 1, k + j⟩))) → (z ∈ P4818T1HalfOpen
        K))))) → (∀ (x : GaussianInt),
    let n : Int := x.re / (k + 1)
    let r : Int := x.re % (k + 1)
    let q : Int := (x.im - k * n) / (2 * k)
    let s : Int := (x.im - k * n) % (2 * k)
    (0 ≤ r) → ((r < k + 1) → ((0 ≤ s) → ((s < 2 * k) → ((x.re = r + n * (k + 1)) → ((x.im = s + 2
        * k * q + k * n) → (
    let h : GaussianInt := ⟨r, s⟩
    (x = h + (-q) • a + n • b) → ((0 ≤ r ∧ r ≤ k ∧ 0 ≤ s ∧ s < 2 * k) → (∃ p : GaussianInt × (Int
        × Int),
      p.1 ∈ P4818T1HalfOpen K ∧
        x = p.1 + p.2.1 • a + p.2.2 • b)))))))))))) := by
  classical
  intro K k a b hB hmem rectMem inHalf x n r q s hr0 hrlt hs0 hslt hre him h hxrep hrectBounds
  by_cases hdiamond : r + s ≤ 2 * k + 1 ∧ r - s ≤ 1
  · have hT : h ∈ DiamondVertexDomains K false := by
      exact (rectMem r s hrectBounds.1 hrectBounds.2.1 hrectBounds.2.2.1 hrectBounds.2.2.2).2
          hdiamond
    by_cases hdel :
        (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h = ⟨k + 1 - j, k + j⟩) ∨
        (∃ j : Int, 0 ≤ j ∧ j < k ∧ h = ⟨k - j, k + j⟩)
    · rcases hdel with (⟨j, hj, hjk, he⟩ | ⟨j, hj, hjk, he⟩)
      · let h' : GaussianInt := ⟨-j, j⟩
        have h'b : h = h' + b := by rw [he]; ext <;> simp [h', b] <;> ring
        have h'T : h' ∈ DiamondVertexDomains K false := by
          have hlist := (hB h').mpr (Or.inl ⟨j, hj, hjk, rfl⟩)
          exact hlist.1
        have hjlt : j < k := by
          have hi := congrArg Zsqrtd.im he
          simp [h] at hi
          omega
        have h'notA : ¬ (h'.im = 2 * k ∧ -1 ≤ h'.re ∧ h'.re ≤ 1) := by
          simp [h']
          omega
        have h'notB : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨k + 1 - j, k + j⟩) ∨
            (∃ j : Int, 0 ≤ j ∧ j < k ∧ h' = ⟨k - j, k + j⟩)) := by
          intro hh
          rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
          · have hre' := congrArg Zsqrtd.re heq
            simp [h'] at hre'
            omega
          · have hre' := congrArg Zsqrtd.re heq
            simp [h'] at hre'
            omega
        have h'notC : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j - 1⟩) ∨
            (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j⟩)) := by
          intro hh
          rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
          · have him' := congrArg Zsqrtd.im heq
            simp [h'] at him'
            omega
          · have him' := congrArg Zsqrtd.im heq
            simp [h'] at him'
            omega
        refine ⟨Prod.mk h' (Prod.mk (-q) (n + 1)), ?_⟩
        constructor
        · exact inHalf h' h'T h'notA h'notB h'notC
        · rw [hxrep, h'b]
          simp only [add_zsmul, one_zsmul]
          abel
      · let h' : GaussianInt := ⟨-1 - j, j⟩
        have h'b : h = h' + b := by rw [he]; ext <;> simp [h', b] <;> ring
        have h'T : h' ∈ DiamondVertexDomains K false := by
          have hlist := (hB h').mpr (Or.inr ⟨j, hj, hjk, rfl⟩)
          exact hlist.1
        have h'notA : ¬ (h'.im = 2 * k ∧ -1 ≤ h'.re ∧ h'.re ≤ 1) := by
          simp [h']
          omega
        have h'notB : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨k + 1 - j, k + j⟩) ∨
            (∃ j : Int, 0 ≤ j ∧ j < k ∧ h' = ⟨k - j, k + j⟩)) := by
          intro hh
          rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
          · have hre' := congrArg Zsqrtd.re heq
            simp [h'] at hre'
            omega
          · have hre' := congrArg Zsqrtd.re heq
            simp [h'] at hre'
            omega
        have h'notC : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j - 1⟩) ∨
            (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j⟩)) := by
          intro hh
          rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
          · have him' := congrArg Zsqrtd.im heq
            simp [h'] at him'
            omega
          · have him' := congrArg Zsqrtd.im heq
            simp [h'] at him'
            omega
        refine ⟨Prod.mk h' (Prod.mk (-q) (n + 1)), ?_⟩
        constructor
        · exact inHalf h' h'T h'notA h'notB h'notC
        · rw [hxrep, h'b]
          simp only [add_zsmul, one_zsmul]
          abel
    · have hnotA : ¬ (h.im = 2 * k ∧ -1 ≤ h.re ∧ h.re ≤ 1) := by
        simp [h]
        omega
      have hnotC : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h = ⟨j - k - 1, k + j - 1⟩) ∨
          (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h = ⟨j - k - 1, k + j⟩)) := by
        intro hh
        rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
        · have hre' := congrArg Zsqrtd.re heq
          simp [h] at hre'
          omega
        · have hre' := congrArg Zsqrtd.re heq
          simp [h] at hre'
          omega
      refine ⟨Prod.mk h (Prod.mk (-q) n), ?_⟩
      constructor
      · exact inHalf h hT hnotA hdel hnotC
      · exact hxrep
  · by_cases hsk : k ≤ s
    · have hsum : 2 * k + 1 < r + s := by omega
      let h' : GaussianInt := ⟨r - k - 1, s - k⟩
      have h'T : h' ∈ DiamondVertexDomains K false := by
        apply (hmem h').2
        simp [h']
        omega
      have h'notA : ¬ (h'.im = 2 * k ∧ -1 ≤ h'.re ∧ h'.re ≤ 1) := by
        simp [h']
        omega
      have h'notB : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨k + 1 - j, k + j⟩) ∨
          (∃ j : Int, 0 ≤ j ∧ j < k ∧ h' = ⟨k - j, k + j⟩)) := by
        intro hh
        rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
        · have hre' := congrArg Zsqrtd.re heq
          simp [h'] at hre'
          omega
        · have hre' := congrArg Zsqrtd.re heq
          simp [h'] at hre'
          omega
      have h'notC : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j - 1⟩) ∨
          (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j⟩)) := by
        simp [h']
        omega
      have h'b : h = h' + b := by ext <;> simp [h, h', b]
      refine ⟨Prod.mk h' (Prod.mk (-q) (n + 1)), ?_⟩
      constructor
      · exact inHalf h' h'T h'notA h'notB h'notC
      · rw [hxrep, h'b]
        simp only [add_zsmul, one_zsmul]
        abel
    · have hlow : s < k := by omega
      have hdiff : 1 < r - s := by omega
      let h' : GaussianInt := ⟨r - k - 1, s + k⟩
      have h'T : h' ∈ DiamondVertexDomains K false := by
        apply (hmem h').2
        simp [h']
        omega
      have h'notA : ¬ (h'.im = 2 * k ∧ -1 ≤ h'.re ∧ h'.re ≤ 1) := by
        simp [h']
        omega
      have h'notB : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨k + 1 - j, k + j⟩) ∨
          (∃ j : Int, 0 ≤ j ∧ j < k ∧ h' = ⟨k - j, k + j⟩)) := by
        intro hh
        rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
        · have hre' := congrArg Zsqrtd.re heq
          simp [h'] at hre'
          omega
        · have hre' := congrArg Zsqrtd.re heq
          simp [h'] at hre'
          omega
      have h'notC : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j - 1⟩) ∨
          (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ h' = ⟨j - k - 1, k + j⟩)) := by
        intro hh
        rcases hh with (⟨l, hl, hlk, heq⟩ | ⟨l, hl, hlk, heq⟩)
        · have him' := congrArg Zsqrtd.im heq
          have hre' := congrArg Zsqrtd.re heq
          simp [h'] at him'
          simp [h'] at hre'
          omega
        · have him' := congrArg Zsqrtd.im heq
          have hre' := congrArg Zsqrtd.re heq
          simp [h'] at him'
          simp [h'] at hre'
          omega
      have h'b : h = h' + a + b := by ext <;> simp [h, h', a, b]; ring
      refine ⟨Prod.mk h' (Prod.mk (-q + 1) (n + 1)), ?_⟩
      constructor
      · exact inHalf h' h'T h'notA h'notB h'notC
      · rw [hxrep, h'b]
        simp only [zsmul_eq_mul]
        push_cast
        ring

private theorem hrel :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    ∀ (x : GaussianInt), ∀ (p : GaussianInt × ℤ × ℤ), (p.1 ∈ P4818T1HalfOpen K ∧ x = p.1 +
        p.2.1 • a + p.2.2 • b) → (∀ (p' : GaussianInt × ℤ × ℤ), (p'.1 ∈ P4818T1HalfOpen K ∧ x =
        p'.1 + p'.2.1 • ⟨(0 : ℤ), (-2 : ℤ) * (↑(K.1 : ℕ) : ℤ)⟩ + p'.2.2 • ⟨(↑(K.1 : ℕ) : ℤ) + (1
            : ℤ), (↑(K.1 : ℕ) : ℤ)⟩) → (p.1 + p.2.1 • a + p.2.2 • b =
      p'.1 + p'.2.1 • a + p'.2.2 • b)) := by
  classical
  intro K k a b x p hp p' hp'
  exact hp.2.symm.trans hp'.2

private theorem hrepr :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    ∀ (p : GaussianInt × ℤ × ℤ), ∀ (p' : GaussianInt × ℤ × ℤ), (p.1 + p.2.1 • a + p.2.2 • b =
        p'.1 + p'.2.1 • a + p'.2.2 • b) → (p'.1 = p.1 + (p.2.1 - p'.2.1) • a + (p.2.2 - p'.2.2) •
        b) := by
  classical
  intro K k a b p p' hrel
  calc
    p'.1 = p.1 + p.2.1 • a + p.2.2 • b - p'.2.1 • a - p'.2.2 • b := by
      rw [hrel]
      abel
    _ = p.1 + (p.2.1 - p'.2.1) • a + (p.2.2 - p'.2.2) • b := by
      rw [sub_zsmul, sub_zsmul]
      abel

private theorem hcAt488 :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    (∀ (h₁ : GaussianInt), ∀ (h₂ : GaussianInt), ∀ (m : Int), ∀ (n : Int), h₁ ∈ P4818T1HalfOpen
        K → h₂ ∈ P4818T1HalfOpen K → h₂ = h₁ + m • a + n • b → m = 0 ∧ n = 0) → (∀ (x :
        GaussianInt), ∀ (p : GaussianInt × ℤ × ℤ), (p.1 ∈ P4818T1HalfOpen K ∧ x = p.1 + p.2.1 •
        a + p.2.2 • b) → (∀ (p' : GaussianInt × ℤ × ℤ), (p'.1 ∈ P4818T1HalfOpen K ∧ x = p'.1 +
        p'.2.1 • ⟨(0 : ℤ), (-2 : ℤ) * (↑(K.1 : ℕ) : ℤ)⟩ + p'.2.2 • ⟨(↑(K.1 :
        ℕ) : ℤ) + (1 : ℤ), (↑(K.1 : ℕ) : ℤ)⟩) → ((p'.1 = p.1 + (p.2.1 - p'.2.1) • a +
        (p.2.2 - p'.2.2) • b) → (p.2.1 - p'.2.1 = (0 : ℤ) ∧ p.2.2 - p'.2.2 = (0 : ℤ))))) := by
  classical
  intro K k a b hinj x p hp p' hp' hrepr
  exact hinj p.1 p'.1 (p.2.1 - p'.2.1) (p.2.2 - p'.2.2)
    hp.1 hp'.1 hrepr

private theorem hm' :
    (DiamondParameter) → ((GaussianInt) → (∀ (p : GaussianInt × ℤ × ℤ), ∀ (p' : GaussianInt × ℤ ×
        ℤ), (p.2.1 - p'.2.1 = (0 : ℤ)) → (p.2.1 = p'.2.1))) := by
  classical
  intro K x p p' hm
  omega

private theorem hn' :
    (DiamondParameter) → ((GaussianInt) → (∀ (p : GaussianInt × ℤ × ℤ), ∀ (p' : GaussianInt × ℤ ×
        ℤ), (p.2.2 - p'.2.2 = (0 : ℤ)) → (p.2.2 = p'.2.2))) := by
  classical
  intro K x p p' hn
  omega

private theorem hpoint :
    ∀ (K : DiamondParameter),
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    ∀ (p : GaussianInt × ℤ × ℤ), ∀ (p' : GaussianInt × ℤ × ℤ), (p.1 + p.2.1 • a + p.2.2 • b =
        p'.1 + p'.2.1 • a + p'.2.2 • b) → ((p.2.1 = p'.2.1) → ((p.2.2 = p'.2.2) → (p.1 = p'.1)))
        := by
  classical
  intro K k a b p p' hrel hm' hn'
  have hrel' := hrel
  rw [hm', hn'] at hrel'
  exact add_right_cancel (add_right_cancel hrel')

end RepresentativesProof

theorem P4818T1Representatives (K : DiamondParameter) :
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    ∀ x : GaussianInt, ∃! p : GaussianInt × (Int × Int),
      p.1 ∈ P4818T1HalfOpen K ∧ x = p.1 + p.2.1 • a + p.2.2 • b := by
-- BODY
  classical
  change {k : Nat // 0 < k} at K
  dsimp only
  let k : Int := K.1
  let a : GaussianInt := ⟨0, -2 * k⟩
  let b : GaussianInt := ⟨k + 1, k⟩
  let c : GaussianInt := ⟨-k - 1, k⟩
  have hk : 0 < k := RepresentativesProof.hk K
  obtain ⟨hcoeff, hA, hB, hC⟩ := P4818T1ClosedOverlaps K
  have hmem (z : GaussianInt) : z ∈ DiamondVertexDomains K false ↔
      -k ≤ z.re ∧ z.re ≤ k ∧ 0 ≤ z.im ∧ z.im ≤ 2 * k ∧
      z.re + z.im ≤ 2 * k + 1 ∧ -z.re + z.im ≤ 2 * k + 1 ∧
      z.re - z.im ≤ 1 ∧ -z.re - z.im ≤ 1 := RepresentativesProof.hmem K z
  have hHmem (z : GaussianInt) (hz : z ∈ P4818T1HalfOpen K) :
      z ∈ DiamondVertexDomains K false := RepresentativesProof.hHmem K z hz
  have noA (u v : GaussianInt) (hu : u ∈ P4818T1HalfOpen K)
      (hv : v ∈ P4818T1HalfOpen K) (hadd : v = u + a) : False := RepresentativesProof.noA K hA
          hHmem u v hu hv hadd
  have noB (u v : GaussianInt) (hu : u ∈ P4818T1HalfOpen K)
      (hv : v ∈ P4818T1HalfOpen K) (hadd : v = u + b) : False := RepresentativesProof.noB K hB
          hHmem u v hu hv hadd
  have noC (u v : GaussianInt) (hu : u ∈ P4818T1HalfOpen K)
      (hv : v ∈ P4818T1HalfOpen K) (hadd : v = u + c) : False := RepresentativesProof.noC K hC
          hHmem u v hu hv hadd
  have hinj : ∀ (h₁ h₂ : GaussianInt) (m n : Int),
      h₁ ∈ P4818T1HalfOpen K → h₂ ∈ P4818T1HalfOpen K →
      h₂ = h₁ + m • a + n • b → m = 0 ∧ n = 0 := RepresentativesProof.hinj K hcoeff hHmem noA noB
          noC
  have rectMem (u v : Int) (hu0 : 0 ≤ u) (huk : u ≤ k)
      (hv0 : 0 ≤ v) (hvk : v < 2 * k) :
      (⟨u, v⟩ : GaussianInt) ∈ DiamondVertexDomains K false ↔
        u + v ≤ 2 * k + 1 ∧ u - v ≤ 1 := RepresentativesProof.rectMem K hmem u v hu0 huk hv0 hvk
  have inHalf (z : GaussianInt) (hz : z ∈ DiamondVertexDomains K false)
      (hnotA : ¬ (z.im = 2 * k ∧ -1 ≤ z.re ∧ z.re ≤ 1))
      (hnotB : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨k + 1 - j, k + j⟩) ∨
        (∃ j : Int, 0 ≤ j ∧ j < k ∧ z = ⟨k - j, k + j⟩)))
      (hnotC : ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨j - k - 1, k + j - 1⟩) ∨
        (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ z = ⟨j - k - 1, k + j⟩))) :
      z ∈ P4818T1HalfOpen K := RepresentativesProof.inHalf K z hz hnotA hnotB hnotC
  intro x
  let n : Int := x.re / (k + 1)
  let r : Int := x.re % (k + 1)
  let q : Int := (x.im - k * n) / (2 * k)
  let s : Int := (x.im - k * n) % (2 * k)
  have hr0 : 0 ≤ r := RepresentativesProof.hr0 K x
  have hrlt : r < k + 1 := RepresentativesProof.hrlt K x
  have hs0 : 0 ≤ s := RepresentativesProof.hs0 K x
  have hslt : s < 2 * k := RepresentativesProof.hslt K x
  have hre : x.re = r + n * (k + 1) := RepresentativesProof.hre K x
  have him : x.im = s + 2 * k * q + k * n := RepresentativesProof.him K x
  let h : GaussianInt := ⟨r, s⟩
  have hxrep : x = h + (-q) • a + n • b := RepresentativesProof.hxrep K x hre him
  have hrectBounds : 0 ≤ r ∧ r ≤ k ∧ 0 ≤ s ∧ s < 2 * k := RepresentativesProof.hrectBounds K x
      hr0 hrlt hs0 hslt hre him
  have hex : ∃ p : GaussianInt × (Int × Int),
      p.1 ∈ P4818T1HalfOpen K ∧
        x = p.1 + p.2.1 • a + p.2.2 • b := RepresentativesProof.hex K hB hmem rectMem inHalf x
            hr0 hrlt hs0 hslt hre him hxrep hrectBounds
  rcases hex with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro p' hp'
  have hrel : p.1 + p.2.1 • a + p.2.2 • b =
      p'.1 + p'.2.1 • a + p'.2.2 • b := RepresentativesProof.hrel K x p hp p' hp'
  have hrepr : p'.1 = p.1 + (p.2.1 - p'.2.1) • a + (p.2.2 - p'.2.2) • b :=
      RepresentativesProof.hrepr K p p' hrel
  have hc := RepresentativesProof.hcAt488 K hinj x p hp p' hp' hrepr
  rcases hc with ⟨hm, hn⟩
  have hm' : p.2.1 = p'.2.1 := RepresentativesProof.hm' K x p p' hm
  have hn' : p.2.2 = p'.2.2 := RepresentativesProof.hn' K x p p' hn
  have hpoint : p.1 = p'.1 := RepresentativesProof.hpoint K p p' hrel hm' hn'
  apply Prod.ext
  · exact hpoint.symm
  · apply Prod.ext <;> omega

end ApollonianSuperharmonic

end
