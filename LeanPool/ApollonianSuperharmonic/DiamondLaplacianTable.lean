/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondOdometer
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: DiamondLaplacianTable]

/-!
# DiamondLaplacianTable

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondLaplacianProof

private theorem habAt289 :
    ∀ (F : ℤ → ℤ → ℤ), ∀ (p : ℤ), ∀ (q : ℤ), ((4 : ℤ) * F (p - (1 : ℤ)) q = (2 : ℤ) * (p - (1 :
        ℤ)) ^ (2 : ℕ) - (2 : ℤ) * |p - (1 : ℤ)| - (p - (1 : ℤ) - q) ^ (2 : ℕ) + (p - (1 : ℤ) - q)
        % (2 : ℤ)) → (((4 : ℤ) * F p (q + (1 : ℤ)) = (2 : ℤ) * p ^ (2 : ℕ) - (2 : ℤ) * |p| - (p -
        (q + (1 : ℤ))) ^ (2 : ℕ) + (p - (q + (1 : ℤ))) % (2 : ℤ)) → (((4 : ℤ) * F p (q - (1 : ℤ))
        = (2 : ℤ) * p ^ (2 : ℕ) - (2 : ℤ) * |p| - (p - (q - (1 : ℤ))) ^ (2 : ℕ) + (p - (q - (1 :
        ℤ))) % (2 : ℤ)) → (((4 : ℤ) * F p q = (2 : ℤ) * p ^ (2 : ℕ) - (2 : ℤ) * |p| - (p - q) ^
        (2 : ℕ) + (p - q) % (2 : ℤ)) → (|p+1| + |p-1| - 2*|p| = (if p=0 then 2 else 0))))) := by
  classical
  intro F p q h2 h3 h4 h0
  split_ifs with hp
  · simp [hp]
  · rcases lt_or_gt_of_ne hp with hp | hp
    · rw [abs_of_nonpos (by omega : p+1 ≤ 0),
        abs_of_nonpos (by omega : p-1 ≤ 0), abs_of_nonpos (by omega : p ≤ 0)]
      omega
    · rw [abs_of_nonneg (by omega : 0 ≤ p+1),
        abs_of_nonneg (by omega : 0 ≤ p-1), abs_of_nonneg (by omega : 0 ≤ p)]
      omega

private theorem bm :
    ∀ (K : DiamondParameter), ∀ (F : ℤ → ℤ → ℤ), ∀ (g : IntegerLatticeFunction), (∀ (x :
        GaussianInt), g (x + ⟨(↑K.1 : ℤ) + (1 : ℤ), (↑K.1 : ℤ)⟩) = g x + (↑K.1 : ℤ) * x.re + x.im
        + (↑K.1 : ℤ) * ((↑K.1 : ℤ) + (1 : ℤ)) / (2 : ℤ)) → (
    let k : Int := K.1
    let C : Int := k*(k+1)/2
    (∀ (p : Int), ∀ (q : Int), (|p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1) → (g ⟨p,q⟩ = F p q)) → (∀
        (p : ℤ), ∀ (q : ℤ), ∀ (e : ℤ), |p + k + (1 : ℤ)| ≤ k ∧ |q| ≤ k ∧ |p + k + (1 : ℤ)| + |q|
        ≤ k + (1 : ℤ) → F (p + k + (1 : ℤ)) (q + k) - k * p - q - C = F p q + e → g ⟨p, q⟩ = F p
        q + e)) := by
  classical
  intro K F g hb k C closed p q e hd he
  have hh := hb ⟨p,q⟩
  have hz := closed (p+k+1) (q+k) (by simpa using hd)
  have hx : (⟨p,q⟩ : GaussianInt)+⟨k+1,k⟩ = ⟨p+k+1,q+k⟩ := by
    ext <;> simp; ring
  change g ((⟨p,q⟩ : GaussianInt)+⟨k+1,k⟩) = g ⟨p,q⟩+k*p+q+C at hh
  rw [hx] at hh
  omega

private theorem cm :
    ∀ (K : DiamondParameter), ∀ (F : ℤ → ℤ → ℤ), ∀ (g : IntegerLatticeFunction), (∀ (x :
        GaussianInt), g (x + ⟨-(↑K.1 : ℤ) - (1 : ℤ), (↑K.1 : ℤ)⟩) = g x - (↑K.1 : ℤ) * x.im -
        (↑K.1 : ℤ) * ((↑K.1 : ℤ) + (1 : ℤ)) / (2 : ℤ)) → (
    let k : Int := K.1
    let C : Int := k*(k+1)/2
    (∀ (p : Int), ∀ (q : Int), (|p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1) → (g ⟨p,q⟩ = F p q)) → (∀
        (p : ℤ), ∀ (q : ℤ), ∀ (e : ℤ), |p - k - (1 : ℤ)| ≤ k ∧ |q| ≤ k ∧ |p - k - (1 : ℤ)| + |q|
        ≤ k + (1 : ℤ) → F (p - k - (1 : ℤ)) (q + k) + k * q + C = F p q + e → g ⟨p, q⟩ = F p q +
        e)) := by
  classical
  intro K F g hc k C closed p q e hd he
  have hh := hc ⟨p,q⟩
  have hz := closed (p-k-1) (q+k) (by simpa using hd)
  have hx : (⟨p,q⟩ : GaussianInt)+⟨-k-1,k⟩ = ⟨p-k-1,q+k⟩ := by
    ext <;> simp; ring
  change g ((⟨p,q⟩ : GaussianInt)+⟨-k-1,k⟩) = g ⟨p,q⟩-k*q-C at hh
  rw [hx] at hh
  omega

private theorem bp :
    ∀ (K : DiamondParameter), ∀ (F : ℤ → ℤ → ℤ), ∀ (g : IntegerLatticeFunction), (∀ (x :
        GaussianInt), g (x + ⟨(↑K.1 : ℤ) + (1 : ℤ), (↑K.1 : ℤ)⟩) = g x + (↑K.1 : ℤ) * x.re + x.im
        + (↑K.1 : ℤ) * ((↑K.1 : ℤ) + (1 : ℤ)) / (2 : ℤ)) → (
    let k : Int := K.1
    let C : Int := k*(k+1)/2
    (∀ (p : Int), ∀ (q : Int), (|p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1) → (g ⟨p,q⟩ = F p q)) → (∀
        (p : ℤ), ∀ (q : ℤ), ∀ (e : ℤ), |p - k - (1 : ℤ)| ≤ k ∧ |q - (2 : ℤ) * k| ≤ k ∧ |p - k -
        (1 : ℤ)| + |q - (2 : ℤ) * k| ≤ k + (1 : ℤ) → F (p - k - (1 : ℤ)) (q - k) + k * (p - k -
        (1 : ℤ)) + (q - k) + C = F p q + e → g ⟨p, q⟩ = F p q + e)) := by
  classical
  intro K F g hb k C closed p q e hd he
  have hh := hb ⟨p-k-1,q-k⟩
  have hz := closed (p-k-1) (q-k)
    (by simpa only [show q-k-k=q-2*k by ring] using hd)
  have hx : (⟨p-k-1,q-k⟩ : GaussianInt)+⟨k+1,k⟩ = ⟨p,q⟩ := by
    ext <;> simp
  change g ((⟨p-k-1,q-k⟩ : GaussianInt)+⟨k+1,k⟩) =
    g ⟨p-k-1,q-k⟩+k*(p-k-1)+(q-k)+C at hh
  rw [hx] at hh
  omega

private theorem cp :
    ∀ (K : DiamondParameter), ∀ (F : ℤ → ℤ → ℤ), ∀ (g : IntegerLatticeFunction), (∀ (x :
        GaussianInt), g (x + ⟨-(↑K.1 : ℤ) - (1 : ℤ), (↑K.1 : ℤ)⟩) = g x - (↑K.1 : ℤ) * x.im -
        (↑K.1 : ℤ) * ((↑K.1 : ℤ) + (1 : ℤ)) / (2 : ℤ)) → (
    let k : Int := K.1
    let C : Int := k*(k+1)/2
    (∀ (p : Int), ∀ (q : Int), (|p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1) → (g ⟨p,q⟩ = F p q)) → (∀
        (p : ℤ), ∀ (q : ℤ), ∀ (e : ℤ), |p + k + (1 : ℤ)| ≤ k ∧ |q - (2 : ℤ) * k| ≤ k ∧ |p + k +
        (1 : ℤ)| + |q - (2 : ℤ) * k| ≤ k + (1 : ℤ) → F (p + k + (1 : ℤ)) (q - k) - k * (q - k) -
        C = F p q + e → g ⟨p, q⟩ = F p q + e)) := by
  classical
  intro K F g hc k C closed p q e hd he
  have hh := hc ⟨p+k+1,q-k⟩
  have hz := closed (p+k+1) (q-k)
    (by simpa only [show q-k-k=q-2*k by ring] using hd)
  have hx : (⟨p+k+1,q-k⟩ : GaussianInt)+⟨-k-1,k⟩ = ⟨p,q⟩ := by
    ext <;> simp
  change g ((⟨p+k+1,q-k⟩ : GaussianInt)+⟨-k-1,k⟩) =
    g ⟨p+k+1,q-k⟩-k*(q-k)-C at hh
  rw [hx] at hh
  omega

private theorem am :
    ∀ (K : DiamondParameter), ∀ (F : ℤ → ℤ → ℤ), ∀ (g : IntegerLatticeFunction), (∀ (x :
        GaussianInt), g (x + ⟨(0 : ℤ), -((2 : ℤ) * (↑K.1 : ℤ))⟩) = g x + -(↑K.1 : ℤ) * x.re +
        ((↑K.1 : ℤ) - (1 : ℤ)) * x.im - (↑K.1 : ℤ) * ((↑K.1 : ℤ) - (2 : ℤ))) → (
    let k : Int := K.1
    (∀ (p : Int), ∀ (q : Int), (|p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1) → (g ⟨p,q⟩ = F p q)) → (∀
        (p : ℤ), ∀ (q : ℤ), ∀ (e : ℤ), |p| ≤ k ∧ |q + k| ≤ k ∧ |p| + |q + k| ≤ k + (1 : ℤ) → F p
        (q + (2 : ℤ) * k) - k * p + (k - (1 : ℤ)) * (q + (2 : ℤ) * k) - k * (k - (2 : ℤ)) = F p q
        + e → g ⟨p, q⟩ = F p q + e)) := by
  classical
  intro K F g ha k closed p q e hd he
  have hh := ha ⟨p,q+2*k⟩
  have hz := closed p (q+2*k)
    (by simpa only [show q+2*k-k=q+k by ring] using hd)
  have hx : (⟨p,q+2*k⟩ : GaussianInt)+⟨0,-(2*k)⟩ = ⟨p,q⟩ := by
    ext <;> simp
  change g ((⟨p,q+2*k⟩ : GaussianInt)+⟨0,-(2*k)⟩) =
    g ⟨p,q+2*k⟩ + -k*p+(k-1)*(q+2*k)-k*(k-2) at hh
  rw [hx] at hh
  nlinarith only [hh, hz, he]

private theorem ap :
    ∀ (K : DiamondParameter), ∀ (F : ℤ → ℤ → ℤ), ∀ (g : IntegerLatticeFunction), (∀ (x :
        GaussianInt), g (x + ⟨(0 : ℤ), -((2 : ℤ) * (↑K.1 : ℤ))⟩) = g x + -(↑K.1 : ℤ) * x.re +
        ((↑K.1 : ℤ) - (1 : ℤ)) * x.im - (↑K.1 : ℤ) * ((↑K.1 : ℤ) - (2 : ℤ))) → (
    let k : Int := K.1
    (∀ (p : Int), ∀ (q : Int), (|p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1) → (g ⟨p,q⟩ = F p q)) → (∀
        (p : ℤ), ∀ (q : ℤ), ∀ (e : ℤ), |p| ≤ k ∧ |q - (3 : ℤ) * k| ≤ k ∧ |p| + |q - (3 : ℤ) * k|
        ≤ k + (1 : ℤ) → F p (q - (2 : ℤ) * k) + k * p - (k - (1 : ℤ)) * q + k * (k - (2 : ℤ)) = F
        p q + e → g ⟨p, q⟩ = F p q + e)) := by
  classical
  intro K F g ha k closed p q e hd he
  have hh := ha ⟨p,q⟩
  have hz := closed p (q-2*k)
    (by simpa only [show q-2*k-k=q-3*k by ring] using hd)
  have hx : (⟨p,q⟩ : GaussianInt)+⟨0,-(2*k)⟩ = ⟨p,q-2*k⟩ := by
    ext <;> simp; ring
  change g ((⟨p,q⟩ : GaussianInt)+⟨0,-(2*k)⟩) =
    g ⟨p,q⟩ + -k*p+(k-1)*q-k*(k-2) at hh
  rw [hx] at hh
  nlinarith only [hh, hz, he]

end DiamondLaplacianProof

theorem DiamondLaplacianTable (K : DiamondParameter) :
    (∀ x, FourNeighborLaplacian (DiamondOdometer K)
        (x + ⟨0, (2 * K.1 : Int)⟩) =
          FourNeighborLaplacian (DiamondOdometer K) x ∧
      FourNeighborLaplacian (DiamondOdometer K)
        (x + ⟨(K.1 + 1 : Int), (K.1 : Int)⟩) =
          FourNeighborLaplacian (DiamondOdometer K) x) ∧
    (∀ x, x ∈ DiamondVertexDomains K false ->
      x ∉ DiamondVertexDomains K true ->
      FourNeighborLaplacian (DiamondOdometer K) x = 1) ∧
    (∀ x, x ∈ DiamondVertexDomains K true ->
      FourNeighborLaplacian (DiamondOdometer K) x =
        (if Even (x.re + x.im) then 1 else -1) -
          (if x.re = 0 then 1 else 0)) := by
-- BODY
  let F (p q : Int) : Int :=
    (Int.natAbs p : Int) * ((Int.natAbs p : Int) - 1) / 2 - (p-q)^2 / 4
  let E (k p q : Int) : Int :=
    if |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1 then 0
    else if q=k then 0 else 1
  have hscale : ∀ p q, 4*F p q=2*p^2-2*|p|-(p-q)^2+(p-q)%2 := scaled
  obtain ⟨ha, hb, hc, hf⟩ :=
    (Classical.choose_spec (DiamondOdometerExistsUnique K)).1
  let k : Int := K.1
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast K.2
  have hF : ∀ x, x ∈ DiamondVertexDomains K false →
      DiamondOdometer K x = F x.re x.im := hf
  have hpa := periodic (DiamondOdometer K) ⟨0,-(2*k)⟩
    (-k) (k-1) (-k*(k-2)) (by
      intro x
      have h := ha x
      change DiamondOdometer K (x+⟨0,-(2*k)⟩) =
        DiamondOdometer K x + -k*x.re + (k-1)*x.im - k*(k-2) at h
      nlinarith only [h])
  have hpb := periodic (DiamondOdometer K) ⟨k+1,k⟩
    k 1 (k*(k+1)/2) (by
      intro x
      have h := hb x
      change DiamondOdometer K (x+⟨k+1,k⟩) =
        DiamondOdometer K x+k*x.re+x.im+k*(k+1)/2 at h
      simpa only [one_mul] using h)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · have h := hpa (x+⟨0,2*k⟩)
      have he : x+⟨0,2*k⟩+⟨0,-(2*k)⟩ = x := by ext <;> simp
      rw [he] at h
      exact h.symm
    · exact hpb x
  · rintro ⟨p,q⟩ hx hi
    have hd := bounds K p q hx
    change ¬ Int.natAbs p + Int.natAbs (q-k) ≤ K.1-1 at hi
    have hpabs := Int.natCast_natAbs p
    have hqabs := Int.natCast_natAbs (q-k)
    have hshell : k ≤ |p|+|q-k| ∧ |p|+|q-k| ≤ k+1 := by
      change |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1 at hd
      omega
    have hv := extended F hscale K (DiamondOdometer K) ha hb hc hF
    have h1 := hv (p+1) q (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
    have h2 := hv (p-1) q (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
    have h3 := hv p (q+1) (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
    have h4 := hv p (q-1) (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
      (by simp only [abs_eq_max_neg] at hd ⊢; omega)
    have hl := stencil F hscale (DiamondOdometer K) p q _ _ _ _ (hF _ hx) h1 h2 h3 h4
    have he := shellErrors k p q hk hd.1 hd.2.1 hshell
    change FourNeighborLaplacian (DiamondOdometer K) ⟨p,q⟩ =
      1-2*((p-q)%2)-(if p=0 then 1 else 0)+
        E k (p+1) q+E k (p-1) q+E k p (q+1)+E k p (q-1) at hl
    linarith only [hl, he]
  · rintro ⟨p,q⟩ hx
    change Int.natAbs p + Int.natAbs (q-k) ≤ K.1-1 at hx
    have hpabs := Int.natCast_natAbs p
    have hqabs := Int.natCast_natAbs (q-k)
    have hi : |p|+|q-k| ≤ k-1 := by omega
    have closed (p' q' : Int)
        (hh : |p'| ≤ k ∧ |q'-k| ≤ k ∧ |p'|+|q'-k| ≤ k+1) :
        DiamondOdometer K ⟨p',q'⟩ = F p' q' := hF _ (domain K p' q' hh)
    have h0 := closed p q (by simp only [abs_eq_max_neg] at hi ⊢; omega)
    have h1 : DiamondOdometer K ⟨p+1,q⟩ = F (p+1) q+0 := by
      simpa using closed (p+1) q (by simp only [abs_eq_max_neg] at hi ⊢; omega)
    have h2 : DiamondOdometer K ⟨p-1,q⟩ = F (p-1) q+0 := by
      simpa using closed (p-1) q (by simp only [abs_eq_max_neg] at hi ⊢; omega)
    have h3 : DiamondOdometer K ⟨p,q+1⟩ = F p (q+1)+0 := by
      simpa using closed p (q+1) (by simp only [abs_eq_max_neg] at hi ⊢; omega)
    have h4 : DiamondOdometer K ⟨p,q-1⟩ = F p (q-1)+0 := by
      simpa using closed p (q-1) (by simp only [abs_eq_max_neg] at hi ⊢; omega)
    have hl := stencil F hscale (DiamondOdometer K) p q 0 0 0 0 h0 h1 h2 h3 h4
    have hpar : (if Even (p+q) then (1 : Int) else -1) = 1-2*((p-q)%2) := by
      simp only [Int.even_iff]
      split_ifs <;> omega
    change FourNeighborLaplacian (DiamondOdometer K) ⟨p,q⟩ =
      (if Even (p+q) then 1 else -1) - (if p=0 then 1 else 0)
    rw [hpar]
    simpa using hl
where
  tri (a : Int) : 2 * (a * (a-1) / 2) = a * (a-1) := by
    have h := Int.emod_two_eq_zero_or_one a
    rcases h with h | h
    · have ha : a = 2 * (a / 2) := by omega
      rw [ha]
      have he : 2 * (a / 2) * (2 * (a / 2) - 1) =
          2 * ((a / 2) * (2 * (a / 2) - 1)) := by ring
      rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2 : Int) ≠ 0)]
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rw [ha]
      have he : (2 * (a / 2) + 1) * (2 * (a / 2) + 1 - 1) =
          2 * ((2 * (a / 2) + 1) * (a / 2)) := by ring
      rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (2 : Int) ≠ 0)]
  square (d : Int) : 4 * (d^2 / 4) = d^2 - d % 2 := by
    rcases Int.emod_two_eq_zero_or_one d with h | h
    · have hd : d = 2 * (d / 2) := by omega
      have he : d^2 = 4 * (d/2)^2 := by
        conv_lhs => rw [hd]
        ring
      rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (4 : Int) ≠ 0), h]
      ring
    · have hd : d = 2 * (d / 2) + 1 := by omega
      have he : d^2 = 4 * ((d/2)^2 + d/2) + 1 := by
        conv_lhs => rw [hd]
        ring
      rw [he, h]
      omega
  scaled (p q : Int) :
      4 * (fun (p q : Int) => (Int.natAbs p : Int) * ((Int.natAbs p : Int) - 1) / 2 - (p-q)^2 /
          4) p q = 2*p^2 - 2*|p| - (p-q)^2 + (p-q)%2 := by
    let F (p q : Int) : Int :=
      (Int.natAbs p : Int) * ((Int.natAbs p : Int) - 1) / 2 - (p-q)^2 / 4
    change 4*F p q = 2*p^2-2*|p|-(p-q)^2+(p-q)%2
    have ht := tri (Int.natAbs p : Int)
    have hs := square (p-q)
    have hab : (Int.natAbs p : Int)^2 = p^2 := by
      rw [Int.natCast_natAbs, sq_abs]
    unfold F
    rw [Int.natCast_natAbs] at ht hab ⊢
    nlinarith only [ht, hs, hab]
  domain (K : DiamondParameter) (p q : Int)
      (h : |p| ≤ (K.1 : Int) ∧ |q-K.1| ≤ (K.1 : Int) ∧
        |p| + |q-K.1| ≤ (K.1 : Int)+1) :
      (⟨p,q⟩ : GaussianInt) ∈ DiamondVertexDomains K false := by
    change max (Int.natAbs p) (max (Int.natAbs (q-K.1))
      (Int.natAbs p + Int.natAbs (q-K.1) - 1)) ≤ K.1
    rw [max_le_iff, max_le_iff]
    have hp := Int.natCast_natAbs p
    have hq := Int.natCast_natAbs (q-K.1)
    omega
  periodic (g : IntegerLatticeFunction) (v : GaussianInt)
      (a b c : Int)
      (h : ∀ x, g (x+v) = g x + a*x.re + b*x.im + c) :
      ∀ x, FourNeighborLaplacian g (x+v) = FourNeighborLaplacian g x := by
    intro x
    unfold FourNeighborLaplacian
    rw [show x+v+1 = (x+1)+v by abel,
      show x+v-1 = (x-1)+v by abel,
      show x+v+⟨0,1⟩ = (x+⟨0,1⟩)+v by abel,
      show x+v-⟨0,1⟩ = (x-⟨0,1⟩)+v by abel]
    rw [h, h, h, h, h]
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub,
      Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
    ring
  formalLap (F : Int → Int → Int)
      (hscale : ∀ p q, 4*F p q=2*p^2-2*|p|-(p-q)^2+(p-q)%2) (p q : Int) :
      F (p+1) q + F (p-1) q + F p (q+1) + F p (q-1) - 4*F p q =
      1 - 2*((p-q)%2) - (if p=0 then 1 else 0) := by
    have h1 := hscale (p+1) q
    have h2 := hscale (p-1) q
    have h3 := hscale p (q+1)
    have h4 := hscale p (q-1)
    have h0 := hscale p q
    have hm : (p+1-q)%2 + (p-1-q)%2 + (p-(q+1))%2 + (p-(q-1))%2 =
        4 - 4*((p-q)%2) := by omega
    have hab : |p+1| + |p-1| - 2*|p| = (if p=0 then 2 else 0) := DiamondLaplacianProof.habAt289 F
        p q h2 h3 h4 h0
    split_ifs at hab ⊢
    all_goals
      apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
      linear_combination h1+h2+h3+h4-4*h0-2*hab+hm
  shellErrors (k p q : Int) (hk : 1 ≤ k)
      (hp : |p| ≤ k) (hq : |q-k| ≤ k)
      (ht : k ≤ |p|+|q-k| ∧ |p|+|q-k| ≤ k+1) :
      (fun (k p q : Int) => if |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1 then 0
    else if q=k then 0 else 1) k (p+1) q + (fun (k p q : Int) => if |p| ≤ k ∧ |q-k| ≤ k ∧
        |p|+|q-k| ≤ k+1 then 0
    else if q=k then 0 else 1) k (p-1) q + (fun (k p q : Int) => if |p| ≤ k ∧ |q-k| ≤ k ∧
        |p|+|q-k| ≤ k+1 then 0
    else if q=k then 0 else 1) k p (q+1) + (fun (k p q : Int) => if |p| ≤ k ∧ |q-k| ≤ k ∧
        |p|+|q-k| ≤ k+1 then 0
    else if q=k then 0 else 1) k p (q-1) =
        2*((p-q)%2) + (if p=0 then 1 else 0) := by
    let E (k p q : Int) : Int :=
      if |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1 then 0
      else if q=k then 0 else 1
    change E k (p+1) q+E k (p-1) q+E k p (q+1)+E k p (q-1) =
      2*((p-q)%2)+(if p=0 then 1 else 0)
    by_cases hp0 : p=0
    · subst p
      have cases : q=0 ∨ q=2*k := by
        simp only [abs_eq_max_neg] at hp hq ht
        omega
      rcases cases with rfl | rfl
      all_goals
        simp only [abs_eq_max_neg] at hp hq ht
        simp (disch := omega) only [E, abs_eq_max_neg, max_eq_left,
          max_eq_right, ite_eq_left, ite_eq_right]
        simp
    by_cases hq0 : q=k
    · subst q
      have cases : p = -k ∨ p=k := by
        simp only [abs_eq_max_neg] at hp hq ht
        omega
      have hmod : (p - k) % 2 = 0 := by
        rcases cases with h | h
        · rw [h, show -k - k = 2 * (-k) by ring]
          omega
        · simp [h]
      rw [hmod]
      rcases cases with rfl | rfl
      all_goals
        simp only [abs_eq_max_neg] at hp hq ht
        simp (disch := omega) only [E, abs_eq_max_neg, max_eq_left,
          max_eq_right, ite_eq_left, ite_eq_right]
        simp
    have cases : |p|+|q-k|=k ∨ |p|+|q-k|=k+1 := by omega
    rcases cases with ht0 | ht0 <;>
      rcases lt_or_gt_of_ne hp0 with hsign | hsign <;>
      rcases lt_or_gt_of_ne hq0 with hside | hside
    all_goals
      simp only [abs_eq_max_neg] at hp hq ht ht0
      simp (disch := omega) only [E, abs_eq_max_neg, max_eq_left,
        max_eq_right, ite_eq_left, ite_eq_right]
      omega
  extended (F : Int → Int → Int)
      (hscale : ∀ p q, 4*F p q=2*p^2-2*|p|-(p-q)^2+(p-q)%2) (K : DiamondParameter) (g :
          IntegerLatticeFunction)
      (ha : ∀ x, g (x + ⟨0, -(2 * K.1 : Int)⟩) = g x +
        (-(K.1 : Int))*x.re + ((K.1 : Int)-1)*x.im - (K.1 : Int)*((K.1 : Int)-2))
      (hb : ∀ x, g (x + ⟨(K.1+1 : Int), (K.1 : Int)⟩) = g x +
        (K.1 : Int)*x.re + x.im + (K.1 : Int)*(K.1+1)/2)
      (hc : ∀ x, g (x + ⟨-(K.1 : Int)-1, (K.1 : Int)⟩) = g x -
        (K.1 : Int)*x.im - (K.1 : Int)*(K.1+1)/2)
      (hf : ∀ x, x ∈ DiamondVertexDomains K false → g x = F x.re x.im)
      (p q : Int) (hp : |p| ≤ (K.1 : Int)+1)
      (hq : |q-K.1| ≤ (K.1 : Int)+1)
      (ht : |p|+|q-K.1| ≤ (K.1 : Int)+2) :
      g ⟨p,q⟩ = F p q + (fun (k p q : Int) => if |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1 then 0
    else if q=k then 0 else 1) K.1 p q := by
    let E (k p q : Int) : Int :=
      if |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1 then 0
      else if q=k then 0 else 1
    change ∀ x, x ∈ DiamondVertexDomains K false → g x=F x.re x.im at hf
    change g ⟨p,q⟩=F p q+E K.1 p q
    let k : Int := K.1
    let C : Int := k*(k+1)/2
    have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast K.2
    change |p| ≤ k+1 at hp
    change |q-k| ≤ k+1 at hq
    change |p|+|q-k| ≤ k+2 at ht
    change g ⟨p,q⟩ = F p q + E k p q
    have closed (p q : Int) (hd : |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1) :
        g ⟨p,q⟩ = F p q := hf _ (domain K p q hd)
    have bm (p q e : Int)
        (hd : |p+k+1| ≤ k ∧ |q| ≤ k ∧ |p+k+1|+|q| ≤ k+1)
        (he : F (p+k+1) (q+k) - k*p-q-C = F p q+e) :
        g ⟨p,q⟩ = F p q+e := DiamondLaplacianProof.bm K F g hb closed p q e hd he
    have cm (p q e : Int)
        (hd : |p-k-1| ≤ k ∧ |q| ≤ k ∧ |p-k-1|+|q| ≤ k+1)
        (he : F (p-k-1) (q+k) + k*q+C = F p q+e) :
        g ⟨p,q⟩ = F p q+e := DiamondLaplacianProof.cm K F g hc closed p q e hd he
    have bp (p q e : Int)
        (hd : |p-k-1| ≤ k ∧ |q-2*k| ≤ k ∧ |p-k-1|+|q-2*k| ≤ k+1)
        (he : F (p-k-1) (q-k) + k*(p-k-1)+(q-k)+C = F p q+e) :
        g ⟨p,q⟩ = F p q+e := DiamondLaplacianProof.bp K F g hb closed p q e hd he
    have cp (p q e : Int)
        (hd : |p+k+1| ≤ k ∧ |q-2*k| ≤ k ∧ |p+k+1|+|q-2*k| ≤ k+1)
        (he : F (p+k+1) (q-k) - k*(q-k)-C = F p q+e) :
        g ⟨p,q⟩ = F p q+e := DiamondLaplacianProof.cp K F g hc closed p q e hd he
    have am (p q e : Int)
        (hd : |p| ≤ k ∧ |q+k| ≤ k ∧ |p|+|q+k| ≤ k+1)
        (he : F p (q+2*k) - k*p+(k-1)*(q+2*k)-k*(k-2) = F p q+e) :
        g ⟨p,q⟩ = F p q+e := DiamondLaplacianProof.am K F g ha closed p q e hd he
    have ap (p q e : Int)
        (hd : |p| ≤ k ∧ |q-3*k| ≤ k ∧ |p|+|q-3*k| ≤ k+1)
        (he : F p (q-2*k) + k*p-(k-1)*q+k*(k-2) = F p q+e) :
        g ⟨p,q⟩ = F p q+e := DiamondLaplacianProof.ap K F g ha closed p q e hd he
    by_cases hd : |p| ≤ k ∧ |q-k| ≤ k ∧ |p|+|q-k| ≤ k+1
    · simp only [E, ite_eq_left hd, add_zero]
      exact closed p q hd
    simp only [E, ite_eq_right hd]
    have hC : 2*C = k*(k+1) := by
      dsimp [C]
      have he : k*(k+1) = (k+1)*((k+1)-1) := by ring
      rw [he]
      exact tri (k+1)
    by_cases hzero : p=0
    · subst p
      have cases : q = -1 ∨ q = 2*k+1 := by
        simp only [abs_eq_max_neg] at hp hq ht hd
        omega
      rcases cases with rfl | rfl
      · rw [ite_eq_right (by omega : (-1 : Int) ≠ k)]
        apply am 0 (-1) 1
        · simp only [abs_eq_max_neg]; omega
        · have hy := hscale 0 (-1)
          have hz := hscale 0 (-1+2*k)
          have hm : (0-(-1+2*k))%2=1 := by omega
          simp only [abs_zero, hm] at hy hz
          have my : (0-(-1 : Int))%2=1 := by norm_num
          rw [my] at hy
          apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
          linear_combination hz-hy
      · rw [ite_eq_right (by omega : 2*k+1 ≠ k)]
        apply ap 0 (2*k+1) 1
        · simp only [abs_eq_max_neg]; omega
        · have hy := hscale 0 (2*k+1)
          have hz := hscale 0 (2*k+1-2*k)
          have hm : (0-(2*k+1))%2=1 := by omega
          have hmz : (0-(2*k+1-2*k))%2=1 := by omega
          simp only [abs_zero, hm, hmz] at hy hz
          apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
          linear_combination hz-hy
    by_cases hmid : q=k
    · rw [ite_eq_left hmid]
      subst q
      have cases : p = -k-1 ∨ p = k+1 := by
        simp only [abs_eq_max_neg] at hp hq ht hd
        omega
      rcases cases with rfl | rfl
      · apply bm (-k-1) k 0
        · simp only [abs_eq_max_neg]; omega
        · have hy := hscale (-k-1) k
          have hz := hscale (-k-1+k+1) (k+k)
          have ay : |-k-1|=k+1 := by simp only [abs_eq_max_neg]; omega
          have az : |-k-1+k+1|=0 := by simp only [abs_eq_max_neg]; omega
          have my : (-k-1-k)%2=1 := by omega
          have mz : (-k-1+k+1-(k+k))%2=0 := by omega
          rw [ay, my] at hy
          rw [az, mz] at hz
          apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
          linear_combination hz-hy-2*hC
      · apply bp (k+1) k 0
        · simp only [abs_eq_max_neg]; omega
        · have hy := hscale (k+1) k
          have hz := hscale (k+1-k-1) (k-k)
          have ay : |k+1|=k+1 := by simp only [abs_eq_max_neg]; omega
          have az : |k+1-k-1|=0 := by simp only [abs_eq_max_neg]; omega
          have my : (k+1-k)%2=1 := by omega
          have mz : (k+1-k-1-(k-k))%2=0 := by omega
          rw [ay, my] at hy
          rw [az, mz] at hz
          apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
          linear_combination hz-hy+2*hC
    rw [ite_eq_right hmid]
    have hout : |p|+|q-k|=k+2 := by
      simp only [abs_eq_max_neg] at hp hq ht hd ⊢
      omega
    rcases lt_or_gt_of_ne hzero with hsign | hsign <;>
      rcases lt_or_gt_of_ne hmid with hside | hside
    · have heq : q = -p-2 := by
        simp only [abs_eq_max_neg] at hout
        omega
      rw [heq]
      apply bm p (-p-2) 1
      · simp only [abs_eq_max_neg] at hp hq ht ⊢; omega
      · have hy := hscale p (-p-2)
        have hz := hscale (p+k+1) ((-p-2)+k)
        have ay : |p| = -p := by simp only [abs_eq_max_neg]; omega
        have az : |p+k+1| = p+k+1 := by simp only [abs_eq_max_neg] at hp ⊢; omega
        have my : (p-(-p-2))%2=0 := by omega
        have mz : (p+k+1-((-p-2)+k))%2=1 := by omega
        rw [ay, my] at hy
        rw [az, mz] at hz
        apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
        linear_combination hz-hy-2*hC
    · have heq : q = p+2*k+2 := by
        simp only [abs_eq_max_neg] at hout
        omega
      rw [heq]
      apply cp p (p+2*k+2) 1
      · simp only [abs_eq_max_neg] at hp hq ht ⊢; omega
      · have hy := hscale p (p+2*k+2)
        have hz := hscale (p+k+1) ((p+2*k+2)-k)
        have ay : |p| = -p := by simp only [abs_eq_max_neg]; omega
        have az : |p+k+1| = p+k+1 := by simp only [abs_eq_max_neg] at hp ⊢; omega
        have my : (p-(p+2*k+2))%2=0 := by omega
        have mz : (p+k+1-((p+2*k+2)-k))%2=1 := by omega
        rw [ay, my] at hy
        rw [az, mz] at hz
        apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
        linear_combination hz-hy-2*hC
    · have heq : q = p-2 := by
        simp only [abs_eq_max_neg] at hout
        omega
      rw [heq]
      apply cm p (p-2) 1
      · simp only [abs_eq_max_neg] at hp hq ht ⊢; omega
      · have hy := hscale p (p-2)
        have hz := hscale (p-k-1) ((p-2)+k)
        have ay : |p| = p := by simp only [abs_eq_max_neg]; omega
        have az : |p-k-1| = -(p-k-1) := by simp only [abs_eq_max_neg] at hp ⊢; omega
        have my : (p-(p-2))%2=0 := by omega
        have mz : (p-k-1-((p-2)+k))%2=1 := by omega
        rw [ay, my] at hy
        rw [az, mz] at hz
        apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
        linear_combination hz-hy+2*hC
    · have heq : q = 2*k+2-p := by
        simp only [abs_eq_max_neg] at hout
        omega
      rw [heq]
      apply bp p (2*k+2-p) 1
      · simp only [abs_eq_max_neg] at hp hq ht ⊢; omega
      · have hy := hscale p (2*k+2-p)
        have hz := hscale (p-k-1) ((2*k+2-p)-k)
        have ay : |p| = p := by simp only [abs_eq_max_neg]; omega
        have az : |p-k-1| = -(p-k-1) := by simp only [abs_eq_max_neg] at hp ⊢; omega
        have my : (p-(2*k+2-p))%2=0 := by omega
        have mz : (p-k-1-((2*k+2-p)-k))%2=1 := by omega
        rw [ay, my] at hy
        rw [az, mz] at hz
        apply mul_left_cancel₀ (by norm_num : (4 : Int) ≠ 0)
        linear_combination hz-hy+2*hC
  bounds (K : DiamondParameter) (p q : Int)
      (h : (⟨p,q⟩ : GaussianInt) ∈ DiamondVertexDomains K false) :
      |p| ≤ (K.1 : Int) ∧ |q-K.1| ≤ (K.1 : Int) ∧
        |p|+|q-K.1| ≤ (K.1 : Int)+1 := by
    change max (Int.natAbs p) (max (Int.natAbs (q-K.1))
      (Int.natAbs p + Int.natAbs (q-K.1) - 1)) ≤ K.1 at h
    rw [max_le_iff, max_le_iff] at h
    have hp := Int.natCast_natAbs p
    have hq := Int.natCast_natAbs (q-K.1)
    omega
  stencil (F : Int → Int → Int)
      (hscale : ∀ p q, 4*F p q=2*p^2-2*|p|-(p-q)^2+(p-q)%2) (g : IntegerLatticeFunction) (p q e1
          e2 e3 e4 : Int)
      (h0 : g ⟨p,q⟩ = F p q)
      (h1 : g ⟨p+1,q⟩ = F (p+1) q+e1)
      (h2 : g ⟨p-1,q⟩ = F (p-1) q+e2)
      (h3 : g ⟨p,q+1⟩ = F p (q+1)+e3)
      (h4 : g ⟨p,q-1⟩ = F p (q-1)+e4) :
      FourNeighborLaplacian g ⟨p,q⟩ =
        1 - 2*((p-q)%2) - (if p=0 then 1 else 0) + e1+e2+e3+e4 := by
    change g ⟨p,q⟩=F p q at h0
    change g ⟨p+1,q⟩=F (p+1) q+e1 at h1
    change g ⟨p-1,q⟩=F (p-1) q+e2 at h2
    change g ⟨p,q+1⟩=F p (q+1)+e3 at h3
    change g ⟨p,q-1⟩=F p (q-1)+e4 at h4
    have a : (⟨p,q⟩ : GaussianInt)+1 = ⟨p+1,q⟩ := by ext <;> simp
    have b : (⟨p,q⟩ : GaussianInt)-1 = ⟨p-1,q⟩ := by ext <;> simp
    have c : (⟨p,q⟩ : GaussianInt)+⟨0,1⟩ = ⟨p,q+1⟩ := by ext <;> simp
    have d : (⟨p,q⟩ : GaussianInt)-⟨0,1⟩ = ⟨p,q-1⟩ := by ext <;> simp
    rw [FourNeighborLaplacian, a, b, c, d, h0, h1, h2, h3, h4]
    linarith only [formalLap F hscale p q]

end ApollonianSuperharmonic

end
