/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Int.Interval

-- [TABLET NODE: P3221T2IntegralSquareFilling]

/-!
# P3221T2IntegralSquareFilling

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3221T2IntegralSquareFilling
    (H V : GaussianInt →₀ ℤ)
    (hdiv : ∀ x, H x - H (x - 1) + V x - V (x - ⟨0, 1⟩) = 0) :
    (∀ m : ℤ, ∑ x ∈ H.support.filter (fun x => x.re = m), H x = 0) ∧
    ∃ c : GaussianInt →₀ ℤ,
      (∀ x, c x = ∑ y ∈ H.support.filter
        (fun y => y.re = x.re ∧ y.im ≤ x.im), H y) ∧
      (∀ x, H x = c x - c (x - ⟨0, 1⟩)) ∧
      (∀ x, V x = c (x - 1) - c x) := by
-- BODY
  classical
  let C : GaussianInt → ℤ := fun x =>
    ∑ y ∈ H.support.filter (fun y => y.re = x.re ∧ y.im ≤ x.im), H y
  let A : ℤ → ℤ := fun m => ∑ y ∈ H.support.filter (fun y => y.re = m), H y
  have hCdiff (x : GaussianInt) : C x - C (x - ⟨0, 1⟩) = H x := by
    have hsum : C x = C (x - ⟨0, 1⟩) +
        ∑ y ∈ H.support, if y = x then H y else 0 := by
      simp only [C, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases he : y = x
      · subst y
        simp [sub_eq_add_neg]
      · have hcoord : ¬(y.re = x.re ∧ y.im = x.im) := by
          intro h
          exact he (Zsqrtd.ext h.1 h.2)
        have hpred : (y.re = x.re ∧ y.im ≤ x.im) ↔
            (y.re = (x - ⟨0, 1⟩).re ∧ y.im ≤ (x - ⟨0, 1⟩).im) := by
          simp only [sub_eq_add_neg, Zsqrtd.re_add, Zsqrtd.re_neg,
            Zsqrtd.im_add, Zsqrtd.im_neg]
          omega
        simp only [ite_eq_right he, add_zero, hpred]
    have hsingle : (∑ y ∈ H.support, if y = x then H y else 0) = H x := by
      by_cases hx : x ∈ H.support
      · simp [hx]
      · simp [hx, Finsupp.notMem_support_iff.mp hx]
    rw [hsingle] at hsum
    omega
  let S := H.support ∪ V.support
  obtain ⟨r, hr⟩ := (S.finite_toSet.image (fun x : GaussianInt => x.im)).bddBelow
  obtain ⟨s, hs⟩ := (S.finite_toSet.image (fun x : GaussianInt => x.im)).bddAbove
  have hHbounds (x : GaussianInt) (hx : x ∈ H.support) : r ≤ x.im ∧ x.im ≤ s := by
    have hmem : x.im ∈ (fun x : GaussianInt => x.im) '' (S : Set GaussianInt) :=
      ⟨x, Finset.mem_union_left _ hx, rfl⟩
    exact ⟨hr hmem, hs hmem⟩
  have hVbounds (x : GaussianInt) (hx : x ∈ V.support) : r ≤ x.im ∧ x.im ≤ s := by
    have hmem : x.im ∈ (fun x : GaussianInt => x.im) '' (S : Set GaussianInt) :=
      ⟨x, Finset.mem_union_right _ hx, rfl⟩
    exact ⟨hr hmem, hs hmem⟩
  have hClower (x : GaussianInt) (hx : x.im < r) : C x = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    obtain ⟨hyH, hyre, hyim⟩ := Finset.mem_filter.mp hy
    have := (hHbounds y hyH).1
    omega
  have hCupper (x : GaussianInt) (hx : s ≤ x.im) : C x = A x.re := by
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro y hy
      have := (hHbounds y hy).2
      omega
    · intro y hy
      rfl
  have hVoutside (x : GaussianInt) (hx : x.im < r ∨ s < x.im) : V x = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have := hVbounds x hmem
    omega
  have hshiftI (m n : ℤ) : (⟨m, n⟩ : GaussianInt) - ⟨0, 1⟩ = ⟨m, n - 1⟩ := by
    ext <;> simp [sub_eq_add_neg]
  have hshiftR (m n : ℤ) : (⟨m, n⟩ : GaussianInt) - 1 = ⟨m - 1, n⟩ := by
    ext <;> simp [sub_eq_add_neg]
  have hCstep (m n : ℤ) : C ⟨m, n + 1⟩ - C ⟨m, n⟩ = H ⟨m, n + 1⟩ := by
    simpa only [hshiftI, add_sub_cancel_right] using hCdiff ⟨m, n + 1⟩
  -- The divergence equation is the vertical difference of E; sum it from r to n.
  let E : ℤ → ℤ → ℤ := fun m n => C ⟨m, n⟩ - C ⟨m - 1, n⟩ + V ⟨m, n⟩
  have hEstep (m n : ℤ) : E m (n + 1) - E m n = 0 := by
    have hd := hdiv ⟨m, n + 1⟩
    rw [hshiftR, hshiftI, add_sub_cancel_right] at hd
    have hc := hCstep m n
    have hc' := hCstep (m - 1) n
    dsimp only [E]
    omega
  have hElower (m n : ℤ) (hn : n < r) : E m n = 0 := by
    dsimp only [E]
    rw [hClower _ hn, hClower _ hn, hVoutside _ (Or.inl hn)]
    omega
  have hEzero (m n : ℤ) : E m n = 0 := by
    by_cases hn : n < r
    · exact hElower m n hn
    · let N := (n - (r - 1)).toNat
      have hN : r - 1 + (N : ℤ) = n := by omega
      have htel := Finset.sum_range_sub (fun k : ℕ => E m (r - 1 + (k : ℤ))) N
      have hzero : (∑ k ∈ Finset.range N,
          (E m (r - 1 + ((k + 1 : ℕ) : ℤ)) - E m (r - 1 + (k : ℤ)))) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          hEstep m (r - 1 + (k : ℤ))
      rw [hzero] at htel
      have hbase := hElower m (r - 1) (by omega)
      simpa only [hN, Nat.cast_zero, add_zero, hbase, sub_zero] using htel.symm
  -- At height s + 1 the same telescoping sum gives equality of column totals.
  have hAstep (m : ℤ) : A m = A (m - 1) := by
    have he := hEzero m (s + 1)
    dsimp only [E] at he
    rw [hCupper _ (by change s ≤ s + 1; omega),
      hCupper _ (by change s ≤ s + 1; omega),
      hVoutside _ (Or.inr (by change s < s + 1; omega))] at he
    change A m - A (m - 1) + 0 = 0 at he
    omega
  obtain ⟨a, ha⟩ := (H.support.finite_toSet.image (fun x : GaussianInt => x.re)).bddBelow
  have hAbase : A (a - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    obtain ⟨hyH, hyre⟩ := Finset.mem_filter.mp hy
    change y.re = a - 1 at hyre
    have hle : a ≤ y.re := ha ⟨y, hyH, rfl⟩
    omega
  have hAzero (m : ℤ) : A m = 0 := by
    refine Int.inductionOn' m (a - 1) hAbase ?_ ?_
    · intro k hk ih
      have := hAstep (k + 1)
      rw [add_sub_cancel_right] at this
      exact this.trans ih
    · intro k hk ih
      exact (hAstep k).symm.trans ih
  -- Only supported columns and rows r through s - 1 can support C.
  let T : Finset GaussianInt :=
    ((H.support.image (fun x => x.re)).product (Finset.Icc r (s - 1))).image
      (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))
  have hCfinite (x : GaussianInt) (hx : C x ≠ 0) : x ∈ T := by
    have hre : x.re ∈ H.support.image (fun y => y.re) := by
      by_contra hn
      apply hx
      apply Finset.sum_eq_zero
      intro y hy
      obtain ⟨hyH, hyre, hyim⟩ := Finset.mem_filter.mp hy
      exact False.elim (hn (Finset.mem_image.mpr ⟨y, hyH, hyre⟩))
    have hlo : r ≤ x.im := by
      by_contra hn
      exact hx (hClower x (by omega))
    have hhi : x.im ≤ s - 1 := by
      by_contra hn
      have hcx := hCupper x (by omega)
      rw [hAzero] at hcx
      exact hx hcx
    apply Finset.mem_image.mpr
    refine ⟨(x.re, x.im), Finset.mem_product.mpr ⟨hre, ?_⟩, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
    · cases x
      rfl
  let c : GaussianInt →₀ ℤ := Finsupp.onFinset T C hCfinite
  have hc (x : GaussianInt) : c x = C x := Finsupp.onFinset_apply
  refine ⟨hAzero, c, hc, ?_, ?_⟩
  · intro x
    rw [hc, hc]
    exact (hCdiff x).symm
  · intro x
    rw [hc, hc]
    rcases x with ⟨m, n⟩
    rw [hshiftR]
    have he := hEzero m n
    dsimp only [E] at he
    omega

end ApollonianSuperharmonic

end
