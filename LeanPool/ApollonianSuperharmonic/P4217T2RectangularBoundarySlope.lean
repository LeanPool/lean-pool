/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope

-- [TABLET NODE: P4217T2RectangularBoundarySlope]

/-!
# P4217T2RectangularBoundarySlope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4217T2RectangularBoundarySlope (h : PartialOdometer)
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) (a b : Int)
    (hdom : (h.domain : Set GaussianInt) =
      {x | 0 ≤ x.re ∧ x.re ≤ (m : Int) ∧ 0 ≤ x.im ∧ x.im ≤ (n : Int)})
    (hleft : ∀ y : Int, 0 ≤ y → y ≤ n → h.value ⟨0, y⟩ = 0)
    (hright : ∀ y : Int, 0 ≤ y → y ≤ n → h.value ⟨(m : Int), y⟩ = a * y)
    (hbottom : ∀ x : Int, 0 ≤ x → x ≤ m → h.value ⟨x, 0⟩ = 0)
    (htop : ∀ x : Int, 0 ≤ x → x ≤ m → h.value ⟨x, (n : Int)⟩ = b * x) :
    PartialOdometerSlope h =
      some ((a : Real) * n / (2 * m), (b : Real) * m / (2 * n)) := by
-- BODY
  classical
  let point (p : Nat × Nat) : GaussianInt := ⟨(p.1 : Int), (p.2 : Int)⟩
  let box := (Finset.range m).product (Finset.range n)
  have inj : Function.Injective point := by
    intro p q hpq
    have hr := congrArg (fun z : GaussianInt => z.re) hpq
    have hi := congrArg (fun z : GaussianInt => z.im) hpq
    apply Prod.ext <;> dsimp [point] at * <;> omega
  have mem (x : GaussianInt) : x ∈ h.domain ↔
      0 ≤ x.re ∧ x.re ≤ (m : Int) ∧ 0 ≤ x.im ∧ x.im ≤ (n : Int) := by
    exact Set.ext_iff.mp hdom x
  have squares : PartialOdometerSquares h = box.image point := by
    ext x
    have corners : x ∈ PartialOdometerSquares h ↔
        0 ≤ x.re ∧ x.re < (m : Int) ∧ 0 ≤ x.im ∧ x.im < (n : Int) := by
      simp only [PartialOdometerSquares, Finset.mem_filter, mem,
        Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
      omega
    rw [corners]
    constructor
    · rintro ⟨hr, hrm, hi, hin⟩
      refine Finset.mem_image.mpr ⟨(x.re.toNat, x.im.toNat), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩
      · apply Zsqrtd.ext <;> simp [point, hr, hi]
    · intro hx
      obtain ⟨⟨r, t⟩, hrt, rfl⟩ := Finset.mem_image.mp hx
      have hr := Finset.mem_range.mp (Finset.mem_product.mp hrt).1
      have ht := Finset.mem_range.mp (Finset.mem_product.mp hrt).2
      dsimp [point]
      omega
  have card : (PartialOdometerSquares h).card = m * n := by
    rw [squares, Finset.card_image_of_injective _ inj]
    simp [box]
  have nonempty : (PartialOdometerSquares h).Nonempty := by
    rw [← Finset.card_pos, card]
    exact Nat.mul_pos hm hn
  let F (r t : Nat) : Real := h.value ⟨(r : Int), (t : Int)⟩
  have odd (k : Nat) : (∑ j ∈ Finset.range k, (2 * (j : Real) + 1)) = (k : Real)^2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have horizontal :
      (∑ r ∈ Finset.range m, ∑ t ∈ Finset.range n,
        (F (r + 1) t - F r t + F (r + 1) (t + 1) - F r (t + 1))) =
        (a : Real) * (n : Real)^2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ t ∈ Finset.range n, (a : Real) * (2 * (t : Real) + 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := Finset.mem_range.mp ht
        have hrow : (∑ r ∈ Finset.range m,
            (F (r + 1) t - F r t + F (r + 1) (t + 1) - F r (t + 1))) =
            (F m t - F 0 t) + (F m (t + 1) - F 0 (t + 1)) := by
          calc
            _ = (∑ r ∈ Finset.range m, (F (r + 1) t - F r t)) +
                ∑ r ∈ Finset.range m, (F (r + 1) (t + 1) - F r (t + 1)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro r hr
              ring
            _ = _ := by
              rw [Finset.sum_range_sub (fun r => F r t),
                Finset.sum_range_sub (fun r => F r (t + 1))]
        rw [hrow]
        dsimp [F]
        rw [hleft _ (by omega) (by omega), hleft _ (by omega) (by omega),
          hright _ (by omega) (by omega), hright _ (by omega) (by omega)]
        push_cast
        ring
      _ = _ := by rw [← Finset.mul_sum, odd]
  have vertical :
      (∑ r ∈ Finset.range m, ∑ t ∈ Finset.range n,
        (F r (t + 1) - F r t + F (r + 1) (t + 1) - F (r + 1) t)) =
        (b : Real) * (m : Real)^2 := by
    calc
      _ = ∑ r ∈ Finset.range m, (b : Real) * (2 * (r : Real) + 1) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hr' := Finset.mem_range.mp hr
        have hcol : (∑ t ∈ Finset.range n,
            (F r (t + 1) - F r t + F (r + 1) (t + 1) - F (r + 1) t)) =
            (F r n - F r 0) + (F (r + 1) n - F (r + 1) 0) := by
          calc
            _ = (∑ t ∈ Finset.range n, (F r (t + 1) - F r t)) +
                ∑ t ∈ Finset.range n, (F (r + 1) (t + 1) - F (r + 1) t) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro t ht
              ring
            _ = _ := by
              rw [Finset.sum_range_sub (fun t => F r t),
                Finset.sum_range_sub (fun t => F (r + 1) t)]
        rw [hcol]
        dsimp [F]
        rw [hbottom _ (by omega) (by omega), hbottom _ (by omega) (by omega),
          htop _ (by omega) (by omega), htop _ (by omega) (by omega)]
        push_cast
        ring
      _ = _ := by rw [← Finset.mul_sum, odd]
  have hsums (f : GaussianInt → Real) :
      (∑ x ∈ PartialOdometerSquares h, f x) =
        ∑ r ∈ Finset.range m, ∑ t ∈ Finset.range n, f ⟨(r : Int), (t : Int)⟩ := by
    rw [squares, Finset.sum_image (fun _ _ _ _ he => inj he)]
    exact Finset.sum_product _ _ _
  unfold PartialOdometerSlope
  rw [ite_eq_left nonempty, card, hsums, hsums]
  have addone (r t : Int) : (⟨r, t⟩ : GaussianInt) + 1 = ⟨r + 1, t⟩ := by
    apply Zsqrtd.ext <;> simp
  have hhor : (∑ r ∈ Finset.range m, ∑ t ∈ Finset.range n,
      ((h.value (⟨(r : Int), (t : Int)⟩ + 1) - h.value ⟨(r : Int), (t : Int)⟩ +
        h.value (⟨(r : Int), (t : Int)⟩ + 1 + ⟨0, 1⟩) -
        h.value (⟨(r : Int), (t : Int)⟩ + ⟨0, 1⟩) : Int) : Real)) =
      (a : Real) * (n : Real)^2 := by
    simpa [F, Nat.cast_add, Int.cast_sub, Int.cast_add, addone] using horizontal
  have hver : (∑ r ∈ Finset.range m, ∑ t ∈ Finset.range n,
      ((h.value (⟨(r : Int), (t : Int)⟩ + ⟨0, 1⟩) - h.value ⟨(r : Int), (t : Int)⟩ +
        h.value (⟨(r : Int), (t : Int)⟩ + 1 + ⟨0, 1⟩) -
        h.value (⟨(r : Int), (t : Int)⟩ + 1) : Int) : Real)) =
      (b : Real) * (m : Real)^2 := by
    simpa [F, Nat.cast_add, Int.cast_sub, Int.cast_add, addone] using vertical
  rw [hhor, hver]
  have hm' : (m : Real) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  congr 2 <;> push_cast <;> field_simp

end ApollonianSuperharmonic

end
