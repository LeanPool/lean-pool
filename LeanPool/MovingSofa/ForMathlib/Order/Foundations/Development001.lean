/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Tactic.Linarith

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Order.Infimum`.
* `ForMathlib.Order.IntervalPartition`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Order / Infimum
-/

@[expose] public section

open Set

/-- Uniformly close real functions have uniformly close infima on a nonempty set. -/
theorem abs_sInf_image_sub_sInf_image_le {ι : Type*} {s : Set ι}
    (hs : s.Nonempty) (f g : ι → ℝ) (hf : BddBelow (f '' s)) (hg : BddBelow (g '' s))
    {C : ℝ} (h : ∀ x ∈ s, |f x - g x| ≤ C) :
    |sInf (f '' s) - sInf (g '' s)| ≤ C := by
  have hfg : sInf (f '' s) - C ≤ sInf (g '' s) := by
    apply le_csInf (hs.image g)
    rintro _ ⟨x, hx, rfl⟩
    have hfx : sInf (f '' s) ≤ f x := csInf_le hf ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).2
    linarith
  have hgf : sInf (g '' s) - C ≤ sInf (f '' s) := by
    apply le_csInf (hs.image f)
    rintro _ ⟨x, hx, rfl⟩
    have hgx : sInf (g '' s) ≤ g x := csInf_le hg ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).1
    linarith
  rw [abs_le]
  constructor <;> linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Order / Interval Partition
-/

@[expose] public section

open Set

/-- Adjacent half-open intervals of a finite monotone sequence cover its endpoint interval. -/
theorem Monotone.iUnion_Ioc_fin {α : Type*} [LinearOrder α] {n : ℕ} (cuts : Fin (n + 1) → α)
    (hcuts : Monotone cuts) :
    (⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ)) = Ioc (cuts 0) (cuts (Fin.last n)) := by
  rw [← hcuts.biUnion_Ico_Ioc_map_succ 0 (Fin.last n)]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i.castSucc, ⟨Fin.zero_le _, i.castSucc_lt_last⟩, ?_⟩
    simpa only [Fin.orderSucc_castSucc] using hi
  · rintro ⟨i, hi, hx⟩
    have hn : i.val < n := hi.2
    refine ⟨⟨i, hn⟩, ?_⟩
    change x ∈ Ioc (cuts (⟨i, hn⟩ : Fin n).castSucc)
      (cuts (Order.succ (⟨i, hn⟩ : Fin n).castSucc)) at hx
    simpa only [Fin.orderSucc_castSucc] using hx

end

end
