/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import LeanPool.LatinQuarter.Cyclic
public import LeanPool.LatinQuarter.Budget

/-!
# Counting the two corner triangles
-/

@[expose] public section

namespace LatinQuarter

/-- Fold the two corner triangles into a rectangle with `n/2` rows and
`n-n/2` columns. Their images lie on opposite sides of its anti-diagonal. -/
theorem cornerSet_card_le (n : ℕ) : (cornerSet n).card ≤ n * n / 4 := by
  classical
  have hk : n / 2 ≤ n := by omega
  have hh : n - n / 2 ≤ n / 2 + 1 := by omega
  have hkh : n / 2 ≤ n - n / 2 := by omega
  let f : {p : Cell n // p ∈ cornerSet n} → Fin (n / 2) × Fin (n - n / 2) :=
    fun p => if hp : p.val.1.val + p.val.2.val < n / 2 then
      (⟨p.val.1.val, by omega⟩, ⟨p.val.2.val, by omega⟩)
    else
      (⟨p.val.1.val - (n - n / 2), by
        have hr := p.val.1.isLt
        have hc := p.val.2.isLt
        have hm := (mem_cornerSet _ _).mp p.property
        omega⟩,
       ⟨p.val.2.val - n / 2, by
        have hr := p.val.1.isLt
        have hc := p.val.2.isLt
        have hm := (mem_cornerSet _ _).mp p.property
        omega⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨pr, pc⟩, hp⟩ ⟨⟨qr, qc⟩, hq⟩ he
    have hp' := (mem_cornerSet pr pc).mp hp
    have hq' := (mem_cornerSet qr qc).mp hq
    have hpr := pr.isLt
    have hpc := pc.isLt
    have hqr := qr.isLt
    have hqc := qc.isLt
    dsimp [f] at he
    split_ifs at he with hp0 hq0 hq0
    all_goals
      have he1 := congrArg (fun x : Fin (n / 2) × Fin (n - n / 2) => x.1.val) he
      have he2 := congrArg (fun x : Fin (n / 2) × Fin (n - n / 2) => x.2.val) he
      simp only at he1 he2
      apply Subtype.ext
      change (pr, pc) = (qr, qc)
      apply Prod.ext <;> apply Fin.ext <;> dsimp only at * <;> omega
  have hc := Fintype.card_le_of_injective f hf
  rw [quarter_eq]
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hc

end LatinQuarter
