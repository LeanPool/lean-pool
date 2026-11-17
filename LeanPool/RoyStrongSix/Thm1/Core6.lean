/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import LeanPool.RoyStrongSix.Thm1.Core3
public import LeanPool.RoyStrongSix.Thm1.Core5
public import LeanPool.RoyStrongSix.Thm1.Growth

/-!
# The core of Theorem 1, part 6: the number of monomials

* `card_Mono_le`: `#Mono ≤ (L₀+1)^{d₀} (L₁+1)^{d₁}`.
* `card_Mono_ge`: `(A+1)^{d₀} (B+1)^{d₁} ≤ #Mono` when `d₀ A ≤ L₀`, `d₁ B ≤ L₁` (and `A ≤ L₀`, `B
≤ L₁`).
-/

@[expose] public section

namespace LeanPool

namespace StrongSix.Thm1

variable {d0 d1 : ℕ}

theorem card_Mono_le (L0 L1 : ℕ) :
    Fintype.card (Mono d0 d1 L0 L1) ≤ (L0 + 1) ^ d0 * (L1 + 1) ^ d1 := by
  unfold Mono
  refine (Fintype.card_subtype_le _).trans (le_of_eq ?_)
  simp [Fintype.card_prod]

theorem card_Mono_ge {L0 L1 A B : ℕ} (hA : d0 * A ≤ L0) (hB : d1 * B ≤ L1) (hAL : A ≤ L0)
    (hBL : B ≤ L1) : (A + 1) ^ d0 * (B + 1) ^ d1 ≤ Fintype.card (Mono d0 d1 L0 L1) := by
  classical
  let f : (Fin d0 → Fin (A + 1)) × (Fin d1 → Fin (B + 1)) → Mono d0 d1 L0 L1 := fun x =>
    ⟨(fun i => Fin.castLE (by omega) (x.1 i), fun j => Fin.castLE (by omega) (x.2 j)), by
      constructor
      · calc (∑ i, ((Fin.castLE (by omega) (x.1 i) : Fin (L0 + 1)) : ℕ)) ≤ ∑ _i : Fin d0, A :=
              Finset.sum_le_sum fun i _ => by
                simpa only [Fin.val_castLE] using Nat.lt_succ_iff.mp (x.1 i).2
          _ = d0 * A := by simp
          _ ≤ L0 := hA
      · calc (∑ j, ((Fin.castLE (by omega) (x.2 j) : Fin (L1 + 1)) : ℕ)) ≤ ∑ _j : Fin d1, B :=
              Finset.sum_le_sum fun j _ => by
                simpa only [Fin.val_castLE] using Nat.lt_succ_iff.mp (x.2 j).2
          _ = d1 * B := by simp
          _ ≤ L1 := hB⟩
  have hf : Function.Injective f := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    have h' := congrArg Subtype.val h
    simp only [f, Prod.mk.injEq] at h'
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · have := congrFun h'.1 i
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · have := congrFun h'.2 j
      exact Fin.ext (by simpa using congrArg Fin.val this)
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, Fintype.card_fun] using this

end StrongSix.Thm1

end LeanPool
