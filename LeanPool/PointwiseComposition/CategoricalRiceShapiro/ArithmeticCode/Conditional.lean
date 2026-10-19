/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# An eager conditional and non-strict comparison

`codeIfPos df dg dh` is arithmetic, not lazy: it evaluates `dg` and `dh`
both, and selects one of them by multiplying with the characteristic values
`codePos df` and `codeInv df`.  `codeLe` is the disjunction of strict order
and equality.

Each construction is accompanied by the theorem that it realizes the intended
function over the natural numbers.  Those `Computes` theorems are the input of
the standard-model bridge, which turns a computation over `ℕ` into evaluation at
standard numerals in an arbitrary model.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

/-- `dg` when `df` is positive and `dh` otherwise, selected arithmetically.

Both branches are evaluated; the construction is a sum of products, not a
selected-branch semantics. -/
def codeIfPos {n : ℕ} (df dg dh : Code n) : Code n :=
  codeAdd (codeMul (codePos df) dg) (codeMul (codeInv df) dh)

/-- The characteristic value of `d₀ ≤ d₁`. -/
def codeLe {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeOr (codeLt d₀ d₁) (codeEq d₀ d₁)

/-!
### Standard computations over the natural numbers -/

theorem computes_codeIfPos {n : ℕ} {df dg dh : Code n} {f g h : List.Vector ℕ n → ℕ}
    (hf : Computes df f) (hg : Computes dg g) (hh : Computes dh h) :
    Computes (codeIfPos df dg dh) (fun v => if 0 < f v then g v else h v) :=
  (computes_codeAdd (computes_codeMul (computes_codePos hf) hg)
        (computes_codeMul (computes_codeInv hf) hh)).of_eq
    (fun v => by
      by_cases hz : f v = 0 <;> simp [hz, Nat.pos, Nat.inv, isLtNat, isEqNat, zero_lt_iff])

theorem computes_codeLe {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeLe d₀ d₁) (fun v => isLeNat (g₀ v) (g₁ v)) :=
  (computes_codeOr (computes_codeLt h₀ h₁) (computes_codeEq h₀ h₁)).of_eq
    (fun v => by
      by_cases h : g₀ v < g₁ v
      · simp [Nat.or, isLeNat, isLtNat, isEqNat, h, le_of_lt h]
      · by_cases h2 : g₀ v = g₁ v
        · simp [Nat.or, isLeNat, isLtNat, isEqNat, h2]
        · have : ¬g₀ v ≤ g₁ v := by omega
          simp [Nat.or, isLeNat, isLtNat, isEqNat, h, h2, this])

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
