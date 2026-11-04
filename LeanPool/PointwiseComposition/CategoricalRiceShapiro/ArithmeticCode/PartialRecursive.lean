/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Recursion

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Decoding a partial-recursive index

Mathlib's `Nat.Partrec.Code` encoding sends the four base constructors to `0`–`3`
and encodes a compound code as `2 * (2 * payload + b₀) + b₁ + 4`, where the two
bits `b₀` and `b₁` name the constructor: `4` pairing, `5` composition, `6`
primitive recursion, `7` minimization.

`codePartrecTag` recovers the constructor number and `codePartrecPayload` the
payload, whose Cantor components `codePartrecPayload₁` and `codePartrecPayload₂`
are the two subcodes of a binary constructor.  The bit extraction needs parity
and halving, which are defined here from remainder and primitive recursion.

Each construction is accompanied by the theorem that it realizes the intended
function over the natural numbers.  Those `Computes` theorems are the input of
the standard-model bridge, which turns a computation over `ℕ` into evaluation at
standard numerals in an arbitrary model.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

/-!
### The numeric view

The functions the codes below realize.  The constructor numbers are `0 zero`,
`1 succ`, `2 left`, `3 right`, `4 pair`, `5 comp`, `6 prec`, `7 rfind'`.  For
`q = r + 4` the payload is `r.div2.div2`; a binary constructor reads its Cantor
components and minimization reads the payload itself. -/

/-- The constructor number of a partial-recursive index. -/
def partrecCodeTag (q : ℕ) : ℕ :=
  if q < 4 then q
  else
    let r := q - 4
    4 + 2 * r.bodd.toNat + r.div2.bodd.toNat

/-- The payload of a compound partial-recursive index. -/
def partrecCodePayload (q : ℕ) : ℕ :=
  (q - 4).div2.div2

/-- The first subcode of a binary partial-recursive constructor. -/
def partrecCodePayload₁ (q : ℕ) : ℕ :=
  (partrecCodePayload q).unpair.1

/-- The second subcode of a binary partial-recursive constructor. -/
def partrecCodePayload₂ (q : ℕ) : ℕ :=
  (partrecCodePayload q).unpair.2

/-!
### The realizing codes -/

/-- The parity bit of `d`. -/
def codeBodd {n : ℕ} (d : Code n) : Code n :=
  codeRem d (codeConst 2)

/-- Halving, as a unary code, by primitive recursion on the argument. -/
def codeDiv2Unary : Code 1 :=
  codePrec (Code.zero 0)
    (codeIfPos (codeBodd (Code.proj 0)) (codeSucc (Code.proj 1)) (Code.proj 1))

/-- Halving of `d`, rounding down. -/
def codeDiv2 {n : ℕ} (d : Code n) : Code n :=
  codeDiv2Unary.comp ![d]

/-- The constructor number of the partial-recursive index `d`: the index itself
below `4`, and otherwise `4` plus the two bits of `d - 4`. -/
def codePartrecTag {n : ℕ} (d : Code n) : Code n :=
  let r := codeSub d (codeConst 4)
  codeIfPos (codeLt d (codeConst 4)) d
    (codeAdd (codeAdd (codeConst 4) (codeMul (codeConst 2) (codeBodd r)))
      (codeBodd (codeDiv2 r)))

/-- The payload of a compound partial-recursive index. -/
def codePartrecPayload {n : ℕ} (d : Code n) : Code n :=
  codeDiv2 (codeDiv2 (codeSub d (codeConst 4)))

/-- The first subcode of a binary partial-recursive constructor. -/
def codePartrecPayload₁ {n : ℕ} (d : Code n) : Code n :=
  codeUnpair₁ (codePartrecPayload d)

/-- The second subcode of a binary partial-recursive constructor. -/
def codePartrecPayload₂ {n : ℕ} (d : Code n) : Code n :=
  codeUnpair₂ (codePartrecPayload d)

/-!
### Standard computations over the natural numbers -/

theorem computes_codeBodd {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ} (h : Computes d g) :
    Computes (codeBodd d) (fun v => (Nat.bodd (g v)).toNat) :=
  (computes_codeRem h (computes_codeConst 2)).of_eq (fun v => Nat.mod_two_of_bodd (g v))

theorem computes_codeDiv2Unary : Computes codeDiv2Unary (fun v => Nat.div2 v.head) :=
  by
  refine
    (computes_codePrec computes_zero
          (computes_codeIfPos (computes_codeBodd (computes_proj 0))
            (computes_codeSucc (computes_proj 1)) (computes_proj 1))).of_eq
      ?_
  intro v
  simp only [List.Vector.get_zero, List.Vector.get_one, List.Vector.head_cons,
    List.Vector.tail_cons]
  generalize v.head = m
  induction m with
  | zero => exact Nat.div2_zero.symm
  | succ y IH =>
    rw [Nat.div2_succ]
    cases hb : Nat.bodd y <;> simp [hb, IH]

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
