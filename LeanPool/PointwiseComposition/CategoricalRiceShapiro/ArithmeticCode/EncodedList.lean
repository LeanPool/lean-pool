/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Pairing
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Recursion

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Codes acting on an encoded list

A list of natural numbers is represented by its `Encodable` code, in which the
empty list is `0` and a cons cell is the successor of a Cantor pair of head and
tail.  `codeListHead?` and `codeListTail` invert that representation, and
`codeListDrop` iterates the tail by primitive recursion, so that
`codeListGet?` reads the entry at an index as an encoded `Option`.  `codeListLength`
minimizes the number of entries that must be dropped to reach the empty list, and
`codeOptionBind` is the bind of the encoded option monad.

Only the code constructions are given here.  The standard computation theorems
over the natural numbers are not part of this migration.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

/-- The head of an encoded list, as an encoded `Option`. -/
def codeListHeadOptional {n : ℕ} (d : Code n) : Code n :=
  codeIfPos d (codeSucc (codeUnpair₁ (codeSub d (codeConst 1)))) (Code.zero n)

/-- The tail of an encoded list. -/
def codeListTail {n : ℕ} (d : Code n) : Code n :=
  codeUnpair₂ (codeSub d (codeConst 1))

/-- Iterated tail of an encoded list, as a code in the index and the list. -/
def codeListDropCore : Code 2 :=
  codePrec (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3)))

/-- Drop `didx` entries from the encoded list `dlist`. -/
def codeListDrop {n : ℕ} (dlist didx : Code n) : Code n :=
  codeListDropCore.comp ![didx, dlist]

/-- The entry of the encoded list `dlist` at index `didx`, as an encoded
`Option`. -/
def codeListGetOptional {n : ℕ} (dlist didx : Code n) : Code n :=
  codeListHeadOptional (codeListDrop dlist didx)

/-- The length of an encoded list: the least index at which dropping that many
entries leaves the empty list. -/
def codeListLength {n : ℕ} (dlist : Code n) : Code n :=
  codeRfindPos (codeInv (codeListDrop (codeLift dlist) codeHead))

/-- Bind on an encoded `Option`: run `dk` on the payload when `dopt` encodes
`some`, and return the encoding of `none` otherwise. -/
def codeOptionBind {n : ℕ} (dopt : Code n) (dk : Code (n + 1)) : Code n :=
  codeIfPos dopt (codeBind (codeSub dopt (Code.one n)) dk) (Code.zero n)

/-- `codeListDrop` applies one fixed arity-two code to its two arguments.

A context that changes only those arguments is therefore a composition context,
to which `eval_comp_congr` applies.  The arity-two code is an implementation
detail and stays private; a proof reaches it by rewriting with this equation. -/
theorem codeListDrop_eq_comp {n : ℕ} (dlist didx : Code n) :
    codeListDrop dlist didx = codeListDropCore.comp ![didx, dlist] :=
  rfl

/-!
### One-layer view of an encoded list

The pinned encoding of `List ℕ` satisfies `encode [] = 0` and
`encode (x :: xs) = Nat.pair x (encode xs) + 1`.  The two constructors below
name that layer as codes; no arithmetic property of the encoding is asserted
here. -/

/-- The encoded empty list. -/
def codeListNil {n : ℕ} : Code n :=
  Code.zero n

/-- The encoded list with head `dx` and tail `dt`. -/
def codeListCons {n : ℕ} (dx dt : Code n) : Code n :=
  codeSucc (codePair dx dt)

/-- The recursion that rebuilds an encoded list with one entry appended: at
recursion argument `i` the entry at index `length - (i + 1)` is consed onto the
list built so far, starting from the singleton `[dx]`. -/
def codeListSnocCore {r : ℕ} (dlist dx : Code r) : Code (r + 1) :=
  codePrec (codeListCons dx (codeListNil (n := r)))
    (codeListCons
      (codeSub
        (codeListGetOptional (codeLift (codeLift dlist))
          (codeSub (codeListLength (codeLift (codeLift dlist)))
            (codeSucc (Code.proj (0 : Fin (r + 2))))))
        (codeConst 1))
      (Code.proj (1 : Fin (r + 2))))

/-- Append `dx` to the end of the encoded list `dlist`. -/
def codeListSnoc {r : ℕ} (dlist dx : Code r) : Code r :=
  codeBind (codeListLength dlist) (codeListSnocCore dlist dx)

/-- `codeListSnoc` binds the length of its list argument as the recursion
argument of one fixed arity-`r + 1` code.

The recursion is an implementation detail and stays private; a proof reaches it
by rewriting with this equation. -/
theorem codeListSnoc_eq_bind {r : ℕ} (dlist dx : Code r) :
    codeListSnoc dlist dx =
      codeBind (codeListLength dlist)
        (codePrec (codeListCons dx (codeListNil (n := r)))
          (codeListCons
            (codeSub
              (codeListGetOptional (codeLift (codeLift dlist))
                (codeSub (codeListLength (codeLift (codeLift dlist)))
                  (codeSucc (Code.proj (0 : Fin (r + 2))))))
              (codeConst 1))
            (Code.proj (1 : Fin (r + 2))))) :=
  rfl

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
