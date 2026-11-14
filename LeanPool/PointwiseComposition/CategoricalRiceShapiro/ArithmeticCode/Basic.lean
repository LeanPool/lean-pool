/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Arithmetic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Total arithmetic codes and their standard computations

`Computes c f` says that the partial-recursive code `c` realizes the total
function `f` over the natural numbers.  This module collects the constructors
used throughout the development -- projection, zero, one, addition,
multiplication, equality, strict order and composition -- together with the
derived total constructors built from them, and records the standard
computation theorem for each.

These are statements about the natural numbers.  Arbitrary-model evaluation is
the subject of `CategoricalRiceShapiro.ArithmeticCode.Evaluation`.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

/-- `c` realizes the total function `f`. -/
def Computes {n : ℕ} (c : Code n) (f : List.Vector ℕ n → ℕ) : Prop :=
  Code.eval c (fun v => (f v : Part ℕ))

theorem eval_of_eq {n : ℕ} {c : Code n} {f g : List.Vector ℕ n →. ℕ} (h : Code.eval c f)
    (e : f = g) : Code.eval c g :=
  e ▸ h

theorem Computes.of_eq {n : ℕ} {c : Code n} {f g : List.Vector ℕ n → ℕ} (h : Computes c f)
    (e : ∀ v, f v = g v) : Computes c g :=
  by
  refine eval_of_eq h ?_
  funext v
  rw [e v]

theorem computes_zero {n : ℕ} : Computes (Code.zero n) (fun _ => 0) :=
  Code.eval.zero

theorem computes_one {n : ℕ} : Computes (Code.one n) (fun _ => 1) :=
  Code.eval.one

theorem computes_add {n : ℕ} (i j : Fin n) :
    Computes (Code.add i j) (fun v => v.get i + v.get j) :=
  Code.eval.add i j

theorem computes_mul {n : ℕ} (i j : Fin n) :
    Computes (Code.mul i j) (fun v => v.get i * v.get j) :=
  Code.eval.mul i j

theorem computes_proj {n : ℕ} (i : Fin n) : Computes (Code.proj i) (fun v => v.get i) :=
  Code.eval.proj i

theorem computes_equal {n : ℕ} (i j : Fin n) :
    Computes (Code.equal i j) (fun v => isEqNat (v.get i) (v.get j)) :=
  Code.eval.equal i j

theorem computes_lt {n : ℕ} (i j : Fin n) :
    Computes (Code.lt i j) (fun v => isLtNat (v.get i) (v.get j)) :=
  Code.eval.lt i j

/-- Generic composition at the total-function layer. -/
theorem computes_comp {m k : ℕ} {c : Code k} {d : Fin k → Code m} {f : List.Vector ℕ k → ℕ}
    {g : Fin k → List.Vector ℕ m → ℕ} (hc : Computes c f) (hd : ∀ i, Computes (d i) (g i)) :
    Computes (c.comp d) (fun v => f (List.Vector.ofFn fun i => g i v)) :=
  by
  have h :=
    Code.eval.comp c d (fun v => (f v : Part ℕ)) (fun i v => ((g i v : ℕ) : Part ℕ)) hc hd
  refine eval_of_eq h ?_
  funext v
  simp

/-!
### Arity-specific composition -/

theorem computes_comp₁ {n : ℕ} {c : Code 1} {d : Code n} {f : ℕ → ℕ} {g : List.Vector ℕ n → ℕ}
    (hc : Computes c (fun w => f (w.get 0))) (hd : Computes d g) :
    Computes (c.comp ![d]) (fun v => f (g v)) :=
  by
  refine (computes_comp (g := ![g]) hc ?_).of_eq ?_
  · intro i;
    match i with
    | ⟨0, _⟩ => exact hd
  · intro v; simp

theorem computes_comp₂ {n : ℕ} {c : Code 2} {d₀ d₁ : Code n} {f : ℕ → ℕ → ℕ}
    {g₀ g₁ : List.Vector ℕ n → ℕ} (hc : Computes c (fun w => f (w.get 0) (w.get 1)))
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (c.comp ![d₀, d₁]) (fun v => f (g₀ v) (g₁ v)) :=
  by
  refine (computes_comp (g := ![g₀, g₁]) hc ?_).of_eq ?_
  · intro i
    match i with
    | ⟨0, _⟩ => exact h₀
    | ⟨1, _⟩ => exact h₁
  · intro v; simp [List.Vector.get_one]

/-!
### Derived total functions -/

/-- The code Succ construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeSucc {n : ℕ} (d : Code n) : Code n :=
  (Code.add (0 : Fin 2) (1 : Fin 2)).comp ![d, Code.one n]

theorem computes_codeSucc {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ} (hd : Computes d g) :
    Computes (codeSucc d) (fun v => g v + 1) :=
  computes_comp₂ (f := fun a b => a + b) (computes_add 0 1) hd computes_one

/-- The code Const construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeConst {n : ℕ} : ℕ → Code n
  | 0 => Code.zero n
  | m + 1 => codeSucc (codeConst m)

theorem computes_codeConst {n : ℕ} : ∀ m : ℕ, Computes (codeConst (n := n) m) (fun _ => m)
  | 0 => computes_zero
  | m + 1 => (computes_codeSucc (computes_codeConst m)).of_eq (fun _ => rfl)

/-- The code Inv construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeInv {n : ℕ} (d : Code n) : Code n :=
  (Code.equal (0 : Fin 2) (1 : Fin 2)).comp ![d, Code.zero n]

theorem computes_codeInv {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ} (hd : Computes d g) :
    Computes (codeInv d) (fun v => Nat.inv (g v)) :=
  (computes_comp₂ (f := fun a b => isEqNat a b) (computes_equal 0 1) hd computes_zero).of_eq
    (fun v => by simp [Nat.inv, isEqNat])

/-- The code Pos construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codePos {n : ℕ} (d : Code n) : Code n :=
  (Code.lt (0 : Fin 2) (1 : Fin 2)).comp ![Code.zero n, d]

theorem computes_codePos {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ} (hd : Computes d g) :
    Computes (codePos d) (fun v => Nat.pos (g v)) :=
  (computes_comp₂ (f := fun a b => isLtNat a b) (computes_lt 0 1) computes_zero hd).of_eq
    (fun v => by simp [Nat.pos, isLtNat])

/-!
### Boolean combinators -/

/-- The code And construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeAnd {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.lt (0 : Fin 2) (1 : Fin 2)).comp
    ![Code.zero n, (Code.mul (0 : Fin 2) (1 : Fin 2)).comp ![d₀, d₁]]

theorem computes_codeAnd {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeAnd d₀ d₁) (fun v => Nat.and (g₀ v) (g₁ v)) :=
  (computes_comp₂ (f := fun a b => isLtNat a b) (computes_lt 0 1) computes_zero
        (computes_comp₂ (f := fun a b => a * b) (computes_mul 0 1) h₀ h₁)).of_eq
    (fun v => by simp [Nat.and, isLtNat])

/-- The code Or construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeOr {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.lt (0 : Fin 2) (1 : Fin 2)).comp
    ![Code.zero n, (Code.add (0 : Fin 2) (1 : Fin 2)).comp ![d₀, d₁]]

theorem computes_codeOr {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeOr d₀ d₁) (fun v => Nat.or (g₀ v) (g₁ v)) :=
  (computes_comp₂ (f := fun a b => isLtNat a b) (computes_lt 0 1) computes_zero
        (computes_comp₂ (f := fun a b => a + b) (computes_add 0 1) h₀ h₁)).of_eq
    (fun v => by simp [Nat.or, isLtNat])

/-- The code Eq construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeEq {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.equal (0 : Fin 2) (1 : Fin 2)).comp ![d₀, d₁]

theorem computes_codeEq {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeEq d₀ d₁) (fun v => isEqNat (g₀ v) (g₁ v)) :=
  computes_comp₂ (f := fun a b => isEqNat a b) (computes_equal 0 1) h₀ h₁

/-- The code Lt construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeLt {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.lt (0 : Fin 2) (1 : Fin 2)).comp ![d₀, d₁]

theorem computes_codeLt {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeLt d₀ d₁) (fun v => isLtNat (g₀ v) (g₁ v)) :=
  computes_comp₂ (f := fun a b => isLtNat a b) (computes_lt 0 1) h₀ h₁

/-- The code Add construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeAdd {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.add (0 : Fin 2) (1 : Fin 2)).comp ![d₀, d₁]

theorem computes_codeAdd {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeAdd d₀ d₁) (fun v => g₀ v + g₁ v) :=
  computes_comp₂ (f := fun a b => a + b) (computes_add 0 1) h₀ h₁

/-- The code Mul construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeMul {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.mul (0 : Fin 2) (1 : Fin 2)).comp ![d₀, d₁]

theorem computes_codeMul {n : ℕ} {d₀ d₁ : Code n} {g₀ g₁ : List.Vector ℕ n → ℕ}
    (h₀ : Computes d₀ g₀) (h₁ : Computes d₁ g₁) :
    Computes (codeMul d₀ d₁) (fun v => g₀ v * g₁ v) :=
  computes_comp₂ (f := fun a b => a * b) (computes_mul 0 1) h₀ h₁

/-!
### Lifting a code under an extra search variable -/

/-- The code Lift construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeLift {n : ℕ} (d : Code n) : Code (n + 1) :=
  d.comp (fun i => Code.proj i.succ)

theorem computes_codeLift {n : ℕ} {d : Code n} {g : List.Vector ℕ n → ℕ} (hd : Computes d g) :
    Computes (codeLift d) (fun w => g w.tail) :=
  by
  refine
    (computes_comp (g := fun i w => w.get i.succ) hd (fun i => computes_proj i.succ)).of_eq ?_
  intro w
  congr 1
  refine List.Vector.ext ?_
  intro i
  simp only [List.Vector.get_ofFn]
  exact (List.Vector.get_tail_succ w i).symm

/-- The code Head construction in `CategoricalRiceShapiro.ArithmeticCode`. -/
def codeHead {n : ℕ} : Code (n + 1) :=
  Code.proj 0

theorem computes_codeHead {n : ℕ} : Computes (codeHead (n := n)) (fun w => w.head) :=
  (computes_proj (0 : Fin (n + 1))).of_eq (fun w => by simp)

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
