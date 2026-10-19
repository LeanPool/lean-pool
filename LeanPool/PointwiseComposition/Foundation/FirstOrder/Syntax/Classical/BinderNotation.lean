/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Syntax.Classical.BinderSemantics

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

open _root_.Lean Lean Elab PrettyPrinter Delaborator SubExpr

namespace Lean
namespace TSyntax

open _root_.Lean.TSyntax

/-- The fresh Ident construction in `Lean.TSyntax`. -/
meta def freshIdent [Monad m] [MonadQuotation m] : m (TSyntax `ident) := do
  let name ← Term.mkFreshBinderName
  return ⟨mkIdent name⟩

end TSyntax
end Lean

namespace FFL
namespace FirstOrder

namespace BinderNotation

/-- The fin Succ Itr construction in `FFL.FirstOrder.BinderNotation`. -/
@[simp]
abbrev finSuccItr {n} (i : Fin n) : (m : ℕ) → Fin (n + m)
  | 0 => i
  | m + 1 => (finSuccItr i m).succ

open Semiterm Semiformula

/-!
### (Literal) Notation for terms -/

/-- The first order term construction in `Lean.Parser.Category`. -/
declare_syntax_cat firstOrderTerm

/-- The quote type construction in `Lean.Parser.Category.first_order`. -/
declare_syntax_cat firstOrder.quoteType

/-- The quote type Lit construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "lit" : firstOrder.quoteType

/-- The quote type Faf construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "faf" : firstOrder.quoteType

/-- The «term Quoteterm( )[ | | ]» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "quoteterm(" firstOrder.quoteType ")[" ident* " | " ident* " | " firstOrderTerm:0 "]" :
  term

/-- The «first order term( )» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "(" firstOrderTerm ")" : firstOrderTerm

/-- The first order term construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max ident : firstOrderTerm

/-- The «first order term# » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "#" term:max : firstOrderTerm

/-- The «first order term& » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "&" term:max : firstOrderTerm

/-- The «first order term!  ⋯» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :80 "!" term:max firstOrderTerm:81* (" ⋯")? : firstOrderTerm

/-- The first order term!! construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :80 "!!" term:max : firstOrderTerm

/-- The !  ⋯» construction in `FFL.FirstOrder.BinderNotation.«firstOrderTerm`. -/
syntax :80 ".!" term:max firstOrderTerm:81* (" ⋯")? : firstOrderTerm

/-- The !! » construction in `FFL.FirstOrder.BinderNotation.«firstOrderTerm`. -/
syntax :80 ".!!" term:max : firstOrderTerm

/-- The first order term  1 construction in `FFL.FirstOrder.BinderNotation`. -/
syntax num : firstOrderTerm

/-- The «first order term↑ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "↑" term:max : firstOrderTerm

/-- The «first order term⋆» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "⋆" : firstOrderTerm

/-- The «first order term + » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :50 firstOrderTerm:50 " + " firstOrderTerm:51 : firstOrderTerm

/-- The «first order term * » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :60 firstOrderTerm:60 " * " firstOrderTerm:61 : firstOrderTerm

/-- The «first order term ^ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :65 firstOrderTerm:65 " ^ " firstOrderTerm:66 : firstOrderTerm

/-- The «first order term ^' » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :70 firstOrderTerm " ^' " num : firstOrderTerm

/-- The «first order term ²» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max firstOrderTerm "²" : firstOrderTerm

/-- The «first order term ³» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max firstOrderTerm "³" : firstOrderTerm

/-- The «first order term ⁴» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max firstOrderTerm "⁴" : firstOrderTerm

/-- The «first order term⌜ ⌝» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "⌜" term:max "⌝" : firstOrderTerm

/-- The first order term Exp construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :67 "exp " firstOrderTerm:68 : firstOrderTerm

macro_rules
  | `(quoteterm($type)[$binders* | $fbinders* | ($e)]) =>
    `(quoteterm($type)[$binders* | $fbinders* | $e])

macro_rules
  | `(quoteterm(lit)[ $binders* | $fbinders* | $x:ident]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable did not found."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(&$i)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(#$i)
  | `(quoteterm(lit)[ $_*       | $_*        | #$x:term   ]) => `(#$x)
  | `(quoteterm(lit)[ $_*       | $_*        | &$x:term   ]) => `(&$x)
  | `(quoteterm(lit)[ $_*       | $_*        | $m:num     ]) => `(Semiterm.numeral $m)
  | `(quoteterm(lit)[ $_*       | $_*        | ↑$m:term   ]) => `(Semiterm.numeral $m)
  | `(quoteterm(lit)[ $_*       | $_*        | ⌜$x:term⌝  ]) => `(⌜$x⌝)
  | `(quoteterm(lit)[ $_*       | $_*        | ⋆          ]) => `(Operator.const Operator.Star.star)
  | `(quoteterm(lit)[ $binders* | $fbinders* | $e₁ + $e₂  ]) =>
      `(Semiterm.Operator.Add.add.operator ![quoteterm(lit)[ $binders* | $fbinders* | $e₁ ],
      quoteterm(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(quoteterm(lit)[ $binders* | $fbinders* | $e₁ * $e₂  ]) =>
      `(Semiterm.Operator.Mul.mul.operator ![quoteterm(lit)[ $binders* | $fbinders* | $e₁ ],
      quoteterm(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(quoteterm(lit)[ $binders* | $fbinders* | $e₁ ^ $e₂  ]) =>
      `(Semiterm.Operator.Pow.pow.operator ![quoteterm(lit)[ $binders* | $fbinders* | $e₁ ],
      quoteterm(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(quoteterm(lit)[ $binders* | $fbinders* | $e ^' $n   ]) => `((Semiterm.Operator.npow _
      $n).operator ![quoteterm(lit)[ $binders* | $fbinders* | $e ]])
  | `(quoteterm(lit)[ $binders* | $fbinders* | $e²        ]) => `((Semiterm.Operator.npow _
      2).operator ![quoteterm(lit)[ $binders* | $fbinders* | $e ]])
  | `(quoteterm(lit)[ $binders* | $fbinders* | $e³        ]) => `((Semiterm.Operator.npow _
      3).operator ![quoteterm(lit)[ $binders* | $fbinders* | $e ]])
  | `(quoteterm(lit)[ $binders* | $fbinders* | $e⁴        ]) => `((Semiterm.Operator.npow _
      4).operator ![quoteterm(lit)[ $binders* | $fbinders* | $e ]])
  | `(quoteterm(lit)[ $binders* | $fbinders* | exp $e     ]) =>
      `(Semiterm.Operator.Exp.exp.operator ![quoteterm(lit)[ $binders* | $fbinders* | $e ]])
  | `(quoteterm(lit)[ $_*       | $_*        | !!$t:term  ]) => `($t)
  | `(quoteterm(lit)[ $_*       | $_*        | .!!$t:term ]) => `(Rew.emb $t)







macro_rules
  | `(quoteterm(lit)[$binders* | $fbinders* | !$t:term$vs:firstOrderTerm*]) => do
    let v ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(![]))
          (fun a s => `(quoteterm(lit)[$binders* | $fbinders* | $a] :> $s))
    `(Rew.subst $v $t)
  | `(quoteterm(lit)[$binders* | $fbinders* | !$t:term$vs:firstOrderTerm* ⋯]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length)))
          (fun a s ↦ `(quoteterm(lit)[$binders* | $fbinders* | $a] :> $s))
    `(Rew.subst $v $t)
  | `(quoteterm(lit)[$binders* | $fbinders* | .!$t:term$vs:firstOrderTerm*]) => do
    let v ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(![]))
          (fun a s ↦ `(quoteterm(lit)[$binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)
  | `(quoteterm(lit)[$binders* | $fbinders* | .!$t:term$vs:firstOrderTerm* ⋯]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length)))
          (fun a s ↦ `(quoteterm(lit)[$binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)

/-- The «term‘ ’» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "‘" firstOrderTerm:0 "’" : term

/-- A term with free variables. -/
syntax "‘" ident* "| " firstOrderTerm:0 "’" : term

/-- A term with bound variables. -/
syntax "‘" ident* ". " firstOrderTerm:0 "’" : term

macro_rules
  | `(‘$e:firstOrderTerm’) => `(quoteterm(lit)[ | | $e])
  | `(‘$fbinders*| $e:firstOrderTerm’) => `(quoteterm(lit)[ | $fbinders* | $e])
  | `(‘$binders*. $e:firstOrderTerm’) => `(quoteterm(lit)[$binders* | | $e])

section delab

/-- The unexpander Nat Lit construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Semiterm.Operator.numeral]
meta def unexpanderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z:num)
  | _ => throw ()







/-- The unexpander Operator Const construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Semiterm.Operator.const]
meta def unexpanderOperatorConst : Unexpander
  | `($_ $z:num) => `(‘ $z:num ’)
  | _ => throw ()







/-- The unexpander Add construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Semiterm.Operator.Add.add]
meta def unexpanderAdd : Unexpander
  | `($_) => `(op(+))

/-- The unexpander Mul construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Semiterm.Operator.Mul.mul]
meta def unexpanderMul : Unexpander
  | `($_) => `(op(*))

/-- The unexpand Func Arith construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Semiterm.Operator.operator]
meta def unexpandFuncArith : Unexpander
  | `($_ op(+) ![‘$t:firstOrderTerm’,   ‘$u:firstOrderTerm’   ]) => `(‘($t     + $u     )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   #$x                     ]) => `(‘($t     + #$x    )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   &$x                     ]) => `(‘($t     + &$x    )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   ↑$m:num                 ]) => `(‘($t     + $m:num )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   $u:term                 ]) => `(‘($t     + !!$u   )’)
  | `($_ op(+) ![#$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(#$x    + $u     )’)
  | `($_ op(+) ![#$x,                     #$y                     ]) => `(‘(#$x    + #$y    )’)
  | `($_ op(+) ![#$x,                     &$y                     ]) => `(‘(#$x    + &$y    )’)
  | `($_ op(+) ![#$x,                     ↑$m:num                 ]) => `(‘(#$x    + $m:num )’)
  | `($_ op(+) ![#$x,                     $u                      ]) => `(‘(#$x    + !!$u   )’)
  | `($_ op(+) ![&$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(&$x    + $u     )’)
  | `($_ op(+) ![&$x,                     #$y                     ]) => `(‘(&$x    + #$y    )’)
  | `($_ op(+) ![&$x,                     &$y                     ]) => `(‘(&$x    + &$y    )’)
  | `($_ op(+) ![&$x,                     ↑$m:num                 ]) => `(‘(&$x    + $m:num )’)
  | `($_ op(+) ![&$x,                     $u                      ]) => `(‘(&$x    + !!$u   )’)
  | `($_ op(+) ![↑$n:num,                 ‘$u:firstOrderTerm’   ]) => `(‘($n:num + $u     )’)
  | `($_ op(+) ![↑$n:num,                 #$y                     ]) => `(‘($n:num + #$y    )’)
  | `($_ op(+) ![↑$n:num,                 &$y                     ]) => `(‘($n:num + &$y    )’)
  | `($_ op(+) ![↑$n:num,                 ↑$m:num                 ]) => `(‘($n:num + $m:num )’)
  | `($_ op(+) ![↑$n:num,                 $u                      ]) => `(‘($n:num + !!$u   )’)
  | `($_ op(+) ![$t:term,                 ‘$u:firstOrderTerm’   ]) => `(‘(!!$t   + $u     )’)
  | `($_ op(+) ![$t:term,                 #$y                     ]) => `(‘(!!$t   + #$y    )’)
  | `($_ op(+) ![$t:term,                 &$y                     ]) => `(‘(!!$t   + &$y    )’)
  | `($_ op(+) ![$t:term,                 ↑$m:num                 ]) => `(‘(!!$t   + $m:num )’)
  | `($_ op(+) ![$t:term,                 $u                      ]) => `(‘(!!$t   + !!$u   )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   ‘$u:firstOrderTerm’   ]) => `(‘($t     * $u     )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   #$x                     ]) => `(‘($t     * #$x    )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   &$x                     ]) => `(‘($t     * &$x    )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   ↑$m:num                 ]) => `(‘($t     * $m:num )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   $u:term                 ]) => `(‘($t     * !!$u   )’)
  | `($_ op(*) ![#$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(#$x    * $u     )’)
  | `($_ op(*) ![#$x,                     #$y                     ]) => `(‘(#$x    * #$y    )’)
  | `($_ op(*) ![#$x,                     &$y                     ]) => `(‘(#$x    * &$y    )’)
  | `($_ op(*) ![#$x,                     ↑$m:num                 ]) => `(‘(#$x    * $m:num )’)
  | `($_ op(*) ![#$x,                     $u                      ]) => `(‘(#$x    * !!$u   )’)
  | `($_ op(*) ![&$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(&$x    * $u     )’)
  | `($_ op(*) ![&$x,                     #$y                     ]) => `(‘(&$x    * #$y    )’)
  | `($_ op(*) ![&$x,                     &$y                     ]) => `(‘(&$x    * &$y    )’)
  | `($_ op(*) ![&$x,                     ↑$m:num                 ]) => `(‘(&$x    * $m:num )’)
  | `($_ op(*) ![&$x,                     $u                      ]) => `(‘(&$x    * !!$u   )’)
  | `($_ op(*) ![↑$n:num,                 ‘$u:firstOrderTerm’   ]) => `(‘($n:num * $u     )’)
  | `($_ op(*) ![↑$n:num,                 #$y                     ]) => `(‘($n:num * #$y    )’)
  | `($_ op(*) ![↑$n:num,                 &$y                     ]) => `(‘($n:num * &$y    )’)
  | `($_ op(*) ![↑$n:num,                 ↑$m:num                 ]) => `(‘($n:num * $m:num )’)
  | `($_ op(*) ![↑$n:num,                 $u                      ]) => `(‘($n:num * !!$u   )’)
  | `($_ op(*) ![$t:term,                 ‘$u:firstOrderTerm’   ]) => `(‘(!!$t   * $u     )’)
  | `($_ op(*) ![$t:term,                 #$y                     ]) => `(‘(!!$t   * #$y    )’)
  | `($_ op(*) ![$t:term,                 &$y                     ]) => `(‘(!!$t   * &$y    )’)
  | `($_ op(*) ![$t:term,                 ↑$m:num                 ]) => `(‘(!!$t   * $m:num )’)
  | `($_ op(*) ![$t:term,                 $u                      ]) => `(‘(!!$t   * !!$u   )’)
  | _                             => throw ()







/-- The unexpand Numeral construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Semiterm.numeral]
meta def unexpandNumeral : Unexpander
  | `($_ $n:num) => `(‘$n:num’)
  | _            => throw ()







end delab

/-!
### Notation for formulae -/

open Semiformula

/-- The first order formula construction in `Lean.Parser.Category`. -/
declare_syntax_cat firstOrderFormula

/-- The «term Quoteformula( )[ | | ]» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "quoteformula(" firstOrder.quoteType ")[" ident* " | " ident* " | " firstOrderFormula:0
  "]" : term

/-- The «first order formula( )» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "(" firstOrderFormula ")" : firstOrderFormula

/-- The «first order formula Of term[ ]» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :60 "of_term[" firstOrderTerm:61 "]" : firstOrderFormula

/-- The «first order formula!  ⋯» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :60 "!" term:max firstOrderTerm:61* ("⋯")? : firstOrderFormula

/-- The first order formula!! construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :60 "!!" term:max : firstOrderFormula

/-- The !  ⋯» construction in `FFL.FirstOrder.BinderNotation.«firstOrderFormula`. -/
syntax :60 ".!" term:max firstOrderTerm:61* ("⋯")? : firstOrderFormula

/-- The !! » construction in `FFL.FirstOrder.BinderNotation.«firstOrderFormula`. -/
syntax :60 ".!!" term:max : firstOrderFormula

/-- The «first order formula⊤» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "⊤" : firstOrderFormula

/-- The «first order formula⊥» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "⊥" : firstOrderFormula

/-- The «first order formula ∧ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :32 firstOrderFormula:33 " ∧ " firstOrderFormula:32 : firstOrderFormula

/-- The «first order formula ∨ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :30 firstOrderFormula:31 " ∨ " firstOrderFormula:30 : firstOrderFormula

/-- The «first order formula¬ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "¬" firstOrderFormula:35 : firstOrderFormula

/-- The «first order formula → » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :10 firstOrderFormula:9 " → " firstOrderFormula:10 : firstOrderFormula

/-- The «first order formula ↔ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :5 firstOrderFormula " ↔ " firstOrderFormula : firstOrderFormula

/-- The «first order formula⋀ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "⋀ " ident ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula⋁ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "⋁ " ident ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula⋀ < , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "⋀ " ident " < " term ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula⋁ < , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "⋁ " ident " < " term ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∀ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∀ " ident+ ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃ " ident+ ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∀¹ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∀¹ " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃¹ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃¹ " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∀¹[ ] » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∀¹[" firstOrderFormula "] " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃¹[ ] » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃¹[" firstOrderFormula "] " firstOrderFormula:0 : firstOrderFormula

macro_rules
  | `(quoteformula($type)[ $binders* | $fbinders* | ($e)          ]) => `(quoteformula($type)[
      $binders* | $fbinders* | $e ])
  | `(quoteformula($type)[ $_*       | $_*        | !!$φ:term     ]) => `($φ)
  | `(quoteformula($type)[ $_*       | $_*        | .!!$φ:term    ]) => `(Rewriting.emb $φ)
  | `(quoteformula($type)[ $_*       | $_*        | ⊤             ]) => `(⊤)
  | `(quoteformula($type)[ $_*       | $_*        | ⊥             ]) => `(⊥)
  | `(quoteformula($type)[ $binders* | $fbinders* | $φ ∧ $ψ       ]) => `(@HWedge.hWedge _ _ _
      Wedge.instHWedge quoteformula($type)[ $binders* | $fbinders* | $φ ] quoteformula($type)[
      $binders* | $fbinders* | $ψ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | $φ ∨ $ψ       ]) => `(@HVee.hVee _ _ _
      Vee.instHVee quoteformula($type)[ $binders* | $fbinders* | $φ ] quoteformula($type)[
      $binders* | $fbinders* | $ψ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | ¬$φ           ]) => `(@HTilde.hTilde _ _
      Tilde.instHTilde quoteformula($type)[ $binders* | $fbinders* | $φ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | $φ → $ψ       ]) => `(@HArrow.hArrow _ _ _
      Arrow.instHArrow quoteformula($type)[ $binders* | $fbinders* | $φ ] quoteformula($type)[
      $binders* | $fbinders* | $ψ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | $φ ↔ $ψ       ]) => `(quoteformula($type)[
      $binders* | $fbinders* | $φ ] ⇔ₗ quoteformula($type)[ $binders* | $fbinders* | $ψ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | ⋀ $i, $φ      ]) => `(Matrix.conj fun $i ↦
      quoteformula($type)[ $binders* | $fbinders* | $φ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | ⋁ $i, $φ      ]) => `(Matrix.disj fun $i ↦
      quoteformula($type)[ $binders* | $fbinders* | $φ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | ⋀ $i < $t, $φ ]) => `(conjLt (fun $i ↦
      quoteformula($type)[ $binders* | $fbinders* | $φ ]) $t)
  | `(quoteformula($type)[ $binders* | $fbinders* | ⋁ $i < $t, $φ ]) => `(disjLt (fun $i ↦
      quoteformula($type)[ $binders* | $fbinders* | $φ ]) $t)
  | `(quoteformula($type)[ $binders* | $fbinders* | ∀ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(quoteformula($type)[ $binders'* | $fbinders* | $φ ])
        (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∀¹ $ψ))
    return s
  | `(quoteformula($type)[ $binders* | $fbinders* | ∃ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(quoteformula($type)[ $binders'* | $fbinders* | $φ ])
        (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∃¹ $ψ))
    return s
  | `(quoteformula($type)[ $binders* | $fbinders* | ∀¹ $φ         ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀¹ quoteformula($type)[ $binders'* | $fbinders* | $φ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | ∃¹ $φ         ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹ quoteformula($type)[ $binders'* | $fbinders* | $φ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | ∀¹[ $φ ] $ψ    ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀¹[quoteformula($type)[ $binders'* | $fbinders* | $φ ]] quoteformula($type)[ $binders'* |
        $fbinders* | $ψ ])
  | `(quoteformula($type)[ $binders* | $fbinders* | ∃¹[ $φ ] $ψ    ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹[quoteformula($type)[ $binders'* | $fbinders* | $φ ]] quoteformula($type)[ $binders'* |
        $fbinders* | $ψ ])







/-- A formula in literal notation. For a formula `φ`, write `!φ` to include `φ` in the formula.
Identifiers may be written after `!φ` as its bound variables.

`⋯` adds enough unnamed bound variables to fill up the arity of `φ`, with indices starting after
the last named identifier. For example, assume `φ` is a `Semiformula L k`, and consider the
formula `“x y z. !φ x y ⋯”`. Here `x`, `y`, and `z` are the bound variables `#0`, `#1`, and `#2`
respectively. Then `!φ x y ⋯` will add `k - 2` new bound variables, and expand to `!φ #0 #1 #3
#4 ... #(k + 1)`.
-/
macro_rules
  | `(quoteformula(lit)[ $binders* | $fbinders* | !$φ:term $vs:firstOrderTerm*   ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s ↦ `(quoteterm(lit)[
        $binders* | $fbinders* | $a ] :> $s))
    `($φ ↜ $v)
  | `(quoteformula(lit)[ $binders* | $fbinders* | !$φ:term $vs:firstOrderTerm* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(quoteterm(lit)[ $binders* | $fbinders* | $a] :> $s))
    `($φ ↜ $v)







/-- The «term“ | ”» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "“" ident* "| " firstOrderFormula:0 "”" : term

/-- The ”» construction in `FFL.FirstOrder.BinderNotation.«term“_`. -/
syntax "“" ident* ". " firstOrderFormula:0 "”" : term

/-- The «term“ ”» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "“" firstOrderFormula:0 "”" : term

macro_rules
  | `(“$e:firstOrderFormula”) => `(quoteformula(lit)[ | | $e])
  | `(“$binders*. $e:firstOrderFormula”) => `(quoteformula(lit)[$binders* | | $e])
  | `(“$fbinders*| $e:firstOrderFormula”) => `(quoteformula(lit)[ | $fbinders* | $e])

/-- The «first order formula = » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " = " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula < » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " < " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula > » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " > " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ≤ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ≤ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ≥ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ≥ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ∈ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ∈ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ∋ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ∋ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ≠ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ≠ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ≮ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ≮ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ≰ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ≰ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula ∉ » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :45 firstOrderTerm:45 " ∉ " firstOrderTerm:0 : firstOrderFormula

/-- The «first order formula∀ < , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∀ " ident " < " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∀ ≤ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∀ " ident " ≤ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∀ ∈ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∀ " ident " ∈ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃ < , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃ " ident " < " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃ ≤ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃ " ident " ≤ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃ ∈ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃ " ident " ∈ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

macro_rules
  | `(quoteformula($type)[$binders* | $fbinders* | $t:firstOrderTerm > $u:firstOrderTerm]) =>
    `(quoteformula($type)[$binders* | $fbinders* | $u:firstOrderTerm < $t:firstOrderTerm])
  | `(quoteformula($type)[$binders* | $fbinders* | $t:firstOrderTerm ≥ $u:firstOrderTerm]) =>
    `(quoteformula($type)[$binders* | $fbinders* | $u:firstOrderTerm ≤ $t:firstOrderTerm])
  | `(quoteformula($type)[$binders* | $fbinders* | $t:firstOrderTerm ∋ $u:firstOrderTerm]) =>
    `(quoteformula($type)[$binders* | $fbinders* | $u:firstOrderTerm ∈ $t:firstOrderTerm])

macro_rules
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm = $u:firstOrderTerm]) =>
    `(Semiformula.Operator.operator Operator.Eq.eq
        ![quoteterm(lit)[$binders* | $fbinders* | $t],
          quoteterm(lit)[$binders* | $fbinders* | $u]])
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm < $u:firstOrderTerm]) =>
    `(Semiformula.Operator.operator Operator.LT.lt
        ![quoteterm(lit)[$binders* | $fbinders* | $t],
          quoteterm(lit)[$binders* | $fbinders* | $u]])
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm ≤ $u:firstOrderTerm]) =>
    `(Semiformula.Operator.operator Operator.LE.le
        ![quoteterm(lit)[$binders* | $fbinders* | $t],
          quoteterm(lit)[$binders* | $fbinders* | $u]])
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm ∈ $u:firstOrderTerm]) =>
    `(Semiformula.Operator.operator Operator.Mem.mem
        ![quoteterm(lit)[$binders* | $fbinders* | $t],
          quoteterm(lit)[$binders* | $fbinders* | $u]])
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm ≠ $u:firstOrderTerm]) =>
    `(@HTilde.hTilde _ _ Tilde.instHTilde
        (Semiformula.Operator.operator Operator.Eq.eq
          ![quoteterm(lit)[$binders* | $fbinders* | $t],
            quoteterm(lit)[$binders* | $fbinders* | $u]]))
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm ≮ $u:firstOrderTerm]) =>
    `(@HTilde.hTilde _ _ Tilde.instHTilde
        (Semiformula.Operator.operator Operator.LT.lt
          ![quoteterm(lit)[$binders* | $fbinders* | $t],
            quoteterm(lit)[$binders* | $fbinders* | $u]]))
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm ≰ $u:firstOrderTerm]) =>
    `(@HTilde.hTilde _ _ Tilde.instHTilde
        (Semiformula.Operator.operator Operator.LE.le
          ![quoteterm(lit)[$binders* | $fbinders* | $t],
            quoteterm(lit)[$binders* | $fbinders* | $u]]))
  | `(quoteformula(lit)[$binders* | $fbinders* | $t:firstOrderTerm ∉ $u:firstOrderTerm]) =>
    `(@HTilde.hTilde _ _ Tilde.instHTilde
        (Semiformula.Operator.operator Operator.Mem.mem
          ![quoteterm(lit)[$binders* | $fbinders* | $t],
            quoteterm(lit)[$binders* | $fbinders* | $u]]))

macro_rules
  | `(quoteformula(lit)[$binders* | $fbinders* | ∀ $x < $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      `(Semiformula.ballLT quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$x$binders* | $fbinders* | $φ])
  | `(quoteformula(lit)[$binders* | $fbinders* | ∀ $x ≤ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      `(Semiformula.ballLE quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$x$binders* | $fbinders* | $φ])
  | `(quoteformula(lit)[$binders* | $fbinders* | ∀ $x ∈ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      `(Semiformula.ballMem quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$x$binders* | $fbinders* | $φ])
  | `(quoteformula(lit)[$binders* | $fbinders* | ∃ $x < $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      `(Semiformula.bexsLT quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$x$binders* | $fbinders* | $φ])
  | `(quoteformula(lit)[$binders* | $fbinders* | ∃ $x ≤ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      `(Semiformula.bexsLE quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$x$binders* | $fbinders* | $φ])
  | `(quoteformula(lit)[$binders* | $fbinders* | ∃ $x ∈ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      `(Semiformula.bexsMem quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$x$binders* | $fbinders* | $φ])

section delab

/-- The unexpander Eq construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Language.Eq.eq]
meta def unexpanderEq : Unexpander
  | `($_) => `(op(=))

/-- The unexpander Le construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Language.LT.lt]
meta def unexpanderLe : Unexpander
  | `($_) => `(op(<))

/-- The unexpand And construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Wedge.wedge]
meta def unexpandAnd : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ ($φ ∧ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ ($φ ∧ !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (!$t ∧ $ψ) ”)
  | _                                                           => throw ()







/-- The unexpand Or construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Vee.vee]
meta def unexpandOr : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ ($φ ∨ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ ($φ ∨ !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (!$t ∨ $ψ) ”)
  | _                                                           => throw ()







/-- The unexpand Neg construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Tilde.tilde]
meta def unexpandNeg : Unexpander
  | `($_ “ $φ:firstOrderFormula ”) => `(“ ¬$φ ”)
  | _                                => throw ()







/-- The unexpand Univ construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander UnivQuantifier.all]
meta def unexpandUniv : Unexpander
  | `($_ “ $φ:firstOrderFormula ”) => `(“ ∀¹ $φ:firstOrderFormula ”)
  | _                                => throw ()







/-- The unexpand Ex construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander ExsQuantifier.exs]
meta def unexpandEx : Unexpander
  | `($_ “ $φ:firstOrderFormula”) => `(“ ∃¹ $φ:firstOrderFormula ”)
  | _                                   => throw ()







/-- The unexpand Ball construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander ball]
meta def unexpandBall : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ (∀¹[$φ] $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ (∀¹[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (∀¹[!$t] $ψ) ”)
  | _                                                           => throw ()







/-- The unexpand Bex construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander bexs]
meta def unexpandBex : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ (∃¹[$φ] $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ (∃¹[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (∃¹[!$t] $ψ) ”)
  | _                                                           => throw ()







/-- The unexpand Arrow construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Arrow.arrow]
meta def unexpandArrow : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula”) => `(“ ($φ → $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                  ) => `(“ ($φ → !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula”) => `(“ (!$t → $ψ) ”)
  | _                                                          => throw ()







/-- The unexpand Iff construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander LogicalConnective.iff]
meta def unexpandIff : Unexpander
  | `($_ “ $φ:firstOrderFormula” “ $ψ:firstOrderFormula”) => `(“ ($φ ↔ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula” $u:term                  ) => `(“ ($φ ↔ !$u) ”)
  | `($_ $t:term                   “ $ψ:firstOrderFormula”) => `(“ (!$t ↔ $ψ) ”)
  | _                                                         => throw ()







/-- The unexpand Op Arith construction in `FFL.FirstOrder.BinderNotation`. -/
@[app_unexpander Semiformula.Operator.operator]
meta def unexpandOpArith : Unexpander
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) => `(“ $t:firstOrderTerm = $u
         ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) => `(“ $t:firstOrderTerm =
      #$y     ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) => `(“ $t:firstOrderTerm =
      &$y     ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  ↑$m:num                ]) => `(“ $t:firstOrderTerm =
      $m:num  ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  $u                     ]) => `(“ $t:firstOrderTerm =
      !!$u    ”)
  | `($_ op(=) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ #$x                 =
      $u      ”)
  | `($_ op(=) ![#$x:term,                 #$y:term               ]) => `(“ #$x
      = #$y     ”)
  | `($_ op(=) ![#$x:term,                 &$y:term               ]) => `(“ #$x
      = &$y     ”)
  | `($_ op(=) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x
      = $m:num  ”)
  | `($_ op(=) ![#$x:term,                 $u                     ]) => `(“ #$x
      = !!$u    ”)
  | `($_ op(=) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ &$x                 =
      $u      ”)
  | `($_ op(=) ![&$x:term,                 #$y:term               ]) => `(“ &$x
      = #$y     ”)
  | `($_ op(=) ![&$x:term,                 &$y:term               ]) => `(“ &$x
      = &$y     ”)
  | `($_ op(=) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x
      = $m:num  ”)
  | `($_ op(=) ![&$x:term,                 $u                     ]) => `(“ &$x
      = !!$u    ”)
  | `($_ op(=) ![↑$n:num,                  ‘ $u:firstOrderTerm ’]) => `(“ $n:num              =
      $u      ”)
  | `($_ op(=) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num
      = #$y     ”)
  | `($_ op(=) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num
      = &$y     ”)
  | `($_ op(=) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num
      = $m:num  ”)
  | `($_ op(=) ![↑$n:num,                  $u                     ]) => `(“ $n:num
      = !!$u    ”)
  | `($_ op(=) ![$t:term,                  ‘ $u:firstOrderTerm ’]) => `(“ !!$t                =
      $u      ”)
  | `($_ op(=) ![$t:term,                  #$y:term               ]) => `(“ !!$t
      = #$y     ”)
  | `($_ op(=) ![$t:term,                  &$y:term               ]) => `(“ !!$t
      = &$y     ”)
  | `($_ op(=) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t
      = $m:num  ”)
  | `($_ op(=) ![$t:term,                  $u                     ]) => `(“ !!$t
      = !!$u    ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) => `(“ $t:firstOrderTerm < $u
         ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) => `(“ $t:firstOrderTerm <
      #$y     ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) => `(“ $t:firstOrderTerm <
      &$y     ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  ↑$m:num                ]) => `(“ $t:firstOrderTerm <
      $m:num  ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  $u                     ]) => `(“ $t:firstOrderTerm <
      !!$u    ”)
  | `($_ op(<) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ #$x                 <
      $u      ”)
  | `($_ op(<) ![#$x:term,                 #$y:term               ]) => `(“ #$x
      < #$y     ”)
  | `($_ op(<) ![#$x:term,                 &$y:term               ]) => `(“ #$x
      < &$y     ”)
  | `($_ op(<) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x
      < $m:num  ”)
  | `($_ op(<) ![#$x:term,                 $u                     ]) => `(“ #$x
      < !!$u    ”)
  | `($_ op(<) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ &$x                 <
      $u      ”)
  | `($_ op(<) ![&$x:term,                 #$y:term               ]) => `(“ &$x
      < #$y     ”)
  | `($_ op(<) ![&$x:term,                 &$y:term               ]) => `(“ &$x
      < &$y     ”)
  | `($_ op(<) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x
      < $m:num  ”)
  | `($_ op(<) ![&$x:term,                 $u                     ]) => `(“ &$x
      < !!$u    ”)
  | `($_ op(<) ![↑$n:num,                  ‘ $u:firstOrderTerm ’]) => `(“ $n:num              <
      $u      ”)
  | `($_ op(<) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num
      < #$y     ”)
  | `($_ op(<) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num
      < &$y     ”)
  | `($_ op(<) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num
      < $m:num  ”)
  | `($_ op(<) ![↑$n:num,                  $u                     ]) => `(“ $n:num
      < !!$u    ”)
  | `($_ op(<) ![$t:term,                  ‘ $u:firstOrderTerm ’]) => `(“ !!$t                <
      $u      ”)
  | `($_ op(<) ![$t:term,                  #$y:term               ]) => `(“ !!$t
      < #$y     ”)
  | `($_ op(<) ![$t:term,                  &$y:term               ]) => `(“ !!$t
      < &$y     ”)
  | `($_ op(<) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t
      < $m:num  ”)
  | `($_ op(<) ![$t:term,                  $u                     ]) => `(“ !!$t
      < !!$u    ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) => `(“ $t:firstOrderTerm ≤ $u
         ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) => `(“ $t:firstOrderTerm ≤
      #$y     ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) => `(“ $t:firstOrderTerm ≤
      &$y     ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  ↑$m:num                ]) => `(“ $t:firstOrderTerm ≤
      $m:num  ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  $u                     ]) => `(“ $t:firstOrderTerm ≤
      !!$u    ”)
  | `($_ op(≤) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ #$x                 ≤
      $u      ”)
  | `($_ op(≤) ![#$x:term,                 #$y:term               ]) => `(“ #$x
      ≤ #$y     ”)
  | `($_ op(≤) ![#$x:term,                 &$y:term               ]) => `(“ #$x
      ≤ &$y     ”)
  | `($_ op(≤) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x
      ≤ $m:num  ”)
  | `($_ op(≤) ![#$x:term,                 $u                     ]) => `(“ #$x
      ≤ !!$u    ”)
  | `($_ op(≤) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ &$x                 ≤
      $u      ”)
  | `($_ op(≤) ![&$x:term,                 #$y:term               ]) => `(“ &$x
      ≤ #$y     ”)
  | `($_ op(≤) ![&$x:term,                 &$y:term               ]) => `(“ &$x
      ≤ &$y     ”)
  | `($_ op(≤) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x
      ≤ $m:num  ”)
  | `($_ op(≤) ![&$x:term,                 $u                     ]) => `(“ &$x
      ≤ !!$u    ”)
  | `($_ op(≤) ![↑$n:num,                  ‘ $u:firstOrderTerm ’]) => `(“ $n:num              ≤
      $u      ”)
  | `($_ op(≤) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num
      ≤ #$y     ”)
  | `($_ op(≤) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num
      ≤ &$y     ”)
  | `($_ op(≤) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num
      ≤ $m:num  ”)
  | `($_ op(≤) ![↑$n:num,                  $u                     ]) => `(“ $n:num
      ≤ !!$u    ”)
  | `($_ op(≤) ![$t:term,                  ‘ $u:firstOrderTerm ’]) => `(“ !!$t                ≤
      $u      ”)
  | `($_ op(≤) ![$t:term,                  #$y:term               ]) => `(“ !!$t
      ≤ #$y     ”)
  | `($_ op(≤) ![$t:term,                  &$y:term               ]) => `(“ !!$t
      ≤ &$y     ”)
  | `($_ op(≤) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t
      ≤ $m:num  ”)
  | `($_ op(≤) ![$t:term,                  $u                     ]) => `(“ !!$t
      ≤ !!$u    ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) => `(“ $t:firstOrderTerm ∈ $u
         ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) => `(“ $t:firstOrderTerm ∈
      #$y     ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) => `(“ $t:firstOrderTerm ∈
      &$y     ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  ↑$m:num                ]) => `(“ $t:firstOrderTerm ∈
      $m:num  ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  $u                     ]) => `(“ $t:firstOrderTerm ∈
      !!$u    ”)
  | `($_ op(∈) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ #$x                 ∈
      $u      ”)
  | `($_ op(∈) ![#$x:term,                 #$y:term               ]) => `(“ #$x
      ∈ #$y     ”)
  | `($_ op(∈) ![#$x:term,                 &$y:term               ]) => `(“ #$x
      ∈ &$y     ”)
  | `($_ op(∈) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x
      ∈ $m:num  ”)
  | `($_ op(∈) ![#$x:term,                 $u                     ]) => `(“ #$x
      ∈ !!$u    ”)
  | `($_ op(∈) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) => `(“ &$x                 ∈
      $u      ”)
  | `($_ op(∈) ![&$x:term,                 #$y:term               ]) => `(“ &$x
      ∈ #$y     ”)
  | `($_ op(∈) ![&$x:term,                 &$y:term               ]) => `(“ &$x
      ∈ &$y     ”)
  | `($_ op(∈) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x
      ∈ $m:num  ”)
  | `($_ op(∈) ![&$x:term,                 $u                     ]) => `(“ &$x
      ∈ !!$u    ”)
  | `($_ op(∈) ![↑$n:num,                  ‘ $u:firstOrderTerm ’]) => `(“ $n:num              ∈
      $u      ”)
  | `($_ op(∈) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num
      ∈ #$y     ”)
  | `($_ op(∈) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num
      ∈ &$y     ”)
  | `($_ op(∈) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num
      ∈ $m:num  ”)
  | `($_ op(∈) ![↑$n:num,                  $u                     ]) => `(“ $n:num
      ∈ !!$u    ”)
  | `($_ op(∈) ![$t:term,                  ‘ $u:firstOrderTerm ’]) => `(“ !!$t                ∈
      $u      ”)
  | `($_ op(∈) ![$t:term,                  #$y:term               ]) => `(“ !!$t
      ∈ #$y     ”)
  | `($_ op(∈) ![$t:term,                  &$y:term               ]) => `(“ !!$t
      ∈ &$y     ”)
  | `($_ op(∈) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t
      ∈ $m:num  ”)
  | `($_ op(∈) ![$t:term,                  $u                     ]) => `(“ !!$t
      ∈ !!$u    ”)
  | _                                                            => throw ()







end delab

/-!
### Notation for formula as term -/

macro_rules
  | `(quoteformula(faf)[$binders* | $fbinders* | !$φ:term$vs:firstOrderTerm*]) => do
    let Ψ ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
          let x : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
          `(quoteterm(faf)[$x$binders* | $fbinders* | $a] :> $s)
    `(($φ).nestFormulae $Ψ)
  | `(quoteformula(faf)[$binders* | $fbinders* | !$φ:term$vs:firstOrderTerm*⋯]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) fun a s ↦
          do
          let x : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
          `(quoteterm(faf)[$x$binders* | $fbinders* | $a] :> $s)
    `(($φ).nestFormulae $Ψ)

macro_rules
  | `(quoteterm(faf)[$binders* | $fbinders* | $x:ident]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none =>
        Macro.throwErrorAt x "error: variable does not appeared."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(“#0 = &$i”)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(“#0 = #$i”)
  | `(quoteterm(faf)[$binders* | $fbinders* | !$f:term$vs:firstOrderTerm*]) => do
    let Ψ ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
          `(quoteterm(faf)[$binders* | $fbinders* | $a] :> $s)
    `(($f).nestFormulaeFunc $Ψ)
  | `(quoteterm(faf)[$binders* | $fbinders* | !$f:term$vs:firstOrderTerm* ⋯]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ←
      vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ “#0 = #(finSuccItr x $length)”))
          fun a s ↦ do
          `(quoteterm(faf)[$binders* | $fbinders* | $a] :> $s)
    `(($f).nestFormulaeFunc $Ψ)

macro_rules
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm = $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 = #0”))))
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm ≠ $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 ≠ #0”))))
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm < $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 < #0”))))
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm ≮ $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 ≮ #0”))))
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm ≤ $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 ≤ #0”))))
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm ≰ $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 ≰ #0”))))
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm ∈ $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 ∈ #0”))))
  | `(quoteformula(faf)[$binders* | $fbinders* | $t:firstOrderTerm ∉ $u:firstOrderTerm]) => do
    let x₁ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    let x₂ : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
    `(∀¹
          (quoteterm(faf)[$x₁$binders* | $fbinders* | $t] ⇒ₗ
            ∀¹ (quoteterm(faf)[$x₁$x₂$binders* | $fbinders* | $u] ⇒ₗ (“#1 ∉ #0”))))

macro_rules
  | `(quoteformula(faf)[$binders* | $fbinders* | ∀ $x < $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let vt : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
      `(∀¹
            (quoteterm(faf)[$vt$binders* | $fbinders* | $t] ⇒ₗ
              Semiformula.ballLT #0 quoteformula(faf)[$x$vt$binders* | $fbinders* | $φ]))
  | `(quoteformula(faf)[$binders* | $fbinders* | ∀ $x ≤ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let vt : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
      `(∀¹
            (quoteterm(faf)[$vt$binders* | $fbinders* | $t] ⇒ₗ
              Semiformula.ballLE #0 quoteformula(faf)[$x$binders* | $fbinders* | $φ]))
  | `(quoteformula(faf)[$binders* | $fbinders* | ∀ $x ∈ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let vt : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
      `(∀¹
            (quoteterm(faf)[$vt$binders* | $fbinders* | $t] ⇒ₗ
              Semiformula.ballMem #0 quoteformula(faf)[$x$vt$binders* | $fbinders* | $φ]))
  | `(quoteformula(faf)[$binders* | $fbinders* | ∃ $x < $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let vt : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
      `(∀¹
            (quoteterm(faf)[$vt$binders* | $fbinders* | $t] ⇒ₗ
              Semiformula.bexsLT #0 quoteformula(faf)[$x$vt$binders* | $fbinders* | $φ]))
  | `(quoteformula(faf)[$binders* | $fbinders* | ∃ $x ≤ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let vt : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
      `(∀¹
            (quoteterm(faf)[$vt$binders* | $fbinders* | $t] ⇒ₗ
              Semiformula.bexsLE #0 quoteformula(faf)[$x$vt$binders* | $fbinders* | $φ]))
  | `(quoteformula(faf)[$binders* | $fbinders* | ∃ $x ∈ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let vt : TSyntax `ident ← PointwiseComposition.Lean.TSyntax.freshIdent
      `(∀¹
            (quoteterm(faf)[$vt$binders* | $fbinders* | $t] ⇒ₗ
              Semiformula.bexsMem #0 quoteformula(faf)[$x$vt$binders* | $fbinders* | $φ]))

/-- The «term F‘ ’» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "f‘" firstOrderTerm:0 "’" : term

/-- The «term F‘ | ’» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "f‘" ident* "| " firstOrderTerm:0 "’" : term

/-- The ’» construction in `FFL.FirstOrder.BinderNotation.«termF‘_`. -/
syntax "f‘" ident* ". " firstOrderTerm:0 "’" : term

macro_rules
  | `(f‘$e:firstOrderTerm’) => `(quoteterm(faf)[ | | $e])
  | `(f‘$fbinders*| $e:firstOrderTerm’) => `(quoteterm(faf)[ | $fbinders* | $e])
  | `(f‘$binders*. $e:firstOrderTerm’) => `(quoteterm(faf)[$binders* | | $e])

/-- The «term F“ | ”» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "f“" ident* "| " firstOrderFormula:0 "”" : term

/-- The ”» construction in `FFL.FirstOrder.BinderNotation.«termF“_`. -/
syntax "f“" ident* ". " firstOrderFormula:0 "”" : term

/-- The «term F“ ”» construction in `FFL.FirstOrder.BinderNotation`. -/
syntax "f“" firstOrderFormula:0 "”" : term

/--
A formula in formula-as-function notation. Use `f“⋯. ⋯”` for bound variables, and `f“⋯ | ⋯”` for
free variables. -/
macro_rules
  | `(f“$e:firstOrderFormula”) => `(quoteformula(faf)[ | | $e])
  | `(f“$fbinders*| $e:firstOrderFormula”) => `(quoteformula(faf)[ | $fbinders* | $e])
  | `(f“$binders*. $e:firstOrderFormula”) => `(quoteformula(faf)[$binders* | | $e])

end BinderNotation

end FirstOrder
end FFL

end

end PointwiseComposition
