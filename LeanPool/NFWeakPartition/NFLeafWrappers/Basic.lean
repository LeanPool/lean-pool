/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.Basic

/-! NF weak partition development: NFLeafWrappers.Basic. -/


public section

namespace NFChoice.NFLeafWrappers

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.PartialLowering
open NFChoice.ReplaySupport

/-! Typed source-leaf adapters for the ten non-extensional Hailperin axioms.

The caller supplies the actual Expander-normalized primitive nominal body.  In
particular, this keeps every synthetic class-abstraction dummy explicit in the
generated term rather than fixing a global name here.  The two computational
side conditions are exactly the certificate accepted by `valid_literal_leaf`:
the universal-closure list covers the free names and lowering that closure is
the literal source sentence.

Although the source `$d` hypotheses are not needed after the lowering
certificate has been checked, they are retained verbatim in every adapter.
This makes the generated call site expose precisely the contract checked by
Metamath before substitution.
-/


theorem source_ax_nin {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) (p : Wff)
    (hcover : p.fv ⊆ [x, y].toFinset)
    (hlower : lowerClosed (closeNames [x, y] p) = some literalAxNin) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axNin [x, y] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_xp {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w t : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hxt : x ≠ t) (_hyz : y ≠ z) (_hyw : y ≠ w)
    (_hyt : y ≠ t) (_hzw : z ≠ w) (_hzt : z ≠ t) (_hwt : w ≠ t) (p : Wff)
    (hcover : p.fv ⊆ [x].toFinset)
    (hlower : lowerClosed (closeNames [x] p) = some literalAxXp) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axXp [x] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_cnv {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) (p : Wff)
    (hcover : p.fv ⊆ [x].toFinset)
    (hlower : lowerClosed (closeNames [x] p) = some literalAxCnv) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axCnv [x] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_1c {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) (p : Wff)
    (hcover : p.fv ⊆ ([] : List Var).toFinset)
    (hlower : lowerClosed (closeNames [] p) = some literalAx1c) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .ax1c [] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_sset {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) (p : Wff)
    (hcover : p.fv ⊆ ([] : List Var).toFinset)
    (hlower : lowerClosed (closeNames [] p) = some literalAxSset) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axSset [] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_si {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) (p : Wff)
    (hcover : p.fv ⊆ [x].toFinset)
    (hlower : lowerClosed (closeNames [x] p) = some literalAxSi) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axSi [x] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_ins2 {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w t : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hxt : x ≠ t) (_hyz : y ≠ z) (_hyw : y ≠ w)
    (_hyt : y ≠ t) (_hzw : z ≠ w) (_hzt : z ≠ t) (_hwt : w ≠ t) (p : Wff)
    (hcover : p.fv ⊆ [x].toFinset)
    (hlower : lowerClosed (closeNames [x] p) = some literalAxIns2) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axIns2 [x] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_ins3 {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w t : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hxt : x ≠ t) (_hyz : y ≠ z) (_hyw : y ≠ w)
    (_hyt : y ≠ t) (_hzw : z ≠ w) (_hzt : z ≠ t) (_hwt : w ≠ t) (p : Wff)
    (hcover : p.fv ⊆ [x].toFinset)
    (hlower : lowerClosed (closeNames [x] p) = some literalAxIns3) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axIns3 [x] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_typlower {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hxw : x ≠ w) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) (p : Wff)
    (hcover : p.fv ⊆ [x].toFinset)
    (hlower : lowerClosed (closeNames [x] p) = some literalAxTypeLower) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axTypeLower [x] p hcover
  simpa [literalAxiomSyntax] using hlower

theorem source_ax_sn {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z : Var) (_hxy : x ≠ y)
    (_hxz : x ≠ z) (_hyz : y ≠ z) (p : Wff) (hcover : p.fv ⊆ [x].toFinset)
    (hlower : lowerClosed (closeNames [x] p) = some literalAxSn) : Wff.Valid S p :=
  by
  apply valid_literal_leaf hNF .axSn [x] p hcover
  simpa [literalAxiomSyntax] using hlower

end NFChoice.NFLeafWrappers
