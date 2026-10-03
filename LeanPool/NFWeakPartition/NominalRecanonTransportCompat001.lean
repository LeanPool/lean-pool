/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalRecanonTransportDev

/-! NF weak partition development: NominalRecanonTransportCompat001. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.RecanonTransportDev.TRecanonWff

open NFChoice.SemanticCore

/-! `Wff.neg` is defined as implication into falsum.  The original
type-valued recanonicalization relation exposes the primitive implication
constructor but omitted this derived convenience constructor, even though
the checked certificate emitter uses the corresponding `Prop`-valued helper.
-/


@[expose]
def neg {p q : Wff} (h : TRecanonWff p q) : TRecanonWff (Wff.neg p) (Wff.neg q) :=
  by
  unfold Wff.neg
  exact .imp h (.same _)


end NFChoice.DirectNominalPrf.Nominal.RecanonTransportDev.TRecanonWff
