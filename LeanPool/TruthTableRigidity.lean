/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

module

public import LeanPool.TruthTableRigidity.Borel
public import LeanPool.TruthTableRigidity.Inverse
public import LeanPool.TruthTableRigidity.Main

/-!
# Baire-measurable rigidity of the truth-table degrees

Source: arxiv:2610.16059, url:https://github.com/bjoernkjoshanssen/tt-auto/tree/3190d8d1a78e709297423d1343f68395127be5de
Authors: Bjørn Kjos-Hanssen
Status: verified
Main declarations: `TT.eq_refl_of_inducedOn_comeager`, `TT.eq_refl_of_inducedByBaireMeasurable'`
Tags: truth-table-reducibility, computability-theory, rigidity, baire-category
MSC: 03D28, 03B35
-/
