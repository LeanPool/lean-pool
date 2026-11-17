/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

-- Preserve the original explicit public re-export.
public import LeanPool.Zeta5Irrational.Growth.TablePrime -- shake: keep
public import LeanPool.Zeta5Irrational.Growth.InnerTable.ThreeToSeven
public import LeanPool.Zeta5Irrational.Growth.InnerTable.SevenToEleven
public import LeanPool.Zeta5Irrational.Growth.InnerTable.ElevenToFifteen
public import LeanPool.Zeta5Irrational.Growth.InnerTable.FifteenToTwenty

/-! # The inner piece table on `[3, 20]`

The interval and coefficient data originate in `gen_lean_inner.py`. The independent piece
proofs are grouped by interval so that compilation can share the work across processes and
keep each compiler's proof state smaller. Import this module for every `inPiece` formula.
-/
