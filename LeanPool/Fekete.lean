/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.Fekete.BoundedDefect
public import LeanPool.Fekete.DeBruijnErdos
public import LeanPool.Fekete.Sharpness
public import LeanPool.Fekete.Superadditive
public import LeanPool.Fekete.SupermultiplicativeCounterexample
public import LeanPool.Fekete.Window

/-!
# Nearly subadditive sequences and Fekete's lemma beyond Mathlib

Source: arxiv:1810.11723, doi:10.1007/s10474-020-01071-0, url:https://github.com/Egly443/lean-fekete
Authors: Brian Sanders
Status: verified
Main declarations: `NearlySubadditive.tendsto_atBot_or_exists_tendsto`,
  `NearlySubadditive.tendsto_lim`, `NearlySubadditive.tendsto_atBot_or_exists_tendsto_of_summable`,
  `summable_div_sq_iff_forall_not_tendsto_atTop`, `Subadditive.tendsto_div_atBot`,
  `exists_tendsto_div_of_le_add_const`, `Supermultiplicative.exists_nonneg_not_tendsto_rpow_inv`
Tags: subadditive-sequences, fekete-lemma, de-bruijn-erdos, sequences-and-limits
MSC: 40A05, 39B62
-/

/-!
## Overview

Imports every module of the library: superadditive and supermultiplicative sequences and the
unbounded case of Fekete's lemma (`LeanPool.Fekete.Superadditive`), bounded defects
(`LeanPool.Fekete.BoundedDefect`), subadditivity on a window (`LeanPool.Fekete.Window`), the
de Bruijn–Erdős theorem (`LeanPool.Fekete.DeBruijnErdos`), its sharpness
(`LeanPool.Fekete.Sharpness`), and the counterexample showing that positivity is needed for
supermultiplicative sequences (`LeanPool.Fekete.SupermultiplicativeCounterexample`).
-/
