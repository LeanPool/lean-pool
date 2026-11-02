/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Template
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

namespace LongTails.OracleTemplate.Gradient

/-- Ordinary gradient descent with constant step size equal to the reciprocal smoothness. -/
noncomputable def gd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ℝ × E → Algorithm E E E 1
  | (L, x0) => {
      State := E
      initial _ := x0
      query x := (0, x)
      update x reply := x - (1 / L) • reply
      output x := x }

end LongTails.OracleTemplate.Gradient
