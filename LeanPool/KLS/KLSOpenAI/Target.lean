/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.KLSOpenAI.Bridge
public import LeanPool.KLS.KLSOpenAI.LocallyLipschitz
public import LeanPool.KLS.FunctionalInequalities.KLS.Target

/-! # The pinned OpenAI KLS statement, proved through the existing KLS library -/

@[expose] public section

namespace KLSOpenAI

/-- The exact OpenAI `KLSStatement`, without additional hypotheses. -/
theorem kls : OAI.LeanBlast.KLS.KLSStatement :=
  of_conjecture FunctionalInequalities.KLS.kls

/-- The locally Lipschitz L2 density formulation of BKL Theorem 1.1. -/
theorem kls_locallyLipschitz : LocallyLipschitzStatement :=
  locallyLipschitz_of_conjecture FunctionalInequalities.KLS.kls

end KLSOpenAI
