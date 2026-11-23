/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.AsymMain

/-!
# Eventually greedy best Egyptian underapproximations

Source: arxiv:2607.28387v2, url:https://arxiv.org/abs/2607.28387v2
Authors: Vjekoslav Kovač, Quanyu Tang
Status: verified
Main declarations: `Egyptian.eventuallyGreedy`, `Egyptian.asymptoticRigidity`
Tags: egyptian-fractions, greedy-algorithms, optimal-control
MSC: 11D68, 49N90
-/

public section

namespace Egyptian

/-- Theorem 1. A common optimal prefix admits uniquely optimal greedy tails
at every positive length, for either ordering convention. -/
theorem eventuallyGreedy : EventuallyGreedy := eventuallyGreedy_proof

/-- Theorem 4. Equality in the extremal growth bound forces eventual
same-index agreement with the optimizing benchmark. -/
theorem asymptoticRigidity : AsymptoticRigidity := fullAsymptoticRigidity

end Egyptian
