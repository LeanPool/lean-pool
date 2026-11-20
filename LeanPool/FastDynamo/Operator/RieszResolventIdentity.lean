/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.Riesz

/-!
# The resolvent identity for bundled-domain operators

The chosen inverse in `HasResolventOn` takes ambient states into the bundled
operator domain.  Its two inverse equations already imply the usual
two-parameter resolvent identity; no additional compatibility assumption
between the chosen inverses at different spectral parameters is needed.

The domain-valued identity `HasResolventOn.inv_sub_inv` and the ambient identity
`HasResolventOn.stateResolvent_sub_stateResolvent` are proved in
`FastDynamo/Operator/Domain.lean`. They supply the algebra for Riesz projections.
-/
