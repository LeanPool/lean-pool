/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscTwist

/-!
# Twisting a disc

The radius-preserving twist used to match two marked boundary points in XII (4.3), claim (7).
-/

public section

namespace GraphMinor.GM12

export Surface (unitOf coe_unitOf norm_mul_unitOf unitOf_mul twistParam continuous_twistParam
  twistParam_low twistParam_high twistMap norm_twistMap continuous_unitOf continuous_twistMap
  exists_twist PreservesCircleOrientation.comp preservesCircleOrientation_mul
  exists_circle_pair_move)

end GraphMinor.GM12
