/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

module

public import LeanPool.HyperellipticCurves.Count.Arithmetic

/-!
# Chabauty–Coleman bounds for odd-degree hyperelliptic curves

Source: doi:10.1112/S0010437X06002168, url:https://github.com/MichaelStollBayreuth/HyperellipticCurves/tree/a541f7182de678e07edcccc7a307c777cecfc8fe
Authors: Michael Stoll
Status: verified
Main declarations: `ChabautyColeman.main_affine_rat_of_rank_le`,
  `ChabautyColeman.NumberFieldBase.main_affine_numberField`,
  `ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField`
Tags: hyperelliptic-curves, chabauty-coleman, rational-points, formal-groups, p-adic-analysis
MSC: 11G30, 14G05, 14H25
-/

/-!
# The Chabauty–Coleman bound for odd-degree hyperelliptic curves

Adapted from MichaelStollBayreuth/HyperellipticCurves at commit
`a541f7182de678e07edcccc7a307c777cecfc8fe`. The Apache-2.0 source and author
attribution are retained in every module. The proofs were produced by Claude models
under Michael Stoll’s mathematical direction and review.

This imports the 189-module dependency closure of the rational and number-field
Chabauty–Coleman bounds; independent archive results and the comparator harness are
not included. The Jacobian is modelled by the ideal class group of the affine
coordinate ring, rather than by an algebraic variety.
-/
