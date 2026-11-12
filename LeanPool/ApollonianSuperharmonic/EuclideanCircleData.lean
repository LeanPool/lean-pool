/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Analysis.Complex.Basic
public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: EuclideanCircleData]

/-!
# EuclideanCircleData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A Euclidean circle datum is a pair $E=(z,r)$ consisting of a center
$z\in\mathbb C$ and a strictly positive radius $r\in\mathbb R$.  Its open
disk is $\{x:|x-z|<r\}$ and its boundary circle is
$\{x:|x-z|=r\}$.
-/
structure EuclideanCircleData where
-- BODY
  /-- The complex coordinate of the circle center. -/
  center : Complex
  /-- The strictly positive Euclidean radius. -/
  radius : Real
  radius_pos : 0 < radius

end ApollonianSuperharmonic

end
