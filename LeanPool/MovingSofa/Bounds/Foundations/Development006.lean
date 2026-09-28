/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development003

public import LeanPool.MovingSofa.Cap.Foundations.Development007
public import LeanPool.MovingSofa.Convex.Foundations.Development004
/-!
# Moving sofa: related mathematical developments

* `Bounds.Upper.Q`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Bounds / Upper / Q
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The cap-tail upper-bound functional Q assembled from cap area, tail arcs and endpoint
segments. -/
def upperBoundQ (T : CapTailSpace) : ℝ :=
  ClassicalResults.area (T.cap.val.val : Set Point) +
    convexArcArea T.leftBody (3 * Real.pi / 2)
      (3 * Real.pi / 2 + paperGerverConstants.2.2) +
    segmentArea (rightLeftTailArcs T.rightBody T.leftBody).2.endPoint
      (distinguishedCapSides T.cap.val).2.corner -
    curveAreaFunctional (capMiddleBV T.cap) +
    segmentArea (distinguishedCapSides T.cap.val).1.corner
      (rightLeftTailArcs T.rightBody T.leftBody).1.startPoint +
    convexArcArea T.rightBody (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)

end MovingSofa

end

end

end
