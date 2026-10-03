/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.RetainedDVRCore

/-!
# Retained source DVR places

The shared constructor lives in `RetainedDVRCore`, so boundary specializations
can project the richer retained data without rebuilding the valuation place.
-/
