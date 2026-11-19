/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


module

public import LeanPool.Ratpoints.Proof.BruteForce
public import LeanPool.Ratpoints.Proof.FastSieve

/-!
# Verified bounded-height rational-point search on hyperelliptic curves

Source: url:https://github.com/MichaelStollBayreuth/RatpointsLean/tree/aa11615d33f7b09c063447c1bffd00849db9acba
Authors: Michael Stoll
Status: verified
Main declarations: `Ratpoints.mem_bruteForce_iff`,
  `Ratpoints.Fast.isPoint_and_inRegion_of_mem_fastPoints`, `Ratpoints.Fast.mem_fastPoints_iff`,
  `Ratpoints.Fast.nodup_fastPoints`
Tags: rational-points, hyperelliptic-curves, verified-algorithms, sieves
MSC: 11G30, 11Y50, 68V20
-/
