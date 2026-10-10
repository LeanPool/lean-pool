/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.Basic

/-!
# Scott's measurement representation theorems

Source: url:https://github.com/catskillsresearch/scott1964
Authors: Lars Warren Ericson
Status: verified
Main declarations: `Scott1964.MeasurementStructures.theorem_4_1_vector`
Tags: measurement-theory, utility-representation, qualitative-probability
MSC: 91B16, 91B06, 60A05, 52A20
-/

/-!
# Scott’s measurement structures and linear inequalities

Ported from catskillsresearch/scott1964 at
591e8a6a5d7d1ebf4cc761b4a1cb749b6480dfeb (Apache-2.0).
Lars Warren Ericson directed and reviewed the AI-generated Lean development.

The third-party source paper is cited, not redistributed. Its copyright remains
with its publisher. The infinite probability equivalence is a modern reconstruction
under an explicit generalized Kelley condition, not a published theorem of Scott.
-/
