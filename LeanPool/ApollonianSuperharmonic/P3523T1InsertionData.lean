/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Finset.Card


-- [TABLET NODE: P3523T1InsertionData]

/-!
# P3523T1InsertionData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an arbitrary label set $I$, insertion data consist of a record
with four independently chosen fields:


- $\mathrm{steps}$ is an arbitrary finite list of ordered triples
$(a,d,b)\in I\times I\times I$. The list may be empty, and its
entries and their component labels may repeat.

- $\mathrm{faces}$ assigns to every $n\in\mathbb N$ an arbitrary
finite set of finite subsets of $I$.

- $\mathrm{vertices}$ assigns to every $n\in\mathbb N$ an
arbitrary finite subset of $I$.

- $\mathrm{boundary}$ assigns to every $n\in\mathbb N$ an
arbitrary finite set of finite subsets of $I$.

All three sequences are defined for every natural number, including
$n\ge |\mathrm{steps}|$; no constancy after the end of the list is
required. The field names indicate their intended roles in insertion
schedules only. Members of $\mathrm{faces}(n)$ and
$\mathrm{boundary}(n)$ are not required to have cardinality three or
two, respectively. No distinctness of step labels, membership of
labels from the steps, faces, or boundary in $\mathrm{vertices}(n)$,
coherence between fields or stages, or geometric correctness is
imposed. Such properties of the actual insertion schedule are
supplied separately by its construction and incidence results, not
by this data carrier.
-/
structure P3523T1InsertionData (I : Type) where
-- BODY
  /-- The finite schedule of triples naming an old edge and its inserted label. -/
  steps : List (I × I × I)
  /-- The finite face family at each stage of the schedule. -/
  faces : Nat → Finset (Finset I)
  /-- The finite set of present labels at each stage. -/
  vertices : Nat → Finset I
  /-- The finite boundary-edge family at each stage. -/
  boundary : Nat → Finset (Finset I)

end ApollonianSuperharmonic

end
