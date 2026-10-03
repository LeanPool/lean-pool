/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.Examples
public import LeanPool.StructuralGraphClasses.NativeInterfaces
public import LeanPool.StructuralGraphClasses.ForbiddenCharacterization

/-!
# Structural graph classes

Split, cograph and threshold membership share Mathlib's `SimpleGraph` and
native induced embeddings. Finite split graphs are characterized by their
forbidden induced subgraphs and by chordality of the graph and complement;
finite cographs are exactly cotree-representable graphs. Threshold membership
is equivalent to split-and-cograph membership and to its three forbidden
induced subgraphs. Existing chordal results are reused, not duplicated.
-/
