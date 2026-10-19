/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalGraphColouring.Konig.Basic
public import LeanPool.ClassicalGraphColouring.Galvin.Galvin
public import LeanPool.ClassicalGraphColouring.Orientations.GallaiRoy
public import LeanPool.ClassicalGraphColouring.Spectrum.Bounds

/-!
# Classical graph colouring through lists, orientations and spectra

Source: doi:10.1006/jctb.1995.1011, url:https://github.com/jtraverso/galvin-dinitz/tree/0aa98fc17e1e96ec408f7bad3198ce37a08d26fc
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `Konig.lineGraph_colorable_of_colorable_two`, `Galvin.galvin`, `GallaiRoy.colorable_of_orientation`, `SpectralBounds.hoffman_chromatic`
Tags: graph-theory, bipartite-graphs, edge-colouring, list-colouring, stable-matchings, orientations, spectral-graph-theory
MSC: 05C15, 05C70, 91B68, 05C50
-/

/-!
## Mathematical overview

Kőnig's edge-colouring theorem supplies a proper colouring of a finite bipartite graph with
`Δ(G)` colours. Galvin's orientation and kernel argument upgrades this to a colouring from
arbitrary edge lists of size at least `Δ(G)`. The development also proves the Gale–Shapley
stable-matching theorem used to construct the kernels and deduces the Dinitz array theorem.
Gallai–Hasse–Roy–Vitaver relates proper colourings to longest directed paths in orientations.
Its path predicate is bridged to Lean Pool's `Digraph.IsSimplePath` API.
Wilf's and Hoffman's bounds compare the chromatic and independence numbers with adjacency
eigenvalues. Two interface corollaries below transfer the spectral colouring bounds to directed
path statements.

The proof of Kőnig's theorem reuses `LeanPool.Vizing` directly. The matching-cover and finite
poset results from the registered Kőnig source are already available in
`LeanPool.ClassicalMatchingFactors` and are not duplicated here.
-/

@[expose] public section

open SimpleGraph

namespace ClassicalGraphColouring

/-- Hoffman's chromatic lower bound also bounds the directed path length of every orientation. -/
theorem hoffman_le_directed_path_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
    (hE : G.edgeSet.Nonempty) (o : V → V → Prop) (ho : GallaiRoy.IsOrientation G o)
    (k : ℕ) (hk : ∀ (m : ℕ) (f : Fin m → V), GallaiRoy.IsDirectedPath o f → m ≤ k) :
    1 - (⨆ i, hA.eigenvalues i) / (⨅ i, hA.eigenvalues i) ≤ k :=
  SpectralBounds.hoffman_chromatic G hA hE
    (GallaiRoy.colorable_of_orientation G o ho k hk)

/-- Wilf's spectral colouring bound gives an orientation with the same bound on directed paths. -/
theorem exists_orientation_of_wilf_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian) :
    ∃ o : V → V → Prop, GallaiRoy.IsOrientation G o ∧
      ∀ (m : ℕ) (f : Fin m → V), GallaiRoy.IsDirectedPath o f →
        m ≤ ⌊⨆ i, hA.eigenvalues i⌋₊ + 1 :=
  GallaiRoy.exists_orientation_of_colorable G _ (SpectralBounds.wilf G hA)

end ClassicalGraphColouring
