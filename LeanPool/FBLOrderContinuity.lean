/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/



module

public import LeanPool.FBLOrderContinuity.Parameters

/-!
# Order continuity of induced homomorphisms between free Banach lattices

Source: arxiv:2611.00451, url:https://github.com/pedrotradacete/FBLOrderContinuousLH/tree/ee3cde5070125ff2356b7144ff7a940a8dff2a54
Authors: Raúl E. Pariente-Martín, Pedro Tradacete, David Muñoz-Lahoz
Status: verified
Main declarations: `FBLOrderContinuousLH.intro_infty`, `FBLOrderContinuousLH.intro_poe`,
  `FBLOrderContinuousLH.cross_parameter_inclusion`
Tags: banach-lattices, free-banach-lattices, order-continuity, operator-extensions
MSC: 46B42, 46A40, 47B60
-/

/-!
## Attribution and dependency scope

The main formalization is preserved from
`pedrotradacete/FBLOrderContinuousLH` at
`ee3cde5070125ff2356b7144ff7a940a8dff2a54` (Apache-2.0).
The completed proof commit is `167b82ad69724d2ddb2a701fc932e52d445faecc`,
dated October 30, 2026, 22:05:46 UTC. The accompanying manuscript,
[arXiv:2611.00451](https://arxiv.org/abs/2611.00451), was submitted on
October 30 at 23:06:06 UTC. Its declaration on AI use credits GPT-6 Astra
and GPT-6 Sol for the Lean formalization, under the authors’ mathematical
direction; this import records AI provenance for the implementation.

David Muñoz-Lahoz’s BanLat at
`33c4b73fce845c4295614326193d4e52111be762` supplies the additional
free-lattice, duality, quotient, AM-space representation and functional-calculus
prerequisites, also under Apache-2.0. The existing BanLat core in
`LeanPool.OrderClosures` is reused. The added subtype, weak-convergence and finite-product
modules restore the interfaces needed by this dependency closure without
copying that core. The original mathematical namespaces and theorem statements
are retained. The main paper’s acknowledgments credit Timur Oikhberg for
discussions and a simplification of Lemma 4.11.
-/
