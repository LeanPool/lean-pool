/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.GaoLeungProblem
public import LeanPool.OrderClosures.WeaklyFatou


/-!
# Order closure, order adherence and Fatou norms

Source: arxiv:2609.06689, url:https://github.com/pedrotradacete/OrderClosures/tree/6189ba7134f6975e7d8e4c8c093a9869d03a769c
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete, David Muñoz-Lahoz
Status: verified
Main declarations: `OrderClosures.exists_weaklyFatou_not_equivalent_fatou`
Tags: banach-lattices, order-convergence, fatou-norms, transfinite-constructions
MSC: 46B42, 46A40, 46A19
-/

/-!
## Scope, attribution and provenance

Imported from `pedrotradacete/OrderClosures` at
`6189ba7134f6975e7d8e4c8c093a9869d03a769c` (Apache-2.0). The public paper
[arXiv:2609.06689](https://arxiv.org/abs/2609.06689), submitted September 6, 2026,
records the completed formalization. The August 26 completion commit is
`5f6833f1934ac915302189e19bf083115f655be3`.

The `BanLat` subtree retains the dependency closure and reusable prerequisites
from David Muñoz-Lahoz's [BanLat](https://github.com/davidmunozlahoz/banlat/tree/b00e59836016aa1099b8011add6b07385e66428e)
at `b00e59836016aa1099b8011add6b07385e66428e`, also Apache-2.0. Unused operator,
projection-band and locally-solid representation developments are omitted.
`BanLat.LatticeSeminorm` extracts the necessary seminorm interface from
`BanLat.LocallySolid.WithSeminorms`; `BanLat.Pi` retains pointwise products.

The paper credits Jaume de Dios Pont for an earlier Lean formalization of
Section 3. It credits Michael Elliott for the unpublished weak Fatou example
previously announced by Anthony Wickstead. These mathematical and formalization
credits are retained independently of the authors of this implementation.

The paper's acknowledgments explicitly attribute the Lean verification to AI
systems, with human direction and review. The AI provenance classification
reflects that first-party account of the main proofs; the imported BanLat
prerequisites retain their authorship credit. The Lean Pool port and proof
repairs were performed with Codex.

For the solid-set tower result, Paper Theorem 2.6 specifies a generating set
of cardinality kappa. The Lean endpoint additionally proves that the minimum
solid generator number is exactly kappa. That exact-minimum conclusion is a
strengthening proved by the formalization, rather than part of the paper's
stated theorem.

`gao_counterexample` states the order-complete `C(K)` construction with a
norm-closed separable sublattice whose only order-closed vector-sublattice
extension is all of `C(K)`. It does not itself state the negation of the
Gao-Leung conjecture: the paper derives that consequence by a
cardinality argument. The registered informal statement describes the actual
Lean endpoint.
-/
