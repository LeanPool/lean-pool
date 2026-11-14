/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/-!
# Source attribution

This project imports the main-result dependency closure of Jason Davies's
CCDN Dimension Growth formalization at commit
`bb025e7207f3a35a21b898629f5678b72aa7e44f`.
Lean Pool changed module paths and ported the proofs to its pinned toolchain.
Original copyright and license notices are retained in the source files.

The upstream NOTICE reads:

CCDN Dimension Growth

This project contains work from rwst/Subspace-Theorems, by Ralf Stephan,
licensed under Apache-2.0. The vendored transitive dependency of
ArithmeticHeights.BombieriVaaler (vendor/bombieri-vaaler) comes from commit
09835cb23557ae5ae0cf55a9c4ab9055f5d60338.
Original copyright and license notices are retained in all source files.
Two compatibility changes for Lean/Mathlib 4.35 are recorded in
vendor/bombieri-vaaler/lean-4.35.patch and upstream.json.

This project contains work adapted from AlexKontorovich/PrimeNumberTheoremAnd,
by the PrimeNumberTheoremAnd contributors, licensed under Apache-2.0.
vendor/mertens/Mertens.lean adapts the first Mertens theorem from
PrimeNumberTheoremAnd/IEANTN/Mertens.lean at commit
c39a751132c88b6e8080b74c74023fd95b3d8be0. The upstream file carries no
copyright header; the adapted file records its source at the top, and the
changes are listed in vendor/mertens/upstream.json. A copy of the Apache
License 2.0 is in vendor/mertens/LICENSE.

The cited paths refer to the pinned upstream repository:
https://github.com/jasondavies/ccdn-dimension-growth/tree/bb025e7207f3a35a21b898629f5678b72aa7e44f
The Apache-2.0 license is preserved in Lean Pool's root LICENSE.
-/
