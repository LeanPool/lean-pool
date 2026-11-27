/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Astala
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Corollary2.Norm
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Corollary2.NormTorus
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Hessian
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Quasiconvex

/-!
# Iwaniec's conjecture on the Beurling–Ahlfors norm

Source: arxiv:2609.28311, url:https://github.com/vltanh/lean4-iwaniec/tree/f310788a42a6935fd9e24092f9df95e2682afb3b
Authors: The-Anh Vu-Le
Status: verified
Main declarations: `Agazzi.theorem1`, `Agazzi.corollary2_norm`
Tags: singular-integrals, quasiconvexity, fourier-multipliers, beltrami-equation
MSC: 42B20, 49J45, 30C62
-/

/-!
## Upstream Lean sources

The theorem proofs come from The-Anh Vu-Le's `lean4-iwaniec`, commit
`f310788a42a6935fd9e24092f9df95e2682afb3b`. The imported support modules retain their
upstream authorship and Apache 2.0 license. They come from the following pinned dependencies.

* `lean4-calculus-of-variations`, `a3778e447c557dd8eb81b84f47db4aa9ed0070d0`.
* `lean4-harmonic-analysis`, `4c9fb088fe3ed7452430f825730e3d23fa4d0a6a`.
* `lean4-banach-probability`, `dc3966ce34fbc31b2936a0ca9b8a50356d690ae1`.

Lean Pool relocated module paths, ported the proofs to its current toolchain and library
pins, and applies its warning, style, performance and trust checks to the imported sources.
-/
