/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section4
public import LeanPool.GraphMinor.GM07.Section5a
public import LeanPool.GraphMinor.GM07.Section5b

/-!
# Graph Minors VII, Section 5: The Main Result, Second Version

This file completes Section 5 (pages 230–237) of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254:
- `(5.1)`–`(5.4)` are proved unconditionally in `GraphMinor/GM07/Section5a.lean` (`theorem_5_1`,
  `theorem_5_2`, `theorem_5_3`, `theorem_5_4`).
- `(5.5)`–`(5.7)` are proved unconditionally in `GraphMinor/GM07/Section5b.lean` (`theorem_5_5`,
  `theorem_5_6`, `theorem_5_7`).
- `(5.8)` (`theorem_5_8` in `GM07/CylinderCap.lean`, page 233): grid linkage of `r` paths and `s`
  non-null-homotopic circuits
  in a cylinder.
- `(5.9)` (`theorem_5_9` in `GM07/CuffFinal.lean`, pages 233–237): second version of the main
  feasibility theorem on
  `Σ ≅ Σ(a, b, c)` (`c ≥ 2`, `(a, b, c) ≠ (0, 0, 2)`) for boundary-linked graphs `G` with
  `α(G) > 9k v(Σ, k)` and `|V(G) ∩ C| ≥ 2` for every cuff `C`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

end GraphMinor.GM07
