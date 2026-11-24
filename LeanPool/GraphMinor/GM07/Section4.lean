/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2
public import LeanPool.GraphMinor.GM07.Section3
public import LeanPool.GraphMinor.GM07.Section35
public import LeanPool.GraphMinor.GM07.Section41
public import LeanPool.GraphMinor.GM07.Bridge
import LeanPool.GraphMinor.GM06.DualExists
import LeanPool.GraphMinor.Surface.OpenDisc

/-!
# Graph Minors VII, Section 4: The Main Result, First Version

This file formalizes Section 4 (pages 221–230) of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254:
- `(4.1)` (`theorem_4_1`): characterization of `G`-feasibility of a forest `H` in a closed disc `Δ`
  (Theorem (3.6) of Graph Minors VI, `GM06.Statement36`, stated in the language of `G`-normal
  proper `I`-arcs);
- `(4.2)` (`theorem_4_2`): an open connected subset `Y` of a connected boundaryless surface `Σ` in
  which every `O`-arc bounds a closed disc is either `Σ` (when `Σ` is a sphere) or an open disc
  (proved unconditionally from `Surface.open_disc`);
- `(4.3)` (`theorem_4_3`, in `Section43.lean`): existence of `v + 1` internally vertex-disjoint
  paths from a cuff `C` to
  `bd(Σ) - C` when every short boundary-disjoint `G`-normal `O`-arc is null-homotopic;
- `(4.4)` (`theorem_4_4`, in `Section44.lean`): moving a forest `H₀` by a homotopy off a forest `L`
  when
  cutting along `U(L)`;
- `(4.5)` (`theorem_4_5`): pullback and pushforward of forests and homoplasties across the
  surjection `φ : Σ' → Σ` obtained by cutting along `U(J)`;
- `vSurface_le_vModel`: unconditional bound `vSurface S k ≤ vModel a b c k`
  when `Nonempty (S ≃ₜ SurfaceModel a b c)`;
- `(4.6)`: first version of the main feasibility theorem on a connected surface with at least two
  cuffs. It is `theorem_4_6` in `GM07/Section46Final.lean`, because its proof needs much of this
  file.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Graph Minors VII, (4.1) (page 221; Theorem (3.6) of Graph Minors VI, `GM06.Statement36`):
"(4.1) *Let $G$ be a proper graph in a closed disc $\Delta$ and let $H$ be a forest in $\Delta$
with $V(H) \cap bd(\Delta) = V(G) \cap bd(\Delta)$. Then $H$ is $G$-feasible if and only if for
every $G$-normal proper $I$-arc $F$ with ends $s, t$ say, $|V(G) \cap (F - \{s, t\})| \ge |\Lambda|$
where $C_1, C_2$ are the two components of $bd(\Delta) - \{s, t\}$, and $\Lambda$ is the set of
vertex sets of the components of $H$ which intersect both $C_1$ and $C_2$, and contain neither $s$
nor $t$.*" -/
theorem theorem_4_1_proof
    [T1Space S] (hS : IsSurface S) (hDisc : IsClosedDisc (univ : Set S))
    (G H : Drawing S) (hG : G.IsProper) (hH : IsSurfaceForest H)
    (hbd : H.V ∩ bd S = G.V ∩ bd S) :
    IsGFeasible G H ↔
      ∀ (F : Set S) (s t : S) (C₁ C₂ : Set S),
        G.IsNormal F → IsProperIArc F → IsLineWithEnds F s t →
        componentsIn (bd S \ {s, t}) = {C₁, C₂} → C₁ ≠ C₂ →
        {V₀ : Set S | ∃ H' : Drawing S,
          GM06.IsGraphComponent H'.toGraph H.toGraph ∧ V₀ = H'.V ∧
          (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀}.ncard ≤
          (G.V ∩ (F \ {s, t})).ncard :=
  discFeasibilityArcTranslation S hS hDisc G H hG hH hbd

/-- Graph Minors VII, (4.2) (page 222):
"(4.2) *Let $\Sigma$ be a connected surface with $bd(\Sigma) = \emptyset$, and let
$Y \subseteq \Sigma$ be connected and open. Suppose that every $O$-arc included in $Y$ bounds a
disc included in $Y$. Then either $\Sigma$ is a sphere and $Y = \Sigma$, or $Y$ is an open disc.*"
Proved unconditionally from `Surface.open_disc` and `isClosedSurface_of_bd_eq_empty`. -/
theorem theorem_4_2_proof (hS : IsSurface S) [hConn : ConnectedSpace S] (hbd : bd S = ∅)
    (Y : Set S) (hY_conn : IsConnected Y) (hY_open : IsOpen Y)
    (hY_oarc : ∀ F : Set S, IsOArc F → F ⊆ Y →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ⊆ Y) :
    (IsSphere S ∧ Y = univ) ∨ IsOpenDisc Y := by
  have hS_closed : IsClosedSurface S := isClosedSurface_of_bd_eq_empty hS hbd
  refine Surface.open_disc S Y hS_closed hConn hY_conn hY_open fun F hFY hF => ?_
  obtain ⟨Δ, hΔ, hbdΔ, hΔY⟩ := hY_oarc F hF hFY
  exact ⟨Δ, hΔY, hΔ, hbdΔ⟩

/-- When `S ≃ₜ SurfaceModel a b c`, `vSurface S k ≤ vModel a b c k`. -/
theorem vSurface_le_vModel {a b c : ℕ}
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) (k : ℕ) :
    vSurface S k ≤ vModel a b c k :=
  Nat.sInf_le ⟨a, b, c, he, rfl⟩

end GraphMinor.GM07
