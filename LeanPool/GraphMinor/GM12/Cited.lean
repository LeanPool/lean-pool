/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM07.Defs

/-!
# Earlier results used for distance and connecting subdrawings

The closed-walk restraint theorem is cited in its original form. The statement of XI (8.12)
is already kept in `GM14.Cited` and is used from there. VII (7.5) is
kept over its original proper graphs and forests for the reduction in XII (3.1).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors XI, (8.5), page 97:
"Let $W$ be a closed walk in $\Gamma$ of length $< 2\theta$. Then $\mathrm{ins}(W)$ is a
restraint and $l(\mathrm{ins}(W)) \le l(W)$." -/
def GM11Theorem85Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ (Γ : Drawing S) (two_theta : ℕ) (ins : Drawing S → Set S),
      IsSlope Γ two_theta ins →
      ∀ (u : S) (W : GraphWalk Γ.toGraph u u), W.length < two_theta →
        IsRestraint Γ ins two_theta (insWalk ins Γ W) ∧
          perimeterWalkLength Γ (insWalk ins Γ W) ≤ W.length


/-- Graph Minors XI, (8.13), page 103:
"Let $a, b \in \Sigma$ with $\{a, b\} \cap U(\Gamma) \subseteq V(\Gamma)$; and let $X$ be a
restraint with $a, b \in X$. Suppose that there is no restraint $Y$ with $X \subseteq Y$ and
$l(Y) < l(X)$. Then $X$ includes an $a, b$-optimal restraint." -/
def GM11Theorem813Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ (Γ : Drawing S) (two_theta : ℕ) (ins : Drawing S → Set S),
      IsSlope Γ two_theta ins →
      ∀ (a b : S) (X : Set S), {a, b} ∩ Γ.U ⊆ Γ.V →
        IsRestraint Γ ins two_theta X → a ∈ X → b ∈ X →
        (∀ Y : Set S, IsRestraint Γ ins two_theta Y → X ⊆ Y →
          ¬ perimeterWalkLength Γ Y < perimeterWalkLength Γ X) →
        ∃ Y : Set S, Y ⊆ X ∧ IsOptimalRestraint Γ ins two_theta a b Y

/-- Graph Minors XI, (7.2), page 93:
"If $\Sigma$ is a connected surface, $Z \subseteq \Sigma$, and $F \subseteq Z$ is an $O$-arc
null-homotopic in $Z$, then $F$ bounds a disc $\Delta \subseteq Z$." -/
def GM11Theorem72Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ Z F : Set S, IsOArc F → F ⊆ Z → IsNullHomotopicOArcIn Z F →
      ∃ Δ : Set S, Δ ⊆ Z ∧ IsClosedDisc Δ ∧ subBd Δ = F

/-- Graph Minors VII, (7.5), page 240:
"Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$. Let $k \ge 0$ be an integer,
and let $v = v(\Sigma(a, b, c+1), k)$. Let $G$ be a boundary-linked proper graph in $\Sigma$
with $\alpha(G) \ge 42kv$ and with $|V(G) \cap bd(\Sigma)| \le 2k - 2c - 2$. Let $H$ be a
forest in $\Sigma$ with $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$. Then $H$ is
$G$-feasible."
The boundary-count inequality is written with addition so that natural
subtraction does not allow a negative upper bound. -/
def GM07Theorem75Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S →
    ∀ a b c : ℕ, 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ k : ℕ, ∀ G : Drawing S, G.IsProper → GM07.IsBoundaryLinked G →
      42 * k * GM07.vModel a b (c + 1) k ≤ GM07.alpha G →
      (G.V ∩ bd S).ncard + 2 * c + 2 ≤ 2 * k →
      ∀ H : Drawing S, GM07.IsSurfaceForest H → G.V ∩ bd S = H.V ∩ bd S →
        GM07.IsGFeasible G H

/-- Graph Minors VII, (5.1), page 230:
"If $\Sigma$ is connected and $X \subseteq \Sigma$ is solid and $X \ne \Sigma$, then $X$ is
planar if and only if every $O$-arc included in $X$ is null-homotopic." -/
def GM07Theorem51Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S → ConnectedSpace S →
    ∀ X : Set S, IsSolid X → X ≠ univ →
      (IsPlanar X ↔ ∀ F : Set S, IsOArc F → F ⊆ X → IsNullHomotopicOArc F)

/-- Graph Minors VII, (5.2), page 230:
"If $X \subseteq \Sigma$ is solid and $X$ is planar in $\Sigma + \hat{C}$, where $C$ is a
cuff, then $X$ surrounds $C$ in $\Sigma$ if and only if some $O$-arc included in $X$
surrounds $C$." -/
def GM07Theorem52Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S →
    ∀ C X : Set S, IsCuff C → IsSolid X → GM07.IsPlanarInCappedCuff C X →
      (GM07.SurroundsCuff X C ↔
        ∃ F : Set S, IsOArc F ∧ F ⊆ X ∧ GM07.SurroundsCuff F C)

/-- Graph Minors VII, (5.5), page 231:
"Let $G$ be a proper graph in a connected surface $\Sigma$, and let $Z$ be the closure of the
union of some of the regions of $G$, with $Z \ne \Sigma$. Then $Z$ is planar if and only if
every $G$-normal $O$-arc included in $Z$ is null-homotopic." -/
def GM07Theorem55Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S → ConnectedSpace S →
    ∀ G : Drawing S, G.IsProper → ∀ R : Set (Set S), R ⊆ G.R →
      closure (⋃₀ R) ≠ univ →
      (IsPlanar (closure (⋃₀ R)) ↔
        ∀ F : Set S, G.IsNormal F → IsOArc F → F ⊆ closure (⋃₀ R) → IsNullHomotopicOArc F)

end GraphMinor.GM12
