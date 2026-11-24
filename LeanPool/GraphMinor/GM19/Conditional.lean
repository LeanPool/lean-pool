/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM19.Defs2

/-!
# Statements of Graph Minors XIX, stated before their proofs

Each statement here is a named `Prop`. A theorem that uses one of them takes it as a hypothesis, and
the statement itself is proved in another file.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe u w

/-- **Graph Minors XIX, (6.4)** (page 341):
"For every surface $\Sigma$ with $bd(\Sigma) = \emptyset$, not a sphere, and every drawing
$H$ in $\Sigma$, there is a number $k$ such that for every drawing $G$ in $\Sigma$ with
$rep(G)\ge k$ there is an enlargement of $H$ in $G$." The paper quotes this as Theorem 9.2 of Graph
Minors VII. `GM19.theorem_6_4_proof` proves it. -/
def Theorem64Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S → ConnectedSpace S → bd S = ∅ → ¬ IsSphere S →
    ∀ H : Drawing S, H.IsGM19Drawing → ∃ k : ℕ, ∀ G : Drawing S, G.IsGM19Drawing →
      (k : ℕ∞) ≤ G.rep → ∃ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement H G σv σe

/-- **Graph Minors VII, (5.1)** (page 230):
"If $\Sigma$ is connected and $X \subseteq \Sigma$ is solid and $X \ne \Sigma$, then $X$ is
planar if and only if every $O$-arc included in $X$ is null-homotopic." `GM07.gm07_planar_iff`
proves it. -/
def GM07PlanarIffStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S], IsSurface S → ConnectedSpace S →
    ∀ X : Set S, GM11.IsSolid X → X ≠ univ →
      (GM11.IsPlanar X ↔ ∀ F : Set S, IsOArc F → F ⊆ X → IsNullHomotopicOArc F)

/-- Graph Minors VII, Section 5 (page 230), on `α(G)`: "(It is easy to see that the minimum exists
provided that $\Sigma \not\cong \Sigma(0, 0, c)$ for $c = 0$, $1$, or $2$.)" We need this for a
surface without boundary that is not a sphere. -/
def GM07AlphaExistsStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S], IsSurface S → ConnectedSpace S → bd S = ∅ →
    ¬ IsSphere S → ∀ G : Drawing S, ∃ X : Set S, GM07.IsAlphaCandidate G X

/-- **Graph Minors XIX, (4.1)** (page 333):
"If $\chi$ satisfies $\mathbf{S}_1$--$\mathbf{S}_4$ then it is not orientedly bad." The paper proves
this in Section 15.
It is a hypothesis of `GM19.theorem_3_1_proof`, and Section 15 proves it. We ask for
infinitely many labels, since the proof makes new colour schemes over the same type `β`. This loses
nothing, because `GM19.theorem_3_1_proof` first moves the labels to an infinite type. -/
def Theorem41Statement : Prop :=
  ∀ (S Shat : Type u) [TopologicalSpace S] [TopologicalSpace Shat] (β : Type w) [Infinite β]
    (cap : IsCappedSurface S Shat) (χ : ColourScheme S β),
    ConditionS1.{u, w} Shat → ConditionS2 χ cap → ConditionS3 χ cap → ConditionS4 χ →
    ¬ χ.IsOrientedlyBad

/-- **Graph Minors XIX, (5.5)** (page 338):
"Let $\chi$ satisfy* **S**$_1$, **S**$_3$, *and let* $(\Gamma_i, \phi_i)$ $(i = 1, 2, \dots)$
*be a similarly oriented bad sequence for $\chi$. Then for all $n \ge 0$ there exists $h \ge
1$ such that $rep(\Gamma_i) > n$ for all $i \ge h$." The value of `rep(Γ_i)` is read from any radial
drawing of `Γ_i`. The proof cuts the surface
along a feature, so it needs (5.2) and (5.3). -/
def Theorem55Statement : Prop :=
  ∀ (S Shat : Type u) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β),
    ConditionS1.{u, w} Shat → ConditionS3 χ cap →
    ∀ P : ℕ → ColouredPainting χ, IsBadSequence χ P → IsSimilarlyOriented χ P →
    ∀ (rad : ∀ i, RadialDrawing cap (P i).Γ) (n : ℕ), ∃ h, ∀ i ≥ h, (n : ℕ∞) < Painting.rep (rad i)

/-- **Graph Minors XIX, (6.2)** (pages 339–340):
"For any surface $\Sigma$ there is a number $n$ with the following property. Let $\Phi$ be a
frame in $\Sigma$, and let $\Gamma_1, \Gamma_2$ be paintings in $\Sigma$ fitting $\Phi$,
with $rep(\Gamma_1) \ge n$. Let $\sigma$ be an* ... *inflation of $\Gamma_1$ in $\Gamma_2$
respecting $\Phi$. Then there is a linear inflation $\sigma'$ of $\Gamma_1$ in $\Gamma_2$
respecting $\Phi$, such that $\sigma(e) = \sigma'(e)$ for all $e \in E(\Gamma_1)$, and
$\sigma(v) \subseteq \sigma'(v)$ for all $v \in V(\Gamma_1)$." -/
def Theorem62Statement : Prop :=
  ∀ (S Shat : Type u) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (cap : IsCappedSurface S Shat), IsSurface S → ∃ n : ℕ, ∀ (Φ : Frame S) (Γ₁ Γ₂ : Painting S)
    (rad : RadialDrawing cap Γ₁), Γ₁.Fits Φ → Γ₂.Fits Φ → (n : ℕ∞) ≤ Painting.rep rad →
    ∀ σv σe, IsInflation Γ₁ Γ₂ σv σe → RespectsFrame Φ Γ₁ σe →
      ∃ σv', IsLinearInflation Γ₁ Γ₂ σv' σe ∧ ∀ v ∈ Γ₁.V, σv v ⊆ σv' v

end GraphMinor.GM19
