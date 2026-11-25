/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section9e
public import LeanPool.GraphMinor.GM19.Section10b
public import LeanPool.GraphMinor.GM19.CutTwo

/-!
# Numbered results of Sections 5, 10, 11, 14 and 15 of Graph Minors XIX, stated before their proofs

Each statement here is a named `Prop`. The proof of (4.1) takes it as a hypothesis, and the
statement itself is proved in another file.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w}

/-- The standing assumption of Sections 10 and 11 of Graph Minors XIX (page 353): "{S}$ is a
similarly oriented set of $\chi$-coloured paintings, such that if $(\Gamma, \phi)
\in \mathscr{S}$ and $\alpha$ is a $\Phi_\chi$-preserving homeomorphism of $\Sigma_\chi$,
then $\mathscr{S}$ contains the image of $(\Gamma, \phi)$ under $\alpha$". -/
structure IsPaintingClass (χ : ColourScheme S α) (𝒮 : Set (ColouredPainting χ)) : Prop where
  similarly_oriented : ¬ IsOrientableSurface S ∨ ∃ ω : SurfaceOrientation S, ∀ P ∈ 𝒮, ∀ e ∈ P.Γ.E,
    (tilde e).ncard = 3 → ∀ a b c : S, P.Γ.γ e = [a, b, c] → ω.pos (closure e) a b c
  image_mem : ∀ P ∈ 𝒮, ∀ (f : S ≃ₜ S) (P' : ColouredPainting χ), IsFramePreservingHomeo χ.Φ f →
    IsColouredImage f P P' → P' ∈ 𝒮

/-- `ω` lists the labels of the edges of `P` bordering `side`, in order: "let the edges of
$\Gamma_0$ bordering $S$ be $f_1, \dots, f_k$, in order" (Graph Minors XIX, (15.2)). There is at
least one such edge,
since a painting that fits a frame includes the boundary, and the labels lie in `Ω_χ(S)`, because
`P`
is a `χ`-coloured painting. -/
def IsBorderLabels {χ : ColourScheme S α} (P : ColouredPainting χ) (side : Set S) (ω : List α) :
    Prop :=
  ω ≠ [] ∧ (∀ x ∈ ω, x ∈ (χ.ΩS side).E) ∧ ∃ (c : Set S) (f : Fin ω.length → Set S) (u₀ u₁ : S),
    c ∈ cuffs S ∧ side ⊆ c ∧ TangleDatum.BordersInOrder χ P.Γ side c f u₀ u₁ ∧
    (∀ e ∈ P.Γ.E, e ⊆ side → ∃ i, f i = e) ∧ ∀ i, ω[i.val] = P.φ (f i)

/-- **Graph Minors XIX, (5.2)** (page 335): "For every surface $\Sigma$, every frame $\Phi$ in
$\Sigma$ and every integer $n \ge 0$,
there are only finitely many equivalence classes of features in $\Phi$ with size $\le n$." -/
def Theorem52Statement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [T2Space S], IsSurface S → ConnectedSpace S → ∀ (Φ : Frame S)
    (n : ℕ),
    ∃ 𝓕 : Set (Drawing S), 𝓕.Finite ∧ ∀ K : Drawing S, IsFeature Φ K → K.V.ncard + K.E.ncard ≤ n →
      ∃ K₀ ∈ 𝓕, FeatureEquiv Φ K₀ K

/-- The orientation of `Σ` lifts to each fragment: the proof of (5.4) says that the paintings of the
fragment are similarly oriented, "for if $\Sigma_{\chi'}$ is orientable then so is $\Sigma_\chi$".
Here `ψ` is one to
one on `Σ₁` off its boundary, so the fragment takes its orientation from `Σ`, and the lift agrees
with the orientation of `Σ` on each closed disc on which `ψ` is one to one. -/
def FragmentOrientationStatement : Prop :=
  ∀ (S S₁ : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]
    (K : Drawing S)
    (ψ : S₁ → S), IsSurface S → ConnectedSpace S → IsCuttingFragment S K S₁ ψ →
    ∀ ω : SurfaceOrientation S, ∃ ω₁ : SurfaceOrientation S₁, ∀ Δ : Set S₁, IsClosedDisc Δ →
      InjOn ψ Δ → ∀ a b c : S₁, a ∈ discBd Δ → b ∈ discBd Δ → c ∈ discBd Δ → a ≠ b → b ≠ c → a ≠ c →
      (ω₁.pos Δ a b c ↔ ω.pos (ψ '' Δ) (ψ a) (ψ b) (ψ c))

/-- Each capping of `Σ(a, b, c)` is `Σ(a, b, 0)`. -/
def CapModelStatement : Prop :=
  ∀ (a b c : ℕ) (Shat : Type) [TopologicalSpace Shat], IsCappedSurface (SurfaceModel a b c) Shat →
    Nonempty (Shat ≃ₜ SurfaceModel a b 0)

/-- If `Σ(a, b, c)` is orientable then so is `Σ(a, b, c + 1)`, which is a part of it. -/
def ModelOrientationStatement : Prop :=
  ∀ a b c : ℕ, IsOrientableSurface (SurfaceModel a b c) → IsOrientableSurface (SurfaceModel a b
    (c + 1))

/-- **Graph Minors XIX, (5.4)** (page 337): "Let $\chi$ satisfy* **S**$_3$, *and let $(\Gamma_i,
\phi_i)$ $(i = 1, 2, \dots)$ be a
similarly oriented bad sequence for $\chi$. Then for all $n \ge 0$, there exists $h \ge 0$
such that $dist(\Gamma_i) > n$ for all $i \ge h$." -/
def Theorem54Statement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β),
    ConditionS3 χ cap → ∀ P : ℕ → ColouredPainting χ, IsBadSequence χ P → IsSimilarlyOriented χ P →
    ∀ (rad : ∀ i, RadialDrawing cap (P i).Γ) (n : ℕ), ∃ h, ∀ i ≥ h, (n : ℕ∞) < Painting.dist (rad i)

/-- **Graph Minors XIX, (10.3)** (page 355): "Let $\chi$ satisfy $\mathbf{S}_1$, and let $n \ge 1$
be an integer. Then there is a
well-behaved set $\mathscr{C}_1(n)$ of $\chi$-places with the following property. Let
$(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ satisfy $rep(\Gamma),
ord(\mathscr{T}) \ge n > rep(\mathscr{T})$, and $dist(\Gamma) \ge \frac{1}{2}n + 1$. Then
there is a rooted location $\mathscr{L}$ which $n$-isolates $\mathscr{T}$ and for which
$(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}_1(n)$." -/
def Theorem103Statement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat)
    (χ : ColourScheme S β) (hd : χ.IsDisjoint)
    (𝒮 : Set (ColouredPainting χ)), IsPaintingClass χ 𝒮 → ConditionS1.{0, w} Shat → ∀ n : ℕ, 1 ≤ n →
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      (n : ℕ∞) ≤ Painting.rep D.rad → n ≤ D.ord → D.rep < n →
      ((n + 2 : ℕ) : ℕ∞) ≤ 2 * Painting.dist D.rad →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb n D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞

/-- **Graph Minors XIX, (10.4)** (page 356): "Let $\chi$ satisfy $\mathbf{S}_3$, and let $n \ge 1$
be an integer. Then there is a
well-behaved set $\mathscr{C}_2(n)$ of $\chi$-places with the following property. Let
$(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be $n$-flawed in distance. Then there
is a rooted location $\mathscr{L}$ which $(n + 1)$-isolates $\mathscr{T}$ and for which
$(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}_2(n)$." -/
def Theorem104Statement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat)
    (χ : ColourScheme S β) (hd : χ.IsDisjoint)
    (𝒮 : Set (ColouredPainting χ)), IsPaintingClass χ 𝒮 → ConditionS3 χ cap → ∀ n : ℕ, 1 ≤ n →
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      D.IsFlawedInDistance n →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (n + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞

/-- Corrected form of **Graph Minors XIX, (10.5)** (page 357). The statement adds $\mathbf{S}_3$
for the fragment with fewer cuffs. The printed statement reads:
"Let $\chi$ satisfy $\mathbf{S}_4$, and let $n \ge 0$
be an integer. Then there is a
well-behaved set $\mathscr{C}_3(n)$ of $\chi$-places with the following property. Let
$(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be $n$-flawed in freedom. Then there
is a rooted location $\mathscr{L}$ which $(n + 1)$-isolates $\mathscr{T}$ and for which
$(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}_3(n)$." -/
def Theorem105Statement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat)
    (χ : ColourScheme S β) (hd : χ.IsDisjoint)
    (𝒮 : Set (ColouredPainting χ)), IsPaintingClass χ 𝒮 → ConditionS3 χ cap → ConditionS4 χ
      → ∀ n : ℕ,
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      D.IsFlawedInFreedom n →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (n + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞

/-- **Graph Minors XIX, (11.1)** (page 358): "Let $\chi$ satisfy $S_4$, let $S$ be a long side of
$\Phi_\chi$, let $\omega_1, \dots,
\omega_m \in E(\Omega_\chi(S))$ with $m \ge 1$, and let $n \ge 4$. Then there is a
well-behaved set $\mathscr{C}_4(S, (\omega_1, \dots, \omega_m), n)$ of $\chi$-places with
the following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be $(n,
(\omega_1, \dots, \omega_m))$-flawed on $S$. Then there is a rooted location $\mathscr{L}$
which $(m + 1)n$-isolates $\mathscr{T}$, and for which $(\Gamma, \phi, \mathscr{L}) \in
\mathscr{C}_4(S, (\omega_1, \dots, \omega_m), n)$." -/
def Theorem111Statement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat)
    (χ : ColourScheme S β) (hd : χ.IsDisjoint)
    (𝒮 : Set (ColouredPainting χ)), IsPaintingClass χ 𝒮 → ConditionS4 χ →
    ∀ side ∈ χ.Φ.longSides, ∀ ω : List β, ω ≠ [] → (∀ x ∈ ω, x ∈ (χ.ΩS side).E) → ∀ n : ℕ, 4 ≤ n →
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      D.IsFlawedOnSide side n ω →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb ((ω.length + 1) * n) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞

/-- **Graph Minors XIX, (14.1)** (page 375): "Let $\chi, \mathscr{S}, \mathscr{D}$ be as in Section
10, and let $\chi$ satisfy
$\mathbf{S_2}$; let $\omega_0 \in E(\Omega_\chi(2)) \cup E(\Omega_\chi(3))$, and let $m \ge
1, n \ge 4$. Then there is a well-behaved set $\mathscr{C}_5(m, n, \omega_0)$ of $\chi$-places
with the following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be
$(m, n, \omega_0)$-flawed internally. Then there is a rooted location $\mathscr{L}$ which
$(4n \cdot 5^{2m} + 3)$-isolates $\mathscr{T}$, and for which $(\Gamma, \phi, \mathscr{L})
\in \mathscr{C}_5(m, n, \omega_0)$."
The printed `q_0` in the family of places is a misprint for `ω₀`. -/
def Theorem141Statement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat)
    (χ : ColourScheme S β) (hd : χ.IsDisjoint)
    (𝒮 : Set (ColouredPainting χ)), IsPaintingClass χ 𝒮 → ConditionS2 χ cap →
    ∀ (k : ℕ) (ω₀ : β), (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3 ∧ ω₀ ∈ χ.Ω3.E) → ∀ m n : ℕ, 1 ≤ m → 4 ≤ n →
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      D.IsFlawedInternally m n k ω₀ →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (4 * n * 5 ^ (2 * m) + 3) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞

/-- **Graph Minors XIX, (15.2)** (page 380): "15.2. *Let $\chi$ be a colour scheme, and let
$(\Gamma_0, \phi_0)$ be a $\chi$-coloured painting. Then there exist $n \ge 0$ with the following
property. Let $(\Gamma, \phi)$ be a $\chi$-coloured painting, such that $(\Gamma_0, \phi_0)$ and
$(\Gamma, \phi)$ are similarly oriented, and there is no inflation of $(\Gamma_0, \phi_0)$ in
$(\Gamma, \phi)$. Let $\mathscr{T}$ be a tangle in $\Gamma$ with metric $d$, with
$\text{rep}(\mathscr{T}) > \frac{3}{2}n$. Then either*" one of four outcomes holds. The proof of
(4.1) asks for `n` even and
at least `8` ("Choose $n \ge 4$ and even such that 15.2 holds"), and then uses (11.1) with `½n ≥ 4`.
The
proof of (15.2) allows this, since it only asks that `n` is large. -/
def Theorem152Statement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) (cap : IsCappedSurface S Shat) (χ : ColourScheme S β) (P₀ : ColouredPainting χ),
    ∃ n : ℕ, 8 ≤ n ∧ Even n ∧ ∃ ω : Set S → List β,
    (∀ side ∈ χ.Φ.longSides, IsBorderLabels P₀ side (ω side)) ∧ ∀ D : TangleDatum cap χ,
      (¬ IsOrientableSurface S ∨ ∃ o : SurfaceOrientation S, ∀ P ∈ ({P₀, D.P} : Set _), ∀ e ∈ P.Γ.E,
        (tilde e).ncard = 3 → ∀ a b c : S, P.Γ.γ e = [a, b, c] → o.pos (closure e) a b c) →
      (¬ ∃ σv σe, IsColouredInflation χ P₀ D.P σv σe) → 3 * n < 2 * D.rep →
      (∃ r₁ ∈ D.rad.poles, ∃ r₂ ∈ D.rad.poles, r₁ ≠ r₂ ∧ D.vDist r₁ r₂ ≤ n) ∨
      (∃ F : Drawing Shat, F.IsCircuitOf D.rad.G ∧ F.E.ncard ≤ 2 * n ∧
        ((∃ side ∈ χ.Φ.longSides, cap.emb '' side ⊆ D.ins F) ∨
          F.E.ncard < 2 * ((cap.emb '' χ.Φ.V) ∩ D.ins F).ncard)) ∨
      (∃ side ∈ χ.Φ.longSides, D.NoSideMatch side (n / 2) (ω side)) ∨
      (∃ f ∈ P₀.Γ.E, Painting.IsInternal f ∧ D.NoInternalMatch P₀.Γ.E.ncard n (tilde f).ncard
        (P₀.φ f))

/-- How a feature `K` sits in an `O`-arc `F` of `Σ̂`. Either `F` is `K`, and `K` meets `bd(Σ)` in at
most one point, or `K` is a
line with both ends on one cuff, and the rest of `F` lies in the disc pasted onto that cuff. These
are the two cases of
"either $|U(F) \cap bd(\Sigma_\chi)| \le 1$ and $U(F) \subseteq \Sigma_\chi$, or $|U(F) \cap
bd(\Sigma_\chi)| = 2$ and $U(F) \not\subseteq \Sigma_\chi$" (page 354). -/
def IsCutFormOf (cap : IsCappedSurface S Shat) (K : Drawing S) (F : Set Shat) : Prop :=
  (F = cap.emb '' K.U ∧ IsOArc K.U ∧ (K.U ∩ bd S).Subsingleton) ∨
    ∃ s t Θ, Θ ∈ cuffs S ∧ s ≠ t ∧ s ∈ Θ ∧ t ∈ Θ ∧ K.U ∩ bd S = {s, t} ∧ IsLineWithEnds K.U s t ∧
      cap.emb '' K.U ⊆ F ∧ F \ cap.emb '' K.U ⊆ cap.cuffDisc Θ

/-- The feature `K` of the proof of (5.5) lies in a non-null-homotopic `O`-arc `F` of `Σ̂` (Graph
Minors XIX, page 339:
"`U(F)` is non-null-homotopic in `Σ̂`"). -/
def IsCutForm (cap : IsCappedSurface S Shat) (K : Drawing S) : Prop :=
  ∃ F : Set Shat, IsOArc F ∧ ¬ IsNullHomotopicOArc F ∧ IsCutFormOf cap K F

/-- The step of the proof of (5.5) (page 339): "For each fragment $\Sigma_1$ say, $\hat{\Sigma}_1$
is simpler than $\hat{\Sigma}_\chi$ because $U(F)$ is non-null-homotopic in $\hat{\Sigma}$". -/
def CutSimplerStatement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (cap : IsCappedSurface S Shat) (K : Drawing S), IsSurface S →
    (∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v} ∧ IsLineWithEnds
      (closure e) u v) →
    (K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e) → K.U ∩ bd S ⊆ K.V → IsCutForm cap K →
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ IsCutMap ψ K.U
      ∧ HasSheets ψ K ∧
      ∀ (y : Y) (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface
        (connectedComponent y) Shat₁ →
        IsSimplerThan Shat₁ Shat

/-- The step of the proof of (10.2) (page 354): "let $\Sigma'$ be the fragment with $\psi(\Sigma')
\subseteq \Sigma_2$", where `Σ₂` is a disc of `Σ̂`
bounded by `F`, and "`Σ̂_{χ'}` is a sphere". -/
def DiscSideStatement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (cap : IsCappedSurface S Shat) (K : Drawing S) (F Δ : Set Shat), IsSurface S
      → IsCutFormOf cap K F → IsClosedDisc Δ →
    discBd Δ = F → ∀ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y
      → IsCutMap ψ K.U →
    ∃ y : Y, ψ '' connectedComponent y = cap.emb ⁻¹' Δ ∧ ∀ (Shat₁ : Type) [TopologicalSpace Shat₁],
      IsCappedSurface (connectedComponent y) Shat₁ → Nonempty (Shat₁ ≃ₜ SurfaceModel 0 0 0)

/-- The shape of a distance flaw, read on `Σ̂`. The set `𝓓` holds the discs `ins(C)`, for the
circuits `C` of `F`. There are
three shapes, the three bullets on pages 355 and 356: one circuit, with two poles in its disc; a
path from a cuff to a circuit,
with one pole in the disc and the cuff outside; and two circuits with a path between them, with one
pole in each disc. -/
def IsOuterShape (cap : IsCappedSurface S Shat) (K : Drawing S) (𝓓 : Set (Set Shat)) : Prop :=
  (∃ Δ, 𝓓 = {Δ} ∧ IsClosedDisc Δ ∧ IsCutFormOf cap K (discBd Δ) ∧ ∃ Θ₁ ∈ cuffs S, ∃ Θ₂ ∈ cuffs S,
    Θ₁ ≠ Θ₂ ∧
    (cap.cuffDisc Θ₁ ∩ Δ).Nonempty ∧ (cap.cuffDisc Θ₂ ∩ Δ).Nonempty) ∨
  (∃ (Δ : Set Shat) (L : Set S) (s u : S) (Θ Θ' : Set S), 𝓓 = {Δ} ∧ IsClosedDisc Δ
    ∧ discBd Δ ⊆ range cap.emb ∧ Θ ∈ cuffs S ∧
    Θ' ∈ cuffs S ∧ Θ ≠ Θ' ∧ s ∈ Θ ∧ ((L = {u} ∧ s = u) ∨ IsLineWithEnds L s u) ∧
    cap.emb '' K.U = discBd Δ ∪ cap.emb '' L ∧ cap.emb '' L ∩ Δ = {cap.emb u} ∧ L ∩ bd S ⊆ {s} ∧
    discBd Δ ∩ cap.emb '' bd S ⊆ {cap.emb u} ∧ Disjoint (cap.cuffDisc Θ) Δ ∧
      (cap.cuffDisc Θ' ∩ Δ).Nonempty) ∨
  (∃ (Δ₁ Δ₂ : Set Shat) (L : Set S) (a b : S) (Θ₁ Θ₂ : Set S), 𝓓 = {Δ₁, Δ₂} ∧ Δ₁ ≠ Δ₂
    ∧ IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
    discBd Δ₁ ⊆ range cap.emb ∧ discBd Δ₂ ⊆ range cap.emb ∧ ((L = {a} ∧ a = b)
      ∨ IsLineWithEnds L a b) ∧
    cap.emb '' K.U = discBd Δ₁ ∪ discBd Δ₂ ∪ cap.emb '' L ∧ cap.emb '' L ∩ Δ₁ = {cap.emb a}
      ∧ cap.emb '' L ∩ Δ₂ = {cap.emb b} ∧
    Disjoint (cap.emb '' bd S) (discBd Δ₁ ∪ cap.emb '' L) ∧ (discBd Δ₂ ∩ cap.emb '' bd
      S).Subsingleton ∧ Δ₁ ∩ Δ₂ ⊆ {cap.emb a} ∧
    Θ₁ ∈ cuffs S ∧ Θ₂ ∈ cuffs S ∧ Θ₁ ≠ Θ₂ ∧ (cap.cuffDisc Θ₁ ∩ Δ₁).Nonempty ∧
      (cap.cuffDisc Θ₂ ∩ Δ₂).Nonempty)

/-- The steps of the proof of (10.4) (page 357): "let $\Sigma'$ be the fragment with $\psi(\Sigma')
\subseteq \Sigma_0$", "`Σ̂_{χ'} ≅ Σ̂_χ`",
"`c(Σ_{χ'}) < c(Σ_χ)`", and "if $\Sigma_{\chi'}$ is orientable then so is $\Sigma_\chi$". -/
def OuterSideStatement : Prop :=
  ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (cap : IsCappedSurface S Shat) (K : Drawing S) (𝓓 : Set (Set Shat)), IsSurface S
      → IsOuterShape cap K 𝓓 →
    ∀ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y → IsCutMap ψ K.U
      →
    ∃ y : Y, ψ '' connectedComponent y = ⋂ Δ ∈ 𝓓, cap.emb ⁻¹' closure Δᶜ ∧
      (∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface (connectedComponent y) Shat₁
        → Nonempty (Shat₁ ≃ₜ Shat)) ∧
      numCuffs (connectedComponent y) < numCuffs S ∧
      (IsOrientableSurface (connectedComponent y) → IsOrientableSurface S)

end GraphMinor.GM19
