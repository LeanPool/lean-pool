/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.EyeInductionParameters
public import LeanPool.GraphMinor.GM16.ProperArrangementFacts

public import LeanPool.GraphMinor.GM15.Section2
public import LeanPool.GraphMinor.GM15.Section3
public import LeanPool.GraphMinor.GM15.Section4
public import LeanPool.GraphMinor.GM15.Section5
public import LeanPool.GraphMinor.GM15.Section6
import LeanPool.GraphMinor.GM15.Section3Parallel
import LeanPool.GraphMinor.GM15.Section3Given
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
public import LeanPool.GraphMinor.GM14.BridgeFacts
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Section4SpanSeparation
import LeanPool.GraphMinor.GM12.Section5Final

import LeanPool.GraphMinor.GM12.Section6

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM14.Bridge

import LeanPool.GraphMinor.GM15.Section3Crosscap
import LeanPool.GraphMinor.GM14.DiscArrangement

/-!
# Graph Minors XV, Section 7: The Main Proof

This file formalizes Section 7 ("The main proof", pages 134–145) of N. Robertson and P. D. Seymour,
*Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148, and proves the main
inductive step **Graph Minors XV, (1.2)** (`GM15Theorem12Statement`, `theorem_1_2`, page 115):
- **Outcomes `(S1)`, `(S2)`, `(S3)`** (`Section7S1`, `Section7S2`, `Section7S3`, page 135).
- **Graph Minors XV, (7.1)** (`GM15Theorem71Statement`, page 135): truncating a `(λ, μ)`-flat
  `Σ`-span of order `≥ θ` with `k` eyes at distance `≥ θ` to order `θ`.
- **Graph Minors XV, (7.2)** (`GM15Theorem72Statement`, page 135): disjointness of the atom
  zones `Z_i` and bridge unions `J_i`.
- **Graph Minors XV, (7.3)** (`GM15Theorem73Statement`, page 136): if clearing a `(3μ + 3)`-zone
  `Λ` yields a rigid drawing for which `Λ` is an eye in `G₀`, then `(S1)` holds.
- **Graph Minors XV, (7.4)** (`GM15Theorem74Statement`, `theorem_7_4`, page 137): if `(S1)` does not
  hold, `G₀` has a `T`-local 3-segregation `S₀` with an arrangement in `Σ` compatible with `H`
  (proved from `(7.3)` and Graph Minors XIV, `(10.1)`).
- **Graph Minors XV, (7.5)** (`GM15Theorem75Statement`, page 138): existence of `(3β + 3)`-zones
  `Λ_i` and `α₀`-normal closed discs `Δ_i` around the `k` eyes.
- **Graph Minors XV, (7.6)** (`GM15Theorem76Statement`, page 139): mutual disjointness of
  `G_1*, ..., G_k*`.
- **Graph Minors XV, (7.7)** (`GM15Theorem77Statement`, page 139): if no `(G_i*, Ω_i*)` has a
  crooked transaction of cardinality `π`, then `(S3)` holds.
- **Graph Minors XV, (7.8)** (`GM15Theorem78Statement`, `theorem_7_8`, page 142): if some
  `(G_i*, Ω_i*)` has a crooked transaction of cardinality `π`, then `(G₀ ∪ J_i, Ω_i)` has a
  transaction `P` with free ends in `T₁` that is a crosscap transaction of size `φ`, a leap
  transaction of size `τ₁`, or a doublecross transaction of size `τ₂` (proved from `(7.5)`, `(6.2)`,
  and Graph Minors X, `(12.2)`).
- **Graph Minors XV, (7.9)** (`GM15Theorem79Statement`, page 143): if `P` is a crosscap transaction
  of cardinality `φ`, then `(S2)` holds.
- **Graph Minors XV, (7.10)** (`GM15Theorem710Statement`, page 143): `P` is not a leap transaction
  of cardinality `τ₁`.
- **Graph Minors XV, (7.11)** (`GM15Theorem711Statement`, page 143): if `P` is a doublecross
  transaction of cardinality `τ₂`, then `(S1)` holds.
- **Graph Minors XV, (1.2)** (`GM15Theorem12Statement`, `theorem_1_2`, page 115): main inductive
  step of Graph Minors XV.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

export _root_.GraphMinor.GM14
  (exists_isHPathWithEnds_of_component_attachments exists_isHPathWithEnds_of_isBridge)

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Section 7 Constructions and Outcomes `(S1)`, `(S2)`, `(S3)` -/

/-- Outcome `(S1)` of Graph Minors XV, Section 7 (page 135):
"There is a $(\lambda', \mu)$-flat $\Sigma$-span of order $\theta'$ with $k + 1$ eyes,
mutually at distance $\theta'$." -/
def Section7S1 (S : Type w) [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (θ_star : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (k μ lam' θ' : ℕ) : Prop :=
  ∃ (H' : Drawing S) (η' : SpanEmbedding H' G)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ) (r : Fin (k + 1) → Set S),
    IsFlatSpan G H' η' θ_star θ' lam' μ T_star T' ∧
    HasTangleMetric H' θ' T' d' ∧
    Injective r ∧
    (∀ i : Fin (k + 1), IsDrawingEye G H' η' θ' T' (r i)) ∧
    (∀ i j : Fin (k + 1), i ≠ j → d' (r i) (r j) = θ')

/-- Outcome `(S2)` of Graph Minors XV, Section 7 (page 135):
"There is a $\Sigma'$-span of order $\phi$, where $\Sigma'$ is a surface obtained by adding a
crosscap to $\Sigma$." -/
def Section7S2 (S : Type w) [TopologicalSpace S]
    (G : Graph α β) (θ_star : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (φ : ℕ) : Prop :=
  ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
    IsObtainedByAddingCrosscap S S' ∧
    ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
      IsSigmaSpan G H' η' θ_star φ T_star T'

/-- Outcome `(S3)` of Graph Minors XV, Section 7 (page 135):
"There is a $\mathcal{T}^*$-central segregation of $G$ of type $(\rho, k)$ with an arrangement
in $\Sigma$." -/
def Section7S3 (S : Type w) [TopologicalSpace S]
    (G : Graph α β) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (p k : ℕ) : Prop :=
  ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
    IsCentralSegregation G T_star S_seg ∧
    IsSegregationOfType G p k S_seg ∧
    IsSurfaceArrangement S_seg α_disc α_pt

/-- Outcome (S3) retaining the properness of the arrangement constructed in XV (7.7). -/
abbrev Section7ProperS3 (S : Type w) [TopologicalSpace S]
    (G : Graph α β) (T_star : Set (Hypergraph α β × Hypergraph α β)) (p k : ℕ) : Prop :=
  ∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
    IsCentralSegregation G T_star 𝒮 ∧
    IsSegregationOfType G p k 𝒮 ∧ GM16.IsProperArrangement 𝒮 disc pt

theorem Section7ProperS3.toSection7S3 {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {T_star : Set (Hypergraph α β × Hypergraph α β)} {p k : ℕ}
    (h : Section7ProperS3 S G T_star p k) : Section7S3 S G T_star p k := by
  obtain ⟨𝒮, disc, pt, hCentral, hType, hProper⟩ := h
  exact ⟨𝒮, disc, pt, hCentral, hType, hProper.1⟩

/-- For `1 ≤ i ≤ k`, `Z_i` is the union of all atoms `a` of `H` with `d(r_i, a) ≤ θ' + 12μ + 14`
(Graph Minors XV, Section 7, page 135). -/
def eyeAtomZone {S : Type w} [TopologicalSpace S]
    (H : Drawing S) (d : Set S → Set S → ℕ) (θ' μ : ℕ) (r_i : Set S) : Set S :=
  ⋃ a ∈ {a ∈ H.A | d r_i a ≤ θ' + 12 * μ + 14}, a

/-- For `1 ≤ i ≤ k`, `J_i` is the union of all bridges `B` of `η(H)` in `G` with
`V(B) ∩ η(V(H) ∩ Z_i) ≠ ∅` (Graph Minors XV, Section 7, page 135). -/
def eyeBridgeUnion {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) (θ' μ : ℕ) (r_i : Set S) : Graph α β :=
  subgraphSUnion G
    {B : Graph α β | IsBridge G η.imageGraph B ∧
      (V(B) ∩ (η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ r_i))).Nonempty}

/-- `J₀` is the union of all bridges `B` of `η(H)` in `G` such that
`V(B) ∩ (Z₁ ∪ ... ∪ Z_k) = ∅` (Graph Minors XV, Section 7, page 135). -/
def remainingBridgeUnion {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) {k : ℕ} (θ' μ : ℕ) (r : Fin k → Set S) : Graph α β :=
  subgraphSUnion G
    {B : Graph α β | IsBridge G η.imageGraph B ∧
      Disjoint V(B) (⋃ i : Fin k, η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ (r i)))}

/-- Edges of the union of the bridges incident with an eye zone. -/
theorem eyeBridgeUnion_edgeSet {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) (θ' μ : ℕ) (r_i : Set S) :
    E(eyeBridgeUnion G H η d θ' μ r_i) =
      ⋃ B ∈ {B : Graph α β | IsBridge G η.imageGraph B ∧
        (V(B) ∩ (η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ r_i))).Nonempty}, E(B) := by
  unfold eyeBridgeUnion
  exact edgeSet_subgraphSUnion fun _ hB => hB.1.2.1

/-- Edges of the union of the bridges disjoint from all eye zones. -/
theorem remainingBridgeUnion_edgeSet {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) {k : ℕ} (θ' μ : ℕ) (r : Fin k → Set S) :
    E(remainingBridgeUnion G H η d θ' μ r) =
      ⋃ B ∈ {B : Graph α β | IsBridge G η.imageGraph B ∧
        Disjoint V(B) (⋃ i : Fin k, η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ (r i)))}, E(B) := by
  unfold remainingBridgeUnion
  exact edgeSet_subgraphSUnion fun _ hB => hB.1.2.1

/-- `G₀ = η(H) ∪ J₀` (Graph Minors XV, Section 7, page 136). -/
def section7G0 {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) {k : ℕ} (θ' μ : ℕ) (r : Fin k → Set S) : Graph α β :=
  subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r}

/-! ## Statements and Proofs of `(7.1)`–`(7.11)` -/

/-- Statement of Graph Minors XV, (7.1) (page 135):
"There is a $(\lambda, \mu)$-flat $\Sigma$-span of order $\theta$, with $k$ eyes mutually at
distance $\theta$." -/
def GM15Theorem71Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G)
    (θ_star θ₀ θ lam μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d₀ : Set S → Set S → ℕ),
    IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ →
    HasTangleMetric H₀ θ₀ T₀ d₀ →
    2 ≤ lam → 4 * lam + μ + 2 ≤ θ → 4 ≤ θ → θ ≤ θ₀ →
    HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ →
    ∃ (H : Drawing S) (η : SpanEmbedding H G)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (r : Fin k → Set S),
      IsFlatSpan G H η θ_star θ lam μ T_star T ∧
      HasTangleMetric H θ T d ∧
      Injective r ∧
      (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) ∧
      (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ)

/-- **Graph Minors XV, (7.1)** (page 135):
Truncating a `(λ, μ)`-flat `Σ`-span `H₀, η₀, T₀` of order `θ₀ ≥ θ` with `k` eyes at distance `≥ θ`
to order `θ` yields a `(λ, μ)`-flat `Σ`-span of order `θ` with `k` eyes mutually at distance `θ`.
Proved from `(5.1)` (`theorem_5_1_proof`). -/
theorem theorem_7_1_proof
     :
    GM15Theorem71Statement.{u, v, w} := by
  intro S _ _ α β G H₀ η₀ θ_star θ₀ θ lam μ k T_star T₀ d₀
    hFlat₀ hMetric₀ hlam2 hθ_ord h4 hθ_le hEyes₀
  let T := GM10.truncation T₀ θ
  have hFlat : IsFlatSpan G H₀ η₀ θ_star θ lam μ T_star T :=
    theorem_5_1_proof G H₀ η₀ θ_star θ₀ θ lam lam μ μ T_star T₀
      hFlat₀ le_rfl le_rfl (by omega) hθ_le hθ_ord (by omega) (fun _ => hlam2)
  obtain ⟨d, hMetric, hd_eq, _⟩ :=
    hasTangleMetric_truncation_of_hasTangleMetric (θ₁ := θ) hMetric₀ (by omega) hθ_le
  rcases hEyes₀ with ⟨r, hr_inj, hr_eye, hr_dist⟩
  refine ⟨H₀, η₀, T, d, r, hFlat, hMetric, hr_inj, ?_, ?_⟩
  · intro i
    rcases hr_eye i with
      ⟨hr_R, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub, hC_U, ha, hb, hc, hd_v,
        hnodup, hord, hFree, hdisj, hP₁, hP₂⟩
    have hcard4 : ({a, b, c, d_v} : Set S).ncard ≤ θ := by
      have h1 := ncard_insert_le a ({b, c, d_v} : Set S)
      have h2 := ncard_insert_le b ({c, d_v} : Set S)
      have h3 := ncard_insert_le c ({d_v} : Set S)
      have h4' : ({d_v} : Set S).ncard = 1 := ncard_singleton d_v
      omega
    have hFree' : IsFreeSet H₀.toHypergraph T θ {a, b, c, d_v} :=
      theorem_3_3_claim_2 hFlat₀.isSpan.isControlling.isTangle_H hFree Subset.rfl hcard4
    exact ⟨hr_R, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub, hC_U, ha, hb, hc, hd_v,
      hnodup, hord, hFree', hdisj, hP₁, hP₂⟩
  · intro i j hij
    have hri : r i ∈ H₀.A := Or.inr (hr_eye i).1
    have hrj : r j ∈ H₀.A := Or.inr (hr_eye j).1
    rw [hd_eq (r i) hri (r j) hrj]
    exact min_eq_left (hr_dist i j hij)

/-- Statement of Graph Minors XV, (7.2) (page 135):
"For $1 \le i < j \le k$, if $\sigma_1 \in Z_i$ and $\sigma_2 \in Z_j$ then $d(\sigma_1,
\sigma_2) \ge \theta - 2(\theta' + 12\mu + 14)$, and so $Z_i \cap Z_j = \emptyset$ and $J_i
\cap J_j \subseteq H$." -/
def GM15Theorem72Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 * (θ' + 12 * μ + 14) + μ ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    ∀ i j : Fin k, i ≠ j →
      (∀ σ₁ ∈ eyeAtomZone H d θ' μ (r i), ∀ σ₂ ∈ eyeAtomZone H d θ' μ (r j),
        θ - 2 * (θ' + 12 * μ + 14) ≤ pointDist H d σ₁ σ₂) ∧
      Disjoint (eyeAtomZone H d θ' μ (r i)) (eyeAtomZone H d θ' μ (r j)) ∧
      V(eyeBridgeUnion G H η d θ' μ (r i)) ∩ V(eyeBridgeUnion G H η d θ' μ (r j)) ⊆
        V(η.imageGraph)

/-- **Graph Minors XV, (7.2)** (pages 135–136):
For `i ≠ j`, points in `Z_i` and `Z_j` are at distance `≥ θ - 2(θ' + 12μ + 14)`, `Z_i ∩ Z_j = ∅`,
and `V(J_i) ∩ V(J_j) ⊆ V(η(H))`. -/
theorem theorem_7_2_proof :
    GM15Theorem72Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam μ k T_star T d r
    hFlat hMetric hμ1 hθ hr_inj hr_eye hr_dist i j hij
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨_, hd_refl, _, hd_symm, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  have hriA : r i ∈ H.A := Or.inr (hr_eye i).1
  have hrjA : r j ∈ H.A := Or.inr (hr_eye j).1
  have hd_ij : d (r i) (r j) = θ := hr_dist i j hij
  have hPart1 : ∀ σ₁ ∈ eyeAtomZone H d θ' μ (r i), ∀ σ₂ ∈ eyeAtomZone H d θ' μ (r j),
      θ - 2 * (θ' + 12 * μ + 14) ≤ pointDist H d σ₁ σ₂ := by
    intro σ₁ hσ₁ σ₂ hσ₂
    obtain ⟨a₁, ⟨ha₁A, hd₁⟩, hσa₁⟩ := mem_iUnion₂.mp hσ₁
    obtain ⟨a₂, ⟨ha₂A, hd₂⟩, hσa₂⟩ := mem_iUnion₂.mp hσ₂
    rw [pointDist_eq_of_mem_atom ha₁A ha₂A hσa₁ hσa₂]
    have htri₁ := hd_tri (r i) hriA a₁ ha₁A (r j) hrjA
    have htri₂ := hd_tri a₁ ha₁A a₂ ha₂A (r j) hrjA
    have hsym₂ := hd_symm a₂ ha₂A (r j) hrjA
    omega
  have hPart2 : Disjoint (eyeAtomZone H d θ' μ (r i)) (eyeAtomZone H d θ' μ (r j)) := by
    refine Set.disjoint_left.mpr fun σ hσ₁ hσ₂ => ?_
    have hge := hPart1 σ hσ₁ σ hσ₂
    obtain ⟨a, haA, hσa⟩ := exists_atom_of_point H σ
    rw [pointDist_eq_of_mem_atom haA haA hσa hσa, hd_refl a haA] at hge
    omega
  refine ⟨hPart1, hPart2, fun x ⟨hx₁, hx₂⟩ => ?_⟩
  by_contra hx_not
  simp only [eyeBridgeUnion, vertexSet_subgraphSUnion, mem_iUnion] at hx₁ hx₂
  obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u, ⟨huH, huZ₁⟩, rfl⟩, hxB₁⟩ := hx₁
  obtain ⟨B₂, ⟨hB₂, z₂, hz₂B₂, v, ⟨hvH, hvZ₂⟩, rfl⟩, hxB₂⟩ := hx₂
  have hB_comp : ∀ {B : Graph α β} {u_v : S},
      IsBridge G η.imageGraph B → x ∈ V(B) → u_v ∈ H.V → η.vMap u_v ∈ V(B) →
      ∃ C ∈ graphComponents (deleteVertices G V(η.imageGraph)),
        x ∈ V(C) ∧ ∃ e ∈ E(G), ∃ w ∈ V(C), G.IsLink e w (η.vMap u_v) := by
    intro B u_v hB hxB hu_vH hu_vB
    rcases hB.2.2 with ⟨e, _, w₁, hw₁, w₂, hw₂, _, hVB, _⟩ | ⟨C, hC, hVB, _⟩
    · rw [hVB] at hxB
      rcases hxB with rfl | rfl
      · exact False.elim (hx_not hw₁)
      · exact False.elim (hx_not hw₂)
    · rw [hVB] at hxB hu_vB
      have hxC : x ∈ V(C) := by
        rcases hxB with hxC | ⟨hxH, _⟩
        · exact hxC
        · exact False.elim (hx_not hxH)
      rcases hu_vB with hu_vC | ⟨_, e, heG, w, hwC, hlink⟩
      · exact False.elim ((hC.1.vertexSet_mono hu_vC).2 (η.bijOn_v.mapsTo hu_vH))
      · exact ⟨C, hC, hxC, e, heG, w, hwC, hlink⟩
  obtain ⟨C₁, hC₁, hxC₁, e₁, he₁G, x₁, hx₁C₁, hlink₁⟩ := hB_comp hB₁ hxB₁ huH hz₁B₁
  obtain ⟨C₂, hC₂, hxC₂, e₂, he₂G, x₂, hx₂C₂, hlink₂⟩ := hB_comp hB₂ hxB₂ hvH hz₂B₂
  have hC_eq : C₁ = C₂ := isGraphComponent_eq_of_mem_inter hC₁ hC₂ ⟨x, hxC₁, hxC₂⟩
  rw [← hC_eq] at hx₂C₂
  have huv_ne : u ≠ v := fun hEq =>
    Set.disjoint_left.mp hPart2 huZ₁ (hEq ▸ hvZ₂)
  have hvu_ne : η.vMap u ≠ η.vMap v :=
    fun hEq => huv_ne (η.bijOn_v.injOn huH hvH hEq)
  obtain ⟨P, hP⟩ :=
    exists_isHPathWithEnds_of_component_attachments η.imageGraph_le hC₁
      (η.bijOn_v.mapsTo huH) (η.bijOn_v.mapsTo hvH) hvu_ne hx₁C₁ hx₂C₂ hlink₁.symm hlink₂
  have hdist_uv : μ ≤ d {u} {v} := by
    have hge := hPart1 u huZ₁ v hvZ₂
    rw [pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨u, huH, rfl⟩))
      (Or.inl (Or.inl ⟨v, hvH, rfl⟩)) (mem_singleton u) (mem_singleton v)] at hge
    dsimp at hge
    omega
  have hord := hFlat.order_ge
  exact not_isMuSteppedSpan_of_isFlatSpan hFlat hMetric (by omega)
    ⟨P, u, v, huH, hvH, hP, hdist_uv⟩

/-- Four distinct vertices `a, b, c, d_v` occurring in cyclic order along a circuit `C` cross on
`C.U`: `PairsCrossOn C.U a c b d_v`. -/
private theorem pairsCrossOn_of_occurInCircuitOrder {S : Type w} [TopologicalSpace S]
    {C : Drawing S} {a b c d_v : S}
    (hnodup : ([a, b, c, d_v]).Nodup) (hord : OccurInCircuitOrder C a b c d_v) :
    PairsCrossOn C.U a c b d_v := by
  obtain ⟨φ, t₁, t₂, t₃, t₄, ht₀, h₁₂, h₂₃, h₃₄, h₄, ha, hb, hc, hd⟩ := hord
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false] at hnodup
  rcases hnodup with ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd, -⟩
  have haU : a ∈ C.U := ha ▸ (φ (Circle.exp t₁)).2
  have hbU : b ∈ C.U := hb ▸ (φ (Circle.exp t₂)).2
  have hcU : c ∈ C.U := hc ▸ (φ (Circle.exp t₃)).2
  have hdU : d_v ∈ C.U := hd ▸ (φ (Circle.exp t₄)).2
  refine ⟨haU, hbU, hcU, hdU, hac, hbd, hab, had, Ne.symm hbc, hcd, fun he => ?_⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  let s₁ := t₁ / (2 * Real.pi)
  let s₂ := t₂ / (2 * Real.pi)
  let s₃ := t₃ / (2 * Real.pi)
  let s₄ := t₄ / (2 * Real.pi)
  have hs₁ : 0 ≤ s₁ := div_nonneg ht₀ hpi.le
  have hs₁₂ : s₁ < s₂ := div_lt_div_of_pos_right h₁₂ hpi
  have hs₂₃ : s₂ < s₃ := div_lt_div_of_pos_right h₂₃ hpi
  have hs₃₄ : s₃ < s₄ := div_lt_div_of_pos_right h₃₄ hpi
  have hs₄ : s₄ < s₁ + 1 := by
    have : s₄ < 1 := (div_lt_one hpi).mpr h₄
    linarith
  have hpt : ∀ t : ℝ, circlePt (t / (2 * Real.pi)) = Circle.exp t := fun t => by
    unfold circlePt
    rw [mul_div_cancel₀ t hpi.ne']
  let k : Circle → S := fun z => (φ z).1
  have hkemb : IsEmbedding k := IsEmbedding.subtypeVal.comp φ.isEmbedding
  set C₀ := C.U \ {a, c}
  have hb₀ : b ∈ C₀ := by
    refine ⟨hbU, ?_⟩
    rintro (rfl | rfl)
    · exact hab rfl
    · exact hbc rfl
  have hd₀ : d_v ∈ C₀ := by
    refine ⟨hdU, ?_⟩
    rintro (rfl | rfl)
    · exact had rfl
    · exact hcd rfl
  have hsub₀ : connectedComponentIn C₀ b ⊆ C₀ := connectedComponentIn_subset _ _
  have hpre : IsPreconnected (k ⁻¹' connectedComponentIn C₀ b) := by
    rw [← hkemb.isInducing.isPreconnected_image, image_preimage_eq_of_subset]
    · exact isPreconnected_connectedComponentIn
    · intro y hy
      have hyU : y ∈ C.U := (hsub₀ hy).1
      exact ⟨φ.symm ⟨y, hyU⟩, by simp [k]⟩
  refine circle_no_cross hs₁₂ hs₂₃ hs₃₄ hs₄ hpre ?_ ?_ ?_ ?_
  · intro hm
    have hka : k (circlePt s₁) = a := by dsimp [k, s₁]; rw [hpt]; exact ha
    exact (hsub₀ hm).2 (Or.inl hka)
  · intro hm
    have hkc : k (circlePt s₃) = c := by dsimp [k, s₃]; rw [hpt]; exact hc
    exact (hsub₀ hm).2 (Or.inr hkc)
  · have hkb : k (circlePt s₂) = b := by dsimp [k, s₂]; rw [hpt]; exact hb
    change k (circlePt s₂) ∈ connectedComponentIn C₀ b
    rw [hkb]
    exact mem_connectedComponentIn hb₀
  · have hkd : k (circlePt s₄) = d_v := by dsimp [k, s₄]; rw [hpt]; exact hd
    change k (circlePt s₄) ∈ connectedComponentIn C₀ b
    rw [hkd, he]
    exact mem_connectedComponentIn hd₀

/-- Pulling back a simple walk `W'` in `G` whose edges lie in `E(η.imageGraph)` to a simple walk
`W` in `Γ.toGraph`. -/
private theorem exists_walk_toGraph_of_edges_subset {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {Γ : Drawing S} (η : SpanEmbedding Γ G)
    {u' v' : α} (W' : GraphWalk G u' v') (hW' : W'.IsSimple)
    {a b : S} (ha : a ∈ Γ.V) (hb : b ∈ Γ.V) (hu' : η.vMap a = u') (hv' : η.vMap b = v')
    (hed : ∀ e ∈ W'.edges, e ∈ E(η.imageGraph)) :
    ∃ W : GraphWalk Γ.toGraph a b,
      W.IsSimple ∧ W'.support = W.support.map η.vMap ∧ W'.edges = W.edges.map η.eMap := by
  induction W' generalizing a with
  | @nil u h =>
    have hab : a = b := η.bijOn_v.injOn ha hb (hu'.trans hv'.symm)
    subst hab
    exact ⟨.nil ha, List.nodup_singleton a, congrArg (· :: []) hu'.symm, rfl⟩
  | @cons u w v e' hlink r ih =>
    have hu_not : u ∉ r.support := (List.nodup_cons.mp hW').1
    have hnd_r : r.IsSimple := (List.nodup_cons.mp hW').2
    have he' : e' ∈ E(η.imageGraph) := hed e' List.mem_cons_self
    obtain ⟨e, he, hee'⟩ := η.bijOn_e.surjOn he'
    have hlink_im : η.imageGraph.IsLink (η.eMap e) (η.vMap a) w := by
      rw [hee', hu']
      exact (η.imageGraph_le.isLink_iff he').mpr hlink
    obtain ⟨c, hc, hcw⟩ := η.bijOn_v.surjOn hlink_im.right_mem
    have huw : u ≠ w := fun hEq => hu_not (hEq ▸ r.start_mem_support)
    have hac : a ≠ c := fun hEq => huw (hu'.symm.trans ((congrArg η.vMap hEq).trans hcw))
    have hlink_Γ : Γ.toGraph.IsLink e a c := by
      refine (η.isLink_iff_of_ne he ha hc hac).mp ?_
      rwa [hcw]
    obtain ⟨W_r, hWr_sim, hsup, hed_r⟩ :=
      ih hnd_r hc hcw hv' (fun f hf => hed f (List.mem_cons_of_mem e' hf))
    refine ⟨.cons hlink_Γ W_r, ?_, by simp [hu', hsup], by simp [hee', hed_r]⟩
    unfold GraphWalk.IsSimple at hWr_sim ⊢
    rw [GraphWalk.support_cons, List.nodup_cons]
    refine ⟨?_, hWr_sim⟩
    intro ha_mem
    apply hu_not
    rw [← hu', hsup]
    exact List.mem_map_of_mem ha_mem

/-- Along a walk `W'` in `G₀` starting at `η₀.vMap a` (`a ∈ H.V ∩ closure Λ`) whose edges are
disjoint from `E(η'.imageGraph)` and not all in `E(η₀.imageGraph)`, the first edge outside
`E(η₀.imageGraph)` has its start vertex in `η₀.vMap '' (H.V ∩ closure Λ)`. -/
private theorem exists_first_non_imageGraph_edge {S : Type w} [TopologicalSpace S] [T2Space S]
    {G₀ : Graph α β} {H : Drawing S} {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ)
    (η₀ : SpanEmbedding H G₀) (η' : SpanEmbedding (clearedSubdrawing H Λ) G₀)
    (hη'_e : ∀ e ∈ (clearedSubdrawing H Λ).E, η'.eMap e = η₀.eMap e)
    {u' v' : α} (W' : GraphWalk G₀ u' v')
    {a : S} (haV : a ∈ H.V) (ha_cl : a ∈ closure Λ) (hu' : η₀.vMap a = u')
    (hnot_H' : ∀ f ∈ W'.edges, f ∉ E(η'.imageGraph))
    (hex : ∃ f ∈ W'.edges, f ∉ E(η₀.imageGraph)) :
    ∃ v ∈ H.V, v ∈ closure Λ ∧ ∃ e x, e ∉ E(η₀.imageGraph) ∧ G₀.IsLink e (η₀.vMap v) x := by
  induction W' generalizing a with
  | nil _ =>
    rcases hex with ⟨_, hf, _⟩
    exact False.elim (List.not_mem_nil hf)
  | @cons u w v e₀ hlink r ih =>
    by_cases he₀ : e₀ ∈ E(η₀.imageGraph)
    · rcases hex with ⟨f, hf, hf_not⟩
      have hex_r : ∃ f ∈ r.edges, f ∉ E(η₀.imageGraph) := by
        rcases List.mem_cons.mp hf with rfl | hfr
        · exact False.elim (hf_not he₀)
        · exact ⟨f, hfr, hf_not⟩
      obtain ⟨f₀, hf₀, hf₀_eq⟩ := η₀.bijOn_e.surjOn he₀
      have hlink_im : η₀.imageGraph.IsLink (η₀.eMap f₀) u w := by
        rw [hf₀_eq]
        exact (η₀.imageGraph_le.isLink_iff he₀).mpr hlink
      obtain ⟨c, hcV, hcw⟩ := η₀.bijOn_v.surjOn hlink_im.right_mem
      have hinc_c : η₀.imageGraph.Inc (η₀.eMap f₀) (η₀.vMap c) := by
        rw [hcw]
        exact ⟨u, hlink_im.symm⟩
      have hc_f₀ : c ∈ closure f₀ := (η₀.inc_iff f₀ hf₀ c hcV).mp hinc_c
      have hf₀_not_H' : f₀ ∉ (clearedSubdrawing H Λ).E := fun hf₀' => by
        apply hnot_H' e₀ List.mem_cons_self
        rw [← hf₀_eq, ← hη'_e f₀ hf₀']
        exact η'.bijOn_e.mapsTo hf₀'
      have hf₀_Λ : f₀ ⊆ Λ := by
        rcases edge_subset_or_subset_compl_of_zone hZone hf₀ with hsub | hcompl
        · exact hsub
        · exfalso
          apply hf₀_not_H'
          rw [(clearedSubdrawing_V_and_E hZone).2]
          exact ⟨hf₀, hcompl⟩
      have hc_cl : c ∈ closure Λ := closure_mono hf₀_Λ hc_f₀
      exact ih hcV hc_cl hcw (fun f hf => hnot_H' f (List.mem_cons_of_mem e₀ hf)) hex_r
    · exact ⟨a, haV, ha_cl, e₀, w, he₀, hu' ▸ hlink⟩

/-- Statement of Graph Minors XV, (7.3) (page 136):
"If there is a* $(3\mu + 3)$*-zone* $\Lambda \subseteq \Sigma$ *for* $H$ *such that* $H \cap
(\Sigma - \Lambda)$ *is rigid and such that* $\Lambda$ *is an eye of* $H \cap (\Sigma -
\Lambda)$ *in* $G_0$ *with respect to the tangle of order* $\theta - 12\mu - 14$ *obtained
from* $\mathcal{T}$ *by clearing* $\Lambda$, *then (S1) holds." -/
def GM15Theorem73Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam lam' μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (z Λ : Set S)
    (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d₁ : Set S → Set S → ℕ)
    (η' : SpanEmbedding (clearedSubdrawing H Λ) (section7G0 G H η d θ' μ r)),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    12 ≤ μ → 4 ≤ lam' → 4 * lam' + μ + 2 ≤ θ' → 6 * μ + 14 < θ' →
    6 * (3 * μ + 3) + 5 * lam' + 3 * μ + 4 ≤ lam →
    θ' + 12 * μ + 14 ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    IsLambdaZoneAround H d (3 * μ + 3) z Λ →
    IsClearedTangle H T d θ (3 * μ + 3) Λ T₁ d₁ →
    IsRigid (clearedSubdrawing H Λ) →
    (∀ v ∈ (clearedSubdrawing H Λ).V, η'.vMap v = η₀.vMap v) →
    (∀ e ∈ (clearedSubdrawing H Λ).E, η'.eMap e = η₀.eMap e) →
    IsDrawingEye (section7G0 G H η d θ' μ r) (clearedSubdrawing H Λ) η'
      (θ - 4 * (3 * μ + 3) - 2) T₁ Λ →
    Section7S1 S G θ_star T_star k μ lam' θ'

private theorem exists_cleared_vertex_outside_eye_zones
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ : ℕ)
    (θ' : ℕ)
    (μ : ℕ)
    (k : ℕ)
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (z : Set S)
    (Λ : Set S)
    (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (η' : SpanEmbedding (clearedSubdrawing H Λ) (section7G0 G H η d θ' μ r))
    (hη₀_v : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (hη₀_e : ∀ e ∈ H.E, η₀.eMap e = η.eMap e)
    (hZone : IsLambdaZoneAround H d (3 * μ + 3) z Λ)
    (hη'_v : ∀ v ∈ (clearedSubdrawing H Λ).V, η'.vMap v = η₀.vMap v)
    (hη'_e : ∀ e ∈ (clearedSubdrawing H Λ).E, η'.eMap e = η₀.eMap e)
    (hEyeΛ : IsDrawingEye (section7G0 G H η d θ' μ r) (clearedSubdrawing H Λ) η' (θ - 4 * (3 * μ +
      3) - 2) T₁ Λ)
    (hS : IsClosedSurface S) :
    let H' : Drawing S := clearedSubdrawing H Λ
    (H'.IsSubdrawing H) →
    ((clearedSubdrawing H Λ).E = {e | e ∈ H.E ∧ e ⊆ univ \ Λ}) →
    ∃ v ∈ H.V, v ∈ closure Λ ∧ ∀ (i : Fin k), v ∉ eyeAtomZone H d θ' μ (r i) := by
  intro H' hSubH' hE_H'
  let G₀ := section7G0 G H η d θ' μ r
  rcases hEyeΛ with
    ⟨_, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub, hC_U, haC, hbC, hcC, hdC,
      hnodup, hord, _, hdisj_P, hP₁, hP₂⟩
  have haH' : a ∈ H'.V := hC_sub.1 haC
  have hbH' : b ∈ H'.V := hC_sub.1 hbC
  have hcH' : c ∈ H'.V := hC_sub.1 hcC
  have hdH' : d_v ∈ H'.V := hC_sub.1 hdC
  have haH : a ∈ H.V := hSubH'.1 haH'
  have hbH : b ∈ H.V := hSubH'.1 hbH'
  have hcH : c ∈ H.V := hSubH'.1 hcH'
  have hdH : d_v ∈ H.V := hSubH'.1 hdH'
  have ha_cl : a ∈ closure Λ := (hC_U ▸ C.V_subset_U haC).1
  have hb_cl : b ∈ closure Λ := (hC_U ▸ C.V_subset_U hbC).1
  obtain ⟨W₁₀, hW₁₀_sim, hVP₁, hEP₁⟩ := hP₁.2.1.2
  obtain ⟨W₁', hW₁'_sup, hW₁'_ed⟩ := exists_walk_up_of_le hP₁.2.1.1 W₁₀
  have hW₁'_sim : W₁'.IsSimple := by
    unfold GraphWalk.IsSimple; rw [hW₁'_sup]; exact hW₁₀_sim
  obtain ⟨W₂₀, hW₂₀_sim, hVP₂, hEP₂⟩ := hP₂.2.1.2
  obtain ⟨W₂', hW₂'_sup, hW₂'_ed⟩ := exists_walk_up_of_le hP₂.2.1.1 W₂₀
  have hW₂'_sim : W₂'.IsSimple := by
    unfold GraphWalk.IsSimple; rw [hW₂'_sup]; exact hW₂₀_sim
  have hNotBoth : ¬ ((∀ e ∈ W₁'.edges, e ∈ E(η₀.imageGraph)) ∧
      (∀ e ∈ W₂'.edges, e ∈ E(η₀.imageGraph))) := by
    rintro ⟨hE₁, hE₂⟩
    obtain ⟨W₁, hW₁_sim, hsup₁, hed₁⟩ :=
      exists_walk_toGraph_of_edges_subset η₀ W₁' hW₁'_sim haH hcH
        (hη'_v a haH').symm (hη'_v c hcH').symm hE₁
    obtain ⟨W₂, hW₂_sim, hsup₂, hed₂⟩ :=
      exists_walk_toGraph_of_edges_subset η₀ W₂' hW₂'_sim hbH hdH
        (hη'_v b hbH').symm (hη'_v d_v hdH').symm hE₂
    let Q₁ := walkDrawing H W₁
    let Q₂ := walkDrawing H W₂
    have hQ₁_sub : Q₁.IsSubdrawing H := walkDrawing_isSubdrawing H W₁
    have hQ₂_sub : Q₂.IsSubdrawing H := walkDrawing_isSubdrawing H W₂
    have hQ₁_path : Q₁.IsPathBetween a c := GM11.walkDrawing_isPathBetween H hW₁_sim
    have hQ₂_path : Q₂.IsPathBetween b d_v := GM11.walkDrawing_isPathBetween H hW₂_sim
    have hdisV : Disjoint Q₁.V Q₂.V := by
      rw [walkDrawing_V, walkDrawing_V]
      refine Set.disjoint_left.mpr fun v hv₁ hv₂ => ?_
      have hv₁' : η₀.vMap v ∈ V(P₁) := by
        rw [hVP₁, mem_ofPred_eq, ← hW₁'_sup, hsup₁]
        exact List.mem_map_of_mem hv₁
      have hv₂' : η₀.vMap v ∈ V(P₂) := by
        rw [hVP₂, mem_ofPred_eq, ← hW₂'_sup, hsup₂]
        exact List.mem_map_of_mem hv₂
      exact Set.disjoint_left.mp hdisj_P hv₁' hv₂'
    have hdisU : Disjoint Q₁.U Q₂.U := disjoint_U_of_disjoint_V hQ₁_sub hQ₂_sub hdisV
    have hQ_sub_cl : ∀ {u v : S} {W' : GraphWalk G₀ (η'.vMap u) (η'.vMap v)}
        {W : GraphWalk H.toGraph u v},
        W'.edges = W.edges.map η₀.eMap →
        (∀ f ∈ W'.edges, f ∉ E(η'.imageGraph)) →
        u ∈ C.V → (walkDrawing H W).U ⊆ closure Λ := by
      intro u v W' W hed hdisE huC
      rw [(walkDrawing H W).U_eq, walkDrawing_V, walkDrawing_E]
      have he_sub : ∀ e ∈ W.edges, closure e ⊆ closure Λ := by
        intro e heW
        have heH : e ∈ H.E := walk_edges_subset_edgeSet W e heW
        have he_not_H' : e ∉ H'.E := fun heH' => by
          have he' : η₀.eMap e ∈ W'.edges := hed ▸ List.mem_map_of_mem heW
          have he_im' : η₀.eMap e ∈ E(η'.imageGraph) := by
            rw [← hη'_e e heH']
            exact η'.bijOn_e.mapsTo heH'
          exact hdisE (η₀.eMap e) he' he_im'
        rcases edge_subset_or_subset_compl_of_zone hZone heH with hsub | hcompl
        · exact closure_mono hsub
        · exfalso
          apply he_not_H'
          rw [hE_H']
          exact ⟨heH, hcompl⟩
      refine union_subset ?_ (iUnion₂_subset fun e heW => he_sub e heW)
      have hsup_cl : ∀ {u₀ v₀ : S} (W₀ : GraphWalk H.toGraph u₀ v₀),
          u₀ ∈ closure Λ → (∀ e ∈ W₀.edges, closure e ⊆ closure Λ) →
          ∀ x ∈ W₀.support, x ∈ closure Λ := by
        intro u₀ v₀ W₀
        induction W₀ with
        | nil _ =>
          intro hu₀ _ x hx
          rw [GraphWalk.support_nil, List.mem_singleton] at hx
          exact hx ▸ hu₀
        | @cons u₁ w₁ v₁ e₀ hlink₀ r₀ ih =>
          intro hu₁ he₀ x hx
          rcases List.mem_cons.mp hx with rfl | hxr
          · exact hu₁
          · have hw₁ : w₁ ∈ closure e₀ ∩ H.V := by
              rw [hlink₀.2.2.2]
              exact mem_insert_of_mem _ (mem_singleton w₁)
            exact ih (he₀ e₀ List.mem_cons_self hw₁.1)
              (fun e he => he₀ e (List.mem_cons_of_mem e₀ he)) x hxr
      exact fun x hxW => hsup_cl W (hC_U ▸ C.V_subset_U huC).1 he_sub x hxW
    have hNotH'₁ : ∀ f ∈ W₁'.edges, f ∉ E(η'.imageGraph) := fun f hf hf' =>
      Set.disjoint_left.mp hP₁.2.2.2.2.2.2 (hEP₁ ▸ (hW₁'_ed ▸ hf)) hf'
    have hNotH'₂ : ∀ f ∈ W₂'.edges, f ∉ E(η'.imageGraph) := fun f hf hf' =>
      Set.disjoint_left.mp hP₂.2.2.2.2.2.2 (hEP₂ ▸ (hW₂'_ed ▸ hf)) hf'
    have hQ₁_cl : Q₁.U ⊆ closure Λ := hQ_sub_cl hed₁ hNotH'₁ haC
    have hQ₂_cl : Q₂.U ⊆ closure Λ := hQ_sub_cl hed₂ hNotH'₂ hbC
    have hcross_CU : PairsCrossOn C.U a c b d_v :=
      pairsCrossOn_of_occurInCircuitOrder hnodup hord
    have hbd_cl : discBd (closure Λ) = C.U := by
      rw [discBd_closure_eq_subBd hS hZone.isOpenDisc hZone.isOArc_bd hZone.isClosedDisc_closure,
        hC_U]
    obtain ⟨φ₁, -⟩ := GM14.isLine_of_isPathBetween hQ₁_path hcross_CU.2.2.2.2.1
    obtain ⟨φ₂, -⟩ := GM14.isLine_of_isPathBetween hQ₂_path hcross_CU.2.2.2.2.2.1
    have hQ₁_range : Q₁.U = range (fun z : unitInterval => (φ₁ z).1) := by
      ext x
      exact ⟨fun hx => ⟨φ₁.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (φ₁ z).2⟩
    have hQ₂_range : Q₂.U = range (fun z : unitInterval => (φ₂ z).1) := by
      ext x
      exact ⟨fun hx => ⟨φ₂.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (φ₂ z).2⟩
    have hQ₁_comp : IsCompact Q₁.U := by
      rw [hQ₁_range]; exact isCompact_range (continuous_subtype_val.comp φ₁.continuous)
    have hQ₂_comp : IsCompact Q₂.U := by
      rw [hQ₂_range]; exact isCompact_range (continuous_subtype_val.comp φ₂.continuous)
    have hQ₁_conn : IsConnected Q₁.U := by
      rw [hQ₁_range]; exact isConnected_range (continuous_subtype_val.comp φ₁.continuous)
    have hQ₂_conn : IsConnected Q₂.U := by
      rw [hQ₂_range]; exact isConnected_range (continuous_subtype_val.comp φ₂.continuous)
    have haQ₁ : a ∈ Q₁.U := Q₁.V_subset_U ((walkDrawing_V H W₁).symm ▸ W₁.start_mem_support)
    have hcQ₁ : c ∈ Q₁.U := Q₁.V_subset_U ((walkDrawing_V H W₁).symm ▸ W₁.end_mem_support)
    have hbQ₂ : b ∈ Q₂.U := Q₂.V_subset_U ((walkDrawing_V H W₂).symm ▸ W₂.start_mem_support)
    have hdQ₂ : d_v ∈ Q₂.U := Q₂.V_subset_U ((walkDrawing_V H W₂).symm ▸ W₂.end_mem_support)
    obtain ⟨x, hx₁, hx₂⟩ := disc_crossing (closure Λ) Q₁.U Q₂.U a c b d_v
      hZone.isClosedDisc_closure hQ₁_cl hQ₂_cl hQ₁_comp hQ₂_comp hQ₁_conn hQ₂_conn
      haQ₁ hcQ₁ hbQ₂ hdQ₂ (hbd_cl.symm ▸ hcross_CU)
    exact Set.disjoint_left.mp hdisU hx₁ hx₂
  have hNotH'₁ : ∀ f ∈ W₁'.edges, f ∉ E(η'.imageGraph) := fun f hf hf' =>
    Set.disjoint_left.mp hP₁.2.2.2.2.2.2 (hEP₁ ▸ (hW₁'_ed ▸ hf)) hf'
  have hNotH'₂ : ∀ f ∈ W₂'.edges, f ∉ E(η'.imageGraph) := fun f hf hf' =>
    Set.disjoint_left.mp hP₂.2.2.2.2.2.2 (hEP₂ ▸ (hW₂'_ed ▸ hf)) hf'
  have hex_v : ∃ v ∈ H.V, v ∈ closure Λ ∧
      ∃ e x, e ∉ E(η₀.imageGraph) ∧ G₀.IsLink e (η₀.vMap v) x := by
    by_cases hE₁ : ∀ e ∈ W₁'.edges, e ∈ E(η₀.imageGraph)
    · have hex₂ : ∃ e ∈ W₂'.edges, e ∉ E(η₀.imageGraph) := by
        by_contra hno
        push Not at hno
        exact hNotBoth ⟨hE₁, hno⟩
      exact exists_first_non_imageGraph_edge hZone η₀ η' hη'_e W₂' hbH hb_cl
        (hη'_v b hbH').symm hNotH'₂ hex₂
    · push Not at hE₁
      exact exists_first_non_imageGraph_edge hZone η₀ η' hη'_e W₁' haH ha_cl
        (hη'_v a haH').symm hNotH'₁ hE₁
  obtain ⟨v, hvH, hv_cl, e, x, he_not_im₀, hlink_e⟩ := hex_v
  have hE_im_eq : E(η₀.imageGraph) = E(η.imageGraph) := by
    rw [← η₀.bijOn_e.image_eq, ← η.bijOn_e.image_eq]
    exact image_congr hη₀_e
  have hJ₀_le_G : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le_G
  have he_G₀ : e ∈ E(G₀) := hlink_e.edge_mem
  have he_J₀ : e ∈ E(remainingBridgeUnion G H η d θ' μ r) := by
    change e ∈ E(subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r}) at he_G₀
    rw [edgeSet_subgraphSUnion hPair_le] at he_G₀
    obtain ⟨Q, hQ, heQ⟩ := mem_iUnion₂.mp he_G₀
    rcases hQ with rfl | rfl
    · exact False.elim (he_not_im₀ (hE_im_eq.symm ▸ heQ))
    · exact heQ
  have hG₀_le_G : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hJ₀_le_G₀ : remainingBridgeUnion G H η d θ' μ r ≤ G₀ :=
    le_subgraphSUnion hPair_le (Or.inr rfl)
  have hlink_J₀ : (remainingBridgeUnion G H η d θ' μ r).IsLink e (η₀.vMap v) x :=
    (hJ₀_le_G₀.isLink_iff he_J₀).mpr hlink_e
  have hv_J₀ : η.vMap v ∈ V(remainingBridgeUnion G H η d θ' μ r) := by
    rw [← hη₀_v v hvH]
    exact hlink_J₀.left_mem
  rw [remainingBridgeUnion, vertexSet_subgraphSUnion] at hv_J₀
  obtain ⟨B, ⟨_, hB_disj⟩, hvB⟩ := mem_iUnion₂.mp hv_J₀
  refine ⟨v, hvH, hv_cl, fun i hvi => ?_⟩
  exact Set.disjoint_left.mp hB_disj hvB
    (mem_iUnion.mpr ⟨i, v, ⟨hvH, hvi⟩, rfl⟩)

private theorem distance_from_cleared_region
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ : ℕ)
    (θ' : ℕ)
    (μ : ℕ)
    (k : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (z : Set S)
    (Λ : Set S)
    (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d₁ : Set S → Set S → ℕ)
    (hr_eye : ∀ (i : Fin k), IsDrawingEye G H η θ T (r i))
    (hZone : IsLambdaZoneAround H d (3 * μ + 3) z Λ)
    (hClear : IsClearedTangle H T d θ (3 * μ + 3) Λ T₁ d₁)
    (hS : IsClosedSurface S)
    [ConnectedSpace S] :
    let H' : Drawing S := clearedSubdrawing H Λ
    (∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a) →
    (∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c) →
    ((H.E.Nonempty → ∀ v ∈ H.V, ∀ r ∈ H.R, v ∈ closure r → d {v} r ≤ 1) ∧ ∀ v ∈ H.V, ∀
      e ∈ H.E, v ∈ closure e → d {v} e ≤ 2) →
    (Λ ∈ H'.A) →
    (H'.IsSubdrawing H) →
    ∀ (v₀ : S),
    (v₀ ∈ H.V) →
    (v₀ ∈ closure Λ) →
    ({v₀} ∈ H.A) →
    (∀ (i : Fin k), θ' + 12 * μ + 14 < d (r i) {v₀}) →
    (∀ (i : Fin k), r i ∈ H'.R) →
    (H.E.Nonempty) →
    ∀ (i : Fin k), θ' ≤ d₁ Λ (r i) := by
  intro H' hd_symm hd_tri hd_inc hΛA hSubH' v₀ hv₀H hv₀_cl hv₀A hrv₀ hri_H' hE_ne i
  have hriA : r i ∈ H.A := Or.inr (hr_eye i).1
  have hriA' : r i ∈ H'.A := Or.inr (hri_H' i)
  let S_R : Set (Set S) := {r₀ ∈ H.R | r₀ ⊆ Λ}
  have hS_R_fin : S_R.Finite :=
    (GM11.finite_R hS H).subset fun _ h => h.1
  have hv₀_u : v₀ ∈ closure (⋃ r₀ ∈ S_R, r₀) := by
    refine mem_closure_iff.mpr fun O hO hv₀O => ?_
    obtain ⟨x, hxO, hxΛ⟩ := mem_closure_iff.mp hv₀_cl O hO hv₀O
    obtain ⟨y, ⟨hyO, hyΛ⟩, hy_notU⟩ :=
      GM11.exists_notMem_U (Γ := H) hS
        (hO.inter hZone.isOpenDisc.1) ⟨x, hxO, hxΛ⟩
    obtain ⟨r₀, hr₀, hy_r₀⟩ := exists_region_of_notMem hy_notU
    have hr₀_Λ : r₀ ⊆ Λ :=
      atom_subset_of_isSubdrawing hSubH' (Or.inr hr₀) hΛA hy_r₀ hyΛ
    exact ⟨y, hyO, mem_iUnion₂.mpr ⟨r₀, ⟨hr₀, hr₀_Λ⟩, hy_r₀⟩⟩
  rw [hS_R_fin.closure_biUnion] at hv₀_u
  obtain ⟨aσ, ⟨haσR, haσ_sub⟩, hv₀_aσ⟩ := mem_iUnion₂.mp hv₀_u
  have haσA : aσ ∈ H.A := Or.inr haσR
  have hd_v₀_aσ : d {v₀} aσ ≤ 1 := hd_inc.1 hE_ne v₀ hv₀H aσ haσR hv₀_aσ
  have htri := hd_tri (r i) hriA aσ haσA {v₀} hv₀A
  have hsym₁ := hd_symm {v₀} hv₀A aσ haσA
  have hsym₂ := hd_symm (r i) hriA aσ haσA
  have hgt := hrv₀ i
  have hbd := (hClear.dist_bounds aσ haσA (r i) hriA Λ hΛA (r i) hriA' haσ_sub Subset.rfl).1
  omega

private theorem eye_survives_clearing
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ : ℕ)
    (θ' : ℕ)
    (lam' : ℕ)
    (μ : ℕ)
    (k : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (z : Set S)
    (Λ : Set S)
    (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d₁ : Set S → Set S → ℕ)
    (hMetric : HasTangleMetric H θ T d)
    (hμ12 : 12 ≤ μ)
    (hlam'4 : 4 ≤ lam')
    (hθ' : 4 * lam' + μ + 2 ≤ θ')
    (hθ'_gt : 6 * μ + 14 < θ')
    (hr_eye : ∀ (i : Fin k), IsDrawingEye G H η θ T (r i))
    (hZone : IsLambdaZoneAround H d (3 * μ + 3) z Λ)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S] :
    let H' : Drawing S := clearedSubdrawing H Λ
    let lam₁ : ℕ := 3 * μ + 3
    let θ₁ : ℕ := θ - (4 * lam₁ + 2)
    (∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c) →
    ((H.E.Nonempty → ∀ v ∈ H.V, ∀ r ∈ H.R, v ∈ closure r → d {v} r ≤ 1) ∧ ∀ v ∈ H.V, ∀
      e ∈ H.E, v ∈ closure e → d {v} e ≤ 2) →
    (Λ ∈ H'.A) →
    ((PaintingOrDrawing.drawing H').IsTwoCell) →
    (∀ a ∈ H'.A, d₁ a a = 0) →
    (IsLambdaCompression H H' θ (4 * lam₁ + 2) T T₁ d d₁) →
    (∀ a ∈ H.A, lam₁ < d z a → a ∈ H'.A) →
    ∀ (v₀ : S),
    (d z {v₀} ≤ lam₁) →
    (∀ (i : Fin k), θ' + 9 * μ + 11 < d z (r i)) →
    (∀ (i : Fin k), r i ∈ H'.R) →
    (H.E.Nonempty) →
    (∀ (i : Fin k), θ' ≤ d₁ Λ (r i)) →
    ∀ (η'_G : SpanEmbedding H' G),
    (∀ v ∈ H'.V, η'_G.vMap v = η.vMap v) →
    (V(η'_G.imageGraph) ⊆ V(η.imageGraph)) →
    (E(η'_G.imageGraph) ⊆ E(η.imageGraph)) →
    ∀ (i : Fin k), IsDrawingEye G H' η'_G θ₁ T₁ (r i) := by
  intro H' lam₁ θ₁ hd_tri hd_inc hΛA h2cell' hd₁_refl hComp₁ hAtoms v₀ hzv₀ hClaim3 hri_H' hE_ne
    hClaim4 η'_G hη'_G_v hV_sub_im hE_sub_im i
  rcases hr_eye i with
    ⟨hri_R, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub, hC_U, ha, hb, hc, hd_v,
      hnodup, hord, hFree, hdisj, hP₁, hP₂⟩
  have hri_ne_Λ : r i ≠ Λ := by
    intro hEq
    have hge := hClaim4 i
    rw [← hEq, hd₁_refl (r i) (Or.inr (hri_H' i))] at hge
    omega
  have hdis_ri_Λ : Disjoint (r i) Λ :=
    GM14.disjoint_of_mem_A_ne (Or.inr (hri_H' i)) hΛA hri_ne_Λ
  have hdis_CU_Λ : Disjoint C.U Λ := by
    rw [hC_U]
    refine Set.disjoint_left.mpr fun x hxbd hxΛ => ?_
    obtain ⟨y, hyΛ, hy_ri⟩ := mem_closure_iff.mp hxbd.1 Λ hZone.isOpenDisc.1 hxΛ
    exact Set.disjoint_left.mp hdis_ri_Λ hy_ri hyΛ
  have hC_sub' : C.IsSubdrawing H' := isSubdrawing_clearedSubdrawing hZone hC_sub hdis_CU_Λ
  let X : Set S := {a, b, c, d_v}
  have hX_card : X.ncard ≤ 4 := by
    have h1 := ncard_insert_le a ({b, c, d_v} : Set S)
    have h2 := ncard_insert_le b ({c, d_v} : Set S)
    have h3 := ncard_insert_le c ({d_v} : Set S)
    have h4 : ({d_v} : Set S).ncard = 1 := ncard_singleton d_v
    dsimp [X]
    omega
  have hDistX : ∀ v ∈ X, 2 * X.ncard + 5 * lam₁ + 2 < d z {v} := by
    intro v hvX
    have hvC : v ∈ C.V := by
      rcases hvX with rfl | rfl | rfl | rfl <;> assumption
    have hv_bd : v ∈ subBd (r i) := hC_U ▸ C.V_subset_U hvC
    have hvH : v ∈ H.V := hC_sub.1 hvC
    have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
    have hriA : r i ∈ H.A := Or.inr hri_R
    have hd_rv : d {v} (r i) ≤ 1 := hd_inc.1 hE_ne v hvH (r i) hri_R hv_bd.1
    have htri := hd_tri z hZone.z_mem {v} hvA (r i) hriA
    have hgt := hClaim3 i
    omega
  have hFree' : IsFreeSet H'.toHypergraph T₁ θ₁ X :=
    theorem_4_7_proof H H' θ lam₁ T T₁ d d₁ z X
      hS hConn hMetric hZone.z_mem (by omega) hFree hDistX h2cell' hAtoms hComp₁
  have hPathH' : ∀ {P : Graph α β} {u w : S},
      u ∈ C.V → w ∈ C.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap w) →
      IsHPathWithEnds G η'_G.imageGraph P (η'_G.vMap u) (η'_G.vMap w) := by
    intro P u w huC hwC hP
    have huH' : u ∈ H'.V := hC_sub'.1 huC
    have hwH' : w ∈ H'.V := hC_sub'.1 hwC
    have hu_eq : η'_G.vMap u = η.vMap u := hη'_G_v u huH'
    have hw_eq : η'_G.vMap w = η.vMap w := hη'_G_v w hwH'
    rw [hu_eq, hw_eq]
    refine ⟨η'_G.imageGraph_le, hP.2.1, hP.2.2.1,
      hu_eq ▸ η'_G.bijOn_v.mapsTo huH', hw_eq ▸ η'_G.bijOn_v.mapsTo hwH', ?_,
      hP.2.2.2.2.2.2.mono_right hE_sub_im⟩
    refine Subset.antisymm ?_ ?_
    · exact (inter_subset_inter_right _ hV_sub_im).trans (le_of_eq hP.2.2.2.2.2.1)
    · rintro x (rfl | rfl)
      · have hx_in : η.vMap u ∈ V(P) ∩ V(η.imageGraph) :=
          hP.2.2.2.2.2.1.symm ▸ Or.inl rfl
        exact ⟨hx_in.1, hu_eq ▸ η'_G.bijOn_v.mapsTo huH'⟩
      · have hx_in : η.vMap w ∈ V(P) ∩ V(η.imageGraph) :=
          hP.2.2.2.2.2.1.symm ▸ Or.inr rfl
        exact ⟨hx_in.1, hw_eq ▸ η'_G.bijOn_v.mapsTo hwH'⟩
  exact ⟨hri_H' i, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub', hC_U, ha, hb, hc, hd_v,
    hnodup, hord, hFree', hdisj, hPathH' ha hc hP₁, hPathH' hb hd_v hP₂⟩

/-- **Graph Minors XV, (7.3)** (pages 136–137):
If there is a `(3μ + 3)`-zone `Λ ⊆ Σ` for `H` such that `H ∩ (Σ - Λ)` is rigid and `Λ` is an eye
of `H ∩ (Σ - Λ)` in `G₀` with respect to the tangle `T₁` obtained from `T` by clearing `Λ`, then
`(S1)` holds.
Proved from `(4.6)`, `(4.7)`, `(5.1)`, `(5.2)`, `(7.1)`, and Graph Minors XI, `(9.1)` and XII,
`(7.7)`, `(7.10)`, `(7.11)`. -/
theorem theorem_7_3_proof
     :
    GM15Theorem73Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam lam' μ k T_star T d r η₀ z Λ T₁ d₁ η'
    hFlat hMetric hμ12 hlam'4 hθ' hθ'_gt hlam hθ hr_inj hr_eye hr_dist
    hη₀_v hη₀_e hZone hClear hRigid' hη'_v hη'_e hEyeΛ
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let H' := clearedSubdrawing H Λ
  let G₀ := section7G0 G H η d θ' μ r
  let lam₁ := 3 * μ + 3
  let θ₁ := θ - (4 * lam₁ + 2)
  have hθ₁_eq : θ - 4 * lam₁ - 2 = θ₁ := by omega
  obtain ⟨_, hd_refl, _, hd_symm, hd_tri, hd_inc⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨hΛR, hatom'⟩ := clearedSubdrawing_mem_R_and_atom hZone
  have hΛA : Λ ∈ H'.A := Or.inr hΛR
  have hSubH' : H'.IsSubdrawing H := clearedSubdrawing_isSubdrawing H Λ
  have h2cell' : (PaintingOrDrawing.drawing H').IsTwoCell :=
    clearedSubdrawing_isTwoCell hMetric.1.1 hZone
  obtain ⟨hV_H', hE_H'⟩ := clearedSubdrawing_V_and_E hZone
  -- Claim (1): `T₁` is a `(4 * lam₁ + 2)`-compression of `T` in `H'`.
  have hM₁ : HasTangleMetric H' θ₁ T₁ d₁ := hθ₁_eq ▸ hClear.hasMetric
  obtain ⟨_, hd₁_refl, _, hd₁_symm, hd₁_tri, _⟩ := gm11_theorem_9_1 H' θ₁ T₁ d₁ hS hConn hM₁
  have hComp₁ : IsLambdaCompression H H' θ (4 * lam₁ + 2) T T₁ d d₁ := by
    refine ⟨by omega, hMetric, hM₁, fun σ₁ σ₂ => ?_⟩
    obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
    obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
    obtain ⟨a₁', ha₁', hσ₁'⟩ := exists_atom_of_point H' σ₁
    obtain ⟨a₂', ha₂', hσ₂'⟩ := exists_atom_of_point H' σ₂
    rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, pointDist_eq_of_mem_atom ha₁' ha₂' hσ₁' hσ₂']
    have hsub₁ := atom_subset_of_isSubdrawing hSubH' ha₁ ha₁' hσ₁ hσ₁'
    have hsub₂ := atom_subset_of_isSubdrawing hSubH' ha₂ ha₂' hσ₂ hσ₂'
    have hle := (hClear.dist_bounds a₁ ha₁ a₂ ha₂ a₁' ha₁' a₂' ha₂' hsub₁ hsub₂).1
    omega
  -- Every atom `a ∈ H.A` with `lam₁ < d z a` belongs to `H'.A`.
  have hAtoms : ∀ a ∈ H.A, lam₁ < d z a → a ∈ H'.A := by
    intro a ha hlt
    have hnot_sub : ¬ a ⊆ closure Λ := fun hsub => by
      have := hZone.dist_le a ha hsub
      omega
    obtain ⟨σ, hσa, hσ_not_cl⟩ := Set.not_subset.mp hnot_sub
    have hσ_not_Λ : σ ∉ Λ := fun h => hσ_not_cl (subset_closure h)
    obtain ⟨a', ha', hσa'⟩ := exists_atom_of_point H' σ
    have ha'_ne : a' ≠ Λ := fun hEq => hσ_not_Λ (hEq ▸ hσa')
    have ha'H : a' ∈ H.A := hatom' a' ha' ha'_ne
    exact atom_eq_of_mem ha ha'H hσa hσa' ▸ ha'
  -- Claim (2): There exists `v ∈ H.V ∩ closure Λ` with `η.vMap v ∈ V(J₀)`, hence `v ∉ Z_i` for all
  -- `i`.
  have hClaim2 : ∃ v ∈ H.V, v ∈ closure Λ ∧ ∀ i : Fin k, v ∉ eyeAtomZone H d θ' μ (r i) := by
    exact exists_cleared_vertex_outside_eye_zones (S := S) (α := α) (β := β) G H η θ θ' μ k d r η₀
      z Λ T₁ η' hη₀_v hη₀_e hZone hη'_v hη'_e hEyeΛ hS hSubH' hE_H'
  obtain ⟨v₀, hv₀H, hv₀_cl, hv₀_not_Z⟩ := hClaim2
  have hv₀A : ({v₀} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v₀, hv₀H, rfl⟩)
  have hzv₀ : d z {v₀} ≤ lam₁ := hZone.dist_le {v₀} hv₀A (singleton_subset_iff.mpr hv₀_cl)
  have hrv₀ : ∀ i : Fin k, θ' + 12 * μ + 14 < d (r i) {v₀} := by
    intro i
    by_contra hle
    exact hv₀_not_Z i (mem_iUnion₂.mpr ⟨{v₀}, ⟨hv₀A, Nat.not_lt.mp hle⟩, mem_singleton v₀⟩)
  -- Claim (3): For `i : Fin k`, `θ' + 9 * μ + 11 < d z (r i)`.
  have hClaim3 : ∀ i : Fin k, θ' + 9 * μ + 11 < d z (r i) := by
    intro i
    have hriA : r i ∈ H.A := Or.inr (hr_eye i).1
    have hgt := hrv₀ i
    have htri := hd_tri (r i) hriA z hZone.z_mem {v₀} hv₀A
    have hsym := hd_symm (r i) hriA z hZone.z_mem
    omega
  have hri_H' : ∀ i : Fin k, r i ∈ H'.R := by
    intro i
    have hriA : r i ∈ H.A := Or.inr (hr_eye i).1
    have hgt := hClaim3 i
    exact region_mem_R_of_mem_A hS (hr_eye i).1 (hAtoms (r i) hriA (by omega))
  have hE_ne : H.E.Nonempty := edges_nonempty_of_tangle hS hMetric.1 (by omega)
  -- Claim (4): For `i : Fin k`, `θ' ≤ d₁ Λ (r i)`.
  have hClaim4 : ∀ i : Fin k, θ' ≤ d₁ Λ (r i) := by
    exact distance_from_cleared_region (S := S) (α := α) (β := β) G H η θ θ' μ k T d r z
      Λ T₁ d₁ hr_eye hZone hClear hS hd_symm hd_tri hd_inc hΛA hSubH' v₀ hv₀H hv₀_cl hv₀A hrv₀
      hri_H' hE_ne
  -- Construct the lifted embedding `η'_G : SpanEmbedding H' G`.
  have hJ₀_le_G : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le_G
  have hG₀_le_G : G₀ ≤ G := subgraphSUnion_le hPair_le
  let η'_G : SpanEmbedding H' G :=
    { imageGraph := η'.imageGraph
      vMap := η'.vMap
      eMap := η'.eMap
      imageGraph_le := η'.imageGraph_le.trans hG₀_le_G
      bijOn_v := η'.bijOn_v
      bijOn_e := η'.bijOn_e
      inc_iff := η'.inc_iff }
  have hη'_G_v : ∀ v ∈ H'.V, η'_G.vMap v = η.vMap v :=
    fun v hv => (hη'_v v hv).trans (hη₀_v v (hSubH'.1 hv))
  have hη'_G_e : ∀ e ∈ H'.E, η'_G.eMap e = η.eMap e :=
    fun e he => (hη'_e e he).trans (hη₀_e e (hSubH'.2 he))
  have hV_sub_im : V(η'_G.imageGraph) ⊆ V(η.imageGraph) := by
    rw [← η'.bijOn_v.image_eq, ← η.bijOn_v.image_eq]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hSubH'.1 hv, (hη'_G_v v hv).symm⟩
  have hE_sub_im : E(η'_G.imageGraph) ⊆ E(η.imageGraph) := by
    rw [← η'.bijOn_e.image_eq, ← η.bijOn_e.image_eq]
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, hSubH'.2 he, (hη'_G_e e he).symm⟩
  -- Claim (5): For `i : Fin k`, `r i` is an eye of `H', T₁` in `G`.
  have hClaim5 : ∀ i : Fin k, IsDrawingEye G H' η'_G θ₁ T₁ (r i) := by
    exact eye_survives_clearing (S := S) (α := α) (β := β) G H η θ θ' lam' μ k T d r z Λ T₁ d₁
      hMetric hμ12 hlam'4 hθ' hθ'_gt hr_eye hZone hS hd_tri hd_inc hΛA h2cell' hd₁_refl
      hComp₁ hAtoms v₀ hzv₀ hClaim3 hri_H' hE_ne hClaim4 η'_G hη'_G_v hV_sub_im hE_sub_im
  -- Also `Λ` is an eye of `H', T₁` in `G`.
  have hEyeΛ_G : IsDrawingEye G H' η'_G θ₁ T₁ Λ := by
    rcases hEyeΛ with
      ⟨hΛ_R, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub, hC_U, ha, hb, hc, hd_v,
        hnodup, hord, hFree, hdisj, hP₁, hP₂⟩
    have hFree' : IsFreeSet H'.toHypergraph T₁ θ₁ {a, b, c, d_v} := hθ₁_eq ▸ hFree
    have hP₁' : IsHPathWithEnds G η'_G.imageGraph P₁ (η'_G.vMap a) (η'_G.vMap c) :=
      ⟨η'_G.imageGraph_le, ⟨hP₁.2.1.1.trans hG₀_le_G, hP₁.2.1.2⟩, hP₁.2.2⟩
    have hP₂' : IsHPathWithEnds G η'_G.imageGraph P₂ (η'_G.vMap b) (η'_G.vMap d_v) :=
      ⟨η'_G.imageGraph_le, ⟨hP₂.2.1.1.trans hG₀_le_G, hP₂.2.1.2⟩, hP₂.2.2⟩
    exact ⟨hΛ_R, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub, hC_U, ha, hb, hc, hd_v,
      hnodup, hord, hFree', hdisj, hP₁', hP₂'⟩
  -- Claim (6): By (4.6) and (5.2), `H', η'_G, T₁` is `(lam', μ)`-flat.
  have hV_rearr : ∀ v ∈ H.V, lam₁ < d z {v} → v ∈ H'.V ∧ η'_G.vMap v = η.vMap v := by
    intro v hv hlt
    have hv' : v ∈ H'.V :=
      vertex_mem_V_of_mem_A hS hv (hAtoms {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩)) hlt)
    exact ⟨hv', hη'_G_v v hv'⟩
  have hE_rearr : ∀ e ∈ H.E, lam₁ < d z e → e ∈ H'.E ∧ η'_G.eMap e = η.eMap e := by
    intro e he hlt
    have he' : e ∈ H'.E :=
      edge_mem_E_of_mem_A hS he (hAtoms e (Or.inl (Or.inr he)) hlt)
    exact ⟨he', hη'_G_e e he'⟩
  have hRearr : IsRearrangedWithin G H H' η η'_G θ_star θ lam₁ T_star T T₁ d d₁ z :=
    theorem_4_6_proof G H H' η η'_G θ_star θ lam₁ T_star T T₁ d d₁ z
      hFlat.isSpan hMetric hZone.z_mem (by omega) (by omega) hRigid' h2cell'
      hAtoms hV_rearr hE_rearr hComp₁
  have hFlat₁ : IsFlatSpan G H' η'_G θ_star θ₁ lam' μ T_star T₁ :=
    theorem_5_2_proof G H H' η η'_G θ_star θ lam lam₁ lam' μ T_star T T₁ d d₁ z
      hFlat (by omega) (by omega) hlam'4 hlam hRearr
  -- Claim (7): Apply (7.1) to `H', η'_G, T₁, d₁` with `k + 1` eyes `Fin.snoc r Λ`.
  let r' : Fin (k + 1) → Set S := Fin.snoc r Λ
  have hr'_inj : Injective r' := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j₀ =>
        exfalso
        simp only [r', Fin.snoc_last, Fin.snoc_castSucc] at hij
        have hge := hClaim4 j₀
        rw [← hij, hd₁_refl Λ hΛA] at hge
        omega
    | cast i₀ =>
      induction j using Fin.lastCases with
      | last =>
        exfalso
        simp only [r', Fin.snoc_last, Fin.snoc_castSucc] at hij
        have hge := hClaim4 i₀
        rw [hij, hd₁_refl Λ hΛA] at hge
        omega
      | cast j₀ =>
        simp only [r', Fin.snoc_castSucc] at hij
        exact congrArg Fin.castSucc (hr_inj hij)
  have hr'_eye : ∀ i : Fin (k + 1), IsDrawingEye G H' η'_G θ₁ T₁ (r' i) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [r', Fin.snoc_last]
      exact hEyeΛ_G
    | cast i₀ =>
      simp only [r', Fin.snoc_castSucc]
      exact hClaim5 i₀
  have hr'_dist : ∀ i j : Fin (k + 1), i ≠ j → θ' ≤ d₁ (r' i) (r' j) := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact False.elim (hij rfl)
      | cast j₀ =>
        simp only [r', Fin.snoc_last, Fin.snoc_castSucc]
        exact hClaim4 j₀
    | cast i₀ =>
      induction j using Fin.lastCases with
      | last =>
        simp only [r', Fin.snoc_last, Fin.snoc_castSucc]
        rw [hd₁_symm (r i₀) (Or.inr (hri_H' i₀)) Λ hΛA]
        exact hClaim4 i₀
      | cast j₀ =>
        simp only [r', Fin.snoc_castSucc]
        have hij₀ : i₀ ≠ j₀ := fun h => hij (congrArg Fin.castSucc h)
        have hd_ij := hr_dist i₀ j₀ hij₀
        have hbd := (hClear.dist_bounds (r i₀) (Or.inr (hr_eye i₀).1) (r j₀) (Or.inr (hr_eye j₀).1)
          (r i₀) (Or.inr (hri_H' i₀)) (r j₀) (Or.inr (hri_H' j₀)) Subset.rfl Subset.rfl).1
        omega
  exact theorem_7_1_proof G H' η'_G θ_star θ₁ θ' lam' μ (k + 1) T_star T₁ d₁
    hFlat₁ hM₁ (by omega) hθ' (by omega) (by omega) ⟨r', hr'_inj, hr'_eye, hr'_dist⟩

/-- Statement of Graph Minors XV, (7.4) (page 137):
"If (S1) does not hold, there is a* $\mathcal{T}$*-local 3-segregation* $\mathcal{S}_0$ *of*
$G_0$ *and an arrangement* $\alpha_0$ *of it in* $\Sigma$ *compatible with* $H$." -/
def GM15Theorem74Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam lam' μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    12 ≤ μ → Even μ → 4 ≤ lam' → 4 * lam' + μ + 2 ≤ θ' → 6 * μ + 14 < θ' →
    6 * (3 * μ + 3) + 5 * lam' + 3 * μ + 4 ≤ lam →
    θ' + 16 * μ + 17 ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    ¬ IsMuSteppedSpan (section7G0 G H η d θ' μ r) H η₀ d μ →
    ¬ Section7S1 S G θ_star T_star k μ lam' θ' →
    ∃ (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S),
      IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ ∧
      IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ ∧
      IsSurfaceArrangement S₀ α₀_disc α₀_pt ∧
      IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt

/-- **Graph Minors XV, (7.4)** (page 137):
If `(S1)` does not hold, there is a `T`-local 3-segregation `S₀` of `G₀` and an arrangement `α₀`
of it in `Σ` compatible with `H`.
Proved from `(7.3)` (`theorem_7_3_proof`) and Graph Minors XIV, `(10.1)`
(`GM14Theorem101Statement`). -/
theorem theorem_7_4_proof
     :
    GM15Theorem74Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam lam' μ k T_star T d r η₀
    hFlat hMetric hμ12 hμ_even hlam'4 hθ' hθ'_gt hlam hθ hr_inj hr_eye hr_dist
    hη₀_v hη₀_e hnot_step hnot_S1
  have hClosed : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x => by
      by_contra hx
      exact Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have h16μ : 16 * μ + 17 ≤ θ := le_trans (Nat.le_add_left _ _) hθ
  have h12μ : θ' + 12 * μ + 14 ≤ θ := by
    have : θ' + 12 * μ + 14 ≤ θ' + 16 * μ + 17 := by omega
    exact this.trans hθ
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : section7G0 G H η d θ' μ r ≤ G := subgraphSUnion_le hPair_le
  have hfinV₀ : V(section7G0 G H η d θ' μ r).Finite :=
    hFlat.isSpan.isControlling.isTangle_star.finite_V.subset hG₀_le.vertexSet_mono
  have hfinE₀ : E(section7G0 G H η d θ' μ r).Finite :=
    hFlat.isSpan.isControlling.isTangle_star.finite_E.subset hG₀_le.edgeSet_mono
  apply GraphMinor.GM14.gm14_theorem_10_1.{u, v, w} (section7G0 G H η d θ' μ r) H η₀ θ μ T d
    hClosed hConn hfinV₀ hfinE₀
    hFlat.isSpan.isRigid hMetric hμ12 hμ_even h16μ hnot_step
  intro z Λ T' d' η' hZone hClear hRigid' hη'_v hη'_e hEye
  exact hnot_S1 (theorem_7_3_proof G H η θ_star θ θ' lam lam' μ k
    T_star T d r η₀ z Λ T' d' η'
    hFlat hMetric hμ12 hlam'4 hθ' hθ'_gt hlam h12μ hr_inj hr_eye hr_dist
    hη₀_v hη₀_e hZone hClear hRigid' hη'_v hη'_e hEye)

/-- Data and properties produced by Graph Minors XV, (7.5) (page 138) for an eye `r_i` (`i : Fin
k`). -/
structure Section75EyeData {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' π beta μ : ℕ) {k : ℕ}
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k) where
  /-- The `(3β + 3)`-zone `Λ_i` around `r_i`. -/
  Λ : Set S
  /-- The closed disc `Δ_i ⊆ Σ`. -/
  Δ : Set S
  /-- The cleared `(12β + 14)`-compression `T₁` of `T` in `H ∩ (Σ - Λ_i)`. -/
  T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))
  /-- The metric `d₁` of `T₁`. -/
  d₁ : Set S → Set S → ℕ
  /-- The restricted span embedding of `H ∩ (Σ - Λ_i)` into `G`. -/
  clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G
  /-- The society `(G₀ ∪ J_i, Ω_i)` where `Ω_i` is a natural order of `V(H) ∩ bd(Λ_i)` from
  `bd(Λ_i)`. -/
  clearedSociety : Society α β
  /-- The society `(G_i*, Ω_i*) = (J_i ∪ α₀⁻¹(Δ_i), α₀⁻¹(bd(Δ_i)))`. -/
  localSociety : Society α β
  /-- `Λ_i` is a `(3β + 3)`-zone around `r_i`. -/
  isZone : IsLambdaZoneAround H d (3 * beta + 3) (r i) Λ
  /-- `T₁` is the tangle of order `θ - 4(3β + 3) - 2` obtained by clearing `Λ_i`. -/
  isCleared : IsClearedTangle H T d θ (3 * beta + 3) Λ T₁ d₁
  /-- `H ∩ (Σ - Λ_i), clearedEmbedding, T₁` is a `Σ`-span of order `θ - 4(3β + 3) - 2` obtained from
  `H, η, T`
  by rearranging within `3β + 3` of `r_i`. -/
  isRearranged : IsRearrangedWithin G H (clearedSubdrawing H Λ) η clearedEmbedding
    θ_star θ (3 * beta + 3) T_star T T₁ d d₁ (r i)
  /-- `(H ∩ (Σ - Λ_i)) ∩ bd(Λ_i)` is a circuit and `bd(Λ_i)` is an `O`-arc. -/
  isCircuit_bd : ((clearedSubdrawing H Λ).interSet (subBd Λ)).IsCircuit
  /-- `Λ_i` is a region of `H ∩ (Σ - Λ_i)`. -/
  mem_R_cleared : Λ ∈ (clearedSubdrawing H Λ).R
  /-- `Δ_i` is a closed disc with `bd(Δ_i)` `α₀`-normal. -/
  isClosedDisc_Δ : IsClosedDisc Δ
  /-- `bd(Δ_i)` is `α₀`-normal. -/
  isNormal_bd : IsArrangementNormal S₀ α₀_disc α₀_pt (subBd Δ)
  /-- `clearedSociety.G ≤ G`. -/
  soc_Λ_le : clearedSociety.G ≤ G
  /-- `clearedSociety.G = G₀ ∪ J_i`. -/
  soc_Λ_G : clearedSociety.G = subgraphUnion G (section7G0 G H η d θ' μ r)
    (eyeBridgeUnion G H η d θ' μ
    (r i))
  /-- `clearedEmbedding` agrees with `η` on vertices of `H ∩ (Σ - Λ_i)`. -/
  vMap_eq : ∀ v ∈ (clearedSubdrawing H Λ).V, clearedEmbedding.vMap v = η.vMap v
  /-- `clearedEmbedding` agrees with `η` on edges of `H ∩ (Σ - Λ_i)`. -/
  eMap_eq : ∀ e ∈ (clearedSubdrawing H Λ).E, clearedEmbedding.eMap e = η.eMap e
  /-- `clearedSociety.Ω.bar = clearedEmbedding.vMap '' ((clearedSubdrawing H Λ).V ∩ subBd Λ)`. -/
  soc_Λ_bar : clearedSociety.Ω.bar = clearedEmbedding.vMap '' ((clearedSubdrawing H Λ).V ∩ subBd Λ)
  /-- `Ω_i` is a natural order of `V(H) ∩ bd(Λ_i)` from `bd(Λ_i)`. -/
  soc_Λ_natural : ∃ inv_v : α → S,
    (∀ x ∈ clearedSociety.Ω.bar, inv_v x ∈ (clearedSubdrawing H Λ).V ∩ subBd Λ
      ∧ clearedEmbedding.vMap (inv_v x) = x) ∧
    IsNaturalOrderFrom inv_v clearedSociety.Ω (subBd Λ)
  /-- `G_i* = J_i ∪ α₀⁻¹(Δ_i)`. -/
  soc_star_G : localSociety.G = subgraphUnion G (eyeBridgeUnion G H η d θ' μ (r i))
    (arrangementPullbackGraph (section7G0 G H η d θ' μ r) S₀ α₀_disc α₀_pt Δ)
  /-- `Ω_i* = α₀⁻¹(bd(Δ_i))`. -/
  soc_star_Ω : IsPullbackPerm S₀ α₀_pt (subBd Δ) localSociety.Ω
  /-- `Λ_i ⊆ Δ_i`. -/
  Λ_subset_Δ : Λ ⊆ Δ
  /-- `(i)` `V(J_i ∩ H) ⊆ Δ_i`. -/
  bridge_V_subset_Δ : ∀ v ∈ H.V, η.vMap v ∈ V(eyeBridgeUnion G H η d θ' μ (r i)) → v ∈ Δ
  /-- `(ii)` `d(r_i, x) ≤ 3β + 6` for all `x ∈ A(H)` with `x ∩ Δ_i ≠ ∅`. -/
  dist_le_of_inter_Δ : ∀ x ∈ H.A, (x ∩ Δ).Nonempty → d (r i) x ≤ 3 * beta + 6
  /-- `(iii)` `x ⊆ Δ_i - bd(Δ_i)` for every `x ∈ A(H)` with `d(r_i, x) < β`. -/
  subset_interior_Δ_of_dist_lt : ∀ x ∈ H.A, d (r i) x < beta → x ⊆ Δ \ subBd Δ
  /-- `(iv)` `H ∩ closure(Σ - Δ_i)` has a circuit. -/
  hasCircuit_compl_Δ : ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing (H.interSet (closure
    (univ \ Δ)))
  /-- `(iv)` `H ∩ closure(Σ - Λ_i)` is rigid (Graph Minors XIV, (9.6)(iii)). The zone `Λ_i` is
  open, so `Σ - Λ_i` is closed and this is `H ∩ (Σ - Λ_i)`. -/
  isRigid_cleared : IsRigid (clearedSubdrawing H Λ)
  /-- Either (a) there is a crooked transaction `P_set` of cardinality `≥ π` in `clearedSociety`
  whose ends
  are
  free with respect to `T₁` and whose paths are `η(H ∩ (Σ - Λ_i))`-paths, or (b) `localSociety` has
  no
  crooked transaction of cardinality `π`. -/
  dichotomy :
    (∃ (P_set : Set (Graph α β)) (X : Set S),
      clearedSociety.IsCrookedTransaction P_set ∧
      π ≤ P_set.ncard ∧
      (∀ P ∈ P_set, ∀ a b : α,
        clearedSociety.IsOmegaPathWithEnds P a b →
        IsHPathWithEnds G clearedEmbedding.imageGraph P a b) ∧
      X ⊆ (clearedSubdrawing H Λ).V ∩ subBd Λ ∧
      clearedSociety.transactionEnds P_set = clearedEmbedding.vMap '' X ∧
      IsFreeSet (clearedSubdrawing H Λ).toHypergraph T₁ (θ - 4 * (3 * beta + 3) - 2) X) ∨
    (∀ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set → P_set.ncard ≠ π)

/-- Statement of Graph Minors XV, (7.5) (page 138):
"For $1 \le i \le k$ there is a $(3\beta + 3)$-zone $\Lambda_i$ around $r_i$ and a closed disc
$\Delta_i \subseteq \Sigma$ with $\text{bd}(\Delta_i)$ $\alpha_0$-normal, with the following
properties:
(i) $\Delta_1, \dots, \Delta_k$ are mutually disjoint, and for $1 \le i \le k$, $V(J_i \cap H)
\subseteq \Delta_i$
(ii) $d(r_i, x) \le 3\beta + 6$ for all $x \in A(H)$ with $x \cap \Delta_i \ne \emptyset$
(iii) $x \subseteq \Delta_i - \text{bd}(\Delta_i)$ for every $x \in A(H)$ with $d(r_i, x) < \beta$
(iv) $H \cap \overline{\Sigma - \Delta_i}$ has a circuit, and $H \cap \overline{\Sigma - \Lambda_i}$
is rigid
(v) for $1 \le i \le k$, one of the following holds:
(a) there is a crooked transaction $\mathcal{P}$ of cardinality $\pi$ in $(G_0 \cup J_i, \Omega_i)$
(where $\Omega_i$ is a natural order of $V(H) \cap \text{bd}(\Lambda_i)$ from
$\text{bd}(\Lambda_i)$)
such that $V(\mathcal{P})$ is free with respect to the $(12\beta + 14)$-compression of
$\mathcal{T}$ in $H \cap (\Sigma - \Lambda_i)$, and each $P \in \mathcal{P}$ meets $H \cap (\Sigma
- \Lambda_i)$ precisely in the ends of $P$
(b) there is no crooked transaction of cardinality $\pi$ in $(J_i \cup \alpha_0^{-1}(\Delta_i),
\alpha_0^{-1}(\text{bd}(\Delta_i)))$." -/
def GM15Theorem75Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 ≤ π → π ≠ 3 → beta = 2 * π + 8 →
    θ' + 13 * μ + 14 ≤ beta → 16 * beta + 17 ≤ θ → 6 * beta + 12 < θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ →
    IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ →
    IsSurfaceArrangement S₀ α₀_disc α₀_pt →
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt →
    ∃ D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i,
      Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ)

/-- **Graph Minors XV, (7.5), Claim (1)** (page 138):
"For* $1 \le i \le k$, *every* $v \in V(J_i \cap H)$ *satisfies* $d(r_i, v) \le \theta' +
13\mu + 13$." -/
theorem theorem_7_5_claim_1 {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ' lam μ k : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Fin k → Set S}
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hμ1 : 1 ≤ μ)
    (hr_eye : ∀ i : Fin k, IsDrawingEye G H η θ T (r i))
    (i : Fin k) {v : S} (hvH : v ∈ H.V)
    (hvJ : η.vMap v ∈ V(eyeBridgeUnion G H η d θ' μ (r i))) :
    d (r i) {v} ≤ θ' + 13 * μ + 13 := by
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨_, _, _, _, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  simp only [eyeBridgeUnion, vertexSet_subgraphSUnion, mem_iUnion] at hvJ
  obtain ⟨B, ⟨hB, _, ⟨hzB, u, ⟨huH, huZ⟩, rfl⟩⟩, hvB⟩ := hvJ
  obtain ⟨a, ⟨haA, hd_ra⟩, hua⟩ := mem_iUnion₂.mp huZ
  have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, huH, rfl⟩)
  have hua_eq : {u} = a := atom_eq_of_mem huA haA (mem_singleton u) hua
  have hd_ru : d (r i) {u} ≤ θ' + 12 * μ + 14 := hua_eq ▸ hd_ra
  by_cases huv : u = v
  · subst huv
    omega
  · have huv_map : η.vMap u ≠ η.vMap v := fun hEq => huv (η.bijOn_v.injOn huH hvH hEq)
    obtain ⟨P, hP⟩ := exists_isHPathWithEnds_of_isBridge hB hzB hvB
      (η.bijOn_v.mapsTo huH) (η.bijOn_v.mapsTo hvH) huv_map
    have hd_uv : d {u} {v} < μ := by
      by_contra hge
      have hord := hFlat.order_ge
      exact not_isMuSteppedSpan_of_isFlatSpan hFlat hMetric (by omega)
        ⟨P, u, v, huH, hvH, hP, Nat.not_lt.mp hge⟩
    have hriA : r i ∈ H.A := Or.inr (hr_eye i).1
    have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
    have htri := hd_tri (r i) hriA {u} huA {v} hvA
    omega

/-- **Graph Minors XV, (7.5)** (pages 138–139):
For `1 ≤ i ≤ k`, there is a `(3β + 3)`-zone `Λ_i` around `r_i` and a closed disc `Δ_i ⊆ Σ` with
`bd(Δ_i)` `α₀`-normal satisfying `(i)`–`(v)` of `(7.5)`.
Proved from Claim `(1)` (`theorem_7_5_claim_1`), `(4.6)` (`theorem_4_6_proof`), and Graph Minors
XIV,
`(9.6)` (`GM14Theorem96Statement`). -/
theorem theorem_7_5_proof
     :
    GM15Theorem75Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt
    hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hθ'_beta h16beta h6beta
    hr_inj hr_eye hr_dist hη₀_v hη₀_e hThree hLocal hArr₀ hCompat₀
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨_, _, _, hd_symm, hd_tri, _⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  have hπ1 : π ≠ 1 := by omega
  have hbeta_ge : 2 * π + 8 ≤ beta := by omega
  have hbeta_even : Even beta := ⟨π + 4, by omega⟩
  have hex : ∀ i : Fin k,
      Nonempty (Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i) := by
    intro i
    let B_J : Set (Graph α β) :=
      {B : Graph α β | IsBridge G η.imageGraph B ∧
        (V(B) ∩ (η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ (r i)))).Nonempty}
    let B_rem : Set (Graph α β) :=
      {B : Graph α β | IsBridge G η.imageGraph B ∧
        Disjoint V(B) (⋃ j : Fin k, η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ (r j)))}
    let J := eyeBridgeUnion G H η d θ' μ (r i)
    let G₀ := section7G0 G H η d θ' μ r
    let G_i := subgraphUnion G G₀ J
    have hDisj_B : Disjoint B_J B_rem := by
      refine Set.disjoint_left.mpr fun B hBJ hBrem => ?_
      obtain ⟨x, hxB, hxZ⟩ := hBJ.2
      exact Set.disjoint_left.mp hBrem.2 hxB (mem_iUnion.mpr ⟨i, hxZ⟩)
    have hDist_J : ∀ v ∈ H.V, η.vMap v ∈ V(J) → d (r i) {v} < beta := by
      intro v hvH hvJ
      have hle := theorem_7_5_claim_1 hFlat hMetric hμ1 hr_eye i hvH hvJ
      omega
    have hriA : r i ∈ H.A := Or.inr (hr_eye i).1
    obtain ⟨Λ, Δ, T₁, d₁, clearedEmbedding, clearedSociety, localSociety,
        hZone, hClear, hDisc_Δ, hNorm_bd, hΛ_sub_Δ,
        hDist_Δ, hSub_int, hCirc_compl, hRigid_Λ,
        hη_Λ_v, hη_Λ_e, hsoc_Λ_G, hsoc_Λ_bar, hsoc_Λ_nat,
        hsoc_star_G, hsoc_star_Ω, hDich⟩ :=
      GraphMinor.GM14.gm14_theorem_9_6.{u, v, w} G G_i G₀ J B_J B_rem H η η₀ θ π beta T d
        (r i) S₀ α₀_disc α₀_pt
        hS hConn hFlat.isSpan.isControlling.isTangle_star.finite_V
        hFlat.isSpan.isControlling.isTangle_star.finite_E
        hFlat.isSpan.isRigid hMetric hriA
        hπ1 hπ3 hbeta_ge hbeta_even h16beta
        (fun _ hB => hB.1) (fun _ hB => hB.1) hDisj_B
        rfl rfl rfl hη₀_v hη₀_e hDist_J hThree hLocal hArr₀ hCompat₀
    have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
      subgraphSUnion_le (fun _ hB => hB.1.2.1)
    have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
        Q ≤ G := by
      rintro Q (rfl | rfl)
      · exact η.imageGraph_le
      · exact hJ₀_le
    have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
    have hJ_le : J ≤ G := subgraphSUnion_le (fun _ hB => hB.1.2.1)
    have hsoc_Λ_le : clearedSociety.G ≤ G := by
      rw [hsoc_Λ_G]
      exact subgraphUnion_le hG₀_le hJ_le
    have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
    let H' := clearedSubdrawing H Λ
    let lam₁ := 3 * beta + 3
    let θ₁ := θ - (4 * lam₁ + 2)
    have hθ₁_eq : θ - 4 * lam₁ - 2 = θ₁ := by omega
    obtain ⟨hΛR, hatom'⟩ := clearedSubdrawing_mem_R_and_atom hZone
    have hSubH' : H'.IsSubdrawing H := clearedSubdrawing_isSubdrawing H Λ
    have h2cell' : (PaintingOrDrawing.drawing H').IsTwoCell :=
      clearedSubdrawing_isTwoCell hMetric.1.1 hZone
    obtain ⟨hV_H', hE_H'⟩ := clearedSubdrawing_V_and_E hZone
    have hM₁ : HasTangleMetric H' θ₁ T₁ d₁ := hθ₁_eq ▸ hClear.hasMetric
    have hComp₁ : IsLambdaCompression H H' θ (4 * lam₁ + 2) T T₁ d d₁ := by
      refine ⟨by omega, hMetric, hM₁, fun σ₁ σ₂ => ?_⟩
      obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
      obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
      obtain ⟨a₁', ha₁', hσ₁'⟩ := exists_atom_of_point H' σ₁
      obtain ⟨a₂', ha₂', hσ₂'⟩ := exists_atom_of_point H' σ₂
      rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, pointDist_eq_of_mem_atom ha₁' ha₂' hσ₁' hσ₂']
      have hsub₁ := atom_subset_of_isSubdrawing hSubH' ha₁ ha₁' hσ₁ hσ₁'
      have hsub₂ := atom_subset_of_isSubdrawing hSubH' ha₂ ha₂' hσ₂ hσ₂'
      have hle := (hClear.dist_bounds a₁ ha₁ a₂ ha₂ a₁' ha₁' a₂' ha₂' hsub₁ hsub₂).1
      omega
    have hAtoms : ∀ a ∈ H.A, lam₁ < d (r i) a → a ∈ H'.A := by
      intro a ha hlt
      have hnot_sub : ¬ a ⊆ closure Λ := fun hsub => by
        have := hZone.dist_le a ha hsub
        omega
      obtain ⟨σ, hσa, hσ_not_cl⟩ := Set.not_subset.mp hnot_sub
      have hσ_not_Λ : σ ∉ Λ := fun h => hσ_not_cl (subset_closure h)
      obtain ⟨a', ha', hσa'⟩ := exists_atom_of_point H' σ
      have ha'_ne : a' ≠ Λ := fun hEq => hσ_not_Λ (hEq ▸ hσa')
      have ha'H : a' ∈ H.A := hatom' a' ha' ha'_ne
      exact atom_eq_of_mem ha ha'H hσa hσa' ▸ ha'
    have hV_rearr : ∀ v ∈ H.V, lam₁ < d (r i) {v} →
        v ∈ H'.V ∧ clearedEmbedding.vMap v = η.vMap v := by
      intro v hv hlt
      have hv' : v ∈ H'.V :=
        vertex_mem_V_of_mem_A hS hv (hAtoms {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩)) hlt)
      exact ⟨hv', hη_Λ_v v hv'⟩
    have hE_rearr : ∀ e ∈ H.E, lam₁ < d (r i) e →
        e ∈ H'.E ∧ clearedEmbedding.eMap e = η.eMap e := by
      intro e he hlt
      have he' : e ∈ H'.E :=
        edge_mem_E_of_mem_A hS he (hAtoms e (Or.inl (Or.inr he)) hlt)
      exact ⟨he', hη_Λ_e e he'⟩
    have hRearr : IsRearrangedWithin G H H' η clearedEmbedding
        θ_star θ lam₁ T_star T T₁ d d₁ (r i) :=
      theorem_4_6_proof G H H' η clearedEmbedding
        θ_star θ lam₁ T_star T T₁ d d₁ (r i)
        hFlat.isSpan hMetric hriA (by omega) (by omega) hRigid_Λ h2cell'
        hAtoms hV_rearr hE_rearr hComp₁
    have hbd_disj : subBd Λ ⊆ univ \ Λ := by
      intro x hx
      have hcl : IsClosed (univ \ Λ) := isClosed_univ.sdiff hZone.isOpenDisc.1
      exact hcl.closure_eq ▸ hx.2
    have hcl_bd : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
    have hInter_eq : H'.interSet (subBd Λ) = H.interSet (subBd Λ) := by
      refine Drawing.ext_of_V_E ?_ ?_
      · rw [interSet_V_of_isClosed H' hcl_bd, interSet_V_of_isClosed H hcl_bd, hV_H']
        ext x
        simp only [mem_inter_iff, mem_sdiff]
        exact ⟨fun ⟨⟨hxV, _⟩, hxbd⟩ => ⟨hxV, hxbd⟩,
          fun ⟨hxV, hxbd⟩ => ⟨⟨hxV, (hbd_disj hxbd).2⟩, hxbd⟩⟩
      · rw [interSet_E, interSet_E, hE_H']
        ext e
        simp only [mem_ofPred_eq]
        exact ⟨fun ⟨⟨heE, _⟩, hebd⟩ => ⟨heE, hebd⟩,
          fun ⟨heE, hebd⟩ => ⟨⟨heE, hebd.trans hbd_disj⟩, hebd⟩⟩
    have hCirc_bd : (H'.interSet (subBd Λ)).IsCircuit := by
      rw [hInter_eq]
      obtain ⟨C_bd, hC_bd, hCH_bd, hCU_bd⟩ :=
        exists_circuit_of_oArc hZone.isOArc_bd hZone.bd_subset_U
      have hEq_C : H.interSet (subBd Λ) = C_bd := by
        refine Drawing.ext_of_V_E ?_ ?_
        · rw [interSet_V_of_isClosed H hcl_bd]
          ext x
          simp only [mem_inter_iff]
          refine ⟨fun ⟨hxV, hxbd⟩ => ?_, fun hxC => ⟨hCH_bd.1 hxC, hCU_bd ▸ C_bd.V_subset_U hxC⟩⟩
          by_contra hxnot
          obtain ⟨e, heC, hxe⟩ := C_bd.exists_edge_of_mem (hCU_bd.symm ▸ hxbd) hxnot
          exact ((hCH_bd.2 heC).2.1 hxe).2 hxV
        · rw [interSet_E]
          ext e
          simp only [mem_ofPred_eq]
          refine ⟨fun ⟨heH, hebd⟩ => ?_,
            fun heC => ⟨hCH_bd.2 heC, hCU_bd ▸ subset_closure.trans (C_bd.closure_subset_U heC)⟩⟩
          obtain ⟨x, hxe⟩ := heH.1
          have hxnotV : x ∉ C_bd.V := fun hxC => (heH.2.1 hxe).2 (hCH_bd.1 hxC)
          obtain ⟨f, hfC, hxf⟩ := C_bd.exists_edge_of_mem (hCU_bd.symm ▸ hebd hxe) hxnotV
          have hef : e = f :=
            atom_eq_of_mem (Or.inl (Or.inr heH)) (Or.inl (Or.inr (hCH_bd.2 hfC))) hxe hxf
          exact hef ▸ hfC
      exact hEq_C ▸ hC_bd
    have hBridge_V : ∀ v ∈ H.V, η.vMap v ∈ V(J) → v ∈ Δ := fun v hvH hvJ =>
      (hSub_int {v} (.inl (.inl ⟨v, hvH, rfl⟩)) (hDist_J v hvH hvJ) (mem_singleton v)).1
    exact ⟨{
      Λ := Λ
      Δ := Δ
      T₁ := T₁
      d₁ := d₁
      clearedEmbedding := clearedEmbedding
      clearedSociety := clearedSociety
      localSociety := localSociety
      isZone := hZone
      isCleared := hClear
      isRearranged := hRearr
      isCircuit_bd := hCirc_bd
      mem_R_cleared := hΛR
      isClosedDisc_Δ := hDisc_Δ
      isNormal_bd := hNorm_bd
      soc_Λ_le := hsoc_Λ_le
      soc_Λ_G := hsoc_Λ_G
      vMap_eq := hη_Λ_v
      eMap_eq := hη_Λ_e
      soc_Λ_bar := hsoc_Λ_bar
      soc_Λ_natural := hsoc_Λ_nat
      soc_star_G := hsoc_star_G
      soc_star_Ω := hsoc_star_Ω
      Λ_subset_Δ := hΛ_sub_Δ
      bridge_V_subset_Δ := hBridge_V
      dist_le_of_inter_Δ := hDist_Δ
      subset_interior_Δ_of_dist_lt := hSub_int
      hasCircuit_compl_Δ := hCirc_compl
      isRigid_cleared := hRigid_Λ
      dichotomy := hDich.imp_right (fun hno P_set hCrook hEq => hno P_set hCrook
        (le_of_eq hEq.symm))
    }⟩
  let D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i
    :=
    fun i => Classical.choice (hex i)
  refine ⟨D, fun i j hij => Set.disjoint_left.mpr fun σ hσi hσj => ?_⟩
  obtain ⟨x, hxA, hσx⟩ := exists_atom_of_point H σ
  have hdi : d (r i) x ≤ 3 * beta + 6 := (D i).dist_le_of_inter_Δ x hxA ⟨σ, hσx, hσi⟩
  have hdj : d (r j) x ≤ 3 * beta + 6 := (D j).dist_le_of_inter_Δ x hxA ⟨σ, hσx, hσj⟩
  have hriA : r i ∈ H.A := Or.inr (hr_eye i).1
  have hrjA : r j ∈ H.A := Or.inr (hr_eye j).1
  have htri := hd_tri (r i) hriA x hxA (r j) hrjA
  have hsym := hd_symm x hxA (r j) hrjA
  have hd_ij := hr_dist i j hij
  omega

/-- Statement of Graph Minors XV, (7.6) (page 139):
"$G^*_1, \dots, G^*_k$ *are mutually disjoint." -/
def GM15Theorem76Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 * (θ' + 12 * μ + 14) + μ ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ →
    IsSurfaceArrangement S₀ α₀_disc α₀_pt →
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt →
    Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ) →
    Pairwise (fun i j : Fin k => Disjoint V((D i).localSociety.G) V((D j).localSociety.G))

/-- **Graph Minors XV, (7.6)** (page 139):
`G_1*, ..., G_k*` are mutually disjoint.
Proved from `(7.2)` (`theorem_7_2_proof`) and `(7.5)` (`Section75EyeData`). -/
theorem theorem_7_6_proof : GM15Theorem76Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
    hFlat hMetric hμ1 hθ_bound hr_inj hr_eye hr_dist hη₀_v hThree hArr₀ hCompat₀ hDisj_Δ
    i j hij
  refine Set.disjoint_left.mpr fun v' hv'i hv'j => ?_
  let G₀ := section7G0 G H η d θ' μ r
  have hmem_star : ∀ m : Fin k, v' ∈ V((D m).localSociety.G) →
      v' ∈ V(eyeBridgeUnion G H η d θ' μ (r m)) ∨
      v' ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D m).Δ) := by
    intro m hvm
    rw [(D m).soc_star_G, vertexSet_subgraphUnion] at hvm
    exact hvm
  have hmem_pullback_Δ : ∀ m : Fin k,
      v' ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D m).Δ) →
      (∃ A ∈ S₀, α₀_disc A ⊆ (D m).Δ ∧ v' ∈ V(A.G)) ∨
      (v' ∈ segregationVertices S₀ ∧ α₀_pt v' ∈ (D m).Δ) := by
    intro m hvm
    rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce] at hvm
    rcases hvm.1 with hA | hseg
    · obtain ⟨A, ⟨hA_mem, hA_sub⟩, hv'A⟩ := mem_iUnion₂.mp hA
      exact Or.inl ⟨A, hA_mem, hA_sub, hv'A⟩
    · exact Or.inr hseg
  -- Case 1: `v' ∈ V(η.imageGraph)`.
  by_cases hv'_im : v' ∈ V(η.imageGraph)
  · obtain ⟨u, huH, rfl⟩ := η.bijOn_v.surjOn hv'_im
    have hu_in_Δ : ∀ m : Fin k, η.vMap u ∈ V((D m).localSociety.G) → u ∈ (D m).Δ := by
      intro m hvm
      rcases hmem_star m hvm with hvJ | hvP
      · exact (D m).bridge_V_subset_Δ u huH hvJ
      · rcases hmem_pullback_Δ m hvP with ⟨A, hA_mem, hA_sub, hvA⟩ | ⟨hv_seg, hpt⟩
        · rw [← hη₀_v u huH] at hvA
          exact hA_sub ((hCompat₀.inter_V_iff A hA_mem u huH).mpr hvA)
        · rw [← hη₀_v u huH] at hv_seg hpt
          rwa [hCompat₀.pt_eq u huH hv_seg] at hpt
    exact Set.disjoint_left.mp (hDisj_Δ hij) (hu_in_Δ i hv'i) (hu_in_Δ j hv'j)
  -- Case 2: `v' ∉ V(η.imageGraph)`.
  · have hnot_J : ∀ m₁ m₂ : Fin k, m₁ ≠ m₂ →
        v' ∈ V((D m₂).localSociety.G) → v' ∉ V(eyeBridgeUnion G H η d θ' μ (r m₁)) := by
      intro m₁ m₂ hm₁₂ hvm₂ hvm₁
      rcases hmem_star m₂ hvm₂ with hvJ₂ | hvP₂
      · exact hv'_im ((theorem_7_2_proof G H η θ_star θ θ' lam μ k T_star T d r
          hFlat hMetric hμ1 hθ_bound hr_inj hr_eye hr_dist m₁ m₂ hm₁₂).2.2 ⟨hvm₁, hvJ₂⟩)
      · have hv'G₀ : v' ∈ V(G₀) := by
          rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce] at hvP₂
          exact hvP₂.2
        have hv'J₀ : v' ∈ V(remainingBridgeUnion G H η d θ' μ r) := by
          change v' ∈ V(section7G0 G H η d θ' μ r) at hv'G₀
          rw [section7G0, vertexSet_subgraphSUnion] at hv'G₀
          obtain ⟨Q, hQ, hv'Q⟩ := mem_iUnion₂.mp hv'G₀
          rcases hQ with rfl | rfl
          · exact False.elim (hv'_im hv'Q)
          · exact hv'Q
        simp only [eyeBridgeUnion, remainingBridgeUnion, vertexSet_subgraphSUnion, mem_iUnion]
          at hvm₁ hv'J₀
        obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩, hv'B₁⟩ := hvm₁
        obtain ⟨B₀, ⟨hB₀, hB₀_disj⟩, hv'B₀⟩ := hv'J₀
        have hB_comp : ∀ {B : Graph α β},
            IsBridge G η.imageGraph B → v' ∈ V(B) →
            ∃ C ∈ graphComponents (deleteVertices G V(η.imageGraph)),
              v' ∈ V(C) ∧
              V(B) = V(C) ∪ {w ∈ V(η.imageGraph) | ∃ e ∈ E(G), ∃ x ∈ V(C), G.IsLink e x w} := by
          intro B hB hv'B
          rcases hB.2.2 with ⟨e, _, w₁, hw₁, w₂, hw₂, _, hVB, _⟩ | ⟨C, hC, hVB, _⟩
          · rw [hVB] at hv'B
            rcases hv'B with rfl | rfl
            · exact False.elim (hv'_im hw₁)
            · exact False.elim (hv'_im hw₂)
          · have hv'C : v' ∈ V(C) := by
              rw [hVB] at hv'B
              rcases hv'B with hv'C | ⟨hv'H, _⟩
              · exact hv'C
              · exact False.elim (hv'_im hv'H)
            exact ⟨C, hC, hv'C, hVB⟩
        obtain ⟨C₁, hC₁, hv'C₁, hVB₁⟩ := hB_comp hB₁ hv'B₁
        obtain ⟨C₀, hC₀, hv'C₀, hVB₀⟩ := hB_comp hB₀ hv'B₀
        have hC_eq : C₁ = C₀ := isGraphComponent_eq_of_mem_inter hC₁ hC₀ ⟨v', hv'C₁, hv'C₀⟩
        have hVB_eq : V(B₁) = V(B₀) := by rw [hVB₁, hVB₀, hC_eq]
        have hz₁B₀ : η.vMap u₁ ∈ V(B₀) := hVB_eq ▸ hz₁B₁
        exact Set.disjoint_left.mp hB₀_disj hz₁B₀
          (mem_iUnion.mpr ⟨m₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩)
    have hv'Pi : v' ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ) :=
      (hmem_star i hv'i).resolve_left (hnot_J i j hij hv'j)
    have hv'Pj : v' ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D j).Δ) :=
      (hmem_star j hv'j).resolve_left (hnot_J j i hij.symm hv'i)
    have hseg_in_bar : ∀ {A : Society α β}, A ∈ S₀ → v' ∈ V(A.G) →
        v' ∈ segregationVertices S₀ → v' ∈ A.Ω.bar := by
      intro A hA hv'A hv'seg
      obtain ⟨A', hA', hv'A'_bar⟩ := mem_iUnion₂.mp hv'seg
      by_cases hAA' : A = A'
      · subst hAA'; exact hv'A'_bar
      · exact (hThree.1.vertex_inter_subset A hA A' hA' hAA' ⟨hv'A, A'.bar_subset hv'A'_bar⟩).1
    by_cases hv'_seg : v' ∈ segregationVertices S₀
    · have hpt_in_Δ : ∀ m : Fin k,
          v' ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D m).Δ) →
          α₀_pt v' ∈ (D m).Δ := by
        intro m hvm
        rcases hmem_pullback_Δ m hvm with ⟨A, hA_mem, hA_sub, hv'A⟩ | ⟨_, hpt⟩
        · have hv'_bar : v' ∈ A.Ω.bar := hseg_in_bar hA_mem hv'A hv'_seg
          have hpt_bd : α₀_pt v' ∈ subBd (α₀_disc A) := (hArr₀.isClosedDisc A hA_mem).2 v' hv'_bar
          have hpt_A : α₀_pt v' ∈ α₀_disc A :=
            (hArr₀.isClosedDisc A hA_mem).1.isClosed.closure_subset_iff.mpr Subset.rfl hpt_bd.1
          exact hA_sub hpt_A
        · exact hpt
      exact Set.disjoint_left.mp (hDisj_Δ hij) (hpt_in_Δ i hv'Pi) (hpt_in_Δ j hv'Pj)
    · rcases hmem_pullback_Δ i hv'Pi with ⟨A, hA_mem, hA_sub, hv'A⟩ | ⟨hseg, _⟩
      · rcases hmem_pullback_Δ j hv'Pj with ⟨A', hA'_mem, hA'_sub, hv'A'⟩ | ⟨hseg, _⟩
        · have hAA'_ne : A ≠ A' := by
            intro hEq
            subst hEq
            obtain ⟨φ_A⟩ := (hArr₀.isClosedDisc A hA_mem).1
            have hx₀ : (φ_A ⟨0, by simp [ClosedUnitDisc]⟩).1 ∈ α₀_disc A :=
              (φ_A ⟨0, by simp [ClosedUnitDisc]⟩).2
            exact Set.disjoint_left.mp (hDisj_Δ hij) (hA_sub hx₀) (hA'_sub hx₀)
          have hv'_bar : v' ∈ A.Ω.bar :=
            (hThree.1.vertex_inter_subset A hA_mem A' hA'_mem hAA'_ne ⟨hv'A, hv'A'⟩).1
          exact hv'_seg (mem_iUnion₂.mpr ⟨A, hA_mem, hv'_bar⟩)
        · exact hv'_seg hseg
      · exact hv'_seg hseg

/-- Claim (1) in the proof of Graph Minors XV, (7.7) (pages 139–140):
"For* $1 \le i \le k$, *if* $(A, \Omega) \in \mathcal{S}'$ *then* $E(G_i^* \cap A) =
\emptyset$ *and* $V(G_i^* \cap A) \subseteq \bar{\Omega}_i^*$." -/
theorem theorem_7_7_claim_1
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ' π beta μ k : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Fin k → Set S}
    {η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)}
    {S₀ : Set (Society α β)} {α₀_disc : Society α β → Set S} {α₀_pt : α → S}
    {i : Fin k}
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (hη₀_v : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (hThree : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (hArr₀ : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (hCompat₀ : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt)
    {A : Society α β} (hA : A ∈ S₀) (hA_not : ¬ α₀_disc A ⊆ D_i.Δ) :
    Disjoint E(D_i.localSociety.G) E(A.G) ∧
    V(D_i.localSociety.G) ∩ V(A.G) ⊆ D_i.localSociety.Ω.bar := by
  let G₀ := section7G0 G H η d θ' μ r
  let J_i := eyeBridgeUnion G H η d θ' μ (r i)
  let P_i := arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ
  have hA_le : A.G ≤ G₀ := hThree.1.le A hA
  have hJ_le : J_i ≤ G := subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hP_le : P_i ≤ G₀ := restrict_le.trans (G₀.induce_le inter_subset_right)
  have hseg_in_bar : ∀ {v' : α}, v' ∈ V(A.G) → v' ∈ segregationVertices S₀ → v' ∈ A.Ω.bar := by
    intro v' hv'A hv'seg
    obtain ⟨A', hA', hv'A'_bar⟩ := mem_iUnion₂.mp hv'seg
    by_cases hAA' : A = A'
    · subst hAA'; exact hv'A'_bar
    · exact (hThree.1.vertex_inter_subset A hA A' hA' hAA' ⟨hv'A, A'.bar_subset hv'A'_bar⟩).1
  obtain ⟨hinter_subBd, _⟩ :=
    inter_disc_subset_subBd_of_not_subset hS hArr₀ D_i.isClosedDisc_Δ D_i.isNormal_bd hA hA_not
  refine ⟨?_, ?_⟩
  · rw [D_i.soc_star_G, edgeSet_subgraphUnion hJ_le (hP_le.trans hG₀_le)]
    refine Set.disjoint_left.mpr ?_
    rintro e (heJ | heP) heA
    · have he_G₀ : e ∈ E(G₀) := hA_le.edgeSet_mono heA
      change e ∈ E(subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r}) at he_G₀
      rw [edgeSet_subgraphSUnion hPair_le] at he_G₀
      change e ∈ E(eyeBridgeUnion G H η d θ' μ (r i)) at heJ
      rw [eyeBridgeUnion_edgeSet] at heJ
      obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩, heB₁⟩ := mem_iUnion₂.mp heJ
      obtain ⟨Q, hQ, heQ⟩ := mem_iUnion₂.mp he_G₀
      rcases hQ with rfl | rfl
      · exact Set.disjoint_left.mp (isBridge_disjoint_edgeSet hB₁) heB₁ heQ
      · rw [remainingBridgeUnion_edgeSet] at heQ
        obtain ⟨B₀, ⟨hB₀, hB₀_disj⟩, heB₀⟩ := mem_iUnion₂.mp heQ
        have hVB_eq : V(B₁) = V(B₀) :=
          (isBridge_vertexSet_eq_of_inter hB₁ hB₀).2 e ⟨heB₁, heB₀⟩
        exact Set.disjoint_left.mp hB₀_disj (hVB_eq ▸ hz₁B₁)
          (mem_iUnion.mpr ⟨i, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩)
    · change e ∈ E(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ) at heP
      rw [arrangementPullbackGraph, edgeSet_restrict] at heP
      obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, heA'⟩ := mem_iUnion₂.mp heP.2
      have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
      exact Set.disjoint_left.mp (hThree.1.edge_disjoint A hA A' hA'_S₀ hAA'_ne) heA heA'
  · rintro x ⟨hx_star, hxA⟩
    rw [D_i.soc_star_G, vertexSet_subgraphUnion] at hx_star
    have hx_seg_and_Δ : x ∈ segregationVertices S₀ ∧ α₀_pt x ∈ D_i.Δ := by
      rcases hx_star with hxJ | hxP
      · have hx_G₀ : x ∈ V(G₀) := hA_le.vertexSet_mono hxA
        have hx_im : x ∈ V(η.imageGraph) := by
          by_contra hx_not_im
          change x ∈ V(subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r})
            at hx_G₀
          rw [vertexSet_subgraphSUnion] at hx_G₀
          obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hx_G₀
          have hxJ₀ : x ∈ V(remainingBridgeUnion G H η d θ' μ r) := by
            rcases hQ with rfl | rfl
            · exact (hx_not_im hxQ).elim
            · exact hxQ
          change x ∈ V(eyeBridgeUnion G H η d θ' μ (r i)) at hxJ
          rw [eyeBridgeUnion, vertexSet_subgraphSUnion] at hxJ
          rw [remainingBridgeUnion, vertexSet_subgraphSUnion] at hxJ₀
          obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩, hxB₁⟩ := mem_iUnion₂.mp hxJ
          obtain ⟨B₀, ⟨hB₀, hB₀_disj⟩, hxB₀⟩ := mem_iUnion₂.mp hxJ₀
          have hVB_eq : V(B₁) = V(B₀) :=
            (isBridge_vertexSet_eq_of_inter hB₁ hB₀).1 x ⟨hxB₁, hxB₀⟩ hx_not_im
          exact Set.disjoint_left.mp hB₀_disj (hVB_eq ▸ hz₁B₁)
            (mem_iUnion.mpr ⟨i, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩)
        obtain ⟨u, huH, rfl⟩ := η.bijOn_v.surjOn hx_im
        have hu_Δ : u ∈ D_i.Δ := D_i.bridge_V_subset_Δ u huH hxJ
        have hu_A : u ∈ α₀_disc A := by
          rw [hCompat₀.inter_V_iff A hA u huH, hη₀_v u huH]
          exact hxA
        obtain ⟨w, hw_bar, hwu⟩ :=
          (inter_disc_subset_subBd_of_not_subset hS hArr₀ D_i.isClosedDisc_Δ
            D_i.isNormal_bd hA hA_not).2 ⟨hu_A, hu_Δ⟩
        have hu_bdA : u ∈ subBd (α₀_disc A) := hwu ▸ (hArr₀.isClosedDisc A hA).2 w hw_bar
        have hu_mem : u ∈ {v ∈ H.V | η₀.vMap v ∈ A.Ω.bar} := by
          rw [← hCompat₀.bd_inter_eq A hA]
          exact ⟨H.V_subset_U huH, hu_bdA⟩
        have hx_bar : η.vMap u ∈ A.Ω.bar := hη₀_v u huH ▸ hu_mem.2
        have hx_seg : η.vMap u ∈ segregationVertices S₀ := mem_biUnion hA hx_bar
        have hpt_eq : α₀_pt (η.vMap u) = u := by
          rw [← hη₀_v u huH]
          exact hCompat₀.pt_eq u huH (hη₀_v u huH ▸ hx_seg)
        exact ⟨hx_seg, hpt_eq.symm ▸ hu_Δ⟩
      · change x ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ) at hxP
        rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce] at hxP
        rcases hxP.1 with hx_union | hx_seg_Δ
        · obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, hxA'⟩ := mem_iUnion₂.mp hx_union
          have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
          have hx_bars := hThree.1.vertex_inter_subset A hA A' hA'_S₀ hAA'_ne ⟨hxA, hxA'⟩
          have hx_bdA' : α₀_pt x ∈ subBd (α₀_disc A') := (hArr₀.isClosedDisc A' hA'_S₀).2 x
            hx_bars.2
          have hx_discA' : α₀_pt x ∈ α₀_disc A' :=
            (hArr₀.isClosedDisc A' hA'_S₀).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA'.1
          exact ⟨mem_biUnion hA hx_bars.1, hA'_sub hx_discA'⟩
        · exact hx_seg_Δ
    have hx_bar : x ∈ A.Ω.bar := hseg_in_bar hxA hx_seg_and_Δ.1
    have hx_bdA : α₀_pt x ∈ subBd (α₀_disc A) := (hArr₀.isClosedDisc A hA).2 x hx_bar
    have hx_discA : α₀_pt x ∈ α₀_disc A :=
      (hArr₀.isClosedDisc A hA).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA.1
    have hx_bdΔ : α₀_pt x ∈ subBd D_i.Δ := hinter_subBd ⟨hx_discA, hx_seg_and_Δ.2⟩
    rw [D_i.soc_star_Ω.1]
    exact ⟨hx_seg_and_Δ.1, hx_bdΔ⟩

/-- If each `F i` (`i : Fin k`) has `ncard ≤ 1`, then `(⋃ i : Fin k, F i).ncard ≤ k`. -/
theorem ncard_iUnion_le_of_ncard_le_one {γ : Type*} :
    ∀ (k : ℕ) (F : Fin k → Set γ), (∀ i, (F i).ncard ≤ 1) → (⋃ i : Fin k, F i).ncard ≤ k
  | 0, F, _ => by simp
  | k + 1, F, hle => by
    have hunion : (⋃ i : Fin (k + 1), F i) = F 0 ∪ ⋃ i : Fin k, F i.succ := by
      ext x
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hx⟩
        exact Fin.cases (fun h0 => Or.inl h0) (fun j hj => Or.inr ⟨j, hj⟩) i hx
      · rintro (hx | ⟨j, hx⟩)
        · exact ⟨0, hx⟩
        · exact ⟨j.succ, hx⟩
    rw [hunion]
    have h1 : (F 0 ∪ ⋃ i : Fin k, F i.succ).ncard ≤ (F 0).ncard + (⋃ i : Fin k, F i.succ).ncard :=
      ncard_union_le _ _
    have h2 : (F 0).ncard ≤ 1 := hle 0
    have h3 : (⋃ i : Fin k, F i.succ).ncard ≤ k :=
      ncard_iUnion_le_of_ncard_le_one k (fun i => F i.succ) (fun i => hle i.succ)
    omega

/-- For any member `A ∈ S_seg` of a graph segregation `S_seg` of `G₀`, there is a complementary
subgraph `B ≤ G₀` such that `(A.G, B)` is a separation of `G₀` with `V(A.G) ∩ V(B) = A.Ω.bar`. -/
private theorem exists_graphSeparation_of_mem_segregation {α : Type u} {β : Type v}
    {G₀ : Graph α β} {S_seg : Set (Society α β)} (hSeg : IsGraphSegregation G₀ S_seg)
    {A : Society α β} (hA : A ∈ S_seg) :
    ∃ B : Graph α β, IsGraphSeparation G₀ A.G B ∧ V(A.G) ∩ V(B) = A.Ω.bar := by
  have hA_le : A.G ≤ G₀ := hSeg.le A hA
  let V_B := (V(G₀) \ V(A.G)) ∪ A.Ω.bar
  let E_B := E(G₀) \ E(A.G)
  let B := (G₀.induce V_B).restrict E_B
  have hVB_sub : V_B ⊆ V(G₀) := by
    rintro v (⟨hvG₀, _⟩ | hv_bar)
    · exact hvG₀
    · exact hA_le.vertexSet_mono (A.bar_subset hv_bar)
  have hB_le : B ≤ G₀ := restrict_le.trans (G₀.induce_le hVB_sub)
  have hVB_eq : V(B) = V_B := by simp [B]
  have hEB_eq : E(B) = E_B := by
    ext e
    simp only [B, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce]
    refine ⟨fun h => h.2, fun ⟨heG₀, he_not_A⟩ => ⟨?_, ⟨heG₀, he_not_A⟩⟩⟩
    have he_union : e ∈ E(subgraphSUnion G₀ ((fun S' : Society α β => S'.G) '' S_seg)) := by
      rw [hSeg.union_eq]
      exact heG₀
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S', hS', rfl⟩; exact hSeg.le S' hS')] at he_union
    obtain ⟨_, ⟨A', hA', rfl⟩, heA'⟩ := mem_iUnion₂.mp he_union
    have hAA'_ne : A ≠ A' := fun hEq => he_not_A (hEq ▸ heA')
    obtain ⟨x, y, hxy_A'⟩ := A'.G.exists_isLink_of_mem_edgeSet heA'
    have hxy_G₀ : G₀.IsLink e x y := hxy_A'.mono (hSeg.le A' hA')
    have hmem_VB : ∀ z ∈ V(A'.G), z ∈ V_B := by
      intro z hzA'
      by_cases hzA : z ∈ V(A.G)
      · exact Or.inr (hSeg.vertex_inter_subset A hA A' hA' hAA'_ne ⟨hzA, hzA'⟩).1
      · exact Or.inl ⟨(hSeg.le A' hA').vertexSet_mono hzA', hzA⟩
    exact ⟨x, y, hxy_G₀, hmem_VB x hxy_A'.left_mem, hmem_VB y hxy_A'.right_mem⟩
  refine ⟨B, ⟨hA_le, hB_le, ?_, ?_, ?_⟩, ?_⟩
  · ext v
    rw [mem_union, hVB_eq]
    refine ⟨?_, fun hvG₀ => ?_⟩
    · rintro (hvA | hvB)
      · exact hA_le.vertexSet_mono hvA
      · exact hVB_sub hvB
    · by_cases hvA : v ∈ V(A.G)
      · exact Or.inl hvA
      · exact Or.inr (Or.inl ⟨hvG₀, hvA⟩)
  · ext e
    rw [mem_union, hEB_eq]
    refine ⟨?_, fun heG₀ => ?_⟩
    · rintro (heA | ⟨heG₀, _⟩)
      · exact hA_le.edgeSet_mono heA
      · exact heG₀
    · by_cases heA : e ∈ E(A.G)
      · exact Or.inl heA
      · exact Or.inr ⟨heG₀, heA⟩
  · rw [hEB_eq]
    exact disjoint_sdiff_self_right
  · ext v
    rw [mem_inter_iff, hVB_eq]
    constructor
    · rintro ⟨hvA, ⟨_, hv_not_A⟩ | hv_bar⟩
      · exact (hv_not_A hvA).elim
      · exact hv_bar
    · intro hv_bar
      exact ⟨A.bar_subset hv_bar, Or.inr hv_bar⟩


/-- Statement of Graph Minors XV, (7.7) (page 139):
"If there is no crooked transaction of cardinality* $\pi$ *in* $(G_i^*, \Omega_i^*)$ *for* $1
\le i \le k$, *then (S3) holds." -/
def GM15Theorem77Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 ≤ π → π ≠ 3 → beta = 2 * π + 8 →
    θ' + 13 * μ + 14 ≤ beta → 100 * beta ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ →
    IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ →
    IsSurfaceArrangement S₀ α₀_disc α₀_pt →
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt →
    Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ) →
    (∀ i : Fin k, ∀ P_set : Set (Graph α β),
      (D i).localSociety.IsCrookedTransaction P_set → P_set.ncard ≠ π) →
    Section7S3 S G T_star (3 * π + 9) k

/-- The retained societies and the local eye segregations together segregate the original graph. -/
theorem assemble_eye_segregation
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (θ' : ℕ)
    (π : ℕ)
    (beta : ℕ)
    (μ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S)
    (α₀_pt : α → S)
    (D : (i : Fin k) → Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt
      i)
    (hη₀_v : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (hThree : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (hArr₀ : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (hCompat₀ : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt)
    (hS : IsClosedSurface S)
    (hDisj_star : Pairwise fun i j => Disjoint V((D i).localSociety.G) V((D j).localSociety.G)) :
    let G₀ : Graph α β := section7G0 G H η d θ' μ r
    (∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)), Q ≤ G) →
    (∀ (i : Fin k), eyeBridgeUnion G H η d θ' μ (r i) ≤ G) →
    (∀ (i : Fin k), arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ ≤ G) →
    (∀ (i : Fin k), (D i).localSociety.G ≤ G) →
    ∀ (S_seg : Fin k → Set (Society α β)),
    (∀ (i : Fin k), IsSegregationOfType (D i).localSociety.G (3 * π + 9) 1 (S_seg i)) →
    (∀ (i : Fin k), (D i).localSociety.Ω.bar ⊆ segregationVertices (S_seg i)) →
    let S' : Set (Society α β) := {A | A ∈ S₀ ∧ ∀ (i : Fin k), ¬α₀_disc A ⊆ (D i).Δ}
    let S_seg' : Fin k → Set (Society α β) := fun i => {B | B ∈ S_seg i ∧ V(B.G).Nonempty ∧ B ∉
      S'}
    let S_final : Set (Society α β) := S' ∪ ⋃ i, S_seg' i
    (S_final.Finite) →
    (∀ B ∈ S_final, B.G ≤ G) →
    (∀ (i : Fin k) {v : α}, v ∈ V((D i).localSociety.G) → ∃ B ∈ S_final, v ∈
      V(B.G)) →
    (∀ (i : Fin k) {e : β}, e ∈ E((D i).localSociety.G) → ∃ B ∈ S_final, e ∈
      E(B.G)) →
    IsGraphSegregation G S_final := by
  intro G₀ hPair_le hJi_le hPi_le hstar_le S_seg hType_i hBar_i S' S_seg' S_final hFin_final
    hLe_final hCover_star_V hCover_star_E
  refine ⟨hFin_final, hLe_final, ?_, ?_, ?_⟩
  · have hU_le : subgraphSUnion G ((fun B : Society α β => B.G) '' S_final) ≤ G :=
      subgraphSUnion_le (by rintro _ ⟨B, hB, rfl⟩; exact hLe_final B hB)
    refine (Compatible.of_le_le hU_le le_rfl).ext ?_ ?_
    · ext v
      rw [vertexSet_subgraphSUnion]
      refine ⟨fun h => hU_le.vertexSet_mono (vertexSet_subgraphSUnion _ _ ▸ h), fun hvG => ?_⟩
      by_cases hex_i_v : ∃ i : Fin k, v ∈ V((D i).localSociety.G)
      · obtain ⟨i, hvi⟩ := hex_i_v
        obtain ⟨B, hB_fin, hvB⟩ := hCover_star_V i hvi
        exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB_fin, rfl⟩, hvB⟩
      · push Not at hex_i_v
        have hvG₀ : v ∈ V(G₀) := by
          by_cases hv_im : v ∈ V(η.imageGraph)
          · exact (le_subgraphSUnion hPair_le (Or.inl rfl)).vertexSet_mono hv_im
          · obtain ⟨B, hB, hvB⟩ := exists_bridge_of_mem_vertexSet η.imageGraph_le hvG hv_im
            have hB_disj : Disjoint V(B) (⋃ i : Fin k, η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ
              (r i))) := by
              refine Set.disjoint_left.mpr fun z hzB hz_u => ?_
              obtain ⟨i, hz_i⟩ := mem_iUnion.mp hz_u
              have hv_Ji : v ∈ V(eyeBridgeUnion G H η d θ' μ (r i)) := by
                rw [eyeBridgeUnion, vertexSet_subgraphSUnion]
                exact mem_iUnion₂.mpr ⟨B, ⟨hB, z, hzB, hz_i⟩, hvB⟩
              have hv_star : v ∈ V((D i).localSociety.G) := by
                rw [(D i).soc_star_G, vertexSet_subgraphUnion]
                exact Or.inl hv_Ji
              exact hex_i_v i hv_star
            have hv_J₀ : v ∈ V(remainingBridgeUnion G H η d θ' μ r) := by
              rw [remainingBridgeUnion, vertexSet_subgraphSUnion]
              exact mem_iUnion₂.mpr ⟨B, ⟨hB, hB_disj⟩, hvB⟩
            exact (le_subgraphSUnion hPair_le (Or.inr rfl)).vertexSet_mono hv_J₀
        have hv_u : v ∈ V(subgraphSUnion G₀ ((fun A : Society α β => A.G) '' S₀)) := by
          rw [hThree.1.union_eq]; exact hvG₀
        rw [vertexSet_subgraphSUnion] at hv_u
        obtain ⟨_, ⟨A, hA_S₀, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_u
        have hA_S' : A ∈ S' := by
          refine ⟨hA_S₀, fun i hsub => hex_i_v i ?_⟩
          rw [(D i).soc_star_G, vertexSet_subgraphUnion]
          refine Or.inr ?_
          rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce]
          exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, hvA⟩), hvG₀⟩
        exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl hA_S', rfl⟩, hvA⟩
    · ext e
      rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact hLe_final B hB)]
      refine ⟨fun h => ?_, fun heG => ?_⟩
      · obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp h
        exact (hLe_final B hB).edgeSet_mono heB
      · by_cases hex_i_e : ∃ i : Fin k, e ∈ E((D i).localSociety.G)
        · obtain ⟨i, hei⟩ := hex_i_e
          obtain ⟨B, hB_fin, heB⟩ := hCover_star_E i hei
          exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB_fin, rfl⟩, heB⟩
        · push Not at hex_i_e
          have heG₀ : e ∈ E(G₀) := by
            by_cases he_im : e ∈ E(η.imageGraph)
            · exact (le_subgraphSUnion hPair_le (Or.inl rfl)).edgeSet_mono he_im
            · obtain ⟨B, hB, heB⟩ := exists_bridge_of_mem_edgeSet η.imageGraph_le heG he_im
              have hB_disj : Disjoint V(B) (⋃ i : Fin k, η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ
                (r i))) := by
                refine Set.disjoint_left.mpr fun z hzB hz_u => ?_
                obtain ⟨i, hz_i⟩ := mem_iUnion.mp hz_u
                have he_Ji : e ∈ E(eyeBridgeUnion G H η d θ' μ (r i)) := by
                  rw [eyeBridgeUnion_edgeSet]
                  exact mem_iUnion₂.mpr ⟨B, ⟨hB, z, hzB, hz_i⟩, heB⟩
                have he_star : e ∈ E((D i).localSociety.G) := by
                  rw [(D i).soc_star_G, edgeSet_subgraphUnion (hJi_le i) (hPi_le i)]
                  exact Or.inl he_Ji
                exact hex_i_e i he_star
              have he_J₀ : e ∈ E(remainingBridgeUnion G H η d θ' μ r) := by
                rw [remainingBridgeUnion_edgeSet]
                exact mem_iUnion₂.mpr ⟨B, ⟨hB, hB_disj⟩, heB⟩
              exact (le_subgraphSUnion hPair_le (Or.inr rfl)).edgeSet_mono he_J₀
          have he_u : e ∈ E(subgraphSUnion G₀ ((fun A : Society α β => A.G) '' S₀)) := by
            rw [hThree.1.union_eq]; exact heG₀
          rw [edgeSet_subgraphSUnion (by rintro _ ⟨A, hA, rfl⟩; exact hThree.1.le A hA)] at he_u
          obtain ⟨_, ⟨A, hA_S₀, rfl⟩, heA⟩ := mem_iUnion₂.mp he_u
          have hA_S' : A ∈ S' := by
            refine ⟨hA_S₀, fun i hsub => hex_i_e i ?_⟩
            rw [(D i).soc_star_G, edgeSet_subgraphUnion (hJi_le i) (hPi_le i)]
            refine Or.inr ?_
            rw [arrangementPullbackGraph, edgeSet_restrict]
            obtain ⟨x, y, hxy_A⟩ := A.G.exists_isLink_of_mem_edgeSet heA
            have hxy_G₀ : G₀.IsLink e x y := hxy_A.mono (hThree.1.le A hA_S₀)
            refine ⟨⟨x, y, hxy_G₀, ?_, ?_⟩, mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, heA⟩⟩
            · exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, hxy_A.left_mem⟩), hxy_G₀.left_mem⟩
            · exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, hxy_A.right_mem⟩),
                hxy_G₀.right_mem⟩
          exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl hA_S', rfl⟩, heA⟩
  · have hV_inter_S'_seg : ∀ (i : Fin k) {A B : Society α β},
        A ∈ S' → B ∈ S_seg i → V(A.G) ∩ V(B.G) ⊆ A.Ω.bar ∩ B.Ω.bar := by
      intro i A B hA_S' hB_i v ⟨hvA, hvB⟩
      have hv_star : v ∈ V((D i).localSociety.G) := ((hType_i i).1.le B hB_i).vertexSet_mono hvB
      have hv_bar_star : v ∈ (D i).localSociety.Ω.bar :=
        (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hA_S'.1 (hA_S'.2 i)).2
          ⟨hv_star, hvA⟩
      have hv_seg₀ : v ∈ segregationVertices S₀ := ((D i).soc_star_Ω.1 ▸ hv_bar_star).1
      have hv_seg_i : v ∈ segregationVertices (S_seg i) := hBar_i i hv_bar_star
      have hv_barA : v ∈ A.Ω.bar := by
        obtain ⟨A', hA', hvA'⟩ := mem_iUnion₂.mp hv_seg₀
        by_cases hAA' : A = A'
        · subst hAA'; exact hvA'
        · exact (hThree.1.vertex_inter_subset A hA_S'.1 A' hA' hAA' ⟨hvA, A'.bar_subset hvA'⟩).1
      have hv_barB : v ∈ B.Ω.bar := by
        obtain ⟨B', hB', hvB'⟩ := mem_iUnion₂.mp hv_seg_i
        by_cases hBB' : B = B'
        · subst hBB'; exact hvB'
        · exact ((hType_i i).1.vertex_inter_subset B hB_i B' hB' hBB' ⟨hvB, B'.bar_subset hvB'⟩).1
      exact ⟨hv_barA, hv_barB⟩
    rintro B₁ (hB₁_S' | hB₁_i) B₂ (hB₂_S' | hB₂_j) hne
    · exact hThree.1.vertex_inter_subset B₁ hB₁_S'.1 B₂ hB₂_S'.1 hne
    · obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
      exact hV_inter_S'_seg j hB₁_S' hB₂_j.1
    · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
      intro v ⟨hv1, hv2⟩
      have h := hV_inter_S'_seg i hB₂_S' hB₁_i.1 ⟨hv2, hv1⟩
      exact ⟨h.2, h.1⟩
    · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
      obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
      by_cases hij : i = j
      · subst hij
        exact (hType_i i).1.vertex_inter_subset B₁ hB₁_i.1 B₂ hB₂_j.1 hne
      · intro v ⟨hv1, hv2⟩
        exact False.elim (Set.disjoint_left.mp (hDisj_star hij)
          (((hType_i i).1.le B₁ hB₁_i.1).vertexSet_mono hv1)
          (((hType_i j).1.le B₂ hB₂_j.1).vertexSet_mono hv2))
  · rintro B₁ (hB₁_S' | hB₁_i) B₂ (hB₂_S' | hB₂_j) hne
    · exact hThree.1.edge_disjoint B₁ hB₁_S'.1 B₂ hB₂_S'.1 hne
    · obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
      have hdisj :=
        (theorem_7_7_claim_1 hS (D j) hη₀_v hThree hArr₀ hCompat₀ hB₁_S'.1 (hB₁_S'.2 j)).1
      exact hdisj.symm.mono_right ((hType_i j).1.le B₂ hB₂_j.1).edgeSet_mono
    · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
      have hdisj :=
        (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hB₂_S'.1 (hB₂_S'.2 i)).1
      exact hdisj.mono_left ((hType_i i).1.le B₁ hB₁_i.1).edgeSet_mono
    · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
      obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
      by_cases hij : i = j
      · subst hij
        exact (hType_i i).1.edge_disjoint B₁ hB₁_i.1 B₂ hB₂_j.1 hne
      · refine Set.disjoint_left.mpr fun e he1 he2 => ?_
        obtain ⟨x, _, hxy₁⟩ := B₁.G.exists_isLink_of_mem_edgeSet he1
        have hxy₂ : B₂.G.IsLink e x _ :=
          (((hType_i j).1.le B₂ hB₂_j.1).trans (hstar_le j)).isLink_iff he2 |>.mpr
            (hxy₁.mono (((hType_i i).1.le B₁ hB₁_i.1).trans (hstar_le i)))
        exact Set.disjoint_left.mp (hDisj_star hij)
          (((hType_i i).1.le B₁ hB₁_i.1).vertexSet_mono hxy₁.left_mem)
          (((hType_i j).1.le B₂ hB₂_j.1).vertexSet_mono hxy₂.left_mem)

/-- Centrality of the assembled segregation follows from the original and local tangle separations.
-/
theorem assembled_eye_segregation_is_central
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (θ' : ℕ)
    (lam : ℕ)
    (π : ℕ)
    (beta : ℕ)
    (μ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S)
    (α₀_pt : α → S)
    (D : (i : Fin k) → Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt
      i)
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hμ1 : 1 ≤ μ)
    (hπ2 : 2 ≤ π)
    (hbeta_eq : beta = 2 * π + 8)
    (hθ_ge : 100 * beta ≤ θ)
    (hr_eye : ∀ (i : Fin k), IsDrawingEye G H η θ T (r i))
    (hη₀_v : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (hη₀_e : ∀ e ∈ H.E, η₀.eMap e = η.eMap e)
    (hThree : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (hLocal : IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀)
    (hCompat₀ : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hθ_bound : 2 * (θ' + 12 * μ + 14) + μ ≤ θ) :
    let G₀ : Graph α β := section7G0 G H η d θ' μ r
    (∀ (i : Fin k), eyeBridgeUnion G H η d θ' μ (r i) ≤ G) →
    (∀ (i : Fin k), arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ ≤ G) →
    ∀ (S_seg : Fin k → Set (Society α β)),
    (∀ (i : Fin k), IsSegregationOfType (D i).localSociety.G (3 * π + 9) 1 (S_seg i)) →
    let S' : Set (Society α β) := {A | A ∈ S₀ ∧ ∀ (i : Fin k), ¬α₀_disc A ⊆ (D i).Δ}
    let S_seg' : Fin k → Set (Society α β) := fun i => {B | B ∈ S_seg i ∧ V(B.G).Nonempty ∧ B ∉
      S'}
    let S_final : Set (Society α β) := S' ∪ ⋃ i, S_seg' i
    (IsSegregationOfType G (3 * π + 9) k S_final) →
    IsCentralSegregation G T_star S_final := by
  intro G₀ hJi_le hPi_le S_seg hType_i S' S_seg' S_final hClaim3
  have hT_star := hFlat.isSpan.isControlling.isTangle_star
  have hθ_le_star := hFlat.isSpan.isControlling.theta_le
  refine theorem_2_1_proof G θ_star (3 * π + 9) k T_star S_final hT_star
    (by omega) (by omega) hClaim3 ?_
  rintro A_soc hA_soc A_star B_star hAB_star hord_le ⟨hB_sub_V, hB_sub_E⟩
  have hsep_star := hT_star.isTangle.isSeparation hAB_star
  obtain ⟨A_star_H, B_star_H, hRestr, hA_star_V, hA_star_E, hB_star_V, hB_star_E, hord_H_le⟩ :=
    GM12.exists_span_restricted_separation hT_star.finite_V hT_star.finite_E H η hsep_star
  have hAB_star_T : (A_star_H, B_star_H) ∈ T :=
    (hFlat.isSpan.isControlling.controls hsep_star (by omega) hRestr).mp hAB_star
  rcases hA_soc with hA_S' | hA_i
  · obtain ⟨B_G₀, hsep_G₀, hbar_G₀⟩ :=
      exists_graphSeparation_of_mem_segregation hThree.1 hA_S'.1
    obtain ⟨A_H, B_H, hsep_H, hAH_V, hBH_V, hAH_E, hBH_E, hAH_T⟩ :=
      hLocal A_soc hA_S'.1 B_G₀ hsep_G₀ hbar_G₀
    have hB_sub_AH_V : B_star_H.vertexSet ⊆ A_H.vertexSet := by
      intro v hv
      rw [hB_star_V] at hv
      rw [hAH_V]
      exact ⟨hv.1, hη₀_v v hv.1 ▸ hB_sub_V hv.2⟩
    have hB_sub_AH_E : B_star_H.edgeSet ⊆ A_H.edgeSet := by
      intro e he
      rw [hB_star_E] at he
      rw [hAH_E]
      exact ⟨he.1, hη₀_e e he.1 ▸ hB_sub_E he.2⟩
    have hcov : A_star_H ∪ A_H ∪ A_H = H.toHypergraph := by
      rw [GM10.union_assoc, GM10.union_self]
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (union_le hRestr.1.left_le hsep_H.left_le) le_rfl
      · ext v
        refine ⟨fun h => (union_le hRestr.1.left_le hsep_H.left_le).vertexSet_subset h,
          fun hv => ?_⟩
        rw [← hRestr.1.vertexSet_union] at hv
        exact hv.imp_right fun h => hB_sub_AH_V h
      · ext e
        refine ⟨fun h => (union_le hRestr.1.left_le hsep_H.left_le).edgeSet_subset h,
          fun he => ?_⟩
        rw [← hRestr.1.edgeSet_union] at he
        exact he.imp_right fun h => hB_sub_AH_E h
    exact hFlat.isSpan.isControlling.isTangle_H.axiom2 hAB_star_T hAH_T hAH_T hcov
  · obtain ⟨i, hAi⟩ := mem_iUnion.mp hA_i
    have hAi_le_star : A_soc.G ≤ (D i).localSociety.G := (hType_i i).1.le A_soc hAi.1
    have hB_sub_star_E : B_star.edgeSet ⊆ E((D i).localSociety.G) :=
      hB_sub_E.trans hAi_le_star.edgeSet_mono
    have hE_ne : H.E.Nonempty :=
      edges_nonempty_of_tangle hS hFlat.isSpan.isRespectful (by omega)
    have hri_A : r i ∈ H.A := Or.inr (hr_eye i).1
    have hB_ne_ri : B_star_H.edgeSet ≠ {r i} := by
      intro hEq
      have hri_E : r i ∈ H.E := by
        have : r i ∈ B_star_H.edgeSet := hEq ▸ mem_singleton (r i)
        rw [hB_star_E] at this
        exact this.1
      obtain ⟨x, hx_ri⟩ := hri_E.1
      obtain ⟨y, hy_compl, hy_eq⟩ := (hr_eye i).1
      have hx_compl : x ∈ Set.univ \ H.U :=
        connectedComponentIn_subset (Set.univ \ H.U) y (hy_eq.symm ▸ hx_ri)
      exact hx_compl.2 (hri_E.2.1 hx_ri).1
    obtain ⟨e₀, he₀_B, hd_ge⟩ :=
      gm14_theorem_7_3 H θ T d A_star_H B_star_H (r i) hS hConn hE_ne hMetric hri_A
        hAB_star_T hB_ne_ri
    rw [hB_star_E] at he₀_B
    obtain ⟨he₀_H, he₀_Bstar⟩ := he₀_B
    have he₀_star : η.eMap e₀ ∈ E((D i).localSociety.G) := hB_sub_star_E he₀_Bstar
    rw [(D i).soc_star_G, edgeSet_subgraphUnion (hJi_le i) (hPi_le i)] at he₀_star
    have he₀_P : η.eMap e₀ ∈ E(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ) := by
      rcases he₀_star with he₀_J | he₀_P
      · rw [eyeBridgeUnion_edgeSet] at he₀_J
        obtain ⟨B, ⟨hB, _⟩, he₀_B⟩ := mem_iUnion₂.mp he₀_J
        exact False.elim (Set.disjoint_left.mp (isBridge_disjoint_edgeSet hB)
          he₀_B (η.bijOn_e.mapsTo he₀_H))
      · exact he₀_P
    rw [arrangementPullbackGraph, edgeSet_restrict] at he₀_P
    obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, he₀_A'⟩ := mem_iUnion₂.mp he₀_P.2
    rw [← hη₀_e e₀ he₀_H] at he₀_A'
    have he₀_sub_Δ : e₀ ⊆ (D i).Δ :=
      ((hCompat₀.inter_E_iff A' hA'_S₀ e₀ he₀_H).mpr he₀_A').trans hA'_sub
    obtain ⟨u, hu_cl, _⟩ := edge_closure_inter_V_nonempty he₀_H
    obtain ⟨σ, hσ_e₀⟩ := closure_nonempty_iff.mp ⟨u, hu_cl⟩
    have hd_le : d (r i) e₀ ≤ 3 * beta + 6 :=
      (D i).dist_le_of_inter_Δ e₀ (Or.inl (Or.inr he₀_H)) ⟨σ, hσ_e₀, he₀_sub_Δ hσ_e₀⟩
    omega

/-- The local discs and points, together with the retained arrangement, give an arrangement of
    the assembled segregation. -/
theorem arrange_replacement_societies
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (θ' : ℕ)
    (lam : ℕ)
    (π : ℕ)
    (beta : ℕ)
    (μ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S)
    (α₀_pt : α → S)
    (D : (i : Fin k) → Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt
      i)
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hArr₀ : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (hDisj_Δ : Pairwise fun i j => Disjoint (D i).Δ (D j).Δ)
    (hS : IsClosedSurface S)
    (S_seg : Fin k → Set (Society α β))
    (α_disc_i : Fin k → Society α β → Set S)
    (α_pt_i : Fin k → α → S)
    (hBar_i : ∀ (i : Fin k), (D i).localSociety.Ω.bar ⊆ segregationVertices (S_seg i))
    (hpt_i_eq_0 : ∀ (i : Fin k), ∀ v ∈ (D i).localSociety.Ω.bar, α_pt_i i v = α₀_pt v)
    (hpt_i_mem_Δ : ∀ (i : Fin k), ∀ v ∈ segregationVertices (S_seg i), α_pt_i i v ∈ (D i).Δ)
    (hinj_i : ∀ (i : Fin k), InjOn (α_pt_i i) (segregationVertices (S_seg i)))
    (hdisc_i_closed : ∀ (i : Fin k), ∀ B ∈ S_seg i, IsClosedDisc (α_disc_i i B) ∧ α_disc_i i B ⊆
      (D i).Δ ∧ ∀ x ∈ B.Ω.bar, α_pt_i i x ∈ subBd (α_disc_i i B))
    (hnat_i : ∀ (i : Fin k), ∀ B ∈ S_seg i, IsNaturalOrderFrom (α_pt_i i) B.Ω (subBd (α_disc_i i
      B)))
    (hinter_bd_i : ∀ (i : Fin k), ∀ B ∈ S_seg i, α_disc_i i B ∩ subBd (D i).Δ ⊆ α_pt_i i ''
      (B.Ω.bar ∩ (D i).localSociety.Ω.bar))
    (hinter_discs_i : ∀ (i : Fin k), ∀ B₁ ∈ S_seg i, ∀ B₂ ∈ S_seg i, B₁ ≠ B₂ → α_disc_i i B₁ ∩
      α_disc_i i B₂ ⊆ α_pt_i i '' (B₁.Ω.bar ∩ B₂.Ω.bar)) :
    let S' : Set (Society α β) := {A | A ∈ S₀ ∧ ∀ (i : Fin k), ¬α₀_disc A ⊆ (D i).Δ}
    let S_seg' : Fin k → Set (Society α β) := fun i => {B | B ∈ S_seg i ∧ V(B.G).Nonempty ∧ B ∉
      S'}
    let S_final : Set (Society α β) := S' ∪ ⋃ i, S_seg' i
    ∀ (α_disc : Society α β → Set S),
    ∀ (α_pt : α → S),
    (∀ {B : Society α β}, B ∈ S' → α_disc B = α₀_disc B) →
    (∀ (i : Fin k) {B : Society α β}, B ∈ S_seg' i → α_disc B = α_disc_i i B) →
    (∀ (i : Fin k) {v : α}, v ∈ segregationVertices (S_seg i) → α_pt v = α_pt_i i v) →
    (∀ {v : α}, v ∈ segregationVertices S' → α_pt v = α₀_pt v) →
    IsSurfaceArrangement S_final α_disc α_pt := by
  intro S' S_seg' S_final α_disc α_pt hα_disc_S' hα_disc_seg' hClaim5 hα_pt_S'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Claim (6): `IsClosedDisc (α_disc B)` and `∀ x ∈ B.Ω.bar, α_pt x ∈ subBd (α_disc B)`.
    rintro B (hB_S' | hB_i)
    · rw [hα_disc_S' hB_S']
      refine ⟨(hArr₀.isClosedDisc B hB_S'.1).1, fun x hx => ?_⟩
      rw [hα_pt_S' (mem_biUnion hB_S' hx)]
      exact (hArr₀.isClosedDisc B hB_S'.1).2 x hx
    · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
      rw [hα_disc_seg' i hBi]
      refine ⟨(hdisc_i_closed i B hBi.1).1, fun x hx => ?_⟩
      rw [hClaim5 i (mem_biUnion hBi.1 hx)]
      exact (hdisc_i_closed i B hBi.1).2.2 x hx
  · -- Claim (7): Intersection of two discs `α_disc B₁ ∩ α_disc B₂` for `B₁ ≠ B₂`.
    have hinter_seg_S' : ∀ (i : Fin k) {B A : Society α β},
        B ∈ S_seg' i → A ∈ S' →
        α_disc B ∩ α_disc A ⊆ α_pt '' (B.Ω.bar ∩ A.Ω.bar) := by
      intro i B A hBi hA_S' x ⟨hxB, hxA⟩
      rw [hα_disc_seg' i hBi] at hxB
      rw [hα_disc_S' hA_S'] at hxA
      have hx_Δ : x ∈ (D i).Δ := (hdisc_i_closed i B hBi.1).2.1 hxB
      have hx_bdΔ : x ∈ subBd (D i).Δ :=
        (inter_disc_subset_subBd_of_not_subset hS hArr₀ (D i).isClosedDisc_Δ
          (D i).isNormal_bd hA_S'.1 (hA_S'.2 i)).1 ⟨hxA, hx_Δ⟩
      obtain ⟨v, hvA_bar, rfl⟩ := (D i).isNormal_bd A hA_S'.1 ⟨hx_bdΔ, hxA⟩
      obtain ⟨w, ⟨hwB_bar, hw_star_bar⟩, hw_eq⟩ := hinter_bd_i i B hBi.1 ⟨hxB, hx_bdΔ⟩
      have hw_eq_0 : α₀_pt w = α₀_pt v := by
        rw [← hpt_i_eq_0 i w hw_star_bar, hw_eq]
      have hv_seg₀ : v ∈ segregationVertices S₀ := mem_biUnion hA_S'.1 hvA_bar
      have hw_seg₀ : w ∈ segregationVertices S₀ := ((D i).soc_star_Ω.1 ▸ hw_star_bar).1
      have hvw : w = v := hArr₀.injOn_pts hw_seg₀ hv_seg₀ hw_eq_0
      subst hvw
      refine ⟨w, ⟨hwB_bar, hvA_bar⟩, ?_⟩
      exact hα_pt_S' (mem_biUnion hA_S' hvA_bar)
    rintro B₁ (hB₁_S' | hB₁_i) B₂ (hB₂_S' | hB₂_j) hne
    · rw [hα_disc_S' hB₁_S', hα_disc_S' hB₂_S']
      intro x hx
      obtain ⟨v, hv, rfl⟩ := hArr₀.inter_discs B₁ hB₁_S'.1 B₂ hB₂_S'.1 hne hx
      exact ⟨v, hv, hα_pt_S' (mem_biUnion hB₁_S' hv.1)⟩
    · obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
      rw [Set.inter_comm, Set.inter_comm B₁.Ω.bar]
      exact hinter_seg_S' j hB₂_j hB₁_S'
    · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
      exact hinter_seg_S' i hB₁_i hB₂_S'
    · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
      obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
      rw [hα_disc_seg' i hB₁_i, hα_disc_seg' j hB₂_j]
      by_cases hij : i = j
      · subst hij
        intro x hx
        obtain ⟨v, hv, rfl⟩ := hinter_discs_i i B₁ hB₁_i.1 B₂ hB₂_j.1 hne hx
        exact ⟨v, hv, hClaim5 i (mem_biUnion hB₁_i.1 hv.1)⟩
      · rintro x ⟨hx1, hx2⟩
        exact False.elim (Set.disjoint_left.mp (hDisj_Δ hij)
          ((hdisc_i_closed i B₁ hB₁_i.1).2.1 hx1)
          ((hdisc_i_closed j B₂ hB₂_j.1).2.1 hx2))
  · -- Intersection with `bd S = ∅`.
    intro B _
    rw [hFlat.isSpan.bd_empty, inter_empty]
    exact empty_subset _
  · -- Claim (8): `InjOn α_pt (segregationVertices S_final)`.
    have hseg_final_cases : ∀ {v : α}, v ∈ segregationVertices S_final →
        v ∈ segregationVertices S' ∨ ∃ i : Fin k, v ∈ segregationVertices (S_seg i) := by
      intro v hv
      rcases mem_iUnion₂.mp hv with ⟨B, hB_S' | hB_i, hvB⟩
      · exact Or.inl (mem_biUnion hB_S' hvB)
      · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
        exact Or.inr ⟨i, mem_biUnion hBi.1 hvB⟩
    have hinj_seg_S' : ∀ (i : Fin k) {u v : α},
        u ∈ segregationVertices (S_seg i) → v ∈ segregationVertices S' →
        α_pt u = α_pt v → u = v := by
      intro i u v hu_i hv_S' huv
      by_cases hv_i : v ∈ segregationVertices (S_seg i)
      · rw [hClaim5 i hu_i, hClaim5 i hv_i] at huv
        exact hinj_i i hu_i hv_i huv
      · exfalso
        have hv_not_bar_star : v ∉ (D i).localSociety.Ω.bar :=
          fun hbar => hv_i (hBar_i i hbar)
        obtain ⟨A, hA_S', hvA_bar⟩ := mem_iUnion₂.mp hv_S'
        have hv_seg₀ : v ∈ segregationVertices S₀ := mem_biUnion hA_S'.1 hvA_bar
        have hv_not_bdΔ : α₀_pt v ∉ subBd (D i).Δ := by
          intro hbd
          apply hv_not_bar_star
          rw [(D i).soc_star_Ω.1]
          exact ⟨hv_seg₀, hbd⟩
        have hv_bdA : α₀_pt v ∈ subBd (α₀_disc A) := (hArr₀.isClosedDisc A hA_S'.1).2 v hvA_bar
        have hv_discA : α₀_pt v ∈ α₀_disc A :=
          (hArr₀.isClosedDisc A hA_S'.1).1.isClosed.closure_subset_iff.mpr Subset.rfl hv_bdA.1
        have hv_not_Δ : α₀_pt v ∉ (D i).Δ := fun hΔ =>
          hv_not_bdΔ ((inter_disc_subset_subBd_of_not_subset hS hArr₀ (D i).isClosedDisc_Δ
            (D i).isNormal_bd hA_S'.1 (hA_S'.2 i)).1 ⟨hv_discA, hΔ⟩)
        rw [hClaim5 i hu_i, hα_pt_S' hv_S'] at huv
        exact hv_not_Δ (huv ▸ hpt_i_mem_Δ i u hu_i)
    intro u hu v hv huv
    rcases hseg_final_cases hu with hu_S' | ⟨i, hu_i⟩ <;>
      rcases hseg_final_cases hv with hv_S' | ⟨j, hv_j⟩
    · rw [hα_pt_S' hu_S', hα_pt_S' hv_S'] at huv
      have hsub : segregationVertices S' ⊆ segregationVertices S₀ :=
        biUnion_mono (fun _ h => h.1) (fun _ _ => Subset.rfl)
      exact hArr₀.injOn_pts (hsub hu_S') (hsub hv_S') huv
    · exact (hinj_seg_S' j hv_j hu_S' huv.symm).symm
    · exact hinj_seg_S' i hu_i hv_S' huv
    · rw [hClaim5 i hu_i, hClaim5 j hv_j] at huv
      by_cases hij : i = j
      · subst hij
        exact hinj_i i hu_i hv_j huv
      · exfalso
        exact Set.disjoint_left.mp (hDisj_Δ hij)
          (hpt_i_mem_Δ i u hu_i) (huv ▸ hpt_i_mem_Δ j v hv_j)
  · -- Claim (9): `IsNaturalOrderFrom α_pt B.Ω (subBd (α_disc B))` for all `B ∈ S_final`.
    have hnat_congr : ∀ {ν₁ ν₂ : α → S} {Ω : CyclicPerm α} {F : Set S},
        (∀ v ∈ Ω.bar, ν₁ v = ν₂ v) → IsNaturalOrderFrom ν₁ Ω F → IsNaturalOrderFrom ν₂ Ω F := by
      intro ν₁ ν₂ Ω F heq ⟨hOArc, φ, hmem, hcw3⟩
      refine ⟨hOArc, φ, fun v hv => heq v hv ▸ hmem v hv, fun v₁ v₂ v₃ hcw => ?_⟩
      obtain ⟨t₁, t₂, t₃, h12, h23, h31, h1, h2, h3⟩ := hcw3 v₁ v₂ v₃ hcw
      have hv1 : v₁ ∈ Ω.bar := hcw.2.1 v₁ (by simp)
      have hv2 : v₂ ∈ Ω.bar := hcw.2.1 v₂ (by simp)
      have hv3 : v₃ ∈ Ω.bar := hcw.2.1 v₃ (by simp)
      exact ⟨t₁, t₂, t₃, h12, h23, h31, h1.trans (heq v₁ hv1),
        h2.trans (heq v₂ hv2), h3.trans (heq v₃ hv3)⟩
    rintro B (hB_S' | hB_i)
    · rw [hα_disc_S' hB_S']
      exact hnat_congr (fun v hv => (hα_pt_S' (mem_biUnion hB_S' hv)).symm)
        (hArr₀.natural_order B hB_S'.1)
    · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
      rw [hα_disc_seg' i hBi]
      exact hnat_congr (fun v hv => (hClaim5 i (mem_biUnion hBi.1 hv)).symm)
        (hnat_i i B hBi.1)

/-- Distinct large societies in the assembled segregation come from different local pieces. -/
private theorem large_boundaries_disjoint_of_eye_segregation
    {G₀ : Graph α β} {S₀ S' : Set (Society α β)} (hThree : IsThreeSegregation G₀ S₀)
    (hRetained : S' ⊆ S₀) {k p : ℕ} {pieces : Fin k → Graph α β}
    {S_seg S_seg' : Fin k → Set (Society α β)} (hLocal : ∀ i, S_seg' i ⊆ S_seg i)
    (hType_i : ∀ i, IsSegregationOfType (pieces i) p 1 (S_seg i))
    (hDisj_star : Pairwise (fun i j : Fin k => Disjoint V(pieces i) V(pieces j))) :
    ∀ A ∈ S' ∪ ⋃ i, S_seg' i, ∀ B ∈ S' ∪ ⋃ i, S_seg' i,
      A ≠ B → 3 < A.Ω.bar.ncard → 3 < B.Ω.bar.ncard → Disjoint A.Ω.bar B.Ω.bar := by
  intro A hA B hB hne hlargeA hlargeB
  have hLargeLocal : ∀ C ∈ S' ∪ ⋃ i, S_seg' i, 3 < C.Ω.bar.ncard → ∃ i, C ∈ S_seg' i := by
    intro C hC hlarge
    rcases hC with hC | hC
    · exact (not_lt_of_ge (hThree.2 C (hRetained hC)) hlarge).elim
    · exact mem_iUnion.mp hC
  obtain ⟨i, hAi⟩ := hLargeLocal A hA hlargeA
  obtain ⟨j, hBj⟩ := hLargeLocal B hB hlargeB
  have hij : i ≠ j := by
    intro hij
    subst j
    have hfin : {C ∈ S_seg i | 3 < C.Ω.bar.ncard}.Finite :=
      (hType_i i).1.finite.subset fun _ h => h.1
    exact hne ((Set.ncard_le_one hfin).mp (hType_i i).vortex_count_le A
      ⟨hLocal i hAi, hlargeA⟩ B ⟨hLocal i hBj, hlargeB⟩)
  exact (hDisj_star hij).mono
    (fun _ hv => ((hType_i i).1.le A (hLocal i hAi)).vertexSet_mono (A.bar_subset hv))
    (fun _ hv => ((hType_i j).1.le B (hLocal j hBj)).vertexSet_mono (B.bar_subset hv))

/-- The construction of XV (7.7), including disjoint boundaries of large societies. -/
theorem assemble_eye_arrangement :
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 ≤ π → π ≠ 3 → beta = 2 * π + 8 →
    θ' + 13 * μ + 14 ≤ beta → 100 * beta ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ →
    IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ →
    IsSurfaceArrangement S₀ α₀_disc α₀_pt →
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt →
    Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ) →
    (∀ i : Fin k, ∀ P_set : Set (Graph α β),
      (D i).localSociety.IsCrookedTransaction P_set → P_set.ncard ≠ π) →
    ∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
      IsCentralSegregation G T_star 𝒮 ∧ IsSegregationOfType G (3 * π + 9) k 𝒮 ∧
      IsSurfaceArrangement 𝒮 disc pt ∧
      (∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B → 3 < A.Ω.bar.ncard → 3 < B.Ω.bar.ncard →
        Disjoint A.Ω.bar B.Ω.bar) := by
  classical
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
    hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
    hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hθ_bound : 2 * (θ' + 12 * μ + 14) + μ ≤ θ := by omega
  have hDisj_star : Pairwise (fun i j : Fin k => Disjoint V((D i).localSociety.G) V((D
    j).localSociety.G))
    :=
    theorem_7_6_proof G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
      hFlat hMetric hμ1 hθ_bound hr_inj hr_eye hr_dist hη₀_v hThree hArr₀ hCompat₀ hDisj_Δ
  let G₀ := section7G0 G H η d θ' μ r
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hJi_le : ∀ i : Fin k, eyeBridgeUnion G H η d θ' μ (r i) ≤ G :=
    fun _ => subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPi_le : ∀ i : Fin k, arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ ≤ G :=
    fun _ => (restrict_le.trans (G₀.induce_le inter_subset_right)).trans hG₀_le
  have hstar_le : ∀ i : Fin k, (D i).localSociety.G ≤ G := by
    intro i
    rw [(D i).soc_star_G]
    exact subgraphUnion_le (hJi_le i) (hPi_le i)
  -- For each `i : Fin k`, apply (6.1) (`theorem_6_1_proof`) and transport to `(D i).Δ`.
  have hex_i : ∀ i : Fin k,
      ∃ (S_seg_i : Set (Society α β)) (α_disc_i : Society α β → Set S) (α_pt_i : α → S),
        IsSegregationOfType (D i).localSociety.G (3 * π + 9) 1 S_seg_i ∧
        (D i).localSociety.Ω.bar ⊆ segregationVertices S_seg_i ∧
        (∀ v ∈ (D i).localSociety.Ω.bar, α_pt_i v = α₀_pt v) ∧
        (∀ v ∈ segregationVertices S_seg_i, α_pt_i v ∈ (D i).Δ) ∧
        (∀ v ∈ segregationVertices S_seg_i, v ∉ (D i).localSociety.Ω.bar →
          α_pt_i v ∈ (D i).Δ \ subBd (D i).Δ) ∧
        InjOn α_pt_i (segregationVertices S_seg_i) ∧
        (∀ B ∈ S_seg_i, IsClosedDisc (α_disc_i B) ∧ α_disc_i B ⊆ (D i).Δ ∧
          ∀ x ∈ B.Ω.bar, α_pt_i x ∈ subBd (α_disc_i B)) ∧
        (∀ B ∈ S_seg_i, IsNaturalOrderFrom α_pt_i B.Ω (subBd (α_disc_i B))) ∧
        (∀ B ∈ S_seg_i, α_disc_i B ∩ subBd (D i).Δ ⊆ α_pt_i '' (B.Ω.bar ∩
          (D i).localSociety.Ω.bar)) ∧
        (∀ B₁ ∈ S_seg_i, ∀ B₂ ∈ S_seg_i, B₁ ≠ B₂ →
          α_disc_i B₁ ∩ α_disc_i B₂ ⊆ α_pt_i '' (B₁.Ω.bar ∩ B₂.Ω.bar)) := by
    intro i
    obtain ⟨S_seg_i, m, A₀_i, A_i, Δ_E, α₀_E, α_disc_E, α_pt_E,
        hS_eq, hType_i, hBar_i, hDiscArr_i⟩ :=
      theorem_6_1_proof (D i).localSociety π hπ2 hπ3 (hno_crooked i)
    subst hS_eq
    have hinj_bar_i : InjOn α₀_pt (D i).localSociety.Ω.bar :=
      hArr₀.injOn_pts.mono (fun v hv => ((D i).soc_star_Ω.1 ▸ hv).1)
    obtain ⟨α_disc_S, α_pt_S, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      exists_surface_disc_arrangement_of_isDiscArrangement hS (D i).localSociety A₀_i A_i
        Δ_E α₀_E α_disc_E α_pt_E hBar_i hDiscArr_i (D i).Δ (D i).isClosedDisc_Δ
        α₀_pt hinj_bar_i (D i).soc_star_Ω.2
    exact ⟨insert A₀_i (range A_i), α_disc_S, α_pt_S, hType_i, hBar_i,
      h1, h2, h3, h4, h5, h6, h7, h8⟩
  choose S_seg α_disc_i α_pt_i hType_i hBar_i hpt_i_eq_0 hpt_i_mem_Δ hpt_i_mem_int
    hinj_i hdisc_i_closed hnat_i hinter_bd_i hinter_discs_i using hex_i
  have hseg_i_sub_V : ∀ i : Fin k, segregationVertices (S_seg i) ⊆ V((D i).localSociety.G) := by
    intro i v hv
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    exact ((hType_i i).1.le B hB).vertexSet_mono (B.bar_subset hvB)
  -- Define `S'`, `S_seg' i`, and `S_final`.
  let S' : Set (Society α β) := {A ∈ S₀ | ∀ i : Fin k, ¬ α₀_disc A ⊆ (D i).Δ}
  let S_seg' : Fin k → Set (Society α β) := fun i =>
    {B ∈ S_seg i | V(B.G).Nonempty ∧ B ∉ S'}
  let S_final : Set (Society α β) := S' ∪ ⋃ i : Fin k, S_seg' i
  have hDisj_S'_seg' : ∀ i : Fin k, Disjoint S' (S_seg' i) :=
    fun i => Set.disjoint_left.mpr fun _ hS' hseg' => hseg'.2.2 hS'
  have hDisj_seg' : Pairwise (fun i j : Fin k => Disjoint (S_seg' i) (S_seg' j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun B hBi hBj => ?_
    obtain ⟨v, hv⟩ := hBi.2.1
    exact Set.disjoint_left.mp (hDisj_star hij)
      (((hType_i i).1.le B hBi.1).vertexSet_mono hv)
      (((hType_i j).1.le B hBj.1).vertexSet_mono hv)
  -- Claim (2): `S_final` is a graph segregation of `G`.
  have hFin₀ : S'.Finite := hThree.1.finite.subset fun _ h => h.1
  have hFin_eye (i : Fin k) : (S_seg' i).Finite := (hType_i i).1.finite.subset fun _ h => h.1
  have hFin_final : S_final.Finite := hFin₀.union (finite_iUnion hFin_eye)
  have hLe_final : ∀ B ∈ S_final, B.G ≤ G := by
    rintro B (hB_S' | hB_i)
    · exact (hThree.1.le B hB_S'.1).trans hG₀_le
    · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
      exact ((hType_i i).1.le B hBi.1).trans (hstar_le i)
  have hCover_star_V : ∀ (i : Fin k) {v : α}, v ∈ V((D i).localSociety.G) →
      ∃ B ∈ S_final, v ∈ V(B.G) := by
    intro i v hv
    have hv_u : v ∈ V(subgraphSUnion (D i).localSociety.G ((fun B : Society α β => B.G) '' S_seg i))
      := by
      rw [(hType_i i).1.union_eq]; exact hv
    rw [vertexSet_subgraphSUnion] at hv_u
    obtain ⟨_, ⟨B, hB, rfl⟩, hvB⟩ := mem_iUnion₂.mp hv_u
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', hvB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨v, hvB⟩, hB_S'⟩), hvB⟩
  have hCover_star_E : ∀ (i : Fin k) {e : β}, e ∈ E((D i).localSociety.G) →
      ∃ B ∈ S_final, e ∈ E(B.G) := by
    intro i e he
    have he_u : e ∈ E(subgraphSUnion (D i).localSociety.G ((fun B : Society α β => B.G) '' S_seg i))
      := by
      rw [(hType_i i).1.union_eq]; exact he
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact (hType_i i).1.le B hB)] at he_u
    obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp he_u
    obtain ⟨x, _, hxy⟩ := B.G.exists_isLink_of_mem_edgeSet heB
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', heB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨x, hxy.left_mem⟩, hB_S'⟩), heB⟩
  have hSegregation : IsGraphSegregation G S_final := by
    exact assemble_eye_segregation (S := S) (α := α) (β := β) G H η θ_star θ θ' π beta μ k T_star
      T d r η₀ S₀ α₀_disc α₀_pt D hη₀_v hThree hArr₀ hCompat₀ hS hDisj_star hPair_le hJi_le
      hPi_le hstar_le S_seg hType_i hBar_i hFin_final hLe_final hCover_star_V
      hCover_star_E
  -- Claim (3): `S_final` is of type `(3 * π + 9, k)`.
  have hClaim3 : IsSegregationOfType G (3 * π + 9) k S_final := by
    refine ⟨hSegregation, ?_, ?_⟩
    · let F : Fin k → Set (Society α β) := fun i => {B ∈ S_seg i | 3 < B.Ω.bar.ncard}
      have hsub : {B ∈ S_final | 3 < B.Ω.bar.ncard} ⊆ ⋃ i : Fin k, F i := by
        rintro B ⟨hB_S' | hB_i, hgt⟩
        · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
        · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
          exact mem_iUnion.mpr ⟨i, hBi.1, hgt⟩
      have hfin_u : (⋃ i : Fin k, F i).Finite :=
        finite_iUnion fun i => (hType_i i).1.finite.subset fun _ h => h.1
      exact (ncard_le_ncard hsub hfin_u).trans
        (ncard_iUnion_le_of_ncard_le_one k F (fun i => (hType_i i).vortex_count_le))
    · rintro B (hB_S' | hB_i) hgt
      · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
      · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
        exact (hType_i i).is_p_vortex hBi.1 hgt
  -- Claim (4): `S_final` is `T_star`-central.
  have hCentral : IsCentralSegregation G T_star S_final := by
    exact assembled_eye_segregation_is_central (S := S) (α := α) (β := β) G H η θ_star θ θ' lam π
      beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D hFlat hMetric hμ1 hπ2 hbeta_eq hθ_ge hr_eye
      hη₀_v hη₀_e hThree hLocal hCompat₀ hS hθ_bound hJi_le hPi_le S_seg hType_i
       hClaim3
  -- Define `α_disc` and `α_pt` and prove Claims (5)–(9).
  let α_disc : Society α β → Set S := fun B =>
    if h : ∃ i : Fin k, B ∈ S_seg' i then α_disc_i (Classical.choose h) B else α₀_disc B
  let α_pt : α → S := fun v =>
    if h : ∃ i : Fin k, v ∈ segregationVertices (S_seg i) then α_pt_i (Classical.choose h) v
    else α₀_pt v
  have hα_disc_S' : ∀ {B : Society α β}, B ∈ S' → α_disc B = α₀_disc B := by
    intro B hB
    have hnot : ¬ ∃ i : Fin k, B ∈ S_seg' i := by
      rintro ⟨i, hBi⟩
      exact Set.disjoint_left.mp (hDisj_S'_seg' i) hB hBi
    simp [α_disc, hnot]
  have hα_disc_seg' : ∀ (i : Fin k) {B : Society α β}, B ∈ S_seg' i → α_disc B = α_disc_i i B := by
    intro i B hBi
    have hex : ∃ j : Fin k, B ∈ S_seg' j := ⟨i, hBi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_seg' hne) (Classical.choose_spec hex) hBi
    simp [α_disc, hex, hij]
  -- Claim (5): For `i : Fin k`, if `v ∈ segregationVertices (S_seg i)` then `α_pt v = α_pt_i i v`.
  have hClaim5 : ∀ (i : Fin k) {v : α}, v ∈ segregationVertices (S_seg i) →
      α_pt v = α_pt_i i v := by
    intro i v hvi
    have hex : ∃ j : Fin k, v ∈ segregationVertices (S_seg j) := ⟨i, hvi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_star hne)
        (hseg_i_sub_V _ (Classical.choose_spec hex)) (hseg_i_sub_V i hvi)
    simp [α_pt, hex, hij]
  have hα_pt_S' : ∀ {v : α}, v ∈ segregationVertices S' → α_pt v = α₀_pt v := by
    intro v hv_S'
    by_cases hex : ∃ i : Fin k, v ∈ segregationVertices (S_seg i)
    · obtain ⟨i, hvi⟩ := hex
      rw [hClaim5 i hvi]
      obtain ⟨A, hA_S', hvA⟩ := mem_iUnion₂.mp hv_S'
      have hv_bar_star : v ∈ (D i).localSociety.Ω.bar :=
        (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hA_S'.1 (hA_S'.2 i)).2
          ⟨hseg_i_sub_V i hvi, A.bar_subset hvA⟩
      exact hpt_i_eq_0 i v hv_bar_star
    · simp [α_pt, hex]
  -- Claims (6)–(9): `(S_final, α_disc, α_pt)` is a surface arrangement in `S`.
  have hArr_final : IsSurfaceArrangement S_final α_disc α_pt := by
    exact arrange_replacement_societies (S := S) (α := α) (β := β) G H η θ_star θ θ' lam π beta μ
      k T_star T d r S₀ α₀_disc α₀_pt D hFlat hArr₀ hDisj_Δ hS S_seg α_disc_i α_pt_i hBar_i
      hpt_i_eq_0 hpt_i_mem_Δ hinj_i hdisc_i_closed hnat_i hinter_bd_i hinter_discs_i
       α_disc α_pt hα_disc_S' hα_disc_seg' hClaim5 hα_pt_S'
  refine ⟨S_final, α_disc, α_pt, hCentral, hClaim3, hArr_final, ?_⟩
  exact large_boundaries_disjoint_of_eye_segregation (S' := S') (S_seg' := S_seg')
    hThree (fun _ h ↦ h.1) (fun _ _ h ↦ h.1) hType_i hDisj_star

/-- **Graph Minors XV, (7.7)** (pages 139–142):
If there is no crooked transaction of cardinality `π` in `(G_i*, Ω_i*)` for `1 ≤ i ≤ k`, then
`(S3)` holds.
Proved from `(2.1)` (`theorem_2_1_proof`), `(6.1)` (`theorem_6_1_proof`), `(7.6)`
(`theorem_7_6_proof`), and Graph
Minors XIV, `(7.3)` (`gm14_theorem_7_3`). -/
theorem theorem_7_7_proof : GM15Theorem77Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
    hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
    hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  obtain ⟨𝒮, disc, pt, hCentral, hType, hArr, _⟩ :=
    assemble_eye_arrangement G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt
      D hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
      hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  exact ⟨𝒮, disc, pt, hCentral, hType, hArr⟩

/-- Statement of Graph Minors XV, (7.8) (page 142):
"There is a transaction $\mathscr{P}$ in $(G_0 \cup J_1, \Omega_1)$ such that $V(\mathscr{P})$ is
free with respect to the $(12\beta + 14)$-compression of $\mathscr{T}$ in $H \cap (\Sigma -
\Lambda_1)$, each $P \in \mathscr{P}$ meets $H \cap (\Sigma - \Lambda_1)$ precisely in the ends of
$P$, and one of the following holds:
(i) $|\mathscr{P}| = \phi$ and $\mathscr{P}$ is a crosscap transaction
(ii) $|\mathscr{P}| = \tau_1$ and $\mathscr{P}$ is a leap transaction
(iii) $|\mathscr{P}| = \tau_2$ and $\mathscr{P}$ is a doublecross transaction." -/
def GM15Theorem78Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' π beta μ φ τ₁ τ₂ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P_star : Set (Graph α β)),
    2 ≤ φ → 3 ≤ τ₁ → 4 ≤ τ₂ →
    (φ - 1) * (2 * τ₁ + τ₂ - 7) ≤ π →
    D_i.localSociety.IsCrookedTransaction P_star → P_star.ncard = π →
    ∃ (P : Set (Graph α β)) (X : Set S),
      D_i.clearedSociety.IsTransaction P ∧
      (∀ P₀ ∈ P, ∀ a b : α,
        D_i.clearedSociety.IsOmegaPathWithEnds P₀ a b →
        IsHPathWithEnds G D_i.clearedEmbedding.imageGraph P₀ a b) ∧
      X ⊆ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ ∧
      D_i.clearedSociety.transactionEnds P = D_i.clearedEmbedding.vMap '' X ∧
      IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X ∧
      ((P.ncard = φ ∧ D_i.clearedSociety.IsCrosscapTransaction P) ∨
       (P.ncard = τ₁ ∧ D_i.clearedSociety.IsLeapTransaction P) ∨
       (P.ncard = τ₂ ∧ D_i.clearedSociety.IsDoublecrossTransaction P))

/-- **Graph Minors XV, (7.8)** (page 142):
If `(G_i*, Ω_i*)` has a crooked transaction of cardinality `π`, then `(G₀ ∪ J_i, Ω_i)` has a
transaction `P` whose ends are free with respect to `T₁` in `H ∩ (Σ - Λ_i)`, each member of `P`
meets `H ∩ (Σ - Λ_i)` precisely in its ends, and `P` is either a crosscap transaction of size `φ`, a
leap transaction of size `τ₁`, or a doublecross transaction of size `τ₂`.
Proved from `(7.5)` (`Section75EyeData.dichotomy`), `(6.2)` (`theorem_6_2_proof`), and Graph Minors
X,
`(12.2)` (`GM10.IsFreeSet.subset`). -/
theorem theorem_7_8_proof :
    GM15Theorem78Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' π beta μ φ τ₁ τ₂ k T_star T d r S₀ α₀_disc α₀_pt
    i D_i P_star hφ2 hτ₁3 hτ₂4 hπ_ge hCrook_star hCard_star
  have hDich := D_i.dichotomy.resolve_right (fun hno => hno P_star hCrook_star hCard_star)
  rcases hDich with ⟨P', X', hCrook', hCard', hPaths', hX'_sub, hEnds', hFree'⟩
  have h62 := theorem_6_2_proof D_i.clearedSociety φ τ₁ τ₂ P' hφ2 hτ₁3 hτ₂4 hCrook'
    (hπ_ge.trans hCard')
  rcases h62 with ⟨P, hPP', hCases⟩
  let X : Set S := {x ∈ X' | D_i.clearedEmbedding.vMap x ∈ D_i.clearedSociety.transactionEnds P}
  have hXX' : X ⊆ X' := sep_subset _ _
  have hT₁ : IsTangle (clearedSubdrawing H D_i.Λ).toHypergraph
      (θ - 4 * (3 * beta + 3) - 2) D_i.T₁ :=
    D_i.isCleared.hasMetric.1.2.1
  have hFreeX : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁
      (θ - 4 * (3 * beta + 3) - 2) X :=
    hFree'.subset hT₁ hXX'
  have hTransP : D_i.clearedSociety.IsTransaction P := by
    rcases hCrook'.1 with ⟨A, B, hDisj, hFence, hAB⟩
    refine ⟨A, B, ⟨?_, ?_⟩, hFence, fun P₀ hP₀ => hAB P₀ (hPP' hP₀)⟩
    · intro P₀ hP₀
      exact hDisj.1 P₀ (hPP' hP₀)
    · intro P₁ hP₁ P₂ hP₂ hne
      exact hDisj.2 (hPP' hP₁) (hPP' hP₂) hne
  have hEndsP : D_i.clearedSociety.transactionEnds P = D_i.clearedEmbedding.vMap '' X := by
    ext v
    constructor
    · intro hv
      have hv' : v ∈ D_i.clearedSociety.transactionEnds P' := by
        rcases hv with ⟨P₀, hP₀, b, hPath⟩
        exact ⟨P₀, hPP' hP₀, b, hPath⟩
      rw [hEnds'] at hv'
      rcases hv' with ⟨x, hxX', rfl⟩
      exact ⟨x, ⟨hxX', hv⟩, rfl⟩
    · rintro ⟨x, ⟨_, hv⟩, rfl⟩
      exact hv
  exact ⟨P, X, hTransP, fun P₀ hP₀ => hPaths' P₀ (hPP' hP₀),
    hXX'.trans hX'_sub, hEndsP, hFreeX, hCases⟩

/-- If `Ω` is a natural order from `F` via `ν : α → S` (`IsNaturalOrderFrom ν Ω F`) and `L` is an
`Ω`-clockwise sequence of length `≥ 3`, then `L.map ν` is listed in order on `F`
(`GM12.IsListedInOrderOn F (L.map ν)`). -/
theorem isListedInOrderOn_of_isClockwiseSeq
    {S : Type w} [TopologicalSpace S] {α : Type u}
    {ν : α → S} {Ω : CyclicPerm α} {F : Set S} {L : List α}
    (hNat : IsNaturalOrderFrom ν Ω F)
    (hcw : Ω.IsClockwiseSeq L) (hlen : 3 ≤ L.length) :
    GM12.IsListedInOrderOn F (L.map ν) := by
  classical
  obtain ⟨_, φ, _, hAgree3⟩ := hNat
  have hpi : 0 < 2 * Real.pi := by positivity
  let pt : ℝ → S := fun t => (φ (Circle.exp t)).1
  have hpt_eq_iff : ∀ t₁ t₂ : ℝ, pt t₁ = pt t₂ ↔ ∃ m : ℤ, t₁ = t₂ + m * (2 * Real.pi) := by
    intro t₁ t₂
    constructor
    · intro h
      have h1 : φ (Circle.exp t₁) = φ (Circle.exp t₂) := Subtype.ext h
      exact Circle.exp_eq_exp.mp (φ.injective h1)
    · rintro ⟨m, rfl⟩
      have h2 : Circle.exp (t₂ + m * (2 * Real.pi)) = Circle.exp t₂ :=
        Circle.exp_eq_exp.mpr ⟨m, rfl⟩
      simp [pt, h2]
  have hpt_inj : ∀ t₀ : ℝ, InjOn pt (Ico t₀ (t₀ + 2 * Real.pi)) := by
    intro t₀ t₁ ht₁ t₂ ht₂ h
    obtain ⟨m, rfl⟩ := (hpt_eq_iff t₁ t₂).mp h
    have hm0 : m = 0 := by
      by_contra hm
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        have : (m : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_le hpi.le
        linarith [ht₁.1, ht₂.2]
      · have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast hgt
        have : 1 * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_ge hpi.le
        linarith [ht₁.2, ht₂.1]
    simp [hm0]
  have h012 : Ω.IsClockwise3 (L[0]'(by omega)) (L[1]'(by omega)) (L[2]'(by omega)) :=
    (Ω.mem_interval_of_lt hcw (by omega) (by omega) hlen).2
  obtain ⟨t₀, t₁, t₂, ht01, ht12, ht20, hpt0, hpt1, hpt2⟩ :=
    hAgree3 (L[0]'(by omega)) (L[1]'(by omega)) (L[2]'(by omega)) h012
  have hshift3 : ∀ v₁ v₂ : α, Ω.IsClockwise3 (L[0]'(by omega)) v₁ v₂ →
      ∃ u₁ u₂ : ℝ, t₀ < u₁ ∧ u₁ < u₂ ∧ u₂ < t₀ + 2 * Real.pi ∧
        pt u₁ = ν v₁ ∧ pt u₂ = ν v₂ := by
    intro v₁ v₂ hcw3
    obtain ⟨s₀, s₁, s₂, hs01, hs12, hs20, hs₀, hs₁, hs₂⟩ := hAgree3 (L[0]'(by omega)) v₁ v₂ hcw3
    obtain ⟨m, hm⟩ := (hpt_eq_iff t₀ s₀).mp (hpt0.trans hs₀.symm)
    refine ⟨s₁ + m * (2 * Real.pi), s₂ + m * (2 * Real.pi), by linarith, by linarith, by linarith,
      ?_, ?_⟩
    · exact ((hpt_eq_iff _ s₁).mpr ⟨m, rfl⟩).trans hs₁
    · exact ((hpt_eq_iff _ s₂).mpr ⟨m, rfl⟩).trans hs₂
  have hex : ∀ (i : ℕ) (hi : i < L.length),
      ∃ u ∈ Ico t₀ (t₀ + 2 * Real.pi), pt u = ν (L[i]'hi) ∧ (0 < i → t₀ < u) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi_pos
    · exact ⟨t₀, ⟨le_rfl, by linarith⟩, hpt0, fun h => (Nat.lt_irrefl 0 h).elim⟩
    · by_cases hi1 : i = 1
      · subst hi1
        exact ⟨t₁, ⟨le_of_lt ht01, by linarith⟩, hpt1, fun _ => ht01⟩
      · have hcw_i : Ω.IsClockwise3 (L[0]'(by omega)) (L[1]'(by omega)) (L[i]'hi) :=
          (Ω.mem_interval_of_lt hcw (by omega) (by omega) hi).2
        obtain ⟨u₁, u₂, hu01, hu12, hu20, _, hu₂⟩ := hshift3 (L[1]'(by omega)) (L[i]'hi) hcw_i
        exact ⟨u₂, ⟨le_of_lt (hu01.trans hu12), hu20⟩, hu₂, fun _ => hu01.trans hu12⟩
  let t : ℕ → ℝ := fun i =>
    if hi : i < L.length then Classical.choose (hex i hi) else t₀ + 2 * Real.pi + i
  have ht_spec : ∀ (i : ℕ) (hi : i < L.length),
      t i ∈ Ico t₀ (t₀ + 2 * Real.pi) ∧ pt (t i) = ν (L[i]'hi) ∧ (0 < i → t₀ < t i) := by
    intro i hi
    have h_eq : t i = Classical.choose (hex i hi) := by
      dsimp only [t]; split_ifs; rfl
    rw [h_eq]
    exact Classical.choose_spec (hex i hi)
  have ht0_eq : t 0 = t₀ := by
    obtain ⟨ht0_mem, ht0_pt, _⟩ := ht_spec 0 (by omega)
    exact hpt_inj t₀ ht0_mem ⟨le_rfl, by linarith⟩ (ht0_pt.trans hpt0.symm)
  refine ⟨φ, t, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hj : j < L.length
    · have hi : i < L.length := hij.trans hj
      rcases Nat.eq_zero_or_pos i with rfl | hi_pos
      · rw [ht0_eq]
        exact (ht_spec j hj).2.2 hij
      · have hcw_ij : Ω.IsClockwise3 (L[0]'(by omega)) (L[i]'hi) (L[j]'hj) :=
          (Ω.mem_interval_of_lt hcw hi_pos hij hj).2
        obtain ⟨u₁, u₂, hu01, hu12, hu20, hu₁, hu₂⟩ := hshift3 (L[i]'hi) (L[j]'hj) hcw_ij
        have hti : t i = u₁ :=
          hpt_inj t₀ (ht_spec i hi).1 ⟨le_of_lt hu01, hu12.trans hu20⟩
            ((ht_spec i hi).2.1.trans hu₁.symm)
        have htj : t j = u₂ :=
          hpt_inj t₀ (ht_spec j hj).1 ⟨le_of_lt (hu01.trans hu12), hu20⟩
            ((ht_spec j hj).2.1.trans hu₂.symm)
        linarith
    · by_cases hi : i < L.length
      · have hti := (ht_spec i hi).1.2
        have htj : t j = t₀ + 2 * Real.pi + j := by dsimp only [t]; split_ifs; rfl
        have hj_nonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      · have hti : t i = t₀ + 2 * Real.pi + i := by dsimp only [t]; split_ifs; rfl
        have htj : t j = t₀ + 2 * Real.pi + j := by dsimp only [t]; split_ifs; rfl
        have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
        linarith
  · intro i hi
    rw [List.length_map] at hi
    rw [ht0_eq]
    exact (ht_spec i hi).1.2
  · intro i hi
    have hi' : i < L.length := by simpa using hi
    simpa [pt] using (ht_spec i hi').2.1

/-- Statement of Graph Minors XV, (7.9) (page 143):
"If $\mathscr{P}$ is a crosscap transaction of cardinality $\phi$ then (S2) is true." -/
def GM15Theorem79Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' π beta μ φ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β)) (X : Set S),
    3 ≤ φ → φ ≤ θ - 4 * (3 * beta + 3) - 2 →
    D_i.clearedSociety.IsTransaction P →
    (∀ P₀ ∈ P, ∀ a b : α,
      D_i.clearedSociety.IsOmegaPathWithEnds P₀ a b →
      IsHPathWithEnds G D_i.clearedEmbedding.imageGraph P₀ a b) →
    X ⊆ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ →
    D_i.clearedSociety.transactionEnds P = D_i.clearedEmbedding.vMap '' X →
    IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X →
    P.ncard = φ → D_i.clearedSociety.IsCrosscapTransaction P →
    Section7S2 S G θ_star T_star φ

/-- Graph Minors XV, (7.9), page 143: use the established (3.3) in the transaction argument. -/
theorem theorem_7_9_proof : GM15Theorem79Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' π beta μ φ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X
    hφ3 hφ_le hTransP hPathsP hX_sub hEndsP hFreeX hCardφ hCross
  rcases hCross with ⟨A_f, B_f, _, p, _, P_idx, a_idx, b_idx, hP_inj, hP_range, hEnds_idx, hcw⟩
  have hp_eq : p = φ := by
    rw [← hCardφ, ← hP_range, Set.ncard_range_of_injective hP_inj, Nat.card_fin]
  subst p
  let a' : Fin φ → α := a_idx ∘ Fin.rev
  let b' : Fin φ → α := b_idx ∘ Fin.rev
  let P' : Fin φ → Graph α β := P_idx ∘ Fin.rev
  have hrev_ofFn : ∀ (f : Fin φ → α), (List.ofFn f).reverse = List.ofFn (f ∘ Fin.rev) := by
    intro f
    apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp only [List.length_ofFn] at hj2
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn, Function.comp_apply]
    congr 1
    ext
    simp [Fin.rev]
    omega
  have hcw' : D_i.clearedSociety.Ω.IsClockwiseSeq (List.ofFn a' ++ List.ofFn b') := by
    rwa [← hrev_ofFn a_idx, ← hrev_ofFn b_idx]
  obtain ⟨inv_v, hinv_v, hNat⟩ := D_i.soc_Λ_natural
  have hinv_mem_X : ∀ x ∈ D_i.clearedSociety.transactionEnds P,
      inv_v x ∈ X ∧ D_i.clearedEmbedding.vMap (inv_v x) = x := by
    intro x hx
    have hx_img : x ∈ D_i.clearedEmbedding.vMap '' X := hEndsP ▸ hx
    obtain ⟨y, hyX, hyx⟩ := hx_img
    rcases hx with ⟨P₀, hP₀, z, hPath⟩
    obtain ⟨hinv_mem, hinv_eq⟩ := hinv_v x hPath.2.2.1
    have hy_eq : inv_v x = y :=
      D_i.clearedEmbedding.bijOn_v.injOn hinv_mem.1 (hX_sub hyX).1 (hinv_eq.trans hyx.symm)
    exact ⟨hy_eq ▸ hyX, hinv_eq⟩
  let a_S : Fin φ → S := inv_v ∘ a'
  let b_S : Fin φ → S := inv_v ∘ b'
  have ha'_ends : ∀ j : Fin φ, a' j ∈ D_i.clearedSociety.transactionEnds P := by
    intro j
    exact ⟨P' j, hP_range ▸ mem_range_self (Fin.rev j), b' j, (hEnds_idx (Fin.rev j)).2.2⟩
  have hb'_ends : ∀ j : Fin φ, b' j ∈ D_i.clearedSociety.transactionEnds P := by
    intro j
    have hP_j := (hEnds_idx (Fin.rev j)).2.2
    exact ⟨P' j, hP_range ▸ mem_range_self (Fin.rev j), a' j,
      ⟨hP_j.1.symm, hP_j.2.1.symm, hP_j.2.2.2, hP_j.2.2.1⟩⟩
  have hmap_eq : (List.ofFn a' ++ List.ofFn b').map inv_v = List.ofFn a_S ++ List.ofFn b_S := by
    simp [List.map_ofFn, a_S, b_S, Function.comp_def]
  have hNodup_S : (List.ofFn a_S ++ List.ofFn b_S).Nodup := by
    rw [← hmap_eq]
    refine hcw'.1.map_on ?_
    intro x hx y hy hxy
    have hx_bar := hcw'.2.1 x hx
    have hy_bar := hcw'.2.1 y hy
    rw [← (hinv_v x hx_bar).2, ← (hinv_v y hy_bar).2, hxy]
  have hOrder_S : GM12.IsListedInOrderOn (subBd D_i.Λ) (List.ofFn a_S ++ List.ofFn b_S) := by
    rw [← hmap_eq]
    exact isListedInOrderOn_of_isClockwiseSeq hNat hcw' (by simp; omega)
  have h_ab_mem : ∀ j : Fin φ,
      a_S j ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ ∧
      b_S j ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ :=
    fun j => ⟨hX_sub (hinv_mem_X (a' j) (ha'_ends j)).1, hX_sub (hinv_mem_X (b' j) (hb'_ends j)).1⟩
  have h_paths : ∀ j : Fin φ,
      IsHPathWithEnds G D_i.clearedEmbedding.imageGraph (P' j) (D_i.clearedEmbedding.vMap (a_S j))
        (D_i.clearedEmbedding.vMap (b_S j))
        := by
    intro j
    dsimp only [a_S, b_S, Function.comp_apply]
    rw [(hinv_mem_X (a' j) (ha'_ends j)).2, (hinv_mem_X (b' j) (hb'_ends j)).2]
    exact hPathsP (P' j) (hP_range ▸ mem_range_self (Fin.rev j)) (a' j) (b' j)
      (hEnds_idx (Fin.rev j)).2.2
  have h_disj : Pairwise (fun j₁ j₂ => Disjoint V(P' j₁) V(P' j₂)) := by
    intro j₁ j₂ hj
    rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
    exact hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _)
      (fun hEq => hj (Fin.rev_injective (hP_inj hEq)))
  have h_free : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁
      (θ - 4 * (3 * beta + 3) - 2) (range a_S ∪ range b_S) := by
    refine hFreeX.subset D_i.isCleared.hasMetric.1.2.1 ?_
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact (hinv_mem_X (a' j) (ha'_ends j)).1
    · exact (hinv_mem_X (b' j) (hb'_ends j)).1
  have hSpan_Λ : IsSigmaSpan G (clearedSubdrawing H D_i.Λ) D_i.clearedEmbedding θ_star
      (θ - 4 * (3 * beta + 3) - 2) T_star D_i.T₁ := by
    have hEq : θ - 4 * (3 * beta + 3) - 2 = θ - (4 * (3 * beta + 3) + 2) := by omega
    exact hEq ▸ D_i.isRearranged.isSpan'
  exact GraphMinor.GM15.theorem_3_3_proof.{u, v, w} G (clearedSubdrawing H D_i.Λ)
    D_i.clearedEmbedding θ_star
    (θ - 4 * (3 * beta + 3) - 2) φ
    T_star D_i.T₁ D_i.Λ P' a_S b_S hSpan_Λ D_i.mem_R_cleared D_i.isZone.isOArc_bd
    D_i.isCircuit_bd hφ3 hφ_le hNodup_S hOrder_S h_ab_mem h_paths h_disj h_free

/-- **Graph Minors XV, (7.9)** (page 143):
"If $\mathscr{P}$ is a crosscap transaction of cardinality $\phi$ then (S2) is true.*
*Proof.* This is immediate from (3.3)." -/
theorem Section7.theorem_7_9_proof
     :
    GM15Theorem79Statement.{u, v, w} := by
  have h33 : GM15Theorem33Statement.{u, v, w} := theorem_3_3_proof
  intro S _ _ α β G H η θ_star θ θ' π beta μ φ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X
  exact _root_.GraphMinor.GM15.theorem_7_9_proof
    G H η θ_star θ θ' π beta μ φ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X

/-- Extending `clearedSubdrawing H D_i.Λ` inside `D_i.Λ` as in `(3.4)` preserves the rearrangement
within `3 * beta + 3` of `r i` (`IsRearrangedWithin`). -/
theorem isRearrangedWithin_of_cleared_extension
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ θ' π beta μ k : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {r : Fin k → Set S}
    {S₀ : Set (Society α β)} {α₀_disc : Society α β → Set S} {α₀_pt : α → S}
    {i : Fin k}
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (hSpan' : IsSigmaSpan G H' η' θ_star (θ - (4 * (3 * beta + 3) + 2)) T_star T')
    (hM' : HasTangleMetric H' (θ - (4 * (3 * beta + 3) + 2)) T' d')
    (hU_diff : H'.U \ D_i.Λ = (clearedSubdrawing H D_i.Λ).U)
    (hSub : (clearedSubdrawing H D_i.Λ).IsSubdrawing H')
    (hvMap : ∀ x ∈ (clearedSubdrawing H D_i.Λ).V, η'.vMap x = D_i.clearedEmbedding.vMap x)
    (heMap : ∀ e ∈ (clearedSubdrawing H D_i.Λ).E, η'.eMap e = D_i.clearedEmbedding.eMap e)
    (hInd : T' = GM10.inducedTangle H'.toHypergraph (clearedSubdrawing H D_i.Λ).toHypergraph
      D_i.T₁ (θ - (4 * (3 * beta + 3) + 2)))
    (hθ₁_ge : 2 ≤ θ - (4 * (3 * beta + 3) + 2)) :
    IsRearrangedWithin G H H' η η' θ_star θ (3 * beta + 3) T_star T T' d d' (r i) := by
  let H₁ := clearedSubdrawing H D_i.Λ
  let lam₁ := 3 * beta + 3
  let θ₁ := θ - (4 * lam₁ + 2)
  have hS : IsClosedSurface S :=
    ⟨D_i.isRearranged.isSpan.isSurface.1, D_i.isRearranged.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp D_i.isRearranged.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := D_i.isRearranged.isSpan.isConnected
  have hM₁ : HasTangleMetric H₁ θ₁ D_i.T₁ D_i.d₁ := D_i.isRearranged.isCompression.hasMetric'
  have hSubHyp : H₁.toHypergraph ≤ H'.toHypergraph := by
    refine ⟨hSub.1, hSub.2, fun e he₁ => ?_⟩
    ext v
    change (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ↔ (e ∈ H₁.E ∧ v ∈ H₁.V ∧ v ∈ closure e)
    constructor
    · rintro ⟨_, hv', hve⟩
      have hv_in : v ∈ closure e ∩ H'.V := ⟨hve, hv'⟩
      rw [← hSub.closure_inter_V he₁] at hv_in
      exact ⟨he₁, hv_in.2, hve⟩
    · rintro ⟨_, hv₁, hve⟩
      exact ⟨hSub.2 he₁, hSub.1 hv₁, hve⟩
  have hIndBySub : T' = GM12.inducedBySubgraph H'.toHypergraph H₁.toHypergraph θ₁ D_i.T₁ := by
    rw [hInd]
    ext ⟨A, B⟩
    constructor
    · rintro ⟨hsep, hord, ⟨C, D⟩, hCD, hCE⟩
      obtain ⟨hsep₁, hle₁⟩ := isSeparation_inter_subhypergraph hSubHyp hsep
      exact ⟨hsep, hord, GM10.theorem_2_9_proof hM₁.1.2.1 hCD hsep₁ (lt_of_le_of_lt hle₁ hord)
        (Or.inr (Or.inr ⟨hθ₁_ge, subset_of_eq hCE.symm⟩))⟩
    · rintro ⟨hsep, hord, hmem₁⟩
      exact ⟨hsep, hord, (A ∩ H₁.toHypergraph, B ∩ H₁.toHypergraph), hmem₁, rfl⟩
  have h77_ii := (GraphMinor.GM12.gm15_theorem_7_7.{w} H' H₁ θ₁ θ₁ T' D_i.T₁ d' D_i.d₁ hS hConn hM'
    hSub hM₁.1.1 le_rfl hM₁).2
    rfl hIndBySub
  refine ⟨D_i.isRearranged.z_mem, D_i.isRearranged.isSpan, hSpan', ?_, ?_, ?_, ?_⟩
  · intro a ha hlt
    have ha₁ : a ∈ H₁.A := D_i.isRearranged.atom_mem a ha hlt
    have ha_ne_Λ : a ≠ D_i.Λ := by
      intro hEq
      have hle := D_i.isZone.dist_le a ha (hEq ▸ subset_closure)
      omega
    rcases ha₁ with (⟨v, hv₁, rfl⟩ | he₁) | hr₁
    · exact Or.inl (Or.inl ⟨v, hSub.1 hv₁, rfl⟩)
    · exact Or.inl (Or.inr (hSub.2 he₁))
    · refine Or.inr ?_
      obtain ⟨x, hx⟩ := (hM₁.1.1.2 a hr₁).isPathConnected.nonempty
      have hx_not_Λ : x ∉ D_i.Λ := fun hxΛ =>
        ha_ne_Λ (region_eq_of_mem hr₁ D_i.mem_R_cleared hx hxΛ)
      have hx_not_U₁ : x ∉ H₁.U := region_subset hr₁ hx
      have hx_not_U' : x ∉ H'.U := fun hxU' => hx_not_U₁ (hU_diff ▸ ⟨hxU', hx_not_Λ⟩)
      refine (mem_R_iff H').mpr ⟨x, hx_not_U', subset_antisymm ?_ ?_⟩
      · refine (region_isPreconnected hr₁).subset_connectedComponentIn hx ?_
        intro y hy
        have hy_not_Λ : y ∉ D_i.Λ := fun hyΛ =>
          ha_ne_Λ (region_eq_of_mem hr₁ D_i.mem_R_cleared hy hyΛ)
        have hy_not_U₁ : y ∉ H₁.U := region_subset hr₁ hy
        exact ⟨mem_univ y, fun hyU' => hy_not_U₁ (hU_diff ▸ ⟨hyU', hy_not_Λ⟩)⟩
      · have hr_eq : connectedComponentIn (univ \ H₁.U) x = a := by
          obtain ⟨z₀, _, hz₀_eq⟩ := (mem_R_iff H₁).mp hr₁
          have hx_z₀ : x ∈ connectedComponentIn (univ \ H₁.U) z₀ := hz₀_eq ▸ hx
          exact (connectedComponentIn_eq hx_z₀).symm.trans hz₀_eq.symm
        rw [← hr_eq]
        refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn ⟨mem_univ x, hx_not_U'⟩) ?_
        exact (connectedComponentIn_subset _ _).trans fun y hy =>
          ⟨mem_univ y, fun hyU₁ => hy.2 (hSub.U_subset hyU₁)⟩
  · intro v hv hlt
    obtain ⟨hv₁, hv_eq⟩ := D_i.isRearranged.vMap_eq v hv hlt
    exact ⟨hSub.1 hv₁, (hvMap v hv₁).trans hv_eq⟩
  · intro e he hlt
    obtain ⟨he₁, he_eq⟩ := D_i.isRearranged.eMap_eq e he hlt
    exact ⟨hSub.2 he₁, (heMap e he₁).trans he_eq⟩
  · refine ⟨D_i.isRearranged.isCompression.lam_lt, D_i.isRearranged.isCompression.hasMetric, hM',
      fun σ₁ σ₂ => ?_⟩
    obtain ⟨a₁', ha₁', hσ₁'⟩ := exists_atom_of_point H' σ₁
    obtain ⟨a₂', ha₂', hσ₂'⟩ := exists_atom_of_point H' σ₂
    obtain ⟨a₁₁, ha₁₁, hσ₁₁⟩ := exists_atom_of_point H₁ σ₁
    obtain ⟨a₂₁, ha₂₁, hσ₂₁⟩ := exists_atom_of_point H₁ σ₂
    have hsub₁ := atom_subset_of_isSubdrawing hSub ha₁' ha₁₁ hσ₁' hσ₁₁
    have hsub₂ := atom_subset_of_isSubdrawing hSub ha₂' ha₂₁ hσ₂' hσ₂₁
    have hle_1_prime := h77_ii a₁' ha₁' a₂' ha₂' a₁₁ ha₁₁ a₂₁ ha₂₁ hsub₁ hsub₂
    have hle_H_1 := D_i.isRearranged.isCompression.dist_le σ₁ σ₂
    rw [pointDist_eq_of_mem_atom (d := D_i.d₁) ha₁₁ ha₂₁ hσ₁₁ hσ₂₁] at hle_H_1
    rw [pointDist_eq_of_mem_atom (d := d') ha₁' ha₂' hσ₁' hσ₂']
    omega

/-- Statement of Graph Minors XV, (7.10) (page 143):
"{P}$ is not a leap transaction of cardinality $\tau_1$." -/
def GM15Theorem710Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ τ₁ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β)) (X : Set S),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    12 ≤ μ → Even μ → τ₁ = 4 + μ / 2 → 3 * beta + 3 ≤ lam →
    2 * τ₁ < θ - 4 * (3 * beta + 3) - 2 →
    D_i.clearedSociety.IsTransaction P →
    (∀ P₀ ∈ P, ∀ a b : α,
      D_i.clearedSociety.IsOmegaPathWithEnds P₀ a b →
      IsHPathWithEnds G D_i.clearedEmbedding.imageGraph P₀ a b) →
    X ⊆ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ →
    D_i.clearedSociety.transactionEnds P = D_i.clearedEmbedding.vMap '' X →
    IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X →
    P.ncard = τ₁ → ¬ D_i.clearedSociety.IsLeapTransaction P

/-- Graph Minors XV, (7.10), page 143: use the established (3.4) in the transaction argument. -/
theorem theorem_7_10_proof : GM15Theorem710Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ τ₁ k T_star T d r
    S₀ α₀_disc α₀_pt i D_i P X
    hFlat hμ12 hμ_even hτ₁_eq hlam_ge h2τ₁_lt hTransP hPathsP hX_sub hEndsP hFreeX hCardτ₁ hLeap
  rcases hLeap with ⟨A_f, B_f, _, p, hp3, P_idx, a_idx, b_idx, hP_inj, hP_range, hEnds_idx, hcw⟩
  have hp_eq : p = τ₁ := by
    rw [← hCardτ₁, ← hP_range, Set.ncard_range_of_injective hP_inj, Nat.card_fin]
  subst p
  let v_α : Fin (2 * τ₁) → α := fun m =>
    if hm1 : m.1 < τ₁ then a_idx ⟨τ₁ - 1 - m.1, by omega⟩
    else if hm2 : m.1 < 2 * τ₁ - 1 then b_idx ⟨m.1 - τ₁ + 1, by omega⟩
    else b_idx ⟨0, by omega⟩
  have hofFn_v_α : List.ofFn v_α =
      (List.ofFn a_idx).reverse ++
        List.ofFn (fun j : Fin (τ₁ - 1) => b_idx ⟨j.1 + 1, by omega⟩) ++
        [b_idx ⟨0, by omega⟩] := by
    apply List.ext_getElem (by simp; omega)
    intro m hm1 hm2
    simp only [List.length_ofFn] at hm1
    simp only [List.getElem_ofFn, v_α]
    split_ifs with h1 h2
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_reverse, List.length_ofFn, List.getElem_ofFn]
    · rw [List.getElem_append_right (by simp; omega)]
      simp
  have hcw' : D_i.clearedSociety.Ω.IsClockwiseSeq (List.ofFn v_α) := by rwa [hofFn_v_α]
  obtain ⟨inv_v, hinv_v, hNat⟩ := D_i.soc_Λ_natural
  have hinv_mem_X : ∀ x ∈ D_i.clearedSociety.transactionEnds P,
      inv_v x ∈ X ∧ D_i.clearedEmbedding.vMap (inv_v x) = x := by
    intro x hx
    have hx_img : x ∈ D_i.clearedEmbedding.vMap '' X := hEndsP ▸ hx
    obtain ⟨y, hyX, hyx⟩ := hx_img
    rcases hx with ⟨P₀, hP₀, z, hPath⟩
    obtain ⟨hinv_mem, hinv_eq⟩ := hinv_v x hPath.2.2.1
    have hy_eq : inv_v x = y :=
      D_i.clearedEmbedding.bijOn_v.injOn hinv_mem.1 (hX_sub hyX).1 (hinv_eq.trans hyx.symm)
    exact ⟨hy_eq ▸ hyX, hinv_eq⟩
  have hv_α_ends : ∀ m : Fin (2 * τ₁), v_α m ∈ D_i.clearedSociety.transactionEnds P := by
    intro m
    dsimp only [v_α]
    split_ifs with h1 h2
    · let idx : Fin τ₁ := ⟨τ₁ - 1 - m.1, by omega⟩
      exact ⟨P_idx idx, hP_range ▸ mem_range_self idx, b_idx idx, (hEnds_idx idx).2.2⟩
    · let idx : Fin τ₁ := ⟨m.1 - τ₁ + 1, by omega⟩
      have hP_idx := (hEnds_idx idx).2.2
      exact ⟨P_idx idx, hP_range ▸ mem_range_self idx, a_idx idx,
        ⟨hP_idx.1.symm, hP_idx.2.1.symm, hP_idx.2.2.2, hP_idx.2.2.1⟩⟩
    · let idx : Fin τ₁ := ⟨0, by omega⟩
      have hP_idx := (hEnds_idx idx).2.2
      exact ⟨P_idx idx, hP_range ▸ mem_range_self idx, a_idx idx,
        ⟨hP_idx.1.symm, hP_idx.2.1.symm, hP_idx.2.2.2, hP_idx.2.2.1⟩⟩
  let v_S : Fin (2 * τ₁) → S := inv_v ∘ v_α
  have hmap_eq : (List.ofFn v_α).map inv_v = List.ofFn v_S := by
    simp [List.map_ofFn, v_S, Function.comp_def]
  have hNodup_v : (List.ofFn v_S).Nodup := by
    rw [← hmap_eq]
    refine hcw'.1.map_on ?_
    intro x hx y hy hxy
    rw [← (hinv_v x (hcw'.2.1 x hx)).2, ← (hinv_v y (hcw'.2.1 y hy)).2, hxy]
  have hOrder_v : GM12.IsListedInOrderOn (subBd D_i.Λ) (List.ofFn v_S) := by
    rw [← hmap_eq]
    exact isListedInOrderOn_of_isClockwiseSeq hNat hcw' (by simp; omega)
  have hv_mem : ∀ m : Fin (2 * τ₁), v_S m ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ :=
    fun m => hX_sub (hinv_mem_X (v_α m) (hv_α_ends m)).1
  have hv_free : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁
      (θ - 4 * (3 * beta + 3) - 2) (range v_S) := by
    refine hFreeX.subset D_i.isCleared.hasMetric.1.2.1 ?_
    rintro _ ⟨m, rfl⟩
    exact (hinv_mem_X (v_α m) (hv_α_ends m)).1
  let P_sub : Fin (τ₁ - 1) → Graph α β := fun j => P_idx ⟨τ₁ - 1 - j.1, by omega⟩
  have hP_sub_paths : ∀ j : Fin (τ₁ - 1), ∃ i₁ i₂ : Fin (2 * τ₁),
      i₁.1 = j.1 ∧ i₂.1 = 2 * τ₁ - 2 - j.1 ∧
      IsHPathWithEnds G D_i.clearedEmbedding.imageGraph (P_sub j)
        (D_i.clearedEmbedding.vMap (v_S i₁)) (D_i.clearedEmbedding.vMap (v_S i₂)) := by
    intro j
    let i₁ : Fin (2 * τ₁) := ⟨j.1, by omega⟩
    let i₂ : Fin (2 * τ₁) := ⟨2 * τ₁ - 2 - j.1, by omega⟩
    refine ⟨i₁, i₂, rfl, rfl, ?_⟩
    rw [show D_i.clearedEmbedding.vMap (v_S i₁) = v_α i₁ from (hinv_mem_X (v_α i₁)
      (hv_α_ends i₁)).2,
      show D_i.clearedEmbedding.vMap (v_S i₂) = v_α i₂ from (hinv_mem_X (v_α i₂) (hv_α_ends i₂)).2]
    have hi₁_eq : v_α i₁ = a_idx ⟨τ₁ - 1 - j.1, by omega⟩ := by
      dsimp only [v_α, i₁]
      split_ifs with h1 h2 <;> try omega
      rfl
    have hi₂_eq : v_α i₂ = b_idx ⟨τ₁ - 1 - j.1, by omega⟩ := by
      dsimp only [v_α, i₂]
      split_ifs with h1 h2 <;> try omega
      congr 1; ext; dsimp; omega
    rw [hi₁_eq, hi₂_eq]
    exact hPathsP (P_sub j) (hP_range ▸ mem_range_self _) _ _ (hEnds_idx _).2.2
  have hP_sub_disj : Pairwise (fun j₁ j₂ => Disjoint V(P_sub j₁) V(P_sub j₂)) := by
    intro j₁ j₂ hj
    rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
    refine hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _) (fun hEq => hj ?_)
    have hidx := congrArg Fin.val (hP_inj hEq)
    dsimp only at hidx
    ext
    omega
  let i_k : Fin (2 * τ₁) := ⟨τ₁ - 1, by omega⟩
  let i_last : Fin (2 * τ₁) := ⟨2 * τ₁ - 1, by omega⟩
  have hEq_θ₁ : θ - 4 * (3 * beta + 3) - 2 = θ - (4 * (3 * beta + 3) + 2) := by omega
  have hSpan_Λ : IsSigmaSpan G (clearedSubdrawing H D_i.Λ) D_i.clearedEmbedding θ_star
      (θ - 4 * (3 * beta + 3) - 2) T_star D_i.T₁ := hEq_θ₁ ▸ D_i.isRearranged.isSpan'
  have hM_Λ : HasTangleMetric (clearedSubdrawing H D_i.Λ)
      (θ - 4 * (3 * beta + 3) - 2) D_i.T₁ D_i.d₁ :=
    hEq_θ₁ ▸ D_i.isRearranged.isCompression.hasMetric'
  obtain ⟨H', η', T', d', r₁, r₂, hSpan', hM', _, _, _, _, _, hU_diff, hSub, hvMap, heMap,
      hImg, hInd, _, _, _, _, _, _, _, _, _, _, hdist_v⟩ :=
    GraphMinor.GM15.theorem_3_4_drawn.{u, v, w} G (clearedSubdrawing H D_i.Λ) D_i.clearedEmbedding
      θ_star
      (θ - 4 * (3 * beta + 3) - 2) τ₁
      T_star D_i.T₁ D_i.d₁ D_i.Λ v_S P_sub i_k i_last
      hSpan_Λ hM_Λ D_i.mem_R_cleared D_i.isZone.isOArc_bd D_i.isCircuit_bd
      hp3 hNodup_v hOrder_v hv_mem hv_free hP_sub_paths hP_sub_disj rfl rfl
  rw [hEq_θ₁] at hSpan' hM' hInd
  have hRearr' : IsRearrangedWithin G H H' η η' θ_star θ (3 * beta + 3) T_star T T' d d' (r i) :=
    isRearrangedWithin_of_cleared_extension D_i hSpan' hM' hU_diff hSub hvMap heMap hInd
      (by omega)
  -- `P_last = P_idx ⟨0, _⟩` is an `η'(H')`-path in `G` with ends `η'(v_S i_k)` and `η'(v_S
  -- i_last)`.
  let P_last := P_idx ⟨0, by omega⟩
  have hP_last_H₁ : IsHPathWithEnds G D_i.clearedEmbedding.imageGraph P_last
      (D_i.clearedEmbedding.vMap (v_S i_k)) (D_i.clearedEmbedding.vMap (v_S i_last)) := by
    rw [show D_i.clearedEmbedding.vMap (v_S i_k) = v_α i_k from (hinv_mem_X (v_α i_k)
      (hv_α_ends i_k)).2,
      show D_i.clearedEmbedding.vMap (v_S i_last) = v_α i_last from (hinv_mem_X (v_α i_last)
        (hv_α_ends i_last)).2]
    have hik_eq : v_α i_k = a_idx ⟨0, by omega⟩ := by
      dsimp only [v_α, i_k]
      split_ifs with h1 h2 <;> try omega
      congr 1; ext; dsimp; omega
    have hil_eq : v_α i_last = b_idx ⟨0, by omega⟩ := by
      dsimp only [v_α, i_last]
      split_ifs with h1 h2 <;> try omega
      rfl
    rw [hik_eq, hil_eq]
    exact hPathsP P_last (hP_range ▸ mem_range_self _) _ _ (hEnds_idx ⟨0, by omega⟩).2.2
  have hDisj_last_sub : ∀ j : Fin (τ₁ - 1), Disjoint V(P_last) V(P_sub j) := by
    intro j
    rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
    refine hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _) (fun hEq => ?_)
    have hidx := congrArg Fin.val (hP_inj hEq)
    dsimp only at hidx
    omega
  have hv_k_eq : η'.vMap (v_S i_k) = D_i.clearedEmbedding.vMap (v_S i_k) := hvMap _ (hv_mem i_k).1
  have hv_last_eq : η'.vMap (v_S i_last) = D_i.clearedEmbedding.vMap (v_S i_last) := hvMap _
    (hv_mem i_last).1
  have hP_last_H' : IsHPathWithEnds G η'.imageGraph P_last
      (η'.vMap (v_S i_k)) (η'.vMap (v_S i_last)) := by
    rw [hv_k_eq, hv_last_eq]
    refine ⟨η'.imageGraph_le, hP_last_H₁.2.1, hP_last_H₁.2.2.1, ?_, ?_, ?_, ?_⟩
    · rw [hImg, vertexSet_subgraphUnion]
      exact Or.inl hP_last_H₁.2.2.2.1
    · rw [hImg, vertexSet_subgraphUnion]
      exact Or.inl hP_last_H₁.2.2.2.2.1
    · rw [hImg, vertexSet_subgraphUnion, inter_union_distrib_left, hP_last_H₁.2.2.2.2.2.1]
      have hEmp : V(P_last) ∩ V(subgraphSUnion G (range P_sub)) = ∅ := by
        rw [vertexSet_subgraphSUnion]
        ext x
        simp only [mem_inter_iff, mem_iUnion, mem_empty_iff_false, iff_false,
          not_and, not_exists]
        rintro hx Q ⟨j, rfl⟩ hxj
        exact Set.disjoint_left.mp (hDisj_last_sub j) hx hxj
      rw [hEmp, union_empty]
    · have hSub_le_mem : ∀ Q ∈ range P_sub, Q ≤ G := by
        rintro _ ⟨j, rfl⟩
        exact (hP_sub_paths j).choose_spec.choose_spec.2.2.2.1.le
      have hSub_le : subgraphSUnion G (range P_sub) ≤ G := subgraphSUnion_le hSub_le_mem
      rw [hImg, edgeSet_subgraphUnion D_i.clearedEmbedding.imageGraph_le hSub_le,
        disjoint_union_right]
      refine ⟨hP_last_H₁.2.2.2.2.2.2, ?_⟩
      rw [edgeSet_subgraphSUnion hSub_le_mem]
      refine Set.disjoint_left.mpr fun e heL heSub => ?_
      simp only [mem_iUnion] at heSub
      obtain ⟨_, ⟨j, rfl⟩, hej⟩ := heSub
      obtain ⟨u, w, hlinkL⟩ := exists_isLink_of_mem_edgeSet heL
      obtain ⟨u', w', hlinkj⟩ := exists_isLink_of_mem_edgeSet hej
      have hlinkG_L : G.IsLink e u w := hlinkL.mono hP_last_H₁.2.1.le
      have hlinkG_j : G.IsLink e u' w' :=
        hlinkj.mono (hP_sub_paths j).choose_spec.choose_spec.2.2.2.1.le
      have hu_eq : u = u' ∨ u = w' := G.eq_or_eq_of_isLink_of_isLink hlinkG_L hlinkG_j
      rcases hu_eq with rfl | rfl
      · exact Set.disjoint_left.mp (hDisj_last_sub j) hlinkL.left_mem hlinkj.left_mem
      · exact Set.disjoint_left.mp (hDisj_last_sub j) hlinkL.left_mem hlinkj.right_mem
  have hStep' : IsMuSteppedSpan G H' η' d' μ := by
    have hμ_eq : 2 * τ₁ - 8 = μ := by
      rcases hμ_even with ⟨m, rfl⟩
      omega
    exact ⟨P_last, v_S i_k, v_S i_last, hSub.1 (hv_mem i_k).1, hSub.1 (hv_mem i_last).1,
      hP_last_H', hμ_eq ▸ hdist_v⟩
  have hord := hFlat.order_ge
  have hFlat_beta : IsFlatSpan G H η θ_star θ (3 * beta + 3) μ T_star (GM10.truncation T θ) :=
    theorem_5_1_proof G H η θ_star θ θ lam (3 * beta + 3) μ μ T_star T
      hFlat hlam_ge le_rfl (by omega) le_rfl (by omega) (fun _ => by omega) (by omega)
  have hTrunc_eq : GM10.truncation T θ = T := by
    ext ⟨A, B⟩
    exact ⟨fun h => h.1, fun h => ⟨h, hFlat.isSpan.isControlling.isTangle_H.order_lt h⟩⟩
  rw [hTrunc_eq] at hFlat_beta
  exact hFlat_beta.no_stepped_rearrangement hRearr' hStep'

/-- **Graph Minors XV, (7.10)** (page 143):
"{P}$ is not a leap transaction of cardinality $\tau_1$."
Proved from `(3.4)` (`theorem_3_4_proof`) and `(5.1)` (`theorem_5_1_proof`). -/
theorem Section7.theorem_7_10_proof
     :
    GM15Theorem710Statement.{u, v, w} := by
  have h34 : GM15Theorem34Statement.{u, v, w} := theorem_3_4_proof
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ τ₁ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X
  exact _root_.GraphMinor.GM15.theorem_7_10_proof
    G H η θ_star θ θ' lam π beta μ τ₁ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X

/-- Statement of Graph Minors XV, (7.11) (page 143):
"If $\mathscr{P}$ is a doublecross transaction of cardinality $\tau_2$ then (S1) holds."
(In Claim `(1)` on page 143, `(3.4)` is applied with `k - 1 = τ₂ - 4` paths, that is, `k = τ₂ - 3`,
which yields `d'(s₁, s₂) ≥ 2k - 6 = 2(τ₂ - 3) - 6 = 2τ₂ - 12` rather than `2τ₂ - 6`; accordingly we
take `τ₂ = 6 + θ' / 2` rather than `3 + θ' / 2`. See the correction to the proof of (7.11) in
`corrections/GM15.md`.) -/
def GM15Theorem711Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam lam' π beta μ τ₂ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β)) (X : Set S),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    2 ≤ μ → 4 ≤ lam' → 4 * lam' + μ + 2 ≤ θ' → Even θ' → τ₂ = 6 + θ' / 2 →
    6 * (3 * beta + 3) + 5 * lam' + 3 * μ + 4 ≤ lam →
    θ' + 13 * μ + 14 ≤ beta →
    100 * beta ≤ θ →
    Injective r →
    (∀ j : Fin k, IsDrawingEye G H η θ T (r j)) →
    (∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → d (r j₁) (r j₂) = θ) →
    D_i.clearedSociety.IsTransaction P →
    (∀ P₀ ∈ P, ∀ a b : α,
      D_i.clearedSociety.IsOmegaPathWithEnds P₀ a b →
      IsHPathWithEnds G D_i.clearedEmbedding.imageGraph P₀ a b) →
    X ⊆ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ →
    D_i.clearedSociety.transactionEnds P = D_i.clearedEmbedding.vMap '' X →
    IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X →
    P.ncard = τ₂ → D_i.clearedSociety.IsDoublecrossTransaction P →
    Section7S1 S G θ_star T_star k μ lam' θ'

/-- Any order-preserving sublist of a list in order on `F` is also in order on `F`. -/
theorem isListedInOrderOn_of_strictMono
    {S : Type w} [TopologicalSpace S] {F : Set S} {n m : ℕ}
    {w : Fin n → S} {f : Fin m → Fin n}
    (hm : 0 < m) (hf : StrictMono f)
    (hOrder : GM12.IsListedInOrderOn F (List.ofFn w)) :
    GM12.IsListedInOrderOn F (List.ofFn (w ∘ f)) := by
  rcases hOrder with ⟨φ, t, ht_mono, ht_lt, ht_eq⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  let t' : ℕ → ℝ := fun i =>
    if hi : i < m then t (f ⟨i, hi⟩).1 else t 0 + 2 * Real.pi + i
  have ht'0 : t' 0 = t (f ⟨0, hm⟩).1 := by dsimp only [t']; split_ifs; rfl
  have ht0_le : t 0 ≤ t (f ⟨0, hm⟩).1 := ht_mono.monotone (Nat.zero_le _)
  refine ⟨φ, t', ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hj : j < m
    · have hi : i < m := hij.trans hj
      have hi_eq : t' i = t (f ⟨i, hi⟩).1 := by dsimp only [t']; split_ifs; rfl
      have hj_eq : t' j = t (f ⟨j, hj⟩).1 := by dsimp only [t']; split_ifs; rfl
      rw [hi_eq, hj_eq]
      exact ht_mono (hf hij)
    · by_cases hi : i < m
      · have hi_eq : t' i = t (f ⟨i, hi⟩).1 := by dsimp only [t']; split_ifs; rfl
        have hj_eq : t' j = t 0 + 2 * Real.pi + j := by dsimp only [t']; split_ifs; rfl
        have hlt := ht_lt (f ⟨i, hi⟩).1 (by simp)
        have hj_nn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      · have hi_eq : t' i = t 0 + 2 * Real.pi + i := by dsimp only [t']; split_ifs; rfl
        have hj_eq : t' j = t 0 + 2 * Real.pi + j := by dsimp only [t']; split_ifs; rfl
        have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
        linarith
  · intro i hi
    rw [List.length_ofFn] at hi
    have hi_eq : t' i = t (f ⟨i, hi⟩).1 := by dsimp only [t']; split_ifs; rfl
    have hlt := ht_lt (f ⟨i, hi⟩).1 (by simp)
    linarith
  · intro i hi
    have hi' : i < m := by simpa using hi
    have hi_eq : t' i = t (f ⟨i, hi'⟩).1 := by dsimp only [t']; split_ifs; rfl
    rw [hi_eq]
    have h := ht_eq (f ⟨i, hi'⟩).1 (by simp)
    simpa using h

/-- Cyclic rotation of a list in order on `F` preserves `GM12.IsListedInOrderOn`. -/
theorem isListedInOrderOn_rotate
    {S : Type w} [TopologicalSpace S] {F : Set S} {L₁ L₂ : List S}
    (h₁ : 0 < L₁.length) (h₂ : 0 < L₂.length)
    (hOrder : GM12.IsListedInOrderOn F (L₁ ++ L₂)) :
    GM12.IsListedInOrderOn F (L₂ ++ L₁) := by
  rcases hOrder with ⟨φ, t, ht_mono, ht_lt, ht_eq⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  let t' : ℕ → ℝ := fun i =>
    if i < L₂.length then t (i + L₁.length)
    else if i < L₂.length + L₁.length then t (i - L₂.length) + 2 * Real.pi
    else t L₁.length + 2 * Real.pi + i
  have ht'0 : t' 0 = t L₁.length := by
    simp only [t', h₂, ↓reduceIte, Nat.zero_add]
  have ht0_lt_n₁ : t 0 < t L₁.length := ht_mono h₁
  refine ⟨φ, t', ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi1 : i < L₂.length
    · by_cases hj1 : j < L₂.length
      · simp only [t', hi1, hj1, ↓reduceIte]
        exact ht_mono (by omega)
      · by_cases hj2 : j < L₂.length + L₁.length
        · simp only [t', hi1, hj1, hj2, ↓reduceIte]
          have hlt := ht_lt (i + L₁.length) (by simp; omega)
          have hle : t 0 ≤ t (j - L₂.length) := ht_mono.monotone (Nat.zero_le _)
          linarith
        · simp only [t', hi1, hj1, hj2, ↓reduceIte]
          have hlt := ht_lt (i + L₁.length) (by simp; omega)
          have hj_nn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith
    · by_cases hi2 : i < L₂.length + L₁.length
      · have hj1 : ¬ j < L₂.length := by omega
        by_cases hj2 : j < L₂.length + L₁.length
        · simp only [t', hi1, hi2, hj1, hj2, ↓reduceIte]
          have hlt : t (i - L₂.length) < t (j - L₂.length) := ht_mono (by omega)
          linarith
        · simp only [t', hi1, hi2, hj1, hj2, ↓reduceIte]
          have hlt : t (i - L₂.length) < t L₁.length := ht_mono (by omega)
          have hj_nn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith
      · have hj1 : ¬ j < L₂.length := by omega
        have hj2 : ¬ j < L₂.length + L₁.length := by omega
        simp only [t', hi1, hi2, hj1, hj2, ↓reduceIte]
        have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
        linarith
  · intro i hi
    rw [List.length_append] at hi
    rw [ht'0]
    by_cases hi1 : i < L₂.length
    · simp only [t', hi1, ↓reduceIte]
      have hlt := ht_lt (i + L₁.length) (by simp; omega)
      linarith
    · simp only [t', hi1, hi, ↓reduceIte]
      have hlt : t (i - L₂.length) < t L₁.length := ht_mono (by omega)
      linarith
  · intro i hi
    have hi_len : i < L₂.length + L₁.length := by simpa using hi
    by_cases hi1 : i < L₂.length
    · simp only [t', hi1, ↓reduceIte]
      have h := ht_eq (i + L₁.length) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at h
      rw [List.getElem_append_left hi1]
      simpa using h
    · simp only [t', hi1, hi_len, ↓reduceIte]
      have h := ht_eq (i - L₂.length) (by simp; omega)
      rw [List.getElem_append_left (by omega)] at h
      rw [List.getElem_append_right (by omega)]
      have hexp : Circle.exp (t (i - L₂.length) + 2 * Real.pi) = Circle.exp (t (i - L₂.length))
        := by
        rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
      simpa [hexp] using h

/-- If `H₁ ≤ H'` and `T'` is the tangle in `H'` induced by a tangle `T₁` of order `θ₁ ≥ 2` in `H₁`,
then any `T₁`-free subset `Y ⊆ V(H₁)` is also `T'`-free in `H'`. -/
theorem isFreeSet_inducedTangle_of_isFreeSet
    {S : Type w} [TopologicalSpace S]
    {H₁ H' : Drawing S} {θ₁ : ℕ}
    {T₁ T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Y : Set S}
    (hSub : H₁.IsSubdrawing H')
    (hT₁ : IsTangle H₁.toHypergraph θ₁ T₁)
    (hInd : T' = GM10.inducedTangle H'.toHypergraph H₁.toHypergraph T₁ θ₁)
    (hθ₁ : 2 ≤ θ₁)
    (hFree : IsFreeSet H₁.toHypergraph T₁ θ₁ Y) :
    IsFreeSet H'.toHypergraph T' θ₁ Y := by
  have hSubHyp : H₁.toHypergraph ≤ H'.toHypergraph := by
    refine ⟨hSub.1, hSub.2, fun e he₁ => ?_⟩
    ext v
    change (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ↔ (e ∈ H₁.E ∧ v ∈ H₁.V ∧ v ∈ closure e)
    constructor
    · rintro ⟨_, hv', hve⟩
      have hv_in : v ∈ closure e ∩ H'.V := ⟨hve, hv'⟩
      rw [← hSub.closure_inter_V he₁] at hv_in
      exact ⟨he₁, hv_in.2, hve⟩
    · rintro ⟨_, hv₁, hve⟩
      exact ⟨hSub.2 he₁, hSub.1 hv₁, hve⟩
  refine ⟨hFree.1.trans hSub.1, hFree.2.1, fun A B hAB hY_sub => ?_⟩
  rw [hInd] at hAB
  rcases hAB with ⟨hsep, hord, ⟨C, D⟩, hCD, hCE⟩
  obtain ⟨hsep₁, hle₁⟩ := isSeparation_inter_subhypergraph hSubHyp hsep
  have hmem₁ : (A ∩ H₁.toHypergraph, B ∩ H₁.toHypergraph) ∈ T₁ :=
    GM10.theorem_2_9_proof hT₁ hCD hsep₁ (lt_of_le_of_lt hle₁ hord)
      (Or.inr (Or.inr ⟨hθ₁, subset_of_eq hCE.symm⟩))
  have hY_sub₁ : Y ⊆ (A ∩ H₁.toHypergraph).vertexSet := fun y hy => ⟨hY_sub hy, hFree.1 hy⟩
  exact (hFree.2.2 hmem₁ hY_sub₁).trans hle₁

/-- An `H₁_G`-path `P₀` in `G` that is vertex-disjoint from each `P_sub j` is also a path with the
same ends over `H₁_G ∪ ⋃ j, P_sub j`. -/
theorem isHPathWithEnds_subgraphUnion_of_disjoint
    {G H₁_G P₀ : Graph α β} {u v : α} {ι : Type*} {P_sub : ι → Graph α β}
    (hH₁_le : H₁_G ≤ G)
    (hSub_le_mem : ∀ Q ∈ range P_sub, Q ≤ G)
    (hP₀ : IsHPathWithEnds G H₁_G P₀ u v)
    (hDisj : ∀ j : ι, Disjoint V(P₀) V(P_sub j)) :
    IsHPathWithEnds G (subgraphUnion G H₁_G (subgraphSUnion G (range P_sub))) P₀ u v := by
  have hSub_le : subgraphSUnion G (range P_sub) ≤ G := subgraphSUnion_le hSub_le_mem
  refine ⟨subgraphUnion_le hH₁_le hSub_le, hP₀.2.1, hP₀.2.2.1, ?_, ?_, ?_, ?_⟩
  · rw [vertexSet_subgraphUnion]
    exact Or.inl hP₀.2.2.2.1
  · rw [vertexSet_subgraphUnion]
    exact Or.inl hP₀.2.2.2.2.1
  · rw [vertexSet_subgraphUnion, inter_union_distrib_left, hP₀.2.2.2.2.2.1]
    have hEmp : V(P₀) ∩ V(subgraphSUnion G (range P_sub)) = ∅ := by
      rw [vertexSet_subgraphSUnion]
      ext x
      simp only [mem_inter_iff, mem_iUnion, mem_empty_iff_false, iff_false, not_and, not_exists]
      rintro hx _ ⟨j, rfl⟩ hxj
      exact Set.disjoint_left.mp (hDisj j) hx hxj
    rw [hEmp, union_empty]
  · rw [edgeSet_subgraphUnion hH₁_le hSub_le, disjoint_union_right]
    refine ⟨hP₀.2.2.2.2.2.2, ?_⟩
    rw [edgeSet_subgraphSUnion hSub_le_mem]
    refine Set.disjoint_left.mpr fun e he₀ heSub => ?_
    simp only [mem_iUnion] at heSub
    obtain ⟨_, ⟨j, rfl⟩, hej⟩ := heSub
    obtain ⟨u₁, w₁, hlink₀⟩ := exists_isLink_of_mem_edgeSet he₀
    obtain ⟨u₂, w₂, hlinkj⟩ := exists_isLink_of_mem_edgeSet hej
    have hlinkG₀ : G.IsLink e u₁ w₁ := hlink₀.mono hP₀.2.1.le
    have hlinkGj : G.IsLink e u₂ w₂ := hlinkj.mono (hSub_le_mem _ (mem_range_self j))
    rcases G.eq_or_eq_of_isLink_of_isLink hlinkG₀ hlinkGj with rfl | rfl
    · exact Set.disjoint_left.mp (hDisj j) hlink₀.left_mem hlinkj.left_mem
    · exact Set.disjoint_left.mp (hDisj j) hlink₀.left_mem hlinkj.right_mem

/-- Rotate the clockwise sequence of a doublecross transaction of cardinality `τ₂ ≥ 12` by 2 so
that the vertices `w_α : Fin (2 * τ₂) → α` start at `a_{τ₂ - 3}` as in the proof of `(7.11)`. -/
theorem exists_doublecross_rotated_seq
    {S : Type w} [TopologicalSpace S] {V₀ : Set S} {vMap : S → α} {Λ : Set S}
    {Ω : CyclicPerm α} {inv_v : α → S} {τ₂ : ℕ} (hτ₂ : 12 ≤ τ₂)
    (a_idx b_idx : Fin τ₂ → α)
    (hinv_v : ∀ x ∈ Ω.bar, inv_v x ∈ V₀ ∧ vMap (inv_v x) = x)
    (hNat : IsNaturalOrderFrom inv_v Ω (subBd Λ))
    (hcw : Ω.IsClockwiseSeq
      ((List.ofFn a_idx).reverse ++
        [b_idx ⟨1, by omega⟩, b_idx ⟨0, by omega⟩] ++
        List.ofFn (fun j : Fin (τ₂ - 4) => b_idx ⟨j.1 + 2, by omega⟩) ++
        [b_idx ⟨τ₂ - 1, by omega⟩, b_idx ⟨τ₂ - 2, by omega⟩])) :
    ∃ w_α : Fin (2 * τ₂) → α,
      (List.ofFn (inv_v ∘ w_α)).Nodup ∧
      GM12.IsListedInOrderOn (subBd Λ) (List.ofFn (inv_v ∘ w_α)) ∧
      (∀ m : Fin (2 * τ₂), (∃ idx, w_α m = a_idx idx) ∨ (∃ idx, w_α m = b_idx idx)) ∧
      (∀ (m : Fin (2 * τ₂)) (_ : m.1 < τ₂ - 2), w_α m = a_idx ⟨τ₂ - 3 - m.1, by omega⟩) ∧
      w_α ⟨τ₂ - 2, by omega⟩ = b_idx ⟨1, by omega⟩ ∧
      w_α ⟨τ₂ - 1, by omega⟩ = b_idx ⟨0, by omega⟩ ∧
      (∀ (m : Fin (2 * τ₂)) (_ : τ₂ ≤ m.1) (_ : m.1 < 2 * τ₂ - 4),
        w_α m = b_idx ⟨m.1 - τ₂ + 2, by omega⟩) ∧
      w_α ⟨2 * τ₂ - 4, by omega⟩ = b_idx ⟨τ₂ - 1, by omega⟩ ∧
      w_α ⟨2 * τ₂ - 3, by omega⟩ = b_idx ⟨τ₂ - 2, by omega⟩ ∧
      w_α ⟨2 * τ₂ - 2, by omega⟩ = a_idx ⟨τ₂ - 1, by omega⟩ ∧
      w_α ⟨2 * τ₂ - 1, by omega⟩ = a_idx ⟨τ₂ - 2, by omega⟩ := by
  let w_α : Fin (2 * τ₂) → α := fun m =>
    if hm1 : m.1 < τ₂ - 2 then a_idx ⟨τ₂ - 3 - m.1, by omega⟩
    else if hm2 : m.1 = τ₂ - 2 then b_idx ⟨1, by omega⟩
    else if hm3 : m.1 = τ₂ - 1 then b_idx ⟨0, by omega⟩
    else if hm4 : m.1 < 2 * τ₂ - 4 then b_idx ⟨m.1 - τ₂ + 2, by omega⟩
    else if hm5 : m.1 = 2 * τ₂ - 4 then b_idx ⟨τ₂ - 1, by omega⟩
    else if hm6 : m.1 = 2 * τ₂ - 3 then b_idx ⟨τ₂ - 2, by omega⟩
    else if hm7 : m.1 = 2 * τ₂ - 2 then a_idx ⟨τ₂ - 1, by omega⟩
    else a_idx ⟨τ₂ - 2, by omega⟩
  let L₁ : List α := [a_idx ⟨τ₂ - 1, by omega⟩, a_idx ⟨τ₂ - 2, by omega⟩]
  let L₂ : List α :=
    List.ofFn (fun j : Fin (τ₂ - 2) => a_idx ⟨τ₂ - 3 - j.1, by omega⟩) ++
      [b_idx ⟨1, by omega⟩, b_idx ⟨0, by omega⟩] ++
      List.ofFn (fun j : Fin (τ₂ - 4) => b_idx ⟨j.1 + 2, by omega⟩) ++
      [b_idx ⟨τ₂ - 1, by omega⟩, b_idx ⟨τ₂ - 2, by omega⟩]
  have hrev_split : (List.ofFn a_idx).reverse =
      L₁ ++ List.ofFn (fun j : Fin (τ₂ - 2) => a_idx ⟨τ₂ - 3 - j.1, by omega⟩) := by
    apply List.ext_getElem (by simp [L₁]; omega)
    intro m hm1 hm2
    simp only [List.length_reverse, List.length_ofFn] at hm1
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    by_cases hm : m < 2
    · rw [List.getElem_append_left (by simp [L₁]; omega)]
      rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
      · simp [L₁]
      · simp only [L₁, List.getElem_cons_succ, List.getElem_cons_zero]
        exact congrArg a_idx (Fin.ext (by dsimp; omega))
    · rw [List.getElem_append_right (by simp [L₁]; omega)]
      simp only [L₁, List.length_cons, List.length_nil, List.getElem_ofFn]
      exact congrArg a_idx (Fin.ext (by dsimp; omega))
  have hcw_L₁₂ : Ω.IsClockwiseSeq (L₁ ++ L₂) := by
    have hEq : (List.ofFn a_idx).reverse ++
        [b_idx ⟨1, by omega⟩, b_idx ⟨0, by omega⟩] ++
        List.ofFn (fun j : Fin (τ₂ - 4) => b_idx ⟨j.1 + 2, by omega⟩) ++
        [b_idx ⟨τ₂ - 1, by omega⟩, b_idx ⟨τ₂ - 2, by omega⟩] = L₁ ++ L₂ := by
      rw [hrev_split]
      simp only [L₂, List.append_assoc]
    rwa [← hEq]
  have hofFn_w_α : List.ofFn w_α = L₂ ++ L₁ := by
    apply List.ext_getElem (by simp [L₁, L₂]; omega)
    intro m hm1 hm2
    simp only [List.length_ofFn] at hm1
    simp only [List.getElem_ofFn, w_α]
    split_ifs with h1 h2 h3 h4 h5 h6 h7
    · rw [List.getElem_append_left (by simp [L₂]; omega)]
      simp only [L₂]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_ofFn]
    · subst h2
      rw [List.getElem_append_left (by simp [L₂])]
      simp only [L₂]
      rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
        List.getElem_append_right (by simp)]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero]
    · subst h3
      rw [List.getElem_append_left (by simp [L₂]; omega)]
      simp only [L₂]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      have h_idx : τ₂ - 1 - (τ₂ - 2) = 1 := by omega
      simp [h_idx]
    · rw [List.getElem_append_left (by simp [L₂]; omega)]
      simp only [L₂]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil,
        List.getElem_ofFn]
      congr 1; ext; dsimp; omega
    · subst h5
      rw [List.getElem_append_left (by simp [L₂]; omega)]
      simp only [L₂]
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have h_idx : 2 * τ₂ - 4 - (τ₂ - 2 + (1 + 1) + (τ₂ - 4)) = 0 := by omega
      simp [h_idx]
    · subst h6
      rw [List.getElem_append_left (by simp [L₂]; omega)]
      simp only [L₂]
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have h_idx : 2 * τ₂ - 3 - (τ₂ - 2 + (1 + 1) + (τ₂ - 4)) = 1 := by omega
      simp [h_idx]
    · subst h7
      rw [List.getElem_append_right (by simp [L₂]; omega)]
      simp only [L₁, L₂, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have h_idx : 2 * τ₂ - 2 - (τ₂ - 2 + (1 + 1) + (τ₂ - 4) + (1 + 1)) = 0 := by omega
      simp [h_idx]
    · have hm_eq : m = 2 * τ₂ - 1 := by omega
      subst hm_eq
      rw [List.getElem_append_right (by simp [L₂]; omega)]
      simp only [L₁, L₂, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have h_idx : 2 * τ₂ - 1 - (τ₂ - 2 + (1 + 1) + (τ₂ - 4) + (1 + 1)) = 1 := by omega
      simp [h_idx]
  have hmap_w : List.ofFn (inv_v ∘ w_α) = (L₂ ++ L₁).map inv_v := by
    rw [← List.map_ofFn, hofFn_w_α]
  have hNodup_L₁₂ : ((L₁ ++ L₂).map inv_v).Nodup := by
    refine hcw_L₁₂.1.map_on ?_
    intro x hx y hy hxy
    rw [← (hinv_v x (hcw_L₁₂.2.1 x hx)).2, ← (hinv_v y (hcw_L₁₂.2.1 y hy)).2, hxy]
  have hOrder_L₁₂ : GM12.IsListedInOrderOn (subBd Λ) ((L₁ ++ L₂).map inv_v) :=
    isListedInOrderOn_of_isClockwiseSeq hNat hcw_L₁₂ (by simp [L₁, L₂]; omega)
  refine ⟨w_α, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap_w, List.map_append]
    rw [List.map_append] at hNodup_L₁₂
    exact hNodup_L₁₂.perm List.perm_append_comm
  · rw [hmap_w, List.map_append]
    rw [List.map_append] at hOrder_L₁₂
    exact isListedInOrderOn_rotate (by simp [L₁]) (by simp [L₂]) hOrder_L₁₂
  · intro m
    dsimp only [w_α]
    by_cases h1 : m.1 < τ₂ - 2
    · rw [dite_eq_left h1]; exact Or.inl ⟨_, rfl⟩
    · rw [dite_eq_right h1]
      by_cases h2 : m.1 = τ₂ - 2
      · rw [dite_eq_left h2]; exact Or.inr ⟨_, rfl⟩
      · rw [dite_eq_right h2]
        by_cases h3 : m.1 = τ₂ - 1
        · rw [dite_eq_left h3]; exact Or.inr ⟨_, rfl⟩
        · rw [dite_eq_right h3]
          by_cases h4 : m.1 < 2 * τ₂ - 4
          · rw [dite_eq_left h4]; exact Or.inr ⟨_, rfl⟩
          · rw [dite_eq_right h4]
            by_cases h5 : m.1 = 2 * τ₂ - 4
            · rw [dite_eq_left h5]; exact Or.inr ⟨_, rfl⟩
            · rw [dite_eq_right h5]
              by_cases h6 : m.1 = 2 * τ₂ - 3
              · rw [dite_eq_left h6]; exact Or.inr ⟨_, rfl⟩
              · rw [dite_eq_right h6]
                by_cases h7 : m.1 = 2 * τ₂ - 2
                · rw [dite_eq_left h7]; exact Or.inl ⟨_, rfl⟩
                · rw [dite_eq_right h7]; exact Or.inl ⟨_, rfl⟩
  · intro m hm
    dsimp only [w_α]
    rw [dite_eq_left hm]
  · dsimp only [w_α]
    rw [dite_eq_right (by omega), dite_eq_left rfl]
  · dsimp only [w_α]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left rfl]
  · intro m hm_ge hm_lt
    dsimp only [w_α]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_left hm_lt]
  · dsimp only [w_α]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_left rfl]
  · dsimp only [w_α]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left rfl]
  · dsimp only [w_α]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_left rfl]
  · dsimp only [w_α]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega)]

private theorem interSet_U_subset_of_isClosed {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) {F : Set S} (hcl : IsClosed F) :
    (H.interSet F).U ⊆ F := by
  change (H.interSet F).V ∪ _ ⊆ F
  rw [interSet_V_of_isClosed H hcl]
  refine union_subset inter_subset_right ?_
  exact iUnion₂_subset fun e he => hcl.closure_subset_iff.mpr he.1.2

private def doublecross_boundary_index (τ : ℕ) (hτ : 12 ≤ τ)
    (j : Fin (2 * (τ - 3))) : Fin (2 * τ) :=
  if hj₁ : j.1 < τ - 3 then ⟨j.1, by omega⟩
  else if hj₂ : j.1 < 2 * (τ - 3) - 1 then ⟨j.1 + 3, by omega⟩
  else ⟨2 * τ - 4, by omega⟩

private def doublecross_middle_paths {α : Type u} {β : Type v} {τ : ℕ}
    (P : Fin τ → Graph α β) (hτ : 12 ≤ τ) (j : Fin (τ - 3 - 1)) : Graph α β :=
  P ⟨τ - 3 - j.1, by omega⟩

private def initial_split_vertices {S : Type w} {k : ℕ} (v : Fin (2 * k) → S) : List S :=
  List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩)

private def final_split_vertices {S : Type w} {k : ℕ} (v : Fin (2 * k) → S) : List S :=
  List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)

private def split_vertices_without_last {S : Type w} {k : ℕ}
    (v : Fin (2 * k) → S) : List S :=
  List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩)

private abbrev SplitRegionOrder {S : Type w} [TopologicalSpace S] [T2Space S]
    (H H' : Drawing S)
    (Λ r : Set S) (order : S → S → S → S → List S) : Prop :=
  ∀ a b c d : S,
    a ∈ H.V ∩ subBd Λ → b ∈ H.V ∩ subBd Λ →
    c ∈ H.V ∩ subBd Λ → d ∈ H.V ∩ subBd Λ →
    (order a b c d).Nodup → GM12.IsListedInOrderOn (subBd Λ) (order a b c d) →
    a ∈ (H'.interSet (subBd r)).V ∧ b ∈ (H'.interSet (subBd r)).V ∧
    c ∈ (H'.interSet (subBd r)).V ∧ d ∈ (H'.interSet (subBd r)).V ∧
    OccurInCircuitOrder (H'.interSet (subBd r)) a b c d

private theorem first_split_region_is_eye
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (θ' : ℕ)
    (π : ℕ)
    (beta : ℕ)
    (μ : ℕ)
    (τ₂ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S)
    (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β))
    (X : Set S)
    (hτ₂_eq : τ₂ = 6 + θ' / 2)
    (hTransP : D_i.clearedSociety.IsTransaction P)
    (hPathsP : ∀ P₀ ∈ P, ∀ (a b : α), D_i.clearedSociety.IsOmegaPathWithEnds P₀ a b
      → IsHPathWithEnds G
      D_i.clearedEmbedding.imageGraph P₀ a b)
    (hCardτ₂ : P.ncard = τ₂)
    (A_f : Set α)
    (B_f : Set α)
    (P_idx : Fin τ₂ → Graph α β)
    (a_idx : Fin τ₂ → α)
    (b_idx : Fin τ₂ → α)
    (hP_inj : Injective P_idx)
    (hP_range : range P_idx = P)
    (hEnds_idx : ∀ (i_1 : Fin τ₂), a_idx i_1 ∈ A_f ∧ b_idx i_1 ∈ B_f ∧
      D_i.clearedSociety.IsOmegaPathWithEnds (P_idx i_1) (a_idx i_1) (b_idx i_1))
    (hτ₂_ge12 : 12 ≤ τ₂)
    (inv_v : α → S)
    (hinv_mem_X : ∀ x ∈ D_i.clearedSociety.transactionEnds P, inv_v x ∈ X
      ∧ D_i.clearedEmbedding.vMap (inv_v x) = x)
    (w_α : Fin (2 * τ₂) → α)
    (hNodup_w : (List.ofFn (inv_v ∘ w_α)).Nodup)
    (hOrder_w : GM12.IsListedInOrderOn (subBd D_i.Λ) (List.ofFn (inv_v ∘ w_α)))
    (hw_α_lt : ∀ (m : Fin (2 * τ₂)) (_ : m.1 < τ₂ - 2),
      w_α m = a_idx ⟨τ₂ - 3 - m.1, by omega⟩)
    (hw_α_m2 : w_α ⟨τ₂ - 2, by omega⟩ = b_idx ⟨1, by omega⟩)
    (hw_α_m1 : w_α ⟨τ₂ - 1, by omega⟩ = b_idx ⟨0, by omega⟩) :
    let w : Fin (2 * τ₂) → S := inv_v ∘ w_α
    ∀ (hw_α_ends : ∀ (m : Fin (2 * τ₂)), w_α m ∈ D_i.clearedSociety.transactionEnds P),
    ∀ (hw_mem : ∀ (m : Fin (2 * τ₂)), w m ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ),
    ∀ (hw_vMap : ∀ (m : Fin (2 * τ₂)), D_i.clearedEmbedding.vMap (w m) = w_α m),
    let k_34 : ℕ := τ₂ - 3
    ∀ (hk_34_ge : 3 ≤ k_34),
    let f_34 := doublecross_boundary_index τ₂ hτ₂_ge12
    let v_34 : Fin (2 * k_34) → S := w ∘ f_34
    let P_sub := doublecross_middle_paths P_idx hτ₂_ge12
    ∀ (H' : Drawing S),
    ∀ (η' : SpanEmbedding H' G),
    ∀ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    ∀ (d' : Set S → Set S → ℕ),
    ∀ (r₁ : Set S),
    ∀ (r₂ : Set S),
    ∀ (hM' : HasTangleMetric H' (θ - (4 * (3 * beta + 3) + 2)) T' d'),
    ∀ (hr₁_R : r₁ ∈ H'.R),
    ∀ (hvMap : ∀ x ∈ (clearedSubdrawing H D_i.Λ).V, η'.vMap x = D_i.clearedEmbedding.vMap x),
    ∀ (hImg : η'.imageGraph = subgraphUnion G D_i.clearedEmbedding.imageGraph (subgraphSUnion G
      (range
      P_sub))),
    ∀ (hOArc_r₁ : IsOArc (subBd r₁)),
    ∀ (hCirc_r₁ : (H'.interSet (subBd r₁)).IsCircuit),
    SplitRegionOrder (clearedSubdrawing H D_i.Λ) H' D_i.Λ r₁
      (fun a b c d => initial_split_vertices v_34 ++ [a, b, c, d] ++ final_split_vertices v_34) →
    ∀ (hSub_le_mem : ∀ Q ∈ range P_sub, Q ≤ G),
    let θ₁ : ℕ := θ - (4 * (3 * beta + 3) + 2)
    (IsFreeSet H'.toHypergraph T' θ₁ X) →
    (IsClosed (subBd r₁)) →
    IsDrawingEye G H' η' θ₁ T' r₁ := by
  intro w hw_α_ends hw_mem hw_vMap k_34 hk_34_ge f_34 v_34 P_sub H' η' T' d' r₁ r₂ hM' hr₁_R hvMap
    hImg
    hOArc_r₁ hCirc_r₁ hOrd_r₁ hSub_le_mem θ₁ hFreeX_T' hcl_bd_r₁
  let w₁ := w ⟨τ₂ - 4, by omega⟩
  let w₂ := w ⟨τ₂ - 3, by omega⟩
  let w₃ := w ⟨τ₂ - 2, by omega⟩
  let w₄ := w ⟨τ₂ - 1, by omega⟩
  let f_r₁ : Fin (2 * τ₂ - 3) → Fin (2 * τ₂) := fun j => ⟨j.1, by omega⟩
  have hf_r₁_mono : StrictMono f_r₁ := fun _ _ h => h
  have hList_r₁_eq :
      (List.ofFn fun j : Fin (k_34 - 1) => v_34 ⟨j.1, by omega⟩) ++
        [w₁, w₂, w₃, w₄] ++
        (List.ofFn fun j : Fin k_34 => v_34 ⟨k_34 + j.1, by omega⟩) =
      List.ofFn (w ∘ f_r₁) := by
    apply List.ext_getElem (by simp [k_34]; omega)
    intro m hm1 hm2
    simp only [List.length_ofFn] at hm2
    simp only [List.getElem_ofFn, Function.comp_apply, f_r₁]
    by_cases hm_left : m < k_34 - 1
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_ofFn, v_34, Function.comp_apply, f_34, doublecross_boundary_index]
      split_ifs <;> try omega
      rfl
    · by_cases hm_mid : m < k_34 - 1 + 4
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp only [List.length_ofFn]
        rcases (by omega : m - (k_34 - 1) = 0 ∨ m - (k_34 - 1) = 1 ∨
            m - (k_34 - 1) = 2 ∨ m - (k_34 - 1) = 3) with h0 | h1 | h2 | h3
        · simp only [h0, List.getElem_cons_zero, w₁]
          exact congrArg w (Fin.ext (by dsimp; omega))
        · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, w₂]
          exact congrArg w (Fin.ext (by dsimp; omega))
        · simp only [h2, List.getElem_cons_succ, List.getElem_cons_zero, w₃]
          exact congrArg w (Fin.ext (by dsimp; omega))
        · simp only [h3, List.getElem_cons_succ, List.getElem_cons_zero, w₄]
          exact congrArg w (Fin.ext (by dsimp; omega))
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil,
          List.getElem_ofFn, v_34, Function.comp_apply, f_34, doublecross_boundary_index]
        split_ifs <;> try omega
        · congr 1; ext; dsimp; omega
        · congr 1; ext; dsimp; omega
  have hNodup_r₁ : ((List.ofFn fun j : Fin (k_34 - 1) => v_34 ⟨j.1, by omega⟩) ++
      [w₁, w₂, w₃, w₄] ++
      (List.ofFn fun j : Fin k_34 => v_34 ⟨k_34 + j.1, by omega⟩)).Nodup := by
    rw [hList_r₁_eq, List.nodup_ofFn]
    exact (List.nodup_ofFn.mp hNodup_w).comp hf_r₁_mono.injective
  have hOrder_r₁ : GM12.IsListedInOrderOn (subBd D_i.Λ)
      ((List.ofFn fun j : Fin (k_34 - 1) => v_34 ⟨j.1, by omega⟩) ++
        [w₁, w₂, w₃, w₄] ++
        (List.ofFn fun j : Fin k_34 => v_34 ⟨k_34 + j.1, by omega⟩)) := by
    rw [hList_r₁_eq]
    exact isListedInOrderOn_of_strictMono (by omega) hf_r₁_mono hOrder_w
  obtain ⟨hw₁_V, hw₂_V, hw₃_V, hw₄_V, hOcc_r₁⟩ :=
    hOrd_r₁ w₁ w₂ w₃ w₄ (hw_mem _) (hw_mem _) (hw_mem _) (hw_mem _) hNodup_r₁ hOrder_r₁
  have hNodup4_r₁ : [w₁, w₂, w₃, w₄].Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hNodup_r₁).1).2.1
  have hFree4_r₁ : IsFreeSet H'.toHypergraph T' θ₁ {w₁, w₂, w₃, w₄} := by
    refine hFreeX_T'.subset hM'.1.2.1 ?_
    rintro x (rfl | rfl | rfl | rfl) <;> exact (hinv_mem_X _ (hw_α_ends _)).1
  let P₁_r₁ := P_idx ⟨1, by omega⟩
  let P₂_r₁ := P_idx ⟨0, by omega⟩
  have hDisj_P₁₂_r₁ : Disjoint V(P₁_r₁) V(P₂_r₁) := by
    rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
    exact hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _)
      (fun hEq => by
        have hIndex := congrArg Fin.val (hP_inj hEq)
        dsimp [P_sub, doublecross_middle_paths] at hIndex
        omega)
  have hP₁_r₁_H' : IsHPathWithEnds G η'.imageGraph P₁_r₁ (η'.vMap w₁) (η'.vMap w₃) := by
    rw [hImg, hvMap w₁ (hw_mem _).1, hvMap w₃ (hw_mem _).1, hw_vMap, hw_vMap]
    refine isHPathWithEnds_subgraphUnion_of_disjoint D_i.clearedEmbedding.imageGraph_le hSub_le_mem
      ?_ ?_
    · have hw₁_eq : w_α ⟨τ₂ - 4, by omega⟩ = a_idx ⟨1, by omega⟩ := by
        rw [hw_α_lt ⟨τ₂ - 4, by omega⟩ (by dsimp; omega)]
        congr 1; ext; dsimp; omega
      rw [hw₁_eq, hw_α_m2]
      exact hPathsP P₁_r₁ (hP_range ▸ mem_range_self _) _ _ (hEnds_idx ⟨1, by omega⟩).2.2
    · intro j
      rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
      exact hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _)
        (fun hEq => by
          have hIndex := congrArg Fin.val (hP_inj hEq)
          dsimp [P_sub, doublecross_middle_paths] at hIndex
          omega)
  have hP₂_r₁_H' : IsHPathWithEnds G η'.imageGraph P₂_r₁ (η'.vMap w₂) (η'.vMap w₄) := by
    rw [hImg, hvMap w₂ (hw_mem _).1, hvMap w₄ (hw_mem _).1, hw_vMap, hw_vMap]
    refine isHPathWithEnds_subgraphUnion_of_disjoint D_i.clearedEmbedding.imageGraph_le hSub_le_mem
      ?_ ?_
    · have hw₂_eq : w_α ⟨τ₂ - 3, by omega⟩ = a_idx ⟨0, by omega⟩ := by
        rw [hw_α_lt ⟨τ₂ - 3, by omega⟩ (by dsimp; omega)]
        congr 1; ext; dsimp; omega
      rw [hw₂_eq, hw_α_m1]
      exact hPathsP P₂_r₁ (hP_range ▸ mem_range_self _) _ _ (hEnds_idx ⟨0, by omega⟩).2.2
    · intro j
      rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
      exact hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _)
        (fun hEq => by
          have hIndex := congrArg Fin.val (hP_inj hEq)
          dsimp [P_sub, doublecross_middle_paths] at hIndex
          omega)
  exact ⟨hr₁_R, H'.interSet (subBd r₁), w₁, w₂, w₃, w₄, P₁_r₁, P₂_r₁,
    hCirc_r₁, H'.span_isSubdrawing _ _,
    GM11.eq_of_oArc_subset (GM11.IsCircuit.isOArc_U hCirc_r₁) hOArc_r₁
      (interSet_U_subset_of_isClosed H' hcl_bd_r₁),
    hw₁_V, hw₂_V, hw₃_V, hw₄_V, hNodup4_r₁, hOcc_r₁, hFree4_r₁,
    hDisj_P₁₂_r₁, hP₁_r₁_H', hP₂_r₁_H'⟩

private theorem last_split_region_is_eye
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (θ' : ℕ)
    (π : ℕ)
    (beta : ℕ)
    (μ : ℕ)
    (τ₂ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S)
    (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β))
    (X : Set S)
    (hτ₂_eq : τ₂ = 6 + θ' / 2)
    (hTransP : D_i.clearedSociety.IsTransaction P)
    (hPathsP : ∀ P₀ ∈ P, ∀ (a b : α), D_i.clearedSociety.IsOmegaPathWithEnds P₀ a b
      → IsHPathWithEnds G
      D_i.clearedEmbedding.imageGraph P₀ a b)
    (hCardτ₂ : P.ncard = τ₂)
    (A_f : Set α)
    (B_f : Set α)
    (P_idx : Fin τ₂ → Graph α β)
    (a_idx : Fin τ₂ → α)
    (b_idx : Fin τ₂ → α)
    (hP_inj : Injective P_idx)
    (hP_range : range P_idx = P)
    (hEnds_idx : ∀ (i_1 : Fin τ₂), a_idx i_1 ∈ A_f ∧ b_idx i_1 ∈ B_f ∧
      D_i.clearedSociety.IsOmegaPathWithEnds (P_idx i_1) (a_idx i_1) (b_idx i_1))
    (hτ₂_ge12 : 12 ≤ τ₂)
    (inv_v : α → S)
    (hinv_mem_X : ∀ x ∈ D_i.clearedSociety.transactionEnds P, inv_v x ∈ X
      ∧ D_i.clearedEmbedding.vMap (inv_v x) = x)
    (w_α : Fin (2 * τ₂) → α)
    (hNodup_w : (List.ofFn (inv_v ∘ w_α)).Nodup)
    (hOrder_w : GM12.IsListedInOrderOn (subBd D_i.Λ) (List.ofFn (inv_v ∘ w_α)))
    (hw_α_last4 : w_α ⟨2 * τ₂ - 4, by omega⟩ = b_idx ⟨τ₂ - 1, by omega⟩)
    (hw_α_last3 : w_α ⟨2 * τ₂ - 3, by omega⟩ = b_idx ⟨τ₂ - 2, by omega⟩)
    (hw_α_last2 : w_α ⟨2 * τ₂ - 2, by omega⟩ = a_idx ⟨τ₂ - 1, by omega⟩)
    (hw_α_last1 : w_α ⟨2 * τ₂ - 1, by omega⟩ = a_idx ⟨τ₂ - 2, by omega⟩) :
    let w : Fin (2 * τ₂) → S := inv_v ∘ w_α
    ∀ (hw_α_ends : ∀ (m : Fin (2 * τ₂)), w_α m ∈ D_i.clearedSociety.transactionEnds P),
    ∀ (hw_mem : ∀ (m : Fin (2 * τ₂)), w m ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ),
    ∀ (hw_vMap : ∀ (m : Fin (2 * τ₂)), D_i.clearedEmbedding.vMap (w m) = w_α m),
    let k_34 : ℕ := τ₂ - 3
    ∀ (hk_34_ge : 3 ≤ k_34),
    let f_34 := doublecross_boundary_index τ₂ hτ₂_ge12
    let v_34 : Fin (2 * k_34) → S := w ∘ f_34
    let P_sub := doublecross_middle_paths P_idx hτ₂_ge12
    ∀ (H' : Drawing S),
    ∀ (η' : SpanEmbedding H' G),
    ∀ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    ∀ (d' : Set S → Set S → ℕ),
    ∀ (r₁ : Set S),
    ∀ (r₂ : Set S),
    ∀ (hM' : HasTangleMetric H' (θ - (4 * (3 * beta + 3) + 2)) T' d'),
    ∀ (hr₂_R : r₂ ∈ H'.R),
    ∀ (hvMap : ∀ x ∈ (clearedSubdrawing H D_i.Λ).V, η'.vMap x = D_i.clearedEmbedding.vMap x),
    ∀ (hImg : η'.imageGraph = subgraphUnion G D_i.clearedEmbedding.imageGraph (subgraphSUnion G
      (range
      P_sub))),
    ∀ (hOArc_r₂ : IsOArc (subBd r₂)),
    ∀ (hCirc_r₂ : (H'.interSet (subBd r₂)).IsCircuit),
    SplitRegionOrder (clearedSubdrawing H D_i.Λ) H' D_i.Λ r₂
      (fun a b c d => split_vertices_without_last v_34 ++ [a, b, c, d]) →
    ∀ (hSub_le_mem : ∀ Q ∈ range P_sub, Q ≤ G),
    let θ₁ : ℕ := θ - (4 * (3 * beta + 3) + 2)
    (IsFreeSet H'.toHypergraph T' θ₁ X) →
    (IsClosed (subBd r₂)) →
    IsDrawingEye G H' η' θ₁ T' r₂ := by
  intro w hw_α_ends hw_mem hw_vMap k_34 hk_34_ge f_34 v_34 P_sub H' η' T' d' r₁ r₂ hM' hr₂_R hvMap
    hImg
    hOArc_r₂ hCirc_r₂ hOrd_r₂ hSub_le_mem θ₁ hFreeX_T' hcl_bd_r₂
  let u₁ := w ⟨2 * τ₂ - 4, by omega⟩
  let u₂ := w ⟨2 * τ₂ - 3, by omega⟩
  let u₃ := w ⟨2 * τ₂ - 2, by omega⟩
  let u₄ := w ⟨2 * τ₂ - 1, by omega⟩
  let f_r₂ : Fin (2 * k_34 + 3) → Fin (2 * τ₂) := fun j =>
    if hj1 : j.1 < k_34 then ⟨j.1, by omega⟩
    else ⟨j.1 + 3, by omega⟩
  have hf_r₂_mono : StrictMono f_r₂ := by
    intro j₁ j₂ hj
    change (f_r₂ j₁).1 < (f_r₂ j₂).1
    dsimp only [f_r₂]
    split_ifs <;> dsimp <;> omega
  have hList_r₂_eq :
      (List.ofFn fun j : Fin (2 * k_34 - 1) => v_34 ⟨j.1, by omega⟩) ++
        [u₁, u₂, u₃, u₄] =
      List.ofFn (w ∘ f_r₂) := by
    apply List.ext_getElem (by simp [k_34]; omega)
    intro m hm1 hm2
    simp only [List.length_ofFn] at hm2
    simp only [List.getElem_ofFn, Function.comp_apply, f_r₂]
    by_cases hm_left : m < 2 * k_34 - 1
    · rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_ofFn, v_34, Function.comp_apply, f_34, doublecross_boundary_index]
      split_ifs <;> try omega
      all_goals rfl
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      rcases (by omega : m - (2 * k_34 - 1) = 0 ∨ m - (2 * k_34 - 1) = 1 ∨
          m - (2 * k_34 - 1) = 2 ∨ m - (2 * k_34 - 1) = 3) with h0 | h1 | h2 | h3
      · simp only [h0, List.getElem_cons_zero, u₁]
        rw [dite_eq_right (by omega)]
        exact congrArg w (Fin.ext (by dsimp; omega))
      · simp only [h1, List.getElem_cons_succ, List.getElem_cons_zero, u₂]
        rw [dite_eq_right (by omega)]
        exact congrArg w (Fin.ext (by dsimp; omega))
      · simp only [h2, List.getElem_cons_succ, List.getElem_cons_zero, u₃]
        rw [dite_eq_right (by omega)]
        exact congrArg w (Fin.ext (by dsimp; omega))
      · simp only [h3, List.getElem_cons_succ, List.getElem_cons_zero, u₄]
        rw [dite_eq_right (by omega)]
        exact congrArg w (Fin.ext (by dsimp; omega))
  have hNodup_r₂ : ((List.ofFn fun j : Fin (2 * k_34 - 1) => v_34 ⟨j.1, by omega⟩) ++
      [u₁, u₂, u₃, u₄]).Nodup := by
    rw [hList_r₂_eq, List.nodup_ofFn]
    exact (List.nodup_ofFn.mp hNodup_w).comp hf_r₂_mono.injective
  have hOrder_r₂ : GM12.IsListedInOrderOn (subBd D_i.Λ)
      ((List.ofFn fun j : Fin (2 * k_34 - 1) => v_34 ⟨j.1, by omega⟩) ++
        [u₁, u₂, u₃, u₄]) := by
    rw [hList_r₂_eq]
    exact isListedInOrderOn_of_strictMono (by omega) hf_r₂_mono hOrder_w
  obtain ⟨hu₁_V, hu₂_V, hu₃_V, hu₄_V, hOcc_r₂⟩ :=
    hOrd_r₂ u₁ u₂ u₃ u₄ (hw_mem _) (hw_mem _) (hw_mem _) (hw_mem _) hNodup_r₂ hOrder_r₂
  have hNodup4_r₂ : [u₁, u₂, u₃, u₄].Nodup := (List.nodup_append.mp hNodup_r₂).2.1
  have hFree4_r₂ : IsFreeSet H'.toHypergraph T' θ₁ {u₁, u₂, u₃, u₄} := by
    refine hFreeX_T'.subset hM'.1.2.1 ?_
    rintro x (rfl | rfl | rfl | rfl) <;> exact (hinv_mem_X _ (hw_α_ends _)).1
  let P₁_r₂ := P_idx ⟨τ₂ - 1, by omega⟩
  let P₂_r₂ := P_idx ⟨τ₂ - 2, by omega⟩
  have hDisj_P₁₂_r₂ : Disjoint V(P₁_r₂) V(P₂_r₂) := by
    rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
    exact hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _)
      (fun hEq => by
        have hIndex := congrArg Fin.val (hP_inj hEq)
        dsimp [P_sub, doublecross_middle_paths] at hIndex
        omega)
  have hP₁_r₂_H' : IsHPathWithEnds G η'.imageGraph P₁_r₂ (η'.vMap u₁) (η'.vMap u₃) := by
    rw [hImg, hvMap u₁ (hw_mem _).1, hvMap u₃ (hw_mem _).1, hw_vMap, hw_vMap]
    refine isHPathWithEnds_subgraphUnion_of_disjoint D_i.clearedEmbedding.imageGraph_le hSub_le_mem
      ?_ ?_
    · rw [hw_α_last4, hw_α_last2]
      have hP_end := (hEnds_idx ⟨τ₂ - 1, by omega⟩).2.2
      exact hPathsP P₁_r₂ (hP_range ▸ mem_range_self _) _ _
        ⟨hP_end.1.symm, hP_end.2.1.symm, hP_end.2.2.2, hP_end.2.2.1⟩
    · intro j
      rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
      exact hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _)
        (fun hEq => by
          have hIndex := congrArg Fin.val (hP_inj hEq)
          dsimp [P_sub, doublecross_middle_paths] at hIndex
          omega)
  have hP₂_r₂_H' : IsHPathWithEnds G η'.imageGraph P₂_r₂ (η'.vMap u₂) (η'.vMap u₄) := by
    rw [hImg, hvMap u₂ (hw_mem _).1, hvMap u₄ (hw_mem _).1, hw_vMap, hw_vMap]
    refine isHPathWithEnds_subgraphUnion_of_disjoint D_i.clearedEmbedding.imageGraph_le hSub_le_mem
      ?_ ?_
    · rw [hw_α_last3, hw_α_last1]
      have hP_end := (hEnds_idx ⟨τ₂ - 2, by omega⟩).2.2
      exact hPathsP P₂_r₂ (hP_range ▸ mem_range_self _) _ _
        ⟨hP_end.1.symm, hP_end.2.1.symm, hP_end.2.2.2, hP_end.2.2.1⟩
    · intro j
      rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
      exact hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _)
        (fun hEq => by
          have hIndex := congrArg Fin.val (hP_inj hEq)
          dsimp [P_sub, doublecross_middle_paths] at hIndex
          omega)
  exact ⟨hr₂_R, H'.interSet (subBd r₂), u₁, u₂, u₃, u₄, P₁_r₂, P₂_r₂,
    hCirc_r₂, H'.span_isSubdrawing _ _,
    GM11.eq_of_oArc_subset (GM11.IsCircuit.isOArc_U hCirc_r₂) hOArc_r₂
      (interSet_U_subset_of_isClosed H' hcl_bd_r₂),
    hu₁_V, hu₂_V, hu₃_V, hu₄_V, hNodup4_r₂, hOcc_r₂, hFree4_r₂,
    hDisj_P₁₂_r₂, hP₁_r₂_H', hP₂_r₂_H'⟩

private theorem other_eye_survives_split
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (θ' : ℕ)
    (lam' : ℕ)
    (π : ℕ)
    (beta : ℕ)
    (μ : ℕ)
    (τ₂ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S)
    (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β))
    (hMetric : HasTangleMetric H θ T d)
    (hμ2 : 2 ≤ μ)
    (hlam'4 : 4 ≤ lam')
    (hθ'_ge : 4 * lam' + μ + 2 ≤ θ')
    (_ : τ₂ = 6 + θ' / 2)
    (hbeta_ge : θ' + 13 * μ + 14 ≤ beta)
    (hθ_ge : 100 * beta ≤ θ)
    (hr_eye : ∀ (j : Fin k), IsDrawingEye G H η θ T (r j))
    (hr_dist : ∀ (j₁ j₂ : Fin k), j₁ ≠ j₂ → d (r j₁) (r j₂) = θ)
    (_ : P.ncard = τ₂)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hd_symm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hd_tri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hd_inc : (H.E.Nonempty → ∀ v ∈ H.V, ∀ r ∈ H.R, v ∈ closure r → d {v} r ≤ 1) ∧ ∀ v ∈ H.V, ∀ e
      ∈ H.E, v ∈ closure e → d {v} e ≤ 2)
    (_ : 12 ≤ τ₂)
    :
    let k_34 : ℕ := τ₂ - 3
    (3 ≤ k_34) →
    ∀ (v_34 : Fin (2 * k_34) → S),
    (∀ (j : Fin (2 * k_34)), v_34 j ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ) →
    ∀ (P_sub : Fin (k_34 - 1) → Graph α β),
    (∀ (j : Fin (k_34 - 1)), ∃ i₁ i₂ : Fin (2 * k_34), i₁.1 = j.1 ∧ i₂.1 = 2 * k_34 - 2 - j.1 ∧
      IsHPathWithEnds G D_i.clearedEmbedding.imageGraph (P_sub j) (D_i.clearedEmbedding.vMap
        (v_34 i₁)) (D_i.clearedEmbedding.vMap (v_34
      i₂))) →
    ∀ (H' : Drawing S),
    ∀ (η' : SpanEmbedding H' G),
    ∀ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    ∀ (d' : Set S → Set S → ℕ),
    (Set S) →
    (Set S) →
    ((clearedSubdrawing H D_i.Λ).IsSubdrawing H') →
    (∀ x ∈ (clearedSubdrawing H D_i.Λ).V, η'.vMap x = D_i.clearedEmbedding.vMap x) →
    (η'.imageGraph = subgraphUnion G D_i.clearedEmbedding.imageGraph (subgraphSUnion G (range
      P_sub))) →
    (T' = inducedTangle H'.toHypergraph (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁
      (θ - (4 * (3 * beta + 3) + 2))) →
    (IsRearrangedWithin G H H' η η' θ_star θ (3 * beta + 3) T_star T T' d d' (r i)) →
    (∀ Q ∈ range P_sub, Q ≤ G) →
    let θ₁ : ℕ := θ - (4 * (3 * beta + 3) + 2)
    (IsTangle (clearedSubdrawing H D_i.Λ).toHypergraph θ₁ D_i.T₁) →
    (IsFlatSpan G H η θ_star θ (3 * beta + 3) μ T_star T) →
    ((clearedSubdrawing H D_i.Λ).IsSubdrawing H) →
    (V(D_i.clearedEmbedding.imageGraph) ⊆ V(η.imageGraph)) →
    (E(D_i.clearedEmbedding.imageGraph) ⊆ E(η.imageGraph)) →
    (H.E.Nonempty) →
    ∀ (j : Fin k), j ≠ i → IsDrawingEye G H' η' θ₁ T' (r j) := by
  intro k_34 hk_34_ge v_34 hv34_mem P_sub hP_sub_paths H' η' T' d' r₁ r₂ hSub hvMap hImg hInd
    hRearr' hSub_le_mem θ₁ hT₁_tangle hFlat_beta hSub_cleared hImg_sub_V hImg_sub_E hE_ne j hj_ne
  have hd_ij : d (r i) (r j) = θ := hr_dist i j hj_ne.symm
  rcases hr_eye j with ⟨hrj_R, C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub, hC_U,
    haC, hbC, hcC, hdvC, hnodup4, hord4, hFree4, hdisj_P₁₂, hP₁, hP₂⟩
  have hrj_A : r j ∈ H.A := Or.inr hrj_R
  have hri_A : r i ∈ H.A := Or.inr (hr_eye i).1
  have hC_vert_dist : ∀ v ∈ C.V, θ - 1 ≤ d (r i) {v} := by
    intro v hvC
    have hv_bd : v ∈ subBd (r j) := hC_U ▸ C.V_subset_U hvC
    have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hC_sub.1 hvC, rfl⟩)
    have hd_v_rj : d {v} (r j) ≤ 1 := hd_inc.1 hE_ne v (hC_sub.1 hvC) (r j) hrj_R hv_bd.1
    have htri := hd_tri (r i) hri_A {v} hvA (r j) hrj_A
    omega
  have hrj_R' : r j ∈ H'.R :=
    region_mem_R_of_mem_A hS hrj_R (hRearr'.atom_mem (r j) hrj_A (by omega))
  have hCV_H₁ : ∀ v ∈ C.V, v ∈ (clearedSubdrawing H D_i.Λ).V ∧ D_i.clearedEmbedding.vMap v
    = η.vMap v := by
    intro v hvC
    have hd_v := hC_vert_dist v hvC
    exact D_i.isRearranged.vMap_eq v (hC_sub.1 hvC) (by omega)
  have hCE_H₁ : ∀ e ∈ C.E, e ∈ (clearedSubdrawing H D_i.Λ).E ∧ D_i.clearedEmbedding.eMap e
    = η.eMap e := by
    intro e heC
    have ⟨v, hve, hvC⟩ : ∃ v, v ∈ closure e ∧ v ∈ C.V := by
      rcases C.edge_cond e heC with ⟨u, w, _, hcap, _⟩ | ⟨u, hcap, _⟩ <;>
        exact ⟨u, by rw [← mem_inter_iff, hcap]; simp⟩
    have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hC_sub.1 hvC, rfl⟩)
    have heA : e ∈ H.A := Or.inl (Or.inr (hC_sub.2 heC))
    have hd_v := hC_vert_dist v hvC
    have hd_v_e : d {v} e ≤ 2 := hd_inc.2 v (hC_sub.1 hvC) e (hC_sub.2 heC) hve
    have htri := hd_tri (r i) hri_A e heA {v} hvA
    have hsym := hd_symm {v} hvA e heA
    exact D_i.isRearranged.eMap_eq e (hC_sub.2 heC) (by omega)
  have hC_sub_H' : C.IsSubdrawing H' :=
    ⟨fun v hv => hSub.1 (hCV_H₁ v hv).1, fun e he => hSub.2 (hCE_H₁ e he).1⟩
  have hcard4 : ({a, b, c, d_v} : Set S).ncard ≤ 4 := by
    have h1 := ncard_insert_le a ({b, c, d_v} : Set S)
    have h2 := ncard_insert_le b ({c, d_v} : Set S)
    have h3 := ncard_insert_le c ({d_v} : Set S)
    have h4' : ({d_v} : Set S).ncard = 1 := ncard_singleton d_v
    omega
  have hFree4_H₁ : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ θ₁ {a, b, c, d_v} := by
    refine theorem_4_7_proof H (clearedSubdrawing H D_i.Λ)
      θ (3 * beta + 3) T D_i.T₁ d D_i.d₁ (r i) {a, b, c, d_v}
      hS hConn hMetric hri_A (by omega) hFree4 ?_
      D_i.isCleared.hasMetric.1.1 D_i.isRearranged.atom_mem D_i.isRearranged.isCompression
    intro v hv
    have hvC : v ∈ C.V := by rcases hv with rfl | rfl | rfl | rfl <;> assumption
    have hd_v := hC_vert_dist v hvC
    omega
  have hFree4_H' : IsFreeSet H'.toHypergraph T' θ₁ {a, b, c, d_v} :=
    isFreeSet_inducedTangle_of_isFreeSet hSub hT₁_tangle hInd (by omega) hFree4_H₁
  have h_ne_v34 : ∀ u ∈ C.V, ∀ idx : Fin (2 * k_34),
      D_i.clearedEmbedding.vMap u ≠ D_i.clearedEmbedding.vMap (v_34 idx) := by
    intro u huC idx hEq
    have huv : u = v_34 idx :=
      D_i.clearedEmbedding.bijOn_v.injOn (hCV_H₁ u huC).1 (hv34_mem idx).1 hEq
    have hd1 := hC_vert_dist u huC
    have hd2 := D_i.isZone.dist_le {v_34 idx}
      (Or.inl (Or.inl ⟨v_34 idx, hSub_cleared.1 (hv34_mem idx).1, rfl⟩))
      (by rw [singleton_subset_iff]; exact (hv34_mem idx).2.1)
    rw [huv] at hd1
    omega
  have hPath_to_H' : ∀ {P₀ : Graph α β} {u₀ w₀ : S},
      u₀ ∈ C.V → w₀ ∈ C.V →
      IsHPathWithEnds G η.imageGraph P₀ (η.vMap u₀) (η.vMap w₀) →
      IsHPathWithEnds G η'.imageGraph P₀ (η'.vMap u₀) (η'.vMap w₀) := by
    intro P₀ u₀ w₀ hu₀C hw₀C hP₀
    have hu₀_eq : η'.vMap u₀ = D_i.clearedEmbedding.vMap u₀ := hvMap u₀ (hCV_H₁ u₀ hu₀C).1
    have hw₀_eq : η'.vMap w₀ = D_i.clearedEmbedding.vMap w₀ := hvMap w₀ (hCV_H₁ w₀ hw₀C).1
    have hu₀_Λ : D_i.clearedEmbedding.vMap u₀ = η.vMap u₀ := (hCV_H₁ u₀ hu₀C).2
    have hw₀_Λ : D_i.clearedEmbedding.vMap w₀ = η.vMap w₀ := (hCV_H₁ w₀ hw₀C).2
    have hP₀_H₁ : IsHPathWithEnds G D_i.clearedEmbedding.imageGraph P₀
        (D_i.clearedEmbedding.vMap u₀) (D_i.clearedEmbedding.vMap w₀) := by
      refine ⟨D_i.clearedEmbedding.imageGraph_le, hu₀_Λ.symm ▸ hw₀_Λ.symm ▸ hP₀.2.1,
        by rw [hu₀_Λ, hw₀_Λ]; exact hP₀.2.2.1,
        D_i.clearedEmbedding.bijOn_v.mapsTo (hCV_H₁ u₀ hu₀C).1,
        D_i.clearedEmbedding.bijOn_v.mapsTo (hCV_H₁ w₀ hw₀C).1, ?_, ?_⟩
      · apply subset_antisymm
        · intro x ⟨hxP, hx₁⟩
          have hx_pair : x ∈ ({η.vMap u₀, η.vMap w₀} : Set α) :=
            hP₀.2.2.2.2.2.1 ▸ ⟨hxP, hImg_sub_V hx₁⟩
          rwa [← hu₀_Λ, ← hw₀_Λ] at hx_pair
        · rintro x (rfl | rfl)
          · exact ⟨hu₀_Λ ▸ hP₀.2.1.left_mem, D_i.clearedEmbedding.bijOn_v.mapsTo (hCV_H₁ u₀ hu₀C).1⟩
          · exact ⟨hw₀_Λ ▸ hP₀.2.1.right_mem, D_i.clearedEmbedding.bijOn_v.mapsTo
              (hCV_H₁ w₀ hw₀C).1⟩
      · exact hP₀.2.2.2.2.2.2.mono_right hImg_sub_E
    rw [hImg, hu₀_eq, hw₀_eq]
    refine isHPathWithEnds_subgraphUnion_of_disjoint D_i.clearedEmbedding.imageGraph_le hSub_le_mem
      hP₀_H₁ ?_
    intro m
    by_contra hnot_disj
    have hne_inter : (V(P₀) ∩ V(P_sub m)).Nonempty :=
      Set.not_disjoint_iff_nonempty_inter.mp hnot_disj
    obtain ⟨i₁, i₂, _, _, hPm_path⟩ := hP_sub_paths m
    have hdisj_ends : Disjoint ({D_i.clearedEmbedding.vMap u₀, D_i.clearedEmbedding.vMap w₀} : Set
      α)
        {D_i.clearedEmbedding.vMap (v_34 i₁), D_i.clearedEmbedding.vMap (v_34 i₂)} := by
      refine Set.disjoint_left.mpr ?_
      intro x hx₁ hx₂
      simp only [mem_insert_iff, mem_singleton_iff] at hx₁ hx₂
      rcases hx₁ with rfl | rfl <;> rcases hx₂ with hEq | hEq
      · exact h_ne_v34 u₀ hu₀C i₁ hEq
      · exact h_ne_v34 u₀ hu₀C i₂ hEq
      · exact h_ne_v34 w₀ hw₀C i₁ hEq
      · exact h_ne_v34 w₀ hw₀C i₂ hEq
    obtain ⟨P_join, hP_join, _, _⟩ :=
      exists_isHPathWithEnds_of_inter_nonempty hP₀_H₁ hPm_path hdisj_ends hne_inter
    have hu₀_A : ({u₀} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u₀, hC_sub.1 hu₀C, rfl⟩)
    have hv₂_A : ({v_34 i₂} : Set S) ∈ H.A :=
      Or.inl (Or.inl ⟨v_34 i₂, hSub_cleared.1 (hv34_mem i₂).1, rfl⟩)
    have hd_ri_u₀ : θ - 1 ≤ d (r i) {u₀} := hC_vert_dist u₀ hu₀C
    have hd_ri_v₂ : d (r i) {v_34 i₂} ≤ 3 * beta + 3 :=
      D_i.isZone.dist_le {v_34 i₂} hv₂_A
        (by rw [singleton_subset_iff]; exact (hv34_mem i₂).2.1)
    have htri_u₀_v₂ := hd_tri (r i) hri_A {v_34 i₂} hv₂_A {u₀} hu₀_A
    have hsymm_u₀_v₂ := hd_symm {v_34 i₂} hv₂_A {u₀} hu₀_A
    have hcomp_val : d {u₀} {v_34 i₂} ≤ D_i.d₁ {u₀} {v_34 i₂} + (4 * (3 * beta + 3) + 2) := by
      have hcomp := D_i.isRearranged.isCompression.dist_le u₀ (v_34 i₂)
      rwa [pointDist_eq_of_mem_atom (d := d) hu₀_A hv₂_A (mem_singleton _) (mem_singleton _),
        pointDist_eq_of_mem_atom (d := D_i.d₁)
          (Or.inl (Or.inl ⟨u₀, (hCV_H₁ u₀ hu₀C).1, rfl⟩))
          (Or.inl (Or.inl ⟨v_34 i₂, (hv34_mem i₂).1, rfl⟩))
          (mem_singleton _) (mem_singleton _)] at hcomp
    have hStep_Λ : IsMuSteppedSpan G (clearedSubdrawing H D_i.Λ) D_i.clearedEmbedding D_i.d₁ μ :=
      ⟨P_join, u₀, v_34 i₂, (hCV_H₁ u₀ hu₀C).1, (hv34_mem i₂).1, hP_join, by omega⟩
    exact hFlat_beta.no_stepped_rearrangement D_i.isRearranged hStep_Λ
  exact ⟨hrj_R', C, a, b, c, d_v, P₁, P₂, hC_circ, hC_sub_H', hC_U,
    haC, hbC, hcC, hdvC, hnodup4, hord4, hFree4_H', hdisj_P₁₂,
    hPath_to_H' haC hcC hP₁, hPath_to_H' hbC hdvC hP₂⟩

private theorem section7S1_of_split_eyes
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (θ' : ℕ)
    (lam : ℕ)
    (lam' : ℕ)
    (π : ℕ)
    (beta : ℕ)
    (μ : ℕ)
    (τ₂ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (r : Fin k → Set S)
    (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S)
    (α₀_pt : α → S)
    (i : Fin k)
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β))
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hμ2 : 2 ≤ μ)
    (hlam'4 : 4 ≤ lam')
    (hθ'_ge : 4 * lam' + μ + 2 ≤ θ')
    (hτ₂_eq : τ₂ = 6 + θ' / 2)
    (hlam_ge : 6 * (3 * beta + 3) + 5 * lam' + 3 * μ + 4 ≤ lam)
    (hbeta_ge : θ' + 13 * μ + 14 ≤ beta)
    (hθ_ge : 100 * beta ≤ θ)
    (hr_eye : ∀ (j : Fin k), IsDrawingEye G H η θ T (r j))
    (hr_dist : ∀ (j₁ j₂ : Fin k), j₁ ≠ j₂ → d (r j₁) (r j₂) = θ)
    (hCardτ₂ : P.ncard = τ₂)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hd_tri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hτ₂_ge12 : 12 ≤ τ₂)
    :
    let k_34 : ℕ := τ₂ - 3
    (3 ≤ k_34) →
    ∀ (H' : Drawing S),
    ∀ (η' : SpanEmbedding H' G),
    ∀ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    ∀ (d' : Set S → Set S → ℕ),
    ∀ (r₁ : Set S),
    ∀ (r₂ : Set S),
    (HasTangleMetric H' (θ - (4 * (3 * beta + 3) + 2)) T' d') →
    (r₁ ∈ H'.R) →
    (r₂ ∈ H'.R) →
    (r₁ ⊆ D_i.Λ) →
    (r₂ ⊆ D_i.Λ) →
    (IsRearrangedWithin G H H' η η' θ_star θ (3 * beta + 3) T_star T T' d d' (r i)) →
    (θ' ≤ d' r₁ r₂) →
    let θ₁ : ℕ := θ - (4 * (3 * beta + 3) + 2)
    (IsDrawingEye G H' η' θ₁ T' r₁) →
    (IsDrawingEye G H' η' θ₁ T' r₂) →
    ((clearedSubdrawing H D_i.Λ).IsSubdrawing H) →
    (∀ (j : Fin k), j ≠ i → IsDrawingEye G H' η' θ₁ T' (r j)) →
    Section7S1 S G θ_star T_star k μ lam' θ' := by
  intro k_34 hk_34_ge H' η' T' d' r₁ r₂ hM' hr₁_R hr₂_R hr₁_sub hr₂_sub hRearr' hdist_r₁r₂_θ' θ₁
    hr₁_eye hr₂_eye hSub_cleared hr_other_eye
  obtain ⟨_, hd'_refl, _, hd'_symm, _, _⟩ := gm11_theorem_9_1 H' θ₁ T' d' hS hConn hM'
  have hdist_new_other : ∀ {r_new : Set S}, r_new ∈ H'.R → r_new ⊆ D_i.Λ →
      ∀ j : Fin k, j ≠ i → θ' ≤ d' r_new (r j) := by
    intro r_new hr_new hsub_Λ j hj_ne
    obtain ⟨σ₁, hσ₁⟩ := (hM'.1.1.2 r_new hr_new).isPathConnected.nonempty
    obtain ⟨σ₂, hσ₂⟩ := (hMetric.1.1.2 (r j) (hr_eye j).1).isPathConnected.nonempty
    obtain ⟨a₁, ha₁, hσ₁_a₁⟩ := exists_atom_of_point H σ₁
    have ha₁_sub_Λ : a₁ ⊆ D_i.Λ :=
      atom_subset_of_isSubdrawing hSub_cleared ha₁ (Or.inr D_i.mem_R_cleared) hσ₁_a₁ (hsub_Λ hσ₁)
    have hd_ri_a₁ : d (r i) a₁ ≤ 3 * beta + 3 :=
      D_i.isZone.dist_le a₁ ha₁ (ha₁_sub_Λ.trans subset_closure)
    have hd_ri_rj : d (r i) (r j) = θ := hr_dist i j hj_ne.symm
    have htri := hd_tri (r i) (Or.inr (hr_eye i).1) a₁ ha₁ (r j) (Or.inr (hr_eye j).1)
    have hrj_R' : r j ∈ H'.R := (hr_other_eye j hj_ne).1
    have hcomp_val : d a₁ (r j) ≤ d' r_new (r j) + (4 * (3 * beta + 3) + 2) := by
      have hcomp := hRearr'.isCompression.dist_le σ₁ σ₂
      rwa [pointDist_eq_of_mem_atom (d := d) ha₁ (Or.inr (hr_eye j).1) hσ₁_a₁ hσ₂,
        pointDist_eq_of_mem_atom (d := d') (Or.inr hr_new) (Or.inr hrj_R') hσ₁ hσ₂] at hcomp
    omega
  have hdist_other_other : ∀ j₁ j₂ : Fin k, j₁ ≠ i → j₂ ≠ i → j₁ ≠ j₂ →
      θ' ≤ d' (r j₁) (r j₂) := by
    intro j₁ j₂ hj₁ hj₂ hj₁₂
    obtain ⟨σ₁, hσ₁⟩ := (hMetric.1.1.2 (r j₁) (hr_eye j₁).1).isPathConnected.nonempty
    obtain ⟨σ₂, hσ₂⟩ := (hMetric.1.1.2 (r j₂) (hr_eye j₂).1).isPathConnected.nonempty
    have hd_j₁j₂ : d (r j₁) (r j₂) = θ := hr_dist j₁ j₂ hj₁₂
    have hrj₁_R' : r j₁ ∈ H'.R := (hr_other_eye j₁ hj₁).1
    have hrj₂_R' : r j₂ ∈ H'.R := (hr_other_eye j₂ hj₂).1
    have hcomp_val : d (r j₁) (r j₂) ≤ d' (r j₁) (r j₂) + (4 * (3 * beta + 3) + 2) := by
      have hcomp := hRearr'.isCompression.dist_le σ₁ σ₂
      rwa [pointDist_eq_of_mem_atom (d := d) (Or.inr (hr_eye j₁).1) (Or.inr (hr_eye j₂).1) hσ₁ hσ₂,
        pointDist_eq_of_mem_atom (d := d') (Or.inr hrj₁_R') (Or.inr hrj₂_R') hσ₁ hσ₂] at hcomp
    omega
  -- Claim (7): `H', η', T'` is `(lam', μ)`-flat.
  have hFlat' : IsFlatSpan G H' η' θ_star θ₁ lam' μ T_star T' :=
    theorem_5_2_proof G H H' η η' θ_star θ lam (3 * beta + 3) lam' μ
      T_star T T' d d' (r i) hFlat (by omega) (by omega) hlam'4 hlam_ge hRearr'
  -- Assemble the `k + 1` eyes `r'` of `H', η', T'` at distance `≥ θ'` and apply (7.1).
  let r' : Fin (k + 1) → Set S := fun m =>
    if hm : m.1 < k then
      if m.1 = i.1 then r₁ else r ⟨m.1, hm⟩
    else r₂
  have hr'_eye : ∀ m : Fin (k + 1), IsDrawingEye G H' η' θ₁ T' (r' m) := by
    intro m
    dsimp only [r']
    split_ifs with hm hmi
    · exact hr₁_eye
    · exact hr_other_eye ⟨m.1, hm⟩ (fun h => hmi (congrArg Fin.val h))
    · exact hr₂_eye
  have hr'_dist : ∀ m₁ m₂ : Fin (k + 1), m₁ ≠ m₂ → θ' ≤ d' (r' m₁) (r' m₂) := by
    intro m₁ m₂ hm_ne
    have hm_val_ne : m₁.1 ≠ m₂.1 := fun h => hm_ne (Fin.ext h)
    by_cases hm₁ : m₁.1 < k
    · by_cases hmi₁ : m₁.1 = i.1
      · by_cases hm₂ : m₂.1 < k
        · have hmi₂ : m₂.1 ≠ i.1 := by omega
          simp only [r', hmi₁, hm₂, hmi₂, i.isLt, ↓reduceDIte, ↓reduceIte]
          exact hdist_new_other hr₁_R hr₁_sub ⟨m₂.1, hm₂⟩ (fun h => hmi₂ (congrArg Fin.val h))
        · simp only [r', hmi₁, hm₂, i.isLt, ↓reduceDIte, ↓reduceIte]
          exact hdist_r₁r₂_θ'
      · by_cases hm₂ : m₂.1 < k
        · by_cases hmi₂ : m₂.1 = i.1
          · simp only [r', hm₁, hmi₁, hmi₂, i.isLt, ↓reduceDIte, ↓reduceIte]
            rw [hd'_symm (r ⟨m₁.1, hm₁⟩) (Or.inr (hr_other_eye ⟨m₁.1, hm₁⟩
              (fun h => hmi₁ (congrArg Fin.val h))).1) r₁ (Or.inr hr₁_R)]
            exact hdist_new_other hr₁_R hr₁_sub ⟨m₁.1, hm₁⟩ (fun h => hmi₁ (congrArg Fin.val h))
          · simp only [r', hm₁, hmi₁, hm₂, hmi₂, ↓reduceDIte, ↓reduceIte]
            exact hdist_other_other ⟨m₁.1, hm₁⟩ ⟨m₂.1, hm₂⟩
              (fun h => hmi₁ (congrArg Fin.val h)) (fun h => hmi₂ (congrArg Fin.val h))
              (fun h => hm_val_ne (Fin.mk.inj h))
        · simp only [r', hm₁, hmi₁, hm₂, ↓reduceDIte, ↓reduceIte]
          rw [hd'_symm (r ⟨m₁.1, hm₁⟩) (Or.inr (hr_other_eye ⟨m₁.1, hm₁⟩
            (fun h => hmi₁ (congrArg Fin.val h))).1) r₂ (Or.inr hr₂_R)]
          exact hdist_new_other hr₂_R hr₂_sub ⟨m₁.1, hm₁⟩ (fun h => hmi₁ (congrArg Fin.val h))
    · have hm₂ : m₂.1 < k := by omega
      by_cases hmi₂ : m₂.1 = i.1
      · simp only [r', hm₁, hmi₂, i.isLt, ↓reduceDIte, ↓reduceIte]
        rw [hd'_symm r₂ (Or.inr hr₂_R) r₁ (Or.inr hr₁_R)]
        exact hdist_r₁r₂_θ'
      · simp only [r', hm₁, hm₂, hmi₂, ↓reduceDIte, ↓reduceIte]
        exact hdist_new_other hr₂_R hr₂_sub ⟨m₂.1, hm₂⟩ (fun h => hmi₂ (congrArg Fin.val h))
  have hr'_inj : Injective r' := by
    intro m₁ m₂ hEq
    by_contra hm_ne
    have hge := hr'_dist m₁ m₂ hm_ne
    rw [hEq, hd'_refl (r' m₂) (Or.inr (hr'_eye m₂).1)] at hge
    omega
  exact theorem_7_1_proof G H' η' θ_star θ₁ θ' lam' μ (k + 1) T_star T' d'
    hFlat' hM' (by omega) hθ'_ge (by omega) (by omega) ⟨r', hr'_inj, hr'_eye, hr'_dist⟩

/-- Graph Minors XV, (7.11), page 143: use the established (3.4) in the transaction argument. -/
theorem theorem_7_11_proof : GM15Theorem711Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ θ' lam lam' π beta μ τ₂ k T_star T d r
    S₀ α₀_disc α₀_pt i D_i P X
    hFlat hMetric hμ2 hlam'4 hθ'_ge hθ'_even hτ₂_eq hlam_ge hbeta_ge hθ_ge
    hr_inj hr_eye hr_dist hTransP hPathsP hX_sub hEndsP hFreeX hCardτ₂ hDouble
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  obtain ⟨_, hd_refl, hd_le_θ, hd_symm, hd_tri, hd_inc⟩ :=
    gm11_theorem_9_1 H θ T d hS hConn hMetric
  rcases hDouble with ⟨A_f, B_f, _, p, _, P_idx, a_idx, b_idx, hP_inj, hP_range, hEnds_idx, hcw⟩
  have hp_eq : p = τ₂ := by
    rw [← hCardτ₂, ← hP_range, Set.ncard_range_of_injective hP_inj, Nat.card_fin]
  subst p
  have hτ₂_ge12 : 12 ≤ τ₂ := by omega
  obtain ⟨inv_v, hinv_v, hNat⟩ := D_i.soc_Λ_natural
  have hinv_mem_X : ∀ x ∈ D_i.clearedSociety.transactionEnds P,
      inv_v x ∈ X ∧ D_i.clearedEmbedding.vMap (inv_v x) = x := by
    intro x hx
    have hx_img : x ∈ D_i.clearedEmbedding.vMap '' X := hEndsP ▸ hx
    obtain ⟨y, hyX, hyx⟩ := hx_img
    rcases hx with ⟨P₀, hP₀, z, hPath⟩
    obtain ⟨hinv_mem, hinv_eq⟩ := hinv_v x hPath.2.2.1
    have hy_eq : inv_v x = y :=
      D_i.clearedEmbedding.bijOn_v.injOn hinv_mem.1 (hX_sub hyX).1 (hinv_eq.trans hyx.symm)
    exact ⟨hy_eq ▸ hyX, hinv_eq⟩
  obtain ⟨w_α, hNodup_w, hOrder_w, hw_α_ab, hw_α_lt, hw_α_m2, hw_α_m1,
      hw_α_mid, hw_α_last4, hw_α_last3, hw_α_last2, hw_α_last1⟩ :=
    exists_doublecross_rotated_seq hτ₂_ge12 a_idx b_idx hinv_v hNat hcw
  let w : Fin (2 * τ₂) → S := inv_v ∘ w_α
  have hw_α_ends : ∀ m : Fin (2 * τ₂), w_α m ∈ D_i.clearedSociety.transactionEnds P := by
    intro m
    rcases hw_α_ab m with ⟨idx, hEq⟩ | ⟨idx, hEq⟩
    · rw [hEq]
      exact ⟨P_idx idx, hP_range ▸ mem_range_self idx, b_idx idx, (hEnds_idx idx).2.2⟩
    · rw [hEq]
      have hP_idx := (hEnds_idx idx).2.2
      exact ⟨P_idx idx, hP_range ▸ mem_range_self idx, a_idx idx,
        ⟨hP_idx.1.symm, hP_idx.2.1.symm, hP_idx.2.2.2, hP_idx.2.2.1⟩⟩
  have hw_mem : ∀ m : Fin (2 * τ₂), w m ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ :=
    fun m => hX_sub (hinv_mem_X (w_α m) (hw_α_ends m)).1
  have hw_vMap : ∀ m : Fin (2 * τ₂), D_i.clearedEmbedding.vMap (w m) = w_α m :=
    fun m => (hinv_mem_X (w_α m) (hw_α_ends m)).2
  -- Now set up the `2 * k_34` vertices `v_34` and `k_34 - 1` paths `P_sub` for (3.4) with `k_34 =
  -- τ₂ - 3`.
  let k_34 : ℕ := τ₂ - 3
  have hk_34_ge : 3 ≤ k_34 := by omega
  let f_34 : Fin (2 * k_34) → Fin (2 * τ₂) := fun j =>
    if hj1 : j.1 < k_34 then ⟨j.1, by omega⟩
    else if hj2 : j.1 < 2 * k_34 - 1 then ⟨j.1 + 3, by omega⟩
    else ⟨2 * τ₂ - 4, by omega⟩
  have hf_34_mono : StrictMono f_34 := by
    intro j₁ j₂ hj
    change (f_34 j₁).1 < (f_34 j₂).1
    dsimp only [f_34]
    split_ifs <;> dsimp <;> omega
  let v_34 : Fin (2 * k_34) → S := w ∘ f_34
  have hNodup_v34 : (List.ofFn v_34).Nodup := by
    rw [List.nodup_ofFn]
    exact (List.nodup_ofFn.mp hNodup_w).comp hf_34_mono.injective
  have hOrder_v34 : GM12.IsListedInOrderOn (subBd D_i.Λ) (List.ofFn v_34) :=
    isListedInOrderOn_of_strictMono (by omega) hf_34_mono hOrder_w
  have hv34_mem : ∀ j : Fin (2 * k_34), v_34 j ∈ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ :=
    fun j => hw_mem (f_34 j)
  have hv34_free : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁
      (θ - 4 * (3 * beta + 3) - 2) (range v_34) := by
    refine hFreeX.subset D_i.isCleared.hasMetric.1.2.1 ?_
    rintro _ ⟨j, rfl⟩
    exact (hinv_mem_X (w_α (f_34 j)) (hw_α_ends (f_34 j))).1
  let P_sub : Fin (k_34 - 1) → Graph α β := fun j => P_idx ⟨τ₂ - 3 - j.1, by omega⟩
  have hP_sub_paths : ∀ j : Fin (k_34 - 1), ∃ i₁ i₂ : Fin (2 * k_34),
      i₁.1 = j.1 ∧ i₂.1 = 2 * k_34 - 2 - j.1 ∧
      IsHPathWithEnds G D_i.clearedEmbedding.imageGraph (P_sub j)
        (D_i.clearedEmbedding.vMap (v_34 i₁)) (D_i.clearedEmbedding.vMap (v_34 i₂)) := by
    intro j
    let i₁ : Fin (2 * k_34) := ⟨j.1, by omega⟩
    let i₂ : Fin (2 * k_34) := ⟨2 * k_34 - 2 - j.1, by omega⟩
    refine ⟨i₁, i₂, rfl, rfl, ?_⟩
    change IsHPathWithEnds G D_i.clearedEmbedding.imageGraph (P_sub j)
      (D_i.clearedEmbedding.vMap (w (f_34 i₁))) (D_i.clearedEmbedding.vMap (w (f_34 i₂)))
    rw [hw_vMap (f_34 i₁), hw_vMap (f_34 i₂)]
    have hf_i₁ : f_34 i₁ = ⟨j.1, by omega⟩ := by
      dsimp only [f_34, i₁]; rw [dite_eq_left (by omega)]
    have hf_i₂ : f_34 i₂ = ⟨2 * k_34 - 2 - j.1 + 3, by omega⟩ := by
      dsimp only [f_34, i₂]; rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    have hi₁_eq : w_α (f_34 i₁) = a_idx ⟨τ₂ - 3 - j.1, by omega⟩ := by
      rw [hf_i₁, hw_α_lt ⟨j.1, by omega⟩ (by dsimp; omega)]
    have hi₂_eq : w_α (f_34 i₂) = b_idx ⟨τ₂ - 3 - j.1, by omega⟩ := by
      rw [hf_i₂, hw_α_mid ⟨2 * k_34 - 2 - j.1 + 3, by omega⟩ (by dsimp; omega) (by dsimp; omega)]
      congr 1; ext; dsimp; omega
    rw [hi₁_eq, hi₂_eq]
    exact hPathsP (P_sub j) (hP_range ▸ mem_range_self _) _ _ (hEnds_idx _).2.2
  have hP_sub_disj : Pairwise (fun j₁ j₂ => Disjoint V(P_sub j₁) V(P_sub j₂)) := by
    intro j₁ j₂ hj
    rcases hTransP with ⟨_, _, ⟨_, hDisjP⟩, _, _⟩
    refine hDisjP (hP_range ▸ mem_range_self _) (hP_range ▸ mem_range_self _) (fun hEq => hj ?_)
    have hidx := congrArg Fin.val (hP_inj hEq)
    dsimp only at hidx
    ext; omega
  let i_k : Fin (2 * k_34) := ⟨k_34 - 1, by omega⟩
  let i_last : Fin (2 * k_34) := ⟨2 * k_34 - 1, by omega⟩
  have hEq_θ₁ : θ - 4 * (3 * beta + 3) - 2 = θ - (4 * (3 * beta + 3) + 2) := by omega
  have hSpan_Λ : IsSigmaSpan G (clearedSubdrawing H D_i.Λ) D_i.clearedEmbedding θ_star
      (θ - 4 * (3 * beta + 3) - 2) T_star D_i.T₁ := hEq_θ₁ ▸ D_i.isRearranged.isSpan'
  have hM_Λ : HasTangleMetric (clearedSubdrawing H D_i.Λ)
      (θ - 4 * (3 * beta + 3) - 2) D_i.T₁ D_i.d₁ :=
    hEq_θ₁ ▸ D_i.isRearranged.isCompression.hasMetric'
  obtain ⟨H', η', T', d', r₁, r₂, hSpan', hM', hr₁_R, hr₂_R, hr₁_sub, hr₂_sub, _,
      hU_diff, hSub, hvMap, heMap, hImg, hInd, _, hOArc_r₁, hOArc_r₂, hCirc_r₁, hCirc_r₂,
      _, _, hOrd_r₁, hOrd_r₂, hdist_r₁r₂, _⟩ :=
    GraphMinor.GM15.theorem_3_4_drawn.{u, v, w} G (clearedSubdrawing H D_i.Λ) D_i.clearedEmbedding
      θ_star
      (θ - 4 * (3 * beta + 3) - 2) k_34
      T_star D_i.T₁ D_i.d₁ D_i.Λ v_34 P_sub i_k i_last
      hSpan_Λ hM_Λ D_i.mem_R_cleared D_i.isZone.isOArc_bd D_i.isCircuit_bd
      hk_34_ge hNodup_v34 hOrder_v34 hv34_mem hv34_free hP_sub_paths hP_sub_disj rfl rfl
  rw [hEq_θ₁] at hSpan' hM' hInd
  -- Claim (1): `H', η', T'` is obtained from `H, η, T` by rearranging within `3 * beta + 3` of `r
  -- i`,
  -- and `d' r₁ r₂ ≥ θ'`.
  have hRearr' : IsRearrangedWithin G H H' η η' θ_star θ (3 * beta + 3) T_star T T' d d' (r i) :=
    isRearrangedWithin_of_cleared_extension D_i hSpan' hM' hU_diff hSub hvMap heMap hInd
      (by omega)
  have hdist_r₁r₂_θ' : θ' ≤ d' r₁ r₂ := by
    change 2 * (τ₂ - 3) - 6 ≤ d' r₁ r₂ at hdist_r₁r₂
    have h2 : 2 * (θ' / 2) = θ' := Nat.mul_div_cancel' (even_iff_two_dvd.mp hθ'_even)
    omega
  have hSub_le_mem : ∀ Q ∈ range P_sub, Q ≤ G := by
    rintro _ ⟨j, rfl⟩
    exact (hP_sub_paths j).choose_spec.choose_spec.2.2.2.1.le
  -- Claim (2): `r₁` and `r₂` are eyes of `G, H', η', θ₁, T'`.
  let θ₁ := θ - (4 * (3 * beta + 3) + 2)
  have hT₁_tangle : IsTangle (clearedSubdrawing H D_i.Λ).toHypergraph θ₁ D_i.T₁ := by
    change IsTangle _ (θ - (4 * (3 * beta + 3) + 2)) _
    rw [← hEq_θ₁]
    exact D_i.isCleared.hasMetric.1.2.1
  have hFreeX_θ₁ : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ θ₁ X := by
    change IsFreeSet _ _ (θ - (4 * (3 * beta + 3) + 2)) _
    rw [← hEq_θ₁]
    exact hFreeX
  have hFreeX_T' : IsFreeSet H'.toHypergraph T' θ₁ X :=
    isFreeSet_inducedTangle_of_isFreeSet hSub hT₁_tangle hInd (by omega) hFreeX_θ₁
  have hcl_bd_r₁ : IsClosed (subBd r₁) := isClosed_closure.inter isClosed_closure
  have hcl_bd_r₂ : IsClosed (subBd r₂) := isClosed_closure.inter isClosed_closure
  have hr₁_eye : IsDrawingEye G H' η' θ₁ T' r₁ := by
    exact first_split_region_is_eye (S := S) (α := α) (β := β) G H η θ_star θ θ' π beta μ
      τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X hτ₂_eq hTransP
      hPathsP hCardτ₂ A_f B_f P_idx a_idx b_idx hP_inj hP_range hEnds_idx hτ₂_ge12 inv_v
      hinv_mem_X w_α hNodup_w hOrder_w hw_α_lt hw_α_m2 hw_α_m1 hw_α_ends hw_mem hw_vMap
      hk_34_ge H' η' T' d' r₁ r₂ hM' hr₁_R hvMap hImg hOArc_r₁ hCirc_r₁ hOrd_r₁
      hSub_le_mem hFreeX_T' hcl_bd_r₁
  have hr₂_eye : IsDrawingEye G H' η' θ₁ T' r₂ := by
    exact last_split_region_is_eye (S := S) (α := α) (β := β) G H η θ_star θ θ' π beta μ
      τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X hτ₂_eq hTransP
      hPathsP hCardτ₂ A_f B_f P_idx a_idx b_idx hP_inj hP_range hEnds_idx hτ₂_ge12 inv_v
      hinv_mem_X w_α hNodup_w hOrder_w hw_α_last4 hw_α_last3 hw_α_last2 hw_α_last1 hw_α_ends
      hw_mem hw_vMap hk_34_ge H' η' T' d' r₁ r₂ hM' hr₂_R hvMap hImg hOArc_r₂
      hCirc_r₂ hOrd_r₂ hSub_le_mem hFreeX_T' hcl_bd_r₂
  -- Claims (3) and (4): for `j ≠ i`, `r j` is an eye of `G, H', η', θ₁, T'`.
  have hFlat_beta : IsFlatSpan G H η θ_star θ (3 * beta + 3) μ T_star T := by
    have hTrunc_eq : GM10.truncation T θ = T := by
      ext ⟨A, B⟩
      exact ⟨fun h => h.1, fun h => ⟨h, hFlat.isSpan.isControlling.isTangle_H.order_lt h⟩⟩
    have hord := hFlat.order_ge
    have h := theorem_5_1_proof G H η θ_star θ θ lam (3 * beta + 3) μ μ T_star T
      hFlat (by omega) le_rfl (by omega) le_rfl (by omega) (fun _ => by omega) (by omega)
    rwa [hTrunc_eq] at h
  have hSub_cleared : (clearedSubdrawing H D_i.Λ).IsSubdrawing H :=
    clearedSubdrawing_isSubdrawing H D_i.Λ
  have hImg_sub_V : V(D_i.clearedEmbedding.imageGraph) ⊆ V(η.imageGraph) := by
    rw [← D_i.clearedEmbedding.bijOn_v.image_eq, ← η.bijOn_v.image_eq]
    rintro _ ⟨x, hx₁, rfl⟩
    exact ⟨x, hSub_cleared.1 hx₁, (D_i.vMap_eq x hx₁).symm⟩
  have hImg_sub_E : E(D_i.clearedEmbedding.imageGraph) ⊆ E(η.imageGraph) := by
    rw [← D_i.clearedEmbedding.bijOn_e.image_eq, ← η.bijOn_e.image_eq]
    rintro _ ⟨e, he₁, rfl⟩
    exact ⟨e, hSub_cleared.2 he₁, (D_i.eMap_eq e he₁).symm⟩
  have hE_ne : H.E.Nonempty := edges_nonempty_of_tangle hS hMetric.1 (by omega)
  have hr_other_eye : ∀ j : Fin k, j ≠ i → IsDrawingEye G H' η' θ₁ T' (r j) := by
    exact other_eye_survives_split (S := S) (α := α) (β := β) G H η θ_star θ θ' lam' π beta μ
      τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P hMetric hμ2 hlam'4 hθ'_ge hτ₂_eq hbeta_ge hθ_ge
      hr_eye hr_dist hCardτ₂ hS hd_symm hd_tri hd_inc hτ₂_ge12 hk_34_ge v_34
      hv34_mem P_sub hP_sub_paths H' η' T' d' r₁ r₂ hSub hvMap hImg hInd hRearr' hSub_le_mem
      hT₁_tangle hFlat_beta hSub_cleared hImg_sub_V hImg_sub_E hE_ne
  -- Claims (5) and (6): distances in `d'` between `r₁, r₂` and `r j` (`j ≠ i`), and between
  -- `r j₁, r j₂` (`j₁ ≠ j₂`, `j₁, j₂ ≠ i`), are all `≥ θ'`.
  have finished_eyes : Section7S1 S G θ_star T_star k μ lam' θ' := by
    exact section7S1_of_split_eyes (S := S) (α := α) (β := β) G H η θ_star θ θ' lam lam' π beta μ
      τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P hFlat hMetric hμ2 hlam'4 hθ'_ge hτ₂_eq hlam_ge
      hbeta_ge hθ_ge hr_eye hr_dist hCardτ₂ hS hd_tri hτ₂_ge12 hk_34_ge H' η' T' d'
      r₁ r₂ hM' hr₁_R hr₂_R hr₁_sub hr₂_sub hRearr' hdist_r₁r₂_θ' hr₁_eye hr₂_eye hSub_cleared
      hr_other_eye
  exact finished_eyes

/-- **Graph Minors XV, (7.11)** (pages 143–145):
"If $\mathscr{P}$ is a doublecross transaction of cardinality $\tau_2$ then (S1) holds."
Proved from `(3.4)`, `(4.7)`, `(5.1)`, `(5.2)`, and `(7.1)`. -/
theorem Section7.theorem_7_11_proof
     :
    GM15Theorem711Statement.{u, v, w} := by
  have h34 : GM15Theorem34Statement.{u, v, w} := theorem_3_4_proof
  intro S _ _ α β G H η θ_star θ θ' lam lam' π beta μ τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X
  exact _root_.GraphMinor.GM15.theorem_7_11_proof
    G H η θ_star θ θ' lam lam' π beta μ τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X

/-! ## Proof of Graph Minors XV, (1.2) -/

/-- Helper lemma: the canonical embedding of `H` into `G₀ = η(H) ∪ J₀` agrees with `η` and is not
`μ`-stepped when `(H, η, T)` is `(λ, μ)`-flat and `1 ≤ μ`
(Graph Minors XV, Section 7, proof of (7.4), page 137). -/
theorem exists_section7G0_embedding
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (hFlat : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (hMetric : HasTangleMetric H θ T d)
    (hμ1 : 1 ≤ μ) :
    ∃ η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r),
      (∀ v ∈ H.V, η₀.vMap v = η.vMap v) ∧
      (∀ e ∈ H.E, η₀.eMap e = η.eMap e) ∧
      ¬ IsMuSteppedSpan (section7G0 G H η d θ' μ r) H η₀ d μ := by
  have hJ0_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ0_le
  have hG0_le : section7G0 G H η d θ' μ r ≤ G := subgraphSUnion_le hPair_le
  have hImg_le : η.imageGraph ≤ section7G0 G H η d θ' μ r :=
    le_subgraphSUnion hPair_le (mem_insert _ _)
  let η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r) :=
    { imageGraph := η.imageGraph
      vMap := η.vMap
      eMap := η.eMap
      imageGraph_le := hImg_le
      bijOn_v := η.bijOn_v
      bijOn_e := η.bijOn_e
      inc_iff := η.inc_iff }
  refine ⟨η₀, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  rintro ⟨P, u, v, hu, hv, ⟨_, hP_path, hne, ha, hb, hVP, hEP⟩, hdist⟩
  have hP_G : IsGraphPathWithEnds G P (η.vMap u) (η.vMap v) :=
    ⟨hP_path.1.trans hG0_le, hP_path.2⟩
  have hStepG : IsMuSteppedSpan G H η d μ :=
    ⟨P, u, v, hu, hv, ⟨η.imageGraph_le, hP_G, hne, ha, hb, hVP, hEP⟩, hdist⟩
  exact not_isMuSteppedSpan_of_isFlatSpan hFlat hMetric (by have := hFlat.order_ge; omega) hStepG

/-- Statement of Graph Minors XV, (1.2) (pages 115–116):
"For any surface $\Sigma$ with $bd(\Sigma) = \emptyset$, and any integers $k \ge 0$, $\phi \ge 8$,
$\mu \ge 12$ and even, $\lambda_{k+1} \ge 4$, and $\theta_{k+1} \ge 4\lambda_{k+1} + \mu + 2$,
there are integers $\rho_k, \lambda_k \ge 0$ and $\theta_k \ge 4\lambda_k + \mu + 2$ such that the
following holds. Let $\mathscr{T}^*$ be a tangle in a graph $G$, and suppose that there is a
$(\lambda_k, \mu)$-flat $\Sigma$-span of order $\ge \theta_k$ with $k$ eyes mutually at distance
$\ge \theta_k$. Then either
(i) there is a $(\lambda_{k+1}, \mu)$-flat $\Sigma$-span of order $\theta_{k+1}$ with $k+1$ eyes,
mutually at distance $\theta_{k+1}$, or ...
(ii) there is a $\Sigma'$-span of order $\phi$, where $\Sigma'$ is a surface obtained by adding a
crosscap to $\Sigma$, or
(iii) there is a $\mathscr{T}^*$-central segregation of $G$ of type $(\rho_k, k)$ with an
arrangement in $\Sigma$." -/
def GM15Theorem12Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (k φ μ lam_next θ_next : ℕ),
      8 ≤ φ → 12 ≤ μ → Even μ → 4 ≤ lam_next →
      4 * lam_next + μ + 2 ≤ θ_next →
      ∃ (p_k lam_k θ_k : ℕ),
        4 * lam_k + μ + 2 ≤ θ_k ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam_k μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ_k ≤ θ₀ →
          HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ_k →
          Section7S1 S G θ_star T_star k μ lam_next θ_next ∨
          Section7S2 S G θ_star T_star φ ∨
          Section7S3 S G T_star p_k k

/-- The eye induction step of XV (1.2) retains the proper arrangement from XV (7.7),
as required in XVI (7.2), page 62. -/
theorem theorem_1_2_proper :
  ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (k φ μ lam_next θ_next : ℕ),
      8 ≤ φ → 12 ≤ μ → Even μ → 4 ≤ lam_next →
      4 * lam_next + μ + 2 ≤ θ_next →
      ∃ (p_k lam_k θ_k : ℕ),
        4 * lam_k + μ + 2 ≤ θ_k ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam_k μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ_k ≤ θ₀ →
          HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ_k →
          Section7S1 S G θ_star T_star k μ lam_next θ_next ∨
          Section7S2 S G θ_star T_star φ ∨
          Section7ProperS3 S G T_star p_k k := by
  have h71 : GM15Theorem71Statement.{u, v, w} :=
    theorem_7_1_proof
  have h75 : GM15Theorem75Statement.{u, v, w} :=
    theorem_7_5_proof
  have h79 : GM15Theorem79Statement.{u, v, w} := Section7.theorem_7_9_proof
  have h710 : GM15Theorem710Statement.{u, v, w} :=
    Section7.theorem_7_10_proof
  have h711 : GM15Theorem711Statement.{u, v, w} :=
    Section7.theorem_7_11_proof
  intro S _ _ _ _ _ k φ μ lam' θ' hφ8 hμ12 hμ_even hlam'4 hθ'_ge
  let θ'' := (eyeInductionParameters φ μ θ').enlargedOrder
  let τ₁ := (eyeInductionParameters φ μ θ').firstThreshold
  let τ₂ := (eyeInductionParameters φ μ θ').secondThreshold
  let π := (eyeInductionParameters φ μ θ').transactionSize
  let beta := (eyeInductionParameters φ μ θ').battlefieldSize
  let θ_k := (eyeInductionParameters φ μ θ').order
  let lam_k := (eyeInductionParameters φ μ θ').flatness
  let p_k := (eyeInductionParameters φ μ θ').segregationWidth
  rcases eye_induction_parameter_bounds hφ8 hμ12 hlam'4 hθ'_ge with
    ⟨hθ''_even, hθ'_le_θ'', h4_θ', h4_θ_k, hθ''_ge, hθ''_gt, hφ2, hφ3, hτ₁_ge, hτ₂_ge,
      hπ2, hπ3, hθ_k_ge, hlam_bound_μ, hθ_bound_μ, hθ''_beta, h16beta, h6beta,
      hφ_le, hbeta_lam, h2τ₁_lt, hlam_bound_beta⟩
  refine ⟨p_k, lam_k, θ_k, hθ_k_ge, ?_⟩
  intro α β G θ_star T_star H₀ η₀ θ₀ T₀ d₀ hFlat₀ hMetric₀ hθ₀_ge hEyes₀
  -- Step 1: Apply (7.1) to obtain a `(lam_k, μ)`-flat `Σ`-span `H, η, T` of order `θ_k` with `k`
  -- eyes `r` mutually at distance `θ_k`.
  obtain ⟨H, η, T, d, r, hFlat, hMetric, hr_inj, hr_eye, hr_dist⟩ :=
    h71 G H₀ η₀ θ_star θ₀ θ_k lam_k μ k T_star T₀ d₀ hFlat₀ hMetric₀
      (by omega) hθ_k_ge h4_θ_k hθ₀_ge hEyes₀
  -- Step 2: Check whether `(S1)` holds for `θ''` (which implies `(S1)` for `θ'` by (7.1)).
  by_cases hS1_θ'' : Section7S1 S G θ_star T_star k μ lam' θ''
  · left
    rcases hS1_θ'' with ⟨H₁, η₁, T₁, d₁, r₁, hFlat₁, hMetric₁, hr₁_inj, hr₁_eye, hr₁_dist⟩
    have hEyes_θ' : HasEyesAtDistance G H₁ η₁ θ'' T₁ d₁ (k + 1) θ' :=
      ⟨r₁, hr₁_inj, hr₁_eye, fun i j hij =>
        hθ'_le_θ''.trans (le_of_eq (hr₁_dist i j hij).symm)⟩
    exact h71 G H₁ η₁ θ_star θ'' θ' lam' μ (k + 1) T_star T₁ d₁ hFlat₁ hMetric₁
      (by omega) hθ'_ge h4_θ' hθ'_le_θ'' hEyes_θ'
  · -- Step 3: Since `(S1)` does not hold for `θ''`, apply (7.4) to obtain `S₀, α₀`.
    obtain ⟨η_G0, hη_G0_v, hη_G0_e, hnot_step_G0⟩ :=
      exists_section7G0_embedding G H η θ_star θ_k θ'' lam_k μ k T_star T d r hFlat hMetric
        (by omega)
    obtain ⟨S₀, α₀_disc, α₀_pt, hThree, hLocal, hArr₀, hCompat₀⟩ :=
      theorem_7_4_proof G H η
        θ_star θ_k θ'' lam_k lam' μ k T_star T d r η_G0
        hFlat hMetric hμ12 hμ_even hlam'4 hθ''_ge hθ''_gt hlam_bound_μ hθ_bound_μ
        hr_inj hr_eye hr_dist hη_G0_v hη_G0_e hnot_step_G0 hS1_θ''
    -- Step 4: Apply (7.5) to obtain the eye data `D i` for `i : Fin k`.
    obtain ⟨D, hDisj_Δ⟩ :=
      h75 G H η θ_star θ_k θ'' lam_k π beta μ k T_star T d r η_G0 S₀ α₀_disc α₀_pt
        hFlat hMetric (by omega) hπ2 hπ3 rfl hθ''_beta h16beta h6beta
        hr_inj hr_eye hr_dist hη_G0_v hη_G0_e hThree hLocal hArr₀ hCompat₀
    -- Step 5: Either no `(G_i*, Ω_i*)` has a crooked transaction of size `π`, or some `i` does.
    by_cases hAllNoCrook :
        ∀ i : Fin k, ∀ P_set : Set (Graph α β),
          (D i).localSociety.IsCrookedTransaction P_set → P_set.ncard ≠ π
    · -- By (7.7), `(S3)` holds.
      right; right
      obtain ⟨𝒮, disc, pt, hCentral, hType, hArr, hDisjoint⟩ :=
        assemble_eye_arrangement G H η θ_star θ_k θ'' lam_k π beta μ k T_star T d r
          η_G0 S₀ α₀_disc α₀_pt D hFlat hMetric (by omega) hπ2 hπ3 rfl hθ''_beta le_rfl
          hr_inj hr_eye hr_dist hη_G0_v hη_G0_e hThree hLocal hArr₀ hCompat₀ hDisj_Δ hAllNoCrook
      exact ⟨𝒮, disc, pt, hCentral, hType,
        GM16.IsSurfaceArrangement.isProper_of_disjoint_boundaries hArr hDisjoint⟩
    · -- Some `i : Fin k` has a crooked transaction `P_star` of cardinality `π`.
      push Not at hAllNoCrook
      rcases hAllNoCrook with ⟨i, P_star, hCrook_star, hCard_star⟩
      -- By (7.8), obtain `P, X` in `(G₀ ∪ J_i, Ω_i)`.
      obtain ⟨P, X, hTransP, hPathsP, hX_sub, hEndsP, hFreeX, hCases⟩ :=
        theorem_7_8_proof G H η θ_star θ_k θ'' π beta μ φ τ₁ τ₂ k T_star T d r
          S₀ α₀_disc α₀_pt i (D i) P_star hφ2 hτ₁_ge hτ₂_ge le_rfl hCrook_star hCard_star
      rcases hCases with ⟨hCardφ, hCross⟩ | ⟨hCardτ₁, hLeap⟩ | ⟨hCardτ₂, hDouble⟩
      · -- Case (i): `P` is a crosscap transaction of size `φ`; by (7.9), `(S2)` holds.
        right; left
        exact h79 G H η θ_star θ_k θ'' π beta μ φ k T_star T d r S₀ α₀_disc α₀_pt i (D i) P X
          hφ3 hφ_le hTransP hPathsP hX_sub hEndsP hFreeX hCardφ hCross
      · -- Case (ii): `P` is a leap transaction of size `τ₁`; impossible by (7.10).
        exfalso
        exact h710 G H η θ_star θ_k θ'' lam_k π beta μ τ₁ k T_star T d r
          S₀ α₀_disc α₀_pt i (D i) P X hFlat hμ12 hμ_even rfl hbeta_lam h2τ₁_lt
          hTransP hPathsP hX_sub hEndsP hFreeX hCardτ₁ hLeap
      · -- Case (iii): `P` is a doublecross transaction of size `τ₂`; by (7.11), `(S1)` holds for
        -- `θ''`.
        exfalso
        exact hS1_θ'' (h711 G H η θ_star θ_k θ'' lam_k lam' π beta μ τ₂ k T_star T d r
          S₀ α₀_disc α₀_pt i (D i) P X hFlat hMetric (by omega) hlam'4 hθ''_ge hθ''_even rfl
          hlam_bound_beta hθ''_beta le_rfl hr_inj hr_eye hr_dist
          hTransP hPathsP hX_sub hEndsP hFreeX hCardτ₂ hDouble)

/-- **Graph Minors XV, (1.2)** (pages 115–116, proved in Section 7, pages 134–145):
For any connected surface `Σ` with `bd(Σ) = ∅` and any `k ≥ 0`, `φ ≥ 8`, `μ ≥ 12` even,
`λ_{k+1} ≥ 4`, and `θ_{k+1} ≥ 4λ_{k+1} + μ + 2`, there exist `p_k, λ_k, θ_k` with
`θ_k ≥ 4λ_k + μ + 2` such that every `(λ_k, μ)`-flat `Σ`-span of order `≥ θ_k` with `k` eyes at
distance `≥ θ_k` yields one of `(S1)`, `(S2)`, or `(S3)`. -/
theorem theorem_1_2_proof
     :
    GM15Theorem12Statement.{u, v, w} := by
  intro S _ _ hSurface hConnected hBoundary k φ μ lam θ hφ hμ hEven hlam hθ
  obtain ⟨width, flatness, order, horder, hstep⟩ :=
    theorem_1_2_proper.{u,v,w} S hSurface hConnected hBoundary k φ μ lam θ hφ hμ hEven hlam hθ
  refine ⟨width, flatness, order, horder, ?_⟩
  intro α β G θ_star T_star H η θ₀ T d hFlat hMetric hle hEyes
  exact (hstep G θ_star T_star H η θ₀ T d hFlat hMetric hle hEyes).imp id
    (Or.imp id Section7ProperS3.toSection7S3)

end GraphMinor.GM15
