/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Defs infrastructure for Steiner spanners

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib. -/

@[expose] public section

open scoped ENNReal

namespace HighDimSteinerSpanners

/-- The `ℓ_p` distance `‖x - y‖_p = (∑_{i=1}^d |x_i - y_i|^p)^(1 / p)` on `ℝ^d` (`Fin d →
ℝ`). -/
noncomputable def lpDist (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, |x i - y i| ^ p) ^ (1 / p)

/-- Maximum pairwise `ℓ_p` distance `max_{i, j} ‖P_i - P_j‖_p` of `P : Fin n → (Fin d → ℝ)`. -/
noncomputable def maxPairwiseDist (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  if hn : 0 < n then
    haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
    Finset.univ.sup' Finset.univ_nonempty (fun ij : Fin n × Fin n => lpDist p (P ij.1) (P ij.2))
  else 0

/-- Minimum distinct-pair `ℓ_p` distance `min_{i ≠ j} ‖P_i - P_j‖_p` of `P : Fin n → (Fin d
→ ℝ)`. -/
noncomputable def minDistinctPairwiseDist (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  let offDiag := Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
  if hne : offDiag.Nonempty then
    offDiag.inf' hne (fun ij => lpDist p (P ij.1) (P ij.2))
  else 0

/-- Aspect ratio `Δ_p(P) = max_{i, j} ‖P_i - P_j‖_p / min_{i ≠ j} ‖P_i - P_j‖_p`. -/
noncomputable def aspectRatio (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  maxPairwiseDist p P / minDistinctPairwiseDist p P

/-- Total edge weight `∑_{i=1}^k w({v_{i-1}, v_i})` of a finite walk in `H : SimpleGraph V`. -/
def walkWeight {V : Type} {H : SimpleGraph V} (w : Sym2 V → ℝ) :
    ∀ {u v : V}, H.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, @SimpleGraph.Walk.cons _ _ _ b _ _ q => w s(u, b) + walkWeight w q

/-- Unrestricted-hop shortest-path distance `d_H(u, v) ∈ ℝ≥0∞` (`⊤` when disconnected). -/
noncomputable def graphDist {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) : ℝ≥0∞ :=
  ⨅ p : H.Walk u v, ENNReal.ofReal (walkWeight w p)

/-- Definition 1.1 for `(P, ‖·‖_p)` in `ℝ^d`: `H = (Fin n ⊕ S, E, w)` is an undirected
non-metric Steiner `C`-spanner of `(P, ‖·‖_p)` with unrestricted hop count. -/
structure IsNonMetricSteinerSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    {S : Type} [Fintype S] (H : SimpleGraph (Fin n ⊕ S)) (w : Sym2 (Fin n ⊕ S) → ℝ) : Prop where
  weight_nonneg : ∀ e ∈ H.edgeSet, 0 ≤ w e
  noncontracting : ∀ i j : Fin n,
    ENNReal.ofReal (lpDist p (P i) (P j)) ≤ graphDist H w (.inl i) (.inl j)
  stretch : ∀ i j : Fin n,
    graphDist H w (.inl i) (.inl j) ≤ ENNReal.ofReal (C * lpDist p (P i) (P j))

/-- Definition 1.1 (`S = ∅` geometric case): `G` is a geometric `C`-spanner of `(P, ‖·‖_p)`. -/
def IsGeometricSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j : Fin n,
    graphDist G
      (Sym2.lift ⟨fun u v => lpDist p (P u) (P v), fun u v => by
        simp only [lpDist, abs_sub_comm]⟩)
      i j ≤ ENNReal.ofReal (C * lpDist p (P i) (P j))

/-- Definition 1.1 for an arbitrary finite metric space `(P, dist)`: `H = (P ⊕ S, E, w)` is
an undirected non-metric Steiner `C`-spanner of `(P, dist)`. -/
structure IsGeneralNonMetricSteinerSpanner {P : Type} [MetricSpace P] [Fintype P]
    (C : ℝ) {S : Type} [Fintype S] (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ) : Prop where
  weight_nonneg : ∀ e ∈ H.edgeSet, 0 ≤ w e
  noncontracting : ∀ x y : P,
    ENNReal.ofReal (dist x y) ≤ graphDist H w (.inl x) (.inl y)
  stretch : ∀ x y : P,
    graphDist H w (.inl x) (.inl y) ≤ ENNReal.ofReal (C * dist x y)

/-- Unscaled one-hot map `ι : [q]^N → {0, 1}^{N q} ⊂ ℝ^{N q}` (`ι(x)_{v, c} = 1[x_v = c]`)
from Theorem 2.1(b). -/
def oneHotEmbed {N q : ℕ} (x : Fin N → Fin q) : Fin (N * q) → ℝ :=
  fun k =>
    let vc := finProdFinEquiv.symm k
    if x vc.1 = vc.2 then 1 else 0

/-- Disagreement coordinate set `Δ(x, y) = {v ∈ [N] : x_v ≠ y_v}`. -/
def disagreeSet {N q : ℕ} (x y : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x v ≠ y v)

/-- Ordered pairs `E_{rStar}(X) = {(x, y) ∈ X × X : d_Ham(x, y) = rStar}` at exact Hamming
distance `rStar`. -/
def exactDistPairs {N q : ℕ} (X : Finset (Fin N → Fin q)) (rStar : ℕ) :
    Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
  (X ×ˢ X).filter (fun xy => hammingDist xy.1 xy.2 = rStar)

/-- Condition **(List-Size)** of Theorem 2.2(a): `|L(a, b)| < K` for `0 < d_Ham(a, b) ≤ C₁
rStar`. -/
def ListSizeCond {N q : ℕ} (C₁ rStar K : ℕ) (X : Finset (Fin N → Fin q))
    (L : ↥X → ↥X → Finset ↥X) : Prop :=
  ∀ a b : ↥X,
    0 < hammingDist a.val b.val →
    hammingDist a.val b.val ≤ C₁ * rStar →
    (L a b).card < K

/-- Condition **(Overlap)** of Theorem 2.2(a): for every `(x, w₀) ∈ X²` with `0 < d_Ham(x,
w₀) ≤ C₁ rStar`, fewer than `K` points `y ∈ X \ {x, w₀}` satisfy `d_Ham(x, y) = rStar`
and `|Δ(x, w₀) ∩ Δ(x, y)| > rStar / 4`. -/
noncomputable def OverlapCond {N q : ℕ} (C₁ rStar K : ℕ) (X : Finset (Fin N → Fin q)) : Prop :=
  ∀ x w₀ : ↥X,
    0 < hammingDist x.val w₀.val →
    hammingDist x.val w₀.val ≤ C₁ * rStar →
    (Finset.univ.filter (fun y : ↥X =>
      y ≠ x ∧ y ≠ w₀ ∧
      hammingDist x.val y.val = rStar ∧
      (rStar : ℝ) / 4 < ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ))).card < K

/-- Condition **(List-Hit)** of Theorem 2.2(a): along any sequence `w₀, ..., w_ℓ ∈ B_X(x, C₁
rStar) \ {x}` (`ℓ ≥ 1`) with step lengths in `(0, C₁ rStar]`, `d_Ham(x, w_ℓ) = rStar`,
and `|Δ(x, w₀) ∩ Δ(x, w_ℓ)| ≤ rStar / 4`, some step `s` satisfies `x ∈ L(w_{s-1}, w_s)`. -/
def ListHitCond {N q : ℕ} (C₁ rStar : ℕ) (X : Finset (Fin N → Fin q))
    (L : ↥X → ↥X → Finset ↥X) : Prop :=
  ∀ (x : ↥X) (ℓ : ℕ), 1 ≤ ℓ →
    ∀ (w : Fin (ℓ + 1) → ↥X),
      (∀ t : Fin (ℓ + 1), w t ≠ x ∧ hammingDist x.val (w t).val ≤ C₁ * rStar) →
      (∀ s : Fin ℓ,
        0 < hammingDist (w s.castSucc).val (w s.succ).val ∧
        hammingDist (w s.castSucc).val (w s.succ).val ≤ C₁ * rStar) →
      hammingDist x.val (w (Fin.last ℓ)).val = rStar →
      ((disagreeSet x.val (w 0).val ∩ disagreeSet x.val (w (Fin.last ℓ)).val).card : ℝ) ≤
        (rStar : ℝ) / 4 →
      ∃ s : Fin ℓ, x ∈ L (w s.castSucc) (w s.succ)

/-- Diameter `D_i = max_{u, v ∈ B} dist(u, v)` of a finite subset `B ⊆ P` (Proposition 3.1). -/
noncomputable def bucketDiam {P : Type} [MetricSpace P] (B : Finset P) : ℝ :=
  if hne : B.Nonempty then
    B.sup' hne (fun u => B.sup' hne (fun v => dist u v))
  else 0

/-- Bipartite bucket-hub graph `H = (P ⊔ I, E)` with `E = {{x, i} : x ∈ B_i}` (Proposition
3.1). -/
def bucketingGraph {P I : Type} (B : I → Finset P) : SimpleGraph (P ⊕ I) where
  Adj u v :=
    match u, v with
    | .inl x, .inr i => x ∈ B i
    | .inr i, .inl x => x ∈ B i
    | _, _ => False
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> exact h⟩
  loopless := ⟨by
    intro u h
    cases u <;> exact h⟩

/-- Edge weights `w({x, i}) = D_i / 2` on `bucketingGraph B` (Proposition 3.1). -/
noncomputable def bucketingWeight {P I : Type} [MetricSpace P] (B : I → Finset P) :
    Sym2 (P ⊕ I) → ℝ :=
  Sym2.lift ⟨fun u v =>
    match u, v with
    | .inl _, .inr i => bucketDiam (B i) / 2
    | .inr i, .inl _ => bucketDiam (B i) / 2
    | _, _ => 0,
    fun u v => by cases u <;> cases v <;> rfl⟩

/-- Standard basis `P = {e_1, ..., e_n} ⊂ {0, 1}^n` (Proposition 3.2(a)). -/
def stdBasis (n : ℕ) : Fin n → (Fin n → ℝ) :=
  fun i j => if i = j then 1 else 0

/-- Inclusion of `{0, 1}^d` (`Fin d → Bool`) into `ℝ^d` (`false ↦ 0`, `true ↦ 1`). -/
def boolVecToReal {d : ℕ} (x : Fin d → Bool) : Fin d → ℝ :=
  fun i => if x i then 1 else 0

/-- Ambient `ℓ_p` distance `‖x - y‖_p` on `{0, 1}^d` (`Fin d → Bool`). -/
noncomputable def cubeLpDist (p : ℝ) {d : ℕ} (x y : Fin d → Bool) : ℝ :=
  lpDist p (boolVecToReal x) (boolVecToReal y)

/-- Ambient `ℓ_p` edge weight `w({u, v}) = ‖u - v‖_p` on any vertex subset `V ⊆ {0, 1}^d`. -/
noncomputable def cubeSubgraphWeight (p : ℝ) {d : ℕ} (V : Finset (Fin d → Bool)) :
    Sym2 ↥V → ℝ :=
  Sym2.lift ⟨fun u v => cubeLpDist p u.val v.val, fun u v => by
    simp only [cubeLpDist, lpDist, abs_sub_comm]⟩

/-- Symmetric binary `2`-CSP constraint family `R` on `K_N` over alphabet `[q]` (Section
6.1). -/
def Symmetric2CSP {N q : ℕ} (R : Fin N → Fin N → Fin q → Fin q → Prop) : Prop :=
  ∀ u v : Fin N, ∀ c₁ c₂ : Fin q, R u v c₁ c₂ ↔ R v u c₂ c₁

/-- Satisfying assignments `Ω(R) = {x ∈ [q]^N : ∀ u < v, (x_u, x_v) ∈ R_{u, v}}` (Section
6.1). -/
noncomputable def satisfyingSet {N q : ℕ} (R : Fin N → Fin N → Fin q → Fin q → Prop) :
    Finset (Fin N → Fin q) := by
  classical
  exact
    Finset.univ.filter (fun x => ∀ u v : Fin N, u < v → R u v (x u) (x v))

/-- Three-way disagreement set `D_3(x, y, z) = {v ∈ [N] : |{x_v, y_v, z_v}| = 3}` (Section
6.1). -/
def threeWayDisagree {N q : ℕ} (x y z : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x v ≠ y v ∧ x v ≠ z v ∧ y v ≠ z v)

/-- Active alternative color `c_v(x, a, b) = a_v` if `a_v ≠ x_v`, else `b_v` (Section 6.1). -/
def activeColor {N q : ℕ} (x a b : Fin N → Fin q) (v : Fin N) : Fin q :=
  if a v ≠ x v then a v else b v

/-- **Definition 6.1 (The Lists `L_R(a, b)`)** -/
noncomputable def bicliqueWitnessList {N q : ℕ}
    (R : Fin N → Fin N → Fin q → Fin q → Prop) (C₁ rStar : ℕ)
    (a b : Fin N → Fin q) : Finset (Fin N → Fin q) := by
  classical
  exact
    let W := fun x => disagreeSet x a ∪ disagreeSet x b
    let I := fun x => disagreeSet x a ∩ disagreeSet x b
    (satisfyingSet R).filter (fun x =>
      x ≠ a ∧ x ≠ b ∧
      hammingDist x a ≤ C₁ * rStar ∧
      hammingDist x b ≤ C₁ * rStar ∧
      ∃ k : ℕ, k ≤ 8 * C₁ ∧
        ∃ (A B_fut B_out : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
          Pairwise (fun i j => Disjoint (A i) (A j)) ∧
          (∀ r : Fin k, Disjoint (A r) I_k) ∧
          Finset.univ.biUnion A ∪ I_k = I x ∧
          (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
          ∀ r : Fin k,
            let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
            B_fut r ⊆ I_rem ∧
            B_out r ⊆ W x \ (A r ∪ I_rem) ∧
            (∀ u ∈ A r, ∀ v ∈ B_fut r ∪ B_out r, R u v (x u) (activeColor x a b v)) ∧
            (((I_rem \ B_fut r).card : ℝ) ≤ (rStar : ℝ) / 80 ∧
             ((A r).card : ℝ) - (11 : ℝ) / 40 * (rStar : ℝ) ≤ ((B_out r).card : ℝ)))

end HighDimSteinerSpanners
