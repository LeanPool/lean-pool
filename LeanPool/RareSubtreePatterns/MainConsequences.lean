/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.MainTheorems
public import LeanPool.RareSubtreePatterns.DirectApplications.DeclumpZero
public import LeanPool.RareSubtreePatterns.DirectApplications.Outdegree


/-!
# Unconditional consequences of the four Introduction theorems

Several corollaries of the paper were formalized as conditional lemmas taking one of the
Introduction theorems as an explicit hypothesis (`h1 : PoissonApproximationStatement`,
`h2 : PoissonApproximation2Statement`, `h : MaxLeafHeightStatement`). Since those theorems are now
proved (`PoissonDeclumping.poissonApproximation`, `PoissonDeclumping.poissonApproximation2`,
`PoissonDeclumping.maxLeafHeight` in `PoissonDeclumping.MainTheorems`), this module exports the
unconditional versions, in the namespace `PoissonDeclumping.Main`. Each statement is the statement
of the corresponding conditional lemma with the main-theorem hypothesis removed.

* `Main.poisson_fringe` (**Corollary `cor:Poisson_fringe`**, C3.1, source lines 924–958);
* `Main.poisson_fringe_prescribed_tree`, `Main.poisson_fringe_size`,
  `Main.poisson_fringe_degreeStatistic` (**Remark `rem:implication_fringe`**, R3.2,
  source lines 971–1006);
* `Main.nonfringe_poisson` (**Corollary `cor:Non-fringe Poisson`**, C3.8, source lines
  1387–1422);
* `Main.large_outdegree` (**Proposition 3.9**, P3.9, large outdegrees);
* `Main.declump_zero` (**Corollary `cor:declump_zero`**, C5.3);
* `Main.poisson_of_convenient_criterion` (the convenient sufficient criterion, source lines
  359–364, U01);
* `Main.leafHeight_div_log_tendsto`, `Main.leafHeight_div_logb_log_tendsto` (the first-order
  consequences of Theorem `thm:max_lh`, source lines 574–581, U03).

It also exports the two parts of Lemmas `lem:S_rary` and `lem:S_lh` that were previously used only
inline in the proofs of Theorems `thm:max_string` and `thm:max_lh`:

* `Applications.lem_S_rary_iii` (**Lemma `lem:S_rary`(iii)**, source lines 2644–2653):
  `E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}` for the complete `r`-ary marks `G_k = 1{H_{r,k} ≺ ·}`;
* `Applications.lem_S_lh_ii` (**Lemma `lem:S_lh`(ii)**, source lines 3053–3064):
  `E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}` for the leaf-height marks `G_k = 1{λ_∅ ≥ k}`.

Both follow, as in the paper, from part (i) (Assumption (S) with respect to
`M_n = max 1 ⌊n^{1-η}⌋₊`) and Corollary `cor:SM`(ii) (`Bridge.integral_markCount_isEquivalent`).
The conclusion does not involve the cutoff, so the exponent `η ∈ (0, 1 - 1/α)` fixed in the paper
is chosen internally (`η = (1 - 1/α)/2`) and does not appear as a hypothesis. The
`n^{o(1)}` hypotheses are used, as in part (i), only through their upper halves `≤ n^δ`.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping

open PlaneTree

namespace Applications

/-- **Lemma `lem:S_rary`(iii)** (source lines 2644–2653): let `(k_n)` be such that
`s_{r,k_n} + ℓ_{r,k_n} = n^{o(1)}` (`s_{r,k}` = number of internal vertices, `ℓ_{r,k}` = number of
leaves of `H_{r,k}`; only the upper half `≤ n^δ`, for every `δ > 0`, eventually along admissible
sizes, is used). Then `E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}` along admissible sizes, where
`N_k(T) = #{v ∈ T : H_{r,k} ≺ T_v}` and `π_k = P(H_{r,k} ≺ 𝒯)`. Proof as in the paper:
Corollary `cor:SM`(ii) applied to Assumption (S) from part (i) (`lem_S_rary_i`) with
`M_n = max 1 ⌊n^{1-η}⌋₊`, `η = (1 - 1/α)/2`. -/
theorem lem_S_rary_iii {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hμ : StableDomain μ α a) {r : ℕ}
    {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ((internalCount (completeTree r (k n)) + leafCount (completeTree r (k n)) : ℕ) : ℝ) ≤
        (n : ℝ) ^ δ) :
    IsEquivalent (admissibleSizes μ)
      (fun n => ∫ T, (markCount (Embeds (completeTree r (k n))) T : ℝ) ∂conditioned μ n)
      (fun n => (n : ℝ) * markProb μ (fun j => Embeds (completeTree r j)) k n) := by
  have hT := Stable.stableToolkit hμ
  obtain ⟨hη, hη1⟩ := Extremes.cutoff_exponent hT
  exact Bridge.integral_markCount_isEquivalent hT (Bridge.isCutoff_max_one_floor_rpow hη.1 hη1)
    (lem_S_rary_i hT hη hk)

/-- **Lemma `lem:S_lh`(ii)** (source lines 3053–3064): let `κ = min{j ≥ 1 : μ_j > 0}` and let
`(k_n)` be such that `k_n = n^{o(1)}` if `κ = 1`, and `κ^{k_n} = n^{o(1)}` if `κ ≥ 2` (only the
upper halves `≤ n^δ`, for every `δ > 0`, eventually along admissible sizes, are used). Then
`E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}` along admissible sizes, where `N_k(T) = #{v ∈ T : λ_∅(T_v) ≥ k}`
and `π_k = P(λ_∅(𝒯) ≥ k)`. Proof as in the paper: Corollary `cor:SM`(ii) applied to
Assumption (S) from part (i) (`lem_S_lh`) with `M_n = max 1 ⌊n^{1-η}⌋₊`, `η = (1 - 1/α)/2`.
(The paper's standing assumption `c > 0` of its Section 7.2 is not needed.) -/
theorem lem_S_lh_ii {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hμ : StableDomain μ α a) {k : ℕ → ℕ}
    (hk1 : LeafHeight.kappa μ = 1 → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      (k n : ℝ) ≤ (n : ℝ) ^ δ)
    (hk2 : 2 ≤ LeafHeight.kappa μ → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      (LeafHeight.kappa μ : ℝ) ^ k n ≤ (n : ℝ) ^ δ) :
    IsEquivalent (admissibleSizes μ)
      (fun n => ∫ T, (markCount (fun U => k n ≤ rootLeafHeight U) T : ℝ) ∂conditioned μ n)
      (fun n => (n : ℝ) * markProb μ (fun j T => j ≤ rootLeafHeight T) k n) := by
  have hT := Stable.stableToolkit hμ
  obtain ⟨hη, hη1⟩ := Extremes.cutoff_exponent hT
  exact Bridge.integral_markCount_isEquivalent hT (Bridge.isCutoff_max_one_floor_rpow hη.1 hη1)
    (lem_S_lh hT hη hk1 hk2)

end Applications

namespace Main

/-! ### Section 3: direct applications of Theorem `thm:PoissonApproximation` -/

/-- **Corollary `cor:Poisson_fringe`** (C3.1, source lines 924–958), unconditional form of
`DirectApplications.poisson_fringe_of`: let `μ` be critical in the domain of attraction of an
`α`-stable law, `α ∈ (1,2]`, let `k_n → ∞` with `k_n = o(n)`, and assume `G_k(τ) = 1 ⇒ |τ| = k`
for every `k ≥ 1` and every plane tree `τ`. Then both conclusions of Theorem 1.1 hold. -/
theorem poisson_fringe {μ : PMF ℕ}
    (hμ : InStableDomain μ) {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hG : ∀ j : ℕ, 1 ≤ j → ∀ τ : PlaneTree, G j τ → τ.vertexCount = j) :
    DirectApplications.PoissonApproximationConclusion μ G k :=
  DirectApplications.poisson_fringe_of poissonApproximation hμ hk hko hG

/-- **Remark `rem:implication_fringe`**, first case (R3.2), unconditional form of
`DirectApplications.poisson_fringe_prescribed_tree`: one prescribed tree `T_n` with `|T_n| = k_n`.
-/
theorem poisson_fringe_prescribed_tree {μ : PMF ℕ}
    (hμ : InStableDomain μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) (Tn : ℕ → PlaneTree)
    (hTn : ∀ n, (Tn n).vertexCount = k n) :
    DirectApplications.PoissonApproximationConclusion μ (fun n T => T = Tn n) id :=
  DirectApplications.poisson_fringe_prescribed_tree poissonApproximation hμ hk hko Tn hTn

/-- **Remark `rem:implication_fringe`**, second case (R3.2), unconditional form of
`DirectApplications.poisson_fringe_size`: all trees of size `k_n`. -/
theorem poisson_fringe_size {μ : PMF ℕ}
    (hμ : InStableDomain μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    DirectApplications.PoissonApproximationConclusion μ (fun j T => T.vertexCount = j) k :=
  DirectApplications.poisson_fringe_size poissonApproximation hμ hk hko

/-- **Remark `rem:implication_fringe`**, third case (R3.2), unconditional form of
`DirectApplications.poisson_fringe_degreeStatistic`: trees with a prescribed degree statistic
`𝐧_{k_n}` of size `k_n`. -/
theorem poisson_fringe_degreeStatistic {μ : PMF ℕ}
    (hμ : InStableDomain μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) (N : ℕ → ℕ →₀ ℕ)
    (hN : ∀ n, DirectApplications.IsDegreeStatistic (N n) (k n)) :
    DirectApplications.PoissonApproximationConclusion μ
      (fun n T => DirectApplications.HasDegreeStatistic (N n) T) id :=
  DirectApplications.poisson_fringe_degreeStatistic poissonApproximation hμ hk hko N hN

/-- **Corollary `cor:Non-fringe Poisson`** (C3.8, source lines 1387–1422), unconditional form of
`DirectApplications.nonfringe_poisson_of`, with the paper's hypotheses. -/
theorem nonfringe_poisson {μ : PMF ℕ} {α : ℝ}
    {a : ℕ → ℝ} (hμ : StableDomain μ α a) (_haper : Stable.latticeSpan μ = 1)
    (Tk : ℕ → PlaneTree) (hTk : ∀ j : ℕ, 1 ≤ j → (Tk j).vertexCount = j) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) {M : ℕ → ℕ} (hM : IsCutoff M)
    (hC : (fun n => ((k n - leafCount (Tk (k n)) : ℕ) : ℝ)) =o[admissibleSizes μ]
      (fun n => (M n : ℝ)))
    (hL : (fun n => (leafCount (Tk (k n)) : ℝ)) =o[admissibleSizes μ] (fun n => a (M n)))
    (hsup : (fun n => ⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ},
        pairProb μ (fun j T => Embeds (Tk j) T) k n ℓ) =o[admissibleSizes μ]
      (fun n => (n : ℝ) / M n * markProb μ (fun j T => Embeds (Tk j) T) k n ^ 2)) :
    DirectApplications.PoissonApproximationConclusion μ (fun j T => Embeds (Tk j) T) k :=
  DirectApplications.nonfringe_poisson_of poissonApproximation hμ _haper Tk hTk hk hM hC hL hsup

/-- **Proposition 3.9** (P3.9, large outdegrees), unconditional form of
`DirectApplications.large_outdegree_of`: for `D_n = #{u ∈ 𝒯^n : k_u(𝒯^n) = d_n}`,
(i) bounded `n μ_{d_n}` gives `d_TV(D_n, Po(n μ_{d_n})) → 0` (and `D_n → Po(λ)` if
`n μ_{d_n} → λ`); (ii) `n μ_{d_n} → ∞` gives `D_n / (n μ_{d_n}) → 1` and `D_n → ∞` in
probability. -/
theorem large_outdegree {μ : PMF ℕ} {α : ℝ}
    {a : ℕ → ℝ} (hμ : StableDomain μ α a) {d : ℕ → ℕ} (hdpos : ∀ n, 0 < d n)
    (_hd : Tendsto d atTop atTop) (_hμd : ∀ᶠ n in atTop, 0 < μ (d n))
    {M : ℕ → ℕ} (hM : IsCutoff M)
    (hdM : (fun n => (d n : ℝ)) =o[admissibleSizes μ] (fun n => a (M n))) :
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * (μ (d n)).toReal ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist
        ((conditioned μ n).map (markCount (fun T => T.rootDegree = d n)))
        (poissonMeasure (Real.toNNReal ((n : ℝ) * (μ (d n)).toReal))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (∀ lam : ℝ≥0,
      Tendsto (fun n : ℕ => (n : ℝ) * (μ (d n)).toReal) (admissibleSizes μ) (𝓝 (lam : ℝ)) →
      Tendsto (fun n : ℕ => paperTVDist
        ((conditioned μ n).map (markCount (fun T => T.rootDegree = d n))) (poissonMeasure lam))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * (μ (d n)).toReal) (admissibleSizes μ) atTop →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (conditioned μ n).real
        {T | ε < |(markCount (fun T => T.rootDegree = d n) T : ℝ) /
          ((n : ℝ) * (μ (d n)).toReal) - 1|}) (admissibleSizes μ) (𝓝 0)) ∧
      (∀ K : ℕ, Tendsto (fun n : ℕ => (conditioned μ n).real
        {T | markCount (fun T => T.rootDegree = d n) T ≤ K}) (admissibleSizes μ) (𝓝 0))) :=
  DirectApplications.large_outdegree_of poissonApproximation hμ hdpos _hd _hμd hM hdM

/-- **The convenient sufficient criterion** (U01, source lines 359–364), unconditional form of
`DirectApplications.poisson_of_convenient_criterion`: if a decomposition `ρ` of
`P(· | G_k(𝒯) = 1)` has `E_{k_n}[C_{k_n} + L_{k_n}] ≤ n^δ` and the pair probabilities satisfy
`sup_{ℓ ≥ 1} A_n(ℓ) ≤ n^δ π_n²` for every `δ > 0` eventually, then both conclusions of
Theorem 1.1 hold. -/
theorem poisson_of_convenient_criterion {μ : PMF ℕ}
    {α : ℝ} {a : ℕ → ℝ} (hμ : StableDomain μ α a) {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (ρ : ℕ → Measure (PlaneTree × ℕ × List PlaneTree))
    (hρ : ∀ j, 0 < bienayme μ {T | G j T} → Skeleton μ (G j) (ρ j))
    (hmom : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂ρ (k n) ≤
        ENNReal.ofReal ((n : ℝ) ^ δ))
    (hpair : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, ∀ ℓ : ℕ, 1 ≤ ℓ →
      pairProb μ G k n ℓ ≤ (n : ℝ) ^ δ * markProb μ G k n ^ 2) :
    DirectApplications.PoissonApproximationConclusion μ G k :=
  DirectApplications.poisson_of_convenient_criterion poissonApproximation hμ ρ hρ hmom hpair

/-! ### Section 5: Corollary `cor:declump_zero` -/

/-- **Corollary `cor:declump_zero`** (C5.3), unconditional form of
`DirectApplications.declump_zero_of`: under (S) for `(G_k)`, (C) for the declumped marks,
propagation outside `B`, `0 < c_B < ∞` and `π_n = O(1/n)`,
`P(N_{k_n}(𝒯^n) = 0) - exp(-c_B n π_n) → 0` along admissible sizes. -/
theorem declump_zero {μ : PMF ℕ} {α : ℝ}
    {a : ℕ → ℝ} (hμ : StableDomain μ α a) {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M) {B : Set ℕ} (hB0 : 0 < cB μ B) (hBfin : cB μ B < ∞)
    (hS : StructuralMicroscopic μ a G k M)
    (hC : NonClustering μ (fun j => declumpedMark B (G j)) k M)
    (hprop : ∀ j, PropagatesOutside B (G j))
    (hO : markProb μ G k =O[admissibleSizes μ] (fun n => 1 / (n : ℝ))) :
    Tendsto (fun n : ℕ => (conditioned μ n).real {T | markCount (G (k n)) T = 0} -
      Real.exp (-((cB μ B).toReal * ((n : ℝ) * markProb μ G k n))))
      (admissibleSizes μ) (𝓝 0) :=
  DirectApplications.declump_zero_of poissonApproximation2 hμ hM hB0 hBfin hS hC hprop hO

/-! ### First-order consequences of Theorem `thm:max_lh` (U03) -/

/-- **U03, first-order consequence of Theorem `thm:max_lh`(i)** (source lines 574–581),
unconditional form of `MaxLeafHeight.leafHeight_div_log_tendsto`: if `μ_1 > 0`, then
`λ(𝒯^n)/log n → 1/log(1/μ_1)` in probability (along admissible sizes). -/
theorem leafHeight_div_log_tendsto {μ : PMF ℕ} (hμ : InStableDomain μ)
    (hpos : 0 < μ 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n).real
      {T | ε < |(leafHeight T : ℝ) / Real.log n - 1 / Real.log (1 / (μ 1).toReal)|})
      (admissibleSizes μ) (𝓝 0) :=
  MaxLeafHeight.leafHeight_div_log_tendsto maxLeafHeight hμ hpos hε

/-- **U03, first-order consequence of Theorem `thm:max_lh`(ii)** (source lines 574–578),
unconditional form of `MaxLeafHeight.leafHeight_div_logb_log_tendsto`: if `μ_1 = 0` and
`κ = min{i ≥ 2 : μ_i > 0}`, then `λ(𝒯^n)/log_κ log n → 1` in probability (along admissible
sizes). -/
theorem leafHeight_div_logb_log_tendsto {μ : PMF ℕ} (hμ : InStableDomain μ)
    (h0 : μ 1 = 0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n).real
      {T | ε < |(leafHeight T : ℝ) / Real.logb (sInf {i : ℕ | 2 ≤ i ∧ 0 < μ i} : ℕ)
        (Real.log n) - 1|})
      (admissibleSizes μ) (𝓝 0) :=
  MaxLeafHeight.leafHeight_div_logb_log_tendsto maxLeafHeight hμ h0 hε

end Main

end PoissonDeclumping
