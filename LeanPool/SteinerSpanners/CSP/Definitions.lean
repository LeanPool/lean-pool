/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

public import Mathlib.Data.FinEnum

public import LeanPool.SteinerSpanners.Defs

/-! # Definitions for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

/-- Coordinates where two assignments disagree. -/
abbrev diffCoords {N q : ℕ} (x y : Fin N → Fin q) : Finset (Fin N) :=
  disagreeSet x y

/-- Hamming distance computed from the finite disagreement set. -/
abbrev dHam {N q : ℕ} (x y : Fin N → Fin q) : ℕ :=
  (disagreeSet x y).card

/-- Coordinates carrying three pairwise distinct assignment values. -/
abbrev d3Coords {N q : ℕ} (x y z : Fin N → Fin q) : Finset (Fin N) :=
  threeWayDisagree x y z

/-- Maximum number of pieces in a candidate peeling witness. -/
def cspKMax (C₁ : ℕ) : ℕ := 8 * C₁

/-- Moment order used to exclude large local cherry lists. -/
def cspKCh (C₁ : ℕ) : ℕ := 20 * C₁ ^ 2

/-- Moment order used to exclude large local biclique-witness lists. -/
def cspKMom (C₁ : ℕ) : ℕ := 20 * C₁ ^ 2

/-- The constant inverse three-way-disagreement tolerance, independent of the stretch parameter. -/
def cspInvEta0 (_C₁ : ℕ) : ℕ := 80

/-- Logarithmic calibration scale controlling the code construction. -/
def cspLam0 (C₁ : ℕ) : ℕ := 100 * C₁ * (2 * Nat.clog 2 C₁ + 6)

/-- Code-size exponent scale, equal to six times the calibration scale. -/
def cspBeta0 (C₁ : ℕ) : ℕ := 6 * cspLam0 C₁

/-- Distance-decay exponent scale, equal to five times the calibration scale. -/
def cspGamma0 (C₁ : ℕ) : ℕ := 5 * cspLam0 C₁

/-- Block-repetition exponent chosen for the calibrated code. -/
def cspL (C₁ : ℕ) : ℕ := 20 + 20 * C₁ ^ 2 * cspInvEta0 C₁ * cspLam0 C₁

/-- Binary logarithm of the number of nonreference alphabet symbols. -/
def cspEq (C₁ : ℕ) : ℕ := 2 * cspBeta0 C₁ * 2 ^ cspL C₁

/-- Alphabet size, one larger than a power of two. -/
def cspQ (C₁ : ℕ) : ℕ := 2 ^ cspEq C₁ + 1

/-- Independent Bernoulli indices: constraint queries on the left, assignment-retention bits on
the right. -/
abbrev cspIota (N q : ℕ) : Type :=
  (Fin N × Fin N × Fin q × Fin q) ⊕ (Fin N → Fin q)

/-- Constraint queries required by an assignment, using increasing coordinate pairs. -/
def homQueries {N q : ℕ} (z : Fin N → Fin q) : Finset (Fin N × Fin N × Fin q × Fin q) :=
  (Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).image
    (fun uv => (uv.1, uv.2, z uv.1, z uv.2))

/-- Product Bernoulli weight of a Boolean outcome with coordinate parameters `p`. -/
noncomputable def bernWeight {ι : Type*} [Fintype ι] (p : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i : ι, if ω i = true then p i else 1 - p i

/-- Exponent determining the probability of retaining a constraint query. -/
noncomputable def cspSigmaEdge (C₁ r_star : ℕ) : ℝ :=
  ((cspEq C₁ + cspL C₁ + cspGamma0 C₁ + 2 : ℕ) : ℝ) / ((2 ^ cspL C₁ * r_star - 1 : ℕ) : ℝ)

/-- Retention probability for each constraint query in the calibrated random CSP. -/
noncomputable def cspPEdge (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ (- cspSigmaEdge C₁ r_star)

/-- Distance-s neighbor weight relative to a fixed satisfying assignment, before vertex
thinning. -/
noncomputable def cspDOmega (C₁ r_star s : ℕ) : ℝ :=
  ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
    (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1) - s.choose 2)

/-- Target degree scale for the randomly thinned code. -/
noncomputable def cspDStar (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ ((1 / 4 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))

/-- Assignment-retention probability normalized to the target degree scale. -/
noncomputable def cspPKeep (C₁ r_star : ℕ) : ℝ :=
  cspDStar C₁ r_star / cspDOmega C₁ r_star r_star

/-- Expected number of assignments retained together with all their required queries. -/
noncomputable def cspN0 (C₁ r_star : ℕ) : ℝ :=
  cspPKeep C₁ r_star * ((cspQ C₁ : ℝ) ^ (2 ^ cspL C₁ * r_star)) *
    (cspPEdge C₁ r_star) ^ ((2 ^ cspL C₁ * r_star).choose 2)

/-- Bernoulli parameter function combining constraint-query and assignment retention. -/
noncomputable def cspPIota (C₁ r_star : ℕ) : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → ℝ :=
  Sum.elim (fun _ => cspPEdge C₁ r_star) (fun _ => cspPKeep C₁ r_star)

/-- Small exponential slack used in the second-moment estimates. -/
noncomputable def cspGamma (r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ ((r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))

/-- Exponential budget for the fraction of assignments removed by bad events. -/
noncomputable def cspDeltaBad (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))

/-- Assignments distinct from two pins and within the prescribed distance of both. -/
def cspPoolCand {N q : ℕ} (C₁ r_star : ℕ) (a b : Fin N → Fin q) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun x : Fin N → Fin q =>
    x ≠ a ∧ x ≠ b ∧ dHam x a ≤ C₁ * r_star ∧ dHam x b ≤ C₁ * r_star)

/-- Coordinate-value pairs revealed by the two pins and the previous witness sequence. -/
def cspRvc {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) : Finset (Fin N × Fin q) :=
  Finset.univ.image (fun v : Fin N => (v, a v)) ∪
    Finset.univ.image (fun v : Fin N => (v, b v)) ∪
    Finset.univ.biUnion (fun t : Fin m => Finset.univ.image (fun v : Fin N => (v, z_prev t v)))

/-- Bernoulli support exposed by the pins, previous candidates and their revealed constraint
values. -/
def cspUCand {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) : Finset (cspIota N q) :=
  ({a, b} : Finset (Fin N → Fin q)).image Sum.inr ∪
    Finset.univ.image (fun t : Fin m => (Sum.inr (z_prev t) : cspIota N q)) ∪
    (Finset.univ.filter (fun t : Fin N × Fin N × Fin q × Fin q =>
      t.1 < t.2.1 ∧ (t.1, t.2.2.1) ∈ cspRvc a b m z_prev ∧
      (t.2.1, t.2.2.2) ∈ cspRvc a b m z_prev)).image Sum.inl

/-- Exact-distance cherry candidates with large pair overlap and controlled three-way
disagreement. -/
def cspPoolCh {N q : ℕ} (C₁ r_star : ℕ) (x w₀ : Fin N → Fin q) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun y : Fin N → Fin q =>
    y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
    r_star < 4 * (disagreeSet x w₀ ∩ disagreeSet x y).card ∧
    cspInvEta0 C₁ * (threeWayDisagree x w₀ y).card ≤ r_star)

/-- Bernoulli support exposed by a cherry center, its pin and the previous candidates. -/
def cspUCh {N q : ℕ} (x w₀ : Fin N → Fin q) (m : ℕ)
    (y_prev : Fin m → (Fin N → Fin q)) : Finset (cspIota N q) :=
  ({x, w₀} : Finset (Fin N → Fin q)).image Sum.inr ∪
    Finset.univ.image (fun t : Fin m => (Sum.inr (y_prev t) : cspIota N q)) ∪
    (homQueries x ∪ homQueries w₀ ∪
      Finset.univ.biUnion (fun t : Fin m => homQueries (y_prev t))).image Sum.inl

/-- Symmetric irreflexive CSP relation induced by the constraint-query bits of an outcome. -/
def symROf {N q : ℕ} (ω : cspIota N q → Bool) : Fin N → Fin N → Fin q → Fin q → Prop :=
  fun u v c₁ c₂ =>
    if u < v then ω (Sum.inl (u, v, c₁, c₂)) = true
    else if v < u then ω (Sum.inl (v, u, c₂, c₁)) = true
    else False

/-- Assignments whose retention bit and all required constraint-query bits are true. -/
def cspPRaw {N q : ℕ} (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun x : Fin N → Fin q =>
    ω (Sum.inr x) = true ∧ ∀ t ∈ homQueries x, ω (Sum.inl t) = true)

open Classical in
/-- Raw assignments admitting a nearby satisfying triple with excessive three-way disagreement. -/
def cspBD3 {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ u ∈ cspPRaw ω, ∃ z : Fin N → Fin q,
      (∀ t ∈ homQueries z, ω (Sum.inl t) = true) ∧
      dHam x u ≤ C₁ * r_star ∧ dHam x z ≤ C₁ * r_star ∧
      r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card)

/-- Raw assignments with a local cherry list reaching the forbidden moment-order threshold. -/
def cspBCh {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ w₀ ∈ cspPRaw ω, x ≠ w₀ ∧ dHam x w₀ ≤ C₁ * r_star ∧
      cspKCh C₁ ≤ ((cspPoolCh C₁ r_star x w₀).filter (fun y => y ∈ cspPRaw ω)).card)

/-- Raw assignments with too many retained biclique witnesses for some nearby second pin. -/
noncomputable def cspBCand {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) :
    Finset (Fin N → Fin q) :=
  by
    classical
    exact
      (cspPRaw ω).filter (fun a =>
        ∃ b ∈ cspPRaw ω, a ≠ b ∧ dHam a b ≤ C₁ * r_star ∧
          cspKMom C₁ ≤
          ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b)).card)

/-- Raw assignments having another raw assignment at distance less than half the target
distance. -/
def cspBDist {N q : ℕ} (r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ y ∈ cspPRaw ω, x ≠ y ∧ 2 * dHam x y < r_star)

/-- Union of the four bad-event sets removed from the raw code. -/
noncomputable def cspBBad {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) :
    Finset (Fin N → Fin q) :=
  cspBD3 C₁ r_star ω ∪ cspBCh C₁ r_star ω ∪ cspBCand C₁ r_star ω ∪ cspBDist r_star ω

/-- Choose the first pin color when it differs from `x`, falling back to the second pin color. -/
abbrev candCStar {N q : ℕ} (a b x : Fin N → Fin q) (v : Fin N) : Fin q :=
  activeColor x a b v

/-- Coordinates whose candidate value has not occurred in the revealed coordinate-value pairs. -/
def candMFresh {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v : Fin N => (v, x v) ∉ cspRvc a b m z_prev)

/-- Increasing coordinate pairs incident to the fresh-coordinate set. -/
def candA1 {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2 ∧ (uv.1 ∈ S ∨ uv.2 ∈ S))

/-- Finite encoding of a peeling depth, coordinate labels, future pieces and exceptional pairs. -/
abbrev candWitType (N C₁ : ℕ) : Type :=
  Fin (cspKMax C₁ + 1) ×
  (Fin N → Fin (cspKMax C₁ + 1)) ×
  (Fin (cspKMax C₁) → Finset (Fin N)) ×
  Finset (Fin (cspKMax C₁) × Fin N)

/-- Coordinate pairs supported by a labeled witness piece and its future or exceptional
coordinates. -/
def candA2 {N q : ℕ} (C₁ : ℕ) (a b x : Fin N → Fin q) (M : Finset (Fin N))
    (w : candWitType N C₁) : Finset (Fin N × Fin N) :=
  (M ×ˢ (disagreeSet x a ∪ disagreeSet x b)).filter
    (fun uv => ∃ r : Fin (cspKMax C₁),
      r.1 < w.1.1 ∧ w.2.1 uv.1 = r.succ ∧ (uv.2 ∈ w.2.2.1 r ∨ (r, uv.2) ∈ w.2.2.2))

/-- Constraint query obtained by reading both endpoint colors from the candidate assignment. -/
def candPhi1 {N q : ℕ} (x : Fin N → Fin q) (uv : Fin N × Fin N) :
    Fin N × Fin N × Fin q × Fin q :=
  (uv.1, uv.2, x uv.1, x uv.2)

/-- Ordered constraint query mixing a candidate color with the selected pin color. -/
def candPhi2 {N q : ℕ} (a b x : Fin N → Fin q) (uv : Fin N × Fin N) :
    Fin N × Fin N × Fin q × Fin q :=
  if uv.1 < uv.2 then (uv.1, uv.2, x uv.1, activeColor x a b uv.2)
  else (uv.2, uv.1, activeColor x a b uv.2, x uv.1)

/-- Admissible finite peeling witnesses with the required residual, future-piece and exception
bounds. -/
def candMWit {N q : ℕ} (C₁ r_star : ℕ) (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    Finset (candWitType N C₁) :=
  let K_max := cspKMax C₁
  let M := candMFresh a b m z_prev x
  let W_ab := disagreeSet x a ∪ disagreeSet x b
  let base := (Finset.univ : Finset (Fin (K_max + 1))) ×ˢ
    (Fintype.piFinset (fun u : Fin N =>
      if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))) ×ˢ
      Fintype.piFinset (fun _ : Fin K_max => M.powerset))
  let s_hat := fun (k : Fin (K_max + 1)) (τ : Fin N → Fin (K_max + 1)) (r : Fin K_max) =>
    if r.1 < k.1 then (M.filter (fun u => τ u = r.succ)).card - (11 * r_star) / 40 else 0
  (base.biUnion (fun ktB =>
    (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).powersetCard
      (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r)).image
      (fun U_out => (ktB.1, ktB.2.1, ktB.2.2, U_out)))).filter
    (fun w =>
      let k := w.1
      let τ := w.2.1
      let B_fut := w.2.2.1
      let U_out := w.2.2.2
      (∀ u ∈ M, (τ u).1 ≤ k.1) ∧
      2 * (M.filter (fun u => τ u = 0)).card ≤ r_star ∧
      ∀ r : Fin K_max, r.1 < k.1 →
        let M_r := M.filter (fun u => τ u = r.succ)
        let I_t := M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1)
        let B_o := W_ab.filter (fun v => (r, v) ∈ U_out)
        B_fut r ⊆ I_t ∧
        80 * (I_t \ B_fut r).card ≤ r_star ∧
        Disjoint B_o (M_r ∪ I_t) ∧
        B_o.card = M_r.card - (11 * r_star) / 40)

/-- New retention and constraint-query indices certified by a candidate peeling witness. -/
def candQCand {N q : ℕ} (C₁ : ℕ) (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (w : candWitType N C₁) : Finset (cspIota N q) :=
  ({x} : Finset (Fin N → Fin q)).image Sum.inr ∪
    ((candA1 (candMFresh a b m z_prev x)).image (candPhi1 x) ∪
      (candA2 C₁ a b x (candMFresh a b m z_prev x) w).image (candPhi2 a b x)).image Sum.inl

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
