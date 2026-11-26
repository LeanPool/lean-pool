/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15a
public import LeanPool.GraphMinor.GM19.Section6b
public import LeanPool.GraphMinor.GM19.Relabel
public import LeanPool.GraphMinor.GM19.Section8a

import LeanPool.GraphMinor.GM19.Section10f

import LeanPool.GraphMinor.GM19.Section10s

import LeanPool.GraphMinor.GM19.Section10t

import LeanPool.GraphMinor.GM19.Section11g

import LeanPool.GraphMinor.GM19.Section14ah

import LeanPool.GraphMinor.GM19.Section15q

import LeanPool.GraphMinor.GM19.Section5oProved

import LeanPool.GraphMinor.GM19.Section5r

import LeanPool.GraphMinor.GM19.Section6Two
import LeanPool.GraphMinor.GM19.UniverseLift2

/-!
# Graph Minors XIX, (4.1)

This is the proof of (4.1) at the end of Section 15. It takes a similarly oriented bad sequence for
a
disjoint colour scheme, and shows that every tangle of large order in a late term is isolated by a
rooted location from one well-behaved set. Then (9.2) gives an inflation, which (6.1) forbids.

The argument for one tangle is `exists_isolating`. In the paper it is the display (1) of the proof
together with the sentence on (10.3), (10.4), (10.5), (11.1) and (14.1).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe u w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {β : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S β}

/-- The arithmetic used in the proof of (4.1), with `B = 5^{2m+2} n = 25n · 5^{2m}`. -/
theorem level_bound (m n : ℕ) : 25 * ((m + 1) * n) ≤ 5 ^ (2 * m + 2) * n := by
  refine Nat.mul_le_mul_right _ ?_ |>.trans' (by rw [Nat.mul_assoc]) |>.trans (le_refl _)
  have h : 2 * m < 5 ^ (2 * m) := Nat.lt_pow_self (by norm_num)
  rw [pow_add]
  omega

omit [T2Space S] in
/-- One tangle in the proof of (4.1): if `𝒯` has order larger than `B = 5^{2m+2} n` in a painting
with
`rep`, `dist` larger than `B`, and there is no inflation of `P₀`, then one of the five kinds of flaw
holds and so `𝒯` is `(B + 1)`-isolated by a rooted location from `𝒞`. -/
theorem exists_isolating (hd : χ.IsDisjoint) {𝒮 : Set (ColouredPainting χ)}
    {P₀ : ColouredPainting χ} {n : ℕ} (hn : 8 ≤ n) {ω : Set S → List β}
    (hω : ∀ side ∈ χ.Φ.longSides, IsBorderLabels P₀ side (ω side))
    {𝒞₁ : Set (Place χ)} {𝒞₂ 𝒞₃ : ℕ → Set (Place χ)} {𝒞₄ 𝒞₅ : Set (Place χ)}
    {B : ℕ} (hB : B = 5 ^ (2 * P₀.Γ.E.ncard + 2) * n)
    (p₁ : ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → ((B + 1 : ℕ) : ℕ∞) ≤ Painting.rep D.rad → B + 1
      ≤ D.ord →
      D.rep < B + 1 → ((B + 1 + 2 : ℕ) : ℕ∞) ≤ 2 * Painting.dist D.rad →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (B + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞₁)
    (p₂ : ∀ a, ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → D.IsFlawedInDistance (a + 1) →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (a + 1 + 1) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞₂ a)
    (p₃ : ∀ a, ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → D.IsFlawedInFreedom a →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (a + 1) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞₃ a)
    (p₄ : ∀ side ∈ χ.Φ.longSides, ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      D.IsFlawedOnSide side (n / 2) (ω side) →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (((ω side).length + 1) * (n / 2)) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞₄)
    (p₅ : ∀ f ∈ P₀.Γ.E, Painting.IsInternal f → ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      D.IsFlawedInternally P₀.Γ.E.ncard n (tilde f).ncard (P₀.φ f) →
      ∃ L : RootedLocation D.P.Γ,
        L.Isolates D.tb (4 * n * 5 ^ (2 * P₀.Γ.E.ncard) + 3) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞₅)
    {𝒞 : Set (Place χ)} (h₁ : 𝒞₁ ⊆ 𝒞) (h₂ : ∀ a ≤ B, 𝒞₂ a ⊆ 𝒞) (h₃ : ∀ a ≤ B, 𝒞₃ a ⊆ 𝒞)
    (h₄ : 𝒞₄ ⊆ 𝒞) (h₅ : 𝒞₅ ⊆ 𝒞)
    (D : TangleDatum cap χ) (hD : D.P ∈ 𝒮) (hrep : (B : ℕ∞) < Painting.rep D.rad)
    (hdist : (B : ℕ∞) < Painting.dist D.rad) (hord : B + 1 ≤ D.ord)
    (h152 : 3 * n < 2 * D.rep →
      (∃ r₁ ∈ D.rad.poles, ∃ r₂ ∈ D.rad.poles, r₁ ≠ r₂ ∧ D.vDist r₁ r₂ ≤ n) ∨
      (∃ F : Drawing Shat, F.IsCircuitOf D.rad.G ∧ F.E.ncard ≤ 2 * n ∧
        ((∃ side ∈ χ.Φ.longSides, cap.emb '' side ⊆ D.ins F) ∨
          F.E.ncard < 2 * ((cap.emb '' χ.Φ.V) ∩ D.ins F).ncard)) ∨
      (∃ side ∈ χ.Φ.longSides, D.NoSideMatch side (n / 2) (ω side)) ∨
      (∃ f ∈ P₀.Γ.E, Painting.IsInternal f ∧
        D.NoInternalMatch P₀.Γ.E.ncard n (tilde f).ncard (P₀.φ f))) :
    ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (B + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞
      := by
  have hlev : 25 * ((P₀.Γ.E.ncard + 1) * n) ≤ B := hB ▸ level_bound _ _
  set m := P₀.Γ.E.ncard with hm
  have hnc : n ≤ (m + 1) * n := Nat.le_mul_of_pos_left _ (by omega)
  have hB25 : 25 * n ≤ B := by omega
  -- The two reductions: a flaw in distance or in freedom at any level up to `B`.
  have G : ∀ a, 1 ≤ a → a ≤ B → D.IsFlawedInDistance a → ∃ L : RootedLocation D.P.Γ,
      L.Isolates D.tb (B + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 := by
    intro a ha₁ haB hf
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨L, hL, hmem⟩ := p₂ b D hD hf
    exact ⟨L, hL.mono (by omega) hord, h₂ b (by omega) hmem⟩
  have H : ∀ a, a ≤ B → D.IsFlawedInFreedom a → ∃ L : RootedLocation D.P.Γ,
      L.Isolates D.tb (B + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 := by
    intro a haB hf
    obtain ⟨L, hL, hmem⟩ := p₃ a D hD hf
    exact ⟨L, hL.mono (by omega) hord, h₃ a haB hmem⟩
  by_cases hrepT : D.rep < B + 1
  · -- `rep(𝒯)` is small, so (10.3) applies.
    obtain ⟨L, hL, hmem⟩ := p₁ D hD (Order.add_one_le_of_lt hrep |>.trans'
      (by norm_cast)) hord hrepT
      (two_mul_le_of_lt hdist (by omega))
    exact ⟨L, hL, h₁ hmem⟩
  have hrepB : B < D.rep := by omega
  rcases h152 (by omega) with ⟨r₁, h₁', r₂, h₂', hne, hle⟩ | ⟨F, hF, hcard, hbad⟩ | ⟨s, hs, hno⟩ |
    ⟨f, hf, hi, hno⟩
  · -- Two poles are close.
    exact G n (by omega) (by omega) ⟨by omega, two_mul_lt_of_lt hdist (by omega), r₁, h₁', r₂,
      h₂', hne, hle⟩
  · -- A short circuit includes a long side or many vertices of the frame.
    by_cases hclose : ∃ r₁ ∈ D.rad.poles, ∃ r₂ ∈ D.rad.poles, r₁ ≠ r₂ ∧ D.vDist r₁ r₂ ≤ (m + 1) * n
    · obtain ⟨r₁, h₁', r₂, h₂', hne, hle⟩ := hclose
      exact G ((m + 1) * n) (by omega) (by omega)
        ⟨by omega, two_mul_lt_of_lt hdist (by omega), r₁, h₁', r₂, h₂', hne, hle⟩
    · push Not at hclose
      exact H ((m + 1) * n) (by omega) ⟨by omega, hclose, F, hF, by omega, hbad⟩
  · -- A long side has no good edges. All edges of a list are distinct edges of `Γ₀`.
    have hlen : (ω s).length ≤ m := by
      obtain ⟨-, -, c, g, u₀, u₁, -, -, hg, -, -⟩ := hω s hs
      have hinj := hg.2.2.1
      have hmaps : ∀ i, g i ∈ P₀.Γ.E := fun i ↦ (hg.2.2.2.1 i).1
      have hcardg := Set.ncard_le_ncard (s := range g) (t := P₀.Γ.E)
        (by rintro _ ⟨i, rfl⟩; exact hmaps i) P₀.Γ.finite_edges
      rw [← image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ] at hcardg
      simpa using hcardg
    set a := ((ω s).length + 1) * (n / 2) with ha
    have ha₁ : a ≤ (m + 1) * n := Nat.mul_le_mul (by omega) (Nat.div_le_self _ _)
    have ha₂ : 1 ≤ a := Nat.mul_pos (by omega) (by omega)
    by_cases hfd : D.IsFlawedInDistance a
    · exact G a ha₂ (by omega) hfd
    by_cases hff : D.IsFlawedInFreedom a
    · exact H a (by omega) hff
    have hflaw : D.IsFlawedOnSide s (n / 2) (ω s) := by
      refine ⟨?_, two_mul_lt_of_lt hdist (by omega), hfd, hff, hno⟩
      have : 2 * ((ω s).length + 1) * (n / 2) = 2 * a := by rw [ha]; ring
      omega
    obtain ⟨L, hL, hmem⟩ := p₄ s hs D hD hflaw
    exact ⟨L, hL.mono (by omega) hord, h₄ hmem⟩
  · -- An internal edge of `Γ₀` has no far apart copies.
    by_cases hfd : D.IsFlawedInDistance B
    · exact G B (by omega) le_rfl hfd
    have hflaw : D.IsFlawedInternally m n (tilde f).ncard (P₀.φ f) := by
      refine ⟨?_, ?_, ?_, hno⟩
      · rw [← hB]
        exact hrepB
      · rw [← hB]
        exact two_mul_lt_of_lt hdist (by omega)
      · rwa [← hB]
    obtain ⟨L, hL, hmem⟩ := p₅ f hf hi D hD hflaw
    have hu : 5 ^ (2 * m + 2) * n = 25 * (5 ^ (2 * m) * n) := by rw [pow_add]; ring
    have hv : 4 * n * 5 ^ (2 * m) = 4 * (5 ^ (2 * m) * n) := by ring
    have hw : n ≤ 5 ^ (2 * m) * n := Nat.le_mul_of_pos_left _ (by positivity)
    exact ⟨L, hL.mono (by omega) hord, h₅ hmem⟩

/-- (4.1) for a disjoint colour scheme. -/
theorem not_orientedlyBad_of_disjoint
     [Infinite β] (hd : χ.IsDisjoint)
    (hS1 : ConditionS1.{0, w} Shat) (hS2 : ConditionS2 χ cap) (hS3 : ConditionS3 χ cap)
    (hS4 : ConditionS4 χ) : ¬ χ.IsOrientedlyBad := by
  classical
  rintro ⟨P, hbad, hsim⟩
  have rad : ∀ i, RadialDrawing cap (P i).Γ := fun i ↦
    ((P i).fits.internally_three_connected.nonempty_radialDrawing χ.isSurface cap).some
  -- "By 6.1 we may assume that for all `j > i ≥ 0` there is no inflation".
  obtain ⟨h₀, hno⟩ := theorem_6_1_proof cap χ hS1 hS3 P hbad hsim rad
  let Q : ℕ → ColouredPainting χ := fun i ↦ P (h₀ + i)
  have hbadQ : IsBadSequence χ Q := fun i j hij ↦ hbad _ _ (by omega)
  have hsimQ : IsSimilarlyOriented χ Q := hsim.imp id fun ⟨o, ho⟩ ↦ ⟨o, fun i ↦ ho _⟩
  let radQ : ∀ i, RadialDrawing cap (Q i).Γ := fun i ↦ rad _
  -- "Choose `n ≥ 4` and even such that 15.2 holds (for `(Γ₀, φ₀)`)."
  obtain ⟨n, hn, hEven, ω, hω, hn152⟩ := GraphMinor.GM19.theorem_15_2_proof.{w} S Shat β cap χ (Q 0)
  set B := 5 ^ (2 * (Q 0).Γ.E.ncard + 2) * n with hB
  -- "By 5.4 and 5.5, we may assume ... that `dist(Γ_i), rep(Γ_i) > 25n · 5^{2|E(Γ₀)|}`".
  obtain ⟨h₁, hh₁⟩ := GraphMinor.GM19.theorem_5_4_proof.{w} S Shat β cap χ hS3 Q hbadQ hsimQ radQ B
  obtain ⟨h₂, hh₂⟩ := GraphMinor.GM19.theorem_5_5_proof.{0, w} S Shat β cap χ hS1 hS3 Q hbadQ hsimQ
    radQ B
  let T : ℕ → ColouredPainting χ := fun i ↦ Q (max h₁ h₂ + 1 + i)
  let radT : ∀ i, RadialDrawing cap (T i).Γ := fun i ↦ radQ _
  have tb : ∀ i, TieBreaker (radT i) := fun i ↦ (nonempty_tieBreaker (radT i)).some
  -- The well-behaved set `𝒞`.
  let 𝒮 := imageClass P
  have hcl : IsPaintingClass χ 𝒮 := isPaintingClass_imageClass hsim
  have hmem : ∀ i, T i ∈ 𝒮 := fun i ↦ mem_imageClass P _
  obtain ⟨𝒞₁, w₁, p₁⟩ := GraphMinor.GM19.theorem_10_3_proof.{w} S Shat β cap χ hd 𝒮 hcl hS1 (B + 1)
    (by omega)
  choose 𝒞₂ w₂ p₂ using fun a : ℕ ↦ GraphMinor.GM19.theorem_10_4_proof.{w} S Shat β cap χ hd 𝒮 hcl
    hS3 (a + 1) (by omega)
  choose 𝒞₃ w₃ p₃ using fun a : ℕ ↦ GraphMinor.GM19.theorem_10_5_proof.{w} S Shat β cap χ hd 𝒮 hcl
    hS3 hS4 a
  have : Finite χ.Φ.longSides := χ.Φ.finite_longSides.to_subtype
  have hne : ∀ s ∈ χ.Φ.longSides, (ω s) ≠ [] := fun s hs ↦ (hω s hs).1
  choose 𝒞₄ w₄ p₄ using fun s : χ.Φ.longSides ↦ GraphMinor.GM19.theorem_11_1_proof.{w} S Shat β cap
    χ hd 𝒮 hcl hS4 s.1 s.2 (ω s)
    (hne s s.2) (hω s s.2).2.1 (n / 2) (by omega)
  have : Finite (Q 0).Γ.E := (Q 0).Γ.finite_edges.to_subtype
  have hsize : ∀ f : (Q 0).Γ.E, Painting.IsInternal f.1 →
      ((tilde f.1).ncard = 2 ∧ (Q 0).φ f.1 ∈ χ.Ω2.E) ∨
        ((tilde f.1).ncard = 3 ∧ (Q 0).φ f.1 ∈ χ.Ω3.E) := by
    intro f hi
    rcases (Q 0).Γ.edge_shape f.1 f.2 with h | h
    · exact Or.inl ⟨h.1, (Q 0).internal_2_mem f.1 f.2 hi h.1⟩
    · exact Or.inr ⟨h.1, (Q 0).internal_3_mem f.1 f.2 hi h.1⟩
  have hm : ∀ f : (Q 0).Γ.E, 1 ≤ (Q 0).Γ.E.ncard := fun f ↦
    (Set.ncard_pos (Q 0).Γ.finite_edges).2 ⟨f.1, f.2⟩
  have hfam : ∀ f : (Q 0).Γ.E, ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧
      (Painting.IsInternal f.1 → ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
        D.IsFlawedInternally (Q 0).Γ.E.ncard n (tilde f.1).ncard ((Q 0).φ f.1) →
        ∃ L : RootedLocation D.P.Γ,
          L.Isolates D.tb (4 * n * 5 ^ (2 * (Q 0).Γ.E.ncard) + 3) D.ord D.𝒯 ∧
          (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞) := by
    intro f
    by_cases hi : Painting.IsInternal f.1
    · obtain ⟨𝒞, hw, hp⟩ := GraphMinor.GM19.theorem_14_1_proof.{w} S Shat β cap χ hd 𝒮 hcl hS2 _ _
        (hsize f hi) (Q 0).Γ.E.ncard n
        (hm f) (by omega)
      exact ⟨𝒞, hw, fun _ ↦ hp⟩
    · refine ⟨∅, fun Ω _ seq hseq ↦ ?_, fun h ↦ absurd h hi⟩
      exact absurd (hseq 0) (notMem_empty _)
  choose 𝒞₅ w₅ p₅ using hfam
  let A₁ : Set (Place χ) := 𝒞₁
  let A₂ : Set (Place χ) := ⋃ a : Fin (B + 1), 𝒞₂ a
  let A₃ : Set (Place χ) := ⋃ a : Fin (B + 1), 𝒞₃ a
  let A₄ : Set (Place χ) := ⋃ s, 𝒞₄ s
  let A₅ : Set (Place χ) := ⋃ f, 𝒞₅ f
  have wA₂ : IsWellBehavedPlaces A₂ := IsWellBehavedPlaces.iUnion fun a : Fin (B + 1) ↦ @w₂ a.1
  have wA₃ : IsWellBehavedPlaces A₃ := IsWellBehavedPlaces.iUnion fun a : Fin (B + 1) ↦ @w₃ a.1
  have wA₄ : IsWellBehavedPlaces A₄ := IsWellBehavedPlaces.iUnion fun s ↦ @w₄ s
  have wA₅ : IsWellBehavedPlaces A₅ := IsWellBehavedPlaces.iUnion fun f ↦ @w₅ f
  have hwell : IsWellBehavedPlaces (A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅) :=
    IsWellBehavedPlaces.union (IsWellBehavedPlaces.union (IsWellBehavedPlaces.union
      (IsWellBehavedPlaces.union w₁ wA₂) wA₃) wA₄) wA₅
  -- "By 9.2 there exist `j > i ≥ 1` such that there is an inflation".
  obtain ⟨i, j, hij, σv, σe, hσ⟩ := theorem_9_2_proof hd T radT tb (θ := B + 1) (by omega) hwell (by
    intro i ord 𝒯 ht hθ
    let D : TangleDatum cap χ := ⟨T i, radT i, tb i, ord, 𝒯, ht⟩
    suffices hsuff : ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (B + 1) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ (A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅) by
      obtain ⟨L, hL, hm'⟩ := hsuff
      exact ⟨L, hm', hL⟩
    refine exists_isolating hd hn hω (𝒮 := 𝒮) hB p₁ p₂ p₃
      (𝒞₄ := A₄) (𝒞₅ := A₅)
      (fun s hs D hD hf ↦ ?_) (fun f hf hi D hD hfl ↦ ?_)
      (fun x hx ↦ Or.inl (Or.inl (Or.inl (Or.inl hx))))
      (fun a ha x hx ↦ Or.inl (Or.inl (Or.inl (Or.inr (show x ∈ A₂ from
        mem_iUnion.2 ⟨⟨a, Nat.lt_succ_of_le ha⟩, hx⟩)))))
      (fun a ha x hx ↦ Or.inl (Or.inl (Or.inr (show x ∈ A₃ from
        mem_iUnion.2 ⟨⟨a, Nat.lt_succ_of_le ha⟩, hx⟩))))
      (fun x hx ↦ Or.inl (Or.inr hx)) (fun x hx ↦ Or.inr hx) D (hmem i) ?_ ?_ hθ ?_
    · obtain ⟨L, hL, hm'⟩ := p₄ ⟨s, hs⟩ D hD hf
      exact ⟨L, hL, show _ ∈ A₄ from mem_iUnion.2 ⟨⟨s, hs⟩, hm'⟩⟩
    · obtain ⟨L, hL, hm'⟩ := p₅ ⟨f, hf⟩ hi D hD hfl
      exact ⟨L, hL, show _ ∈ A₅ from mem_iUnion.2 ⟨⟨f, hf⟩, hm'⟩⟩
    · exact hh₂ _ (by omega)
    · exact hh₁ _ (by omega)
    · intro hrep
      refine hn152 D ?_ ?_ hrep
      · rcases hsimQ with h | ⟨o, ho⟩
        · exact Or.inl h
        · refine Or.inr ⟨o, fun P' hP' ↦ ?_⟩
          rcases hP' with rfl | rfl
          · exact ho 0
          · exact ho _
      · exact hno _ (by omega) _ (by omega))
  exact hno _ (by omega) _ (by omega) ⟨σv, σe, hσ⟩

/-- **Graph Minors XIX, (4.1)** (page 333), in surface universe `0`. -/
private theorem theorem_4_1_zero
     : Theorem41Statement.{0, w} := by
  intro S Shat _ _ β _ cap χ hS1 hS2 hS3 hS4 hb
  have : T2Space S := χ.isSurface.2.1
  have : T2Space Shat := cap.isSurface.2.1
  obtain ⟨χ', hd, hS2', hS3', hS4', hb'⟩ := χ.exists_disjoint cap hS2 hS3 hS4 hb
  exact not_orientedlyBad_of_disjoint hd hS1 hS2' hS3' hS4'
    hb'

/-- **Graph Minors XIX, (4.1)** (page 333): "If $\chi$ satisfies $\mathbf{S}_1$--$\mathbf{S}_4$ then
it is not orientedly bad." -/
theorem theorem_4_1_proof : Theorem41Statement.{u, w} :=
  theorem_4_1_lift theorem_4_1_zero

end GraphMinor.GM19
