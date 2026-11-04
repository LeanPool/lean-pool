/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ApexPairCount
public import LeanPool.DistinctDistances.BisectorWitnessGeometry
public import LeanPool.DistinctDistances.BisectorWitnessInjective
public import LeanPool.DistinctDistances.PalettePairCounting
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Row J: the κ-image length gap in ordered-pair form

Formalizes part (ii) of Lemma J and row J of
`docs/results/explicit-constant-gain-1-40-2026-10-21.md` (§1–§2), in the count form used as
row 1 of `docs/results/short-chain-constant-gain-1-60-2026-10-21.md` (§3). Thresholds are
squared and in units of `ρ²`. Write `P(t)` for the number of ordered pairs of distinct points
at squared distance at most `t`, in the form `Σ_j (N_j(t) - 1)`, and `Q = 3D - n + 1`.

Let every point lie in the annulus `s²ρ² ≤ |p_i - c|² ≤ ρ²`, and let the parameters satisfy the
hypotheses of `bisector_witness_dist_sq_dichotomy`, with `g² ≤ G''`. Then

  `P(G'ρ²) - P(lρ²) - P(G''ρ²) ≤ 2nQ`.

Proof. An ordered pair `(a, b)` with `|ab|² > lρ²` either has a number of equidistant witnesses
`α ≠ 2`, so `α ≤ 1` by no three collinear points and these pairs number at most
`Σ (2 - α) ≤ 2nQ` (`sum_two_sub_witnesses_le`); or it has exactly two witnesses `w ≠ w'`. In
the second case the ordered witness pair `κ(a, b) = (w, w')`, oriented so that `a < b` exactly
when `w < w'`, is at squared distance at most `g²ρ² ≤ G''ρ²` or more than `G'ρ²`
(`bisector_witness_dist_sq_dichotomy`), and `κ` is injective
(`eq_or_swap_of_common_bisector_points` and the orientation). So the number of ordered pairs
with `lρ² < |ab|²`, minus the number with `G'ρ² < |ab|²`, is at most `P(G''ρ²) + 2nQ`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- For any threshold, the closed ball about a point has at most one point more than its
close-pair row. -/
private lemma closedBall_sq_card_le_closePairRow_card_add_one (p : Config n) (t : ℝ)
    (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card ≤
      (ClosePairRow p j t).card + 1 := by
  calc ((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card
      ≤ (insert j (ClosePairRow p j t)).card := by
        apply Finset.card_le_card
        intro q hq
        rw [Finset.mem_filter] at hq
        rw [Finset.mem_insert]
        by_cases hqj : q = j
        · exact Or.inl hqj
        · right
          simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Ne.symm hqj, hq.2⟩
    _ ≤ (ClosePairRow p j t).card + 1 := Finset.card_insert_le _ _

/-- For any threshold, `Σ_j (N_j(t) - 1)` is at most the number of ordered close pairs. -/
private lemma sum_closedBall_sq_card_sub_one_le_orderedClosePairs (p : Config n) (t : ℝ) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤
      ((OrderedClosePairs p t).card : ℝ) := by
  rw [orderedClosePairs_card_eq_sum_row, Nat.cast_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have h : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) ≤ ((ClosePairRow p j t).card : ℝ) + 1 := by
    exact_mod_cast closedBall_sq_card_le_closePairRow_card_add_one p t j
  linarith

/-- For a threshold `t ≥ 0`, `Σ_j (N_j(t) - 1)` is the number of ordered close pairs.
(The public `orderedClosePairs_card_eq_sum_closedBall_sq` of `Esgk.PalettePairCounting`,
stated in the other direction.) -/
private lemma sum_closedBall_sq_card_sub_one_eq_orderedClosePairs (p : Config n) {t : ℝ}
    (ht : 0 ≤ t) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) =
      ((OrderedClosePairs p t).card : ℝ) :=
  (orderedClosePairs_card_eq_sum_closedBall_sq p ht).symm

/-- Membership in the index-level witness set. -/
private lemma mem_indexedEquidistantWitnesses {p : Config n} {i j x : Fin n} :
    x ∈ IndexedEquidistantWitnesses p i j ↔ dist (p x) (p i) = dist (p x) (p j) := by
  simp [IndexedEquidistantWitnesses]

/-- The point of an index lies in the image finset of the configuration. -/
private lemma mem_toFinset (p : Config n) (i : Fin n) : p i ∈ Config.toFinset p :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The κ injection. The ordered pairs with `|ab|² > lρ²` and exactly two equidistant
witnesses are at most as many as the ordered pairs at squared distance at most `G''ρ²` or more
than `G'ρ²`. Each such pair is sent to its two witnesses, ordered like the pair. -/
private lemma card_far_two_witnesses_le {p : Config n} {c : Point} {ρ s l H G' G'' g u : ℝ}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) (hρ : 0 < ρ)
    (hlo : ∀ i, s ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hl : 0 < l) (hH : (1 - s ^ 2) ^ 2 ≤ 4 * l * H) (hG' : G' < 4 * (s ^ 2 - H))
    (hu0 : 0 ≤ u) (hu : u ^ 2 ≤ s ^ 2 - H) (hg0 : 0 ≤ g)
    (hg : 1 - s ^ 2 ≤ g ^ 2 + 2 * g * u) (hgG : g ^ 2 ≤ G'') :
    ((Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦
        l * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2 ∧
          (IndexedEquidistantWitnesses p ab.1 ab.2).card = 2)).card ≤
      ((Finset.univ : Finset (Fin n)).offDiag.filter (fun ww ↦
        dist (p ww.1) (p ww.2) ^ 2 ≤ G'' * ρ ^ 2 ∨
          G' * ρ ^ 2 < dist (p ww.1) (p ww.2) ^ 2)).card := by
  refine Finset.card_le_card_of_forall_subsingleton
    (fun ab ww ↦ IndexedEquidistantWitnesses p ab.1 ab.2 = {ww.1, ww.2} ∧ ww.1 ≠ ww.2 ∧
      (ab.1 < ab.2 ↔ ww.1 < ww.2)) ?_ ?_
  · -- Every such pair has an oriented witness pair in the target.
    intro ab hab
    rw [Finset.mem_filter] at hab
    obtain ⟨_, hfar, hW⟩ := hab
    obtain ⟨w, w', hww, hWeq⟩ := Finset.card_eq_two.mp hW
    have hw : dist (p w) (p ab.1) = dist (p w) (p ab.2) :=
      mem_indexedEquidistantWitnesses.mp (by rw [hWeq]; simp)
    have hw' : dist (p w') (p ab.1) = dist (p w') (p ab.2) :=
      mem_indexedEquidistantWitnesses.mp (by rw [hWeq]; simp)
    have hdich := bisector_witness_dist_sq_dichotomy hρ (hlo ab.1) (hhi ab.1) (hlo ab.2)
      (hhi ab.2) (hlo w) (hhi w) (hlo w') (hhi w') hl hH hfar hw hw' hG' hu0 hu hg0 hg
    have hgρ : g ^ 2 * ρ ^ 2 ≤ G'' * ρ ^ 2 := mul_le_mul_of_nonneg_right hgG (sq_nonneg ρ)
    have hdich' : dist (p w) (p w') ^ 2 ≤ G'' * ρ ^ 2 ∨
        G' * ρ ^ 2 < dist (p w) (p w') ^ 2 :=
      hdich.imp (fun h ↦ h.trans hgρ) id
    by_cases hor : (ab.1 < ab.2 ↔ w < w')
    · refine ⟨(w, w'), ?_, hWeq, hww, hor⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hww⟩, hdich'⟩
    · refine ⟨(w', w), ?_, by rw [hWeq, Finset.pair_comm], hww.symm, ?_⟩
      · refine Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hww.symm⟩, ?_⟩
        simpa only [dist_comm (p w') (p w)] using hdich'
      · have hlt : w' < w ↔ ¬w < w' :=
          ⟨fun h ↦ not_lt.mpr h.le, fun h ↦ lt_of_le_of_ne (not_lt.mp h) hww.symm⟩
        simp only [hlt]
        tauto
  · -- Two pairs with the same oriented witness pair are the same pair.
    intro ww _ ab hab ab' hab'
    obtain ⟨hab_mem, hW1, hne, hor1⟩ := hab
    obtain ⟨hab'_mem, hW2, _, hor2⟩ := hab'
    have hne1 : ab.1 ≠ ab.2 := (Finset.mem_offDiag.mp (Finset.mem_filter.mp hab_mem).1).2.2
    have hne2 : ab'.1 ≠ ab'.2 :=
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp hab'_mem).1).2.2
    have h1 : dist (p ww.1) (p ab.1) = dist (p ww.1) (p ab.2) :=
      mem_indexedEquidistantWitnesses.mp (by rw [hW1]; simp)
    have h2 : dist (p ww.2) (p ab.1) = dist (p ww.2) (p ab.2) :=
      mem_indexedEquidistantWitnesses.mp (by rw [hW1]; simp)
    have h3 : dist (p ww.1) (p ab'.1) = dist (p ww.1) (p ab'.2) :=
      mem_indexedEquidistantWitnesses.mp (by rw [hW2]; simp)
    have h4 : dist (p ww.2) (p ab'.1) = dist (p ww.2) (p ab'.2) :=
      mem_indexedEquidistantWitnesses.mp (by rw [hW2]; simp)
    rcases eq_or_swap_of_common_bisector_points hgp (mem_toFinset p ab.1) (mem_toFinset p ab.2)
        (mem_toFinset p ab'.1) (mem_toFinset p ab'.2) (hp.ne hne1) (hp.ne hne2) (hp.ne hne)
        h1 h2 h3 h4 with h | h
    · exact Prod.ext (hp h.1) (hp h.2)
    · exfalso
      have e1 : ab.1 = ab'.2 := hp h.1
      have e2 : ab.2 = ab'.1 := hp h.2
      rw [← e1, ← e2] at hor2
      rcases lt_or_gt_of_ne hne1 with hlt | hgt
      · exact lt_asymm hlt (hor2.mpr (hor1.mp hlt))
      · exact lt_asymm hgt (hor1.mpr (hor2.mp hgt))

/-- Row J of Theorem C60, the κ-image length gap in ordered-pair form. Let every point lie in
the annulus `s²ρ² ≤ |p_i - c|² ≤ ρ²`, with `(1 - s²)² ≤ 4lH`, `G' < 4(s² - H)`, `0 ≤ u`,
`u² ≤ s² - H`, `0 ≤ g`, `1 - s² ≤ g² + 2gu` and `g² ≤ G''`. Then, with `P(t)` the number of
ordered pairs of distinct points at squared distance at most `t` and `Q = 3D - n + 1`,
`P(G'ρ²) - P(lρ²) - P(G''ρ²) ≤ 2nQ`. -/
theorem sum_closedBall_sq_card_kappa_gap {p : Config n} {c : Point} {ρ s l H G' G'' g u : ℝ}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p)) (hρ : 0 < ρ)
    (hlo : ∀ i, s ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hl : 0 < l) (hH : (1 - s ^ 2) ^ 2 ≤ 4 * l * H) (hG' : G' < 4 * (s ^ 2 - H))
    (hu0 : 0 ≤ u) (hu : u ^ 2 ≤ s ^ 2 - H) (hg0 : 0 ≤ g)
    (hg : 1 - s ^ 2 ≤ g ^ 2 + 2 * g * u) (hgG : g ^ 2 ≤ G'') :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ G' * ρ ^ 2)).card : ℝ) - 1) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ l * ρ ^ 2)).card : ℝ) - 1) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ G'' * ρ ^ 2)).card : ℝ) - 1) ≤
      2 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by
  set O := (Finset.univ : Finset (Fin n)).offDiag with hO
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  -- Convert the three ball sums to ordered close-pair counts.
  have hPG' := sum_closedBall_sq_card_sub_one_le_orderedClosePairs p (G' * ρ ^ 2)
  have hPl := sum_closedBall_sq_card_sub_one_eq_orderedClosePairs p
    (mul_nonneg hl.le hρ2)
  have hPG'' := sum_closedBall_sq_card_sub_one_eq_orderedClosePairs p
    (mul_nonneg ((sq_nonneg g).trans hgG) hρ2)
  -- Complements of the close pairs at `lρ²` and at `G'ρ²`.
  have hsplit : ∀ t : ℝ, (OrderedClosePairs p t).card +
      (O.filter (fun ab ↦ t < dist (p ab.1) (p ab.2) ^ 2)).card = O.card := by
    intro t
    have h := Finset.card_filter_add_card_filter_not (s := O)
      (fun ab ↦ dist (p ab.1) (p ab.2) ^ 2 ≤ t)
    simp only [not_le] at h
    exact h
  have hl_split := hsplit (l * ρ ^ 2)
  have hG'_split := hsplit (G' * ρ ^ 2)
  -- The far pairs split by the number of witnesses.
  have hfar : (O.filter (fun ab ↦ l * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2)).card ≤
      (O.filter (fun ab ↦ l * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2 ∧
          (IndexedEquidistantWitnesses p ab.1 ab.2).card = 2)).card +
        (O.filter (fun ab ↦ (IndexedEquidistantWitnesses p ab.1 ab.2).card ≠ 2)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro ab hab
    rw [Finset.mem_filter] at hab
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hW : (IndexedEquidistantWitnesses p ab.1 ab.2).card = 2
    · exact Or.inl ⟨hab.1, hab.2, hW⟩
    · exact Or.inr ⟨hab.1, hW⟩
  -- Pairs with exactly two witnesses: the κ injection.
  have hgood := card_far_two_witnesses_le hp hgp hρ hlo hhi hl hH hG' hu0 hu hg0 hg hgG
  have htarget : (O.filter (fun ww ↦ dist (p ww.1) (p ww.2) ^ 2 ≤ G'' * ρ ^ 2 ∨
        G' * ρ ^ 2 < dist (p ww.1) (p ww.2) ^ 2)).card ≤
      (OrderedClosePairs p (G'' * ρ ^ 2)).card +
        (O.filter (fun ab ↦ G' * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2)).card := by
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  -- Pairs without exactly two witnesses: the witness deficiency.
  have hbad : ((O.filter (fun ab ↦
      (IndexedEquidistantWitnesses p ab.1 ab.2).card ≠ 2)).card : ℝ) ≤
      2 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by
    set B := O.filter (fun ab ↦ (IndexedEquidistantWitnesses p ab.1 ab.2).card ≠ 2) with hB
    have hBsub : B ⊆ O := Finset.filter_subset _ _
    refine le_trans ?_ (sum_two_sub_witnesses_le hp hgp.1 hBsub)
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_le_sum fun ab hab ↦ ?_
    rw [hB, Finset.mem_filter] at hab
    have hle := indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp.1
      (Finset.mem_offDiag.mp hab.1).2.2
    have hle1 : (IndexedEquidistantWitnesses p ab.1 ab.2).card ≤ 1 := by omega
    have hle1' : ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤ 1 := by
      exact_mod_cast hle1
    linarith
  -- Combine.
  have hl_split' : ((OrderedClosePairs p (l * ρ ^ 2)).card : ℝ) +
      ((O.filter (fun ab ↦ l * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2)).card : ℝ) =
        (O.card : ℝ) := by exact_mod_cast hl_split
  have hG'_split' : ((OrderedClosePairs p (G' * ρ ^ 2)).card : ℝ) +
      ((O.filter (fun ab ↦ G' * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2)).card : ℝ) =
        (O.card : ℝ) := by exact_mod_cast hG'_split
  have hfar' := (Nat.cast_le (α := ℝ)).mpr hfar
  have hgood' := (Nat.cast_le (α := ℝ)).mpr hgood
  have htarget' := (Nat.cast_le (α := ℝ)).mpr htarget
  push_cast at hfar' htarget'
  rw [hPl, hPG'']
  linarith

end Esgk
