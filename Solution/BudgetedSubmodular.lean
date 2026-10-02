/-
Copyright (c) 2026 deadczarvc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: deadczarvc
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Solution: Modified greedy for budgeted monotone submodular maximisation

Challenge: `budgeted-submodular-modified-greedy` (`Challenge.BudgetedSubmodular`)
Proves: `Challenge.BudgetedSubmodular.modifiedGreedy_approx`
Solved by: deadczarvc

This module restates the challenge statement under its own name and proves it. It must not import
the challenge module: comparator exports both environments separately and checks that the statements
agree, which is what makes the verdict independent of the statement file.
-/

/-!
## Proof outline (Khuller, Moss and Naor)

1. If the optimum `O` lies inside the greedy set, monotonicity finishes.
2. Otherwise let `l` be the first step at which the best item `y` of `O` outside the greedy
   set (by marginal gain per unit cost) no longer fits the budget. Before `l`, every greedy pick
   has gain per cost at least that of every item of `O`, and submodularity gives
   `F O - F G' ≤ (1 - c x / B) * (F O - F G) ≤ exp (-c x / B) * (F O - F G)`, so after the
   prefix `F O - F G_l ≤ exp (-c(G_l) / B) * F O`.
3. One virtual step with `y` costs more than `B` in total, so
   `F O - F (insert y G_l) ≤ exp (-1) * F O`.
4. Submodularity splits the virtual set: `F (insert y G_l) ≤ F G_l + F {y}`, where `F G_l` is at
   most the greedy value and `F {y}` at most the best single item. Hence `(1 - 1/e) * F O` is at
   most their sum, and the larger of the two is at least half of it.
-/

public section

namespace Challenge.BudgetedSubmodular

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A monotone set function with diminishing returns (submodular). -/
structure MonoSubmodular (F : Finset ι → ℝ) : Prop where
  mono : ∀ {S U : Finset ι}, S ⊆ U → F S ≤ F U
  dr : ∀ {S U : Finset ι}, S ⊆ U → ∀ x, F (insert x U) - F U ≤ F (insert x S) - F S

/-- The items of `U` outside `G` that still fit the budget `B` next to `G`. -/
noncomputable def fits (c : ι → ℝ) (B : ℝ) (U G : Finset ι) : Finset ι :=
  (U \ G).filter fun x => ∑ y ∈ G, c y + c x ≤ B

/-- When some item fits, one of them has the largest gain per unit cost. A named theorem rather
than a proof inside `greedyStep`: Lean moves a nested proof into a private auxiliary lemma whose
name carries the module, which no solution module could reproduce. -/
theorem exists_best (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U G : Finset ι)
    (h : (fits c B U G).Nonempty) :
    ∃ x ∈ fits c B U G, ∀ y ∈ fits c B U G,
      (F (insert y G) - F G) / c y ≤ (F (insert x G) - F G) / c x :=
  (fits c B U G).exists_max_image _ h

/-- One greedy step: add an item of `fits` with the largest gain per unit cost (ties broken
arbitrarily); keep `G` when nothing fits. -/
noncomputable def greedyStep (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U G : Finset ι) :
    Finset ι :=
  if h : (fits c B U G).Nonempty then insert (Classical.choose (exists_best F c B U G h)) G
  else G

/-- The greedy run on the ground set `U`: `U.card` steps from the empty set. -/
noncomputable def greedy (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U : Finset ι) : Finset ι :=
  (greedyStep F c B U)^[U.card] ∅

/-- The best value of a single item of `U` that fits the budget (`0` when none fits). -/
noncomputable def bestSingle (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U : Finset ι) : ℝ :=
  if h : (U.filter fun x => c x ≤ B).Nonempty then
    (U.filter fun x => c x ≤ B).sup' h fun x => F {x}
  else 0

section Proof

variable {F : Finset ι → ℝ} {c : ι → ℝ} {B : ℝ} {U : Finset ι}

/-- Gain per unit cost of adding `x` to `G`. -/
private noncomputable def ratio (F : Finset ι → ℝ) (c : ι → ℝ) (G : Finset ι) (x : ι) : ℝ :=
  (F (insert x G) - F G) / c x

private lemma ratio_nonneg (hF : MonoSubmodular F) (hc : ∀ i, 0 < c i) (G : Finset ι) (x : ι) :
    0 ≤ ratio F c G x :=
  div_nonneg (sub_nonneg.2 (hF.mono (subset_insert x G))) (hc x).le

private lemma ratio_of_mem {G : Finset ι} {x : ι} (hx : x ∈ G) : ratio F c G x = 0 := by
  simp [ratio, insert_eq_of_mem hx]

/-- The greedy pick when something fits: it fits and has the best ratio among what fits. -/
private lemma step_pos {G : Finset ι} (h : (fits c B U G).Nonempty) :
    ∃ x ∈ fits c B U G, (∀ z ∈ fits c B U G, ratio F c G z ≤ ratio F c G x) ∧
      greedyStep F c B U G = insert x G := by
  have hs := Classical.choose_spec
    ((fits c B U G).exists_max_image (fun x => (F (insert x G) - F G) / c x) h)
  exact ⟨_, hs.1, fun z hz => hs.2 z hz, by simp [greedyStep, h]⟩

private lemma step_neg {G : Finset ι} (h : ¬ (fits c B U G).Nonempty) :
    greedyStep F c B U G = G := by
  simp [greedyStep, h]

private lemma mem_fits {G : Finset ι} {x : ι} :
    x ∈ fits c B U G ↔ x ∈ U ∧ x ∉ G ∧ ∑ y ∈ G, c y + c x ≤ B := by
  simp [fits, and_assoc]

private lemma subset_step (G : Finset ι) : G ⊆ greedyStep F c B U G := by
  by_cases h : (fits c B U G).Nonempty
  · obtain ⟨x, -, -, hx⟩ := step_pos (F := F) h
    rw [hx]; exact subset_insert x G
  · rw [step_neg h]

/-- The greedy after `k` steps. -/
private noncomputable def run (F : Finset ι → ℝ) (c : ι → ℝ) (B : ℝ) (U : Finset ι) (k : ℕ) :
    Finset ι :=
  (greedyStep F c B U)^[k] ∅

private lemma run_succ (k : ℕ) : run F c B U (k + 1) = greedyStep F c B U (run F c B U k) := by
  simp [run, Function.iterate_succ_apply']

private lemma run_mono {j k : ℕ} (hjk : j ≤ k) : run F c B U j ⊆ run F c B U k := by
  induction hjk with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans (by rw [run_succ]; exact subset_step _)

private lemma run_sub (k : ℕ) : run F c B U k ⊆ U := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [run_succ]
    by_cases h : (fits c B U (run F c B U k)).Nonempty
    · obtain ⟨x, hx, -, he⟩ := step_pos (F := F) h
      rw [he]; exact insert_subset (mem_fits.1 hx).1 ih
    · rw [step_neg h]; exact ih

/-- Once nothing fits, the greedy stays put. -/
private lemma run_stable {k : ℕ} (h : ¬ (fits c B U (run F c B U k)).Nonempty) (m : ℕ) :
    run F c B U (k + m) = run F c B U k := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, run_succ, ih, step_neg h]

/-- After `U.card` steps nothing fits any more. -/
private lemma run_done : ¬ (fits c B U (run F c B U U.card)).Nonempty := by
  intro hN
  have hcard : ∀ k ≤ U.card, (run F c B U k).card = k := by
    intro k hk
    induction k with
    | zero => simp [run]
    | succ k ih =>
      have hk' : k ≤ U.card := Nat.le_of_succ_le hk
      by_cases h : (fits c B U (run F c B U k)).Nonempty
      · obtain ⟨x, hx, -, he⟩ := step_pos (F := F) h
        rw [run_succ, he, card_insert_of_notMem (mem_fits.1 hx).2.1, ih hk']
      · exfalso
        have := run_stable (F := F) h (U.card - k)
        rw [Nat.add_sub_cancel' hk'] at this
        exact h (this ▸ hN)
  have hU : run F c B U U.card = U :=
    eq_of_subset_of_card_le (run_sub _) (by rw [hcard _ le_rfl])
  obtain ⟨x, hx⟩ := hN
  exact (mem_fits.1 hx).2.1 (by rw [hU]; exact (mem_fits.1 hx).1)

private lemma greedy_eq : greedy F c B U = run F c B U U.card := rfl

/-- Adding a whole set gains at most the sum of the single gains. -/
private lemma union_le (hF : MonoSubmodular F) (S O : Finset ι) :
    F (S ∪ O) ≤ F S + ∑ y ∈ O, (F (insert y S) - F S) := by
  induction O using Finset.induction_on with
  | empty => simp
  | insert a O ha ih =>
    rw [union_insert, sum_insert ha]
    have h1 := hF.dr (subset_union_left : S ⊆ S ∪ O) a
    linarith

/-- One step against the optimum: a pick whose ratio beats every item of `O` closes `c x / B`
of the gap. -/
private lemma step_bound (hF : MonoSubmodular F) (hc : ∀ i, 0 < c i) (hB : 0 < B) (G O : Finset ι)
    (hO : ∑ y ∈ O, c y ≤ B) (x : ι) (hx : ∀ y ∈ O, ratio F c G y ≤ ratio F c G x) :
    c x / B * (F O - F G) ≤ F (insert x G) - F G := by
  set r := ratio F c G x with hr_def
  have hgain : ∀ y ∈ O, F (insert y G) - F G ≤ r * c y := fun y hy => by
    have := hx y hy
    rwa [ratio, div_le_iff₀ (hc y)] at this
  have h1 : F O ≤ F (G ∪ O) := hF.mono subset_union_right
  have h2 := union_le hF G O
  have h3 : ∑ y ∈ O, (F (insert y G) - F G) ≤ r * ∑ y ∈ O, c y := by
    rw [mul_sum]; exact sum_le_sum hgain
  have hr : 0 ≤ r := ratio_nonneg hF hc G x
  have h4 : r * ∑ y ∈ O, c y ≤ r * B := mul_le_mul_of_nonneg_left hO hr
  have h5 : F O - F G ≤ r * B := by linarith
  have h6 : c x / B * (F O - F G) ≤ c x / B * (r * B) :=
    mul_le_mul_of_nonneg_left h5 (div_nonneg (hc x).le hB.le)
  have h7 : c x / B * (r * B) = F (insert x G) - F G := by
    rw [hr_def, ratio]; field_simp [(hc x).ne', hB.ne']
  linarith

/-- The gap after one step that closes `t` of it, with `0 ≤ t`. -/
private lemma gap_step {gap gap' E t opt : ℝ} (hstep : gap' ≤ (1 - t) * gap) (ht : t ≤ 1)
    (hgap : gap ≤ E * opt) (hE : 0 ≤ E * opt) : gap' ≤ Real.exp (-t) * (E * opt) := by
  have h1 : (1 - t) * gap ≤ (1 - t) * (E * opt) := mul_le_mul_of_nonneg_left hgap (by linarith)
  have h2 : (1 - t) * (E * opt) ≤ Real.exp (-t) * (E * opt) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-t)]) hE
  linarith

end Proof

/-- The modified greedy guarantee `(1 - 1/e)/2` (Khuller–Moss–Naor 1999; see Tang et al. 2021,
who prove `0.405` for the same algorithm). -/
theorem modifiedGreedy_approx (F : Finset ι → ℝ) (hF : MonoSubmodular F) (hF0 : F ∅ = 0)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (B : ℝ) (U O : Finset ι) (hOU : O ⊆ U)
    (hOB : ∑ y ∈ O, c y ≤ B) :
    (1 - Real.exp (-1)) / 2 * F O ≤ max (F (greedy F c B U)) (bestSingle F c B U) := by
  classical
  have hopt : 0 ≤ F O := hF0 ▸ hF.mono (empty_subset O)
  have hexp1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hexp0 : 0 < Real.exp (-1) := Real.exp_pos _
  rw [greedy_eq]
  -- the optimum inside the greedy set: done
  by_cases hsub : O ⊆ run F c B U U.card
  · have h1 := hF.mono hsub
    have h2 : (1 - Real.exp (-1)) / 2 * F O ≤ F O := by nlinarith
    exact (h2.trans h1).trans (le_max_left _ _)
  have hB : 0 < B := by
    obtain ⟨y, hy⟩ : O.Nonempty := by
      rcases O.eq_empty_or_nonempty with h | h
      · exact absurd (h ▸ empty_subset _) hsub
      · exact h
    linarith [hc y, single_le_sum (fun i _ => (hc i).le) hy (f := c)]
  -- Q j: the best item of O outside the greedy set after j steps does not fit
  let Q : ℕ → Prop := fun j => ∃ y ∈ O \ run F c B U j,
    (∀ z ∈ O \ run F c B U j, ratio F c (run F c B U j) z ≤ ratio F c (run F c B U j) y) ∧
      B < ∑ x ∈ run F c B U j, c x + c y
  have hQN : Q U.card := by
    obtain ⟨y, hy, hmax⟩ := (O \ run F c B U U.card).exists_max_image
      (ratio F c (run F c B U U.card)) (sdiff_nonempty.2 hsub)
    refine ⟨y, hy, hmax, ?_⟩
    by_contra hle
    push Not at hle
    exact run_done (F := F) ⟨y, mem_fits.2 ⟨hOU (mem_sdiff.1 hy).1, (mem_sdiff.1 hy).2, hle⟩⟩
  have hex : ∃ j, Q j := ⟨_, hQN⟩
  set l := Nat.find hex with hl_def
  have hl : Q l := Nat.find_spec hex
  have hlN : l ≤ U.card := Nat.find_min' hex hQN
  have hbefore : ∀ j < l, ¬ Q j := fun j hj => Nat.find_min hex hj
  -- until l, every greedy pick beats every item of O: the gap shrinks by exp (-cost / B)
  have inv : ∀ j ≤ l, F O - F (run F c B U j) ≤
      Real.exp (-(∑ x ∈ run F c B U j, c x) / B) * F O := by
    intro j hj
    induction j with
    | zero => simp [run, hF0]
    | succ j ih =>
      have hjl : j < l := hj
      have ihj := ih hjl.le
      have hnq := hbefore j hjl
      by_cases hfit : (fits c B U (run F c B U j)).Nonempty
      · obtain ⟨x, hx, hxmax, hstep⟩ := step_pos (F := F) hfit
        have hxm := mem_fits.1 hx
        have hdom : ∀ y ∈ O, ratio F c (run F c B U j) y ≤ ratio F c (run F c B U j) x := by
          intro y hy
          by_cases hyG : y ∈ run F c B U j
          · rw [ratio_of_mem hyG]; exact ratio_nonneg hF hc _ _
          · obtain ⟨y', hy', hmax'⟩ := (O \ run F c B U j).exists_max_image
              (ratio F c (run F c B U j)) ⟨y, mem_sdiff.2 ⟨hy, hyG⟩⟩
            have hfit' : ∑ z ∈ run F c B U j, c z + c y' ≤ B := by
              by_contra h
              push Not at h
              exact hnq ⟨y', hy', hmax', h⟩
            have hy'f : y' ∈ fits c B U (run F c B U j) :=
              mem_fits.2 ⟨hOU (mem_sdiff.1 hy').1, (mem_sdiff.1 hy').2, hfit'⟩
            exact (hmax' y (mem_sdiff.2 ⟨hy, hyG⟩)).trans (hxmax y' hy'f)
        have hsb := step_bound hF hc hB _ O hOB x hdom
        have hcx : c x ≤ B := by
          have : 0 ≤ ∑ z ∈ run F c B U j, c z := sum_nonneg fun i _ => (hc i).le
          linarith [hxm.2.2]
        rw [run_succ, hstep, sum_insert hxm.2.1]
        have hE : 0 ≤ Real.exp (-(∑ z ∈ run F c B U j, c z) / B) * F O :=
          mul_nonneg (Real.exp_pos _).le hopt
        have hlin : F O - F (insert x (run F c B U j)) ≤
            (1 - c x / B) * (F O - F (run F c B U j)) := by
          have : (1 - c x / B) * (F O - F (run F c B U j)) =
              (F O - F (run F c B U j)) - c x / B * (F O - F (run F c B U j)) := by ring
          linarith
        have h := gap_step hlin (by rw [div_le_one hB]; exact hcx) ihj hE
        calc F O - F (insert x (run F c B U j))
            ≤ Real.exp (-(c x / B)) * (Real.exp (-(∑ z ∈ run F c B U j, c z) / B) * F O) := h
          _ = Real.exp (-(c x + ∑ z ∈ run F c B U j, c z) / B) * F O := by
            rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
      · rw [run_succ, step_neg hfit]
        exact ihj
  -- a virtual step with the best item of O at l pushes the cost past B
  obtain ⟨y, hy, hmax, hover⟩ := hl
  have hym := mem_sdiff.1 hy
  have hdom : ∀ z ∈ O, ratio F c (run F c B U l) z ≤ ratio F c (run F c B U l) y := by
    intro z hz
    by_cases hzG : z ∈ run F c B U l
    · rw [ratio_of_mem hzG]; exact ratio_nonneg hF hc _ _
    · exact hmax z (mem_sdiff.2 ⟨hz, hzG⟩)
  have hsb := step_bound hF hc hB _ O hOB y hdom
  have hcy : c y ≤ B := (single_le_sum (fun i _ => (hc i).le) hym.1).trans hOB
  have hE : 0 ≤ Real.exp (-(∑ z ∈ run F c B U l, c z) / B) * F O :=
    mul_nonneg (Real.exp_pos _).le hopt
  have hlin : F O - F (insert y (run F c B U l)) ≤ (1 - c y / B) * (F O - F (run F c B U l)) := by
    have : (1 - c y / B) * (F O - F (run F c B U l)) =
        (F O - F (run F c B U l)) - c y / B * (F O - F (run F c B U l)) := by ring
    linarith
  have hvirt := gap_step hlin (by rw [div_le_one hB]; exact hcy) (inv l le_rfl) hE
  have hcost : Real.exp (-(c y / B)) * (Real.exp (-(∑ z ∈ run F c B U l, c z) / B) * F O) ≤
      Real.exp (-1) * F O := by
    rw [← mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ hopt
    apply Real.exp_le_exp.2
    have h1 : 1 < (∑ z ∈ run F c B U l, c z + c y) / B := (one_lt_div hB).2 hover
    have h2 : -(c y / B) + -(∑ z ∈ run F c B U l, c z) / B =
        -((∑ z ∈ run F c B U l, c z + c y) / B) := by ring
    linarith
  -- submodularity splits the virtual set into the greedy prefix and one item
  have hsplit : F (insert y (run F c B U l)) ≤ F (run F c B U l) + F {y} := by
    have := hF.dr (empty_subset (run F c B U l)) y
    simp only [insert_empty, hF0] at this
    linarith
  have hGl : F (run F c B U l) ≤ F (run F c B U U.card) := hF.mono (run_mono hlN)
  have hsingle : F {y} ≤ bestSingle F c B U := by
    have hmem : y ∈ U.filter fun x => c x ≤ B := mem_filter.2 ⟨hOU hym.1, hcy⟩
    rw [bestSingle, dite_eq_left_of_eq_true (eq_true ⟨y, hmem⟩)]
    exact le_sup' (fun x => F {x}) hmem
  have hsum : (1 - Real.exp (-1)) * F O ≤ F (run F c B U U.card) + bestSingle F c B U := by
    linarith
  have h2 := le_max_left (F (run F c B U U.card)) (bestSingle F c B U)
  have h3 := le_max_right (F (run F c B U U.card)) (bestSingle F c B U)
  linarith



end Challenge.BudgetedSubmodular
