/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Positivity
public import LeanPool.AaronsonAmbainis.RowDefs
public import LeanPool.AaronsonAmbainis.Bridge.Positivity

/-!
# The two-sided inequality, the determinant inequality and the packing bound

The propositions `TwoSidedInequality`, `DetInequality` and `PackingBound` are compared with the
statements of the paper and with two further forms:

* `twoSided_iff_printed : TwoSidedInequality ↔ TwoSidedPrinted` — the two-sided inequality as
  stated in the introduction of the paper (it is the inequality of Theorem 5.4): non-constant
  `g`, any choice of rows, expectations over the whole cube and `max_j I_j(g)`;
* `twoSidedMinCost_of_twoSided : TwoSidedInequality → TwoSidedMinCost` — the same inequality
  with the least cost of a row of `g` at `x` in place of `‖λ^x‖` (the paper does not state this
  form);
* `detInequality_iff_printed : DetInequality ↔ DetInequalityPrinted` — the determinant
  inequality as stated in the paper (Corollary 3.2), with the true minimum `D_g(u, A_u; ℓ)` (a
  value that is attained and is a lower bound) in place of "every lower bound `d u`"; the proof
  uses that the family of the minimum is non-empty;
* `packingBound_iff_nonempty : PackingBound ↔ PackingBoundNonempty` — the packing bound
  (Lemma 6.5) with `κ` constrained and summed over non-empty sets only (in the paper, as in
  `PackingBound`, the family `κ` is indexed by all subsets).

Nothing here says that any of these statements holds. The propositions are proved in
`Chain.lean` (`twoSidedInequality`, `packingBound`) and `DetTheorem.lean` (`detInequality`).
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem infl_nonneg (g : Cube ι → Bool) (j : ι) : 0 ≤ infl g j := by
  unfold infl
  positivity

/-! ### The two-sided inequality (Theorem 5.4) -/

/-- The two-sided inequality as stated in the introduction of the paper (it is the inequality of
Theorem 5.4): if `g` is a non-constant Boolean function and `λ^x` is a row of `g` at `x` for
every `x`, then `4 E_x[1_{g(x)=1} / ‖λ^x‖] E_x[1_{g(x)=0} / ‖λ^x‖] ≤ max_j I_j(g)`.
(`Nonempty ι` is needed to write the maximum; it follows from `g` being non-constant.) -/
def TwoSidedPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (g : Cube ι → Bool),
    (∃ x y, g x ≠ g y) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    4 * ((∑ x : Cube ι, if g x = true then 1 / (∑ j, lam x j) else 0) / 2 ^ Fintype.card ι)
      * ((∑ x : Cube ι, if g x = false then 1 / (∑ j, lam x j) else 0) / 2 ^ Fintype.card ι)
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => infl g j)

theorem twoSided_iff_printed : TwoSidedInequality ↔ TwoSidedPrinted := by
  constructor
  · intro h ι _ _ hne g _ lam hrow
    have hτ0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => infl g j) := by
      obtain ⟨j⟩ := hne
      exact (infl_nonneg g j).trans (Finset.le_sup' (fun j => infl g j) (Finset.mem_univ j))
    have h1 := h ι g lam hrow _ hτ0
      (fun j => Finset.le_sup' (fun j => infl g j) (Finset.mem_univ j))
    rw [Finset.sum_filter, Finset.sum_filter] at h1
    simp only [one_div]
    exact h1
  · intro h ι _ _ g lam hrow τ hτ hinfl
    by_cases hnc : ∃ x y, g x ≠ g y
    · obtain ⟨x, y, hxy⟩ := hnc
      have : Nonempty ι := nonempty_of_ne hxy
      have h1 := h ι g ⟨x, y, hxy⟩ lam hrow
      simp only [one_div] at h1
      rw [Finset.sum_filter, Finset.sum_filter]
      exact h1.trans ((Finset.sup'_le_iff _ _).mpr (fun j _ => hinfl j))
    · have hconst : ∀ x y, g x = g y := by
        intro x y
        by_contra hxy
        exact hnc ⟨x, y, hxy⟩
      have hz : (∑ x ∈ univ.filter (fun x : Cube ι => g x = true), (∑ j, lam x j)⁻¹) = 0 ∨
          (∑ x ∈ univ.filter (fun x : Cube ι => g x = false), (∑ j, lam x j)⁻¹) = 0 := by
        cases h0 : g (fun _ => false)
        · left
          apply Finset.sum_eq_zero
          intro x hx
          exfalso
          have hx' : g x = true := (Finset.mem_filter.mp hx).2
          rw [hconst x (fun _ => false), h0] at hx'
          exact Bool.noConfusion hx'
        · right
          apply Finset.sum_eq_zero
          intro x hx
          exfalso
          have hx' : g x = false := (Finset.mem_filter.mp hx).2
          rw [hconst x (fun _ => false), h0] at hx'
          exact Bool.noConfusion hx'
      rcases hz with hz | hz
      · rw [hz, zero_div, mul_zero, zero_mul]
        exact hτ
      · rw [hz, zero_div, mul_zero]
        exact hτ

/-- The two-sided inequality with the least cost of a row at each point: for non-constant `g`,
`4 E_x[1_{g(x)=1} / F(x)] E_x[1_{g(x)=0} / F(x)] ≤ max_j I_j(g)`, where `F x` is the minimum of
`‖λ‖` over the rows `λ` of `g` at `x`: a value that is attained by a row at `x` and is a lower
bound for all rows at `x`. The paper does not state this form. -/
def TwoSidedMinCost : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (g : Cube ι → Bool),
    (∃ x y, g x ≠ g y) →
  ∀ (F : Cube ι → ℝ),
    (∀ x, (∃ lam : ι → ℝ, IsRow g x lam ∧ ∑ j, lam j = F x) ∧
      ∀ lam : ι → ℝ, IsRow g x lam → F x ≤ ∑ j, lam j) →
    4 * ((∑ x : Cube ι, if g x = true then 1 / F x else 0) / 2 ^ Fintype.card ι)
      * ((∑ x : Cube ι, if g x = false then 1 / F x else 0) / 2 ^ Fintype.card ι)
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => infl g j)

/-- `TwoSidedInequality` gives the form with the least cost as well (take rows of least cost). The
converse would need the existence of a row of least cost (compactness); it is not formalised
here. -/
theorem twoSidedMinCost_of_twoSided (h : TwoSidedInequality) : TwoSidedMinCost := by
  intro ι _ _ _ g hnc F hF
  choose lam hrow hval using fun x => (hF x).1
  have h1 := twoSided_iff_printed.mp h ι g hnc lam hrow
  simp only [hval] at h1
  exact h1

/-! ### The determinant inequality (Corollary 3.2) -/

theorem flipSet_antipode_sdiff (u : Cube ι) (A : Finset ι) :
    flipSet (antipode u) (univ \ A) = flipSet u A := by
  funext i
  by_cases h : i ∈ A <;> simp [flipSet, antipode, h]

/-- The determinant inequality as stated in the paper (Corollary 3.2): for every Boolean function
`g`, every `ℓ ∈ (0,∞)^n` and every choice of a 1-wing `A_u` of `g` at each `u ∈ Z(g)`,
`∑_{u ∈ Z(g)} D_g(u, A_u; ℓ) ≤ ∑_j ℓ_j b_j(g)`, where
`D_g(u, A; ℓ) := min {ℓ(G) : G ⊆ [n] ∖ A, g(ū^G) = 1}`. Here `D u` is that minimum: a value
that is attained in the family and is a lower bound of it. -/
def DetInequalityPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (ℓ : ι → ℝ), (∀ j, 0 < ℓ j) →
  ∀ (A : Cube ι → Finset ι), (∀ u ∈ zone g, IsWing g u (A u)) →
  ∀ (D : Cube ι → ℝ),
    (∀ u ∈ zone g,
      (∃ G : Finset ι, G ⊆ univ \ A u ∧ g (flipSet (antipode u) G) = true ∧
          D u = ∑ j ∈ G, ℓ j) ∧
      ∀ G : Finset ι, G ⊆ univ \ A u → g (flipSet (antipode u) G) = true →
          D u ≤ ∑ j ∈ G, ℓ j) →
    ∑ u ∈ zone g, D u ≤ ∑ j, ℓ j * (bdry g j : ℝ)

theorem detInequality_iff_printed : DetInequality ↔ DetInequalityPrinted := by
  constructor
  · intro h ι _ _ g ℓ hℓ A hA D hD
    apply h ι g ℓ hℓ A hA D
    intro u hu G hGA hG
    exact (hD u hu).2 G (Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, hGA⟩) hG
  · intro h ι _ _ g ℓ hℓ A hA d hd
    -- the minimum exists at every point of the zone: the family is non-empty
    have key : ∀ u : Cube ι, ∃ D0 : ℝ, u ∈ zone g →
        ((∃ G : Finset ι, G ⊆ univ \ A u ∧ g (flipSet (antipode u) G) = true ∧
            D0 = ∑ j ∈ G, ℓ j) ∧
          ∀ G : Finset ι, G ⊆ univ \ A u → g (flipSet (antipode u) G) = true →
            D0 ≤ ∑ j ∈ G, ℓ j) := by
      intro u
      by_cases hu : u ∈ zone g
      · have hne : (univ.filter fun G : Finset ι =>
            G ⊆ univ \ A u ∧ g (flipSet (antipode u) G) = true).Nonempty := by
          refine ⟨univ \ A u, ?_⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, Finset.Subset.refl _, ?_⟩
          rw [flipSet_antipode_sdiff]
          exact hA u hu (A u) (Finset.Subset.refl _)
        obtain ⟨G0, hG0, hmin⟩ :=
          Finset.exists_min_image _ (fun G : Finset ι => ∑ j ∈ G, ℓ j) hne
        rw [Finset.mem_filter] at hG0
        refine ⟨∑ j ∈ G0, ℓ j, fun _ => ⟨⟨G0, hG0.2.1, hG0.2.2, rfl⟩, fun G hGA hG => ?_⟩⟩
        exact hmin G (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGA, hG⟩)
      · exact ⟨0, fun h => absurd h hu⟩
    choose D hD using key
    have h1 := h ι g ℓ hℓ A hA D hD
    refine le_trans (Finset.sum_le_sum fun u hu => ?_) h1
    obtain ⟨G, hGA, hG, hDG⟩ := (hD u hu).1
    rw [hDG]
    exact hd u hu G (Finset.subset_sdiff.mp hGA).2 hG

/-! ### The packing bound (Lemma 6.5) -/

/-- The packing bound with the family `κ` indexed by the non-empty sets: if `x ∈ {-1,1}^n` and
`κ_S ≥ 0` (`∅ ≠ S ⊆ [n]`) satisfy `∑_{S ∋ i} κ_S ≤ 1` for every `i`, then
`∑_S κ_S |f(x) − f(x^S)| ≤ π² d²` (`f` with values in `[-1,1]` and of degree at most `d`).
Nothing is asked of, and nothing is summed at, the empty set. In Lemma 6.5 of the paper the
family `κ` is indexed by all subsets of `[n]`, as in `PackingBound`. -/
def PackingBoundNonempty : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (κ : Finset ι → ℝ), (∀ S : Finset ι, S.Nonempty → 0 ≤ κ S) →
    (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
    ∑ S ∈ univ.filter (fun S : Finset ι => S.Nonempty), κ S * |f x - f (flipSet x S)|
      ≤ Real.pi ^ 2 * (d : ℝ) ^ 2

theorem packingBound_iff_nonempty : PackingBound ↔ PackingBoundNonempty := by
  constructor
  · intro h ι _ _ d f hbd hdeg x κ hκ hpack
    have h1 := h ι d f hbd hdeg x (fun S => if S.Nonempty then κ S else 0)
      (fun S => by
        split_ifs with hS
        · exact hκ S hS
        · exact le_refl 0)
      (fun i => by
        refine le_of_eq_of_le (Finset.sum_congr rfl fun S hS => ?_) (hpack i)
        have hS' : S.Nonempty := ⟨i, (Finset.mem_filter.mp hS).2⟩
        change (if S.Nonempty then κ S else 0) = κ S
        exact ite_eq_left hS')
    rw [Finset.sum_filter]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun S _ => ?_) h1
    change (if S.Nonempty then κ S * |f x - f (flipSet x S)| else 0)
      = (if S.Nonempty then κ S else 0) * |f x - f (flipSet x S)|
    split_ifs with hS
    · rfl
    · exact (zero_mul _).symm
  · intro h ι _ _ d f hbd hdeg x κ hκ hpack
    have h1 := h ι d f hbd hdeg x κ (fun S _ => hκ S) hpack
    refine le_of_eq_of_le ?_ h1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · rfl
    · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      rw [hS', AaronsonAmbainis.Bridge.flipSet_empty, sub_self, abs_zero, mul_zero]

end AaronsonAmbainis.Bridge
