/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.IterationLemma
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows

/-!
# StepFiveSubWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 5: the sub-window re-run of the iteration lemma

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The per-scale decay hypothesis, named -/

/-- **`e.Ej.decay.assumption`** — the per-scale excess-decay hypothesis of
`l.iteration.lemma`, transcribed character for character from the anchor
`Algsuperdiff.Frozen.Section4.iteration_lemma` and given a name, so that it can
be quoted as the one input Step 5 takes from Step 4.

For every scale `j ∈ [n,m]` outside the bad set `B`, `E(u, U_{j-h}) ≤ θ^h E(u,
U_j) + ε_j |∇l_j| + δ_j`. -/
def IterationDecay (U : ℤ → Set (Vec d)) (u : Vec d → ℝ) (g : ℤ → Vec d)
    (h : ℕ) (θ : ℝ) (ε δ : ℤ → ℝ) (B : Finset ℤ) (n m : ℤ) : Prop :=
  ∀ j : ℤ, n ≤ j → j ≤ m → j ∉ B →
    affineExcess (U (j - (h : ℤ))) u ≤
      θ ^ h * affineExcess (U j) u + ε j * slopeMagnitude (g j) + δ j

/-! ## 2. Elementary consequences of the window binders -/

/-- Nesting `U (j-1) ⊆ U j` iterates to `U a ⊆ U b` for `a ≤ b ≤ m`. -/
theorem subset_of_iterationNest {U : ℤ → Set (Vec d)} {m : ℤ}
    (hnest : ∀ j : ℤ, j ≤ m → U (j - 1) ⊆ U j) {a : ℤ} :
    ∀ b : ℤ, a ≤ b → b ≤ m → U a ⊆ U b := by
  intro b hab
  induction b, hab using Int.leInduction with
  | base => exact fun _ => subset_rfl
  | succ b hab ih =>
      intro hb1
      have hb : b ≤ m := by omega
      have hstep : U b ⊆ U (b + 1) := by
        have hn := hnest (b + 1) hb1
        have hbb : b + 1 - 1 = b := by omega
        rwa [hbb] at hn
      exact fun x hx => hstep (ih hb hx)

/-! ## 3. Scalar atoms of the budget-inheritance argument -/

/-- `1 ≤ exp E` for `E ≥ 0`, in the form the degenerate case needs. -/
theorem one_le_exp_of_nonneg {E : ℝ} (hE : 0 ≤ E) : (1 : ℝ) ≤ Real.exp E := by
  have h := Real.exp_le_exp.mpr hE
  rwa [Real.exp_zero] at h

/-- The trivial sub-window bound at a degenerate window `n' = m'`: with `A ≥ 0`, `S
≥ 0` and `E ≥ 0` one has `A ≤ e^E (A + S)`.  Kept as an abstract-real atom so
that `exp` never meets the geometry. -/
theorem le_exp_mul_add_of_nonneg {A S E : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hE : 0 ≤ E) : A ≤ Real.exp E * (A + S) := by
  have h1 : (1 : ℝ) ≤ Real.exp E := one_le_exp_of_nonneg hE
  have h2 : A + S ≤ Real.exp E * (A + S) :=
    le_mul_of_one_le_left (by linarith only [hA, hS]) h1
  linarith only [h2, hS]

/-- The prefactor/budget comparison, with `exp` isolated: a smaller exponent and a
smaller nonnegative second factor give a smaller product. -/
theorem exp_mul_le_exp_mul {E E' X X' : ℝ} (hEE : E' ≤ E) (hXX : X' ≤ X)
    (hX' : 0 ≤ X') : Real.exp E' * X' ≤ Real.exp E * X :=
  mul_le_mul (Real.exp_le_exp.mpr hEE) hXX hX' (Real.exp_pos E).le

/-! ## 4. The sub-window device -/

/-- **The sub-window device.**  The frozen iteration anchor, conclusion (i),
re-exported at every sub-window `[n', m'] ⊆ [n, m]` with the outer budgets `|𝓑|`,
`∑_{Icc n m} ε` and `∑_{Icc n m} δ` in place of the sub-window's own.

This is the exact statement the manuscript uses ("The iteration lemma now
yields, for every `n', m' ∈ ℤ` with `n ≤ n' ≤ m' ≤ m`") and the exact statement
`l.iteration.lemma` does NOT literally provide.  The constant `C` is the
anchor's own.

Note the window binder is relaxed from the anchor's `n < m` to `n ≤ m`: the
degenerate windows are handled by `le_exp_mul_add_of_nonneg`. -/
theorem exists_oscillation_subwindow_of_iterationLemma (d : ℕ) (hd : d ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → θ ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) →
        ∀ n m : ℤ, n ≤ m →
          ∀ U : ℤ → Set (Vec d), IterationWindowFamily U m →
            ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (U m)) →
              ∀ B : Finset ℤ, B ⊆ Finset.Icc n m →
                ∀ ε δ : ℤ → ℝ,
                  (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ ε j) →
                  (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ δ j) →
                    ∀ (c : ℤ → ℝ) (g : ℤ → Vec d),
                      (∀ j : ℤ, j ≤ m → IsAffineMinimizer (U j) u (c j) (g j)) →
                      IterationDecay U u g h θ ε δ B n m →
                        ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
                          (3 : ℝ) ^ (-n') *
                              normalizedL2On (U n')
                                (fun x => u x - volumeAverage (U n') u) ≤
                            Real.exp
                                (C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) +
                                  C * ∑ j ∈ Finset.Icc n m, ε j) *
                              ((3 : ℝ) ^ (-m') *
                                  normalizedL2On (U m')
                                    (fun x => u x - volumeAverage (U m') u) +
                                ∑ j ∈ Finset.Icc n m, δ j) := by
  obtain ⟨C, hC, hlem⟩ := Algsuperdiff.Frozen.Section4.iteration_lemma d hd
  refine ⟨C, hC, ?_⟩
  intro h θ hθ hθh n m hnm U hU u hu B hB ε δ hε hδ c g hmin hdec n' m' hn' hn'm' hm'm
  obtain ⟨hmeas, hnest, hsand⟩ := hU
  -- The outer budget sums and the outer exponent.
  have hIccsub : Finset.Icc n' m' ⊆ Finset.Icc n m := by
    intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  have hsumε : ∑ j ∈ Finset.Icc n' m', ε j ≤ ∑ j ∈ Finset.Icc n m, ε j :=
    Finset.sum_le_sum_of_subset_of_nonneg hIccsub fun j hj _ => by
      rw [Finset.mem_Icc] at hj; exact hε j hj.1 hj.2
  have hsumδ : ∑ j ∈ Finset.Icc n' m', δ j ≤ ∑ j ∈ Finset.Icc n m, δ j :=
    Finset.sum_le_sum_of_subset_of_nonneg hIccsub fun j hj _ => by
      rw [Finset.mem_Icc] at hj; exact hδ j hj.1 hj.2
  have hsumεnn : 0 ≤ ∑ j ∈ Finset.Icc n m, ε j :=
    Finset.sum_nonneg fun j hj => by rw [Finset.mem_Icc] at hj; exact hε j hj.1 hj.2
  have hsumδnn : 0 ≤ ∑ j ∈ Finset.Icc n m, δ j :=
    Finset.sum_nonneg fun j hj => by rw [Finset.mem_Icc] at hj; exact hδ j hj.1 hj.2
  have hEnn : 0 ≤ C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) + C * ∑ j ∈ Finset.Icc n m, ε j := by
    have h1 : 0 ≤ C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) := by
      have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
      have hb : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg B.card
      have ha : (0 : ℝ) ≤ C * ((h : ℝ) + 1) := mul_nonneg hC.le (by linarith only [hh])
      exact mul_nonneg ha (by linarith only [hb])
    have h2 : 0 ≤ C * ∑ j ∈ Finset.Icc n m, ε j := mul_nonneg hC.le hsumεnn
    linarith only [h1, h2]
  have hXnn : 0 ≤ (3 : ℝ) ^ (-m') *
      normalizedL2On (U m') (fun x => u x - volumeAverage (U m') u) :=
    mul_nonneg (zpow_nonneg (by norm_num) _) (normalizedL2On_nonneg _ _)
  rcases eq_or_lt_of_le hn'm' with heq | hlt
  · -- Degenerate sub-window `n' = m'`.
    subst heq
    exact le_exp_mul_add_of_nonneg hXnn hsumδnn hEnn
  · -- The genuine sub-window run.
    have hsub : U m' ⊆ U m := subset_of_iterationNest hnest m hm'm le_rfl
    have hu' : MemLp u 2 (volume.restrict (U m')) :=
      hu.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hBsub : B ∩ Finset.Icc n' m' ⊆ Finset.Icc n' m' := Finset.inter_subset_right
    have hrun :=
      (hlem h θ hθ hθh n' m' hlt U (fun j hj => hmeas j (by omega))
          (fun j hj => hnest j (by omega)) (fun j hj => hsand j (by omega)) u hu'
          (B ∩ Finset.Icc n' m') hBsub ε δ
          (fun j hj1 hj2 => hε j (by omega) (by omega))
          (fun j hj1 hj2 => hδ j (by omega) (by omega)) c g
          (fun j hj => hmin j (by omega))
          (fun j hj1 hj2 hj3 =>
            hdec j (by omega) (by omega) fun hjB =>
              hj3 (Finset.mem_inter.mpr ⟨hjB, Finset.mem_Icc.mpr ⟨hj1, hj2⟩⟩))).1
    refine le_trans hrun ?_
    have hcard : ((B ∩ Finset.Icc n' m').card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left)
    have hE' :
        C * ((h : ℝ) + 1) * (((B ∩ Finset.Icc n' m').card : ℝ) + 1) +
            C * ∑ j ∈ Finset.Icc n' m', ε j ≤
          C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) + C * ∑ j ∈ Finset.Icc n m, ε j := by
      have hh : (0 : ℝ) ≤ C * ((h : ℝ) + 1) := by
        have := Nat.cast_nonneg (α := ℝ) h
        exact mul_nonneg hC.le (by linarith only [this])
      have h1 : C * ((h : ℝ) + 1) * (((B ∩ Finset.Icc n' m').card : ℝ) + 1) ≤
          C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only [hcard]) hh
      have h2 : C * ∑ j ∈ Finset.Icc n' m', ε j ≤ C * ∑ j ∈ Finset.Icc n m, ε j :=
        mul_le_mul_of_nonneg_left hsumε hC.le
      linarith only [h1, h2]
    have hsumδ'nn : 0 ≤ ∑ j ∈ Finset.Icc n' m', δ j :=
      Finset.sum_nonneg fun j hj => by
        rw [Finset.mem_Icc] at hj; exact hδ j (by omega) (by omega)
    exact exp_mul_le_exp_mul hE' (by linarith only [hsumδ])
      (by linarith only [hXnn, hsumδ'nn])

end

end Algsuperdiff.Section4.Provider.Regularity
