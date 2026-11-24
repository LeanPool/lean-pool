/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalDiagonalScaling
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-!
# Diagonal scaling along a convex combination

For two genuine `θ`-PSH potentials `a`, `b` and a weight `t ∈ (0,1)` the
diagonal global mixed measure of the convex combination dominates `tⁿ` times
the diagonal measure of `a`:

  `tⁿ · θⁿ_a ≤ θⁿ_{t a + (1-t) b}`   as measures on every set.

This is the manifold form of the elementary current inequality
`θ_{t a + (1-t) b} = t θ_a + (1-t) θ_b ≥ t θ_a`.  It is proved exactly as
`Pending.GlobalDiagonalScaling.globalMixedMeasure_diagonal_scale`, by replacing
one slot at a time and dropping the `b`-summand, but with the constant `0` of
that lemma replaced by an arbitrary second potential `b`.  That generality is
what the Monge--Ampere capacity needs: in a big but non-semipositive class the
constant `0` need not be `θ`-PSH, so the comparison potential has to be
`V_θ` (or any other genuine potential) rather than a constant.

The pole hypotheses of one-slot linearity
(`Pending.GlobalSlotLinear.globalMixedMeasure_update_add_smul`) are free here:
the pole set of a genuine `θ`-PSH potential is locally pluripolar and hence
null for every global mixed measure
(`globalMixedMeasure_pole_null_of_nondegenerate`).  No boundedness and no
semipositivity of `θ` is assumed.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling

open FirstPass FirstPass.PositiveClasses
open GlobalNonPluripolar GlobalDiagonalScaling
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Diagonal domination along a convex combination.**  For genuine `θ`-PSH
potentials `a`, `b` and `0 < t < 1`,
`tⁿ · θⁿ_a (S) ≤ θⁿ_{t a + (1-t) b} (S)` for every `S`. -/
theorem globalMixedMeasure_diagonal_convexComb_le {θ : ClosedRealOneOneForm n M}
    {a b : M → EReal} (ha : IsThetaPshPotential θ.val a)
    (hb : IsThetaPshPotential θ.val b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (S : Set M) :
    ENNReal.ofReal (t ^ n) *
        globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha.1) S ≤
      globalMixedMeasure (fun _ => θ) (fun _ => convexComb t a b)
        (fun _ => (isThetaPshPotential_convexComb ha hb ht0 ht1).1) S := by
  have hr : 0 < 1 - t := by linarith
  have hθeq : t • θ + (1 - t) • θ = θ := by
    rw [← add_smul, add_sub_cancel, one_smul]
  set w : M → EReal := convexComb t a b with hw_def
  have hwθ : ThetaPlurisubharmonic θ.val w :=
    (isThetaPshPotential_convexComb ha hb ht0 ht1).1
  -- The tuples whose first `m` slots carry `w` and the others `a`.
  let x : ℕ → Fin n → M → EReal := fun m i => if (i : ℕ) < m then w else a
  have hx : ∀ m i, ThetaPlurisubharmonic ((fun _ : Fin n => θ) i).val (x m i) := by
    intro m i
    by_cases h : (i : ℕ) < m
    · simpa only [x, h, ite_true] using hwθ
    · simpa only [x, h, ite_false] using ha.1
  have step : ∀ m, m ≤ n → ∀ S : Set M, ENNReal.ofReal (t ^ m) *
      globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha.1) S ≤
      globalMixedMeasure (fun _ => θ) (x m) (hx m) S := by
    intro m
    induction m with
    | zero =>
      intro _ S
      have e : x 0 = fun _ => a := by funext i; simp [x]
      rw [pow_zero, ENNReal.ofReal_one, one_mul,
        globalMixedMeasure_congr rfl e (hx 0) (fun _ => ha.1)]
    | succ m ih =>
      intro hm S
      have hmn : m < n := hm
      set i₀ : Fin n := ⟨m, hmn⟩ with hi₀
      have e1 : x (m + 1) = Function.update (x m) i₀ w := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [x, i₀]
        · rw [Function.update_of_ne h]
          have him : (i : ℕ) ≠ m := fun h' => h (Fin.ext h')
          simp only [x]
          split_ifs <;> first | rfl | omega
      have e2 : Function.update (x m) i₀ a = x m := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [x, i₀]
        · rw [Function.update_of_ne h]
      have eθ : Function.update (fun _ : Fin n => θ) i₀ θ = fun _ => θ :=
        Function.update_eq_self i₀ _
      have hc' : ∀ i, ThetaPlurisubharmonic ((fun _ : Fin n => θ) i).val
          (Function.update (x m) i₀ (fun p => (t : EReal) * a p +
            ((1 - t : ℝ) : EReal) * b p) i) := by
        have : (fun p => (t : EReal) * a p + ((1 - t : ℝ) : EReal) * b p) = w := rfl
        rw [this, ← e1]; exact hx (m + 1)
      have ha' : ∀ i, ThetaPlurisubharmonic
          (Function.update (fun _ : Fin n => θ) i₀ θ i).val
          (Function.update (x m) i₀ a i) := by
        rw [eθ, e2]; exact hx m
      have hb' : ∀ i, ThetaPlurisubharmonic
          (Function.update (fun _ : Fin n => θ) i₀ θ i).val
          (Function.update (x m) i₀ b i) := by
        intro i
        rw [eθ]
        by_cases h : i = i₀
        · rw [h, Function.update_self]; exact hb.1
        · rw [Function.update_of_ne h]; exact hx m i
      have hpa : globalMixedMeasure _ _ hb' {p | a p = ⊥} = 0 :=
        globalMixedMeasure_pole_null_of_nondegenerate hb' ha
      have hpb : globalMixedMeasure _ _ ha' {p | b p = ⊥} = 0 :=
        globalMixedMeasure_pole_null_of_nondegenerate ha' hb
      have hlin := GlobalSlotLinear.globalMixedMeasure_update_add_smul
        (θ := fun _ => θ) i₀ ht0 hr hθeq.symm hc' ha' hb' hpa hpb
      have hA : globalMixedMeasure (Function.update (fun _ => θ) i₀ θ)
          (Function.update (x m) i₀ a) ha' =
            globalMixedMeasure (fun _ => θ) (x m) (hx m) :=
        globalMixedMeasure_congr eθ e2 _ _
      have hC : globalMixedMeasure (fun _ => θ) (x (m + 1)) (hx (m + 1)) =
          globalMixedMeasure (fun _ => θ)
            (Function.update (x m) i₀ (fun p => (t : EReal) * a p +
              ((1 - t : ℝ) : EReal) * b p)) hc' :=
        globalMixedMeasure_congr rfl e1 _ _
      rw [hC, hlin, hA, add_apply, smul_apply, smul_eq_mul]
      calc ENNReal.ofReal (t ^ (m + 1)) *
            globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha.1) S
          = ENNReal.ofReal t * (ENNReal.ofReal (t ^ m) *
            globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha.1) S) := by
            rw [pow_succ', ENNReal.ofReal_mul ht0.le, mul_assoc]
        _ ≤ ENNReal.ofReal t * globalMixedMeasure (fun _ => θ) (x m) (hx m) S := by
            gcongr
            exact ih (Nat.le_of_succ_le hm) S
        _ ≤ _ := le_self_add
  have hfull : x n = fun _ => w := by funext i; simp [x, i.isLt]
  calc ENNReal.ofReal (t ^ n) *
        globalMixedMeasure (fun _ => θ) (fun _ => a) (fun _ => ha.1) S
      ≤ globalMixedMeasure (fun _ => θ) (x n) (hx n) S := step n le_rfl S
    _ = _ := by rw [globalMixedMeasure_congr rfl hfull (hx n) _]

end

end SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
