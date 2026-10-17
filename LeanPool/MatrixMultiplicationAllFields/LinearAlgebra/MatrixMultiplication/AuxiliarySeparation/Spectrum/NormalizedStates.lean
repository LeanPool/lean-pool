/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.Order.Field

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Compact convex spaces of normalized additive states

These are the closed linear constraints in Appendix A. The nonemptiness of
this state space, and its instantiation by the tensor restriction semiring,
are separate statements.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- Additive restriction-monotone states with a fixed detector inequality. -/
def normalizedStates (R : S → ℝ) (d : S) (k : ℝ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧
    (∀ x, k * f x ≤ f (d * x))}

theorem normalizedStates_isClosed (R : S → ℝ) (d : S) (k : ℝ) :
    IsClosed (normalizedStates R d k) := by
  unfold normalizedStates
  have hb : IsClosed {f : S → ℝ | ∀ x, 0 ≤ f x ∧ f x ≤ R x} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (continuous_apply x)).inter
      (isClosed_le (continuous_apply x) continuous_const)
  have hn : IsClosed {f : S → ℝ | f 1 = 1} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have ha : IsClosed {f : S → ℝ | ∀ x y, f (x + y) = f x + f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y))
        ((continuous_apply x).add (continuous_apply y))
  have hm : IsClosed {f : S → ℝ | ∀ x y, x ≤ y → f x ≤ f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_le (continuous_apply x) (continuous_apply y)
  have hd : IsClosed {f : S → ℝ | ∀ x, k * f x ≤ f (d * x)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_le (continuous_const.mul (continuous_apply x)) (continuous_apply (d * x))
  exact hb.inter (hn.inter (ha.inter (hm.inter hd)))

theorem normalizedStates_isCompact (R : S → ℝ) (d : S) (k : ℝ) :
    IsCompact (normalizedStates R d k) := by
  apply (isCompact_univ_pi (fun x => isCompact_Icc (a := (0 : ℝ)) (b := R x))).of_isClosed_subset
    (normalizedStates_isClosed R d k)
  intro f hf x _
  exact hf.1 x

theorem normalizedStates_convex (R : S → ℝ) (d : S) (k : ℝ) :
    Convex ℝ (normalizedStates R d k) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ a * f x + b * g x ∧ a * f x + b * g x ≤ R x
    constructor
    · exact add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1)
    · calc
        a * f x + b * g x ≤ a * R x + b * R x :=
          add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha)
            (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)
        _ = R x := by rw [← add_mul, hab, one_mul]
  · change a * f 1 + b * g 1 = 1
    rw [hf.2.1, hg.2.1, mul_one, mul_one, hab]
  · intro x y
    change a * f (x + y) + b * g (x + y) =
      (a * f x + b * g x) + (a * f y + b * g y)
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro x y hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 x y hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 x y hxy) hb)
  · intro x
    change k * (a * f x + b * g x) ≤ a * f (d * x) + b * g (d * x)
    calc
      k * (a * f x + b * g x) = a * (k * f x) + b * (k * g x) := by ring
      _ ≤ a * f (d * x) + b * g (d * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 x) ha)
          (mul_le_mul_of_nonneg_left (hg.2.2.2.2 x) hb)

theorem state_zero {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) : f 0 = 0 := by
  have h := hf.2.2.1 0 0
  rw [zero_add] at h
  linarith

theorem state_nat_mul {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) (n : ℕ) (x : S) :
    f ((n : S) * x) = (n : ℝ) * f x := by
  induction n with
  | zero => simp [state_zero hf]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hf.2.2.1, ih]
    push_cast
    ring

theorem state_one_le {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) {z : S} (hz : 1 ≤ z) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 1 z hz

/-- Translation followed by normalization preserves every state constraint.
The two order hypotheses are exactly those supplied by tensor multiplication
and the finite rank bound in the restriction semiring. -/
theorem state_rescale {R : S → ℕ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates (fun x => (R x : ℝ)) d k) (z : S)
    (hz : 1 ≤ z)
    (hmulmono : ∀ x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ x : S, z * x ≤ (R x : S) * z) :
    (fun x => f (z * x) / f z) ∈ normalizedStates (fun x => (R x : ℝ)) d k := by
  have hfz : 0 < f z := lt_of_lt_of_le zero_lt_one (state_one_le hf hz)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨div_nonneg (hf.1 (z * x)).1 hfz.le, ?_⟩
    apply (div_le_iff₀ hfz).mpr
    have h := hf.2.2.2.1 (z * x) ((R x : S) * z) (hdom x)
    simpa only [state_nat_mul hf] using h
  · simp [mul_one, ne_of_gt hfz]
  · intro x y
    change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · intro x y hxy
    exact div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (hmulmono x y hxy)) hfz.le
  · intro x
    have h := hf.2.2.2.2 (z * x)
    have hc : d * (z * x) = z * (d * x) := by ring
    rw [hc] at h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hfz.le

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
