/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevLeibniz
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Leibniz splits of ordered spatial derivatives

Every ordered derivative of a scalar product is a finite sum indexed by
the assignments of its derivative letters to the two factors. Keeping
the assignments as a list retains the binomial multiplicities when
some coordinate directions coincide.
-/

public section

open CKN

open MeasureTheory CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Assign each letter of an ordered derivative word to one of two
factors, retaining repeated assignments (eq:lps-Hm-energy). -/
@[expose] def lpsLeibnizSplits : List (Fin 3) →
    List (List (Fin 3) × List (Fin 3))
  | [] => [([], [])]
  | j :: α =>
      (lpsLeibnizSplits α).map (fun p => (j :: p.1, p.2)) ++
        (lpsLeibnizSplits α).map (fun p => (p.1, j :: p.2))

/-- Every split retains the total derivative degree
(`eq:lps-Hm-energy`). -/
theorem lps_leibniz_splits_degree (α : List (Fin 3))
    (p : List (Fin 3) × List (Fin 3))
    (hp : p ∈ lpsLeibnizSplits α) :
    p.1.length + p.2.length = α.length := by
  induction α generalizing p with
  | nil =>
      simp [lpsLeibnizSplits] at hp
      simp [hp]
  | cons j α ih =>
      simp only [lpsLeibnizSplits, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have h := ih q hq
        simp only [List.length_cons]
        omega
      · have h := ih q hq
        simp only [List.length_cons]
        omega

/-- A word of length `n` has `2^n` Leibniz assignments, counted with
multiplicity (eq:lps-Hm-energy). -/
theorem lps_leibniz_splits_length (α : List (Fin 3)) :
    (lpsLeibnizSplits α).length = 2 ^ α.length := by
  induction α with
  | nil => simp [lpsLeibnizSplits]
  | cons j α ih =>
      simp only [lpsLeibnizSplits, List.length_append, List.length_map,
        List.length_cons, pow_succ, ih]
      omega

/-- The ordered Leibniz family is the sum of products over all
derivative assignments (eq:lps-Hm-energy). -/
theorem lps_leibniz_splits_sum (α : List (Fin 3))
    (A B : List (Fin 3) → Vec3 → ℝ) (x : Vec3) :
    sobolevLeibnizFamily α A B x =
      ((lpsLeibnizSplits α).map
        (fun p => A p.1 x * B p.2 x)).sum := by
  induction α generalizing A B with
  | nil => simp [lpsLeibnizSplits, sobolevLeibnizFamily]
  | cons j α ih =>
      simp only [sobolevLeibnizFamily, lpsLeibnizSplits,
        List.map_append, List.sum_append, List.map_map]
      rw [ih (fun β => A (j :: β)) B, ih A (fun β => B (j :: β))]
      rfl

/-- A finite bound on every Leibniz term controls the square integral
of the full ordered derivative, with its binomial multiplicities
(`eq:lps-Hm-energy`). -/
theorem lps_leibniz_integral_bound (α : List (Fin 3))
    (A B : List (Fin 3) → Vec3 → ℝ) (K : ℝ)
    (hterm : ∀ p ∈ lpsLeibnizSplits α,
      MemLp (fun x => A p.1 x * B p.2 x) 2 volume ∧
      (∫ x, (A p.1 x * B p.2 x) ^ 2) ≤ K) :
    Integrable (fun x => sobolevLeibnizFamily α A B x ^ 2) volume ∧
    (∫ x, sobolevLeibnizFamily α A B x ^ 2) ≤
      ((lpsLeibnizSplits α).length : ℝ) ^ 2 * K := by
  let l := lpsLeibnizSplits α
  let F : Fin l.length → Vec3 → ℝ := fun i x =>
    A (l.get i).1 x * B (l.get i).2 x
  have hsum (x : Vec3) :
      sobolevLeibnizFamily α A B x = ∑ i : Fin l.length, F i x := by
    rw [lps_leibniz_splits_sum]
    change (l.map (fun p => A p.1 x * B p.2 x)).sum = _
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  have hF (i : Fin l.length) :
      MemLp (F i) 2 volume ∧ (∫ x, F i x ^ 2) ≤ K :=
    hterm (l.get i) (List.get_mem l i)
  have hsumLp : MemLp (fun x => ∑ i : Fin l.length, F i x)
      2 volume :=
    memLp_finsetSum Finset.univ (fun i _ => (hF i).1)
  have hrightInt : Integrable
      (fun x => (l.length : ℝ) * ∑ i : Fin l.length, F i x ^ 2)
      volume := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hF i).1.integrable_sq)
  have hpoint (x : Vec3) :
      (∑ i : Fin l.length, F i x) ^ 2 ≤
        (l.length : ℝ) * ∑ i : Fin l.length, F i x ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin l.length))
      (fun i => F i x) (fun _ => (1 : ℝ))
    simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, mul_one, one_mul, mul_comm] using h
  rw [show (fun x => sobolevLeibnizFamily α A B x ^ 2) =
      (fun x => (∑ i : Fin l.length, F i x) ^ 2) from
      funext (fun x => congrArg (· ^ 2) (hsum x))]
  refine ⟨hsumLp.integrable_sq, ?_⟩
  calc
    (∫ x, (∑ i : Fin l.length, F i x) ^ 2) ≤
        ∫ x, (l.length : ℝ) * ∑ i : Fin l.length, F i x ^ 2 :=
          integral_mono hsumLp.integrable_sq hrightInt hpoint
    _ = (l.length : ℝ) * ∑ i : Fin l.length, ∫ x, F i x ^ 2 := by
      rw [integral_const_mul]
      rw [integral_finsetSum _ (fun i _ => (hF i).1.integrable_sq)]
    _ ≤ (l.length : ℝ) * ∑ _i : Fin l.length, K := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => (hF i).2)) (by positivity)
    _ = (l.length : ℝ) ^ 2 * K := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

end ESS
