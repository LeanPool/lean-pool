/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricDefect
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.OrdinaryConjugation
public import LeanPool.SuzukiCancellation.Algebra.BigOperators.Group.List.Fin

/-!
# Ordinary conjugation remainders of the half-defect

The logarithmic derivative is a sum of generators transported by their suffixes.
Expanding each conjugation separately retains the original commutator constant.

## Main definitions

* `logDerivConjugationTerms`: suffixes paired with their transported generators.
* `halfDefectCommutatorConstant`: the original finite commutator remainder constant.

## Main results

* `groupedConjCoeff_eq_conjCoeff_sum`: the grouped and ordinary coefficient decompositions agree.
* `halfDefectCommutatorConstant_eq`: the paper's formula with unnegated generators.
* `norm_halfDefect_add_sub_sum_le_commutator`: the original constant controls the even defect.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError Finset
open scoped RealScalar algebraMap

namespace FQFP

/-- Each generator is transported by the part of the half-list strictly after it. -/
def logDerivConjugationTerms {A : Type*} : List A → List (List A × A)
  | [] => []
  | a :: l => (l, a) :: logDerivConjugationTerms l

/-- Appending a generator extends every previous suffix and adds one untransported term. -/
lemma logDerivConjugationTerms_append_singleton {A : Type*} (l : List A) (a : A) :
    logDerivConjugationTerms (l ++ [a]) =
      (logDerivConjugationTerms l).map (fun q ↦ (q.1 ++ [a], q.2)) ++ [([], a)] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [logDerivConjugationTerms, ih]

section Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Reindexing a finite conjugation coefficient along an equality preserves its value. -/
lemma conjCoeff_cast {s t : ℕ} (h : s = t) (Z : Fin s → A) (B : A) (n : ℕ) :
    conjCoeff (fun i : Fin t ↦ Z (Fin.cast h.symm i)) B n = conjCoeff Z B n := by
  subst t
  rfl

/-- Reindexing the grouped coefficients along an equality preserves their value. -/
lemma groupedConjCoeff_cast {s t : ℕ} (h : s = t) (Z K : Fin s → A) (B : A) (n : ℕ) :
    groupedConjCoeff (fun i : Fin t ↦ Z (Fin.cast h.symm i))
      (fun i : Fin t ↦ K (Fin.cast h.symm i)) B n = groupedConjCoeff Z K B n := by
  subst t
  rfl

/-- A singleton appended to a list is the outermost adjoint in its conjugation coefficients. -/
lemma conjCoeff_get_append_singleton (l : List A) (a B : A) (n : ℕ) :
    conjCoeff (fun i : Fin (l ++ [a]).length ↦ -(l ++ [a]).get i) B n =
      ∑ q ∈ range (n + 1), (Nat.factorial q : ℝ)⁻¹ • adPow (-a) q
        (conjCoeff (fun i : Fin l.length ↦ -l.get i) B (n - q)) := by
  let h : (l ++ [a]).length = l.length + 1 := by simp
  rw [← conjCoeff_cast h]
  rw [conjCoeff_succ]
  simp [List.get_eq_getElem]

/-- A singleton appended to a list adds one last kick to the coefficient recursion. -/
lemma groupedConjCoeff_get_append_singleton (l : List A) (a B : A) (n : ℕ) :
    groupedConjCoeff (fun i : Fin (l ++ [a]).length ↦ -(l ++ [a]).get i)
      (l ++ [a]).get B n =
      (∑ q ∈ range (n + 1), (Nat.factorial q : ℝ)⁻¹ • adPow (-a) q
        (groupedConjCoeff (fun i : Fin l.length ↦ -l.get i)
          (fun i ↦ l.get i) B (n - q))) +
      if n = 0 then a else 0 := by
  let h : (l ++ [a]).length = l.length + 1 := by simp
  rw [← groupedConjCoeff_cast h]
  rw [groupedConjCoeff]
  simp [List.get_eq_getElem]

/-- With no generators the conjugation series is constant. -/
lemma conjCoeff_get_nil (B : A) (n : ℕ) :
    conjCoeff (fun i : Fin ([] : List A).length ↦ -([] : List A).get i) B n =
      if n = 0 then B else 0 := by
  by_cases hn : n = 0
  · simp [conjCoeff, finAntidiagonal_zero, hn]
  · simp [conjCoeff, finAntidiagonal_zero, hn]

/-- The kick coefficients are the sum of the ordinary conjugation coefficients of their suffixes. -/
lemma groupedConjCoeff_eq_conjCoeff_sum (l : List A) (G : A) (n : ℕ) :
    groupedConjCoeff (fun i : Fin l.length ↦ -l.get i) l.get G n =
      conjCoeff (fun i : Fin l.length ↦ -l.get i) G n +
        ((logDerivConjugationTerms l).map fun q ↦
          conjCoeff (fun i : Fin q.1.length ↦ -q.1.get i) q.2 n).sum := by
  induction l using List.reverseRecOn generalizing n with
  | nil =>
      simpa only [groupedConjCoeff, logDerivConjugationTerms, List.map_nil,
        List.sum_nil, add_zero] using (conjCoeff_get_nil G n).symm
  | append_singleton l a ih =>
      rw [groupedConjCoeff_get_append_singleton, conjCoeff_get_append_singleton,
        logDerivConjugationTerms_append_singleton]
      simp only [List.map_append, List.map_map, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Function.comp_def, conjCoeff_get_nil]
      simp_rw [ih, map_add, smul_add, Finset.sum_add_distrib,
        conjCoeff_get_append_singleton]
      simp only [add_assoc]
      congr 1
      apply congrArg (· + (if n = 0 then a else 0))
      rw [TrotterError.List.sum_map_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [map_list_sum, List.smul_sum]
      simp only [List.map_map, Function.comp_def]

/-- The grouped polynomial is the sum of the ordinary conjugation polynomials. -/
lemma sum_groupedConjCoeff_eq_sum_conjCoeff (l : List A) (G : A) (p : ℕ) (x : ℝ) :
    (∑ k ∈ range p, x ^ k •
      groupedConjCoeff (fun i : Fin l.length ↦ -l.get i) l.get G k) =
      (∑ k ∈ range p, x ^ k • conjCoeff (fun i : Fin l.length ↦ -l.get i) G k) +
        ((logDerivConjugationTerms l).map fun q ↦
          ∑ k ∈ range p, x ^ k •
            conjCoeff (fun i : Fin q.1.length ↦ -q.1.get i) q.2 k).sum := by
  simp_rw [groupedConjCoeff_eq_conjCoeff_sum, smul_add, Finset.sum_add_distrib]
  congr 1
  rw [TrotterError.List.sum_map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [List.smul_sum]
  simp only [List.map_map, Function.comp_def]

/-- Passing through the list of a finite family preserves the grouped coefficients. -/
lemma groupedConjCoeff_get_ofFn {s : ℕ} (Z : Fin s → A) (G : A) (n : ℕ) :
    groupedConjCoeff (fun i : Fin (List.ofFn Z).length ↦ -(List.ofFn Z).get i)
      (List.ofFn Z).get G n = groupedConjCoeff (fun i ↦ -Z i) Z G n := by
  rw [← groupedConjCoeff_cast (show (List.ofFn Z).length = s by simp)]
  simp

end Algebra

/-- The original commutator remainder constant of the symmetric half-defect.
The seed is split into `X` and `Y` only in this norm estimate. -/
def halfDefectCommutatorConstant {A : Type*} [NormedRing A] [Algebra ℝ A]
    (l : List A) (X Y : A) (p : ℕ) : ℝ :=
  (2 * ((logDerivConjugationTerms l).map fun q ↦
    αCommConj (fun i : Fin q.1.length ↦ -q.1.get i) q.2 p).sum +
    αCommConj (fun i : Fin l.length ↦ -l.get i) X p +
    αCommConj (fun i : Fin l.length ↦ -l.get i) Y p) /
      (Nat.factorial (p + 1) : ℝ)

/-- The original commutator remainder constant is nonnegative. -/
lemma halfDefectCommutatorConstant_nonneg {A : Type*} [NormedRing A] [Algebra ℝ A]
    (l : List A) (X Y : A) (p : ℕ) : 0 ≤ halfDefectCommutatorConstant l X Y p := by
  have hα {s : ℕ} (Z : Fin s → A) (B : A) : 0 ≤ αCommConj Z B p := by
    unfold αCommConj
    positivity
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply add_nonneg (add_nonneg (mul_nonneg (by norm_num) _) (hα _ X)) (hα _ Y)
  apply List.sum_nonneg
  intro a ha
  rcases List.mem_map.mp ha with ⟨q, _, rfl⟩
  exact hα _ q.2

section NormBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The ordinary multinomial constant is homogeneous in its transported element. -/
lemma αCommConj_smul_eq {s : ℕ} (Z : Fin s → A) (B : A) (c : ℝ) (p : ℕ) :
    αCommConj Z (c • B) p = |c| * αCommConj Z B p := by
  simp only [αCommConj, adSequence_smul, norm_smul, Real.norm_eq_abs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The ordinary multinomial constant is subadditive in its transported element. -/
lemma αCommConj_add_le {s : ℕ} (Z : Fin s → A) (B C : A) (p : ℕ) :
    αCommConj Z (B + C) p ≤ αCommConj Z B p + αCommConj Z C p := by
  simp only [αCommConj, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  rw [← adSequenceLinear_apply, map_add, adSequenceLinear_apply, adSequenceLinear_apply,
    ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)

/-- Negating every generator leaves the multinomial commutator constant unchanged. -/
lemma αCommConj_neg_eq {s : ℕ} (Z : Fin s → A) (B : A) (p : ℕ) :
    αCommConj (fun i ↦ -Z i) B p = αCommConj Z B p := by
  have hneg : (fun i ↦ -Z i) = (fun i ↦ (-1 : ℝ) • Z i) := by simp
  rw [hneg]
  simp only [αCommConj, adSequence_smul_fun, norm_smul, Real.norm_eq_abs, abs_prod,
    abs_pow, abs_neg, abs_one, one_pow, Finset.prod_const_one, one_mul]

/-- The half-defect constant is exactly the paper's formula with unnegated generators. -/
lemma halfDefectCommutatorConstant_eq (l : List A) (X Y : A) (p : ℕ) :
    halfDefectCommutatorConstant l X Y p =
      (2 * ((logDerivConjugationTerms l).map fun q ↦
        αCommConj q.1.get q.2 p).sum + αCommConj l.get X p + αCommConj l.get Y p) /
          (Nat.factorial (p + 1) : ℝ) := by
  simp only [halfDefectCommutatorConstant, αCommConj_neg_eq]

end NormBounds

section Analysis

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The logarithmic derivative is the sum of its suffix-transported generators. -/
theorem expListLogDeriv_eq_sum_conj (l : List A) (t : ℝ) :
    expListLogDeriv l t =
      ((logDerivConjugationTerms l).map fun q ↦ expListConj q.1 q.2 t).sum := by
  induction l using List.reverseRecOn with
  | nil =>
      simp [expListLogDeriv, logDerivConjugationTerms,
        show expListProduct ([] : List A) = fun _ ↦ (1 : A) from rfl]
  | append_singleton l a ih =>
      rw [expListLogDeriv_append_singleton, ih, logDerivConjugationTerms_append_singleton]
      change expSMulConjLin (-a) t _ + a = _
      rw [map_list_sum]
      simp only [List.map_append, List.map_map, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
      simp only [expListConj_append_singleton]
      rw [show expListConj ([] : List A) a t = a by simp [expListConj]]
      rfl

/-- Moving-frame transport is the existing ordinary conjugation in increasing index order. -/
lemma expListConj_eq_multiConj (l : List A) (B : A) (t : ℝ) :
    expListConj l B t = multiConj (fun i : Fin l.length ↦ -l.get i) B t := by
  simp only [expListConj, expListProduct, multiConj, List.map_reverse, smul_neg,
    neg_smul, neg_neg, List.get_eq_getElem]
  rw [List.ofFn_getElem_eq_map l (fun a ↦ exp (-(t • a))),
    List.ofFn_getElem_eq_map l (fun a ↦ exp (t • a))]

omit [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A] in
/-- Each suffix in the logarithmic derivative is a sublist of the half-list. -/
lemma logDerivConjugationTerms_sublist (l : List A) (q : List A × A)
    (hq : q ∈ logDerivConjugationTerms l) : q.1.Sublist l := by
  induction l with
  | nil => simp [logDerivConjugationTerms] at hq
  | cons a l ih =>
      simp only [logDerivConjugationTerms, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.sublist_cons_self a l
      · exact (ih hq).trans (List.sublist_cons_self a l)

/-- The ordinary polynomial for moving-frame transport has its multinomial
remainder bound under the half-list's exponential contraction assumptions. -/
lemma norm_expListConj_sub_sum_le (l : List A) (B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖expListConj l B x -
      ∑ k ∈ range p, x ^ k • conjCoeff (fun i : Fin l.length ↦ -l.get i) B k‖ ≤
      αCommConj (fun i : Fin l.length ↦ -l.get i) B p * |x| ^ p /
        (Nat.factorial p : ℝ) := by
  rw [expListConj_eq_multiConj]
  have hA (i : Fin l.length) (u : ℝ) : ‖exp (u • -l.get i)‖ ≤ 1 := by
    simpa only [smul_neg, neg_smul] using hZ (l.get i) (List.get_mem ..) (-u)
  simpa only [← map_pow (algebraMap ℝ A), ← smul_eq_mul_right] using
    norm_multiConj_sub_sum_le_of_le_one (fun i : Fin l.length ↦ -l.get i) B p hp x hA

/-- The half-defect is a seed conjugation plus all suffix conjugations. -/
lemma halfDefect_eq_conj_seed_add_sum (l : List A) (G : A) (x : ℝ) :
    halfDefect l G x = expListConj l (-(1 / 2 : ℝ) • G) x +
      ((logDerivConjugationTerms l).map fun q ↦ expListConj q.1 q.2 x).sum := by
  have hlin : expListConj l (-(1 / 2 : ℝ) • G) x =
      -(1 / 2 : ℝ) • expListConj l G x := by
    change expListProduct l.reverse (-x) * (-(1 / 2 : ℝ) • G) * expListProduct l x =
      -(1 / 2 : ℝ) • (expListProduct l.reverse (-x) * G * expListProduct l x)
    rw [mul_smul_comm, smul_mul_assoc]
  rw [halfDefect, expListLogDeriv_eq_sum_conj, hlin]
  module

omit [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A] in
/-- Bounds for the remainders of a finite family also bound its summed remainder. -/
lemma norm_sum_map_sub_sum_le_of_bound {B ι : Type*} [SeminormedAddCommGroup B] (l : List ι)
    (f g : ι → B) (b : ι → ℝ) (hb : ∀ a ∈ l, ‖f a - g a‖ ≤ b a) :
    ‖(l.map f).sum - (l.map g).sum‖ ≤ (l.map b).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_sub_add_comm]
      exact (norm_add_le _ _).trans (add_le_add (hb a (by simp))
        (ih fun a ha ↦ hb a (by simp [ha])))

/-- The half-defect's ordinary conjugation expansion, before splitting its seed
inside the remainder constant. -/
theorem norm_halfDefect_sub_sum_le_conj (l : List A) (G : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖halfDefect l G x - ∑ k ∈ range p, x ^ k •
      groupedConjCoeff (fun i : Fin l.length ↦ -l.get i) l.get (-(1 / 2 : ℝ) • G) k‖ ≤
      (αCommConj (fun i : Fin l.length ↦ -l.get i) (-(1 / 2 : ℝ) • G) p +
        ((logDerivConjugationTerms l).map fun q ↦
          αCommConj (fun i : Fin q.1.length ↦ -q.1.get i) q.2 p).sum) *
        |x| ^ p / (Nat.factorial p : ℝ) := by
  let α (q : List A × A) := αCommConj (fun i : Fin q.1.length ↦ -q.1.get i) q.2 p
  have hsum :
      ‖((logDerivConjugationTerms l).map fun q ↦ expListConj q.1 q.2 x).sum -
        ((logDerivConjugationTerms l).map fun q ↦ ∑ k ∈ range p,
          x ^ k • conjCoeff (fun i : Fin q.1.length ↦ -q.1.get i) q.2 k).sum‖ ≤
        ((logDerivConjugationTerms l).map fun q ↦ α q * |x| ^ p /
          (Nat.factorial p : ℝ)).sum := by
    apply norm_sum_map_sub_sum_le_of_bound
    intro q hq
    exact norm_expListConj_sub_sum_le q.1 q.2
      (fun Z hmem ↦ hZ Z ((logDerivConjugationTerms_sublist l q hq).subset hmem)) p hp x
  have hfactor (terms : List (List A × A)) :
      (terms.map fun q ↦ α q * |x| ^ p / (Nat.factorial p : ℝ)).sum =
        (terms.map α).sum * |x| ^ p / (Nat.factorial p : ℝ) := by
    simp only [div_eq_mul_inv, List.sum_map_mul_right]
  rw [hfactor] at hsum
  rw [halfDefect_eq_conj_seed_add_sum, sum_groupedConjCoeff_eq_sum_conjCoeff,
    add_sub_add_comm]
  calc
    _ ≤ ‖expListConj l (-(1 / 2 : ℝ) • G) x - ∑ k ∈ range p,
          x ^ k • conjCoeff (fun i : Fin l.length ↦ -l.get i) (-(1 / 2 : ℝ) • G) k‖ +
        ‖((logDerivConjugationTerms l).map fun q ↦ expListConj q.1 q.2 x).sum -
          ((logDerivConjugationTerms l).map fun q ↦ ∑ k ∈ range p,
            x ^ k • conjCoeff (fun i : Fin q.1.length ↦ -q.1.get i) q.2 k).sum‖ :=
      norm_add_le _ _
    _ ≤ αCommConj (fun i : Fin l.length ↦ -l.get i) (-(1 / 2 : ℝ) • G) p *
          |x| ^ p / (Nat.factorial p : ℝ) +
        ((logDerivConjugationTerms l).map α).sum * |x| ^ p / (Nat.factorial p : ℝ) :=
      add_le_add (norm_expListConj_sub_sum_le l _ hZ p hp x) hsum
    _ = _ := by
      dsimp only [α]
      ring

/-- Splitting the total generator only in the remainder recovers the original
commutator constant for the half-defect. -/
theorem norm_halfDefect_sub_sum_le_commutator (l : List A) (X Y : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖halfDefect l (X + Y) x - ∑ k ∈ range p, x ^ k •
      groupedConjCoeff (fun i : Fin l.length ↦ -l.get i) l.get
        (-(1 / 2 : ℝ) • (X + Y)) k‖ ≤
      ((p + 1 : ℝ) / 2) * halfDefectCommutatorConstant l X Y p * |x| ^ p := by
  have hseed : αCommConj (fun i : Fin l.length ↦ -l.get i)
      (-(1 / 2 : ℝ) • (X + Y)) p ≤
      (1 / 2 : ℝ) * (αCommConj (fun i : Fin l.length ↦ -l.get i) X p +
        αCommConj (fun i : Fin l.length ↦ -l.get i) Y p) := by
    rw [αCommConj_smul_eq]
    norm_num only [abs_neg, abs_div, abs_one, show |(2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (αCommConj_add_le _ X Y p) (by norm_num)
  calc
    _ ≤ (αCommConj (fun i : Fin l.length ↦ -l.get i) (-(1 / 2 : ℝ) • (X + Y)) p +
        ((logDerivConjugationTerms l).map fun q ↦
          αCommConj (fun i : Fin q.1.length ↦ -q.1.get i) q.2 p).sum) *
        |x| ^ p / (Nat.factorial p : ℝ) := norm_halfDefect_sub_sum_le_conj l _ hZ p hp x
    _ ≤ ((1 / 2 : ℝ) * (αCommConj (fun i : Fin l.length ↦ -l.get i) X p +
          αCommConj (fun i : Fin l.length ↦ -l.get i) Y p) +
        ((logDerivConjugationTerms l).map fun q ↦
          αCommConj (fun i : Fin q.1.length ↦ -q.1.get i) q.2 p).sum) *
        |x| ^ p / (Nat.factorial p : ℝ) := by gcongr
    _ = _ := by
      unfold halfDefectCommutatorConstant
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hf : (Nat.factorial p : ℝ) ≠ 0 := by positivity
      have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- The original commutator constant bounds the even middle defect for every
positive expansion order and every real time. -/
theorem norm_halfDefect_add_sub_sum_le_commutator_list (l : List A) (X Y : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖halfDefect l (X + Y) x + halfDefect l (X + Y) (-x) -
      ∑ k ∈ range p, (x ^ k + (-x) ^ k) •
        groupedConjCoeff (fun i : Fin l.length ↦ -l.get i) l.get
          (-(1 / 2 : ℝ) • (X + Y)) k‖ ≤
      (p + 1 : ℝ) * halfDefectCommutatorConstant l X Y p * |x| ^ p := by
  let c := groupedConjCoeff (fun i : Fin l.length ↦ -l.get i) l.get
    (-(1 / 2 : ℝ) • (X + Y))
  let C := halfDefectCommutatorConstant l X Y p
  have hb (t : ℝ) : ‖halfDefect l (X + Y) t - ∑ k ∈ range p, t ^ k • c k‖ ≤
      ((p + 1 : ℝ) / 2) * C * |t| ^ p :=
    norm_halfDefect_sub_sum_le_commutator l X Y hZ p hp t
  change ‖_ + _ - ∑ k ∈ range p, (x ^ k + (-x) ^ k) • c k‖ ≤ (p + 1 : ℝ) * C * |x| ^ p
  simp_rw [add_smul]
  rw [sum_add_distrib, add_sub_add_comm]
  calc
    _ ≤ ‖halfDefect l (X + Y) x - ∑ k ∈ range p, x ^ k • c k‖ +
        ‖halfDefect l (X + Y) (-x) - ∑ k ∈ range p, (-x) ^ k • c k‖ := norm_add_le _ _
    _ ≤ ((p + 1 : ℝ) / 2) * C * |x| ^ p +
        ((p + 1 : ℝ) / 2) * C * |-x| ^ p := add_le_add (hb x) (hb (-x))
    _ = _ := by
      rw [abs_neg]
      ring

/-- The finite-family form of the ordinary even-defect remainder, with exactly
the original multinomial constant and the grouped polynomial coefficients. -/
theorem norm_halfDefect_add_sub_sum_le_commutator {s : ℕ} (Z : Fin s → A) (X Y : A)
    (hZ : ∀ (i : Fin s) (t : ℝ), ‖exp (t • Z i)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖halfDefect (List.ofFn Z) (X + Y) x + halfDefect (List.ofFn Z) (X + Y) (-x) -
      ∑ k ∈ range p, (x ^ k + (-x) ^ k) •
        groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • (X + Y)) k‖ ≤
      (p + 1 : ℝ) * halfDefectCommutatorConstant (List.ofFn Z) X Y p * |x| ^ p := by
  have hlist : ∀ z ∈ List.ofFn Z, ∀ t : ℝ, ‖exp (t • z)‖ ≤ 1 := by
    intro z hz t
    rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩
    exact hZ i t
  simpa only [groupedConjCoeff_get_ofFn] using
    norm_halfDefect_add_sub_sum_le_commutator_list (List.ofFn Z) X Y hlist p hp x

end Analysis

end FQFP
