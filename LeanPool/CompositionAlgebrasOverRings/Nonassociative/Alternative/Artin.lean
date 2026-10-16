/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Moufang
public import Mathlib.RingTheory.NonUnitalSubring.Basic

/-!
# Artin's theorem

**Artin's theorem.** A non-associative ring is alternative if and only if every subring generated
by two elements is associative.

## Proof strategy

The hard direction follows Schafer's proof of Theorem 3.1. First prove the result for
non-associative monomials in the two generators, by strong induction on the sum of the three
degrees. At a fixed induction stage every shorter monomial can be reassociated so that its first
letter is exposed. Two of the three monomials begin with the same generator, and Schafer's
linearized Moufang identity reduces their associator to associators of smaller total degree.

Finally, every element of `NonUnitalSubring.closure {a, b}` is an additive combination of such
monomials. Trilinearity of the associator therefore extends the monomial result to the closure.

## The reduction

The Teichmüller identity, mathlib's `associator_cocycle`, holds in *any* non-associative ring:

`w * [x,y,z] - [wx, y, z] + [w, xy, z] - [w, x, yz] + [w,x,y] * z = 0`

Say `n` is **nuclear in** `S` when `[n, y, z] = 0` for all `y, z ∈ S`. If `S` is closed under
multiplication, then the elements of `S` nuclear in `S` are closed under `0`, `+`, `-` (associator
additivity) and under `*` (Teichmüller — see `IsNuclearIn.mul`, where every term but `[wx, y, z]`
vanishes). So the nucleus of `S` is a subring of `S`.

Consequently, if the generators `a, b` are nuclear in `S = ⟨a, b⟩`, the nucleus contains
`{a, b}`, hence contains the whole closure, hence equals `S` — exactly associativity of `S`.

⚠ Note that **none of this uses alternativity**. Alternativity enters in the monomial argument
that proves `generators_nuclear`.

## References

* E. Artin, *Zur Theorie der hyperkomplexen Zahlen*, Abh. Math. Sem. Univ. Hamburg **5** (1927),
  251–260.
* Schafer, *An Introduction to Nonassociative Algebras*, §3, Theorem 3.1.
* Zhevlakov, Slin'ko, Shestakov, Shirshov, *Rings That Are Nearly Associative*, ch. 2.
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Ch. 13.
-/

@[expose] public section

universe u

/-! ## Non-associative monomials -/

/-- A nonempty, non-associatively parenthesized word in two letters. -/
inductive NonAssocWord where
  | left
  | right
  | mul (p q : NonAssocWord)

namespace NonAssocWord

/-- The number of letters in a non-associative word. -/
@[simp] def degree : NonAssocWord → ℕ
  | left | right => 1
  | mul p q => p.degree + q.degree

/-- Evaluate a non-associative word at two elements. -/
@[simp] def eval {α : Type u} [Mul α] (a b : α) : NonAssocWord → α
  | left => a
  | right => b
  | mul p q => p.eval a b * q.eval a b

/-- The one-letter word selected by a Boolean. -/
def ofBool : Bool → NonAssocWord
  | false => left
  | true => right

/-- The element selected by a Boolean. -/
def letter {α : Type u} (a b : α) : Bool → α
  | false => a
  | true => b

@[simp] theorem degree_pos (p : NonAssocWord) : 0 < p.degree := by
  induction p with
  | left => exact Nat.zero_lt_one
  | right => exact Nat.zero_lt_one
  | mul p q hp _ =>
      exact Nat.add_pos_left hp q.degree

@[simp] theorem degree_ofBool (x : Bool) : (ofBool x).degree = 1 := by cases x <;> rfl

@[simp] theorem eval_ofBool {α : Type u} [Mul α] (a b : α) (x : Bool) :
    (ofBool x).eval a b = letter a b x := by
  cases x <;> rfl

/-- Evaluation of a word with its first letter exposed. -/
def prependEval {α : Type u} [Mul α] (a b : α) (x : Bool) :
    Option NonAssocWord → α
  | none => letter a b x
  | some p => letter a b x * p.eval a b

/-- Degree of a word with its first letter exposed. -/
def prependDegree : Option NonAssocWord → ℕ
  | none => 1
  | some p => p.degree + 1

end NonAssocWord

/-- Two-generated associativity, as a predicate on a ring. -/
def TwoGeneratedAssoc (α : Type u) [NonUnitalNonAssocRing α] : Prop :=
  ∀ (a b : α) {x y z : α},
    x ∈ NonUnitalSubring.closure ({a, b} : Set α) →
    y ∈ NonUnitalSubring.closure ({a, b} : Set α) →
    z ∈ NonUnitalSubring.closure ({a, b} : Set α) →
    (x * y) * z = x * (y * z)

/-! ## Nuclearity relative to a set -/

section Nucleus

variable {α : Type u} [NonUnitalNonAssocRing α]

/-- `n` is **nuclear in** `S` if the associator vanishes whenever `n` occupies the first slot and
the other two arguments lie in `S`.

In an alternative ring the associator is alternating, so this single condition is equivalent to
nuclearity in any of the three slots (`IsAlternative.associator_swap_left`,
`IsAlternative.associator_swap_right`). The proofs below need only the first-slot form. -/
def IsNuclearIn (S : Set α) (n : α) : Prop := ∀ y ∈ S, ∀ z ∈ S, associator n y z = 0

namespace IsNuclearIn

variable {S : Set α} {m n : α}

theorem zero : IsNuclearIn S 0 := fun _ _ _ _ ↦ associator_zero_left _ _

theorem add (hm : IsNuclearIn S m) (hn : IsNuclearIn S n) : IsNuclearIn S (m + n) := by
  intro y hy z hz
  rw [associator_add_left, hm y hy z hz, hn y hy z hz, add_zero]

theorem neg (hm : IsNuclearIn S m) : IsNuclearIn S (-m) := by
  intro y hy z hz
  rw [associator_neg_left, hm y hy z hz, neg_zero]

/-- The nucleus is closed under multiplication. This is the Teichmüller identity
(`associator_cocycle`): with `w = m` and `x = n`, every term but `[mn, y, z]` vanishes.

Requires `S` closed under multiplication, and `m, n ∈ S` (not merely nuclear in `S`). -/
theorem mul (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hm : IsNuclearIn S m) (hn : IsNuclearIn S n) (_hmS : m ∈ S) (hnS : n ∈ S) :
    IsNuclearIn S (m * n) := by
  intro y hy z hz
  have key := associator_cocycle m n y z
  have h1 : associator m (n * y) z = 0 := hm _ (hS _ hnS _ hy) _ hz
  have h2 : associator m n (y * z) = 0 := hm _ hnS _ (hS _ hy _ hz)
  have h3 : associator n y z = 0 := hn _ hy _ hz
  have h4 : associator m n y = 0 := hm _ hnS _ hy
  rw [h1, h2, h3, h4] at key
  simpa using key

end IsNuclearIn

end Nucleus

namespace IsAlternative

/-! ## Easy direction -/

variable {α : Type u} [NonUnitalNonAssocRing α]

/-- If every two-generated subring is associative, the left alternative law holds. -/
theorem left_alt_of_two_generated_assoc (h : TwoGeneratedAssoc α) (a b : α) :
    a * (a * b) = (a * a) * b := by
  refine (h a b ?_ ?_ ?_).symm
  · exact NonUnitalSubring.subset_closure (Or.inl rfl)
  · exact NonUnitalSubring.subset_closure (Or.inl rfl)
  · exact NonUnitalSubring.subset_closure (Or.inr rfl)

/-- If every two-generated subring is associative, the right alternative law holds. -/
theorem right_alt_of_two_generated_assoc (h : TwoGeneratedAssoc α) (a b : α) :
    (b * a) * a = b * (a * a) := by
  refine h a b ?_ ?_ ?_
  · exact NonUnitalSubring.subset_closure (Or.inr rfl)
  · exact NonUnitalSubring.subset_closure (Or.inl rfl)
  · exact NonUnitalSubring.subset_closure (Or.inl rfl)

/-- **Artin's theorem, easy direction**: two-generated associativity implies alternativity. -/
theorem of_two_generated_assoc (h : TwoGeneratedAssoc α) : IsAlternative α where
  left_alt := left_alt_of_two_generated_assoc h
  right_alt := right_alt_of_two_generated_assoc h

/-! ## Hard direction -/

section Hard
variable [IsAlternative α]

/-! ### The associator identities used by Schafer's induction -/

/-- A form of the right Moufang identity used in the proof of Artin's theorem
[Schafer, (3.7)]. -/
theorem associator_mul_right_self (y x c : α) :
    associator y (x * c) x = -associator y x c * x := by
  simp only [associator]
  rw [flexible, ← right_moufang x c y]
  simp only [neg_mul]
  rw [sub_mul]
  abel

/-- The linearization of `associator_mul_right_self` [Schafer, (3.8)]. -/
theorem associator_mul_right_self_linearized (y x z c : α) :
    associator y (x * c) z + associator y (z * c) x =
      -associator y x c * z - associator y z c * x := by
  have h := associator_mul_right_self y (x + z) c
  have hx := associator_mul_right_self y x c
  have hz := associator_mul_right_self y z c
  simp only [add_mul, mul_add, associator_add_mid, associator_add_right, neg_add_rev,
    neg_mul] at h
  rw [hx, hz] at h
  simp only [neg_mul] at h ⊢
  have h' := congrArg (fun w ↦
    w + associator y x c * x + associator y z c * z) h
  abel_nf at h' ⊢
  exact h'

/-- A cyclic permutation does not change an associator in an alternative ring. -/
theorem associator_cyclic (x y z : α) : associator x y z = associator y z x := by
  rw [associator_swap_left, associator_swap_right, neg_neg]

/-- Swapping the outside arguments negates an associator. -/
theorem associator_swap_outer (x y z : α) : associator x y z = -associator z y x := by
  rw [associator_cyclic, associator_cyclic, associator_swap_right]

open NonAssocWord

omit [IsAlternative α] in
/-- If all associators of words of total degree less than `n` vanish, then every word of degree
less than `n` can be reassociated to expose its first letter. -/
theorem exists_head (a b : α) {n : ℕ}
    (h : ∀ p q r : NonAssocWord,
      p.degree + q.degree + r.degree < n →
        associator (p.eval a b) (q.eval a b) (r.eval a b) = 0)
    (w : NonAssocWord) (hw : w.degree < n) :
    ∃ x t, w.eval a b = prependEval a b x t ∧ w.degree = prependDegree t := by
  induction w with
  | left => exact ⟨false, none, rfl, rfl⟩
  | right => exact ⟨true, none, rfl, rfl⟩
  | mul p q ihp _ =>
      obtain ⟨x, t, hp, hdegree⟩ := ihp (by simp only [degree] at hw ⊢; omega)
      cases t with
      | none =>
          refine ⟨x, some q, ?_, ?_⟩
          · simpa only [eval, prependEval] using congrArg (· * q.eval a b) hp
          · simp only [degree, prependDegree] at hdegree ⊢
            omega
      | some p' =>
          have hassoc :
              (letter a b x * p'.eval a b) * q.eval a b =
                letter a b x * (p'.eval a b * q.eval a b) := by
            apply (associator_eq_zero_iff _ _ _).mp
            simpa only [eval_ofBool] using h (ofBool x) p' q (by
              simp only [degree, degree_ofBool, prependDegree] at hw hdegree ⊢
              omega)
          refine ⟨x, some (.mul p' q), ?_, ?_⟩
          · simp only [eval, prependEval]
            rw [hp]
            exact hassoc
          · simp only [degree, prependDegree] at hw hdegree ⊢
            omega

/-- Schafer's induction step when the last two words start with the same letter. -/
theorem associator_prepend_same_head (a b : α) {n : ℕ}
    (h : ∀ p q r : NonAssocWord,
      p.degree + q.degree + r.degree < n →
        associator (p.eval a b) (q.eval a b) (r.eval a b) = 0)
    (p : NonAssocWord) (x : Bool) (qTail rTail : Option NonAssocWord)
    (hdegree : p.degree + prependDegree qTail + prependDegree rTail = n) :
    associator (p.eval a b) (prependEval a b x qTail) (prependEval a b x rTail) = 0 := by
  cases qTail with
  | none =>
      cases rTail with
      | none => exact associator_self_right _ _
      | some r =>
          simp only [prependEval]
          rw [associator_swap_right, associator_mul_right_self]
          have hsmall := h p (ofBool x) r (by
            simp only [prependDegree, degree_ofBool] at hdegree ⊢
            omega)
          simp only [eval_ofBool] at hsmall
          rw [hsmall, neg_zero, zero_mul, neg_zero]
  | some q =>
      cases rTail with
      | none =>
          simp only [prependEval]
          rw [associator_mul_right_self]
          have hsmall := h p (ofBool x) q (by
            simp only [prependDegree, degree_ofBool] at hdegree ⊢
            omega)
          simp only [eval_ofBool] at hsmall
          rw [hsmall, neg_zero, zero_mul]
      | some r =>
          have hpdegree := p.degree_pos
          have hleft := h (.mul (ofBool x) r) (ofBool x) q (by
            simp only [degree, degree_ofBool, prependDegree] at hdegree ⊢
            omega)
          have hmid := h (.mul (ofBool x) r) p q (by
            simp only [degree, degree_ofBool, prependDegree] at hdegree ⊢
            omega)
          have hright := h (.mul p q) (ofBool x) r (by
            simp only [degree, degree_ofBool, prependDegree] at hdegree ⊢
            omega)
          simp only [eval, eval_ofBool] at hleft hmid hright
          have hlast :
              associator (letter a b x * r.eval a b) (p.eval a b * q.eval a b)
                (letter a b x) = 0 := by
            rw [associator_swap_outer, associator_cyclic,
              associator_mul_right_self, hright, neg_zero, zero_mul, neg_zero]
          have hlinear := associator_mul_right_self_linearized
            (letter a b x * r.eval a b) (letter a b x) (p.eval a b) (q.eval a b)
          rw [hleft, hmid, hlast, neg_zero, zero_mul, add_zero] at hlinear
          simp only [zero_mul, sub_zero] at hlinear
          simp only [prependEval]
          calc
            associator (p.eval a b) (letter a b x * q.eval a b)
                (letter a b x * r.eval a b) =
                -associator (letter a b x * r.eval a b)
                  (letter a b x * q.eval a b) (p.eval a b) := associator_swap_outer _ _ _
            _ = -0 := congrArg Neg.neg hlinear
            _ = 0 := neg_zero

/-- The associator of three non-associative monomials in two elements vanishes. This is the
monomial form of Artin's theorem [Schafer, Theorem 3.1]. -/
theorem associator_word (a b : α) (p q r : NonAssocWord) :
    associator (p.eval a b) (q.eval a b) (r.eval a b) = 0 := by
  generalize hn : p.degree + q.degree + r.degree = n
  induction n using Nat.strong_induction_on generalizing p q r with
  | h n ih =>
      have lower : ∀ p' q' r' : NonAssocWord,
          p'.degree + q'.degree + r'.degree < n →
            associator (p'.eval a b) (q'.eval a b) (r'.eval a b) = 0 := by
        intro p' q' r' hlt
        exact ih _ hlt p' q' r' rfl
      obtain ⟨xp, pt, hp, hpDegree⟩ := exists_head a b lower p (by
        have hqpos := q.degree_pos
        have hrpos := r.degree_pos
        omega)
      obtain ⟨xq, qt, hq, hqDegree⟩ := exists_head a b lower q (by
        have hppos := p.degree_pos
        have hrpos := r.degree_pos
        omega)
      obtain ⟨xr, rt, hr, hrDegree⟩ := exists_head a b lower r (by
        have hppos := p.degree_pos
        have hqpos := q.degree_pos
        omega)
      have hpigeon : xp = xq ∨ xq = xr ∨ xp = xr := by
        cases xp <;> cases xq <;> cases xr <;> simp
      rcases hpigeon with hpq | hqr | hpr
      · subst xq
        rw [associator_cyclic, associator_cyclic, hp, hq]
        apply associator_prepend_same_head a b lower r xp pt qt
        omega
      · subst xr
        rw [hq, hr]
        apply associator_prepend_same_head a b lower p xq qt rt
        omega
      · subst xr
        rw [associator_cyclic, hr, hp]
        apply associator_prepend_same_head a b lower q xp rt pt
        omega

/-! ### From monomials to the additive closure -/

/-- Additive combinations of non-associative monomials in `a` and `b`. -/
inductive WordSpan (a b : α) : α → Prop where
  | word (p : NonAssocWord) : WordSpan a b (p.eval a b)
  | zero : WordSpan a b 0
  | add {x y : α} : WordSpan a b x → WordSpan a b y → WordSpan a b (x + y)
  | neg {x : α} : WordSpan a b x → WordSpan a b (-x)

namespace WordSpan

omit [IsAlternative α] in
/-- The additive span of words is closed under multiplication. -/
theorem mul {a b x y : α} (hx : WordSpan a b x) (hy : WordSpan a b y) :
    WordSpan a b (x * y) := by
  induction hx generalizing y with
  | word p =>
      induction hy with
      | word q => exact word (.mul p q)
      | zero => simpa only [mul_zero] using (zero : WordSpan a b 0)
      | add _ _ ihx ihy => simpa only [mul_add] using ihx.add ihy
      | neg _ ih => simpa only [mul_neg] using ih.neg
  | zero => simpa only [zero_mul] using (zero : WordSpan a b 0)
  | add _ _ ihx ihy =>
      simpa only [add_mul] using (ihx hy).add (ihy hy)
  | neg _ ih => simpa only [neg_mul] using (ih hy).neg

omit [IsAlternative α] in
/-- Every element of the non-associative ring closure is an additive combination of words. -/
theorem of_mem_closure (a b : α) {x : α}
    (hx : x ∈ NonUnitalSubring.closure ({a, b} : Set α)) : WordSpan a b x := by
  induction hx using NonUnitalSubring.closure_induction with
  | mem x hx =>
      change x = a ∨ x = b at hx
      rcases hx with rfl | rfl
      · exact word .left
      · exact word .right
  | zero => exact zero
  | add _ _ _ _ ihx ihy => exact ihx.add ihy
  | neg _ _ ih => exact ih.neg
  | mul _ _ _ _ ihx ihy => exact ihx.mul ihy

/-- A word is nuclear relative to the additive span of all words. -/
theorem word_nuclear (a b : α) (p : NonAssocWord) :
    IsNuclearIn {x | WordSpan a b x} (p.eval a b) := by
  intro y hy z hz
  induction hy generalizing z with
  | word q =>
      induction hz with
      | word r => exact associator_word a b p q r
      | zero => exact associator_zero_right _ _
      | add _ _ ihx ihy =>
          rw [associator_add_right, ihx, ihy, add_zero]
      | neg _ ih => rw [associator_neg_right, ih, neg_zero]
  | zero => exact associator_zero_mid _ _
  | add _ _ ihx ihy =>
      rw [associator_add_mid, ihx z hz, ihy z hz, add_zero]
  | neg _ ih => rw [associator_neg_mid, ih z hz, neg_zero]

/-- Every additive combination of words is nuclear relative to the span. -/
theorem nuclear {a b x : α} (hx : WordSpan a b x) :
    IsNuclearIn {y | WordSpan a b y} x := by
  induction hx with
  | word p => exact word_nuclear a b p
  | zero => exact IsNuclearIn.zero
  | add _ _ ihx ihy => exact ihx.add ihy
  | neg _ ih => exact ih.neg

end WordSpan

/-- The associator vanishes on any triple drawn from `{a, b}`: two of the three arguments coincide
by pigeonhole, and the associator is alternating.

This is the base case of `generators_nuclear`. -/
theorem associator_of_mem_pair (a b : α) {x y z : α}
    (hx : x ∈ ({a, b} : Set α)) (hy : y ∈ ({a, b} : Set α)) (hz : z ∈ ({a, b} : Set α)) :
    associator x y z = 0 := by
  change x = a ∨ x = b at hx
  change y = a ∨ y = b at hy
  change z = a ∨ z = b at hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp [associator_self_left, associator_self_right, associator_self_mid]

/-- Each generator is nuclear in the non-associative subring generated by the pair. -/
theorem generators_nuclear (a b : α) :
    IsNuclearIn (NonUnitalSubring.closure ({a, b} : Set α) : Set α) a ∧
      IsNuclearIn (NonUnitalSubring.closure ({a, b} : Set α) : Set α) b := by
  constructor
  · intro y hy z hz
    exact WordSpan.word_nuclear a b .left y (WordSpan.of_mem_closure a b hy) z
      (WordSpan.of_mem_closure a b hz)
  · intro y hy z hz
    exact WordSpan.word_nuclear a b .right y (WordSpan.of_mem_closure a b hy) z
      (WordSpan.of_mem_closure a b hz)

/-- Every element of the closure is nuclear in the closure.

Pure nucleus bookkeeping on top of `generators_nuclear`: the nuclear elements form a subring
(`IsNuclearIn.zero/add/neg/mul`), so they contain the closure of the generators. -/
theorem nuclear_of_mem_closure (a b : α) {x : α}
    (hx : x ∈ NonUnitalSubring.closure ({a, b} : Set α)) :
    IsNuclearIn (NonUnitalSubring.closure ({a, b} : Set α) : Set α) x := by
  have hab := generators_nuclear a b
  have hS : ∀ u ∈ (NonUnitalSubring.closure ({a, b} : Set α) : Set α),
      ∀ v ∈ (NonUnitalSubring.closure ({a, b} : Set α) : Set α),
      u * v ∈ (NonUnitalSubring.closure ({a, b} : Set α) : Set α) :=
    fun _ hu _ hv ↦ mul_mem hu hv
  induction hx using NonUnitalSubring.closure_induction with
  | mem w hw =>
      change w = a ∨ w = b at hw
      rcases hw with rfl | rfl
      · exact hab.1
      · exact hab.2
  | zero => exact IsNuclearIn.zero
  | add _ _ _ _ ihx ihy => exact ihx.add ihy
  | neg _ _ ih => exact ih.neg
  | mul _ _ hx' hy' ihx ihy => exact ihx.mul hS ihy hx' hy'

/-- **Artin's theorem, hard direction**: in an alternative ring, the subring generated by any two
elements is associative. -/
theorem artin_two_generated_assoc : TwoGeneratedAssoc α := by
  intro a b x y z hx hy hz
  exact (associator_eq_zero_iff x y z).mp (nuclear_of_mem_closure a b hx y hy z hz)

end Hard

/-- **Artin's theorem.** -/
theorem isAlternative_iff_two_generated_assoc :
    IsAlternative α ↔ TwoGeneratedAssoc α :=
  ⟨fun _ ↦ artin_two_generated_assoc, of_two_generated_assoc⟩

end IsAlternative
