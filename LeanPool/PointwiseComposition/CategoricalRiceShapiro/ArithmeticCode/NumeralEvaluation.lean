/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EvaluationCongruence
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.PartialRecursive
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Evaluation of the derived constructors at standard numerals

Where `CategoricalRiceShapiro.ArithmeticCode.Evaluation` characterises the
graph of a constructor at arbitrary values, the results here compute it at the
image of a natural number.  A code whose graph holds at `(n : M)` has, at the
same assignment, the graph of its truncated difference, integer square root and
Cantor components at the corresponding natural numbers.

`eval_codeIfPos_of` is the introduction rule for the eager conditional and is
used by every proof below; it evaluates both branches, as the construction does.

`eval_of_computes` is the bridge from the standard model: a code that realizes a
function over `ℕ` has, in any model of `𝐏𝐀⁻`, the graph of that function at the
images of standard arguments.  It is the only route by which a construction
proved correct over `ℕ` — here halving, defined by primitive recursion — becomes
usable in an arbitrary model.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M]

/-!
### The eager conditional -/

/-- Introduction rule for `codeIfPos`.  Both branches are evaluated, and the
test selects which of their values the conditional takes. -/
theorem eval_codeIfPos_of [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (df dg dh : Code k) (f g h z : M)
    (vv : Fin k → M) (hf : Semiformula.Evalb (f :> vv) (code df))
    (hg : Semiformula.Evalb (g :> vv) (code dg)) (hh : Semiformula.Evalb (h :> vv) (code dh))
    (hz : (0 < f ∧ z = g) ∨ (f = 0 ∧ z = h)) :
    Semiformula.Evalb (z :> vv) (code (codeIfPos df dg dh)) :=
  by
  have hfne : 0 < f → f ≠ 0 := by
    intro hpos hc
    rw [hc] at hpos
    exact absurd hpos (_root_.lt_irrefl 0)
  simp only [codeIfPos]
  rcases hz with ⟨hfpos, hzg⟩ | ⟨hf0, hzh⟩
  · rw [hzg]
    refine (eval_codeAdd_iff _ _ _ vv).mpr ⟨g, 0, ?_, ?_, by simp⟩
    · exact
        (eval_codeMul_iff _ _ _ vv).mpr
          ⟨1, g, (eval_codePos_iff _ _ vv).mpr ⟨f, hf, Or.inl ⟨hfpos, rfl⟩⟩, hg, by simp⟩
    · exact
        (eval_codeMul_iff _ _ _ vv).mpr
          ⟨0, h, (eval_codeInv_iff _ _ vv).mpr ⟨f, hf, Or.inr ⟨hfne hfpos, rfl⟩⟩, hh, by simp⟩
  · rw [hzh]
    refine (eval_codeAdd_iff _ _ _ vv).mpr ⟨0, h, ?_, ?_, by simp⟩
    · refine (eval_codeMul_iff _ _ _ vv).mpr ⟨0, g, ?_, hg, by simp⟩
      refine (eval_codePos_iff _ _ vv).mpr ⟨f, hf, Or.inr ⟨?_, rfl⟩⟩
      rw [hf0]
      exact _root_.lt_irrefl 0
    · exact
        (eval_codeMul_iff _ _ _ vv).mpr
          ⟨1, h, (eval_codeInv_iff _ _ vv).mpr ⟨f, hf, Or.inl ⟨hf0, rfl⟩⟩, hh, by simp⟩

/-- Elimination rule for `codeIfPos`: a value of the conditional comes from one
of the two branches, chosen by the test.  Converse of `eval_codeIfPos_of`. -/
theorem eval_codeIfPos_cases [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (df dg dh : Code k) (z : M)
    (vv : Fin k → M) (hz : Semiformula.Evalb (z :> vv) (code (codeIfPos df dg dh))) :
    ∃ f : M,
      Semiformula.Evalb (f :> vv) (code df) ∧
        ((0 < f ∧ Semiformula.Evalb (z :> vv) (code dg)) ∨
          (f = 0 ∧ Semiformula.Evalb (z :> vv) (code dh))) :=
  by
  rw [codeIfPos, eval_codeAdd_iff] at hz
  obtain ⟨p, q, hp, hq, hzpq⟩ := hz
  rw [eval_codeMul_iff] at hp
  obtain ⟨pp, gg, hpp, hgg, hpv⟩ := hp
  rw [eval_codeMul_iff] at hq
  obtain ⟨ii, hh, hii, hhh, hqv⟩ := hq
  rw [eval_codePos_iff] at hpp
  obtain ⟨a, ha, hacase⟩ := hpp
  rw [eval_codeInv_iff] at hii
  obtain ⟨a', ha', ha'case⟩ := hii
  have haa : a' = a := eval_unique ha' ha
  rw [haa] at ha'case
  refine ⟨a, ha, ?_⟩
  rcases hacase with ⟨hpos, hpp1⟩ | ⟨hnpos, hpp0⟩
  · have hane : ¬a = 0 := by
      intro h
      rw [h] at hpos
      exact absurd hpos (_root_.lt_irrefl 0)
    have hii0 : ii = 0 := by
      rcases ha'case with ⟨h0, -⟩ | ⟨-, h0⟩
      · exact absurd h0 hane
      · exact h0
    have hzg : z = gg := by rw [hzpq, hpv, hqv, hpp1, hii0, one_mul, zero_mul, add_zero]
    refine Or.inl ⟨hpos, ?_⟩
    rw [hzg]; exact hgg
  · have ha0 : a = 0 := by
      by_contra hne
      exact hnpos (pos_iff_ne_zero.mpr hne)
    have hii1 : ii = 1 := by
      rcases ha'case with ⟨-, h1⟩ | ⟨h0, -⟩
      · exact h1
      · exact absurd ha0 h0
    have hzh : z = hh := by rw [hzpq, hpv, hqv, hpp0, hii1, one_mul, zero_mul, zero_add]
    refine Or.inr ⟨ha0, ?_⟩
    rw [hzh]; exact hhh

/-!
### Truncated subtraction -/

/-- Truncated subtraction at standard numerals. -/
theorem eval_codeSub_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A B : Code k) (a b : ℕ) (vv : Fin k → M)
    (hA : Semiformula.Evalb (((a : ℕ) : M) :> vv) (code A))
    (hB : Semiformula.Evalb (((b : ℕ) : M) :> vv) (code B)) :
    Semiformula.Evalb ((((a - b : ℕ)) : M) :> vv) (code (codeSub A B)) :=
  by
  have hlift :
    ∀ (X : Code k) (x t : M),
      Semiformula.Evalb (x :> vv) (code X) →
        Semiformula.Evalb (x :> t :> vv) (code (codeLift X)) :=
    fun X x t hX => (eval_codeLift_iff X x t vv).mpr hX
  have hhead : ∀ t : M, Semiformula.Evalb (t :> t :> vv) (code (codeHead (n := k))) := fun t =>
    (eval_codeHead_iff t (t :> vv)).mpr rfl
  have hYzero :
    b ≤ a →
      ∀ t : M,
        Semiformula.Evalb ((0 : M) :> t :> vv)
          (code
            (codeAnd (codeLt (codeLift A) (codeLift B))
              (codeEq (codeHead (n := k)) (Code.zero (k + 1))))) :=
    by
    intro hba t
    have hnab : ¬((a : ℕ) : M) < ((b : ℕ) : M) :=
      by
      intro hc
      have : a < b := by exact_mod_cast hc
      omega
    have hlt :
      Semiformula.Evalb ((0 : M) :> t :> vv) (code (codeLt (codeLift A) (codeLift B))) :=
      (eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hlift A _ t hA, hlift B _ t hB, Or.inr ⟨hnab, rfl⟩⟩
    have hz0 : Semiformula.Evalb ((0 : M) :> t :> vv) (code (Code.zero (k + 1))) :=
      (eval_zero_iff _ _).mpr rfl
    by_cases ht0 : t = (0 : M)
    · exact
        (eval_codeAnd_iff _ _ _ _).mpr
          ⟨0, 1, hlt, (eval_codeEq_iff _ _ _ _).mpr ⟨t, 0, hhead t, hz0, Or.inl ⟨ht0, rfl⟩⟩,
            Or.inr ⟨by simp, rfl⟩⟩
    · exact
        (eval_codeAnd_iff _ _ _ _).mpr
          ⟨0, 0, hlt, (eval_codeEq_iff _ _ _ _).mpr ⟨t, 0, hhead t, hz0, Or.inr ⟨ht0, rfl⟩⟩,
            Or.inr ⟨by simp, rfl⟩⟩
  simp only [codeSub]
  rw [eval_codeRfindPos_iff]
  by_cases hba : b ≤ a
  · have hsum : (((a - b : ℕ)) : M) + ((b : ℕ) : M) = ((a : ℕ) : M) :=
      by
      have hn : (a - b) + b = a := by omega
      calc
        (((a - b : ℕ)) : M) + ((b : ℕ) : M) = (((a - b) + b : ℕ) : M) := by push_cast; rfl
        _ = ((a : ℕ) : M) := by rw [hn]
    constructor
    · refine ⟨1, _root_.zero_lt_one, ?_⟩
      refine (eval_codeOr_iff _ _ _ _).mpr ⟨1, 0, ?_, hYzero hba _, Or.inl ⟨by simp, rfl⟩⟩
      exact
        (eval_codeEq_iff _ _ _ _).mpr
          ⟨_, _, (eval_codeAdd_iff _ _ _ _).mpr ⟨_, _, hhead _, hlift B _ _ hB, rfl⟩,
            hlift A _ _ hA, Or.inl ⟨hsum, rfl⟩⟩
    · intro t ht
      refine (eval_codeOr_iff _ _ _ _).mpr ⟨0, 0, ?_, hYzero hba t, Or.inr ⟨by simp, rfl⟩⟩
      refine
        (eval_codeEq_iff _ _ _ _).mpr
          ⟨t + ((b : ℕ) : M), ((a : ℕ) : M),
            (eval_codeAdd_iff _ _ _ _).mpr ⟨t, _, hhead t, hlift B _ t hB, rfl⟩, hlift A _ t hA,
            Or.inr ⟨?_, rfl⟩⟩
      intro hcontra
      have h2 := add_lt_add_right ht (((b : ℕ)) : M)
      have h1 : t + ((b : ℕ) : M) < (((a - b : ℕ)) : M) + ((b : ℕ) : M) := by
        simpa [add_comm] using h2
      rw [hsum, hcontra] at h1
      exact absurd h1 (_root_.lt_irrefl _)
  · have hab : a < b := by omega
    have habM : ((a : ℕ) : M) < ((b : ℕ) : M) := by exact_mod_cast hab
    have hzero : (((a - b : ℕ)) : M) = (0 : M) :=
      by
      have hn : a - b = 0 := by omega
      rw [hn]; simp
    constructor
    · refine ⟨1, _root_.zero_lt_one, ?_⟩
      rw [hzero]
      refine (eval_codeOr_iff _ _ _ _).mpr ⟨0, 1, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩
      · refine
          (eval_codeEq_iff _ _ _ _).mpr
            ⟨(0 : M) + ((b : ℕ) : M), ((a : ℕ) : M),
              (eval_codeAdd_iff _ _ _ _).mpr ⟨0, _, hhead (0 : M), hlift B _ _ hB, rfl⟩,
              hlift A _ _ hA, Or.inr ⟨?_, rfl⟩⟩
        intro hcontra
        rw [zero_add] at hcontra
        rw [hcontra] at habM
        exact absurd habM (_root_.lt_irrefl _)
      · exact
          (eval_codeAnd_iff _ _ _ _).mpr
            ⟨1, 1,
              (eval_codeLt_iff _ _ _ _).mpr
                ⟨_, _, hlift A _ _ hA, hlift B _ _ hB, Or.inl ⟨habM, rfl⟩⟩,
              (eval_codeEq_iff _ _ _ _).mpr
                ⟨0, 0, hhead (0 : M), (eval_zero_iff _ _).mpr rfl, Or.inl ⟨rfl, rfl⟩⟩,
              Or.inl ⟨by simp, rfl⟩⟩
    · intro t ht
      rw [hzero] at ht
      exact absurd ht (by simp)

/-!
### Integer square root and Cantor unpairing -/

/-- The integer square root at a standard numeral. -/
theorem eval_codeSqrt_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (d : Code k) (n : ℕ) (v : Fin k → M)
    (hd : Semiformula.Evalb (((n : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((Nat.sqrt n : ℕ) : M) :> v) (code (codeSqrt d)) :=
  by
  have hcastmul : ∀ a b : ℕ, ((a : ℕ) : M) * ((b : ℕ) : M) = (((a * b : ℕ)) : M) := by
    intro a b; push_cast; rfl
  have hcastsucc : ∀ a : ℕ, ((a : ℕ) : M) + 1 = (((a + 1 : ℕ)) : M) :=
    by
    intro a
    push_cast
    rfl
  have hhead :
    ∀ j : ℕ,
      Semiformula.Evalb (((j : ℕ) : M) :> ((j : ℕ) : M) :> v) (code (codeHead (n := k))) :=
    fun j => (eval_codeHead_iff _ _).mpr rfl
  have hheadsq :
    ∀ j : ℕ,
      Semiformula.Evalb ((((j * j : ℕ)) : M) :> ((j : ℕ) : M) :> v)
        (code (codeMul (codeHead (n := k)) (codeHead (n := k)))) :=
    by
    intro j
    refine (eval_codeMul_iff _ _ _ _).mpr ⟨_, _, hhead j, hhead j, ?_⟩
    rw [hcastmul j j]
  have hheadsucc :
    ∀ j : ℕ,
      Semiformula.Evalb ((((j + 1 : ℕ)) : M) :> ((j : ℕ) : M) :> v)
        (code (codeSucc (codeHead (n := k)))) :=
    by
    intro j
    refine (eval_codeSucc_iff _ _ _).mpr ⟨_, hhead j, ?_⟩
    rw [hcastsucc j]
  have hheadsuccsq :
    ∀ j : ℕ,
      Semiformula.Evalb ((((j + 1) * (j + 1) : ℕ) : M) :> ((j : ℕ) : M) :> v)
        (code (codeMul (codeSucc (codeHead (n := k))) (codeSucc (codeHead (n := k))))) :=
    by
    intro j
    refine (eval_codeMul_iff _ _ _ _).mpr ⟨_, _, hheadsucc j, hheadsucc j, ?_⟩
    rw [hcastmul (j + 1) (j + 1)]
  have hliftd :
    ∀ j : ℕ, Semiformula.Evalb (((n : ℕ) : M) :> ((j : ℕ) : M) :> v) (code (codeLift d)) :=
    fun j => (eval_codeLift_iff d _ _ v).mpr hd
  have hAone :
    ∀ j : ℕ,
      j * j ≤ n →
        Semiformula.Evalb ((1 : M) :> ((j : ℕ) : M) :> v)
          (code
            (codeOr (codeLt (codeMul (codeHead (n := k)) (codeHead (n := k))) (codeLift d))
              (codeEq (codeMul (codeHead (n := k)) (codeHead (n := k))) (codeLift d)))) :=
    by
    intro j hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · refine (eval_codeOr_iff _ _ _ _).mpr ⟨1, 0, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩
      · exact
          (eval_codeLt_iff _ _ _ _).mpr
            ⟨_, _, hheadsq j, hliftd j, Or.inl ⟨by exact_mod_cast hlt, rfl⟩⟩
      · refine (eval_codeEq_iff _ _ _ _).mpr ⟨_, _, hheadsq j, hliftd j, Or.inr ⟨?_, rfl⟩⟩
        intro hc
        have : j * j = n := by exact_mod_cast hc
        omega
    · refine (eval_codeOr_iff _ _ _ _).mpr ⟨0, 1, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩
      · refine (eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hheadsq j, hliftd j, Or.inr ⟨?_, rfl⟩⟩
        intro hc
        have : j * j < n := by exact_mod_cast hc
        omega
      · exact
          (eval_codeEq_iff _ _ _ _).mpr
            ⟨_, _, hheadsq j, hliftd j, Or.inl ⟨by exact_mod_cast heq, rfl⟩⟩
  have hBval :
    ∀ (j : ℕ) (y : M),
      ((n < (j + 1) * (j + 1) ∧ y = 1) ∨ (¬n < (j + 1) * (j + 1) ∧ y = 0)) →
        Semiformula.Evalb (y :> ((j : ℕ) : M) :> v)
          (code
            (codeLt (codeLift d)
              (codeMul (codeSucc (codeHead (n := k))) (codeSucc (codeHead (n := k)))))) :=
    by
    intro j y hy
    refine (eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hliftd j, hheadsuccsq j, ?_⟩
    rcases hy with ⟨hlt, rfl⟩ | ⟨hnlt, rfl⟩
    · exact Or.inl ⟨by exact_mod_cast hlt, rfl⟩
    · exact Or.inr ⟨fun hc => hnlt (by exact_mod_cast hc), rfl⟩
  have hsqle : Nat.sqrt n * Nat.sqrt n ≤ n := by simpa [pow_two] using Nat.sqrt_le' n
  have hsqlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
    simpa [pow_two] using Nat.lt_succ_sqrt' n
  simp only [codeSqrt]
  rw [eval_codeRfindPos_iff]
  constructor
  · exact
      ⟨1, _root_.zero_lt_one,
        (eval_codeAnd_iff _ _ _ _).mpr
          ⟨1, 1, hAone (Nat.sqrt n) hsqle, hBval (Nat.sqrt n) 1 (Or.inl ⟨hsqlt, rfl⟩),
            Or.inl ⟨by simp, rfl⟩⟩⟩
  · intro t ht
    obtain ⟨j, rfl⟩ := FFL.FirstOrder.Arithmetic.eq_fin_of_lt_nat ht
    have hup : ((j : ℕ) + 1) * ((j : ℕ) + 1) ≤ n := by
      simpa [pow_two] using Nat.le_sqrt'.mp j.isLt
    have hjj : (j : ℕ) * (j : ℕ) < n :=
      lt_of_lt_of_le (Nat.mul_self_lt_mul_self (Nat.lt_succ_self (j : ℕ))) hup
    exact
      (eval_codeAnd_iff _ _ _ _).mpr
        ⟨1, 0, hAone (j : ℕ) (le_of_lt hjj), hBval (j : ℕ) 0 (Or.inr ⟨by omega, rfl⟩),
          Or.inr ⟨by simp, rfl⟩⟩

/-- The three subterms both Cantor components are built from, evaluated once. -/
private theorem eval_unpair_parts [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (d : Code k) (n : ℕ) (v : Fin k → M)
    (hd : Semiformula.Evalb (((n : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((Nat.sqrt n : ℕ) : M) :> v) (code (codeSqrt d)) ∧
      Semiformula.Evalb ((((n - Nat.sqrt n * Nat.sqrt n : ℕ)) : M) :> v)
          (code (codeSub d (codeMul (codeSqrt d) (codeSqrt d)))) ∧
        Semiformula.Evalb ((((n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n : ℕ)) : M) :> v)
          (code (codeSub (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d))) :=
  by
  have hsq := eval_codeSqrt_natCast d n v hd
  have hmulss :
    Semiformula.Evalb ((((Nat.sqrt n * Nat.sqrt n : ℕ)) : M) :> v)
      (code (codeMul (codeSqrt d) (codeSqrt d))) :=
    by
    refine (eval_codeMul_iff _ _ _ _).mpr ⟨_, _, hsq, hsq, ?_⟩
    push_cast; rfl
  have hsub1 := eval_codeSub_natCast d _ n (Nat.sqrt n * Nat.sqrt n) v hd hmulss
  exact
    ⟨hsq, hsub1,
      eval_codeSub_natCast _ _ (n - Nat.sqrt n * Nat.sqrt n) (Nat.sqrt n) v hsub1 hsq⟩

/-- The first Cantor component at a standard numeral. -/
theorem eval_codeUnpair₁_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (d : Code k) (n : ℕ) (v : Fin k → M)
    (hd : Semiformula.Evalb (((n : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb ((((Nat.unpair n).1 : ℕ) : M) :> v) (code (codeUnpair₁ d)) :=
  by
  obtain ⟨hsq, hsub1, -⟩ := eval_unpair_parts d n v hd
  by_cases hcase : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
  · have hu : (Nat.unpair n).1 = n - Nat.sqrt n * Nat.sqrt n := by simp [Nat.unpair, hcase]
    rw [hu]
    simp only [codeUnpair₁]
    refine
      eval_codeIfPos_of _ _ _ (1 : M) _ _ _ v ?_ hsub1 hsq (Or.inl ⟨_root_.zero_lt_one, rfl⟩)
    exact
      (eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hsub1, hsq, Or.inl ⟨by exact_mod_cast hcase, rfl⟩⟩
  · have hu : (Nat.unpair n).1 = Nat.sqrt n := by simp [Nat.unpair, hcase]
    rw [hu]
    simp only [codeUnpair₁]
    refine eval_codeIfPos_of _ _ _ (0 : M) _ _ _ v ?_ hsub1 hsq (Or.inr ⟨rfl, rfl⟩)
    exact
      (eval_codeLt_iff _ _ _ _).mpr
        ⟨_, _, hsub1, hsq, Or.inr ⟨fun hc => hcase (by exact_mod_cast hc), rfl⟩⟩

/-- The second Cantor component at a standard numeral. -/
theorem eval_codeUnpair₂_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (d : Code k) (n : ℕ) (v : Fin k → M)
    (hd : Semiformula.Evalb (((n : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb ((((Nat.unpair n).2 : ℕ) : M) :> v) (code (codeUnpair₂ d)) :=
  by
  obtain ⟨hsq, hsub1, hsub2⟩ := eval_unpair_parts d n v hd
  by_cases hcase : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
  · have hu : (Nat.unpair n).2 = Nat.sqrt n := by simp [Nat.unpair, hcase]
    rw [hu]
    simp only [codeUnpair₂]
    refine
      eval_codeIfPos_of _ _ _ (1 : M) _ _ _ v ?_ hsq hsub2 (Or.inl ⟨_root_.zero_lt_one, rfl⟩)
    exact
      (eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hsub1, hsq, Or.inl ⟨by exact_mod_cast hcase, rfl⟩⟩
  · have hu : (Nat.unpair n).2 = n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n := by
      simp [Nat.unpair, hcase]
    rw [hu]
    simp only [codeUnpair₂]
    refine eval_codeIfPos_of _ _ _ (0 : M) _ _ _ v ?_ hsq hsub2 (Or.inr ⟨rfl, rfl⟩)
    exact
      (eval_codeLt_iff _ _ _ _).mpr
        ⟨_, _, hsub1, hsq, Or.inr ⟨fun hc => hcase (by exact_mod_cast hc), rfl⟩⟩

/-!
### The standard-model bridge -/

/-- A code realizing `f` over `ℕ` has the graph of `f` at standard arguments in
any model of `𝐏𝐀⁻`.

`Computes` is a statement about `ℕ`.  Sigma-one completeness transports the
corresponding sentence, whose free variables are all interpreted by numerals. -/
theorem eval_of_computes [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (c : Code k) (f : List.Vector ℕ k → ℕ)
    (hc : Computes c f) (w : Fin k → ℕ) :
    Semiformula.Evalb (M := M)
      (((f (List.Vector.ofFn w) : ℕ) : M) :> (fun i => ((w i : ℕ) : M))) (code c) :=
  by
  have hnat : Semiformula.Evalb (M := ℕ) ((f (List.Vector.ofFn w)) :> w) (code c) :=
    (FFL.FirstOrder.Arithmetic.models_code hc _ w).mpr (by simp)
  have htr :=
    FFL.FirstOrder.Arithmetic.bold_sigma_one_completeness' (M := M)
      (FFL.FirstOrder.Arithmetic.code_sigma_one c) hnat
  rw [FFL.FirstOrder.Arithmetic.numeral_eq_natCast] at htr
  have heq :
    (Nat.cast ∘ ((f (List.Vector.ofFn w)) :> w) : Fin (k + 1) → M) =
      (((f (List.Vector.ofFn w) : ℕ) : M) :> (fun i => ((w i : ℕ) : M))) :=
    by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl
  rw [heq] at htr
  exact htr

/-- Halving at a standard numeral. -/
theorem eval_codeDiv2_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A : Code k) (n : ℕ) (vv : Fin k → M)
    (hA : Semiformula.Evalb (((n : ℕ) : M) :> vv) (code A)) :
    Semiformula.Evalb ((((Nat.div2 n : ℕ)) : M) :> vv) (code (codeDiv2 A)) :=
  by
  simp only [codeDiv2]
  refine (eval_comp_iff _ _ _ _).mpr ⟨fun i => (((![n] : Fin 1 → ℕ) i : ℕ) : M), ?_, ?_⟩
  · have hs :=
      eval_of_computes (M := M) codeDiv2Unary (fun w => Nat.div2 w.head) computes_codeDiv2Unary
        ![n]
    have hhead : (List.Vector.ofFn (![n] : Fin 1 → ℕ)).head = n := by simp
    rw [hhead] at hs
    exact hs
  · intro i
    refine Fin.cases ?_ (fun j => j.elim0) i
    simpa using hA

/-!
### Divisibility, remainder and parity -/

/-- Every element below a standard numeral is itself a standard numeral. -/
private theorem exists_lt_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] :
    ∀ (n : ℕ) (t : M), t < ((n : ℕ) : M) → ∃ j : ℕ, j < n ∧ t = ((j : ℕ) : M) :=
  by
  intro n
  induction n with
  | zero => intro t h; simp at h
  | succ m ih =>
    intro t h
    have hcast : (((m + 1 : ℕ)) : M) = ((m : ℕ) : M) + 1 := by push_cast; rfl
    rw [hcast] at h
    have hle : t ≤ ((m : ℕ) : M) := FFL.FirstOrder.Arithmetic.lt_succ_iff_le.mp h
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨j, hj, hjt⟩ := ih t hlt
      exact ⟨j, Nat.lt_succ_of_lt hj, hjt⟩
    · exact ⟨m, Nat.lt_succ_self m, heq⟩

/-- Introduction rule for the non-strict comparison. -/
theorem eval_codeLe_of [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A B : Code k) (x y z : M) (vv : Fin k → M)
    (hA : Semiformula.Evalb (x :> vv) (code A)) (hB : Semiformula.Evalb (y :> vv) (code B))
    (hz : (x ≤ y ∧ z = 1) ∨ (¬x ≤ y ∧ z = 0)) :
    Semiformula.Evalb (z :> vv) (code (codeLe A B)) :=
  by
  simp only [codeLe]
  by_cases hlt : x < y
  · refine (eval_codeOr_iff _ _ _ _).mpr ⟨1, 0, ?_, ?_, ?_⟩
    · exact (eval_codeLt_iff _ _ _ _).mpr ⟨x, y, hA, hB, Or.inl ⟨hlt, rfl⟩⟩
    · exact
        (eval_codeEq_iff _ _ _ _).mpr
          ⟨x, y, hA, hB, Or.inr ⟨fun hc => absurd (hc ▸ hlt) (_root_.lt_irrefl _), rfl⟩⟩
    · rcases hz with ⟨_, rfl⟩ | ⟨hnle, _⟩
      · exact Or.inl ⟨by simp, rfl⟩
      · exact absurd (le_of_lt hlt) hnle
  · by_cases heq : x = y
    · refine (eval_codeOr_iff _ _ _ _).mpr ⟨0, 1, ?_, ?_, ?_⟩
      · exact (eval_codeLt_iff _ _ _ _).mpr ⟨x, y, hA, hB, Or.inr ⟨hlt, rfl⟩⟩
      · exact (eval_codeEq_iff _ _ _ _).mpr ⟨x, y, hA, hB, Or.inl ⟨heq, rfl⟩⟩
      · rcases hz with ⟨_, rfl⟩ | ⟨hnle, _⟩
        · exact Or.inl ⟨by simp, rfl⟩
        · exact absurd (le_of_eq heq) hnle
    · refine (eval_codeOr_iff _ _ _ _).mpr ⟨0, 0, ?_, ?_, ?_⟩
      · exact (eval_codeLt_iff _ _ _ _).mpr ⟨x, y, hA, hB, Or.inr ⟨hlt, rfl⟩⟩
      · exact (eval_codeEq_iff _ _ _ _).mpr ⟨x, y, hA, hB, Or.inr ⟨heq, rfl⟩⟩
      · rcases hz with ⟨hle, _⟩ | ⟨_, rfl⟩
        · exact absurd (lt_of_le_of_ne hle heq) hlt
        · exact Or.inr ⟨by simp, rfl⟩

/-- Divisibility at standard numerals. -/
theorem eval_codeDvd_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A B : Code k) (a b : ℕ) (z : M)
    (vv : Fin k → M) (hA : Semiformula.Evalb (((a : ℕ) : M) :> vv) (code A))
    (hB : Semiformula.Evalb (((b : ℕ) : M) :> vv) (code B))
    (hz : (a ∣ b ∧ z = 1) ∨ (¬a ∣ b ∧ z = 0)) :
    Semiformula.Evalb (z :> vv) (code (codeDvd A B)) :=
  by
  have hlift :
    ∀ (X : Code k) (x t : M),
      Semiformula.Evalb (x :> vv) (code X) →
        Semiformula.Evalb (x :> t :> vv) (code (codeLift X)) :=
    fun X x t hX => (eval_codeLift_iff X x t vv).mpr hX
  have hhead : ∀ t : M, Semiformula.Evalb (t :> t :> vv) (code (codeHead (n := k))) := fun t =>
    (eval_codeHead_iff t (t :> vv)).mpr rfl
  have hex : ∃ m : ℕ, m * a = b ∨ b < m := ⟨b + 1, Or.inr (Nat.lt_succ_self b)⟩
  have hspec : Nat.find hex * a = b ∨ b < Nat.find hex := Nat.find_spec hex
  have hmin : ∀ j : ℕ, j < Nat.find hex → ¬(j * a = b ∨ b < j) := fun j hj =>
    Nat.find_min hex hj
  have hEqComp :
    ∀ (j : ℕ) (y : M),
      ((j * a = b ∧ y = 1) ∨ (¬j * a = b ∧ y = 0)) →
        Semiformula.Evalb (y :> ((j : ℕ) : M) :> vv)
          (code (codeEq (codeMul (codeHead (n := k)) (codeLift A)) (codeLift B))) :=
    by
    intro j y hy
    have hmulv :
      Semiformula.Evalb ((((j * a : ℕ)) : M) :> ((j : ℕ) : M) :> vv)
        (code (codeMul (codeHead (n := k)) (codeLift A))) :=
      by
      refine (eval_codeMul_iff _ _ _ _).mpr ⟨_, _, hhead _, hlift A _ _ hA, ?_⟩
      push_cast; rfl
    refine (eval_codeEq_iff _ _ _ _).mpr ⟨_, _, hmulv, hlift B _ _ hB, ?_⟩
    rcases hy with ⟨he, rfl⟩ | ⟨hne, rfl⟩
    · exact Or.inl ⟨by exact_mod_cast he, rfl⟩
    · exact Or.inr ⟨fun h => hne (by exact_mod_cast h), rfl⟩
  have hLtComp :
    ∀ (j : ℕ) (y : M),
      ((b < j ∧ y = 1) ∨ (¬b < j ∧ y = 0)) →
        Semiformula.Evalb (y :> ((j : ℕ) : M) :> vv)
          (code (codeLt (codeLift B) (codeHead (n := k)))) :=
    by
    intro j y hy
    refine (eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hlift B _ _ hB, hhead _, ?_⟩
    rcases hy with ⟨he, rfl⟩ | ⟨hne, rfl⟩
    · exact Or.inl ⟨by exact_mod_cast he, rfl⟩
    · exact Or.inr ⟨fun h => hne (by exact_mod_cast h), rfl⟩
  have hG1 :
    ∀ j : ℕ,
      (j * a = b ∨ b < j) →
        Semiformula.Evalb ((1 : M) :> ((j : ℕ) : M) :> vv)
          (code
            (codeOr (codeEq (codeMul (codeHead (n := k)) (codeLift A)) (codeLift B))
              (codeLt (codeLift B) (codeHead (n := k))))) :=
    by
    intro j hj
    by_cases h1 : j * a = b
    · by_cases h2 : b < j
      · exact
          (eval_codeOr_iff _ _ _ _).mpr
            ⟨1, 1, hEqComp j 1 (Or.inl ⟨h1, rfl⟩), hLtComp j 1 (Or.inl ⟨h2, rfl⟩),
              Or.inl ⟨by simp, rfl⟩⟩
      · exact
          (eval_codeOr_iff _ _ _ _).mpr
            ⟨1, 0, hEqComp j 1 (Or.inl ⟨h1, rfl⟩), hLtComp j 0 (Or.inr ⟨h2, rfl⟩),
              Or.inl ⟨by simp, rfl⟩⟩
    · have h2 : b < j := hj.resolve_left h1
      exact
        (eval_codeOr_iff _ _ _ _).mpr
          ⟨0, 1, hEqComp j 0 (Or.inr ⟨h1, rfl⟩), hLtComp j 1 (Or.inl ⟨h2, rfl⟩),
            Or.inl ⟨by simp, rfl⟩⟩
  have hG0 :
    ∀ j : ℕ,
      ¬(j * a = b ∨ b < j) →
        Semiformula.Evalb ((0 : M) :> ((j : ℕ) : M) :> vv)
          (code
            (codeOr (codeEq (codeMul (codeHead (n := k)) (codeLift A)) (codeLift B))
              (codeLt (codeLift B) (codeHead (n := k))))) :=
    by
    intro j hj
    exact
      (eval_codeOr_iff _ _ _ _).mpr
        ⟨0, 0, hEqComp j 0 (Or.inr ⟨fun h => hj (Or.inl h), rfl⟩),
          hLtComp j 0 (Or.inr ⟨fun h => hj (Or.inr h), rfl⟩), Or.inr ⟨by simp, rfl⟩⟩
  simp only [codeDvd]
  rw [eval_codeBind_iff]
  refine ⟨((Nat.find hex : ℕ) : M), ?_, ?_⟩
  · rw [eval_codeRfindPos_iff]
    refine ⟨⟨1, _root_.zero_lt_one, hG1 (Nat.find hex) hspec⟩, ?_⟩
    intro t ht
    obtain ⟨j, hj, rfl⟩ := exists_lt_natCast (Nat.find hex) t ht
    exact hG0 j (hmin j hj)
  · refine
      eval_codeLe_of _ _ ((Nat.find hex : ℕ) : M) ((b : ℕ) : M) z _ (hhead _) (hlift B _ _ hB)
        ?_
    rcases hz with ⟨hdvd, rfl⟩ | ⟨hndvd, rfl⟩
    · refine Or.inl ⟨?_, rfl⟩
      obtain ⟨c, hc⟩ := hdvd
      have hcs : c * a = b := by rw [hc, Nat.mul_comm]
      have hfc : Nat.find hex ≤ c := Nat.find_le (Or.inl hcs)
      have hle : Nat.find hex ≤ b :=
        by
        rcases Nat.eq_zero_or_pos a with ha0 | hap
        · have hb0 : b = 0 := by rw [hc, ha0, Nat.zero_mul]
          have h0 : Nat.find hex ≤ 0 := Nat.find_le (Or.inl (by simp [ha0, hb0]))
          omega
        · calc
            Nat.find hex ≤ c := hfc
            _ = c * 1 := (Nat.mul_one c).symm
            _ ≤ c * a := (Nat.mul_le_mul_left c hap)
            _ = b := hcs
      exact_mod_cast hle
    · refine Or.inr ⟨?_, rfl⟩
      have hlt : b < Nat.find hex := by
        rcases hspec with hfa | hbf
        · exact
            absurd ⟨Nat.find hex, ((Nat.mul_comm (Nat.find hex) a).symm.trans hfa).symm⟩ hndvd
        · exact hbf
      intro hcon
      have hle : Nat.find hex ≤ b := by exact_mod_cast hcon
      omega

/-- Remainder at standard numerals. -/
theorem eval_codeRem_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A B : Code k) (a b : ℕ) (vv : Fin k → M)
    (hA : Semiformula.Evalb (((a : ℕ) : M) :> vv) (code A))
    (hB : Semiformula.Evalb (((b : ℕ) : M) :> vv) (code B)) :
    Semiformula.Evalb ((((a % b : ℕ)) : M) :> vv) (code (codeRem A B)) :=
  by
  have hlift :
    ∀ (X : Code k) (x t : M),
      Semiformula.Evalb (x :> vv) (code X) →
        Semiformula.Evalb (x :> t :> vv) (code (codeLift X)) :=
    fun X x t hX => (eval_codeLift_iff X x t vv).mpr hX
  have hhead : ∀ t : M, Semiformula.Evalb (t :> t :> vv) (code (codeHead (n := k))) := fun t =>
    (eval_codeHead_iff t (t :> vv)).mpr rfl
  simp only [codeRem]
  rw [eval_codeRfindPos_iff]
  constructor
  · refine ⟨1, _root_.zero_lt_one, ?_⟩
    exact
      eval_codeDvd_natCast _ _ b (a - a % b) 1 _ (hlift B _ _ hB)
        (eval_codeSub_natCast _ _ a (a % b) _ (hlift A _ _ hA) (hhead _))
        (Or.inl ⟨Nat.dvd_sub_mod a, rfl⟩)
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := exists_lt_natCast (a % b) t ht
    refine
      eval_codeDvd_natCast _ _ b (a - j) 0 _ (hlift B _ _ hB)
        (eval_codeSub_natCast _ _ a j _ (hlift A _ _ hA) (hhead _)) (Or.inr ⟨?_, rfl⟩)
    intro hdvd
    have hmod_le : a % b ≤ a := Nat.mod_le _ _
    rcases Nat.eq_zero_or_pos b with hz0 | hbpos
    · rw [hz0] at hdvd
      rw [hz0, Nat.mod_zero] at hj
      rw [Nat.zero_dvd] at hdvd
      omega
    · have hsub2 : b ∣ a % b - j :=
        by
        have heq : a - j - (a - a % b) = a % b - j := by omega
        rw [← heq]
        exact Nat.dvd_sub hdvd (Nat.dvd_sub_mod a)
      have hpos : 0 < a % b - j := by omega
      have hmodlt : a % b < b := Nat.mod_lt _ hbpos
      exact absurd (Nat.le_of_dvd hpos hsub2) (by omega)

/-- Parity at a standard numeral. -/
theorem eval_codeBodd_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A : Code k) (n : ℕ) (vv : Fin k → M)
    (hA : Semiformula.Evalb (((n : ℕ) : M) :> vv) (code A)) :
    Semiformula.Evalb ((((n % 2 : ℕ)) : M) :> vv) (code (codeBodd A)) :=
  by
  simp only [codeBodd]
  exact eval_codeRem_natCast A _ n 2 vv hA (by simpa using eval_codeConst (M := M) 2 vv)

/-!
### Truncated subtraction, square root and the Cantor components at
arbitrary values

The results above compute a constructor at the image of a natural number.  Those
below compute the same constructors at an arbitrary element, against the
operations the pinned `IOpen` theory of Foundation already supplies:
`FFL.FirstOrder.Arithmetic.sqrt`, `pair`, `pi₁` and `pi₂`, together with their
specifications.  No arithmetic identity is reproved here; each proof only
matches a code against the operation Foundation defines. -/

/-- Truncated subtraction at arbitrary values. -/
theorem eval_codeSub [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A B : Code k) (a b : M) (v : Fin k → M)
    (hA : Semiformula.Evalb (a :> v) (code A)) (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb ((a - b) :> v) (code (codeSub A B)) :=
  by
  have hhead : ∀ t : M, Semiformula.Evalb (t :> t :> v) (code (codeHead (n := k))) := fun t =>
    (eval_codeHead_iff _ _).mpr rfl
  have hliftA : ∀ t : M, Semiformula.Evalb (a :> t :> v) (code (codeLift A)) := fun t =>
    (eval_codeLift_iff A _ _ v).mpr hA
  have hliftB : ∀ t : M, Semiformula.Evalb (b :> t :> v) (code (codeLift B)) := fun t =>
    (eval_codeLift_iff B _ _ v).mpr hB
  have hzero : ∀ t : M, Semiformula.Evalb ((0 : M) :> t :> v) (code (Code.zero (k + 1))) :=
    fun t => (eval_zero_iff _ _).mpr rfl
  have hsum :
    ∀ t : M,
      Semiformula.Evalb ((t + b) :> t :> v) (code (codeAdd (codeHead (n := k)) (codeLift B))) :=
    fun t => (eval_codeAdd_iff _ _ _ _).mpr ⟨t, b, hhead t, hliftB t, rfl⟩
  have heqs :
    ∀ t y : M,
      ((t + b = a ∧ y = 1) ∨ (¬t + b = a ∧ y = 0)) →
        Semiformula.Evalb (y :> t :> v)
          (code (codeEq (codeAdd (codeHead (n := k)) (codeLift B)) (codeLift A))) :=
    fun t y hy => (eval_codeEq_iff _ _ _ _).mpr ⟨t + b, a, hsum t, hliftA t, hy⟩
  have hcmp :
    ∀ t y : M,
      ((a < b ∧ y = 1) ∨ (¬a < b ∧ y = 0)) →
        Semiformula.Evalb (y :> t :> v) (code (codeLt (codeLift A) (codeLift B))) :=
    fun t y hy => (eval_codeLt_iff _ _ _ _).mpr ⟨a, b, hliftA t, hliftB t, hy⟩
  have hnil :
    ∀ t : M,
      ∃ y : M,
        Semiformula.Evalb (y :> t :> v)
          (code (codeEq (codeHead (n := k)) (Code.zero (k + 1)))) :=
    by
    intro t
    by_cases h : t = 0
    · exact ⟨1, (eval_codeEq_iff _ _ _ _).mpr ⟨t, 0, hhead t, hzero t, Or.inl ⟨h, rfl⟩⟩⟩
    · exact ⟨0, (eval_codeEq_iff _ _ _ _).mpr ⟨t, 0, hhead t, hzero t, Or.inr ⟨h, rfl⟩⟩⟩
  simp only [codeSub]
  rw [eval_codeRfindPos_iff]
  by_cases hba : b ≤ a
  · have hab : ¬a < b := not_lt.mpr hba
    have hand :
      ∀ t : M,
        Semiformula.Evalb ((0 : M) :> t :> v)
          (code
            (codeAnd (codeLt (codeLift A) (codeLift B))
              (codeEq (codeHead (n := k)) (Code.zero (k + 1))))) :=
      by
      intro t
      obtain ⟨y, hy⟩ := hnil t
      exact
        (eval_codeAnd_iff _ _ _ _).mpr
          ⟨0, y, hcmp t 0 (Or.inr ⟨hab, rfl⟩), hy, Or.inr ⟨by simp, rfl⟩⟩
    constructor
    · exact
        ⟨1, _root_.zero_lt_one,
          (eval_codeOr_iff _ _ _ _).mpr
            ⟨1, 0, heqs _ 1 (Or.inl ⟨sub_add_self_of_le hba, rfl⟩), hand _,
              Or.inl ⟨by simp, rfl⟩⟩⟩
    · intro t ht
      have hne : ¬t + b = a := by
        intro hc
        have hlt' : t + b < a - b + b := by simpa [add_comm] using (add_lt_add_left ht b)
        rw [hc, sub_add_self_of_le hba] at hlt'
        exact absurd hlt' (_root_.lt_irrefl a)
      exact
        (eval_codeOr_iff _ _ _ _).mpr
          ⟨0, 0, heqs t 0 (Or.inr ⟨hne, rfl⟩), hand t, Or.inr ⟨by simp, rfl⟩⟩
  · have hab : a < b := not_le.mp hba
    rw [sub_spec_of_lt hab]
    constructor
    · refine
        ⟨1, _root_.zero_lt_one,
          (eval_codeOr_iff _ _ _ _).mpr
            ⟨0, 1, heqs 0 0 (Or.inr ⟨?_, rfl⟩), ?_, Or.inl ⟨by simp, rfl⟩⟩⟩
      · intro hc
        rw [zero_add] at hc
        exact absurd hc (ne_of_gt hab)
      · exact
          (eval_codeAnd_iff _ _ _ _).mpr
            ⟨1, 1, hcmp 0 1 (Or.inl ⟨hab, rfl⟩),
              (eval_codeEq_iff _ _ _ _).mpr ⟨0, 0, hhead 0, hzero 0, Or.inl ⟨rfl, rfl⟩⟩,
              Or.inl ⟨by simp, rfl⟩⟩
    · intro t ht
      exact absurd ht (by simp)

/-- The integer square root at an arbitrary value, given the defining bounds. -/
theorem eval_codeSqrt_of_bounds [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (d : Code k) (a r : M) (v : Fin k → M)
    (hd : Semiformula.Evalb (a :> v) (code d)) (hle : r * r ≤ a) (hlt : a < (r + 1) * (r + 1)) :
    Semiformula.Evalb (r :> v) (code (codeSqrt d)) :=
  by
  have hhead : ∀ t : M, Semiformula.Evalb (t :> t :> v) (code (codeHead (n := k))) := fun t =>
    (eval_codeHead_iff _ _).mpr rfl
  have hliftd : ∀ t : M, Semiformula.Evalb (a :> t :> v) (code (codeLift d)) := fun t =>
    (eval_codeLift_iff d _ _ v).mpr hd
  have hheadsq :
    ∀ t : M,
      Semiformula.Evalb ((t * t) :> t :> v)
        (code (codeMul (codeHead (n := k)) (codeHead (n := k)))) :=
    fun t => (eval_codeMul_iff _ _ _ _).mpr ⟨t, t, hhead t, hhead t, rfl⟩
  have hheadsucc :
    ∀ t : M, Semiformula.Evalb ((t + 1) :> t :> v) (code (codeSucc (codeHead (n := k)))) :=
    fun t => (eval_codeSucc_iff _ _ _).mpr ⟨t, hhead t, rfl⟩
  have hheadsuccsq :
    ∀ t : M,
      Semiformula.Evalb (((t + 1) * (t + 1)) :> t :> v)
        (code (codeMul (codeSucc (codeHead (n := k))) (codeSucc (codeHead (n := k))))) :=
    fun t => (eval_codeMul_iff _ _ _ _).mpr ⟨t + 1, t + 1, hheadsucc t, hheadsucc t, rfl⟩
  have hAone :
    ∀ t : M,
      t * t ≤ a →
        Semiformula.Evalb ((1 : M) :> t :> v)
          (code
            (codeOr (codeLt (codeMul (codeHead (n := k)) (codeHead (n := k))) (codeLift d))
              (codeEq (codeMul (codeHead (n := k)) (codeHead (n := k))) (codeLift d)))) :=
    by
    intro t hlet
    rcases lt_or_eq_of_le hlet with hltt | heqt
    · exact
        (eval_codeOr_iff _ _ _ _).mpr
          ⟨1, 0,
            (eval_codeLt_iff _ _ _ _).mpr ⟨t * t, a, hheadsq t, hliftd t, Or.inl ⟨hltt, rfl⟩⟩,
            (eval_codeEq_iff _ _ _ _).mpr
              ⟨t * t, a, hheadsq t, hliftd t, Or.inr ⟨ne_of_lt hltt, rfl⟩⟩,
            Or.inl ⟨by simp, rfl⟩⟩
    · exact
        (eval_codeOr_iff _ _ _ _).mpr
          ⟨0, 1,
            (eval_codeLt_iff _ _ _ _).mpr
              ⟨t * t, a, hheadsq t, hliftd t,
                Or.inr ⟨by rw [heqt]; exact _root_.lt_irrefl a, rfl⟩⟩,
            (eval_codeEq_iff _ _ _ _).mpr ⟨t * t, a, hheadsq t, hliftd t, Or.inl ⟨heqt, rfl⟩⟩,
            Or.inl ⟨by simp, rfl⟩⟩
  have hBval :
    ∀ t y : M,
      ((a < (t + 1) * (t + 1) ∧ y = 1) ∨ (¬a < (t + 1) * (t + 1) ∧ y = 0)) →
        Semiformula.Evalb (y :> t :> v)
          (code
            (codeLt (codeLift d)
              (codeMul (codeSucc (codeHead (n := k))) (codeSucc (codeHead (n := k)))))) :=
    fun t y hy =>
    (eval_codeLt_iff _ _ _ _).mpr ⟨a, (t + 1) * (t + 1), hliftd t, hheadsuccsq t, hy⟩
  simp only [codeSqrt]
  rw [eval_codeRfindPos_iff]
  constructor
  · exact
      ⟨1, _root_.zero_lt_one,
        (eval_codeAnd_iff _ _ _ _).mpr
          ⟨1, 1, hAone r hle, hBval r 1 (Or.inl ⟨hlt, rfl⟩), Or.inl ⟨by simp, rfl⟩⟩⟩
  · intro t ht
    have hsucc : t + 1 ≤ r := FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr ht
    have hup : (t + 1) * (t + 1) ≤ r * r := mul_le_mul hsucc hsucc (by simp) (by simp)
    have hnlt : ¬a < (t + 1) * (t + 1) := not_lt.mpr (le_trans hup hle)
    have hstt : t * t ≤ a :=
      le_trans
        (le_trans (mul_le_mul (le_of_lt (by simp)) (le_of_lt (by simp)) (by simp) (by simp))
          hup)
        hle
    exact
      (eval_codeAnd_iff _ _ _ _).mpr
        ⟨1, 0, hAone t hstt, hBval t 0 (Or.inr ⟨hnlt, rfl⟩), Or.inr ⟨by simp, rfl⟩⟩

/-- The integer square root at an arbitrary value. -/
theorem eval_codeSqrt [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (d : Code k) (a : M) (v : Fin k → M)
    (hd : Semiformula.Evalb (a :> v) (code d)) :
    Semiformula.Evalb (FFL.FirstOrder.Arithmetic.sqrt a :> v) (code (codeSqrt d)) :=
  eval_codeSqrt_of_bounds d a _ v hd (FFL.FirstOrder.Arithmetic.sqrt_spec_le a)
    (FFL.FirstOrder.Arithmetic.sqrt_spec_lt a)

/-- Cantor pairing at arbitrary values. -/
theorem eval_codePair [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (A B : Code k) (a b : M) (v : Fin k → M)
    (hA : Semiformula.Evalb (a :> v) (code A)) (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pair a b :> v) (code (codePair A B)) :=
  by
  have hhigh : Semiformula.Evalb ((b * b + a) :> v) (code (codeAdd (codeMul B B) A)) :=
    (eval_codeAdd_iff _ _ _ _).mpr
      ⟨b * b, a, (eval_codeMul_iff _ _ _ _).mpr ⟨b, b, hB, hB, rfl⟩, hA, rfl⟩
  have hlow :
    Semiformula.Evalb ((a * a + a + b) :> v) (code (codeAdd (codeAdd (codeMul A A) A) B)) :=
    (eval_codeAdd_iff _ _ _ _).mpr
      ⟨a * a + a, b,
        (eval_codeAdd_iff _ _ _ _).mpr
          ⟨a * a, a, (eval_codeMul_iff _ _ _ _).mpr ⟨a, a, hA, hA, rfl⟩, hA, rfl⟩,
        hB, rfl⟩
  simp only [codePair]
  by_cases hab : a < b
  · refine
      eval_codeIfPos_of _ _ _ 1 (b * b + a) (a * a + a + b) _ v
        ((eval_codeLt_iff _ _ _ _).mpr ⟨a, b, hA, hB, Or.inl ⟨hab, rfl⟩⟩) hhigh hlow
        (Or.inl ⟨by simp, ?_⟩)
    simp [FFL.FirstOrder.Arithmetic.pair, hab]
  · refine
      eval_codeIfPos_of _ _ _ 0 (b * b + a) (a * a + a + b) _ v
        ((eval_codeLt_iff _ _ _ _).mpr ⟨a, b, hA, hB, Or.inr ⟨hab, rfl⟩⟩) hhigh hlow
        (Or.inr ⟨rfl, ?_⟩)
    simp [FFL.FirstOrder.Arithmetic.pair, hab]

/-- The first Cantor component at an arbitrary value. -/
theorem eval_codeUnpair₁ [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (d : Code k) (a : M) (v : Fin k → M)
    (hd : Semiformula.Evalb (a :> v) (code d)) :
    Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pi₁ a :> v) (code (codeUnpair₁ d)) :=
  by
  have hsq := eval_codeSqrt d a v hd
  have hmul :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.sqrt a * FFL.FirstOrder.Arithmetic.sqrt a) :> v)
      (code (codeMul (codeSqrt d) (codeSqrt d))) :=
    (eval_codeMul_iff _ _ _ _).mpr ⟨_, _, hsq, hsq, rfl⟩
  have hsub :=
    eval_codeSub d (codeMul (codeSqrt d) (codeSqrt d)) a
      (FFL.FirstOrder.Arithmetic.sqrt a * FFL.FirstOrder.Arithmetic.sqrt a) v hd hmul
  simp only [codeUnpair₁]
  by_cases hlt :
    a - FFL.FirstOrder.Arithmetic.sqrt a * FFL.FirstOrder.Arithmetic.sqrt a <
      FFL.FirstOrder.Arithmetic.sqrt a
  · refine
      eval_codeIfPos_of _ _ _ 1 _ _ _ v
        ((eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hsub, hsq, Or.inl ⟨hlt, rfl⟩⟩) hsub hsq
        (Or.inl ⟨by simp, ?_⟩)
    simp [FFL.FirstOrder.Arithmetic.pi₁, FFL.FirstOrder.Arithmetic.unpair, hlt]
  · refine
      eval_codeIfPos_of _ _ _ 0 _ _ _ v
        ((eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hsub, hsq, Or.inr ⟨hlt, rfl⟩⟩) hsub hsq
        (Or.inr ⟨rfl, ?_⟩)
    simp [FFL.FirstOrder.Arithmetic.pi₁, FFL.FirstOrder.Arithmetic.unpair, hlt]

/-- The second Cantor component at an arbitrary value. -/
theorem eval_codeUnpair₂ [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (d : Code k) (a : M) (v : Fin k → M)
    (hd : Semiformula.Evalb (a :> v) (code d)) :
    Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pi₂ a :> v) (code (codeUnpair₂ d)) :=
  by
  have hsq := eval_codeSqrt d a v hd
  have hmul :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.sqrt a * FFL.FirstOrder.Arithmetic.sqrt a) :> v)
      (code (codeMul (codeSqrt d) (codeSqrt d))) :=
    (eval_codeMul_iff _ _ _ _).mpr ⟨_, _, hsq, hsq, rfl⟩
  have hsub :=
    eval_codeSub d (codeMul (codeSqrt d) (codeSqrt d)) a
      (FFL.FirstOrder.Arithmetic.sqrt a * FFL.FirstOrder.Arithmetic.sqrt a) v hd hmul
  have hsub2 :=
    eval_codeSub (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d)
      (a - FFL.FirstOrder.Arithmetic.sqrt a * FFL.FirstOrder.Arithmetic.sqrt a)
      (FFL.FirstOrder.Arithmetic.sqrt a) v hsub hsq
  simp only [codeUnpair₂]
  by_cases hlt :
    a - FFL.FirstOrder.Arithmetic.sqrt a * FFL.FirstOrder.Arithmetic.sqrt a <
      FFL.FirstOrder.Arithmetic.sqrt a
  · refine
      eval_codeIfPos_of _ _ _ 1 _ _ _ v
        ((eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hsub, hsq, Or.inl ⟨hlt, rfl⟩⟩) hsq hsub2
        (Or.inl ⟨by simp, ?_⟩)
    simp [FFL.FirstOrder.Arithmetic.pi₂, FFL.FirstOrder.Arithmetic.unpair, hlt]
  · refine
      eval_codeIfPos_of _ _ _ 0 _ _ _ v
        ((eval_codeLt_iff _ _ _ _).mpr ⟨_, _, hsub, hsq, Or.inr ⟨hlt, rfl⟩⟩) hsq hsub2
        (Or.inr ⟨rfl, ?_⟩)
    simp [FFL.FirstOrder.Arithmetic.pi₂, FFL.FirstOrder.Arithmetic.unpair, hlt]

/-- The first Cantor component of a pair is its first argument. -/
theorem eval_codeUnpair₁_codePair [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (A B : Code k) (a b : M)
    (v : Fin k → M) (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb (a :> v) (code (codeUnpair₁ (codePair A B))) :=
  by
  have h :=
    eval_codeUnpair₁ (codePair A B) (FFL.FirstOrder.Arithmetic.pair a b) v
      (eval_codePair A B a b v hA hB)
  rwa [FFL.FirstOrder.Arithmetic.pi₁_pair] at h

/-- The second Cantor component of a pair is its second argument. -/
theorem eval_codeUnpair₂_codePair [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (A B : Code k) (a b : M)
    (v : Fin k → M) (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb (b :> v) (code (codeUnpair₂ (codePair A B))) :=
  by
  have h :=
    eval_codeUnpair₂ (codePair A B) (FFL.FirstOrder.Arithmetic.pair a b) v
      (eval_codePair A B a b v hA hB)
  rwa [FFL.FirstOrder.Arithmetic.pi₂_pair] at h

/-!
### Divisibility, remainder and the Gödel beta value at arbitrary values

`codeDvd` searches for the least quotient candidate, `codeRem` searches for the
least amount whose removal leaves a multiple of the divisor, and `codeBeta`
composes the two Cantor components with that remainder.  The three results below
compute each construction at arbitrary elements of a model of `𝐈𝐎𝐩𝐞𝐧`, against
the division and remainder Foundation already defines there.  No division
identity is reproved; each proof identifies the searched value and shows that
the search body vanishes below it. -/

/-- Divisibility at arbitrary values. -/
theorem eval_codeDvd [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (A B : Code k) (a b z : M) (v : Fin k → M)
    (hA : Semiformula.Evalb (a :> v) (code A)) (hB : Semiformula.Evalb (b :> v) (code B))
    (hz : (a ∣ b ∧ z = 1) ∨ (¬a ∣ b ∧ z = 0)) :
    Semiformula.Evalb (z :> v) (code (codeDvd A B)) :=
  by
  have hhead : ∀ t : M, Semiformula.Evalb (t :> t :> v) (code (codeHead (n := k))) := fun t =>
    (eval_codeHead_iff _ _).mpr rfl
  have hliftA : ∀ t : M, Semiformula.Evalb (a :> t :> v) (code (codeLift A)) := fun t =>
    (eval_codeLift_iff A _ _ v).mpr hA
  have hliftB : ∀ t : M, Semiformula.Evalb (b :> t :> v) (code (codeLift B)) := fun t =>
    (eval_codeLift_iff B _ _ v).mpr hB
  have hEq :
    ∀ t y : M,
      ((t * a = b ∧ y = 1) ∨ (¬t * a = b ∧ y = 0)) →
        Semiformula.Evalb (y :> t :> v)
          (code (codeEq (codeMul (codeHead (n := k)) (codeLift A)) (codeLift B))) :=
    fun t y hy =>
    (eval_codeEq_iff _ _ _ _).mpr
      ⟨t * a, b, (eval_codeMul_iff _ _ _ _).mpr ⟨t, a, hhead t, hliftA t, rfl⟩, hliftB t, hy⟩
  have hLt :
    ∀ t y : M,
      ((b < t ∧ y = 1) ∨ (¬b < t ∧ y = 0)) →
        Semiformula.Evalb (y :> t :> v) (code (codeLt (codeLift B) (codeHead (n := k)))) :=
    fun t y hy => (eval_codeLt_iff _ _ _ _).mpr ⟨b, t, hliftB t, hhead t, hy⟩
  have hG1 :
    ∀ t : M,
      (t * a = b ∨ b < t) →
        Semiformula.Evalb ((1 : M) :> t :> v)
          (code
            (codeOr (codeEq (codeMul (codeHead (n := k)) (codeLift A)) (codeLift B))
              (codeLt (codeLift B) (codeHead (n := k))))) :=
    by
    intro t ht
    by_cases h1 : t * a = b
    · by_cases h2 : b < t
      · exact
          (eval_codeOr_iff _ _ _ _).mpr
            ⟨1, 1, hEq t 1 (Or.inl ⟨h1, rfl⟩), hLt t 1 (Or.inl ⟨h2, rfl⟩),
              Or.inl ⟨by simp, rfl⟩⟩
      · exact
          (eval_codeOr_iff _ _ _ _).mpr
            ⟨1, 0, hEq t 1 (Or.inl ⟨h1, rfl⟩), hLt t 0 (Or.inr ⟨h2, rfl⟩),
              Or.inl ⟨by simp, rfl⟩⟩
    · exact
        (eval_codeOr_iff _ _ _ _).mpr
          ⟨0, 1, hEq t 0 (Or.inr ⟨h1, rfl⟩), hLt t 1 (Or.inl ⟨ht.resolve_left h1, rfl⟩),
            Or.inl ⟨by simp, rfl⟩⟩
  have hG0 :
    ∀ t : M,
      ¬(t * a = b ∨ b < t) →
        Semiformula.Evalb ((0 : M) :> t :> v)
          (code
            (codeOr (codeEq (codeMul (codeHead (n := k)) (codeLift A)) (codeLift B))
              (codeLt (codeLift B) (codeHead (n := k))))) :=
    fun t ht =>
    (eval_codeOr_iff _ _ _ _).mpr
      ⟨0, 0, hEq t 0 (Or.inr ⟨fun h => ht (Or.inl h), rfl⟩),
        hLt t 0 (Or.inr ⟨fun h => ht (Or.inr h), rfl⟩), Or.inr ⟨by simp, rfl⟩⟩
  simp only [codeDvd]
  rw [eval_codeBind_iff]
  by_cases hdvd : a ∣ b
  · obtain ⟨c, hcb, hbc⟩ := dvd_iff_bounded.mp hdvd
    have hz1 : z = 1 := by
      rcases hz with ⟨-, h⟩ | ⟨hnd, -⟩
      · exact h
      · exact absurd hdvd hnd
    refine ⟨c, ?_, ?_⟩
    · rw [eval_codeRfindPos_iff]
      refine ⟨⟨1, _root_.zero_lt_one, hG1 c (Or.inl ?_)⟩, ?_⟩
      · rw [mul_comm]; exact hbc.symm
      · intro t ht
        refine hG0 t ?_
        rintro (h1 | h2)
        · by_cases ha0 : a = 0
          · have hb0 : b = 0 := by rw [hbc, ha0, zero_mul]
            have hc0 : c = 0 := by
              rw [hb0] at hcb
              exact le_antisymm hcb (FFL.FirstOrder.Arithmetic.zero_le c)
            rw [hc0] at ht
            exact absurd ht (not_lt.mpr (FFL.FirstOrder.Arithmetic.zero_le t))
          · have hap : 0 < a := pos_iff_ne_zero.mpr ha0
            have hbb : b < b := by
              calc
                b = t * a := h1.symm
                _ < c * a := (mul_lt_mul_of_pos_right ht hap)
                _ = a * c := (mul_comm c a)
                _ = b := hbc.symm
            exact absurd hbb (_root_.lt_irrefl b)
        · exact absurd (lt_of_lt_of_le ht hcb) (not_lt.mpr (le_of_lt h2))
    · rw [hz1]
      exact eval_codeLe_of _ _ c b 1 _ (hhead _) (hliftB _) (Or.inl ⟨hcb, rfl⟩)
  · have hz0 : z = 0 := by
      rcases hz with ⟨hd, -⟩ | ⟨-, h⟩
      · exact absurd hd hdvd
      · exact h
    refine ⟨b + 1, ?_, ?_⟩
    · rw [eval_codeRfindPos_iff]
      refine ⟨⟨1, _root_.zero_lt_one, hG1 (b + 1) (Or.inr (lt_add_one b))⟩, ?_⟩
      intro t ht
      have htb : t ≤ b := FFL.FirstOrder.Arithmetic.lt_succ_iff_le.mp ht
      refine hG0 t ?_
      rintro (h1 | h2)
      · exact absurd ⟨t, by rw [← h1, mul_comm]⟩ hdvd
      · exact absurd h2 (not_lt.mpr htb)
    · rw [hz0]
      refine eval_codeLe_of _ _ (b + 1) b 0 _ (hhead _) (hliftB _) (Or.inr ⟨?_, rfl⟩)
      intro hcon
      exact absurd (lt_of_lt_of_le (lt_add_one b) hcon) (_root_.lt_irrefl b)

/-- The remainder at arbitrary values. -/
theorem eval_codeRem [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (A B : Code k) (a b : M) (v : Fin k → M)
    (hA : Semiformula.Evalb (a :> v) (code A)) (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb ((a % b) :> v) (code (codeRem A B)) :=
  by
  have hhead : ∀ t : M, Semiformula.Evalb (t :> t :> v) (code (codeHead (n := k))) := fun t =>
    (eval_codeHead_iff _ _).mpr rfl
  have hliftA : ∀ t : M, Semiformula.Evalb (a :> t :> v) (code (codeLift A)) := fun t =>
    (eval_codeLift_iff A _ _ v).mpr hA
  have hliftB : ∀ t : M, Semiformula.Evalb (b :> t :> v) (code (codeLift B)) := fun t =>
    (eval_codeLift_iff B _ _ v).mpr hB
  have hsub :
    ∀ t : M,
      Semiformula.Evalb ((a - t) :> t :> v) (code (codeSub (codeLift A) (codeHead (n := k)))) :=
    fun t => eval_codeSub (codeLift A) (codeHead (n := k)) a t (t :> v) (hliftA t) (hhead t)
  have hdm : b * (a / b) + a % b = a := div_add_mod a b
  simp only [codeRem]
  rw [eval_codeRfindPos_iff]
  constructor
  · refine ⟨1, _root_.zero_lt_one, ?_⟩
    refine
      eval_codeDvd (codeLift B) (codeSub (codeLift A) (codeHead (n := k))) b (a - a % b) 1 _
        (hliftB _) (hsub _) (Or.inl ⟨?_, rfl⟩)
    have hsplit : a - a % b = b * (a / b) := FFL.FirstOrder.Arithmetic.sub_remove_left hdm.symm
    rw [hsplit]
    exact Dvd.intro _ rfl
  · intro t ht
    refine
      eval_codeDvd (codeLift B) (codeSub (codeLift A) (codeHead (n := k))) b (a - t) 0 _
        (hliftB _) (hsub _) (Or.inr ⟨?_, rfl⟩)
    intro hdvd
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, FFL.FirstOrder.Arithmetic.mod_zero] at ht
      rw [hb0] at hdvd
      exact absurd ht (not_lt.mpr (sub_eq_zero_iff_le.mp (zero_dvd_iff.mp hdvd)))
    · have hbpos : 0 < b := pos_iff_ne_zero.mpr hb0
      have hmlt : a % b < b := mod_lt a hbpos
      have hsplit : a - t = b * (a / b) + (a % b - t) :=
        by
        conv_lhs => rw [← hdm]
        exact add_sub_of_le (le_of_lt ht) _
      have hmod : (a - t) % b = a % b - t := by
        rw [hsplit, mod_mul_add' (a / b) (a % b - t) hbpos,
          mod_eq_self_of_lt (lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.sub_le_self _ _) hmlt)]
      have hzero : a % b - t = 0 := by rw [← hmod]; exact mod_eq_zero_iff_dvd.mpr hdvd
      have hpos : 0 < a % b - t := pos_sub_iff_lt.mpr ht
      rw [hzero] at hpos
      exact absurd hpos (_root_.lt_irrefl 0)

/-- The Gödel beta value at arbitrary values.  `eval_codeBeta` in `Arithmetic`
computes the same construction over `ℕ`; this result instead proves that the
graph of `codeBeta N I` holds at the displayed remainder in an arbitrary model.
It does not assert the existence of a finite sequence with that beta value. -/
theorem eval_codeBeta_of_values [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (N I : Code k) (n i : M)
    (v : Fin k → M) (hN : Semiformula.Evalb (n :> v) (code N))
    (hI : Semiformula.Evalb (i :> v) (code I)) :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.pi₁ n % ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n + 1)) :> v)
      (code (codeBeta N I)) :=
  by
  have h1 := eval_codeUnpair₁ N n v hN
  have h2 := eval_codeUnpair₂ N n v hN
  have hsi : Semiformula.Evalb ((i + 1) :> v) (code (codeSucc I)) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨i, hI, rfl⟩
  have hmul :
    Semiformula.Evalb (((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n) :> v)
      (code (codeMul (codeSucc I) (codeUnpair₂ N))) :=
    (eval_codeMul_iff _ _ _ _).mpr ⟨_, _, hsi, h2, rfl⟩
  have hsucc :
    Semiformula.Evalb (((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n + 1) :> v)
      (code (codeSucc (codeMul (codeSucc I) (codeUnpair₂ N)))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨_, hmul, rfl⟩
  simp only [codeBeta]
  exact eval_codeRem _ _ _ _ v h1 hsucc

/-- The eager conditional has a value once its test and both of its branches
have one.  Both branches are evaluated whichever way the test goes. -/
theorem eval_codeIfPos_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n : ℕ} (df dg dh : Code n)
    (v : Fin n → M) (hf : ∃ f : M, Semiformula.Evalb (f :> v) (code df))
    (hg : ∃ g : M, Semiformula.Evalb (g :> v) (code dg))
    (hh : ∃ h : M, Semiformula.Evalb (h :> v) (code dh)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeIfPos df dg dh)) :=
  by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  obtain ⟨h, hh⟩ := hh
  by_cases hpos : 0 < f
  · exact ⟨g, eval_codeIfPos_of _ _ _ f g h g v hf hg hh (Or.inl ⟨hpos, rfl⟩)⟩
  · exact
      ⟨h,
        eval_codeIfPos_of _ _ _ f g h h v hf hg hh
          (Or.inr ⟨le_antisymm (not_lt.mp hpos) (by simp), rfl⟩)⟩

namespace IndexDecoder

/-- The parity bit as a remainder. -/
private theorem bodd_toNat_eq_mod_two (n : ℕ) : n.bodd.toNat = n % 2 := by
  rw [Nat.mod_two_of_bodd]

/-- The production tag decoder, written with remainders. -/
theorem partrecCodeTag_eq (q : ℕ) :
    partrecCodeTag q = if q < 4 then q else 4 + 2 * ((q - 4) % 2) + Nat.div2 (q - 4) % 2 := by
  simp only [partrecCodeTag, bodd_toNat_eq_mod_two]

/-- The constructor number of a standard index, read inside a model. -/
theorem eval_codePartrecTag_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodeTag q : ℕ) : M) :> v) (code (codePartrecTag d)) :=
  by
  have h4 : Semiformula.Evalb (((4 : ℕ) : M) :> v) (code (codeConst (n := r) 4)) :=
    eval_codeConst 4 v
  have h2 : Semiformula.Evalb (((2 : ℕ) : M) :> v) (code (codeConst (n := r) 2)) :=
    eval_codeConst 2 v
  have hrr := eval_codeSub_natCast d (codeConst 4) q 4 v hd (by simpa using h4)
  have hbodd0 := eval_codeBodd_natCast (codeSub d (codeConst 4)) (q - 4) v hrr
  have hbodd1 :=
    eval_codeBodd_natCast (codeDiv2 (codeSub d (codeConst 4))) (Nat.div2 (q - 4)) v
      (eval_codeDiv2_natCast _ (q - 4) v hrr)
  have hmul :
    Semiformula.Evalb ((((2 * ((q - 4) % 2) : ℕ)) : M) :> v)
      (code (codeMul (codeConst 2) (codeBodd (codeSub d (codeConst 4))))) :=
    by
    refine (eval_codeMul_iff _ _ _ v).mpr ⟨_, _, h2, hbodd0, ?_⟩
    push_cast
    norm_num
  have hadd1 :
    Semiformula.Evalb ((((4 + 2 * ((q - 4) % 2) : ℕ)) : M) :> v)
      (code
        (codeAdd (codeConst 4) (codeMul (codeConst 2) (codeBodd (codeSub d (codeConst 4)))))) :=
    by
    refine (eval_codeAdd_iff _ _ _ v).mpr ⟨_, _, h4, hmul, ?_⟩
    push_cast
    norm_num
  have hbig :
    Semiformula.Evalb ((((4 + 2 * ((q - 4) % 2) + Nat.div2 (q - 4) % 2 : ℕ)) : M) :> v)
      (code
        (codeAdd
          (codeAdd (codeConst 4) (codeMul (codeConst 2) (codeBodd (codeSub d (codeConst 4)))))
          (codeBodd (codeDiv2 (codeSub d (codeConst 4)))))) :=
    by
    refine (eval_codeAdd_iff _ _ _ v).mpr ⟨_, _, hadd1, hbodd1, ?_⟩
    push_cast
    norm_num
  rw [partrecCodeTag_eq]
  simp only [codePartrecTag]
  by_cases hq : q < 4
  · have hlt1 : Semiformula.Evalb ((1 : M) :> v) (code (codeLt d (codeConst 4))) :=
      by
      refine (eval_codeLt_iff _ _ _ v).mpr ⟨_, _, hd, by simpa using h4, Or.inl ⟨?_, rfl⟩⟩
      exact_mod_cast hq
    rw [ite_eq_left hq]
    exact
      eval_codeIfPos_of _ _ _ (1 : M) (((q : ℕ)) : M) _ _ v hlt1 hd hbig
        (Or.inl ⟨_root_.zero_lt_one, rfl⟩)
  · have hlt0 : Semiformula.Evalb ((0 : M) :> v) (code (codeLt d (codeConst 4))) :=
      by
      refine (eval_codeLt_iff _ _ _ v).mpr ⟨_, _, hd, by simpa using h4, Or.inr ⟨?_, rfl⟩⟩
      intro hc
      exact hq (by exact_mod_cast hc)
    rw [ite_eq_right hq]
    exact eval_codeIfPos_of _ _ _ (0 : M) (((q : ℕ)) : M) _ _ v hlt0 hd hbig (Or.inr ⟨rfl, rfl⟩)

/-- The payload of a standard compound index, read inside a model. -/
theorem eval_codePartrecPayload_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload q : ℕ) : M) :> v) (code (codePartrecPayload d)) :=
  by
  have h4 : Semiformula.Evalb (((4 : ℕ) : M) :> v) (code (codeConst (n := r) 4)) :=
    eval_codeConst 4 v
  have hrr := eval_codeSub_natCast d (codeConst 4) q 4 v hd (by simpa using h4)
  simpa only [codePartrecPayload, partrecCodePayload] using
    eval_codeDiv2_natCast _ _ v (eval_codeDiv2_natCast _ (q - 4) v hrr)

/-- The first subcode of a standard index, read inside a model. -/
theorem eval_codePartrecPayload₁_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₁ q : ℕ) : M) :> v) (code (codePartrecPayload₁ d)) :=
  eval_codeUnpair₁_natCast (codePartrecPayload d) _ v (eval_codePartrecPayload_natCast d q v hd)

/-- The second subcode of a standard index, read inside a model. -/
theorem eval_codePartrecPayload₂_natCast [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (q : ℕ)
    (v : Fin r → M) (hd : Semiformula.Evalb (((q : ℕ) : M) :> v) (code d)) :
    Semiformula.Evalb (((partrecCodePayload₂ q : ℕ) : M) :> v) (code (codePartrecPayload₂ d)) :=
  eval_codeUnpair₂_natCast (codePartrecPayload d) _ v (eval_codePartrecPayload_natCast d q v hd)

end IndexDecoder

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
