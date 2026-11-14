/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.Algebra.MvPolynomial.Polynomial

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring

/-!
# Exponential polynomials on `ℕ`

**`expPoly_indep`**: let `ρ` range over a finite set of distinct nonzero elements of a field of
characteristic `0`, and let `Q_ρ` be polynomials. If `Σ_ρ Q_ρ(n) ρⁿ = 0` for every `n ∈ ℕ`, then
every
`Q_ρ = 0`.

The proof is by induction on `Σ (deg Q_ρ + 1)`, applying the operator `f(n) ↦ f(n+1) − ρ₀ f(n)`.
It lowers
the degree of `Q_{ρ₀}` and keeps the other `Q_ρ ≠ 0`. This is the one-variable form of Roy's
argument for
DALAG Prop. 5.6.
-/

@[expose] public section

namespace LeanPool

open _root_.Polynomial

namespace StrongSix.M2

variable {K : Type*} [Field K]

/-- The weight `deg p + 1` (and `0` for `p = 0`). -/
noncomputable def pw (p : K[X]) : ℕ := by
  classical
  exact if p = 0 then 0 else p.natDegree + 1

theorem pw_zero : pw (0 : K[X]) = 0 := by simp [pw]

theorem pw_of_ne {p : K[X]} (hp : p ≠ 0) : pw p = p.natDegree + 1 := by simp [pw, hp]

theorem shift_natDegree (p : K[X]) : (p.comp (X + C 1)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem shift_leadingCoeff (p : K[X]) : (p.comp (X + C 1)).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C,
    one_pow, mul_one]

theorem shift_ne_zero {p : K[X]} (hp : p ≠ 0) : p.comp (X + C 1) ≠ 0 := by
  intro h
  have := shift_leadingCoeff p
  rw [h, leadingCoeff_zero] at this
  exact hp (leadingCoeff_eq_zero.mp this.symm)

theorem pw_shift_sub_lt {p : K[X]} (hp : p ≠ 0) (a : K) :
    pw (C a * (p.comp (X + C 1) - p)) < pw p := by
  rw [pw_of_ne hp]
  by_cases h : C a * (p.comp (X + C 1) - p) = 0
  · rw [h, pw_zero]; omega
  rw [pw_of_ne h]
  have hd : p.comp (X + C 1) - p ≠ 0 := fun h' => h (by rw [h', mul_zero])
  have hcp := shift_ne_zero hp
  have hdeg : degree (p.comp (X + C 1)) = degree p := by
    rw [degree_eq_natDegree hcp, degree_eq_natDegree hp, shift_natDegree]
  have hlt := degree_sub_lt_left hdeg hcp (shift_leadingCoeff p)
  have hlt' : (p.comp (X + C 1) - p).natDegree < p.natDegree :=
    natDegree_lt_natDegree hd (hlt.trans_le hdeg.le)
  have := natDegree_C_mul_le a (p.comp (X + C 1) - p)
  omega

theorem pw_twist_le {p : K[X]} (hp : p ≠ 0) {ρ ρ₀ : K} (hne : ρ ≠ ρ₀) :
    C ρ * p.comp (X + C 1) - C ρ₀ * p ≠ 0 ∧ pw (C ρ * p.comp (X + C 1) - C ρ₀ * p) ≤ pw p := by
  set q := C ρ * p.comp (X + C 1) - C ρ₀ * p
  have hcoeff : q.coeff p.natDegree = (ρ - ρ₀) * p.leadingCoeff := by
    simp only [q, coeff_sub, coeff_C_mul]
    rw [← shift_natDegree p, coeff_natDegree, shift_leadingCoeff, shift_natDegree, coeff_natDegree]
    ring
  have hq : q ≠ 0 := fun h => by
    rw [h, coeff_zero] at hcoeff
    exact mul_ne_zero (sub_ne_zero.mpr hne) (leadingCoeff_ne_zero.mpr hp) hcoeff.symm
  refine ⟨hq, ?_⟩
  rw [pw_of_ne hq, pw_of_ne hp]
  have h1 : q.natDegree ≤ p.natDegree := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (shift_natDegree p).le
    · exact natDegree_C_mul_le _ _
  omega

variable [CharZero K]

theorem eq_zero_of_eval_nat {p : K[X]} (h : ∀ n : ℕ, p.eval (n : K) = 0) : p = 0 := by
  apply eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono (s := Set.range (Nat.cast : ℕ → K))
  · rintro _ ⟨n, rfl⟩; exact h n
  · exact Set.infinite_range_of_injective Nat.cast_injective

/-- **Independence of exponential polynomials on `ℕ`.** -/
theorem expPoly_indep (R : Finset K) (h0 : ∀ ρ ∈ R, ρ ≠ 0) :
    ∀ Q : K → K[X], (∀ n : ℕ, ∑ ρ ∈ R, (Q ρ).eval (n : K) * ρ ^ n = 0) → ∀ ρ ∈ R, Q ρ = 0 := by
  intro Q
  induction hμ : ∑ ρ ∈ R, pw (Q ρ) using Nat.strong_induction_on generalizing Q with
  | _ μ ih =>
  intro hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ₀, hρ₀R, hQ₀⟩ := hcon
  classical
  let Q' : K → K[X] := fun ρ => C ρ * (Q ρ).comp (X + C 1) - C ρ₀ * Q ρ
  have hsum' : ∀ n : ℕ, ∑ ρ ∈ R, (Q' ρ).eval (n : K) * ρ ^ n = 0 := by
    intro n
    have e : ∀ ρ, (Q' ρ).eval (n : K) * ρ ^ n =
        (Q ρ).eval ((n + 1 : ℕ) : K) * ρ ^ (n + 1) - ρ₀ * ((Q ρ).eval (n : K) * ρ ^ n) := by
      intro ρ
      simp only [Q', eval_sub, eval_mul, eval_C, eval_comp, eval_add, eval_X, Nat.cast_succ]
      ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  have hlt : ∑ ρ ∈ R, pw (Q' ρ) < μ := by
    rw [← hμ]
    apply Finset.sum_lt_sum
    · intro ρ _
      by_cases hρ : ρ = ρ₀
      · subst hρ
        have : Q' ρ = C ρ * ((Q ρ).comp (X + C 1) - Q ρ) := by simp only [Q']; ring
        rw [this]; exact (pw_shift_sub_lt hQ₀ ρ).le
      · by_cases hQ : Q ρ = 0
        · simp [Q', hQ, pw_zero]
        · exact (pw_twist_le hQ hρ).2
    · refine ⟨ρ₀, hρ₀R, ?_⟩
      have : Q' ρ₀ = C ρ₀ * ((Q ρ₀).comp (X + C 1) - Q ρ₀) := by simp only [Q']; ring
      rw [this]; exact pw_shift_sub_lt hQ₀ ρ₀
  have hzero := ih _ hlt Q' rfl hsum'
  by_cases hother : ∃ ρ₁ ∈ R, ρ₁ ≠ ρ₀ ∧ Q ρ₁ ≠ 0
  · obtain ⟨ρ₁, hρ₁R, hne, hQ₁⟩ := hother
    exact (pw_twist_le hQ₁ hne).1 (hzero ρ₁ hρ₁R)
  · push Not at hother
    apply hQ₀
    apply eq_zero_of_eval_nat
    intro n
    have := hsum n
    rw [Finset.sum_eq_single ρ₀ (fun ρ hρ hne => by rw [hother ρ hρ hne]; simp)
      (fun h => absurd hρ₀R h)] at this
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ (h0 ρ₀ hρ₀R))

/-! ### Substitution helpers -/

omit [CharZero K] in
theorem poly_eval_aeval {σ : Type*} (A : MvPolynomial σ K) (h : σ → K[X]) (x : K) :
    (MvPolynomial.aeval h A).eval x = MvPolynomial.eval (fun k => (h k).eval x) A := by
  rw [MvPolynomial.aeval_def, MvPolynomial.polynomial_eval_eval₂]
  have : (Polynomial.evalRingHom x).comp (algebraMap K K[X]) = RingHom.id K := by
    ext; simp
  rw [this]; rfl

omit [CharZero K] in
theorem mv_eval_aeval {σ τ : Type*} (A : MvPolynomial σ K) (h : σ → MvPolynomial τ K)
    (u : τ → K) :
    MvPolynomial.eval u (MvPolynomial.aeval h A) = MvPolynomial.eval (fun k => MvPolynomial.eval
      u (h k)) A := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_eval₂]
  have : (MvPolynomial.eval u).comp (algebraMap K (MvPolynomial τ K)) = RingHom.id K := by
    ext; simp
  rw [this]; rfl

/-! ### Multivariate exponential polynomials on a subgroup -/

section Subgroup

variable {d0 d1 s : ℕ}

/-- The character `y ↦ y^γ` of `(K^×)^{d₁}`. -/
def chr (y : Fin d1 → Kˣ) (γ : Fin d1 → ℤ) : K := ∏ j, ((y j : Kˣ) : K) ^ (γ j)

omit [CharZero K] in
theorem chr_mul (y y' : Fin d1 → Kˣ) (γ : Fin d1 → ℤ) : chr (y * y') γ = chr y γ * chr y' γ := by
  simp only [chr, Pi.mul_apply, Units.val_mul, mul_zpow, Finset.prod_mul_distrib]

omit [CharZero K] in
theorem chr_pow (y : Fin d1 → Kˣ) (γ : Fin d1 → ℤ) (n : ℕ) : chr (y ^ n) γ = chr y γ ^ n := by
  induction n with
  | zero => simp [chr]
  | succ n ih => rw [pow_succ, chr_mul, ih, pow_succ]

omit [CharZero K] in
theorem chr_ne_zero (y : Fin d1 → Kˣ) (γ : Fin d1 → ℤ) : chr y γ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => zpow_ne_zero _ (Units.ne_zero _)

/-- A subset of `K^{d₀} × (K^×)^{d₁}` containing the identity and closed under the group law. -/
structure IsSubmonoidG (S : Set ((Fin d0 → K) × (Fin d1 → Kˣ))) : Prop where
  one_mem : ((0 : Fin d0 → K), (1 : Fin d1 → Kˣ)) ∈ S
  add_mem : ∀ g ∈ S, ∀ g' ∈ S, (g.1 + g'.1, g.2 * g'.2) ∈ S

omit [CharZero K] in
theorem IsSubmonoidG.nsmul_mem {S : Set ((Fin d0 → K) × (Fin d1 → Kˣ))} (hS : IsSubmonoidG S)
    {g : (Fin d0 → K) × (Fin d1 → Kˣ)} (hg : g ∈ S) (n : ℕ) : (n • g.1, g.2 ^ n) ∈ S := by
  induction n with
  | zero => simpa using hS.one_mem
  | succ n ih =>
    have := hS.add_mem _ ih g hg
    rw [succ_nsmul, pow_succ]; exact this

/-- **Base case**: a polynomial vanishing on the image of a spanning additive submonoid is zero. -/
theorem eq_zero_of_vanish_on_span {S : Set ((Fin d0 → K) × (Fin d1 → Kˣ))} (hS : IsSubmonoidG S)
    (L : (Fin d0 → K) →ₗ[K] (Fin s → K))
    (hspan : Submodule.span K ((fun g : (Fin d0 → K) × (Fin d1 → Kˣ) => L g.1) '' S) = ⊤)
    {A : MvPolynomial (Fin s) K} (hA : ∀ g ∈ S, MvPolynomial.eval (L g.1) A = 0) : A = 0 := by
  classical
  set Cs := (fun g : (Fin d0 → K) × (Fin d1 → Kˣ) => L g.1) '' S
  -- closure of `C` under `ℕ`-combinations
  have hcomb : ∀ (t : Finset (Fin s → K)), (↑t ⊆ Cs) → ∀ n : (Fin s → K) → ℕ,
      ∃ g ∈ S, L g.1 = ∑ c ∈ t, n c • c := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _ n; exact ⟨_, hS.one_mem, by simp⟩
    | insert c t hc ih =>
      intro ht n
      obtain ⟨g, hg, hgL⟩ := ih (fun x hx => ht (Finset.mem_insert_of_mem hx)) n
      obtain ⟨g0, hg0, hg0L⟩ := ht (Finset.mem_insert_self c t)
      refine ⟨_, hS.add_mem _ (hS.nsmul_mem hg0 (n c)) g hg, ?_⟩
      simp only [map_add, map_nsmul, hg0L, hgL, Finset.sum_insert hc]
  -- a basis inside `C`
  obtain ⟨b, hbC, hbspan, hbli⟩ := exists_linearIndependent K Cs
  have hbfin : b.Finite := hbli.setFinite
  have : Fintype b := hbfin.fintype
  have hbtop : Submodule.span K b = ⊤ := hbspan.trans hspan
  let bas : Module.Basis b K (Fin s → K) := Module.Basis.mk hbli (by rw
    [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbtop])
  -- the pulled-back polynomial
  let A' : MvPolynomial b K := MvPolynomial.aeval (fun k => ∑ i : b, MvPolynomial.C (i.1 k) *
    MvPolynomial.X i) A
  have hA' : ∀ u : b → K, MvPolynomial.eval u A' = MvPolynomial.eval (∑ i : b, u i • i.1) A := by
    intro u
    simp only [A', mv_eval_aeval, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    congr 2
    funext k
    simp [Finset.sum_apply, mul_comm]
  have hA'0 : A' = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → K))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro u hu
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_range, forall_const] at hu
    choose n hn using hu
    rw [hA', map_zero]
    obtain ⟨g, hg, hgL⟩ := hcomb (Finset.univ.image (fun i : b => i.1)) (by
        intro x hx
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hbC i.2)
      (fun c => if h : c ∈ b then n ⟨c, h⟩ else 0)
    have := hA g hg
    rw [hgL, Finset.sum_image (fun i _ j _ h => Subtype.ext h)] at this
    convert this using 3
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [← hn, Nat.cast_smul_eq_nsmul]
  apply MvPolynomial.funext
  intro t
  rw [map_zero]
  have : t = ∑ i : b, bas.repr t i • i.1 := by
    conv_lhs => rw [← bas.sum_repr t]
    exact Finset.sum_congr rfl fun i _ => by rw [Module.Basis.mk_apply]
  rw [this, ← hA', hA'0, map_zero]

omit [CharZero K] in
/-- **Independence of exponential polynomials on a subgroup** (the core of Roy, DALAG Prop. 5.6).
If `Σ_{i ∈ s₀} A_i(L x) y^{γ_i}` vanishes on `S`, the characters `y^{γ_i}` are pairwise distinct
on `S`,
and `L(S_x)` spans `K^s`, then every `A_i = 0`. -/
theorem expPoly_indep_subgroup [CharZero K] {S : Set ((Fin d0 → K) × (Fin d1 → Kˣ))}
    (hS : IsSubmonoidG S) (L : (Fin d0 → K) →ₗ[K] (Fin s → K))
    (hspan : Submodule.span K ((fun g : (Fin d0 → K) × (Fin d1 → Kˣ) => L g.1) '' S) = ⊤)
    {ι : Type*} : ∀ (s0 : Finset ι) (A : ι → MvPolynomial (Fin s) K) (γ : ι → Fin d1 → ℤ),
      (∀ i ∈ s0, ∀ j ∈ s0, i ≠ j → ∃ g ∈ S, chr g.2 (γ i) ≠ chr g.2 (γ j)) →
      (∀ g ∈ S, ∑ i ∈ s0, MvPolynomial.eval (L g.1) (A i) * chr g.2 (γ i) = 0) →
      ∀ i ∈ s0, A i = 0 := by
  classical
  intro s0
  induction hcard : s0.card using Nat.strong_induction_on generalizing s0 with
  | _ N ih =>
  intro A γ hγ hf i1 hi1
  -- restriction to lines
  have line : ∀ g ∈ S, ∀ g' ∈ S, ∑ i ∈ s0.filter (fun i => chr g.2 (γ i) = chr g.2 (γ i1)),
      MvPolynomial.eval (L g'.1) (A i) * chr g'.2 (γ i) = 0 := by
    intro g hg g' hg'
    let P : ι → K[X] := fun i => C (chr g'.2 (γ i)) *
      MvPolynomial.aeval (fun k => C (L g'.1 k) + C (L g.1 k) * X) (A i)
    have hP : ∀ i (x : K), (P i).eval x =
        MvPolynomial.eval (fun k => L g'.1 k + x * L g.1 k) (A i) * chr g'.2 (γ i) := by
      intro i x
      rw [eval_mul, eval_C, poly_eval_aeval, mul_comm]
      congr 1
      apply congrArg (fun f => MvPolynomial.eval f (A i))
      funext k
      simp only [eval_add, eval_C, eval_mul, eval_X]
      ring
    have hn : ∀ n : ℕ, ∑ i ∈ s0, (P i).eval (n : K) * chr g.2 (γ i) ^ n = 0 := by
      intro n
      have hmem := hS.add_mem _ hg' _ (hS.nsmul_mem hg n)
      have := hf _ hmem
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      have harg : L (g'.1 + n • g.1) = fun k => L g'.1 k + (n : K) * L g.1 k := by
        funext k; rw [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
      rw [hP, chr_mul, chr_pow, harg]
      ring
    let R := s0.image fun i => chr g.2 (γ i)
    let Q : K → K[X] := fun ρ => ∑ i ∈ s0.filter (fun i => chr g.2 (γ i) = ρ), P i
    have hQ : ∀ n : ℕ, ∑ ρ ∈ R, (Q ρ).eval (n : K) * ρ ^ n = 0 := by
      intro n
      rw [← hn n]
      simp only [Q, eval_finsetSum, Finset.sum_mul]
      rw [Finset.sum_image' (fun i => (P i).eval (n : K) * chr g.2 (γ i) ^ n)]
      intro ρ _
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    have hzero := expPoly_indep R (fun ρ hρ => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hρ; exact chr_ne_zero _ _) Q hQ
      (chr g.2 (γ i1)) (Finset.mem_image_of_mem _ hi1)
    have := congrArg (fun q : K[X] => q.eval 0) hzero
    simp only [Q, eval_finsetSum, eval_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP]; simp
  by_cases hsep : ∃ g ∈ S, ∃ j ∈ s0, chr g.2 (γ j) ≠ chr g.2 (γ i1)
  · obtain ⟨g, hg, j, hj, hne⟩ := hsep
    set s1 := s0.filter (fun i => chr g.2 (γ i) = chr g.2 (γ i1))
    have hlt : s1.card < N := by
      rw [← hcard]
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have : j ∈ s1 := h ▸ hj
      exact hne (Finset.mem_filter.mp this).2
    exact ih _ hlt s1 rfl A γ (fun i hi j hj hij => hγ i (Finset.mem_filter.mp hi).1 j
      (Finset.mem_filter.mp hj).1 hij) (fun g' hg' => line g hg g' hg') i1
      (Finset.mem_filter.mpr ⟨hi1, rfl⟩)
  · push Not at hsep
    have hsingle : ∀ j ∈ s0, j = i1 := by
      intro j hj
      by_contra hne
      obtain ⟨g, hg, hneq⟩ := hγ j hj i1 hi1 hne
      exact hneq (hsep g hg j hj)
    apply eq_zero_of_vanish_on_span hS L hspan
    intro g hg
    have := hf g hg
    rw [Finset.sum_eq_single i1 (fun j hj hne => absurd (hsingle j hj) hne)
      (fun h => absurd hi1 h)] at this
    exact (mul_eq_zero.mp this).resolve_right (chr_ne_zero _ _)

end Subgroup

end StrongSix.M2

end LeanPool
