/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.Algebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Auxiliary-polynomial coefficient space

Constructs the coefficient space and base-`q` encoding of Harcos (2015), §5, equations
(18)–(22). The variable-versus-equation count yields a nonzero solution, and the
degree decomposition prevents cancellation; see also Stepanov (1972).
-/

@[expose] public section

open scoped BigOperators

namespace KloostermanWeil.Stepanov

open Module Polynomial

/-- A polynomial is a square after extension to an algebraic closure
exactly when it is a nonzero scalar times a square over the ground field.
This predicate is the form needed in Stepanov's
nonvanishing argument. -/
def IsScalarSquare {F : Type*} [Field F] (f : F[X]) : Prop :=
  ∃ c : F, c ≠ 0 ∧ ∃ g : F[X], f = C c * g ^ 2

/-- UFD cancellation used in the auxiliary-polynomial nonvanishing proof. -/
theorem isScalarSquare_of_sq_mul_eq_sq_mul_C
    {F : Type*} [Field F] {f r s : F[X]} {c : F}
    (hc : c ≠ 0) (hr : r ≠ 0)
    (heq : r ^ 2 * f = s ^ 2 * C c) :
    IsScalarSquare f := by
  have hu : IsUnit (C c : F[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hd0 : r ^ 2 ∣ s ^ 2 * C c := ⟨f, heq.symm⟩
  have hd : r ^ 2 ∣ s ^ 2 := (hu.dvd_mul_right).mp hd0
  have hrs : r ∣ s :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := F[X]) (n := 2) (by norm_num)).mp hd
  obtain ⟨t, rfl⟩ := hrs
  refine ⟨c, hc, t, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hr)
  calc
    r ^ 2 * f = (r * t) ^ 2 * C c := heq
    _ = r ^ 2 * (C c * t ^ 2) := by ring

/-- The pairs of coefficient families `(r_j,s_j)` in Stepanov equation
(18), with every polynomial of degree strictly less than `d`. -/
abbrev StepanovCoefficientSpace (F : Type*) [Field F]
    (J d : ℕ) :=
  (Fin J → Polynomial.degreeLT F d) ×
    (Fin J → Polynomial.degreeLT F d)

/-- Exact number `2 J d` of scalar variables in the auxiliary-polynomial
coefficient space. -/
theorem finrank_stepanovCoefficientSpace {F : Type*} [Field F]
    (J d : ℕ) :
    finrank F (StepanovCoefficientSpace F J d) = 2 * J * d := by
  rw [Module.finrank_prod]
  simp only [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F d),
    Module.finrank_pi_fintype, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ]
  simp
  ring

/-- Exact number `l E` of scalar equations in an `l`-tuple of polynomial
constraints of degree below `E`. -/
theorem finrank_stepanovConstraintSpace {F : Type*} [Field F]
    (l E : ℕ) :
    finrank F (Fin l → Polynomial.degreeLT F E) = l * E := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F E),
    Fintype.card_fin, Finset.sum_const, Finset.card_univ]
  simp

/-- A homogeneous finite-dimensional linear system with fewer equations
than variables has a nonzero solution. -/
theorem exists_ne_zero_solution_of_finrank_lt
    {F : Type*} [Field F]
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (L : V →ₗ[F] W) (h : finrank F W < finrank F V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 := by
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt h
  rw [Submodule.ne_bot_iff] at hk
  obtain ⟨v, hv, hv0⟩ := hk
  exact ⟨v, hv0, hv⟩

/-- A base-`q` sum of polynomial blocks of degree below `q` has a unique
block expansion.  This is the exact algebra behind the first congruence in
the nonvanishing argument following equation (19). -/
theorem polynomial_block_sum_eq_zero_iff
    {F : Type*} [Field F] (P : ℕ → F[X]) (J q : ℕ)
    (hdeg : ∀ j < J, (P j).natDegree < q) :
    (∑ j ∈ Finset.range J, P j * X ^ (j * q) = 0) ↔
      ∀ j < J, P j = 0 := by
  constructor
  · intro hsum j hj
    ext n
    have hn : q ≤ n → (P j).coeff n = 0 := by
      intro hqn
      exact coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le (hdeg j hj) hqn)
    by_cases hnq : n < q
    · have hc := congrArg (Polynomial.lcoeff F (n + j * q)) hsum
      simp only [map_sum, Polynomial.lcoeff_apply, coeff_zero] at hc
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)] at hc
      · simpa [coeff_mul_X_pow', Nat.le_add_left,
          Nat.add_sub_cancel_right] using hc
      · intro i hi hij
        simp only [Finset.mem_range] at hi
        by_cases hijlt : i < j
        · rw [coeff_mul_X_pow', ite_eq_left]
          · apply coeff_eq_zero_of_natDegree_lt
            have hmul : (i + 1) * q ≤ j * q :=
              Nat.mul_le_mul_right q (Nat.succ_le_iff.2 hijlt)
            have hadd : q + i * q ≤ n + j * q := by
              calc
                q + i * q = (i + 1) * q := by ring
                _ ≤ j * q := hmul
                _ ≤ n + j * q := Nat.le_add_left _ _
            have hdiff : q ≤ n + j * q - i * q :=
              Nat.le_sub_of_add_le hadd
            exact (hdeg i hi).trans_le hdiff
          · have hmul : i * q ≤ j * q :=
              Nat.mul_le_mul_right q (Nat.le_of_lt hijlt)
            exact hmul.trans (Nat.le_add_left _ _)
        · rw [coeff_mul_X_pow', ite_eq_right]
          have hji : j < i :=
            lt_of_le_of_ne (Nat.le_of_not_gt hijlt) hij.symm
          have hmul : (j + 1) * q ≤ i * q :=
            Nat.mul_le_mul_right q (Nat.succ_le_iff.2 hji)
          have hlt : n + j * q < i * q := by
            calc
              n + j * q < q + j * q := Nat.add_lt_add_right hnq _
              _ = (j + 1) * q := by ring
              _ ≤ i * q := hmul
          exact Nat.not_le_of_lt hlt
    · exact hn (Nat.le_of_not_gt hnq)
  · intro hzero
    apply Finset.sum_eq_zero
    intro j hj
    rw [hzero j (Finset.mem_range.1 hj), zero_mul]

/-- If every earlier block vanishes and a base-`q` block sum is zero, its
first remaining block is divisible by `X^q`.  Unlike block uniqueness, this
statement requires no degree bound and is the congruence actually used in
the source nonvanishing argument after equation (19). -/
theorem X_pow_dvd_first_nonzero_polynomial_block
    {F : Type*} [Field F] (P : ℕ → F[X]) (J q i : ℕ)
    (hi : i < J) (hprev : ∀ j < i, P j = 0)
    (hsum : ∑ j ∈ Finset.range J, P j * X ^ (j * q) = 0) :
    X ^ q ∣ P i := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hc := congrArg (Polynomial.lcoeff F (n + i * q)) hsum
  simp only [map_sum, Polynomial.lcoeff_apply, coeff_zero] at hc
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi)] at hc
  · simpa [coeff_mul_X_pow', Nat.le_add_left,
      Nat.add_sub_cancel_right] using hc
  · intro j hj hji
    simp only [Finset.mem_range] at hj
    by_cases hji_lt : j < i
    · rw [hprev j hji_lt, zero_mul, coeff_zero]
    · rw [coeff_mul_X_pow', ite_eq_right]
      have hij : i < j :=
        lt_of_le_of_ne (Nat.le_of_not_gt hji_lt) hji.symm
      have hmul : (i + 1) * q ≤ j * q :=
        Nat.mul_le_mul_right q (Nat.succ_le_iff.2 hij)
      have hlt : n + i * q < j * q := by
        calc
          n + i * q < q + i * q := Nat.add_lt_add_right hn _
          _ = (i + 1) * q := by ring
          _ ≤ j * q := hmul
      exact Nat.not_le_of_lt hlt

/-- Over a finite field, `f^q` is congruent to its constant coefficient
modulo `X^q`.  This is the Frobenius congruence used verbatim in the
nonvanishing argument following equation (19). -/
theorem X_card_pow_dvd_pow_card_sub_C_coeff_zero
    {F : Type*} [Field F] [Fintype F] (f : F[X]) :
    X ^ Fintype.card F ∣ f ^ Fintype.card F - C (f.coeff 0) := by
  rw [← FiniteField.Polynomial.expand_card f]
  rw [X_pow_dvd_iff]
  intro n hn
  rw [coeff_sub, coeff_expand (Fintype.card_pos) f]
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hndvd : ¬ Fintype.card F ∣ n := by
      intro hdvd
      exact hn0 (Nat.eq_zero_of_dvd_of_lt hdvd hn)
    rw [ite_eq_right hndvd, zero_sub, coeff_C]
    simp [hn0]

/-- Squaring the first-block congruence and applying finite-field
Frobenius gives the source congruence
`r² f ≡ s² f(0) (mod X^q)`. -/
theorem X_card_pow_dvd_sq_mul_sub_sq_mul_C
    {F : Type*} [Field F] [Fintype F]
    {f r s : F[X]} (hqodd : Odd (Fintype.card F))
    (hd : X ^ Fintype.card F ∣
      r + s * f ^ ((Fintype.card F - 1) / 2)) :
    X ^ Fintype.card F ∣ r ^ 2 * f - s ^ 2 * C (f.coeff 0) := by
  let q := Fintype.card F
  let e := (q - 1) / 2
  have he : 2 * e + 1 = q := by
    rcases hqodd with ⟨t, ht⟩
    dsimp [q, e]
    omega
  have h1 : X ^ q ∣ (r + s * f ^ e) * ((r - s * f ^ e) * f) :=
    dvd_mul_of_dvd_left hd _
  have h1' : X ^ q ∣ r ^ 2 * f - s ^ 2 * f ^ q := by
    convert h1 using 1
    rw [← he]
    ring
  have hfrob := X_card_pow_dvd_pow_card_sub_C_coeff_zero f
  have h2 : X ^ q ∣ s ^ 2 * (f ^ q - C (f.coeff 0)) :=
    dvd_mul_of_dvd_right hfrob _
  have htotal := dvd_add h1' h2
  convert htotal using 1
  ring

/-- A polynomial of degree below `q` divisible by `X^q` is zero. -/
theorem eq_zero_of_X_pow_dvd_of_natDegree_lt
    {F : Type*} [Field F] {P : F[X]} {q : ℕ}
    (hd : X ^ q ∣ P) (hdeg : P.natDegree < q) : P = 0 := by
  obtain ⟨u, rfl⟩ := hd
  by_cases hu : u = 0
  · simp [hu]
  have hx : (X ^ q : F[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  rw [natDegree_mul hx hu, natDegree_X_pow] at hdeg
  omega

/-- Under the source degree restriction, the preceding congruence is an
actual polynomial identity. -/
theorem sq_mul_eq_sq_mul_C_of_X_card_pow_dvd
    {F : Type*} [Field F] [Fintype F]
    {f : F[X]} {d : ℕ} (hd : 0 < d)
    (hsize : 2 * (d - 1) + f.natDegree < Fintype.card F)
    (r s : Polynomial.degreeLT F d)
    (hdiv : X ^ Fintype.card F ∣
      (r : F[X]) ^ 2 * f - (s : F[X]) ^ 2 * C (f.coeff 0)) :
    (r : F[X]) ^ 2 * f = (s : F[X]) ^ 2 * C (f.coeff 0) := by
  have hrdeg : (r : F[X]).natDegree < d := by
    by_cases hr : (r : F[X]) = 0
    · simp [hr, hd]
    · exact (natDegree_lt_iff_degree_lt hr).2 (mem_degreeLT.1 r.2)
  have hsdeg : (s : F[X]).natDegree < d := by
    by_cases hs : (s : F[X]) = 0
    · simp [hs, hd]
    · exact (natDegree_lt_iff_degree_lt hs).2 (mem_degreeLT.1 s.2)
  have hleft : (((r : F[X]) ^ 2 * f).natDegree) < Fintype.card F := by
    calc
      _ ≤ 2 * (r : F[X]).natDegree + f.natDegree := by
        exact natDegree_mul_le.trans
          (Nat.add_le_add_right
            (natDegree_pow_le : ((r : F[X]) ^ 2).natDegree ≤
              2 * (r : F[X]).natDegree) _)
      _ ≤ 2 * (d - 1) + f.natDegree := by omega
      _ < _ := hsize
  have hright : (((s : F[X]) ^ 2 * C (f.coeff 0)).natDegree) <
      Fintype.card F := by
    calc
      _ ≤ 2 * (s : F[X]).natDegree := by
        calc
          _ = (C (f.coeff 0) * (s : F[X]) ^ 2).natDegree := by rw [mul_comm]
          _ ≤ ((s : F[X]) ^ 2).natDegree := natDegree_C_mul_le _ _
          _ ≤ 2 * (s : F[X]).natDegree := by exact natDegree_pow_le
      _ ≤ 2 * (d - 1) := by omega
      _ ≤ 2 * (d - 1) + f.natDegree := Nat.le_add_right _ _
      _ < _ := hsize
  have hdeg : (((r : F[X]) ^ 2 * f -
      (s : F[X]) ^ 2 * C (f.coeff 0)).natDegree) < Fintype.card F :=
    (natDegree_sub_le _ _).trans_lt (max_lt hleft hright)
  have hz : (r : F[X]) ^ 2 * f -
      (s : F[X]) ^ 2 * C (f.coeff 0) = 0 :=
    eq_zero_of_X_pow_dvd_of_natDegree_lt hdiv hdeg
  exact sub_eq_zero.mp hz

/-- One coefficient block in equation (18) is injective modulo `X^q`
under the source nonsquare and degree hypotheses. -/
theorem stepanovCoefficientPair_eq_zero_of_X_card_pow_dvd
    {F : Type*} [Field F] [Fintype F]
    {f : F[X]} {d : ℕ} (hd : 0 < d)
    (hqodd : Odd (Fintype.card F))
    (hsize : 2 * (d - 1) + f.natDegree < Fintype.card F)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f)
    (r s : Polynomial.degreeLT F d)
    (hdiv : X ^ Fintype.card F ∣
      (r : F[X]) + (s : F[X]) *
        f ^ ((Fintype.card F - 1) / 2)) :
    r = 0 ∧ s = 0 := by
  have hcong := X_card_pow_dvd_sq_mul_sub_sq_mul_C hqodd hdiv
  have heq := sq_mul_eq_sq_mul_C_of_X_card_pow_dvd hd hsize r s hcong
  have hr : (r : F[X]) = 0 := by
    by_contra hr
    exact hnsq (isScalarSquare_of_sq_mul_eq_sq_mul_C hf0 hr heq)
  have hs : (s : F[X]) = 0 := by
    rw [hr, zero_pow (by norm_num), zero_mul] at heq
    have hc : (C (f.coeff 0) : F[X]) ≠ 0 := C_ne_zero.mpr hf0
    exact eq_zero_of_pow_eq_zero
      (mul_eq_zero.mp heq.symm |>.resolve_right hc)
  exact ⟨Subtype.ext hr, Subtype.ext hs⟩

/-- In a finite base-`q` block sum, if all earlier blocks vanish, the
first remaining block is divisible by `X^q`. -/
theorem X_pow_dvd_first_fin_polynomial_block
    {F : Type*} [Field F]
    {J q : ℕ} (P : Fin J → F[X]) (i : Fin J)
    (hprev : ∀ j : Fin J, (j : ℕ) < i → P j = 0)
    (hsum : ∑ j : Fin J, P j * X ^ ((j : ℕ) * q) = 0) :
    X ^ q ∣ P i := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hc := congrArg (Polynomial.lcoeff F (n + (i : ℕ) * q)) hsum
  simp only [map_sum, Polynomial.lcoeff_apply, coeff_zero] at hc
  rw [Finset.sum_eq_single i] at hc
  · simpa [coeff_mul_X_pow', Nat.le_add_left,
      Nat.add_sub_cancel_right] using hc
  · intro j _hj hji
    by_cases hji_lt : (j : ℕ) < i
    · rw [hprev j hji_lt, zero_mul, coeff_zero]
    · rw [coeff_mul_X_pow', ite_eq_right]
      have hij : (i : ℕ) < j := lt_of_le_of_ne
        (Nat.le_of_not_gt hji_lt) (fun h ↦ hji (Fin.ext h.symm))
      have hmul : ((i : ℕ) + 1) * q ≤ (j : ℕ) * q :=
        Nat.mul_le_mul_right q (Nat.succ_le_iff.2 hij)
      have hlt : n + (i : ℕ) * q < (j : ℕ) * q := by
        calc
          n + (i : ℕ) * q < q + (i : ℕ) * q :=
            Nat.add_lt_add_right hn _
          _ = ((i : ℕ) + 1) * q := by ring
          _ ≤ (j : ℕ) * q := hmul
      exact Nat.not_le_of_lt hlt
  · simp

/-- The polynomial inside the leading factor `f^l` in Stepanov equation
(18). -/
noncomputable def stepanovAuxiliaryCore
    {F : Type*} [Field F] (f : F[X])
    (q J d : ℕ) (v : StepanovCoefficientSpace F J d) : F[X] :=
  ∑ j : Fin J,
    ((v.1 j : F[X]) + (v.2 j : F[X]) * f ^ ((q - 1) / 2)) *
      X ^ ((j : ℕ) * q)

/-- Stepanov's auxiliary polynomial `h_a`; the sign `a` enters the
homogeneous constraints rather than this defining expression. -/
noncomputable def stepanovAuxiliary
    {F : Type*} [Field F] (f : F[X])
    (q l J d : ℕ) (v : StepanovCoefficientSpace F J d) : F[X] :=
  f ^ l * stepanovAuxiliaryCore f q J d v

/-- Exact equation (18), exposed as a theorem for later source-order
composition. -/
theorem stepanovAuxiliary_equation18
    {F : Type*} [Field F] (f : F[X])
    (q l J d : ℕ) (v : StepanovCoefficientSpace F J d) :
    stepanovAuxiliary f q l J d v =
      f ^ l * ∑ j : Fin J,
        ((v.1 j : F[X]) + (v.2 j : F[X]) * f ^ ((q - 1) / 2)) *
          X ^ ((j : ℕ) * q) := rfl

/-- The nonzero coefficient vector supplied by the homogeneous system
produces a genuinely nonzero auxiliary polynomial.  This completes the
nonvanishing paragraph following equation (19), rather than assuming it. -/
theorem stepanovAuxiliary_ne_zero
    {F : Type*} [Field F] [Fintype F]
    {f : F[X]} {l J d : ℕ} (hf : f ≠ 0) (hd : 0 < d)
    (hqodd : Odd (Fintype.card F))
    (hsize : 2 * (d - 1) + f.natDegree < Fintype.card F)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f)
    (v : StepanovCoefficientSpace F J d) (hv : v ≠ 0) :
    stepanovAuxiliary f (Fintype.card F) l J d v ≠ 0 := by
  intro hzero
  have hcore : stepanovAuxiliaryCore f (Fintype.card F) J d v = 0 := by
    unfold stepanovAuxiliary at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hf)
  have hall : ∀ i : ℕ, (hi : i < J) →
      v.1 ⟨i, hi⟩ = 0 ∧ v.2 ⟨i, hi⟩ = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      let ii : Fin J := ⟨i, hi⟩
      have hprev : ∀ j : Fin J, (j : ℕ) < ii →
          ((v.1 j : F[X]) + (v.2 j : F[X]) *
            f ^ ((Fintype.card F - 1) / 2)) = 0 := by
        intro j hj
        obtain ⟨hr, hs⟩ := ih j hj j.isLt
        rw [hr, hs]
        simp
      have hdiv : X ^ Fintype.card F ∣
          (v.1 ii : F[X]) + (v.2 ii : F[X]) *
            f ^ ((Fintype.card F - 1) / 2) := by
        apply X_pow_dvd_first_fin_polynomial_block
          (fun j : Fin J => (v.1 j : F[X]) + (v.2 j : F[X]) *
            f ^ ((Fintype.card F - 1) / 2)) ii hprev
        exact hcore
      exact stepanovCoefficientPair_eq_zero_of_X_card_pow_dvd
        hd hqodd hsize hf0 hnsq (v.1 ii) (v.2 ii) hdiv
  apply hv
  apply Prod.ext
  · funext i
    exact (hall i i.isLt).1
  · funext i
    exact (hall i i.isLt).2

/-- Exact Hasse-derivative factorization (20) for the auxiliary polynomial.
The two quotient families are the source polynomials `r_j^(k)` and
`s_j^(k)` from Lemma 10. -/
theorem stepanovAuxiliary_equation20
    {F : Type*} [Field F] {p n l J d k : ℕ}
    [Fact p.Prime] [CharP F p]
    (f : F[X]) (v : StepanovCoefficientSpace F J d)
    (hk : k ≤ l) (hkq : k < p ^ n) :
    hasseDeriv k (stepanovAuxiliary f (p ^ n) l J d v) =
      f ^ (l - k) * ∑ j : Fin J,
        (hassePowerQuotient f hk (v.1 j) +
          hassePowerQuotient f
            (show k ≤ l + ((p ^ n - 1) / 2) by omega) (v.2 j) *
              f ^ ((p ^ n - 1) / 2)) *
          X ^ ((j : ℕ) * (p ^ n)) := by
  let e := (p ^ n - 1) / 2
  have hkle : k ≤ l + e := by omega
  have hsource : stepanovAuxiliary f (p ^ n) l J d v =
      ∑ j : Fin J,
        ((v.1 j : F[X]) * f ^ l + (v.2 j : F[X]) * f ^ (l + e)) *
          X ^ ((j : ℕ) * (p ^ n)) := by
    rw [stepanovAuxiliary_equation18]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [e]
    ring
  rw [hsource, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hasseDeriv_mul_X_mul_prime_pow hkq]
  rw [map_add]
  rw [hassePowerQuotient_spec f hk]
  rw [hassePowerQuotient_spec f hkle]
  have hexp : l + e - k = (l - k) + e := by omega
  rw [hexp, pow_add]
  dsimp [e]
  ring

/-- Source-sharp cancellation-safe form of equation (21).  Moving `k` to
the right recovers `deg g^(k) < d + k (deg f - 1)` without truncated
subtraction in the Lean statement. -/
theorem stepanovQuotient_equation21
    {F : Type*} [Field F] (f : F[X])
    (hf : f ≠ 0) (hfdeg : 0 < f.natDegree)
    {d N k : ℕ} (hd : 0 < d) (hk : k ≤ N)
    (g : Polynomial.degreeLT F d) :
    (hassePowerQuotient f hk g).natDegree + k <
      d + k * f.natDegree := by
  have hgdeg : (g : F[X]).natDegree < d := by
    by_cases hg : (g : F[X]) = 0
    · rw [hg, natDegree_zero]
      exact hd
    · exact (natDegree_lt_iff_degree_lt hg).2
        (Polynomial.mem_degreeLT.1 g.2)
  exact (hassePowerQuotient_natDegree f g hf hfdeg hk).trans_lt
    (Nat.add_lt_add_right hgdeg _)

/-- The `k`th homogeneous polynomial constraint in equation (22). -/
noncomputable def stepanovConstraintPolynomial
    {F : Type*} [Field F] (f : F[X]) (a : F)
    (q l J d k : ℕ) (hk : k ≤ l)
    (v : StepanovCoefficientSpace F J d) : F[X] :=
  ∑ j : Fin J,
    (hassePowerQuotient f hk (v.1 j) +
      C a * hassePowerQuotient f
        (show k ≤ l + ((q - 1) / 2) by omega) (v.2 j)) *
      X ^ (j : ℕ)

/-- Exact degree count behind equations (21)--(22). -/
theorem stepanovConstraintPolynomial_natDegree
    {F : Type*} [Field F] (f : F[X]) (a : F)
    (hf : f ≠ 0) (hm : 0 < f.natDegree)
    {q l J d k : ℕ} (hd : 0 < d) (hk : k ≤ l)
    (v : StepanovCoefficientSpace F J d) :
    (stepanovConstraintPolynomial f a q l J d k hk v).natDegree <
      d + k * (f.natDegree - 1) + J := by
  have hbase : d + k * (f.natDegree - 1) + k =
      d + k * f.natDegree := by
    have hm' : f.natDegree - 1 + 1 = f.natDegree := by omega
    calc
      d + k * (f.natDegree - 1) + k =
          d + (k * (f.natDegree - 1) + k * 1) := by omega
      _ = d + k * ((f.natDegree - 1) + 1) := by rw [Nat.mul_add]
      _ = d + k * f.natDegree := by rw [hm']
  unfold stepanovConstraintPolynomial
  have hsum : (∑ j : Fin J,
      (hassePowerQuotient f hk (v.1 j) +
        C a * hassePowerQuotient f
          (show k ≤ l + ((q - 1) / 2) by omega) (v.2 j)) * X ^ (j : ℕ)).natDegree ≤
      d + k * (f.natDegree - 1) + J - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j _hj
    have hr := stepanovQuotient_equation21 f hf hm hd hk (v.1 j)
    have hs := stepanovQuotient_equation21 f hf hm hd
      (show k ≤ l + ((q - 1) / 2) by omega) (v.2 j)
    have hr' : (hassePowerQuotient f hk (v.1 j)).natDegree <
        d + k * (f.natDegree - 1) := by omega
    have hs' : (hassePowerQuotient f
        (show k ≤ l + ((q - 1) / 2) by omega) (v.2 j)).natDegree <
        d + k * (f.natDegree - 1) := by omega
    have hterm : ((hassePowerQuotient f hk (v.1 j) +
        C a * hassePowerQuotient f
          (show k ≤ l + ((q - 1) / 2) by omega) (v.2 j)) *
        X ^ (j : ℕ)).natDegree < d + k * (f.natDegree - 1) + J := by
      calc
        _ ≤ max (hassePowerQuotient f hk (v.1 j)).natDegree
            (C a * hassePowerQuotient f
              (show k ≤ l + ((q - 1) / 2) by omega) (v.2 j)).natDegree + j := by
          exact natDegree_mul_le.trans
            (add_le_add (natDegree_add_le _ _) (by simp))
        _ < d + k * (f.natDegree - 1) + J := by
          have hca : (C a * hassePowerQuotient f
              (show k ≤ l + ((q - 1) / 2) by omega) (v.2 j)).natDegree <
              d + k * (f.natDegree - 1) :=
            (natDegree_C_mul_le _ _).trans_lt hs'
          exact Nat.add_lt_add (max_lt hr' hca) j.isLt
    exact Nat.le_pred_of_lt hterm
  exact hsum.trans_lt (by omega)

/-- The complete homogeneous linear system (22), with each row placed in
its source-sharp degree-bounded polynomial space. -/
noncomputable def stepanovConstraintLinearMap
    {F : Type*} [Field F] (f : F[X]) (a : F)
    (hf : f ≠ 0) (hm : 0 < f.natDegree)
    (q l J d : ℕ) (hd : 0 < d) :
    StepanovCoefficientSpace F J d →ₗ[F]
      ((k : Fin l) → Polynomial.degreeLT F
        (d + (k : ℕ) * (f.natDegree - 1) + J)) where
  toFun v k := ⟨stepanovConstraintPolynomial f a q l J d k k.isLt.le v, by
    rw [Polynomial.mem_degreeLT]
    by_cases hz : stepanovConstraintPolynomial f a q l J d k k.isLt.le v = 0
    · rw [hz, degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree hz, Nat.cast_lt]
      exact stepanovConstraintPolynomial_natDegree
        f a hf hm hd k.isLt.le v⟩
  map_add' v w := by
    apply _root_.funext
    intro k
    apply Subtype.ext
    change stepanovConstraintPolynomial f a q l J d k k.isLt.le (v + w) =
      stepanovConstraintPolynomial f a q l J d k k.isLt.le v +
        stepanovConstraintPolynomial f a q l J d k k.isLt.le w
    unfold stepanovConstraintPolynomial
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    have hr : hassePowerQuotient f k.isLt.le ((v + w).1 j) =
        hassePowerQuotient f k.isLt.le (v.1 j) +
          hassePowerQuotient f k.isLt.le (w.1 j) := by
      change hassePowerQuotient f k.isLt.le (v.1 j + w.1 j) = _
      exact (hassePowerQuotientLinearMap f hf k.isLt.le).map_add _ _
    have hs : hassePowerQuotient f
          (show (k : ℕ) ≤ l + ((q - 1) / 2) by omega) ((v + w).2 j) =
        hassePowerQuotient f
            (show (k : ℕ) ≤ l + ((q - 1) / 2) by omega) (v.2 j) +
          hassePowerQuotient f
            (show (k : ℕ) ≤ l + ((q - 1) / 2) by omega) (w.2 j) := by
      change hassePowerQuotient f _ (v.2 j + w.2 j) = _
      exact (hassePowerQuotientLinearMap f hf
        (show (k : ℕ) ≤ l + ((q - 1) / 2) by omega)).map_add _ _
    rw [hr, hs]
    ring
  map_smul' c v := by
    apply _root_.funext
    intro k
    apply Subtype.ext
    change stepanovConstraintPolynomial f a q l J d k k.isLt.le (c • v) =
      c • stepanovConstraintPolynomial f a q l J d k k.isLt.le v
    unfold stepanovConstraintPolynomial
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    have hr : hassePowerQuotient f k.isLt.le ((c • v).1 j) =
        c • hassePowerQuotient f k.isLt.le (v.1 j) := by
      change hassePowerQuotient f k.isLt.le (c • v.1 j) = _
      exact (hassePowerQuotientLinearMap f hf k.isLt.le).map_smul c _
    have hs : hassePowerQuotient f
          (show (k : ℕ) ≤ l + ((q - 1) / 2) by omega) ((c • v).2 j) =
        c • hassePowerQuotient f
          (show (k : ℕ) ≤ l + ((q - 1) / 2) by omega) (v.2 j) := by
      change hassePowerQuotient f _ (c • v.2 j) = _
      exact (hassePowerQuotientLinearMap f hf
        (show (k : ℕ) ≤ l + ((q - 1) / 2) by omega)).map_smul c _
    rw [hr, hs]
    simp only [smul_eq_C_mul]
    ring

/-- Exact scalar equation count of system (22). -/
theorem finrank_stepanovConstraintSystem
    {F : Type*} [Field F] (m l J d : ℕ) :
    finrank F ((k : Fin l) → Polynomial.degreeLT F
        (d + (k : ℕ) * (m - 1) + J)) =
      ∑ k : Fin l, (d + (k : ℕ) * (m - 1) + J) := by
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro k _hk
  simpa using Module.finrank_eq_card_basis
    (Polynomial.degreeLT.basis F (d + (k : ℕ) * (m - 1) + J))

/-- Dimension-count existence theorem for a nonzero solution of all
constraints (22).  Its hypothesis is the exact source variable-versus-row
count, before the later numerical choice of `l` and `J`. -/
theorem exists_stepanovCoefficient_constraints_eq_zero
    {F : Type*} [Field F] (f : F[X]) (a : F)
    (hf : f ≠ 0) (hm : 0 < f.natDegree)
    (q l J d : ℕ) (hd : 0 < d)
    (hdim : (∑ k : Fin l,
        (d + (k : ℕ) * (f.natDegree - 1) + J)) < 2 * J * d) :
    ∃ v : StepanovCoefficientSpace F J d,
      v ≠ 0 ∧ stepanovConstraintLinearMap f a hf hm q l J d hd v = 0 := by
  apply exists_ne_zero_solution_of_finrank_lt
  rw [finrank_stepanovConstraintSystem,
    finrank_stepanovCoefficientSpace]
  exact hdim

/-- A zero of the `k`th row of (22) forces the `k`th Hasse derivative of
the auxiliary polynomial to vanish at every point with quadratic value
`a`. -/
theorem stepanovConstraint_implies_hasse_eval_zero
    {F : Type*} [Field F] [Fintype F]
    {p n l J d k : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (f : F[X]) (a x : F) (v : StepanovCoefficientSpace F J d)
    (hk : k < l) (hlq : l ≤ p ^ n)
    (ha : (f.eval x) ^ ((p ^ n - 1) / 2) = a)
    (hconstraint :
      stepanovConstraintPolynomial f a (p ^ n) l J d k hk.le v = 0) :
    (hasseDeriv k (stepanovAuxiliary f (p ^ n) l J d v)).eval x = 0 := by
  rw [stepanovAuxiliary_equation20 f v hk.le (hk.trans_le hlq)]
  rw [eval_mul]
  suffices hsum : (eval x) (∑ j : Fin J,
      (hassePowerQuotient f hk.le (v.1 j) +
        hassePowerQuotient f
          (show k ≤ l + ((p ^ n - 1) / 2) by omega) (v.2 j) *
            f ^ ((p ^ n - 1) / 2)) * X ^ ((j : ℕ) * p ^ n)) = 0 by
    rw [hsum, mul_zero]
  have hc := congrArg (eval x) hconstraint
  unfold stepanovConstraintPolynomial at hc
  simp only [eval_finsetSum, eval_mul, eval_add, eval_C, eval_pow, eval_X] at hc ⊢
  rw [ha]
  have hxq : x ^ (p ^ n) = x := by
    rw [← hcard]
    exact FiniteField.pow_card x
  have hjq (j : Fin J) : (j : ℕ) * p ^ n = p ^ n * (j : ℕ) :=
    Nat.mul_comm _ _
  simp_rw [hjq, pow_mul, hxq]
  simpa [mul_comm] using hc

/-- If the whole system (22) vanishes, every point where `f(x)` is zero
or has quadratic value `a` is a root of the auxiliary polynomial with
multiplicity at least `l`; this is implication (17). -/
theorem stepanovAuxiliary_uniform_rootMultiplicity
    {F : Type*} [Field F] [Fintype F]
    {p n l J d : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (f : F[X]) (a : F) (hf : f ≠ 0) (hm : 0 < f.natDegree)
    (hd : 0 < d) (hlq : l ≤ p ^ n)
    (v : StepanovCoefficientSpace F J d)
    (hconstraints :
      stepanovConstraintLinearMap f a hf hm (p ^ n) l J d hd v = 0)
    (x : F)
    (hx : f.eval x = 0 ∨
      (f.eval x) ^ ((p ^ n - 1) / 2) = a) :
    (X - C x) ^ l ∣ stepanovAuxiliary f (p ^ n) l J d v := by
  apply (hasseRootMultiplicityCriterion _ _ _).2
  intro k hk
  rcases hx with hx0 | hxa
  · rw [stepanovAuxiliary_equation20 f v hk.le (hk.trans_le hlq)]
    rw [eval_mul, eval_pow, hx0]
    have hlk : 0 < l - k := Nat.sub_pos_of_lt hk
    rw [zero_pow hlk.ne', zero_mul]
  · apply stepanovConstraint_implies_hasse_eval_zero
      hcard f a x v hk hlq hxa
    have hkzero := congrFun hconstraints ⟨k, hk⟩
    exact congrArg Subtype.val hkzero

/-- The source degree estimate for the Stepanov auxiliary polynomial.
This is the strict form of the estimate immediately preceding (14). -/
theorem stepanovAuxiliary_natDegree_lt
    {F : Type*} [Field F] (f : F[X])
    {q l J d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (v : StepanovCoefficientSpace F J d) :
    (stepanovAuxiliary f q l J d v).natDegree <
      f.natDegree * (l + ((q - 1) / 2)) + d + J * q := by
  let e := (q - 1) / 2
  have hcore : (stepanovAuxiliaryCore f q J d v).natDegree <
      d + e * f.natDegree + J * q := by
    unfold stepanovAuxiliaryCore
    have hsum : (∑ j : Fin J,
        ((v.1 j : F[X]) + (v.2 j : F[X]) * f ^ e) *
          X ^ ((j : ℕ) * q)).natDegree ≤
        d + e * f.natDegree + J * q - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro j _hj
      have hr : (v.1 j : F[X]).natDegree < d := by
        by_cases hz : (v.1 j : F[X]) = 0
        · simp [hz, hd]
        · exact (natDegree_lt_iff_degree_lt hz).2 (mem_degreeLT.1 (v.1 j).2)
      have hs : (v.2 j : F[X]).natDegree < d := by
        by_cases hz : (v.2 j : F[X]) = 0
        · simp [hz, hd]
        · exact (natDegree_lt_iff_degree_lt hz).2 (mem_degreeLT.1 (v.2 j).2)
      have hterm : (((v.1 j : F[X]) + (v.2 j : F[X]) * f ^ e) *
          X ^ ((j : ℕ) * q)).natDegree <
          d + e * f.natDegree + J * q := by
        calc
          _ ≤ max (v.1 j : F[X]).natDegree
              ((v.2 j : F[X]) * f ^ e).natDegree + (j : ℕ) * q := by
            exact natDegree_mul_le.trans
              (Nat.add_le_add (natDegree_add_le _ _) (by simp))
          _ ≤ max (v.1 j : F[X]).natDegree
              ((v.2 j : F[X]).natDegree + e * f.natDegree) + (j : ℕ) * q := by
            gcongr
            exact natDegree_mul_le.trans
              (Nat.add_le_add_left natDegree_pow_le _)
          _ < d + e * f.natDegree + J * q := by
            have hmax : max (v.1 j : F[X]).natDegree
                ((v.2 j : F[X]).natDegree + e * f.natDegree) <
                d + e * f.natDegree := by
              apply max_lt
              · exact hr.trans_le (Nat.le_add_right _ _)
              · exact Nat.add_lt_add_right hs _
            exact Nat.add_lt_add hmax
              (Nat.mul_lt_mul_of_pos_right j.isLt hq)
      exact Nat.le_pred_of_lt hterm
    exact hsum.trans_lt (by omega)
  unfold stepanovAuxiliary
  calc
    _ ≤ l * f.natDegree + (stepanovAuxiliaryCore f q J d v).natDegree := by
      exact natDegree_mul_le.trans
        (Nat.add_le_add_right natDegree_pow_le _)
    _ < l * f.natDegree + (d + e * f.natDegree + J * q) :=
      Nat.add_lt_add_left hcore _
    _ = f.natDegree * (l + ((q - 1) / 2)) + d + J * q := by
      dsimp [e]
      ring

/-- Stepanov inequality (14), with the exact source parameter conditions.
The left side counts every zero of `f` together with every point where its
quadratic character has the prescribed value. -/
theorem stepanov_point_set_cardinality_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {p n l J d : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (f : F[X]) (a : F) (hf : f ≠ 0) (hm : 0 < f.natDegree)
    (hd : 0 < d) (hl : 0 < l) (hlq : l ≤ p ^ n)
    (hqodd : Odd (p ^ n))
    (hsize : 2 * (d - 1) + f.natDegree < p ^ n)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f)
    (hdim : (∑ k : Fin l,
        (d + (k : ℕ) * (f.natDegree - 1) + J)) < 2 * J * d) :
    l * (Finset.univ.filter fun x : F =>
      f.eval x = 0 ∨ (f.eval x) ^ ((p ^ n - 1) / 2) = a).card <
      f.natDegree * (l + ((p ^ n - 1) / 2)) + d + J * (p ^ n) := by
  classical
  obtain ⟨v, hv, hconstraints⟩ :=
    exists_stepanovCoefficient_constraints_eq_zero
      f a hf hm (p ^ n) l J d hd hdim
  have hqoddF : Odd (Fintype.card F) := by
    rw [hcard]
    exact hqodd
  have hsizeF : 2 * (d - 1) + f.natDegree < Fintype.card F := by
    rw [hcard]
    exact hsize
  have haux : stepanovAuxiliary f (p ^ n) l J d v ≠ 0 := by
    simpa only [hcard] using
      (stepanovAuxiliary_ne_zero (f := f) (l := l) (J := J) (d := d)
        hf hd hqoddF hsizeF hf0 hnsq v hv)
  have hmul : l * (Finset.univ.filter fun x : F =>
      f.eval x = 0 ∨ (f.eval x) ^ ((p ^ n - 1) / 2) = a).card ≤
      (stepanovAuxiliary f (p ^ n) l J d v).natDegree := by
    apply card_mul_le_natDegree_of_uniform_rootMultiplicity _ haux _ hl
    intro x hx
    exact stepanovAuxiliary_uniform_rootMultiplicity
      hcard f a hf hm hd hlq v hconstraints x (Finset.mem_filter.mp hx).2
  exact hmul.trans_lt (stepanovAuxiliary_natDegree_lt f
    (pow_pos (Fact.out : p.Prime).pos n) hd v)

end KloostermanWeil.Stepanov
