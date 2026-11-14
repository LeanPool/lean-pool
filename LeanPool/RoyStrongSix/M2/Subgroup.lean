/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Funext

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Thm1.MultEst

/-!
# The obstruction subgroups `h₀ × T_U` and their Hilbert functions

For a `K`-subspace `h₀ ⊆ K^{d₀}` and a `ℚ`-subspace `U ⊆ ℚ^{d₁}`, `TU U ⊆ (K^×)^{d₁}` is the
subtorus cut
out by the characters `y^φ`, `φ ∈ U ∩ ℤ^{d₁}`. The subgroup `h₀ × T_U` has dimension
`h = dim h₀` plus `r = d₁ − dim U`.

* `exists_torus_pt`: for integral `c ∉ U` there is `y ∈ T_U` with `y^c ≠ 1` (char 0).
* **`exists_indep_restr`**: there are `(N₀/h + 1)^h · (N₁/r + 1)^r` polynomials of bidegree
  `≤ (N₀, N₁)` whose restrictions to `h₀ × T_U` are linearly independent. This is the lower bound
  `H(h₀ × T_U; D) ≫ D₀^h D₁^r` (Roy, LIL Prop. 8.3; here by a direct count). The proof uses
  coordinates on `h₀`, independent characters on `T_U`, and Dedekind's lemma.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] {d0 d1 : ℕ}

/-! ### Bidegree bookkeeping -/

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.mono
    {P : MvPolynomial (Var d0 d1) K} {a b a' b' : ℕ} (h :
  BidegLE P a b)
    (ha : a ≤ a') (hb : b ≤ b') : BidegLE P a' b' := fun m hm =>
  ⟨(h m hm).1.trans ha, (h m hm).2.trans hb⟩

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.one
    (a b : ℕ) : BidegLE (1 : MvPolynomial (Var d0 d1) K) a
  b := by
  intro m hm
  classical
  rw [show (1 : MvPolynomial (Var d0 d1) K) = monomial 0 1 from rfl] at hm
  have hm0 : m = 0 := by simpa only [Finset.mem_singleton] using support_monomial_subset hm
  subst m
  simp

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.add
    {P Q : MvPolynomial (Var d0 d1) K} {a b : ℕ} (hP :
  BidegLE P a b)
    (hQ : BidegLE Q a b) : BidegLE (P + Q) a b := fun m hm => by
  classical
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hP m h
  · exact hQ m h

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.smul
    {P : MvPolynomial (Var d0 d1) K} {a b : ℕ} (hP :
  BidegLE P a b) (c : K) :
    BidegLE (c • P) a b := fun m hm => hP m (support_smul hm)

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.sum
    {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial (Var
  d0 d1) K} {a b : ℕ}
    (h : ∀ i ∈ s, BidegLE (P i) a b) : BidegLE (∑ i ∈ s, P i) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m hm; simp at hm
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.mul
    {P Q : MvPolynomial (Var d0 d1) K} {a b a' b' : ℕ} (hP
  : BidegLE P a b)
    (hQ : BidegLE Q a' b') : BidegLE (P * Q) (a + a') (b + b') := fun m hm => by
  classical
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  exact ⟨add_le_add (hP u hu).1 (hQ v hv).1, add_le_add (hP u hu).2 (hQ v hv).2⟩

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.pow
    {P : MvPolynomial (Var d0 d1) K} {a b : ℕ} (hP :
  BidegLE P a b) (n : ℕ) :
    BidegLE (P ^ n) (n * a) (n * b) := by
  induction n with
  | zero => simpa using BidegLE.one 0 0
  | succ n ih => rw [pow_succ, add_mul, add_mul, one_mul, one_mul]; exact ih.mul hP

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.prod
    {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial (Var
  d0 d1) K} {a b : ι → ℕ}
    (h : ∀ i ∈ s, BidegLE (P i) (a i) (b i)) :
    BidegLE (∏ i ∈ s, P i) (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BidegLE.one 0 0
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.X_inl
    (i : Fin d0) : BidegLE (X (Sum.inl i) : MvPolynomial
  (Var d0 d1) K) 1 0 := by
  intro m hm
  classical
  rw [X, support_monomial, ite_eq_right one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp [Finsupp.single_apply]

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.X_inr
    (j : Fin d1) : BidegLE (X (Sum.inr j) : MvPolynomial
  (Var d0 d1) K) 0 1 := by
  intro m hm
  classical
  rw [X, support_monomial, ite_eq_right one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp [Finsupp.single_apply]

theorem _root_.LeanPool.StrongSix.Thm1.BidegLE.C_mul
    {P : MvPolynomial (Var d0 d1) K} {a b : ℕ} (hP :
  BidegLE P a b) (c : K) :
    BidegLE (C c * P) a b := by
  rw [← smul_eq_C_mul]; exact hP.smul c

/-! ### The subtorus `T_U` -/

/-- The subtorus `T_U = {y : y^φ = 1 for all integral φ ∈ U}`. -/
def TU (K : Type*) [Field K] (U : Submodule ℚ (Fin d1 → ℚ)) : Subgroup (Fin d1 → Kˣ) where
  carrier := {y | ∀ φ : Fin d1 → ℤ, (fun j => (φ j : ℚ)) ∈ U → ∏ j, y j ^ φ j = 1}
  one_mem' φ _ := by simp
  mul_mem' {y z} hy hz φ hφ := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, hy φ hφ, hz φ hφ, mul_one]
  inv_mem' {y} hy φ hφ := by
    simp only [Pi.inv_apply, inv_zpow', zpow_neg, Finset.prod_inv_distrib, hy φ hφ, inv_one]

theorem prod_zpow_eq {G : Type*} [CommGroup G] (u : G) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ j ∈ s, u ^ f j = u ^ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add]

/-- Points of `T_U` separate characters outside `U` (char 0). -/
theorem exists_torus_pt [CharZero K] (U : Submodule ℚ (Fin d1 → ℚ)) {c : Fin d1 → ℤ}
    (hc : (fun j => (c j : ℚ)) ∉ U) : ∃ y ∈ TU K U, ∏ j, y j ^ c j ≠ 1 := by
  obtain ⟨f, hfc, hUf⟩ := Submodule.exists_le_ker_of_notMem hc
  let β : Fin d1 → ℚ := fun j => f (Pi.single j 1)
  let N : ℕ := ∏ j, (β j).den
  have hden : ∀ j, (β j).den ∣ N := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let b : Fin d1 → ℤ := fun j => (β j).num * ((N / (β j).den : ℕ) : ℤ)
  have hb : ∀ j, (b j : ℚ) = N * β j := by
    intro j
    simp only [b, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hden j) (by exact_mod_cast (β j).den_nz)]
    nth_rewrite 3 [← Rat.num_div_den (β j)]
    field_simp
  have hN : (N : ℚ) ≠ 0 := by
    simp only [N, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (β j).den_nz
  -- `Σ b_j ψ_j = N f(ψ)`
  have hlin : ∀ ψ : Fin d1 → ℤ, ((∑ j, b j * ψ j : ℤ) : ℚ) = N * f (fun j => (ψ j : ℚ)) := by
    intro ψ
    rw [LinearMap.pi_apply_eq_sum_univ f, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j]
    simp only [β, smul_eq_mul]
    have : (fun i => if j = i then (1 : ℚ) else 0) = Pi.single j 1 := by
      funext i; simp [Pi.single_apply, eq_comm]
    rw [this]; ring
  let u : Kˣ := Units.mk0 2 two_ne_zero
  have hu : ∀ n : ℤ, u ^ n = 1 → n = 0 := by
    intro n hn
    have h2 : ((2 : ℚ) ^ n : ℚ) = 1 := by
      have : ((u ^ n : Kˣ) : K) = 1 := by rw [hn]; rfl
      rw [Units.val_zpow_eq_zpow_val] at this
      have : (((2 : ℚ) ^ n : ℚ) : K) = ((1 : ℚ) : K) := by push_cast; exact this
      exact_mod_cast this
    exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h2
  refine ⟨fun j => u ^ b j, fun φ hφ => ?_, fun h => ?_⟩
  · simp only [← zpow_mul]
    rw [prod_zpow_eq]
    have : ((∑ j, b j * φ j : ℤ) : ℚ) = 0 := by rw [hlin, hUf hφ, mul_zero]
    rw [show ∑ j, b j * φ j = 0 by exact_mod_cast this, zpow_zero]
  · simp only [← zpow_mul] at h
    rw [prod_zpow_eq] at h
    have h0 := hu _ h
    have : ((∑ j, b j * c j : ℤ) : ℚ) = 0 := by rw [h0]; rfl
    rw [hlin] at this
    exact hfc ((mul_eq_zero.mp this).resolve_left hN)

/-! ### Independent characters -/

/-- The character `y ↦ ∏ₖ y_{j k}^{b k}` of `T_U`. -/
def torusChar (U : Submodule ℚ (Fin d1 → ℚ)) {κ : Type*} [Fintype κ] (jj : κ → Fin d1) (b : κ → ℕ) :
    TU K U →* K where
  toFun y := ∏ k, ((y.1 (jj k) : Kˣ) : K) ^ b k
  map_one' := by simp
  map_mul' y z := by
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, mul_pow, Finset.prod_mul_distrib]

theorem torusChar_injective [CharZero K] (U : Submodule ℚ (Fin d1 → ℚ)) {κ : Type*} [Fintype κ]
    (jj : κ → Fin d1) (_ : Function.Injective jj)
    (hind : LinearIndependent ℚ fun k => U.mkQ (Pi.single (jj k) 1)) :
    Function.Injective (torusChar (K := K) U jj) := by
  classical
  intro b b' hbb
  let c : Fin d1 → ℤ := fun i => ∑ k, if jj k = i then ((b k : ℤ) - b' k) else 0
  have hcU : (fun i => (c i : ℚ)) ∈ U := by
    by_contra hc
    obtain ⟨y, hy, hne⟩ := exists_torus_pt (K := K) U hc
    apply hne
    have hyc : ∏ i, y i ^ c i = ∏ k, y (jj k) ^ ((b k : ℤ) - b' k) := by
      simp only [c, ← prod_zpow_eq]
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Finset.prod_eq_single (jj k) (fun i _ hi => by rw [ite_eq_right (Ne.symm hi), zpow_zero])
        (by simp)]
      simp
    rw [hyc]
    have := congrArg (fun χ : TU K U →* K => χ ⟨y, hy⟩) hbb
    simp only [torusChar, MonoidHom.coe_mk, OneHom.coe_mk] at this
    have e : ∏ k, y (jj k) ^ ((b k : ℤ) - b' k) =
        (∏ k, y (jj k) ^ b k) / ∏ k, y (jj k) ^ b' k := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_sub, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    rw [e, div_eq_one]
    apply Units.val_injective
    simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
    exact this
  -- `π(c) = Σ (b k − b' k) π(e_{j k}) = 0`
  have hvec : (fun i => (c i : ℚ)) =
      ∑ k, (((b k : ℤ) - b' k : ℤ) : ℚ) • Pi.single (jj k) (1 : ℚ) := by
    funext i
    simp only [c, Int.cast_sum, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : jj k = i
    · simp [h]
    · simp [h, Ne.symm h]
  have hsum : ∑ k, (((b k : ℤ) - b' k : ℤ) : ℚ) • U.mkQ (Pi.single (jj k) 1) = 0 := by
    have : U.mkQ (fun i => (c i : ℚ)) = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hcU
    rw [hvec, map_sum] at this
    simpa only [map_smul] using this
  have := (Fintype.linearIndependent_iff.mp hind) _ hsum
  funext k
  have hk := this k
  have : ((b k : ℤ) : ℚ) = ((b' k : ℤ) : ℚ) := by push_cast at hk ⊢; linarith
  exact_mod_cast this

/-! ### The main count -/

/-- The points of `h₀ × T_U`. -/
abbrev HPts (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ)) :=
  {g : GPt K d0 d1 // g.1 ∈ h0 ∧ g.2 ∈ TU K U}

/-- The restriction of a polynomial to `h₀ × T_U`. -/
noncomputable def restr (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ))
    (P : MvPolynomial (Var d0 d1) K) : HPts h0 U → K := fun g => eval g.1.coords P

theorem exists_indep_quot (U : Submodule ℚ (Fin d1 → ℚ)) :
    ∃ (κ : Type) (_ : Fintype κ) (jj : κ → Fin d1), Function.Injective jj ∧
      Fintype.card κ = d1 - finrank ℚ U ∧
      LinearIndependent ℚ fun k => U.mkQ (Pi.single (jj k) 1) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ :=
    exists_linearIndependent' ℚ (fun i : Fin d1 => U.mkQ (Pi.single i (1 : ℚ)))
  have : Fintype κ := Fintype.ofInjective a ha
  refine ⟨κ, inferInstance, a, ha, ?_, hli⟩
  have hspan : Submodule.span ℚ (Set.range fun i : Fin d1 => U.mkQ (Pi.single i (1 : ℚ))) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective U x
    have hv : v = ∑ i, v i • Pi.single i (1 : ℚ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [LinearMap.map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := finrank_span_eq_card hli
  rw [hsp, hspan, finrank_top] at h1
  have h2 := Submodule.finrank_quotient_add_finrank U
  simp only [Module.finrank_fin_fun] at h2
  omega

/-- **Lower bound for the Hilbert function of `h₀ × T_U`.** -/
theorem exists_indep_restr [CharZero K] (h0 : Submodule K (Fin d0 → K))
    (U : Submodule ℚ (Fin d1 → ℚ)) (N0 N1 : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → MvPolynomial (Var d0 d1) K),
      Fintype.card ι = (N0 / finrank K h0 + 1) ^ finrank K h0 *
        (N1 / (d1 - finrank ℚ U) + 1) ^ (d1 - finrank ℚ U) ∧
      (∀ i, BidegLE (P i) N0 N1) ∧ LinearIndependent K fun i => restr h0 U (P i) := by
  classical
  set h := finrank K h0 with hh
  obtain ⟨κ, _, jj, hj, hκ, hind⟩ := exists_indep_quot U
  set r := d1 - finrank ℚ U with hr
  -- coordinates on `h₀`
  let v := Module.finBasis K h0
  have hL : ∀ i : Fin h, ∃ L : (Fin d0 → K) →ₗ[K] K, L.comp h0.subtype = v.coord i :=
    fun i => LinearMap.exists_extend _
  choose L hLv using hL
  have hLk : ∀ i k, L i (v k : Fin d0 → K) = if k = i then 1 else 0 := by
    intro i k
    have := congrArg (fun f => f (v k)) (hLv i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  let lpoly : Fin h → MvPolynomial (Var d0 d1) K :=
    fun i => ∑ j, C (L i (Pi.single j 1)) * X (Sum.inl j)
  have hlpoly : ∀ i (g : GPt K d0 d1), eval g.coords (lpoly i) = L i g.1 := by
    intro i g
    simp only [lpoly, map_sum, map_mul, eval_C, eval_X, GPt.coords, Sum.elim_inl]
    rw [LinearMap.pi_apply_eq_sum_univ (L i) g.1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext i'; simp [Pi.single_apply, eq_comm]
  have hlpolyB : ∀ i, BidegLE (lpoly i) 1 0 := fun i =>
    BidegLE.sum _ fun j _ => (BidegLE.X_inl j).C_mul _
  -- the family
  let M0 := N0 / h + 1
  let M1 := N1 / r + 1
  let ι := (Fin h → Fin M0) × (κ → Fin M1)
  let P : ι → MvPolynomial (Var d0 d1) K := fun ab =>
    (∏ i, lpoly i ^ (ab.1 i : ℕ)) * ∏ k, X (Sum.inr (jj k)) ^ (ab.2 k : ℕ)
  refine ⟨ι, inferInstance, P, ?_, ?_, ?_⟩
  · simp [ι, Fintype.card_prod, Fintype.card_fin, hκ, M0, M1]
  · intro ab
    have hA := BidegLE.prod Finset.univ (a := fun i => (ab.1 i : ℕ) * 1) (b := fun _ => (ab.1 _
      : ℕ) * 0)
      (P := fun i => lpoly i ^ (ab.1 i : ℕ)) fun i _ => (hlpolyB i).pow _
    have hB := BidegLE.prod Finset.univ (a := fun k => (ab.2 k : ℕ) * 0) (b := fun k => (ab.2 k
      : ℕ) * 1)
      (P := fun k => (X (Sum.inr (jj k)) : MvPolynomial (Var d0 d1) K) ^ (ab.2 k : ℕ))
      fun k _ => (BidegLE.X_inr (jj k)).pow _
    refine (hA.mul hB).mono ?_ ?_
    · simp only [mul_one, mul_zero, Finset.sum_const_zero, add_zero]
      calc ∑ i, (ab.1 i : ℕ) ≤ ∑ _i : Fin h, N0 / h :=
            Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (ab.1 i).2
        _ = h * (N0 / h) := by simp
        _ ≤ N0 := Nat.mul_div_le N0 h
    · simp only [mul_one, mul_zero, Finset.sum_const_zero, zero_add]
      calc ∑ k, (ab.2 k : ℕ) ≤ ∑ _k : κ, N1 / r :=
            Finset.sum_le_sum fun k _ => Nat.lt_succ_iff.mp (ab.2 k).2
        _ = r * (N1 / r) := by simp [hκ]
        _ ≤ N1 := Nat.mul_div_le N1 r
  · rw [Fintype.linearIndependent_iff]
    intro w hw
    -- evaluate at the points `(Σ sᵢ vᵢ, y)`
    let χ := torusChar (K := K) U jj
    have hχinj := torusChar_injective (K := K) U jj hj hind
    have hval : ∀ (s : Fin h → K) (y : TU K U),
        ∑ ab : ι, w ab * ((∏ i, s i ^ (ab.1 i : ℕ)) * χ (fun k => (ab.2 k : ℕ)) y) = 0 := by
      intro s y
      let x : Fin d0 → K := ∑ k, s k • (v k : Fin d0 → K)
      have hx : x ∈ h0 := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (v k).2
      have hLx : ∀ i, L i x = s i := by
        intro i
        simp only [x, map_sum, map_smul, hLk, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have := congrFun hw ⟨(x, y.1), hx, y.2⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, restr] at this
      rw [← this]
      refine Finset.sum_congr rfl fun ab _ => ?_
      simp only [P, map_mul, map_prod, map_pow, hlpoly, hLx]
      simp only [eval_X, GPt.coords, Sum.elim_inr, χ, torusChar, MonoidHom.coe_mk, OneHom.coe_mk]
    -- step 1: for each `y`, the coefficient of each monomial in `s` vanishes
    have hstep : ∀ (a : Fin h → Fin M0) (y : TU K U),
        ∑ b : κ → Fin M1, w (a, b) * χ (fun k => (b k : ℕ)) y = 0 := by
      intro a y
      let mono : (Fin h → Fin M0) → (Fin h →₀ ℕ) :=
        fun a => Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)
      have hmono : Function.Injective mono := by
        intro a a' haa
        funext i
        have := congrArg (fun m : Fin h →₀ ℕ => m i) haa
        simp only [mono, Finsupp.coe_equivFunOnFinite_symm] at this
        exact Fin.ext this
      let Q : MvPolynomial (Fin h) K :=
        ∑ a : Fin h → Fin M0, monomial (mono a) (∑ b : κ → Fin M1, w (a, b) * χ (fun k => (b k :
          ℕ)) y)
      have hQ : Q = 0 := by
        apply MvPolynomial.funext
        intro s
        rw [map_zero, ← hval s y, Fintype.sum_prod_type]
        simp only [Q, map_sum, eval_monomial]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [mono, Finsupp.coe_equivFunOnFinite_symm]
        ring
      have := congrArg (fun p : MvPolynomial (Fin h) K => p.coeff (mono a)) hQ
      simp only [Q, coeff_sum, coeff_monomial] at this
      rw [Finset.sum_eq_single a (fun a' _ ha' => by rw [ite_eq_right (hmono.ne ha')])
        (by simp)] at this
      simpa using this
    -- step 2: Dedekind
    have hded : LinearIndependent K fun b : κ → Fin M1 => (χ (fun k => (b k : ℕ)) : TU K U → K)
      := by
      have := (linearIndependent_monoidHom (TU K U) K).comp (fun b : κ → Fin M1 => χ fun k => (b
        k : ℕ))
        (hχinj.comp fun b b' hb => funext fun k => Fin.ext (congrFun hb k))
      exact this
    rintro ⟨a, b⟩
    have := (Fintype.linearIndependent_iff.mp hded) (fun b => w (a, b)) (by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hstep a y)
    exact this b

end StrongSix.M2

end LeanPool
