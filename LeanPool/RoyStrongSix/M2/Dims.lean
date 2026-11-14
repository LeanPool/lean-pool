/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.RingTheory.Regular.RegularSequence

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import LeanPool.RoyStrongSix.M2.Separate
public import LeanPool.RoyStrongSix.M2.Subgroup

/-!
# Dimension bounds for `V × T_U`

* `lsat U`: the saturated lattice `U ∩ ℤ^{d₁}`. `prodSet h₀ (lsat U)` is the connected subgroup
  `h₀ × T_U` of MultEst.
* `liftP`: polynomials in `X, Y` (`StrongSix.Thm1.Var`) viewed in `B = K[X, Y, Z]`.
* `hfun_prodSet_ge`: the lower bound
  `(tD₀/h + 1)^h (tD₁/r + 1)^r ≤ hfun I(h₀ × T_U) t`, with `h = dim h₀` and `r = d₁ − dim U`, from
  `exists_indep_restr` (`Subgroup.lean`).
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

/-- The saturated lattice `U ∩ ℤ^{d₁}`. -/
def lsat (U : Submodule ℚ (Fin d1 → ℚ)) : AddSubgroup (Fin d1 → ℤ) where
  carrier := {φ | (fun j => (φ j : ℚ)) ∈ U}
  add_mem' {a b} ha hb := by
    have := U.add_mem ha hb
    simpa [Pi.add_def] using this
  zero_mem' := by
    change (fun j => (((0 : Fin d1 → ℤ) j : ℤ) : ℚ)) ∈ U
    rw [show (fun j => (((0 : Fin d1 → ℤ) j : ℤ) : ℚ)) = 0 from by funext j; simp]
    exact U.zero_mem
  neg_mem' {a} ha := by
    have := U.neg_mem ha
    simpa [Pi.neg_def] using this

omit [CharZero K] in
theorem chr_eq_units (y : Fin d1 → Kˣ) (φ : Fin d1 → ℤ) :
    chr y φ = ((∏ j, y j ^ φ j : Kˣ) : K) := by
  rw [chr, Units.coe_prod]
  simp [Units.val_zpow_eq_zpow_val]

omit [CharZero K] in
theorem chr_eq_one_iff (y : Fin d1 → Kˣ) (φ : Fin d1 → ℤ) :
    chr y φ = 1 ↔ ∏ j, y j ^ φ j = 1 := by
  rw [chr_eq_units, Units.val_eq_one]

omit [CharZero K] in
theorem mem_prodSet_lsat_iff (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ))
    (g : GPt K d0 d1) : g ∈ prodSet h0 (lsat U) ↔ g.1 ∈ h0 ∧ g.2 ∈ TU K U := by
  simp only [prodSet, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl ⟨fun h φ hφ => (chr_eq_one_iff _ _).mp (h φ hφ),
    fun h φ hφ => (chr_eq_one_iff _ _).mpr (h φ hφ)⟩

/-- Polynomials in `X, Y` as polynomials in `X, Y, Z`. -/
noncomputable def liftP : MvPolynomial (Var d0 d1) K →ₐ[K] MvPolynomial (V3 d0 d1) K :=
  rename (Sum.elim Sum.inl fun j => Sum.inr (Sum.inl j))

theorem liftP_injective_map :
    Function.Injective (Sum.elim Sum.inl fun j => Sum.inr (Sum.inl j) : Var d0 d1 → V3 d0 d1) := by
  rintro (a | a) (b | b) h <;> simp_all

omit [CharZero K] in
theorem eval_liftP (g : GPt K d0 d1) (P : MvPolynomial (Var d0 d1) K) :
    eval (pt g) (liftP P) = eval g.coords P := by
  rw [liftP, eval_rename]
  apply congrArg (fun f => eval f P)
  funext v
  rcases v with k | j <;> rfl

omit [CharZero K] in
theorem liftP_mem_FLE {P : MvPolynomial (Var d0 d1) K} {N0 N1 : ℕ} (h : BidegLE P N0 N1) :
    liftP P ∈ FLE K blk ![N0, N1] := by
  classical
  rw [FLE, mem_restrictSupport_iff, liftP, support_rename_of_injective liftP_injective_map]
  intro m' hm' i
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  obtain ⟨h0, h1⟩ := h m hm
  have hv : ∀ v : Var d0 d1, Finsupp.mapDomain (Sum.elim Sum.inl fun j => Sum.inr (Sum.inl j)) m
      ((Sum.elim Sum.inl fun j => Sum.inr (Sum.inl j)) v) = m v :=
    fun v => Finsupp.mapDomain_apply_of_injective liftP_injective_map m v
  have hz : ∀ j : Fin d1, Finsupp.mapDomain (Sum.elim Sum.inl fun j => Sum.inr (Sum.inl j)) m
      (Sum.inr (Sum.inr j) : V3 d0 d1) = 0 := by
    intro j
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    rcases v with k | k <;> simp at hv
  unfold bdeg
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  fin_cases i
  · simp only [blk, Sum.elim_inl, Sum.elim_inr, Fin.zero_eta, Fin.isValue, ite_true,
      Matrix.cons_val_zero, one_ne_zero, ite_false, Finset.sum_const_zero, add_zero]
    calc ∑ k, Finsupp.mapDomain _ m (Sum.inl k) = ∑ k, m (Sum.inl k) :=
          Finset.sum_congr rfl fun k _ => hv (Sum.inl k)
      _ ≤ N0 := h0
  · simp only [blk, Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, zero_ne_one, ite_false,
      Finset.sum_const_zero, zero_add, ite_true, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc (∑ j, Finsupp.mapDomain _ m (Sum.inr (Sum.inl j))) +
          ∑ j, Finsupp.mapDomain _ m (Sum.inr (Sum.inr j))
        = ∑ j, m (Sum.inr j) + 0 := by
          congr 1
          · exact Finset.sum_congr rfl fun j _ => hv (Sum.inr j)
          · exact Finset.sum_eq_zero fun j _ => hz j
      _ ≤ N1 := by simpa using h1

theorem smul_D (D0 D1 t : ℕ) : t • (![D0, D1] : Fin 2 → ℕ) = ![t * D0, t * D1] := by
  funext i; fin_cases i <;> simp

/-- **Lower bound** for `hfun I(h₀ × T_U)`. -/
theorem hfun_prodSet_ge (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ))
    (D0 D1 t : ℕ) :
    (t * D0 / finrank K h0 + 1) ^ finrank K h0 *
        (t * D1 / (d1 - finrank ℚ U) + 1) ^ (d1 - finrank ℚ U) ≤
      hfun blk ![D0, D1] K (vanish (prodSet h0 (lsat U))) t := by
  classical
  obtain ⟨ι, _, P, hcard, hdeg, hind⟩ := exists_indep_restr h0 U (t * D0) (t * D1)
  rw [hfun_vanish_eq, ← hcard]
  set G0 := prodSet h0 (lsat U)
  set R := (FLE K blk (t • ![D0, D1])).map (restrE G0)
  have hmem : ∀ i, restrE G0 (liftP (P i)) ∈ R := fun i =>
    ⟨liftP (P i), by rw [smul_D]; exact liftP_mem_FLE (hdeg i), rfl⟩
  let f : ι → R := fun i => ⟨restrE G0 (liftP (P i)), hmem i⟩
  have hf : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ i, c i • restr h0 U (P i) = 0 := by
      funext g
      have := congrArg (fun x : R => (x : GPt K d0 d1 → K) g.1) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply, f] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, restr]
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hg : g.1 ∈ G0 := (mem_prodSet_lsat_iff h0 U g.1).mpr g.2
      rw [restrE_apply, ite_eq_left hg, eval_liftP]
    exact (Fintype.linearIndependent_iff.mp hind) c hc'
  exact hf.fintype_card_le_finrank

/-! ### Upper bound for `hfun I(h₀ × T_U)` -/

omit [CharZero K] in
/-- Linear coordinates on a subspace. -/
theorem exists_coords (V : Submodule K (Fin d0 → K)) :
    ∃ L : (Fin d0 → K) →ₗ[K] (Fin (finrank K V) → K),
      ∀ x ∈ V, x = ∑ i, L x i • ((Module.finBasis K V i : V) : Fin d0 → K) := by
  classical
  let bV := Module.finBasis K V
  have hLex : ∀ i, ∃ Li : (Fin d0 → K) →ₗ[K] K, Li.comp V.subtype = bV.coord i :=
    fun i => LinearMap.exists_extend _
  choose Li hLi using hLex
  refine ⟨LinearMap.pi Li, fun x hx => ?_⟩
  have h1 : (⟨x, hx⟩ : V) = ∑ i, bV.repr ⟨x, hx⟩ i • bV i := (bV.sum_repr _).symm
  have h2 := congrArg Subtype.val h1
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  convert h2 using 3 with i
  have := congrArg (fun f => f ⟨x, hx⟩) (hLi i)
  simpa using this

/-- Integer "rational coordinates" modulo `U`: a map `ℤ^{d₁} → ℤ^{r}` (`r = d₁ − dim U`) whose
fibres
are the classes modulo `lsat U`, bounded linearly by `Σ |mⱼ|`. -/
theorem exists_wv (U : Submodule ℚ (Fin d1 → ℚ)) :
    ∃ (wv : (Fin d1 → ℤ) → Fin (d1 - finrank ℚ U) → ℤ) (M : ℕ),
      (∀ m m', wv m = wv m' → m - m' ∈ lsat U) ∧
      (∀ m k, |wv m k| ≤ M * ∑ j, |m j|) := by
  classical
  set r := d1 - finrank ℚ U
  have hr : finrank ℚ ((Fin d1 → ℚ) ⧸ U) = r := by
    have := Submodule.finrank_quotient_add_finrank U
    simp only [Module.finrank_fin_fun] at this
    omega
  let bq := (Module.finBasis ℚ ((Fin d1 → ℚ) ⧸ U)).reindex (finCongr hr)
  let q : (Fin d1 → ℚ) →ₗ[ℚ] (Fin r → ℚ) := bq.equivFun.toLinearMap ∘ₗ U.mkQ
  have hq : ∀ v, q v = 0 → v ∈ U := by
    intro v hv
    have : U.mkQ v = 0 := by
      apply bq.equivFun.injective
      simpa [q] using hv
    simpa using this
  let qe : Fin d1 → Fin r → ℚ := fun i => q (Pi.single i 1)
  let δ : ℕ := ∏ i, ∏ k, (qe i k).den
  have hδ : (δ : ℚ) ≠ 0 := by
    simp only [δ, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun k _ => by
      exact_mod_cast (qe i k).den_nz
  have hden : ∀ i k, (qe i k).den ∣ δ := fun i k =>
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ k, (qe i k).den) (Finset.mem_univ i))
  let W : Fin d1 → Fin r → ℤ := fun i k => (qe i k).num * ((δ / (qe i k).den : ℕ) : ℤ)
  have hW : ∀ i k, (W i k : ℚ) = δ * qe i k := by
    intro i k
    simp only [W, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hden i k) (by exact_mod_cast (qe i k).den_nz)]
    nth_rewrite 3 [← Rat.num_div_den (qe i k)]
    field_simp
  let wv : (Fin d1 → ℤ) → Fin r → ℤ := fun m k => ∑ i, m i * W i k
  have hwv : ∀ m k, (wv m k : ℚ) = δ * q (fun j => (m j : ℚ)) k := by
    intro m k
    have hm : (fun j => (m j : ℚ)) = ∑ i, (m i : ℚ) • Pi.single i (1 : ℚ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hm, map_sum, Finset.sum_apply, Finset.mul_sum]
    push_cast [wv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hW]
    simp only [qe]; ring
  refine ⟨wv, ∑ i, ∑ k, (W i k).natAbs, fun m m' h => ?_, fun m k => ?_⟩
  · apply hq
    funext k
    have h1 := hwv m k
    have h2 := hwv m' k
    rw [h] at h1
    have : q (fun j => (m j : ℚ)) k = q (fun j => (m' j : ℚ)) k := by
      have := h1.symm.trans h2
      exact mul_left_cancel₀ hδ this
    rw [show (fun j => (((m - m') j : ℤ) : ℚ)) = (fun j => (m j : ℚ)) - fun j => (m' j : ℚ) by
      funext j; simp, map_sub, Pi.sub_apply, this, sub_self]
    rfl
  · simp only [wv]
    calc |∑ i, m i * W i k| ≤ ∑ i, |m i * W i k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |m i| * |W i k| := by simp [abs_mul]
      _ ≤ ∑ i, |m i| * ((∑ i, ∑ k, (W i k).natAbs : ℕ) : ℤ) := by
          gcongr with i
          rw [Int.abs_eq_natAbs]
          exact_mod_cast (Finset.single_le_sum (f := fun k => (W i k).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans
            (Finset.single_le_sum (f := fun i => ∑ k, (W i k).natAbs)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      _ = _ := by rw [← Finset.sum_mul, mul_comm]

omit [CharZero K] in
theorem totalDegree_prod_le' {σ' : Type*} {ι' : Type*} (s : Finset ι') (f : ι' → MvPolynomial σ'
  K) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact (totalDegree_mul _ _).trans (add_le_add le_rfl ih)

omit [CharZero K] in
theorem eval_monomial_pt (g : GPt K d0 d1) (e : V3 d0 d1 →₀ ℕ) (c : K) :
    eval (pt g) (monomial e c) = c * ((∏ k, g.1 k ^ e (Sum.inl k)) *
      chr g.2 (fun j => (e (Sum.inr (Sum.inl j)) : ℤ) - e (Sum.inr (Sum.inr j)))) := by
  rw [eval_monomial, ← prod_pt]
  congr 1
  exact Finsupp.prod_fintype e (fun i k => pt g i ^ k) (fun _ => pow_zero _)

omit [CharZero K] in
/-- **Upper bound** for `hfun I(h₀ × T_U)`. -/
theorem hfun_prodSet_le (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ))
    (D0 D1 : ℕ) : ∃ M : ℕ, ∀ t, hfun blk ![D0, D1] K (vanish (prodSet h0 (lsat U))) t ≤
      (t * D0 + 1) ^ finrank K h0 * (2 * M * (t * D1) + 1) ^ (d1 - finrank ℚ U) := by
  classical
  obtain ⟨L, hL⟩ := exists_coords h0
  obtain ⟨wv, M, hwv1, hwv2⟩ := exists_wv U
  refine ⟨M, fun t => ?_⟩
  set N0 := t * D0
  set N1 := t * D1
  set G0 := prodSet h0 (lsat U)
  let bV := Module.finBasis K h0
  let pick : (Fin (d1 - finrank ℚ U) → ℤ) → (Fin d1 → ℤ) :=
    fun w => if hw : ∃ m, wv m = w then hw.choose else 0
  have hpick : ∀ m, m - pick (wv m) ∈ lsat U := by
    intro m
    have hex : ∃ m', wv m' = wv m := ⟨m, rfl⟩
    have : wv (pick (wv m)) = wv m := by simp only [pick, dite_eq_left hex]; exact hex.choose_spec
    exact hwv1 m _ this.symm
  let Φ : (Fin (finrank K h0) → Fin (N0 + 1)) × (Fin (d1 - finrank ℚ U) → Fin (2 * M * N1 + 1)) →
      (GPt K d0 d1 → K) :=
    fun bw g => if g ∈ G0 then (∏ i, L g.1 i ^ (bw.1 i : ℕ)) *
      chr g.2 (pick fun k => (bw.2 k : ℤ) - (M * N1 : ℕ)) else 0
  have hspan : (FLE K blk (t • ![D0, D1])).map (restrE G0) ≤ Submodule.span K (Set.range Φ) := by
    rintro _ ⟨P, hP, rfl⟩
    rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    have heS : e ∈ S blk (t • ![D0, D1]) := by
      have hP' : P ∈ FLE K blk (t • ![D0, D1]) := hP
      rw [FLE, mem_restrictSupport_iff] at hP'; exact hP' he
    rw [smul_D] at heS
    -- the data of the monomial
    set α : Fin d0 → ℕ := fun k => e (Sum.inl k)
    set m : Fin d1 → ℤ := fun j => (e (Sum.inr (Sum.inl j)) : ℤ) - e (Sum.inr (Sum.inr j))
    have hα : ∑ k, α k ≤ N0 := by
      have := heS 0
      unfold bdeg at this
      rw [Fintype.sum_sum_type] at this
      simpa [blk] using this
    have hm : ∑ j, |m j| ≤ N1 := by
      have := heS 1
      unfold bdeg at this
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at this
      simp only [blk, Sum.elim_inl, Sum.elim_inr, Fin.isValue, zero_ne_one, ite_false,
        Finset.sum_const_zero, zero_add, ite_true, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          at this
      have hb : ∀ j, |m j| ≤ (e (Sum.inr (Sum.inl j)) : ℤ) + e (Sum.inr (Sum.inr j)) := fun j => by
        simp only [m]; rw [abs_le]; constructor <;> omega
      calc ∑ j, |m j| ≤ ∑ j, ((e (Sum.inr (Sum.inl j)) : ℤ) + e (Sum.inr (Sum.inr j))) :=
            Finset.sum_le_sum fun j _ => hb j
        _ ≤ N1 := by rw [Finset.sum_add_distrib]; exact_mod_cast this
    -- the polynomial in the coordinates
    let Qα : MvPolynomial (Fin (finrank K h0)) K := ∏ k, (∑ i, C ((bV i : Fin d0 → K) k) * X i)
      ^ α k
    have hQdeg : Qα.totalDegree ≤ N0 := by
      refine (totalDegree_prod_le' _ _).trans ?_
      calc ∑ k, ((∑ i, C ((bV i : Fin d0 → K) k) * X i) ^ α k).totalDegree ≤ ∑ k, α k * 1 := by
            refine Finset.sum_le_sum fun k _ => (totalDegree_pow _ _).trans ?_
            apply Nat.mul_le_mul_left
            refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
            exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])
        _ ≤ N0 := by simpa using hα
    have hQeval : ∀ x ∈ h0, eval (L x) Qα = ∏ k, x k ^ α k := by
      intro x hx
      simp only [Qα, map_prod, map_pow, map_sum, map_mul, eval_C, eval_X]
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      have e := congrFun (hL x hx).symm k
      rw [← e]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    -- the restricted monomial as a combination of `Φ`
    have hw : ∀ k, 0 ≤ wv m k + (M * N1 : ℕ) ∧ wv m k + (M * N1 : ℕ) ≤ 2 * (M : ℤ) * N1 := by
      intro k
      have h1 := hwv2 m k
      have h2 : (M : ℤ) * ∑ j, |m j| ≤ M * N1 := by gcongr
      rw [abs_le] at h1
      push_cast
      constructor <;> nlinarith
    let w' : Fin (d1 - finrank ℚ U) → Fin (2 * M * N1 + 1) := fun k =>
      ⟨(wv m k + (M * N1 : ℕ)).toNat, by
        have := hw k
        push_cast at this
        zify
        rw [Int.toNat_of_nonneg this.1]
        linarith [this.2]⟩
    have hw' : (fun k => ((w' k : ℕ) : ℤ) - (M * N1 : ℕ)) = wv m := by
      funext k
      simp only [w']
      rw [Int.toNat_of_nonneg (hw k).1]
      ring
    have hβ : ∀ β ∈ Qα.support, ∀ i, β i < N0 + 1 := fun β hβ i =>
      Nat.lt_succ_of_le ((Finsupp.le_degree i β).trans ((le_totalDegree hβ).trans hQdeg))
    have hrep : restrE G0 (monomial e (P.coeff e)) = ∑ β ∈ Qα.support.attach,
        (P.coeff e * Qα.coeff β.1) • Φ (fun i => ⟨β.1 i, hβ β.1 β.2 i⟩, w') := by
      funext g
      rw [restrE_apply, Finset.sum_apply]
      by_cases hg : g ∈ G0
      · rw [ite_eq_left hg, eval_monomial_pt]
        simp only [Pi.smul_apply, smul_eq_mul, Φ, ite_eq_left hg]
        have hx : g.1 ∈ h0 := hg.1
        have hchr : chr g.2 m = chr g.2 (pick (wv m)) := by
          apply chr_eq_of_sub_mem hg.2
          have := (lsat U).neg_mem (hpick m)
          simpa [neg_sub, sub_eq_neg_add] using this
        rw [hw', ← hchr, ← hQeval g.1 hx, eval_eq]
        rw [show (fun j => (e (Sum.inr (Sum.inl j)) : ℤ) - e (Sum.inr (Sum.inr j))) = m from rfl]
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_attach]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [show (∏ i ∈ β.1.support, L g.1 i ^ β.1 i) = ∏ i, L g.1 i ^ β.1 i from
          Finsupp.prod_fintype β.1 (fun i k => L g.1 i ^ k) (fun _ => pow_zero _)]
        ring
      · rw [ite_eq_right hg]
        simp [Φ, hg]
    rw [hrep]
    exact Submodule.sum_mem _ fun β _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  rw [hfun_vanish_eq]
  have : FiniteDimensional K (Submodule.span K (Set.range Φ)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range Φ)
  calc finrank K ((FLE K blk (t • ![D0, D1])).map (restrE G0))
      ≤ finrank K (Submodule.span K (Set.range Φ)) := Submodule.finrank_mono hspan
    _ ≤ Fintype.card ((Fin (finrank K h0) → Fin (N0 + 1)) ×
          (Fin (d1 - finrank ℚ U) → Fin (2 * M * N1 + 1))) :=
        finrank_range_le_card Φ
    _ = (N0 + 1) ^ finrank K h0 * (2 * M * N1 + 1) ^ (d1 - finrank ℚ U) := by
        simp [Fintype.card_prod]

/-! ### The base complete intersection `I_G = (Y_j Z_j − 1)` -/

/-- The generators `Y_j Z_j − 1`. -/
noncomputable def lG : List (MvPolynomial (V3 d0 d1) K) :=
  List.ofFn fun j : Fin d1 => X (Sum.inr (Sum.inl j)) * X (Sum.inr (Sum.inr j)) - 1

/-- The ideal `I_G` of `G` in `K[X, Y, Z]`. -/
noncomputable def IG : Ideal (MvPolynomial (V3 d0 d1) K) := Ideal.ofList (lG (K := K) (d0 := d0))

omit [CharZero K] in
theorem lG_length : (lG (K := K) (d0 := d0) (d1 := d1)).length = d1 := by simp [lG]

omit [CharZero K] in
theorem YZ_mem_IG (j : Fin d1) :
    X (Sum.inr (Sum.inl j)) * X (Sum.inr (Sum.inr j)) - 1 ∈ (IG : Ideal (MvPolynomial (V3 d0 d1)
      K)) :=
  Ideal.subset_span (by simp [lG])

omit [CharZero K] in
theorem pow_mul_pow_of_mul_eq_one {R : Type*} [CommRing R] {y z : R} (h : y * z = 1) (a b : ℕ) :
    y ^ a * z ^ b = if b ≤ a then y ^ (a - b) else z ^ (b - a) := by
  split_ifs with hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [show b + c - b = c by omega, pow_add, mul_comm (y ^ b), mul_assoc, ← mul_pow, h, one_pow,
      mul_one]
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.mp hab)
    rw [show a + c + 1 - a = c + 1 by omega, show a + c + 1 = a + (c + 1) by ring, pow_add,
      ← mul_assoc, ← mul_pow, h, one_pow, one_mul]

omit [CharZero K] in
/-- **Upper bound** for `hfun I_G`: reduction modulo `Y_j Z_j ≡ 1`. -/
theorem hfun_IG_le (D0 D1 t : ℕ) :
    hfun blk ![D0, D1] K (IG (K := K) (d0 := d0) (d1 := d1)) t ≤
      (t * D0 + 1) ^ d0 * (2 * (t * D1) + 1) ^ d1 := by
  classical
  set N0 := t * D0
  set N1 := t * D1
  set F := FLE K blk (t • ![D0, D1])
  let Ψ : (Fin d0 → Fin (N0 + 1)) × (Fin d1 → Fin (2 * N1 + 1)) → MvPolynomial (V3 d0 d1) K :=
    fun aw => (∏ k, X (Sum.inl k) ^ (aw.1 k : ℕ)) * monoChr fun j => (aw.2 j : ℤ) - N1
  let π := Ideal.Quotient.mk (IG (K := K) (d0 := d0) (d1 := d1))
  have hπ : ∀ j : Fin d1, π (X (Sum.inr (Sum.inl j))) * π (X (Sum.inr (Sum.inr j))) = 1 := by
    intro j
    rw [← map_mul, ← sub_eq_zero, ← map_one π, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (YZ_mem_IG j)
  have hcover : F ≤ Submodule.span K (Set.range Ψ) ⊔ ((IG (K := K) (d0 := d0) (d1 :=
    d1)).restrictScalars K ⊓ F) := by
    intro P hP
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    have heS : e ∈ S blk (t • ![D0, D1]) := by
      have hP' : P ∈ FLE K blk (t • ![D0, D1]) := hP
      rw [FLE, mem_restrictSupport_iff] at hP'; exact hP' he
    rw [smul_D] at heS
    set α : Fin d0 → ℕ := fun k => e (Sum.inl k)
    set a : Fin d1 → ℕ := fun j => e (Sum.inr (Sum.inl j))
    set b : Fin d1 → ℕ := fun j => e (Sum.inr (Sum.inr j))
    have hα : ∑ k, α k ≤ N0 := by
      have := heS 0
      unfold bdeg at this
      rw [Fintype.sum_sum_type] at this
      simpa [blk] using this
    have hab : ∑ j, (a j + b j) ≤ N1 := by
      have := heS 1
      unfold bdeg at this
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at this
      simp only [blk, Sum.elim_inl, Sum.elim_inr, Fin.isValue, zero_ne_one, ite_false,
        Finset.sum_const_zero, zero_add, ite_true, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          at this
      rw [Finset.sum_add_distrib]; exact this
    have hαk : ∀ k, α k < N0 + 1 := fun k => Nat.lt_succ_of_le ((Finset.single_le_sum
      (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans hα)
    have habj : ∀ j, a j + b j ≤ N1 := fun j => (Finset.single_le_sum
      (f := fun j => a j + b j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hab
    let w : Fin d1 → Fin (2 * N1 + 1) := fun j =>
      ⟨((a j : ℤ) - b j + N1).toNat, by have := habj j; omega⟩
    have hw : (fun j => ((w j : ℕ) : ℤ) - N1) = fun j => (a j : ℤ) - b j := by
      funext j; have := habj j; simp only [w]; omega
    set R := Ψ (fun k => ⟨α k, hαk k⟩, w)
    have hRF : R ∈ F := by
      simp only [R, Ψ, hw]
      have h1 : (∏ k, X (Sum.inl k) ^ α k : MvPolynomial (V3 d0 d1) K) ∈
          FLE K blk (∑ k, α k • (Pi.single 0 1 : Fin 2 → ℕ)) :=
        prod_mem_FLE _ _ _ fun k _ => pow_mem_FLE (translVar_mem (K := K) GPt.zero (Sum.inl k) |>
          fun h => by simpa [translVar, GPt.zero, blk] using h) _
      have h2 : monoChr (K := K) (d0 := d0) (fun j => (a j : ℤ) - b j) ∈
          FLE K blk (∑ j, (a j + b j) • (Pi.single 1 1 : Fin 2 → ℕ)) := by
        apply prod_mem_FLE
        intro j _
        have hY := pow_mem_FLE (translVar_mem (K := K) (d0 := d0) GPt.zero (Sum.inr (Sum.inl j)))
        have hZ := pow_mem_FLE (translVar_mem (K := K) (d0 := d0) GPt.zero (Sum.inr (Sum.inr j)))
        simp only [translVar, GPt.zero, blk, Sum.elim_inr, Sum.elim_inl, Pi.one_apply,
          Units.val_one, map_one, one_mul, inv_one] at hY hZ
        split_ifs with hj
        · refine FLE_mono K blk ?_ (hY ((a j : ℤ) - b j).toNat)
          intro i
          fin_cases i
          · simp only [Fin.zero_eta, Fin.isValue, Int.toNat_sub', Int.toNat_natCast,
              Pi.smul_apply, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
              nsmul_zero, Std.le_refl]
          · simp only [Fin.mk_one, Fin.isValue, Int.toNat_sub', Int.toNat_natCast,
              Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, tsub_le_iff_right]
            omega
        · refine FLE_mono K blk ?_ (hZ (-((a j : ℤ) - b j)).toNat)
          intro i
          fin_cases i
          · simp only [Fin.zero_eta, Fin.isValue, neg_sub, Int.toNat_sub', Int.toNat_natCast,
              Pi.smul_apply, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
              nsmul_zero, Std.le_refl]
          · simp only [Fin.mk_one, Fin.isValue, neg_sub, Int.toNat_sub', Int.toNat_natCast,
              Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, tsub_le_iff_right]
            omega
      have := mul_mem_FLE K h1 h2
      refine FLE_mono K blk ?_ this
      rw [smul_D]
      intro i
      fin_cases i
      · simpa [Finset.sum_apply] using hα
      · simpa [Finset.sum_apply] using hab
    have hR : R = (∏ k, X (Sum.inl k) ^ α k) * monoChr (fun j => (a j : ℤ) - b j) := by
      simp only [R, Ψ]; rw [hw]
    have hdiff : monomial e (1 : K) - R ∈ IG (K := K) (d0 := d0) (d1 := d1) := by
      rw [← Ideal.Quotient.eq, hR]
      simp only [monomial_eq, C_1, one_mul, map_mul, map_prod, map_pow, monoChr]
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
      simp only [map_pow]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      congr 1
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [pow_mul_pow_of_mul_eq_one (hπ j), apply_ite (Ideal.Quotient.mk _)]
      simp only [map_pow]
      have ha : a j = e (Sum.inr (Sum.inl j)) := rfl
      have hb : b j = e (Sum.inr (Sum.inr j)) := rfl
      split_ifs with h1 h2 h2
      · congr 1; omega
      · exfalso; omega
      · exfalso; omega
      · congr 1; omega
    have hmono : monomial e (P.coeff e) = P.coeff e • R + P.coeff e • (monomial e 1 - R) := by
      rw [← smul_add, add_sub_cancel, smul_monomial, smul_eq_mul, mul_one]
    rw [hmono]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · apply Submodule.mem_sup_right
      refine Submodule.smul_mem _ _ ⟨hdiff, ?_⟩
      apply Submodule.sub_mem _ _ hRF
      exact (monomial_mem_restrictSupport (R := K)).mpr (Or.inl (by rw [smul_D]; exact heS))
  have : FiniteDimensional K (Submodule.span K (Set.range Ψ)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range Ψ)
  have : FiniteDimensional K ↥((IG (K := K) (d0 := d0) (d1 := d1)).restrictScalars K ⊓ F) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have h1 := Submodule.finrank_mono hcover
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span K (Set.range Ψ))
    ((IG (K := K) (d0 := d0) (d1 := d1)).restrictScalars K ⊓ F)
  have h3 : finrank K (Submodule.span K (Set.range Ψ)) ≤ (N0 + 1) ^ d0 * (2 * N1 + 1) ^ d1 := by
    refine (finrank_range_le_card Ψ).trans (le_of_eq ?_)
    simp [Fintype.card_prod]
  have e : hfun blk ![D0, D1] K (IG (K := K) (d0 := d0) (d1 := d1)) t =
      finrank K F - finrank K ↥((IG (K := K) (d0 := d0) (d1 := d1)).restrictScalars K ⊓ F) := rfl
  rw [e]
  omega

end StrongSix.M2

end LeanPool
