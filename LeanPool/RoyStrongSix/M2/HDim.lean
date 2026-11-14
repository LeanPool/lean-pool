/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Section

/-!
# Hilbert dimension of ideals of `K[σ]`

* `hfun_section_s`: the section inequality for `P` of block degree `≤ s • D`:
  `hfun (J + (P)) (t + s) ≤ hfun J (t + s) − hfun J t`.
* `hdata J`: the data `(dimension, degree)` of `hfun J`. For `J ≠ ⊤` it is genuine data
  (`hdata_spec`), with positive degree.
* `hdim_bot_le`: `hdim ⊥ ≤ card σ`, by a growth bound.
* `hdim_section_lt`: a non-zero-divisor (of any degree) strictly lowers the dimension of a proper
  ideal containing the section.
* `hdim_lt_of_lt`: `q ⊊ q'` with `q` prime and `q' ≠ ⊤` gives `hdim q' < hdim q`.
Throughout, `D i ≥ 1` for every block, so every polynomial has block degree `≤ s • D` for some `s`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

/-! ### Pure lemmas on data -/

theorem HasData.le_of_iter_zero {g : ℕ → ℤ} {b n : ℕ} {d : ℤ} (hg : HasData g b d)
    (hz : ∀ᶠ k in Filter.atTop, (Δ^[n + 1] g) k = 0) : b ≤ n := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hlt
  have := iter_Δ_eventually_zero_le (show n + 1 ≤ n + 1 + j by omega) hz
  obtain ⟨k, h1, h2⟩ := (this.and hg.2).exists
  exact hg.1 (h2 ▸ h1)

theorem HasData.dim_le {f g : ℕ → ℤ} {a n : ℕ} {c : ℤ} (hf : HasData f a c)
    (hnn : ∀ᶠ k in Filter.atTop, 0 ≤ f k) (hfg : ∀ᶠ k in Filter.atTop, f k ≤ g k)
    (hz : ∀ᶠ k in Filter.atTop, (Δ^[n + 1] g) k = 0) : a ≤ n := by
  have hc := hf.pos hnn
  have hgz : ¬ ∀ᶠ k in Filter.atTop, g k = 0 := fun h => by
    obtain ⟨k, h1, h2, h3⟩ := ((hf.eventually_pos hc).and (hfg.and h)).exists
    linarith
  obtain ⟨b, d, hgd⟩ := HasData.exists ⟨n + 1, hz⟩ hgz
  have hb := hgd.le_of_iter_zero hz
  rcases hf.compare hgd hfg hnn with h | ⟨rfl, -⟩ <;> omega

theorem iter_Δ_comp_cast (F : ℤ → ℤ) (k : ℕ) :
    (Δ^[k] fun t : ℕ => F t) = fun t : ℕ => ((fwdDiff 1)^[k] F) (t : ℤ) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have : Δ (fun t : ℕ => F t) = fun t : ℕ => fwdDiff 1 F (t : ℤ) := by
      funext t; simp [fwdDiff]
    rw [this, ih]

/-- `t ↦ (N t + 1)^n` has vanishing `(n+1)`-st difference. -/
theorem iter_Δ_pow_zero (N n : ℕ) :
    (Δ^[n + 1] fun t : ℕ => ((N * t + 1 : ℕ) : ℤ) ^ n) = 0 := by
  let P : Polynomial ℤ := (Polynomial.C (N : ℤ) * Polynomial.X + Polynomial.C 1) ^ n
  have hP : P.natDegree < n + 1 := by
    have : P.natDegree ≤ n := by
      apply (Polynomial.natDegree_pow_le).trans
      have : (Polynomial.C (N : ℤ) * Polynomial.X + Polynomial.C 1).natDegree ≤ 1 :=
        Polynomial.natDegree_linear_le
      calc n * (Polynomial.C (N : ℤ) * Polynomial.X + Polynomial.C 1).natDegree ≤ n * 1 :=
            Nat.mul_le_mul_left _ this
        _ = n := by ring
    omega
  have h := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP
  have e : (fun t : ℕ => ((N * t + 1 : ℕ) : ℤ) ^ n) = fun t : ℕ => P.eval (t : ℤ) := by
    funext t; simp [P]
  rw [e, iter_Δ_comp_cast (fun x => P.eval x), h]
  rfl

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
variable (β : σ → ι) (D : ι → ℕ) (K : Type*) [Field K]

/-! ### The step-`s` section inequality -/

omit [DecidableEq σ] [Fintype ι] in
theorem hfun_section_s [Finite ι] {J : Ideal (MvPolynomial σ K)} {P : MvPolynomial σ K} {s : ℕ}
    (hP : P ∈ FLE K β (s • D)) (hnzd : ∀ Q, P * Q ∈ J → Q ∈ J) (t : ℕ) :
    (hfun β D K (J ⊔ Ideal.span {P}) (t + s) : ℤ) ≤ hfun β D K J (t + s) - hfun β D K J t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  by_cases hP0 : P = 0
  · have htop : J = ⊤ := (Ideal.eq_top_iff_one _).mpr (hnzd 1 (by simp [hP0]))
    have h0 : ∀ t, hfun β D K (⊤ : Ideal (MvPolynomial σ K)) t = 0 := fun t => by
      unfold hfun; rw [Submodule.restrictScalars_top, top_inf_eq, Nat.sub_self]
    simp [htop, h0]
  set F0 := FLE K β (t • D)
  set F1 := FLE K β ((t + s) • D)
  let mP : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K P
  have hinj : Function.Injective mP := fun x y hxy => mul_left_cancel₀ hP0 hxy
  set M := F0.map mP
  have hM : M ≤ F1 := by
    rintro _ ⟨Q, hQ, rfl⟩
    have := mul_mem_FLE K hP hQ
    rwa [show s • D + t • D = (t + s) • D by rw [add_nsmul, add_comm]] at this
  set J1 := J.restrictScalars K ⊓ F1
  set J0 := J.restrictScalars K ⊓ F0
  set J2 := (J ⊔ Ideal.span {P}).restrictScalars K ⊓ F1
  have : FiniteDimensional K J1 := Submodule.finiteDimensional_of_le inf_le_right
  have : FiniteDimensional K M := Submodule.finiteDimensional_of_le hM
  have : FiniteDimensional K J2 := Submodule.finiteDimensional_of_le inf_le_right
  have hsup : J1 ⊔ M ≤ J2 := by
    apply sup_le (inf_le_inf_right _ (Submodule.restrictScalars_mono K le_sup_left))
    intro x hx
    refine ⟨?_, hM hx⟩
    obtain ⟨Q, -, rfl⟩ := hx
    exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self P))
  have hinf : J1 ⊓ M = J0.map mP := by
    apply le_antisymm
    · rintro x ⟨⟨hxJ, -⟩, Q, hQ, rfl⟩
      exact ⟨Q, ⟨hnzd Q hxJ, hQ⟩, rfl⟩
    · rintro _ ⟨Q, ⟨hQJ, hQ⟩, rfl⟩
      exact ⟨⟨J.mul_mem_left P hQJ, hM ⟨Q, hQ, rfl⟩⟩, Q, hQ, rfl⟩
  have e1 : ∀ (U : Submodule K (MvPolynomial σ K)) [FiniteDimensional K U],
      finrank K (U.map mP) = finrank K U :=
    fun U _ => LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj U).symm
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq J1 M
  rw [hinf] at h1
  have eM : finrank K M = finrank K F0 := e1 F0
  have eJ0 : finrank K (J0.map mP) = finrank K J0 := e1 J0
  have h2 := Submodule.finrank_mono hsup
  have h3 : finrank K J2 ≤ finrank K F1 := Submodule.finrank_mono inf_le_right
  have h4 : finrank K J0 ≤ finrank K F0 := Submodule.finrank_mono inf_le_right
  have h5 : finrank K J1 ≤ finrank K F1 := Submodule.finrank_mono inf_le_right
  have f1 : hfun β D K (J ⊔ Ideal.span {P}) (t + s) = finrank K F1 - finrank K J2 := rfl
  have f2 : hfun β D K J (t + s) = finrank K F1 - finrank K J1 := rfl
  have f3 : hfun β D K J t = finrank K F0 - finrank K J0 := rfl
  rw [f1, f2, f3, Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_sub h5]
  omega

/-! ### Data of an ideal -/

/-- The data `(dimension, degree)` of `hfun J` (junk `(0, 0)` if there is none). -/
noncomputable def hdata (J : Ideal (MvPolynomial σ K)) : ℕ × ℤ := by
  classical
  exact if h : ∃ p : ℕ × ℤ, HasData (fun t => (hfun β D K J t : ℤ)) p.1 p.2 then
    Classical.choose h else (0, 0)

omit [DecidableEq σ] [Fintype ι] in
theorem one_le_hfun [Finite ι] {J : Ideal (MvPolynomial σ K)} (hJ : J ≠ ⊤) (t : ℕ) : 1 ≤ hfun β
  D K J t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  unfold hfun
  have h1 : (1 : MvPolynomial σ K) ∈ FLE K β (t • D) := by
    rw [show (1 : MvPolynomial σ K) = monomial 0 1 from rfl, FLE, monomial_mem_restrictSupport]
    exact Or.inl fun i => by simp
  have hlt : J.restrictScalars K ⊓ FLE K β (t • D) < FLE K β (t • D) := by
    refine lt_of_le_of_ne inf_le_right fun h => hJ ?_
    have : (1 : MvPolynomial σ K) ∈ J.restrictScalars K ⊓ FLE K β (t • D) := by rw [h]; exact h1
    exact (Ideal.eq_top_iff_one _).mpr this.1
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

omit [DecidableEq σ] [Fintype ι] in
theorem hdata_spec [Finite ι] {J : Ideal (MvPolynomial σ K)} (hJ : J ≠ ⊤) :
    HasData (fun t => (hfun β D K J t : ℤ)) (hdata β D K J).1 (hdata β D K J).2 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hz : ¬ ∀ᶠ k in Filter.atTop, (hfun β D K J k : ℤ) = 0 := fun h => by
    obtain ⟨k, hk⟩ := h.exists
    have := one_le_hfun β D K hJ k
    omega
  obtain ⟨a, c, hac⟩ := HasData.exists (hfun_evPoly β D K J) hz
  have hex : ∃ p : ℕ × ℤ, HasData (fun t => (hfun β D K J t : ℤ)) p.1 p.2 := ⟨(a, c), hac⟩
  unfold hdata
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

omit [DecidableEq σ] [Fintype ι] in
theorem hdata_pos [Finite ι] {J : Ideal (MvPolynomial σ K)} (hJ : J ≠ ⊤) : 0 < (hdata β D K J).2
  := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact
    (hdata_spec β D K hJ).pos (Filter.Eventually.of_forall fun _ => by positivity)

omit [DecidableEq σ] [Fintype ι] in
theorem hdata_eq [Finite ι] {J : Ideal (MvPolynomial σ K)} (hJ : J ≠ ⊤) {a : ℕ} {c : ℤ}
    (h : HasData (fun t => (hfun β D K J t : ℤ)) a c) : hdata β D K J = (a, c) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨h1, h2⟩ := (hdata_spec β D K hJ).unique h
  exact Prod.ext h1 h2

omit [DecidableEq σ] [Fintype ι] in
/-- Comparison of data under inclusion of proper ideals. -/
theorem hdata_le_of_le [Finite ι] {J J' : Ideal (MvPolynomial σ K)} (h : J ≤ J') (hJ' : J' ≠ ⊤) :
    (hdata β D K J').1 < (hdata β D K J).1 ∨
      ((hdata β D K J').1 = (hdata β D K J).1 ∧ (hdata β D K J').2 ≤ (hdata β D K J).2) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact
    (hdata_spec β D K hJ').compare (hdata_spec β D K (ne_top_of_le_ne_top hJ' h))
        (Filter.Eventually.of_forall fun t => by exact_mod_cast hfun_mono β D K h t)
        (Filter.Eventually.of_forall fun _ => by positivity)

/-! ### The dimension of the zero ideal -/

omit [DecidableEq σ] in
theorem finrank_FLE_le (t : ℕ) :
    finrank K (FLE K β (t • D)) ≤ (t * (∑ i, D i) + 1) ^ Fintype.card σ := by
  classical
  set N := t * ∑ i, D i
  have : Finite (S β (t • D)) := (S_finite β (t • D)).to_subtype
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K (S β (t • D)))]
  have hbd : ∀ m ∈ S β (t • D), ∀ s, m s < N + 1 := fun m hm s => by
    have := (le_bdeg β m s).trans (hm (β s))
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have : D (β s) ≤ ∑ i, D i := Finset.single_le_sum (f := D) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ _)
    have : t * D (β s) ≤ N := Nat.mul_le_mul_left _ this
    omega
  let f : S β (t • D) → (σ → Fin (N + 1)) := fun m s => ⟨m.1 s, hbd m.1 m.2 s⟩
  have hf : Function.Injective f := fun m m' h => by
    apply Subtype.ext
    ext s
    have := congrFun h s
    simpa [f] using congrArg Fin.val this
  calc Nat.card (S β (t • D)) ≤ Nat.card (σ → Fin (N + 1)) := Nat.card_le_card_of_injective f hf
    _ = (N + 1) ^ Fintype.card σ := by simp [Nat.card_eq_fintype_card]

omit [DecidableEq σ] [Fintype ι] in
theorem hdim_bot_le [Finite ι] : (hdata β D K (⊥ : Ideal (MvPolynomial σ K))).1 ≤ Fintype.card σ
  := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hb : (⊥ : Ideal (MvPolynomial σ K)) ≠ ⊤ := bot_ne_top
  apply HasData.dim_le (hdata_spec β D K hb) (Filter.Eventually.of_forall fun _ => by positivity)
    (g := fun t : ℕ => (((∑ i, D i) * t + 1 : ℕ) : ℤ) ^ Fintype.card σ)
  · refine Filter.Eventually.of_forall fun t => ?_
    have := finrank_FLE_le β D K t
    have e : hfun β D K ⊥ t ≤ finrank K (FLE K β (t • D)) := hfun_le β D K _ t
    rw [mul_comm (∑ i, D i) t]
    exact_mod_cast e.trans this
  · exact Filter.Eventually.of_forall fun t => by
      rw [iter_Δ_pow_zero]; rfl

/-! ### Strict decrease -/

omit [DecidableEq σ] [Fintype ι] in
theorem mem_FLE_totalDegree (hD : ∀ i, 1 ≤ D i) (P : MvPolynomial σ K) :
    P ∈ FLE K β (P.totalDegree • D) := by
  rw [FLE, mem_restrictSupport_iff]
  intro m hm i
  have h1 : bdeg β m i ≤ m.degree := by
    calc bdeg β m i ≤ ∑ s, m s := Finset.sum_le_sum fun s _ => by split_ifs <;> simp
      _ = m.degree := by
        change _ = ∑ s ∈ m.support, m s
        exact (Finset.sum_subset (Finset.subset_univ _)
          (fun s _ hs => Finsupp.notMem_support_iff.mp hs)).symm
  have h2 : m.degree ≤ P.totalDegree := le_totalDegree hm
  simp only [Pi.smul_apply, smul_eq_mul]
  calc bdeg β m i ≤ P.totalDegree := h1.trans h2
    _ ≤ P.totalDegree * D i := Nat.le_mul_of_pos_right _ (hD i)

omit [DecidableEq σ] [Fintype ι] in
/-- **A non-zero-divisor strictly lowers the dimension.** If `P` is a non-zero-divisor modulo the
proper ideal `J` and `J + (P) ≤ L` with `L ≠ ⊤`, then `hdim L < hdim J`. -/
theorem hdim_section_lt [Finite ι] (hD : ∀ i, 1 ≤ D i) {J L : Ideal (MvPolynomial σ K)} {P :
  MvPolynomial σ K}
    (hnzd : ∀ Q, P * Q ∈ J → Q ∈ J) (hL : J ⊔ Ideal.span {P} ≤ L) (hLt : L ≠ ⊤) :
    (hdata β D K L).1 < (hdata β D K J).1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top hLt (le_sup_left.trans hL)
  have hJP : J ⊔ Ideal.span {P} ≠ ⊤ := ne_top_of_le_ne_top hLt hL
  set s := P.totalDegree + 1
  have hP : P ∈ FLE K β (s • D) :=
    FLE_mono K β (fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact Nat.mul_le_mul_right (D i) (Nat.le_succ _))
      (mem_FLE_totalDegree β D K hD P)
  have hsec := hfun_section_s β D K hP hnzd
  -- data of `J + (P)`
  have hJd := hdata_spec β D K hJ
  have hJPd := hdata_spec β D K hJP
  have hcmp := hdata_le_of_le β D K hL hLt
  -- `hdim (J + (P)) < hdim J`
  have key : (hdata β D K (J ⊔ Ideal.span {P})).1 < (hdata β D K J).1 := by
    set aJ := (hdata β D K J).1
    rcases Nat.eq_zero_or_pos aJ with h0 | hpos
    · exfalso
      -- in dimension 0 the section is eventually zero
      obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp (h0 ▸ hJd).2
      have := one_le_hfun β D K hJP (k0 + s)
      have h1 := hsec k0
      have h2 : (hfun β D K J (k0 + s) : ℤ) = (hdata β D K J).2 := hk0 _ (by omega)
      have h3 : (hfun β D K J k0 : ℤ) = (hdata β D K J).2 := hk0 _ (by omega)
      omega
    · obtain ⟨b, hb⟩ : ∃ b, aJ = b + 1 := ⟨aJ - 1, by omega⟩
      have hf : HasData (fun t => (hfun β D K J t : ℤ)) (b + 1) (hdata β D K J).2 := hb ▸ hJd
      let h : ℕ → ℤ := fun k => (hfun β D K J k : ℤ) - hfun β D K J (k - s)
      have hh : HasData h b (s * (hdata β D K J).2) :=
        HasData.of_sub_shift (by omega) hf fun k => by simp [h]
      have hcomp := hJPd.compare hh
        (Filter.eventually_atTop.mpr ⟨s, fun k hk => by
          obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
          have := hsec t
          simp only [h, show s + t - s = t by omega]
          rw [show s + t = t + s by ring]
          exact this⟩)
        (Filter.Eventually.of_forall fun _ => by positivity)
      omega
  rcases hcmp with h | ⟨h, -⟩ <;> omega

omit [DecidableEq σ] [Fintype ι] in
/-- **Strict decrease along prime inclusions.** -/
theorem hdim_lt_of_lt [Finite ι] (hD : ∀ i, 1 ≤ D i) {q q' : Ideal (MvPolynomial σ K)} [hq :
  q.IsPrime]
    (hq' : q' ≠ ⊤) (hlt : q < q') : (hdata β D K q').1 < (hdata β D K q).1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨f, hf', hf⟩ := IsConcreteLE.exists_of_lt hlt
  refine hdim_section_lt β D K hD (P := f) (fun Q hQ => ?_) (sup_le hlt.le ?_) hq'
  · exact (hq.mem_or_mem hQ).resolve_left hf
  · rw [Ideal.span_le]; simpa using hf'

end StrongSix.M2

end LeanPool
