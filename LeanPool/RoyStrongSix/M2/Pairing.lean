/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Deriv
public import LeanPool.RoyStrongSix.M2.Wustholz

/-!
# Dual families of derivations and equations (Roy Lemmas 8.13–8.15)

For `G′ = V × T_Λ`, write `Te = V × Λ^⊥` (`Λ^⊥ = torusLie K (qspan Λ)`), and `ℓ = dim W − dim (W ∩
Te)`.

* `gensN V Λ`: the span of the linear forms vanishing on `V` and of the `Y^λ − 1`, `λ ∈ Λ`. Every
  `D_w P` with `P ∈ gensN` is constant on `G′` (`gensN_const`).
* `exists_biorth`: Gram–Schmidt for a bilinear pairing `φ`, giving `ℓ_φ = dim W − dim (W ∩ ker φ)`
  pairs with `φ(wᵢ, cⱼ) = δᵢⱼ`.
* **`lemma814`** (Roy 8.14): `w₁..w_ℓ ∈ W`, `P₁..P_ℓ ∈ I(G′)` with `D_{wᵢ} Pⱼ ≡ δᵢⱼ` on `G′`.
* **`lemma815`** (Roy 8.15): the same modulo `I(E)` for a finite union `E` of distinct cosets of
`G′`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

/-! ### Gram–Schmidt for a pairing -/

section Biorth

variable {K : Type*} [Field K] {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N]

theorem exists_biorth (φ : M →ₗ[K] N →ₗ[K] K) (W : Submodule K M) [FiniteDimensional K W] :
    ∀ n ≤ finrank K W - finrank K ↥(W ⊓ LinearMap.ker φ), ∃ (w : Fin n → M) (c : Fin n → N),
      (∀ i, w i ∈ W) ∧ ∀ i j, φ (w i) (c j) = if i = j then 1 else 0 := by
  intro n
  induction n with
  | zero => intro _; exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro hn
    obtain ⟨w, c, hwW, hwc⟩ := ih (by omega)
    have hex : ∃ w' ∈ W, φ w' ∉ Submodule.span K (Set.range (φ ∘ w)) := by
      by_contra hcon
      push Not at hcon
      have h1 : W.map φ ≤ Submodule.span K (Set.range (φ ∘ w)) := by
        rintro _ ⟨x, hx, rfl⟩; exact hcon x hx
      have h2 : finrank K (W.map φ) ≤ n := by
        have : FiniteDimensional K (Submodule.span K (Set.range (φ ∘ w))) :=
          FiniteDimensional.span_of_finite K (Set.finite_range _)
        calc finrank K (W.map φ) ≤ finrank K (Submodule.span K (Set.range (φ ∘ w))) :=
              Submodule.finrank_mono h1
          _ ≤ Fintype.card (Fin n) := finrank_range_le_card _
          _ = n := Fintype.card_fin n
      have h3 := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict W)
      rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, finrank_comap_subtype] at h3
      omega
    obtain ⟨w', hw'W, hw'⟩ := hex
    let w'' := w' - ∑ i, φ w' (c i) • w i
    have hw''W : w'' ∈ W := W.sub_mem hw'W (W.sum_mem fun i _ => W.smul_mem _ (hwW i))
    have hw''c : ∀ j, φ w'' (c j) = 0 := by
      intro j
      simp only [w'', map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, hwc, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]
    have hw''ne : φ w'' ≠ 0 := by
      intro h
      apply hw'
      have : φ w' = ∑ i, φ w' (c i) • φ (w i) := by
        have : φ w'' = φ w' - ∑ i, φ w' (c i) • φ (w i) := by
          simp only [w'', map_sub, map_sum, map_smul]
        rw [h] at this
        exact (sub_eq_zero.mp this.symm)
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c', hc'⟩ : ∃ c', φ w'' c' ≠ 0 := by
      by_contra h; push Not at h; exact hw''ne (LinearMap.ext h)
    let c1 := (φ w'' c')⁻¹ • c'
    have hc1 : φ w'' c1 = 1 := by simp only [c1, map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hc'
    let c'' := c1 - ∑ j, φ (w j) c1 • c j
    have hlast : φ w'' c'' = 1 := by
      simp only [c'', map_sub, map_sum, map_smul, hc1, hw''c, smul_zero, Finset.sum_const_zero,
        sub_zero]
    have hlast' : ∀ i, φ (w i) c'' = 0 := by
      intro i
      simp only [c'', map_sub, map_sum, map_smul, hwc, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_self]
    refine ⟨Fin.snoc w w'', Fin.snoc c c'', fun i => ?_, fun i j => ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hw''W
      · simpa using hwW i
    · refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hlast
      · simp [hw''c, (Fin.castSucc_lt_last j).ne']
      · simp [hlast' i, (Fin.castSucc_lt_last i).ne]
      · simp [hwc, Fin.castSucc_inj]

end Biorth

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K

/-! ### `D_w` is linear in `w` -/

omit [CharZero K] in
theorem Dw_add_apply (w w' : LieG K d0 d1) (P : B) : Dw (w + w') P = Dw w P + Dw w' P := by
  simp only [Dw_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

omit [CharZero K] in
theorem Dw_smul_apply (c : K) (w : LieG K d0 d1) (P : B) : Dw (c • w) P = c • Dw w P := by
  simp only [Dw_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
    smul_add, Finset.smul_sum]

/-! ### Derivatives of characters and linear forms -/

theorem derivation_pow_of_eigen {R : Type*} [CommRing R] [Algebra K R] (D : Derivation K R R)
    {x : R} {c : K} (hx : D x = c • x) (n : ℕ) : D (x ^ n) = ((n : K) * c) • x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Derivation.leibniz, ih, hx, smul_eq_mul, smul_eq_mul, Nat.cast_succ]
    simp only [Algebra.smul_def, map_mul, map_add, map_one]
    ring

omit [CharZero K] in
theorem derivation_prod_of_eigen {R : Type*} [CommRing R] [Algebra K R] (D : Derivation K R R)
    {ι : Type*} (s : Finset ι) (f : ι → R) (c : ι → K) (hf : ∀ i ∈ s, D (f i) = c i • f i) :
    D (∏ i ∈ s, f i) = (∑ i ∈ s, c i) • ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi), hf a (Finset.mem_insert_self _ _)]
    simp only [smul_eq_mul, Algebra.smul_def, map_add]
    ring

/-- `D_w(Y^λ) = ⟨λ, η⟩ Y^λ`. -/
theorem Dw_monoChr (w : LieG K d0 d1) (l : Fin d1 → ℤ) :
    Dw w (monoChr l) = (∑ j, (l j : K) * w.2 j) • monoChr l := by
  rw [monoChr]
  apply derivation_prod_of_eigen
  intro j _
  split_ifs with h
  · rw [derivation_pow_of_eigen _ (Dw_Y w j)]
    congr 2
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
  · rw [derivation_pow_of_eigen _ (c := -w.2 j) (by rw [Dw_Z, neg_smul])]
    congr 1
    rw [mul_neg, ← neg_mul, ← Int.cast_natCast, ← Int.cast_neg, Int.toNat_of_nonneg (by omega),
      neg_neg]

/-- The linear form `μ(X)`. -/
noncomputable def linF (μ : Module.Dual K (Fin d0 → K)) : B :=
  ∑ k, C (μ (Pi.single k 1)) * X (Sum.inl k)

omit [CharZero K] in
theorem eval_linF (μ : Module.Dual K (Fin d0 → K)) (h : GPt K d0 d1) :
    eval (pt h) (linF μ) = μ h.1 := by
  simp only [linF, map_sum, map_mul, eval_C, eval_X, pt, Sum.elim_inl]
  rw [LinearMap.pi_apply_eq_sum_univ μ h.1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  funext i; simp [Pi.single_apply, eq_comm]

omit [CharZero K] in
theorem Dw_linF (w : LieG K d0 d1) (μ : Module.Dual K (Fin d0 → K)) :
    Dw w (linF μ) = C (μ w.1) := by
  rw [linF, map_sum]
  simp only [Derivation.leibniz, Dw_X, Dw_C, smul_eq_mul, mul_zero, add_zero]
  rw [LinearMap.pi_apply_eq_sum_univ μ w.1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, mul_comm, map_mul]
  congr 3
  funext i; simp [Pi.single_apply, eq_comm]

/-! ### The generating space `E` of `I(G′)` -/

/-- Roy's space `E = ⟨L₁..L_r, Y^{λ₁} − 1, …⟩`. -/
noncomputable def gensN (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    Submodule K B :=
  Submodule.span K ({P | ∃ μ : Module.Dual K (Fin d0 → K), (∀ v ∈ V, μ v = 0) ∧ P = linF μ} ∪
    {P | ∃ l ∈ Λ, P = monoChr l - 1})

omit [CharZero K] in
theorem gensN_le (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    gensN V Λ ≤ (vanish (prodSet V Λ)).restrictScalars K := by
  rw [gensN, Submodule.span_le]
  rintro P (⟨μ, hμ, rfl⟩ | ⟨l, hl, rfl⟩) g hg
  · rw [eval_linF]; exact hμ _ hg.1
  · simp [eval_monoChr, hg.2 l hl]

/-- `D_w P` is constant on `G′` for `P ∈ E`. -/
theorem gensN_const (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ))
    (w : LieG K d0 d1) {P : B} (hP : P ∈ gensN V Λ) {g : GPt K d0 d1} (hg : g ∈ prodSet V Λ) :
    eval (pt g) (Dw w P) = eval (pt GPt.zero) (Dw w P) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, _, rfl⟩ | ⟨l, hl, rfl⟩
    · simp [Dw_linF]
    · rw [map_sub, Derivation.map_one_eq_zero, sub_zero, Dw_monoChr]
      simp only [smul_eq_C_mul, map_mul, eval_C, eval_monoChr, hg.2 l hl]
      simp [GPt.zero, chr]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => rw [Derivation.map_smul, smul_eq_C_mul, map_mul, map_mul, hx, eval_C, eval_C]

/-- The pairing `b(w, P) = (D_w P)(e)` on `K^d × E`. -/
noncomputable def pairing (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    LieG K d0 d1 →ₗ[K] gensN V Λ →ₗ[K] K :=
  LinearMap.mk₂ K (fun w P => eval (pt GPt.zero) (Dw w (P : B)))
    (fun w w' P => by simp [Dw_add_apply])
    (fun c w P => by simp [Dw_smul_apply])
    (fun w P P' => by simp)
    (fun c w P => by simp)

theorem mem_torusLie_qspan {Λ : AddSubgroup (Fin d1 → ℤ)} {η : Fin d1 → K}
    (h : ∀ l ∈ Λ, ∑ j, (l j : K) * η j = 0) : η ∈ torusLie K (qspan Λ) := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    simpa using h l hl
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, Rat.cast_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul a x _ hx =>
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]

/-- The left kernel of the pairing lies in `Te = V × Λ^⊥` (Roy Lemma 8.13). -/
theorem ker_pairing_le (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    LinearMap.ker (pairing V Λ) ≤ V.prod (torusLie K (qspan Λ)) := by
  intro w hw
  have hw' : ∀ P (hP : P ∈ gensN V Λ), eval (pt GPt.zero) (Dw w P) = 0 := fun P hP =>
    LinearMap.congr_fun (LinearMap.mem_ker.mp hw) ⟨P, hP⟩
  refine ⟨?_, ?_⟩
  · by_contra hx
    obtain ⟨μ, hμ, hVμ⟩ := Submodule.exists_le_ker_of_notMem hx
    have := hw' (linF μ) (Submodule.subset_span (Or.inl ⟨μ, fun v hv => hVμ hv, rfl⟩))
    rw [Dw_linF, eval_C] at this
    exact hμ this
  · apply mem_torusLie_qspan
    intro l hl
    have := hw' (monoChr l - 1) (Submodule.subset_span (Or.inr ⟨l, hl, rfl⟩))
    rw [map_sub, Derivation.map_one_eq_zero, sub_zero, Dw_monoChr, smul_eq_C_mul, map_mul, eval_C,
      eval_monoChr] at this
    simpa [GPt.zero, chr] using this

/-- **Roy Lemma 8.14.** -/
theorem lemma814 (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ))
    (W : Submodule K (LieG K d0 d1)) :
    ∃ (w : Fin (finrank K W - finrank K ↥(W ⊓ V.prod (torusLie K (qspan Λ)))) → LieG K d0 d1)
      (P : Fin (finrank K W - finrank K ↥(W ⊓ V.prod (torusLie K (qspan Λ)))) → B),
      (∀ i, w i ∈ W) ∧ (∀ j, P j ∈ gensN V Λ) ∧
      ∀ i j, eval (pt GPt.zero) (Dw (w i) (P j)) = if i = j then 1 else 0 := by
  have hle : finrank K W - finrank K ↥(W ⊓ V.prod (torusLie K (qspan Λ))) ≤
      finrank K W - finrank K ↥(W ⊓ LinearMap.ker (pairing V Λ)) := by
    have : finrank K ↥(W ⊓ LinearMap.ker (pairing V Λ)) ≤
        finrank K ↥(W ⊓ V.prod (torusLie K (qspan Λ))) :=
      Submodule.finrank_mono (inf_le_inf_left _ (ker_pairing_le V Λ))
    omega
  obtain ⟨w, c, hwW, hwc⟩ := exists_biorth (pairing V Λ) W _ hle
  exact ⟨w, fun j => c j, hwW, fun j => (c j).2, hwc⟩

/-! ### Finite unions of cosets (Roy Lemma 8.15) -/

/-- **Roy Lemma 8.15.** -/
theorem lemma815 (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ))
    (W : Submodule K (LieG K d0 d1)) (R : Finset (GPt K d0 d1))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → gmul (ginv b) a ∉ prodSet V Λ) :
    ∃ (w : Fin (finrank K W - finrank K ↥(W ⊓ V.prod (torusLie K (qspan Λ)))) → LieG K d0 d1)
      (Q : Fin (finrank K W - finrank K ↥(W ⊓ V.prod (torusLie K (qspan Λ)))) → B),
      (∀ i, w i ∈ W) ∧ (∀ j, Q j ∈ vanish (⋃ a ∈ R, gtransl a (prodSet V Λ))) ∧
      ∀ i j, Dw (w i) (Q j) - (if i = j then 1 else 0) ∈
        vanish (⋃ a ∈ R, gtransl a (prodSet V Λ)) := by
  classical
  obtain ⟨w, P, hwW, hPN, hwP⟩ := lemma814 V Λ W
  set G' := prodSet V Λ
  -- separating polynomials
  have hsep : ∀ a b : GPt K d0 d1, ∃ A : B, a ∈ R → b ∈ R → a ≠ b →
      A ∈ vanish G' ∧ ∀ g ∈ G', eval (pt (gmul (gmul (ginv b) a) g)) A = 1 := by
    intro a b
    by_cases h : a ∈ R ∧ b ∈ R ∧ a ≠ b
    · obtain ⟨A, hA1, hA2⟩ := exists_sep V Λ _ (hdist a h.1 b h.2.1 h.2.2)
      exact ⟨A, fun _ _ _ => ⟨hA1, hA2⟩⟩
    · exact ⟨0, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose Asep hAsep using hsep
  let Bk : GPt K d0 d1 → B := fun k => ∏ b ∈ R.erase k, transl (ginv b) (Asep k b)
  -- values of `Bk` on the cosets
  have hB1 : ∀ k ∈ R, ∀ g ∈ G', eval (pt (gmul k g)) (Bk k) = 1 := by
    intro k hk g hg
    simp only [Bk, map_prod, eval_transl]
    refine Finset.prod_eq_one fun b hb => ?_
    have hbR := Finset.mem_of_mem_erase hb
    have hbk := Finset.ne_of_mem_erase hb
    rw [← gmul_assoc]
    exact (hAsep k b hk hbR (Ne.symm hbk)).2 g hg
  have hB0 : ∀ k ∈ R, ∀ m ∈ R, k ≠ m → ∀ g ∈ G', eval (pt (gmul m g)) (Bk k) = 0 := by
    intro k hk m hm hkm g hg
    simp only [Bk, map_prod, eval_transl]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hkm, hm⟩) ?_
    rw [← gmul_assoc, gmul_ginv, gzero_gmul]
    exact (hAsep k m hk hm hkm).1 g hg
  let Q : Fin (finrank K W - finrank K ↥(W ⊓ V.prod (torusLie K (qspan Λ)))) → B :=
    fun j => ∑ k ∈ R, Bk k * (Bk k * transl (ginv k) (P j))
  have hPG : ∀ j, ∀ g ∈ G', eval (pt g) (P j) = 0 := fun j g hg => gensN_le V Λ (hPN j) g hg
  have hinv : ∀ m g : GPt K d0 d1, gmul (ginv m) (gmul m g) = g := fun m g => by
    rw [← gmul_assoc, gmul_ginv, gzero_gmul]
  -- points of `E`
  have hE : ∀ h ∈ ⋃ a ∈ R, gtransl a G', ∃ m ∈ R, ∃ g ∈ G', h = gmul m g := by
    intro h hh
    simp only [Set.mem_iUnion] at hh
    obtain ⟨m, hm, g, hg, rfl⟩ := hh
    exact ⟨m, hm, g, hg, rfl⟩
  refine ⟨w, Q, hwW, fun j h hh => ?_, fun i j h hh => ?_⟩
  · obtain ⟨m, hm, g, hg, rfl⟩ := hE h hh
    simp only [Q, map_sum, map_mul]
    refine Finset.sum_eq_zero fun k hk => ?_
    by_cases hkm : k = m
    · subst hkm; rw [eval_transl, hinv, hPG j g hg, mul_zero, mul_zero]
    · rw [hB0 k hk m hm hkm g hg, zero_mul]
  · obtain ⟨m, hm, g, hg, rfl⟩ := hE h hh
    simp only [Q, map_sum, Derivation.leibniz, smul_eq_mul, map_sub, map_add, map_mul]
    rw [Finset.sum_eq_single m]
    · rw [hB1 m hm g hg, Dw_transl, eval_transl, eval_transl, hinv, hPG j g hg,
        gensN_const V Λ (w i) (hPN j) hg, hwP i j]
      split_ifs <;> simp
    · intro k hk hkm
      rw [hB0 k hk m hm hkm g hg]
      ring
    · intro hm'; exact absurd hm hm'

omit [CharZero K] in
/-- Every polynomial has some block degree `≤ c • D`. -/
theorem exists_c0 {D : Fin 2 → ℕ} (hD : ∀ i, 1 ≤ D i) {ℓ : ℕ} (Q : Fin ℓ → B) :
    ∃ c0 : ℕ, ∀ j, Q j ∈ FLE K blk (c0 • D) := by
  refine ⟨∑ j, (Q j).totalDegree, fun j => ?_⟩
  refine FLE_mono K blk ?_ (mem_FLE_totalDegree blk D K hD (Q j))
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Nat.mul_le_mul_right _
    (Finset.single_le_sum (f := fun j => (Q j).totalDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j))

end StrongSix.M2

end LeanPool
