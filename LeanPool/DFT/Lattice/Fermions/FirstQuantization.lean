/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Fermions.SecondQuantization

/-!
# Powers of the many-body Hamiltonian via first quantisation

* `H1 h`: first-quantised one-body operator on functions of position tuples; `H1_conf` (it acts as
  `Γ h`).
* `gamma_pow_apply`, `H1_iter_prod` (word expansion on product states),
* `gamma_pow_formula`: `(Γ h ^ k)_{s c} = Σ_σ sign σ Σ_ι Π_l (h ^ cnt ι l)_{s_l, c_{σ⁻¹ l}}`.
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-- First-quantised one-body operator. -/
def H1 (h : Matrix (Fin M) (Fin M) ℝ) (f : (Fin N → Fin M) → ℝ) : (Fin N → Fin M) → ℝ :=
  fun τ => ∑ i, ∑ b, h (τ i) b * f (Function.update τ i b)

/-- A wavefunction transforms by the sign of each permutation of particle labels. -/
def Antisym (f : (Fin N → Fin M) → ℝ) : Prop :=
  ∀ (τ : Fin N → Fin M) (σ : Equiv.Perm (Fin N)), f (fun k => τ (σ k)) =
      (Equiv.Perm.sign σ : ℝ) * f τ

lemma antisym_zero_of_not_injective {f : (Fin N → Fin M) → ℝ} (hf : Antisym f) {τ : Fin N → Fin M}
    (h : ¬ Function.Injective τ) : f τ = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨a, b, hab, hne⟩ := h
  have hsw := hf τ (Equiv.swap a b)
  have : (fun k => τ (Equiv.swap a b k)) = τ := by
    funext k
    by_cases hka : k = a
    · subst hka; simp [Equiv.swap_apply_left, hab]
    · by_cases hkb : k = b
      · subst hkb; simp [Equiv.swap_apply_right, hab]
      · simp [Equiv.swap_apply_of_ne_of_ne hka hkb]
  rw [this, Equiv.Perm.sign_swap hne] at hsw
  simp at hsw
  linarith

lemma antisym_expand {f : (Fin N → Fin M) → ℝ} (hf : Antisym f) (τ : Fin N → Fin M) :
    f τ = ∑ s : Conf M N, amp s τ * f (τs s) := by
  by_cases hinj : Function.Injective τ
  · set S := Finset.univ.image τ
    have hS : S.card = N := by rw [Finset.card_image_of_injective _ hinj]; simp
    set s0 : Conf M N := ⟨S, hS⟩
    have hmem : ∀ k, τ k ∈ s0.1 := fun k => Finset.mem_image_of_mem τ (Finset.mem_univ k)
    obtain ⟨σ, hσ⟩ := exists_perm_of_injective s0 hinj hmem
    have hτ : τ = fun k => τs s0 (σ k) := funext hσ
    rw [Finset.sum_eq_single s0]
    · rw [hτ, hf, amp, slater_perm]
      have := amp_self s0
      unfold amp at this
      rw [this]; ring
    · intro s _ hs
      have : ∃ k, τ k ∉ s.1 := by
        by_contra hall
        push Not at hall
        apply hs
        apply Subtype.ext
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
          exact hall k
        · rw [s.2, hS]
      obtain ⟨k, hk⟩ := this
      rw [amp_of_not_mem s hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ s0) h
  · rw [antisym_zero_of_not_injective hf hinj]
    symm
    apply Finset.sum_eq_zero
    intro s _
    rw [amp, slater_of_not_injective _ hinj, zero_mul]

lemma amp_antisym (c : Conf M N) : Antisym (fun τ => amp c τ) := fun τ σ => by
  simp only [amp]; exact slater_perm _ τ σ

lemma H1_antisym (h : Matrix (Fin M) (Fin M) ℝ) {f : (Fin N → Fin M) → ℝ} (hf : Antisym f) :
    Antisym (H1 h f) := by
  intro τ σ
  simp only [H1]
  rw [Finset.mul_sum, ← Equiv.sum_comp σ.symm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  have hupd : Function.update (fun k => τ (σ k)) (σ.symm i) b =
      fun k => Function.update τ i b (σ k) := by
    funext k
    by_cases hk : k = σ.symm i
    · subst hk; simp
    · have : σ k ≠ i := by intro h'; apply hk; rw [← h']; simp
      simp [Function.update_of_ne hk, Function.update_of_ne this]
  simp only [Equiv.apply_symm_apply]
  rw [hupd, hf]; ring

lemma H1_conf (h : Matrix (Fin M) (Fin M) ℝ) {f : (Fin N → Fin M) → ℝ} (hf : Antisym f)
    (s : Conf M N) :
    H1 h f (τs s) = ((Γ h : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ (fun s' => f (τs s'))) s := by
  simp only [H1, Matrix.mulVec, dotProduct, Γ]
  have e : ∀ k b, h (τs s k) b * f (Function.update (τs s) k b) =
      ∑ s', h (τs s k) b * amp s' (Function.update (τs s) k b) * f (τs s') := by
    intro k b
    rw [antisym_expand hf (Function.update (τs s) k b), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s' _; ring
  simp_rw [e, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

theorem gamma_pow_apply (h : Matrix (Fin M) (Fin M) ℝ) (c : Conf M N) (k : ℕ) (s : Conf M N) :
    ((Γ h : Matrix (Conf M N) (Conf M N) ℝ) ^ k) s c = (H1 h)^[k] (fun τ => amp c τ) (τs s) := by
  induction k generalizing s with
  | zero =>
    simp only [pow_zero, Function.iterate_zero, id, Matrix.one_apply, amp_tau_eq]
  | succ k ih =>
    have hanti : Antisym ((H1 h)^[k] (fun τ => amp c τ)) := by
      clear ih
      induction k with
      | zero => exact amp_antisym c
      | succ k ihk => rw [Function.iterate_succ_apply']; exact H1_antisym h ihk
    rw [pow_succ', Matrix.mul_apply, Function.iterate_succ_apply', H1_conf h hanti]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl; intro s' _
    rw [ih]

/-- Product function. -/
def prodFun (g : Fin N → Fin M → ℝ) : (Fin N → Fin M) → ℝ := fun τ => ∏ l, g l (τ l)

/-- Number of times particle `l` occurs in a word. -/
def cnt {k : ℕ} (ι : Fin k → Fin N) (l : Fin N) : ℕ := (Finset.univ.filter (fun j => ι j = l)).card

lemma H1_sum (h : Matrix (Fin M) (Fin M) ℝ) {α : Type*} (S : Finset α)
    (F : α → (Fin N → Fin M) → ℝ) :
    H1 h (fun τ => ∑ a ∈ S, F a τ) = fun τ => ∑ a ∈ S, H1 h (F a) τ := by
  funext τ
  simp only [H1]
  have e : ∀ i b, h (τ i) b * ∑ a ∈ S, F a (Function.update τ i b) =
      ∑ a ∈ S, h (τ i) b * F a (Function.update τ i b) := fun i b => Finset.mul_sum _ _ _
  simp_rw [e]
  conv_lhs => rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

lemma H1_prodFun (h : Matrix (Fin M) (Fin M) ℝ) (g : Fin N → Fin M → ℝ) :
    H1 h (prodFun g) = fun τ => ∑ i, prodFun (Function.update g i (h *ᵥ g i)) τ := by
  funext τ
  simp only [H1, prodFun]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest : ∀ b, ∏ l, g l (Function.update τ i b l) =
      g i b * ∏ l ∈ Finset.univ.erase i, g l (τ l) := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.prod_congr rfl; intro l hl
      simp [Function.update_of_ne (Finset.mem_erase.mp hl).1]
  simp_rw [hrest]
  have : ∏ l ∈ Finset.univ.erase i, Function.update g i (h *ᵥ g i) l (τ l) =
      ∏ l ∈ Finset.univ.erase i, g l (τ l) := by
    apply Finset.prod_congr rfl; intro l hl
    simp [Function.update_of_ne (Finset.mem_erase.mp hl).1]
  rw [this]
  simp only [Function.update_self, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro b _
  ring

lemma cnt_snoc {k : ℕ} (ι : Fin k → Fin N) (i l : Fin N) :
    cnt (Fin.snoc ι i : Fin (k + 1) → Fin N) l = cnt ι l + if i = l then 1 else 0 := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- **Word expansion** of `H1ᵏ` on product functions. -/
theorem H1_iter_prod (h : Matrix (Fin M) (Fin M) ℝ) (g : Fin N → Fin M → ℝ) (k : ℕ) :
    (H1 h)^[k] (prodFun g) =
      fun τ => ∑ ι : Fin k → Fin N, prodFun (fun l => (h ^ cnt ι l) *ᵥ g l) τ := by
  induction k with
  | zero =>
    funext τ
    simp [prodFun, cnt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, H1_sum]
    funext τ
    simp_rw [H1_prodFun]
    rw [← (Fin.snocEquiv (fun _ => Fin N)).sum_comp, Fintype.sum_prod_type]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro w _
    simp only [Fin.snocEquiv_apply, prodFun]
    apply Finset.prod_congr rfl; intro l _
    rw [cnt_snoc]
    by_cases hl : l = x
    · subst hl; simp [pow_succ', Matrix.mulVec_mulVec]
    · simp [Function.update_of_ne hl, Ne.symm hl]

lemma H1_smul (h : Matrix (Fin M) (Fin M) ℝ) (a : ℝ) (f : (Fin N → Fin M) → ℝ) :
    H1 h (fun τ => a * f τ) = fun τ => a * H1 h f τ := by
  funext τ; simp only [H1, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro b _; ring

lemma H1_iter_lin (h : Matrix (Fin M) (Fin M) ℝ) {α : Type*} (S : Finset α) (a : α → ℝ)
    (F : α → (Fin N → Fin M) → ℝ) (k : ℕ) :
    (H1 h)^[k] (fun τ => ∑ x ∈ S, a x * F x τ) = fun τ => ∑ x ∈ S, a x * (H1 h)^[k] (F x) τ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, H1_sum]
    funext τ
    apply Finset.sum_congr rfl; intro x _
    rw [H1_smul, Function.iterate_succ_apply']

lemma amp_as_prod (c : Conf M N) (τ : Fin N → Fin M) :
    amp c τ = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℝ) *
      prodFun (fun l x => if x = τs c (σ.symm l) then (1 : ℝ) else 0) τ := by
  rw [amp, slater_eq_sum]
  apply Finset.sum_congr rfl; intro σ _
  congr 1
  simp only [prodFun]
  rw [← Equiv.prod_comp σ (fun l => if τ l = τs c (σ.symm l) then (1 : ℝ) else 0)]
  simp

/-- **Many-body powers as signed sums of products of single-particle powers.** -/
theorem gamma_pow_formula (h : Matrix (Fin M) (Fin M) ℝ) (s c : Conf M N) (k : ℕ) :
    ((Γ h : Matrix (Conf M N) (Conf M N) ℝ) ^ k) s c =
      ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℝ) *
        ∑ ι : Fin k → Fin N, ∏ l, (h ^ cnt ι l) (τs s l) (τs c (σ.symm l)) := by
  rw [gamma_pow_apply]
  have hamp : (fun τ => amp c τ) = fun τ => ∑ σ ∈ Finset.univ, (Equiv.Perm.sign σ : ℝ) *
      prodFun (fun l x => if x = τs c (σ.symm l) then (1 : ℝ) else 0) τ := by
    funext τ; exact amp_as_prod c τ
  rw [hamp, H1_iter_lin]
  apply Finset.sum_congr rfl; intro σ _
  congr 1
  rw [H1_iter_prod]
  apply Finset.sum_congr rfl; intro ι _
  simp only [prodFun]
  apply Finset.prod_congr rfl; intro l _
  simp [Matrix.mulVec, dotProduct]

end

end DFT
