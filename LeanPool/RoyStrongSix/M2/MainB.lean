/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Bezout
public import LeanPool.RoyStrongSix.M2.Chain

/-!
# The multiplicity estimate in `K[X, Y, Z]` (Roy §8.4.1)

**`multEstB`**: Philippon's multiplicity estimate for `G = G_a^{d₀} × G_m^{d₁}` over an
algebraically
closed field of characteristic `0`, in the ideal-theoretic language of `M2`.

Proof (Roy §8.4.1):
* the chain `L_r` and the pigeonhole (`exists_flat`);
* a prime `p ⊇ L_{r+1}` with `hdim p = hdim L_r`, `V = Z(p)`, the stabilizer `G_V = V₀ × T_{Λ₀}`
  (`component`, `classify`), and `G⁰ = V₀ × T_{lsat(qspan Λ₀)}`;
* `A = I_G + (τ_v Q : Q ∈ gens L_r, v ∈ V)`, which vanishes to order `> T` along `W` on `S·G_V`
  (`VO`);
* `bezout` (`deg A ≤ deg I_G`), `wustholz` with `lemma815`, `hfun_cosets_ge`, `hdata_prodSet`,
  `hdata_IG`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K

/-! ### Cosets -/

theorem prodSet_isSubgroup (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    IsSubgroupG (prodSet V Λ) where
  one_mem := zero_mem_prodSet V Λ
  mul_mem g hg h hh := ⟨V.add_mem hg.1 hh.1, fun l hl => by
    simp only [gmul]; rw [chr_mul, hg.2 l hl, hh.2 l hl, one_mul]⟩
  inv_mem g hg := ⟨V.neg_mem hg.1, fun l hl => by
    simp only [ginv]; rw [chr_inv, hg.2 l hl, inv_one]⟩

theorem gtransl_gtransl (a b : GPt K d0 d1) (E : Set (GPt K d0 d1)) :
    gtransl a (gtransl b E) = gtransl (gmul a b) E := by
  simp only [gtransl, Set.image_image]
  congr 1
  funext x
  rw [gmul_assoc]

theorem gtransl_self {H : Set (GPt K d0 d1)} (hH : IsSubgroupG H) {c : GPt K d0 d1} (hc : c ∈ H) :
    gtransl c H = H := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩; exact hH.mul_mem c hc h hh
  · intro h hh
    exact ⟨gmul (ginv c) h, hH.mul_mem _ (hH.inv_mem c hc) h hh, gmul_ginv_cancel c h⟩

theorem gtransl_eq_of_mem {H : Set (GPt K d0 d1)} (hH : IsSubgroupG H) {a b : GPt K d0 d1}
    (h : gmul (ginv b) a ∈ H) : gtransl a H = gtransl b H := by
  rw [← gmul_ginv_cancel b a, ← gtransl_gtransl, gtransl_self hH h]

theorem ginv_gmul_ginv (a t : GPt K d0 d1) : ginv (gmul (ginv t) a) = gmul (ginv a) t := by
  refine Prod.ext ?_ ?_
  · simp only [ginv, gmul]; abel
  · simp only [ginv, gmul, mul_inv, inv_inv, mul_comm]

/-- Distinct coset representatives. -/
theorem exists_reps {H : Set (GPt K d0 d1)} (hH : IsSubgroupG H) (T' : Finset (GPt K d0 d1)) :
    ∃ Rs ⊆ T', (⋃ a ∈ Rs, gtransl a H) = (⋃ a ∈ T', gtransl a H) ∧
      ∀ a ∈ Rs, ∀ b ∈ Rs, a ≠ b → gmul (ginv b) a ∉ H := by
  classical
  induction T' using Finset.induction_on with
  | empty => exact ⟨∅, subset_refl _, by simp, by simp⟩
  | insert t T' ht ih =>
    obtain ⟨Rs, hsub, hU, hd⟩ := ih
    by_cases hc : ∃ a ∈ Rs, gmul (ginv a) t ∈ H
    · obtain ⟨a, ha, hat⟩ := hc
      refine ⟨Rs, hsub.trans (Finset.subset_insert _ _), ?_, hd⟩
      rw [Finset.set_biUnion_insert, ← hU, gtransl_eq_of_mem hH hat]
      exact (Set.union_eq_right.mpr
        (Set.subset_iUnion₂ (s := fun a (_ : a ∈ Rs) => gtransl a H) a ha)).symm
    · push Not at hc
      refine ⟨insert t Rs, Finset.insert_subset_insert _ hsub, ?_, ?_⟩
      · rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert, hU]
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · exact absurd rfl hab
          · exact hc b hb'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · intro hmem
            apply hc a ha'
            have := hH.inv_mem _ hmem
            rwa [ginv_gmul_ginv] at this
          · exact hd a ha' b hb' hab

theorem qspan_lsat (Λ : AddSubgroup (Fin d1 → ℤ)) : qspan (lsat (qspan Λ)) = qspan Λ := by
  apply le_antisymm
  · rw [qspan, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hl
  · exact Submodule.span_mono (Set.image_mono (le_lsat_qspan Λ))

theorem equivMod_of_cosets {V0 : Submodule K (Fin d0 → K)} {U : Submodule ℚ (Fin d1 → ℚ)}
    {a u u' f f' : GPt K d0 d1} (hu : u ∈ prodSet V0 (lsat U)) (hu' : u' ∈ prodSet V0 (lsat U))
    (hf : gmul a u = f) (hf' : gmul a u' = f') : EquivMod V0 U f f' := by
  subst hf hf'
  refine ⟨?_, fun φ hφ => ?_⟩
  · simp only [gmul]
    rw [add_sub_add_left_eq_sub]
    exact V0.sub_mem hu.1 hu'.1
  · have h1 := hu.2 φ hφ
    have h2 := hu'.2 φ hφ
    rw [chr_eq_units] at h1 h2
    have h1' : ∏ j, u.2 j ^ φ j = 1 := Units.ext (by simpa using h1)
    have h2' : ∏ j, u'.2 j ^ φ j = 1 := Units.ext (by simpa using h2)
    have e : ∀ j, (gmul a u).2 j / (gmul a u').2 j = u.2 j / u'.2 j := fun j => by
      simp only [gmul, Pi.mul_apply]; exact mul_div_mul_left_eq_div _ _ _
    simp only [e, div_zpow, Finset.prod_div_distrib, h1', h2', div_one]

/-! ### Comparison of degrees -/

theorem HasData.addShift {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c) (e : ℕ) :
    HasData (fun k => f (k + e)) a c := by
  induction e with
  | zero => simpa using h
  | succ e ih =>
    refine hasData_congr ih.shift (Filter.Eventually.of_forall fun k => ?_)
    change f (k + 1 + e) = f (k + (e + 1))
    congr 1
    omega

variable (D : Fin 2 → ℕ)

theorem deg_le_of_hfun {J A : Ideal B} (hJ : J ≠ ⊤) (hA : A ≠ ⊤)
    (hdimEq : (hdata blk D K A).1 = (hdata blk D K J).1) {κ c : ℕ} (hκ : 1 ≤ κ)
    (h : ∀ t, κ * hfun blk D K J t ≤ hfun blk D K A (t + c)) :
    (κ : ℤ) * (hdata blk D K J).2 ≤ (hdata blk D K A).2 := by
  have hf := (hdata_spec blk D K hJ).smul (κ := (κ : ℤ)) (by exact_mod_cast (by omega : κ ≠ 0))
  have hg := (hdata_spec blk D K hA).addShift c
  rcases hf.compare hg (Filter.Eventually.of_forall fun t => by exact_mod_cast h t)
      (Filter.Eventually.of_forall fun _ => by positivity) with h1 | ⟨-, h2⟩
  · omega
  · exact h2

/-! ### Arithmetic -/

/-- The constant of the multiplicity estimate. -/
def Cst (d0 d1 : ℕ) : ℕ :=
  (d0 + d1) ^ (d0 + d1) * d0 ^ d0 * d1 ^ d1 * (d0 + d1).factorial * 2 ^ d1

theorem pow_self_le_pow_self {a b : ℕ} (h : a ≤ b) : a ^ a ≤ b ^ b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact Nat.one_le_pow _ _ hb
  · exact (Nat.pow_le_pow_left h a).trans (Nat.pow_le_pow_right (by omega) h)

theorem pow_le_div_bound (T ℓ : ℕ) : T ^ ℓ ≤ ℓ ^ ℓ * (T / ℓ + 1) ^ ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  · rw [← mul_pow]
    exact Nat.pow_le_pow_left (Nat.lt_mul_div_succ T hℓ).le ℓ

theorem final_arith {d0 d1 ℓ h r k T nF nR D0 D1 : ℕ} {deg0 degJ degA degIG : ℤ}
    (hℓ : ℓ ≤ d0 + d1) (hh : h ≤ d0) (hr : r ≤ d1)
    (hT : T ^ ℓ ≤ ℓ ^ ℓ * (k + 1) ^ ℓ) (hF : nF ≤ nR) (h0pos : 0 ≤ deg0)
    (A1 : (((k + 1) ^ ℓ : ℕ) : ℤ) * degJ ≤ degA) (A2 : (nR : ℤ) * deg0 ≤ degJ) (A3 : degA ≤ degIG)
    (A4 : degIG ≤ (((d0 + d1).factorial * D0 ^ d0 * (2 * D1) ^ d1 : ℕ) : ℤ))
    (A5 : (((h + r).factorial * D0 ^ h * D1 ^ r : ℕ) : ℤ) ≤ ((h ^ h * r ^ r : ℕ) : ℤ) * deg0) :
    ((T ^ ℓ * nF * D0 ^ h * D1 ^ r : ℕ) : ℤ) ≤ ((Cst d0 d1 * D0 ^ d0 * D1 ^ d1 : ℕ) : ℤ) := by
  set X : ℕ := D0 ^ h * D1 ^ r
  set H : ℕ := h ^ h * r ^ r
  set M : ℕ := ℓ ^ ℓ
  set P : ℕ := (k + 1) ^ ℓ
  have hfac : (X : ℤ) ≤ (H : ℤ) * deg0 := by
    refine le_trans ?_ A5
    have := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (h + r))
    have : X ≤ (h + r).factorial * D0 ^ h * D1 ^ r := by
      simp only [X, mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    exact_mod_cast this
  have hJ0 : 0 ≤ degJ := le_trans (mul_nonneg (by positivity) h0pos) A2
  have hA0 : 0 ≤ degA := le_trans (mul_nonneg (by positivity) hJ0) A1
  have step1 : ((T ^ ℓ * nF * D0 ^ h * D1 ^ r : ℕ) : ℤ) ≤ (M : ℤ) * P * nR * X := by
    have : T ^ ℓ * nF * D0 ^ h * D1 ^ r ≤ M * P * nR * X := by
      simp only [X, mul_assoc]
      exact Nat.mul_le_mul hT (Nat.mul_le_mul hF le_rfl) |>.trans_eq (by ring)
    exact_mod_cast this
  have step2 : (M : ℤ) * P * nR * X ≤ (M : ℤ) * H * degIG := by
    calc (M : ℤ) * P * nR * X ≤ (M : ℤ) * P * nR * (H * deg0) := by gcongr
      _ = (M : ℤ) * H * (P * (nR * deg0)) := by ring
      _ ≤ (M : ℤ) * H * (P * degJ) := by gcongr
      _ ≤ (M : ℤ) * H * degA := by gcongr
      _ ≤ (M : ℤ) * H * degIG := by gcongr
  have step3 : (M : ℤ) * H * degIG ≤ ((Cst d0 d1 * D0 ^ d0 * D1 ^ d1 : ℕ) : ℤ) := by
    have hMH : M * H ≤ (d0 + d1) ^ (d0 + d1) * d0 ^ d0 * d1 ^ d1 := by
      simp only [M, H, mul_assoc]
      exact Nat.mul_le_mul (pow_self_le_pow_self hℓ)
        (Nat.mul_le_mul (pow_self_le_pow_self hh) (pow_self_le_pow_self hr))
    calc (M : ℤ) * H * degIG ≤ (M : ℤ) * H * (((d0 + d1).factorial * D0 ^ d0 * (2 * D1) ^ d1 :
      ℕ) : ℤ) := by
          gcongr
      _ = (((M * H) * ((d0 + d1).factorial * D0 ^ d0 * (2 * D1) ^ d1) : ℕ) : ℤ) := by
        push_cast
        ring
      _ ≤ ((Cst d0 d1 * D0 ^ d0 * D1 ^ d1 : ℕ) : ℤ) := by
          apply Nat.cast_le.mpr
          rw [Cst, mul_pow]
          calc M * H * ((d0 + d1).factorial * D0 ^ d0 * (2 ^ d1 * D1 ^ d1))
              = (M * H) * (d0 + d1).factorial * 2 ^ d1 * D0 ^ d0 * D1 ^ d1 := by ring
            _ ≤ ((d0 + d1) ^ (d0 + d1) * d0 ^ d0 * d1 ^ d1) * (d0 + d1).factorial * 2 ^ d1 *
                D0 ^ d0 * D1 ^ d1 := by gcongr
            _ = _ := by ring
  linarith

/-! ### The main theorem -/

/-- **Philippon's multiplicity estimate, in `K[X, Y, Z]`.** -/
theorem multEstB [CharZero K] [IsAlgClosed K]
    (W : Submodule K (LieG K d0 d1)) (S : Finset (GPt K d0 d1))
    (hS : GPt.zero ∈ S) (Pt : B) (hPt : Pt ∉ vanish (Set.univ : Set (GPt K d0 d1)))
    {D0 D1 T : ℕ} (hD0 : 1 ≤ D0) (hD1 : 1 ≤ D1) (hPD : Pt ∈ FLE K blk ![D0, D1])
    (hvan : ∀ g ∈ sig S (d0 + d1), ∀ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) →
      l.length ≤ (d0 + d1) * T → eval (pt g) (DwL l Pt) = 0) :
    ∃ (h0 : Submodule K (Fin d0 → K)) (U : Submodule ℚ (Fin d1 → ℚ)), (h0 ≠ ⊤ ∨ U ≠ ⊥) ∧
      ∀ F : Finset (GPt K d0 d1), F ⊆ S → (∀ g ∈ F, ∀ g' ∈ F, EquivMod h0 U g g' → g = g') →
        ((T ^ (finrank K W - finrank K ↥(W ⊓ h0.prod (torusLie K U))) * F.card *
          D0 ^ finrank K h0 * D1 ^ (d1 - finrank ℚ U) : ℕ) : ℤ) ≤
        ((Cst d0 d1 * D0 ^ d0 * D1 ^ d1 : ℕ) : ℤ) := by
  classical
  set D : Fin 2 → ℕ := ![D0, D1] with hDdef
  have hD : ∀ i, 1 ≤ D i := fun i => by fin_cases i <;> simp [D, hD0, hD1]
  /- 1. The chain. -/
  have hlast : Lr W S Pt T (d0 + d1) ≠ ⊤ := ne_top_of_le_ne_top
    (one_notMem_vanish ⟨GPt.zero, Set.mem_singleton _⟩) (Lr_le_vanish_zero W S Pt T hvan)
  obtain ⟨r, hr, hflat⟩ := exists_flat W S Pt T D hD hDdef hS hPt hlast
  have hLne : Lr W S Pt T (r + 1) ≠ ⊤ :=
    ne_top_of_le_ne_top hlast (Lr_mono' W S Pt T hS (by omega))
  obtain ⟨p, hp, hLp, hpdim⟩ := exists_prime_hdim blk D hD hLne
  have := hp
  have hIGp : (IG : Ideal B) ≤ p := le_sup_left.trans hLp
  have hLrp : Lr W S Pt T r ≤ p := (Lr_mono W S Pt T hS r).trans hLp
  have hpdim' : (hdata blk D K p).1 = (hdata blk D K (Lr W S Pt T r)).1 := hpdim.trans hflat
  /- 2. The stabilizer of `V = Z(p)`. -/
  have hGVsub : IsSubgroupG (stabG (zeros (p : Set B))) := stabG_isSubgroup D hIGp hD
  obtain ⟨R, -, hZR⟩ := component D hIGp hD (gensR W S Pt T r) rfl hLrp hpdim'
  obtain ⟨V0, Λ0, hGVcl⟩ : ∃ V0 Λ0, stabG (zeros (p : Set B)) = prodSet V0 Λ0 :=
    ⟨_, _, classify hGVsub (stabG_eq_zeros (p := p))⟩
  set GV := stabG (zeros (p : Set B)) with hGV
  set U := qspan Λ0 with hU
  set G0 := prodSet V0 (lsat U) with hG0
  have hG0sub : IsSubgroupG G0 := prodSet_isSubgroup V0 (lsat U)
  have hG0GV : G0 ⊆ GV := by rw [hGVcl]; exact prodSet_sat_subset V0 Λ0
  obtain ⟨Rc, hRcG, hcov⟩ := finite_cosets V0 Λ0
  have hGV_eq : GV = ⋃ c ∈ Rc, gtransl c G0 := by
    apply le_antisymm
    · rw [hGVcl]; exact hcov
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨c, hc, y, hy, rfl⟩ := hx
      exact hGVsub.mul_mem c (by rw [hGVcl]; exact hRcG c hc) y (hG0GV hy)
  have hRc_ne : Rc.Nonempty := by
    have : GPt.zero ∈ GV := hGVsub.one_mem
    rw [hGV_eq] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨c, hc, -⟩ := this
    exact ⟨c, hc⟩
  have hdimGV : (hdata blk D K (vanish GV)).1 = (hdata blk D K (vanish G0)).1 := by
    rw [hGV_eq]; exact hdim_vanish_cosets D G0 ⟨_, zero_mem_prodSet _ _⟩ Rc hRc_ne
  /- 3. The ideal `A` and Roy's vanishing claim. -/
  set Fs : Set B := {Q | ∃ P ∈ gensR W S Pt T r, ∃ v ∈ zeros (p : Set B), Q = transl v P} with hFs
  set A : Ideal B := IG ⊔ Ideal.span Fs with hA
  set SG : Set (GPt K d0 d1) := ⋃ s ∈ S, gtransl s GV with hSGdef
  have hAVO : A ≤ VO W T (vanish SG) := by
    refine sup_le (IG_le_VO W T SG) (Ideal.span_le.mpr ?_)
    rintro _ ⟨P, ⟨σ, hσ, l0, hl0W, hl0, rfl⟩, v, hv, rfl⟩ l hlW hl x hx
    simp only [SG, Set.mem_iUnion] at hx
    obtain ⟨s, hs, u, hu, rfl⟩ := hx
    rw [DwL_transl, DwL_transl, ← DwL_append, eval_transl, eval_transl]
    have hpt : gmul σ (gmul v (gmul s u)) = gmul (gmul σ s) (gmul u v) := by
      refine Prod.ext ?_ ?_
      · simp only [gmul]; abel
      · simp only [gmul]; ac_rfl
    rw [hpt, ← eval_transl]
    have hgen : transl (gmul σ s) (DwL (l0 ++ l) Pt) ∈ gensR W S Pt T (r + 1) :=
      ⟨gmul σ s, gmul_mem_sig hσ hs, l0 ++ l,
        fun w hw => (List.mem_append.mp hw).elim (hl0W w) (hlW w),
        by rw [List.length_append, Nat.succ_mul]; omega, rfl⟩
    exact (hu v hv) _ (hLp (Ideal.mem_sup_right (Ideal.subset_span hgen)))
  have hSGne : SG.Nonempty :=
    ⟨GPt.zero, Set.mem_biUnion hS ⟨GPt.zero, hGVsub.one_mem, gmul_zero _⟩⟩
  have hAne : A ≠ ⊤ :=
    ne_top_of_le_ne_top (one_notMem_vanish hSGne) (hAVO.trans (VO_le W T _))
  have hIGA : (IG : Ideal B) ≤ A := le_sup_left
  /- 4. `hdim A ≤ hdim G_V`. -/
  have hzA : zeros (A : Set B) ⊆ ⋃ a ∈ R, gtransl a GV := fun g hg =>
    hZR (fun Q hQ => hg Q (Ideal.mem_sup_right (Ideal.subset_span hQ)))
  have hradA : vanish (⋃ a ∈ R, gtransl a GV) ≤ A.radical := by
    rw [← vanish_zeros_eq hIGA]; exact fun P hP g hg => hP g (hzA hg)
  have hradne : A.radical ≠ ⊤ := fun h => hAne (Ideal.radical_eq_top.mp h)
  have hRne : R.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    apply hradne
    rw [eq_top_iff]
    refine le_trans ?_ hradA
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, vanish_empty, le_refl]
  have hdimA_le : (hdata blk D K A).1 ≤ (hdata blk D K (vanish G0)).1 := by
    have h1 := hdata_le_of_le blk D K hradA hradne
    rw [hdim_radical blk D hD hAne] at h1
    have h2 := hdim_vanish_cosets D GV ⟨_, hGVsub.one_mem⟩ R hRne
    rcases h1 with h1 | ⟨h1, -⟩ <;> omega
  /- 5. Cosets of `G⁰` covering `S·G_V`. -/
  set T' : Finset (GPt K d0 d1) := (S ×ˢ Rc).image fun x => gmul x.1 x.2 with hT'
  have hSG : SG = ⋃ a ∈ T', gtransl a G0 := by
    ext x
    simp only [SG, T', Set.mem_iUnion, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨s, hs, y, hy, rfl⟩
      rw [hGV_eq] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨c, hc, z, hz, rfl⟩ := hy
      exact ⟨gmul s c, ⟨(s, c), ⟨hs, hc⟩, rfl⟩, z, hz, by rw [gmul_assoc]⟩
    · rintro ⟨a, ⟨⟨s, c⟩, ⟨hs, hc⟩, rfl⟩, z, hz, rfl⟩
      refine ⟨s, hs, gmul c z, ?_, by rw [gmul_assoc]⟩
      rw [hGV_eq]
      exact Set.mem_biUnion hc ⟨z, hz, rfl⟩
  obtain ⟨Rs, -, hRsU, hdist⟩ := exists_reps hG0sub T'
  have hESG : (⋃ a ∈ Rs, gtransl a G0) = SG := hRsU.trans hSG.symm
  have hRs_ne : Rs.Nonempty := by
    obtain ⟨x, hx⟩ := hSGne
    rw [← hESG] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨a, ha, -⟩ := hx
    exact ⟨a, ha⟩
  set J := vanish (⋃ a ∈ Rs, gtransl a G0) with hJdef
  have hJSG : J = vanish SG := by rw [hJdef, hESG]
  have hJne : J ≠ ⊤ := by rw [hJSG]; exact one_notMem_vanish hSGne
  have hdimJ : (hdata blk D K J).1 = (hdata blk D K (vanish G0)).1 :=
    hdim_vanish_cosets D G0 ⟨_, zero_mem_prodSet _ _⟩ Rs hRs_ne
  have hAVO' : A ≤ VO W T J := by rw [hJSG]; exact hAVO
  have hAJ : A ≤ J := hAVO'.trans (VO_le W T J)
  have hdimA : (hdata blk D K A).1 = (hdata blk D K J).1 := by
    rcases hdata_le_of_le blk D K hAJ hJne with h | ⟨h, -⟩
    · omega
    · exact h.symm
  /- 6. Wüstholz. -/
  have h815 := lemma815 V0 (lsat U) W Rs hdist
  rw [qspan_lsat Λ0] at h815
  obtain ⟨w, Q, hwW, hQJ, hδ⟩ := h815
  obtain ⟨c0, hQdeg⟩ := exists_c0 hD Q
  have hk := Nat.mul_div_le T (finrank K W - finrank K ↥(W ⊓ V0.prod (torusLie K (qspan Λ0))))
  have hAW : ∀ x ∈ A, ∀ l : List (Fin (finrank K W - finrank K ↥(W ⊓ V0.prod (torusLie K (qspan
    Λ0))))),
      l.length ≤ T → DL (fun i => Dw (w i)) l x ∈ J := by
    intro x hx l hl
    rw [DL_eq_DwL]
    exact hAVO' hx (l.map w) (fun v hv => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv; exact hwW i) (by simpa using hl)
  have A1 :=
    deg_le_of_hfun D hJne hAne hdimA (Nat.one_le_pow _ _ (Nat.succ_pos _))
      (fun t => wustholz (fun i => Dw (w i)) hQJ hδ hQdeg hk hAW t)
  /- 7. Cosets, Bézout, and the two dimension computations. -/
  obtain ⟨c1, hc1⟩ := hfun_cosets_ge D hD V0 (lsat U) Rs hdist
  have A2 : (Rs.card : ℤ) * (hdata blk D K (vanish G0)).2 ≤ (hdata blk D K J).2 :=
    deg_le_of_hfun D (one_notMem_vanish ⟨_, zero_mem_prodSet _ _⟩) hJne hdimJ
      (Finset.card_pos.mpr hRs_ne) hc1
  have hFD : ∀ Q ∈ Fs, Q ∈ FLE K blk D := by
    rintro _ ⟨P, hP, v, -, rfl⟩
    exact transl_mem_FLE D v (gensR_mem_FLE W S Pt T hPD r P hP)
  have hl : (Ideal.ofList (lG (K := K) (d0 := d0) (d1 := d1))).height =
      (lG (K := K) (d0 := d0) (d1 := d1)).length := by
    rw [lG_length]; exact height_IG
  have A3 : (hdata blk D K A).2 ≤ (hdata blk D K (IG : Ideal B)).2 :=
    bezout blk D hD hl hFD hAne
  have A4 := (hdata_IG (K := K) (d0 := d0) (d1 := d1) hD0 hD1).2.2
  obtain ⟨-, A5⟩ := hdata_prodSet (K := K) V0 U hD0 hD1
  have h0pos : 0 ≤ (hdata blk D K (vanish G0)).2 :=
    (hdata_pos blk D K (one_notMem_vanish ⟨_, zero_mem_prodSet V0 (lsat U)⟩)).le
  /- 8. Properness of the obstruction. -/
  have hproper : V0 ≠ ⊤ ∨ U ≠ ⊥ := by
    by_contra hc
    push Not at hc
    obtain ⟨hV0, hU0⟩ := hc
    have huniv : GV = Set.univ := by
      rw [hGVcl, hV0]
      refine Set.eq_univ_of_forall fun g => ?_
      have : g ∈ prodSet (⊤ : Submodule K (Fin d0 → K)) (lsat (⊥ : Submodule ℚ (Fin d1 → ℚ))) := by
        rw [prodSet_top_bot]; trivial
      refine prodSet_antitone ⊤ ?_ this
      rw [← hU0]; exact le_lsat_qspan Λ0
    have := le_vanish_univ_of_stabG hIGp hLrp huniv
    exact hPt (this (Lr_mono' W S Pt T hS (Nat.zero_le r) (Pt_mem_L0 W S Pt T)))
  /- 9. Conclusion. -/
  refine ⟨V0, U, hproper, fun F hFS hFd => ?_⟩
  have hcardF : F.card ≤ Rs.card := by
    have hmem : ∀ f ∈ F, ∃ a ∈ Rs, f ∈ gtransl a G0 := by
      intro f hf
      have : f ∈ ⋃ a ∈ Rs, gtransl a G0 := by
        rw [hESG]; exact Set.mem_biUnion (hFS hf) ⟨GPt.zero, hGVsub.one_mem, gmul_zero f⟩
      simpa only [Set.mem_iUnion, exists_prop] using this
    choose! φ hφR hφf using hmem
    refine Finset.card_le_card_of_injOn φ (fun f hf => hφR f hf) (fun f hf f' hf' heq => ?_)
    apply hFd f hf f' hf'
    obtain ⟨u, hu, hfu⟩ := hφf f hf
    obtain ⟨u', hu', hfu'⟩ := hφf f' hf'
    rw [heq] at hfu
    exact equivMod_of_cosets hu hu' hfu hfu'
  have hℓle : finrank K W - finrank K ↥(W ⊓ V0.prod (torusLie K (qspan Λ0))) ≤ d0 + d1 := by
    have h1 : finrank K (LieG K d0 d1) = d0 + d1 := by
      simp [LieG, Module.finrank_prod]
    have := Submodule.finrank_le W
    omega
  have hhle : finrank K V0 ≤ d0 := by
    have := Submodule.finrank_le V0
    rwa [Module.finrank_fin_fun] at this
  exact final_arith hℓle hhle (Nat.sub_le _ _) (pow_le_div_bound T _) hcardF h0pos A1 A2 A3 A4 A5

end StrongSix.M2

end LeanPool
