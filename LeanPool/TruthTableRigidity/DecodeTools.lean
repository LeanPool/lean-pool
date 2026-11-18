/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import Mathlib.Tactic.Linarith
public import LeanPool.TruthTableRigidity.BaireLemmas

/-!
# Tools for the coding lemma (Proposition 4.3)

* closure properties of tt-functionals: reading a bit of an iterate, finite windows,
  definition by cases on a bit of a third functional;
* 2-adic arithmetic: the elements `2^l` and `0^l⌢S^m(X)`, and hitting a basic open set by
  adding a multiple of `2^{l+1}`.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-! ### Closure properties of tt-functionals -/

/-- `B ↦ (Ψ(Θ^m(B))(j))_m` is a tt-functional. -/
theorem IsTTFunctional.iterate_read {Θ Ψ : Oracle → Oracle} (hΘ : IsTTFunctional Θ)
    (hΨ : IsTTFunctional Ψ) (j : ℕ) : IsTTFunctional fun B m => Ψ (Θ^[m] B) j := by
  let Ξ : Oracle → Oracle := fun S => ojoin (Ψ (Θ (odds S))) (Θ (odds S))
  have hΞ : IsTTFunctional Ξ :=
    (hΨ.comp (hΘ.comp isTTFunctional_odds)).join (hΘ.comp isTTFunctional_odds)
  let S₀ : Oracle → Oracle := fun B => ojoin (Ψ B) B
  have hS₀ : IsTTFunctional S₀ := hΨ.join isTTFunctional_id
  have hit : ∀ m B, Ξ^[m] (S₀ B) = ojoin (Ψ (Θ^[m] B)) (Θ^[m] B) := by
    intro m
    induction m with
    | zero => intro B; rfl
    | succ m ih =>
      intro B
      rw [Function.iterate_succ_apply', ih]
      simp only [Ξ, odds_ojoin, Function.iterate_succ_apply']
  have := (hΞ.iterate (2 * j)).comp hS₀
  convert this using 1
  funext B m
  simp only [Function.comp, hit, ojoin_even]

theorem pre_const_eq_replicate (b : Bool) (N : ℕ) : pre (fun _ => b) N = List.replicate N b := by
  simp [pre, List.map_const']

/-- `Z ↦ (∃ c < N, Z c ≠ b)` (as a constant oracle) is a tt-functional. -/
theorem isTTFunctional_someNe (N : ℕ) (b : Bool) :
    IsTTFunctional fun Z (_ : ℕ) => decide (∃ c < N, Z c ≠ b) := by
  refine isTTFunctional_of_use (u := fun _ => N)
    (t := fun _ L => !decide (L = List.replicate N b)) (Primrec.const N) ?_ ?_
  · exact Primrec.not.comp (Primrec.eq.comp Primrec.snd (Primrec.const _)).decide
  · intro Z n
    have h : pre Z N = List.replicate N b ↔ ∀ c < N, Z c = b := by
      rw [← pre_const_eq_replicate, pre_eq_iff]
    by_cases hc : ∃ c < N, Z c ≠ b
    · have : ¬ pre Z N = List.replicate N b := fun h' => by
        obtain ⟨c, hc, hne⟩ := hc; exact hne (h.mp h' c hc)
      simp [hc, this]
    · have : pre Z N = List.replicate N b := h.mpr (by push Not at hc; exact hc)
      simp [hc, this]

/-! ### 2-adic arithmetic -/

/-- The 2-adic integer `0^l⌢S^m(X)`. -/
def zseq (l : ℕ) (X : Oracle) (m : ℕ) : Z2 := prep (List.replicate l false) (shift^[m] X)

theorem lowZero_zseq (l : ℕ) (X : Oracle) (m : ℕ) : LowZero l (zseq l X m) :=
  lowZero_prep_rep l _

theorem trunc_zpow2 (l k : ℕ) : trunc (zpow2 l) k = if l < k then 2 ^ l else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [trunc_succ, ih, zpow2_apply]
    by_cases h : k = l
    · subst h; simp [bv]
    · have : (l < k + 1) ↔ (l < k) := by omega
      simp [h, bv, this]

theorem trunc_zpow2_mod (l k : ℕ) : trunc (zpow2 l) k = 2 ^ l % 2 ^ k := by
  rw [trunc_zpow2]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)]
  · rw [Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))]

theorem trunc_nsmul (c : ℕ) (A : Z2) (k : ℕ) : trunc (c • A) k = (c * trunc A k) % 2 ^ k := by
  induction c with
  | zero => simp [Z2.zero_def]
  | succ c ih =>
    rw [succ_nsmul, Z2.trunc_add, ih, Nat.mod_add_mod, add_mul, one_mul]

theorem lowZero_zero (k : ℕ) : LowZero k (0 : Z2) := fun _ _ => rfl

theorem lowZero_nsmul {k : ℕ} {A : Z2} (hA : LowZero k A) (c : ℕ) : LowZero k (c • A) := by
  induction c with
  | zero => rw [zero_smul]; exact lowZero_zero k
  | succ c ih => rw [succ_nsmul]; exact Z2.lowZero_add ih hA

theorem lowZero_zpow2_two (l : ℕ) : LowZero (l + 1) (zpow2 l + zpow2 l) := by
  rw [Z2.add_self]; exact lowZero_cons (lowZero_zpow2 l)

/-- Pure arithmetic: we can adjust `x` by a multiple of `M` to hit any residue modulo `M K`
which agrees with `x` modulo `M`. -/
theorem nat_hit (x v M K : ℕ) (hM : 0 < M) (hK : 0 < K) (h : x % M = v % M) (hv : v < M * K) :
    ∃ c < K, (x + c * M) % (M * K) = v := by
  set r := x % M
  set q := x / M
  set q' := v / M
  have hx : x = q * M + r := by rw [mul_comm]; exact (Nat.div_add_mod x M).symm
  have hv' : v = q' * M + r := by rw [h, mul_comm]; exact (Nat.div_add_mod v M).symm
  have hr : r < M := Nat.mod_lt _ hM
  have hq' : q' < K := by
    rw [Nat.div_lt_iff_lt_mul hM]; rwa [mul_comm]
  refine ⟨(q' + K - q % K) % K, Nat.mod_lt _ hK, ?_⟩
  set c := (q' + K - q % K) % K
  have hqc : (q + c) % K = q' := by
    have hqK : q % K < K := Nat.mod_lt _ hK
    have hsub : q' + K - q % K + q % K = q' + K :=
      Nat.sub_add_cancel (le_trans hqK.le (Nat.le_add_left K q'))
    have hq := Nat.div_add_mod q K
    have e : q + (q' + K - q % K) = q' + K * (q / K + 1) := by linarith
    simp only [c]
    rw [Nat.add_mod_mod, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq']
  have key : x + c * M = (q + c) / K * (M * K) + (q' * M + r) := by
    have hd := Nat.div_add_mod (q + c) K
    rw [hqc] at hd
    rw [hx]
    have : (q + c) * M = (K * ((q + c) / K) + q') * M := by rw [hd]
    linarith [this]
  rw [key, hv', Nat.mul_add_mod_of_lt]
  calc q' * M + r < q' * M + M := by omega
    _ = (q' + 1) * M := by ring
    _ ≤ K * M := Nat.mul_le_mul_right _ hq'
    _ = M * K := mul_comm _ _

theorem trunc_of_mem_Ncyl {τ : List Bool} {Z : Oracle} (h : Z ∈ Ncyl τ) :
    trunc Z τ.length = val τ := by
  rw [← val_pre]; exact congrArg val h

theorem mem_Ncyl_of_trunc {τ : List Bool} {Z : Oracle} (h : trunc Z τ.length = val τ) :
    Z ∈ Ncyl τ := by
  rw [mem_Ncyl_iff]
  intro i hi
  apply eq_of_trunc_eq _ hi
  rw [h, ← val_pre, pre_prep]

/-- If `G ∈ N_{σ⌢i}`, `T ∈ N_{0^l}` with `T(l) = 1` (where `l = |σ|`) and `q₁ ⊇ σ⌢(1-i)`, then
some `G + T + c·2^{l+1}` with `c < 2^{|q₁| - l - 1}` lies in `N_{q₁}`. -/
theorem exists_hit {σ q₁ : List Bool} {i : Bool} {G T : Z2} (hG : G ∈ Ncyl (σ ++ [i]))
    (hT : LowZero σ.length T) (hTl : T σ.length = true) (hq : σ ++ [!i] <+: q₁) :
    ∃ c < 2 ^ (q₁.length - (σ.length + 1)),
      (G + (T + c • (zpow2 σ.length + zpow2 σ.length)) : Z2) ∈ Ncyl q₁ := by
  set l := σ.length
  set L := q₁.length
  have hlL : l + 1 ≤ L := by have := hq.length_le; simp at this; omega
  have hML : 2 ^ (l + 1) * 2 ^ (L - (l + 1)) = 2 ^ L := by rw [← pow_add]; congr 1; omega
  -- low bits of `G + T` and of `q₁`
  have hGl : trunc G (l + 1) = trunc G l + bv i * 2 ^ l := by
    rw [trunc_succ]
    have := (mem_Ncyl.mp hG) l (by simp [l])
    rw [this]; simp [l]
  have hTl' : trunc T (l + 1) = 2 ^ l := by
    rw [trunc_succ, lowZero_iff_trunc.mp hT, hTl]; simp [bv]
  have hσG : val σ = trunc G l := by
    have h3 : pre G (σ ++ [i]).length = σ ++ [i] := hG
    rw [List.length_append, List.length_singleton, pre_succ] at h3
    rw [← List.append_inj_left' h3 rfl, val_pre]
  have hq₁ : trunc (prep q₁ zzero) (l + 1) = trunc G l + bv (!i) * 2 ^ l := by
    have hpre : pre (prep q₁ zzero) (l + 1) = σ ++ [!i] := by
      have h1 : pre (prep q₁ zzero) L = q₁ := pre_prep q₁ zzero
      have h2 : pre (prep q₁ zzero) (l + 1) <+: pre (prep q₁ zzero) L := pre_prefix _ hlL
      rw [h1] at h2
      have hlen : (pre (prep q₁ zzero) (l + 1)).length = (σ ++ [!i]).length := by
        simp [length_pre, l]
      exact (List.prefix_of_prefix_length_le h2 hq (le_of_eq hlen)).eq_of_length hlen
    rw [← val_pre, hpre, val_append_singleton, hσG]
  have hGTlow : trunc (G + T : Z2) (l + 1) = trunc G l + bv (!i) * 2 ^ l := by
    rw [Z2.trunc_add, hGl, hTl', pow_succ]
    have hlt := trunc_lt G l
    cases i
    · simp only [bv, Bool.false_eq_true, ite_false, Bool.not_false, ite_true, zero_mul, add_zero,
        one_mul]
      exact Nat.mod_eq_of_lt (by omega)
    · simp only [bv, ite_true, Bool.not_true, Bool.false_eq_true, ite_false, zero_mul, add_zero,
        one_mul]
      rw [show trunc G l + 2 ^ l + 2 ^ l = trunc G l + 2 ^ l * 2 by ring, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  -- the target residue
  have hvq : val q₁ = trunc (prep q₁ zzero) L := (trunc_of_mem_Ncyl (prep_mem q₁ zzero)).symm
  have hxv : trunc (G + T : Z2) L % 2 ^ (l + 1) = val q₁ % 2 ^ (l + 1) := by
    rw [trunc_mod _ hlL, hGTlow, hvq, trunc_mod _ hlL, hq₁]
  have hvlt : val q₁ < 2 ^ (l + 1) * 2 ^ (L - (l + 1)) := by
    rw [hML, hvq]; exact trunc_lt _ _
  obtain ⟨c, hc, hcx⟩ := nat_hit _ _ _ _ (by positivity) (by positivity) hxv hvlt
  refine ⟨c, hc, mem_Ncyl_of_trunc ?_⟩
  have e : (G + (T + c • (zpow2 l + zpow2 l)) : Z2) = (G + T) + c • (zpow2 l + zpow2 l) := by
    abel
  rw [e, Z2.trunc_add (G + T), trunc_nsmul, Z2.trunc_add (zpow2 l) (zpow2 l), trunc_zpow2_mod,
    ← hcx, hML,
    ← Nat.add_mod (2 ^ l) (2 ^ l), Nat.mul_mod_mod, Nat.add_mod_mod,
    show 2 ^ l + 2 ^ l = 2 ^ (l + 1) by ring]

end TT
