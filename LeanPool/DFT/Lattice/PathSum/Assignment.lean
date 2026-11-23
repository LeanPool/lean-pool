/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Fermions.SecondQuantization
public import LeanPool.DFT.Lattice.StrongPotential.LeadingCoefficient
public import Mathlib.Combinatorics.SimpleGraph.Metric
meta import Mathlib.Tactic.Push

/-!
# Optimal particle assignments

* `Mopt`, `mopt`: optimal-assignment (transport) distance between configurations; `lip_mopt`: it
  grows by at most one per fermion hop.
* `exists_opt_fixing`: an optimal assignment leaving all common sites in place exists.
* `opt_unique_of_through`: only that assignment routes every moving particle through its partner.
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-- Cost of the assignment `σ` (particle `l` of the target tuple comes from `c_{σ l}`). -/
noncomputable def acost (G : SimpleGraph (Fin M)) (c : Conf M N) (τ : Fin N → Fin M)
    (σ : Equiv.Perm (Fin N)) : ℕ :=
  ∑ l, G.dist (τs c (σ l)) (τ l)

/-- Optimal-assignment distance. -/
noncomputable def Mopt (G : SimpleGraph (Fin M)) (c : Conf M N) (τ : Fin N → Fin M) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (acost G c τ)

/-- The minimum sum of graph distances over matchings of two configurations. -/
noncomputable def mopt (G : SimpleGraph (Fin M)) (c : Conf M N) (y : Conf M N) : ℕ :=
    Mopt G c (τs y)

lemma Mopt_le (G : SimpleGraph (Fin M)) (c : Conf M N) (τ : Fin N → Fin M)
    (σ : Equiv.Perm (Fin N)) :
    Mopt G c τ ≤ acost G c τ σ := Finset.inf'_le _ (Finset.mem_univ σ)

lemma Mopt_exists (G : SimpleGraph (Fin M)) (c : Conf M N) (τ : Fin N → Fin M) :
    ∃ σ, Mopt G c τ = acost G c τ σ := by
  obtain ⟨σ, -, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (acost G c τ)
  exact ⟨σ, h⟩

lemma mopt_self (G : SimpleGraph (Fin M)) (c : Conf M N) : mopt G c c = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc mopt G c c ≤ acost G c (τs c) 1 := Mopt_le _ _ _ _
    _ = 0 := by simp [acost]

lemma Mopt_perm (G : SimpleGraph (Fin M)) (c : Conf M N) (τ : Fin N → Fin M)
    (ρ : Equiv.Perm (Fin N)) :
    Mopt G c (fun l => τ (ρ l)) = Mopt G c τ := by
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := Mopt_exists G c τ
    calc Mopt G c (fun l => τ (ρ l)) ≤ acost G c (fun l => τ (ρ l)) (ρ.trans σ) := Mopt_le _ _ _ _
      _ = acost G c τ σ := by
          unfold acost
          exact Equiv.sum_comp ρ (fun l => G.dist (τs c (σ l)) (τ l))
      _ = Mopt G c τ := hσ.symm
  · obtain ⟨σ, hσ⟩ := Mopt_exists G c (fun l => τ (ρ l))
    calc Mopt G c τ ≤ acost G c τ (ρ.symm.trans σ) := Mopt_le _ _ _ _
      _ = acost G c (fun l => τ (ρ l)) σ := by
          unfold acost
          rw [← Equiv.sum_comp ρ]
          simp
      _ = Mopt G c (fun l => τ (ρ l)) := hσ.symm

lemma Mopt_update {G : SimpleGraph (Fin M)} (hG : G.Connected) (c : Conf M N) (τ : Fin N → Fin M)
    (k : Fin N) (a : Fin M) : Mopt G c (Function.update τ k a) ≤ Mopt G c τ + G.dist (τ k) a := by
  obtain ⟨σ, hσ⟩ := Mopt_exists G c τ
  calc Mopt G c (Function.update τ k a) ≤ acost G c (Function.update τ k a) σ := Mopt_le _ _ _ _
    _ ≤ acost G c τ σ + G.dist (τ k) a := by
        unfold acost
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
          ← Finset.add_sum_erase _ (fun l => G.dist (τs c (σ l)) (τ l)) (Finset.mem_univ k)]
        have hrest : ∑ l ∈ Finset.univ.erase k, G.dist (τs c (σ l)) (Function.update τ k a l) =
            ∑ l ∈ Finset.univ.erase k, G.dist (τs c (σ l)) (τ l) := by
          apply Finset.sum_congr rfl; intro l hl
          rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]
        rw [hrest, Function.update_self]
        have := hG.dist_triangle (u := τs c (σ k)) (v := τ k) (w := a)
        omega
    _ = Mopt G c τ + G.dist (τ k) a := by rw [hσ]

/-- `mopt` is a valid distance for the fermionic hopping matrix. -/
theorem lip_mopt {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ) (c : Conf M N) :
    Lip (Γ (-hopM G t) : Matrix (Conf M N) (Conf M N) ℝ) (mopt G c) := by
  intro y z _ hyz
  -- a nonzero matrix element comes from one hop `τs y k → b` along an edge
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyz
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  have hadj : G.Adj (τs y k) b := by
    by_contra hna
    apply hb
    simp [hopM, hna]
  have hamp : amp z (Function.update (τs y) k b) ≠ 0 := by
    intro h0; apply hb; rw [h0, mul_zero]
  -- the hopped tuple is a permutation of `τs z`
  have hinj : Function.Injective (Function.update (τs y) k b) := by
    by_contra hni; exact hamp (by rw [amp, slater_of_not_injective _ hni])
  have hmem : ∀ l, Function.update (τs y) k b l ∈ z.1 := by
    intro l; by_contra hnm; exact hamp (amp_of_not_mem z hnm)
  obtain ⟨ρ, hρ⟩ := exists_perm_of_injective z hinj hmem
  have hz : Mopt G c (Function.update (τs y) k b) = mopt G c z := by
    rw [show Function.update (τs y) k b = fun l => τs z (ρ l) from funext hρ, Mopt_perm]; rfl
  have hback : τs y = Function.update (Function.update (τs y) k b) k (τs y k) := by simp
  have h1 := Mopt_update hG c (Function.update (τs y) k b) k (τs y k)
  rw [← hback, hz, Function.update_self, SimpleGraph.dist_comm,
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h1
  exact h1

end

section

open Matrix

variable {M N : ℕ}

/-- The matching specified by the permutation attains the minimum assignment cost. -/
abbrev isOpt (G : SimpleGraph (Fin M)) (c y : Conf M N) (σ : Equiv.Perm (Fin N)) : Prop :=
  acost G c (τs y) σ.symm = mopt G c y

/-- Number of common targets served by themselves. -/
noncomputable def nfix (c y : Conf M N) (σ : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter (fun l => τs y l ∈ c.1 ∧ τs c (σ.symm l) = τs y l)).card

theorem exists_opt_fixing {G : SimpleGraph (Fin M)} (hG : G.Connected) (c y : Conf M N) :
    ∃ σ0, isOpt G c y σ0 ∧ ∀ l, τs y l ∈ c.1 → τs c (σ0.symm l) = τs y l := by
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => isOpt G c y σ)
  have hS : S.Nonempty := by
    obtain ⟨ρ, hρ⟩ := Mopt_exists G c (τs y)
    exact ⟨ρ.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [isOpt, mopt, hρ]⟩⟩
  obtain ⟨σ, hσS, hmax⟩ := Finset.exists_max_image S (nfix c y) hS
  have hσ : isOpt G c y σ := (Finset.mem_filter.mp hσS).2
  refine ⟨σ, hσ, ?_⟩
  by_contra hbad
  push Not at hbad
  obtain ⟨l, hlc, hlne⟩ := hbad
  obtain ⟨j, hj⟩ := τs_surj c hlc
  set l2 := σ j
  have hl2 : σ.symm l2 = j := by simp [l2]
  have hll2 : l ≠ l2 := by
    intro h; apply hlne; rw [h, hl2, hj, h]
  -- swap the targets `l` and `l2`
  set σ' : Equiv.Perm (Fin N) := ((Equiv.swap l l2).trans σ.symm).symm
  have hσ'l : σ'.symm l = j := by simp [σ', Equiv.swap_apply_left, hl2]
  have hσ'l2 : σ'.symm l2 = σ.symm l := by simp [σ', Equiv.swap_apply_right]
  have hσ'o : ∀ k, k ≠ l → k ≠ l2 → σ'.symm k = σ.symm k := by
    intro k h1 h2; simp [σ', Equiv.swap_apply_of_ne_of_ne h1 h2]
  -- the new assignment is still optimal
  have hcost : acost G c (τs y) σ'.symm ≤ acost G c (τs y) σ.symm := by
    unfold acost
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l),
      ← Finset.add_sum_erase _ (fun k => G.dist (τs c (σ.symm k)) (τs y k)) (Finset.mem_univ l),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hll2.symm, Finset.mem_univ l2⟩),
      ← Finset.add_sum_erase _ (fun k => G.dist (τs c (σ.symm k)) (τs y k))
        (Finset.mem_erase.mpr ⟨hll2.symm, Finset.mem_univ l2⟩)]
    have hrest : ∑ k ∈ (Finset.univ.erase l).erase l2, G.dist (τs c (σ'.symm k)) (τs y k) =
        ∑ k ∈ (Finset.univ.erase l).erase l2, G.dist (τs c (σ.symm k)) (τs y k) := by
      apply Finset.sum_congr rfl; intro k hk
      rw [hσ'o k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1]
    rw [hrest, hσ'l, hσ'l2, hj, hl2, hj, SimpleGraph.dist_self]
    have := hG.dist_triangle (u := τs c (σ.symm l)) (v := τs y l) (w := τs y l2)
    omega
  have hσ'opt : isOpt G c y σ' := by
    unfold isOpt at hσ ⊢
    apply le_antisymm (hσ ▸ hcost)
    exact Mopt_le G c (τs y) σ'.symm
  -- and it fixes strictly more common targets
  have hlt : nfix c y σ < nfix c y σ' := by
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro k hk
      obtain ⟨-, hkc, hkfix⟩ := Finset.mem_filter.mp hk
      have hkl : k ≠ l := by intro h; subst h; exact hlne hkfix
      have hkl2 : k ≠ l2 := by
        intro h; subst h; apply hll2
        apply τs_injective y
        rw [← hkfix, hl2, hj]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkc, by rw [hσ'o k hkl hkl2]; exact hkfix⟩
    · intro hsub
      have : l ∈ Finset.univ.filter (fun k => τs y k ∈ c.1 ∧ τs c (σ'.symm k) = τs y k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlc, by rw [hσ'l, hj]⟩
      exact hlne (Finset.mem_filter.mp (hsub this)).2.2
  have := hmax σ' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ'opt⟩)
  omega

theorem opt_unique_of_through {G : SimpleGraph (Fin M)} (hG : G.Connected) (c y : Conf M N)
    {σ0 σ : Equiv.Perm (Fin N)} (h0 : isOpt G c y σ0)
    (hfix : ∀ l, τs y l ∈ c.1 → τs c (σ0.symm l) = τs y l) (hσ : isOpt G c y σ)
    (hthr : ∀ l, τs y l ∉ c.1 →
      G.dist (τs c (σ.symm l)) (τs c (σ0.symm l)) + G.dist (τs c (σ0.symm l)) (τs y l) =
        G.dist (τs c (σ.symm l)) (τs y l)) : σ = σ0 := by
  -- termwise: cost of σ ≥ cost of σ0, with equality forcing equal starts
  have hterm : ∀ l, G.dist (τs c (σ0.symm l)) (τs y l) + G.dist (τs c (σ.symm l)) (τs c (σ0.symm l))
      ≤ G.dist (τs c (σ.symm l)) (τs y l) := by
    intro l
    by_cases hl : τs y l ∈ c.1
    · rw [hfix l hl, SimpleGraph.dist_self, zero_add]
    · rw [← hthr l hl]; omega
  have hsum : ∑ l, G.dist (τs c (σ0.symm l)) (τs y l) +
      ∑ l, G.dist (τs c (σ.symm l)) (τs c (σ0.symm l))
      ≤ ∑ l, G.dist (τs c (σ.symm l)) (τs y l) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum (fun l _ => hterm l)
  have hc0 : ∑ l, G.dist (τs c (σ0.symm l)) (τs y l) = ∑ l, G.dist (τs c (σ.symm l)) (τs y l) := by
    unfold isOpt acost at h0 hσ; rw [h0, hσ]
  have hzero : ∑ l, G.dist (τs c (σ.symm l)) (τs c (σ0.symm l)) = 0 := by omega
  have hall : ∀ l, τs c (σ.symm l) = τs c (σ0.symm l) := by
    intro l
    have := (Finset.sum_eq_zero_iff.mp hzero) l (Finset.mem_univ l)
    exact ((hG.preconnected _ _).dist_eq_zero_iff).mp this
  have hsymm : σ.symm = σ0.symm := Equiv.ext fun l => τs_injective c (hall l)
  simpa using congrArg Equiv.symm hsymm

end

end DFT
