/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.PathSum.Assignment
public import LeanPool.DFT.Lattice.Fermions.FirstQuantization
public import LeanPool.DFT.Lattice.StrongPotential.PowerSums
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Ring

/-!
# Leading coefficients of free fermions

* `T_MB_formula`: the many-body leading coefficient is a signed sum over optimal assignments of
  products of single-particle leading coefficients.
* `T_MB_powersum`, `assign_rigid`, and `alpha_eq_D`: `α_y(y) = D(u)`, the Slater-type sum over
  optimal assignments.
-/

@[expose] public section

namespace DFT

section

open Matrix Polynomial

variable {M N : ℕ}

lemma Hl_map_eval {C : Type*} [DecidableEq C] (B : Matrix C C ℝ) (x : C → ℝ) (lam : ℝ) :
    (Hl B 0 x).map (Polynomial.eval lam) = B + Matrix.diagonal (lam • x) := by
  simpa using Hl_eval_eq B 0 x lam

lemma eval_pow_entry {C : Type*} [Fintype C] [DecidableEq C] (P : Matrix C C ℝ[X]) (n : ℕ) (a b : C)
    (lam : ℝ) : ((P ^ n) a b).eval lam = ((P.map (Polynomial.eval lam)) ^ n) a b := by
  rw [← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
  rfl

lemma lip_dist {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ) (b : Fin M) :
    Lip (-hopM G t) (fun a => G.dist b a) := by
  intro a z _ haz
  have hadj : G.Adj a z := by
    by_contra hna; apply haz; simp [hopM, hna]
  have := hG.dist_triangle (u := b) (v := z) (w := a)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at this
  exact this

lemma sum_cnt {k : ℕ} (ι : Fin k → Fin N) : ∑ l, cnt ι l = k := by
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (ι j))]
  simp

/-- Configuration energies along `u`. -/
def wC (u : Fin M → ℝ) (s : Conf M N) : ℝ := ∑ i, u i * occF i s

/-- Polynomial version of `gamma_pow_formula`. -/
lemma gamma_pow_poly (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ)
    (u : Fin M → ℝ)
    (y c : Conf M N) (k : ℕ) :
    (Hl (Γ (-hopM G t)) 0 (wC u) ^ k) y c =
      ∑ σ : Equiv.Perm (Fin N), Polynomial.C (Equiv.Perm.sign σ : ℝ) *
        ∑ ι : Fin k → Fin N, ∏ l, (Hl (-hopM G t) 0 u ^ cnt ι l) (τs y l) (τs c (σ.symm l)) := by
  apply Polynomial.funext
  intro lam
  rw [eval_pow_entry, Hl_map_eval]
  have hG : (Γ (-hopM G t) : Matrix (Conf M N) (Conf M N) ℝ) + Matrix.diagonal (lam • wC u) =
      Γ (-hopM G t + Matrix.diagonal (lam • u)) := by
    rw [gamma_add, gamma_diagonal]
    congr 1
    ext s s'
    simp [wC, Matrix.diagonal_apply, Finset.mul_sum, mul_assoc]
  rw [hG, gamma_pow_formula]
  rw [← Polynomial.coe_evalRingHom, map_sum]
  apply Finset.sum_congr rfl; intro σ _
  rw [map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C, ← Polynomial.coe_evalRingHom, map_sum]
  congr 1
  apply Finset.sum_congr rfl; intro ι _
  rw [map_prod]
  apply Finset.prod_congr rfl; intro l _
  rw [Polynomial.coe_evalRingHom, eval_pow_entry, Hl_map_eval]

/-- One term: only optimal assignments reach the top degree. -/
lemma term_coeff {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ) (u : Fin M → ℝ)
    (c y : Conf M N) {k : ℕ} (σ : Equiv.Perm (Fin N)) (ι : Fin k → Fin N) :
    (if mopt G c y ≤ k then
      (∏ l, (Hl (-hopM G t) 0 u ^ cnt ι l) (τs y l) (τs c (σ.symm l))).coeff (k - mopt G c y)
      else 0) =
    if isOpt G c y σ then
      ∏ l, T (-hopM G t) u (fun a => G.dist (τs c (σ.symm l)) a) (τs c (σ.symm l)) (cnt ι l)
          (τs y l)
    else 0 := by
  set P : Fin N → ℝ[X] := fun l => (Hl (-hopM G t) 0 u ^ cnt ι l) (τs y l) (τs c (σ.symm l))
  set dd : Fin N → ℕ := fun l => G.dist (τs c (σ.symm l)) (τs y l)
  have hsumn : ∑ l, cnt ι l = k := sum_cnt ι
  have hsumd : ∑ l, dd l = acost G c (τs y) σ.symm := rfl
  have hmle : mopt G c y ≤ acost G c (τs y) σ.symm := Mopt_le G c (τs y) σ.symm
  have hdeg : ∀ l, (P l).natDegree ≤ cnt ι l - dd l := fun l =>
    entry_natDegree (lip_dist hG t _) (SimpleGraph.dist_self) 0 u (cnt ι l) (τs y l)
  have hT : ∀ l, T (-hopM G t) u (fun a => G.dist (τs c (σ.symm l)) a) (τs c (σ.symm l))
      (cnt ι l) (τs y l) = if dd l ≤ cnt ι l then (P l).coeff (cnt ι l - dd l) else 0 :=
          fun l => rfl
  by_cases hall : ∀ l, dd l ≤ cnt ι l
  · have hle : acost G c (τs y) σ.symm ≤ k := by
      rw [← hsumd, ← hsumn]; exact Finset.sum_le_sum (fun l _ => hall l)
    have hsub : ∑ l, (cnt ι l - dd l) = k - acost G c (τs y) σ.symm := by
      rw [Finset.sum_tsub_distrib _ (fun l _ => hall l), hsumn, hsumd]
    by_cases hopt : isOpt G c y σ
    · rw [ite_eq_left (by omega), ite_eq_left hopt, ← hopt, ← hsub,
        prod_coeff_top _ _ _ (fun l _ => hdeg l)]
      apply Finset.prod_congr rfl; intro l _
      rw [hT l, ite_eq_left (hall l)]
    · rw [ite_eq_right hopt, ite_eq_left (by omega)]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      calc (∏ l, P l).natDegree ≤ ∑ l, (P l).natDegree := Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ l, (cnt ι l - dd l) := Finset.sum_le_sum (fun l _ => hdeg l)
        _ < k - mopt G c y := by
          change acost G c (τs y) σ.symm ≠ mopt G c y at hopt
          rw [hsub]
          omega
  · push Not at hall
    obtain ⟨l0, hl0⟩ := hall
    have hP0 : P l0 = 0 := entry_zero (lip_dist hG t _) (SimpleGraph.dist_self) 0 u hl0
    have hprod : ∏ l, P l = 0 := Finset.prod_eq_zero (Finset.mem_univ l0) hP0
    rw [show (∏ l, (Hl (-hopM G t) 0 u ^ cnt ι l) (τs y l) (τs c (σ.symm l))) = ∏ l, P l from rfl,
      hprod, coeff_zero, ite_self]
    split_ifs with h
    · symm; apply Finset.prod_eq_zero (Finset.mem_univ l0)
      rw [hT l0, ite_eq_right (by omega)]
    · rfl

/-- **Leading coefficient of free fermions = signed sum over optimal assignments of products of
single-particle leading coefficients.** -/
theorem T_MB_formula {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    (u : Fin M → ℝ) (c y : Conf M N) (k : ℕ) :
    T (Γ (-hopM G t)) (wC u) (mopt G c) c k y =
      ∑ σ ∈ Finset.univ.filter (isOpt G c y),
        (Equiv.Perm.sign σ : ℝ) * ∑ ι : Fin k → Fin N, ∏ l,
          T (-hopM G t) u (fun a => G.dist (τs c (σ.symm l)) a) (τs c (σ.symm l)) (cnt ι l)
            (τs y l) := by
  have hT : T (Γ (-hopM G t)) (wC u) (mopt G c) c k y =
      if mopt G c y ≤ k then ((Hl (Γ (-hopM G t)) 0 (wC u) ^ k) y c).coeff (k - mopt G c y)
      else 0 := rfl
  rw [hT, gamma_pow_poly, Finset.sum_filter]
  split_ifs with hk
  · rw [finsetSum_coeff]
    apply Finset.sum_congr rfl; intro σ _
    rw [coeff_C_mul, finsetSum_coeff]
    have := fun ι : Fin k → Fin N => term_coeff hG t u c y σ ι
    simp only [ite_eq_left hk] at this
    split_ifs with hopt
    · congr 1; apply Finset.sum_congr rfl; intro ι _
      rw [this ι, ite_eq_left hopt]
    · rw [Finset.sum_eq_zero (fun ι _ => by rw [this ι, ite_eq_right hopt]), mul_zero]
  · symm
    apply Finset.sum_eq_zero; intro σ _
    split_ifs with hopt
    · rw [Finset.sum_eq_zero, mul_zero]
      intro ι _
      have := term_coeff hG t u c y σ ι
      rw [ite_eq_right hk, ite_eq_left hopt] at this
      exact this.symm
    · rfl

end

section

open Matrix Polynomial

variable {M N : ℕ}

lemma words_pow (x : Fin N → ℝ) (k : ℕ) :
    ∑ ι : Fin k → Fin N, ∏ l, x l ^ cnt ι l = (∑ l, x l) ^ k := by
  induction k with
  | zero => simp [cnt]
  | succ k ih =>
    rw [← (Fin.snocEquiv (fun _ => Fin N)).sum_comp, Fintype.sum_prod_type, pow_succ, ← ih,
      Finset.sum_mul, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ι _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [Fin.snocEquiv_apply]
    simp_rw [cnt_snoc, pow_add]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · intro h; exact absurd (Finset.mem_univ i) h

/-- Single-particle divided-difference coefficients for the hop `c_{σ⁻¹ l} → y_l`. -/
noncomputable def βsp (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    (u : Fin M → ℝ) (hu : Function.Injective u) (c y : Conf M N) (σ : Equiv.Perm (Fin N))
        (l : Fin N) :
    Fin M → ℝ :=
  alphaRep (-hopM G t) u hu (fun a => G.dist (τs c (σ.symm l)) a) (lip_dist hG t _)
    (τs c (σ.symm l)) SimpleGraph.dist_self (τs y l)

theorem T_MB_powersum {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    (u : Fin M → ℝ) (hu : Function.Injective u) (c y : Conf M N) (k : ℕ) :
    T (Γ (-hopM G t)) (wC u) (mopt G c) c k y =
      ∑ σ ∈ Finset.univ.filter (isOpt G c y),
        (Equiv.Perm.sign σ : ℝ) * ∑ z : Fin N → Fin M,
          (∏ l, βsp G hG t u hu c y σ l (z l)) * (∑ l, u (z l)) ^ k := by
  rw [T_MB_formula hG t u c y k]
  apply Finset.sum_congr rfl; intro σ _
  congr 1
  simp_rw [alphaRep_rep hu (lip_dist hG t _) SimpleGraph.dist_self]
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  simp_rw [Finset.prod_mul_distrib]
  rw [← Finset.mul_sum, words_pow]
  rfl


/-- Assignment rigidity: a non-vanishing term with target positions permuted by `ρ` forces `ρ = 1`.
-/
lemma assign_rigid {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    (u : Fin M → ℝ) (hu : Function.Injective u) (c y : Conf M N) (σ : Equiv.Perm (Fin N))
    (hopt : isOpt G c y σ) (ρ : Equiv.Perm (Fin N))
    (hβ : ∏ l, βsp G hG t u hu c y σ l (τs y (ρ l)) ≠ 0) : ρ = 1 := by
  have hfac : ∀ l, τs y (ρ l) = τs y l ∨
      G.dist (τs c (σ.symm l)) (τs y (ρ l)) < G.dist (τs c (σ.symm l)) (τs y l) := by
    intro l
    have hne : βsp G hG t u hu c y σ l (τs y (ρ l)) ≠ 0 := fun h0 =>
      hβ (Finset.prod_eq_zero (Finset.mem_univ l) h0)
    exact alphaRep_supp hu (lip_dist hG t _) SimpleGraph.dist_self _ _ hne
  have hle : ∀ l, G.dist (τs c (σ.symm l)) (τs y (ρ l)) ≤ G.dist (τs c (σ.symm l)) (τs y l) := by
    intro l; rcases hfac l with h | h
    · rw [h]
    · exact h.le
  have hcost : acost G c (τs y) σ.symm ≤ acost G c (fun l => τs y (ρ l)) σ.symm := by
    rw [hopt]
    calc mopt G c y = Mopt G c (fun l => τs y (ρ l)) := (Mopt_perm G c (τs y) ρ).symm
      _ ≤ _ := Mopt_le _ _ _ _
  refine Equiv.ext fun l => ?_
  by_contra hl
  have hstrict : acost G c (fun l => τs y (ρ l)) σ.symm < acost G c (τs y) σ.symm := by
    apply Finset.sum_lt_sum (fun l _ => hle l)
    refine ⟨l, Finset.mem_univ l, (hfac l).resolve_left ?_⟩
    intro h; apply hl; simpa using (τs_injective y h)
  omega

/-- **α_y(y) equals the Slater-type sum over optimal assignments.** -/
theorem alpha_eq_D {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    (u : Fin M → ℝ) (hu : Function.Injective u) (hw : Function.Injective (wC u : Conf M N → ℝ))
    (c y : Conf M N)
    (hgen : ∀ z : Fin N → Fin M, ∑ l, u (z l) = wC u y →
        ∃ ρ : Equiv.Perm (Fin N), ∀ l, z l = τs y (ρ l)) :
    alphaRep (Γ (-hopM G t)) (wC u) hw (mopt G c) (lip_mopt hG t c) c (mopt_self G c) y y =
      ∑ σ ∈ Finset.univ.filter (isOpt G c y),
        (Equiv.Perm.sign σ : ℝ) * ∏ l, βsp G hG t u hu c y σ l (τs y l) := by
  classical
  set opt := isOpt G c y
  set b : Equiv.Perm (Fin N) × (Fin N → Fin M) → ℝ := fun p =>
    if opt p.1 then (Equiv.Perm.sign p.1 : ℝ) * ∏ l, βsp G hG t u hu c y p.1 l (p.2 l) else 0
  set yv : Equiv.Perm (Fin N) × (Fin N → Fin M) → ℝ := fun p => ∑ l, u (p.2 l)
  have h : ∀ k : ℕ, ∑ s, alphaRep (Γ (-hopM G t)) (wC u) hw (mopt G c) (lip_mopt hG t c) c
      (mopt_self G c) y s * wC u s ^ k = ∑ p, b p * yv p ^ k := by
    intro k
    rw [← alphaRep_rep, T_MB_powersum hG t u hu c y k, Fintype.sum_prod_type, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro σ _
    simp only [b, yv]
    split_ifs with ho
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    · simp
  have hu_y : ∑ l, u (τs y l) = wC u y := by rw [sum_tau]; rfl
  have key := ps_unique _ _ _ _ h (wC u y)
  -- left side: only `s = y`
  have hL : ∑ s ∈ Finset.univ.filter (fun s => wC u s = wC u y),
      alphaRep (Γ (-hopM G t)) (wC u) hw (mopt G c) (lip_mopt hG t c) c (mopt_self G c) y s =
      alphaRep (Γ (-hopM G t)) (wC u) hw (mopt G c) (lip_mopt hG t c) c (mopt_self G c) y y := by
    rw [Finset.sum_eq_single y]
    · intro s hs hsy; exact absurd (hw (Finset.mem_filter.mp hs).2) hsy
    · intro h0; simp at h0
  -- right side: only `z = τs y`
  have hR : ∑ p ∈ Finset.univ.filter (fun p => yv p = wC u y), b p =
      ∑ σ, b (σ, τs y) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro σ _
    rw [Finset.sum_eq_single (τs y)]
    · simp [yv, hu_y]
    · intro z _ hz
      split_ifs with hzy
      · obtain ⟨ρ, hρ⟩ := hgen z hzy
        simp only [b]
        split_ifs with ho
        · have hz' : z = fun l => τs y (ρ l) := funext hρ
          by_contra hne
          have hprod : ∏ l, βsp G hG t u hu c y σ l (z l) ≠ 0 := by
            intro h0; apply hne; rw [h0, mul_zero]
          rw [hz'] at hprod
          have := assign_rigid hG t u hu c y σ ho ρ hprod
          apply hz; rw [hz', this]; rfl
        · rfl
      · rfl
    · intro h0; exact absurd (Finset.mem_univ _) h0
  rw [← hL, key, hR, Finset.sum_filter]

end

end DFT
