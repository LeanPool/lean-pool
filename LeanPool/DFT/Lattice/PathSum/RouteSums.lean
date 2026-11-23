/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.PathSum.FreeFermions
public import LeanPool.DFT.Lattice.StrongPotential.Resolvent
meta import Mathlib.Tactic.Linarith

/-!
# Explicit single-particle route sums

Layer-recursive route sums `Gr`, `alphaExp` (defined for every potential), with
`alphaRep_eq_alphaExp` and the explicit Slater-type sum `DExp` (`D_eq_DExp`).
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {M N : ℕ}

section
variable (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ) (u : Fin M → ℝ)

/-- A hopping-weighted sum over adjacent sites whose distance from the base passes a layer test. -/
noncomputable abbrev predecessorSum (b p : Fin M) (layer : ℕ → Prop) [DecidablePred layer]
    (f : Fin M → ℝ) : ℝ :=
  ∑ q, if G.Adj p q ∧ layer (G.dist b q) then -t p q * f q else 0

/-- Layered resolvent route sums. -/
noncomputable def Gr (b a : Fin M) : ℕ → Fin M → ℝ
  | 0, p => if p = b then 1 / (u a - u b) else 0
  | n + 1, p => if G.dist b p = n + 1 then
      predecessorSum G t b p (· = n) (Gr b a n) / (u a - u p) else 0

/-- The leading one-body coefficient assembled from shortest-route sums. -/
noncomputable def alphaExp (b a : Fin M) : ℝ :=
  (if a = b then 1 else 0) +
    predecessorSum G t b a (fun depth => depth + 1 = G.dist b a)
      (fun p => Gr G t u b a (G.dist b p) p)

end

lemma dist_eq_zero_iff {G : SimpleGraph (Fin M)} (hG : G.Connected) {b p : Fin M} :
    G.dist b p = 0 ↔ p = b := by
  rw [(hG.preconnected b p).dist_eq_zero_iff]; exact eq_comm

private lemma sum_erase_hopM_eq_predecessorSum {G : SimpleGraph (Fin M)}
    [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ) (b p : Fin M)
    (layer : ℕ → Prop) [DecidablePred layer] (f g : Fin M → ℝ)
    (h : ∀ q, G.Adj p q → layer (G.dist b q) → f q = g q) :
    (∑ q ∈ Finset.univ.erase p, if layer (G.dist b q) then (-hopM G t) p q * f q else 0) =
      predecessorSum G t b p layer g := by
  unfold predecessorSum
  rw [← Finset.sum_erase Finset.univ (a := p)
    (f := fun q => if G.Adj p q ∧ layer (G.dist b q) then -t p q * g q else 0) (by simp)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases ha : G.Adj p q
  · by_cases hl : layer (G.dist b q)
    · simp [hopM, ha, hl, h q ha hl]
    · simp [hl]
  · simp [hopM, ha]

theorem Fres_eq_Gr {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    {u : Fin M → ℝ} (hu : Function.Injective u) (b a : Fin M) :
    ∀ n p, G.dist b p = n → n < G.dist b a →
      Fres hu (lip_dist hG t b) (SimpleGraph.dist_self (v := b)) p (u a) = Gr G t u b a n p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    have hpb : p = b := (dist_eq_zero_iff hG).mp hp
    subst hpb
    have hrec := Fres_rec hu (lip_dist hG t p) (SimpleGraph.dist_self (v := p)) p (u a)
      (fun z hz => by
        intro h; have := hu h; subst this; rw [hp] at hz; omega)
    have hsum : ∑ q ∈ Finset.univ.erase p, (if G.dist p q + 1 = G.dist p p then
        (-hopM G t) p q * Fres hu (lip_dist hG t p) (SimpleGraph.dist_self (v := p)) q (u a)
        else 0) = 0 := by
      apply Finset.sum_eq_zero; intro q _; rw [SimpleGraph.dist_self]; simp
    rw [hsum, ite_eq_left rfl, add_zero] at hrec
    have hne : u a - u p ≠ 0 := sub_ne_zero.mpr (fun h => by
      have := hu h; subst this; rw [hp] at *; omega)
    have hG0 : Gr G t u p a 0 p = 1 / (u a - u p) := by simp [Gr]
    rw [hG0, eq_div_iff hne]
    linarith
  | succ n ih =>
    intro p hp hlt
    have hpb : p ≠ b := by intro h; subst h; rw [SimpleGraph.dist_self] at hp; omega
    have hx : ∀ z, G.dist b z ≤ G.dist b p → u a ≠ u z := by
      intro z hz h; have := hu h; subst this; omega
    have hrec := Fres_rec hu (lip_dist hG t b) (SimpleGraph.dist_self (v := b)) p (u a) hx
    rw [ite_eq_right hpb, zero_add] at hrec
    have hne : u a - u p ≠ 0 := sub_ne_zero.mpr (hx p le_rfl)
    have hGs : Gr G t u b a (n + 1) p =
        predecessorSum G t b p (fun depth => depth + 1 = G.dist b p) (Gr G t u b a n) /
          (u a - u p) := by
      simp [Gr, hp]
    rw [hGs, eq_div_iff hne, hrec]
    refine sum_erase_hopM_eq_predecessorSum t b p (fun depth => depth + 1 = G.dist b p)
      (fun q => Fres hu (lip_dist hG t b) (SimpleGraph.dist_self (v := b)) q (u a))
      (Gr G t u b a n) ?_
    intro q _ hdq
    exact ih q (by omega) (by omega)

theorem alphaRep_eq_alphaExp {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    {u : Fin M → ℝ} (hu : Function.Injective u) (b a : Fin M) :
    alphaRep (-hopM G t) u hu (fun z => G.dist b z) (lip_dist hG t b) b
      (SimpleGraph.dist_self (v := b)) a a = alphaExp G t u b a := by
  rw [alpha_diag, alphaExp]
  congr 1
  refine sum_erase_hopM_eq_predecessorSum t b a (fun depth => depth + 1 = G.dist b a)
    (fun p => Fres hu (lip_dist hG t b) (SimpleGraph.dist_self (v := b)) p (u a))
    (fun p => Gr G t u b a (G.dist b p) p) ?_
  intro p _ hd
  exact Fres_eq_Gr hG t hu b a _ p rfl (by omega)

/-- Explicit Slater-type sum. -/
noncomputable def DExp (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ)
    (u : Fin M → ℝ)
    (c y : Conf M N) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (isOpt G c y),
    (Equiv.Perm.sign σ : ℝ) * ∏ l, alphaExp G t u (τs c (σ.symm l)) (τs y l)

theorem D_eq_DExp {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    (t : Fin M → Fin M → ℝ)
    {u : Fin M → ℝ} (hu : Function.Injective u) (c y : Conf M N) :
    ∑ σ ∈ Finset.univ.filter (isOpt G c y),
      (Equiv.Perm.sign σ : ℝ) * ∏ l, βsp G hG t u hu c y σ l (τs y l) = DExp G t u c y := by
  apply Finset.sum_congr rfl; intro σ _
  congr 1
  apply Finset.prod_congr rfl; intro l _
  exact alphaRep_eq_alphaExp hG t hu _ _

end

end DFT
