/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspChain
public import LeanPool.HyperellipticCurves.Log.Fold.MomentDet

import LeanPool.HyperellipticCurves.Log.Fold.CuspBase
import LeanPool.HyperellipticCurves.Log.Fold.CuspWitness

/-!
# The generic cuspidal fold chain

This file runs the cuspidal fold chain `ChabautyColeman.cuspChain` with its **generic
scalars** and discharges all of its composition conditions and avoidance values from the
nonvanishing of the value atoms — the certificate interface of `thm:cusp-witness`.

The initial step is special: stage `0` composes a node of the base support (the fold adds
`P_1` to a state containing `P_1`), so it is the single **doubling** step of
`def:centre-fold` — its scalar `H₀` and its composition condition come from the tangency
data and are *supplied*, not derived from an atom. From stage `1` on the steps are
disjoint and the scalar is the field-division value `H_j = (t_j^N - V_j(t_j²))/U_j(t_j²)`
of the chain itself.

* `ChabautyColeman.cuspChain_congr_H`: the chain reads its scalar sequence only below the
  current stage, so the self-referential scalar sequence `ChabautyColeman.cuspGenH`
  (supplied `H₀`, then the generic values) is well defined by strong recursion over a
  truncation, with defining property `ChabautyColeman.cuspGenH_succ`.
* `ChabautyColeman.cuspChain_cond_of_atoms` — **the chain induction**: given the base
  state, `A₀(0) ≠ 0`, nonzero nodes, the doubling condition at stage `0`, and the
  nonvanishing of the zero-node, step− and step+ value atoms of the stage alphabets for
  `1 ≤ j < g`, all composition conditions and all interior avoidance values `A_j(0)` hold
  up to stage `g`. The step atoms produce the disjointness values `A_j(±t_j)` through
  `ChabautyColeman.eval_ne_zero_of_momentDet_ne_zero` — no moment-matrix invertibility is
  needed anywhere.
* `ChabautyColeman.isCuspState_cuspChain_of_atoms`,
  `ChabautyColeman.cuspChain_congruence_of_atoms`,
  `ChabautyColeman.cuspChain_eval_ne_zero_of_atoms`: the packaged consequences — the chain
  invariants, the master congruence, and the general value-extraction interface (any state
  evaluation whose value atom is nonzero is itself nonzero), which the step, avoidance and
  mirror conditions of `thm:cusp-witness` instantiate.

The atom hypotheses are stated directly at the stage alphabets
`(-1)^g·A₀·∏_(i<j)(tᵢ - X)`; identifying them with the doubles-and-singles atoms of
`LeanPool.HyperellipticCurves.Log.Fold.GenericAtom` (via `ChabautyColeman.cusp_alphabet_comp_neg`)
is the
concern of the instantiation at generic nodes, not of the chain induction.
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section CongrH

variable {R : Type*} [CommRing R] {g : ℕ} {U₀ V₀ A₀ : R[X]} {t : ℕ → R}

/-- The fold chain reads its node and scalar sequences only below the current stage. -/
theorem cuspChain_congr {t' H H' : ℕ → R} {m : ℕ} (ht : ∀ i < m, t i = t' i)
    (hH : ∀ i < m, H i = H' i) :
    cuspChain g U₀ V₀ A₀ t H m = cuspChain g U₀ V₀ A₀ t' H' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cuspChain_succ, cuspChain_succ,
      ih (fun i hi ↦ ht i (by lia)) fun i hi ↦ hH i (by lia), ht m (by lia), hH m (by lia)]

/-- The fold chain reads its scalar sequence only below the current stage. -/
theorem cuspChain_congr_H {H H' : ℕ → R} {m : ℕ} (h : ∀ i < m, H i = H' i) :
    cuspChain g U₀ V₀ A₀ t H m = cuspChain g U₀ V₀ A₀ t H' m :=
  cuspChain_congr (fun _ _ ↦ rfl) h

end CongrH

section GenH

variable {F : Type*} [Field F] {g : ℕ}

/-- **The generic fold scalars**: the supplied doubling scalar `H₀` at the initial
(doubling) step, and from stage `1` on the field-division value
`H_j = (t_j^N - V_j(t_j²))/U_j(t_j²)` of the chain run with the earlier scalars. -/
noncomputable def cuspGenH (g : ℕ) (U₀ V₀ A₀ : F[X]) (t : ℕ → F) (H₀ : F) : ℕ → F
  | 0 => H₀
  | j + 1 =>
    let s := cuspChain g U₀ V₀ A₀ t
      (fun i ↦ if _ : i < j + 1 then cuspGenH g U₀ V₀ A₀ t H₀ i else 0) (j + 1)
    (t (j + 1) ^ (2 * g + 1) - s.2.1.eval (t (j + 1) ^ 2)) / s.1.eval (t (j + 1) ^ 2)
  decreasing_by assumption

variable {U₀ V₀ A₀ : F[X]} {t : ℕ → F} {H₀ : F}

@[simp] theorem cuspGenH_zero : cuspGenH g U₀ V₀ A₀ t H₀ 0 = H₀ := by rw [cuspGenH]

/-- The defining property of the generic scalars beyond the initial step, with the
truncation replaced by the full scalar sequence. -/
theorem cuspGenH_succ (j : ℕ) :
    cuspGenH g U₀ V₀ A₀ t H₀ (j + 1)
      = (t (j + 1) ^ (2 * g + 1)
          - (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) (j + 1)).2.1.eval
              (t (j + 1) ^ 2))
        / (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) (j + 1)).1.eval
            (t (j + 1) ^ 2) := by
  rw [cuspGenH, show cuspChain g U₀ V₀ A₀ t
      (fun i ↦ if _ : i < j + 1 then cuspGenH g U₀ V₀ A₀ t H₀ i else 0) (j + 1)
    = cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) (j + 1) from
    cuspChain_congr_H fun i hi ↦ dite_eq_left hi]

/-- The generic scalar sequence reads the node sequence only up to the current stage. -/
theorem cuspGenH_congr {t' : ℕ → F} (m : ℕ) (ht : ∀ i ≤ m, t i = t' i) :
    cuspGenH g U₀ V₀ A₀ t H₀ m = cuspGenH g U₀ V₀ A₀ t' H₀ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp
    | j + 1 =>
      rw [cuspGenH, cuspGenH,
        cuspChain_congr (t' := t')
          (H' := fun i ↦ if _ : i < j + 1 then cuspGenH g U₀ V₀ A₀ t' H₀ i else 0)
          (fun i hi ↦ ht i (by lia)) (fun i hi ↦ by
            rw [dite_eq_left hi, dite_eq_left hi, ih i hi fun l hl ↦ ht l (by lia)]),
        ht (j + 1) le_rfl]

end GenH

section ChainInduction

variable {F : Type*} [Field F] {g : ℕ} {U₀ V₀ A₀ : F[X]} {t : ℕ → F} {H₀ : F}

private theorem d0_congruence (g : ℕ) (A₀ : F[X]) :
    X ^ (2 * g + 1) ∣ A₀ * ((-1) ^ g * A₀).comp (-X) - A₀.comp (-X) * ((-1) ^ g * A₀) := by
  rw [show A₀ * ((-1) ^ g * A₀).comp (-X) - A₀.comp (-X) * ((-1) ^ g * A₀) = 0 by
    simp only [mul_comp, pow_comp, neg_comp, one_comp]
    ring]
  exact dvd_zero _

/-- **The chain induction** (`thm:cusp-witness`, chain part): with the generic scalars,
all composition conditions and all interior avoidance values `A_j(0)` of the cuspidal fold
hold up to stage `g`, given the base state, the initial **doubling** step's composition
condition (stage `0` composes a node of the base support, so its condition comes from the
tangency data, not from an atom), and the nonvanishing of the value atoms of the later
stages (the zero-node, step− and step+ pattern determinants of the stage alphabets). -/
theorem cuspChain_cond_of_atoms (h2 : (2 : F) ≠ 0) (hg : 0 < g)
    (hbase : IsCuspState g U₀ V₀ A₀) (ht0 : ∀ j < g, t j ≠ 0) (hA00 : A₀.eval 0 ≠ 0)
    (hok0 : A₀ * (X - C (t 0))
      ∣ X ^ (2 * g + 1) - (V₀ + C H₀ * U₀).comp (X ^ 2))
    (hzero : ∀ j, 1 ≤ j → j < g → momentDet g
      (((-1) ^ g * A₀ * ∏ i ∈ Finset.range j, (C (t i) - X)).comp (-X) * X)
      (fun m ↦ (m : ℕ)) ≠ 0)
    (hpair : ∀ j, 1 ≤ j → j < g → momentDet g
      (((-1) ^ g * A₀ * ∏ i ∈ Finset.range j, (C (t i) - X)).comp (-X) * (C (-t j) + X))
      (fun m ↦ (m : ℕ)) ≠ 0)
    (hplus : ∀ j, 1 ≤ j → j < g → momentDet g
      (((-1) ^ g * A₀ * ∏ i ∈ Finset.range j, (C (t i) - X)).comp (-X) * (C (t j) + X))
      (fun m ↦ (m : ℕ)) ≠ 0)
    {m : ℕ} (hm : m ≤ g) :
    (∀ j < m,
        (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) j).2.2 * (X - C (t j))
        ∣ X ^ (2 * g + 1)
          - ((cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) j).2.1
            + C (cuspGenH g U₀ V₀ A₀ t H₀ j)
              * (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) j).1).comp (X ^ 2))
      ∧ ∀ j < m,
        ((cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) j).2.2).eval 0 ≠ 0 := by
  induction m with
  | zero =>
    exact ⟨fun j hj ↦ absurd hj (Nat.not_lt_zero j), fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  | succ m ih =>
    obtain ⟨hok, hA0⟩ := ih (by lia)
    have hst := isCuspState_cuspChain hbase hok
    have hcong := cuspChain_moment_congruence hbase hok hA0 (fun j hj ↦ ht0 j (by lia))
      (d0_congruence g A₀)
    -- the composition condition and interior avoidance value at stage `m`
    have hokm : (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.2 * (X - C (t m))
        ∣ X ^ (2 * g + 1)
          - ((cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.1
            + C (cuspGenH g U₀ V₀ A₀ t H₀ m)
              * (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).1).comp
            (X ^ 2) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · -- the initial doubling step: the supplied condition
        rwa [cuspChain_zero, cuspGenH_zero]
      · -- a generic disjoint step: the disjointness values come from the step atoms
        have hAt := eval_ne_zero_of_momentDet_ne_zero h2 hg hst.monicA hst.natDegree_A
          hcong (w := -t m) (hpair m hm1 (by lia))
        rw [neg_neg] at hAt
        have hAmt := eval_ne_zero_of_momentDet_ne_zero h2 hg hst.monicA hst.natDegree_A
          hcong (w := t m) (hplus m hm1 (by lia))
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by lia⟩
        rw [cuspGenH_succ]
        exact cuspStep_cond_of_generic hst hAt hAmt
    have hA0m :
        ((cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.2).eval 0 ≠ 0 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · exact hA00
      · have h1 := eval_ne_zero_of_momentDet_ne_zero h2 hg hst.monicA hst.natDegree_A
          hcong (w := 0) (by
            rw [show (C (0 : F) + X : F[X]) = X by simp]
            exact hzero m hm1 (by lia))
        rwa [neg_zero] at h1
    refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hok j hj'
      · exact hokm
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hA0 j hj'
      · exact hA0m

variable (h2 : (2 : F) ≠ 0) (hg : 0 < g) (hbase : IsCuspState g U₀ V₀ A₀)
  (ht0 : ∀ j < g, t j ≠ 0) (hA00 : A₀.eval 0 ≠ 0)
  (hok0 : A₀ * (X - C (t 0)) ∣ X ^ (2 * g + 1) - (V₀ + C H₀ * U₀).comp (X ^ 2))
  (hzero : ∀ j, 1 ≤ j → j < g → momentDet g
    (((-1) ^ g * A₀ * ∏ i ∈ Finset.range j, (C (t i) - X)).comp (-X) * X)
    (fun m ↦ (m : ℕ)) ≠ 0)
  (hpair : ∀ j, 1 ≤ j → j < g → momentDet g
    (((-1) ^ g * A₀ * ∏ i ∈ Finset.range j, (C (t i) - X)).comp (-X) * (C (-t j) + X))
    (fun m ↦ (m : ℕ)) ≠ 0)
  (hplus : ∀ j, 1 ≤ j → j < g → momentDet g
    (((-1) ^ g * A₀ * ∏ i ∈ Finset.range j, (C (t i) - X)).comp (-X) * (C (t j) + X))
    (fun m ↦ (m : ℕ)) ≠ 0)

include h2 hg hbase ht0 hA00 hok0 hzero hpair hplus

/-- The chain invariants hold at every stage of the generic fold, from the atom
certificates alone. -/
theorem isCuspState_cuspChain_of_atoms {m : ℕ} (hm : m ≤ g) :
    IsCuspState g (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).1
      (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.1
      (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.2 :=
  isCuspState_cuspChain hbase
    (cuspChain_cond_of_atoms h2 hg hbase ht0 hA00 hok0 hzero hpair hplus hm).1

/-- The master congruence holds at every stage of the generic fold, from the atom
certificates alone. -/
theorem cuspChain_congruence_of_atoms {m : ℕ} (hm : m ≤ g) :
    X ^ (2 * g + 1) ∣ (cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.2
        * ((-1) ^ g * A₀ * ∏ i ∈ Finset.range m, (C (t i) - X)).comp (-X)
      - ((cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.2).comp (-X)
        * ((-1) ^ g * A₀ * ∏ i ∈ Finset.range m, (C (t i) - X)) := by
  obtain ⟨hok, hA0⟩ :=
    cuspChain_cond_of_atoms h2 hg hbase ht0 hA00 hok0 hzero hpair hplus hm
  exact cuspChain_moment_congruence hbase hok hA0 (fun j hj ↦ ht0 j (by lia))
    (d0_congruence g A₀)

/-- **Value extraction along the generic fold**: every state evaluation whose value atom is
a nonzero pattern determinant is itself nonzero — the interface consumed by the step,
avoidance and mirror conditions of `thm:cusp-witness`. -/
theorem cuspChain_eval_ne_zero_of_atoms {m : ℕ} (hm : m ≤ g) {w : F}
    (hne : momentDet g (((-1) ^ g * A₀ * ∏ i ∈ Finset.range m, (C (t i) - X)).comp (-X)
      * (C w + X)) (fun m ↦ (m : ℕ)) ≠ 0) :
    ((cuspChain g U₀ V₀ A₀ t (cuspGenH g U₀ V₀ A₀ t H₀) m).2.2).eval (-w) ≠ 0 :=
  eval_ne_zero_of_momentDet_ne_zero h2 hg
    (isCuspState_cuspChain_of_atoms h2 hg hbase ht0 hA00 hok0 hzero hpair hplus
      hm).monicA
    (isCuspState_cuspChain_of_atoms h2 hg hbase ht0 hA00 hok0 hzero hpair hplus
      hm).natDegree_A
    (cuspChain_congruence_of_atoms h2 hg hbase ht0 hA00 hok0 hzero hpair hplus hm)
    hne

end ChainInduction

end ChabautyColeman

end
