/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspBase
public import LeanPool.HyperellipticCurves.Log.Fold.CuspGeneric

import LeanPool.HyperellipticCurves.Log.Fold.CuspWitness
import LeanPool.HyperellipticCurves.Log.Fold.GenericAtom

/-!
# The cuspidal witness over the function field

This file instantiates the generic cuspidal fold chain of
`LeanPool.HyperellipticCurves.Log.Fold.CuspGeneric` at the **generic nodes** — the variables of
`MvPolynomial ℕ k` viewed in its fraction field (`ChabautyColeman.genNode`) — and
discharges every certificate hypothesis, proving the phase-1 chain part of
`thm:cusp-witness`:

* the base facts: `ChabautyColeman.genNode_ne_zero`,
  `ChabautyColeman.genNode_sq_injective`, `ChabautyColeman.eval_zero_genA₀_ne_zero`;
* the atom certificates: `ChabautyColeman.genNode_zero_atom_ne_zero`,
  `ChabautyColeman.genNode_pair_atom_ne_zero`,
  `ChabautyColeman.genNode_plus_atom_ne_zero`,
  `ChabautyColeman.genNode_trio_atom_ne_zero`,
  `ChabautyColeman.genNode_tripled_atom_ne_zero`
  — each stage alphabet is identified as a doubles-and-singles product by
  `ChabautyColeman.cusp_alphabet_comp_neg` (the step+ atom is the next stage's avoidance
  alphabet, the step− atom completes the extension node's single to the signed pair, and
  the mirror atoms complete the last-added double to the signed trio resp. the tripled
  node via `ChabautyColeman.doublesPoly_succ_left`), and the resulting pattern
  determinant is the `algebraMap`-image of the corresponding fold-order atom of
  `LeanPool.HyperellipticCurves.Log.Fold.GenericAtom`, nonzero by injectivity
  (`IsFractionRing.injective`);
* the assembly: `ChabautyColeman.genCuspChain` (the chain at the base datum
  `ChabautyColeman.genU₀`/`genV₀`/`genA₀`) and
  `ChabautyColeman.exists_genCuspChain_witness` — **there is a doubling scalar `H₀` such
  that along the generic cuspidal fold every stage satisfies the fold invariants, every
  interior avoidance value `A_m(0)` is nonzero, every composition condition holds, and
  every state evaluation with a nonzero value atom is nonzero** (the interface the step,
  avoidance and mirror conditions instantiate; the mirror atoms are consumed by the
  phase-2 stages of `LeanPool.HyperellipticCurves.Log.Fold.CuspMirror`, which retrace the phase-1
  states).
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section CuspField

variable (k : Type*) [Field k]

/-- The generic nodes: the variables of `MvPolynomial ℕ k`, viewed in its fraction
field. -/
noncomputable def genNode (m : ℕ) : FractionRing (MvPolynomial ℕ k) :=
  algebraMap (MvPolynomial ℕ k) _ (MvPolynomial.X m)

variable {k}

private theorem algebraMap_injective :
    Function.Injective
      (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))) :=
  IsFractionRing.injective _ _

/-- `2 ≠ 0` in the function field over a coefficient field of characteristic `≠ 2`. -/
theorem two_ne_zero_fractionRing [NeZero (2 : k)] :
    (2 : FractionRing (MvPolynomial ℕ k)) ≠ 0 := by
  have h := ((algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))).comp
    MvPolynomial.C).injective
  have h2 := (map_ne_zero_iff _ h).mpr (NeZero.ne (2 : k))
  rwa [map_ofNat] at h2

theorem genNode_ne_zero (m : ℕ) : genNode k m ≠ 0 := by
  rw [genNode, map_ne_zero_iff _ algebraMap_injective]
  exact MvPolynomial.X_ne_zero m

theorem genNode_sq_injective {g : ℕ} :
    Function.Injective fun i : Fin g ↦ genNode k (i : ℕ) ^ 2 := by
  intro a b hab
  simp only [genNode, ← map_pow] at hab
  have h1 := algebraMap_injective hab
  by_contra hne
  have hne' : ¬(b : ℕ) = (a : ℕ) := fun h ↦ hne (Fin.ext h.symm)
  have h2 := congrArg (MvPolynomial.aeval fun m ↦ if m = (a : ℕ) then (1 : k) else 0) h1
  simp [hne'] at h2

end CuspField

section Atoms

variable {k : Type*} [Field k] {g : ℕ}

/-- Nonvanishing of pattern determinants transports into the fraction field. -/
theorem momentDet_algebraMap_ne_zero (q : (MvPolynomial ℕ k)[X])
    (hq : momentDet g q (fun m ↦ (m : ℕ)) ≠ 0) :
    momentDet g (q.map (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
      (fun m ↦ (m : ℕ)) ≠ 0 := by
  rw [momentDet_map]
  exact (map_ne_zero_iff _ algebraMap_injective).mpr hq

/-- **The zero atoms at the generic nodes**: the `hzero` hypothesis of the chain
induction. -/
theorem genNode_zero_atom_ne_zero [NeZero (2 : k)] {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ g) :
    momentDet g (((-1) ^ g * tupleU (fun i : Fin g ↦ genNode k i)
        * ∏ i ∈ Finset.range j, (Polynomial.C (genNode k i) - X)).comp (-X) * X)
      (fun m ↦ (m : ℕ)) ≠ 0 := by
  rw [cusp_alphabet_comp_neg (fun m ↦ genNode k m) hj]
  have hmap : ((doublesPoly (fun l ↦ (MvPolynomial.X (j - 1 - l) : MvPolynomial ℕ k))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) j (g - j) * X).map
          (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
      = doublesPoly (fun l ↦ genNode k (j - 1 - l)) (fun i ↦ genNode k (g - 1 - i))
          j (g - j) * X := by
    simp only [Polynomial.map_mul, doublesPoly_map, Polynomial.map_X, genNode]
  rw [← hmap]
  exact momentDet_algebraMap_ne_zero _ (momentDet_generic_doubles_mul_X_ne_zero hj1 hj)

/-- **The step− atoms at the generic nodes**: the `hpair` hypothesis of the chain
induction. -/
theorem genNode_pair_atom_ne_zero [NeZero (2 : k)] {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < g) :
    momentDet g (((-1) ^ g * tupleU (fun i : Fin g ↦ genNode k i)
        * ∏ i ∈ Finset.range j, (Polynomial.C (genNode k i) - X)).comp (-X)
      * (Polynomial.C (-genNode k j) + X)) (fun m ↦ (m : ℕ)) ≠ 0 := by
  rw [cusp_alphabet_comp_neg (fun m ↦ genNode k m) hj.le,
    show (Polynomial.C (-genNode k j) + X : (FractionRing (MvPolynomial ℕ k))[X])
      = X - Polynomial.C (genNode k j) by rw [map_neg]; ring,
    show g - j = g - j - 1 + 1 by lia, doublesPoly_succ_right,
    show g - 1 - (g - j - 1) = j by lia, mul_assoc,
    show (Polynomial.C (genNode k j) + X) * (X - Polynomial.C (genNode k j))
      = X ^ 2 - Polynomial.C (genNode k j ^ 2) by rw [map_pow]; ring]
  have hmap : ((doublesPoly (fun l ↦ (MvPolynomial.X (j - 1 - l) : MvPolynomial ℕ k))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) j (g - j - 1)
          * (X ^ 2 - Polynomial.C (MvPolynomial.X j ^ 2))).map
          (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
      = doublesPoly (fun l ↦ genNode k (j - 1 - l)) (fun i ↦ genNode k (g - 1 - i))
          j (g - j - 1) * (X ^ 2 - Polynomial.C (genNode k j ^ 2)) := by
    simp only [Polynomial.map_mul, doublesPoly_map, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map_pow, genNode]
  rw [← hmap]
  exact momentDet_algebraMap_ne_zero _ (momentDet_generic_pair_ne_zero hj1 hj)

/-- **The step+ atoms at the generic nodes**: the `hplus` hypothesis of the chain
induction — the extended alphabet is the next stage's avoidance alphabet. -/
theorem genNode_plus_atom_ne_zero [NeZero (2 : k)] {j : ℕ} (hj : j < g) :
    momentDet g (((-1) ^ g * tupleU (fun i : Fin g ↦ genNode k i)
        * ∏ i ∈ Finset.range j, (Polynomial.C (genNode k i) - X)).comp (-X)
      * (Polynomial.C (genNode k j) + X)) (fun m ↦ (m : ℕ)) ≠ 0 := by
  rw [← comp_neg_X_mul, mul_assoc,
    ← Finset.prod_range_succ (fun i ↦ Polynomial.C (genNode k i) - X) j,
    cusp_alphabet_comp_neg (fun m ↦ genNode k m) (by lia : j + 1 ≤ g)]
  have hmap : ((doublesPoly (fun l ↦ (MvPolynomial.X (j + 1 - 1 - l) : MvPolynomial ℕ k))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) (j + 1) (g - (j + 1))).map
          (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
      = doublesPoly (fun l ↦ genNode k (j + 1 - 1 - l)) (fun i ↦ genNode k (g - 1 - i))
          (j + 1) (g - (j + 1)) := by
    simp only [doublesPoly_map, genNode]
  rw [← hmap]
  exact momentDet_algebraMap_ne_zero _ (momentDet_generic_doubles_ne_zero (by lia))

/-- The stage-`j` fold alphabet splits off the last-added node's double. -/
private theorem genNode_doubles_split {j : ℕ} (hj1 : 1 ≤ j) :
    doublesPoly (fun l ↦ genNode k (j - 1 - l)) (fun i ↦ genNode k (g - 1 - i)) j (g - j)
      = (Polynomial.C (genNode k (j - 1)) + X) ^ 2
        * doublesPoly (fun l ↦ genNode k (j - 2 - l)) (fun i ↦ genNode k (g - 1 - i))
            (j - 1) (g - j) := by
  have h1 := doublesPoly_succ_left (fun l ↦ genNode k (j - 1 - l))
    (fun i ↦ genNode k (g - 1 - i)) (j - 1) (g - j)
  rw [Nat.sub_add_cancel hj1,
    doublesPoly_congr (v := fun l ↦ genNode k (j - 1 - (l + 1)))
      (v' := fun l ↦ genNode k (j - 2 - l)) (u' := fun i ↦ genNode k (g - 1 - i))
      (d := j - 1)
      (fun l hl ↦ by rw [show j - 1 - (l + 1) = j - 2 - l by lia])
      (fun i hi ↦ rfl)] at h1
  simpa only [Nat.sub_zero] using h1

/-- **The mirror− atoms at the generic nodes**: the stage-`j` alphabet extended at the
negated last-added node — the value atom of `A_j(t_{j-1})`. -/
theorem genNode_trio_atom_ne_zero [NeZero (2 : k)] {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ g) :
    momentDet g (((-1) ^ g * tupleU (fun i : Fin g ↦ genNode k i)
        * ∏ i ∈ Finset.range j, (Polynomial.C (genNode k i) - X)).comp (-X)
      * (Polynomial.C (-genNode k (j - 1)) + X)) (fun m ↦ (m : ℕ)) ≠ 0 := by
  rw [cusp_alphabet_comp_neg (fun m ↦ genNode k m) hj,
    show (Polynomial.C (-genNode k (j - 1)) + X : (FractionRing (MvPolynomial ℕ k))[X])
      = X - Polynomial.C (genNode k (j - 1)) by rw [map_neg]; ring,
    genNode_doubles_split hj1, show (Polynomial.C (genNode k (j - 1)) + X) ^ 2
        * doublesPoly (fun l ↦ genNode k (j - 2 - l)) (fun i ↦ genNode k (g - 1 - i))
          (j - 1) (g - j) * (X - Polynomial.C (genNode k (j - 1)))
      = doublesPoly (fun l ↦ genNode k (j - 2 - l)) (fun i ↦ genNode k (g - 1 - i))
          (j - 1) (g - j)
        * ((Polynomial.C (genNode k (j - 1)) + X) ^ 2
          * (X - Polynomial.C (genNode k (j - 1)))) by ring]
  rcases eq_or_lt_of_le hj1 with rfl | hj2
  · simp only [Nat.sub_self, doublesPoly_zero]
    have hmap : ((singlesPoly (fun i ↦ (MvPolynomial.X (g - 1 - i) : MvPolynomial ℕ k))
          (g - 1) * ((Polynomial.C (MvPolynomial.X 0) + X) ^ 2
            * (X - Polynomial.C (MvPolynomial.X 0)))).map
            (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
        = singlesPoly (fun i ↦ genNode k (g - 1 - i)) (g - 1)
          * ((Polynomial.C (genNode k 0) + X) ^ 2 * (X - Polynomial.C (genNode k 0))) := by
      simp only [Polynomial.map_mul, singlesPoly_map, Polynomial.map_pow,
        Polynomial.map_add, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
        genNode]
    rw [← hmap]
    have hatom := momentDet_generic_trio_id_ne_zero (K := k) (g := g - 1)
    rw [show g - 1 + 1 = g by lia] at hatom
    exact momentDet_algebraMap_ne_zero _ hatom
  · have hmap : ((doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ k))
          (fun i ↦ MvPolynomial.X (g - 1 - i)) (j - 1) (g - j)
          * ((Polynomial.C (MvPolynomial.X (j - 1)) + X) ^ 2
            * (X - Polynomial.C (MvPolynomial.X (j - 1))))).map
            (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
        = doublesPoly (fun l ↦ genNode k (j - 2 - l)) (fun i ↦ genNode k (g - 1 - i))
            (j - 1) (g - j)
          * ((Polynomial.C (genNode k (j - 1)) + X) ^ 2
            * (X - Polynomial.C (genNode k (j - 1)))) := by
      simp only [Polynomial.map_mul, doublesPoly_map, Polynomial.map_pow,
        Polynomial.map_add, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
        genNode]
    rw [← hmap]
    exact momentDet_algebraMap_ne_zero _ (momentDet_generic_trio_ne_zero hj2 hj)

/-- **The mirror+ atoms at the generic nodes**: the stage-`j` alphabet extended at the
last-added node itself — the value atom of `A_j(-t_{j-1})` (`2 ≤ g`: at `g = 1` the
tripled atom degenerates to the characteristic-3 fingerprint `3t²`). -/
theorem genNode_tripled_atom_ne_zero [NeZero (2 : k)] (hg2 : 2 ≤ g) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ g) :
    momentDet g (((-1) ^ g * tupleU (fun i : Fin g ↦ genNode k i)
        * ∏ i ∈ Finset.range j, (Polynomial.C (genNode k i) - X)).comp (-X)
      * (Polynomial.C (genNode k (j - 1)) + X)) (fun m ↦ (m : ℕ)) ≠ 0 := by
  rw [cusp_alphabet_comp_neg (fun m ↦ genNode k m) hj,
    genNode_doubles_split hj1, show (Polynomial.C (genNode k (j - 1)) + X) ^ 2
        * doublesPoly (fun l ↦ genNode k (j - 2 - l)) (fun i ↦ genNode k (g - 1 - i))
          (j - 1) (g - j) * (Polynomial.C (genNode k (j - 1)) + X)
      = doublesPoly (fun l ↦ genNode k (j - 2 - l)) (fun i ↦ genNode k (g - 1 - i))
          (j - 1) (g - j)
        * (Polynomial.C (genNode k (j - 1)) + X) ^ 3 by ring]
  rcases eq_or_lt_of_le hj1 with rfl | hj2
  · simp only [Nat.sub_self, doublesPoly_zero]
    rw [show singlesPoly (fun i ↦ genNode k (g - 1 - i)) (g - 1)
        = singlesPoly (fun i ↦ genNode k (g - 1 - i)) (g - 2)
          * (Polynomial.C (genNode k 1) + X) by
      rw [show g - 1 = g - 2 + 1 by lia, singlesPoly_succ,
        show g - 2 + 1 - (g - 2) = 1 by lia]]
    have hmap : ((singlesPoly
            (fun i ↦ (MvPolynomial.X (g - 2 + 1 - i) : MvPolynomial ℕ k)) (g - 2)
          * (Polynomial.C (MvPolynomial.X 1) + X)
          * (Polynomial.C (MvPolynomial.X 0) + X) ^ 3).map
            (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
        = singlesPoly (fun i ↦ genNode k (g - 1 - i)) (g - 2)
          * (Polynomial.C (genNode k 1) + X)
          * (Polynomial.C (genNode k 0) + X) ^ 3 := by
      simp only [Polynomial.map_mul, singlesPoly_map, Polynomial.map_pow,
        Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, genNode]
      refine congrArg (· * _) (congrArg (· * _) (singlesPoly_congr fun i hi ↦ ?_))
      rw [show g - 2 + 1 - i = g - 1 - i by lia]
    rw [← hmap]
    have hatom := momentDet_generic_tripled_one_ne_zero (K := k) (g := g - 2)
    rw [show g - 2 + 2 = g by lia] at hatom
    exact momentDet_algebraMap_ne_zero _ hatom
  · have hmap : ((doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ k))
          (fun i ↦ MvPolynomial.X (g - 1 - i)) (j - 1) (g - j)
          * (Polynomial.C (MvPolynomial.X (j - 1)) + X) ^ 3).map
            (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
        = doublesPoly (fun l ↦ genNode k (j - 2 - l)) (fun i ↦ genNode k (g - 1 - i))
            (j - 1) (g - j)
          * (Polynomial.C (genNode k (j - 1)) + X) ^ 3 := by
      simp only [Polynomial.map_mul, doublesPoly_map, Polynomial.map_pow,
        Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, genNode]
    rw [← hmap]
    exact momentDet_algebraMap_ne_zero _ (momentDet_generic_tripled_ne_zero hj2 hj)

end Atoms

section Witness

variable (k : Type*) [Field k] (g : ℕ)

/-- The `u`-polynomial of the generic cuspidal base datum. -/
noncomputable def genU₀ : (FractionRing (MvPolynomial ℕ k))[X] :=
  tupleU fun i : Fin g ↦ genNode k i ^ 2

/-- The `v`-polynomial of the generic cuspidal base datum. -/
noncomputable def genV₀ : (FractionRing (MvPolynomial ℕ k))[X] :=
  tupleV (fun i : Fin g ↦ genNode k i ^ 2) fun i ↦ genNode k i ^ (2 * g + 1)

/-- The support of the generic cuspidal base datum. -/
noncomputable def genA₀ : (FractionRing (MvPolynomial ℕ k))[X] :=
  tupleU fun i : Fin g ↦ genNode k i

/-- **The generic cuspidal fold chain**: the fold at the parametrized cusp points
`(tᵢ², tᵢ^N)` with the variables as parameters, run with the doubling scalar `H₀` at the
initial step and the generic division scalars beyond. -/
noncomputable def genCuspChain (H₀ : FractionRing (MvPolynomial ℕ k)) :
    ℕ → (FractionRing (MvPolynomial ℕ k))[X] × (FractionRing (MvPolynomial ℕ k))[X]
      × (FractionRing (MvPolynomial ℕ k))[X] :=
  cuspChain g (genU₀ k g) (genV₀ k g) (genA₀ k g) (genNode k)
    (cuspGenH g (genU₀ k g) (genV₀ k g) (genA₀ k g) (genNode k) H₀)

variable {k g}

theorem eval_zero_genA₀_ne_zero : (genA₀ k g).eval 0 ≠ 0 := by
  rw [genA₀, eval_tupleU]
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
  rw [zero_sub, neg_ne_zero]
  exact genNode_ne_zero _

/-- **`thm:cusp-witness` over the function field, the phase-1 chain**: there is a doubling
scalar `H₀` such that along the generic cuspidal fold chain every stage satisfies the
fold invariants, every interior avoidance value `A_m(0)` is nonzero, every composition
condition holds, and every state evaluation with a nonzero value atom is nonzero. -/
theorem exists_genCuspChain_witness [NeZero (2 : k)] (hg : 0 < g) :
    ∃ H₀ : FractionRing (MvPolynomial ℕ k), ∀ m ≤ g,
      (IsCuspState g (genCuspChain k g H₀ m).1 (genCuspChain k g H₀ m).2.1
        (genCuspChain k g H₀ m).2.2)
      ∧ ((genCuspChain k g H₀ m).2.2).eval 0 ≠ 0
      ∧ (m < g → (genCuspChain k g H₀ m).2.2 * (X - Polynomial.C (genNode k m))
          ∣ X ^ (2 * g + 1) - ((genCuspChain k g H₀ m).2.1
            + Polynomial.C (cuspGenH g (genU₀ k g) (genV₀ k g) (genA₀ k g) (genNode k)
                H₀ m)
              * (genCuspChain k g H₀ m).1).comp (X ^ 2))
      ∧ ∀ w : FractionRing (MvPolynomial ℕ k),
          momentDet g (((-1) ^ g * genA₀ k g
              * ∏ i ∈ Finset.range m, (Polynomial.C (genNode k i) - X)).comp (-X)
            * (Polynomial.C w + X)) (fun m ↦ (m : ℕ)) ≠ 0 →
          ((genCuspChain k g H₀ m).2.2).eval (-w) ≠ 0 := by
  obtain ⟨H₀, hH⟩ := exists_cuspStep_H (t := fun i : Fin g ↦ genNode k i) two_ne_zero_fractionRing
    genNode_sq_injective ⟨0, hg⟩ (genNode_ne_zero _)
  have hok0 : genA₀ k g * (X - Polynomial.C (genNode k 0))
      ∣ X ^ (2 * g + 1) - (genV₀ k g + Polynomial.C H₀ * genU₀ k g).comp (X ^ 2) :=
    cuspStep_cond_base genNode_sq_injective ⟨0, hg⟩ hH
  have hbase : IsCuspState g (genU₀ k g) (genV₀ k g) (genA₀ k g) :=
    isCuspState_base genNode_sq_injective
  have ht0 : ∀ j < g, genNode k j ≠ 0 := fun j _ ↦ genNode_ne_zero j
  have hzero := fun j hj1 (hj : j < g) ↦ genNode_zero_atom_ne_zero (k := k) hj1 hj.le
  have hpair := fun j hj1 (hj : j < g) ↦ genNode_pair_atom_ne_zero (k := k) hj1 hj
  have hplus := fun j (_ : 1 ≤ j) (hj : j < g) ↦ genNode_plus_atom_ne_zero (k := k) hj
  refine ⟨H₀, fun m hm ↦ ⟨?_, ?_, fun hmg ↦ ?_, fun w hw ↦ ?_⟩⟩
  · exact isCuspState_cuspChain_of_atoms two_ne_zero_fractionRing hg hbase ht0
      eval_zero_genA₀_ne_zero hok0 hzero hpair hplus hm
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact eval_zero_genA₀_ne_zero
    · have h1 := cuspChain_eval_ne_zero_of_atoms two_ne_zero_fractionRing hg hbase ht0
        eval_zero_genA₀_ne_zero hok0 hzero hpair hplus hm (w := 0) (by
          rw [show (Polynomial.C (0 : FractionRing (MvPolynomial ℕ k)) + X
              : (FractionRing (MvPolynomial ℕ k))[X]) = X by simp]
          exact genNode_zero_atom_ne_zero hm1 hm)
      rwa [neg_zero] at h1
  · exact (cuspChain_cond_of_atoms two_ne_zero_fractionRing hg hbase ht0 eval_zero_genA₀_ne_zero
      hok0 hzero hpair hplus (show m + 1 ≤ g from hmg)).1 m (Nat.lt_succ_self m)
  · exact cuspChain_eval_ne_zero_of_atoms two_ne_zero_fractionRing hg hbase ht0
      eval_zero_genA₀_ne_zero hok0 hzero hpair hplus hm hw

end Witness

end ChabautyColeman

end
