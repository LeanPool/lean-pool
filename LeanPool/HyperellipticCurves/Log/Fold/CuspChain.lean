/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CantorPipeline
public import LeanPool.HyperellipticCurves.Log.Fold.CuspFold

/-!
# The instantiated cuspidal fold chain

This file turns the certificate-level step lemmas of
`LeanPool.HyperellipticCurves.Log.Fold.CuspFold` into an
honest recursion (`ChabautyColeman.cuspChain`): the state triple `(U, V, A)` — a reduced
Mumford pair on `y² = X^N` together with its `A`-picture support — advances by single-point
Cantor composition with the parametrized cusp point `(t_j², t_j^N)` at composition scalar
`H j`, followed by the canonical reduction `ChabautyColeman.cantorReduce` (with certificate
`-1`, the cofactor's leading coefficient in the unconditional regime), while the support
advances by `A' = (-1)^g·C_c(-z)`.

The scalars `H` are data: each step is valid as soon as its single **composition condition**
holds — the composed support divides the `z`-lift of the composed square root. Under these
conditions the full invariant package `ChabautyColeman.IsCuspState` propagates
(`ChabautyColeman.IsCuspState.step`, `ChabautyColeman.isCuspState_cuspChain`), including the
`U`–`A` identity `U(z²) = (-1)^g·A(z)·A(-z)` (`ChabautyColeman.cuspNext_U`, the remaining
half of `lem:cusp-reduction`), and the master congruence of `thm:cusp-moment` (1) holds along
the chain (`ChabautyColeman.cuspChain_moment_congruence`).

## Main statements

* `ChabautyColeman.cuspChain`, `ChabautyColeman.IsCuspState`: the fold recursion and its
  invariant state.
* `ChabautyColeman.IsCuspState.step`: one step preserves the invariants, given only the
  composition condition of that step.
* `ChabautyColeman.cuspNext_U`: the reduced Mumford support satisfies the `U`–`A` identity
  again (`lem:cusp-reduction`).
* `ChabautyColeman.cuspChain_moment_congruence`: the master congruence at every stage of the
  instantiated chain.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### Composition identities and the fold recursion -/

section CommRing

variable {R : Type*} [CommRing R] {g : ℕ} {A Vc Cc U : R[X]} {t : R}

/-- A monic divisor times the corresponding quotient recovers the dividend. -/
theorem monic_mul_divByMonic_of_dvd {p q : R[X]} (hp : p.Monic) (h : p ∣ q) :
    p * (q /ₘ p) = q := by
  have h1 := modByMonic_add_div q p
  rwa [(modByMonic_eq_zero_iff_dvd hp).mpr h, zero_add] at h1

/-- The even lift of the composed support: `U_c(z²) = (-1)^(g+1)·A_c(z)·A_c(-z)`. -/
theorem cuspCompose_U_comp (hU : U.comp (X ^ 2) = (-1) ^ g * (A * A.comp (-X))) :
    (U * (X - C (t ^ 2))).comp (X ^ 2)
      = (-1) ^ (g + 1) * ((A * (X - C t)) * (A * (X - C t)).comp (-X)) := by
  simp only [mul_comp, sub_comp, X_comp, C_comp]
  rw [hU, map_pow]
  ring

/-- The even lift of the squared Mumford relation factors through the composed supports. -/
theorem cuspCompose_sq_comp (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2)) :
    (Vc ^ 2 - X ^ (2 * g + 1)).comp (X ^ 2)
      = ((A * (X - C t)) * (A * (X - C t)).comp (-X)) * (Cc * Cc.comp (-X)) := by
  have h2 := cuspCompose_comp_neg_X hCc
  simp only [sub_comp, pow_comp, X_comp]
  linear_combination (-((A * (X - C t)).comp (-X) * Cc.comp (-X))) * hCc
    - (X ^ (2 * g + 1) - Vc.comp (X ^ 2)) * h2

/-- **The cuspidal fold chain** on state triples `(U, V, A)`: step `j` composes the Mumford
pair with the parametrized cusp point `(t_j², t_j^N)` at composition scalar `H j` and reduces
canonically (`ChabautyColeman.cantorReduce` with certificate `-1` — the cofactor's leading
coefficient throughout the unconditional regime), while the `A`-picture support advances by
`A' = (-1)^g·C_c(-z)` (`def:cusp-fold`). The scalars `H` are data; the invariants hold
whenever each step satisfies its composition condition
(`ChabautyColeman.isCuspState_cuspChain`). -/
noncomputable def cuspChain (g : ℕ) (U₀ V₀ A₀ : R[X]) (t H : ℕ → R) : ℕ → R[X] × R[X] × R[X]
  | 0 => (U₀, V₀, A₀)
  | j + 1 =>
    let s := cuspChain g U₀ V₀ A₀ t H j
    let Vc := s.2.1 + C (H j) * s.1
    ((cantorReduce (X ^ (2 * g + 1)) (s.1 * (X - C (t j ^ 2))) Vc (-1)).1,
      (cantorReduce (X ^ (2 * g + 1)) (s.1 * (X - C (t j ^ 2))) Vc (-1)).2,
      (-1) ^ g * ((X ^ (2 * g + 1) - Vc.comp (X ^ 2)) /ₘ (s.2.2 * (X - C (t j)))).comp (-X))

variable {U₀ V₀ A₀ : R[X]} {t H : ℕ → R}

@[simp] theorem cuspChain_zero : cuspChain g U₀ V₀ A₀ t H 0 = (U₀, V₀, A₀) := rfl

theorem cuspChain_succ (j : ℕ) :
    cuspChain g U₀ V₀ A₀ t H (j + 1)
      = ((cantorReduce (X ^ (2 * g + 1))
            ((cuspChain g U₀ V₀ A₀ t H j).1 * (X - C (t j ^ 2)))
            ((cuspChain g U₀ V₀ A₀ t H j).2.1
              + C (H j) * (cuspChain g U₀ V₀ A₀ t H j).1) (-1)).1,
          (cantorReduce (X ^ (2 * g + 1))
            ((cuspChain g U₀ V₀ A₀ t H j).1 * (X - C (t j ^ 2)))
            ((cuspChain g U₀ V₀ A₀ t H j).2.1
              + C (H j) * (cuspChain g U₀ V₀ A₀ t H j).1) (-1)).2,
          (-1) ^ g * ((X ^ (2 * g + 1)
              - ((cuspChain g U₀ V₀ A₀ t H j).2.1
                + C (H j) * (cuspChain g U₀ V₀ A₀ t H j).1).comp (X ^ 2))
            /ₘ ((cuspChain g U₀ V₀ A₀ t H j).2.2 * (X - C (t j)))).comp (-X)) := rfl

/-- **The invariant state of the cuspidal fold** (`def:cusp-fold`, `lem:cusp-divisibility`,
`lem:cusp-reduction`): a reduced Mumford pair `(U, V)` on `y² = X^N` together with its
`A`-picture support: `U` and `A` are monic of degree `g`, `V` is reduced, the Mumford
relation and its `z`-lift hold, and `U(z²) = (-1)^g·A(z)·A(-z)`. -/
structure IsCuspState (g : ℕ) (U V A : R[X]) : Prop where
  /-- The support is monic. -/
  monicU : U.Monic
  /-- The support has the generic degree `g`. -/
  natDegree_U : U.natDegree = g
  /-- The Mumford divisibility on the cusp `y² = X^(2g+1)`. -/
  dvd_sq : U ∣ V ^ 2 - X ^ (2 * g + 1)
  /-- The interpolant is reduced against the support. -/
  degree_V : V.degree < (g : WithBot ℕ)
  /-- The `A`-picture support is monic. -/
  monicA : A.Monic
  /-- The `A`-picture support has degree `g`. -/
  natDegree_A : A.natDegree = g
  /-- The `z`-lift of the Mumford relation. -/
  dvd_lift : A ∣ X ^ (2 * g + 1) - V.comp (X ^ 2)
  /-- The two supports match: `U(z²) = (-1)^g·A(z)·A(-z)`. -/
  comp_sq : U.comp (X ^ 2) = (-1) ^ g * (A * A.comp (-X))

end CommRing

/-! ### Preservation of the invariants -/

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {g : ℕ}

/-- Divisibility descends along a nonconstant substitution: if `p ∘ r ∣ q ∘ r` with `p` monic
and `r` nonconstant, then `p ∣ q`. -/
theorem dvd_of_comp_dvd {p q r : R[X]} (hp : p.Monic) (hr : 0 < r.natDegree)
    (h : p.comp r ∣ q.comp r) : p ∣ q := by
  rcases eq_or_ne (q %ₘ p) 0 with h0 | h0
  · exact (modByMonic_eq_zero_iff_dvd hp).mp h0
  -- otherwise the substituted remainder is a nonzero multiple of `p ∘ r` of smaller degree
  exfalso
  have hrdvd : p.comp r ∣ (q %ₘ p).comp r := by
    have h2 : (q %ₘ p).comp r = q.comp r - p.comp r * (q /ₘ p).comp r := by
      rw [← mul_comp, modByMonic_eq_sub_mul_div q p, sub_comp]
    rw [h2]
    exact h.sub (dvd_mul_right _ _)
  have hr0 : (q %ₘ p).comp r ≠ 0 := fun hc ↦ h0 (by
    rcases comp_eq_zero_iff.mp hc with hc | ⟨-, hc⟩
    · exact hc
    · rw [hc, natDegree_C] at hr
      exact absurd hr (lt_irrefl 0))
  have hdeg : ((q %ₘ p).comp r).degree < (p.comp r).degree := by
    have h3 : (q %ₘ p).natDegree < p.natDegree :=
      natDegree_lt_natDegree h0 (degree_modByMonic_lt q hp)
    refine degree_lt_degree ?_
    rw [natDegree_comp, natDegree_comp]
    exact Nat.mul_lt_mul_of_pos_right h3 hr
  exact hr0 (eq_zero_of_dvd_of_degree_lt hrdvd hdeg)

variable {A Vc Cc A' U U' w : R[X]} {t : R}

/-- **`lem:cusp-reduction`, the `U`–`A` identity**: the reduced Mumford support satisfies
`U'(z²) = (-1)^g·A'(z)·A'(-z)` again. All data enter through their defining identities;
the composed supports cancel from the squared Mumford relation. -/
theorem cuspNext_U (hA : A.Monic)
    (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2))
    (hA' : A' = (-1) ^ g * Cc.comp (-X))
    (hU : U.comp (X ^ 2) = (-1) ^ g * (A * A.comp (-X)))
    (hw : Vc ^ 2 - X ^ (2 * g + 1) = U * (X - C (t ^ 2)) * w) (hU' : U' = -w) :
    U'.comp (X ^ 2) = (-1) ^ g * (A' * A'.comp (-X)) := by
  have hAc : (A * (X - C t)).Monic := hA.mul (monic_X_sub_C t)
  have hE : (A * (X - C t)) * (A * (X - C t)).comp (-X) ≠ 0 :=
    mul_ne_zero hAc.ne_zero fun hc ↦ hAc.ne_zero (comp_neg_X_eq_zero_iff.mp hc)
  have h0 := congrArg (·.comp (X ^ 2)) hw
  simp only [sub_comp, pow_comp, mul_comp, X_comp, C_comp, map_pow] at h0
  rw [hU] at h0
  have hAcs : (A * (X - C t)).comp (-X) = A.comp (-X) * (-X - C t) := by
    simp only [mul_comp, sub_comp, X_comp, C_comp]
  have hccw : Cc * Cc.comp (-X) = (-1) ^ (g + 1) * w.comp (X ^ 2) := by
    refine mul_left_cancel₀ hE ?_
    linear_combination ((A * (X - C t)).comp (-X) * Cc.comp (-X)) * hCc
      + (X ^ (2 * g + 1) - Vc.comp (X ^ 2)) * cuspCompose_comp_neg_X hCc + h0
      + ((-1 : R[X]) ^ g * A * w.comp (X ^ 2) * (X - C t)) * hAcs
  have hsq : ((-1 : R[X]) ^ g) * ((-1) ^ g) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨g, rfl⟩
  have h3 : ((-1 : R[X]) ^ g * Cc.comp (-X)).comp (-X) = (-1) ^ g * Cc := by
    simp only [mul_comp, pow_comp, neg_comp, one_comp, comp_neg_X_comp_neg_X]
  rw [hU', hA', neg_comp, h3]
  linear_combination (-(((-1 : R[X]) ^ g) ^ 3)) * hccw
    + (w.comp (X ^ 2) * (((-1 : R[X]) ^ g) ^ 2 + 1)) * hsq

/-- **The composed Mumford divisibility from the cusp-level composition condition**: the
`z`-lift condition of one fold step descends to the Mumford divisibility of the composed
pair. -/
theorem cuspStep_mumford {U V A : R[X]} {t' H' : R} (hs : IsCuspState g U V A)
    (hAc : A * (X - C t') ∣ X ^ (2 * g + 1) - (V + C H' * U).comp (X ^ 2)) :
    U * (X - C (t' ^ 2)) ∣ (V + C H' * U) ^ 2 - X ^ (2 * g + 1) := by
  set Vc := V + C H' * U
  set Ac := A * (X - C t')
  have hAcm : Ac.Monic := hs.monicA.mul (monic_X_sub_C t')
  set Cc := (X ^ (2 * g + 1) - Vc.comp (X ^ 2)) /ₘ Ac
  have hCc : Ac * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2) :=
    monic_mul_divByMonic_of_dvd hAcm hAc
  have hUcm : (U * (X - C (t' ^ 2))).Monic := hs.monicU.mul (monic_X_sub_C _)
  refine dvd_of_comp_dvd (r := X ^ 2) hUcm (by simp) ?_
  rw [cuspCompose_sq_comp hCc, cuspCompose_U_comp hs.comp_sq]
  have hsq : ((-1 : R[X]) ^ (g + 1)) * ((-1) ^ (g + 1)) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨g + 1, rfl⟩
  exact ⟨(-1) ^ (g + 1) * (Cc * Cc.comp (-X)), by
    linear_combination (-((Ac * Ac.comp (-X)) * (Cc * Cc.comp (-X)))) * hsq⟩

/-- **One fold step preserves the invariants**, given the single composition condition: the
composed support divides the `z`-lift of the composed square root. (The condition is produced
by `ChabautyColeman.cuspCompose_dvd` at a disjoint step and by the tangency argument at the
doubling step.) -/
theorem IsCuspState.step {U V A : R[X]} {t' H' : R} (hs : IsCuspState g U V A)
    (hAc : A * (X - C t') ∣ X ^ (2 * g + 1) - (V + C H' * U).comp (X ^ 2)) :
    IsCuspState g
      (cantorReduce (X ^ (2 * g + 1)) (U * (X - C (t' ^ 2))) (V + C H' * U) (-1)).1
      (cantorReduce (X ^ (2 * g + 1)) (U * (X - C (t' ^ 2))) (V + C H' * U) (-1)).2
      ((-1) ^ g * ((X ^ (2 * g + 1) - (V + C H' * U).comp (X ^ 2))
        /ₘ (A * (X - C t'))).comp (-X)) := by
  have hMum := cuspStep_mumford hs hAc
  obtain ⟨hUm, hUdeg, hUdvd, hVdeg, hAm, hAdeg, hAdvd, hUA⟩ := hs
  set Vc := V + C H' * U
  set Ac := A * (X - C t')
  have hAcm : Ac.Monic := hAm.mul (monic_X_sub_C t')
  set Cc := (X ^ (2 * g + 1) - Vc.comp (X ^ 2)) /ₘ Ac
  have hCc : Ac * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2) :=
    monic_mul_divByMonic_of_dvd hAcm hAc
  have hVcdeg : Vc.natDegree ≤ g := by
    refine (natDegree_add_le _ _).trans
      (max_le (natDegree_le_iff_degree_le.mpr hVdeg.le) ?_)
    exact natDegree_mul_le.trans (by simp [hUdeg])
  have hCcm : Cc.Monic := cuspCofactor_monic hAm hCc hVcdeg
  have hCcdeg : Cc.natDegree = g := cuspCofactor_natDegree hAm hAdeg hCc hVcdeg
  -- the composed Mumford pair and its exact cofactor
  set Uc := U * (X - C (t' ^ 2)) with hUcdef
  have hUcm : Uc.Monic := hUm.mul (monic_X_sub_C _)
  have hUcdeg : Uc.natDegree = g + 1 := by
    rw [hUcdef, hUm.natDegree_mul (monic_X_sub_C _), natDegree_X_sub_C, hUdeg]
  set w := cantorCofactor (X ^ (2 * g + 1)) Uc Vc
  have hw : Vc ^ 2 - X ^ (2 * g + 1) = Uc * w := cantorCofactor_spec _ hUcm hMum
  obtain ⟨hwlc, hwdeg⟩ := leadingCoeff_natDegree_cantorCofactor (X ^ (2 * g + 1))
    (monic_X_pow _) (natDegree_X_pow _) hUcm hUcdeg hMum
    (by
      refine degree_le_natDegree.trans_lt ?_
      rw [degree_eq_natDegree hUcm.ne_zero, hUcdeg]
      exact_mod_cast by lia)
    (by lia)
  -- the reduced pair
  have hU' : (cantorReduce (X ^ (2 * g + 1)) Uc Vc (-1)).1 = -w := by
    change C (-1) * w = -w
    rw [map_neg, map_one, neg_one_mul]
  have hU'm : (-w).Monic := by rw [Monic, leadingCoeff_neg, hwlc, neg_neg]
  have hU'deg : (-w).natDegree = g := by
    rw [natDegree_neg]
    lia
  have hV' : (cantorReduce (X ^ (2 * g + 1)) Uc Vc (-1)).2 = (-Vc) %ₘ (-w) := by
    change (-Vc) %ₘ (C (-1) * w) = (-Vc) %ₘ (-w)
    rw [map_neg, map_one, neg_one_mul]
  -- the new `A` and its invariants
  have hA'm : ((-1) ^ g * Cc.comp (-X)).Monic := cuspNext_monic hCcm hCcdeg rfl
  have hA'deg : ((-1) ^ g * Cc.comp (-X)).natDegree = g := cuspNext_natDegree hCcdeg rfl
  have hcompU' : (-w).comp (X ^ 2) = (-1) ^ g
      * (((-1) ^ g * Cc.comp (-X)) * ((-1) ^ g * Cc.comp (-X)).comp (-X)) :=
    cuspNext_U hAm hCc rfl hUA (by rw [hw, hUcdef]) rfl
  rw [hU', hV']
  refine ⟨hU'm, hU'deg, ?_, ?_, hA'm, hA'deg, ?_, hcompU'⟩
  · have h5 : -w ∣ (-Vc) ^ 2 - X ^ (2 * g + 1) := by
      rw [neg_sq, hw]
      exact neg_dvd.mpr (dvd_mul_left w Uc)
    exact dvd_modByMonic_sq_sub_of_dvd _ h5
  · have h6 := degree_modByMonic_lt (-Vc) hU'm
    rwa [degree_eq_natDegree hU'm.ne_zero, hU'deg] at h6
  · refine cuspNext_dvd hCc rfl ?_
    have h7 : -w ∣ (-Vc) %ₘ (-w) + Vc := by
      have h8 := dvd_modByMonic_sub (-Vc) (-w)
      rwa [sub_neg_eq_add] at h8
    obtain ⟨k, hk⟩ := h7
    have h9 : ((-1 : R[X]) ^ g * Cc.comp (-X)) ∣ (-w).comp (X ^ 2) :=
      ⟨(-1) ^ g * ((-1) ^ g * Cc.comp (-X)).comp (-X), by rw [hcompU']; ring⟩
    exact h9.trans ⟨k.comp (X ^ 2), by rw [hk, mul_comp]⟩

variable {U₀ V₀ A₀ : R[X]} {t H : ℕ → R}

/-- **The chain invariants** (`lem:cusp-divisibility`, `lem:cusp-reduction`, assembled): the
fold state satisfies `ChabautyColeman.IsCuspState` at every stage, as long as every earlier
step satisfies its composition condition. -/
theorem isCuspState_cuspChain (hbase : IsCuspState g U₀ V₀ A₀) {m : ℕ}
    (hok : ∀ j < m, (cuspChain g U₀ V₀ A₀ t H j).2.2 * (X - C (t j))
      ∣ X ^ (2 * g + 1) - ((cuspChain g U₀ V₀ A₀ t H j).2.1
          + C (H j) * (cuspChain g U₀ V₀ A₀ t H j).1).comp (X ^ 2)) :
    IsCuspState g (cuspChain g U₀ V₀ A₀ t H m).1 (cuspChain g U₀ V₀ A₀ t H m).2.1
      (cuspChain g U₀ V₀ A₀ t H m).2.2 := by
  induction m with
  | zero => exact hbase
  | succ m ih => exact (ih fun j hj ↦ hok j (by lia)).step (hok m (by lia))

end Domain

/-! ### The master congruence along the instantiated chain -/

section ChainMoment

variable {F : Type*} [Field F] {g : ℕ} {U₀ V₀ A₀ d₀ : F[X]} {t H : ℕ → F}

/-- **The master congruence along the instantiated fold chain** (`thm:cusp-moment` (1) for
`def:cusp-fold`): under the composition conditions and the avoidance values, the reduced
support at stage `m` satisfies the congruence against `d₀·∏_(j<m) (t_j - z)`. -/
theorem cuspChain_moment_congruence (hbase : IsCuspState g U₀ V₀ A₀) {m : ℕ}
    (hok : ∀ j < m, (cuspChain g U₀ V₀ A₀ t H j).2.2 * (X - C (t j))
      ∣ X ^ (2 * g + 1) - ((cuspChain g U₀ V₀ A₀ t H j).2.1
          + C (H j) * (cuspChain g U₀ V₀ A₀ t H j).1).comp (X ^ 2))
    (hA0 : ∀ j < m, ((cuspChain g U₀ V₀ A₀ t H j).2.2).eval 0 ≠ 0)
    (ht : ∀ j < m, t j ≠ 0)
    (hd0 : X ^ (2 * g + 1) ∣ A₀ * d₀.comp (-X) - A₀.comp (-X) * d₀) :
    X ^ (2 * g + 1) ∣ (cuspChain g U₀ V₀ A₀ t H m).2.2
        * (d₀ * ∏ i ∈ Finset.range m, (C (t i) - X)).comp (-X)
      - ((cuspChain g U₀ V₀ A₀ t H m).2.2).comp (-X)
        * (d₀ * ∏ i ∈ Finset.range m, (C (t i) - X)) := by
  refine cuspMoment_congruence
    (Vc := fun j ↦ (cuspChain g U₀ V₀ A₀ t H j).2.1
      + C (H j) * (cuspChain g U₀ V₀ A₀ t H j).1)
    (Cc := fun j ↦ (X ^ (2 * g + 1) - ((cuspChain g U₀ V₀ A₀ t H j).2.1
        + C (H j) * (cuspChain g U₀ V₀ A₀ t H j).1).comp (X ^ 2))
      /ₘ ((cuspChain g U₀ V₀ A₀ t H j).2.2 * (X - C (t j))))
    (fun j hj ↦ ?_) (fun j hj ↦ rfl) hA0 ht hd0
  have hst := isCuspState_cuspChain hbase fun i hi ↦ hok i (hi.trans hj)
  exact monic_mul_divByMonic_of_dvd (hst.monicA.mul (monic_X_sub_C _)) (hok j hj)

end ChainMoment

end ChabautyColeman

end
