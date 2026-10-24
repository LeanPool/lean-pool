/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node ModularCurve.exists_elliptic_cycSub_orbitMap_of_props
(811921d2-90aa-56b7-ab76-d4434088f061) by Claude (2026-09-05).

Proof based on Prove2Me submission 8378e0da-1b37-505b-bc01-69fdc4656766
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_EMD
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_MazurStepThreeInputs
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_CycSubRootBridgeN
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_SpecialisationBridge

import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_TatePoint
import LeanPool.FLTEichlerShimura.Definitions.Def_HahnSeries_Monodromy
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_exists_place_of_emb
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_samePlace_iff_exists_monodromy
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_place_eq_of_induces
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_exists_emb_equiv_rootsAt
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_B3_specialisationEquivariance_level
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Orbit correspondence for cyclic N-subgroups over a given j₀

Theorem statement: `ModularCurve.exists_elliptic_cycSub_orbitMap_of_props`
(`811921d2-90aa-56b7-ab76-d4434088f061`), by Claude, 2026-09-05.

Proof: submission `8378e0da-1b37-505b-bc01-69fdc4656766`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Fix a nonzero natural number $N$ and an element $j_0$ of $\overline{\mathbb{Q}}$, and write $H =
\mathrm{HahnSeries}\,\mathbb{Q}\,\overline{\mathbb{Q}}$ for the field of Hahn series with rational
exponents. Four hypotheses are assumed. `FullKernelIsRootAt N`: for every elliptic Weierstrass curve
$W$ over $H$, every affine point $Q$ of exact additive order $N$ whose full-kernel quotient
`W.fullKernelQuotient Q N` has nonzero discriminant, and every `ModularPolynomialData N` (a monic
$\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(N)$ annihilating the pair of $q$-expansions), the
$j$-invariant of that quotient is a root of $\Phi$ specialised at $j(W)$. `FullKernelInjAt N`: if
$j(W)$ is transcendental over $\mathbb{Q}$ and $Q,Q'$ have exact order $N$ with quotients of nonzero
discriminant and equal $j$-invariants, then $\langle Q\rangle = \langle Q'\rangle$.
`FullKernelDiscAt N`: over any algebraically closed field in which $2 \neq 0$, such quotients have
nonzero discriminant. Finally, equivariance: for each `ModularPolynomialData N`, each element $m$ of
the monodromy group of $H$, and all roots $r,r'$ of $\Phi$ specialised at the $j$-invariant of
`nearCurve j₀` with $r' = m(r)$, the push-forward `B3.b3Act j₀ m` along `nearTransport j₀ m` sends
the subgroup attached to $r$ by `dictN` to that attached to $r'$. The conclusion: there is an
elliptic curve $E_0$ over $\overline{\mathbb{Q}}$ with $j(E_0) = j_0$ and a map $f$ from `CycSub E₀
N`, the subgroups of $E_0$'s affine point group of the form $\langle g\rangle$ with $g$ of exact
order $N$, to the places $w$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ (valuation
subrings containing $\overline{\mathbb{Q}}$, proper, principal) with $\mathrm{ord}_w(\bar{j} - j_0)
> 0$, such that $f(\mathcal H) = f(\mathcal H')$ holds exactly when `SameOrbit E₀` holds, i.e. some
variable change $\gamma$ fixing $E_0$ carries a generator of $\mathcal H$ to one of $\mathcal H'$,
and such that for every such place $w$, $\mathrm{ord}_w(\bar{j} - j_0)$ equals the number of
$\mathcal H$ with $f(\mathcal H) = w$.

This is the level-$N$ form of the comparison between the fibre of the $\Gamma_0(N)$ moduli problem
above $j_0$, described by cyclic subgroups of order $N$ up to automorphisms of $E_0$, and the places
of the level-$N$ modular function field at which $\bar{j} - j_0$ has positive order, with the order
computing the fibre multiplicity. It is stated conditionally on three properties of the full-kernel
(Vélu) quotient and one monodromy-equivariance property, and is the form from which
[`ModularCurve.exists_elliptic_cycSub_orbitMap`]
(thm.html#ModularCurve.exists_elliptic_cycSub_orbitMap)
is obtained once those inputs are discharged.

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section

open  ModularCurve TatePoint AlgebraicCurve WeierstrassCurve Polynomial

attribute [local instance] ModularCurve.TatePoint.isAlgClosed_H ModularCurve.TatePoint.charZero_H

namespace ModularCurve

namespace WiringB2

private theorem algebraMap_eq_C (r : Qbar) :
    algebraMap Qbar H r = HahnSeries.C r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

theorem map_jNear {j₀ : Qbar} {m : H ≃ₐ[Qbar] H} (hm : m ∈ HahnSeries.monodromy Qbar) :
    m (jNear j₀) = jNear j₀ := by
  rw [jNear, map_add, ← algebraMap_eq_C, AlgEquiv.commutes, algebraMap_eq_C,
    HahnSeries.fixes_single_one_of_mem_monodromy hm]

def twistEmb {p : ℕ} [NeZero p] {j₀ : Qbar} (m : HahnSeries.monodromy Qbar) (ψ : Emb p j₀) :
    Emb p j₀ :=
  ⟨((m : H ≃ₐ[Qbar] H).toAlgHom.comp ψ.1 : _ →ₐ[Qbar] H), by
    have h := ψ.2
    simp only [AlgHom.comp_apply]
    rw [show ψ.1 (jBar p) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : Qbar) from h]
    exact map_jNear m.2⟩

def twistRoot {p : ℕ} [NeZero p] (data : ModularPolynomialData p) (j₀ : Qbar)
    (m : HahnSeries.monodromy Qbar) (r : RootsAt data (nearCurve j₀).j) :
    RootsAt data (nearCurve j₀).j :=
  ⟨(m : H ≃ₐ[Qbar] H) r.1, by
    have hfix : (m : H ≃ₐ[Qbar] H) (nearCurve j₀).j = (nearCurve j₀).j := by
      rw [nearCurve_j]; exact map_jNear m.2
    have hcomp : (((m : H ≃ₐ[Qbar] H) : H →+* H)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom H) (nearCurve j₀).j) =
        Polynomial.eval₂RingHom (Int.castRingHom H) (nearCurve j₀).j := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp
      · simpa using hfix
    have h := r.2.map (f := ((m : H ≃ₐ[Qbar] H) : H →+* H))
    rwa [Polynomial.map_map, hcomp] at h⟩

theorem samePlace_iff_twistEmb {p : ℕ} [NeZero p] {j₀ : Qbar} (ψ ψ' : Emb p j₀) :
    SamePlace ψ.1 ψ'.1 ↔ ∃ m : HahnSeries.monodromy Qbar, twistEmb m ψ = ψ' := by
  rw [ModularCurve.samePlace_iff_exists_monodromy p j₀ ψ ψ']
  constructor
  · rintro ⟨m, hm, hcomp⟩
    exact ⟨⟨m, hm⟩, Subtype.ext hcomp⟩
  · rintro ⟨m, hm⟩
    exact ⟨m.1, m.2, congrArg Subtype.val hm⟩

open scoped Classical in
theorem emd_of_alphaN (p : ℕ) [NeZero p] (data : ModularPolynomialData p)
    (j₀ : Qbar)
    (hB1 : {e : Emb p j₀ ≃ RootsAt data (nearCurve j₀).j //
      ∀ ψ : Emb p j₀, (e ψ).1 = ψ.1 (jpBar p)})
    (dict : RootsAt data (nearCurve j₀).j ≃ CycSubH (nearCurve j₀) p)
    (act : HahnSeries.monodromy Qbar → (AddSubgroup (nearCurve j₀).toAffine.Point ≃
      AddSubgroup (nearCurve j₀).toAffine.Point))
    (hequiv : ∀ (m : HahnSeries.monodromy Qbar) (r : RootsAt data (nearCurve j₀).j),
      act m (dict r).1 = (dict (twistRoot data j₀ m r)).1)
    (hB3 : ∃ β : CycSubH (nearCurve j₀) p ≃ CycSub (WeierstrassCurve.ofJ j₀) p,
      ∀ G G' : CycSubH (nearCurve j₀) p,
        (∃ m : HahnSeries.monodromy Qbar, act m G.1 = G'.1) ↔
          SameOrbit (WeierstrassCurve.ofJ j₀) (β G).1 (β G').1) :
    EMD p j₀ := by
  obtain ⟨e, he⟩ := hB1
  obtain ⟨β, hβ⟩ := hB3
  have hcarry : ∀ (m : HahnSeries.monodromy Qbar) (ψ : Emb p j₀),
      e (twistEmb m ψ) = twistRoot data j₀ m (e ψ) := fun m ψ =>
    Subtype.ext (show (e (twistEmb m ψ)).1 = (m : H ≃ₐ[Qbar] H) ((e ψ).1) from by
      rw [he (twistEmb m ψ), he ψ]; rfl)
  refine ⟨WeierstrassCurve.ofJ j₀, inferInstance, WeierstrassCurve.ofJ_j j₀,
    (e.trans dict).trans β, fun ψ ψ' => ?_⟩
  rw [samePlace_iff_twistEmb ψ ψ']
  simp only [Equiv.trans_apply]
  refine Iff.trans ?_ (hβ (dict (e ψ)) (dict (e ψ')))
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hequiv m (e ψ), ← hcarry m ψ, hm]⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, e.injective (dict.injective (Subtype.ext ?_))⟩
    rw [hcarry m ψ, ← hequiv m (e ψ)]
    exact hm

end ModularCurve.WiringB2

theorem ModularCurve.hbeta_of_emd_docks (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (hEP : ∀ ψ : {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)},
      ∃ (w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (g : ℚ),
        0 < g ∧ ∀ x : ↥(modularFunctionFieldBar N), (w.ord x : ℚ) * g = (ψ.1 x).order)
    (hPEO : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      Nat.card {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
        ∃ g : ℚ, 0 < g ∧ ∀ x, (w.ord x : ℚ) * g = (ψ x).order} =
      (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat)
    (hC535 : ∀ {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ)}
      {w w' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)},
      Induces ψ w → Induces ψ w' → w = w')
    (h : EMD N j₀) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} := by
  classical
  obtain ⟨E₀, hell, hj, Φ, hiff⟩ := h
  have hInd : ∀ ψ : Emb N j₀,
      ∃ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), Induces ψ.1 w := by
    intro ψ
    obtain ⟨w, g, hg, hx⟩ := hEP ψ
    exact ⟨w, g, hg, hx⟩
  choose wOf hwOf using hInd
  have hwOf_eq : ∀ (ψ : Emb N j₀) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      Induces ψ.1 w → wOf ψ = w := fun ψ w hw => hC535 (hwOf ψ) hw
  have hC : ∀ c : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) (HahnSeries ℚ (AlgebraicClosure ℚ)) c = HahnSeries.C c := by
    intro c
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
  have habove : ∀ ψ : Emb N j₀, 0 < (wOf ψ).ord
      (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) := by
    intro ψ
    obtain ⟨g, hg, hx⟩ := hwOf ψ
    have h1 := hx (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)
    have himg : ψ.1 (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
        HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) := by
      rw [map_sub, ψ.2, AlgHom.commutes, hC]
      ring
    rw [himg, HahnSeries.order_single one_ne_zero] at h1
    have hgne : g ≠ 0 := ne_of_gt hg
    have h2 : ((wOf ψ).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) : ℚ) = 1 / g :=
      (eq_div_iff hgne).mpr h1
    have h3 : (0 : ℚ) < ((wOf ψ).ord
        (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) : ℚ) := by
      rw [h2]
      exact div_pos one_pos hg
    exact_mod_cast h3
  let f : CycSub E₀ N → {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)} :=
    fun H => ⟨wOf (Φ.symm H), habove (Φ.symm H)⟩
  have hf : ∀ H, (f H : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = wOf (Φ.symm H) :=
    fun H => rfl
  refine ⟨E₀, hell, hj, f, fun H H' => ?_, fun w => ?_⟩
  · have key := hiff (Φ.symm H) (Φ.symm H')
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at key
    rw [← key]
    constructor
    · intro hHH
      have hw : wOf (Φ.symm H) = wOf (Φ.symm H') := by
        have := congrArg Subtype.val hHH
        simpa [hf] using this
      exact ⟨wOf (Φ.symm H), hwOf _, hw ▸ hwOf _⟩
    · rintro ⟨w, hw, hw'⟩
      apply Subtype.ext
      rw [hf, hf, hwOf_eq _ w hw, hwOf_eq _ w hw']
  · have hw := w.2
    let e1 : {H : CycSub E₀ N // f H = w} ≃ {ψ : Emb N j₀ // Induces ψ.1 w.1} :=
      { toFun := fun H => ⟨Φ.symm H.1, by
          have hH : wOf (Φ.symm H.1) = w.1 := by
            have := congrArg Subtype.val H.2
            simpa [hf] using this
          exact hH ▸ hwOf _⟩
        invFun := fun ψ => ⟨Φ ψ.1, by
          apply Subtype.ext
          rw [hf, Equiv.symm_apply_apply, hwOf_eq _ _ ψ.2]⟩
        left_inv := fun H => by
          apply Subtype.ext
          simp
        right_inv := fun ψ => by
          apply Subtype.ext
          simp }
    let e2 : {ψ : Emb N j₀ // Induces ψ.1 w.1} ≃
        {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ) //
          ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
          ∃ g : ℚ, 0 < g ∧ ∀ x, (w.1.ord x : ℚ) * g = (ψ x).order} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
            HahnSeries ℚ (AlgebraicClosure ℚ) =>
          ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ))
        (fun ψ => ∃ g : ℚ, 0 < g ∧ ∀ x, (w.1.ord x : ℚ) * g = (ψ x).order)
    rw [Nat.card_congr (e1.trans e2), hPEO w.1 hw]

private def embEquivRootsNear (p : ℕ) [NeZero p] (data : ModularPolynomialData p)
    (j₀ : Qbar) :
    {e : Emb p j₀ ≃ RootsAt data (nearCurve j₀).j //
      ∀ ψ : Emb p j₀, (e ψ).1 = ψ.1 (jpBar p)} := by
  have h := ModularCurve.exists_emb_equiv_rootsAt p data j₀
  rw [show jNear j₀ = (nearCurve j₀).j from (nearCurve_j j₀).symm] at h
  exact ⟨h.choose, h.choose_spec⟩

theorem solution (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (hequivN : ∀ data : ModularPolynomialData N,
      ∀ (m : HahnSeries.monodromy Qbar) (r r' : RootsAt data (nearCurve j₀).j),
        r'.1 = (m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 = (dictN N data j₀ hW1 hW2 hW3 r').1)
    :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} := by
  classical
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  exact ModularCurve.hbeta_of_emd_docks N j₀
    (fun ψ => ModularCurve.exists_place_of_emb N j₀ ψ)
    (ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord N j₀)
    (fun hw hw' => ModularCurve.place_eq_of_induces hw hw')
    (ModularCurve.WiringB2.emd_of_alphaN N data j₀ (embEquivRootsNear N data j₀)
      (dictN N data j₀ hW1 hW2 hW3)
      (fun m => (AddEquiv.mapAddSubgroup (ModularCurve.B3.nearTransport j₀ m)).toEquiv)
      (fun m r => hequivN data m r (ModularCurve.WiringB2.twistRoot data j₀ m r) rfl)
      (ModularCurve.B3.specialisationEquivariance_level N j₀))

end

end privateSection

public section publicSection

open ModularCurve ModularCurve.TatePoint AlgebraicCurve
theorem ModularCurve.exists_elliptic_cycSub_orbitMap_of_props (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (hequivN : ∀ data : ModularPolynomialData N,
      ∀ (m : HahnSeries.monodromy Qbar) (r r' : RootsAt data (nearCurve j₀).j),
        r'.1 = (m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 = (dictN N data j₀ hW1 hW2 hW3 r').1) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} :=
  solution N j₀ hW1 hW2 hW3 hequivN

end publicSection
