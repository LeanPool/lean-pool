/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.Annihilator
public import LeanPool.HyperellipticCurves.Curve.Basic
public import LeanPool.HyperellipticCurves.Count.DiskCount
public import LeanPool.HyperellipticCurves.Log.Ftau.TauExists

import LeanPool.HyperellipticCurves.Count.DiskAssembled
import LeanPool.HyperellipticCurves.ForMathlib.Resultant
import LeanPool.HyperellipticCurves.ForMathlib.SetCard
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# The main theorem: the Chabauty–Coleman bound

The final assembly of blueprint `thm:main-count` and `thm:main-arith`. The witness layer produces,
for each residue disk, every input of the per-disk bounds of
`LeanPool.HyperellipticCurves.Count.DiskAssembled`.

## Main statements

* `ChabautyColeman.disk_bound_generic`, `ChabautyColeman.disk_bound_weierstrass`,
  `ChabautyColeman.disk_bound_inf`: the per-disk bound at each of the three chart types, from
  the `τ`-witness pack alone — the auxiliary point, its slope series and per-disk certificate
  packs are constructed here; the `hW`-identification runs per disk over `Frac(K⟦z⟧)`, so no
  global pack and no inverse differential matrix enters anywhere.
* `ChabautyColeman.disk_bound_ordSpace`: the same bound at an arbitrary residue point and in
  terms of `ChabautyColeman.ordSpace`, obtained by choosing the differential of the annihilating
  space that vanishes there to the least order.
* `ChabautyColeman.chabauty_coleman_odd_hyperelliptic` (blueprint `thm:main-count`): summing over
  the disks, `#S ≤ #T + 2r` for any set `S` of points with `K₀`-rational coordinates
  reducing into `T`, where `r < g` bounds the Mordell–Weil rank and `p > 2r + e + 1` for
  `e` a bound on the absolute ramification index of `O`.
* `ChabautyColeman.ratPoints_finite_of_rank_le`, `ChabautyColeman.main_affine`
  (blueprint `thm:main-count`): finiteness, and the affine restatement via
  `ChabautyColeman.CurvePoint.encard_univ`.
* `ChabautyColeman.exists_finset_redPoint_rational`: the arithmetic half of blueprint
  `lem:disk-decomp` — for an arithmetic valuation ring `O₀ ⊆ K₀` compatible with `O` and
  with finite residue field, the reductions of the `K₀`-rational points land in a finite
  set of residue points, of cardinality at most the point count of the reduced curve over
  the residue field of `O₀`.
* `ChabautyColeman.chabauty_coleman_odd_hyperelliptic_arith`,
  `ChabautyColeman.main_affine_arith`, `ChabautyColeman.ratPoints_finite_arith`: the fully
  arithmetic forms `#C(K₀) ≤ #C_bar(𝔽_q) + 2r` — no undischarged hypothesis remains
  beyond the standing ones.

The genericity of the `τ`-datum enters through
`ChabautyColeman.hasGoodCenter_of_pos_genus` (blueprint `lem:tau-generic`), proved for
every positive genus by the centre-fold witness (the cusp engine at genus `≥ 2`, the
direct tangent-chord computation of `LeanPool.HyperellipticCurves.Log.Fold.GenusOne` at genus `1`,
where the
squarefree reduction is used); the main theorems assume no genus lower bound beyond the
Chabauty condition `r < genus f₀`, which already forces positive genus. Everything in this
file is proved from that interface — the project is sorry-free.
-/

@[expose] public section

open Polynomial IsLocalRing
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

private theorem inter_eq_diff_singleton_inter {α : Type*} {S D : Set α} {a : α}
    (ha : a ∉ D) : S ∩ D = (S \ {a}) ∩ D :=
  ((Set.sdiff_inter_right_comm ..).trans (Set.sdiff_singleton_eq_self fun h ↦ ha h.2)).symm

private theorem natDegree_map_le_sub_one {R S : Type*} [Semiring R] [Semiring S]
    {φ : R →+* S} {h₀ : R[X]} {n : ℕ} (hh : h₀.map φ ≠ 0)
    (hdeg : h₀.degree < (n : WithBot ℕ)) : (h₀.map φ).natDegree ≤ n - 1 :=
  Nat.le_sub_one_of_lt ((natDegree_lt_iff_degree_lt hh).mpr (degree_map_le.trans_lt hdeg))

section MainAssembly

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  [IsAlgClosed (ResidueField O)] [Invertible (2 : O)] {C : HyperellipticCurve O} [C.IsOdd]
  (td : TauData O C.f) {π : O} {p e : ℕ} (cs : Fin td.u.natDegree → FractionRing O)
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The per-disk bound at a generic affine centre, from the witness pack**: the auxiliary
point, its slope series and per-disk certificate packs are constructed here from the
`τ`-datum pack; the identification runs per disk over `Frac(K⟦z⟧)`
(`LeanPool.HyperellipticCurves.Log.Trace.TraceKz`), so no global pack and no inverse differential
matrix
is needed. -/
theorem disk_bound_generic {h₀ : O[X]}
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * td.u.natDegree + 1)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    (hann : ∀ c, lambda td.hu rfl td.hv td.hw td.hbez cs C.monic_f C.natDegree_pos hfdeg td.hsqres
        td.hroot td.hcc td.ha td.hbv td.hsplit td.hunit td.hd
      hram hpe hf₀ c = 0)
    (hh : h₀.map (residue O) ≠ 0)
    (hmap : h₀.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
      tracePoly (td.u.map (algebraMap O (FractionRing O)))
        (td.c₂.map (algebraMap O (FractionRing O)))
        (Fin.cast (td.hu.natDegree_map (algebraMap O (FractionRing O))).symm i))
    {x y : ResidueField O} (he : y ^ 2 = (C.f.map (residue O)).eval x) (hy0 : y ≠ 0)
    (hτx : (td.u.map (residue O)).eval x ≠ 0)
    (hord : ordPoint (C.f.map (residue O)) (h₀.map (residue O)) (.affine x y he) + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine x y he)).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h₀.map (residue O)) (.affine x y he) := by
  classical
  have h2 : IsUnit (2 : O) := isUnit_of_invertible 2
  have hfdegO : C.f.natDegree = 2 * td.u.natDegree + 1 :=
    (C.monic_f.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg
  -- the point at infinity does not meet an affine residue disk
  rw [inter_eq_diff_singleton_inter infinity_notMem_residueDisk_affine]
  replace hrat : ∀ P ∈ S \ {.infinity}, ∃ x₀ y₀ : K₀,
      P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀ :=
    fun P hP ↦ hrat P hP.1 hP.2
  -- lift the centre
  obtain ⟨a, b, hb, rfl, rfl⟩ := exists_lift_curve_point h2 he hy0
  have hfares : (C.f.map (residue O)).eval (residue O a) ≠ 0 := by
    rw [← he]
    exact pow_ne_zero 2 hy0
  have hfa : IsUnit (C.f.eval a) := isUnit_eval_of_map_residue_ne_zero hfares
  have hτa : IsUnit (td.u.eval a) := isUnit_eval_of_map_residue_ne_zero hτx
  -- the auxiliary point and the per-disk pack
  obtain ⟨xQ, yQ, m₀, hsep, hyQu, hyQ, hm₀, hQ⟩ :=
    exists_auxiliary_point_phi h2 C.monic_f td.hu td.hv ⟨td.w, td.hw⟩ td.hcopres hτa hb hfa hfdegO
  obtain ⟨m, hm⟩ := exists_slope_series_generic (f := C.f) (b := b) (yQ := yQ) hsep
  obtain ⟨d, hcerts, havr, -⟩ := hQ m hm
  have hgτ : 2 * td.u.natDegree < C.f.natDegree := by lia
  exact encard_inter_residueDisk_le_ordPoint_tracePoly cs hsep hm hm₀ hb hfa hyQ td.hu td.hv td.hw
    td.hbez hgτ hcerts hfdeg td.hsqres td.hroot td.hcc td.ha td.hbv td.hsplit td.hunit td.hd hram
    hpe hf₀ rfl hann hh hyQu td.havoid havr hmap hord hrat

/-- **The per-disk bound at a Weierstrass affine centre, from the witness pack**: the centre
is Hensel-lifted to a simple integral root of `C.f`, and the auxiliary point and per-disk
certificate packs are constructed from the `τ`-datum pack; the identification runs per disk
over `Frac(K⟦z⟧)` (`LeanPool.HyperellipticCurves.Log.Trace.TraceKzWeierstrass`). -/
theorem disk_bound_weierstrass {h₀ : O[X]}
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * td.u.natDegree + 1)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    (hann : ∀ c, lambda td.hu rfl td.hv td.hw td.hbez cs C.monic_f C.natDegree_pos hfdeg td.hsqres
        td.hroot td.hcc td.ha td.hbv td.hsplit td.hunit td.hd
      hram hpe hf₀ c = 0)
    (hh : h₀.map (residue O) ≠ 0)
    (hmap : h₀.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
      tracePoly (td.u.map (algebraMap O (FractionRing O)))
        (td.c₂.map (algebraMap O (FractionRing O)))
        (Fin.cast (td.hu.natDegree_map (algebraMap O (FractionRing O))).symm i))
    {x : ResidueField O} (he : (0 : ResidueField O) ^ 2 = (C.f.map (residue O)).eval x)
    (hτx : (td.u.map (residue O)).eval x ≠ 0)
    (hord : ordPoint (C.f.map (residue O)) (h₀.map (residue O)) (.affine x 0 he) + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine x 0 he)).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h₀.map (residue O)) (.affine x 0 he) := by
  classical
  have h2 : IsUnit (2 : O) := isUnit_of_invertible 2
  have hfdegO : C.f.natDegree = 2 * td.u.natDegree + 1 :=
    (C.monic_f.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg
  -- the point at infinity does not meet an affine residue disk
  rw [inter_eq_diff_singleton_inter infinity_notMem_residueDisk_affine]
  replace hrat : ∀ P ∈ S \ {.infinity}, ∃ x₀ y₀ : K₀,
      P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀ :=
    fun P hP ↦ hrat P hP.1 hP.2
  -- lift the centre: a simple integral root of `C.f`
  have hx : (C.f.map (residue O)).eval x = 0 := by rw [← he, zero_pow two_ne_zero]
  have hx' : ((C.f.map (residue O)).derivative).eval x ≠ 0 :=
    eval_derivative_ne_zero_of_squarefree Fact.out hx
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := O) x
  obtain ⟨ω, hω, hωm⟩ := exists_smooth_root (g := C.f) (a₀ := a₀)
    ((residue_eq_zero_iff _).mp (by rwa [← ha₀, eval_map_apply] at hx))
    (isUnit_eval_of_map_residue_ne_zero (u := C.f.derivative)
      (by rw [ha₀, ← derivative_map]; exact hx'))
  have hωx : residue O ω = x := by
    rw [← ha₀]
    exact residue_eq_of_sub_mem hωm
  subst hωx
  have hωu : IsUnit (C.f.derivative.eval ω) := isUnit_eval_of_map_residue_ne_zero
    (u := C.f.derivative) (by rw [← derivative_map]; exact hx')
  have hτa : IsUnit (td.u.eval ω) := isUnit_eval_of_map_residue_ne_zero hτx
  -- the auxiliary point and the per-disk pack
  obtain ⟨xQ, yQ, m₀, hsep, hyQu, hyQ, hm₀, hQ⟩ :=
    exists_auxiliary_point_phi_weierstrass h2 C.monic_f C.natDegree_pos td.hu td.hv ⟨td.w, td.hw⟩
      td.hcopres hτa hω hωu hfdegO
  obtain ⟨m, hm⟩ :=
    exists_slope_series_weierstrass (yQ := yQ) C.monic_f C.natDegree_pos hω hωu hsep
  obtain ⟨d, hcerts, havr, -⟩ := hQ m hm
  have hgτ : 2 * td.u.natDegree < C.f.natDegree := by lia
  exact encard_inter_residueDisk_le_ordPoint_tracePoly_weierstrass cs hω hωu hsep
    hm hm₀ hyQ td.hu td.hv td.hw td.hbez hgτ hcerts hfdeg td.hsqres td.hroot td.hcc td.ha td.hbv
    td.hsplit td.hunit td.hd hram hpe hf₀
    rfl hann hh hyQu td.havoid havr hmap hord hrat

/-- **The per-disk bound at the disk at infinity, from the witness pack**: the reduced
closed datum at infinity is constructed from the `τ`-datum pack; the identification runs
per disk over `Frac(K⟦z⟧)` (`LeanPool.HyperellipticCurves.Log.Trace.TraceKzInf`), so no global pack
and no
inverse differential matrix is needed. -/
theorem disk_bound_inf {h₀ : O[X]} (hn0 : td.u.natDegree ≠ 0)
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * td.u.natDegree + 1)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    (hann : ∀ c, lambda td.hu rfl td.hv td.hw td.hbez cs C.monic_f C.natDegree_pos hfdeg td.hsqres
        td.hroot td.hcc td.ha td.hbv td.hsplit td.hunit td.hd
      hram hpe hf₀ c = 0)
    (hh : h₀.map (residue O) ≠ 0) (hh₀deg : h₀.degree < td.u.natDegree)
    (hmap : h₀.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
      tracePoly (td.u.map (algebraMap O (FractionRing O)))
        (td.c₂.map (algebraMap O (FractionRing O)))
        (Fin.cast (td.hu.natDegree_map (algebraMap O (FractionRing O))).symm i))
    (hord : ordPoint (C.f.map (residue O)) (h₀.map (residue O)) .infinity + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.infinity : CurvePoint (ResidueField O) (C.f.map (residue O)))).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h₀.map (residue O)) .infinity := by
  classical
  have hfdegO : C.f.natDegree = 2 * td.u.natDegree + 1 :=
    (C.monic_f.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg
  have hvτn : td.v.natDegree < td.u.natDegree := by
    rcases eq_or_ne td.v 0 with h0 | hvne
    · rw [h0, natDegree_zero]
      exact Nat.pos_of_ne_zero hn0
    · exact natDegree_lt_natDegree hvne td.hv
  -- the reduced infinity-disk datum
  obtain ⟨V, hV, hVdeg, hVdvd⟩ := exists_infVred C.monic_f td.hu hvτn hfdegO ⟨td.w, td.hw⟩
  have hhdegO : (h₀.map (residue O)).natDegree ≤ genus C.f - 1 := by
    rw [← td.hne]
    exact natDegree_map_le_sub_one hh hh₀deg
  exact encard_inter_residueDisk_le_ordPoint_tracePoly_inf cs td.hu td.hv td.hw td.hbez hvτn
    hV hVdeg hVdvd hfdeg td.hsqres td.hroot td.hcc td.ha td.hbv
    td.hsplit td.hunit td.hd hram hpe hf₀ rfl hann hh hhdegO
    td.havoid hmap hord hrat

/-- **The per-disk bound from the annihilating space**: at an arbitrary residue point the
element of `V` vanishing there to the least order is chosen, and the three chart bounds
above are dispatched on the shape of the point. The order that appears is
`ChabautyColeman.ordSpace`, so summing over the disks
(`ChabautyColeman.sum_ordSpace_le`) turns these bounds into the `2r` of the main theorem. -/
theorem disk_bound_ordSpace {V : Submodule (ResidueField O) (ResidueField O)[X]}
    (hn0 : td.u.natDegree ≠ 0)
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * td.u.natDegree + 1)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p) {r : ℕ} (hpr : 2 * r + e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    (hV0 : V ≠ ⊥) (hVrank : genus (C.f.map (residue O)) ≤ Module.finrank (ResidueField O) V + r)
    (hVlift : ∀ h ∈ V, h.degree < td.u.natDegree ∧
        ∃ (cs : Fin td.u.natDegree → FractionRing O) (h₀ : O[X]),
        (∀ c, lambda td.hu rfl td.hv td.hw td.hbez cs C.monic_f C.natDegree_pos hfdeg td.hsqres
            td.hroot td.hcc td.ha td.hbv td.hsplit td.hunit td.hd hram hpe hf₀ c = 0)
        ∧ h₀.map (residue O) = h ∧ h₀.degree < td.u.natDegree
        ∧ h₀.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
            tracePoly (td.u.map (algebraMap O (FractionRing O)))
              (td.c₂.map (algebraMap O (FractionRing O)))
              (Fin.cast (td.hu.natDegree_map (algebraMap O (FractionRing O))).symm i))
    (P₀ : CurvePoint (ResidueField O) (C.f.map (residue O)))
    (hτx : ∀ {x y : ResidueField O} {he : y ^ 2 = (C.f.map (residue O)).eval x},
        CurvePoint.affine x y he = P₀ → (td.u.map (residue O)).eval x ≠ 0)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk P₀).encard ≤ 1 + ordSpace (C.f.map (residue O)) V P₀ := by
  have hgres : genus (C.f.map (residue O)) = td.u.natDegree :=
    (genus_map C.monic_f (residue O)).trans td.hne.symm
  have hVdeg : ∀ h ∈ V, h.degree < genus (C.f.map (residue O)) :=
    fun h hh ↦ by rw [hgres]; exact (hVlift h hh).1
  obtain ⟨hbar, hbarV, hbar0, hbarmin⟩ := exists_ordPoint_eq_ordSpace hV0 P₀
  obtain ⟨-, cs, h₀, hann, hres, hdeg₀, hmap⟩ := hVlift _ hbarV
  have hh : h₀.map (residue O) ≠ 0 := hres ▸ hbar0
  have hord : ordPoint (C.f.map (residue O)) (h₀.map (residue O)) P₀ + e + 1 < p := by
    have hbud := sum_ordSpace_le hV0 hVdeg hVrank {P₀}
    rw [Finset.sum_singleton] at hbud
    rw [hres, hbarmin]
    lia
  rw [← hbarmin, ← hres]
  cases P₀ with
  | affine x y he =>
    rcases eq_or_ne y 0 with rfl | hy0
    · exact disk_bound_weierstrass td cs hfdeg hram hpe hf₀ hann
        hh hmap he (hτx rfl) hord hrat
    · exact disk_bound_generic td cs hfdeg hram hpe hf₀ hann
        hh hmap he hy0 (hτx rfl) hord hrat
  | infinity =>
    exact disk_bound_inf td cs hn0 hfdeg hram hpe hf₀ hann hh hdeg₀
      hmap hord hrat

end MainAssembly

section RatPoints

variable {O : Type*} [CommRing O] [IsDomain O] {f : O[X]}
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] {f₀ : K₀[X]}

/-- **The `K₀`-points inject into the `K₀`-rational locus**: the point count of the curve
over the arithmetic base field is at most the size of the set of points with `K₀`-rational
coordinates — the point at infinity has coordinates `(0, 0)`, so it belongs to the locus. -/
theorem encard_univ_le_encard_ratPoints
    (hf₀ : f₀.map (algebraMap K₀ (FractionRing O)) = f.map (algebraMap O (FractionRing O))) :
    (Set.univ : Set (CurvePoint K₀ f₀)).encard
      ≤ {P : CurvePoint (FractionRing O) (f.map (algebraMap O (FractionRing O)))
          | ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
            ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀}.encard := by
  set ψ := algebraMap O (FractionRing O)
  set ψ₀ := algebraMap K₀ (FractionRing O)
  have hmapeq : ∀ {x₀ y₀ : K₀}, y₀ ^ 2 = f₀.eval x₀ →
      (ψ₀ y₀) ^ 2 = (f.map ψ).eval (ψ₀ x₀) := by
    intro x₀ y₀ h
    rw [← hf₀, eval_map_apply, ← map_pow, h]
  set ι : CurvePoint K₀ f₀ → CurvePoint (FractionRing O) (f.map ψ) :=
    fun P ↦ match P with
      | .affine x₀ y₀ h => .affine (ψ₀ x₀) (ψ₀ y₀) (hmapeq h)
      | .infinity => .infinity with hιdef
  have hinj : Function.Injective ι := by
    intro P Q hPQ
    cases P with
    | affine xP yP hP =>
      cases Q with
      | affine xQ yQ hQ =>
        simp only [hιdef, CurvePoint.affine.injEq] at hPQ
        obtain ⟨h1, h2⟩ := hPQ
        simp only [CurvePoint.affine.injEq]
        exact ⟨(algebraMap K₀ (FractionRing O)).injective h1,
          (algebraMap K₀ (FractionRing O)).injective h2⟩
      | infinity => simp [hιdef] at hPQ
    | infinity =>
      cases Q with
      | affine xQ yQ hQ => simp [hιdef] at hPQ
      | infinity => rfl
  have himg : Set.MapsTo ι Set.univ {P : CurvePoint (FractionRing O) (f.map ψ)
      | ∃ x₀ y₀ : K₀, P.xCoord = ψ₀ x₀ ∧ P.yCoord = ψ₀ y₀} := by
    intro Q _
    cases Q with
    | affine x₀ y₀ h => exact ⟨x₀, y₀, rfl, rfl⟩
    | infinity => exact ⟨0, 0, by simp [hιdef], by simp [hιdef]⟩
  exact Set.encard_le_encard_of_injOn himg hinj.injOn

end RatPoints

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAlgClosed (ResidueField O)] [Invertible (2 : O)]
  {C : HyperellipticCurve O} [C.IsOdd]
  {π : O} {p e : ℕ}
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The Chabauty–Coleman bound** (blueprint `thm:main-count`), for an odd-degree hyperelliptic
curve `C` over `O` — its unit discriminant is the good reduction — and an odd-degree curve `C₀`
over the arithmetic field `K₀` agreeing with `C` over the fraction field. The curves supply all
polynomial-level hypotheses of the inner layers (monicity, degrees, oddness and squarefreeness
over `K`, `K₀` and the residue field) through their instances; the adic completeness is derived
in the proof. No genus hypothesis beyond the Chabauty condition `hrg : r < C₀.genus` is needed:
that condition already forces positive genus, and the centre-fold witness covers genus `1` since
the reduction of `C` is a curve, i.e. squarefree.

The bound is `2r`, not `2g - 2`: each residue disk is counted with the differential of the
annihilating space `V` that vanishes to the smallest order there, and those orders sum to
`2r` (`ChabautyColeman.sum_ordSpace_le`) because `V` has codimension at most `r`. The prime
only has to satisfy `p > 2r + e + 1`, which is what bounds every single order by
`p - e - 1`. -/
theorem chabauty_coleman_odd_hyperelliptic (hram : IsUniformizer π p e) {r : ℕ}
    (hpr : 2 * r + e + 1 < p) (hf₀ : C₀.baseChange (FractionRing O) = C.baseChange (FractionRing O))
    (hrk : HypJac.rank K₀ C₀.f ≤ r) (hrg : r < C₀.genus)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (T : Finset (CurvePoint (ResidueField O) (C.f.map (residue O))))
    (hT : ∀ P ∈ S, redPoint P ∈ T)
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    S.encard ≤ T.card + 2 * r := by
  classical
  have hpe : e + 1 < p := by lia
  -- the polynomial data of the curves, in the form the inner layers consume
  have hf : C.f.Monic := C.monic_f
  have hdeg : 0 < C.f.natDegree := C.natDegree_pos
  have hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)) :=
    congrArg HyperellipticCurve.f hf₀
  rw [← C₀.genus_f] at hrg
  have : IsAdicComplete (maximalIdeal O) O :=
    (IsAdic.isAdicComplete_iff (Fact.out : IsAdic (maximalIdeal O))).mpr ⟨‹_›, ‹_›⟩
  have h2 : IsUnit (2 : O) := isUnit_of_invertible 2
  have hfdegO : C.f.natDegree = 2 * genus C.f + 1 :=
    (two_mul_genus_add_one C.odd_natDegree_f).symm
  -- the rank hypothesis forces positive genus
  have hgf₀ : genus C₀.f = genus C.f :=
    genus_eq_of_natDegree_map _ (by rwa [hf₀, hf.natDegree_map])
  have hgpos : 0 < genus C.f := hgf₀ ▸ Nat.zero_lt_of_lt hrg
  -- the τ-datum, avoiding the x-coordinates of the residue disks to be counted
  have hTfin : (CurvePoint.xCoord ''
      (↑T : Set (CurvePoint (ResidueField O) (C.f.map (residue O))))).Finite :=
    T.finite_toSet.image _
  obtain ⟨td, hτT⟩ := TauData.exists_of_hasGoodCenter h2 hf hfdegO
    (hasGoodCenter_of_pos_genus hTfin hf hgpos (.inr Fact.out) hfdegO)
  have hn0 : td.u.natDegree ≠ 0 := by rw [td.hne]; lia
  have hfdegOu : C.f.natDegree = 2 * td.u.natDegree + 1 := by rwa [td.hne]
  have hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree
      = 2 * td.u.natDegree + 1 := by
    rwa [hf.natDegree_map]
  have hgres : genus (C.f.map (residue O)) = td.u.natDegree :=
    (genus_map hf (residue O)).trans td.hne.symm
  -- the space of annihilating differentials, of codimension at most the rank
  obtain ⟨V, hVrank, hVlift⟩ := exists_annihilator_tracePoly td.hu td.hv td.hw
    td.hbez hfdeg td.hsqres td.hroot td.hcc td.ha td.hbv
    td.hsplit td.hunit td.hd hram hpe hf₀ hrk
  rw [← hgres] at hVrank
  have hVdeg : ∀ h ∈ V, h.degree < genus (C.f.map (residue O)) :=
    fun h hh ↦ by rw [hgres]; exact (hVlift h hh).1
  have hV0 : V ≠ ⊥ := fun h0 ↦ by
    rw [h0, finrank_bot] at hVrank
    lia
  -- the per-disk bounds, each disk with its own differential, then the sum over the disks
  have hdisk P₀ (hP₀ : P₀ ∈ T) := disk_bound_ordSpace td hn0 hfdeg hram hpe hpr hf₀
    hV0 hVrank hVlift P₀
    (fun {x _ _} hPe ↦ hτT x ⟨P₀, hP₀, by rw [← hPe, CurvePoint.xCoord_affine]⟩) hrat
  exact ratPoints_encard_le T hT hdisk hV0 hVdeg hVrank

/-- **Finiteness of the rational points** (blueprint `thm:main-count`, projective form). -/
theorem ratPoints_finite_of_rank_le (hram : IsUniformizer π p e) {r : ℕ}
    (hpr : 2 * r + e + 1 < p) (hf₀ : C₀.baseChange (FractionRing O) = C.baseChange (FractionRing O))
    (hrk : HypJac.rank K₀ C₀.f ≤ r) (hrg : r < C₀.genus)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (T : Finset (CurvePoint (ResidueField O) (C.f.map (residue O))))
    (hT : ∀ P ∈ S, redPoint P ∈ T)
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    S.Finite :=
  Set.finite_of_encard_le_coe
    (k := T.card + 2 * r)
    (mod_cast chabauty_coleman_odd_hyperelliptic hram hpr hf₀ hrk hrg T hT hrat)

/-- **The Chabauty–Coleman bound, affine form** (blueprint `thm:main-count`). -/
theorem main_affine (hram : IsUniformizer π p e) {r : ℕ}
    (hpr : 2 * r + e + 1 < p) (hf₀ : C₀.baseChange (FractionRing O) = C.baseChange (FractionRing O))
    (hrk : HypJac.rank K₀ C₀.f ≤ r) (hrg : r < C₀.genus)
    (T : Finset (CurvePoint (ResidueField O) (C.f.map (residue O))))
    (hT : ∀ P : CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))),
      (∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) → redPoint P ∈ T) :
    {q : K₀ × K₀ | q.2 ^ 2 = C₀.f.eval q.1}.encard + 1
      ≤ ({q : ResidueField O × ResidueField O
            | q.2 ^ 2 = (C.f.map (residue O)).eval q.1}.encard + 1) + 2 * r := by
  classical
  set ψ := algebraMap O (FractionRing O)
  set ψ₀ := algebraMap K₀ (FractionRing O)
  set S : Set (CurvePoint (FractionRing O) (C.f.map ψ)) :=
    {P | ∃ x₀ y₀ : K₀, P.xCoord = ψ₀ x₀ ∧ P.yCoord = ψ₀ y₀}
  -- the projective bound at the set of `K₀`-rational points
  have hmain := chabauty_coleman_odd_hyperelliptic hram hpr hf₀ hrk hrg
    (S := S) T hT (fun P hP _ ↦ hP)
  -- the `K₀`-points inject into `S`
  have hle : (Set.univ : Set (CurvePoint K₀ C₀.f)).encard ≤ S.encard :=
    encard_univ_le_encard_ratPoints (congrArg HyperellipticCurve.f hf₀)
  -- the residue disks are residue points
  have hTle : (T.card : ℕ∞) ≤ {q : ResidueField O × ResidueField O
      | q.2 ^ 2 = (C.f.map (residue O)).eval q.1}.encard + 1 := by
    calc (T.card : ℕ∞) = (↑T : Set (CurvePoint (ResidueField O) (C.f.map (residue O)))).encard
        := (Set.encard_coe_eq_coe_finsetCard T).symm
      _ ≤ (Set.univ : Set (CurvePoint (ResidueField O) (C.f.map (residue O)))).encard :=
          Set.encard_mono (Set.subset_univ _)
      _ = _ := CurvePoint.encard_univ _
  calc {q : K₀ × K₀ | q.2 ^ 2 = C₀.f.eval q.1}.encard + 1
      = (Set.univ : Set (CurvePoint K₀ C₀.f)).encard := (CurvePoint.encard_univ C₀.f).symm
    _ ≤ S.encard := hle
    _ ≤ T.card + 2 * r := hmain
    _ ≤ ({q : ResidueField O × ResidueField O
            | q.2 ^ 2 = (C.f.map (residue O)).eval q.1}.encard + 1) + 2 * r := by gcongr

end Main


section RedRational

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {f : O[X]}
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)]
  {O₀ : Type*} [CommRing O₀] [IsLocalRing O₀] [Finite (ResidueField O₀)]

/-- **Reductions of rational points are rational over the arithmetic residue field**
(the arithmetic half of blueprint `lem:disk-decomp`): given an arithmetic valuation ring
`O₀ ⊆ K₀` compatible with `O` whose residue field is finite, the reductions of the
`K₀`-rational points land in a finite set `T` of residue points of cardinality at most the
number of affine points of the reduced curve over the residue field of `O₀`, plus one. -/
theorem exists_finset_redPoint_rational (ι : O₀ →+* O) [IsLocalHom ι] (ι₀ : O₀ →+* K₀)
    (hcomm : (algebraMap K₀ (FractionRing O)).comp ι₀ = (algebraMap O (FractionRing O)).comp ι)
    (hint : ∀ x : K₀, (IsDiscreteValuationRing.maximalIdeal O).valuation (FractionRing O)
        (algebraMap K₀ (FractionRing O) x) ≤ 1 → ∃ a : O₀, ι₀ a = x)
    {fA : O₀[X]} (hfA : fA.map ι = f) :
    ∃ T : Finset (CurvePoint (ResidueField O) (f.map (residue O))),
      (∀ P : CurvePoint (FractionRing O) (f.map (algebraMap O (FractionRing O))),
        (∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
          ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) → redPoint P ∈ T)
      ∧ (T.card : ℕ∞) ≤ {q : ResidueField O₀ × ResidueField O₀
          | q.2 ^ 2 = (fA.map (residue O₀)).eval q.1}.encard + 1 := by
  classical
  set ρ : ResidueField O₀ →+* ResidueField O := ResidueField.map ι
  set Ts : Set (CurvePoint (ResidueField O) (f.map (residue O))) :=
    {P | P.xCoord ∈ Set.range ρ ∧ P.yCoord ∈ Set.range ρ}
  -- the reduced curve equation descends along `ρ`
  have hfred (x : ResidueField O₀) :
      (f.map (residue O)).eval (ρ x) = ρ ((fA.map (residue O₀)).eval x) := by
    have h1 : f.map (residue O) = (fA.map (residue O₀)).map ρ := by
      rw [← hfA, Polynomial.map_map, Polynomial.map_map, ResidueField.map_comp_residue ι]
    rw [h1, eval_map_apply]
  -- `Ts` is finite: the affine part injects into the finite coordinate square
  have hfin : Ts.Finite := by
    refine Set.Finite.subset (Set.Finite.insert _ ?_)
      (Set.subset_insert_sdiff_singleton CurvePoint.infinity Ts)
    refine Set.Finite.of_finite_image ?_
      (CurvePoint.injOn_xCoord_yCoord.mono fun P hP ↦ hP.2)
    refine Set.Finite.subset (Set.Finite.prod (Set.finite_range ρ) (Set.finite_range ρ)) ?_
    intro q ⟨P, hP, hPq⟩
    rw [← hPq]
    exact ⟨hP.1.1, hP.1.2⟩
  refine ⟨hfin.toFinset, fun P hP ↦ ?_, ?_⟩
  · -- reductions of rational points lie in `Ts`
    rw [Set.Finite.mem_toFinset]
    obtain ⟨x₀, y₀, hx, hy⟩ := hP
    have hzero : (CurvePoint.infinity : CurvePoint (ResidueField O) (f.map (residue O))) ∈ Ts :=
      ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
    cases P with
    | infinity =>
      rw [show redPoint (.infinity : CurvePoint (FractionRing O)
        (f.map (algebraMap O (FractionRing O)))) = .infinity from redPoint_infinity]
      exact hzero
    | affine x y he =>
      simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine] at hx hy
      subst hx hy
      by_cases hvx : (IsDiscreteValuationRing.maximalIdeal O).valuation (FractionRing O)
          (algebraMap K₀ (FractionRing O) x₀) ≤ 1
      · by_cases hvy : (IsDiscreteValuationRing.maximalIdeal O).valuation (FractionRing O)
            (algebraMap K₀ (FractionRing O) y₀) ≤ 1
        · rw [redPoint_affine he hvx hvy]
          obtain ⟨a, rfl⟩ := hint x₀ hvx
          obtain ⟨b, rfl⟩ := hint y₀ hvy
          have hxa : algebraMap K₀ (FractionRing O) (ι₀ a)
              = algebraMap O (FractionRing O) (ι a) := RingHom.congr_fun hcomm a
          have hyb : algebraMap K₀ (FractionRing O) (ι₀ b)
              = algebraMap O (FractionRing O) (ι b) := RingHom.congr_fun hcomm b
          refine ⟨⟨residue O₀ a, ?_⟩, ⟨residue O₀ b, ?_⟩⟩
          · rw [CurvePoint.xCoord_affine, hxa, redK_algebraMap, ResidueField.map_residue]
          · rw [CurvePoint.yCoord_affine, hyb, redK_algebraMap, ResidueField.map_residue]
        · rw [redPoint_eq_infinity_of_not_le he hvx hvy]
          exact hzero
      · rw [redPoint_eq_infinity_of_lt he (not_le.mp hvx)]
        exact hzero
  · -- the cardinality bound: the affine part injects into the small solution set
    rw [← Set.Finite.encard_eq_coe_toFinset_card hfin]
    calc Ts.encard
        ≤ (insert .infinity (Ts \ {.infinity})).encard :=
          Set.encard_mono (Set.subset_insert_sdiff_singleton _ _)
      _ ≤ (Ts \ {.infinity}).encard + 1 := Set.encard_insert_le _ _
      _ ≤ {q : ResidueField O₀ × ResidueField O₀
            | q.2 ^ 2 = (fA.map (residue O₀)).eval q.1}.encard + 1 := by
          gcongr
          set g : CurvePoint (ResidueField O) (f.map (residue O))
              → ResidueField O₀ × ResidueField O₀ :=
            fun P ↦ (Function.invFun ρ P.xCoord, Function.invFun ρ P.yCoord) with hg
          have hval : ∀ {c : ResidueField O}, c ∈ Set.range ρ
              → ρ (Function.invFun ρ c) = c := fun hc ↦ Function.invFun_eq hc
          have himg : Set.MapsTo g (Ts \ {.infinity})
              {q : ResidueField O₀ × ResidueField O₀
                | q.2 ^ 2 = (fA.map (residue O₀)).eval q.1} := by
            intro P ⟨⟨hPx, hPy⟩, hne⟩
            cases P with
            | infinity => exact absurd rfl hne
            | affine x y he =>
              simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine] at hPx hPy
              refine ρ.injective ?_
              simp only [hg, CurvePoint.xCoord_affine, CurvePoint.yCoord_affine]
              rwa [map_pow, hval hPy, ← hfred, hval hPx]
          have hinj : Set.InjOn g (Ts \ {.infinity}) := by
            intro P hP Q hQ hPQ
            have h1 : P.xCoord = Q.xCoord := by
              rw [← hval hP.1.1, ← hval hQ.1.1]
              exact congrArg (fun q ↦ ρ q.1) hPQ
            have h2 : P.yCoord = Q.yCoord := by
              rw [← hval hP.1.2, ← hval hQ.1.2]
              exact congrArg (fun q ↦ ρ q.2) hPQ
            exact CurvePoint.injOn_xCoord_yCoord hP.2 hQ.2 (Prod.ext h1 h2)
          exact Set.encard_le_encard_of_injOn himg hinj

end RedRational

section Arith

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAlgClosed (ResidueField O)] [Invertible (2 : O)]
  {C : HyperellipticCurve O} [C.IsOdd]
  {π : O} {p e : ℕ}
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]
  {O₀ : Type*} [CommRing O₀] [IsLocalRing O₀] [Finite (ResidueField O₀)]

/-- **The Chabauty–Coleman bound, arithmetic form** (blueprint `thm:main-arith`): the number of
`K₀`-rational points of the curve is at most the number of points of the reduced curve over
the residue field of the arithmetic valuation ring `O₀`, plus `2r`. -/
theorem chabauty_coleman_odd_hyperelliptic_arith (hram : IsUniformizer π p e) {r : ℕ}
    (hpr : 2 * r + e + 1 < p) (hf₀ : C₀.baseChange (FractionRing O) = C.baseChange (FractionRing O))
    (hrk : HypJac.rank K₀ C₀.f ≤ r) (hrg : r < C₀.genus)
    (ι : O₀ →+* O) [IsLocalHom ι] (ι₀ : O₀ →+* K₀)
    (hcomm : (algebraMap K₀ (FractionRing O)).comp ι₀ = (algebraMap O (FractionRing O)).comp ι)
    (hint : ∀ x : K₀, (IsDiscreteValuationRing.maximalIdeal O).valuation (FractionRing O)
        (algebraMap K₀ (FractionRing O) x) ≤ 1 → ∃ a : O₀, ι₀ a = x)
    {fA : O₀[X]} (hfA : fA.map ι = C.f) :
    {P : CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O)))
      | ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀}.encard
      ≤ ({q : ResidueField O₀ × ResidueField O₀
            | q.2 ^ 2 = (fA.map (residue O₀)).eval q.1}.encard + 1)
        + 2 * r := by
  obtain ⟨T, hT, hTcard⟩ := exists_finset_redPoint_rational ι ι₀ hcomm hint hfA
  calc {P : CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O)))
        | ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
          ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀}.encard
      ≤ T.card + 2 * r :=
        chabauty_coleman_odd_hyperelliptic hram hpr hf₀ hrk hrg T
          hT (fun P hP _ ↦ hP)
    _ ≤ ({q : ResidueField O₀ × ResidueField O₀
            | q.2 ^ 2 = (fA.map (residue O₀)).eval q.1}.encard + 1)
        + 2 * r := by gcongr

/-- **The Chabauty–Coleman bound, affine arithmetic form** (blueprint `thm:main-arith`):
`#{(x,y) ∈ K₀² : y² = f₀(x)} + 1 ≤ #{(x_bar,y_bar) ∈ 𝔽² : y_bar² = f_bar(x_bar)} + 1 + 2r`, both
sides
counting the projective sets with the point at infinity made explicit. -/
theorem main_affine_arith (hram : IsUniformizer π p e) {r : ℕ}
    (hpr : 2 * r + e + 1 < p) (hf₀ : C₀.baseChange (FractionRing O) = C.baseChange (FractionRing O))
    (hrk : HypJac.rank K₀ C₀.f ≤ r) (hrg : r < C₀.genus)
    (ι : O₀ →+* O) [IsLocalHom ι] (ι₀ : O₀ →+* K₀)
    (hcomm : (algebraMap K₀ (FractionRing O)).comp ι₀ = (algebraMap O (FractionRing O)).comp ι)
    (hint : ∀ x : K₀, (IsDiscreteValuationRing.maximalIdeal O).valuation (FractionRing O)
        (algebraMap K₀ (FractionRing O) x) ≤ 1 → ∃ a : O₀, ι₀ a = x)
    {fA : O₀[X]} (hfA : fA.map ι = C.f) :
    {q : K₀ × K₀ | q.2 ^ 2 = C₀.f.eval q.1}.encard + 1
      ≤ ({q : ResidueField O₀ × ResidueField O₀
            | q.2 ^ 2 = (fA.map (residue O₀)).eval q.1}.encard + 1)
        + 2 * r := by
  refine le_trans ?_ (chabauty_coleman_odd_hyperelliptic_arith hram hpr hf₀ hrk hrg ι ι₀ hcomm
    hint hfA)
  rw [← CurvePoint.encard_univ C₀.f]
  exact encard_univ_le_encard_ratPoints (congrArg HyperellipticCurve.f hf₀)

/-- **Finiteness of the rational points, arithmetic form** (blueprint `thm:main-arith`):
under the rank hypothesis the affine `K₀`-solution set of `y² = f₀(x)` is finite. -/
theorem ratPoints_finite_arith (hram : IsUniformizer π p e) {r : ℕ}
    (hpr : 2 * r + e + 1 < p) (hf₀ : C₀.baseChange (FractionRing O) = C.baseChange (FractionRing O))
    (hrk : HypJac.rank K₀ C₀.f ≤ r) (hrg : r < C₀.genus)
    (ι : O₀ →+* O) [IsLocalHom ι] (ι₀ : O₀ →+* K₀)
    (hcomm : (algebraMap K₀ (FractionRing O)).comp ι₀ = (algebraMap O (FractionRing O)).comp ι)
    (hint : ∀ x : K₀, (IsDiscreteValuationRing.maximalIdeal O).valuation (FractionRing O)
        (algebraMap K₀ (FractionRing O) x) ≤ 1 → ∃ a : O₀, ι₀ a = x)
    {fA : O₀[X]} (hfA : fA.map ι = C.f) :
    {q : K₀ × K₀ | q.2 ^ 2 = C₀.f.eval q.1}.Finite := by
  have hfin : {q : ResidueField O₀ × ResidueField O₀
      | q.2 ^ 2 = (fA.map (residue O₀)).eval q.1}.Finite := Set.toFinite _
  have h := main_affine_arith hram hpr hf₀ hrk hrg ι ι₀ hcomm hint hfA
  refine Set.Finite.of_encard_le_add hfin (c := 1 + 2 * r) ?_
  refine le_self_add.trans (h.trans_eq ?_)
  push_cast
  ring

end Arith

end ChabautyColeman

end
