/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FtauFold
public import LeanPool.HyperellipticCurves.Log.Ftau.GoodPosition
public import LeanPool.HyperellipticCurves.Specialization.Pointwise

import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
import LeanPool.HyperellipticCurves.Log.Fold.CenterFold
import LeanPool.HyperellipticCurves.Log.Fold.FoldTrace

/-!
# Existence of the `τ`-datum (blueprint `lem:tau-exists`)

Over a complete DVR-type base `O` with algebraically closed residue field:

* `ChabautyColeman.HasGoodCenter` (the residue-side genericity, blueprint
  `lem:tau-generic`): a tuple of affine curve points over the residue field — distinct
  `x`-coordinates avoiding a prescribed set, nonzero `y`-coordinates — whose tuple datum
  carries a valid, Weierstrass-avoiding fold certificate pack
  (`ChabautyColeman.IsFoldCerts`, `ChabautyColeman.IsFoldAvoid`). It holds for *every*
  curve of positive genus — squarefree reduction at genus one —
  (`ChabautyColeman.hasGoodCenter_of_pos_genus`), by the centre-fold witness
  `ChabautyColeman.exists_centerFoldPack`.
* `ChabautyColeman.TauData` (blueprint `lem:tau-exists`): everything the fold form of
  the translated group law `F_τ` consumes, bundled — the integral Mumford datum with its
  cofactor and Jacobian-unit Bézout certificates over `O`, the `τ`-point tuple splitting
  `u`, the moving points (Hensel roots of the `Y`-side chart), and a valid fold pack
  over `O⟦X;Y⟧` with its Weierstrass avoidance. It exists under `HasGoodCenter`
  (`ChabautyColeman.TauData.exists_of_hasGoodCenter`).

The construction: each residue point Hensel-lifts to a disk center
(`ChabautyColeman.exists_generic_center`), `u` is the product of the lifted linear
factors and `v` interpolates the lifted points by the Chinese remainder theorem
(the lifted `x`-coordinates differ by units, so the linear factors are pairwise
comaximal); the fold pack lifts by Nakayama per step
(`ChabautyColeman.exists_isFoldCerts_ftau`) and its avoidance descends from the residue
configuration (`ChabautyColeman.isFtauFoldAvoid_of_center`).
-/

@[expose] public section

open Function Polynomial IsLocalRing

namespace ChabautyColeman

/-- **Interpolating a Mumford datum through prescribed points** by the Chinese remainder
theorem: for points `(A i, B i)` on `y² = f` whose `x`-coordinates are pairwise unit-separated,
some `v` of degree below `u = ∏ (X - C (A i))` satisfies `u ∣ v² - f` and passes through all of
them. Unit separation is what makes the linear factors pairwise comaximal. -/
theorem exists_interpolating_datum {O : Type*} [CommRing O] [Nontrivial O] {ι : Type*} [Fintype ι]
    {f : O[X]} {A B : ι → O} (hAne : ∀ i j, i ≠ j → IsUnit (A i - A j))
    (hB : ∀ i, B i ^ 2 = f.eval (A i)) :
    ∃ v : O[X], v.degree < (∏ i, (X - C (A i))).degree ∧ (∏ i, (X - C (A i))) ∣ v ^ 2 - f
      ∧ ∀ i, v.eval (A i) = B i := by
  obtain ⟨v, hvdeg, hveval⟩ := exists_degree_lt_eval_eq hAne B
  refine ⟨v, hvdeg, ?_, hveval⟩
  refine Finset.prod_dvd_of_coprime (fun i _ j _ hij ↦
    isCoprime_X_sub_C_of_isUnit_sub (hAne i j hij)) fun i _ ↦ ?_
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, hveval i, hB i]
  ring

section GoodCenter

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- **The residue-level genericity hypothesis** (the content of blueprint node
`lem:tau-generic`): a tuple of affine curve points over the residue field — pairwise
distinct `x`-coordinates avoiding the prescribed set `T`, nonzero `y`-coordinates —
whose tuple datum carries a valid fold certificate pack with Weierstrass avoidance at
every stage of the fold pipeline. The set `T` is the `x`-support avoidance that the
per-disk configuration of `lem:global-generic` needs: `τ` must miss the centres of the
residue disks it counts. -/
def HasGoodCenter (f : O[X]) (T : Set (ResidueField O)) : Prop :=
  ∃ (x y : Fin (genus f) → ResidueField O)
    (d' : FoldCertData (ResidueField O) (genus f)),
    (∀ i, y i ^ 2 = (f.map (residue O)).eval (x i)) ∧ Function.Injective x
      ∧ (∀ i, y i ≠ 0) ∧ (∀ i, ∀ t ∈ T, x i ≠ t)
      ∧ IsFoldCerts (f.map (residue O)) (foldXs x) (foldYs y) (tupleU x) (tupleV x y) d'
      ∧ IsFoldAvoid (f.map (residue O)) (foldXs x) (foldYs y) (tupleU x) (tupleV x y) d'

/-- **`lem:tau-generic`**: the good-center hypothesis holds for *every* curve — monic of
odd degree `2g + 1` with `g ≥ 1`, with squarefree reduction if `g = 1`, over a base whose
residue field is algebraically closed of characteristic `≠ 2` — by the centre-fold
witness (`ChabautyColeman.exists_centerFoldPack`). Everything downstream — in particular
blueprint `thm:main-count` — is proved from this interface. The genus-one proviso is sharp: for
`f` reducing to `X³` in residue characteristic `3` the fold conditions vanish on all
curve points (`LeanPool.HyperellipticCurves.Log.Fold.GenusOne`). -/
theorem hasGoodCenter_of_pos_genus [IsAlgClosed (ResidueField O)]
    [NeZero (2 : ResidueField O)] {f : O[X]}
    {T : Set (ResidueField O)} (hT : T.Finite) (hf : f.Monic) (hg : 0 < genus f)
    (hgen : 2 ≤ genus f ∨ Squarefree (f.map (residue O)))
    (hdeg : f.natDegree = 2 * genus f + 1) : HasGoodCenter f T :=
  exists_centerFoldPack (hf.map (residue O)) (by rw [hf.natDegree_map, hdeg]) hg hgen hT

/-- **`lem:tau-generic` at genus 2**: the special case of
`ChabautyColeman.hasGoodCenter_of_pos_genus` for a quintic. -/
theorem hasGoodCenter_genus_two [IsAlgClosed (ResidueField O)]
    [NeZero (2 : ResidueField O)] {f : O[X]}
    {T : Set (ResidueField O)} (hT : T.Finite) (hf : f.Monic)
    (hdeg : f.natDegree = 5) : HasGoodCenter f T := by
  have hg : genus f = 2 := genus_eq_of_natDegree hdeg
  exact hasGoodCenter_of_pos_genus hT hf (by lia) (.inl hg.ge) (by rw [hdeg, hg])

/-- **The `τ`-datum pack**: everything the fold form of the translated group law `F_τ`
consumes, bundled. Downstream nodes (`thm:Ftau-assoc`, `def:Lam`, `thm:chart-mem`, …)
take a single `TauData O f` parameter instead of a long hypothesis list; it exists under
`ChabautyColeman.HasGoodCenter` (`ChabautyColeman.TauData.exists_of_hasGoodCenter`).
The pack is indexed by `deg u`, not by the genus it agrees with (`hne`): the consumers
work at `deg u` throughout, and an index expressed through `hne` would force them to
transport along it. Beyond the Mumford datum with its certificates, the pack carries the
honest point data of the fold — the `τ`-point tuple splitting `u` and the moving points
of the `Y`-side chart — together with a valid fold certificate pack over `O⟦X;Y⟧` and
its Weierstrass avoidance, both descending to the residue configuration by
construction. -/
structure TauData (O : Type*) [CommRing O] [IsLocalRing O] (f : O[X]) where
  u : O[X]
  v : O[X]
  w : O[X]
  c₁ : O[X]
  c₂ : O[X]
  hu : u.Monic
  hv : v.degree < u.degree
  hw : v ^ 2 - f = u * w
  hbez : c₁ * u + c₂ * (2 * v) = 1
  /-- The datum has the degree the Chabauty–Coleman argument needs: `deg u` is the genus. -/
  hne : u.natDegree = genus f
  /-- The `x`-coordinates of the `τ`-points: `u` splits over `O`. -/
  a : Fin u.natDegree → O
  /-- The `y`-coordinates of the `τ`-points. -/
  b : Fin u.natDegree → O
  hsplit : u = ∏ m, (X - C (a m))
  hbv : ∀ i, v.eval (a i) = b i
  /-- The `τ`-roots are pairwise unit-separated: distinct residue disks. -/
  hunit : ∀ i j, i ≠ j → IsUnit (a i - a j)
  /-- The moving points: the Hensel roots of the `Y`-side chart polynomial. -/
  A : Fin u.natDegree → MvPowerSeries (Fin u.natDegree ⊕ Fin u.natDegree) O
  hroot : ∀ i, (ftauUY u u.natDegree).eval (A i) = 0
  hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i
  /-- The fold certificate pack: one Bézout triple per step of the `2·deg u`-step fold. -/
  d : FoldCertData (MvPowerSeries (Fin u.natDegree ⊕ Fin u.natDegree) O) u.natDegree
  hd : IsFtauFoldCerts A a b hu rfl hv hw hbez d
  /-- Weierstrass avoidance of the fold pipeline over `O⟦X;Y⟧`, descended from the
  residue-field avoidance of the witness pack. -/
  havoid : IsFtauFoldAvoid A a b hu rfl hv hw hbez d
  /-- The reduction of `u` is coprime to the reduced curve polynomial — the good-position
  condition that the auxiliary-point construction consumes. -/
  hcopres : IsCoprime (u.map (residue O)) (f.map (residue O))

section TauDataAPI

variable {f : O[X]}

/-- The `τ`-roots of the pack are roots of its support. -/
theorem TauData.ha (td : TauData O f) (i : Fin td.u.natDegree) : td.u.eval (td.a i) = 0 := by
  rw [td.hsplit, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eval_sub, eval_X, eval_C, sub_self])

/-- The reduction of the pack's support is squarefree: the unit-separated roots stay
distinct in the residue field. This is the good-position condition that the trace-form
pairing `λ` and the per-disk bounds consume. -/
theorem TauData.hsqres (td : TauData O f) : Squarefree (td.u.map (residue O)) := by
  have hres : ∀ i j, i ≠ j → residue O (td.a i) ≠ residue O (td.a j) := by
    intro i j hij h
    have := td.hunit i j hij
    rw [← residue_ne_zero_iff_isUnit] at this
    exact this (by rw [map_sub]; exact sub_eq_zero.mpr h)
  rw [td.hsplit, Polynomial.map_prod]
  simp only [Polynomial.map_sub, map_X, map_C]
  refine Separable.squarefree ?_
  rw [separable_prod_X_sub_C_iff']
  exact fun i _ j _ h ↦ by_contra fun hij ↦ hres i j hij h

end TauDataAPI

end GoodCenter

section Exists

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]

/-- The `τ`-datum pack exists under the genericity hypothesis, with the support avoiding
the prescribed set of residue `x`-values. The residue points Hensel-lift to disk centres,
`u` is the product of the lifted linear factors, `v` interpolates the lifted points by
the Chinese remainder theorem, the fold pack lifts per step by Nakayama
(`ChabautyColeman.exists_isFoldCerts_ftau`), and its avoidance descends from the residue
configuration (`ChabautyColeman.isFtauFoldAvoid_of_center`). -/
theorem TauData.exists_of_hasGoodCenter {f : O[X]} {T : Set (ResidueField O)}
    (h2 : IsUnit (2 : O)) (hf : f.Monic) (hdeg : f.natDegree = 2 * genus f + 1)
    (hgen : HasGoodCenter f T) :
    ∃ td : TauData O f, ∀ t ∈ T, (td.u.map (residue O)).eval t ≠ 0 := by
  classical
  obtain ⟨x, y, d', hcv, hxinj, hy0, hxT, hcc', hav'⟩ := hgen
  -- Hensel-lift the residue points to disk centres
  have hlift (i : Fin (genus f)) : ∃ a b : O,
      residue O a = x i ∧ residue O b = y i ∧ b ^ 2 = f.eval a := by
    obtain ⟨a, b, ha, hb, hsq, -⟩ := exists_generic_center h2 (hcv i) (hy0 i)
    exact ⟨a, b, ha, hb, hsq⟩
  choose a₀ b₀ ha₀ hb₀ hsq₀ using hlift
  have hane (i j : Fin (genus f)) (hij : i ≠ j) : IsUnit (a₀ i - a₀ j) := by
    refine isUnit_sub_of_residue_ne ?_
    rw [ha₀ i, ha₀ j]
    exact fun h ↦ hij (hxinj h)
  -- the support and the interpolated square root
  set u : O[X] := tupleU a₀ with hudef
  have humonic : u.Monic := monic_tupleU a₀
  have hne : u.natDegree = genus f := natDegree_tupleU a₀
  obtain ⟨v, hvdeg, hdvd, hveq⟩ := exists_interpolating_datum hane hsq₀
  obtain ⟨w, hw⟩ := hdvd
  -- the reductions of the datum are the tuple datum of the residue points
  have hured : u.map (residue O) = tupleU x := by
    rw [hudef, map_tupleU]
    exact congrArg tupleU (funext ha₀)
  have hvred : v.map (residue O) = tupleV x y := by
    have hx : (fun i ↦ residue O (a₀ i)) = x := funext ha₀
    have hy : (fun i ↦ residue O (b₀ i)) = y := funext hb₀
    rw [← hx, ← hy]
    exact map_eq_tupleV (residue O) (by rw [hx]; exact hxinj) hvdeg hveq
  -- the Jacobian-unit Bézout certificate over `O`, lifted from the stage-0 avoidance
  have hav0 : IsCoprime (tupleU x) (2 * tupleV x y) := hav' 0 (Nat.zero_le _)
  obtain ⟨A', B', hAB⟩ := hav0
  obtain ⟨c₁, c₂, c₃, hbez0⟩ := exists_bezout_lift (g := 2 * v) (h := 0) humonic ⟨A', B', 0, by
    rw [hured, Polynomial.map_mul, Polynomial.map_ofNat, hvred, Polynomial.map_zero,
      zero_mul, add_zero]
    exact hAB⟩
  rw [mul_zero, add_zero] at hbez0
  -- re-index the point tuple by the degree of the support
  set a : Fin u.natDegree → O := fun i ↦ a₀ (Fin.cast hne i) with hadef
  set b : Fin u.natDegree → O := fun i ↦ b₀ (Fin.cast hne i)
  have hsplit : u = ∏ m : Fin u.natDegree, (X - C (a m)) :=
    (Fintype.prod_equiv (finCongr hne) (fun m ↦ X - C (a m)) (fun i ↦ X - C (a₀ i))
      fun m ↦ rfl).symm
  have hbv (i : Fin u.natDegree) : v.eval (a i) = b i := hveq (Fin.cast hne i)
  have hunit (i j : Fin u.natDegree) (hij : i ≠ j) : IsUnit (a i - a j) :=
    hane _ _ fun h ↦ hij ((finCongr hne).injective h)
  -- the moving points: Hensel roots of the `Y`-side chart
  have hai (i : Fin u.natDegree) : u.eval (a i) = 0 := by
    rw [hudef, eval_tupleU]
    exact Finset.prod_eq_zero (Finset.mem_univ (Fin.cast hne i)) (sub_self _)
  have hder (i : Fin u.natDegree) : IsUnit (u.derivative.eval (a i)) := by
    rw [hudef, hadef, derivative_tupleU_eval]
    exact isUnit_nodeDiff hane _
  choose A hroot hcc using fun i : Fin u.natDegree ↦
    exists_ftauUY_root humonic le_rfl (hai i) (hder i)
  -- the certificate pack: Nakayama lift of the re-indexed residue pack
  have hfdegn : f.natDegree = 2 * u.natDegree + 1 := by rw [hne]; exact hdeg
  have hxsr : (foldXs fun i ↦ residue O (a i)) = foldXs x := by
    have h1 : (fun i : Fin u.natDegree ↦ residue O (a i))
        = fun i ↦ x (Fin.cast hne i) := funext fun i ↦ ha₀ _
    rw [h1, foldXs_cast hne x]
  have hysr : (foldYs fun i ↦ residue O (b i)) = foldYs y := by
    have h1 : (fun i : Fin u.natDegree ↦ residue O (b i))
        = fun i ↦ y (Fin.cast hne i) := funext fun i ↦ hb₀ _
    rw [h1, foldYs_cast hne y]
  have hd'' : IsFoldCerts (f.map (residue O)) (foldXs fun i ↦ residue O (a i))
      (foldYs fun i ↦ residue O (b i)) (u.map (residue O)) (v.map (residue O))
      (fun j ↦ d' (Fin.cast (show 2 * u.natDegree = 2 * genus f by rw [hne]) j)) := by
    rw [hxsr, hysr, hured, hvred]
    exact isFoldCerts_cast hne hcc'
  obtain ⟨D, hD, hDmap⟩ := exists_isFoldCerts_ftau humonic rfl hvdeg hw hbez0 hf hfdegn
    hroot hcc hai hbv _ hd''
  -- avoidance over `O⟦X;Y⟧` by descent from the residue avoidance
  have hav'' : IsFoldAvoid (f.map (residue O)) (foldXs fun i ↦ residue O (a i))
      (foldYs fun i ↦ residue O (b i)) (u.map (residue O)) (v.map (residue O))
      (D.map (mvSeriesResidue _ O)) := by
    rw [hDmap, hxsr, hysr, hured, hvred]
    exact isFoldAvoid_cast hne hav'
  have havoid := isFtauFoldAvoid_of_center humonic rfl hvdeg hw hbez0 hf hfdegn hroot hcc
    hai hbv hD hav''
  -- coprimality of the reduced support with the reduced curve polynomial
  have hcop : IsCoprime (u.map (residue O)) (f.map (residue O)) := by
    rw [hured]
    exact isCoprime_tupleU fun i h ↦ pow_ne_zero 2 (hy0 i) ((hcv i).trans h)
  refine ⟨⟨u, v, w, c₁, c₂, humonic, hvdeg, hw, hbez0, hne, a, b, hsplit, hbv, hunit,
    A, hroot, hcc, D, hD, havoid, hcop⟩, fun t ht ↦ ?_⟩
  rw [hured, eval_tupleU]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ sub_ne_zero.mpr fun h ↦ hxT i t ht h.symm

/-- **`lem:tau-exists`, unconditional at genus 2**: over a local base with algebraically
closed residue field, a genus-2 curve with `2` a unit admits the full `τ`-datum pack,
with support avoiding any prescribed finite set of residue `x`-values. Taking for `T`
the `x`-coordinates of the residue disks to be counted is what the per-disk
configuration of `lem:global-generic` needs (`ChabautyColeman.exists_auxiliary_point`). -/
theorem TauData.exists_genus_two [IsAlgClosed (ResidueField O)] {f : O[X]}
    {T : Set (ResidueField O)} (hT : T.Finite)
    (h2 : IsUnit (2 : O)) (hf : f.Monic) (hdeg : f.natDegree = 5) :
    ∃ td : TauData O f, ∀ t ∈ T, (td.u.map (residue O)).eval t ≠ 0 := by
  have h20 : (2 : ResidueField O) ≠ 0 := by
    rw [← map_ofNat (residue O) 2]
    exact (residue_ne_zero_iff_isUnit 2).mpr h2
  have : NeZero (2 : ResidueField O) := ⟨h20⟩
  have hg : genus f = 2 := genus_eq_of_natDegree hdeg
  exact TauData.exists_of_hasGoodCenter h2 hf (by rw [hdeg, hg])
    (hasGoodCenter_genus_two hT hf hdeg)

end Exists

end ChabautyColeman

end
