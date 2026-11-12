/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3821T1LoopIndex
public import LeanPool.ApollonianSuperharmonic.P3821T1AngularIncrementLaws
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Basic.Real.Basic
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import LeanPool.ApollonianSuperharmonic.P3821T1LoopIndexLaws
public import LeanPool.ApollonianSuperharmonic.GridStepLogLiftDelta
public import Mathlib.Analysis.Normed.Group.Bounded
public import LeanPool.ApollonianSuperharmonic.GridCellCenter
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Basic

-- [TABLET NODE: P3821T1ComponentContours]

/-!
# P3821T1ComponentContours

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ComponentContoursProof

private theorem loop_of_path :
    ∀ (f : C((↑unitInterval : Type), ℂ)), (f : (↑unitInterval : Type) → ℂ) (0 : (↑unitInterval :
        Type)) = (f : (↑unitInterval : Type) → ℂ) (1 : (↑unitInterval : Type)) → ∃ (g : C(Circle,
        ℂ)), (∀ (t : (↑unitInterval : Type)), (g : Circle → ℂ) ((Circle.exp : ℝ → Circle) ((2 :
        ℝ) * Real.pi * (↑t : ℝ))) = (f : (↑unitInterval : Type) → ℂ) t) ∧ Set.range (⇑g : Circle
        → ℂ) ⊆ Set.range (⇑f : (↑unitInterval : Type) → ℂ) := by
  classical
  intro f hf
  let e : unitInterval → Circle := fun t => Circle.exp (2 * Real.pi * (t : ℝ))
  have he : Continuous e := by fun_prop
  have hsurj : Function.Surjective e := by
    intro z
    let a : ℝ := if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi
    have ha : 0 ≤ a ∧ a ≤ 2 * Real.pi := by
      dsimp [a]
      split_ifs with hz
      · constructor
        · exact hz
        · linarith [Complex.arg_le_pi (z : ℂ), Real.pi_pos]
      · constructor
        · linarith [Complex.neg_pi_lt_arg (z : ℂ), Real.pi_pos]
        · linarith
    refine ⟨⟨a / (2 * Real.pi), ⟨div_nonneg ha.1 (by positivity),
      (div_le_one (by positivity)).mpr ha.2⟩⟩, ?_⟩
    change Circle.exp (2 * Real.pi * (a / (2 * Real.pi))) = z
    rw [mul_div_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    dsimp [a]
    split_ifs
    · exact Circle.exp_arg z
    · rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
      exact Circle.exp_arg z
  have hquot : Topology.IsQuotientMap e := he.isClosedMap.isQuotientMap he hsurj
  have hfiber : ∀ x y, e x = e y → f x = f y := by
    intro x y hxy
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hxy
    have hdiff : (x : ℝ) - (y : ℝ) = (n : ℝ) := by
      nlinarith [Real.pi_pos]
    have hnlo : -1 ≤ n := by exact_mod_cast (by linarith [x.2.1, y.2.2] : (-1 : ℝ) ≤ n)
    have hnhi : n ≤ 1 := by exact_mod_cast (by linarith [x.2.2, y.2.1] : (n : ℝ) ≤ 1)
    have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl | rfl
    · have hx : x = 0 := Subtype.ext (by change (x : ℝ) = 0; norm_num at hdiff; linarith [x.2.1,
        y.2.2])
      have hy : y = 1 := Subtype.ext (by change (y : ℝ) = 1; norm_num at hdiff; linarith [x.2.1,
          y.2.2])
      simpa [hx, hy] using hf
    · congr 1
      apply Subtype.ext
      norm_num at hdiff
      linarith
    · have hx : x = 1 := Subtype.ext (by change (x : ℝ) = 1; norm_num at hdiff; linarith [x.2.2,
        y.2.1])
      have hy : y = 0 := Subtype.ext (by change (y : ℝ) = 0; norm_num at hdiff; linarith [x.2.2,
          y.2.1])
      simpa [hx, hy] using hf.symm
  let g : Circle → ℂ := fun z => f (Classical.choose (hsurj z))
  have hcomp : g ∘ e = f := by
    funext t
    apply hfiber
    exact Classical.choose_spec (hsurj (e t))
  have hg : Continuous g := hquot.continuous_iff.mpr (by rw [hcomp]; exact f.continuous)
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · exact fun t => congrFun hcomp t
  · rintro z ⟨w, rfl⟩
    exact ⟨Classical.choose (hsurj w), rfl⟩

private theorem grid_edge_avoids :
    ∀ (r : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), FourNeighborAdjacent a b → ∀
        (t : (↑unitInterval : Type)), (Path.segment ((GaussianInt.toComplex : GaussianInt → ℂ) a)
        ((GaussianInt.toComplex : GaussianInt → ℂ) b) : (↑unitInterval : Type) → ℂ) t ≠
        GridCellCenter r := by
  classical
  intro r a b hab t ht
  have hhalf (m n : ℤ) : (m : ℝ) ≠ (n : ℝ) + 1 / 2 := by
    intro he
    have he' : ((2 * (m - n) : ℤ) : ℝ) = 1 := by push_cast; linarith
    have : 2 * (m - n) = 1 := by exact_mod_cast he'
    omega
  rcases hab with rfl | rfl | rfl | rfl
  · have hi := congrArg Complex.im ht
    simp? [Path.segment_apply, AffineMap.lineMap_apply, GridCellCenter,
      Complex.real_smul, Complex.mul_im] at hi
    rw [← GaussianInt.intCast_im a, ← GaussianInt.intCast_im r] at hi
    exact hhalf a.im r.im (by linarith)
  · have hi := congrArg Complex.im ht
    simp? [Path.segment_apply, AffineMap.lineMap_apply, GridCellCenter,
      Complex.real_smul, Complex.mul_im] at hi
    rw [← GaussianInt.intCast_im a, ← GaussianInt.intCast_im r] at hi
    exact hhalf a.im r.im (by linarith)
  · have hi := congrArg Complex.re ht
    simp? [Path.segment_apply, AffineMap.lineMap_apply, GridCellCenter,
      Complex.real_smul, Complex.mul_re] at hi
    rw [← GaussianInt.intCast_re a, ← GaussianInt.intCast_re r] at hi
    exact hhalf a.re r.re (by linarith)
  · have hi := congrArg Complex.re ht
    simp? [Path.segment_apply, AffineMap.lineMap_apply, GridCellCenter,
      Complex.real_smul, Complex.mul_re] at hi
    rw [← GaussianInt.intCast_re a, ← GaussianInt.intCast_re r] at hi
    exact hhalf a.re r.re (by linarith)

private theorem grid_edge_increment :
    (∀ (r : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
        (∀ t : unitInterval, Path.segment (a : ℂ) (b : ℂ) t ≠ GridCellCenter r)) → (∀ (r :
            GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), FourNeighborAdjacent a b →
        P3821T1AngularIncrement (Path.segment ((GaussianInt.toComplex : GaussianInt → ℂ) a)
        ((GaussianInt.toComplex : GaussianInt → ℂ) b)).toContinuousMap (GridCellCenter r) =
        (Complex.log ((GaussianInt.toComplex : GaussianInt → ℂ) b - GridCellCenter r)).im -
        (Complex.log ((GaussianInt.toComplex : GaussianInt → ℂ) a - GridCellCenter r)).im - (2 :
        ℝ) * Real.pi * (↑(if b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ a.im = r.im ∧ a.re ≤ r.re then (1 : ℤ)
        else if b = a - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ b.im = r.im ∧ a.re ≤ r.re then (-1 : ℤ) else (0 :
        ℤ)) : ℝ)) := by
  classical
  intro grid_edge_avoids r a b hab
  let g := (Path.segment (a : ℂ) (b : ℂ)).toContinuousMap
  obtain ⟨theta, ht, hind, _⟩ := P3821T1AngularIncrementLaws.1 g (GridCellCenter r)
    (grid_edge_avoids r a b hab)
  let L : C(unitInterval, ℂ) :=
    ⟨fun t => (Real.log ‖g t - GridCellCenter r‖ : ℂ) + (theta t : ℂ) * Complex.I,
      by
        apply Continuous.add
        · exact Complex.continuous_ofReal.comp
            ((g.continuous.sub continuous_const).norm.log
              (fun t => norm_ne_zero_iff.mpr
                (sub_ne_zero.mpr (grid_edge_avoids r a b hab t))))
        · fun_prop⟩
  have hL (t : unitInterval) : Complex.exp (L t) =
      (1 - (t : ℝ)) * ((a : ℂ) - GridCellCenter r) +
        (t : ℝ) * ((b : ℂ) - GridCellCenter r) := by
    change Complex.exp ((Real.log ‖g t - GridCellCenter r‖ : ℂ) +
      (theta t : ℂ) * Complex.I) = _
    have hpos : 0 < ‖g t - GridCellCenter r‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (grid_edge_avoids r a b hab t))
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos, ht t]
    have hnorm : (‖g t - GridCellCenter r‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
    rw [mul_div_cancel₀ _ hnorm]
    simp only [g, Path.coe_toContinuousMap, Path.segment_apply,
      AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    ring
  have hdelta := congrArg Complex.im
    (GridStepLogLiftDelta r a b hab L L.continuous hL)
  have htheta := hind theta ht
  simp only [Complex.sub_im, L, ContinuousMap.coe_mk, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hdelta
  convert hdelta using 1
  · exact htheta.symm
  · split_ifs <;> norm_num

private theorem concatenate_paths :
    ∀ {E : Type}, ∀ (source : E → ℂ), ∀ (target : E → ℂ), ∀ (edge : (e : E) → Path (source e)
        (target e)), ∀ (e : E), ∀ (b : E), ∀ (l : List E), (e :: l).getLast? = some b →
        List.IsChain (fun (a b : E) => target a = source b) (e :: l) → ∃ (γ : Path (source e)
        (target b)), (∀ (t : (↑unitInterval : Type)), ∃ d ∈ e :: l, ∃ (s : (↑unitInterval :
        Type)), (γ : (↑unitInterval : Type) → ℂ) t = (edge d : (↑unitInterval : Type) → ℂ) s) ∧ ∀
            (r : ℂ), (∀ d ∈ e :: l, ∀ (s : (↑unitInterval : Type)), (edge d : (↑unitInterval : Type)
        → ℂ) s ≠ r) → P3821T1AngularIncrement γ.toContinuousMap r = (List.map (fun (d : E) =>
        P3821T1AngularIncrement (edge d).toContinuousMap r) (e :: l)).sum := by
  classical
  intro E source target edge e b l hlast hc
  induction l generalizing e with
  | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst b
      refine ⟨edge e, ?_, ?_⟩
      · intro t
        exact ⟨e, by simp, t, rfl⟩
      · intro r hr
        simp
  | cons d l ih =>
      obtain ⟨hed, htail⟩ := List.isChain_cons_cons.mp hc
      obtain ⟨γ, hγ, hsum⟩ := ih d
        (by simpa only [List.getLast?_cons_cons] using hlast) htail
      let γ' : Path (target e) (target b) :=
        γ.cast hed rfl
      refine ⟨(edge e).trans γ', ?_, ?_⟩
      · intro t
        rw [Path.trans_apply]
        split_ifs
        · exact ⟨e, by simp, _, rfl⟩
        · obtain ⟨a, ha, s, hs⟩ := hγ _
          exact ⟨a, List.mem_cons_of_mem _ ha, s, hs⟩
      · intro r hr
        have heAvoid : ∀ t, edge e t ≠ r := fun t => hr e (by simp) t
        have hγAvoid : ∀ t, γ' t ≠ r := by
          intro t
          obtain ⟨a, ha, s, hs⟩ := hγ t
          change γ t ≠ r
          rw [hs]
          exact hr a (List.mem_cons_of_mem _ ha) s
        rw [P3821T1AngularIncrementLaws.2.1 _ _ _ _ (edge e) γ' heAvoid hγAvoid]
        change P3821T1AngularIncrement (edge e).toContinuousMap r +
          P3821T1AngularIncrement γ.toContinuousMap r = _
        rw [hsum r (fun a ha => hr a (List.mem_cons_of_mem _ ha))]
        simp

private theorem loop_of_edges :
    (∀ (f : C(unitInterval, ℂ)), (f 0 = f 1) → (∃ g : C(Circle, ℂ), (∀ t : unitInterval, g
        (Circle.exp (2 * Real.pi * (t : ℝ))) = f t) ∧ Set.range g ⊆ Set.range f)) → ((∀
            {E : Type}, ∀ (source : E → ℂ), ∀ (target : E → ℂ), ∀ (edge : ∀ e, Path (source e)
        (target e)), ∀ (e : E), ∀ (b : E), ∀ (l : List E), ((e :: l).getLast? = some b) →
        ((List.IsChain (fun a b => target a = source b) (e :: l)) → (∃ γ : Path (source e)
        (target b), (∀ t, ∃ d ∈ e :: l, ∃ s, γ t = edge d s) ∧ (∀ r : ℂ, (∀ d ∈ e :: l, ∀ s, edge
        d s ≠ r) → P3821T1AngularIncrement γ.toContinuousMap r = ((e :: l).map (fun d =>
        P3821T1AngularIncrement (edge d).toContinuousMap r)).sum)))) → (∀ {E : Type}, ∀
            [DecidableEq E], ∀ (source : E → ℂ), ∀ (target : E → ℂ), ∀ (edge : (e : E) → Path
            (source
        e) (target e)), ∀ (l : List E), l.Nodup → l ≠ [] → (∀ (e : E), ∀ (he : e ∈ l), target e =
        source (l.next e he)) → ∃ (g : C(Circle, ℂ)), (∀ (z : Circle), ∃ e ∈ l, ∃ (t :
        (↑unitInterval : Type)), (g : Circle → ℂ) z = (edge e : (↑unitInterval : Type) → ℂ) t) ∧
        ∀ (r : ℂ), (∀ e ∈ l, ∀ (t : (↑unitInterval : Type)), (edge e : (↑unitInterval : Type) →
        ℂ) t ≠ r) → P3821T1LoopIndex g r = (List.map (fun (e : E) => P3821T1AngularIncrement
        (edge e).toContinuousMap r) l).sum / ((2 : ℝ) * Real.pi))) := by
  classical
  intro loop_of_path concatenate_paths E typeclassInstance0 source target edge l hl hne hnext
  have hchain : List.IsChain (fun a b => target a = source b) l := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hn := hnext l[i] (List.getElem_mem (by omega))
    simpa only [List.next_getElem l hl i (by omega), Nat.mod_eq_of_lt hi] using hn
  have hclose : target (l.getLast hne) = source (l.head hne) := by
    have hn := hnext (l.getLast hne) (List.getLast_mem hne)
    rwa [List.next_getLast_eq_head l hne hl] at hn
  cases l with
  | nil => exact (hne rfl).elim
  | cons e l =>
      obtain ⟨γ, hγ, hsum⟩ := concatenate_paths source target edge e
        ((e :: l).getLast hne) l
        (List.getLast?_eq_getLast_of_ne_nil hne) hchain
      have hclosed : γ.toContinuousMap 0 = γ.toContinuousMap 1 := by
        simp only [Path.coe_toContinuousMap, Path.source, Path.target]
        exact hclose.symm
      obtain ⟨g, hg, hrange⟩ := loop_of_path γ.toContinuousMap hclosed
      refine ⟨g, ?_, ?_⟩
      · intro z
        obtain ⟨t, ht⟩ := hrange ⟨z, rfl⟩
        obtain ⟨d, hd, s, hs⟩ := hγ t
        exact ⟨d, hd, s, ht.symm.trans hs⟩
      · intro r hr
        unfold P3821T1LoopIndex
        have hmaps : g.comp ⟨fun t : unitInterval => Circle.exp
            (2 * Real.pi * (t : ℝ)), by fun_prop⟩ = γ.toContinuousMap := by
          ext t
          exact hg t
        rw [hmaps, hsum r hr]

private theorem cycles_of_perm :
    ∀ {E : Type}, ∀ [Fintype E], ∀ [DecidableEq E], ∀ (σ : Equiv.Perm E), (∀ (e : E), (σ : E → E)
        e ≠ e) → ∃ (n : ℕ) (l : Fin n → List E), (∀ (j : Fin n), (l j).Nodup ∧ l
        j ≠ [] ∧ ∀ (e : E), ∀ (he : e ∈ l j), (l j).next e he = (σ : E → E) e) ∧ ∀ (f : E → ℝ), ∑
        j : Fin n, (List.map f (l j)).sum = ∑ e : E, f e := by
  classical
  intro E typeclassInstance0 typeclassInstance1 σ hσ
  classical
  let J := {c : Equiv.Perm E // c ∈ σ.cycleFactorsFinset}
  have hnon (c : J) : c.val.support.Nonempty :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
  let base (c : J) : E := Classical.choose (hnon c)
  have hb (c : J) : base c ∈ c.val.support := Classical.choose_spec (hnon c)
  let L (c : J) : List E := σ.toList (base c)
  have hcycle (c : J) : c.val = σ.cycleOf (base c) :=
    Equiv.Perm.cycle_is_cycleOf (hb c) c.property
  have hL (c : J) : (L c).toFinset = c.val.support := by
    ext e
    simp only [L, List.mem_toFinset, Equiv.Perm.mem_toList_iff,
      hcycle c, Equiv.Perm.mem_support_cycleOf_iff]
  have hprop (c : J) : (L c).Nodup ∧ L c ≠ [] ∧
      ∀ e (he : e ∈ L c), (L c).next e he = σ e := by
    refine ⟨σ.nodup_toList _, ?_, ?_⟩
    · exact fun hnil => (hσ (base c))
        (Equiv.Perm.notMem_support.mp (σ.toList_eq_nil_iff.mp hnil))
    · exact fun e he => σ.next_toList_eq_apply (base c) e he
  have hcover : σ.cycleFactorsFinset.biUnion Equiv.Perm.support = Finset.univ := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp
      (Equiv.Perm.mem_support.mpr (hσ e))
  have hdisj : (σ.cycleFactorsFinset : Set (Equiv.Perm E)).PairwiseDisjoint
      Equiv.Perm.support := by
    intro c hc d hd hcd
    exact (σ.cycleFactorsFinset_pairwise_disjoint hc hd hcd).disjoint_support
  have hsum (f : E → ℝ) : ∑ c : J, ((L c).map f).sum = ∑ e, f e := by
    have hlist (l : List E) (hl : l.Nodup) : (l.map f).sum = ∑ e ∈ l.toFinset, f e := by
      induction l with
      | nil => simp
      | cons e l ih =>
          simp only [List.nodup_cons] at hl
          simp [List.toFinset_cons, ih hl.2, hl.1]
    calc
      ∑ c : J, ((L c).map f).sum = ∑ c : J, ∑ e ∈ c.val.support, f e := by
        apply Finset.sum_congr rfl
        intro c _
        rw [hlist _ (hprop c).1, hL c]
      _ = ∑ c ∈ σ.cycleFactorsFinset, ∑ e ∈ c.support, f e := by
        exact (Finset.sum_subtype σ.cycleFactorsFinset (fun _ => Iff.rfl)
          (fun c => ∑ e ∈ c.support, f e)).symm
      _ = ∑ e, f e := by rw [← Finset.sum_biUnion hdisj, hcover]
  let eqv : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun j => L (eqv j), fun j => hprop (eqv j), ?_⟩
  intro f
  exact (Fintype.sum_equiv eqv _ _ (fun _ => rfl)).trans (hsum f)

private theorem grid_boundary_sum :
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    let neighbor (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u - ⟨0, 1⟩, u + 1, u + ⟨0, 1⟩, u - 1]
    (∀ (u : GaussianInt), ∀ (k : Fin 4), neighbor (neighbor u k) (k + 2) = u ∧ corner (neighbor u
        k) (k + 2) = corner u (k + 1) ∧ corner (neighbor u k) ((k + 2) + 1) = corner u k) → ((∀
            (u : GaussianInt), ∀ (k : Fin 4), FourNeighborAdjacent (corner u k) (corner u (k +
            1))) →
        (∀ (D : Finset GaussianInt), ∀ (f : GaussianInt → GaussianInt → ℝ), (∀ (a : LatticeCell),
            ∀ (b : LatticeCell), FourNeighborAdjacent a b → f b a = -f a b) → ∑ e :
        { e : ↥D × Fin (4 : ℕ) // neighbor (↑e.1 : GaussianInt) e.2 ∉ D }, f (corner (↑(↑e : ↥D ×
        Fin (4 : ℕ)).1 : GaussianInt) (↑e : ↥D × Fin (4 : ℕ)).2) (corner (↑(↑e : ↥D × Fin (4 :
        ℕ)).1 : GaussianInt) ((↑e : ↥D × Fin (4 : ℕ)).2 + (1 : Fin (4 : ℕ)))) = ∑ u ∈ D, (f u (u
        + (1 : GaussianInt)) + f (u + (1 : GaussianInt)) (u + (1 : GaussianInt) + ⟨(0 : ℤ), (1 :
        ℤ)⟩) + f (u + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) (u + ⟨(0 : ℤ), (1 : ℤ)⟩) + f (u +
        ⟨(0 : ℤ), (1 : ℤ)⟩) u))) := by
  classical
  intro corner neighbor dart_reverse dart_adjacent D f hanti
  classical
  let A := D × Fin 4
  let I := {e : A // neighbor e.1.val e.2 ∈ D}
  let rev : I → I := fun e =>
    ⟨(⟨neighbor e.val.1.val e.val.2, e.property⟩, e.val.2 + 2), by
      change neighbor (neighbor e.val.1.val e.val.2) (e.val.2 + 2) ∈ D
      rw [(dart_reverse _ _).1]
      exact e.val.1.property⟩
  have hrev : Function.Involutive rev := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact (dart_reverse _ _).1
    · change (e.val.2 + 2) + 2 = e.val.2
      have hk (k : Fin 4) : (k + 2) + 2 = k := by fin_cases k <;> rfl
      exact hk _
  let ρ : Equiv.Perm I := ⟨rev, rev, hrev, hrev⟩
  let F : A → ℝ := fun e => f (corner e.1.val e.2) (corner e.1.val (e.2 + 1))
  have hantiI (e : I) : F (ρ e).val = -F e.val := by
    change f (corner (neighbor e.val.1.val e.val.2) (e.val.2 + 2))
      (corner (neighbor e.val.1.val e.val.2) ((e.val.2 + 2) + 1)) =
        -f (corner e.val.1.val e.val.2) (corner e.val.1.val (e.val.2 + 1))
    rw [(dart_reverse _ _).2.1, (dart_reverse _ _).2.2]
    exact hanti _ _ (dart_adjacent _ _)
  have hsumI : (∑ e : I, F e.val) = 0 := by
    have heq := Fintype.sum_equiv ρ (fun e => F e.val) (fun e => -F e.val)
      (fun e => by rw [hantiI, neg_neg])
    rw [Finset.sum_neg_distrib] at heq
    linarith
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun e : A => neighbor e.1.val e.2 ∈ D) F
  rw [hsumI, zero_add] at hsplit
  change (∑ e : {e : A // neighbor e.1.val e.2 ∉ D}, F e.val) = _
  rw [hsplit, Fintype.sum_prod_type]
  have hfour (u : GaussianInt) :
      (∑ k : Fin 4, f (corner u k) (corner u (k + 1))) =
      f u (u + 1) + f (u + 1) (u + 1 + ⟨0, 1⟩) +
        f (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) + f (u + ⟨0, 1⟩) u := by
    simp [Fin.sum_univ_succ, corner, add_assoc]
  simp only [F, hfour]
  exact (Finset.sum_subtype D (fun _ => Iff.rfl) (fun u =>
    f u (u + 1) + f (u + 1) (u + 1 + ⟨0, 1⟩) +
      f (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) + f (u + ⟨0, 1⟩) u)).symm

private theorem square_step :
    let rayStep (r a b : GaussianInt) : ℤ :=
      if b = a + ⟨0, 1⟩ ∧ a.im = r.im ∧ a.re ≤ r.re then 1
      else if b = a - ⟨0, 1⟩ ∧ b.im = r.im ∧ a.re ≤ r.re then -1
      else 0
    ∀ (r : GaussianInt), ∀ (u : GaussianInt), rayStep r u (u + (1 : GaussianInt)) + rayStep r (u
        + (1 : GaussianInt)) (u + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) + rayStep r (u + (1 :
        GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) (u + ⟨(0 : ℤ), (1 : ℤ)⟩) + rayStep r (u + ⟨(0 : ℤ), (1
        : ℤ)⟩) u = if u = r then (-1 : ℤ) else (0 : ℤ) := by
  classical
  intro rayStep r u
  by_cases him : u.im = r.im
  · by_cases hre : u.re = r.re
    · have hue : u = r := Zsqrtd.ext hre him
      simp [rayStep, Zsqrtd.ext_iff, hue]
    · simp [rayStep, Zsqrtd.ext_iff, him, hre]
      omega
  · simp [rayStep, Zsqrtd.ext_iff, him]
    omega

private theorem square_increment :
    (∀ (r : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
        (P3821T1AngularIncrement (Path.segment (a : ℂ) (b : ℂ)).toContinuousMap (GridCellCenter
        r) = (Complex.log ((b : ℂ) - GridCellCenter r)).im - (Complex.log ((a : ℂ) -
        GridCellCenter r)).im - 2 * Real.pi * (if b = a + ⟨0, 1⟩ ∧ a.im = r.im ∧ a.re ≤ r.re then
        (1 : ℤ) else if b = a - ⟨0, 1⟩ ∧ b.im = r.im ∧ a.re ≤ r.re then (-1 : ℤ) else 0))) → (
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    (∀ (u : GaussianInt), ∀ (k : Fin 4), FourNeighborAdjacent (corner u k) (corner u (k + 1))) → (
    let rayStep (r a b : GaussianInt) : ℤ :=
      if b = a + ⟨0, 1⟩ ∧ a.im = r.im ∧ a.re ≤ r.re then 1
      else if b = a - ⟨0, 1⟩ ∧ b.im = r.im ∧ a.re ≤ r.re then -1
      else 0
    (∀ (r : GaussianInt), ∀ (u : GaussianInt), rayStep r u (u + 1) + rayStep r (u + 1) (u + 1 +
        ⟨0, 1⟩) + rayStep r (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) + rayStep r (u + ⟨0, 1⟩) u = if u = r
        then -1 else 0) → (∀ (r : GaussianInt), ∀ (u : GaussianInt), ∑ k : Fin (4 : ℕ),
        P3821T1AngularIncrement (Path.segment ((GaussianInt.toComplex : GaussianInt → ℂ)
        (corner u k)) ((GaussianInt.toComplex : GaussianInt → ℂ) (corner u (k + (1 : Fin (4 :
        ℕ)))))).toContinuousMap (GridCellCenter r) = (2 : ℝ) * Real.pi * if u = r then (1 : ℝ)
        else (0 : ℝ)))) := by
  classical
  intro grid_edge_increment corner dart_adjacent rayStep square_step r u
  let inc (a b : GaussianInt) := P3821T1AngularIncrement
    (Path.segment (a : ℂ) (b : ℂ)).toContinuousMap (GridCellCenter r)
  have hinc (a b : GaussianInt) (hab : FourNeighborAdjacent a b) :
      inc a b = (Complex.log ((b : ℂ) - GridCellCenter r)).im -
        (Complex.log ((a : ℂ) - GridCellCenter r)).im - 2 * Real.pi * (rayStep r a b : ℝ) :=
    grid_edge_increment r a b hab
  have hfour : (∑ k : Fin 4, inc (corner u k) (corner u (k + 1))) =
      inc u (u + 1) + inc (u + 1) (u + 1 + ⟨0, 1⟩) +
        inc (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) + inc (u + ⟨0, 1⟩) u := by
    simp [Fin.sum_univ_succ, corner, add_assoc]
  change (∑ k : Fin 4, inc (corner u k) (corner u (k + 1))) = _
  rw [hfour]
  calc
    _ = -(2 * Real.pi) * ((rayStep r u (u + 1) +
        rayStep r (u + 1) (u + 1 + ⟨0, 1⟩) +
        rayStep r (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) +
        rayStep r (u + ⟨0, 1⟩) u : ℤ) : ℝ) := by
      have ha : FourNeighborAdjacent u (u + 1) := dart_adjacent u 0
      have hb : FourNeighborAdjacent (u + 1) (u + 1 + ⟨0, 1⟩) := dart_adjacent u 1
      have hc : FourNeighborAdjacent (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) := dart_adjacent u 2
      have hd : FourNeighborAdjacent (u + ⟨0, 1⟩) u := dart_adjacent u 3
      rw [hinc _ _ ha, hinc _ _ hb, hinc _ _ hc, hinc _ _ hd]
      push_cast
      ring
    _ = _ := by rw [square_step]; split_ifs <;> norm_num

private theorem grid_contours :
    (∀ (r : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
        (∀ t : unitInterval, Path.segment (a : ℂ) (b : ℂ) t ≠ GridCellCenter r)) → ((∀
            {E : Type}, ∀ [DecidableEq E], ∀ (source : E → ℂ), ∀ (target : E → ℂ), ∀ (edge : ∀ e,
            Path (source e) (target e)), ∀ (l : List E), (l.Nodup) → ((l ≠ []) → ((∀ e, ∀ (he : e ∈
        l), target e = source (l.next e he)) → (∃ g : C(Circle, ℂ), (∀ z, ∃ e ∈ l, ∃ t, g z =
        edge e t) ∧ (∀ r : ℂ, (∀ e ∈ l, ∀ t, edge e t ≠ r) → P3821T1LoopIndex g r = (l.map (fun
        e => P3821T1AngularIncrement (edge e).toContinuousMap r)).sum / (2 * Real.pi)))))) →
        ((∀ {E : Type}, ∀ [Fintype E], ∀ [DecidableEq E], ∀ (σ : Equiv.Perm E), (∀ e, σ e ≠ e) →
        (∃ n : ℕ, ∃ l : Fin n → List E, (∀ j, (l j).Nodup ∧ (l j) ≠ [] ∧ ∀ e, ∀ (he : e ∈ l j),
            (l j).next e he = σ e) ∧ (∀ f : E → ℝ, ∑ j, ((l j).map f).sum = ∑ e, f e))) → ((∀
            {E : Type}, ∀ {V : Type}, ∀ [Fintype E], ∀ [DecidableEq E], ∀ [DecidableEq V], ∀
            (source : E → V), ∀ (target : E → V), (∀ v, Fintype.card {e // target e = v} =
            Fintype.card
        {e // source e = v}) → (∃ σ : Equiv.Perm E, ∀ e, source (σ e) = target e)) → (
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    let neighbor (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u - ⟨0, 1⟩, u + 1, u + ⟨0, 1⟩, u - 1]
    (∀ (u : GaussianInt), ∀ (k : Fin 4), FourNeighborAdjacent (corner u k) (corner u (k + 1))) →
        ((∀ (D : Finset GaussianInt), ∀ (f : GaussianInt → GaussianInt → ℝ), (∀ a, ∀ b,
            FourNeighborAdjacent a b → f b a = -f a b) → ((∑ e :
        {e : D × Fin 4 // neighbor e.1.val e.2 ∉ D}, f (corner e.val.1.val e.val.2) (corner
        e.val.1.val (e.val.2 + 1))) = ∑ u ∈ D, (f u (u + 1) + f (u + 1) (u + 1 + ⟨0, 1⟩) + f (u +
        1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) + f (u + ⟨0, 1⟩) u))) → ((∀ (r : GaussianInt), ∀ (u :
            GaussianInt), (∑ k : Fin 4, P3821T1AngularIncrement (Path.segment (corner u k : ℂ)
        (corner u (k + 1) : ℂ)).toContinuousMap (GridCellCenter r)) = 2 * Real.pi * (if u = r
        then 1 else 0)) → (∀ (D : Finset GaussianInt), ∃ (n : ℕ) (g : Fin n → C(Circle, ℂ)), (∀
            (j : Fin n), ∀ (z : Circle), ∃ u ∈ D, ∃ (k : Fin (4 : ℕ)), neighbor u k ∉ D ∧ ∃ (t :
        (↑unitInterval : Type)), (g j : Circle → ℂ) z = (Path.segment ((GaussianInt.toComplex :
        GaussianInt → ℂ) (corner u k)) ((GaussianInt.toComplex : GaussianInt → ℂ) (corner u (k +
        (1 : Fin (4 : ℕ))))) : (↑unitInterval : Type) → ℂ) t) ∧ ∀ (r : GaussianInt), ∑ j : Fin n,
        P3821T1LoopIndex (g j) (GridCellCenter r) = if r ∈ D then (1 : ℝ) else (0 : ℝ))))))))
        := by
  classical
  intro grid_edge_avoids loop_of_edges cycles_of_perm balance_permutation corner neighbor
      dart_adjacent grid_boundary_sum square_increment D
  classical
  let E := {e : D × Fin 4 // neighbor e.1.val e.2 ∉ D}
  let src : E → GaussianInt := fun e => corner e.val.1.val e.val.2
  let dst : E → GaussianInt := fun e => corner e.val.1.val (e.val.2 + 1)
  have hadj (e : E) : FourNeighborAdjacent (src e) (dst e) := dart_adjacent _ _
  have hneq (e : E) : src e ≠ dst e := by
    have h := hadj e
    rcases h with h | h | h | h <;>
      rw [h] <;> simp [Zsqrtd.ext_iff] <;> omega
  have hbalance (v : GaussianInt) :
      Fintype.card {e : E // dst e = v} = Fintype.card {e : E // src e = v} := by
    let f (a b : GaussianInt) : ℝ := (if a = v then 1 else 0) - (if b = v then 1 else 0)
    have hs := grid_boundary_sum D f (fun a b _ => by dsimp [f]; ring)
    have hzero : (∑ u ∈ D, (f u (u + 1) + f (u + 1) (u + 1 + ⟨0, 1⟩) +
        f (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) + f (u + ⟨0, 1⟩) u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      dsimp [f]
      ring
    rw [hzero] at hs
    change (∑ e : E, ((if src e = v then (1 : ℝ) else 0) -
      (if dst e = v then 1 else 0))) = 0 at hs
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole] at hs
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact_mod_cast (by linarith [hs] :
      ((Finset.univ.filter (fun e : E => dst e = v)).card : ℝ) =
        (Finset.univ.filter (fun e : E => src e = v)).card)
  obtain ⟨σ, hσ⟩ := balance_permutation src dst hbalance
  have hσne (e : E) : σ e ≠ e := by
    intro h
    apply hneq e
    simpa [h] using hσ e
  obtain ⟨n, l, hl, hsum⟩ := cycles_of_perm σ hσne
  let edge (e : E) : Path (src e : ℂ) (dst e : ℂ) := Path.segment _ _
  have hex (j : Fin n) :
      ∃ g : C(Circle, ℂ),
        (∀ z, ∃ e ∈ l j, ∃ t, g z = edge e t) ∧
        (∀ r : ℂ, (∀ e ∈ l j, ∀ t, edge e t ≠ r) →
          P3821T1LoopIndex g r = ((l j).map (fun e =>
            P3821T1AngularIncrement (edge e).toContinuousMap r)).sum /
              (2 * Real.pi)) := by
    apply loop_of_edges (fun e => (src e : ℂ)) (fun e => (dst e : ℂ)) edge
      (l j) (hl j).1 (hl j).2.1
    intro e he
    rw [(hl j).2.2 e he]
    exact congrArg GaussianInt.toComplex (hσ e).symm
  choose g hg hi using hex
  refine ⟨n, g, ?_, ?_⟩
  · intro j z
    obtain ⟨e, he, t, ht⟩ := hg j z
    exact ⟨e.val.1.val, e.val.1.property, e.val.2, e.property, t, ht⟩
  · intro r
    let inc (a b : GaussianInt) := P3821T1AngularIncrement
      (Path.segment (a : ℂ) (b : ℂ)).toContinuousMap (GridCellCenter r)
    have hindices (j : Fin n) :
        P3821T1LoopIndex (g j) (GridCellCenter r) =
          ((l j).map (fun e => inc (src e) (dst e))).sum / (2 * Real.pi) :=
      hi j _ (fun e _ => grid_edge_avoids r _ _ (hadj e))
    have hanti (a b : GaussianInt) (hab : FourNeighborAdjacent a b) :
        inc b a = -inc a b := by
      have hh := P3821T1AngularIncrementLaws.2.2 (a : ℂ) (b : ℂ)
        (GridCellCenter r) (Path.segment _ _) (grid_edge_avoids r a b hab)
      simpa only [inc, Path.segment_symm] using hh
    have hledger := grid_boundary_sum D inc hanti
    have hsquare (u : GaussianInt) :
        inc u (u + 1) + inc (u + 1) (u + 1 + ⟨0, 1⟩) +
          inc (u + 1 + ⟨0, 1⟩) (u + ⟨0, 1⟩) + inc (u + ⟨0, 1⟩) u =
          2 * Real.pi * (if u = r then 1 else 0) := by
      have h := square_increment r u
      simpa only [Fin.sum_univ_four, corner, Matrix.cons_val,
        Fin.reduceFinMk, Fin.reduceAdd] using h
    calc
      ∑ j, P3821T1LoopIndex (g j) (GridCellCenter r) =
          (∑ e : E, inc (src e) (dst e)) / (2 * Real.pi) := by
        simp only [hindices, ← Finset.sum_div]
        rw [hsum]
      _ = (∑ u ∈ D, 2 * Real.pi * (if u = r then 1 else 0)) /
          (2 * Real.pi) := by
        rw [hledger]
        congr 1
        apply Finset.sum_congr rfl
        exact fun u _ => hsquare u
      _ = if r ∈ D then 1 else 0 := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
        split_ifs <;> simp [Real.pi_ne_zero]

private theorem box_dist :
    let box (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) ≤ z.re ∧ z.re ≤ (u.re : ℝ) + 1 ∧
        (u.im : ℝ) ≤ z.im ∧ z.im ≤ (u.im : ℝ) + 1
    (∀ (u : GaussianInt), (GridCellCenter u).re = (u.re : ℝ) + 1 / 2) → ((∀ (u : GaussianInt),
        (GridCellCenter u).im = (u.im : ℝ) + 1 / 2) → (∀ (u : GaussianInt), ∀ (z : ℂ), box u z →
        ‖z - GridCellCenter u‖ ≤ (1 : ℝ))) := by
  classical
  intro box center_re center_im u z hz
  have hr : |(z - GridCellCenter u).re| ≤ 1 / 2 := by
    rw [Complex.sub_re, center_re, abs_le]
    dsimp [box] at hz
    constructor <;> linarith [hz.1, hz.2.1]
  have hi : |(z - GridCellCenter u).im| ≤ 1 / 2 := by
    rw [Complex.sub_im, center_im, abs_le]
    dsimp [box] at hz
    constructor <;> linarith [hz.2.2.1, hz.2.2.2]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

private theorem edge_box :
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    let neighbor (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u - ⟨0, 1⟩, u + 1, u + ⟨0, 1⟩, u - 1]
    let box (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) ≤ z.re ∧ z.re ≤ (u.re : ℝ) + 1 ∧
        (u.im : ℝ) ≤ z.im ∧ z.im ≤ (u.im : ℝ) + 1
    ∀ (u : GaussianInt), ∀ (k : Fin (4 : ℕ)), ∀ (t : (↑unitInterval : Type)), box u
        ((Path.segment ((GaussianInt.toComplex : GaussianInt → ℂ) (corner u k))
        ((GaussianInt.toComplex : GaussianInt → ℂ) (corner u (k + (1 : Fin (4 : ℕ))))) :
        (↑unitInterval : Type) → ℂ) t) ∧ box (neighbor u k) ((Path.segment
        ((GaussianInt.toComplex : GaussianInt → ℂ) (corner u k)) ((GaussianInt.toComplex :
        GaussianInt → ℂ) (corner u (k + (1 : Fin (4 : ℕ))))) : (↑unitInterval : Type) → ℂ) t) := by
  classical
  intro corner neighbor box u k t
  change box u ((t : ℝ) • ((corner u (k + 1) : ℂ) - (corner u k : ℂ)) + (corner u k : ℂ)) ∧
    box (neighbor u k) ((t : ℝ) • ((corner u (k + 1) : ℂ) - (corner u k : ℂ)) + (corner u k : ℂ))
  fin_cases k <;>
    simp only [corner, neighbor, Fin.reduceFinMk, Fin.reduceAdd, Matrix.cons_val,
      box, Complex.real_smul, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
      ← GaussianInt.intCast_re, ← GaussianInt.intCast_im, Zsqrtd.re_add,
      Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
      Int.cast_add, Int.cast_sub, Int.cast_one]
  all_goals repeat' apply And.intro
  all_goals nlinarith [t.2.1, t.2.2]

private theorem shift_exists :
    ∀ (a : ℝ), ∀ (b : ℝ), ∃ (s : ℝ), (0 : ℝ) < s ∧ s < (1 : ℝ) ∧ (∀ (n : ℤ), a - s ≠ (↑n : ℝ)) ∧
        ∀ (n : ℤ), b - s ≠ (↑n : ℝ) := by
  classical
  intro a b
  obtain ⟨s, hs, hnot⟩ := (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).exists_notMem_finset
    ({Int.fract a, Int.fract b} : Finset ℝ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  refine ⟨s, hs.1, hs.2, ?_, ?_⟩
  · intro n hn
    exact hnot.1 (Int.fract_eq_iff.mpr ⟨hs.1.le, hs.2, n, hn⟩).symm
  · intro n hn
    exact hnot.2 (Int.fract_eq_iff.mpr ⟨hs.1.le, hs.2, n, hn⟩).symm

private theorem segment_hits :
    ∀ (K : Set ℂ), ∀ (p : ℂ), ∀ (a : ℂ), ∀ (b : ℂ), a ∈ connectedComponentIn Kᶜ p → b ∉
        connectedComponentIn Kᶜ p → ∃ (t : (↑unitInterval : Type)), (Path.segment a b :
        (↑unitInterval : Type) → ℂ) t ∈ K := by
  classical
  intro K p a b ha hb
  by_contra h
  have hav : Set.range (Path.segment a b) ⊆ Kᶜ := by
    rintro z ⟨t, rfl⟩
    exact fun hz => h ⟨t, hz⟩
  have hcomp := (isPreconnected_range (Path.segment a b).continuous).subset_connectedComponentIn
    (Path.segment a b).source_mem_range hav
  have hbm : b ∈ connectedComponentIn Kᶜ a := hcomp (Path.segment a b).target_mem_range
  rw [← connectedComponentIn_eq ha] at hbm
  exact hb hbm

private theorem finite_centers :
    (∀ (u : GaussianInt), (GridCellCenter u).re = (u.re : ℝ) + 1 / 2) → ((∀ (u : GaussianInt),
        (GridCellCenter u).im = (u.im : ℝ) + 1 / 2) → (∀ (U : Set ℂ), Bornology.IsBounded U → ∀
        (h : ℝ), (0 : ℝ) < h → ∀ (o : ℂ), {u : GaussianInt | (↑h : ℂ) * GridCellCenter u + o ∈
        U}.Finite)) := by
  classical
  intro center_re center_im U hU h hh o
  obtain ⟨R, hR⟩ := hU.exists_norm_le
  obtain ⟨M, hM⟩ := exists_nat_gt ((R + ‖o‖) / h + 1)
  let B : Set (ℤ × ℤ) := Set.Icc (-(M : ℤ)) M ×ˢ Set.Icc (-(M : ℤ)) M
  have hB : B.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hinj : Function.Injective (fun u : GaussianInt => (u.re, u.im)) := by
    intro a b he
    exact Zsqrtd.ext (congrArg Prod.fst he) (congrArg Prod.snd he)
  apply (hB.preimage hinj.injOn).subset
  intro u hu
  have hnorm : h * ‖GridCellCenter u‖ ≤ R + ‖o‖ := by
    have hhNorm : ‖(h : ℂ)‖ = h := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    calc
      h * ‖GridCellCenter u‖ = ‖(h : ℂ) * GridCellCenter u‖ := by rw [norm_mul, hhNorm]
      _ = ‖((h : ℂ) * GridCellCenter u + o) - o‖ := by congr 1; ring
      _ ≤ ‖(h : ℂ) * GridCellCenter u + o‖ + ‖o‖ := norm_sub_le _ _
      _ ≤ R + ‖o‖ := by linarith [hR _ hu]
  have hnormM : ‖GridCellCenter u‖ + 1 < M := by
    have hl : ‖GridCellCenter u‖ ≤ (R + ‖o‖) / h :=
      (le_div_iff₀ hh).mpr (by nlinarith [hnorm])
    linarith
  have hr := abs_le.mp (Complex.abs_re_le_norm (GridCellCenter u))
  have hi := abs_le.mp (Complex.abs_im_le_norm (GridCellCenter u))
  rw [center_re] at hr
  rw [center_im] at hi
  change (-(M : ℤ) ≤ u.re ∧ u.re ≤ M) ∧ (-(M : ℤ) ≤ u.im ∧ u.im ≤ M)
  have hbounds : (-(M : ℝ) ≤ (u.re : ℝ) ∧ (u.re : ℝ) ≤ M) ∧
      (-(M : ℝ) ≤ (u.im : ℝ) ∧ (u.im : ℝ) ≤ M) := by
    constructor <;> constructor <;> linarith [hr.1, hr.2, hi.1, hi.2]
  exact_mod_cast hbounds

private theorem hrp :
    ∀ (p : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → (∀ (s : ℝ), (∀ (n : ℤ), p.re / h - s ≠ (↑n : ℝ)) → (∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rp : ℂ := (p - o) / (h : ℂ)
    ∀ n : ℤ, rp.re ≠ n)) := by
  classical
  intro p η εp εq h hh s hspr t o rp n hn
  have : p.re / h - s = n := by
    dsimp [rp, o] at hn ⊢
    simp only [Complex.div_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hn
    simp only [Complex.normSq_ofReal] at hn
    field_simp [ne_of_gt hh] at hn ⊢
    nlinarith
  exact hspr n this

private theorem hip :
    ∀ (p : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → (∀ (s : ℝ), ∀ (t : ℝ), (∀ (n : ℤ), p.im / h - t ≠ (↑n : ℝ)) → (
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rp : ℂ := (p - o) / (h : ℂ)
    ∀ n : ℤ, rp.im ≠ n)) := by
  classical
  intro p η εp εq h hh s t htsp o rp n hn
  have : p.im / h - t = n := by
    dsimp [rp, o] at hn ⊢
    simp only [Complex.div_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, add_zero] at hn
    simp only [Complex.normSq_ofReal] at hn
    field_simp [ne_of_gt hh] at hn ⊢
    nlinarith
  exact htsp n this

private theorem hrq :
    ∀ (q : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → (∀ (s : ℝ), (∀ (n : ℤ), q.re / h - s ≠ (↑n : ℝ)) → (∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rq : ℂ := (q - o) / (h : ℂ)
    ∀ n : ℤ, rq.re ≠ n)) := by
  classical
  intro q η εp εq h hh s hspq t o rq n hn
  have : q.re / h - s = n := by
    dsimp [rq, o] at hn ⊢
    simp only [Complex.div_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hn
    simp only [Complex.normSq_ofReal] at hn
    field_simp [ne_of_gt hh] at hn ⊢
    nlinarith
  exact hspq n this

private theorem hiq :
    ∀ (q : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → (∀ (s : ℝ), ∀ (t : ℝ), (∀ (n : ℤ), q.im / h - t ≠ (↑n : ℝ)) → (
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rq : ℂ := (q - o) / (h : ℂ)
    ∀ n : ℤ, rq.im ≠ n)) := by
  classical
  intro q η εp εq h hh s t htq o rq n hn
  have : q.im / h - t = n := by
    dsimp [rq, o] at hn ⊢
    simp only [Complex.div_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, add_zero] at hn
    simp only [Complex.normSq_ofReal] at hn
    field_simp [ne_of_gt hh] at hn ⊢
    nlinarith
  exact htq n this

private theorem hpclose :
    ∀ (p : ℂ),
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rp : ℂ := (p - o) / (h : ℂ)
    ∀ (up : GaussianInt), (openbox up rp) → ((∀ (u : GaussianInt), ∀ (z : ℂ), (openbox u z) → (‖z
        - GridCellCenter u‖ ≤ 1)) → (‖p - ((h : ℂ) * GridCellCenter up + o)‖ ≤ h))) := by
  classical
  intro p openbox η εp εq h hh s t o rp up hup close_in_cell
  have hp_eq : p = (h : ℂ) * rp + o := by
    dsimp [rp]
    rw [mul_div_cancel₀ (p - o) (by exact_mod_cast hh.ne')]
    ring
  have heq : p - ((h : ℂ) * GridCellCenter up + o) =
      (h : ℂ) * (rp - GridCellCenter up) := by rw [hp_eq]; ring
  rw [heq, norm_mul]
  have hnorm : ‖(h : ℂ)‖ = h := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  rw [hnorm]
  calc
    h * ‖rp - GridCellCenter up‖ ≤ h * 1 := mul_le_mul_of_nonneg_left
      (close_in_cell up rp hup) hh.le
    _ = h := mul_one h

private theorem hqclose :
    ∀ (q : ℂ),
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rq : ℂ := (q - o) / (h : ℂ)
    ∀ (uq : GaussianInt), (openbox uq rq) → ((∀ (u : GaussianInt), ∀ (z : ℂ), (openbox u z) → (‖z
        - GridCellCenter u‖ ≤ 1)) → (‖q - ((h : ℂ) * GridCellCenter uq + o)‖ ≤ h))) := by
  classical
  intro q openbox η εp εq h hh s t o rq uq huq close_in_cell
  have hq_eq : q = (h : ℂ) * rq + o := by
    dsimp [rq]
    rw [mul_div_cancel₀ (q - o) (by exact_mod_cast hh.ne')]
    ring
  have heq : q - ((h : ℂ) * GridCellCenter uq + o) =
      (h : ℂ) * (rq - GridCellCenter uq) := by rw [hq_eq]; ring
  rw [heq, norm_mul]
  have hnorm : ‖(h : ℂ)‖ = h := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  rw [hnorm]
  calc
    h * ‖rq - GridCellCenter uq‖ ≤ h * 1 := mul_le_mul_of_nonneg_left
      (close_in_cell uq rq huq) hh.le
    _ = h := mul_one h

private theorem hpcenter_comp :
    ∀ (K : Set ℂ), (∀ (p : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), (Metric.ball p εp ⊆ Kᶜ) → (∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (h < εp) → (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    ∀ (up : GaussianInt), (‖p - ((h : ℂ) * GridCellCenter up + o)‖ ≤ h) → ((∀ (a : ℂ), ∀ (b : ℂ),
        (‖b - a‖ ≤ h) → (∀ (v : unitInterval), ∀ (ε : ℝ), (h < ε) → (‖Path.segment a b v - a‖ <
        ε))) → ((h : ℂ) * GridCellCenter up + o ∈ connectedComponentIn Kᶜ p))))) := by
  classical
  intro K p η εp hballp εq h h2p s t o up hpclose segment_ball
  have hpath : Set.range (Path.segment p ((h : ℂ) * GridCellCenter up + o)) ⊆ Kᶜ := by
    rintro z ⟨v, rfl⟩
    have hreal : (v : ℝ) ∈ Set.Icc 0 1 := v.2
    apply hballp
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm]
    exact segment_ball p ((h : ℂ) * GridCellCenter up + o)
      (by simpa [norm_sub_rev] using hpclose) v εp h2p
  have hc := (isPreconnected_range (Path.segment p ((h : ℂ) * GridCellCenter up +
      o)).continuous).subset_connectedComponentIn
    (Path.segment p _).source_mem_range hpath
  exact hc (Path.segment p _).target_mem_range

private theorem hqcenter_comp :
    ∀ (K : Set ℂ), (∀ (q : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ), (Metric.ball q εq ⊆ Kᶜ) → (
    let h : ℝ := min η (min εp εq) / 10
    (h < εq) → (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    ∀ (uq : GaussianInt), (‖q - ((h : ℂ) * GridCellCenter uq + o)‖ ≤ h) → ((∀ (a : ℂ), ∀ (b : ℂ),
        (‖b - a‖ ≤ h) → (∀ (v : unitInterval), ∀ (ε : ℝ), (h < ε) → (‖Path.segment a b v - a‖ <
        ε))) → ((h : ℂ) * GridCellCenter uq + o ∈ connectedComponentIn Kᶜ q))))) := by
  classical
  intro K q η εp εq hballq h h2q s t o uq hqclose segment_ball
  have hpath : Set.range (Path.segment q ((h : ℂ) * GridCellCenter uq + o)) ⊆ Kᶜ := by
    rintro z ⟨v, rfl⟩
    have hreal : (v : ℝ) ∈ Set.Icc 0 1 := v.2
    apply hballq
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm]
    exact segment_ball q ((h : ℂ) * GridCellCenter uq + o)
      (by simpa [norm_sub_rev] using hqclose) v εq h2q
  have hc := (isPreconnected_range (Path.segment q ((h : ℂ) * GridCellCenter uq +
      o)).continuous).subset_connectedComponentIn
    (Path.segment q _).source_mem_range hpath
  exact hc (Path.segment q _).target_mem_range

private theorem similarity_index :
    ∀ (a : ℝ), (0 < a) → (∀ (c : ℂ), ∀ (r : ℂ), ∀ (f : C(Circle, ℂ)), (∀ z, f z ≠ r) →
        (P3821T1LoopIndex ⟨fun z => (a : ℂ) * f z + c, (continuous_const.mul f.continuous).add
        continuous_const⟩ ((a : ℂ) * r + c) = P3821T1LoopIndex f r)) := by
  classical
  intro a ha c r f hf
  let q₀ : C(unitInterval, Circle) :=
    ⟨fun v => Circle.exp (2 * Real.pi * (v : ℝ)), by fun_prop⟩
  let f₀ : C(unitInterval, ℂ) := f.comp q₀
  let f₁ : C(unitInterval, ℂ) :=
    (⟨fun z => (a : ℂ) * f z + c, (continuous_const.mul f.continuous).add continuous_const⟩ :
      C(Circle, ℂ)).comp q₀
  have hf₀ : ∀ v, f₀ v ≠ r := fun v => hf (q₀ v)
  obtain ⟨θ, hθ, hθind, _⟩ := P3821T1AngularIncrementLaws.1 f₀ r hf₀
  have hav : ∀ v, f₁ v ≠ (a : ℂ) * r + c := by
    intro v hv
    have heq : f₁ v - ((a : ℂ) * r + c) = (a : ℂ) * (f₀ v - r) := by
      dsimp [f₀, f₁]
      ring
    rw [hv] at heq
    have heq' : (a : ℂ) * (f₀ v - r) = 0 := by simpa using heq.symm
    have : (a : ℂ) = 0 ∨ f₀ v - r = 0 := mul_eq_zero.mp heq'
    rcases this with hzero | hzero
    · exact (Complex.ofReal_ne_zero.mpr ha.ne') hzero
    · exact hf₀ v (sub_eq_zero.mp hzero)
  have haNorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hlift : ∀ v, Complex.exp ((θ v : ℂ) * Complex.I) =
      (f₁ v - ((a : ℂ) * r + c)) /
        (‖f₁ v - ((a : ℂ) * r + c)‖ : ℂ) := by
    intro v
    have hvec : f₁ v - ((a : ℂ) * r + c) = (a : ℂ) * (f₀ v - r) := by
      dsimp [f₀, f₁]
      ring
    rw [hvec, norm_mul, haNorm]
    have hnorm : ‖f₀ v - r‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hf₀ v))
    have hrat :
        (a : ℂ) * (f₀ v - r) / ((a * ‖f₀ v - r‖ : ℝ) : ℂ) =
          (f₀ v - r) / (‖f₀ v - r‖ : ℂ) := by
      field_simp [ne_of_gt ha, hnorm]
      push_cast
      ring
    rw [hrat]
    exact hθ v
  obtain ⟨_, _, hθ₁ind, _⟩ := P3821T1AngularIncrementLaws.1 f₁ ((a : ℂ) * r + c) hav
  change P3821T1AngularIncrement f₁ ((a : ℂ) * r + c) / (2 * Real.pi) =
    P3821T1AngularIncrement f₀ r / (2 * Real.pi)
  rw [← hθ₁ind θ hlift, ← hθind θ hθ]

private theorem edge_not_openbox :
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    (∀ (a : ℂ), ∀ (b : ℂ), ∀ (t : unitInterval), (Path.segment a b t).re = (1 - (t : ℝ)) * a.re +
        (t : ℝ) * b.re) → ((∀ (a : ℂ), ∀ (b : ℂ), ∀ (t : unitInterval), (Path.segment a b t).im =
        (1 - (t : ℝ)) * a.im + (t : ℝ) * b.im) → (∀ (a : GaussianInt), ∀ (k : Fin (4 : ℕ)), ∀ (v
            : GaussianInt), ∀ (t₀ : (↑unitInterval : Type)), openbox v ((Path.segment
        ((GaussianInt.toComplex : GaussianInt → ℂ) (corner a k)) ((GaussianInt.toComplex :
        GaussianInt → ℂ) (corner a (k + (1 : Fin (4 : ℕ))))) : (↑unitInterval : Type) → ℂ) t₀) →
        False)) := by
  classical
  intro corner openbox segment_re segment_im a k v t₀ hv
  change (v.re : ℝ) < _ ∧ _ < (v.re : ℝ) + 1 ∧
    (v.im : ℝ) < _ ∧ _ < (v.im : ℝ) + 1 at hv
  fin_cases k
  · have h1 : (v.im : ℝ) < (a.im : ℝ) := by
      have hx := hv.2.2.1
      rw [segment_im] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_im v, ← GaussianInt.intCast_im a] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h2 : (a.im : ℝ) < (v.im : ℝ) + 1 := by
      have hx := hv.2.2.2
      rw [segment_im] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_im a, ← GaussianInt.intCast_im v] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h1' : v.im < a.im := by exact_mod_cast h1
    have h2' : a.im < v.im + 1 := by exact_mod_cast h2
    omega
  · have h1 : (v.re : ℝ) < (a.re : ℝ) + 1 := by
      have hx := hv.1
      rw [segment_re] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_re v, ← GaussianInt.intCast_re a] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h2 : (a.re : ℝ) + 1 < (v.re : ℝ) + 1 := by
      have hx := hv.2.1
      rw [segment_re] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_re a, ← GaussianInt.intCast_re v] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h1' : v.re < a.re + 1 := by exact_mod_cast h1
    have h2' : a.re + 1 < v.re + 1 := by exact_mod_cast h2
    omega
  · have h1 : (v.im : ℝ) < (a.im : ℝ) + 1 := by
      have hx := hv.2.2.1
      rw [segment_im] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_im v, ← GaussianInt.intCast_im a] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h2 : (a.im : ℝ) + 1 < (v.im : ℝ) + 1 := by
      have hx := hv.2.2.2
      rw [segment_im] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_im a, ← GaussianInt.intCast_im v] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h1' : v.im < a.im + 1 := by exact_mod_cast h1
    have h2' : a.im + 1 < v.im + 1 := by exact_mod_cast h2
    omega
  · have h1 : (v.re : ℝ) < (a.re : ℝ) := by
      have hx := hv.1
      rw [segment_re] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_re v, ← GaussianInt.intCast_re a] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h2 : (a.re : ℝ) < (v.re : ℝ) + 1 := by
      have hx := hv.2.1
      rw [segment_re] at hx
      simp? [corner] at hx
      rw [← GaussianInt.intCast_re a, ← GaussianInt.intCast_re v] at hx
      nlinarith [t₀.2.1, t₀.2.2]
    have h1' : v.re < a.re := by exact_mod_cast h1
    have h2' : a.re < v.re + 1 := by exact_mod_cast h2
    omega

private theorem open_convex_bounds :
    ∀ (x : ℝ), ∀ (y : ℝ), ∀ (lo : ℝ), ∀ (hi : ℝ), ∀ (s : ℝ), lo < x → lo < y → x < hi → y < hi →
        (0 : ℝ) ≤ s → s ≤ (1 : ℝ) → lo < ((1 : ℝ) - s) * x + s * y ∧ ((1 : ℝ) - s) * x + s * y <
        hi := by
  classical
  intro x y lo hi s hxlo hylo hxhi hyhi hs0 hs1
  constructor
  · by_cases hs : s = 0
    · simpa [hs] using hxlo
    · by_cases hs' : s = 1
      · simpa [hs'] using hylo
      · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
        have hslt : s < 1 := lt_of_le_of_ne hs1 hs'
        have h1pos : 0 < 1 - s := sub_pos.mpr hslt
        have hleft := mul_pos h1pos (sub_pos.mpr hxlo)
        have hright := mul_pos hspos (sub_pos.mpr hylo)
        have hsum := add_pos hleft hright
        have heq : (1 - s) * x + s * y - lo = (1 - s) * (x - lo) + s * (y - lo) := by ring
        have hpositive : 0 < (1 - s) * x + s * y - lo := by rw [heq]; exact hsum
        linarith
  · by_cases hs : s = 0
    · simpa [hs] using hxhi
    · by_cases hs' : s = 1
      · simpa [hs'] using hyhi
      · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
        have hslt : s < 1 := lt_of_le_of_ne hs1 hs'
        have h1pos : 0 < 1 - s := sub_pos.mpr hslt
        have hleft := mul_pos h1pos (sub_pos.mpr hxhi)
        have hright := mul_pos hspos (sub_pos.mpr hyhi)
        have hsum := add_pos hleft hright
        have heq : hi - ((1 - s) * x + s * y) =
            (1 - s) * (hi - x) + s * (hi - y) := by ring
        have hpositive : 0 < hi - ((1 - s) * x + s * y) := by rw [heq]; exact hsum
        linarith

private theorem open_segment :
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    (∀ (u : GaussianInt), (GridCellCenter u).re = (u.re : ℝ) + 1 / 2) → ((∀ (u : GaussianInt),
        (GridCellCenter u).im = (u.im : ℝ) + 1 / 2) → ((∀ (a : ℂ), ∀ (b : ℂ), ∀ (t :
        unitInterval), (Path.segment a b t).re = (1 - (t : ℝ)) * a.re + (t : ℝ) * b.re) → ((∀ (a
        : ℂ), ∀ (b : ℂ), ∀ (t : unitInterval), (Path.segment a b t).im = (1 - (t : ℝ)) * a.im +
        (t : ℝ) * b.im) → ((∀ (u : GaussianInt), openbox u (GridCellCenter u)) → ((∀ (x : ℝ), ∀
            (y : ℝ), ∀ (lo : ℝ), ∀ (hi : ℝ), ∀ (s : ℝ), (lo < x) → ((lo < y) → ((x < hi) → ((y < hi)
        → ((0 ≤ s) → ((s ≤ 1) → (lo < (1 - s) * x + s * y ∧ (1 - s) * x + s * y < hi))))))) → (∀
            (u : GaussianInt), ∀ (r : ℂ), openbox u r → ∀ (v : (↑unitInterval : Type)), openbox u
        ((Path.segment r (GridCellCenter u) : (↑unitInterval : Type) → ℂ) v))))))) := by
  classical
  intro openbox center_re center_im segment_re segment_im center_open open_convex_bounds u r hr v
  have hc := center_open u
  change (u.re : ℝ) < (Path.segment r (GridCellCenter u) v).re ∧
    (Path.segment r (GridCellCenter u) v).re < (u.re : ℝ) + 1 ∧
    (u.im : ℝ) < (Path.segment r (GridCellCenter u) v).im ∧
    (Path.segment r (GridCellCenter u) v).im < (u.im : ℝ) + 1
  rw [segment_re, segment_im, center_re, center_im]
  exact ⟨(by simpa [center_re] using (open_convex_bounds r.re (GridCellCenter u).re (u.re : ℝ)
      ((u.re : ℝ) + 1) (v : ℝ)
      hr.1 hc.1 hr.2.1 hc.2.1 v.2.1 v.2.2).1),
    (by simpa [center_re] using (open_convex_bounds r.re (GridCellCenter u).re (u.re : ℝ) ((u.re
        : ℝ) + 1) (v : ℝ)
      hr.1 hc.1 hr.2.1 hc.2.1 v.2.1 v.2.2).2),
    (by simpa [center_im] using (open_convex_bounds r.im (GridCellCenter u).im (u.im : ℝ) ((u.im
        : ℝ) + 1) (v : ℝ)
      hr.2.2.1 hc.2.2.1 hr.2.2.2 hc.2.2.2 v.2.1 v.2.2).1),
    (by simpa [center_im] using (open_convex_bounds r.im (GridCellCenter u).im (u.im : ℝ) ((u.im
        : ℝ) + 1) (v : ℝ)
      hr.2.2.1 hc.2.2.1 hr.2.2.2 hc.2.2.2 v.2.1 v.2.2).2)⟩

private theorem cell_index :
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    (∀ (u : GaussianInt), openbox u (GridCellCenter u)) → ((∀ (a : ℝ), (0 < a) → (∀ (c : ℂ), ∀ (r
        : ℂ), ∀ (f : C(Circle, ℂ)), (∀ z, f z ≠ r) → (P3821T1LoopIndex ⟨fun z => (a : ℂ) * f z
        + c, (continuous_const.mul f.continuous).add continuous_const⟩ ((a : ℂ) * r + c) =
        P3821T1LoopIndex f r))) → (∀ (n : ℕ), ∀ (loops : Fin n → C(Circle, ℂ)), (∀ (u :
            GaussianInt), ∀ (r : ℂ), (openbox u r) → (∀ (j : Fin n), ∀ z, loops j z ≠ r)) → ((∀
            (u : GaussianInt), ∀ (r : ℂ), (openbox u r) → (∀ (v : unitInterval), openbox u
            (Path.segment r
        (GridCellCenter u) v))) → (∀ (u : GaussianInt), ∀ (r : ℂ), openbox u r → ∀ (j : Fin n),
            P3821T1LoopIndex (loops j) r = P3821T1LoopIndex (loops j) (GridCellCenter u)))))
            := by
  classical
  intro openbox center_open similarity_index n loops hloop_open_avoid open_segment u r hr j
  let H : C(unitInterval × Circle, ℂ) :=
    ⟨fun x => loops j x.2 - Path.segment r (GridCellCenter u) x.1,
      (loops j).continuous.comp continuous_snd |>.sub
        ((Path.segment r (GridCellCenter u)).continuous.comp continuous_fst)⟩
  have havoid : ∀ s z, H (s, z) ≠ 0 := by
    intro s z hz
    have hloop := hloop_open_avoid u (Path.segment r (GridCellCenter u) s)
      (open_segment u r hr s) j z
    apply hloop
    dsimp [H] at hz
    exact sub_eq_zero.mp hz
  have hhom := P3821T1LoopIndexLaws.2.2 H 0 havoid
  have hleft :
      P3821T1LoopIndex
        ⟨fun z => H (⟨0, by norm_num⟩, z), H.continuous.comp (continuous_const.prodMk
            continuous_id)⟩ 0 =
      P3821T1LoopIndex (loops j) r := by
    have hloop0 :
        (⟨fun z => H (⟨0, by norm_num⟩, z), H.continuous.comp (continuous_const.prodMk
            continuous_id)⟩ : C(Circle, ℂ)) =
          ⟨fun z => loops j z - r, (loops j).continuous.sub continuous_const⟩ := by
      ext z
      simp [H]
    rw [hloop0]
    simpa [sub_eq_add_neg] using similarity_index 1 one_pos (-r) r (loops j) (hloop_open_avoid u
        r hr j)
  have hright :
      P3821T1LoopIndex
        ⟨fun z => H (⟨1, by norm_num⟩, z), H.continuous.comp (continuous_const.prodMk
            continuous_id)⟩ 0 =
      P3821T1LoopIndex (loops j) (GridCellCenter u) := by
    have hloop1 :
        (⟨fun z => H (⟨1, by norm_num⟩, z), H.continuous.comp (continuous_const.prodMk
            continuous_id)⟩ : C(Circle, ℂ)) =
          ⟨fun z => loops j z - GridCellCenter u, (loops j).continuous.sub continuous_const⟩ := by
      ext z
      simp [H]
    rw [hloop1]
    simpa [sub_eq_add_neg] using similarity_index 1 one_pos (-(GridCellCenter u)) (GridCellCenter u)
      (loops j) (hloop_open_avoid u (GridCellCenter u) (center_open u) j)
  exact hleft.symm.trans (hhom.trans hright)

private theorem scaled_edge_in_V :
    ∀ (K : Set ℂ), ∀ (N : Set ℂ), ∀ (p : ℂ), ∀ (q : ℂ), ∀ (hb : Bornology.IsBounded
        (connectedComponentIn Kᶜ p)),
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    let neighbor (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u - ⟨0, 1⟩, u + 1, u + ⟨0, 1⟩, u - 1]
    let box (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) ≤ z.re ∧ z.re ≤ (u.re : ℝ) + 1 ∧
        (u.im : ℝ) ≤ z.im ∧ z.im ≤ (u.im : ℝ) + 1
    (∀ (u : GaussianInt), ∀ (z : ℂ), (box u z) → (‖z - GridCellCenter u‖ ≤ 1)) → ((∀ (u :
        GaussianInt), ∀ (k : Fin 4), ‖GridCellCenter (neighbor u k) - GridCellCenter u‖ ≤ 1) →
        ((∀ (u : GaussianInt), ∀ (k : Fin 4), ∀ (t : unitInterval), box u (Path.segment (corner u
        k : ℂ) (corner u (k + 1) : ℂ) t) ∧ box (neighbor u k) (Path.segment (corner u k : ℂ)
        (corner u (k + 1) : ℂ) t)) → ((∀ (K : Set ℂ), ∀ (p : ℂ), ∀ (a : ℂ), ∀ (b : ℂ), (a ∈
        connectedComponentIn Kᶜ p) → ((b ∉ connectedComponentIn Kᶜ p) → (∃ t : unitInterval,
        Path.segment a b t ∈ K))) → (∀ (finite_centers : ∀ (U : Set ℂ), (Bornology.IsBounded U) →
        (∀ (h : ℝ), (0 < h) → (∀ (o : ℂ), {u : GaussianInt | (h : ℂ) * GridCellCenter u + o ∈
        U}.Finite))),
    let V := N ∩ ({p, q} : Set ℂ)ᶜ
    ∀ (η : ℝ), ((0 : ℝ) < η) → ((Metric.thickening η K ⊆ V) → (∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (hh : 0 < h), (3 * h < η) → (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let D : Finset GaussianInt := (finite_centers (connectedComponentIn Kᶜ p) hb h hh o).toFinset
    (∀ (u : GaussianInt), u ∈ D ↔ (h : ℂ) * GridCellCenter u + o ∈ connectedComponentIn Kᶜ p) →
        (∀ (a : GaussianInt), ∀ (k : Fin (4 : ℕ)), ∀ (t₀ : (↑unitInterval : Type)), a ∈ D →
        neighbor a k ∉ D → (↑h : ℂ) * (Path.segment ((GaussianInt.toComplex : GaussianInt → ℂ)
        (corner a k)) ((GaussianInt.toComplex : GaussianInt → ℂ) (corner a (k + (1 : Fin (4 :
        ℕ))))) : (↑unitInterval : Type) → ℂ) t₀ + o ∈ V)))))))) := by
  classical
  intro K N p q hb corner neighbor box box_dist neighbor_dist edge_box segment_hits
      finite_centers V η hη hcollar εp εq h hh h3 s t o D hmemD a k t₀ ha hk
  let A : ℂ := (h : ℂ) * GridCellCenter a + o
  let B : ℂ := (h : ℂ) * GridCellCenter (neighbor a k) + o
  let e : ℂ := Path.segment (corner a k : ℂ) (corner a (k + 1) : ℂ) t₀
  have hA : A ∈ connectedComponentIn Kᶜ p := (hmemD a).1 ha
  have hB : B ∉ connectedComponentIn Kᶜ p := by
    intro hB
    exact hk ((hmemD (neighbor a k)).2 hB)
  obtain ⟨v, hvK⟩ := segment_hits K p A B hA hB
  have hnorm : ‖(h : ℂ)‖ = h := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have he : ‖(h : ℂ) * e + o - A‖ ≤ h := by
    have hbox := (edge_box a k t₀).1
    have hdist := box_dist a e hbox
    have heq : (h : ℂ) * e + o - A = (h : ℂ) * (e - GridCellCenter a) := by
      dsimp [A]
      ring
    rw [heq, norm_mul, hnorm]
    calc
      h * ‖e - GridCellCenter a‖ ≤ h * 1 := mul_le_mul_of_nonneg_left hdist hh.le
      _ = h := mul_one h
  have hAB : ‖B - A‖ ≤ h := by
    have hd := neighbor_dist a k
    have heq : B - A = (h : ℂ) *
        (GridCellCenter (neighbor a k) - GridCellCenter a) := by
      dsimp [A, B]
      ring
    rw [heq, norm_mul, hnorm]
    calc
      h * ‖GridCellCenter (neighbor a k) - GridCellCenter a‖ ≤ h * 1 :=
        mul_le_mul_of_nonneg_left hd hh.le
      _ = h := mul_one h
  let w : ℂ := Path.segment A B v
  have hwA : ‖w - A‖ ≤ h := by
    change ‖(v : ℝ) • (B - A) + A - A‖ ≤ h
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg v.2.1]
    calc
      (v : ℝ) * ‖B - A‖ ≤ 1 * ‖B - A‖ := mul_le_mul_of_nonneg_right v.2.2 (norm_nonneg _)
      _ ≤ h := by simpa using hAB
  have hnear : ‖(h : ℂ) * e + o - w‖ ≤ 2 * h := by
    calc
      ‖(h : ℂ) * e + o - w‖ = ‖((h : ℂ) * e + o - A) - (w - A)‖ := by congr 1; ring
      _ ≤ ‖(h : ℂ) * e + o - A‖ + ‖w - A‖ := norm_sub_le _ _
      _ ≤ h + h := add_le_add he hwA
      _ = 2 * h := (two_mul h).symm
  have h2eta : 2 * h < η :=
    (mul_lt_mul_of_pos_right (by norm_num : (2 : ℝ) < 3) hh).trans h3
  have hnearK : ‖(h : ℂ) * e + o - Path.segment A B v‖ < η := by
    exact lt_of_le_of_lt hnear h2eta
  have hthick : (h : ℂ) * e + o ∈ Metric.thickening η K := by
    apply (Metric.mem_thickening_iff_exists_edist_lt (δ := η) K _).2
    refine ⟨Path.segment A B v, hvK, ?_⟩
    rw [edist_dist, dist_eq_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hη).mpr hnearK
  exact hcollar hthick

private theorem hsumAt1198 :
    ∀ (p : ℂ),
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rp : ℂ := (p - o) / (h : ℂ)
    ∀ (up : GaussianInt), (openbox up rp) → (∀ (n : ℕ), ∀ (loops : Fin n → C(Circle, ℂ)),
    let g : Fin n → C(Circle, ℂ) := fun j =>
      ⟨fun z => (h : ℂ) * loops j z + o, (continuous_const.mul (loops j).continuous).add
          continuous_const⟩
    (∀ (j : Fin n), ∀ (r : ℂ), (∀ z, loops j z ≠ r) → (P3821T1LoopIndex (g j) ((h : ℂ) * r + o)
        = P3821T1LoopIndex (loops j) r)) → ((∀ (u : GaussianInt), ∀ (r : ℂ), (openbox u r) → (∀
            (j : Fin n), ∀ z, loops j z ≠ r)) → ((∀ (u : GaussianInt), ∀ (r : ℂ), (openbox u r) →
            (∀ (j : Fin n), P3821T1LoopIndex (loops j) r = P3821T1LoopIndex (loops j)
        (GridCellCenter u))) → (((h : ℂ) * rp + o = p) → ((∑ j, P3821T1LoopIndex (g j) p) = ∑
        j, P3821T1LoopIndex (loops j) (GridCellCenter up)))))) := by
  classical
  intro p openbox η εp εq h s t o rp up hup n loops g hscaled_index hloop_open_avoid cell_index
      hpgrid
  apply Finset.sum_congr rfl
  intro j hj
  calc
      P3821T1LoopIndex (g j) p =
          P3821T1LoopIndex (g j) ((h : ℂ) * rp + o) := by
        exact congrArg (P3821T1LoopIndex (g j)) hpgrid.symm
    _ = P3821T1LoopIndex (loops j) rp :=
      hscaled_index j rp (hloop_open_avoid up rp hup j)
    _ = P3821T1LoopIndex (loops j) (GridCellCenter up) :=
      cell_index up rp hup j

private theorem hsumAt1214 :
    ∀ (q : ℂ),
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rq : ℂ := (q - o) / (h : ℂ)
    ∀ (uq : GaussianInt), (openbox uq rq) → (∀ (n : ℕ), ∀ (loops : Fin n → C(Circle, ℂ)),
    let g : Fin n → C(Circle, ℂ) := fun j =>
      ⟨fun z => (h : ℂ) * loops j z + o, (continuous_const.mul (loops j).continuous).add
          continuous_const⟩
    (∀ (j : Fin n), ∀ (r : ℂ), (∀ z, loops j z ≠ r) → (P3821T1LoopIndex (g j) ((h : ℂ) * r + o)
        = P3821T1LoopIndex (loops j) r)) → ((∀ (u : GaussianInt), ∀ (r : ℂ), (openbox u r) → (∀
            (j : Fin n), ∀ z, loops j z ≠ r)) → ((∀ (u : GaussianInt), ∀ (r : ℂ), (openbox u r) →
            (∀ (j : Fin n), P3821T1LoopIndex (loops j) r = P3821T1LoopIndex (loops j)
        (GridCellCenter u))) → (((h : ℂ) * rq + o = q) → ((∑ j, P3821T1LoopIndex (g j) q) = ∑
        j, P3821T1LoopIndex (loops j) (GridCellCenter uq)))))) := by
  classical
  intro q openbox η εp εq h s t o rq uq huq n loops g hscaled_index hloop_open_avoid cell_index
      hqgrid
  apply Finset.sum_congr rfl
  intro j hj
  calc
      P3821T1LoopIndex (g j) q =
          P3821T1LoopIndex (g j) ((h : ℂ) * rq + o) := by
        exact congrArg (P3821T1LoopIndex (g j)) hqgrid.symm
    _ = P3821T1LoopIndex (loops j) rq :=
      hscaled_index j rq (hloop_open_avoid uq rq huq j)
    _ = P3821T1LoopIndex (loops j) (GridCellCenter uq) :=
      cell_index uq rq huq j

end ComponentContoursProof

namespace ComponentContourDetails

private theorem balance_permutation :
    ∀ {E : Type}, ∀ {V : Type}, ∀ [Fintype E], ∀ [DecidableEq V], ∀ (source : E →
        V), ∀ (target : E → V), (∀ (v : V), Fintype.card { e : E // target e = v } = Fintype.card
        { e : E // source e = v }) → ∃ (σ : Equiv.Perm E), ∀ (e : E), source ((σ : E → E) e) =
        target e := by
  classical
  intro E V typeclassInstance0 typeclassInstance2 source target hbalance
  classical
  let fibers (v : V) : {e // target e = v} ≃ {e // source e = v} :=
    Fintype.equivOfCardEq (hbalance v)
  exact ⟨Equiv.ofFiberEquiv fibers, Equiv.ofFiberEquiv_map fibers⟩

private theorem dart_reverse :
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    let neighbor (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u - ⟨0, 1⟩, u + 1, u + ⟨0, 1⟩, u - 1]
    ∀ (u : GaussianInt), ∀ (k : Fin (4 : ℕ)), neighbor (neighbor u k) (k + (2 : Fin (4 : ℕ))) = u
        ∧ corner (neighbor u k) (k + (2 : Fin (4 : ℕ))) = corner u (k + (1 : Fin (4 : ℕ))) ∧
        corner (neighbor u k) (k + (2 : Fin (4 : ℕ)) + (1 : Fin (4 : ℕ))) = corner u k := by
  classical
  intro corner neighbor u k
  fin_cases k <;> simp [corner, neighbor, Zsqrtd.ext_iff]

private theorem dart_adjacent :
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    ∀ (u : GaussianInt), ∀ (k : Fin (4 : ℕ)), FourNeighborAdjacent (corner u k) (corner u (k + (1
        : Fin (4 : ℕ)))) := by
  classical
  intro corner u k
  fin_cases k <;> simp [FourNeighborAdjacent, corner, Zsqrtd.ext_iff]

private theorem neighbor_dist :
    let neighbor (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u - ⟨0, 1⟩, u + 1, u + ⟨0, 1⟩, u - 1]
    (∀ (u : GaussianInt), (GridCellCenter u).re = (u.re : ℝ) + 1 / 2) → ((∀ (u : GaussianInt),
        (GridCellCenter u).im = (u.im : ℝ) + 1 / 2) → (∀ (u : GaussianInt), ∀ (k : Fin (4 : ℕ)),
        ‖GridCellCenter (neighbor u k) - GridCellCenter u‖ ≤ (1 : ℝ))) := by
  classical
  intro neighbor center_re center_im u k
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  rw [Complex.sub_re, Complex.sub_im, center_re, center_re, center_im, center_im]
  fin_cases k <;> simp [neighbor]

private theorem segment_re :
    ∀ (a : ℂ), ∀ (b : ℂ), ∀ (t : (↑unitInterval : Type)), ((Path.segment a b : (↑unitInterval :
        Type) → ℂ) t).re = ((1 : ℝ) - (↑t : ℝ)) * a.re + (↑t : ℝ) * b.re := by
  classical
  intro a b t
  change (((t : ℝ) • (b - a) + a) : ℂ).re = _
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem segment_im :
    ∀ (a : ℂ), ∀ (b : ℂ), ∀ (t : (↑unitInterval : Type)), ((Path.segment a b : (↑unitInterval :
        Type) → ℂ) t).im = ((1 : ℝ) - (↑t : ℝ)) * a.im + (↑t : ℝ) * b.im := by
  classical
  intro a b t
  change (((t : ℝ) • (b - a) + a) : ℂ).im = _
  simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

private theorem cell_exists :
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    ∀ (z : ℂ), (∀ (n : ℤ), z.re ≠ (↑n : ℝ)) → (∀ (n : ℤ), z.im ≠ (↑n : ℝ)) → ∃ (u : GaussianInt),
        openbox u z := by
  classical
  intro openbox z hr hi
  refine ⟨⟨Int.floor z.re, Int.floor z.im⟩, ?_⟩
  refine ⟨lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hr _)), Int.lt_floor_add_one _,
    lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hi _)), Int.lt_floor_add_one _⟩

private theorem hKne :
    ∀ (K : Set ℂ), ∀ (p : ℂ), ∀ (q : ℂ), (connectedComponentIn Kᶜ p ≠ connectedComponentIn Kᶜ q)
        → (K.Nonempty) := by
  classical
  intro K p q hne
  by_contra h
  apply hne
  simp only [(Set.not_nonempty_iff_eq_empty.mp h), Set.compl_empty]
  rw [isPreconnected_univ.connectedComponentIn (Set.mem_univ p),
    isPreconnected_univ.connectedComponentIn (Set.mem_univ q)]

private theorem hKV :
    ∀ (K : Set ℂ), ∀ (N : Set ℂ), (K ⊆ N) → (∀ (p : ℂ), ∀ (q : ℂ), (p ∈ Kᶜ) → ((q ∈ Kᶜ) →
        ((connectedComponentIn Kᶜ p ≠ connectedComponentIn Kᶜ q) → ((Bornology.IsBounded
        (connectedComponentIn Kᶜ p)) → (
    let V := N ∩ ({p, q} : Set ℂ)ᶜ
    (IsOpen V) → (K ⊆ V)))))) := by
  classical
  intro K N hKN p q hp hq hne hb V hV z hz
  refine ⟨hKN hz, ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (rfl | rfl)
  · exact hp hz
  · exact hq hz

private theorem h3 :
    ∀ (η : ℝ), ((0 : ℝ) < η) → (∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    3 * h < η) := by
  classical
  intro η hη εp εq h
  dsimp [h]
  nlinarith [min_le_left η (min εp εq)]

private theorem h2p :
    ∀ (η : ℝ), ∀ (εp : ℝ), (εp > (0 : ℝ)) → (∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    h < εp) := by
  classical
  intro η εp hεp εq h
  dsimp [h]
  nlinarith [le_trans (min_le_right η (min εp εq)) (min_le_left εp εq)]

private theorem h2q :
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ), (εq > (0 : ℝ)) → (
    let h : ℝ := min η (min εp εq) / 10
    h < εq) := by
  classical
  intro η εp εq hεq h
  dsimp [h]
  nlinarith [le_trans (min_le_right η (min εp εq)) (min_le_right εp εq)]

private theorem center_open :
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    (∀ (u : GaussianInt), (GridCellCenter u).re = (u.re : ℝ) + 1 / 2) → ((∀ (u : GaussianInt),
        (GridCellCenter u).im = (u.im : ℝ) + 1 / 2) → (∀ (s : ℝ), ((0 : ℝ) < s) → ((s < (1 : ℝ))
        → (∀ (u : GaussianInt), openbox u (GridCellCenter u))))) := by
  classical
  intro openbox center_re center_im s hs0 hs1 u
  simp only [openbox, center_re, center_im]
  constructor
  · linarith
  · constructor
    · linarith
    · constructor <;> linarith

private theorem segment_ball :
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (a : ℂ), ∀ (b : ℂ), ‖b - a‖ ≤ h → ∀ (v : (↑unitInterval : Type)), ∀ (ε : ℝ), h < ε →
        ‖(Path.segment a b : (↑unitInterval : Type) → ℂ) v - a‖ < ε := by
  classical
  intro η εp εq h a b hab v ε hε
  change ‖(v : ℝ) • (b - a) + a - a‖ < ε
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg v.2.1]
  calc
    (v : ℝ) * ‖b - a‖ ≤ 1 * ‖b - a‖ := mul_le_mul_of_nonneg_right v.2.2 (norm_nonneg _)
    _ ≤ h := by simpa using hab
    _ < ε := hε

private theorem hq_not_pcomp :
    ∀ (K : Set ℂ), ∀ (p : ℂ), ∀ (q : ℂ), (connectedComponentIn Kᶜ p ≠ connectedComponentIn Kᶜ q) → (
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ), (Metric.ball q εq ⊆ Kᶜ) → (
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → ((h < εq) → (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rq : ℂ := (q - o) / (h : ℂ)
    ∀ (uq : GaussianInt), (openbox uq rq) → ((∀ (u : GaussianInt), ∀ (z : ℂ), (openbox u z) → (‖z
        - GridCellCenter u‖ ≤ 1)) → ((∀ (a : ℂ), ∀ (b : ℂ), (‖b - a‖ ≤ h) → (∀ (v :
        unitInterval), ∀ (ε : ℝ), (h < ε) → (‖Path.segment a b v - a‖ < ε))) → ((h : ℂ) *
        GridCellCenter uq + o ∉ connectedComponentIn Kᶜ p))))))) := by
  classical
  intro K p q hne openbox η εp εq hballq h hh h2q s t o rq uq huq close_in_cell segment_ball hqmem
  have e1 := connectedComponentIn_eq hqmem
  have e2 := connectedComponentIn_eq (ComponentContoursProof.hqcenter_comp K q η εp εq hballq h2q
      s t uq (ComponentContoursProof.hqclose q η εp εq hh s t uq huq close_in_cell) segment_ball)
  exact hne (e1.trans e2.symm)

private theorem hmemD :
    ∀ (K : Set ℂ), ∀ (p : ℂ), ∀ (hb : Bornology.IsBounded (connectedComponentIn Kᶜ p)), ∀
        (finite_centers : ∀ (U : Set ℂ), (Bornology.IsBounded U) → (∀ (h : ℝ), (0 < h) → (∀ (o :
        ℂ), {u : GaussianInt | (h : ℂ) * GridCellCenter u + o ∈ U}.Finite))), ∀ (η : ℝ), ∀ (εp :
        ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (hh : 0 < h), (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let D : Finset GaussianInt := (finite_centers (connectedComponentIn Kᶜ p) hb h hh o).toFinset
    ∀ (u : GaussianInt), u ∈ D ↔ (↑h : ℂ) * GridCellCenter u + o ∈ connectedComponentIn Kᶜ p) := by
  classical
  intro K p hb finite_centers η εp εq h hh s t o D u
  simp [D]

private theorem huqD :
    ∀ (K : Set ℂ), ∀ (p : ℂ), ∀ (hb : Bornology.IsBounded (connectedComponentIn Kᶜ p)), ∀
        (finite_centers : ∀ (U : Set ℂ), (Bornology.IsBounded U) → (∀ (h : ℝ), (0 < h) → (∀ (o :
        ℂ), {u : GaussianInt | (h : ℂ) * GridCellCenter u + o ∈ U}.Finite))), ∀ (η : ℝ), ∀ (εp :
        ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (hh : 0 < h), (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    ∀ (uq : GaussianInt), ((h : ℂ) * GridCellCenter uq + o ∉ connectedComponentIn Kᶜ p) → (
    let D : Finset GaussianInt := (finite_centers (connectedComponentIn Kᶜ p) hb h hh o).toFinset
    (∀ (u : GaussianInt), u ∈ D ↔ (h : ℂ) * GridCellCenter u + o ∈ connectedComponentIn Kᶜ p) →
        (uq ∉ D))) := by
  classical
  intro K p hb finite_centers η εp εq h hh s t o uq hq_not_pcomp D hmemD hu
  exact hq_not_pcomp ((hmemD uq).1 hu)

private theorem hscaled_index :
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    (0 < h) → (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    (∀ (a : ℝ), (0 < a) → (∀ (c : ℂ), ∀ (r : ℂ), ∀ (f : C(Circle, ℂ)), (∀ z, f z ≠ r) →
        (P3821T1LoopIndex ⟨fun z => (a : ℂ) * f z + c, (continuous_const.mul f.continuous).add
        continuous_const⟩ ((a : ℂ) * r + c) = P3821T1LoopIndex f r))) → (∀ (n : ℕ), ∀ (loops :
        Fin n → C(Circle, ℂ)),
    let g : Fin n → C(Circle, ℂ) := fun j =>
      ⟨fun z => (h : ℂ) * loops j z + o, (continuous_const.mul (loops j).continuous).add
          continuous_const⟩
    ∀ (j : Fin n), ∀ (r : ℂ), (∀ (z : Circle), (loops j : Circle → ℂ) z ≠ r) → P3821T1LoopIndex
        (g j) ((↑h : ℂ) * r + o) = P3821T1LoopIndex (loops j) r)) := by
  classical
  intro η εp εq h hh s t o similarity_index n loops g j r hr
  simpa [g, o] using similarity_index h hh o r (loops j) hr

private theorem hloop_open_avoid :
    ∀ (K : Set ℂ), ∀ (p : ℂ), ∀ (hb : Bornology.IsBounded (connectedComponentIn Kᶜ p)),
    let openbox (u : GaussianInt) (z : ℂ) : Prop :=
      (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
        (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
    (∀ (a : ℂ), ∀ (b : ℂ), ∀ (t : unitInterval), (Path.segment a b t).re = (1 - (t : ℝ)) * a.re +
        (t : ℝ) * b.re) → ((∀ (a : ℂ), ∀ (b : ℂ), ∀ (t : unitInterval), (Path.segment a b t).im =
        (1 - (t : ℝ)) * a.im + (t : ℝ) * b.im) → (∀ (finite_centers : ∀ (U : Set ℂ),
        (Bornology.IsBounded U) → (∀ (h : ℝ), (0 < h) → (∀ (o : ℂ), {u : GaussianInt | (h : ℂ) *
        GridCellCenter u + o ∈ U}.Finite))), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (hh : 0 < h), (∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let D : Finset GaussianInt := (finite_centers (connectedComponentIn Kᶜ p) hb h hh o).toFinset
    ∀ (n : ℕ), ∀ (loops : Fin n → C(Circle, ℂ)), (∀ (j : Fin n), ∀ (z : Circle), ∃ u ∈ D, ∃ (k :
        Fin (4 : ℕ)), (fun (u : GaussianInt) => ![u - ⟨(0 : ℤ), (1 : ℤ)⟩, u + (1 : GaussianInt),
        u + ⟨(0 : ℤ), (1 : ℤ)⟩, u - (1 : GaussianInt)]) u k ∉ D ∧ ∃ (t : (↑unitInterval : Type)),
        (loops j : Circle → ℂ) z = (Path.segment ((GaussianInt.toComplex : GaussianInt → ℂ) ((fun
        (u : GaussianInt) => ![u, u + (1 : GaussianInt), u + (1 : GaussianInt) + ⟨(0 : ℤ), (1 :
        ℤ)⟩, u + ⟨(0 : ℤ), (1 : ℤ)⟩]) u k)) ((GaussianInt.toComplex : GaussianInt → ℂ) ((fun (u :
        GaussianInt) => ![u, u + (1 : GaussianInt), u + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩, u
        + ⟨(0 : ℤ), (1 : ℤ)⟩]) u (k + (1 : Fin (4 : ℕ))))) : (↑unitInterval : Type) → ℂ) t) → (∀
        (u : GaussianInt), ∀ (r : ℂ), openbox u r → ∀ (j : Fin n), ∀ (z : Circle), (loops j :
        Circle → ℂ) z ≠ r)))) := by
  classical
  intro K p hb openbox segment_re segment_im finite_centers η εp εq h hh s t o D n loops htrace u
      r hr j z heq
  obtain ⟨a, ha, k, hk, t₀, ht⟩ := htrace j z
  apply (ComponentContoursProof.edge_not_openbox segment_re segment_im) a k u t₀
  rw [← ht, heq]
  exact hr

private theorem hpgrid :
    ∀ (p : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rp : ℂ := (p - o) / (h : ℂ)
    ((h : ℂ) ≠ 0) → ((h : ℂ) * rp + o = p) := by
  classical
  intro p η εp εq h s t o rp hdenom
  have hcancel : (h : ℂ) * ((p - o) / (h : ℂ)) = p - o :=
    mul_div_cancel₀ (p - o) hdenom
  change (h : ℂ) * ((p - o) / (h : ℂ)) + o = p
  calc
    _ = (p - o) + o := congrArg (fun z : ℂ => z + o) hcancel
    _ = p := sub_add_cancel p o

private theorem hqgrid :
    ∀ (q : ℂ), ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    let rq : ℂ := (q - o) / (h : ℂ)
    ((h : ℂ) ≠ 0) → ((h : ℂ) * rq + o = q) := by
  classical
  intro q η εp εq h s t o rq hdenom
  have hcancel : (h : ℂ) * ((q - o) / (h : ℂ)) = q - o :=
    mul_div_cancel₀ (q - o) hdenom
  change (h : ℂ) * ((q - o) / (h : ℂ)) + o = q
  calc
    _ = (q - o) + o := congrArg (fun z : ℂ => z + o) hcancel
    _ = q := sub_add_cancel q o

private theorem hpoint :
    let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
      ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
    ∀ (η : ℝ), ∀ (εp : ℝ), ∀ (εq : ℝ),
    let h : ℝ := min η (min εp εq) / 10
    ∀ (s : ℝ), ∀ (t : ℝ),
    let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
    ∀ (n : ℕ), ∀ (loops : Fin n → C(Circle, ℂ)),
    let g : Fin n → C(Circle, ℂ) := fun j =>
      ⟨fun z => (h : ℂ) * loops j z + o, (continuous_const.mul (loops j).continuous).add
          continuous_const⟩
    ∀ (j : Fin n), ∀ (z : Circle), ∀ (a : GaussianInt), ∀ (k : Fin (4 : ℕ)), ∀ (t₀ :
        (↑unitInterval : Type)), ((loops j : Circle → ℂ) z = (Path.segment
        ((GaussianInt.toComplex : GaussianInt → ℂ) ((fun (u : GaussianInt) => ![u, u + (1 :
        GaussianInt), u + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩, u + ⟨(0 : ℤ), (1 : ℤ)⟩]) a k))
        ((GaussianInt.toComplex : GaussianInt → ℂ) ((fun (u : GaussianInt) => ![u, u + (1 :
        GaussianInt), u + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩, u + ⟨(0 : ℤ), (1 : ℤ)⟩]) a (k +
        (1 : Fin (4 : ℕ))))) : (↑unitInterval : Type) → ℂ) t₀) → (g j z = (h : ℂ) * Path.segment
        (corner a k : ℂ) (corner a (k + 1) : ℂ) t₀ + o) := by
  classical
  intro corner η εp εq h s t o n loops g j z a k t₀ ht
  dsimp [g]
  rw [ht]

end ComponentContourDetails

theorem P3821T1ComponentContours (K N : Set ℂ) (hK : IsCompact K)
    (hN : IsOpen N) (hKN : K ⊆ N) (p q : ℂ)
    (hp : p ∈ Kᶜ) (hq : q ∈ Kᶜ)
    (hne : connectedComponentIn Kᶜ p ≠ connectedComponentIn Kᶜ q)
    (hb : Bornology.IsBounded (connectedComponentIn Kᶜ p)) :
    ∃ n : ℕ, ∃ g : Fin n → C(Circle, ℂ),
      (∀ i, Set.range (g i) ⊆ N) ∧
      (∀ i z, g i z ≠ p ∧ g i z ≠ q) ∧
      (∑ i, P3821T1LoopIndex (g i) p) = 1 ∧
      (∑ i, P3821T1LoopIndex (g i) q) = 0 := by
-- BODY
  classical
  have grid_edge_avoids (r a b : GaussianInt) (hab : FourNeighborAdjacent a b) :
      ∀ t : unitInterval, Path.segment (a : ℂ) (b : ℂ) t ≠ GridCellCenter r :=
          ComponentContoursProof.grid_edge_avoids r a b hab
  have balance_permutation {E V : Type} [Fintype E] [DecidableEq E] [DecidableEq V]
      (source target : E → V)
      (hbalance : ∀ v, Fintype.card {e // target e = v} =
        Fintype.card {e // source e = v}) :
      ∃ σ : Equiv.Perm E, ∀ e, source (σ e) = target e :=
          ComponentContourDetails.balance_permutation (E := E) (V := V) source target hbalance
  let corner (u : GaussianInt) : Fin 4 → GaussianInt :=
    ![u, u + 1, u + 1 + ⟨0, 1⟩, u + ⟨0, 1⟩]
  let neighbor (u : GaussianInt) : Fin 4 → GaussianInt :=
    ![u - ⟨0, 1⟩, u + 1, u + ⟨0, 1⟩, u - 1]
  have dart_reverse (u : GaussianInt) (k : Fin 4) :
      neighbor (neighbor u k) (k + 2) = u ∧
      corner (neighbor u k) (k + 2) = corner u (k + 1) ∧
      corner (neighbor u k) ((k + 2) + 1) = corner u k := ComponentContourDetails.dart_reverse u k
  have dart_adjacent (u : GaussianInt) (k : Fin 4) :
      FourNeighborAdjacent (corner u k) (corner u (k + 1)) :=
          ComponentContourDetails.dart_adjacent u k
  let rayStep (r a b : GaussianInt) : ℤ :=
    if b = a + ⟨0, 1⟩ ∧ a.im = r.im ∧ a.re ≤ r.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = r.im ∧ a.re ≤ r.re then -1
    else 0
  let box (u : GaussianInt) (z : ℂ) : Prop :=
    (u.re : ℝ) ≤ z.re ∧ z.re ≤ (u.re : ℝ) + 1 ∧
      (u.im : ℝ) ≤ z.im ∧ z.im ≤ (u.im : ℝ) + 1
  let openbox (u : GaussianInt) (z : ℂ) : Prop :=
    (u.re : ℝ) < z.re ∧ z.re < (u.re : ℝ) + 1 ∧
      (u.im : ℝ) < z.im ∧ z.im < (u.im : ℝ) + 1
  have center_re (u : GaussianInt) : (GridCellCenter u).re = (u.re : ℝ) + 1 / 2 := by
    simp [GridCellCenter]
  have center_im (u : GaussianInt) : (GridCellCenter u).im = (u.im : ℝ) + 1 / 2 := by
    simp [GridCellCenter]
  have box_dist (u : GaussianInt) (z : ℂ) (hz : box u z) : ‖z - GridCellCenter u‖ ≤ 1 :=
      ComponentContoursProof.box_dist center_re center_im u z hz
  have neighbor_dist (u : GaussianInt) (k : Fin 4) :
      ‖GridCellCenter (neighbor u k) - GridCellCenter u‖ ≤ 1 :=
          ComponentContourDetails.neighbor_dist center_re center_im u k
  have segment_re (a b : ℂ) (t : unitInterval) :
      (Path.segment a b t).re = (1 - (t : ℝ)) * a.re + (t : ℝ) * b.re :=
          ComponentContourDetails.segment_re a b t
  have segment_im (a b : ℂ) (t : unitInterval) :
      (Path.segment a b t).im = (1 - (t : ℝ)) * a.im + (t : ℝ) * b.im :=
          ComponentContourDetails.segment_im a b t
  have shift_exists (a b : ℝ) : ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      (∀ n : ℤ, a - s ≠ n) ∧ (∀ n : ℤ, b - s ≠ n) := ComponentContoursProof.shift_exists a b
  have cell_exists (z : ℂ) (hr : ∀ n : ℤ, z.re ≠ n) (hi : ∀ n : ℤ, z.im ≠ n) :
      ∃ u : GaussianInt, openbox u z := ComponentContourDetails.cell_exists z hr hi
  have finite_centers (U : Set ℂ) (hU : Bornology.IsBounded U)
      (h : ℝ) (hh : 0 < h) (o : ℂ) :
      {u : GaussianInt | (h : ℂ) * GridCellCenter u + o ∈ U}.Finite :=
          ComponentContoursProof.finite_centers center_re center_im U hU h hh o
  have hKne : K.Nonempty := ComponentContourDetails.hKne K p q hne
  let V := N ∩ ({p, q} : Set ℂ)ᶜ
  have hV : IsOpen V := hN.inter
    (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have hKV : K ⊆ V := ComponentContourDetails.hKV K N hKN p q hp hq hne hb hV
  obtain ⟨η, hη, hcollar⟩ := hK.exists_thickening_subset_open hV hKV
  obtain ⟨εp, hεp, hballp⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl p hp
  obtain ⟨εq, hεq, hballq⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl q hq
  let h : ℝ := min η (min εp εq) / 10
  have hh : 0 < h := by dsimp [h]; positivity
  have h3 : 3 * h < η := ComponentContourDetails.h3 η hη εp εq
  have h2p : h < εp := ComponentContourDetails.h2p η εp hεp εq
  have h2q : h < εq := ComponentContourDetails.h2q η εp εq hεq
  obtain ⟨s, hs0, hs1, hspr, hspq⟩ := shift_exists (p.re / h) (q.re / h)
  obtain ⟨t, ht0, ht1, htsp, htq⟩ := shift_exists (p.im / h) (q.im / h)
  let o : ℂ := (h * s : ℝ) + (h * t : ℝ) * Complex.I
  let rp : ℂ := (p - o) / (h : ℂ)
  let rq : ℂ := (q - o) / (h : ℂ)
  obtain ⟨up, hup⟩ := cell_exists rp (ComponentContoursProof.hrp p η εp εq hh s hspr t)
      (ComponentContoursProof.hip p η εp εq hh s t htsp)
  obtain ⟨uq, huq⟩ := cell_exists rq (ComponentContoursProof.hrq q η εp εq hh s hspq t)
      (ComponentContoursProof.hiq q η εp εq hh s t htq)
  have box_of_open (u : GaussianInt) (z : ℂ) (hz : openbox u z) : box u z := by
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have center_open (u : GaussianInt) : openbox u (GridCellCenter u) :=
      ComponentContourDetails.center_open center_re center_im s hs0 hs1 u
  have close_in_cell (u : GaussianInt) (z : ℂ) (hz : openbox u z) :
      ‖z - GridCellCenter u‖ ≤ 1 := box_dist u z (box_of_open u z hz)
  have segment_ball (a b : ℂ) (hab : ‖b - a‖ ≤ h) (v : unitInterval)
      (ε : ℝ) (hε : h < ε) : ‖Path.segment a b v - a‖ < ε := ComponentContourDetails.segment_ball
          η εp εq a b hab v ε hε
  have hq_not_pcomp : (h : ℂ) * GridCellCenter uq + o ∉ connectedComponentIn Kᶜ p :=
      ComponentContourDetails.hq_not_pcomp K p q hne η εp εq hballq hh h2q s t uq huq
      close_in_cell segment_ball
  let D : Finset GaussianInt := (finite_centers (connectedComponentIn Kᶜ p) hb h hh o).toFinset
  have hmemD (u : GaussianInt) : u ∈ D ↔ (h : ℂ) * GridCellCenter u + o ∈ connectedComponentIn Kᶜ
      p := ComponentContourDetails.hmemD K p hb finite_centers η εp εq hh s t u
  have hupD : up ∈ D := hmemD up |>.2 (ComponentContoursProof.hpcenter_comp K p η εp hballp εq
      h2p s t up (ComponentContoursProof.hpclose p η εp εq hh s t up hup close_in_cell)
      segment_ball)
  have huqD : uq ∉ D := ComponentContourDetails.huqD K p hb finite_centers η εp εq hh s t uq
      hq_not_pcomp hmemD
  have similarity_index (a : ℝ) (ha : 0 < a) (c r : ℂ) (f : C(Circle, ℂ))
      (hf : ∀ z, f z ≠ r) :
      P3821T1LoopIndex
          ⟨fun z => (a : ℂ) * f z + c, (continuous_const.mul f.continuous).add continuous_const⟩
          ((a : ℂ) * r + c) = P3821T1LoopIndex f r := ComponentContoursProof.similarity_index a
              ha c r f hf
  obtain ⟨n, loops, htrace, hgrididx⟩ := (ComponentContoursProof.grid_contours grid_edge_avoids
      (ComponentContoursProof.loop_of_edges (ComponentContoursProof.loop_of_path)
      (ComponentContoursProof.concatenate_paths)) (ComponentContoursProof.cycles_of_perm)
      balance_permutation dart_adjacent (ComponentContoursProof.grid_boundary_sum dart_reverse
      dart_adjacent) (ComponentContoursProof.square_increment
      (ComponentContoursProof.grid_edge_increment grid_edge_avoids) dart_adjacent
      (ComponentContoursProof.square_step))) D
  let g : Fin n → C(Circle, ℂ) := fun j =>
    ⟨fun z => (h : ℂ) * loops j z + o, (continuous_const.mul (loops j).continuous).add
        continuous_const⟩
  have hscaled_index (j : Fin n) (r : ℂ) (hr : ∀ z, loops j z ≠ r) :
      P3821T1LoopIndex (g j) ((h : ℂ) * r + o) =
        P3821T1LoopIndex (loops j) r := ComponentContourDetails.hscaled_index η εp εq hh s t
            similarity_index n loops j r hr
  have hloop_open_avoid (u : GaussianInt) (r : ℂ) (hr : openbox u r) (j : Fin n) :
      ∀ z, loops j z ≠ r := ComponentContourDetails.hloop_open_avoid K p hb segment_re segment_im
          finite_centers η εp εq hh s t n loops htrace u r hr j
  have cell_index (u : GaussianInt) (r : ℂ) (hr : openbox u r) (j : Fin n) :
      P3821T1LoopIndex (loops j) r = P3821T1LoopIndex (loops j) (GridCellCenter u) :=
          ComponentContoursProof.cell_index center_open similarity_index n loops hloop_open_avoid
          (ComponentContoursProof.open_segment center_re center_im segment_re segment_im
              center_open (ComponentContoursProof.open_convex_bounds)) u r hr j
  have scaled_edge_in_V (a : GaussianInt) (k : Fin 4) (t₀ : unitInterval)
      (ha : a ∈ D) (hk : neighbor a k ∉ D) :
      (h : ℂ) * Path.segment (corner a k : ℂ) (corner a (k + 1) : ℂ) t₀ + o ∈ V :=
          ComponentContoursProof.scaled_edge_in_V K N p q hb box_dist neighbor_dist
              (ComponentContoursProof.edge_box)
          (ComponentContoursProof.segment_hits) finite_centers η hη hcollar εp εq hh h3 s t hmemD
              a k t₀ ha hk
  have hdenom : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hpgrid : (h : ℂ) * rp + o = p := ComponentContourDetails.hpgrid p η εp εq s t hdenom
  have hqgrid : (h : ℂ) * rq + o = q := ComponentContourDetails.hqgrid q η εp εq s t hdenom
  refine ⟨n, g, ?_, ?_, ?_, ?_⟩
  · intro j
    rintro x ⟨z, rfl⟩
    obtain ⟨a, ha, k, hk, t₀, ht⟩ := htrace j z
    have hVx : (h : ℂ) * Path.segment (corner a k : ℂ) (corner a (k + 1) : ℂ) t₀ + o ∈ V :=
      scaled_edge_in_V a k t₀ ha hk
    have : g j z = (h : ℂ) * Path.segment (corner a k : ℂ) (corner a (k + 1) : ℂ) t₀ + o := by
      dsimp [g]
      rw [ht]
    rw [this]
    exact hVx.1
  · intro j z
    obtain ⟨a, ha, k, hk, t₀, ht⟩ := htrace j z
    have hVx : (h : ℂ) * Path.segment (corner a k : ℂ) (corner a (k + 1) : ℂ) t₀ + o ∈ V :=
      scaled_edge_in_V a k t₀ ha hk
    have hpoint : g j z = (h : ℂ) * Path.segment (corner a k : ℂ) (corner a (k + 1) : ℂ) t₀ + o
        := ComponentContourDetails.hpoint η εp εq s t n loops j z a k t₀ ht
    rw [hpoint]
    have hnot := hVx.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
    exact hnot
  · have hsum : (∑ j, P3821T1LoopIndex (g j) p) =
        ∑ j, P3821T1LoopIndex (loops j) (GridCellCenter up) :=
            ComponentContoursProof.hsumAt1198 p η εp εq s t up hup n loops hscaled_index
            hloop_open_avoid cell_index hpgrid
    rw [hsum]
    have hidx := hgrididx up
    rw [ite_eq_left hupD] at hidx
    exact hidx
  · have hsum : (∑ j, P3821T1LoopIndex (g j) q) =
        ∑ j, P3821T1LoopIndex (loops j) (GridCellCenter uq) :=
            ComponentContoursProof.hsumAt1214 q η εp εq s t uq huq n loops hscaled_index
            hloop_open_avoid cell_index hqgrid
    rw [hsum]
    have hidx := hgrididx uq
    rw [ite_eq_right huqD] at hidx
    exact hidx

end ApollonianSuperharmonic

end
