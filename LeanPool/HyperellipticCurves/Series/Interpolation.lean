/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Series.MvPSeries
public import LeanPool.HyperellipticCurves.Series.ZeroCount

import Mathlib.Data.Finsupp.Option
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Interpolation: power series vanishing on the unit polydisk are zero

Over a domain `O` of the standing setting with principal maximal ideal
`𝔪 = (π)`, `π ≠ 0`, and `O` infinite:

* a one-variable power series vanishing at every point of `𝔪` is zero
  (`ChabautyColeman.PSeries.eq_zero_of_forall_eval_zero`): its reduction must vanish
  (else the zero set would be finite by `cor:wprep-count`, but `𝔪` is infinite), so `π`
  divides all coefficients; iterating and using separatedness kills all coefficients.

* a multivariate power series in finitely many variables vanishing at every point of
  `𝔪^σ` is zero (`ChabautyColeman.MvPSeries.eq_zero_of_forall_eval_zero`), by induction
  on the (finite) index type: adjoining one variable, the coefficient slices collapse
  into a one-variable series computing the evaluation (an exchange of summation), and
  the one-variable case applies.

No hypothesis on the residue field is needed: `Infinite O` suffices (`ℤ_p` qualifies directly).

Blueprint node: `thm:interpolation`.
-/

@[expose] public section

open PowerSeries MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

namespace PSeries

private lemma infinite_maximalIdeal [IsLocalRing O] [IsDomain O] [Infinite O] {π : O}
    (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0) :
    (maximalIdeal O : Set O).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun x : O ↦ π * x)
  · exact mul_right_injective₀ hπ0
  · intro x
    rw [SetLike.mem_coe, hπ, Ideal.mem_span_singleton]
    exact ⟨x, rfl⟩

end PSeries

namespace MvPSeries

section slices

variable {σ : Type*}

-- the coefficient slices of a series in one more variable
private noncomputable def slice (k : ℕ) (h : MvPowerSeries (Option σ) O) :
    MvPowerSeries σ O :=
  fun d ↦ h (Finsupp.optionElim k d)

private lemma coeff_slice (k : ℕ) (h : MvPowerSeries (Option σ) O) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (slice k h) = MvPowerSeries.coeff (Finsupp.optionElim k d) h :=
  rfl

private lemma eq_zero_of_slice (h : MvPowerSeries (Option σ) O)
    (hs : ∀ k, slice k h = 0) : h = 0 := by
  funext e
  have h1 : h (Finsupp.optionElim (e none) e.some) = 0 := congrFun (hs (e none)) e.some
  rwa [Finsupp.optionElim_some e] at h1

end slices

section collapse

variable {σ : Type*} [UniformSpace O]

-- collapsing all but the distinguished variable at a point family
private noncomputable def collapse (z : σ → O) (h : MvPowerSeries (Option σ) O) : O⟦X⟧ :=
  PowerSeries.mk fun k ↦ eval z (slice k h)

@[simp] private lemma coeff_collapse (z : σ → O) (h : MvPowerSeries (Option σ) O) (k : ℕ) :
    PowerSeries.coeff k (collapse z h) = eval z (slice k h) :=
  PowerSeries.coeff_mk _ _

end collapse

section rename

variable {σ τ : Type*} [UniformSpace O] [IsTopologicalRing O]

-- rename along an equivalence of index types is continuous
private lemma continuous_rename (e : σ ≃ τ) :
    Continuous (MvPowerSeries.rename (e : σ → τ) : MvPowerSeries σ O → MvPowerSeries τ O) := by
  refine continuous_pi fun x ↦ ?_
  change Continuous fun h : MvPowerSeries σ O ↦
    MvPowerSeries.coeff x (MvPowerSeries.rename (e : σ → τ) h)
  have heq : (fun h : MvPowerSeries σ O ↦
        MvPowerSeries.coeff x (MvPowerSeries.rename (e : σ → τ) h))
      = fun h ↦ ∑ d ∈ (TendstoCofinite.finite_preimage_singleton
          (Finsupp.mapDomain (e : σ → τ)) x).toFinset, MvPowerSeries.coeff d h := by
    funext h
    exact MvPowerSeries.coeff_rename _ h x
  rw [heq]
  exact continuous_finsetSum _ fun d _ ↦ MvPowerSeries.WithPiTopology.continuous_coeff O d

end rename

end MvPSeries

variable [UniformSpace O] [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))]

namespace MvPSeries

private lemma hasEval_optionElim {σ : Type*} {z : σ → O} (hz : MvPowerSeries.HasEval z)
    {t : O} (ht : t ∈ maximalIdeal O) :
    MvPowerSeries.HasEval (fun o : Option σ ↦ o.elim t z) := by
  constructor
  · rintro (_ | s)
    · exact (Fact.out : IsAdic (maximalIdeal O)).isTopologicallyNilpotent_of_mem ht
    · exact hz.hpow s
  · intro U hU
    have h1 := hz.tendsto_zero hU
    rw [mem_map, mem_cofinite] at h1 ⊢
    refine Set.Finite.subset (Set.Finite.insert none (Set.Finite.image some h1)) ?_
    rintro (_ | s) ho
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨s, ho, rfl⟩

end MvPSeries

variable [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

namespace MvPSeries

section optionStep

variable {σ : Type*}


-- the Fubini step: evaluation at an extended point computes the collapse
private lemma eval_optionElim {z : σ → O} (hz : MvPowerSeries.HasEval z) {t : O}
    (ht : t ∈ maximalIdeal O) (h : MvPowerSeries (Option σ) O) :
    eval (fun o : Option σ ↦ o.elim t z) h = PSeries.eval t (collapse z h) := by
  classical
  set F : (Option σ →₀ ℕ) → O :=
    fun e ↦ MvPowerSeries.coeff e h * e.prod fun o i ↦ (o.elim t z : O) ^ i with hF
  have htot : HasSum F (eval (fun o : Option σ ↦ o.elim t z) h) :=
    hasSum_eval (hasEval_optionElim hz ht) h
  set E := (Finsupp.optionEquiv : (Option σ →₀ ℕ) ≃ ℕ × (σ →₀ ℕ))
  have htrans : HasSum (F ∘ E.symm) (eval (fun o : Option σ ↦ o.elim t z) h) :=
    (E.symm.hasSum_iff (f := F)).mpr htot
  have hrow (k : ℕ) : HasSum (fun d : σ →₀ ℕ ↦ (F ∘ E.symm) (k, d))
      (eval z (slice k h) * t ^ k) := by
    have hs := (hasSum_eval hz (slice k h)).mul_right (t ^ k)
    have heq : (fun d : σ →₀ ℕ ↦
          (MvPowerSeries.coeff d (slice k h) * d.prod fun s i ↦ z s ^ i) * t ^ k)
        = fun d : σ →₀ ℕ ↦ (F ∘ E.symm) (k, d) := by
      funext d
      have hsymm : E.symm (k, d) = Finsupp.optionElim k d := rfl
      have hnone : (Finsupp.optionElim k d) none = k :=
        Finsupp.optionElim_apply_none k d
      have hsome := Finsupp.some_optionElim k d
      rw [Function.comp_apply, hsymm, hF]
      dsimp only
      rw [Finsupp.prod_option_index _ _ (by simp) (by intros; rw [pow_add]), hnone, hsome,
        ← coeff_slice]
      simp only [Option.elim]
      ring
    exact heq ▸ hs
  have hcol := htrans.prod_fiberwise hrow
  have hone := PSeries.hasSum_eval ht (collapse z h)
  have heq2 : (fun k ↦ PowerSeries.coeff k (collapse z h) * t ^ k)
      = fun k ↦ eval z (slice k h) * t ^ k := by
    funext k
    rw [coeff_collapse]
  rw [heq2] at hone
  exact hcol.unique hone

end optionStep

end MvPSeries

variable [IsDomain O] [Infinite O] {π : O} (hπ : maximalIdeal O = Ideal.span {π})
  (hπ0 : π ≠ 0)

namespace PSeries

include hπ hπ0

private lemma exists_div_of_forall_eval_zero {g : O⟦X⟧}
    (hg : ∀ z ∈ maximalIdeal O, eval z g = 0) :
    ∃ g₁ : O⟦X⟧, g = PowerSeries.C π * g₁ ∧ ∀ z ∈ maximalIdeal O, eval z g₁ = 0 := by
  have hred : g.map (residue O) = 0 := by
    by_contra hne
    have hfin := finite_setOf_eval_eq_zero hne
    have hall : {z ∈ maximalIdeal O | eval z g = 0} = (maximalIdeal O : Set O) := by
      ext z
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
      exact ⟨fun hz ↦ hz.1, fun hz ↦ ⟨hz, hg z hz⟩⟩
    rw [hall] at hfin
    exact infinite_maximalIdeal hπ hπ0 hfin
  have hdvd (k : ℕ) : π ∣ PowerSeries.coeff k g := by
    have h0 : residue O (PowerSeries.coeff k g) = 0 := by
      simpa [PowerSeries.coeff_map] using congrArg (PowerSeries.coeff k) hred
    have := (residue_eq_zero_iff _).mp h0
    rwa [hπ, Ideal.mem_span_singleton] at this
  set g₁ : O⟦X⟧ := PowerSeries.mk fun k ↦ (hdvd k).choose with hg₁def
  have hg1 : g = PowerSeries.C π * g₁ := by
    ext k
    rw [PowerSeries.coeff_C_mul, hg₁def, PowerSeries.coeff_mk]
    exact (hdvd k).choose_spec
  refine ⟨g₁, hg1, fun z hz ↦ ?_⟩
  have h1 := hg z hz
  rw [hg1, eval_mul hz, eval_C] at h1
  exact (mul_eq_zero.mp h1).resolve_left hπ0

/-- One-variable interpolation: a power series vanishing on the maximal ideal is zero.
No condition on the residue field is needed. -/
theorem eq_zero_of_forall_eval_zero {h : O⟦X⟧}
    (hvan : ∀ z ∈ maximalIdeal O, eval z h = 0) : h = 0 := by
  have hiter (s : ℕ) : ∃ hs : O⟦X⟧, h = PowerSeries.C (π ^ s) * hs
      ∧ ∀ z ∈ maximalIdeal O, eval z hs = 0 := by
    induction s with
    | zero => exact ⟨h, by simp, hvan⟩
    | succ n ih =>
      obtain ⟨g, hg, hvg⟩ := ih
      obtain ⟨g₁, hg1, hv1⟩ := exists_div_of_forall_eval_zero hπ hπ0 hvg
      exact ⟨g₁, by rw [hg, hg1, ← mul_assoc, ← map_mul, ← pow_succ], hv1⟩
  ext k
  rw [map_zero]
  have hmem (s : ℕ) : PowerSeries.coeff k h ∈ maximalIdeal O ^ s := by
    obtain ⟨hs, hh, -⟩ := hiter s
    rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hh,
      PowerSeries.coeff_C_mul]
    exact ⟨PowerSeries.coeff k hs, rfl⟩
  have hH : IsHausdorff (maximalIdeal O) O := inferInstance
  refine hH.haus _ fun s ↦ ?_
  rw [SModEq.zero]
  simpa [smul_eq_mul, Ideal.mul_top] using hmem s

end PSeries

namespace MvPSeries

include hπ hπ0 in
private theorem interp_key {α : Type*} [Finite α] :
    ∀ h : MvPowerSeries α O,
      (∀ z : α → O, (∀ i, z i ∈ maximalIdeal O) → MvPowerSeries.HasEval z →
        eval z h = 0) → h = 0 := by
  classical
  induction α using Finite.induction_empty_option with
  | of_equiv e IH =>
    intro h hvan
    have hg0 : MvPowerSeries.rename (e.symm : _ → _) h = 0 := by
      refine IH _ fun z hmem hz ↦ ?_
      have hcomp := eval_algHom hz (continuous_rename e.symm) h
      have hfam : (fun c ↦ eval z
            ((MvPowerSeries.rename (e.symm : _ → _)) (MvPowerSeries.X c)))
          = fun c ↦ z (e.symm c) := by
        funext c
        rw [MvPowerSeries.rename_X, eval_X]
      rw [hfam] at hcomp
      rw [hcomp]
      refine hvan _ (fun c ↦ hmem (e.symm c)) ?_
      exact ⟨fun c ↦ hz.hpow (e.symm c), hz.tendsto_zero.comp
        (e.symm.injective.tendsto_cofinite)⟩
    have hinj : Function.Injective (MvPowerSeries.renameEquiv (R := O) e.symm) :=
      (MvPowerSeries.renameEquiv (R := O) e.symm).injective
    refine hinj ?_
    rwa [map_zero]
  | h_empty =>
    intro h hvan
    have hz : MvPowerSeries.HasEval (fun x : PEmpty ↦ (0 : O)) := by
      constructor
      · rintro ⟨⟩
      · rw [Filter.cofinite_eq_bot]
        exact tendsto_bot
    have hv := hvan _ (fun i ↦ i.elim) hz
    have hsum := hasSum_eval hz h
    have hsingle : HasSum (fun d : PEmpty →₀ ℕ ↦
          MvPowerSeries.coeff d h * d.prod fun s e ↦ (0 : O) ^ e)
        (MvPowerSeries.coeff 0 h) := by
      have := hasSum_single (f := fun d : PEmpty →₀ ℕ ↦
        MvPowerSeries.coeff d h * d.prod fun s e ↦ (0 : O) ^ e) 0
        (fun b hb ↦ absurd (Subsingleton.elim b 0) hb)
      simpa [Finsupp.prod_zero_index] using this
    have hc0 : MvPowerSeries.coeff (R := O) 0 h = 0 := by rw [← hv, hsingle.unique hsum]
    funext d
    rwa [Subsingleton.elim d 0]
  | h_option IH =>
    intro h hvan
    refine eq_zero_of_slice h fun k ↦ ?_
    refine IH _ fun z hmem hz ↦ ?_
    have hcol : collapse z h = 0 := by
      refine PSeries.eq_zero_of_forall_eval_zero hπ hπ0 fun t ht ↦ ?_
      refine (eval_optionElim hz ht h).symm.trans ?_
      refine hvan _ ?_ (hasEval_optionElim hz ht)
      rintro (_ | s)
      · exact ht
      · exact hmem s
    have := congrArg (PowerSeries.coeff k) hcol
    rwa [collapse, PowerSeries.coeff_mk, map_zero] at this

include hπ hπ0 in
/-- Interpolation: a multivariate power series in finitely many variables vanishing at
every point of `𝔪^σ` is zero. No condition on the residue field is needed. -/
theorem eq_zero_of_forall_eval_zero {σ : Type*} [Finite σ] {h : MvPowerSeries σ O}
    (hvan : ∀ z : σ → O, (∀ i, z i ∈ maximalIdeal O) → eval z h = 0) : h = 0 :=
  interp_key hπ hπ0 h fun z hmem _ ↦ hvan z hmem

include hπ hπ0 in
/-- **Interpolation for polynomial coefficients**: two polynomials over the power series ring
whose images under every evaluation at a point of `𝔪^σ`, read in a faithful `O`-algebra (e.g. a
fraction field), agree are equal. -/
theorem polynomial_eq_of_forall_eval_eq {σ : Type*} [Finite σ] {K : Type*} [CommRing K]
    [Algebra O K] [FaithfulSMul O K] {P P' : Polynomial (MvPowerSeries σ O)}
    (h : ∀ (x : σ → O) (hx : ∀ s, x s ∈ maximalIdeal O),
      P.map ((algebraMap O K).comp (evalRingHom (hasEval_of_mem hx)))
        = P'.map ((algebraMap O K).comp (evalRingHom (hasEval_of_mem hx)))) :
    P = P' := by
  refine Polynomial.ext fun k ↦ ?_
  refine sub_eq_zero.mp (eq_zero_of_forall_eval_zero hπ hπ0 fun x hx ↦ ?_)
  rw [← evalRingHom_apply (hasEval_of_mem hx), map_sub, sub_eq_zero]
  have h' := congrArg (fun q ↦ q.coeff k) (h x hx)
  simp only [Polynomial.coeff_map, RingHom.comp_apply] at h'
  exact FaithfulSMul.algebraMap_injective O K h'

end MvPSeries

end ChabautyColeman

end
