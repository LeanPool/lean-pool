/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/GeneratedHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCoverInjection

/-!
# Generated Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTerm

theorem internal_leaf_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hω : ZFSet.omega.{u} ∈ M)
    {t : ZFSet.{u}} (ht : t ∈ M) (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ M) :
    ∃ L ∈ M, Functional L ∧ ∀ x ∈ t ∪ FiniteTuple.elements xs,
      ∃ a ∈ FiniteTuple.indexSpace t, ZFSet.pair a x ∈ L := by
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  have hs := binary_union_mem M hM hP hU ht (FiniteTuple.elements_mem M hM hP hU h0 xs hxs)
  have hA := FiniteTuple.indexSpace_mem M hM hP hU hPow hS hω ht
  obtain ⟨f,hf,hfg⟩ := FiniteTuple.internal_finite_extension_injection M hM hP hU hPow hS hR hω ht
    xs hxs
  let L := inverseCover (FiniteTuple.indexSpace t) (t ∪ FiniteTuple.elements xs) f
  have hL := inverseCover_mem M hM hP hU hPow hS hA hs hf
  refine ⟨L,hL,?_,?_⟩
  · intro a x y hx hy
    have hx' := (inverseCover_pair _ _ _ _ _).mp hx
    have hy' := (inverseCover_pair _ _ _ _ _).mp hy
    have hfx := (hfg.pair_iff x a).mp hx'.2.2
    have hfy := (hfg.pair_iff y a).mp hy'.2.2
    exact FiniteTuple.finiteIndex_injective t xs x hfx.1 y hfy.1 (hfx.2.symm.trans hfy.2)
  · intro x hx
    refine ⟨_,FiniteTuple.finiteIndex_mem t xs x,(inverseCover_pair _ _ _ _ _).mpr ?_⟩
    exact ⟨FiniteTuple.finiteIndex_mem t xs x,hx,(hfg.pair_iff x _).mpr ⟨hx,rfl⟩⟩

theorem eval_tuple {A B L O D : ZFSet.{u}} (hD : Transitive D)
    (hzero : ∃ c, Eval A B L O D c ∅) (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, ∃ c, Eval A B L O D c x) (hcode : FiniteTuple.code xs ∈ D) :
    ∃ c, Eval A B L O D c (FiniteTuple.code xs) := by
  induction xs with
  | nil => exact hzero
  | cons x xs ih =>
    obtain ⟨a,ha⟩ := hxs x List.mem_cons_self
    have htail : FiniteTuple.code xs ∈ D := (FiniteTuple.pair_components hD hcode).2
    obtain ⟨b,hb⟩ := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) htail
    exact ⟨_,Eval.pair ha hb hcode⟩

/-- The values in `d` paired by `E` with a term code in `K`. -/
noncomputable def generatedRange (d K E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ c ∈ K, ZFSet.pair c x ∈ E) d

theorem generatedRange_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {d K E : ZFSet.{u}} (hd : d ∈ M) (hK : K ∈ M) (hE : E ∈ M) : generatedRange d K E ∈ M := by
  simpa only [generatedRange,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.pairMem 0 1 3)) (cons K (fun _ => E))
      (by intro i; cases i <;> assumption) hd

theorem mem_generatedRange {A B L O D d K E : ZFSet.{u}}
    (hE : ∀ c x, ZFSet.pair c x ∈ E ↔ Eval A B L O D c x)
    (hsub : E ⊆ ZFSet.prod K D) (x : ZFSet.{u}) :
    x ∈ generatedRange d K E ↔ x ∈ d ∧ ∃ c, Eval A B L O D c x := by
  rw [generatedRange,ZFSet.mem_sep]
  apply and_congr_right; intro _
  constructor
  · rintro ⟨c,_,hc⟩; exact ⟨c,(hE c x).mp hc⟩
  · rintro ⟨c,hc⟩
    have hcx := (hE c x).mpr hc
    obtain ⟨a,ha,b,_,he⟩ := ZFSet.mem_prod.mp (hsub hcx)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨c,ha,hcx⟩

theorem generatedRange_closed {A L O V d K E : ZFSet.{u}} (n : ℕ)
    (hV : Transitive V) (hdV : d ⊆ V) (hspace : FiniteTuple.space d n ⊆ V)
    (hE : ∀ c x, ZFSet.pair c x ∈ E ↔ Eval A ZFSet.omega L O V c x)
    (hsub : E ⊆ ZFSet.prod K V) (hzero : ∃ c, Eval A ZFSet.omega L O V c ∅)
    {g : ZFSet.{u}} (hg : g ⊆ ZFSet.prod (FiniteTuple.space d n) d) (i : ℕ)
    (hop : ∀ c x, ZFSet.pair c x ∈ g → ZFSet.pair (ZFSet.pair (natSet i) c) x ∈ O) :
    FiniteTuple.Closed n g (generatedRange d K E) := by
  intro xs hlen hxs y hy
  have hxsd : ∀ x ∈ xs, x ∈ d := fun x hx => ((mem_generatedRange hE hsub x).mp (hxs x hx)).1
  have hcode : FiniteTuple.code xs ∈ V := hspace (hlen ▸ FiniteTuple.code_mem_space d xs hxsd)
  obtain ⟨c,hc⟩ := eval_tuple hV hzero xs
    (fun x hx => ((mem_generatedRange hE hsub x).mp (hxs x hx)).2) hcode
  have hyd : y ∈ d := by
    obtain ⟨a,_,b,hb,he⟩ := ZFSet.mem_prod.mp (hg hy)
    obtain ⟨_,rfl⟩ := ZFSet.pair_inj.mp he
    exact hb
  apply (mem_generatedRange hE hsub y).mpr
  exact ⟨hyd,_,Eval.app ((mem_omega _).mpr ⟨i,rfl⟩) hc (hdV hyd) (hop _ _ hy)⟩
end FiniteTerm
namespace FiniteTuple

theorem witnesses_of_closed_graphs (d h : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (hn : φ.width ≤ n) (hhd : h ⊆ d)
    (hgs : ∀ ψ ∈ fragment n φ, ∃ g, SkolemGraph d n ψ (fun _ => d) g ∧ Closed n g h) :
    Witnesses d h φ := by
  intro i ψ hm e he hw
  have hbounds := occurrence_width φ i ψ hm
  have hin : i < n := lt_of_lt_of_le hbounds.1 hn
  have hψn : ψ.scope ≤ n+1 := by omega
  obtain ⟨g,hg,hcl⟩ := hgs _ (List.mem_map.mpr ⟨(i,ψ),hm,rfl⟩)
  let xs := takeEnv n e
  have hxs : ∀ x ∈ xs, x ∈ h := takeEnv_mem n e h he
  have hlen : xs.length = n := length_takeEnv n e
  obtain ⟨y,hy,hyi,hψ⟩ := hw
  have hsuccess := (eval_witnessBody n i ψ hin hψn d y e).mpr ⟨hyi,hψ⟩
  obtain ⟨z,_,hz,_⟩ := hg.2 xs hlen (fun x hx => hhd (hxs x hx)) ⟨y,hy,hsuccess⟩
  exact ⟨z,hcl xs hlen hxs z hz,
    (eval_witnessBody n i ψ hin hψn d z e).mp (hg.correct xs hlen hz).2.2⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
