/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FragmentHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteFragment
public import LeanPool.TuringConeRigidity.SetModels.FiniteSkolem
public import LeanPool.TuringConeRigidity.SetModels.SkolemHull
public import LeanPool.TuringConeRigidity.SetModels.InternalStructureCollapse

/-!
# Fragment Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

theorem internal_skolem_family (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) (fs : List Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    ∃ g ∈ M, g ⊆ ZFSet.prod (space d n) d ∧
      ∀ φ ∈ fs, ∃ f ∈ M, f ⊆ g ∧ SkolemGraph d n φ e f := by
  induction fs with
  | nil =>
    have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ (omega_mem M hM hS hI) _ ZFSet.omega_zero
    exact ⟨∅,h0,by simp,by simp⟩
  | cons φ fs ih =>
    obtain ⟨g,hg,hgp,hgs⟩ := ih
    obtain ⟨f,hf,hfg⟩ := internal_skolem_graph M hM hP hU hPow hS hR hI hAC hd n φ e he
    refine ⟨f ∪ g,binary_union_mem M hM hP hU hf hg,?_,?_⟩
    · intro z hz
      rcases ZFSet.mem_union.mp hz with hz|hz
      · exact (ZFSet.mem_sep.mp (hfg.1 hz)).1
      · exact hgp hz
    · intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl|hψ
      · exact ⟨f,hf,fun z hz => ZFSet.mem_union.mpr (Or.inl hz),hfg⟩
      · obtain ⟨v,hv,hvg,hvφ⟩ := hgs ψ hψ
        exact ⟨v,hv,fun z hz => ZFSet.mem_union.mpr (Or.inr (hvg hz)),hvφ⟩

theorem closed_witnesses (d h g : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (hn : φ.width ≤ n) (hhd : h ⊆ d) (hcl : Closed n g h)
    (hgs : ∀ ψ ∈ fragment n φ, ∃ f, f ⊆ g ∧ SkolemGraph d n ψ (fun _ => d) f) :
    Witnesses d h φ := by
  intro i ψ hm e he hw
  have hbounds := occurrence_width φ i ψ hm
  have hin : i < n := lt_of_lt_of_le hbounds.1 hn
  have hψn : ψ.scope ≤ n+1 := by omega
  have hbmem : witnessBody n i ψ ∈ fragment n φ := List.mem_map.mpr ⟨(i,ψ),hm,rfl⟩
  obtain ⟨f,hfg,hf⟩ := hgs _ hbmem
  let xs := takeEnv n e
  have hxs : ∀ x ∈ xs, x ∈ h := takeEnv_mem n e h he
  have hxsd : ∀ x ∈ xs, x ∈ d := fun x hx => hhd (hxs x hx)
  have hlen : xs.length = n := length_takeEnv n e
  have hsuccess : ∃ y ∈ d, (witnessBody n i ψ).Eval (cons y (prepend xs (fun _ => d))) := by
    obtain ⟨y,hy,hyi,hψ⟩ := hw
    exact ⟨y,hy,(eval_witnessBody n i ψ hin hψn d y e).mpr ⟨hyi,hψ⟩⟩
  obtain ⟨y,_,hy,_⟩ := hf.2 xs hlen hxsd hsuccess
  have hyh := hcl xs hlen hxs y (hfg hy)
  have hb := (hf.correct xs hlen hy).2.2
  exact ⟨y,hyh,(eval_witnessBody n i ψ hin hψn d y e).mp hb⟩

def differenceBody : Formula := .neg (.iff (.member 0 1) (.member 0 2))

theorem eval_differenceBody (x y z : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    differenceBody.Eval (cons z (cons x (cons y e))) ↔ ¬ (z ∈ x ↔ z ∈ y) := by
  simp only [differenceBody,Formula.Eval,Formula.eval_iff,cons_zero,cons_succ]

theorem closed_extensional (d h g : ZFSet.{u}) (n : ℕ) (hn : 2 ≤ n)
    (hd : Transitive d) (hhd : h ⊆ d) (hcl : Closed n g h)
    (hgs : ∃ f, f ⊆ g ∧ SkolemGraph d n differenceBody (fun _ => d) f) :
    RelationCollapse.StructureExtensional h := by
  classical
  intro x hx y hy hext
  by_contra hne
  have hdiff : ∃ z, ¬ (z ∈ x ↔ z ∈ y) := by
    by_contra hnz
    apply hne
    apply ZFSet.ext; intro z
    exact Classical.byContradiction (fun hz => hnz ⟨z,hz⟩)
  obtain ⟨z,hz⟩ := hdiff
  have hzd : z ∈ d := by
    by_cases hzx : z ∈ x
    · exact hd x (hhd hx) z hzx
    · have hzy : z ∈ y := by
        by_contra hzy
        exact hz ⟨fun h => False.elim (hzx h),fun h => False.elim (hzy h)⟩
      exact hd y (hhd hy) z hzy
  let e := cons x (cons y (fun _ => x))
  let xs := takeEnv n e
  have heh : ∀ i, e i ∈ h := by
    intro i
    rcases i with _ | i
    · exact hx
    rcases i with _ | i
    · exact hy
    exact hx
  have hxs : ∀ v ∈ xs, v ∈ h := takeEnv_mem n e h heh
  have hlen : xs.length = n := length_takeEnv n e
  have eval (v : ZFSet.{u}) : differenceBody.Eval (cons v (prepend xs (fun _ => d))) ↔
      ¬ (v ∈ x ↔ v ∈ y) := by
    simp only [differenceBody,Formula.Eval,Formula.eval_iff,cons_zero,cons_succ]
    rw [takeEnv_agree n e _ 0 (by omega),takeEnv_agree n e _ 1 (by omega)]
    rfl
  obtain ⟨f,hfg,hf⟩ := hgs
  obtain ⟨v,_,hv,_⟩ := hf.2 xs hlen (fun v hv => hhd (hxs v hv)) ⟨z,hzd,(eval z).mpr hz⟩
  have hvh := hcl xs hlen hxs v (hfg hv)
  exact (eval v).mp (hf.correct xs hlen hv).2.2 (hext v hvh)

theorem internal_fragment_hull (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {d s : ZFSet.{u}} (hdM : d ∈ M) (hsM : s ∈ M) (hd : Transitive d)
    (hsd : s ⊆ d) (φ : Formula) :
    ∃ h ∈ M, s ⊆ h ∧ h ⊆ d ∧ RelationCollapse.StructureExtensional h ∧
      ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ h) → (φ.Realize h e ↔ φ.Realize d e) := by
  let n := max 2 φ.width
  obtain ⟨g,hg,hgp,hgs⟩ := internal_skolem_family M hM hP hU hPow hS hR hI hAC hdM n
    (differenceBody :: fragment n φ) (fun _ => d) (fun _ => hdM)
  obtain ⟨h,hh,hsh,hhd,hcl,_⟩ := internal_finite_hull M hM hP hU hPow hS hR hI hdM hsM hg n hsd hgp
  have hext := closed_extensional d h g n (Nat.le_max_left _ _) hd hhd hcl (by
    obtain ⟨f,_,hfg,hf⟩ := hgs differenceBody List.mem_cons_self
    exact ⟨f,hfg,hf⟩)
  refine ⟨h,hh,hsh,hhd,hext,?_⟩
  intro e he
  apply realize_of_witnesses d h hhd φ _ e he
  apply closed_witnesses d h g n φ (Nat.le_max_right _ _) hhd hcl
  intro ψ hψ
  obtain ⟨f,_,hfg,hf⟩ := hgs ψ (List.mem_cons_of_mem _ hψ)
  exact ⟨f,hfg,hf⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
