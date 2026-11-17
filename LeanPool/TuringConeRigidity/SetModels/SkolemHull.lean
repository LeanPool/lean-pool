/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SkolemHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.FiniteClosure

/-!
# Skolem Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

noncomputable def hull (d q s : ZFSet.{u}) (n : ℕ) (g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∀ h ∈ q, s ⊆ h → Closed n g h → x ∈ h) d

theorem mem_hull (d q s x : ZFSet.{u}) (n : ℕ) (g : ZFSet.{u}) :
    x ∈ hull d q s n g ↔ x ∈ d ∧ ∀ h ∈ q, s ⊆ h → Closed n g h → x ∈ h := ZFSet.mem_sep

def hullFormula (n : ℕ) : Formula :=
  .allMem 1 (.imp (.subset 3 0) (.imp (closedFormula n 4 5 6 7 8 0) (.member 1 0)))

theorem hull_mem (M d q s c g : ZFSet.{u}) (n : ℕ) (hM : Transitive M)
    (hS : Separation M) (hd : d ∈ M) (hqM : q ∈ M) (hs : s ∈ M) (hcM : c ∈ M)
    (h0 : (∅ : ZFSet.{u}) ∈ M) (hgM : g ∈ M) (haM : space d n ∈ M)
    (hq : ∀ h, h ∈ q ↔ h ∈ M ∧ h ⊆ d) (hc : Transitive c) (hac : space d n ⊆ c)
    (hg : g ⊆ ZFSet.prod (space d n) d) : hull d q s n g ∈ M := by
  let e := cons q (cons s (cons (space d n) (cons d (cons c (cons ∅ (cons g (fun _ => d)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hqM
    rcases i with _ | i
    · exact hs
    rcases i with _ | i
    · exact haM
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hcM
    rcases i with _ | i
    · exact h0
    rcases i with _ | i
    · exact hgM
    exact hd
  have hsep := sep_mem M hM hS (hullFormula n) e he hd
  have heq : ZFSet.sep (fun x => (hullFormula n).Eval (cons x e)) d = hull d q s n g := by
    apply ZFSet.ext; intro x
    rw [ZFSet.mem_sep,mem_hull]
    apply and_congr_right; intro _
    simp only [hullFormula,Formula.eval_allMem,Formula.eval_imp,Formula.eval_subset,
      Formula.Eval,cons_zero,cons_succ]
    apply forall_congr'; intro h
    apply forall_congr'; intro hh
    apply imp_congr_right; intro _
    have heval := eval_closedFormula n 4 5 6 7 8 0 (cons h (cons x e))
      rfl hc hac rfl hg ((hq h).mp hh).2
    exact imp_congr heval Iff.rfl
  exact heq ▸ hsep

theorem hull_subset (d q s : ZFSet.{u}) (n : ℕ) (g : ZFSet.{u}) : hull d q s n g ⊆ d :=
  fun _ hx => (mem_hull _ _ _ _ _ _).mp hx |>.1

theorem seed_subset_hull (d q s : ZFSet.{u}) (n : ℕ) (g : ZFSet.{u}) (hs : s ⊆ d) :
    s ⊆ hull d q s n g :=
  fun _x hx => (mem_hull _ _ _ _ _ _).mpr ⟨hs hx,fun _ _ hsh _ => hsh hx⟩

theorem hull_closed (d q s : ZFSet.{u}) (n : ℕ) (g : ZFSet.{u})
    (hg : g ⊆ ZFSet.prod (space d n) d) : Closed n g (hull d q s n g) := by
  intro xs hlen hxs y hy
  have hyd : y ∈ d := by
    obtain ⟨t,_,v,hv,hp⟩ := ZFSet.mem_prod.mp (hg hy)
    obtain ⟨_,rfl⟩ := ZFSet.pair_inj.mp hp
    exact hv
  refine (mem_hull _ _ _ _ _ _).mpr ⟨hyd,?_⟩
  intro h hh hsh hclosed
  exact hclosed xs hlen (fun x hx => ((mem_hull _ _ _ _ _ _).mp (hxs x hx)).2 h hh hsh hclosed) y hy

theorem hull_least (d q s h : ZFSet.{u}) (n : ℕ) (g : ZFSet.{u})
    (hh : h ∈ q) (hs : s ⊆ h) (hc : Closed n g h) : hull d q s n g ⊆ h :=
  fun _ hx => ((mem_hull _ _ _ _ _ _).mp hx).2 h hh hs hc

theorem internal_finite_hull (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {d s g : ZFSet.{u}} (hd : d ∈ M) (hs : s ∈ M) (hgM : g ∈ M) (n : ℕ)
    (hsd : s ⊆ d) (hg : g ⊆ ZFSet.prod (space d n) d) :
    ∃ h ∈ M, s ⊆ h ∧ h ⊆ d ∧ Closed n g h ∧
      ∀ v ∈ M, v ⊆ d → s ⊆ v → Closed n g v → h ⊆ v := by
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hd
  have ha := space_mem M hM hP hU hPow hS hd n
  obtain ⟨c,hc,hct,hac⟩ := internal_transitive_container M hM hP hU hS hR hI ha
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ (omega_mem M hM hS hI) _ ZFSet.omega_zero
  refine ⟨hull d q s n g,hull_mem M d q s c g n hM hS hd hqM hs hc h0 hgM ha hq hct
    (fun x hx => hct _ hac x hx) hg,seed_subset_hull d q s n g hsd,
    hull_subset d q s n g,hull_closed d q s n g hg,?_⟩
  intro v hv hvd hsv hcv
  exact hull_least d q s v n g ((hq v).mpr ⟨hv,hvd⟩) hsv hcv

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
