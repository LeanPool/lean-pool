/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericBinding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericHierarchy
public import LeanPool.TuringConeRigidity.SetModels.BindCanonicalArithmetic

/-!
# Numeric Binding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability RelativeConstructible
universe u

noncomputable def bindNumbers (p : SentenceForm) : SentenceForm :=
  .ex (.conj (canonicalOmega 0)
    (.ex (.conj (fromBounded (squareFormula 1 0))
      (.ex (.conj (FullSetForcing.ownPower 1 0)
        (.ex (.conj (fromBounded (.empty 0)) p)))))))

theorem bindNumbers_spec (N : ZFSet.{u}) (hN : Transitive N)
    (hw : ZFSet.omega.{u} ∈ N) (hs : ZFSet.prod ZFSet.omega ZFSet.omega ∈ N)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ N) :
    (bindNumbers p).Sat (N : Set ZFSet) e ↔
      ∃ B ∈ N, PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B ∧
        p.Sat (N : Set ZFSet) (cons (natSet 0) (cons B
          (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e)))) := by
  have hc {a : ZFSet.{u}} {d : ℕ → ZFSet.{u}} (ha : a ∈ N) (hd : ∀ i, d i ∈ N) :
      ∀ i, cons a d i ∈ N := by
        intro i
        cases i
        · exact ha
        · exact hd _
  have hz : natSet.{u} 0 ∈ N := hN _ hw _ ((mem_omega _).mpr ⟨0,rfl⟩)
  have hwf (w : ZFSet.{u}) (hwN : w ∈ N) := canonicalOmega_spec N hN hw 0 (cons w e) (hc hwN he)
  have hsf (s : ZFSet.{u}) (hsN : s ∈ N) :
      (fromBounded (squareFormula 1 0)).Sat (N : Set ZFSet) (cons s (cons ZFSet.omega e)) ↔
        s = ZFSet.prod ZFSet.omega ZFSet.omega := by
    rw [bounded_sat,Formula.absolute _ N hN _ (hc hsN (hc hw he)),squareFormula_spec]
    rfl
  have hbf (B : ZFSet.{u}) (hBN : B ∈ N) :
      (FullSetForcing.ownPower 1 0).Sat (N : Set ZFSet)
        (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e))) ↔
      PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B := by
    rw [FullSetForcing.ownPower_spec N hN _ _ _ (hc hBN (hc hs (hc hw he)))]
    rfl
  have hzf (B z : ZFSet.{u}) (hBN : B ∈ N) (hzN : z ∈ N) :
      (fromBounded (.empty 0)).Sat (N : Set ZFSet)
        (cons z (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e)))) ↔
      z = natSet 0 := by
    rw [bounded_sat,Formula.absolute _ N hN _ (hc hzN (hc hBN (hc hs (hc hw
      he)))),Formula.eval_empty]
    rfl
  change (∃ w ∈ N, (canonicalOmega 0).Sat _ (cons w e) ∧
    ∃ s ∈ N, (fromBounded (squareFormula 1 0)).Sat _ (cons s (cons w e)) ∧
    ∃ B ∈ N, (FullSetForcing.ownPower 1 0).Sat _ (cons B (cons s (cons w e))) ∧
    ∃ z ∈ N, (fromBounded (.empty 0)).Sat _ (cons z (cons B (cons s (cons w e)))) ∧
      p.Sat _ (cons z (cons B (cons s (cons w e))))) ↔ _
  constructor
  · rintro ⟨w,hwN,hwS,s,hsN,hsS,B,hBN,hBS,z,hzN,hzS,hp⟩
    obtain rfl := (hwf w hwN).mp hwS
    obtain rfl := (hsf s hsN).mp hsS
    obtain rfl := (hzf B z hBN hzN).mp hzS
    exact ⟨B,hBN,(hbf B hBN).mp hBS,hp⟩
  · rintro ⟨B,hBN,hBS,hp⟩
    exact ⟨_,hw,(hwf _ hw).mpr rfl,_,hs,(hsf _ hs).mpr rfl,B,hBN,(hbf B hBN).mpr hBS,
      _,hz,(hzf B _ hBN hz).mpr rfl,hp⟩

theorem finiteGraph_subset (f : ℕ → ℕ) (k : ℕ) :
    finiteNaturalGraph.{u} f k ⊆ ZFSet.prod ZFSet.omega ZFSet.omega := by
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteNaturalGraph f k z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,(mem_omega _).mpr ⟨f i,rfl⟩,rfl⟩

theorem covers_of_power {N B : ZFSet.{u}}
    (hfin : ∀ f k, finiteNaturalGraph f k ∈ N)
    (hB : PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B) : Covers B :=
  fun f k => (hB _).mpr ⟨hfin f k,finiteGraph_subset f k⟩

end TuringRigidity.NumericSyntax

end OAI
