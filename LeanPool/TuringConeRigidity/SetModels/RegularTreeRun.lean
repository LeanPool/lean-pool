/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularTreeRun.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularBinaryTree
public import LeanPool.TuringConeRigidity.SetModels.ModelIterationFormula

/-!
# Regular Tree Run
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularTreeRun
open TransitiveNameModel BoundedSetTheory InternalProjectedGeneric RegularBinaryTree

noncomputable def bit (w i : ZFSet.{0}) : Bool := by
  classical
  exact decide (ZFSet.pair i (InternalCohen.bitSet true) ∈ w)

theorem bit_word (s : List Bool) (n : ℕ) (hn : n < s.length) :
    bit (InternalCohen.wordCode s) (natSet n) = s[n] := by
  classical
  simp only [bit,InternalCohen.pair_mem_wordCode]
  cases h : s[n] <;> simp [h,hn]

noncomputable def run (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (w : ZFSet.{0}) : ℕ → ZFSet.{0}
  | 0 => c
  | n+1 => children B T (run c B T E w n) (E n) (bit w (natSet n))

theorem run_positive (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (w : ZFSet.{0})
    (hc : c ∈ positive B)
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hE : ∀ n, E n ∈ B) : ∀ n, run c B T E w n ∈ positive B := by
  intro n; induction n with
  | zero => exact hc
  | succ n ih => exact (children_spec B T _ _ hf ih (hE n)).1 _

theorem run_take (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool)
    (n : ℕ) (hn : n ≤ s.length) :
    run c B T E (InternalCohen.wordCode s) n = tree c B T E (s.take n) := by
  induction n with
  | zero => simp only [run,List.take_zero,tree_nil]
  | succ n ih =>
    have hlt : n < s.length := hn
    rw [run,List.take_succ_eq_append_getElem hlt,tree_append,ih (Nat.le_of_lt hlt),
      List.length_take,Nat.min_eq_left (Nat.le_of_lt hlt),bit_word s n hlt]

theorem run_word (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool) :
    run c B T E (InternalCohen.wordCode s) s.length = tree c B T E s := by
  simpa only [List.take_length] using run_take c B T E s s.length le_rfl

def stepFormula (B P X Y T E w b1 i U V : ℕ) : Formula :=
  .existsMem B (.existsMem (P+1) (.existsMem (P+2)
    (.existsMem (X+3) (.existsMem (Y+4)
      (.conj (.orderedPair 1 (U+5) 4) (.conj (.orderedPair 0 3 2)
        (.conj (.pairMem (i+5) 4 (E+5)) (.conj (.pairMem 1 0 (T+5))
          (.disj (.conj (.pairMem (i+5) (b1+5) (w+5)) (.equal (V+5) 2))
            (.conj (.neg (.pairMem (i+5) (b1+5) (w+5))) (.equal (V+5) 3)))))))))))

theorem stepFormula_spec (B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (w U V : ZFSet.{0}) (n : ℕ)
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hU : U ∈ positive B) (hE : ∀ n, E n ∈ B)
    (b p x y t e word b1 i u v : ℕ) (env : ℕ → ZFSet.{0})
    (hb : env b = B) (hp : env p = positive B)
    (hx : env x = ZFSet.prod (positive B) B) (hy : env y = ZFSet.prod (positive B) (positive B))
    (ht : env t = T) (he : env e = orbitGraph E) (hw : env word = w)
    (h1 : env b1 = InternalCohen.bitSet true) (hi : env i = natSet n)
    (hu : env u = U) (hv : env v = V) :
    (stepFormula b p x y t e word b1 i u v).Eval env ↔
      V = children B T U (E n) (bit w (natSet n)) := by
  classical
  simp only [stepFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    Formula.eval_disj,cons_zero,cons_succ,hb,hp,hx,hy,ht,he,hw,h1,hi,hu,hv]
  constructor
  · rintro ⟨D,_,L,_,R,_,a,_,z,_,ha,hz,hED,haz,hout⟩
    obtain rfl := (orbitGraph_pair E n D).mp hED
    subst a; subst z
    obtain ⟨hL,hR⟩ := children_unique B T U (E n) L R hf hU (hE n) haz
    rcases hout with ⟨hbit,hV⟩|⟨hbit,hV⟩
    · simpa [bit,hbit] using hV.trans hR
    · simpa [bit,hbit] using hV.trans hL
  · intro hV
    have hc := children_spec B T U (E n) hf hU (hE n)
    refine ⟨E n,hE n,children B T U (E n) false,hc.1 false,
      children B T U (E n) true,hc.1 true,ZFSet.pair U (E n),
      ZFSet.pair_mem_prod.mpr ⟨hU,hE n⟩,_,ZFSet.pair_mem_prod.mpr ⟨hc.1 false,hc.1 true⟩,
      rfl,rfl,(orbitGraph_pair E n _).mpr rfl,hc.2,?_⟩
    by_cases hbit : ZFSet.pair (natSet n) (InternalCohen.bitSet true) ∈ w
    · exact Or.inl ⟨hbit,by simpa [bit,hbit] using hV⟩
    · exact Or.inr ⟨hbit,by simpa [bit,hbit] using hV⟩

end TuringRigidity.RegularTreeRun

end OAI
