/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteEvaluatorGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Arithmetic graph equations for actual primitive-recursion program indices.
The equations hold over arbitrary PA models, including nonstandard inputs. -/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.PartialRecursive

open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace ConcreteEvaluator

variable {M : Type*} [ORingStructure M]

/-!
### The constructor-6 branch of the eager dispatcher -/

/-- With positive fuel and a tag reading of `6`, the cell value is the value of
the primitive-recursion branch.  The first comparison of the dispatcher, with
`4`, and the second, with `5`, both fail, and the third, with `6`, succeeds. -/
private theorem tagSix_prec_branch [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (dtable dn : Code r) (v : Fin r → M)
    (z k : M) (hk : Semiformula.Evalb (k :> v) (code (codeUnpair₁ (codeListLength dtable))))
    (hkpos : 0 < k)
    (htag :
      Semiformula.Evalb ((6 : M) :> v)
        (code (codePartrecTag (codeUnpair₂ (codeListLength dtable)))))
    (hcell : Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn))) :
    Semiformula.Evalb (z :> v)
      (code
        (codePrecEvaluatorCell dtable
          (codeSub (codeUnpair₁ (codeListLength dtable)) (codeConst 1))
          (codeUnpair₂ (codeListLength dtable))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength dtable)))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength dtable))) dn)) :=
  by
  have hconst :
    ∀ (m : ℕ) (x : M),
      Semiformula.Evalb (x :> v) (code (codeConst (n := r) m)) → x = ((m : ℕ) : M) :=
    fun m x hx => eval_unique hx (eval_codeConst m v)
  have hcast4 : ((4 : ℕ) : M) = (4 : M) := by simp
  have hcast5 : ((5 : ℕ) : M) = (5 : M) := by simp
  have hcast6 : ((6 : ℕ) : M) = (6 : M) := by simp
  have hne64 : ¬((6 : M) = ((4 : ℕ) : M)) :=
    by
    rw [hcast4]
    exact fun hc =>
      absurd hc.symm
        (_root_.ne_of_lt
          (by
            simpa [FFL.FirstOrder.Arithmetic.numeral_eq_natCast] using
              (FFL.FirstOrder.Arithmetic.numeral_lt_of_lt (M := M) (by omega : 4 < 6))))
  have hne65 : ¬((6 : M) = ((5 : ℕ) : M)) :=
    by
    rw [hcast5]
    exact fun hc =>
      absurd hc.symm
        (_root_.ne_of_lt
          (by
            simpa [FFL.FirstOrder.Arithmetic.numeral_eq_natCast] using
              (FFL.FirstOrder.Arithmetic.numeral_lt_of_lt (M := M) (by omega : 5 < 6))))
  simp only [codeEvaluatorCell] at hcell
  obtain ⟨kf, hkf, hkcase⟩ := eval_codeIfPos_cases _ _ _ z v hcell
  have hkfk : kf = k := eval_unique hkf hk
  rcases hkcase with ⟨-, hafterFuel⟩ | ⟨h0, -⟩
  swap
  · exact absurd (hkfk ▸ h0 : k = 0) (ne_of_gt hkpos)
  obtain ⟨e4, he4, h4case⟩ := eval_codeIfPos_cases _ _ _ z v hafterFuel
  rw [eval_codeEq_iff] at he4
  obtain ⟨a4, b4, ha4, hb4, hc4⟩ := he4
  have ha46 : a4 = (6 : M) := eval_unique ha4 htag
  have hb44 : b4 = ((4 : ℕ) : M) := hconst 4 b4 hb4
  have he40 : e4 = 0 := by
    rcases hc4 with ⟨heq, -⟩ | ⟨-, h0⟩
    · exact absurd (by rw [← ha46, ← hb44]; exact heq) hne64
    · exact h0
  rcases h4case with ⟨hpos, -⟩ | ⟨-, hafterFour⟩
  · exact absurd (he40 ▸ hpos) (_root_.lt_irrefl 0)
  obtain ⟨e5, he5, h5case⟩ := eval_codeIfPos_cases _ _ _ z v hafterFour
  rw [eval_codeEq_iff] at he5
  obtain ⟨a5, b5, ha5, hb5, hc5⟩ := he5
  have ha56 : a5 = (6 : M) := eval_unique ha5 htag
  have hb55 : b5 = ((5 : ℕ) : M) := hconst 5 b5 hb5
  have he50 : e5 = 0 := by
    rcases hc5 with ⟨heq, -⟩ | ⟨-, h0⟩
    · exact absurd (by rw [← ha56, ← hb55]; exact heq) hne65
    · exact h0
  rcases h5case with ⟨hpos, -⟩ | ⟨-, hafterFive⟩
  · exact absurd (he50 ▸ hpos) (_root_.lt_irrefl 0)
  obtain ⟨e6, he6, h6case⟩ := eval_codeIfPos_cases _ _ _ z v hafterFive
  rw [eval_codeEq_iff] at he6
  obtain ⟨a6, b6, ha6, hb6, hc6⟩ := he6
  have ha66 : a6 = (6 : M) := eval_unique ha6 htag
  have hb66 : b6 = ((6 : ℕ) : M) := hconst 6 b6 hb6
  have he61 : e6 = 1 := by
    rcases hc6 with ⟨-, h1⟩ | ⟨hne, -⟩
    · exact h1
    · exact absurd (by rw [ha66, hb66, hcast6]) hne
  rcases h6case with ⟨-, hprec⟩ | ⟨h0, -⟩
  · exact hprec
  · exact absurd (he61 ▸ h0 : (1 : M) = 0) _root_.one_ne_zero

/-!
### Fuel arithmetic and the readings the branch uses -/

/-- The dispatcher evaluates the branch at the decremented fuel `k - 1`; for
positive `k`, its successor, the key of the base lookup, is `k`. -/
private theorem tagSix_succ_pred [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : M} (hk : 0 < k) : k - 1 + 1 = k :=
  FFL.FirstOrder.Arithmetic.sub_add_self_of_le
    (FFL.FirstOrder.Arithmetic.one_le_of_zero_lt k hk)

/-- The decremented fuel, as the dispatcher computes it. -/
private theorem tagSix_decremented_fuel [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u : M) :
    Semiformula.Evalb ((s - 1) :> ![s, qCode, u])
      (code
        (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codeConst 1))) :=
  by
  have hone : Semiformula.Evalb ((1 : M) :> ![s, qCode, u]) (code (codeConst (n := 3) 1)) :=
    by
    have h := eval_codeConst (M := M) (k := 3) 1 ![s, qCode, u]
    have hcast : (((1 : ℕ)) : M) = (1 : M) := by simp
    rwa [hcast] at h
  exact
    eval_codeSub _ (codeConst 1) s (1 : M) ![s, qCode, u]
      (eval_codeEvaluatorCell_fuel s qCode u) hone

/-- The key of the base lookup is the fuel. -/
private theorem tagSix_base_key [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u : M) (hs : 0 < s) :
    Semiformula.Evalb (s :> ![s, qCode, u])
      (code
        (codeSucc
          (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codeConst 1)))) :=
  by
  refine (eval_codeSucc_iff _ _ _).mpr ⟨s - 1, tagSix_decremented_fuel s qCode u, ?_⟩
  exact (tagSix_succ_pred hs).symm

/-!
### Relating the base lookup of the branch to the history bridges

The branch reads its table, key, query and argument through decoded codes; the
history bridges use the fuel key, a constant query and the argument itself.  The
four congruences below prove that the two forms have the same values. -/

private theorem tagSix_table_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s qCode u z x : M) :
    Semiformula.Evalb (x :> ![s, qCode, u]) (code codeEvaluatorHistoryBeforeCell) ↔
      Semiformula.Evalb (x :> ![s, qCode, z]) (code codeEvaluatorHistoryBeforeCell) :=
  by
  have hpair :
    ∀ c : M,
      Semiformula.Evalb (FFL.FirstOrder.Arithmetic.pair s qCode :> ![s, qCode, c])
        (code (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))) :=
    fun c =>
    eval_codePair _ _ s qCode ![s, qCode, c] ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  rw [codeEvaluatorHistoryBeforeCell, eval_comp_iff, eval_comp_iff]
  constructor
  · rintro ⟨w, hw, hcomp⟩
    refine ⟨w, hw, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    have h0 := hcomp 0
    have : w 0 = FFL.FirstOrder.Arithmetic.pair s qCode := eval_unique h0 (hpair u)
    simpa [this] using hpair z
  · rintro ⟨w, hw, hcomp⟩
    refine ⟨w, hw, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    have h0 := hcomp 0
    have : w 0 = FFL.FirstOrder.Arithmetic.pair s qCode := eval_unique h0 (hpair z)
    simpa [this] using hpair u

private theorem tagSix_key_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s qCode u z : M) (hs : 0 < s) (x : M) :
    Semiformula.Evalb (x :> ![s, qCode, u])
        (code
          (codeSucc
            (codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
              (codeConst 1)))) ↔
      Semiformula.Evalb (x :> ![s, qCode, z])
        (code (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))) :=
  by
  constructor
  · intro hx
    have hxs : x = s := eval_unique hx (tagSix_base_key s qCode u hs)
    rw [hxs]
    exact eval_codeEvaluatorCell_fuel s qCode z
  · intro hx
    have hxs : x = s := eval_unique hx (eval_codeEvaluatorCell_fuel s qCode z)
    rw [hxs]
    exact tagSix_base_key s qCode u hs

private theorem tagSix_query_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (s u z : M) (q : ℕ) (hq : partrecCodeTag q = 6) (x : M) :
    Semiformula.Evalb (x :> ![s, ((q : ℕ) : M), u])
        (code
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) ↔
      Semiformula.Evalb (x :> ![s, ((q : ℕ) : M), z])
        (code (codeConst (n := 3) (partrecCodePayload₁ q))) :=
  by
  have hleft := tagSix_read_payload₁ _ q hq _ (eval_codeEvaluatorCell_index s ((q : ℕ) : M) u)
  have hright :
    Semiformula.Evalb (((partrecCodePayload₁ q : ℕ) : M) :> ![s, ((q : ℕ) : M), z])
      (code (codeConst (n := 3) (partrecCodePayload₁ q))) :=
    eval_codeConst _ ![s, ((q : ℕ) : M), z]
  constructor
  · intro hx
    have hxv : x = ((partrecCodePayload₁ q : ℕ) : M) := eval_unique hx hleft
    rw [hxv]
    exact hright
  · intro hx
    have hxv : x = ((partrecCodePayload₁ q : ℕ) : M) := eval_unique hx hright
    rw [hxv]
    exact hleft

private theorem tagSix_argument_congr [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s qCode z x : M) :
    Semiformula.Evalb (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codeUnpair₁ (Code.proj (2 : Fin 3)))) ↔
      Semiformula.Evalb (x :> ![s, qCode, z]) (code (Code.proj (2 : Fin 3))) :=
  by
  have hleft :
    Semiformula.Evalb (z :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z 0])
      (code (codeUnpair₁ (Code.proj (2 : Fin 3)))) :=
    by
    have h :=
      eval_codeUnpair₁ (Code.proj (2 : Fin 3)) (FFL.FirstOrder.Arithmetic.pair z 0)
        ![s, qCode, FFL.FirstOrder.Arithmetic.pair z 0] ((eval_proj_iff _ _ _).mpr rfl)
    rwa [FFL.FirstOrder.Arithmetic.pi₁_pair] at h
  have hright : Semiformula.Evalb (z :> ![s, qCode, z]) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  constructor
  · intro hx
    have hxz : x = z := eval_unique hx hleft
    rw [hxz]
    exact hright
  · intro hx
    have hxz : x = z := eval_unique hx hright
    rw [hxz]
    exact hleft

/-- The predecessor lookup reads the argument `pair z a` from `pair z (a + 1)`. -/
private theorem tagSix_predecessor_argument [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (s qCode z a : M) :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.pair z a) :>
        ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code
        (codePair (codeUnpair₁ (Code.proj (2 : Fin 3)))
          (codeSub (codeUnpair₂ (Code.proj (2 : Fin 3))) (codeConst 1)))) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hproj :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair z (a + 1) :>
        ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have h1 := eval_codeUnpair₁ (Code.proj (2 : Fin 3)) _ _ hproj
  rw [FFL.FirstOrder.Arithmetic.pi₁_pair] at h1
  have h2 := eval_codeUnpair₂ (Code.proj (2 : Fin 3)) _ _ hproj
  rw [FFL.FirstOrder.Arithmetic.pi₂_pair] at h2
  have hone :
    Semiformula.Evalb ((1 : M) :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code (codeConst (n := 3) 1)) :=
    by rw [eval_codeConst_iff]; simp
  have h3 := eval_codeSub _ (codeConst 1) (a + 1) 1 _ h2 hone
  rw [add_sub_self] at h3
  exact eval_codePair _ _ z a _ h1 h3

/-- The step lookup reads the argument `pair z (pair a x)` in the lifted
environment, where the intermediate value `x` is the new head. -/
private theorem tagSix_step_argument [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (s qCode z a x : M) :
    Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.pair z (FFL.FirstOrder.Arithmetic.pair a x)) :>
        (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code
        (codePair (codeLift (codeUnpair₁ (Code.proj (2 : Fin 3))))
          (codePair (codeLift (codeSub (codeUnpair₂ (Code.proj (2 : Fin 3))) (codeConst 1)))
            (codeHead (n := 3))))) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hproj :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair z (a + 1) :>
        ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have h1 := eval_codeUnpair₁ (Code.proj (2 : Fin 3)) _ _ hproj
  rw [FFL.FirstOrder.Arithmetic.pi₁_pair] at h1
  have h2 := eval_codeUnpair₂ (Code.proj (2 : Fin 3)) _ _ hproj
  rw [FFL.FirstOrder.Arithmetic.pi₂_pair] at h2
  have hone :
    Semiformula.Evalb ((1 : M) :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)])
      (code (codeConst (n := 3) 1)) :=
    by rw [eval_codeConst_iff]; simp
  have h3 := eval_codeSub _ (codeConst 1) (a + 1) 1 _ h2 hone
  rw [add_sub_self] at h3
  have hz :
    Semiformula.Evalb (z :> (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code (codeLift (codeUnpair₁ (Code.proj (2 : Fin 3))))) :=
    (eval_codeLift_iff _ _ _ _).mpr h1
  have ha :
    Semiformula.Evalb (a :> (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code (codeLift (codeSub (codeUnpair₂ (Code.proj (2 : Fin 3))) (codeConst 1)))) :=
    (eval_codeLift_iff _ _ _ _).mpr h3
  have hx :
    Semiformula.Evalb (x :> (x :> ![s, qCode, FFL.FirstOrder.Arithmetic.pair z (a + 1)]))
      (code (codeHead (n := 3))) :=
    (eval_codeHead_iff _ _).mpr rfl
  exact eval_codePair _ _ z _ _ hz (eval_codePair _ _ a x _ ha hx)

/-- At a positive stage, zero-argument primitive recursion is the base program,
with the caller's argument bound imposed by the concrete evaluator. -/
theorem evaln_tag_six_zero_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hq : partrecCodeTag q = 6) (s z y : M) (hs : 0 < s) :
    Semiformula.Evalb
        ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      FFL.FirstOrder.Arithmetic.pair z 0 < s ∧
        Semiformula.Evalb ![s, (partrecCodePayload₁ q : M), z, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
        -- the argument codes of the primitive-recursion branch of the dispatcher, named once
  set dtable : Code 3 := codeEvaluatorHistoryBeforeCell with hdtable
  set dk' : Code 3 :=
    codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)) (codeConst 1) with
    hdk'
  set dq : Code 3 := codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell) with hdq
  set dcf : Code 3 :=
    codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcf
  set dcg : Code 3 :=
    codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcg
  set dn : Code 3 := Code.proj (2 : Fin 3) with hdn
  obtain ⟨Hs, hHs, _⟩ :=
    eval_codeEvaluatorHistoryBeforeCell_exists s (q : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have hidx_s :=
    eval_codeEvaluatorCell_index s (q : M)
      (FFL.FirstOrder.Arithmetic.pair z 0)
  have htag_s := tagSix_read_tag _ q hq _ hidx_s
  have hn_s :
    Semiformula.Evalb
      (FFL.FirstOrder.Arithmetic.pair z 0 :>
        ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0])
      (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have source_equivalence :
    Semiformula.Evalb
        ((y + 1) :>
          ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      Semiformula.Evalb
        ((y + 1) :>
          ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codeTableLookup dtable (codeSucc dk') dcf (codeUnpair₁ dn))) :=
    eval_codePrecEvaluatorCell_succ_iff_of_zero dtable dk' dq dcf dcg dn Hs (s - 1)
      ((q : ℕ) : M) ((partrecCodePayload₁ q : ℕ) : M) ((partrecCodePayload₂ q : ℕ) : M) z y
      ![s, ((q : ℕ) : M), FFL.FirstOrder.Arithmetic.pair z 0] hHs
      (tagSix_decremented_fuel s ((q : ℕ) : M)
        (FFL.FirstOrder.Arithmetic.pair z 0))
      hidx_s (tagSix_read_payload₁ _ q hq _ hidx_s) (tagSix_read_payload₂ _ q hq _ hidx_s) hn_s
  have lookup_equivalence :
    Semiformula.Evalb
        ((y + 1) :>
          ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0])
        (code (codeTableLookup dtable (codeSucc dk') dcf (codeUnpair₁ dn))) ↔
      Semiformula.Evalb ((y + 1) :> ![s, (q : M), z])
        (code
          (codeTableLookup codeEvaluatorHistoryBeforeCell
            (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
            (codeConst (n := 3) (partrecCodePayload₁ q)) (Code.proj (2 : Fin 3)))) :=
    eval_codeTableLookup_congr_at _ _ _ _ _ _ _ _ _ _ _
      (tagSix_table_congr s (q : M)
        (FFL.FirstOrder.Arithmetic.pair z 0) z)
      (tagSix_key_congr s (q : M)
        (FFL.FirstOrder.Arithmetic.pair z 0) z hs)
      (tagSix_query_congr s (FFL.FirstOrder.Arithmetic.pair z 0) z
        q hq)
      (tagSix_argument_congr s (q : M) z)
  have payload₁_lt : partrecCodePayload₁ q < q := (partrecCodePayloads_lt_of_tag_six q hq).1
  have prefix_s :
    FFL.FirstOrder.Arithmetic.pair s (partrecCodePayload₁ q : M) <
      FFL.FirstOrder.Arithmetic.pair s (q : M) :=
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast payload₁_lt)
  constructor
  · intro hc
    have hh :=
      (evalnCertificateFormula_eval_history_iff s (q : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
        hc
    obtain ⟨hu, hcell⟩ :=
      (eval_codeHistoryEvaluator_succ_iff_cell s (q : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
        hh
    have hb :=
      tagSix_prec_branch _ _ _ (y + 1) s
        (eval_codeEvaluatorCell_fuel s (q : M)
          (FFL.FirstOrder.Arithmetic.pair z 0))
        hs htag_s hcell
    have hl := lookup_equivalence.mp (source_equivalence.mp hb)
    have hf :=
      eval_codeHistoryEvaluator_succ_of_prefix_lookup s (q : M) z y (partrecCodePayload₁ q)
        prefix_s hl
    exact
      ⟨hu, (evalnCertificateFormula_eval_history_iff s (partrecCodePayload₁ q : M) z y).mpr hf⟩
  · rintro ⟨hu, hc⟩
    have hf :=
      (evalnCertificateFormula_eval_history_iff s (partrecCodePayload₁ q : M) z y).mp hc
    have hl :=
      eval_prefix_lookup_succ_of_codeHistoryEvaluator s (q : M) z y (partrecCodePayload₁ q)
        prefix_s hf
    have hb := source_equivalence.mpr (lookup_equivalence.mpr hl)
    obtain ⟨w, hw⟩ :=
      eval_codeEvaluatorCell_exists_of_values dtable dn Hs
        (FFL.FirstOrder.Arithmetic.pair z 0)
        ![s, (q : M), FFL.FirstOrder.Arithmetic.pair z 0] hHs hn_s
    have hbw :=
      tagSix_prec_branch _ _ _ w s
        (eval_codeEvaluatorCell_fuel s (q : M)
          (FFL.FirstOrder.Arithmetic.pair z 0))
        hs htag_s hw
    have hwy : w = y + 1 := eval_unique hbw hb
    rw [hwy] at hw
    exact
      (evalnCertificateFormula_eval_history_iff s (q : M)
            (FFL.FirstOrder.Arithmetic.pair z 0) y).mpr
        ((eval_codeHistoryEvaluator_succ_iff_cell s (q : M)
              (FFL.FirstOrder.Arithmetic.pair z 0) y).mpr
          ⟨hu, hw⟩)

/-- A successor recursion computation at stage `k + 1` consists of the
predecessor computation at stage `k` and the step computation at stage `k + 1`. -/
theorem evaln_tag_six_succ_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hq : partrecCodeTag q = 6) (k z a y : M) :
    Semiformula.Evalb
        ![k + 1, (q : M),
          FFL.FirstOrder.Arithmetic.pair z (a + 1), y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      FFL.FirstOrder.Arithmetic.pair z (a + 1) < k + 1 ∧
        ∃ x : M,
          Semiformula.Evalb
              ![k, (q : M), FFL.FirstOrder.Arithmetic.pair z a, x]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
            Semiformula.Evalb
              ![k + 1, (partrecCodePayload₂ q : M),
                FFL.FirstOrder.Arithmetic.pair z
                  (FFL.FirstOrder.Arithmetic.pair a x),
                y]
              (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ :=
    models_of_subtheory
      (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
        -- the argument codes of the primitive-recursion branch, named once
  set dtable : Code 3 := codeEvaluatorHistoryBeforeCell with hdtable
  set dk' : Code 3 :=
    codeSub (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)) (codeConst 1) with
    hdk'
  set dq : Code 3 := codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell) with hdq
  set dcf : Code 3 :=
    codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcf
  set dcg : Code 3 :=
    codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)) with hdcg
  set dn : Code 3 := Code.proj (2 : Fin 3) with hdn
  set u : M := FFL.FirstOrder.Arithmetic.pair z (a + 1) with hu
  have hs : (0 : M) < k + 1 :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le k)
      (lt_add_one k)
        -- readings at the source stage
  obtain ⟨Hs, hHs, hHistS⟩ := eval_codeEvaluatorHistoryBeforeCell_exists (k + 1) ((q : ℕ) : M) u
  have hidx_s := eval_codeEvaluatorCell_index (k + 1) ((q : ℕ) : M) u
  have htag_s := tagSix_read_tag _ q hq _ hidx_s
  have hn_s : Semiformula.Evalb (u :> ![k + 1, ((q : ℕ) : M), u]) (code dn) :=
    (eval_proj_iff _ _ _).mpr rfl
  have source_equivalence :
    Semiformula.Evalb ((y + 1) :> ![k + 1, ((q : ℕ) : M), u])
        (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) ↔
      ∃ x : M,
        Semiformula.Evalb ((x + 1) :> ![k + 1, ((q : ℕ) : M), u])
            (code
              (codeTableLookup dtable dk' dq
                (codePair (codeUnpair₁ dn) (codeSub (codeUnpair₂ dn) (codeConst 1))))) ∧
          Semiformula.Evalb ((y + 1) :> x :> ![k + 1, ((q : ℕ) : M), u])
            (code
              (codeTableLookup (codeLift dtable) (codeLift (codeSucc dk')) (codeLift dcg)
                (codePair (codeLift (codeUnpair₁ dn))
                  (codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1)))
                    (codeHead (n := 3)))))) :=
    eval_codePrecEvaluatorCell_succ_iff_of_succ dtable dk' dq dcf dcg dn Hs (k + 1 - 1)
      ((q : ℕ) : M) ((partrecCodePayload₁ q : ℕ) : M) ((partrecCodePayload₂ q : ℕ) : M) z a y
      ![k + 1, ((q : ℕ) : M), u] hHs (tagSix_decremented_fuel (k + 1) ((q : ℕ) : M) u) hidx_s
      (tagSix_read_payload₁ _ q hq _ hidx_s) (tagSix_read_payload₂ _ q hq _ hidx_s) hn_s
  have hpayload₂_lt : partrecCodePayload₂ q < q := (partrecCodePayloads_lt_of_tag_six q hq).2
  have hrow_step :
    ∀ s : M,
      FFL.FirstOrder.Arithmetic.pair s
          ((partrecCodePayload₂ q : ℕ) : M) <
        FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M) :=
    fun s =>
    FFL.FirstOrder.Arithmetic.pair_lt_pair_right s
      (by exact_mod_cast hpayload₂_lt)
  have hstep_bridge (x : M) :
    ∀ s : M,
      (0 : M) < s →
        ∀ H : M,
          Semiformula.Evalb (H :> ![s, ((q : ℕ) : M), u]) (code dtable) →
            Semiformula.Evalb
                ![H,
                  FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M)]
                (code codeEvaluatorHistory) →
              (Semiformula.Evalb ((y + 1) :> x :> ![s, ((q : ℕ) : M), u])
                  (code
                    (codeTableLookup (codeLift dtable) (codeLift (codeSucc dk')) (codeLift dcg)
                      (codePair (codeLift (codeUnpair₁ dn))
                        (codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1)))
                          (codeHead (n := 3)))))) ↔
                Semiformula.Evalb
                  ![y + 1, s, ((partrecCodePayload₂ q : ℕ) : M),
                    FFL.FirstOrder.Arithmetic.pair z
                      (FFL.FirstOrder.Arithmetic.pair a x)]
                  (code codeHistoryEvaluator)) :=
    by
    intro s hspos H hH hHist
    exact
      eval_codeTableLookup_succ_iff_codeHistoryEvaluator_of_history (codeLift dtable)
        (codeLift (codeSucc dk')) (codeLift dcg) _ (x :> ![s, ((q : ℕ) : M), u])
        (FFL.FirstOrder.Arithmetic.pair s ((q : ℕ) : M)) H s
        (FFL.FirstOrder.Arithmetic.pair z
          (FFL.FirstOrder.Arithmetic.pair a x))
        y (partrecCodePayload₂ q) hHist (hrow_step s) ((eval_codeLift_iff _ _ _ _).mpr hH)
        ((eval_codeLift_iff _ _ _ _).mpr (tagSix_base_key s ((q : ℕ) : M) u hspos))
        ((eval_codeLift_iff _ _ _ _).mpr
          (tagSix_read_payload₂ _ q hq _ (eval_codeEvaluatorCell_index s ((q : ℕ) : M) u)))
        (tagSix_step_argument s ((q : ℕ) : M) z a x)
  constructor
  · intro hc
    have hh := (evalnCertificateFormula_eval_history_iff (k + 1) (q : M) u y).mp hc
    obtain ⟨hu, hcell⟩ := (eval_codeHistoryEvaluator_succ_iff_cell (k + 1) (q : M) u y).mp hh
    have hb :=
      tagSix_prec_branch _ _ _ (y + 1) (k + 1) (eval_codeEvaluatorCell_fuel (k + 1) (q : M) u)
        hs htag_s hcell
    obtain ⟨x, hp, hg⟩ := source_equivalence.mp hb
    have hph := (eval_prec_predecessor_lookup_succ_iff_codeHistoryEvaluator k z a x q).mp hp
    have hgh := (hstep_bridge x (k + 1) hs Hs hHs hHistS).mp hg
    exact
      ⟨hu, x,
        (evalnCertificateFormula_eval_history_iff k (q : M)
              (FFL.FirstOrder.Arithmetic.pair z a) x).mpr
          hph,
        (evalnCertificateFormula_eval_history_iff (k + 1) (partrecCodePayload₂ q : M)
              (FFL.FirstOrder.Arithmetic.pair z
                (FFL.FirstOrder.Arithmetic.pair a x))
              y).mpr
          hgh⟩
  · rintro ⟨hu, x, hp, hg⟩
    have hph :=
      (evalnCertificateFormula_eval_history_iff k (q : M)
            (FFL.FirstOrder.Arithmetic.pair z a) x).mp
        hp
    have hgh :=
      (evalnCertificateFormula_eval_history_iff (k + 1) (partrecCodePayload₂ q : M)
            (FFL.FirstOrder.Arithmetic.pair z
              (FFL.FirstOrder.Arithmetic.pair a x))
            y).mp
        hg
    have hpl := (eval_prec_predecessor_lookup_succ_iff_codeHistoryEvaluator k z a x q).mpr hph
    have hgl := (hstep_bridge x (k + 1) hs Hs hHs hHistS).mpr hgh
    have hb := source_equivalence.mpr ⟨x, hpl, hgl⟩
    obtain ⟨w, hw⟩ :=
      eval_codeEvaluatorCell_exists_of_values dtable dn Hs u ![k + 1, (q : M), u] hHs hn_s
    have hbw :=
      tagSix_prec_branch _ _ _ w (k + 1) (eval_codeEvaluatorCell_fuel (k + 1) (q : M) u) hs
        htag_s hw
    have hwy : w = y + 1 := eval_unique hbw hb
    rw [hwy] at hw
    exact
      (evalnCertificateFormula_eval_history_iff (k + 1) (q : M) u y).mpr
        ((eval_codeHistoryEvaluator_succ_iff_cell (k + 1) (q : M) u y).mpr ⟨hu, hw⟩)

/-- Primitive recursion at zero realizes the base graph in every PA model. -/
theorem eventualGraph_prec_zero_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (fCode gCode : ℕ)
    (z y : M) :
    (eventualGraph (canonicalPartrecPrecIndex fCode gCode)).val.Evalb
        ![FFL.FirstOrder.Arithmetic.pair z 0, y] ↔
      (eventualGraph fCode).val.Evalb ![z, y] :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  let q := canonicalPartrecPrecIndex fCode gCode
  have hq : partrecCodeTag q = 6 := canonicalPartrecPrecIndex_constructor_number fCode gCode
  have hf : partrecCodePayload₁ q = fCode := canonicalPartrecPrecIndex_base_index fCode gCode
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp h
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    have hu :=
      ((eval_codeHistoryEvaluator_succ_iff_cell s (q : M) (FFL.FirstOrder.Arithmetic.pair z 0)
              y).mp
          ((evalnCertificateFormula_eval_history_iff s (q : M)
                (FFL.FirstOrder.Arithmetic.pair z 0) y).mp
            hs)).1
    have hpos : (0 : M) < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) hu
    have hc := ((evaln_tag_six_zero_iff q hq s z y hpos).mp hs).2
    rw [hf] at hc
    exact
      (eventualGraph_eval fCode _).mpr
        ⟨s, by
          simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
            hc⟩
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval fCode _).mp h
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    let t := s + FFL.FirstOrder.Arithmetic.pair z 0 + 1
    have hst : s ≤ t := le_trans le_self_add (le_of_lt (lt_add_one _))
    have hu : FFL.FirstOrder.Arithmetic.pair z 0 < t :=
      lt_of_le_of_lt le_add_self (lt_add_one _)
    have hpos : (0 : M) < t := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) hu
    have hc := evalnCertificateFormula_natCode_persist fCode s t z y hst hs
    rw [← hf] at hc
    have hr := (evaln_tag_six_zero_iff q hq t z y hpos).mpr ⟨hu, hc⟩
    exact
      (eventualGraph_eval q _).mpr
        ⟨t, by
          simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
            hr⟩

/-- Primitive recursion at a successor realizes the predecessor-then-step
graph in every PA model. The recursion argument may be nonstandard. -/
theorem eventualGraph_prec_succ_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (fCode gCode : ℕ)
    (z a y : M) :
    (eventualGraph (canonicalPartrecPrecIndex fCode gCode)).val.Evalb
        ![FFL.FirstOrder.Arithmetic.pair z (a + 1), y] ↔
      ∃ x : M,
        (eventualGraph (canonicalPartrecPrecIndex fCode gCode)).val.Evalb
            ![FFL.FirstOrder.Arithmetic.pair z a, x] ∧
          (eventualGraph gCode).val.Evalb
            ![FFL.FirstOrder.Arithmetic.pair z (FFL.FirstOrder.Arithmetic.pair a x), y] :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  let q := canonicalPartrecPrecIndex fCode gCode
  have hq : partrecCodeTag q = 6 := canonicalPartrecPrecIndex_constructor_number fCode gCode
  have hg : partrecCodePayload₂ q = gCode := canonicalPartrecPrecIndex_step_index fCode gCode
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp h
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    have hu :=
      ((eval_codeHistoryEvaluator_succ_iff_cell s (q : M)
              (FFL.FirstOrder.Arithmetic.pair z (a + 1)) y).mp
          ((evalnCertificateFormula_eval_history_iff s (q : M)
                (FFL.FirstOrder.Arithmetic.pair z (a + 1)) y).mp
            hs)).1
    have hpos : (0 : M) < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) hu
    have hpred : s - 1 + 1 = s := tagSix_succ_pred hpos
    have hh := evaln_tag_six_succ_iff q hq (s - 1) z a y
    rw [hpred] at hh
    obtain ⟨_, x, hp, hf⟩ := hh.mp hs
    rw [hg] at hf
    exact
      ⟨x,
        (eventualGraph_eval q _).mpr
          ⟨s - 1, by
            simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
              hp⟩,
        (eventualGraph_eval gCode _).mpr
          ⟨s, by
            simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
              hf⟩⟩
  · rintro ⟨x, hp, hf⟩
    obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp hp
    obtain ⟨t, ht⟩ := (eventualGraph_eval gCode _).mp hf
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ht
    let k := s + t + FFL.FirstOrder.Arithmetic.pair z (a + 1)
    have hsk : s ≤ k := le_trans le_self_add le_self_add
    have htk : t ≤ k + 1 :=
      le_trans (le_trans le_add_self le_self_add) (le_of_lt (lt_add_one _))
    have hu : FFL.FirstOrder.Arithmetic.pair z (a + 1) < k + 1 :=
      lt_of_le_of_lt le_add_self (lt_add_one _)
    have hs' :=
      evalnCertificateFormula_natCode_persist q s k (FFL.FirstOrder.Arithmetic.pair z a) x hsk
        hs
    have ht' :=
      evalnCertificateFormula_natCode_persist gCode t (k + 1)
        (FFL.FirstOrder.Arithmetic.pair z (FFL.FirstOrder.Arithmetic.pair a x)) y htk ht
    rw [← hg] at ht'
    have hr := (evaln_tag_six_succ_iff q hq k z a y).mpr ⟨hu, x, hs', ht'⟩
    exact
      (eventualGraph_eval q _).mpr
        ⟨k + 1, by
          simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
            hr⟩

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
