/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages
import DomainSemantics.Domain.Decoder.DecoderStrictness
import DomainSemantics.Domain.Decoder.PiFixedPoint

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}
variable {g : CoherentGraph Γ}

theorem CoherentGraph.isCode_output_of_lamGenerator_le {graph : CoherentGraph Γ}
    (h : graph.lamGenerator ≤ g.lamGenerator) (hg : ∀ i, Shape.IsCode false (g.1.outs i)) :
    ∀ i, Shape.IsCode false (graph.1.outs i) := by
  intro i
  rcases CoherentGraph.lamGenerator_le_iff.mp h i with hbot | ⟨j, _, _, hout⟩
  · exact .bottom hbot
  · exact Shape.IsCode.of_le hout (hg j)

theorem OutputAtom.isCode (hg : ∀ i, Shape.IsCode false (g.1.outs i))
    {name : Σ A : Ty Γ, Tm Γ A} {x w : CoherentShape Γ}
    (h : OutputAtom (principalIdeal g.lamGenerator).val name x w) : IsCode false w := by
  obtain ⟨graph, entry, hgraph, _, _, rfl⟩ := h
  exact CoherentGraph.isCode_output_of_lamGenerator_le (by simpa using hgraph) hg entry

theorem Evaluates.isCode (hg : ∀ i, Shape.IsCode false (g.val.outs i))
    {name : Σ A : Ty Γ, Tm Γ A} {x w : CoherentShape Γ}
    (h : Evaluates (principalIdeal g.lamGenerator) name x w) : IsCode false w := by
  induction h with
  | entry h => exact h.isCode hg
  | bottom => exact IsCode.bottom
  | lower h _ ih => exact IsCode.of_le h ih
  | join _ _ _ ih ih' => exact Shape.IsCode.cSup ih ih'

theorem isCode_of_mem_application_lamGenerator
    (hg : ∀ i, Shape.IsCode false (g.1.outs i)) (name : Σ A : Ty Γ, Tm Γ A)
    (Y : Domain Γ) (σ : Γ₁ ⟶ Γ) {c : CoherentShape Γ₁}
    (hc : (application (principalIdeal g.lamGenerator) name Y).mem σ c) : IsCode false c := by
  have ⟨_, _, hy⟩ := (mem_application _ _ _ _ _).mp hc
  simp at hy
  exact hy.isCode (g := g.reindex σ) (fun i => (hg i).map _ _)

namespace CodeAssignment

theorem resultOperator_arrowAction_value (D : CodeAssignment) (T : Domain Γ) (B : IdealAction Γ)
    (L : Domain Γ) (σ₁ : Γ₁ ⟶ Γ) (name : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    ((D.resultOperator B).arrowAction (D.decode T) L).val.app _ (σ₁.op, name) X =
      D.extend (B.val.app _ (σ₁.op, name) (D.extend (T.pullback σ₁) X))
        (application (L.pullback σ₁) name (D.extend (T.pullback σ₁) X)) := rfl

theorem piStage_eval_prop (k : Nat) {Γ₁ : Ctx} (c : CoherentShape Γ₁) :
    IsCode false c → ∀ X : Domain Γ₁, (piStage k).eval c X = bottomIdeal Γ₁ := by
  intro hc X
  induction k generalizing Γ₁ with
  | zero => rfl
  | succ k ih =>
    have ⟨a, ha⟩ := c
    cases a with
    | sort => cases Shape.IsCode.eq_true_of_sort hc
    | nat => cases hc with | bottom h => nomatch h
    | forallE label a m names ins outs =>
      have hf : ∀ i, Shape.IsCode false (outs i) := by
        cases hc with
        | bottom h => nomatch h
        | forallE_prop hf => exact hf
      change ((piStage k).piOperator (principalIdeal ⟨a, ha.forallE_inv.1⟩)
        (graphAction ⟨⟨m, names, ins, outs⟩, ha.forallE_inv.2⟩)).val.app _ (𝟙 Γ₁).op X =
          bottomIdeal Γ₁
      rw [piOperator, DependentOperator.arrow_value_id]
      apply IdealAction.abstraction_eq_bottom
      intro Γ₂ σ₁ name Y
      rw [resultOperator_arrowAction_value]
      erw [graphAction_value]
      apply le_antisymm
      · intro Γ₃ σ₂ y hy
        have ⟨c, hc, hy⟩ := (mem_extend _ _ _ _ _).mp hy
        have hcode := isCode_of_mem_application_lamGenerator
          (fun i => (hf i).map _ _) name _ σ₂ hc
        rw [ih c hcode, bottomIdeal_mem] at hy
        exact (bottomIdeal_mem σ₂ y).mpr hy
      · exact IdealOperator.bottomIdeal_le _
    | _ => rfl

theorem piLimit_eval_prop {c : CoherentShape Γ} (hc : IsCode false c) (X : Domain Γ) :
    piLimit.eval c X = bottomIdeal Γ := by
  unfold eval
  rw [piLimit_app]
  exact piStage_eval_prop _ c hc X

theorem piLimit_value_sort (r : Bool) :
    piLimit.app _ (sortAtom r : CoherentShape Γ) = universeOperator r := by
  rw [← piLimit_fixedPoint]
  rfl

theorem mem_piLimit_rawExtend_sort_iff (r : Bool) (T : RawValue Γ)
    (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁) :
    (piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom r)) T).mem σ y ↔
      T.mem σ y ∧ IsCode r y := by
  rw [mem_rawExtend]
  constructor
  · intro ⟨c, hc, x, hx, hy⟩
    have hc' : c ≤ sortAtom r := hc
    have hy' := piLimit.eval_mono_code hc' (principalIdeal x) (𝟙 Γ₁) y hy
    change ((piLimit.app _ (sortAtom r)).val.app _ (𝟙 Γ₁).op (principalIdeal x)).mem (𝟙 Γ₁) y at hy'
    rw [piLimit_value_sort] at hy'
    change (universeIdeal r (principalIdeal x)).mem (𝟙 Γ₁) y at hy'
    rw [mem_universeIdeal_iff, principalIdeal_mem, reindex_id] at hy'
    have ⟨hy', hcode⟩ := hy'
    exact ⟨T.lower σ hy' hx, hcode⟩
  · intro ⟨hy, hcode⟩
    refine ⟨sortAtom r, le_rfl, y, hy, ?_⟩
    change ((piLimit.app _ (sortAtom r)).val.app _ (𝟙 Γ₁).op (principalIdeal y)).mem (𝟙 Γ₁) y
    rw [piLimit_value_sort]
    change (universeIdeal r (principalIdeal y)).mem (𝟙 Γ₁) y
    rw [mem_universeIdeal_iff, principalIdeal_mem, reindex_id]
    exact ⟨le_rfl, hcode⟩

theorem piLimit_rawExtend_prop {T : RawValue Γ}
    (hT : piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom false)) T = T)
    (X : RawValue Γ) : piLimit.rawExtend T X = ⊥ := by
  apply le_antisymm
  · intro Γ₁ σ y hy
    have ⟨c, hc, x, _, hy⟩ := (mem_rawExtend _ _ _ _ _).mp hy
    rw [← hT, mem_piLimit_rawExtend_sort_iff] at hc
    have ⟨_, hcode⟩ := hc
    rw [piLimit_eval_prop hcode, bottomIdeal_mem] at hy
    exact (ΩLower.mem_bot _ _).mpr hy
  · intro Γ₁ σ y hy
    exact (piLimit.rawExtend T X).lower σ ((ΩLower.mem_bot _ _).mp hy)
      ((piLimit.rawExtend T X).bottom σ)

end CodeAssignment

end DomainSemantics.CoherentShape
