/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Nat.Relation

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape.NatRecLabelRelation

open CategoryTheory

theorem syntactic_pullback {Γ₁ Γ₂ : Ctx} {C a b : Term} {v : Bool}
    (hC : .nat :: Γ₁.as.terms ⊢ C : .sort v)
    (ha : Γ₁.as.terms ⊢ a : C[Term.zero/])
    (hb : Γ₁.as.terms ⊢ b : Term.natRecType C)
    (σ₁ : Γ₂.as ⟶ Γ₁.as) :
    (syntactic hC ha hb).pullback (RawCtx.toCtx.map σ₁) =
      syntactic (Tm.natRec.substMotive hC σ₁)
        (Tm.natRec.substZero ha σ₁) (Tm.natRec.substStep hb σ₁) := by
  ext Γ₃ σ₂ predecessor result
  change Presheaf.Section.graph _ _ _ _ _ ↔ Presheaf.Section.graph _ _ _ _ _
  rw [← Tm.natRec.subst hC ha hb σ₁]
  exact Presheaf.Section.graph_comp (Ctx.extensionIsPullback .nat σ₁)
    (Ctx.map_extensionMap_binderVar .nat σ₁) _ _ _ _

end DomainSemantics.CoherentShape.NatRecLabelRelation
