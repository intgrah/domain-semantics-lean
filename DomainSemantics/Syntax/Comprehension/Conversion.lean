/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Comprehension

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.Ctx

open CategoryTheory

variable {Γ₁ Γ₂ : Ctx} {A A' : Term} {u : Bool}

def contextConversionRaw (h : Γ₁.as.terms ⊢ A ≡ A' : .sort u) :
    ((extension Γ₁ h.hasType.2).as ⟶ (extension Γ₁ h.hasType.1).as) where
  srcWF := (extension Γ₁ h.hasType.2).as.wf
  subst := Term.bvar
  typed := by
    simpa [extension] using
      (Raw.SubstEq.id Γ₁.as.wf).lift_at h.hasType.1 h.hasType.2 (subst_id ▸ h)

def contextConversion (h : Γ₁.as.terms ⊢ A ≡ A' : .sort u) :
    extension Γ₁ h.hasType.2 ⟶ extension Γ₁ h.hasType.1 :=
  RawCtx.toCtx.map (contextConversionRaw h)

@[simp]
theorem contextConversion_projection (h : Γ₁.as.terms ⊢ A ≡ A' : .sort u) :
    contextConversion h ≫ rawProjection Γ₁ h.hasType.1 = rawProjection Γ₁ h.hasType.2 := by
  change RawCtx.toCtx.map (contextConversionRaw h) ≫ RawCtx.toCtx.map (projectionRaw Γ₁ h.hasType.1) =
    RawCtx.toCtx.map (projectionRaw Γ₁ h.hasType.2)
  rw [← RawCtx.toCtx.map_comp]
  congr 1

@[simp]
theorem contextConversion_binderVar (h : Γ₁.as.terms ⊢ A ≡ A' : .sort u) :
    Tm.presheaf.map (contextConversion h).op
        (Tm.rawBinderVar Γ₁.as.wf h.hasType.1) =
      Tm.rawBinderVar Γ₁.as.wf h.hasType.2 := by
  rw [contextConversion]
  unfold Tm.rawBinderVar
  erw [Tm.map_ofTyping]
  refine Tm.pairOfTyping_eq ⟨u, ?_⟩ ?_
  · change A' :: Γ₁.as.terms ⊢ A⟨↑⟩[Term.bvar] ≡ A'⟨↑⟩ : .sort u
    simp
    exact h.weak
  · change A' :: Γ₁.as.terms ⊢ (Term.bvar 0)[Term.bvar] ≡ .bvar 0 :
      A⟨↑⟩[Term.bvar]
    simp
    exact h.weak.symm.defeqDF (.bvar .zero h.hasType.2.weak)

end DomainSemantics.Ctx

namespace DomainSemantics.Raw.ContextSection

open CategoryTheory Ctx

variable {Γ₁ Γ₂ : Ctx} {A A' : Term} {u : Bool}

def convert (h : Γ₁.as.terms ⊢ A ≡ A' : .sort u) {σ₁ : Γ₂ ⟶ Γ₁}
    {label : Σ A : Ty Γ₂, Tm Γ₂ A} (s : Raw.ContextSection h.hasType.2 σ₁ label) :
    Raw.ContextSection h.hasType.1 σ₁ label :=
  s.map (contextConversion h) (by rw [contextConversion_projection, s.over])
    (contextConversion_binderVar h)

end DomainSemantics.Raw.ContextSection
