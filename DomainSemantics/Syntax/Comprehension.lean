/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Intrinsic

@[expose] public section

namespace DomainSemantics

open CategoryTheory

variable {A : Term} {u : Bool}

namespace Ctx

@[simp]
theorem map_binderVar_cons {Γ₁ : Ctx} (Γ₂ : Ctx)
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as) (e : Term)
    (he : Γ₁.as.terms ⊢ e : A.subst σ₁.subst) :
    Tm.presheaf.map (RawCtx.toCtx.map (Y := (extension Γ₂ hA).as) (σ₁.cons hA e he)).op
        (Tm.rawBinderVar Γ₂.as.wf hA) =
      Tm.pairOfTyping σ₁.srcWF (hA.subst σ₁.srcWF σ₁.typed) he := by
  unfold Tm.rawBinderVar
  erw [Tm.map_ofTyping]
  simp! [lift_subst_cons]

end Ctx

namespace Raw.ContextSection

open Ctx

def ofTyping {Γ₁ Γ₂ : Ctx}
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as) (e : Term)
    (he : Γ₁.as.terms ⊢ e : A.subst σ₁.subst) :
    Raw.ContextSection hA (RawCtx.toCtx.map σ₁)
      (Tm.pairOfTyping σ₁.srcWF (hA.subst σ₁.srcWF σ₁.typed) he) where
  hom := RawCtx.toCtx.map (σ₁.cons hA e he)
  over := cons_projection Γ₂ hA σ₁ e he
  generic := map_binderVar_cons Γ₂ hA σ₁ e he

def ofTerm {Γ₁ : Ctx} {e : Term}
    (hA : Γ₁.as.terms ⊢ A : .sort u) (he : Γ₁.as.terms ⊢ e : A) :
    Raw.ContextSection hA (𝟙 Γ₁) (Tm.pairOfTyping Γ₁.as.wf hA he) where
  hom := RawCtx.toCtx.map (Raw.Hom.one Γ₁.as.wf he)
  over := by
    change RawCtx.toCtx.map (Raw.Hom.one Γ₁.as.wf he) ≫ RawCtx.toCtx.map (projectionRaw Γ₁ hA) = 𝟙 Γ₁
    rw [← RawCtx.toCtx.map_comp]
    exact RawCtx.toCtx.map_id Γ₁.as
  generic := Tm.inst_rawBinderVar Γ₁.as.wf hA he

def ofHom {Γ₁ Γ₂ : Ctx}
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁ ⟶ extension Γ₂ hA) :
    Raw.ContextSection hA (σ₁ ≫ rawProjection Γ₂ hA)
      (Tm.presheaf.map σ₁.op (Tm.rawBinderVar Γ₂.as.wf hA)) :=
  Presheaf.Section.ofHom (rawExtensionIsRepresented hA) σ₁

end Raw.ContextSection

end DomainSemantics
