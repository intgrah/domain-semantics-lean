/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Comprehension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

namespace DomainSemantics

open CategoryTheory Limits

variable {Γ₁ Γ₂ Γ₃ : Ctx} {A : Term} {u : Bool}

namespace Ctx

def extensionMap
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as) :
    extension Γ₁ (hA.subst σ₁.srcWF σ₁.typed) ⟶ extension Γ₂ hA :=
  RawCtx.toCtx.map (σ₁.lift hA)

theorem extensionMap_projection
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as) :
    extensionMap hA σ₁ ≫ rawProjection Γ₂ hA =
      rawProjection Γ₁ (hA.subst σ₁.srcWF σ₁.typed) ≫ RawCtx.toCtx.map σ₁ := by
  change RawCtx.toCtx.map (σ₁.lift hA) ≫ RawCtx.toCtx.map (projectionRaw Γ₂ hA) =
    RawCtx.toCtx.map (projectionRaw Γ₁ (hA.subst σ₁.srcWF σ₁.typed)) ≫ RawCtx.toCtx.map σ₁
  rw [← RawCtx.toCtx.map_comp, ← RawCtx.toCtx.map_comp]
  congr 1
  apply Raw.Hom.ext
  funext i
  change (σ₁.subst i).lift =
    (σ₁.subst i).subst (Subst.id.lift_r (.skip .refl))
  rw [← lift'_subst, subst_id]

@[simp]
theorem map_extensionMap_binderVar
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as) :
    Tm.presheaf.map (extensionMap hA σ₁).op
        (Tm.rawBinderVar Γ₂.as.wf hA) =
      Tm.rawBinderVar Γ₁.as.wf (hA.subst σ₁.srcWF σ₁.typed) := by
  rw [extensionMap]
  unfold Tm.rawBinderVar
  erw [Tm.map_ofTyping]
  simp! [lift_subst_lift]

theorem extensionIsPullback
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as) :
    IsPullback (extensionMap hA σ₁)
      (rawProjection Γ₁ (hA.subst σ₁.srcWF σ₁.typed))
      (rawProjection Γ₂ hA) (RawCtx.toCtx.map σ₁) := by
  apply IsPullback.of_map yoneda (extensionMap_projection hA σ₁)
  have h := rawExtensionIsRepresented (hA.subst σ₁.srcWF σ₁.typed)
  have hg := congrArg (fun a => a.2.val) (map_extensionMap_binderVar hA σ₁)
  change yoneda.map (extensionMap hA σ₁) ≫ (Tm.rawBinderVar Γ₂.as.wf hA).2.val = _ at hg
  rw [← hg, ← Ty.map_ofTyping hA σ₁] at h
  exact h.of_right (by simpa using congrArg yoneda.map (extensionMap_projection hA σ₁))
    (rawExtensionIsRepresented hA)

end Ctx

namespace Raw.ContextSection

open Ctx

def mapExtension
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as)
    {σ₂ : Γ₃ ⟶ Γ₁} {label : Σ A : Ty Γ₃, Tm Γ₃ A}
    (s : Raw.ContextSection (hA.subst σ₁.srcWF σ₁.typed) σ₂ label) :
    Raw.ContextSection hA (σ₂ ≫ RawCtx.toCtx.map σ₁) label :=
  s.map (extensionMap hA σ₁) (by rw [extensionMap_projection, ← Category.assoc, s.over])
    (map_extensionMap_binderVar hA σ₁)

noncomputable def cartesianLift
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as)
    {σ₂ : Γ₃ ⟶ Γ₁} {label : Σ A : Ty Γ₃, Tm Γ₃ A}
    (s : Raw.ContextSection hA (σ₂ ≫ RawCtx.toCtx.map σ₁) label) :
    Raw.ContextSection (hA.subst σ₁.srcWF σ₁.typed) σ₂ label :=
  s.lift (extensionIsPullback hA σ₁) (map_extensionMap_binderVar hA σ₁)

@[simp]
theorem cartesianLift_extensionMap
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as)
    {σ₂ : Γ₃ ⟶ Γ₁} {label : Σ A : Ty Γ₃, Tm Γ₃ A}
    (s : Raw.ContextSection hA (σ₂ ≫ RawCtx.toCtx.map σ₁) label) :
    (cartesianLift hA σ₁ s).hom ≫ extensionMap hA σ₁ = s.hom :=
  (extensionIsPullback hA σ₁).lift_fst s.hom σ₂ s.over

end Raw.ContextSection

end DomainSemantics
