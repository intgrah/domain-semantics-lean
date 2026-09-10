/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation
import DomainSemantics.Meta.Judgement
public import DomainSemantics.Domain.Decoder.PiStages

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

judgement SourceAdmissible : {Γ : List Term} → {hΓ₁ : Raw.WF Γ} →
    {Γ₂ : Ctx} → (Γ₂ ⟶ ((RawCtx.toCtx.obj ⟨Γ, hΓ₁⟩) : Ctx)) → RawValuation Γ₂ → Prop where

  ──────────────────── nil {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ (RawCtx.toCtx.obj ⟨[], .nil⟩)) (ρ : RawValuation Γ₂)
  SourceAdmissible σ₁ ρ

  SourceAdmissible (σ₁ ≫ (RawCtx.toCtx.obj ⟨Γ, hΓ₁⟩).rawProjection hA) ρ.tail
  ((rawInterpret CodeAssignment.piLimit (RawCtx.toCtx.obj ⟨Γ, hΓ₁⟩) A).app _
    (σ₁ ≫ (RawCtx.toCtx.obj ⟨Γ, hΓ₁⟩).rawProjection hA).op ρ.tail).IsDirected
  (ρ 0).IsDirected
  CodeAssignment.piLimit.rawExtend
    ((rawInterpret CodeAssignment.piLimit (RawCtx.toCtx.obj ⟨Γ, hΓ₁⟩) A).app _
      (σ₁ ≫ (RawCtx.toCtx.obj ⟨Γ, hΓ₁⟩).rawProjection hA).op ρ.tail) (ρ 0) = ρ 0
  ──────────────────── cons {Γ : List Term} {hΓ₁ : Raw.WF Γ} {Γ₂ : Ctx} {A : Term} {u : Bool}
    (hA : Γ ⊢ A : .sort u) (σ₁ : Γ₂ ⟶ (RawCtx.toCtx.obj ⟨Γ, hΓ₁⟩).extension hA)
    (ρ : RawValuation Γ₂)
  SourceAdmissible σ₁ ρ

namespace SourceAdmissible

variable {Γ₁ Γ₂ Γ₃ : Ctx} {A : Term} {u : Bool}

theorem cons_iff (hA : Γ₁.as.terms ⊢ A : .sort u)
    (σ₁ : Γ₂ ⟶ Ctx.extension Γ₁ hA) (ρ : RawValuation Γ₂) :
    SourceAdmissible σ₁ ρ ↔
      SourceAdmissible (σ₁ ≫ Ctx.rawProjection Γ₁ hA) ρ.tail ∧
      ((rawInterpret CodeAssignment.piLimit Γ₁ A).app _ (σ₁ ≫ Ctx.rawProjection Γ₁ hA).op ρ.tail).IsDirected ∧
      (ρ 0).IsDirected ∧
      CodeAssignment.piLimit.rawExtend
        ((rawInterpret CodeAssignment.piLimit Γ₁ A).app _ (σ₁ ≫ Ctx.rawProjection Γ₁ hA).op ρ.tail) (ρ 0) = ρ 0 := by
  constructor
  · intro hρ
    cases hρ with
    | cons _ _ _ htail hAideal hhead hfixed =>
      exact ⟨htail, hAideal, hhead, hfixed⟩
  · intro ⟨htail, hAideal, hhead, hfixed⟩
    exact .cons hA σ₁ ρ htail hAideal hhead hfixed

theorem tail (hA : Γ₁.as.terms ⊢ A : .sort u)
    {σ₁ : Γ₂ ⟶ Ctx.extension Γ₁ hA} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ₁ ρ) :
    SourceAdmissible (σ₁ ≫ Ctx.rawProjection Γ₁ hA) ρ.tail :=
  ((cons_iff hA σ₁ ρ).mp hρ).1

theorem pullback {σ₁ : Γ₂ ⟶ Γ₁} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ₁ ρ) (σ₂ : Γ₃ ⟶ Γ₂) :
    SourceAdmissible (σ₂ ≫ σ₁) (ρ.pullback σ₂) := by
  have ⟨Γ, hΓ₁⟩ := Γ₁
  change @SourceAdmissible Γ hΓ₁ Γ₂ σ₁ ρ at hρ
  induction hρ with
  | nil σ₁ ρ => exact .nil _ _
  | @cons Γ hΓ₁ Γ₂ A u hA σ₁ ρ htail hAideal hhead hfixed ih =>
    refine cons hA (σ₂ ≫ σ₁) (ρ.pullback σ₂) ?_ ?_ ?_ ?_
    · simpa using ih σ₂
    · rw [Category.assoc, ← RawValuation.pullback_tail,
        op_comp, ← RawFamily.app_pullback]
      exact hAideal.pullback σ₂
    · exact hhead.pullback σ₂
    · have h := congrArg (fun X : RawValue Γ₂ ↦ X.pullback σ₂) hfixed
      rw [CodeAssignment.pullback_rawExtend, RawFamily.app_pullback] at h
      simpa [RawValuation.pullback] using h

theorem push {σ₁ : Γ₂ ⟶ Γ₁} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ₁ ρ) (hA : Γ₁.as.terms ⊢ A : .sort u)
    {label : Σ A : Ty Γ₂, Tm Γ₂ A} (s : Raw.ContextSection hA σ₁ label)
    {X : RawValue Γ₂}
    (hAideal : ((rawInterpret CodeAssignment.piLimit Γ₁ A).app _ σ₁.op ρ).IsDirected)
    (hX : X.IsDirected)
    (hfixed : CodeAssignment.piLimit.rawExtend
      ((rawInterpret CodeAssignment.piLimit Γ₁ A).app _ σ₁.op ρ) X = X) :
    SourceAdmissible s.hom (ρ.push X) :=
  cons hA s.hom (ρ.push X) (s.over.symm ▸ hρ)
    (s.over.symm ▸ hAideal) hX (s.over.symm ▸ hfixed)

end SourceAdmissible

end DomainSemantics.CoherentShape
