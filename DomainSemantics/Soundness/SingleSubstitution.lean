/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Renaming
import DomainSemantics.Meta.Judgement
import DomainSemantics.Syntax.Comprehension.Pullback

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory

judgement SingleSubstitution : {Γ Γ₁ Γ₂ : Ctx} → (Γ₁.as ⟶ Γ.as) →
    (Γ₂ ⟶ Γ₁) → RawValuation Γ₂ → RawValuation Γ₂ → Prop where

  ──────────────────── one {Γ Γ₂ : Ctx} {A a : Term} {u : Bool}
    (hA : Γ.as.terms ⊢ A : .sort u) (ha : Γ.as.terms ⊢ a : A)
    (hren : HasRenaming Γ a) (σ : Γ₂ ⟶ Γ) (ρ : RawValuation Γ₂)
  SingleSubstitution (Γ := Γ.extension hA) (Raw.Hom.one Γ.as.wf ha) σ
    (ρ.push ((rawInterpret CodeAssignment.piLimit Γ a).app _ σ.op ρ)) ρ

  ──────────────────── oneAlong {Γ Γ₁ Γ₂ : Ctx} {A a : Term} {u : Bool}
    (hA : Γ.as.terms ⊢ A : .sort u) (r : Ctx.VariableMap Γ₁ Γ)
    (ha : Γ₁.as.terms ⊢ a : A.subst r.toRawHom.subst) (hren : HasRenaming Γ₁ a)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hTarget : SourceAdmissible σ ρ)
  SingleSubstitution (Γ := Γ.extension hA) (r.toRawHom.cons hA a ha) σ
    (RawValuation.push (fun i ↦ ρ (r.index i))
      ((rawInterpret CodeAssignment.piLimit Γ₁ a).app _ σ.op ρ)) ρ

  ──────────────────── ren {Γ Γ₁ Γ₂ : Ctx} (r : Ctx.VariableMap Γ₁ Γ) (σ : Γ₂ ⟶ Γ₁)
    (ρ : RawValuation Γ₂)
  SingleSubstitution r.toRawHom σ (fun i ↦ ρ (r.index i)) ρ

  SingleSubstitution θ (σ ≫ Γ₁.rawProjection (hB.subst θ.srcWF θ.typed)) ρs ρt.tail
  ──────────────────── lift {Γ Γ₁ Γ₂ : Ctx} {B : Term} {w : Bool}
    (hB : Γ.as.terms ⊢ B : .sort w) (θ : Γ₁.as ⟶ Γ.as)
    (σ : Γ₂ ⟶ Γ₁.extension (hB.subst θ.srcWF θ.typed)) (ρs ρt : RawValuation Γ₂)
  SingleSubstitution (Γ := Γ.extension hB) (θ.lift hB) σ (ρs.push (ρt 0)) ρt

namespace SingleSubstitution

variable {Γ Γ₁ Γ₂ : Ctx} {θ : Γ₁.as ⟶ Γ.as}
  {σ : Γ₂ ⟶ Γ₁} {ρs ρt : RawValuation Γ₂}

theorem pullback (h : SingleSubstitution θ σ ρs ρt) {Γ₃ : Ctx} (σ₁ : Γ₃ ⟶ Γ₂) :
    SingleSubstitution θ (σ₁ ≫ σ) (ρs.pullback σ₁) (ρt.pullback σ₁) := by
  induction h with
  | one hA ha hren σ ρ =>
    rw [RawValuation.pullback_push, RawFamily.app_pullback]
    exact SingleSubstitution.one hA ha hren (σ₁ ≫ σ) (ρ.pullback σ₁)
  | oneAlong hA r ha hren σ ρ hTarget =>
    rw [RawValuation.pullback_push, RawFamily.app_pullback]
    exact SingleSubstitution.oneAlong hA r ha hren (σ₁ ≫ σ) (ρ.pullback σ₁)
      (hTarget.pullback σ₁)
  | ren r σ ρ => exact SingleSubstitution.ren r (σ₁ ≫ σ) (ρ.pullback σ₁)
  | lift hB θ σ ρs ρt _ ih =>
    rw [RawValuation.pullback_push]
    apply SingleSubstitution.lift hB θ (σ₁ ≫ σ) (ρs.pullback σ₁) (ρt.pullback σ₁)
    simpa using ih σ₁

theorem variable_reindex (h : SingleSubstitution θ σ ρs ρt)
    {Γ₃ : Ctx} (r : Ctx.VariableMap Γ₃ Γ₁) (σ₁ : Γ₂ ⟶ Γ₃)
    (ν : RawValuation Γ₂) :
      σ₁ ≫ r.hom = σ → (∀ i, ν (r.index i) = ρt i) →
      SourceAdmissible (σ ≫ RawCtx.toCtx.map θ) ρs → ∀ i,
      (rawInterpret CodeAssignment.piLimit Γ₃ ((θ.subst i).subst r.toRawHom.subst)).app _ σ₁.op ν = ρs i := by
  intro hσ hν hsource i
  induction h generalizing i with
  | @one Γ Γ₂ A a u hA ha hren σ ρ =>
    have htail := SourceAdmissible.tail hA hsource
    have hover : RawCtx.toCtx.map
        (Raw.Hom.one Γ.as.wf ha) ≫ Ctx.rawProjection Γ hA = 𝟙 Γ :=
      (Raw.ContextSection.ofTerm hA ha).over
    rw [Category.assoc, hover, Category.comp_id, RawValuation.tail_push] at htail
    have hν' : (fun i ↦ ν (r.index i)) = ρ := funext hν
    cases i with
    | zero =>
      change (rawInterpret CodeAssignment.piLimit Γ₃ (a.subst r.toRawHom.subst)).app _ σ₁.op ν = (rawInterpret CodeAssignment.piLimit Γ a).app _ σ.op ρ
      simpa [hσ, hν'] using hren r σ₁ ν (by simpa [hσ, hν'] using htail)
    | succ i => exact hν i
  | @oneAlong Γ Γ₁ Γ₂ A a u hA r₀ ha hren σ ρ hTarget =>
      have hν' : (fun i ↦ ν (r.index i)) = ρ := funext hν
      cases i with
      | zero =>
        change (rawInterpret CodeAssignment.piLimit Γ₃ (a.subst r.toRawHom.subst)).app _ σ₁.op ν = (rawInterpret CodeAssignment.piLimit Γ₁ a).app _ σ.op ρ
        simpa [hσ, hν'] using hren r σ₁ ν (by simpa [hσ, hν'] using hTarget)
      | succ i => exact hν (r₀.index i)
  | ren r₀ σ ρ => exact hν (r₀.index i)
  | @lift Γ Γ₁ Γ₂ B w hB θ σ ρs ρt htail ih =>
    have hsourceTail := SourceAdmissible.tail hB hsource
    change SourceAdmissible
      ((σ ≫ Ctx.extensionMap hB θ) ≫ Ctx.rawProjection Γ hB)
      (ρs.push (ρt 0)).tail at hsourceTail
    rw [Category.assoc, Ctx.extensionMap_projection hB θ, ← Category.assoc,
      RawValuation.tail_push] at hsourceTail
    cases i with
    | zero => exact hν 0
    | succ i =>
      change (rawInterpret CodeAssignment.piLimit Γ₃
        ((θ.subst i).lift.subst r.toRawHom.subst)).app _ σ₁.op ν = ρs i
      rw [lift_subst]
      have hB' : Γ₁.as.terms ⊢ B.subst θ.subst : .sort w := hB.subst θ.srcWF θ.typed
      have hcomp : σ₁ ≫ (r.tail hB').hom = σ ≫ Ctx.rawProjection Γ₁ hB' := by
        rw [Ctx.VariableMap.tail_hom, ← Category.assoc, hσ]
      exact ih (r.tail hB') σ₁ ν hcomp (fun j ↦ hν (j + 1)) hsourceTail i

theorem variable_eq (h : SingleSubstitution θ σ ρs ρt)
    (hsource : SourceAdmissible (σ ≫ RawCtx.toCtx.map θ) ρs) (i : ℕ) :
    (rawInterpret CodeAssignment.piLimit Γ₁ (θ.subst i)).app _ σ.op ρt = ρs i := by
  have hvar := h.variable_reindex (Ctx.VariableMap.id Γ₁) σ ρt
    (Category.comp_id σ) (fun _ ↦ rfl) hsource i
  change (rawInterpret CodeAssignment.piLimit Γ₁ ((θ.subst i).subst Subst.id)).app _ σ.op ρt = ρs i at hvar
  simpa using hvar

end SingleSubstitution

end DomainSemantics.CoherentShape
