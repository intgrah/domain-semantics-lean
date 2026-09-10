/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Structural
public import DomainSemantics.Soundness.SingleSubstitution
import DomainSemantics.Interpretation.BinderIdeality

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

def HasSubstitution (Γ : Ctx) (t : Term) : Prop :=
  ∀ {Γ₁ Γ₂ : Ctx} (θ : Γ₁.as ⟶ Γ.as) (σ : Γ₂ ⟶ Γ₁)
    (ρs ρt : RawValuation Γ₂),
    SingleSubstitution θ σ ρs ρt → SourceAdmissible (σ ≫ RawCtx.toCtx.map θ) ρs →
      (rawInterpret piLimit Γ₁ (t[θ.subst])).app _ σ.op ρt =
        (rawInterpret piLimit Γ t).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs

theorem HasRenaming.of_substitution {Γ : Ctx} {t : Term} (h : HasSubstitution Γ t) :
    HasRenaming Γ t :=
  fun r σ ρ hρ => h r.toRawHom σ _ ρ (.ren r σ ρ) hρ

def HasFixedness (Γ : Ctx) (t A : Term) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁),
    SourceAdmissible σ ρ →
      piLimit.rawExtend ((rawInterpret piLimit Γ A).app _ σ.op ρ)
        ((rawInterpret piLimit Γ t).app _ σ.op ρ) = (rawInterpret piLimit Γ t).app _ σ.op ρ

def HasEquality (Γ : Ctx) (t t' : Term) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁),
    SourceAdmissible σ ρ →
      (rawInterpret piLimit Γ t).app _ σ.op ρ = (rawInterpret piLimit Γ t').app _ σ.op ρ

def PiReady (Γ : Ctx) (A B : Term) : Prop :=
  ∃ (u v : Bool) (hA : Γ.as.terms ⊢ A : .sort u) (_ : A :: Γ.as.terms ⊢ B : .sort v),
    HasIdeality Γ A ∧ ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁),
      SourceAdmissible σ ρ →
        (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) (rawInterpret piLimit Γ A)
          (rawInterpret piLimit (Ctx.extension Γ hA) B) σ ρ).IsIdealValued

def HasReady (Γ : Ctx) : Term → Prop
  | .forallE A B => PiReady Γ A B
  | _ => True

structure RawTermProperties (Γ : Ctx) (t : Term) : Prop where
  ideal : HasIdeality Γ t
  subst : HasSubstitution Γ t
  ready : HasReady Γ t

theorem RawTermProperties.ren {Γ : Ctx} {t : Term} (p : RawTermProperties Γ t) :
    HasRenaming Γ t :=
  HasRenaming.of_substitution p.subst

structure RawJudgment (Γ : Ctx) (t t' A : Term) : Prop where
  regular : ∃ u, Γ.as.terms ⊢ A : .sort u ∧ HasFixedness Γ A (.sort u)
  type : RawTermProperties Γ A
  left : RawTermProperties Γ t
  right : RawTermProperties Γ t'
  equal : HasEquality Γ t t'
  fixed : HasFixedness Γ t A

noncomputable def RawJudgment.eval {Γ Γ₁ : Ctx} {t t' A : Term}
    (p : RawJudgment Γ t t' A) {σ : Γ₁ ⟶ Γ} {ρ : RawValuation Γ₁}
    (hρ : SourceAdmissible σ ρ) : Domain Γ₁ := hρ.eval p.left.ideal

theorem RawJudgment.eval_fixed {Γ Γ₁ : Ctx} {t t' A : Term}
    (p : RawJudgment Γ t t' A) {σ : Γ₁ ⟶ Γ} {ρ : RawValuation Γ₁}
    (hρ : SourceAdmissible σ ρ) :
    piLimit.rawExtend (hρ.eval p.type.ideal).val (p.eval hρ).val = (p.eval hρ).val :=
  p.fixed σ ρ hρ

theorem HasIdeality.bodyAction {Γ : Ctx} {A b : Term} {u : Bool}
    (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    (hbI : HasIdeality (Ctx.extension Γ hA) b)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) (rawInterpret piLimit Γ A)
      (rawInterpret piLimit (Ctx.extension Γ hA) b) σ ρ).IsIdealValued :=
  RawFamily.normalizedBodyAction_isIdealValued (Ctx.rawDisplay hA) _ _ σ ρ (hAI σ ρ hρ) (fun σ₁ _ s J hJ =>
    hbI s.hom ((ρ.pullback σ₁).push J.val)
      ((hρ.pullback σ₁).push hA s (hAI _ _ (hρ.pullback σ₁)) J.property hJ))

theorem HasSubstitution.instantiate {Γ : Ctx} {A a C : Term} {u : Bool}
    (hA : Γ.as.terms ⊢ A : .sort u) (ha : Γ.as.terms ⊢ a : A)
    (hAI : HasIdeality Γ A) (haI : HasIdeality Γ a) (haF : HasFixedness Γ a A)
    (haR : HasRenaming Γ a) (hC : HasSubstitution (Ctx.extension Γ hA) C)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret piLimit (Ctx.extension Γ hA) C).app _ (σ ≫ (Raw.ContextSection.ofTerm hA ha).hom).op
        (ρ.push ((rawInterpret piLimit Γ a).app _ σ.op ρ)) =
      (rawInterpret piLimit Γ (C[a/])).app _ σ.op ρ :=
  have hsource := hρ.push hA ((Raw.ContextSection.ofTerm hA ha).pullbackId σ)
    (hAI σ ρ hρ) (haI σ ρ hρ) (haF σ ρ hρ)
  (hC (Raw.Hom.one Γ.as.wf ha) σ _ ρ
    (SingleSubstitution.one hA ha haR σ ρ) hsource).symm

namespace HasEquality

variable {Γ : Ctx} {t t' t'' A : Term}

theorem refl (Γ : Ctx) (t : Term) : HasEquality Γ t t := fun _ _ _ ↦ rfl

theorem symm (h : HasEquality Γ t t') : HasEquality Γ t' t :=
  fun σ ρ hρ ↦ (h σ ρ hρ).symm

theorem trans (h : HasEquality Γ t t') (h' : HasEquality Γ t' t'') :
    HasEquality Γ t t'' := fun σ ρ hρ ↦ (h σ ρ hρ).trans (h' σ ρ hρ)

theorem eval (h : HasEquality Γ t t') {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {ρ : RawValuation Γ₁}
    (hρ : SourceAdmissible σ ρ) (ht : HasIdeality Γ t) (ht' : HasIdeality Γ t') :
    hρ.eval ht = hρ.eval ht' := Subtype.val_injective (h σ ρ hρ)

theorem fixed_right (h : HasEquality Γ t t') (hf : HasFixedness Γ t A) :
    HasFixedness Γ t' A := by
  intro Γ₁ σ ρ hρ
  rw [← h σ ρ hρ]
  exact hf σ ρ hρ

theorem ideal_right (h : HasEquality Γ t t') (hi : HasIdeality Γ t) :
    HasIdeality Γ t' := by
  intro Γ₁ σ ρ hρ
  rw [← h σ ρ hρ]
  exact hi σ ρ hρ

end HasEquality

namespace HasFixedness

variable {Γ : Ctx} {t A B : Term}

theorem convert (h : HasFixedness Γ t A) (hAB : HasEquality Γ A B) :
    HasFixedness Γ t B := by
  intro Γ₁ σ ρ hρ
  rw [← hAB σ ρ hρ]
  exact h σ ρ hρ

end HasFixedness

namespace PiReady

variable {Γ : Ctx} {A B : Term} {u : Bool}

theorem domain (h : PiReady Γ A B) : HasIdeality Γ A :=
  let ⟨_, _, _, _, hA, _⟩ := h
  hA

theorem action (h : PiReady Γ A B) (hA : Γ.as.terms ⊢ A : .sort u)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) (rawInterpret piLimit Γ A)
      (rawInterpret piLimit (Ctx.extension Γ hA) B) σ ρ).IsIdealValued := by
  have ⟨_, _, hA', _, _, h⟩ := h
  rw [Ctx.rawDisplay_congr hA hA']
  exact fun _ => h σ ρ hρ

end PiReady

namespace RawJudgment

variable {Γ : Ctx} {t t' t'' A B : Term}

theorem fixed_right (h : RawJudgment Γ t t' A) : HasFixedness Γ t' A :=
  HasEquality.fixed_right h.equal h.fixed

theorem symm (h : RawJudgment Γ t t' A) : RawJudgment Γ t' t A where
  regular := h.regular
  type := h.type
  left := h.right
  right := h.left
  equal := HasEquality.symm h.equal
  fixed := h.fixed_right

theorem trans (h : RawJudgment Γ t t' A) (h' : RawJudgment Γ t' t'' A') :
    RawJudgment Γ t t'' A where
  regular := h.regular
  type := h.type
  left := h.left
  right := h'.right
  equal := HasEquality.trans h.equal h'.equal
  fixed := h.fixed

theorem convert {u : Bool} (hAB : Γ.as.terms ⊢ A ≡ B : .sort u)
    (h : RawJudgment Γ A B (.sort u)) (ht : RawJudgment Γ t t' A) :
    RawJudgment Γ t t' B where
  regular := ⟨u, hAB.hasType.2, h.fixed_right⟩
  type := h.right
  left := ht.left
  right := ht.right
  equal := ht.equal
  fixed := HasFixedness.convert ht.fixed h.equal

end RawJudgment

end DomainSemantics.CoherentShape
