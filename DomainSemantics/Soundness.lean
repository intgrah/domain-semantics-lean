/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.BasicJudgments
public import DomainSemantics.Soundness.BinderRules
public import DomainSemantics.Soundness.EliminationRules
public import DomainSemantics.Soundness.Nat.RecRules
public import DomainSemantics.Soundness.Nat.RecComputation
import DomainSemantics.Soundness.Nat.Rules
import DomainSemantics.Domain.Decoder.DecoderStrictness

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics

open CategoryTheory CoherentShape CodeAssignment Presheaf

variable {Γ : List Term}

theorem IsDefEq.rawSemantics {t t' A : Term}
    (d : Γ ⊢ t ≡ t' : A) (hΓ : ⊢ Γ) :
    ContextRen (RawCtx.toCtx.obj ⟨Γ, hΓ⟩) → RawJudgment (RawCtx.toCtx.obj ⟨Γ, hΓ⟩) t t' A := by
  intro hR
  induction d with
  | bvar hi hA ihA =>
    exact RawJudgment.bvar hi hA (ihA hΓ hR) hR
  | symm _ ih =>
    exact (ih hΓ hR).symm
  | trans _ _ ih₁ ih₂ | trans' _ _ ih₁ ih₂ =>
    exact (ih₁ hΓ hR).trans (ih₂ hΓ hR)
  | sort =>
    exact RawJudgment.sort (RawCtx.toCtx.obj ⟨_, hΓ⟩) _
  | appDF hA hB _ ha hResult ihA ihB ihf iha ihResult =>
    exact RawJudgment.appDF hA hB ha hResult
      (ihB (.cons hΓ hA) (.cons hA hR (ihA hΓ hR).left.ren))
      (ihf hΓ hR) (iha hΓ hR) (ihResult hΓ hR)
  | lamDF hA hB _ _ hPi ihA ihB ihBody ihBody' ihPi =>
    have pA := ihA hΓ hR
    have hRA := ContextRen.cons hA.hasType.1 hR pA.left.ren
    have hRA' := ContextRen.cons hA.hasType.2 hR pA.right.ren
    exact RawJudgment.lamDF hA hB hPi
      pA (ihB _ hRA) (ihBody _ hRA) (ihBody' _ hRA') (ihPi hΓ hR)
  | forallEDF hA hB hB' ihA ihB ihB' =>
    have pA := ihA hΓ hR
    have hRA := ContextRen.cons hA.hasType.1 hR pA.left.ren
    have hRA' := ContextRen.cons hA.hasType.2 hR pA.right.ren
    exact RawJudgment.forallEDF hA hB hB'
      pA (ihB _ hRA) (ihB' _ hRA')
  | defeqDF hAB _ ihAB iht =>
    exact RawJudgment.convert hAB (ihAB hΓ hR) (iht hΓ hR)
  | beta hA _ ha _ _ ihA ihBody iha ihApp ihInst =>
    have pA := ihA hΓ hR
    exact RawJudgment.beta hA ha pA
      (ihBody (.cons hΓ hA) (.cons hA hR pA.left.ren))
      (iha hΓ hR) (ihApp hΓ hR) (ihInst hΓ hR)
  | eta _ _ ihe ihLam =>
    exact RawJudgment.eta (ihe hΓ hR) (ihLam hΓ hR)
  | nat =>
    exact RawJudgment.nat (RawCtx.toCtx.obj ⟨_, hΓ⟩)
  | zero =>
    exact RawJudgment.zero (RawCtx.toCtx.obj ⟨_, hΓ⟩)
  | succDF hn ihn =>
    exact RawJudgment.succDF hn (ihn hΓ hR)
  | natRecDF hC hM ha hb hResult ihC ihM iha ihb ihResult =>
    have pC := ihC (.cons hΓ .nat)
      (.cons .nat hR (HasRenaming.of_substitution (HasSubstitution.nat _)))
    exact RawJudgment.natRecDF hC hM
      ha hb hResult pC
      (ihM hΓ hR) (iha hΓ hR) (ihb hΓ hR) (ihResult hΓ hR)
  | natRec_zero hC ha hb _ ihC iha _ ihRec =>
    have pC := ihC (.cons hΓ .nat)
      (.cons .nat hR (HasRenaming.of_substitution (HasSubstitution.nat _)))
    exact RawJudgment.natRec_zero hC ha hb
      pC (iha hΓ hR) (ihRec hΓ hR)
  | natRec_succ hC hn ha hb _ _ ihC ihn iha ihb ihRec ihStep =>
    have pC := ihC (.cons hΓ .nat)
      (.cons .nat hR (HasRenaming.of_substitution (HasSubstitution.nat _)))
    exact RawJudgment.natRec_succ hC hn
      ha hb pC (ihn hΓ hR)
      (iha hΓ hR) (ihb hΓ hR) (ihRec hΓ hR) (ihStep hΓ hR)
  | idDF _ _ _ ihA iha ihb =>
    exact RawJudgment.idDF (ihA hΓ hR) (iha hΓ hR) (ihb hΓ hR)
  | reflDF _ _ hId _ _ ihId =>
    exact RawJudgment.reflDF hId (ihId hΓ hR)
  | trDF hA _ hb hC hC' _ _ hTarget _ ihA _ ihb ihC ihC' ihx _ ihTarget _ =>
    have pA := ihA hΓ hR
    have hRA := ContextRen.cons hA.hasType.1 hR pA.left.ren
    have hRA' := ContextRen.cons hA.hasType.2 hR pA.right.ren
    exact RawJudgment.trDF hA hb hTarget
      pA (ihb hΓ hR) (ihC _ hRA) (ihC' _ hRA') (ihx hΓ hR) (ihTarget hΓ hR)
  | tr_K hA hab _ _ _ _ _ ihA ihab ihC ihx _ ihTr ihTarget =>
    have pA := ihA hΓ hR
    exact RawJudgment.tr_K hA hab pA (ihab hΓ hR)
      (ihC (.cons hΓ hA) (.cons hA hR pA.left.ren))
      (ihx hΓ hR) (ihTr hΓ hR) (ihTarget hΓ hR)
  | proofIrrel _ _ _ ihp iht iht' =>
    exact RawJudgment.proofIrrel (ihp hΓ hR) (iht hΓ hR) (iht' hΓ hR)

theorem Raw.WF.contextRen {Γ : List Term} (hΓ : Raw.WF Γ) : ContextRen (RawCtx.toCtx.obj ⟨Γ, hΓ⟩) := by
  induction hΓ with
  | nil => exact .nil
  | cons hΓ hA ih => exact .cons hA ih (hA.rawSemantics hΓ ih).left.ren

theorem IsDefEq.rawSoundness {t t' A : Term}
    (hΓ : Raw.WF Γ) (d : Γ ⊢ t ≡ t' : A) :
    RawJudgment (RawCtx.toCtx.obj ⟨Γ, hΓ⟩) t t' A :=
  d.rawSemantics hΓ hΓ.contextRen

theorem Raw.WF.bottom_admissible {Γ : List Term} (hΓ : Raw.WF Γ) {Γ₁ : Ctx}
    (σ : Γ₁ ⟶ ((RawCtx.toCtx.obj ⟨Γ, hΓ⟩) : Ctx)) : SourceAdmissible σ (fun _ ↦ ⊥) := by
  induction hΓ with
  | nil => exact .nil σ _
  | cons hΓ hA ih =>
    have htail := ih (σ ≫ Ctx.rawProjection (RawCtx.toCtx.obj ⟨_, hΓ⟩) hA)
    exact SourceAdmissible.cons hA σ (fun _ ↦ ⊥) htail ((hA.rawSoundness hΓ).left.ideal _ _ htail)
      ΩLower.isDirected_bot (rawExtend_bottom_payload piLimit_isPayloadStrict _)

end DomainSemantics
