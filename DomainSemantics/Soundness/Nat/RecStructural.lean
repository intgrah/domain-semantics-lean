/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
public import DomainSemantics.Syntax.Comprehension.Pullback
import DomainSemantics.Interpretation.ApplicationSubstitution
import DomainSemantics.Interpretation.BinderSubstitution
import DomainSemantics.Interpretation.Nat.Relations
import DomainSemantics.Interpretation.Nat.Witnesses
import DomainSemantics.Soundness.Nat.Rules
import DomainSemantics.Soundness.StructuralRules

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment Presheaf

variable {Γ Γ₁ Γ₂ : Ctx} {C M a b : Term} {v : Bool}

theorem RawFamily.natRec_substitution_eq
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (θ : Γ₁.as ⟶ Γ.as)
    (Cs : RawFamily (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)))
    (Ct : RawFamily (Ctx.extension Γ₁ (.nat : Γ₁.as.terms ⊢ .nat : .type)))
    (Ms Zs Bs : RawFamily Γ) (Mt Zt Bt : RawFamily Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (ρs ρt : RawValuation Γ₂)
    (hMI : (Ms.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs).IsDirected)
    (hMs : Ms.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs = Mt.app _ σ.op ρt)
    (hZ : Zs.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs = Zt.app _ σ.op ρt)
    (hB : Bs.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs = Bt.app _ σ.op ρt)
    (hbody : ∀ {Γ₃ : Ctx} (σ₁ : Γ₃ ⟶ Γ₂) (label : Σ A : Ty Γ₃, Tm Γ₃ A)
      (s : Raw.ContextSection (.nat : Γ₁.as.terms ⊢ .nat : .type) (σ₁ ≫ σ) label)
      (J : Domain Γ₃),
      piLimit.rawExtend ((nat : RawFamily Γ).app _ ((σ₁ ≫ σ) ≫ RawCtx.toCtx.map θ).op
          (ρs.pullback σ₁)) J.val = J.val →
      Cs.app _ (s.hom ≫ Ctx.extensionMap (.nat : Γ.as.terms ⊢ .nat : .type) θ).op
          ((ρs.pullback σ₁).push J.val) =
        Ct.app _ s.hom.op ((ρt.pullback σ₁).push J.val)) :
    (natRec piLimit hC hM ha hb Cs Ms Zs Bs).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs =
      (natRec piLimit (Tm.natRec.substMotive hC θ)
        (hM.subst θ.srcWF θ.typed) (Tm.natRec.substZero ha θ)
        (Tm.natRec.substStep hb θ) Ct Mt Zt Bt).app _ σ.op ρt := by
  have hR : (NatRecLabelRelation.syntactic hC ha hb).pullback (σ ≫ RawCtx.toCtx.map θ) =
      (NatRecLabelRelation.syntactic (Tm.natRec.substMotive hC θ)
        (Tm.natRec.substZero ha θ)
        (Tm.natRec.substStep hb θ)).pullback σ := by
    rw [← NatRecLabelRelation.pullback_comp, NatRecLabelRelation.syntactic_pullback]
  have hlabel : Tm.presheaf.map (σ ≫ RawCtx.toCtx.map θ).op
        (Tm.pairOfTyping Γ.as.wf .nat hM) =
      Tm.presheaf.map σ.op
        (Tm.pairOfTyping Γ₁.as.wf .nat (hM.subst θ.srcWF θ.typed)) :=
    (reindex_ofTyping_subst .nat hM θ σ).symm
  change (RawAction.natRec piLimit
    (normalizedBodyAction piLimit (Ctx.rawDisplay .nat) nat Cs (σ ≫ RawCtx.toCtx.map θ) ρs)
    ((NatRecLabelRelation.syntactic hC ha hb).pullback (σ ≫ RawCtx.toCtx.map θ))
    (Zs.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs) (Bs.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs)).app _
      ((𝟙 Γ₂).op, Tm.presheaf.map (σ ≫ RawCtx.toCtx.map θ).op (Tm.pairOfTyping Γ.as.wf .nat hM))
      (Ms.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs) =
    (RawAction.natRec piLimit (normalizedBodyAction piLimit (Ctx.rawDisplay .nat) nat Ct σ ρt)
      ((NatRecLabelRelation.syntactic (Tm.natRec.substMotive hC θ)
        (Tm.natRec.substZero ha θ) (Tm.natRec.substStep hb θ)).pullback σ)
      (Zt.app _ σ.op ρt) (Bt.app _ σ.op ρt)).app _
        ((𝟙 Γ₂).op, Tm.presheaf.map σ.op (Tm.pairOfTyping Γ₁.as.wf .nat (hM.subst θ.srcWF θ.typed)))
        (Mt.app _ σ.op ρt)
  rw [hR, hlabel, ← hMs, ← hZ, ← hB]
  let I := (Ms.app _ (σ ≫ RawCtx.toCtx.map θ).op ρs).toIdeal hMI
  apply RawAction.natRec_eq_on_ideals piLimit _ _ _ (𝟙 Γ₂) _ I
  intro Γ₃ σ₁ label J
  apply normalizedBodyAction_substitution_eq_on_ideals
    (Ctx.rawDisplay (.nat : Γ.as.terms ⊢ .nat : .type)) (Ctx.rawDisplay .nat)
    (Ctx.extensionIsPullback .nat θ) (Ctx.map_extensionMap_binderVar .nat θ) nat nat Cs Ct σ ρs ρt
  · rw [nat_value]
    exact ΩLower.isDirected_principal _
  · simp only [nat_value]
  · exact hbody

theorem HasSubstitution.natRec (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (hMI : HasIdeality Γ M)
    (hCS : HasSubstitution (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (hMS : HasSubstitution Γ M) (haS : HasSubstitution Γ a) (hbS : HasSubstitution Γ b) :
    HasSubstitution Γ (.natRec C M a b) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  change (rawInterpret piLimit Γ₁ (.natRec (C[⇑θ.subst]) (M[θ.subst])
    (a[θ.subst]) (b[θ.subst]))).app _ σ.op ρt = _
  rw [rawInterpret_natRec piLimit hC hM ha hb,
    rawInterpret_natRec piLimit (Tm.natRec.substMotive hC θ)
      (hM.subst θ.srcWF θ.typed) (Tm.natRec.substZero ha θ)
      (Tm.natRec.substStep hb θ)]
  symm
  apply RawFamily.natRec_substitution_eq hC hM ha hb θ
  · exact hMI _ _ hρ
  · exact (hMS θ σ ρs ρt hθ hρ).symm
  · exact (haS θ σ ρs ρt hθ hρ).symm
  · exact (hbS θ σ ρs ρt hθ hρ).symm
  · exact HasSubstitution.binder_body (.nat : Γ.as.terms ⊢ .nat : .type)
      (HasIdeality.nat Γ) hCS θ σ ρs ρt hθ hρ

end DomainSemantics.CoherentShape
