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
import DomainSemantics.Interpretation.Witnesses

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

variable {Γ Γ₁ Γ₂ : Ctx} {A B a b C x h : Term} {u v : Bool}

namespace HasSubstitution

theorem bvar (Γ : Ctx) (i : ℕ) : HasSubstitution Γ (.bvar i) :=
  fun _ _ _ _ hθ hρ => hθ.variable_eq hρ i

theorem sort (Γ : Ctx) (u : Bool) : HasSubstitution Γ (.sort u) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  simp only [Term.subst, rawInterpret, RawFamily.sort_value]

theorem refl (Γ : Ctx) (a : Term) : HasSubstitution Γ (.refl a) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  rfl

theorem identity (hA : HasSubstitution Γ A) (ha : HasSubstitution Γ a)
    (hb : HasSubstitution Γ b) : HasSubstitution Γ (.id A a b) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  exact congr(RawValue.identity $(hA θ σ ρs ρt hθ hρ)
    $(ha θ σ ρs ρt hθ hρ) $(hb θ σ ρs ρt hθ hρ))

theorem binder_body (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    (hb : HasSubstitution (Ctx.extension Γ hA) b)
    (θ : Γ₁.as ⟶ Γ.as) (σ : Γ₂ ⟶ Γ₁) (ρs ρt : RawValuation Γ₂)
    (hθ : SingleSubstitution θ σ ρs ρt)
    (hρ : SourceAdmissible (σ ≫ RawCtx.toCtx.map θ) ρs)
    {Γ₃ : Ctx} (σ₁ : Γ₃ ⟶ Γ₂) (name : Σ A : Ty Γ₃, Tm Γ₃ A)
    (s : Raw.ContextSection (hA.subst θ.srcWF θ.typed) (σ₁ ≫ σ) name)
    (J : Domain Γ₃)
    (hJ : piLimit.rawExtend
      ((rawInterpret piLimit Γ A).app _ ((σ₁ ≫ σ) ≫ RawCtx.toCtx.map θ).op
        (ρs.pullback σ₁)) J.val = J.val) :
    (rawInterpret piLimit (Ctx.extension Γ hA) b).app _ (s.hom ≫ Ctx.extensionMap hA θ).op ((ρs.pullback σ₁).push J.val) =
      (rawInterpret piLimit (Ctx.extension Γ₁ (hA.subst θ.srcWF θ.typed))
        (b.subst θ.subst.lift)).app _ s.hom.op
        ((ρt.pullback σ₁).push J.val) := by
  have hbase : SourceAdmissible ((σ₁ ≫ σ) ≫ RawCtx.toCtx.map θ) (ρs.pullback σ₁) := by
    simpa using hρ.pullback σ₁
  have hhead := hbase.push hA (s.mapExtension hA θ)
    (hAI _ _ hbase) J.property hJ
  have htail : SingleSubstitution θ
      (s.hom ≫ Ctx.rawProjection Γ₁ (hA.subst θ.srcWF θ.typed))
      (ρs.pullback σ₁) ((ρt.pullback σ₁).push J.val).tail := by
    rw [s.over, RawValuation.tail_push]
    exact hθ.pullback σ₁
  have htest := SingleSubstitution.lift hA θ s.hom (ρs.pullback σ₁)
    ((ρt.pullback σ₁).push J.val) htail
  exact (hb (Γ₁ := Ctx.extension Γ₁ (hA.subst θ.srcWF θ.typed))
    (θ.lift hA) s.hom ((ρs.pullback σ₁).push J.val)
    ((ρt.pullback σ₁).push J.val) htest hhead).symm

theorem lam (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    (hAs : HasSubstitution Γ A) (hb : HasSubstitution (Ctx.extension Γ hA) b) :
    HasSubstitution Γ (.lam A b) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  change (rawInterpret piLimit Γ₁ (.lam (A.subst θ.subst) (b.subst θ.subst.lift))).app _ σ.op ρt = _
  rw [rawInterpret_lam piLimit hA,
    rawInterpret_lam piLimit (hA.subst θ.srcWF θ.typed)]
  symm
  apply RawFamily.abstraction_substitution_eq (Ctx.rawDisplay hA) (Ctx.rawDisplay (hA.subst θ.srcWF θ.typed))
    (Ctx.extensionIsPullback hA θ) (Ctx.map_extensionMap_binderVar hA θ)
  · exact hAI _ _ hρ
  · exact (hAs θ σ ρs ρt hθ hρ).symm
  · exact binder_body hA hAI hb θ σ ρs ρt hθ hρ

theorem forallE (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hAI : HasIdeality Γ A) (hAs : HasSubstitution Γ A)
    (hBs : HasSubstitution (Ctx.extension Γ hA) B) :
    HasSubstitution Γ (.forallE A B) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  have hBθ : A.subst θ.subst :: Γ₁.as.terms ⊢ B.subst θ.subst.lift : .sort v := by
    simpa [Ctx.extension, Term.subst] using
      hB.subst (Ctx.extension Γ₁ (hA.subst θ.srcWF θ.typed)).as.wf (θ.lift hA).typed
  change (rawInterpret piLimit Γ₁ (.forallE (A.subst θ.subst) (B.subst θ.subst.lift))).app _ σ.op ρt = _
  rw [rawInterpret_forallE piLimit hA hB,
    rawInterpret_forallE piLimit (hA.subst θ.srcWF θ.typed) hBθ]
  symm
  erw [← Ty.pairPresheaf_map_ofTyping hA hB θ]
  exact
    RawFamily.pi_substitution_eq (Ctx.rawDisplay hA) (Ctx.rawDisplay (hA.subst θ.srcWF θ.typed))
    (Ctx.extensionIsPullback hA θ) (Ctx.map_extensionMap_binderVar hA θ) (Ty.pairOfTyping Γ.as.wf hA hB)
      _ _ _ _ σ ρs ρt (hAI _ _ hρ) (hAs θ σ ρs ρt hθ hρ).symm
      (binder_body hA hAI hBs θ σ ρs ρt hθ hρ)

end HasSubstitution

theorem HasSubstitution.app (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (ha : Γ.as.terms ⊢ a : A) (hAI : HasIdeality Γ A)
    (hfI : HasIdeality Γ f) (haI : HasIdeality Γ a)
    (hfF : HasFixedness Γ f (.forallE A B))
    (hbody : ∀ {Γ₂ : Ctx} (σ : Γ₂ ⟶ Γ) (ρ : RawValuation Γ₂),
      SourceAdmissible σ ρ →
        (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) (rawInterpret piLimit Γ A)
          (rawInterpret piLimit (Ctx.extension Γ hA) B) σ ρ).IsIdealValued)
    (hfs : HasSubstitution Γ f) (has : HasSubstitution Γ a) :
    HasSubstitution Γ (.app f a) :=
  fun θ σ ρs ρt hθ hρ => rawInterpret_app_subst hA hB ha θ σ ρs ρt
    (hAI _ _ hρ) (hbody _ _ hρ) (hfI _ _ hρ) (haI _ _ hρ)
    (hfF _ _ hρ) (hfs θ σ ρs ρt hθ hρ) (has θ σ ρs ρt hθ hρ)

private theorem ofTerm_subst_hom (hA : Γ.as.terms ⊢ A : .sort u)
    (hb : Γ.as.terms ⊢ b : A) (θ : Γ₁.as ⟶ Γ.as) :
    (Raw.ContextSection.ofTerm (hA.subst θ.srcWF θ.typed)
        (hb.subst θ.srcWF θ.typed)).hom ≫ Ctx.extensionMap hA θ =
      RawCtx.toCtx.map θ ≫ (Raw.ContextSection.ofTerm hA hb).hom := by
  change RawCtx.toCtx.map (Y := (Ctx.extension Γ₁ (hA.subst θ.srcWF θ.typed)).as)
    (Raw.Hom.one Γ₁.as.wf (hb.subst θ.srcWF θ.typed)) ≫
    RawCtx.toCtx.map (X := (Ctx.extension Γ₁ (hA.subst θ.srcWF θ.typed)).as) (θ.lift hA) =
    RawCtx.toCtx.map θ ≫ RawCtx.toCtx.map (Y := (Ctx.extension Γ hA).as)
      (Raw.Hom.one Γ.as.wf hb)
  rw [← RawCtx.toCtx.map_comp, ← RawCtx.toCtx.map_comp]
  apply congrArg (RawCtx.toCtx.map)
  apply Raw.Hom.ext
  funext i
  cases i with
  | zero => rfl
  | succ i => exact lift_inst _

theorem HasSubstitution.tr (hA : Γ.as.terms ⊢ A : .sort u) (hb : Γ.as.terms ⊢ b : A)
    (hAI : HasIdeality Γ A) (hbI : HasIdeality Γ b) (hbF : HasFixedness Γ b A)
    (hbs : HasSubstitution Γ b) (hCs : HasSubstitution (Ctx.extension Γ hA) C)
    (hxs : HasSubstitution Γ x) : HasSubstitution Γ (.tr A a b C x h) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  have hAθ : Γ₁.as.terms ⊢ A.subst θ.subst : .sort u := hA.subst θ.srcWF θ.typed
  let Y := (rawInterpret piLimit Γ b).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs
  let s := (Raw.ContextSection.ofTerm hAθ
    (hb.subst θ.srcWF θ.typed)).pullbackId σ
  have hhead := hρ.push hA (Raw.ContextSection.mapExtension hA θ s)
    (hAI _ _ hρ) (hbI _ _ hρ) (hbF _ _ hρ)
  have htail : SingleSubstitution θ
      (s.hom ≫ Ctx.rawProjection Γ₁ hAθ)
      ρs (ρt.push Y).tail := by
    rw [s.over, RawValuation.tail_push]
    exact hθ
  have htest := SingleSubstitution.lift hA θ s.hom ρs (ρt.push Y) htail
  have hbody := hCs (Γ₁ := Ctx.extension Γ₁ hAθ)
    (θ.lift hA) s.hom (ρs.push Y) (ρt.push Y) htest hhead
  change (rawInterpret piLimit (Ctx.extension Γ₁ hAθ)
      (C.subst θ.subst.lift)).app _ s.hom.op (ρt.push Y) =
    (rawInterpret piLimit (Ctx.extension Γ hA) C).app _ (s.hom ≫ Ctx.extensionMap hA θ).op (ρs.push Y) at hbody
  have hover : s.hom ≫ Ctx.extensionMap hA θ =
      (σ ≫ RawCtx.toCtx.map θ) ≫ (Raw.ContextSection.ofTerm hA hb).hom := by
    change (σ ≫ (Raw.ContextSection.ofTerm hAθ
      (hb.subst θ.srcWF θ.typed)).hom) ≫ Ctx.extensionMap hA θ = _
    rw [Category.assoc, ofTerm_subst_hom, ← Category.assoc]
  rw [hover] at hbody
  change (rawInterpret piLimit Γ₁ (.tr (A.subst θ.subst) (a.subst θ.subst)
    (b.subst θ.subst) (C.subst θ.subst.lift) (x.subst θ.subst) (h.subst θ.subst))).app _ σ.op ρt = _
  rw [rawInterpret_tr piLimit hA hb,
    rawInterpret_tr piLimit hAθ (hb.subst θ.srcWF θ.typed),
    RawFamily.decode_app_hom_coe, RawFamily.decode_app_hom_coe,
    RawFamily.instantiate_value, RawFamily.instantiate_value,
    hbs θ σ ρs ρt hθ hρ, hxs θ σ ρs ρt hθ hρ]
  exact congrArg (fun T ↦ piLimit.rawExtend T
    ((rawInterpret piLimit Γ x).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs)) hbody

end DomainSemantics.CoherentShape
