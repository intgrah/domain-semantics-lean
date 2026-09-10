/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages
public import DomainSemantics.Interpretation
import DomainSemantics.Interpretation.PiSupport
import DomainSemantics.Interpretation.SourceQuery
import DomainSemantics.Interpretation.Witnesses
import DomainSemantics.Syntax.Comprehension.Pullback

@[expose] public section

namespace DomainSemantics.CoherentShape.RawFamily

open CategoryTheory CodeAssignment

variable {Γ Γ₁ Γ₂ Γ₃ : Ctx} {A a : Term} {u : Bool}

theorem reindex_ofTyping_subst (hA : Γ.as.terms ⊢ A : .sort u)
    (ha : Γ.as.terms ⊢ a : A) (θ : Γ₁.as ⟶ Γ.as) (σ : Γ₂ ⟶ Γ₁) :
    Tm.presheaf.map σ.op
        (Tm.pairOfTyping Γ₁.as.wf (hA.subst θ.srcWF θ.typed) (ha.subst θ.srcWF θ.typed)) =
      Tm.presheaf.map (σ ≫ RawCtx.toCtx.map θ).op
        (Tm.pairOfTyping Γ.as.wf hA ha) := by
  simp
  exact congrArg (Tm.presheaf.map σ.op) (Tm.map_ofTyping hA ha θ).symm

theorem rawApplication_subst_query_eq (hA : Γ.as.terms ⊢ A : .sort u)
    (ha : Γ.as.terms ⊢ a : A) (θ : Γ₁.as ⟶ Γ.as) (σ : Γ₂ ⟶ Γ₁)
    (F X : Domain Γ₂)
    (hsupport : ∀ {Γ₃ : Ctx} (σ₁ : Γ₃ ⟶ Γ₂) (name : Σ A : Ty Γ₃, Tm Γ₃ A)
      {x y : CoherentShape Γ₃}, OutputAtom (F.pullback σ₁).val name x y →
        y ≤ ⊥ ∨
          Nonempty (Raw.ContextSection hA (σ₁ ≫ (σ ≫ RawCtx.toCtx.map θ)) name)) :
    rawApplication F.val
        (Tm.presheaf.map σ.op '' sourceQuery Γ₁ (a.subst θ.subst)) X.val =
      rawApplication F.val
        (Tm.presheaf.map (σ ≫ RawCtx.toCtx.map θ).op '' sourceQuery Γ a)
        X.val := by
  have htarget := rawApplication_eq_of_sections (hA.subst θ.srcWF θ.typed)
    (ha.subst θ.srcWF θ.typed) σ F X (fun τ name _ _ hy =>
      (hsupport τ name hy).imp_right fun ⟨s⟩ =>
        ⟨Raw.ContextSection.cartesianLift hA θ (by simpa using s)⟩)
  rw [reindex_ofTyping_subst hA ha θ σ] at htarget
  exact htarget.trans (rawApplication_eq_of_sections hA ha
    (σ ≫ RawCtx.toCtx.map θ) F X hsupport).symm

theorem outputAtom_rawPi_fixed_bot_or_section (hA : Γ.as.terms ⊢ A : .sort u)
    (label : Σ A : Ty Γ, Ty (Γ.extend A)) (C : RawFamily Γ)
    {B : RawFamily (Ctx.extension Γ hA)} (hB : B.IsFinitary)
    (χ : Γ₂ ⟶ Γ) (ρ : RawValuation Γ₂) (hC : (C.app _ χ.op ρ).IsDirected)
    (hD : (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B χ ρ).IsIdealValued)
    {F : Domain Γ₂}
    (hF : piLimit.rawExtend ((pi piLimit (Ctx.rawDisplay hA) label C B).app _ χ.op ρ) F.val = F.val)
    (σ₁ : Γ₃ ⟶ Γ₂) {name : Σ A : Ty Γ₃, Tm Γ₃ A} {x y : CoherentShape Γ₃}
    (hy : OutputAtom (F.pullback σ₁).val name x y) :
    y ≤ ⊥ ∨ Nonempty (Raw.ContextSection hA (σ₁ ≫ χ) name) := by
  by_cases hbottom : y ≤ ⊥
  · exact Or.inl hbottom
  · exact Or.inr (outputAtom_rawPi_fixed_support hA label C hB χ ρ hC hD hF σ₁ hy hbottom)

theorem rawApplication_subst_query_rawPi_fixed (hA : Γ.as.terms ⊢ A : .sort u)
    (ha : Γ.as.terms ⊢ a : A) (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (C : RawFamily Γ) {B : RawFamily (Ctx.extension Γ hA)} (hB : B.IsFinitary)
    (θ : Γ₁.as ⟶ Γ.as) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hC : (C.app _ (σ ≫ RawCtx.toCtx.map θ).op ρ).IsDirected)
    (hD : (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B (σ ≫ RawCtx.toCtx.map θ) ρ).IsIdealValued)
    {F : Domain Γ₂}
    (hF : piLimit.rawExtend
      ((pi piLimit (Ctx.rawDisplay hA) label C B).app _ (σ ≫ RawCtx.toCtx.map θ).op ρ) F.val = F.val)
    (X : Domain Γ₂) :
    rawApplication F.val
        (Tm.presheaf.map σ.op '' sourceQuery Γ₁ (a.subst θ.subst)) X.val =
      rawApplication F.val
        (Tm.presheaf.map (σ ≫ RawCtx.toCtx.map θ).op '' sourceQuery Γ a)
        X.val :=
  rawApplication_subst_query_eq hA ha θ σ F X (fun σ₁ _ _ _ hy =>
    outputAtom_rawPi_fixed_bot_or_section hA label C hB (σ ≫ RawCtx.toCtx.map θ) ρ hC hD hF σ₁ hy)

end DomainSemantics.CoherentShape.RawFamily

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

variable {Γ Γ₁ Γ₂ : Ctx} {A B f a : Term} {u v : Bool}

theorem rawInterpret_app_subst (hA : Γ.as.terms ⊢ A : .sort u)
    (hB : A :: Γ.as.terms ⊢ B : .sort v) (ha : Γ.as.terms ⊢ a : A)
    (θ : Γ₁.as ⟶ Γ.as) (σ : Γ₂ ⟶ Γ₁) (ρs ρt : RawValuation Γ₂)
    (hC : ((rawInterpret piLimit Γ A).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs).IsDirected)
    (hD : (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) (rawInterpret piLimit Γ A)
      (rawInterpret piLimit (Ctx.extension Γ hA) B)
      (σ ≫ RawCtx.toCtx.map θ) ρs).IsIdealValued)
    (hFideal : ((rawInterpret piLimit Γ f).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs).IsDirected)
    (hXideal : ((rawInterpret piLimit Γ a).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs).IsDirected)
    (hFfixed : piLimit.rawExtend
      ((rawInterpret piLimit Γ (.forallE A B)).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs)
      ((rawInterpret piLimit Γ f).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs) =
      (rawInterpret piLimit Γ f).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs)
    (ihf : (rawInterpret piLimit Γ₁ (f.subst θ.subst)).app _ σ.op ρt =
      (rawInterpret piLimit Γ f).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs)
    (iha : (rawInterpret piLimit Γ₁ (a.subst θ.subst)).app _ σ.op ρt =
      (rawInterpret piLimit Γ a).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs) :
    (rawInterpret piLimit Γ₁ ((Term.app f a).subst θ.subst)).app _ σ.op ρt =
      (rawInterpret piLimit Γ (.app f a)).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs := by
  let F : Domain Γ₂ :=
    ((rawInterpret piLimit Γ f).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs).toIdeal hFideal
  let X : Domain Γ₂ :=
    ((rawInterpret piLimit Γ a).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs).toIdeal hXideal
  have hfixed : piLimit.rawExtend
      ((RawFamily.pi piLimit (Ctx.rawDisplay hA) (Ty.pairOfTyping Γ.as.wf hA hB)
        (rawInterpret piLimit Γ A) (rawInterpret piLimit (Ctx.extension Γ hA) B)).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs) F.val = F.val := by
    rw [rawInterpret_forallE piLimit hA hB] at hFfixed
    exact hFfixed
  change rawApplication ((rawInterpret piLimit Γ₁ (f.subst θ.subst)).app _ σ.op ρt)
      (Tm.presheaf.map σ.op '' RawFamily.sourceQuery Γ₁ (a.subst θ.subst))
      ((rawInterpret piLimit Γ₁ (a.subst θ.subst)).app _ σ.op ρt) =
    rawApplication ((rawInterpret piLimit Γ f).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs)
      (Tm.presheaf.map (σ ≫ RawCtx.toCtx.map θ).op '' RawFamily.sourceQuery Γ a)
      ((rawInterpret piLimit Γ a).app _ (σ ≫ RawCtx.toCtx.map θ).op ρs)
  rw [ihf, iha]
  exact RawFamily.rawApplication_subst_query_rawPi_fixed hA ha _ (rawInterpret piLimit Γ A)
    (rawInterpret_isFinitary piLimit (Ctx.extension Γ hA) B) θ σ ρs hC hD hfixed X

end DomainSemantics.CoherentShape
