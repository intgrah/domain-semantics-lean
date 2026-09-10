/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.FamilyApplication
public import DomainSemantics.Interpretation.Binder
import DomainSemantics.Interpretation.Abstraction
import DomainSemantics.Interpretation.BinderSupport

@[expose] public section

namespace DomainSemantics.CoherentShape.RawFamily

open CategoryTheory

variable {Γ₁ Γ₂ Γ₃ : Ctx} {A a : Term} {u : Bool}

theorem sourceQuery_eq_of_section (hA : Γ₁.as.terms ⊢ A : .sort u)
    (ha : Γ₁.as.terms ⊢ a : A) (σ₁ : Γ₂ ⟶ Γ₁) {label : Σ A : Ty Γ₂, Tm Γ₂ A}
    (hlabel : label ∈ Tm.presheaf.map σ₁.op '' sourceQuery Γ₁ a)
    (hs : Nonempty (Raw.ContextSection hA σ₁ label)) :
    label = Tm.presheaf.map σ₁.op (Tm.pairOfTyping Γ₁.as.wf hA ha) := by
  obtain ⟨_, ⟨A', u', hA', ha', rfl⟩, rfl⟩ := hlabel
  have ⟨s, hover, hgeneric⟩ := hs
  obtain ⟨σ₁, rfl⟩ := RawCtx.toCtx.map_surjective σ₁
  obtain ⟨σ₂, rfl⟩ := RawCtx.toCtx.map_surjective s
  have htail : Γ₂.as.terms ⊢ σ₂.subst.tail ≡ σ₁.subst ⊣ Γ₁.as.terms := by
    have htail' := (RawCtx.toCtx_map_eq_iff ((Ctx.projectionRaw Γ₁ hA).comp σ₂) σ₁).mp hover
    rwa [Ctx.projectionRaw_comp_subst] at htail'
  unfold Tm.rawBinderVar at hgeneric
  erw [Tm.map_ofTyping, Tm.map_ofTyping] at hgeneric
  have ⟨⟨v, htype⟩, _⟩ := Tm.pairOfTyping_eq_iff.mp hgeneric
  simp! [lift_subst] at htype
  erw [Tm.map_ofTyping, Tm.map_ofTyping]
  exact Tm.pairOfTyping_eq ⟨v, htype.symm.trans' (hA.subst Γ₂.as.wf htail)⟩
    (ha'.subst σ₁.srcWF σ₁.typed)

theorem reindex_ofTyping_mem_sourceQuery (hA : Γ₁.as.terms ⊢ A : .sort u)
    (ha : Γ₁.as.terms ⊢ a : A) (σ₁ : Γ₂ ⟶ Γ₁) :
    (Tm.presheaf.map σ₁.op (Tm.pairOfTyping Γ₁.as.wf hA ha)) ∈
      Tm.presheaf.map σ₁.op '' sourceQuery Γ₁ a :=
  ⟨Tm.pairOfTyping Γ₁.as.wf hA ha, ofTyping_mem_sourceQuery hA ha, rfl⟩

theorem sourceQuery_eq_of_section_reindex (hA : Γ₁.as.terms ⊢ A : .sort u)
    (ha : Γ₁.as.terms ⊢ a : A) (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂)
    {label : Σ A : Ty Γ₃, Tm Γ₃ A}
    (hlabel : label ∈ Tm.presheaf.map σ₂.op ''
      (Tm.presheaf.map σ₁.op '' sourceQuery Γ₁ a))
    (hs : Nonempty (Raw.ContextSection hA (σ₂ ≫ σ₁) label)) :
    label = Tm.presheaf.map σ₂.op
      (Tm.presheaf.map σ₁.op (Tm.pairOfTyping Γ₁.as.wf hA ha)) := by
  rw [← Functor.map_comp_apply, ← op_comp]
  apply sourceQuery_eq_of_section hA ha (σ₂ ≫ σ₁) _ hs
  simpa [Set.image_image] using hlabel

theorem rawApplication_eq_of_sections (hA : Γ₁.as.terms ⊢ A : .sort u)
    (ha : Γ₁.as.terms ⊢ a : A) (σ : Γ₂ ⟶ Γ₁) (F X : Domain Γ₂)
    (hsupport : ∀ {Γ₃ : Ctx} (τ : Γ₃ ⟶ Γ₂) (name : Σ A : Ty Γ₃, Tm Γ₃ A)
      {x y : CoherentShape Γ₃}, OutputAtom (F.pullback τ).val name x y →
        y ≤ ⊥ ∨ Nonempty (Raw.ContextSection hA (τ ≫ σ) name)) :
    rawApplication F.val (Tm.presheaf.map σ.op '' sourceQuery Γ₁ a) X.val =
      (CoherentShape.application F (Tm.presheaf.map σ.op (Tm.pairOfTyping Γ₁.as.wf hA ha)) X).val :=
  rawApplication_eq_of_support F X _ (reindex_ofTyping_mem_sourceQuery hA ha σ)
    fun {_} τ name hname _ _ hy => (hsupport τ name hy).imp_right
      (sourceQuery_eq_of_section_reindex hA ha σ τ hname)

theorem rawApplication_sourceQuery_abstraction_eq_value (D : CodeAssignment)
    (hA : Γ₁.as.terms ⊢ A : .sort u) (ha : Γ₁.as.terms ⊢ a : A)
    (C : RawFamily Γ₁) {B : RawFamily (Ctx.extension Γ₁ hA)} (hB : B.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hD : (normalizedBodyAction D (Ctx.rawDisplay hA) C B σ₁ ρ).IsIdealValued)
    (X : Domain Γ₂) :
    rawApplication (normalizedBodyAction D (Ctx.rawDisplay hA) C B σ₁ ρ).abstraction
        (Tm.presheaf.map σ₁.op '' sourceQuery Γ₁ a) X.val =
      normalizedSectionValue D (Ctx.rawDisplay hA) C B σ₁ ρ
        (Tm.presheaf.map σ₁.op (Tm.pairOfTyping Γ₁.as.wf hA ha)) X.val := by
  apply rawApplication_normalizedAbstraction_eq_value D (Ctx.rawDisplay hA) C hB σ₁ ρ hD X
    _ _ (reindex_ofTyping_mem_sourceQuery hA ha σ₁)
  intro Γ₃ σ₂ label hlabel hs
  exact sourceQuery_eq_of_section_reindex hA ha σ₁ σ₂ hlabel hs

theorem rawApplication_sourceQuery_abstraction_eq_body (D : CodeAssignment)
    (hA : Γ₁.as.terms ⊢ A : .sort u) (ha : Γ₁.as.terms ⊢ a : A)
    (C : RawFamily Γ₁) {B : RawFamily (Ctx.extension Γ₁ hA)} (hB : B.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hD : (normalizedBodyAction D (Ctx.rawDisplay hA) C B σ₁ ρ).IsIdealValued)
    (X : Domain Γ₂) :
    rawApplication (normalizedBodyAction D (Ctx.rawDisplay hA) C B σ₁ ρ).abstraction
        (Tm.presheaf.map σ₁.op '' sourceQuery Γ₁ a) X.val =
      B.app _ ((Raw.ContextSection.ofTerm hA ha).pullbackId σ₁).hom.op
        (ρ.push (D.rawExtend (C.app _ σ₁.op ρ) X.val)) := by
  rw [rawApplication_sourceQuery_abstraction_eq_value D hA ha C hB σ₁ ρ hD X]
  exact normalizedSectionValue_eq_value D (Ctx.rawDisplay hA) C B σ₁ ρ _ X.val
    ((Raw.ContextSection.ofTerm hA ha).pullbackId σ₁)

end DomainSemantics.CoherentShape.RawFamily
