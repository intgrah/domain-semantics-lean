/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Action
public import DomainSemantics.Presheaf.Partial
public import DomainSemantics.Domain.Decoder.CodeExtension
public import DomainSemantics.Interpretation.Family
public import DomainSemantics.Syntax.Comprehension
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Subfunctor.Image
import DomainSemantics.Interpretation.DecodedFamily
import DomainSemantics.Interpretation.Substitution
import Mathlib.Order.Filter.Basic

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Opposite MonoidalCategory Presheaf

abbrev RawActionFamily (Γ : Ctx) :=
  (RawValuation.presheaf.functorHom RawAction.presheaf).obj (op Γ)

variable {Γ Γ₁ Γ₂ ΓA : Ctx} (D : CodeAssignment)

namespace RawFamily

def sectionDomain (hA : Display Tm.typing Γ ΓA)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) : PartialDomain Γ₁ where
  Witness τ := hA.Section (τ ≫ σ) (Tm.presheaf.map τ.op label)
  pullback s τ := {
    hom := τ ≫ s.hom
    over := by simp [s.over]
    generic := by simp [Tm.presheaf, s.generic] }

noncomputable def bodySection (hA : Display Tm.typing Γ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : RawValue Γ₁) : PartialSection pointedOrder (sectionDomain hA σ label) where
  value τ s := B.app _ s.hom.op ((ρ.pullback τ).push (I.pullback τ))
  natural τ υ s t := by
    rw [B.app_pullback, RawValuation.pullback_push, RawValuation.pullback_comp,
      ΩLower.pullback_pullback]
    have h := Presheaf.Section.hom_eq ((sectionDomain hA σ label).pullback s υ) t
    change υ ≫ s.hom = t.hom at h
    rw [← op_comp, h]

noncomputable def sectionValue (hA : Display Tm.typing Γ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : RawValue Γ₁) : RawValue Γ₁ :=
  (bodySection hA B σ ρ label I).extend

@[simp] theorem mem_sectionValue {Γ₁ Γ₂ Γ₄ : Ctx}
    (hA : Display Tm.typing Γ₂ ΓA) (B : RawFamily ΓA)
    (σ₁ : Γ₁ ⟶ Γ₂) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : RawValue Γ₁) (σ₂ : Γ₄ ⟶ Γ₁) (y : CoherentShape Γ₄) :
    (sectionValue hA B σ₁ ρ label I).mem σ₂ y ↔ y ≤ ⊥ ∨
      ∃ s : hA.Section (σ₂ ≫ σ₁) (Tm.presheaf.map σ₂.op label),
        (B.app _ s.hom.op ((ρ.pullback σ₂).push (I.pullback σ₂))).mem (𝟙 Γ₄) y :=
  Iff.rfl

theorem sectionValue_eq_value (hA : Display Tm.typing Γ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : RawValue Γ₁) (s : hA.Section σ label) :
    sectionValue hA B σ ρ label I = B.app _ s.hom.op (ρ.push I) := by
  let s' : (sectionDomain hA σ label).Witness (𝟙 Γ₁) := {
    hom := s.hom
    over := by simpa using s.over
    generic := by simpa using s.generic }
  simpa [sectionValue, bodySection, s'] using
    (bodySection hA B σ ρ label I).pullback_extend (𝟙 Γ₁) s'

noncomputable def bodyHom (hA : Display Tm.typing Γ ΓA) (B : RawFamily ΓA) :
    Functor.HomObj (RawValuation.presheaf ⊗ ΩLower.presheaf pointedOrder)
      (ΩLower.presheaf pointedOrder) (coyoneda.obj (op (op Γ)) ⊗ Tm.presheaf) where
  app _ := fun (σ, label) => Preord.ofHom {
    toFun := fun (ρ, I) => sectionValue hA B σ.unop ρ label I
    monotone' := by
      rintro ⟨ρ, I⟩ ⟨ρ', I'⟩ ⟨hρ, hI⟩
      apply PartialSection.extend_mono
      intro Γ₂ τ s
      exact (B.app _ s.hom.op).hom.monotone
        (RawValuation.push_mono (RawValuation.pullback_mono hρ τ)
          (ΩLower.pullback_mono hI τ)) }
  naturality := by
    rintro ⟨Γ₁⟩ ⟨Γ₂⟩ ⟨σ₁⟩ ⟨⟨σ⟩, label⟩
    apply Preord.ext
    rintro ⟨ρ, I⟩
    change (_ : RawValue Γ₂) = _
    ext Γ₃ σ₂ (y : CoherentShape Γ₃)
    change (sectionValue hA B (σ₁ ≫ σ) (ρ.pullback σ₁)
      (Tm.presheaf.map σ₁.op label) (I.pullback σ₁)).mem σ₂ y ↔
        ((sectionValue hA B σ ρ label I).pullback σ₁).mem σ₂ y
    rw [ΩLower.presheaf_map_mem, mem_sectionValue, mem_sectionValue,
      Category.assoc, op_comp, Functor.map_comp_apply,
      RawValuation.pullback_comp, ΩLower.pullback_pullback]

theorem sectionValue_finitary (hA : Display Tm.typing Γ ΓA)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) :
    ΩLower.IsFinitary (sectionValue hA B σ ρ label) := by
  intro I y hy
  simp_rw [mem_sectionValue] at hy ⊢
  rcases hy with hy | ⟨s, hy⟩
  · exact ⟨∅, by simp, Or.inl hy⟩
  · simp at hy
    have ⟨l, hl, hy⟩ := hB.head s.hom ρ I hy
    refine ⟨l, hl, Or.inr ⟨s, ?_⟩⟩
    simp
    exact hy

theorem sectionValue_support (hA : Display Tm.typing Γ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : RawValue Γ₁) {y : CoherentShape Γ₁}
    (hy : (sectionValue hA B σ ρ label I).mem (𝟙 Γ₁) y)
    (hne : ¬ y ≤ ⊥) :
    Nonempty (hA.Section σ label) := by
  simpa [sectionDomain] using (bodySection hA B σ ρ label I).support hy hne

end RawFamily

namespace RawActionFamily

noncomputable def normalizedBody (D : CodeAssignment)
    (hA : Display Tm.typing Γ ΓA) (C : RawFamily Γ) (B : RawFamily ΓA) : RawActionFamily Γ :=
  let f : Functor.HomObj (RawValuation.presheaf ⊗ ΩLower.presheaf pointedOrder)
      (ΩLower.presheaf pointedOrder) (coyoneda.obj (op (op Γ)) ⊗ Tm.presheaf) :=
    ((Functor.HomObj.fst.pair
      (((Functor.HomObj.fst.comp C).pair .snd).comp (.ofNatTrans D.rawExtendHom))).map
        { app _ := ↾Prod.fst }).comp (RawFamily.bodyHom hA B)
  let p : RawAction.arguments ⊗ ((RawValuation.presheaf ⋙ forget Preord) ⊗ coyoneda.obj (op (op Γ))) ⟶
      (ΩLower.presheaf pointedOrder ⋙ forget Preord) :=
    { app _ := ↾fun ((label, I), ρ, σ) => ((ρ, I), σ, label) } ≫
      Functor.homObjEquiv _ _ _ f.toTypes
  let q := Subfunctor.lift (MonoidalClosed.curry p) (by
    rintro X _ ⟨⟨ρ, σ⟩, rfl⟩ Y τ label
    exact (f.app Y (σ ≫ τ, label)).hom.monotone.comp
      ((monotone_const (β := RawValuation Y.unop)).prodMk (β := RawValue Y.unop) monotone_id))
  ((Functor.homObjEquiv _ _ _).symm q).ofTypes (by
    intro X σ ρ ρ' h Y ⟨τ, label⟩ I
    exact (f.app Y (σ ≫ τ, label)).hom.monotone
      (a := (ρ.pullback τ.unop, I)) (b := (ρ'.pullback τ.unop, I))
      ⟨RawValuation.pullback_mono h τ.unop, by rfl⟩)

end RawActionFamily

namespace RawFamily

noncomputable def normalizedSectionValue (hA : Display Tm.typing Γ ΓA)
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : RawValue Γ₁) : RawValue Γ₁ :=
  sectionValue hA B σ ρ label (D.rawExtend (C.app _ σ.op ρ) I)

noncomputable def normalizedBodyAction (hA : Display Tm.typing Γ ΓA)
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) : RawAction Γ₁ :=
  (RawActionFamily.normalizedBody D hA C B).app _ σ.op ρ

theorem normalizedSectionValue_finitary_valuation
    (hA : Display Tm.typing Γ ΓA)
    {C : RawFamily Γ} (hC : C.IsFinitary)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (i : ℕ) (ρ : RawValuation Γ₁) (J : RawValue Γ₁)
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) :
    ΩLower.IsFinitary (fun I => normalizedSectionValue D hA C B σ (ρ.replace i I) label J) := by
  intro I y hy
  simp_rw [normalizedSectionValue, mem_sectionValue] at hy ⊢
  rcases hy with hy | ⟨s, hy⟩
  · exact ⟨∅, by simp, Or.inl hy⟩
  · simp at hy
    let X : RawFamily Γ₁ := decode D (C.pullback σ) (constant J)
    have hX : X.IsFinitary :=
      IsFinitary.decode D (IsFinitary.pullback hC σ) (constant_isFinitary J)
    have hxy : (B.app _ s.hom.op
        ((ρ.replace i I).push (X.app _ (𝟙 Γ₁).op (ρ.replace i I)))).mem (𝟙 Γ₁) y := by
      dsimp only [X]
      rw [decode_app_hom_coe, constant_app_hom_coe, RawFamily.pullback, Functor.functorHom_map_app]
      simpa using hy
    have ⟨l, hl, hy⟩ := hB.compose_value hX (𝟙 Γ₁) s.hom i ρ I hxy
    refine ⟨l, hl, Or.inr ⟨s, ?_⟩⟩
    dsimp only [X] at hy
    rw [decode_app_hom_coe, constant_app_hom_coe, RawFamily.pullback, Functor.functorHom_map_app] at hy
    simpa using hy

theorem normalizedSectionValue_finitary
    (hA : Display Tm.typing Γ ΓA) (C : RawFamily Γ)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) :
    ΩLower.IsFinitary (normalizedSectionValue D hA C B σ ρ label) :=
  ΩLower.IsFinitary.comp (sectionValue_finitary hA hB σ ρ label)
    (.of_eventually fun _ _ h => D.rawExtend_eventually
      (fun {_} hc => Filter.Eventually.of_forall fun _ => hc) ΩLower.eventually_mem h)
    (((bodyHom hA B).app _ (σ.op, label)).hom.monotone.comp
      (monotone_const.prodMk monotone_id))
    (fun _ _ h => D.rawExtend_mono_right h)

theorem normalizedBodyAction_isFinitary
    (hA : Display Tm.typing Γ ΓA) (C : RawFamily Γ)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (normalizedBodyAction D hA C B σ ρ).IsFinitary :=
  fun σ₁ => normalizedSectionValue_finitary D hA C hB (σ₁ ≫ σ) (ρ.pullback σ₁)

end RawFamily

end DomainSemantics.CoherentShape
