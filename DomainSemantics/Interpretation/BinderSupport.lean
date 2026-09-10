/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Application
public import DomainSemantics.Domain.Decoder.PiStages
public import DomainSemantics.Interpretation.Binder
import DomainSemantics.Domain.Decoder.DecoderStrictness

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ Γ₂ ΓA : Ctx}

theorem RawAction.rawApplication_abstraction_eq_value (F : RawAction Γ)
    (hF : F.IsFinitary) (hD : F.IsIdealValued)
    (X : Domain Γ)
    (Q : Set (Σ A : Ty Γ, Tm Γ A)) (label : Σ A : Ty Γ, Tm Γ A) (hlabel : label ∈ Q)
    (hsupport : ∀ {Γ₁} (σ : Γ₁ ⟶ Γ) (label' : Σ A : Ty Γ₁, Tm Γ₁ A),
    label' ∈ Tm.presheaf.map σ.op '' Q →
    ∀ {x y : CoherentShape Γ₁},
    OutputAtom (F.abstraction.pullback σ) label' x y →
    y ≤ ⊥ ∨ label' = Tm.presheaf.map σ.op label) :
    rawApplication F.abstraction Q X.val = F.app _ ((𝟙 Γ).op, label) X.val := by
  ext Γ₁ σ y
  let label' := Tm.presheaf.map σ.op label
  let Y := F.app _ (σ.op, label') (X.pullback σ).val
  have hvalue : (F.app _ ((𝟙 Γ).op, label) X.val).mem σ y ↔ Y.mem (𝟙 Γ₁) y := by
    rw [← ΩLower.presheaf_map_mem_id, ← F.app_pullback, op_id, Category.id_comp]
    rfl
  rw [hvalue, mem_rawApplication]
  constructor
  · rintro (hbot | ⟨name, hname, u, x, hu, hx, x', hx', hy⟩)
    · exact Y.lower (𝟙 Γ₁) hbot (Y.bottom (𝟙 Γ₁))
    simp at hy
    apply hy.mem_of_outputAtom (hD σ label' (X.pullback σ))
    intro w hw'
    have hatom : OutputAtom (F.abstraction.pullback σ) (Tm.presheaf.map σ.op name) x' w :=
      hw'.mono_function (ΩLower.principal_le_iff.mpr (by simpa using hu))
    rcases hsupport σ _ ⟨name, hname, rfl⟩ hatom with hbottom | hname'
    · exact Y.lower (𝟙 Γ₁) hbottom (Y.bottom (𝟙 Γ₁))
    rw [hname'] at hatom
    exact (F.app _ (σ.op, label')).hom.monotone
      (ΩLower.principal_le_iff.mpr
        ((X.pullback σ).lower (𝟙 Γ₁) (by simpa using hx') (by simpa using hx)))
      (𝟙 Γ₁) w (BasisAction.mem_value_of_outputAtom hatom)
  · intro hy
    have ⟨x, hx, hy'⟩ := hF.exists_principal σ label' (X.pullback σ) hy
    have ⟨g, e, hg, hlab, hin, hout⟩ := BasisAction.outputAtom_of_mem_value (F := F.onBasis) hy'
    refine Or.inr ⟨label, hlabel, g.lamGenerator, x, by simpa using hg, by simpa using hx, ?_⟩
    exact OutputAtom.mem_application ⟨g, e, by simp, hlab, hin, hout⟩ (by simp)

namespace RawFamily

variable (D : CodeAssignment)

theorem rawExtend_sectionValue_support
    (hD : ∀ {Γ : Ctx}, D.app _ (⊥ : CoherentShape Γ) = IdealOperator.bottom)
    (hA : Display Tm.typing Γ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I X : RawValue Γ₁) {y : CoherentShape Γ₁}
    (hy : (D.rawExtend (sectionValue hA B σ ρ label I) X).mem (𝟙 Γ₁) y)
    (hne : ¬ y ≤ ⊥) : Nonempty (hA.Section σ label) := by
  have ⟨c, hc, hcne⟩ := D.rawExtend_nonbottom_code hD hy hne
  exact sectionValue_support hA B σ ρ label I hc hcne

theorem piLimit_rawExtend_sectionValue_support
    (hA : Display Tm.typing Γ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I X : RawValue Γ₁) {y : CoherentShape Γ₁}
    (hy : (CodeAssignment.piLimit.rawExtend
      (sectionValue hA B σ ρ label I) X).mem (𝟙 Γ₁) y)
    (hne : ¬ y ≤ ⊥) : Nonempty (hA.Section σ label) :=
  rawExtend_sectionValue_support CodeAssignment.piLimit
    CodeAssignment.piLimit_value_bottom hA B σ ρ label I X hy hne

theorem normalizedBodyAction_outputAtom_support
    (hA : Display Tm.typing Γ ΓA) (C : RawFamily Γ)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) {label : Σ A : Ty Γ₂, Tm Γ₂ A} {x y : CoherentShape Γ₂}
    (hy : OutputAtom
      ((normalizedBodyAction D hA C B σ ρ).abstraction.pullback σ₁) label x y)
    (hne : ¬ y ≤ ⊥) :
    Nonempty (hA.Section (σ₁ ≫ σ) label) :=
  sectionValue_support hA B (σ₁ ≫ σ) (ρ.pullback σ₁) label _
    (BasisAction.mem_value_of_outputAtom hy) hne

theorem rawApplication_normalizedAbstraction_eq_value
    (hA : Display Tm.typing Γ ΓA) (C : RawFamily Γ)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (hD : (normalizedBodyAction D hA C B σ ρ).IsIdealValued)
    (X : Domain Γ₁)
    (Q : Set (Σ A : Ty Γ₁, Tm Γ₁ A)) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (hlabel : label ∈ Q)
    (hsections : ∀ {Γ₂} (σ₁ : Γ₂ ⟶ Γ₁) (label' : Σ A : Ty Γ₂, Tm Γ₂ A),
      label' ∈ Tm.presheaf.map σ₁.op '' Q →
      Nonempty (hA.Section (σ₁ ≫ σ) label') →
      label' = Tm.presheaf.map σ₁.op label) :
    rawApplication (normalizedBodyAction D hA C B σ ρ).abstraction Q X.val =
      normalizedSectionValue D hA C B σ ρ label X.val := by
  have hcollapse := RawAction.rawApplication_abstraction_eq_value
    (normalizedBodyAction D hA C B σ ρ)
    (normalizedBodyAction_isFinitary D hA C hB σ ρ) hD X Q label hlabel (by
      intro Γ₂ σ₁ label' hlabel' x y hy
      by_cases hbottom : y ≤ ⊥
      · exact Or.inl hbottom
      · exact Or.inr (hsections σ₁ label' hlabel'
          (normalizedBodyAction_outputAtom_support D hA C B σ ρ σ₁ hy hbottom)))
  change _ = normalizedSectionValue D hA C B ((𝟙 _) ≫ σ) (ρ.pullback (𝟙 _)) label X.val at hcollapse
  simpa using hcollapse

end RawFamily

end DomainSemantics.CoherentShape
