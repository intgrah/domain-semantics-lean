/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages
public import DomainSemantics.Interpretation.Binder

@[expose] public section

namespace DomainSemantics.CoherentShape.RawFamily

open CategoryTheory CodeAssignment Presheaf

variable {Γ Γ₁ Γ₂ ΓA : Ctx}

theorem sectionValue_isDirected (hA : Display Tm.typing Γ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : RawValue Γ₁)
    (hB : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁)
      (s : hA.Section (σ₁ ≫ σ) (Tm.presheaf.map σ₁.op label)),
      (B.app _ s.hom.op ((ρ.pullback σ₁).push (I.pullback σ₁))).IsDirected) :
    (sectionValue hA B σ ρ label I).IsDirected :=
  (bodySection hA B σ ρ label I).isDirected hB

theorem normalizedSectionValue_isDirected (hA : Display Tm.typing Γ ΓA)
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : Domain Γ₁)
    (hC : (C.app _ σ.op ρ).IsDirected)
    (hB : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (s : hA.Section (σ₁ ≫ σ) name)
      (J : Domain Γ₂),
      piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) J.val = J.val →
      (B.app _ s.hom.op ((ρ.pullback σ₁).push J.val)).IsDirected) :
    (normalizedSectionValue piLimit hA C B σ ρ label I.val).IsDirected := by
  apply sectionValue_isDirected
  intro Γ₂ σ₁ s
  have hCτ : (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)).IsDirected := by
    rw [op_comp, ← C.app_pullback]
    exact hC.pullback σ₁
  rw [piLimit.pullback_rawExtend, C.app_pullback]
  exact fun _ => hB σ₁ (Tm.presheaf.map σ₁.op label) s
    ⟨_, piLimit.rawExtend_isDirected hCτ (I.pullback σ₁).property⟩
    (piLimit.rawExtend_idempotent piLimit_isIdempotent hCτ (I.pullback σ₁).property)

theorem normalizedBodyAction_isIdealValued (hA : Display Tm.typing Γ ΓA)
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (hC : (C.app _ σ.op ρ).IsDirected)
    (hB : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (s : hA.Section (σ₁ ≫ σ) name)
      (J : Domain Γ₂),
      piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) J.val = J.val →
      (B.app _ s.hom.op ((ρ.pullback σ₁).push J.val)).IsDirected) :
    (normalizedBodyAction piLimit hA C B σ ρ).IsIdealValued := by
  intro Γ₂ σ₁ label I
  have hCτ : (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)).IsDirected := by
    rw [op_comp, ← C.app_pullback]
    exact hC.pullback σ₁
  apply normalizedSectionValue_isDirected hA C B (σ₁ ≫ σ) (ρ.pullback σ₁) label I hCτ
  intro Γ₃ σ₂ name s J hfixed
  rw [RawValuation.pullback_comp] at hfixed ⊢
  have hB' := hB (σ₂ ≫ σ₁) name
  rw [Category.assoc] at hB'
  exact fun _ => hB' s J hfixed

end DomainSemantics.CoherentShape.RawFamily
