/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.ActionFamily

@[expose] public section

namespace DomainSemantics.CoherentShape.RawFamily

open CategoryTheory Presheaf

variable {Γ Γ₁ Γ₂ ΓA : Ctx}
variable (D : CodeAssignment)

theorem normalizedSectionValue_eq_value
    (hA : Display Tm.typing Γ ΓA) (C : RawFamily Γ)
    (B : RawFamily ΓA) (σ : Γ₁ ⟶ Γ)
    (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : RawValue Γ₁)
    (s : hA.Section σ label) :
    normalizedSectionValue D hA C B σ ρ label I =
      B.app _ s.hom.op (ρ.push (D.rawExtend (C.app _ σ.op ρ) I)) :=
  sectionValue_eq_value hA B σ ρ label (D.rawExtend (C.app _ σ.op ρ) I) s

noncomputable def abstraction (hA : Display Tm.typing Γ ΓA)
    (C : RawFamily Γ) (B : RawFamily ΓA) : RawFamily Γ :=
  (RawActionFamily.normalizedBody D hA C B).comp (.ofNatTrans RawAction.abstractionHom)

@[simp]
theorem abstraction_value (hA : Display Tm.typing Γ ΓA)
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (abstraction D hA C B).app _ σ.op ρ =
      (normalizedBodyAction D hA C B σ ρ).abstraction := rfl

theorem IsFinitary.abstraction (hA : Display Tm.typing Γ ΓA)
    {C : RawFamily Γ} (hC : C.IsFinitary)
    {B : RawFamily ΓA} (hB : B.IsFinitary) :
    (abstraction D hA C B).IsFinitary := by
  intro Γ₁ σ i ρ
  apply ΩLower.IsFinitary.of_eventually
  intro I y hy
  have ⟨f, hf, hyf⟩ := RawAction.abstraction_mem.mp hy
  filter_upwards
    [RawActionFamily.IsFinitary.graph_eventually
      (RawActionFamily.IsFinitary.normalizedBody D hA hC hB) σ i ρ I f hf]
    with J hf
  exact RawAction.abstraction_mem.mpr ⟨f, hf, hyf⟩

end DomainSemantics.CoherentShape.RawFamily
