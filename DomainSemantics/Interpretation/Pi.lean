/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Pi
public import DomainSemantics.Interpretation.ActionFamily

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory MonoidalCategory Presheaf

variable {Γ Γ₁ Γ₂ ΓA : Ctx}
variable (D : CodeAssignment)

noncomputable abbrev rawPi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : RawValue Γ) (B : RawAction Γ) : RawValue Γ :=
  BasisAction.pi label A B.onBasis

theorem pullback_rawPi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : RawValue Γ)
    (B : RawAction Γ) (σ : Γ₁ ⟶ Γ) :
    (rawPi label A B).pullback σ =
      rawPi (Ty.pairPresheaf.map σ.op label) (A.pullback σ) (B.pullback σ) :=
  BasisAction.pullback_pi label A B.onBasis σ

@[simp]
theorem mem_piAtom_rawPi_iff (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (A : RawValue Γ) (B : RawAction Γ) (σ : Γ₁ ⟶ Γ) (label' : Σ A : Ty Γ₁, Ty (Γ₁.extend A)) :
    (rawPi label A B).mem σ (piAtom label') ↔
      label' = Ty.pairPresheaf.map σ.op label :=
  BasisAction.mem_piAtom_pi_iff label A B.onBasis σ label'

theorem rawPi_toIdealAction (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (A : Domain Γ) (B : RawAction Γ)
    (hB : B.IsFinitary) (hD : B.IsIdealValued) :
    rawPi label A.val B = (pi label A (B.toIdealAction hB hD)).val :=
  rfl

theorem rawPi_isDirected (label : Σ A : Ty Γ, Ty (Γ.extend A)) {A : RawValue Γ}
    (B : RawAction Γ) (hA : A.IsDirected) (hD : B.IsIdealValued) :
    (rawPi label A B).IsDirected :=
  BasisAction.pi_isDirected label A B.onBasis hA
    (fun σ label x => hD σ label (principalIdeal x))

noncomputable def rawPiHom : Functor.HomObj (ΩLower.presheaf pointedOrder ⊗ RawAction.presheaf)
    (ΩLower.presheaf pointedOrder) Ty.pairPresheaf where
  app _ label := Preord.ofHom {
    toFun := fun (A, B) => rawPi label A B
    monotone' := fun _ _ ⟨hA, hB⟩ {_} σ _ ⟨a, f, ha, hf, hq⟩ =>
      ⟨a, f, hA σ a ha, RawAction.GraphValid.mono hB hf, hq⟩ }
  naturality σ label := Preord.ext fun (A, B) => (pullback_rawPi label A B σ.unop).symm

namespace RawFamily

noncomputable def pi
    (hA : Display Tm.typing Γ ΓA) (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (C : RawFamily Γ) (B : RawFamily ΓA) : RawFamily Γ :=
  (C.pair (RawActionFamily.normalizedBody D hA C B)).comp
    (rawPiHom.map (coyonedaEquiv.symm label))

@[simp]
theorem pi_value
    (hA : Display Tm.typing Γ ΓA) (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (pi D hA label C B).app _ σ.op ρ =
      rawPi (Ty.pairPresheaf.map σ.op label) (C.app _ σ.op ρ)
        (normalizedBodyAction D hA C B σ ρ) := rfl

theorem IsFinitary.pi
    (hA : Display Tm.typing Γ ΓA) (label : Σ A : Ty Γ, Ty (Γ.extend A))
    {C : RawFamily Γ} (hC : C.IsFinitary)
    {B : RawFamily ΓA} (hB : B.IsFinitary) :
    (pi D hA label C B).IsFinitary := by
  intro Γ₁ σ i ρ
  apply ΩLower.IsFinitary.of_eventually
  intro I q hq
  have ⟨a, f, ha, hf, hq⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hq
  filter_upwards [hC.eventually σ i ρ I ha,
    RawActionFamily.IsFinitary.graph_eventually
      (RawActionFamily.IsFinitary.normalizedBody D hA hC hB) σ i ρ I f hf]
    with J ha hf
  exact (BasisAction.mem_pi _ _ _ _ _).mpr ⟨a, f, ha, hf, hq⟩

@[simp]
theorem mem_piAtom_pi_value_iff
    (hA : Display Tm.typing Γ ΓA) (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) (label' : Σ A : Ty Γ₂, Ty (Γ₂.extend A)) :
    ((pi D hA label C B).app _ σ.op ρ).mem σ₁ (piAtom label') ↔
      label' = Ty.pairPresheaf.map (σ₁ ≫ σ).op label := by
  rw [pi_value, mem_piAtom_rawPi_iff, op_comp, Functor.map_comp_apply]

end RawFamily

end DomainSemantics.CoherentShape
