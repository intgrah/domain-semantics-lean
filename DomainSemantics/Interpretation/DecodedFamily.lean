/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Family
public import DomainSemantics.Domain.Decoder.CodeExtension

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

namespace RawFamily

variable {Γ Γ₁ : Ctx}
variable (D : CodeAssignment)

noncomputable def decode (C X : RawFamily Γ) : RawFamily Γ :=
  (C.pair X).comp (.ofNatTrans D.rawExtendHom)

@[simp] theorem decode_app_hom_coe (C X : RawFamily Γ) {Γ₁ : Ctxᵒᵖ}
    (σ : Opposite.op Γ ⟶ Γ₁) (ρ : RawValuation Γ₁.unop) :
    (decode D C X).app _ σ ρ = D.rawExtend (C.app _ σ ρ) (X.app _ σ ρ) := rfl

theorem IsFinitary.decode {C X : RawFamily Γ}
    (hC : C.IsFinitary) (hX : X.IsFinitary) : (decode D C X).IsFinitary := by
  intro Γ₁ σ i ρ
  exact ΩLower.IsFinitary.of_eventually fun I _ hy =>
    D.rawExtend_eventually (hC.eventually σ i ρ I) (hX.eventually σ i ρ I) hy

theorem pullback_decode (C X : RawFamily Γ) (σ : Γ₁ ⟶ Γ) :
    (decode D C X).pullback σ = decode D (C.pullback σ) (X.pullback σ) := rfl

end RawFamily

end DomainSemantics.CoherentShape
