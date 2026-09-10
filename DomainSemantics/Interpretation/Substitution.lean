/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Family
public import DomainSemantics.Syntax.Comprehension

@[expose] public section

namespace DomainSemantics.CoherentShape.RawFamily

open CategoryTheory Presheaf

variable {Γ Γ₁ ΓA : Ctx}

theorem IsFinitary.head {F : RawFamily Γ} (hF : F.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    ΩLower.IsFinitary (fun I => F.app _ σ.op (ρ.push I)) := by
  simpa using hF σ 0 (ρ.push ⊥)

noncomputable def instantiate
    (B : RawFamily ΓA)
    (s : Γ ⟶ ΓA) (X : RawFamily Γ) : RawFamily Γ :=
  ((Functor.HomObj.id _).pair X).comp (.ofNatTrans RawValuation.pushHom) |>.comp (B.pullback s)

@[simp]
theorem instantiate_value
    (B : RawFamily ΓA)
    (s : Γ ⟶ ΓA) (X : RawFamily Γ)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (instantiate B s X).app _ σ.op ρ = B.app _ (σ ≫ s).op (ρ.push (X.app _ σ.op ρ)) := rfl

theorem IsFinitary.compose_value {Γ₂ : Ctx} {B : RawFamily Γ₂}
    (hB : B.IsFinitary) {X : RawFamily Γ} (hX : X.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (σ₁ : Γ₁ ⟶ Γ₂) (i : ℕ) (ρ : RawValuation Γ₁) :
    ΩLower.IsFinitary (fun I => B.app _ σ₁.op
      ((ρ.replace i I).push (X.app _ σ.op (ρ.replace i I)))) :=
  ΩLower.IsFinitary.apply
    (fun J => by simpa using hB σ₁ (i + 1) (ρ.push J))
    (fun J => hB.head σ₁ (ρ.replace i J)) (hX σ i ρ)
    (fun _ _ h J => (B.app _ σ₁.op).hom.monotone
      (RawValuation.push_mono (RawValuation.replace_mono i le_rfl h) (fun _ _ hx => hx)))
    (fun J _ _ h => (B.app _ σ₁.op).hom.monotone (RawValuation.push_mono le_rfl h))
    ((X.app _ σ.op).hom.monotone.comp (Function.update_mono (f := ρ)))

theorem IsFinitary.instantiate
    {B : RawFamily ΓA}
    (hB : B.IsFinitary) (s : Γ ⟶ ΓA)
    {X : RawFamily Γ} (hX : X.IsFinitary) :
    (instantiate B s X).IsFinitary :=
  fun _ σ i ρ I {_} => hB.compose_value hX σ (σ ≫ s) i ρ I

end DomainSemantics.CoherentShape.RawFamily
