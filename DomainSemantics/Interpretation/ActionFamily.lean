/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Binder
import Mathlib.Order.Filter.Finite

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Opposite Presheaf

variable {Γ Γ₁ Γ₂ ΓA : Ctx}

namespace RawActionFamily

noncomputable abbrev presheaf := RawValuation.presheaf.functorHom RawAction.presheaf

def IsFinitary (F : RawActionFamily Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (i : ℕ) (ρ : RawValuation Γ₁)
    (X : RawValue Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A),
    ΩLower.IsFinitary (fun I => (F.app _ σ.op (ρ.replace i I)).app _ ((𝟙 Γ₁).op, label) X)

theorem IsFinitary.eventually {F : RawActionFamily Γ} (hF : F.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (i : ℕ) (ρ : RawValuation Γ₁) (I X : RawValue Γ₁)
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) {y : CoherentShape Γ₁}
    (hy : ((F.app _ σ.op (ρ.replace i I)).app _ ((𝟙 Γ₁).op, label) X).mem (𝟙 Γ₁) y) :
    ∀ᶠ J in I.approximations,
      ((F.app _ σ.op (ρ.replace i J)).app _ ((𝟙 Γ₁).op, label) X).mem (𝟙 Γ₁) y :=
  (hF σ i ρ X label).eventually
    (fun _ _ h => (F.app _ σ.op).hom.monotone
      (RawValuation.replace_mono i le_rfl h) _ ((𝟙 Γ₁).op, label) X)
    ΩLower.eventually_mem hy

theorem IsFinitary.graph_eventually {F : RawActionFamily Γ} (hF : F.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (i : ℕ) (ρ : RawValuation Γ₁) (I : RawValue Γ₁)
    (f : CoherentGraph Γ₁)
    (hf : RawAction.GraphValid (F.app _ σ.op (ρ.replace i I)) (𝟙 Γ₁) f) :
    ∀ᶠ J in I.approximations,
      RawAction.GraphValid (F.app _ σ.op (ρ.replace i J)) (𝟙 Γ₁) f :=
  Filter.eventually_all.mpr fun j => hF.eventually σ i ρ I _ _ (hf j)

theorem IsFinitary.normalizedBody (D : CodeAssignment)
    (hA : Display Tm.typing Γ ΓA) {C : RawFamily Γ} (hC : C.IsFinitary)
    {B : RawFamily ΓA} (hB : B.IsFinitary) :
    (normalizedBody D hA C B).IsFinitary := by
  intro Γ₁ σ i ρ X label
  change ΩLower.IsFinitary (fun I => RawFamily.normalizedSectionValue D hA C B
    ((𝟙 _) ≫ σ) ((ρ.replace i I).pullback (𝟙 _)) label X)
  simpa using RawFamily.normalizedSectionValue_finitary_valuation D hA hC hB σ i ρ X label

noncomputable def apply (F : RawActionFamily Γ) (X : RawFamily Γ) (label : Σ A : Ty Γ, Tm Γ A) :
    RawFamily Γ :=
  let p := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.snd _ _ ≫ coyonedaEquiv.symm label)
      (Functor.homObjEquiv _ _ _ X.toTypes))
    (Functor.homObjEquiv _ _ _ F.toTypes)
  ((Functor.homObjEquiv _ _ _).symm (p ≫ MonoidalClosed.uncurry RawAction.monotone.ι)).ofTypes
    fun Y σ _ _ h =>
      OrderHom.apply_mono ((F.app Y σ).hom.monotone h Y (𝟙 Y, Tm.presheaf.map σ label))
        ((X.app Y σ).hom.monotone h)

theorem IsFinitary.apply {F : RawActionFamily Γ} (hF : F.IsFinitary)
    (hArg : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁),
      RawAction.IsFinitary (F.app _ σ.op ρ))
    {X : RawFamily Γ} (hX : X.IsFinitary) (label : Σ A : Ty Γ, Tm Γ A) :
    (F.apply X label).IsFinitary :=
  fun {Γ₁} σ i ρ => ΩLower.IsFinitary.apply
    (fun J => hF σ i ρ J (Tm.presheaf.map σ.op label))
    (fun I => hArg σ (ρ.replace i I) (𝟙 Γ₁) (Tm.presheaf.map σ.op label)) (hX σ i ρ)
    (fun _ _ h J => (F.app _ σ.op).hom.monotone (RawValuation.replace_mono i le_rfl h) _ _ J)
    (fun I => ((F.app _ σ.op (ρ.replace i I)).app _ _).hom.monotone)
    ((X.app _ σ.op).hom.monotone.comp (Function.update_mono (f := ρ) (i := i)))

end RawActionFamily

end DomainSemantics.CoherentShape
