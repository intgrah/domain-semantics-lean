/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Constructors
public import DomainSemantics.Interpretation.Family

@[expose] public section

universe u

namespace DomainSemantics.CoherentShape

open CategoryTheory MonoidalCategory Presheaf

variable {Γ Γ₁ Γ₂ : Ctx}
variable {ι : Sort u} (r : Bool)

namespace RawValue

noncomputable def identity (A X Y : RawValue Γ) : RawValue Γ :=
  ΩLower.map₃ identityHom A X Y

@[simp] theorem mem_identity {Γ₁ Γ₂ : Ctx} (A X Y : RawValue Γ₂)
    (σ₁ : Γ₁ ⟶ Γ₂) (z : CoherentShape Γ₁) :
    (identity A X Y).mem σ₁ z ↔ ∃ a x y,
      A.mem σ₁ a ∧ X.mem σ₁ x ∧ Y.mem σ₁ y ∧ z ≤ identityMap a x y :=
  ΩLower.mem_map₃ identityHom A X Y σ₁ z

theorem identity_mono {A A' X X' Y Y' : RawValue Γ}
    (hA : A ≤ A') (hX : X ≤ X') (hY : Y ≤ Y') :
    identity A X Y ≤ identity A' X' Y' :=
  ΩLower.map₃_mono identityHom hA hX hY

@[simp]
theorem pullback_identity (A X Y : RawValue Γ) (σ : Γ₁ ⟶ Γ) :
    (identity A X Y).pullback σ = identity (A.pullback σ) (X.pullback σ)
      (Y.pullback σ) := ΩLower.pullback_map₃ identityHom A X Y σ

noncomputable def identityHom :
    ΩLower.presheaf pointedOrder ⊗ ΩLower.presheaf pointedOrder ⊗ ΩLower.presheaf pointedOrder ⟶
      ΩLower.presheaf pointedOrder where
  app _ := Preord.ofHom {
    toFun := fun (A, X, Y) => identity A X Y
    monotone' := fun _ _ ⟨hA, hX, hY⟩ => identity_mono hA hX hY }
  naturality _ _ σ := Preord.ext fun (A, X, Y) => (pullback_identity A X Y σ.unop).symm

end RawValue

namespace RawFamily

@[simp] theorem iSup_app (F : ι → RawFamily Γ) {X : Ctxᵒᵖ}
    (σ : Opposite.op Γ ⟶ X) (ρ : RawValuation X.unop) :
    (⨆ i, F i).app X σ ρ = ⨆ i, (F i).app X σ ρ := ΩLower.homObj_iSup_app F X σ ρ

theorem iSup_eq {F : ι → RawFamily Γ} (i₀ : ι) {X : RawFamily Γ}
    (h : ∀ i, F i = X) : ⨆ i, F i = X :=
  le_antisymm (iSup_le fun i => (h i).le) (by rw [← h i₀]; exact le_iSup F i₀)

theorem mem_iSup_app (F : ι → RawFamily Γ) {X : Ctxᵒᵖ}
    (σ₁ : Opposite.op Γ ⟶ X) (ρ : RawValuation X.unop) {Y : Ctx} (σ₂ : Y ⟶ X.unop)
    (y : CoherentShape Y) :
    ((⨆ i, F i).app X σ₁ ρ).mem σ₂ y ↔ y ≤ ⊥ ∨ ∃ i, ((F i).app X σ₁ ρ).mem σ₂ y := by
  rw [iSup_app, ΩLower.mem_iSup]

theorem IsFinitary.iSup {F : ι → RawFamily Γ}
    (hF : ∀ i, (F i).IsFinitary) : (⨆ i, F i).IsFinitary := by
  intro Γ₁ σ j ρ I y hy
  rcases (mem_iSup_app F σ.op _ (𝟙 Γ₁) y).mp hy with hy | ⟨i, hy⟩
  · exact ⟨∅, by simp, (mem_iSup_app F σ.op _ (𝟙 Γ₁) y).mpr (Or.inl hy)⟩
  · have ⟨l, hl, hy⟩ := hF i σ j ρ I hy
    exact ⟨l, hl, (mem_iSup_app F σ.op _ (𝟙 Γ₁) y).mpr (Or.inr ⟨i, hy⟩)⟩

theorem pullback_iSup (F : ι → RawFamily Γ) (σ : Γ₁ ⟶ Γ) :
    (⨆ i, F i).pullback σ = ⨆ i, (F i).pullback σ :=
  Functor.functorHom_ext fun _ σ₁ => Preord.ext fun ρ => by
    change (_ : RawValue _) = _
    ext Y g y
    simp only [RawFamily.pullback]
    rw [Functor.functorHom_map_app, mem_iSup_app, mem_iSup_app]
    rfl

noncomputable def sort  : RawFamily Γ :=
  constant (principalIdeal (sortAtom r)).val

@[simp]
theorem sort_value (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (sort r).app _ σ.op ρ = (principalIdeal (sortAtom r : CoherentShape Γ₁)).val :=
  ΩLower.presheaf_map_principal (R := pointedOrder) (sortAtom r) σ

theorem sort_isFinitary  : (sort r : RawFamily Γ).IsFinitary :=
  constant_isFinitary _

theorem sort_value_isDirected (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    ((sort r).app _ σ.op ρ).IsDirected := by
  rw [sort_value]
  exact (principalIdeal (sortAtom r : CoherentShape Γ₁)).property

noncomputable def identity (A X Y : RawFamily Γ) : RawFamily Γ :=
  (A.pair (X.pair Y)).comp (.ofNatTrans RawValue.identityHom)

theorem pullback_identity (A X Y : RawFamily Γ) (σ : Γ₁ ⟶ Γ) :
    (identity A X Y).pullback σ =
      identity (A.pullback σ) (X.pullback σ)
        (Y.pullback σ) :=
  Functor.functorHom_ext (fun _ _ => Preord.ext fun _ => rfl)

theorem IsFinitary.identity {A X Y : RawFamily Γ}
    (hA : A.IsFinitary) (hX : X.IsFinitary) (hY : Y.IsFinitary) :
    (identity A X Y).IsFinitary := by
  intro Γ₁ σ i ρ
  exact ΩLower.IsFinitary.of_eventually fun I _ hz => ΩLower.map₃_eventually identityHom
    (hA.eventually σ i ρ I) (hX.eventually σ i ρ I) (hY.eventually σ i ρ I) hz

end RawFamily

end DomainSemantics.CoherentShape
