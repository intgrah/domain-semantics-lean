/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Application
public import DomainSemantics.Interpretation.Family

@[expose] public section

namespace DomainSemantics.CoherentShape.RawFamily

open CategoryTheory Presheaf

variable {Γ Γ₁ Γ₂ : Ctx}

def sourceQuery (Γ : Ctx) (a : Term) : Set (Σ A : Ty Γ, Tm Γ A) :=
  {label | ∃ (A : Term) (u : Bool) (hA : Γ.as.terms ⊢ A : .sort u)
    (ha : Γ.as.terms ⊢ a : A), Tm.pairOfTyping Γ.as.wf hA ha = label}

theorem ofTyping_mem_sourceQuery {A a : Term} {u : Bool}
    (hA : Γ.as.terms ⊢ A : .sort u) (ha : Γ.as.terms ⊢ a : A) :
    Tm.pairOfTyping Γ.as.wf hA ha ∈ sourceQuery Γ a :=
  ⟨A, u, hA, ha, rfl⟩

noncomputable def application (F X : RawFamily Γ) (Q : Set (Σ A : Ty Γ, Tm Γ A)) : RawFamily Γ where
  app _ σ := Preord.ofHom {
    toFun ρ := rawApplication (F.app _ σ ρ)
      (Tm.presheaf.map σ '' Q) (X.app _ σ ρ)
    monotone' _ _ hρ := rawApplication_mono ((F.app _ σ).hom.monotone hρ) (Set.Subset.refl _) ((X.app _ σ).hom.monotone hρ) }
  naturality σ₁ σ := Preord.ext fun ρ => by
    change (rawApplication (F.app _ (σ ≫ σ₁) (ρ.pullback σ₁.unop))
      (Tm.presheaf.map (σ ≫ σ₁) '' Q) (X.app _ (σ ≫ σ₁) (ρ.pullback σ₁.unop))) =
      ((rawApplication (F.app _ σ ρ)
      (Tm.presheaf.map σ '' Q) (X.app _ σ ρ)).pullback σ₁.unop)
    symm
    refine (pullback_rawApplication (F.app _ σ ρ) (X.app _ σ ρ) _ σ₁.unop).trans ?_
    rw [← ΩLower.presheaf_map_eq_pullback, ← ΩLower.presheaf_map_eq_pullback,
      ← F.naturality_apply, ← X.naturality_apply]
    simp [Set.image_image]
    rfl

@[simp]
theorem application_value (F X : RawFamily Γ) (Q : Set (Σ A : Ty Γ, Tm Γ A))
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (application F X Q).app _ σ.op ρ = rawApplication (F.app _ σ.op ρ)
      (Tm.presheaf.map σ.op '' Q) (X.app _ σ.op ρ) := rfl

theorem pullback_application (F X : RawFamily Γ) (Q : Set (Σ A : Ty Γ, Tm Γ A))
    (σ : Γ₁ ⟶ Γ) :
    (application F X Q).pullback σ =
      application (F.pullback σ) (X.pullback σ)
        (Tm.presheaf.map σ.op '' Q) := by
  ext Γ₂ ⟨σ₁⟩ ρ
  change rawApplication (F.app _ (σ₁ ≫ σ).op ρ)
      (Tm.presheaf.map (σ₁ ≫ σ).op '' Q) (X.app _ (σ₁ ≫ σ).op ρ) =
    rawApplication (F.app _ (σ₁ ≫ σ).op ρ)
      (Tm.presheaf.map σ₁.op '' (Tm.presheaf.map σ.op '' Q))
      (X.app _ (σ₁ ≫ σ).op ρ)
  simp [Set.image_image]

theorem IsFinitary.application {F X : RawFamily Γ}
    (hF : F.IsFinitary) (hX : X.IsFinitary) (Q : Set (Σ A : Ty Γ, Tm Γ A)) :
    (application F X Q).IsFinitary := by
  intro Γ₁ σ i ρ
  exact ΩLower.IsFinitary.of_eventually fun I _ hy =>
    rawApplication_eventually (hF.eventually σ i ρ I) (hX.eventually σ i ρ I) hy

end DomainSemantics.CoherentShape.RawFamily
