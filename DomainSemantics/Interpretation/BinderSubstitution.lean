/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Comprehension.Pullback
public import DomainSemantics.Interpretation.Pi
public import DomainSemantics.Domain.Decoder.PiStages
public import DomainSemantics.Interpretation.Abstraction

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ Γ₂ ΓA ΓA' : Ctx} {θ : Γ₁ ⟶ Γ} {f : ΓA' ⟶ ΓA}

namespace RawFamily

theorem sectionValue_substitution_eq
    (hA : Display Tm.typing Γ ΓA) (hA' : Display Tm.typing Γ₁ ΓA')
    (hπ : IsPullback f hA'.projection hA.projection θ)
    (hq : Tm.presheaf.map f.op hA.generic = hA'.generic)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ ρ' : RawValuation Γ₂) (label : Σ A : Ty Γ₂, Tm Γ₂ A)
    (I J : RawValue Γ₂)
    (hbody : ∀ {Γ₃ : Ctx} (σ₂ : Γ₃ ⟶ Γ₂)
      (s : hA'.Section (σ₂ ≫ σ₁)
        (Tm.presheaf.map σ₂.op label)),
      B.app _ (s.hom ≫ f).op
          ((ρ.pullback σ₂).push (I.pullback σ₂)) =
        B'.app _ s.hom.op ((ρ'.pullback σ₂).push (J.pullback σ₂))) :
    sectionValue hA B (σ₁ ≫ θ) ρ label I =
      sectionValue hA' B' σ₁ ρ' label J := by
  apply (bodySection hA' B' σ₁ ρ' label J).eq_extend
  · intro Γ₃ τ y hy hne
    have ⟨s⟩ := (bodySection hA B (σ₁ ≫ θ) ρ label I).support hy hne
    exact ⟨Presheaf.Section.lift (h := hA.isPullback) hπ hq {
      hom := s.hom
      over := s.over.trans (Category.assoc _ _ _).symm
      generic := s.generic }⟩
  · intro Γ₃ τ s
    let t : hA.Section _ _ := s.map f (by rw [hπ.w, ← Category.assoc, s.over]) hq
    let t' : (sectionDomain hA (σ₁ ≫ θ) label).Witness τ := {
      hom := t.hom
      over := t.over.trans (Category.assoc _ _ _)
      generic := t.generic }
    rw [sectionValue, (bodySection hA B (σ₁ ≫ θ) ρ label I).pullback_extend τ t']
    exact hbody τ s

open CodeAssignment

def BodyAgreesOnFixed (hA' : Display Tm.typing Γ₁ ΓA') (θ : Γ₁ ⟶ Γ) (f : ΓA' ⟶ ΓA)
    (C : RawFamily Γ) (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ ρ' : RawValuation Γ₂) : Prop :=
  ∀ {Γ₃ : Ctx} (σ₂ : Γ₃ ⟶ Γ₂) (name : Σ A : Ty Γ₃, Tm Γ₃ A)
    (s : hA'.Section (σ₂ ≫ σ₁) name)
    (J : Domain Γ₃),
    piLimit.rawExtend
        (C.app _ ((σ₂ ≫ σ₁) ≫ θ).op (ρ.pullback σ₂)) J.val = J.val →
    B.app _ (s.hom ≫ f).op ((ρ.pullback σ₂).push J.val) =
      B'.app _ s.hom.op ((ρ'.pullback σ₂).push J.val)

theorem normalizedSectionValue_substitution_eq
    (hA : Display Tm.typing Γ ΓA) (hA' : Display Tm.typing Γ₁ ΓA')
    (hπ : IsPullback f hA'.projection hA.projection θ)
    (hq : Tm.presheaf.map f.op hA.generic = hA'.generic)
    (C : RawFamily Γ) (C' : RawFamily Γ₁)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ ρ' : RawValuation Γ₂) (label : Σ A : Ty Γ₂, Tm Γ₂ A)
    (I : Domain Γ₂)
    (hC : (C.app _ (σ₁ ≫ θ).op ρ).IsDirected)
    (hcode : C.app _ (σ₁ ≫ θ).op ρ = C'.app _ σ₁.op ρ')
    (hbody : BodyAgreesOnFixed hA' θ f C B B' σ₁ ρ ρ') :
    normalizedSectionValue piLimit hA C B (σ₁ ≫ θ) ρ label I.val =
      normalizedSectionValue piLimit hA' C' B'
        σ₁ ρ' label I.val := by
  unfold normalizedSectionValue
  rw [← hcode]
  apply sectionValue_substitution_eq hA hA' hπ hq B B' σ₁ ρ ρ' label
  intro Γ₃ σ₂ s
  have hCυ : (C.app _ ((σ₂ ≫ σ₁) ≫ θ).op (ρ.pullback σ₂)).IsDirected := by
    rw [Category.assoc, op_comp, ← C.app_pullback]
    exact hC.pullback σ₂
  rw [piLimit.pullback_rawExtend, C.app_pullback, ← op_comp, ← Category.assoc]
  exact hbody σ₂ (Tm.presheaf.map σ₂.op label) s
    ⟨_, piLimit.rawExtend_isDirected hCυ (I.pullback σ₂).property⟩
    (piLimit.rawExtend_idempotent piLimit_isIdempotent hCυ (I.pullback σ₂).property)

theorem normalizedBodyAction_substitution_eq_on_ideals
    (hA : Display Tm.typing Γ ΓA) (hA' : Display Tm.typing Γ₁ ΓA')
    (hπ : IsPullback f hA'.projection hA.projection θ)
    (hq : Tm.presheaf.map f.op hA.generic = hA'.generic)
    (C : RawFamily Γ) (C' : RawFamily Γ₁)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ ρ' : RawValuation Γ₂)
    (hC : (C.app _ (σ₁ ≫ θ).op ρ).IsDirected)
    (hcode : C.app _ (σ₁ ≫ θ).op ρ = C'.app _ σ₁.op ρ')
    (hbody : BodyAgreesOnFixed hA' θ f C B B' σ₁ ρ ρ')
    {Γ₃ : Ctx} (σ₂ : Γ₃ ⟶ Γ₂) (label : Σ A : Ty Γ₃, Tm Γ₃ A)
    (I : Domain Γ₃) :
    (normalizedBodyAction piLimit hA C B (σ₁ ≫ θ) ρ).app _ (σ₂.op, label) I.val =
      (normalizedBodyAction piLimit hA' C' B' σ₁ ρ').app _ (σ₂.op, label) I.val := by
  change normalizedSectionValue piLimit hA C B (σ₂ ≫ (σ₁ ≫ θ))
      (ρ.pullback σ₂) label I.val =
    normalizedSectionValue piLimit hA' C' B' (σ₂ ≫ σ₁)
      (ρ'.pullback σ₂) label I.val
  rw [← Category.assoc]
  have hCυ : (C.app _ ((σ₂ ≫ σ₁) ≫ θ).op (ρ.pullback σ₂)).IsDirected := by
    rw [Category.assoc, op_comp, ← C.app_pullback]
    exact hC.pullback σ₂
  have hcodeυ : C.app _ ((σ₂ ≫ σ₁) ≫ θ).op (ρ.pullback σ₂) =
      C'.app _ (σ₂ ≫ σ₁).op (ρ'.pullback σ₂) := by
    rw [Category.assoc, op_comp, ← C.app_pullback, op_comp (g := σ₁), ← C'.app_pullback, hcode]
  apply normalizedSectionValue_substitution_eq hA hA' hπ hq C C' B B'
    (σ₂ ≫ σ₁) (ρ.pullback σ₂) (ρ'.pullback σ₂) label I hCυ hcodeυ
  intro Γ₄ χ name s J hfixed
  simp_rw [RawValuation.pullback_comp] at hfixed ⊢
  have hbody' := hbody (χ ≫ σ₂) name
  rw [Category.assoc] at hbody'
  exact hbody' s J hfixed

end RawFamily

theorem rawPi_eq_of_eq_on_ideals (label : Σ A : Ty Γ, Ty (Γ.extend A)) (C : RawValue Γ)
    {F G : RawAction Γ}
    (h : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (name : Σ A : Ty Γ₁, Tm Γ₁ A)
      (I : Domain Γ₁),
      F.app _ (σ.op, name) I.val = G.app _ (σ.op, name) I.val) :
    rawPi label C F = rawPi label C G :=
  congrArg (BasisAction.pi label C) (RawAction.onBasis_eq_of_eq_on_ideals h)

namespace RawFamily

open CodeAssignment

theorem abstraction_substitution_eq
    (hA : Display Tm.typing Γ ΓA) (hA' : Display Tm.typing Γ₁ ΓA')
    (hπ : IsPullback f hA'.projection hA.projection θ)
    (hq : Tm.presheaf.map f.op hA.generic = hA'.generic)
    (C : RawFamily Γ) (C' : RawFamily Γ₁)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ ρ' : RawValuation Γ₂)
    (hC : (C.app _ (σ₁ ≫ θ).op ρ).IsDirected)
    (hcode : C.app _ (σ₁ ≫ θ).op ρ = C'.app _ σ₁.op ρ')
    (hbody : BodyAgreesOnFixed hA' θ f C B B' σ₁ ρ ρ') :
    (abstraction piLimit hA C B).app _ (σ₁ ≫ θ).op ρ =
      (abstraction piLimit hA' C' B').app _ σ₁.op ρ' :=
  RawAction.abstraction_eq_of_eq_on_ideals (normalizedBodyAction_substitution_eq_on_ideals
    hA hA' hπ hq C C' B B' σ₁ ρ ρ' hC hcode hbody)

theorem pi_substitution_eq
    (hA : Display Tm.typing Γ ΓA) (hA' : Display Tm.typing Γ₁ ΓA')
    (hπ : IsPullback f hA'.projection hA.projection θ)
    (hq : Tm.presheaf.map f.op hA.generic = hA'.generic)
    (label : Σ A : Ty Γ, Ty (Γ.extend A)) (C : RawFamily Γ) (C' : RawFamily Γ₁)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ ρ' : RawValuation Γ₂)
    (hC : (C.app _ (σ₁ ≫ θ).op ρ).IsDirected)
    (hcode : C.app _ (σ₁ ≫ θ).op ρ = C'.app _ σ₁.op ρ')
    (hbody : BodyAgreesOnFixed hA' θ f C B B' σ₁ ρ ρ') :
    (pi piLimit hA label C B).app _ (σ₁ ≫ θ).op ρ =
      (pi piLimit hA'
        (Ty.pairPresheaf.map (θ).op label) C' B').app _ σ₁.op ρ' := by
  rw [pi_value, pi_value, op_comp, Functor.map_comp_apply, ← hcode]
  apply rawPi_eq_of_eq_on_ideals
  exact normalizedBodyAction_substitution_eq_on_ideals hA hA' hπ hq C C' B B'
    σ₁ ρ ρ' hC hcode hbody

end RawFamily

end DomainSemantics.CoherentShape
