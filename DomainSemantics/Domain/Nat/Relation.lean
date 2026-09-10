/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.RecursiveLabel
public import DomainSemantics.Domain.Constructors
public import DomainSemantics.Domain.Evaluation
public import Mathlib.CategoryTheory.Subfunctor.Image

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

open CategoryTheory Opposite MonoidalCategory Presheaf

theorem compatible_succMap_iff {Γ : Ctx} {label label' : Σ A : Ty Γ, Tm Γ A}
    {a b : CoherentShape Γ} :
    Compatible (succMap label a) (succMap label' b) ↔ label = label' ∧ Compatible a b := by
  change (Tm.presheaf.map (𝟙 Γ).op label = Tm.presheaf.map (𝟙 Γ).op label' ∧
    Shape.Compatible (𝟙 Γ) a.1 b.1) ↔ _
  simp [Compatible]

theorem succMap_le_succMap_iff {Γ : Ctx} {label label' : Σ A : Ty Γ, Tm Γ A}
    {a b : CoherentShape Γ} :
    succMap label a ≤ succMap label' b ↔ label = label' ∧ a ≤ b :=
  ⟨Basis.LE.succ_inv, fun ⟨hl, h⟩ => hl ▸ .succ h⟩

theorem not_compatible_zeroAtom_succMap {Γ : Ctx} (label : Σ A : Ty Γ, Tm Γ A)
    (a : CoherentShape Γ) : ¬Compatible (zeroAtom : CoherentShape Γ) (succMap label a) :=
  fun h => h

theorem Evaluates.application_argument_finitary
    {Γ : Ctx} {B X : Domain Γ} {label outerLabel : Σ A : Ty Γ, Tm Γ A}
    {input output : CoherentShape Γ}
    (h : Evaluates (application B label X) outerLabel input output) :
    ∃ x, X.mem (𝟙 Γ) x ∧
      Evaluates (application B label (principalIdeal x)) outerLabel input output :=
  h.exists_principal (fun _ _ h => application_mono_right B label h)
    (CoherentShape.application_argument_finitary B label)

structure NatRecLabelRelation (Γ₁ : Ctx) where
  predicate : Subfunctor ((uliftYoneda.obj Γ₁ ⊗ Tm.presheaf) ⊗
    Tm.presheaf)
  functional {Γ₂ : Ctx} {σ₁ : Γ₂ ⟶ Γ₁} {predecessor result result'} :
    predicate.obj (op Γ₂) ((⟨σ₁⟩, predecessor), result) →
    predicate.obj (op Γ₂) ((⟨σ₁⟩, predecessor), result') → result = result'

namespace NatRecLabelRelation

abbrev holds (R : NatRecLabelRelation Γ₁) (σ₁ : Γ₂ ⟶ Γ₁)
    (predecessor result : Σ A : Ty Γ₂, Tm Γ₂ A) : Prop :=
  R.predicate.obj (op Γ₂) ((⟨σ₁⟩, predecessor), result)

theorem natural (R : NatRecLabelRelation Γ₁) {σ₁ : Γ₂ ⟶ Γ₁} {predecessor result}
    (h : R.holds σ₁ predecessor result) (σ₂ : Γ₃ ⟶ Γ₂) :
    R.holds (σ₂ ≫ σ₁) (Tm.presheaf.map σ₂.op predecessor)
      (Tm.presheaf.map σ₂.op result) :=
  R.predicate.map σ₂.op h

@[ext] theorem ext {R S : NatRecLabelRelation Γ₁}
    (h : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) predecessor result,
      R.holds σ₁ predecessor result ↔ S.holds σ₁ predecessor result) : R = S := by
  cases R
  cases S
  congr
  ext Γ₂ ⟨⟨⟨σ⟩, predecessor⟩, result⟩
  exact h σ predecessor result

def ofMorphism {Γ ΓA : Ctx} (D : Display Tm.typing Γ ΓA)
    (f : yoneda.obj ΓA ⟶ Tm.presheaf) : NatRecLabelRelation Γ where
  predicate.obj _ p := Section.graph D.isPullback f p.1.1.down p.1.2 p.2
  predicate.map σ _ h := Section.graph_map h σ.unop
  functional := Section.graph_functional

def syntactic {Γ : Ctx} {C a b : Term} {v : Bool}
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/])
    (hb : Γ.as.terms ⊢ b : Term.natRecType C) : NatRecLabelRelation Γ :=
  ofMorphism (Ctx.rawDisplay (.nat : Γ.as.terms ⊢ .nat : .type)) (Tm.natRec hC ha hb)

theorem syntactic_congr
    {Γ : Ctx} {C C' a a' b b' : Term} {v v' w : Bool}
    {hC : .nat :: Γ.as.terms ⊢ C : .sort v}
    {hC' : .nat :: Γ.as.terms ⊢ C' : .sort v'}
    {ha : Γ.as.terms ⊢ a : C[Term.zero/]}
    {ha' : Γ.as.terms ⊢ a' : C'[Term.zero/]}
    {hb : Γ.as.terms ⊢ b : Term.natRecType C}
    {hb' : Γ.as.terms ⊢ b' : Term.natRecType C'}
    (hCC' : .nat :: Γ.as.terms ⊢ C ≡ C' : .sort w)
    (haa' : Γ.as.terms ⊢ a ≡ a' : C[Term.zero/])
    (hbb' : Γ.as.terms ⊢ b ≡ b' : Term.natRecType C) :
    syntactic hC ha hb = syntactic hC' ha' hb' :=
  congrArg (ofMorphism _) (Tm.natRec.congr hCC' haa' hbb')

def pullback {Γ₁ Γ : Ctx} (R : NatRecLabelRelation Γ)
    (σ : Γ₁ ⟶ Γ) : NatRecLabelRelation Γ₁ where
  predicate := R.predicate.preimage
    ((uliftYoneda.map σ ▷ Tm.presheaf) ▷ Tm.presheaf)
  functional := R.functional

@[simp] theorem holds_pullback {Γ₁ Γ₂ Γ : Ctx} (R : NatRecLabelRelation Γ) (σ : Γ₂ ⟶ Γ)
    (σ₁ : Γ₁ ⟶ Γ₂) (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A) :
    (R.pullback σ).holds σ₁ predecessor result ↔ R.holds (σ₁ ≫ σ) predecessor result := Iff.rfl

@[simp]
theorem pullback_id (R : NatRecLabelRelation Γ) :
    R.pullback (𝟙 Γ) = R := by
  ext Γ₁ σ predecessor result
  change R.holds (σ ≫ 𝟙 Γ) predecessor result ↔
    R.holds σ predecessor result
  simp

theorem pullback_comp {Γ₁ Γ₂ Γ : Ctx}
    (R : NatRecLabelRelation Γ) (σ : Γ₂ ⟶ Γ) (σ₁ : Γ₁ ⟶ Γ₂) :
    (R.pullback σ).pullback σ₁ = R.pullback (σ₁ ≫ σ) := by
  ext Γ₃ σ₂ predecessor result
  change R.holds ((σ₂ ≫ σ₁) ≫ σ) predecessor result ↔
    R.holds (σ₂ ≫ (σ₁ ≫ σ)) predecessor result
  simp

end NatRecLabelRelation

end DomainSemantics.CoherentShape
