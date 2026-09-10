/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Evaluation
public import Mathlib.Order.Filter.Defs
import DomainSemantics.Domain.Action
import DomainSemantics.Presheaf.Approximation

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory MonoidalCategory Opposite Presheaf

variable {Γ Γ₁ Γ₂ : Ctx}

theorem stepApplication_mono (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    {p q : CoherentShape Γ₁ × CoherentShape Γ₁} (h : p ≤ q) :
    application (principalIdeal p.1) label (principalIdeal p.2) ≤
      application (principalIdeal q.1) label (principalIdeal q.2) :=
  fun f a ha =>
    application_mono_right (principalIdeal q.1) label
      (ΩLower.principal_mono h.2) f a
      (application_mono_left
        (ΩLower.principal_mono h.1) label (principalIdeal p.2) f a ha)

noncomputable def stepApplication (label : Σ A : Ty Γ, Tm Γ A) :
    Functor.HomObj (order ⊗ order) (ΩIdeal.presheaf pointedOrder)
      (uliftYoneda.{0}.obj Γ) where
  app _ f := Preord.ofHom {
    toFun p := application (principalIdeal p.1) (Tm.presheaf.map f.down.op label)
      (principalIdeal p.2)
    monotone' _ _ h := stepApplication_mono _ h }
  naturality σ₁ f := by
    ext ⟨u, x⟩
    change application (principalIdeal (reindex σ₁.unop u))
        (Tm.presheaf.map (σ₁.unop ≫ f.down).op label)
        (principalIdeal (reindex σ₁.unop x)) =
      (application (principalIdeal u) (Tm.presheaf.map f.down.op label)
        (principalIdeal x)).pullback σ₁.unop
    rw [pullback_application, ΩIdeal.presheaf_map_principal,
      ΩIdeal.presheaf_map_principal, op_comp, Functor.map_comp_apply]
    rfl

noncomputable abbrev stepApplicationRaw (label : Σ A : Ty Γ, Tm Γ A) :=
  (stepApplication label).comp (.ofNatTrans (ΩIdeal.toLowerNatTrans pointedOrder))

@[simp] theorem stepApplication_app (label : Σ A : Ty Γ, Tm Γ A) (σ : Γ₁ ⟶ Γ)
    (u x : CoherentShape Γ₁) :
    (stepApplication label).app (op Γ₁) ⟨σ⟩ (u, x) =
      application (principalIdeal u) (Tm.presheaf.map σ.op label) (principalIdeal x) :=
  rfl

@[simp] theorem stepApplicationRaw_app (label : Σ A : Ty Γ, Tm Γ A) (σ : Γ₁ ⟶ Γ)
    (u x : CoherentShape Γ₁) :
    (stepApplicationRaw label).app (op Γ₁) ⟨σ⟩ (u, x) =
      (application (principalIdeal u) (Tm.presheaf.map σ.op label)
        (principalIdeal x)).val :=
  rfl

theorem application_eq_bind₂ (I : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) (X : Domain Γ) :
    application I label X = ΩIdeal.bind₂ I X (stepApplication label) := by
  ext Γ₁ σ y
  rw [mem_application, ΩIdeal.mem_bind₂]
  constructor
  · intro ⟨x, hx, heval⟩
    have ⟨u, hu, heval'⟩ := Evaluates.function_ideal_finitary heval
    refine ⟨u, x, by simpa using hu, hx, ?_⟩
    rw [stepApplication_app, mem_application]
    exact ⟨x, by simp, by simpa using heval'⟩
  · intro ⟨u, x, hu, hx, hy⟩
    rw [stepApplication_app, mem_application] at hy
    have ⟨x', hx', heval⟩ := hy
    refine ⟨x, hx, ?_⟩
    have hle : principalIdeal u ≤ I.pullback σ :=
      ΩLower.principal_le_iff.mpr (by simpa using hu)
    exact ((by simpa using heval : Evaluates (principalIdeal u)
      (Tm.presheaf.map σ.op label) x' y).mono (by simpa using hx')).mono_ideal hle

noncomputable def rawApplication (F : RawValue Γ) (Q : Set (Σ A : Ty Γ, Tm Γ A)) (X : RawValue Γ) :
    RawValue Γ :=
  ⨆ label ∈ Q, ΩLower.bind₂ F X (stepApplicationRaw label)

theorem mem_rawApplication (F : RawValue Γ) (Q : Set (Σ A : Ty Γ, Tm Γ A)) (X : RawValue Γ)
    (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁) :
    (rawApplication F Q X).mem σ y ↔ y ≤ ⊥ ∨ ∃ label ∈ Q, ∃ u x, F.mem σ u ∧ X.mem σ x ∧
      (application (principalIdeal u) (Tm.presheaf.map σ.op label)
        (principalIdeal x)).mem (𝟙 Γ₁) y := by
  simp only [rawApplication, ΩLower.mem_iSup, ΩLower.mem_bind₂,
    stepApplicationRaw_app, ΩIdeal.val_mem]
  constructor
  · rintro (h | ⟨label, h | ⟨hlabel, h⟩⟩)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr ⟨label, hlabel, h⟩
  · rintro (h | ⟨label, hlabel, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨label, Or.inr ⟨hlabel, h⟩⟩

theorem rawApplication_mono {F G X Y : RawValue Γ} {Q R : Set (Σ A : Ty Γ, Tm Γ A)}
    (hFG : F ≤ G) (hQR : Q ⊆ R) (hXY : X ≤ Y) :
    rawApplication F Q X ≤ rawApplication G R Y := by
  intro Γ₁ σ y hy
  rw [mem_rawApplication] at hy ⊢
  rcases hy with hy | ⟨label, hlabel, u, x, hu, hx, hy⟩
  · exact Or.inl hy
  · exact Or.inr ⟨label, hQR hlabel, u, x, hFG σ u hu, hXY σ x hx, hy⟩

theorem pullback_rawApplication (F X : RawValue Γ)
    (Q : Set (Σ A : Ty Γ, Tm Γ A)) (σ : Γ₁ ⟶ Γ) :
    (rawApplication F Q X).pullback σ =
      rawApplication (F.pullback σ) (Tm.presheaf.map σ.op '' Q) (X.pullback σ) := by
  ext Γ₂ σ₁ y
  rw [ΩLower.presheaf_map_mem, mem_rawApplication, mem_rawApplication]
  simp [-Sigma.exists]
  rfl

theorem rawApplication_singleton (F X : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) :
    rawApplication F.val {label} X.val = (application F label X).val := by
  rw [rawApplication, iSup_singleton, application_eq_bind₂]
  rfl

theorem rawApplication_eq_of_support (F X : Domain Γ)
    {Q : Set (Σ A : Ty Γ, Tm Γ A)} (label : Σ A : Ty Γ, Tm Γ A) (hlabel : label ∈ Q)
    (hsupport : ∀ {Γ₁} (σ : Γ₁ ⟶ Γ) (label' : Σ A : Ty Γ₁, Tm Γ₁ A),
      label' ∈ Tm.presheaf.map σ.op '' Q →
      ∀ {x y : CoherentShape Γ₁}, OutputAtom (F.pullback σ).val label' x y →
        y ≤ ⊥ ∨ label' = Tm.presheaf.map σ.op label) :
    rawApplication F.val Q X.val = (application F label X).val := by
  apply le_antisymm
  · intro Γ₁ σ y hy
    simp
    rcases (mem_rawApplication _ _ _ _ _).mp hy with hy | ⟨name, hname, u, x, hu, hx, hy⟩
    · exact (application F label X).lower σ hy ((application F label X).bottom σ)
    rw [mem_application] at hy
    have ⟨x', hx', heval⟩ := hy
    simp at heval
    have hle : principalIdeal u ≤ F.pullback σ :=
      ΩLower.principal_le_iff.mpr (by simpa using hu)
    have heval := (heval.mono_ideal hle).mono (show x' ≤ x by simpa using hx')
    by_cases hname' : Tm.presheaf.map σ.op name = Tm.presheaf.map σ.op label
    · exact ⟨x, hx, hname' ▸ heval⟩
    · refine (application F label X).lower σ ?_ ((application F label X).bottom σ)
      apply heval.le_of_outputAtom
      intro w hw
      rcases hsupport σ _ ⟨name, hname, rfl⟩ hw with hbottom | hlabel
      · exact hbottom
      · exact absurd hlabel hname'
  · intro Γ₁ σ y hy
    rw [ΩIdeal.val_mem, application_eq_bind₂, ΩIdeal.mem_bind₂] at hy
    have ⟨u, x, hu, hx, hy⟩ := hy
    rw [stepApplication_app] at hy
    rw [mem_rawApplication]
    exact Or.inr ⟨label, hlabel, u, x, hu, hx, hy⟩

theorem rawApplication_eventually {α : Type*} {l : Filter α}
    {F X : RawValue Γ} {Fs Xs : α → RawValue Γ} {Q : Set (Σ A : Ty Γ, Tm Γ A)}
    (hF : ∀ {x}, F.mem (𝟙 Γ) x → ∀ᶠ a in l, (Fs a).mem (𝟙 Γ) x)
    (hX : ∀ {x}, X.mem (𝟙 Γ) x → ∀ᶠ a in l, (Xs a).mem (𝟙 Γ) x)
    {y : CoherentShape Γ} (hy : (rawApplication F Q X).mem (𝟙 Γ) y) :
    ∀ᶠ a in l, (rawApplication (Fs a) Q (Xs a)).mem (𝟙 Γ) y :=
  ΩLower.iSup_eventually (fun label => ΩLower.iSup_eventually
    (fun _ => ΩLower.bind₂_eventually (stepApplicationRaw label) hF hX)) hy

end DomainSemantics.CoherentShape
