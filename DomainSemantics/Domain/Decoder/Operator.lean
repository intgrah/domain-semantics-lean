/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Action

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Opposite Presheaf MonoidalCategory

noncomputable abbrev IdealOperator.operations : Ctxᵒᵖ ⥤ Preord where
  __ := ((ΩIdeal.presheaf pointedOrder).functorHom (ΩIdeal.presheaf pointedOrder)).toPreord
    (order := fun _ => Functor.HomObj.instPreorder)
    (fun {_ _} f {_ _} h Γ g => h Γ (f ≫ g))
  obj Γ := Preord.of (Functor.HomObj
    (ΩIdeal.presheaf pointedOrder) (ΩIdeal.presheaf pointedOrder) (coyoneda.obj (op Γ)))

@[implicit_reducible] def IdealOperator.finitary : Subfunctor (operations ⋙ forget Preord) where
  obj _ := {F | ΩIdeal.Finitary F}
  map _ _ h := h.map _

noncomputable abbrev IdealOperator.presheaf := finitary.toPreord

abbrev IdealOperator (Γ₁ : Ctx) : Type := IdealOperator.presheaf.obj (op Γ₁)

noncomputable def IdealOperator.pullback {Γ Γ₁ : Ctx} (P : IdealOperator Γ) (σ : Γ₁ ⟶ Γ) : IdealOperator Γ₁ :=
  IdealOperator.presheaf.map σ.op P

theorem IdealOperator.pullback_id {Γ : Ctx} (P : IdealOperator Γ) : P.pullback (𝟙 Γ) = P :=
  IdealOperator.presheaf.map_id_apply (op Γ) P

theorem IdealOperator.pullback_pullback {Γ Γ₁ Γ₂ : Ctx} (P : IdealOperator Γ) (σ : Γ₁ ⟶ Γ)
    (σ₁ : Γ₂ ⟶ Γ₁) : (P.pullback σ).pullback σ₁ = P.pullback (σ₁ ≫ σ) :=
  (IdealOperator.presheaf.map_comp_apply σ.op σ₁.op P).symm

namespace IdealOperator

@[simp] theorem app_pullback {Γ₁ Γ₂ Γ₃ : Ctx} (F : IdealOperator Γ₁)
    (σ₁ : op Γ₁ ⟶ op Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (I : Domain Γ₂) :
    F.val.app _ (σ₁ ≫ σ₂.op) (I.pullback σ₂) = ((F.val.app _ σ₁ I).pullback σ₂) :=
  F.val.naturality_apply σ₂.op σ₁ I

noncomputable def ofBasis (G : Functor.HomObj order (ΩIdeal.presheaf pointedOrder) (coyoneda.obj (op (op Γ)))) :
    IdealOperator Γ :=
  ⟨ΩIdeal.ofBasis G, ΩIdeal.finitary_ofBasis G⟩

theorem bottomIdeal_le (I : Domain Γ) :
    bottomIdeal Γ ≤ I := by
  rw [bottomIdeal_eq_bot]
  exact @bot_le (Domain Γ) _ _ I

noncomputable def bottom : IdealOperator Γ where
  val.app Γ₁ _ := Preord.ofHom (OrderHom.const _ (bottomIdeal Γ₁.unop))
  val.naturality σ₁ _ := Preord.ext fun _ => (pullback_bottomIdeal σ₁.unop).symm
  property _ _ I _ h := ⟨⊥, I.bottom (𝟙 _), h⟩

theorem bottom_le (F : IdealOperator Γ) : bottom ≤ F :=
  fun _ σ₁ I ↦ bottomIdeal_le (F.val.app _ σ₁ I)

noncomputable instance : OrderBot (IdealOperator Γ) where
  bot := bottom
  bot_le := bottom_le

noncomputable def applicationAction (F : Domain Γ) : IdealAction Γ where
  val.app _ p := Preord.ofHom {
    toFun := application (F.pullback p.1.unop) p.2
    monotone' _ _ h := application_mono_right (F.pullback p.1.unop) p.2 h }
  val.naturality σ₂ p := Preord.ext fun I =>
    (congrArg (fun H => application H (Tm.presheaf.map σ₂ p.2) (I.pullback σ₂.unop))
      (ΩIdeal.pullback_pullback F p.1.unop σ₂.unop).symm).trans
      (pullback_application (F.pullback p.1.unop) I p.2 σ₂.unop).symm
  property _ := fun (⟨σ⟩, label) => application_argument_finitary (F.pullback σ) label

noncomputable def branchAction (K : IdealOperator Γ) (F : Domain Γ) : IdealAction Γ :=
  ⟨(applicationAction F).val.comp
      (Functor.HomObj.map (A' := coyoneda.obj (op (op Γ)) ⊗ Tm.presheaf)
        { app := fun _ => ↾Prod.fst } K.val),
    (applicationAction F).property.comp (K.property.map _)⟩

end IdealOperator

theorem application_function_finitary
    (F : Domain Γ) {X : Domain Γ} (label : Σ A : Ty Γ, Tm Γ A)
    {y : CoherentShape Γ} (hy : (application F label X).mem (𝟙 Γ) y) :
    ∃ f, F.mem (𝟙 Γ) f ∧
      (application (principalIdeal f) label X).mem (𝟙 Γ) y := by
  have ⟨x, hx, heval⟩ := (CoherentShape.mem_application _ _ _ _ _).mp hy
  simp at heval
  have ⟨f, hf, heval⟩ := heval.function_ideal_finitary
  exact ⟨f, hf, (CoherentShape.mem_application _ _ _ _ _).mpr ⟨x, hx, by simpa using heval⟩⟩

theorem IdealAction.abstraction_finitary
    (H : Domain Γ → IdealAction Γ)
    (hmono : ∀ {I J : Domain Γ}, I ≤ J →
      ∀ (label : Σ A : Ty Γ, Tm Γ A) (X : Domain Γ),
        (H I).val.app _ ((𝟙 Γ).op, label) X ≤ (H J).val.app _ ((𝟙 Γ).op, label) X)
    (hfin : ∀ (I : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A)
      (X : Domain Γ) {y : CoherentShape Γ},
      ((H I).val.app _ ((𝟙 Γ).op, label) X).mem (𝟙 Γ) y →
        ∃ f, I.mem (𝟙 Γ) f ∧
          ((H (principalIdeal f)).val.app _ ((𝟙 Γ).op, label) X).mem (𝟙 Γ) y)
    (I : Domain Γ) {q : CoherentShape Γ}
    (hq : (abstraction (H I)).mem (𝟙 Γ) q) :
    ∃ f, I.mem (𝟙 Γ) f ∧ (abstraction (H (principalIdeal f))).mem (𝟙 Γ) q := by
  have ⟨⟨graph, hcoh⟩, hgraph, hq⟩ := (mem_abstraction _ _ _).mp hq
  let J : Order.Ideal (CoherentShape Γ) := I.fibre (𝟙 Γ)
  have ⟨f, hf, hvalid⟩ := BasisAction.GraphValid.exists_mem
    (H := fun f : CoherentShape Γ => (H (principalIdeal f)).onBasis)
    (f := ⟨graph, hcoh⟩)
    J.nonempty J.directed
    (fun label x _ _ h => hmono (ΩLower.principal_mono h) label (principalIdeal x))
    (fun i => hfin I (graph.names i) _ (hgraph i))
  exact ⟨f, hf, (mem_abstraction _ _ _).mpr ⟨⟨graph, hcoh⟩, hvalid, hq⟩⟩

end DomainSemantics.CoherentShape
