/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Presheaf.IdealMap

@[expose] public section

universe u v

namespace DomainSemantics.Presheaf.ΩIdeal

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {R S : Cᵒᵖ ⥤ CondSemilatSup.{max u v}}
  {A : Cᵒᵖ ⥤ Type (max u v)}

def IsFinitary {X : C} (f : ΩIdeal R X → ΩIdeal S X) : Prop :=
  ∀ I {y}, (f I).mem (𝟙 X) y →
    ∃ x, I.mem (𝟙 X) x ∧ (f (principal R x)).mem (𝟙 X) y

theorem IsFinitary.comp {T : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X : C}
    {f : ΩIdeal R X → ΩIdeal S X} {g : ΩIdeal S X → ΩIdeal T X}
    (hg : IsFinitary g) (hf : IsFinitary f) (hm : Monotone g) : IsFinitary (g ∘ f) := by
  intro I y hy
  have ⟨b, hb, hy⟩ := hg (f I) hy
  have ⟨a, ha, hb⟩ := hf I hb
  exact ⟨a, ha, hm (ΩLower.principal_le_iff.mpr hb) (𝟙 X) y hy⟩

theorem IsFinitary.comp₂ {T U : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X : C}
    {f : ΩIdeal R X × ΩIdeal S X → ΩIdeal T X}
    (hf : Monotone f)
    (h₁ : ∀ J, IsFinitary fun I => f (I, J))
    (h₂ : ∀ I, IsFinitary fun J => f (I, J))
    {g : ΩIdeal U X → ΩIdeal R X} {h : ΩIdeal U X → ΩIdeal S X}
    (hg : IsFinitary g) (hh : IsFinitary h) (hgm : Monotone g) (hhm : Monotone h) :
    IsFinitary fun I => f (g I, h I) := by
  intro I y hy
  have ⟨a, ha, hy⟩ := h₁ (h I) (g I) hy
  have ⟨b, hb, hy⟩ := h₂ (principal R a) (h I) hy
  have ⟨c, hc, ha⟩ := hg I ha
  have ⟨d, hd, hb⟩ := hh I hb
  have ⟨e, he, hce, hde⟩ := I.property (𝟙 X) hc hd
  exact ⟨e, he, hf
    ⟨ΩLower.principal_le_iff.mpr (hgm (ΩLower.principal_mono hce) (𝟙 X) a ha),
      ΩLower.principal_le_iff.mpr (hhm (ΩLower.principal_mono hde) (𝟙 X) b hb)⟩ (𝟙 X) y hy⟩

def Finitary (F : Functor.HomObj (presheaf R) (presheaf S) A) : Prop :=
  ∀ (X : Cᵒᵖ) (a : A.obj X), IsFinitary (F.app X a)

theorem Finitary.map {A' : Cᵒᵖ ⥤ Type (max u v)} (f : A' ⟶ A)
    {F : Functor.HomObj (presheaf R) (presheaf S) A} (hF : Finitary F) : Finitary (F.map f) :=
  fun X a => hF X (f.app X a)

theorem Finitary.id : Finitary (Functor.HomObj.id A : Functor.HomObj (presheaf R) (presheaf R) A) :=
  fun _ _ _ y hy => ⟨y, hy, (ΩLower.mem_principal_id y y).mpr le_rfl⟩

theorem Finitary.comp {T : Cᵒᵖ ⥤ CondSemilatSup.{max u v}}
    {F : Functor.HomObj (presheaf R) (presheaf S) A} {G : Functor.HomObj (presheaf S) (presheaf T) A}
    (hF : Finitary F) (hG : Finitary G) : Finitary (F.comp G) :=
  fun X a => (hG X a).comp (hF X a) (G.app X a).hom.monotone

def basisSlice (G : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) A) {X : Cᵒᵖ}
    (a : A.obj X) :
    Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (ΩLower.presheaf S) (uliftYoneda.{u}.obj X.unop) :=
  (G.map (uliftYonedaEquiv.symm a)).comp (.ofNatTrans (toLowerNatTrans S))

def ofBasis (G : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) A) :
    Functor.HomObj (presheaf R) (presheaf S) A where
  app _ a := Preord.ofHom {
    toFun I := ⟨I.val.bind (basisSlice G a),
      ΩLower.IsDirected.bind I.property _ fun _ _ _ => (G.app _ _ _).property⟩
    monotone' _ _ h := ΩLower.bind_mono h fun _ _ _ => fun _ _ h => h }
  naturality f a := Preord.ext fun I => Subtype.ext <|
    (congrArg (fun T => (I.val.pullback f.unop).bind
        ((G.map T).comp (.ofNatTrans (toLowerNatTrans S)))) (uliftYonedaEquiv_symm_map f a)).trans
      (ΩLower.pullback_bind I.val (basisSlice G a) f.unop).symm

@[simp] theorem basisSlice_app (G : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) A)
    {X : Cᵒᵖ} (a : A.obj X) {Y : C} (f : Y ⟶ X.unop) (x : R.obj (op Y)) :
    (basisSlice G a).app (op Y) ⟨f⟩ x = (G.app (op Y) (A.map f.op a) x).val := rfl

@[simp] theorem ofBasis_app_val (G : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) A)
    (X : Cᵒᵖ) (a : A.obj X) (I : ΩIdeal R X.unop) :
    ((ofBasis G).app X a I).val = I.val.bind (basisSlice G a) := by
  unfold ofBasis
  rfl

theorem mem_ofBasis (G : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) A)
    (X : Cᵒᵖ) (a : A.obj X) (I : ΩIdeal R X.unop) {Y : C} (f : Y ⟶ X.unop) (y : S.obj (op Y)) :
    ((ofBasis G).app X a I).mem f y ↔
      ∃ x, I.mem f x ∧ (G.app (op Y) (A.map f.op a) x).mem (𝟙 Y) y := by
  rw [← val_mem, ofBasis_app_val, ΩLower.mem_bind]
  rfl

theorem finitary_ofBasis (G : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) A) :
    Finitary (ofBasis G) := fun X a I y hy =>
  have ⟨x, hx, hy⟩ := (mem_ofBasis G X a I (𝟙 _) y).mp hy
  ⟨x, hx, (mem_ofBasis G X a _ (𝟙 _) y).mpr ⟨x, (ΩLower.mem_principal_id x x).mpr le_rfl, hy⟩⟩

end DomainSemantics.Presheaf.ΩIdeal
