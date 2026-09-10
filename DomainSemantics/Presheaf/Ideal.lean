/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Presheaf.Lower.Basic
public import Mathlib.Order.Ideal

@[expose] public section

universe u v

namespace DomainSemantics.Presheaf

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C]

abbrev ΩIdeal (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (X : C) :=
  {L : ΩLower R X // L.IsDirected}

@[implicit_reducible, simps! obj]
def ΩIdeal.presheaf (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) : Cᵒᵖ ⥤ Preord.{max u v} where
  __ := (ΩLower.directedSubfunctor R).toPreord
  obj X := Preord.of (ΩIdeal R X.unop)

namespace ΩIdeal

variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y Z : C}

instance (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (X : Cᵒᵖ) :
    PartialOrder ((presheaf R).obj X) := inferInstanceAs (PartialOrder (ΩIdeal R X.unop))

def pullback (I : ΩIdeal R X) (f : Y ⟶ X) : ΩIdeal R Y := (presheaf R).map f.op I

@[simp↓] theorem presheaf_map_eq_pullback {X Y : Cᵒᵖ} (g : X ⟶ Y) (I : ΩIdeal R X.unop) :
    (presheaf R).map g I = I.pullback g.unop := rfl

@[simp] theorem pullback_id (I : ΩIdeal R X) : I.pullback (𝟙 X) = I :=
  (presheaf R).map_id_apply _ I

@[simp] theorem pullback_pullback (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    (I.pullback f).pullback g = I.pullback (g ≫ f) :=
  ((presheaf R).map_comp_apply f.op g.op I).symm

theorem pullback_mono {I J : ΩIdeal R X} (h : I ≤ J) (f : Y ⟶ X) : I.pullback f ≤ J.pullback f :=
  ((presheaf R).map f.op).hom.monotone h

abbrev mem (I : ΩIdeal R X) (f : Y ⟶ X) (a : R.obj (op Y)) := I.val.mem f a

theorem bottom (I : ΩIdeal R X) (f : Y ⟶ X) : I.mem f ⊥ := I.val.bottom f

theorem lower (I : ΩIdeal R X) (f : Y ⟶ X) {a b : R.obj (op Y)}
    (h : a ≤ b) : I.mem f b → I.mem f a := I.val.lower f h

theorem natural (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Y)) :
    I.mem f a → I.mem (g ≫ f) (R.map g.op a) := I.val.natural f g a

end ΩIdeal

namespace ΩLower

variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y : C}

def toIdeal (L : ΩLower R X) (hL : L.IsDirected) : ΩIdeal R X := ⟨L, hL⟩

end ΩLower

namespace ΩIdeal

variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y Z : C}

def fibre (I : ΩIdeal R X) (f : Y ⟶ X) :
    Order.Ideal (R.obj (op Y)) :=
  ⟨⟨{a | I.mem f a}, fun _ _ h hb => I.lower f h hb⟩,
    ⟨(⊥ : R.obj (op Y)), I.bottom f⟩, fun _ ha _ hb => I.property f ha hb⟩

@[simp]
theorem val_mem (I : ΩIdeal R X) (f : Y ⟶ X) (a : R.obj (op Y)) :
    I.val.mem f a ↔ I.mem f a := Iff.rfl

@[ext]
theorem ext {I J : ΩIdeal R X}
    (h : ∀ {Y : C} (f : Y ⟶ X) (a : R.obj (op Y)),
      I.mem f a ↔ J.mem f a) : I = J :=
  Subtype.val_injective (ΩLower.ext h)

theorem le_def {I J : ΩIdeal R X} :
    I ≤ J ↔ ∀ {Y : C} (f : Y ⟶ X) (a : R.obj (op Y)), I.mem f a → J.mem f a :=
  Iff.rfl

instance : Bot (ΩIdeal R X) := ⟨⟨⊥, ΩLower.isDirected_bot⟩⟩

instance : OrderBot (ΩIdeal R X) where
  bot_le I := @bot_le (ΩLower R X) _ _ I.val

@[simp]
theorem mem_bot (f : Y ⟶ X) (a : R.obj (op Y)) :
    (⊥ : ΩIdeal R X).mem f a ↔ a ≤ ⊥ := ΩLower.mem_bot f a

@[simp↓] theorem presheaf_map_mem (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Z)) :
    (I.pullback f).mem g a ↔ I.mem (g ≫ f) a := Iff.rfl

@[simp↓] theorem presheaf_map_mem_id (I : ΩIdeal R X) (f : Y ⟶ X)
    (a : R.obj (op Y)) :
    (I.pullback f).mem (𝟙 Y) a ↔ I.mem f a := by simp

def principal (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (x : R.obj (op X)) : ΩIdeal R X where
  val := ΩLower.principal R x
  property := ΩLower.isDirected_principal x

@[simp] theorem mem_principal (x : R.obj (op X)) (f : Y ⟶ X) (a : R.obj (op Y)) :
    (principal R x).mem f a ↔ a ≤ R.map f.op x := ΩLower.mem_principal x f a

@[simp]
theorem principal_bottom : principal R (⊥ : R.obj (op X)) = ⊥ :=
  Subtype.val_injective ΩLower.principal_bottom

@[simp]
theorem presheaf_map_principal (x : R.obj (op X)) (f : Y ⟶ X) :
    (principal R x).pullback f = principal R (R.map f.op x) :=
  Subtype.val_injective (ΩLower.presheaf_map_principal x f)

@[simps! app_hom_coe] def principalNatTrans (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) : (R ⋙ forget₂ CondSemilatSup Preord) ⟶ presheaf R where
  app _ := Preord.ofHom {
    toFun := principal R
    monotone' _ _ h := ΩLower.principal_mono h }
  naturality {_ _} f := Preord.ext fun x => (presheaf_map_principal x f.unop).symm

@[simps! app_hom_coe] def toLowerNatTrans (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) : presheaf R ⟶ ΩLower.presheaf R where
  app _ := Preord.ofHom (OrderEmbedding.subtype _).toOrderHom
  naturality {_ _} _ := rfl

end ΩIdeal

end DomainSemantics.Presheaf

namespace DomainSemantics.Presheaf

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C]
variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y : C}

@[simp]
theorem ΩIdeal.val_presheaf_map (I : ΩIdeal R X) (f : Y ⟶ X) :
    (I.pullback f).val = I.val.pullback f := rfl

@[simp]
theorem ΩIdeal.val_principal (a : R.obj (op X)) :
    (principal R a).val = ΩLower.principal R a := rfl

@[simp]
theorem ΩLower.val_toIdeal (L : ΩLower R X) (hL : L.IsDirected) :
    (L.toIdeal hL).val = L := rfl

end DomainSemantics.Presheaf
