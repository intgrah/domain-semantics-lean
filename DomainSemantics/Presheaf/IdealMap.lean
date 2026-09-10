/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Presheaf.Ideal

@[expose] public section

universe u v

namespace DomainSemantics.Presheaf

open CategoryTheory MonoidalCategory Opposite

variable {C : Type u} [Category.{v} C]

namespace ΩLower

variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {S : Cᵒᵖ ⥤ CondSemilatSup.{max u v}}
variable {T : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {U : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y : C}

def pair (I : ΩLower R X) (J : ΩLower S X) : ΩLower (R ⊗ S) X where
  mem f := fun (a, b) => I.mem f a ∧ J.mem f b
  natural f g := fun (a, b) ⟨ha, hb⟩ => ⟨I.natural f g a ha, J.natural f g b hb⟩
  bottom f := ⟨I.bottom f, J.bottom f⟩
  lower f := fun ⟨ha, hb⟩ ⟨ha', hb'⟩ => ⟨I.lower f ha ha', J.lower f hb hb'⟩

theorem IsDirected.pair {I : ΩLower R X} {J : ΩLower S X}
    (hI : I.IsDirected) (hJ : J.IsDirected) : (I.pair J).IsDirected := by
  intro Y f a b ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
  have ⟨c, hc, hac, hbc⟩ := hI f ha₁ hb₁
  have ⟨d, hd, had, hbd⟩ := hJ f ha₂ hb₂
  exact ⟨(c, d), ⟨hc, hd⟩, ⟨hac, had⟩, ⟨hbc, hbd⟩⟩

theorem pair_mono {I I' : ΩLower R X} {J J' : ΩLower S X}
    (hI : I ≤ I') (hJ : J ≤ J') : I.pair J ≤ I'.pair J' :=
  fun f (a, b) ⟨ha, hb⟩ => ⟨hI f a ha, hJ f b hb⟩

def bind (I : ΩLower R X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) : ΩLower S X where
  mem f b := ∃ a, I.mem f a ∧ (F.app _ ⟨f⟩ a).mem (𝟙 _) b
  natural f g b := fun ⟨a, ha, hb⟩ =>
    ⟨R.map g.op a, I.natural f g a ha, (homObj_app_map_mem F g.op ⟨f⟩ a (𝟙 _) _).mpr
      (by simpa using (F.app _ ⟨f⟩ a).natural (𝟙 _) g b hb)⟩
  bottom f := ⟨(⊥ : R.obj (op _)), I.bottom f, (F.app _ ⟨f⟩ (⊥ : R.obj (op _))).bottom _⟩
  lower f h := fun ⟨a, ha, hb⟩ => ⟨a, ha, (F.app _ ⟨f⟩ a).lower _ h hb⟩

@[simp] theorem mem_bind (I : ΩLower R X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) (f : Y ⟶ X) (b : S.obj (op Y)) :
    (I.bind F).mem f b ↔ ∃ a, I.mem f a ∧ (F.app (op Y) ⟨f⟩ a).mem (𝟙 Y) b := Iff.rfl

theorem IsDirected.bind {I : ΩLower R X} (hI : I.IsDirected)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) (hF : ∀ Y f a, (F.app Y f a).IsDirected) :
    (I.bind F).IsDirected := by
  intro Y f a b ⟨a₁, ha₁, ha⟩ ⟨a₂, ha₂, hb⟩
  have ⟨c, hc, h₁, h₂⟩ := hI f ha₁ ha₂
  have ⟨d, hd, had, hbd⟩ := hF (op Y) ⟨f⟩ c (𝟙 Y)
    ((F.app (op Y) ⟨f⟩).hom.monotone h₁ _ _ ha)
    ((F.app (op Y) ⟨f⟩).hom.monotone h₂ _ _ hb)
  exact ⟨d, ⟨c, hc, hd⟩, had, hbd⟩

@[simp] theorem bind_principal (a : R.obj (op X))
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) :
    (principal R a).bind F = F.app (op X) ⟨𝟙 X⟩ a := by
  ext Y f b
  have h : (F.app (op Y) ⟨f⟩ (R.map f.op a)).mem (𝟙 Y) b ↔
      (F.app (op X) ⟨𝟙 X⟩ a).mem f b := by
    have h := congrArg (fun L : ΩLower S Y => L.mem (𝟙 Y) b)
      (F.naturality_apply f.op ⟨𝟙 X⟩ a)
    change (F.app (op Y) ⟨f ≫ 𝟙 X⟩ (R.map f.op a)).mem (𝟙 Y) b =
      ((F.app (op X) ⟨𝟙 X⟩ a).pullback f).mem (𝟙 Y) b at h
    simpa using h
  rw [mem_bind, ← h]
  exact ⟨fun ⟨c, hc, hb⟩ => (F.app (op Y) ⟨f⟩).hom.monotone
    ((mem_principal a f c).mp hc) _ _ hb,
    fun hb => ⟨R.map f.op a, (mem_principal a f _).mpr le_rfl, hb⟩⟩

theorem bind_mono {I I' : ΩLower R X}
    {F F' : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) (uliftYoneda.{u}.obj X)}
    (hI : I ≤ I') (hF : ∀ Y f a, F.app Y f a ≤ F'.app Y f a) : I.bind F ≤ I'.bind F' :=
  fun {Y} f b ⟨a, ha, hb⟩ => ⟨a, hI f a ha, hF (op Y) ⟨f⟩ a (𝟙 Y) b hb⟩

@[simp] theorem pullback_bind (I : ΩLower R X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) (uliftYoneda.{u}.obj X))
    (f : Y ⟶ X) :
    (I.bind F).pullback f = (I.pullback f).bind (F.map (uliftYoneda.map f)) := by
  ext
  rw [presheaf_map_mem, mem_bind, mem_bind]
  rfl

def bind₂ (I : ΩLower R X) (J : ΩLower S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : ΩLower T X :=
  (I.pair J).bind F

@[simp] theorem mem_bind₂ (I : ΩLower R X) (J : ΩLower S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) (f : Y ⟶ X) (c : T.obj (op Y)) :
    (bind₂ I J F).mem f c ↔ ∃ a b, I.mem f a ∧ J.mem f b ∧
      (F.app (op Y) ⟨f⟩ (a, b)).mem (𝟙 Y) c :=
  ⟨fun ⟨(a, b), ⟨ha, hb⟩, hc⟩ => ⟨a, b, ha, hb, hc⟩,
    fun ⟨a, b, ha, hb, hc⟩ => ⟨(a, b), ⟨ha, hb⟩, hc⟩⟩

theorem IsDirected.bind₂ {I : ΩLower R X} {J : ΩLower S X} (hI : I.IsDirected) (hJ : J.IsDirected)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X))
    (hF : ∀ Y f p, (F.app Y f p).IsDirected) : (bind₂ I J F).IsDirected :=
  IsDirected.bind (IsDirected.pair hI hJ) F hF

theorem bind₂_mono {I I' : ΩLower R X} {J J' : ΩLower S X} (hI : I ≤ I') (hJ : J ≤ J')
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : bind₂ I J F ≤ bind₂ I' J' F :=
  bind_mono (pair_mono hI hJ) (fun _ _ _ {_} _ _ h => h)

variable (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (S ⋙ forget₂ CondSemilatSup Preord)
    (uliftYoneda.{u}.obj X))

def map (I : ΩLower R X) : ΩLower S X :=
  I.bind (F.comp (.ofNatTrans (principalNatTrans S)))

@[simp] theorem mem_map (I : ΩLower R X) (f : Y ⟶ X) (b : S.obj (op Y)) :
    (I.map F).mem f b ↔ ∃ a, I.mem f a ∧ b ≤ F.app (op Y) ⟨f⟩ a := by
  rw [map, mem_bind]
  change (∃ a, I.mem f a ∧ (principal S (F.app (op Y) ⟨f⟩ a)).mem (𝟙 Y) b) ↔ _
  simp

theorem IsDirected.map {I : ΩLower R X} (hI : I.IsDirected) : (I.map F).IsDirected :=
  hI.bind _ fun _ f a => isDirected_principal (F.app _ f a)

theorem map_mono {I J : ΩLower R X} (h : I ≤ J) : I.map F ≤ J.map F :=
  bind_mono h fun _ _ _ _ _ _ h => h

@[simp]
theorem pullback_map (I : ΩLower R X) (f : Y ⟶ X) :
    (I.map F).pullback f = (I.pullback f).map (F.map (uliftYoneda.map f)) := by
  ext
  rw [presheaf_map_mem, mem_map, mem_map]
  rfl

theorem map_principal (a : R.obj (op X)) :
    (principal R a).map F =
      principal S (F.app (op X) ⟨𝟙 X⟩ a) := by
  rw [map, bind_principal]
  rfl

@[simp] theorem map_id (I : ΩLower R X) : I.map (.id _) = I := by
  ext Y f a
  rw [mem_map]
  exact ⟨fun ⟨b, hb, hab⟩ => I.lower f hab hb, fun ha => ⟨a, ha, le_rfl⟩⟩

@[simp] theorem map_map (I : ΩLower R X)
    (G : Functor.HomObj (S ⋙ forget₂ CondSemilatSup Preord)
      (T ⋙ forget₂ CondSemilatSup Preord) (uliftYoneda.{u}.obj X)) :
    (I.map F).map G = I.map (F.comp G) := by
  ext Y f c
  simp
  exact ⟨fun ⟨b, ⟨a, ha, hab⟩, hbc⟩ =>
    ⟨a, ha, hbc.trans ((G.app (op Y) ⟨f⟩).hom.monotone hab)⟩,
    fun ⟨a, ha, hac⟩ => ⟨F.app (op Y) ⟨f⟩ a, ⟨a, ha, le_rfl⟩, hac⟩⟩

def map₃ (G : R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord ⊗
      T ⋙ forget₂ CondSemilatSup Preord ⟶ U ⋙ forget₂ CondSemilatSup Preord)
    (I : ΩLower R X) (J : ΩLower S X) (K : ΩLower T X) : ΩLower U X :=
  map (R := R ⊗ S ⊗ T) (.ofNatTrans G) (I.pair (J.pair K))

@[simp] theorem mem_map₃
    (G : R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord ⊗
      T ⋙ forget₂ CondSemilatSup Preord ⟶ U ⋙ forget₂ CondSemilatSup Preord)
    (I : ΩLower R X) (J : ΩLower S X) (K : ΩLower T X)
    (f : Y ⟶ X) (d : U.obj (op Y)) :
    (map₃ G I J K).mem f d ↔ ∃ a b c,
      I.mem f a ∧ J.mem f b ∧ K.mem f c ∧ d ≤ G.app (op Y) (a, b, c) := by
  rw [map₃, mem_map]
  exact ⟨fun ⟨(a, b, c), ⟨ha, hb, hc⟩, hd⟩ => ⟨a, b, c, ha, hb, hc, hd⟩,
    fun ⟨a, b, c, ha, hb, hc, hd⟩ => ⟨(a, b, c), ⟨ha, hb, hc⟩, hd⟩⟩

theorem IsDirected.map₃ (G : R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord ⊗
      T ⋙ forget₂ CondSemilatSup Preord ⟶ U ⋙ forget₂ CondSemilatSup Preord)
    {I : ΩLower R X} {J : ΩLower S X} {K : ΩLower T X}
    (hI : I.IsDirected) (hJ : J.IsDirected) (hK : K.IsDirected) :
    (map₃ G I J K).IsDirected :=
  IsDirected.map (R := R ⊗ S ⊗ T) (.ofNatTrans G)
    (hI.pair (hJ.pair hK))

theorem map₃_mono
    (G : R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord ⊗
      T ⋙ forget₂ CondSemilatSup Preord ⟶ U ⋙ forget₂ CondSemilatSup Preord)
    {I I' : ΩLower R X} {J J' : ΩLower S X} {K K' : ΩLower T X}
    (hI : I ≤ I') (hJ : J ≤ J') (hK : K ≤ K') : map₃ G I J K ≤ map₃ G I' J' K' :=
  map_mono (R := R ⊗ S ⊗ T) (.ofNatTrans G)
    (pair_mono hI (pair_mono hJ hK))

@[simp]
theorem pullback_map₃
    (G : R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord ⊗
      T ⋙ forget₂ CondSemilatSup Preord ⟶ U ⋙ forget₂ CondSemilatSup Preord)
    (I : ΩLower R X) (J : ΩLower S X) (K : ΩLower T X) (f : Y ⟶ X) :
    (map₃ G I J K).pullback f =
      map₃ G (I.pullback f) (J.pullback f) (K.pullback f) := by
  ext
  rw [presheaf_map_mem, mem_map₃, mem_map₃]
  rfl

end ΩLower

namespace ΩIdeal

variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {S : Cᵒᵖ ⥤ CondSemilatSup.{max u v}}
variable {T : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {U : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y : C}

def bind₂ (I : ΩIdeal R X) (J : ΩIdeal S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : ΩIdeal T X where
  val := ΩLower.bind₂ I.val J.val (F.comp (.ofNatTrans (toLowerNatTrans T)))
  property := ΩLower.IsDirected.bind₂ I.property J.property _ fun Y f p => (F.app Y f p).property

@[simp] theorem mem_bind₂ (I : ΩIdeal R X) (J : ΩIdeal S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) (f : Y ⟶ X) (c : T.obj (op Y)) :
    (bind₂ I J F).mem f c ↔ ∃ a b, I.mem f a ∧ J.mem f b ∧
      (F.app (op Y) ⟨f⟩ (a, b)).mem (𝟙 Y) c :=
  ΩLower.mem_bind₂ _ _ _ f c

theorem bind₂_mono {I I' : ΩIdeal R X} {J J' : ΩIdeal S X} (hI : I ≤ I') (hJ : J ≤ J')
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : bind₂ I J F ≤ bind₂ I' J' F :=
  ΩLower.bind₂_mono hI hJ _

end ΩIdeal

end DomainSemantics.Presheaf
