/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.UniverseShape
public import DomainSemantics.Domain.Constructors
public import DomainSemantics.Domain.Decoder.Operator

@[expose] public section

namespace DomainSemantics.CoherentShape

variable {Γ Γ₁ : Ctx}

def IsCode (r : Bool) (a : CoherentShape Γ) : Prop := Shape.IsCode r a.1

namespace IsCode

theorem of_le {r : Bool} {a b : CoherentShape Γ} (h : a ≤ b) (hb : IsCode r b) : IsCode r a :=
  Shape.IsCode.of_le h hb

theorem reindex {r : Bool} (σ : Γ₁ ⟶ Γ) {a : CoherentShape Γ} (h : IsCode r a) :
    IsCode r (reindex σ a) :=
  h.map _ _

theorem bottom {r : Bool} : IsCode r (⊥ : CoherentShape Γ) := Shape.IsCode.bot

end IsCode

theorem isCode_natAtom : IsCode true (natAtom : CoherentShape Γ) := .nat

theorem isCode_identityMap (r : Bool) (A a b : CoherentShape Γ) : IsCode r (identityMap A a b) :=
  .id

def universeLower (r : Bool) (X : Domain Γ) : Presheaf.ΩLower pointedOrder Γ where
  mem σ a := X.mem σ a ∧ IsCode r a
  natural σ σ₁ a := fun ⟨ha, hcode⟩ => ⟨X.natural σ σ₁ a ha, hcode.reindex σ₁⟩
  bottom σ := ⟨X.bottom σ, IsCode.bottom⟩
  lower σ hab := fun ⟨hb, hcode⟩ => ⟨X.lower σ hab hb, hcode.of_le hab⟩

theorem mem_universeLower (r : Bool) (X : Domain Γ) (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁) :
    (universeLower r X).mem σ y ↔ X.mem σ y ∧ IsCode r y := Iff.rfl

def universeIdeal (r : Bool) (X : Domain Γ) : Domain Γ where
  val := universeLower r X
  property := by
    intro Γ₁ σ a b ⟨ha, hacode⟩ ⟨hb, hbcode⟩
    have ⟨c, hc, hac, hbc⟩ := X.property σ ha hb
    have hab := Compatible.of_common_upper hac hbc
    exact ⟨sup a b hab, ⟨X.lower σ (sup_le hab hac hbc) hc,
      Shape.IsCode.cSup hacode hbcode⟩, le_sup hab⟩

@[simp]
theorem mem_universeIdeal_iff (r : Bool) (X : Domain Γ)
    (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁) :
    (universeIdeal r X).mem σ y ↔ X.mem σ y ∧ IsCode r y :=
  mem_universeLower r X σ y

theorem universeIdeal_le (r : Bool) (X : Domain Γ) :
    universeIdeal r X ≤ X :=
  fun _ {σ} y hy => ((mem_universeIdeal_iff r X σ y).mp hy).1

theorem universeIdeal_mono {X Y : Domain Γ} (r : Bool) (h : X ≤ Y) :
    universeIdeal r X ≤ universeIdeal r Y :=
  fun σ z ⟨hz, hcode⟩ => ⟨h σ z hz, hcode⟩

theorem universeIdeal_eq_self_iff (r : Bool) {X : Domain Γ} :
    universeIdeal r X = X ↔ ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁), X.mem σ y → IsCode r y := by
  constructor
  · intro h Γ₁ σ y hy
    exact ((mem_universeIdeal_iff r X σ y).mp (by rw [h]; exact hy)).2
  · intro h
    apply le_antisymm
    · exact universeIdeal_le r X
    · intro Γ₁ σ y hy
      exact (mem_universeIdeal_iff r X σ y).mpr ⟨hy, h σ y hy⟩

@[simp]
theorem universeIdeal_bottom (r : Bool) : universeIdeal r (bottomIdeal Γ) = bottomIdeal Γ :=
  le_antisymm
    (fun {_} => universeIdeal_le r (bottomIdeal Γ))
    (fun {_} => IdealOperator.bottomIdeal_le _)

theorem universeIdeal_idempotent (r : Bool) (X : Domain Γ) :
    universeIdeal r (universeIdeal r X) = universeIdeal r X :=
  (universeIdeal_eq_self_iff r).mpr fun σ y hy => ((mem_universeIdeal_iff r X σ y).mp hy).2

theorem universeIdeal_principal {r : Bool} {a : CoherentShape Γ} (h : IsCode r a) :
    universeIdeal r (principalIdeal a) = principalIdeal a :=
  (universeIdeal_eq_self_iff r).mpr fun σ y hy =>
    IsCode.of_le ((principalIdeal_mem a σ y).mp hy) (h.reindex σ)

theorem pullback_universeIdeal (r : Bool) (X : Domain Γ) (σ : Γ₁ ⟶ Γ) :
    (universeIdeal r X).pullback σ = universeIdeal r (X.pullback σ) := by
  ext Γ₂ σ₁ y
  rw [Presheaf.ΩIdeal.presheaf_map_mem, mem_universeIdeal_iff, mem_universeIdeal_iff,
    Presheaf.ΩIdeal.presheaf_map_mem]

noncomputable def universeOperator (r : Bool) : IdealOperator Γ where
  val.app _ _ := Preord.ofHom {
    toFun := universeIdeal r
    monotone' _ _ h := universeIdeal_mono r h }
  val.naturality σ₁ _ := Preord.ext fun X => (pullback_universeIdeal r X σ₁.unop).symm
  property := by
    intro Γ₁ σ₁ X z hz
    have ⟨hz, hcode⟩ := (mem_universeIdeal_iff _ _ _ _).mp hz
    exact ⟨z, hz, (mem_universeIdeal_iff _ _ _ _).mpr ⟨by simp, hcode⟩⟩

theorem universeIdeal_type_sort (s : Bool) :
    universeIdeal true (principalIdeal (sortAtom s : CoherentShape Γ)) =
      principalIdeal (sortAtom s) :=
  universeIdeal_principal .sort

end DomainSemantics.CoherentShape
