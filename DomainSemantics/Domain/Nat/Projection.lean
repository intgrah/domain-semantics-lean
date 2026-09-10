/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.NatShape
public import DomainSemantics.Domain.Constructors
public import DomainSemantics.Domain.Decoder.Operator

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}

def natMap (a : CoherentShape Γ) : CoherentShape Γ := ⟨a.1.natProjection, a.2.natProjection⟩

theorem natMap_mono {a b : CoherentShape Γ} (h : a ≤ b) : natMap a ≤ natMap b :=
  Shape.natProjection_mono h

@[simp]
theorem natMap_idempotent (a : CoherentShape Γ) : natMap (natMap a) = natMap a :=
  Subtype.ext (Shape.natProjection_idempotent a.1)

theorem reindex_natMap (σ : Γ₁ ⟶ Γ) (a : CoherentShape Γ) :
    reindex σ (natMap a) = natMap (reindex σ a) :=
  Subtype.ext (Shape.natProjection_map _ _ a.1).symm

noncomputable def natHom : order ⟶ order where
  app _ := Preord.ofHom {
    toFun := natMap
    monotone' := fun _ _ h => natMap_mono h }
  naturality _ _ σ₁ := Preord.ext fun a =>
    (reindex_natMap σ₁.unop a).symm

namespace RawValue

noncomputable def natProjection (X : RawValue Γ) : RawValue Γ :=
  X.map (.ofNatTrans natHom)

@[simp] theorem mem_natProjection {Γ₁ Γ₂ : Ctx} (X : RawValue Γ₂)
    (σ₁ : Γ₁ ⟶ Γ₂) (y : CoherentShape Γ₁) :
    X.natProjection.mem σ₁ y ↔ ∃ x, X.mem σ₁ x ∧ y ≤ natMap x :=
  ΩLower.mem_map (.ofNatTrans natHom) X σ₁ y

theorem natProjection_le (X : RawValue Γ) : X.natProjection ≤ X := by
  intro Γ₁ σ₁ y
  rw [mem_natProjection]
  exact fun ⟨⟨x, _⟩, hx, hy⟩ => X.lower σ₁ (le_trans hy x.natProjection_le) hx

@[simp]
theorem pullback_natProjection (X : RawValue Γ) (σ : Γ₁ ⟶ Γ) :
    X.natProjection.pullback σ = natProjection (X.pullback σ) :=
  ΩLower.pullback_map (.ofNatTrans natHom) X σ

@[simp]
theorem natProjection_idempotent (X : RawValue Γ) :
    X.natProjection.natProjection = X.natProjection := by
  unfold natProjection
  rw [ΩLower.map_map]
  congr 1
  ext Γ₁ σ a
  exact natMap_idempotent a

theorem natProjection_principal (a : CoherentShape Γ) :
    natProjection (ΩLower.principal pointedOrder a) =
      ΩLower.principal pointedOrder (natMap a) :=
  ΩLower.map_principal (.ofNatTrans natHom) a

theorem natProjection_succ (label : Σ A : Ty Γ, Tm Γ A) (X : RawValue Γ) :
    (succ label X).natProjection = succ label X.natProjection := by
  unfold natProjection succ
  rw [ΩLower.map_map, ΩLower.map_map]
  rfl

end RawValue

noncomputable def natIdeal (X : Domain Γ) : Domain Γ :=
  ⟨RawValue.natProjection X.val, ΩLower.IsDirected.map _ X.property⟩

theorem natIdeal_le (X : Domain Γ) : natIdeal X ≤ X := RawValue.natProjection_le X.val

theorem natIdeal_idempotent (X : Domain Γ) : natIdeal (natIdeal X) = natIdeal X :=
  Subtype.val_injective (RawValue.natProjection_idempotent X.val)

@[simp]
theorem natIdeal_bottom : natIdeal (bottomIdeal Γ) = bottomIdeal Γ :=
  le_antisymm (fun _ => natIdeal_le _) (IdealOperator.bottomIdeal_le _)

@[simp]
theorem natIdeal_principal (a : CoherentShape Γ) :
    natIdeal (principalIdeal a) = principalIdeal (natMap a) :=
  Subtype.val_injective (RawValue.natProjection_principal a)

noncomputable def natOperator : IdealOperator Γ :=
  .ofBasis (.ofNatTrans (natHom ≫ ΩIdeal.principalNatTrans pointedOrder))

theorem natIdeal_zero : natIdeal (principalIdeal (zeroAtom : CoherentShape Γ)) =
    principalIdeal zeroAtom := natIdeal_principal _

end DomainSemantics.CoherentShape
