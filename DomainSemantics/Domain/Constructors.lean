/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Join
public import DomainSemantics.Presheaf.IdealMap

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory MonoidalCategory Presheaf

variable {Γ Γ₁ : Ctx}

noncomputable def identityHom : order ⊗ order ⊗ order ⟶ order where
  app _ := Preord.ofHom {
    toFun := fun (a, x, y) => identityMap a x y
    monotone' := fun _ _ ⟨ha, hx, hy⟩ => .id ha hx hy }
  naturality _ _ _ := rfl

def sortAtom (r : Bool) : CoherentShape Γ := ⟨.sort r, .sort⟩

def natAtom : CoherentShape Γ := ⟨.nat, .nat⟩

def zeroAtom : CoherentShape Γ := ⟨.zero, .zero⟩

theorem sortAtom_le_iff {u v : Bool} : (sortAtom u : CoherentShape Γ) ≤ sortAtom v ↔ u = v :=
  ⟨Basis.LE.sort_inv, fun h => h ▸ .sort u⟩

def succMap (label : Σ A : Ty Γ, Tm Γ A) (a : CoherentShape Γ) : CoherentShape Γ :=
  ⟨.succ label a.1, .succ a.2⟩

theorem succMap_mono (label : Σ A : Ty Γ, Tm Γ A) {a b : CoherentShape Γ} (h : a ≤ b) :
    succMap label a ≤ succMap label b :=
  .succ h

@[simps! app_hom_coe] noncomputable def succHom (label : Σ A : Ty Γ, Tm Γ A) :
    Functor.HomObj order order (uliftYoneda.obj Γ) where
  app _ σ₁ := Preord.ofHom {
    toFun := succMap (Tm.presheaf.map σ₁.down.op label)
    monotone' _ _ h := succMap_mono _ h }
  naturality σ₂ σ₁ := by
    ext a
    exact congrArg (fun label => succMap label (reindex σ₂.unop a))
      (Tm.presheaf.map_comp_apply σ₁.down.op σ₂ label)

namespace RawValue

noncomputable def succ (label : Σ A : Ty Γ, Tm Γ A) (X : RawValue Γ) : RawValue Γ :=
  X.map (succHom label)

@[simp] theorem mem_succ {Γ₁ Γ₂ : Ctx} (label : Σ A : Ty Γ₂, Tm Γ₂ A)
    (X : RawValue Γ₂) (σ₁ : Γ₁ ⟶ Γ₂) (y : CoherentShape Γ₁) :
    (succ label X).mem σ₁ y ↔ ∃ x, X.mem σ₁ x ∧
      y ≤ succMap (Tm.presheaf.map σ₁.op label) x :=
  ΩLower.mem_map
    (succHom label) X σ₁ y

theorem succ_mono (label : Σ A : Ty Γ, Tm Γ A) {X Y : RawValue Γ} (h : X ≤ Y) :
    succ label X ≤ succ label Y :=
  ΩLower.map_mono (succHom label) h

@[simp]
theorem pullback_succ (label : Σ A : Ty Γ, Tm Γ A) (X : RawValue Γ) (σ : Γ₁ ⟶ Γ) :
    (succ label X).pullback σ =
      succ (Tm.presheaf.map σ.op label) (X.pullback σ) := by
  change (_ : RawValue Γ₁) = _
  ext Γ₂ σ₁ y
  rw [ΩLower.presheaf_map_mem, mem_succ, mem_succ,
    op_comp, Functor.map_comp_apply]
  rfl

theorem succ_isDirected (label : Σ A : Ty Γ, Tm Γ A) {X : RawValue Γ}
    (hX : X.IsDirected) : (succ label X).IsDirected :=
  ΩLower.IsDirected.map
    (succHom label) hX

end RawValue

noncomputable def succIdeal (label : Σ A : Ty Γ, Tm Γ A) (I : Domain Γ) : Domain Γ :=
  ⟨RawValue.succ label I.val, RawValue.succ_isDirected label I.property⟩

end DomainSemantics.CoherentShape
