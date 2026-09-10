/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Intrinsic
public import DomainSemantics.Basis.Order

@[expose] public section

namespace DomainSemantics.Shape

open CategoryTheory Opposite

noncomputable abbrev reindexHom {Γ₁ Γ₂ : Ctx} (σ₁ : Γ₁ ⟶ Γ₂) : Shape Γ₂ → Shape Γ₁ :=
  map (Tm.presheaf.map σ₁.op) (Ty.pairPresheaf.map σ₁.op)

@[simp] theorem reindexHom_id {Γ₁ : Ctx} (a : Shape Γ₁) : a.reindexHom (𝟙 Γ₁) = a := by
  induction a <;> simp_all [reindexHom, map]

theorem reindexHom_comp {Γ₁ Γ₂ : Ctx} (σ₁ : Γ₁ ⟶ Γ₂) (σ₂ : Γ₃ ⟶ Γ₁) (a : Shape Γ₂) :
    a.reindexHom (σ₂ ≫ σ₁) = (a.reindexHom σ₁).reindexHom σ₂ := by
  induction a <;> simp_all [reindexHom, map]

@[implicit_reducible] noncomputable def presheaf : Ctxᵒᵖ ⥤ Type where
  obj Γ₁ := Shape Γ₁.unop
  map σ₁ := ↾reindexHom σ₁.unop
  map_id _ := ConcreteCategory.hom_ext _ _ reindexHom_id
  map_comp σ₁ σ₂ := ConcreteCategory.hom_ext _ _ (reindexHom_comp σ₁.unop σ₂.unop)

end DomainSemantics.Shape

namespace DomainSemantics.Graph

open CategoryTheory Opposite

noncomputable abbrev reindexHom {Γ₁ Γ₂ : Ctx} (σ₁ : Γ₁ ⟶ Γ₂) : Graph Γ₂ → Graph Γ₁ :=
  map (Tm.presheaf.map σ₁.op) (Ty.pairPresheaf.map σ₁.op)

@[simp] theorem reindexHom_id {Γ₁ : Ctx} (f : Graph Γ₁) : f.reindexHom (𝟙 Γ₁) = f := by
  have h := Shape.reindexHom_id (Γ₁ := Γ₁)
  simp [Shape.reindexHom] at h
  simp [reindexHom, map, h]

theorem reindexHom_comp {Γ₁ Γ₂ : Ctx} (σ₁ : Γ₁ ⟶ Γ₂) (σ₂ : Γ₃ ⟶ Γ₁) (f : Graph Γ₂) :
    f.reindexHom (σ₂ ≫ σ₁) = (f.reindexHom σ₁).reindexHom σ₂ := by
  have h := Shape.reindexHom_comp σ₁ σ₂
  simp [Shape.reindexHom] at h
  simp [reindexHom, map, h]

end DomainSemantics.Graph
