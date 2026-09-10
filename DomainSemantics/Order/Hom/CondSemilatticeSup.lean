/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Order.CondSemilatticeSup
public import Mathlib.Order.Hom.Bounded

@[expose] public section

structure CondSemilatSup.Hom (α β : Type*) [CondSemilatticeSup α] [CondSemilatticeSup β]
    extends OrderHom α β, BotHom α β where
  map_cSup' (a b : α) (h : ∃ c, a ≤ c ∧ b ≤ c) {d : β} :
    toFun a ≤ d → toFun b ≤ d → toFun (cSup a b h) ≤ d

namespace CondSemilatSup.Hom

variable {α β γ : Type*} [CondSemilatticeSup α] [CondSemilatticeSup β] [CondSemilatticeSup γ]

instance : FunLike (Hom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

instance : OrderHomClass (Hom α β) α β where
  map_rel f := f.monotone' (b := _)

instance : BotHomClass (Hom α β) α β where
  map_bot f := f.map_bot'

@[ext] theorem ext {f g : Hom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

theorem map_le_bot (f : Hom α β) {a : α} (h : a ≤ ⊥) : f a ≤ ⊥ :=
  (f.monotone h).trans_eq (map_bot f)

def id (α : Type*) [CondSemilatticeSup α] : Hom α α where
  __ := OrderHom.id
  map_bot' := rfl
  map_cSup' _ _ h := cSup_le h

def comp (g : Hom β γ) (f : Hom α β) : Hom α γ where
  __ := g.toOrderHom.comp f.toOrderHom
  map_bot' := show g (f ⊥) = ⊥ by simp
  map_cSup' a b h {d} hga hgb :=
    have hf : ∃ c, f a ≤ c ∧ f b ≤ c :=
      h.elim fun c ⟨ha, hb⟩ => ⟨f c, f.monotone' ha, f.monotone' hb⟩
    (g.monotone' (f.map_cSup' a b h (le_cSup_left _ _ hf) (le_cSup_right _ _ hf))).trans
      (g.map_cSup' (f a) (f b) hf hga hgb)

end CondSemilatSup.Hom
