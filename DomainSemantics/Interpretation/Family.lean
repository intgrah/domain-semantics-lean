/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Join
public import DomainSemantics.Presheaf.Approximation
import Mathlib.Algebra.GroupWithZero.Nat

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory MonoidalCategory Opposite Presheaf

abbrev RawValuation (Γ : Ctx) := ℕ → RawValue Γ

namespace RawValuation

variable {Γ Γ₁ Γ₂ : Ctx}

noncomputable def pullback (ρ : RawValuation Γ) (σ : Γ₁ ⟶ Γ) : RawValuation Γ₁ :=
  fun i ↦ (ρ i).pullback σ

def push (ρ : RawValuation Γ) (I : RawValue Γ) : RawValuation Γ
  | 0 => I
  | i + 1 => ρ i

def tail (ρ : RawValuation Γ) : RawValuation Γ := fun i ↦ ρ (i + 1)

def replace (ρ : RawValuation Γ) (i : ℕ) (I : RawValue Γ) : RawValuation Γ :=
  Function.update ρ i I

@[simp]
theorem replace_same (ρ : RawValuation Γ) (i : ℕ) (I : RawValue Γ) :
    (ρ.replace i I) i = I := by
  simp [replace]

@[simp]
theorem replace_ne (ρ : RawValuation Γ) {i j : ℕ} (h : j ≠ i) (I : RawValue Γ) :
    (ρ.replace i I) j = ρ j := by
  simp [replace, h]

@[simp]
theorem tail_push (ρ : RawValuation Γ) (I : RawValue Γ) : (ρ.push I).tail = ρ := rfl

@[simp]
theorem pullback_id (ρ : RawValuation Γ) : ρ.pullback (𝟙 Γ) = ρ :=
  funext fun i => ΩLower.pullback_id (ρ i)

theorem pullback_comp (ρ : RawValuation Γ) (σ : Γ₁ ⟶ Γ) (σ₁ : Γ₂ ⟶ Γ₁) :
    (ρ.pullback σ).pullback σ₁ = ρ.pullback (σ₁ ≫ σ) :=
  funext fun i => ΩLower.pullback_pullback (ρ i) σ σ₁

@[simp]
theorem pullback_push (ρ : RawValuation Γ) (I : RawValue Γ) (σ : Γ₁ ⟶ Γ) :
    (ρ.push I).pullback σ = (ρ.pullback σ).push (I.pullback σ) := by
  funext i
  cases i <;> rfl

@[simp]
theorem pullback_tail (ρ : RawValuation Γ) (σ : Γ₁ ⟶ Γ) :
    ρ.tail.pullback σ = (ρ.pullback σ).tail := rfl

@[simp]
theorem replace_zero_push (ρ : RawValuation Γ) (I J : RawValue Γ) :
    (ρ.push J).replace 0 I = ρ.push I := by
  funext i
  cases i <;> simp [replace, push]

@[simp]
theorem push_replace (ρ : RawValuation Γ) (i : ℕ) (I J : RawValue Γ) :
    (ρ.replace i I).push J = (ρ.push J).replace (i + 1) I := by
  funext j
  cases j <;> simp [replace, push, Function.update_apply]

theorem pullback_mono {ρ : RawValuation Γ} (h : ρ ≤ ρ') (σ : Γ₁ ⟶ Γ) :
    ρ.pullback σ ≤ ρ'.pullback σ :=
  fun i ↦ ΩLower.pullback_mono (h i) σ

theorem push_mono {ρ : RawValuation Γ} {I I' : RawValue Γ}
    (hρ : ρ ≤ ρ') (hI : I ≤ I') : ρ.push I ≤ ρ'.push I'
  | 0 => hI
  | i + 1 => hρ i

theorem replace_mono {ρ : RawValuation Γ} {I I' : RawValue Γ} (i : ℕ)
    (hρ : ρ ≤ ρ') (hI : I ≤ I') : ρ.replace i I ≤ ρ'.replace i I' :=
  update_le_update_iff.mpr ⟨hI, fun j _ => hρ j⟩

@[implicit_reducible, simps! obj map_hom_coe] noncomputable def presheaf : Ctxᵒᵖ ⥤ Preord where
  obj Γ₁ := Preord.of (RawValuation Γ₁.unop)
  map σ₁ := Preord.ofHom {
    toFun := fun ρ => ρ.pullback σ₁.unop
    monotone' := fun _ _ h => pullback_mono h σ₁.unop }
  map_id _ := Preord.ext pullback_id
  map_comp σ₁ σ₂ := Preord.ext fun ρ => (pullback_comp ρ σ₁.unop σ₂.unop).symm

noncomputable def pushHom : presheaf ⊗ ΩLower.presheaf pointedOrder ⟶ presheaf where
  app _ := Preord.ofHom {
    toFun := fun (ρ, I) => ρ.push I
    monotone' _ _ h := push_mono h.1 h.2 }
  naturality _ _ σ := Preord.ext fun (ρ, I) => (pullback_push ρ I σ.unop).symm

end RawValuation

abbrev RawFamily (Γ₁ : Ctx) :=
  (RawValuation.presheaf.functorHom (ΩLower.presheaf pointedOrder)).obj (op Γ₁)

namespace RawFamily

noncomputable abbrev presheaf := RawValuation.presheaf.functorHom (ΩLower.presheaf pointedOrder)

noncomputable def pullback {Γ Γ₁ : Ctx} (F : RawFamily Γ) (σ : Γ₁ ⟶ Γ) : RawFamily Γ₁ := presheaf.map σ.op F

noncomputable instance : CompleteLattice (RawFamily Γ) :=
  inferInstanceAs (CompleteLattice (Functor.HomObj _ _ _))

variable {Γ Γ₁ Γ₂ : Ctx}

@[simp] theorem app_pullback (F : RawFamily Γ) {Γ₁ : Ctxᵒᵖ} {Γ₂ : Ctx}
    (σ₁ : op Γ ⟶ Γ₁) (σ₂ : Γ₂ ⟶ Γ₁.unop) (ρ : RawValuation Γ₁.unop) :
    (F.app Γ₁ σ₁ ρ).pullback σ₂ =
      F.app (op Γ₂) (σ₁ ≫ σ₂.op) (ρ.pullback σ₂) :=
  (F.naturality_apply σ₂.op σ₁ ρ).symm

def IsFinitary (F : RawFamily Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (i : ℕ) (ρ : RawValuation Γ₁),
    ΩLower.IsFinitary (fun I => F.app _ σ.op (ρ.replace i I))

theorem IsFinitary.eventually {F : RawFamily Γ} (hF : F.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (i : ℕ) (ρ : RawValuation Γ₁) (I : RawValue Γ₁)
    {y : CoherentShape Γ₁} (hy : (F.app _ σ.op (ρ.replace i I)).mem (𝟙 Γ₁) y) :
    ∀ᶠ J in I.approximations, (F.app _ σ.op (ρ.replace i J)).mem (𝟙 Γ₁) y :=
  (hF σ i ρ).eventually
    ((F.app _ σ.op).hom.monotone.comp (Function.update_mono (f := ρ) (i := i)))
    ΩLower.eventually_mem hy

@[simps! app_hom_coe] noncomputable def lookup (i : ℕ) : RawFamily Γ where
  app _ _ := Preord.ofHom (Pi.evalOrderHom i)
  naturality _ _ := rfl

@[simps! app_hom_coe] noncomputable def constant (I : RawValue Γ) : RawFamily Γ where
  app _ σ₁ := Preord.ofHom (OrderHom.const _ (I.pullback σ₁.unop))
  naturality σ₂ σ₁ := Preord.ext fun _ =>
    (ΩLower.pullback_pullback I σ₁.unop σ₂.unop).symm

theorem bottom_isFinitary : (⊥ : RawFamily Γ).IsFinitary :=
  fun _ _ _ => ΩLower.IsFinitary.const _

theorem constant_isFinitary (I : RawValue Γ) : (constant I).IsFinitary :=
  fun _ _ _ => ΩLower.IsFinitary.const _

theorem IsFinitary.pullback {F : RawFamily Γ} (hF : F.IsFinitary)
    (σ : Γ₁ ⟶ Γ) : IsFinitary (presheaf.map σ.op F) :=
  fun σ₁ => hF (σ₁ ≫ σ)

theorem lookup_isFinitary (i : ℕ) : (lookup i : RawFamily Γ).IsFinitary := by
  intro Γ₁ σ j ρ
  change ΩLower.IsFinitary (fun I => (ρ.replace j I) i)
  by_cases h : i = j
  · subst j
    simpa using ΩLower.IsFinitary.id
  · simpa [h] using ΩLower.IsFinitary.const (ρ i)

end RawFamily

end DomainSemantics.CoherentShape
