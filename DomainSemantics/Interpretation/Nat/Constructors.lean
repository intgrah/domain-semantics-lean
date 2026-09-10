/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Family
public import DomainSemantics.Domain.Constructors

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}

namespace RawFamily

noncomputable def nat : RawFamily Γ := constant (principalIdeal natAtom).val

noncomputable def zero : RawFamily Γ := constant (principalIdeal zeroAtom).val

@[simp]
theorem nat_value (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (nat : RawFamily Γ).app _ σ.op ρ = (principalIdeal (natAtom : CoherentShape Γ₁)).val :=
  ΩLower.presheaf_map_principal (R := pointedOrder) natAtom σ

@[simp]
theorem zero_value (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (zero : RawFamily Γ).app _ σ.op ρ =
      (principalIdeal (zeroAtom : CoherentShape Γ₁)).val :=
  ΩLower.presheaf_map_principal (R := pointedOrder) zeroAtom σ

theorem nat_isFinitary : (nat : RawFamily Γ).IsFinitary := constant_isFinitary _

theorem zero_isFinitary : (zero : RawFamily Γ).IsFinitary := constant_isFinitary _

noncomputable def succHom : Functor.HomObj (ΩLower.presheaf pointedOrder)
    (ΩLower.presheaf pointedOrder) Tm.presheaf where
  app _ label := Preord.ofHom {
    toFun := RawValue.succ label
    monotone' := fun _ _ => RawValue.succ_mono label }
  naturality σ label := Preord.ext fun I => (RawValue.pullback_succ label I σ.unop).symm

noncomputable def succ (label : Σ A : Ty Γ, Tm Γ A) (X : RawFamily Γ) : RawFamily Γ :=
  X.comp (succHom.map (coyonedaEquiv.symm label))

@[simp] theorem succ_value (label : Σ A : Ty Γ, Tm Γ A) (X : RawFamily Γ)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (succ label X).app _ σ.op ρ = RawValue.succ (Tm.presheaf.map σ.op label) (X.app _ σ.op ρ) :=
  rfl

theorem IsFinitary.succ {X : RawFamily Γ} (hX : X.IsFinitary)
    (label : Σ A : Ty Γ, Tm Γ A) : (succ label X).IsFinitary := by
  intro Γ₁ σ i ρ I y hy
  have ⟨x, hx, hy⟩ := (RawValue.mem_succ _ _ _ _).mp hy
  have ⟨l, hl, hx⟩ := hX σ i ρ I hx
  exact ⟨l, hl, (RawValue.mem_succ _ _ _ _).mpr ⟨x, hx, hy⟩⟩

end RawFamily

end DomainSemantics.CoherentShape
