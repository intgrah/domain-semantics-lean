/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Interpretation.Computation
import DomainSemantics.Interpretation.Prop
import DomainSemantics.Interpretation.Witnesses

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

open CodeAssignment Presheaf

variable {Γ Γ₁ : Ctx} {A a b C x h : Term} {u : Bool}

theorem rawExtend_sort_identity (A a b : RawValue Γ₁) :
    piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom false))
      (RawValue.identity A a b) = RawValue.identity A a b := by
  apply le_antisymm
  · intro Γ₂ σ y hy
    exact ((mem_piLimit_rawExtend_sort_iff false _ σ y).mp hy).1
  · intro Γ₂ σ y hy
    have ⟨c, x, z, _, _, _, hy'⟩ := (RawValue.mem_identity _ _ _ _ _).mp hy
    exact (mem_piLimit_rawExtend_sort_iff false _ σ y).mpr
      ⟨hy, IsCode.of_le hy' (isCode_identityMap false c x z)⟩

namespace HasIdeality

theorem sort (Γ : Ctx) (u : Bool) : HasIdeality Γ (.sort u) :=
  fun σ ρ _ ↦ RawFamily.sort_value_isDirected u σ ρ

theorem refl (Γ : Ctx) (a : Term) : HasIdeality Γ (.refl a) :=
  fun _ _ _ ↦ ΩLower.isDirected_bot

theorem identity (hAI : HasIdeality Γ A) (haI : HasIdeality Γ a)
    (hbI : HasIdeality Γ b) : HasIdeality Γ (.id A a b) :=
  fun σ ρ hρ => ΩLower.IsDirected.map₃ identityHom (hAI σ ρ hρ) (haI σ ρ hρ) (hbI σ ρ hρ)

end HasIdeality

namespace HasFixedness

theorem sort (Γ : Ctx) (u : Bool) : HasFixedness Γ (.sort u) .type :=
  fun σ ρ _ ↦ rawInterpret_sort_fixed u σ ρ

theorem refl (Γ : Ctx) (a A : Term) : HasFixedness Γ (.refl a) A :=
  fun σ ρ _ ↦ rawInterpret_refl_fixed _ a σ ρ

theorem identity (Γ : Ctx) (A a b : Term) : HasFixedness Γ (.id A a b) .prop := by
  intro Γ₁ σ ρ hρ
  change piLimit.rawExtend ((RawFamily.sort false).app _ σ.op ρ)
    (RawValue.identity ((rawInterpret piLimit Γ A).app _ σ.op ρ)
      ((rawInterpret piLimit Γ a).app _ σ.op ρ)
      ((rawInterpret piLimit Γ b).app _ σ.op ρ)) = _
  simp
  exact rawExtend_sort_identity _ _ _

end HasFixedness

theorem rawInterpret_transport_value (hA : Γ.as.terms ⊢ A : .sort u)
    (hb : Γ.as.terms ⊢ b : A) (hAI : HasIdeality Γ A) (hbI : HasIdeality Γ b)
    (hbF : HasFixedness Γ b A) (hbR : HasRenaming Γ b)
    (hCS : HasSubstitution (Ctx.extension Γ hA) C)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret piLimit Γ (.tr A a b C x h)).app _ σ.op ρ =
      piLimit.rawExtend ((rawInterpret piLimit Γ (C[b/])).app _ σ.op ρ)
        ((rawInterpret piLimit Γ x).app _ σ.op ρ) := by
  rw [rawInterpret_tr piLimit hA hb, RawFamily.decode_app_hom_coe,
    RawFamily.instantiate_value,
    HasSubstitution.instantiate hA hb hAI hbI hbF hbR hCS σ ρ hρ]

namespace HasEquality

theorem identity {A' a' b' : Term} (hA : HasEquality Γ A A')
    (ha : HasEquality Γ a a') (hb : HasEquality Γ b b') :
    HasEquality Γ (.id A a b) (.id A' a' b') := by
  intro Γ₁ σ ρ hρ
  exact congr(RawValue.identity $(hA σ ρ hρ) $(ha σ ρ hρ) $(hb σ ρ hρ))

theorem refl_term (Γ : Ctx) (a b : Term) : HasEquality Γ (.refl a) (.refl b) :=
  fun _ _ _ ↦ rfl

theorem tr_K (hA : Γ.as.terms ⊢ A : .sort u) (hab : Γ.as.terms ⊢ a ≡ b : A)
    (hAI : HasIdeality Γ A) (haI : HasIdeality Γ a) (haF : HasFixedness Γ a A)
    (haR : HasRenaming Γ a) (habE : HasEquality Γ a b)
    (hCS : HasSubstitution (Ctx.extension Γ hA) C)
    (hxF : HasFixedness Γ x (C[a/])) : HasEquality Γ (.tr A a b C x h) x :=
  fun σ ρ hρ => rawInterpret_tr_K piLimit hA hab σ ρ (habE σ ρ hρ)
    (HasSubstitution.instantiate hA hab.hasType.1 hAI haI haF haR hCS σ ρ hρ)
    (hxF σ ρ hρ)

theorem beta (hA : Γ.as.terms ⊢ A : .sort u) (ha : Γ.as.terms ⊢ a : A)
    (hAI : HasIdeality Γ A) (hbI : HasIdeality (Ctx.extension Γ hA) b)
    (haI : HasIdeality Γ a) (haF : HasFixedness Γ a A) (haR : HasRenaming Γ a)
    (hbS : HasSubstitution (Ctx.extension Γ hA) b) :
    HasEquality Γ (.app (.lam A b) a) (b[a/]) :=
  fun σ ρ hρ => rawInterpret_beta piLimit hA ha σ ρ
    (HasIdeality.bodyAction hA hAI hbI σ ρ hρ) (haI σ ρ hρ) (haF σ ρ hρ)
    (HasSubstitution.instantiate hA ha hAI haI haF haR hbS σ ρ hρ)

theorem proofIrrel {p t t' : Term} (hp : HasFixedness Γ p .prop)
    (ht : HasFixedness Γ t p) (ht' : HasFixedness Γ t' p) : HasEquality Γ t t' :=
  fun σ ρ hρ ↦ rawInterpret_proofIrrel σ ρ (hp σ ρ hρ) (ht σ ρ hρ) (ht' σ ρ hρ)

end HasEquality

end DomainSemantics.CoherentShape
