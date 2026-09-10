/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation
public import DomainSemantics.Domain.Decoder.PiStages
import DomainSemantics.Domain.Decoder.DecoderStrictness
import DomainSemantics.Domain.Decoder.PiFixedPoint

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory

variable {Γ Γ₁ : Ctx} {A B a b C x h : Term} {u v : Bool}
variable (D : CodeAssignment)

theorem rawInterpret_sort_fixed (r : Bool) (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    CodeAssignment.piLimit.rawExtend
      ((rawInterpret CodeAssignment.piLimit Γ (.sort true)).app _ σ.op ρ)
      ((rawInterpret CodeAssignment.piLimit Γ (.sort r)).app _ σ.op ρ) =
      (rawInterpret CodeAssignment.piLimit Γ (.sort r)).app _ σ.op ρ := by
  change CodeAssignment.piLimit.rawExtend ((RawFamily.sort true).app _ σ.op ρ)
    ((RawFamily.sort r).app _ σ.op ρ) = (RawFamily.sort r).app _ σ.op ρ
  rw [RawFamily.sort_value, RawFamily.sort_value]
  rw [CodeAssignment.rawExtend_toLower, CodeAssignment.piLimit_extend_sort,
    universeIdeal_type_sort]

theorem rawInterpret_refl_fixed (T : RawValue Γ₁) (a : Term)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    CodeAssignment.piLimit.rawExtend T
      ((rawInterpret CodeAssignment.piLimit Γ (.refl a)).app _ σ.op ρ) =
      (rawInterpret CodeAssignment.piLimit Γ (.refl a)).app _ σ.op ρ :=
  CodeAssignment.rawExtend_bottom_payload CodeAssignment.piLimit_isPayloadStrict T

theorem rawInterpret_lam (hA : Γ.as.terms ⊢ A : .sort u) :
    rawInterpret D Γ (.lam A b) =
      RawFamily.abstraction D (Ctx.rawDisplay hA) (rawInterpret D Γ A)
        (rawInterpret D (Ctx.extension Γ hA) b) := by
  rw [rawInterpret]
  exact RawFamily.iSup_eq ⟨u, hA⟩ fun ⟨_, hA'⟩ => by
    dsimp only
    rw [Ctx.rawDisplay_congr hA' hA]
    rfl

theorem rawInterpret_forallE
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v) :
    rawInterpret D Γ (.forallE A B) =
      RawFamily.pi D (Ctx.rawDisplay hA) (Ty.pairOfTyping Γ.as.wf hA hB)
        (rawInterpret D Γ A) (rawInterpret D (Ctx.extension Γ hA) B) := by
  rw [rawInterpret]
  exact RawFamily.iSup_eq ⟨(u, v), hA, hB⟩ fun ⟨_, hA', hB'⟩ => by
    dsimp only
    rw [Ty.pairOfTyping_congrWitness Γ.as.wf hA' hB' hA hB, Ctx.rawDisplay_congr hA' hA]
    rfl

theorem rawInterpret_tr
    (hA : Γ.as.terms ⊢ A : .sort u) (hb : Γ.as.terms ⊢ b : A) :
    rawInterpret D Γ (.tr A a b C x h) =
      RawFamily.decode D
        (RawFamily.instantiate (rawInterpret D (Ctx.extension Γ hA) C)
          (Raw.ContextSection.ofTerm hA hb).hom (rawInterpret D Γ b))
        (rawInterpret D Γ x) := by
  rw [rawInterpret]
  exact RawFamily.iSup_eq ⟨u, hA, hb⟩ fun ⟨_, hA', hb'⟩ => by
    dsimp only

    rfl

theorem mem_piAtom_rawInterpret_forallE_iff
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) {label : Σ A : Ty Γ₁, Ty (Γ₁.extend A)} :
    ((rawInterpret D Γ (.forallE A B)).app _ σ.op ρ).mem (𝟙 Γ₁) (piAtom label) ↔
      label = Ty.pairPresheaf.map σ.op
        (Ty.pairOfTyping Γ.as.wf hA hB) := by
  rw [rawInterpret_forallE D hA hB, RawFamily.mem_piAtom_pi_value_iff]
  simp

theorem rawInterpret_forallE_inversion
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hA' : Γ.as.terms ⊢ A' : .sort u') (hB' : A' :: Γ.as.terms ⊢ B' : .sort v')
    (ρ : RawValuation Γ)
    (heq : (rawInterpret D Γ (.forallE A B)).app _ (𝟙 Γ).op ρ =
      (rawInterpret D Γ (.forallE A' B')).app _ (𝟙 Γ).op ρ) :
    Γ.as.terms ⊢ A ≡ A' type ∧ A :: Γ.as.terms ⊢ B ≡ B' type ∧
      A' :: Γ.as.terms ⊢ B ≡ B' type := by
  have hp : ((rawInterpret D Γ (.forallE A B)).app _ (𝟙 Γ).op ρ).mem (𝟙 Γ)
      (piAtom (Ty.pairOfTyping Γ.as.wf hA hB)) := by
    apply (mem_piAtom_rawInterpret_forallE_iff D hA hB (𝟙 Γ) ρ).mpr
    simp
  rw [heq] at hp
  have hlabel := (mem_piAtom_rawInterpret_forallE_iff D hA' hB' (𝟙 Γ) ρ).mp hp
  simp at hlabel
  exact (Ty.pairOfTyping_eq_iff Γ.as.wf hA hB hA' hB').mp hlabel

end DomainSemantics.CoherentShape
