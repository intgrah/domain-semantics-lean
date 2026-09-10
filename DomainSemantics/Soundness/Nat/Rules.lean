/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Domain.Decoder.PiFixedPoint
import DomainSemantics.Domain.Nat.Decoder
import DomainSemantics.Interpretation.ApplicationSubstitution
import DomainSemantics.Soundness.BasicJudgments
import DomainSemantics.Soundness.ComputationRules

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment Presheaf

variable {Γ Γ₁ Γ₂ : Ctx} {n n' : Term}

theorem piLimit_rawExtend_natProjection (X : RawValue Γ) :
    piLimit.rawExtend (principalIdeal natAtom).val X = X.natProjection := by
  ext Γ₁ σ y
  rw [mem_rawExtend, RawValue.mem_natProjection]
  constructor
  · intro ⟨c, hc, x, hx, hy⟩
    have hc' : c ≤ (natAtom : CoherentShape Γ₁) := hc
    have hy' := piLimit.eval_mono_code hc' (principalIdeal x) (𝟙 Γ₁) y hy
    rw [← extend_principal, piLimit_extend_nat, natIdeal_principal,
      ΩIdeal.val_mem, principalIdeal_mem, reindex_id] at hy'
    exact ⟨x, hx, hy'⟩
  · intro ⟨x, hx, hy⟩
    refine ⟨natAtom, le_rfl, x, hx, ?_⟩
    rw [← extend_principal, piLimit_extend_nat, natIdeal_principal,
      principalIdeal_mem, reindex_id]
    exact hy

theorem rawInterpret_succ (D : CodeAssignment) (hn : Γ.as.terms ⊢ n : .nat) :
    rawInterpret D Γ (.succ n) =
      RawFamily.succ (Tm.pairOfTyping Γ.as.wf .nat hn) (rawInterpret D Γ n) :=
  RawFamily.iSup_eq hn fun _ ↦ rfl

namespace HasIdeality

theorem nat (Γ : Ctx) : HasIdeality Γ .nat := by
  intro Γ₂ σ ρ hρ
  change ((RawFamily.nat : RawFamily Γ).app _ σ.op ρ).IsDirected
  rw [RawFamily.nat_value]
  exact ΩLower.isDirected_principal _

theorem zero (Γ : Ctx) : HasIdeality Γ .zero := by
  intro Γ₂ σ ρ hρ
  change ((RawFamily.zero : RawFamily Γ).app _ σ.op ρ).IsDirected
  rw [RawFamily.zero_value]
  exact ΩLower.isDirected_principal _

theorem succ (hn : Γ.as.terms ⊢ n : .nat) (hI : HasIdeality Γ n) :
    HasIdeality Γ (.succ n) := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_succ piLimit hn]
  exact RawValue.succ_isDirected _ (hI σ ρ hρ)

end HasIdeality

namespace HasFixedness

theorem nat (Γ : Ctx) : HasFixedness Γ .nat .type := by
  intro Γ₂ σ ρ hρ
  simp [rawInterpret]
  rw [RawFamily.nat_value, RawFamily.sort_value]
  rw [rawExtend_toLower, piLimit_extend_sort, universeIdeal_principal isCode_natAtom]

theorem zero (Γ : Ctx) : HasFixedness Γ .zero .nat := by
  intro Γ₂ σ ρ hρ
  simp [rawInterpret]
  rw [RawFamily.nat_value, RawFamily.zero_value]
  rw [rawExtend_toLower, piLimit_extend_nat, natIdeal_zero]

theorem succ (hn : Γ.as.terms ⊢ n : .nat) (hF : HasFixedness Γ n .nat) :
    HasFixedness Γ (.succ n) .nat := by
  intro Γ₂ σ ρ hρ
  have h := hF σ ρ hρ
  change piLimit.rawExtend ((RawFamily.nat : RawFamily Γ).app _ σ.op ρ)
    ((rawInterpret piLimit Γ n).app _ σ.op ρ) = _ at h
  rw [RawFamily.nat_value, piLimit_rawExtend_natProjection] at h
  rw [rawInterpret_succ piLimit hn, RawFamily.succ_value]
  change piLimit.rawExtend ((RawFamily.nat : RawFamily Γ).app _ σ.op ρ)
    (RawValue.succ _ _) = _
  rw [RawFamily.nat_value, piLimit_rawExtend_natProjection,
    RawValue.natProjection_succ, h]

end HasFixedness

namespace HasSubstitution

theorem nat (Γ : Ctx) : HasSubstitution Γ .nat := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  simp only [subst_nat, rawInterpret, RawFamily.nat_value]

theorem zero (Γ : Ctx) : HasSubstitution Γ .zero := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  simp only [subst_zero, rawInterpret, RawFamily.zero_value]

theorem succ (hn : Γ.as.terms ⊢ n : .nat) (hS : HasSubstitution Γ n) :
    HasSubstitution Γ (.succ n) := by
  intro Γ₁ Γ₂ θ σ ρs ρt hθ hρ
  have hn' : Γ₁.as.terms ⊢ n[θ.subst] : .nat := hn.subst Γ₁.as.wf θ.typed
  change (rawInterpret piLimit Γ₁ (.succ (n[θ.subst]))).app _ σ.op ρt = _
  rw [rawInterpret_succ piLimit hn', rawInterpret_succ piLimit hn]
  simp only [RawFamily.succ_value]
  rw [hS θ σ ρs ρt hθ hρ]
  congr 1
  exact RawFamily.reindex_ofTyping_subst .nat hn θ σ

end HasSubstitution

theorem HasEquality.succ (hnn' : Γ.as.terms ⊢ n ≡ n' : .nat) (hE : HasEquality Γ n n') :
    HasEquality Γ (.succ n) (.succ n') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_succ piLimit hnn'.hasType.1,
    rawInterpret_succ piLimit hnn'.hasType.2]
  simp only [RawFamily.succ_value]
  rw [hE σ ρ hρ]
  congr 1
  exact congrArg (Tm.presheaf.map σ.op)
    (Tm.pairOfTyping_congr Γ.as.wf .nat hnn')

namespace RawTermProperties

theorem nat (Γ : Ctx) : RawTermProperties Γ .nat where
  ideal := HasIdeality.nat Γ
  subst := HasSubstitution.nat Γ
  ready := True.intro

theorem zero (Γ : Ctx) : RawTermProperties Γ .zero where
  ideal := HasIdeality.zero Γ
  subst := HasSubstitution.zero Γ
  ready := True.intro

theorem succ (hn : Γ.as.terms ⊢ n : .nat) (pn : RawTermProperties Γ n) :
    RawTermProperties Γ (.succ n) where
  ideal := HasIdeality.succ hn pn.ideal
  subst := HasSubstitution.succ hn pn.subst
  ready := True.intro

end RawTermProperties

namespace RawJudgment

theorem nat (Γ : Ctx) : RawJudgment Γ .nat .nat .type where
  regular := ⟨true, IsDefEq.sort, HasFixedness.sort Γ true⟩
  type := RawTermProperties.sort Γ true
  left := RawTermProperties.nat Γ
  right := RawTermProperties.nat Γ
  equal := HasEquality.refl Γ _
  fixed := HasFixedness.nat Γ

theorem zero (Γ : Ctx) : RawJudgment Γ .zero .zero .nat where
  regular := ⟨true, IsDefEq.nat, HasFixedness.nat Γ⟩
  type := RawTermProperties.nat Γ
  left := RawTermProperties.zero Γ
  right := RawTermProperties.zero Γ
  equal := HasEquality.refl Γ _
  fixed := HasFixedness.zero Γ

theorem succDF (hnn' : Γ.as.terms ⊢ n ≡ n' : .nat)
    (pn : RawJudgment Γ n n' .nat) : RawJudgment Γ (.succ n) (.succ n') .nat where
  regular := pn.regular
  type := pn.type
  left := RawTermProperties.succ hnn'.hasType.1 pn.left
  right := RawTermProperties.succ hnn'.hasType.2 pn.right
  equal := HasEquality.succ hnn' pn.equal
  fixed := HasFixedness.succ hnn'.hasType.1 pn.fixed

end RawJudgment

end DomainSemantics.CoherentShape
