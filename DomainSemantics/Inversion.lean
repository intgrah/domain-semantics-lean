/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Admissible
import DomainSemantics.Domain.Decoder.DecoderStrictness
import DomainSemantics.Interpretation.Witnesses
import DomainSemantics.Soundness

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics

open CategoryTheory CoherentShape CodeAssignment Presheaf

private theorem mem_of_equal {Γ : List Term} {t t' A : Term} (hΓ : ⊢ Γ)
    (p : RawJudgment (RawCtx.toCtx.obj ⟨Γ, hΓ⟩) t t' A) {x : CoherentShape (RawCtx.toCtx.obj ⟨Γ, hΓ⟩)}
    (hx : ((rawInterpret piLimit _ t).app _ (𝟙 _).op (fun _ ↦ ⊥)).mem (𝟙 _) x) :
    ((rawInterpret piLimit _ t').app _ (𝟙 _).op (fun _ ↦ ⊥)).mem (𝟙 _) x :=
  p.equal (𝟙 _) (fun _ ↦ ⊥) (hΓ.bottom_admissible (𝟙 _)) ▸ hx

private theorem natAtom_mem {Γ : Ctx} (ρ : RawValuation Γ) :
    ((rawInterpret piLimit Γ .nat).app _ (𝟙 _).op ρ).mem (𝟙 _) natAtom := by
  simp only [rawInterpret, RawFamily.nat_value]
  exact (ΩLower.mem_principal_id _ _).mpr le_rfl

private theorem identityMap_mem {Γ : Ctx} (A a b : Term) (ρ : RawValuation Γ) :
    ((rawInterpret piLimit Γ (.id A a b)).app _ (𝟙 _).op ρ).mem (𝟙 _) (identityMap ⊥ ⊥ ⊥) :=
  (RawValue.mem_identity _ _ _ _ _).mpr
    ⟨⊥, ⊥, ⊥, ΩLower.bottom _ _, ΩLower.bottom _ _, ΩLower.bottom _ _, le_rfl⟩

private theorem le_sortAtom_of_mem {Γ : Ctx} {u : Bool} {ρ : RawValuation Γ} {x : CoherentShape Γ}
    (hx : ((rawInterpret piLimit Γ (.sort u)).app _ (𝟙 _).op ρ).mem (𝟙 _) x) : x ≤ sortAtom u := by
  simp only [rawInterpret, RawFamily.sort_value] at hx
  exact (ΩLower.mem_principal_id _ _).mp hx

private theorem le_natAtom_of_mem {Γ : Ctx} {ρ : RawValuation Γ} {x : CoherentShape Γ}
    (hx : ((rawInterpret piLimit Γ .nat).app _ (𝟙 _).op ρ).mem (𝟙 _) x) : x ≤ natAtom := by
  simp only [rawInterpret, RawFamily.nat_value] at hx
  exact (ΩLower.mem_principal_id _ _).mp hx

private theorem le_piGenerator_of_mem {Γ : Ctx} {A B : Term} {u v : Bool}
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    {ρ : RawValuation Γ} {x : CoherentShape Γ}
    (hx : ((rawInterpret piLimit Γ (.forallE A B)).app _ (𝟙 _).op ρ).mem (𝟙 _) x) :
    ∃ label a f, x ≤ piGenerator label a f := by
  rw [rawInterpret_forallE piLimit hA hB, RawFamily.pi_value] at hx
  have ⟨a, f, _, _, hle⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hx
  exact ⟨_, a, f, hle⟩

theorem IsDefEq.sort_forallE_inv {Γ : List Term} {u : Bool} {A B T : Term} :
    ⊢ Γ →
    Γ ⊢ .sort u ≡ .forallE A B : T →
    False := by
  intro hΓ h
  have p := h.rawSoundness hΓ
  have ⟨_, _, hA, hB, _, _⟩ := p.right.ready
  exact nomatch le_sortAtom_of_mem (mem_of_equal hΓ p.symm
    ((mem_piAtom_rawInterpret_forallE_iff piLimit hA hB (𝟙 _) _
      (label := Ty.pairOfTyping hΓ hA hB)).mpr (by simp)))

theorem IsDefEq.sort_nat_inv {Γ : List Term} {u : Bool} {T : Term} :
    ⊢ Γ →
    Γ ⊢ .sort u ≡ .nat : T →
    False := by
  intro hΓ h
  exact nomatch le_sortAtom_of_mem (mem_of_equal hΓ (h.rawSoundness hΓ).symm (natAtom_mem _))

theorem IsDefEq.forallE_nat_inv {Γ : List Term} {A B T : Term} :
    ⊢ Γ →
    Γ ⊢ .forallE A B ≡ .nat : T →
    False := by
  intro hΓ h
  have p := h.rawSoundness hΓ
  have ⟨_, _, hA, hB, _, _⟩ := p.left.ready
  have ⟨_, _, _, hle⟩ := le_piGenerator_of_mem hA hB (mem_of_equal hΓ p.symm (natAtom_mem _))
  nomatch hle

theorem IsDefEq.id_sort_inv {Γ : List Term} {u : Bool} {A a b T : Term} :
    ⊢ Γ →
    Γ ⊢ .id A a b ≡ .sort u : T →
    False := by
  intro hΓ h
  nomatch le_sortAtom_of_mem (mem_of_equal hΓ (h.rawSoundness hΓ) (identityMap_mem A a b _))

theorem IsDefEq.id_nat_inv {Γ : List Term} {A a b T : Term} :
    ⊢ Γ →
    Γ ⊢ .id A a b ≡ .nat : T →
    False := by
  intro hΓ h
  nomatch le_natAtom_of_mem (mem_of_equal hΓ (h.rawSoundness hΓ) (identityMap_mem A a b _))

theorem IsDefEq.id_forallE_inv {Γ : List Term} {A a b A' B' T : Term} :
    ⊢ Γ →
    Γ ⊢ .id A a b ≡ .forallE A' B' : T →
    False := by
  intro hΓ h
  have p := h.rawSoundness hΓ
  have ⟨_, _, hA, hB, _, _⟩ := p.right.ready
  have ⟨_, _, _, hle⟩ := le_piGenerator_of_mem hA hB (mem_of_equal hΓ p (identityMap_mem A a b _))
  nomatch hle

theorem IsDefEq.forallE_inv {Γ : List Term} {A A' B B' T : Term} :
    ⊢ Γ →
    Γ ⊢ .forallE A B ≡ .forallE A' B' : T →
    Γ ⊢ A ≡ A' type ∧
    A :: Γ ⊢ B ≡ B' type ∧
    A' :: Γ ⊢ B ≡ B' type := by
  intro hΓ h
  have p := h.rawSoundness hΓ
  have ⟨_, _, hA, hB, _, _⟩ := p.left.ready
  have ⟨_, _, hA', hB', _, _⟩ := p.right.ready
  exact rawInterpret_forallE_inversion piLimit hA hB hA' hB' (fun _ ↦ ⊥)
    (p.equal (𝟙 _) (fun _ ↦ ⊥) (hΓ.bottom_admissible (𝟙 _)))

theorem IsDefEq.sort_inv {Γ : List Term} {u v : Bool} {T : Term} :
    ⊢ Γ →
    Γ ⊢ .sort u ≡ .sort v : T →
    u = v := by
  intro hΓ h
  have h : (RawFamily.sort u).app _ (𝟙 _).op _ = (RawFamily.sort v).app _ (𝟙 _).op _ :=
    (h.rawSoundness hΓ).equal (𝟙 _) (fun _ ↦ ⊥) (hΓ.bottom_admissible (𝟙 _))
  rw [RawFamily.sort_value, RawFamily.sort_value] at h
  have hmem : (principalIdeal (sortAtom v : CoherentShape (RawCtx.toCtx.obj ⟨Γ, hΓ⟩))).mem
      (𝟙 _) (sortAtom u) := by
    rw [← ΩIdeal.val_mem, ← h]
    exact (ΩLower.mem_principal_id _ _).mpr le_rfl
  exact sortAtom_le_iff.mp hmem

end DomainSemantics
