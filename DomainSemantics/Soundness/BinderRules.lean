/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Comprehension.Conversion
public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Domain.Decoder.DecoderStrictness
import DomainSemantics.Domain.Decoder.PiUniverse
import DomainSemantics.Interpretation.BinderSubstitution
import DomainSemantics.Interpretation.LambdaFixed
import DomainSemantics.Interpretation.Prop
import DomainSemantics.Interpretation.Witnesses
import DomainSemantics.Soundness.BasicJudgments
import DomainSemantics.Soundness.ComputationRules
import DomainSemantics.Soundness.StructuralRules

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment Presheaf

variable {Γ Γ₁ Γ₂ : Ctx} {A A' B B' b b' : Term} {u v : Bool}

theorem piLimit_rawExtend_sort_le (r : Bool) {I : RawValue Γ} :
    piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom r)) I ≤ I := by
  intro Γ₁ σ y hy
  exact ((mem_piLimit_rawExtend_sort_iff r I σ y).mp hy).1

theorem RawFamily.sectionValue_decode_fixed (hA : Γ.as.terms ⊢ A : .sort u)
    (C M : RawFamily (Ctx.extension Γ hA))
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : RawValue Γ₁)
    (hbody : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁)
      (s : Raw.ContextSection hA (σ₁ ≫ σ) (Tm.presheaf.map σ₁.op label)),
      piLimit.rawExtend (C.app _ s.hom.op ((ρ.pullback σ₁).push (I.pullback σ₁)))
          (M.app _ s.hom.op ((ρ.pullback σ₁).push (I.pullback σ₁))) =
        M.app _ s.hom.op ((ρ.pullback σ₁).push (I.pullback σ₁))) :
    piLimit.rawExtend (sectionValue (Ctx.rawDisplay hA) C σ ρ label I) (sectionValue (Ctx.rawDisplay hA) M σ ρ label I) =
      sectionValue (Ctx.rawDisplay hA) M σ ρ label I := by
  apply (bodySection (Ctx.rawDisplay hA) M σ ρ label I).eq_extend
  · intro Γ₂ τ y hy hne
    have ⟨c, hc, hcne⟩ := piLimit.rawExtend_nonbottom_code piLimit_value_bottom hy hne
    exact (bodySection (Ctx.rawDisplay hA) C σ ρ label I).support hc hcne
  · intro Γ₂ τ s
    rw [piLimit.pullback_rawExtend, sectionValue, sectionValue,
      (bodySection (Ctx.rawDisplay hA) C σ ρ label I).pullback_extend τ s,
      (bodySection (Ctx.rawDisplay hA) M σ ρ label I).pullback_extend τ s]
    exact hbody τ s

theorem RawFamily.sectionValue_sort_fixed (hA : Γ.as.terms ⊢ A : .sort u)
    (C : RawFamily (Ctx.extension Γ hA)) (r : Bool)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : RawValue Γ₁)
    (hbody : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁)
      (s : Raw.ContextSection hA (σ₁ ≫ σ) (Tm.presheaf.map σ₁.op label)),
      piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom r))
          (C.app _ s.hom.op ((ρ.pullback σ₁).push (I.pullback σ₁))) =
        C.app _ s.hom.op ((ρ.pullback σ₁).push (I.pullback σ₁))) :
    piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom r))
        (sectionValue (Ctx.rawDisplay hA) C σ ρ label I) = sectionValue (Ctx.rawDisplay hA) C σ ρ label I := by
  apply (bodySection (Ctx.rawDisplay hA) C σ ρ label I).eq_extend
  · intro Γ₂ τ y hy
    exact (bodySection (Ctx.rawDisplay hA) C σ ρ label I).support (piLimit_rawExtend_sort_le r τ y hy)
  · intro Γ₂ τ s
    rw [piLimit.pullback_rawExtend, ΩLower.presheaf_map_principal, sectionValue,
      (bodySection (Ctx.rawDisplay hA) C σ ρ label I).pullback_extend τ s]
    exact hbody τ s

theorem SourceAdmissible.push_fixed_pullback (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    {σ : Γ₁ ⟶ Γ} {ρ : RawValuation Γ₁} (hρ : SourceAdmissible σ ρ)
    (J : Domain Γ₁)
    (hJ : piLimit.rawExtend ((rawInterpret piLimit Γ A).app _ σ.op ρ) J.val = J.val)
    (σ₁ : Γ₂ ⟶ Γ₁) {label : Σ A : Ty Γ₂, Tm Γ₂ A}
    (s : Raw.ContextSection hA (σ₁ ≫ σ) label) :
    SourceAdmissible s.hom ((ρ.pullback σ₁).push (J.val.pullback σ₁)) := by
  have hJτ := congrArg (fun I : RawValue Γ₁ ↦ I.pullback σ₁) hJ
  rw [piLimit.pullback_rawExtend, RawFamily.app_pullback] at hJτ
  exact (hρ.pullback σ₁).push hA s (hAI _ _ (hρ.pullback σ₁))
    (J.pullback σ₁).property hJτ

theorem HasFixedness.section_fixed (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    (hm : HasFixedness (Ctx.extension Γ hA) b B)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ)
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) (J : Domain Γ₁)
    (hJ : piLimit.rawExtend ((rawInterpret piLimit Γ A).app _ σ.op ρ) J.val = J.val) :
    piLimit.rawExtend
        (RawFamily.sectionValue (Ctx.rawDisplay hA) (rawInterpret piLimit (Ctx.extension Γ hA) B)
          σ ρ label J.val)
        (RawFamily.sectionValue (Ctx.rawDisplay hA) (rawInterpret piLimit (Ctx.extension Γ hA) b)
          σ ρ label J.val) =
      RawFamily.sectionValue (Ctx.rawDisplay hA) (rawInterpret piLimit (Ctx.extension Γ hA) b)
        σ ρ label J.val :=
  RawFamily.sectionValue_decode_fixed hA _ _ σ ρ label J.val
    (fun σ₁ s => hm s.hom _ (hρ.push_fixed_pullback hA hAI J hJ σ₁ s))

theorem HasFixedness.section_sort (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    (hB : HasFixedness (Ctx.extension Γ hA) B (.sort v))
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ)
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) (J : Domain Γ₁)
    (hJ : piLimit.rawExtend ((rawInterpret piLimit Γ A).app _ σ.op ρ) J.val = J.val) :
    piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom v))
        (RawFamily.sectionValue (Ctx.rawDisplay hA) (rawInterpret piLimit (Ctx.extension Γ hA) B)
          σ ρ label J.val) =
      RawFamily.sectionValue (Ctx.rawDisplay hA) (rawInterpret piLimit (Ctx.extension Γ hA) B)
        σ ρ label J.val := by
  apply RawFamily.sectionValue_sort_fixed
  intro Γ₂ σ₁ s
  have h := hB s.hom _ (hρ.push_fixed_pullback hA hAI J hJ σ₁ s)
  rw [rawInterpret, RawFamily.sort_value] at h
  exact h

theorem HasFixedness.normalizedBodyAction_prop_code (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    (hB : HasFixedness (Ctx.extension Γ hA) B .prop)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ)
    (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A) (x y : CoherentShape Γ₂)
    (hy : ((RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) (rawInterpret piLimit Γ A)
      (rawInterpret piLimit (Ctx.extension Γ hA) B) σ ρ).app _ (σ₁.op, name)
        (principalIdeal x).val).mem (𝟙 Γ₂) y) :
    IsCode false y := by
  have hT : ((rawInterpret piLimit Γ A).app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)).IsDirected :=
    hAI _ _ (hρ.pullback σ₁)
  let J : Domain Γ₂ := ⟨_, piLimit.rawExtend_isDirected hT (principalIdeal x).property⟩
  have hJ := piLimit.rawExtend_idempotent piLimit_isIdempotent hT (principalIdeal x).property
  change (RawFamily.sectionValue (Ctx.rawDisplay hA) (rawInterpret piLimit (Ctx.extension Γ hA) B)
    (σ₁ ≫ σ) (ρ.pullback σ₁) name J.val).mem (𝟙 Γ₂) y at hy
  rw [← section_sort hA hAI hB _ _ (hρ.pullback σ₁) name J hJ] at hy
  have ⟨_, hcode⟩ := (mem_piLimit_rawExtend_sort_iff _ _ _ _).mp hy
  exact hcode

theorem PiReady.of_ideality (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hAI : HasIdeality Γ A) (hBI : HasIdeality (Ctx.extension Γ hA) B) :
    PiReady Γ A B :=
  ⟨u, v, hA, hB, hAI, HasIdeality.bodyAction hA hAI hBI⟩

theorem HasIdeality.forallE (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hAI : HasIdeality Γ A) (hBI : HasIdeality (Ctx.extension Γ hA) B) :
    HasIdeality Γ (.forallE A B) := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_forallE piLimit hA hB, RawFamily.pi_value]
  apply rawPi_isDirected
  · exact hAI σ ρ hρ
  · exact bodyAction hA hAI hBI σ ρ hρ

theorem HasIdeality.lam (hA : Γ.as.terms ⊢ A : .sort u) (hAI : HasIdeality Γ A)
    (hbI : HasIdeality (Ctx.extension Γ hA) b) : HasIdeality Γ (.lam A b) := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_lam piLimit hA, RawFamily.abstraction_value]
  exact RawAction.abstraction_isDirected _ (bodyAction hA hAI hbI σ ρ hρ)

theorem rawPi_type_fixed (label : Σ A : Ty Γ, Ty (Γ.extend A)) (C : RawValue Γ) (M : RawAction Γ) :
    piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom true))
      (rawPi label C M) = rawPi label C M := by
  apply le_antisymm
  · exact piLimit_rawExtend_sort_le _
  · intro Γ₁ σ y hy
    have ⟨a, f, _, _, hy'⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hy
    exact (mem_piLimit_rawExtend_sort_iff _ _ σ y).mpr
      ⟨hy, IsCode.of_le hy' (isCode_type_piGenerator _ a f)⟩

theorem rawPi_prop_fixed (label : Σ A : Ty Γ, Ty (Γ.extend A)) (C : RawValue Γ) (M : RawAction Γ)
    (hM : ∀ {Γ₃ : Ctx} (σ : Γ₃ ⟶ Γ) (name : Σ A : Ty Γ₃, Tm Γ₃ A) (x y : CoherentShape Γ₃),
      (M.app _ (σ.op, name) (principalIdeal x).val).mem (𝟙 Γ₃) y → IsCode false y) :
    piLimit.rawExtend (ΩLower.principal pointedOrder (sortAtom false))
      (rawPi label C M) = rawPi label C M := by
  apply le_antisymm
  · exact piLimit_rawExtend_sort_le _
  · intro Γ₁ σ y hy
    have ⟨a, ⟨f, hcoh⟩, _, hf, hy'⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hy
    exact (mem_piLimit_rawExtend_sort_iff _ _ σ y).mpr
      ⟨hy, IsCode.of_le hy' (isCode_prop_piGenerator _ a ⟨f, hcoh⟩ fun i =>
        hM σ (f.names i) (CoherentGraph.input ⟨f, hcoh⟩ i) (CoherentGraph.output ⟨f, hcoh⟩ i) (hf i))⟩

theorem HasFixedness.forallE (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hAI : HasIdeality Γ A) (hBsort : HasFixedness (Ctx.extension Γ hA) B (.sort v)) :
    HasFixedness Γ (.forallE A B) (.sort v) := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_forallE piLimit hA hB, RawFamily.pi_value]
  simp [rawInterpret]
  rw [RawFamily.sort_value]
  cases v with
  | true => exact rawPi_type_fixed _ _ _
  | false =>
    exact rawPi_prop_fixed _ _ _ fun σ₁ name x y hy =>
      normalizedBodyAction_prop_code hA hAI hBsort σ ρ hρ σ₁ name x y hy

theorem HasFixedness.lam (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hAI : HasIdeality Γ A) (hBI : HasIdeality (Ctx.extension Γ hA) B)
    (hbI : HasIdeality (Ctx.extension Γ hA) b)
    (hb : HasFixedness (Ctx.extension Γ hA) b B) :
    HasFixedness Γ (.lam A b) (.forallE A B) := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_lam piLimit hA, rawInterpret_forallE piLimit hA hB,
    RawFamily.abstraction_value, RawFamily.pi_value]
  apply RawFamily.normalizedAbstraction_fixed
  · exact rawInterpret_isFinitary piLimit _ B
  · exact rawInterpret_isFinitary piLimit _ b
  · exact hAI σ ρ hρ
  · exact HasIdeality.bodyAction hA hAI hBI σ ρ hρ
  · exact HasIdeality.bodyAction hA hAI hbI σ ρ hρ
  · intro Γ₂ σ₁ label J hJ
    exact section_fixed hA hAI hb _ _ (hρ.pullback σ₁) label J hJ

theorem RawFamily.sectionValue_contextConversion_eq (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u)
    (C : RawFamily (Ctx.extension Γ hAA'.hasType.1))
    (C' : RawFamily (Ctx.extension Γ hAA'.hasType.2))
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : RawValue Γ₁)
    (hbody : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁)
      (s : Raw.ContextSection hAA'.hasType.2 (σ₁ ≫ σ)
        (Tm.presheaf.map σ₁.op label)),
      C.app _ (s.convert hAA').hom.op ((ρ.pullback σ₁).push (I.pullback σ₁)) =
        C'.app _ s.hom.op ((ρ.pullback σ₁).push (I.pullback σ₁))) :
    sectionValue (Ctx.rawDisplay hAA'.hasType.1) C σ ρ label I =
      sectionValue (Ctx.rawDisplay hAA'.hasType.2) C' σ ρ label I := by
  ext Γ₂ σ₁ y
  simp_rw [mem_sectionValue]
  constructor
  · intro
    | .inl hy =>
      exact Or.inl hy
    | .inr ⟨s, hy⟩ =>
      let t := Raw.ContextSection.convert hAA'.symm s
      have ht : (t.convert hAA').hom = s.hom := Presheaf.Section.hom_eq _ _
      refine Or.inr ⟨t, ?_⟩
      rw [← hbody σ₁ t, ht]
      exact hy
  · intro
    | .inl hy =>
      exact Or.inl hy
    | .inr ⟨s, hy⟩ =>
      exact Or.inr ⟨Raw.ContextSection.convert hAA' s, by rw [hbody σ₁ s]; exact hy⟩

namespace HasEquality

theorem section_contextConversion
    (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u) (hAI : HasIdeality Γ A)
    (hbb' : HasEquality (Ctx.extension Γ hAA'.hasType.1) b b')
    (hb' : HasRenaming (Ctx.extension Γ hAA'.hasType.1) b')
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ)
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) (J : Domain Γ₁)
    (hJ : piLimit.rawExtend ((rawInterpret piLimit Γ A).app _ σ.op ρ) J.val = J.val) :
    RawFamily.sectionValue (Ctx.rawDisplay hAA'.hasType.1)
        (rawInterpret piLimit (Ctx.extension Γ hAA'.hasType.1) b) σ ρ label J.val =
      RawFamily.sectionValue (Ctx.rawDisplay hAA'.hasType.2)
        (rawInterpret piLimit (Ctx.extension Γ hAA'.hasType.2) b') σ ρ label J.val := by
  apply RawFamily.sectionValue_contextConversion_eq
  intro Γ₂ σ₁ s
  have hadm := hρ.push_fixed_pullback hAA'.hasType.1 hAI J hJ σ₁ (s.convert hAA')
  apply (hbb' (s.convert hAA').hom _ hadm).trans
  let r : Ctx.VariableMap (Ctx.extension Γ hAA'.hasType.2)
      (Ctx.extension Γ hAA'.hasType.1) :=
    ⟨id, (Ctx.contextConversionRaw hAA').typed⟩
  have hr : r.hom = Ctx.contextConversion hAA' := rfl
  have hcoords : (fun i ↦ ((ρ.pullback σ₁).push (J.val.pullback σ₁)) (r.index i)) =
      (ρ.pullback σ₁).push (J.val.pullback σ₁) := rfl
  have h := hb' r s.hom ((ρ.pullback σ₁).push (J.val.pullback σ₁)) hadm
  change (rawInterpret piLimit _ (b'[Term.bvar])).app _ _ _ = _ at h
  rw [subst_id, hr, hcoords] at h
  exact h.symm

theorem normalizedBodyAction_contextConversion
    (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u) (hAI : HasIdeality Γ A)
    (hAeq : HasEquality Γ A A')
    (hbb' : HasEquality (Ctx.extension Γ hAA'.hasType.1) b b')
    (hb' : HasRenaming (Ctx.extension Γ hAA'.hasType.1) b')
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ)
    (σ₁ : Γ₂ ⟶ Γ₁) (label : Σ A : Ty Γ₂, Tm Γ₂ A) (I : Domain Γ₂) :
    (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hAA'.hasType.1) (rawInterpret piLimit Γ A)
      (rawInterpret piLimit (Ctx.extension Γ hAA'.hasType.1) b) σ ρ).app _ (σ₁.op, label) I.val =
      (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hAA'.hasType.2) (rawInterpret piLimit Γ A')
        (rawInterpret piLimit (Ctx.extension Γ hAA'.hasType.2) b') σ ρ).app _ (σ₁.op, label) I.val := by
  have hT : ((rawInterpret piLimit Γ A).app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)).IsDirected :=
    hAI _ _ (hρ.pullback σ₁)
  let J : Domain Γ₂ := ⟨_, piLimit.rawExtend_isDirected hT I.property⟩
  change RawFamily.sectionValue (Ctx.rawDisplay _) _ _ _ _ J.val = RawFamily.sectionValue (Ctx.rawDisplay _) _ _ _ _
    (piLimit.rawExtend ((rawInterpret piLimit Γ A').app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) I.val)
  rw [← hAeq _ _ (hρ.pullback σ₁)]
  exact section_contextConversion hAA' hAI hbb' hb' _ _ (hρ.pullback σ₁) label J
    (piLimit.rawExtend_idempotent piLimit_isIdempotent hT I.property)

theorem lam (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u) (hAI : HasIdeality Γ A)
    (hAeq : HasEquality Γ A A')
    (hbb' : HasEquality (Ctx.extension Γ hAA'.hasType.1) b b')
    (hb' : HasRenaming (Ctx.extension Γ hAA'.hasType.1) b') :
    HasEquality Γ (.lam A b) (.lam A' b') := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_lam piLimit hAA'.hasType.1,
    rawInterpret_lam piLimit hAA'.hasType.2, RawFamily.abstraction_value,
    RawFamily.abstraction_value]
  exact RawAction.abstraction_eq_of_eq_on_ideals (normalizedBodyAction_contextConversion hAA' hAI hAeq hbb' hb' σ ρ hρ)

theorem forallE (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u)
    (hBB' : A :: Γ.as.terms ⊢ B ≡ B' : .sort v)
    (hBB'₂ : A' :: Γ.as.terms ⊢ B ≡ B' : .sort v)
    (hAI : HasIdeality Γ A) (hAeq : HasEquality Γ A A')
    (hBeq : HasEquality (Ctx.extension Γ hAA'.hasType.1) B B')
    (hB' : HasRenaming (Ctx.extension Γ hAA'.hasType.1) B') :
    HasEquality Γ (.forallE A B) (.forallE A' B') := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_forallE piLimit hAA'.hasType.1 hBB'.hasType.1,
    rawInterpret_forallE piLimit hAA'.hasType.2 hBB'₂.hasType.2,
    RawFamily.pi_value, RawFamily.pi_value]
  rw [Ty.pairOfTyping_congr Γ.as.wf hAA' hBB' hBB'₂, hAeq σ ρ hρ]
  apply rawPi_eq_of_eq_on_ideals
  exact normalizedBodyAction_contextConversion hAA' hAI hAeq hBeq hB' σ ρ hρ

end HasEquality

end DomainSemantics.CoherentShape

namespace DomainSemantics.CoherentShape

variable {Γ : Ctx} {A A' B B' b b' : Term} {u v : Bool}

theorem RawTermProperties.forallE (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (pA : RawTermProperties Γ A) (pB : RawTermProperties (Ctx.extension Γ hA) B) :
    RawTermProperties Γ (.forallE A B) where
  ideal := HasIdeality.forallE hA hB pA.ideal pB.ideal
  subst := HasSubstitution.forallE hA hB pA.ideal pA.subst pB.subst
  ready := PiReady.of_ideality hA hB pA.ideal pB.ideal

theorem RawTermProperties.lam (hA : Γ.as.terms ⊢ A : .sort u)
    (pA : RawTermProperties Γ A) (pb : RawTermProperties (Ctx.extension Γ hA) b) :
    RawTermProperties Γ (.lam A b) where
  ideal := HasIdeality.lam hA pA.ideal pb.ideal
  subst := HasSubstitution.lam hA pA.ideal pA.subst pb.subst
  ready := True.intro

theorem RawJudgment.forallEDF (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u)
    (hBB' : A :: Γ.as.terms ⊢ B ≡ B' : .sort v)
    (hBB'₂ : A' :: Γ.as.terms ⊢ B ≡ B' : .sort v)
    (pA : RawJudgment Γ A A' (.sort u))
    (pB : RawJudgment (Ctx.extension Γ hAA'.hasType.1) B B' (.sort v))
    (pB' : RawJudgment (Ctx.extension Γ hAA'.hasType.2) B B' (.sort v)) :
    RawJudgment Γ (.forallE A B) (.forallE A' B') (.sort v) where
  regular := ⟨true, IsDefEq.sort, HasFixedness.sort Γ v⟩
  type := RawTermProperties.sort Γ v
  left := RawTermProperties.forallE hAA'.hasType.1 hBB'.hasType.1 pA.left pB.left
  right := RawTermProperties.forallE hAA'.hasType.2 hBB'₂.hasType.2 pA.right pB'.right
  equal := HasEquality.forallE hAA' hBB' hBB'₂ pA.left.ideal pA.equal pB.equal pB.right.ren
  fixed := HasFixedness.forallE hAA'.hasType.1 hBB'.hasType.1 pA.left.ideal pB.fixed

theorem RawJudgment.lamDF (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u)
    (hB : A :: Γ.as.terms ⊢ B : .sort v) (hPi : Γ.as.terms ⊢ .forallE A B : .sort v)
    (pA : RawJudgment Γ A A' (.sort u))
    (pB : RawJudgment (Ctx.extension Γ hAA'.hasType.1) B B (.sort v))
    (pb : RawJudgment (Ctx.extension Γ hAA'.hasType.1) b b' B)
    (pb' : RawJudgment (Ctx.extension Γ hAA'.hasType.2) b b' B)
    (pPi : RawJudgment Γ (.forallE A B) (.forallE A B) (.sort v)) :
    RawJudgment Γ (.lam A b) (.lam A' b') (.forallE A B) where
  regular := ⟨v, hPi, pPi.fixed⟩
  type := pPi.left
  left := RawTermProperties.lam hAA'.hasType.1 pA.left pb.left
  right := RawTermProperties.lam hAA'.hasType.2 pA.right pb'.right
  equal := HasEquality.lam hAA' pA.left.ideal pA.equal pb.equal pb.right.ren
  fixed := HasFixedness.lam hAA'.hasType.1 hB pA.left.ideal pB.left.ideal pb.left.ideal
    pb.fixed

end DomainSemantics.CoherentShape
