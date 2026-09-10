/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Interpretation.ApplicationSubstitution
import DomainSemantics.Interpretation.PiSupport
import DomainSemantics.Interpretation.SourceQuery
import DomainSemantics.Interpretation.Witnesses
import DomainSemantics.Soundness.BasicJudgments
import DomainSemantics.Soundness.StructuralRules

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment Presheaf

variable {Γ Γ₁ Γ₂ : Ctx} {A B f f' a a' e : Term} {u v : Bool}

theorem PiReady.application_value_subst (hready : PiReady Γ A B)
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (θ : Γ₁.as ⟶ Γ.as) (ha : Γ₁.as.terms ⊢ a : A.subst θ.subst)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hρ : SourceAdmissible (σ ≫ RawCtx.toCtx.map θ) ρ) {F : Domain Γ₂}
    (hF : piLimit.rawExtend
      ((rawInterpret piLimit Γ (.forallE A B)).app _ (σ ≫ RawCtx.toCtx.map θ).op ρ)
      F.val = F.val) (X : Domain Γ₂) :
    rawApplication F.val (Tm.presheaf.map σ.op '' RawFamily.sourceQuery Γ₁ a) X.val =
      (application F (Tm.presheaf.map σ.op
        (Tm.pairOfTyping Γ₁.as.wf (hA.subst θ.srcWF θ.typed) ha)) X).val := by
  rw [rawInterpret_forallE piLimit hA hB] at hF
  apply RawFamily.rawApplication_eq_of_sections (hA.subst θ.srcWF θ.typed) ha σ F X
  intro Γ₃ τ name x y hy
  refine (RawFamily.outputAtom_rawPi_fixed_bot_or_section hA _ (rawInterpret piLimit Γ A)
    (rawInterpret_isFinitary piLimit _ B) _ ρ (hready.domain _ ρ hρ)
    (hready.action hA _ ρ hρ) hF τ hy).imp_right ?_
  rintro ⟨s⟩
  exact ⟨Raw.ContextSection.cartesianLift hA θ (by simpa using s)⟩

theorem PiReady.application_fixed (hready : PiReady Γ A B)
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ)
    {F X : Domain Γ₁} {name : Σ A : Ty Γ₁, Tm Γ₁ A}
    (s : Raw.ContextSection hA σ name)
    (hF : piLimit.rawExtend ((rawInterpret piLimit Γ (.forallE A B)).app _ σ.op ρ)
      F.val = F.val)
    (hX : piLimit.rawExtend ((rawInterpret piLimit Γ A).app _ σ.op ρ) X.val = X.val) :
    piLimit.rawExtend
      ((rawInterpret piLimit (Γ.extension hA) B).app _ s.hom.op (ρ.push X.val))
      (application F name X).val = (application F name X).val := by
  rw [rawInterpret_forallE piLimit hA hB] at hF
  have h := RawFamily.application_rawPi_fixed hA _ (rawInterpret piLimit Γ A)
    (rawInterpret_isFinitary piLimit _ B) σ ρ (hready.domain σ ρ hρ)
    (hready.action hA σ ρ hρ) hF (𝟙 Γ₁) name X (by simpa using hX)
  simpa [RawFamily.sectionValue_eq_value (Ctx.rawDisplay hA) _ σ ρ name X.val s] using h

theorem PiReady.application_value (hready : PiReady Γ A B)
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (ha : Γ.as.terms ⊢ a : A) (hFI : HasIdeality Γ f) (hXI : HasIdeality Γ a)
    (hFF : HasFixedness Γ f (.forallE A B))
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret piLimit Γ (.app f a)).app _ σ.op ρ =
      (application (hρ.eval hFI)
        (Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf hA ha)) (hρ.eval hXI)).val := by
  let F := hρ.eval hFI
  let X := hρ.eval hXI
  have hF := hFF σ ρ hρ
  rw [rawInterpret_forallE piLimit hA hB] at hF
  exact RawFamily.rawApplication_eq_of_sections hA ha σ F X (fun τ _ _ _ hy =>
    RawFamily.outputAtom_rawPi_fixed_bot_or_section hA _ (rawInterpret piLimit Γ A)
      (rawInterpret_isFinitary piLimit _ B) σ ρ (hready.domain σ ρ hρ)
      (hready.action hA σ ρ hρ) hF τ hy)

theorem HasIdeality.app (hready : PiReady Γ A B) (ha : Γ.as.terms ⊢ a : A)
    (hFI : HasIdeality Γ f) (hXI : HasIdeality Γ a)
    (hFF : HasFixedness Γ f (.forallE A B)) : HasIdeality Γ (.app f a) := by
  have ⟨u, v, hA, hB, hAI, hD⟩ := hready
  intro Γ₁ σ ρ hρ
  rw [PiReady.application_value ⟨u, v, hA, hB, hAI, hD⟩
    hA hB ha hFI hXI hFF σ ρ hρ]
  exact (application ..).property

theorem HasEquality.app (hready : PiReady Γ A B)
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hab : Γ.as.terms ⊢ a ≡ a' : A)
    (hFI : HasIdeality Γ f) (hXI : HasIdeality Γ a)
    (hFF : HasFixedness Γ f (.forallE A B))
    (hfg : HasEquality Γ f f') (hxy : HasEquality Γ a a') :
    HasEquality Γ (.app f a) (.app f' a') := by
  intro Γ₁ σ ρ hρ
  rw [hready.application_value hA hB hab.hasType.1 hFI hXI hFF σ ρ hρ,
    hready.application_value hA hB hab.hasType.2
      (HasEquality.ideal_right hfg hFI) (HasEquality.ideal_right hxy hXI)
      (HasEquality.fixed_right hfg hFF) σ ρ hρ]
  have hlabel : Tm.pairOfTyping Γ.as.wf hA hab.hasType.1 =
      Tm.pairOfTyping Γ.as.wf hA hab.hasType.2 := Tm.pairOfTyping_eq ⟨u, hA⟩ hab
  rw [hlabel, hfg.eval hρ hFI (hfg.ideal_right hFI),
    hxy.eval hρ hXI (hxy.ideal_right hXI)]

theorem HasFixedness.app (hready : PiReady Γ A B)
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (ha : Γ.as.terms ⊢ a : A) (hFI : HasIdeality Γ f) (haI : HasIdeality Γ a)
    (hFF : HasFixedness Γ f (.forallE A B)) (haF : HasFixedness Γ a A)
    (haR : HasRenaming Γ a) (hBS : HasSubstitution (Ctx.extension Γ hA) B) :
    HasFixedness Γ (.app f a) (B.inst a) := by
  intro Γ₁ σ ρ hρ
  let F := hρ.eval hFI
  let X := hρ.eval haI
  have hresult := hready.application_fixed hA hB σ ρ hρ
    ((Raw.ContextSection.ofTerm hA ha).pullbackId σ) (F := F) (X := X)
    (hFF σ ρ hρ) (haF σ ρ hρ)
  erw [HasSubstitution.instantiate hA ha hready.domain haI haF haR hBS σ ρ hρ] at hresult
  rw [hready.application_value hA hB ha hFI haI hFF σ ρ hρ]
  exact hresult

theorem eta_query_eq_of_section (hA : Γ.as.terms ⊢ A : .sort u)
    (χ : Γ₁ ⟶ Γ) {label name : Σ A : Ty Γ₁, Tm Γ₁ A}
    (s : Raw.ContextSection hA χ label)
    (hname : name ∈ Tm.presheaf.map s.hom.op ''
      RawFamily.sourceQuery (Ctx.extension Γ hA) (.bvar 0))
    (t : Raw.ContextSection hA χ name) : name = label := by
  let θ := Ctx.projectionRaw Γ hA
  have htype : (Ctx.extension Γ hA).as.terms ⊢ A.lift : .sort u := hA.weak' (.skip .refl)
  have hvar : (Ctx.extension Γ hA).as.terms ⊢ .bvar 0 : A.subst θ.subst := by
    simpa [θ, Ctx.projectionRaw, ← lift'_subst, Term.lift, Ctx.extension] using
      (IsDefEq.bvar Lookup.zero htype)
  let t' : Raw.ContextSection hA (s.hom ≫ RawCtx.toCtx.map θ) name := {
    hom := t.hom
    over := t.over.trans s.over.symm
    generic := t.generic
  }
  have hcanonical := RawFamily.sourceQuery_eq_of_section (hA.subst θ.srcWF θ.typed)
    hvar s.hom hname ⟨Raw.ContextSection.cartesianLift hA θ t'⟩
  have hlabel : Tm.pairOfTyping (Ctx.extension Γ hA).as.wf
      (hA.subst θ.srcWF θ.typed) hvar = Tm.rawBinderVar Γ.as.wf hA := by
    unfold Tm.rawBinderVar
    refine Tm.pairOfTyping_eq ⟨u, ?_⟩ ?_
    · simpa [θ, Ctx.projectionRaw, ← lift'_subst] using htype
    · exact hvar
  exact hcanonical.trans ((congrArg (Tm.presheaf.map s.hom.op) hlabel).trans
    s.generic)

theorem HasRenaming.eta_weaken (hren : HasRenaming Γ e)
    (hA : Γ.as.terms ⊢ A : .sort u) (χ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (hρ : SourceAdmissible χ ρ) {label : Σ A : Ty Γ₁, Tm Γ₁ A}
    (s : Raw.ContextSection hA χ label) (X : RawValue Γ₁) :
    (rawInterpret piLimit (Ctx.extension Γ hA) e.lift).app _ s.hom.op (ρ.push X) =
      (rawInterpret piLimit Γ e).app _ χ.op ρ := by
  let r := Ctx.VariableMap.projection Γ hA
  have hsource : SourceAdmissible (s.hom ≫ r.hom)
      (fun i ↦ (ρ.push X) (r.index i)) := by
    change SourceAdmissible (s.hom ≫ Ctx.rawProjection Γ hA) ρ
    rw [s.over]
    exact hρ
  have h := hren r s.hom (ρ.push X) hsource
  change (rawInterpret piLimit (Ctx.extension Γ hA)
      (e.subst (Subst.id.lift_r (.skip .refl)))).app _ s.hom.op (ρ.push X) =
    (rawInterpret piLimit Γ e).app _ (s.hom ≫ Ctx.rawProjection Γ hA).op ρ at h
  simpa [← lift'_subst, s.over] using h

theorem eta_body_value (hA : Γ.as.terms ⊢ A : .sort u) (hren : HasRenaming Γ e)
    (χ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible χ ρ)
    (F : Domain Γ₁)
    (hF : F.val = (rawInterpret piLimit Γ e).app _ χ.op ρ)
    (hsupport : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (X : Domain Γ₂) {y : CoherentShape Γ₂},
      (application (F.pullback σ₁) name X).mem (𝟙 Γ₂) y →
      ¬ y ≤ ⊥ →
      Nonempty (Raw.ContextSection hA (σ₁ ≫ χ) name))
    {label : Σ A : Ty Γ₁, Tm Γ₁ A} (s : Raw.ContextSection hA χ label)
    (X : Domain Γ₁) :
    (rawInterpret piLimit (Ctx.extension Γ hA) (.app e.lift (.bvar 0))).app _ s.hom.op (ρ.push X.val) = (application F label X).val := by
  change rawApplication
    ((rawInterpret piLimit (Ctx.extension Γ hA) e.lift).app _ s.hom.op (ρ.push X.val))
    (Tm.presheaf.map s.hom.op '' RawFamily.sourceQuery (Ctx.extension Γ hA)
      (.bvar 0)) X.val = _
  rw [hren.eta_weaken hA χ ρ hρ s X.val, ← hF]
  apply rawApplication_eq_of_support F X label
  · exact ⟨Tm.rawBinderVar Γ.as.wf hA,
      RawFamily.ofTyping_mem_sourceQuery _ _, s.generic⟩
  · intro Γ₂ σ₁ name hname x y hy
    by_cases hbottom : y ≤ ⊥
    · exact Or.inl hbottom
    · have hmem := hy.mem_application ((principalIdeal_mem x (𝟙 Γ₂) x).mpr
        (by simp))
      have ⟨t⟩ := hsupport σ₁ name (principalIdeal x) hmem hbottom
      have hname' : name ∈ Tm.presheaf.map (s.pullback σ₁).hom.op ''
          RawFamily.sourceQuery (Ctx.extension Γ hA) (.bvar 0) := by
        simpa [-Sigma.exists, Presheaf.Section.pullback, Function.comp_def] using hname
      exact Or.inr (eta_query_eq_of_section hA (σ₁ ≫ χ) (s.pullback σ₁) hname' t)

theorem eta_sectionValue (hA : Γ.as.terms ⊢ A : .sort u) (hren : HasRenaming Γ e)
    (χ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible χ ρ)
    (F : Domain Γ₁)
    (hF : F.val = (rawInterpret piLimit Γ e).app _ χ.op ρ)
    (hsupport : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (X : Domain Γ₂) {y : CoherentShape Γ₂},
      (application (F.pullback σ₁) name X).mem (𝟙 Γ₂) y →
      ¬ y ≤ ⊥ →
      Nonempty (Raw.ContextSection hA (σ₁ ≫ χ) name))
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    RawFamily.sectionValue (Ctx.rawDisplay hA)
      (rawInterpret piLimit (Ctx.extension Γ hA) (.app e.lift (.bvar 0)))
      χ ρ label X.val = (application F label X).val := by
  have hbody {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁)
      (s : Raw.ContextSection hA (σ₁ ≫ χ) (Tm.presheaf.map σ₁.op label)) :
      (rawInterpret piLimit (Ctx.extension Γ hA) (.app e.lift (.bvar 0))).app _ s.hom.op ((ρ.pullback σ₁).push (X.pullback σ₁).val) =
        (application (F.pullback σ₁) (Tm.presheaf.map σ₁.op label)
          (X.pullback σ₁)).val := by
    apply eta_body_value hA hren (σ₁ ≫ χ) (ρ.pullback σ₁) (hρ.pullback σ₁) (F.pullback σ₁)
    · calc
        (F.pullback σ₁).val = (F.val.pullback σ₁) := rfl
        _ = (((rawInterpret piLimit Γ e).app _ χ.op ρ).pullback σ₁) :=
          congrArg (fun I : RawValue Γ₁ ↦ I.pullback σ₁) hF
        _ = _ := ((rawInterpret piLimit Γ e).app_pullback χ.op σ₁ ρ)
    · intro Γ₃ σ₂ name Y y hy hne
      have hy' : (application (F.pullback (σ₂ ≫ σ₁)) name Y).mem (𝟙 Γ₃) y := by
        simpa using hy
      simpa using hsupport (σ₂ ≫ σ₁) name Y hy' hne
  ext Γ₂ σ₁ y
  rw [RawFamily.mem_sectionValue]
  change CoherentShape Γ₂ at y
  have happ : (application F label X).mem σ₁ y ↔
      (application (F.pullback σ₁) (Tm.presheaf.map σ₁.op label)
        (X.pullback σ₁)).mem (𝟙 Γ₂) y := by
    rw [← pullback_application]
    exact (ΩIdeal.presheaf_map_mem_id (application F label X) σ₁ y).symm
  constructor
  · intro
    | .inl hy =>
      exact (application F label X).lower σ₁ hy ((application F label X).bottom σ₁)
    | .inr ⟨s, hy⟩ =>
      apply happ.mpr
      rw [← ΩIdeal.val_presheaf_map, hbody σ₁ s] at hy
      exact hy
  · intro hy
    by_cases hbottom : y ≤ ⊥
    · exact Or.inl hbottom
    · have ⟨s⟩ := hsupport σ₁ _ (X.pullback σ₁) (happ.mp hy) hbottom
      refine Or.inr ⟨s, ?_⟩
      rw [← ΩIdeal.val_presheaf_map, hbody σ₁ s]
      exact happ.mp hy

theorem HasEquality.eta_formation (hready : PiReady Γ A B)
    (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (hEI : HasIdeality Γ e) (hEF : HasFixedness Γ e (.forallE A B))
    (hER : HasRenaming Γ e) :
    HasEquality Γ (.lam A (.app e.lift (.bvar 0))) e := by
  intro Γ₁ σ ρ hρ
  let C := rawInterpret piLimit Γ A
  let N := rawInterpret piLimit (Ctx.extension Γ hA) B
  let E := rawInterpret piLimit (Ctx.extension Γ hA) (.app e.lift (.bvar 0))
  let T := hρ.eval hready.domain
  let Vraw := RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) C N σ ρ
  have hV : Vraw.IsFinitary := RawFamily.normalizedBodyAction_isFinitary piLimit (Ctx.rawDisplay hA) C
    (rawInterpret_isFinitary piLimit _ B) σ ρ
  let V := Vraw.toIdealAction hV (hready.action hA σ ρ hρ)
  let F := hρ.eval hEI
  let label := Ty.pairOfTyping Γ.as.wf hA hB
  have hfixed : piLimit.rawExtend ((RawFamily.pi piLimit (Ctx.rawDisplay hA) label C N).app _ σ.op ρ)
      F.val = F.val := by
    have h := hEF σ ρ hρ
    rw [rawInterpret_forallE piLimit hA hB] at h
    exact h
  have hF : (piLimit.piOperator T V).val.app _ (𝟙 Γ₁).op F = F :=
    piOperator_fixed_of_rawExtend_rawPi (Ty.pairPresheaf.map σ.op label)
      T Vraw hV (hready.action hA σ ρ hρ) hfixed
  let P := piLimit.decode T
  let Q := piLimit.resultOperator V
  let K := Q.arrowAction P F
  let U := RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay hA) C E σ ρ
  have hsupport {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (X : Domain Γ₂) {y : CoherentShape Γ₂}
      (hy : (application (F.pullback σ₁) name X).mem (𝟙 Γ₂) y)
      (hne : ¬ y ≤ ⊥) :
      Nonempty (Raw.ContextSection hA (σ₁ ≫ σ) name) :=
    RawFamily.application_rawPi_fixed_support hA label C
      (rawInterpret_isFinitary piLimit _ B) σ ρ (hready.domain σ ρ hρ)
      (hready.action hA σ ρ hρ) hfixed σ₁ name X hy hne
  have hvalues {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (X : Domain Γ₂) :
      U.app _ (σ₁.op, name) X.val = (K.val.app _ (σ₁.op, name) X).val := by
    let Y := P.val.app _ σ₁.op X
    have hY : P.val.app _ σ₁.op Y = Y := piLimit.decode_isIdempotent piLimit_isIdempotent T σ₁ X
    have hK : K.val.app _ (σ₁.op, name) X = application (F.pullback σ₁) name Y :=
      Q.application_fixed P hF σ₁ name Y hY
    have hhead : piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) X.val =
        Y.val := by
      change piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) X.val =
        (piLimit.extend (T.pullback σ₁) X).val
      rw [← piLimit.rawExtend_toLower]
      exact congrArg (fun I : RawValue Γ₂ ↦ piLimit.rawExtend I X.val)
        ((C.app_pullback σ.op σ₁ ρ)).symm
    change RawFamily.sectionValue (Ctx.rawDisplay hA) E (σ₁ ≫ σ) (ρ.pullback σ₁) name
      (piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) X.val) = _
    rw [hhead, hK]
    apply eta_sectionValue hA hER (σ₁ ≫ σ) (ρ.pullback σ₁) (hρ.pullback σ₁) (F.pullback σ₁)
    · exact ((rawInterpret piLimit Γ e).app_pullback σ.op σ₁ ρ)
    · intro Γ₃ σ₂ name' Z y hy hne
      have hy' : (application (F.pullback (σ₂ ≫ σ₁)) name' Z).mem (𝟙 Γ₃) y := by
        simpa using hy
      simpa using hsupport (σ₂ ≫ σ₁) name' Z hy' hne
  rw [rawInterpret_lam piLimit hA]
  calc
    _ = _ := U.abstraction_eq_of_ideal_values K hvalues
    _ = _ := congrArg Subtype.val ((Q.arrow_value_id P F).symm.trans hF)

theorem HasEquality.eta (hready : PiReady Γ A B)
    (hEI : HasIdeality Γ e) (hEF : HasFixedness Γ e (.forallE A B))
    (hER : HasRenaming Γ e) :
    HasEquality Γ (.lam A (.app e.lift (.bvar 0))) e :=
  have ⟨u, v, hA, hB, hAI, hD⟩ := hready
  HasEquality.eta_formation ⟨u, v, hA, hB, hAI, hD⟩ hA hB hEI hEF hER

theorem RawJudgment.eta (pe : RawJudgment Γ e e (.forallE A B))
    (pExpansion : RawJudgment Γ (.lam A (.app e.lift (.bvar 0)))
      (.lam A (.app e.lift (.bvar 0))) (.forallE A B)) :
    RawJudgment Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B) :=
  RawJudgment.of_typings pExpansion pe (HasEquality.eta pe.type.ready pe.left.ideal pe.fixed
    pe.left.ren)

end DomainSemantics.CoherentShape

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

variable {Γ : Ctx} {A B f f' a a' : Term} {u v : Bool}

theorem RawTermProperties.app (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (ha : Γ.as.terms ⊢ a : A) (hready : PiReady Γ A B)
    (pf : RawTermProperties Γ f) (pa : RawTermProperties Γ a)
    (hfF : HasFixedness Γ f (.forallE A B)) : RawTermProperties Γ (.app f a) where
  ideal := HasIdeality.app hready ha pf.ideal pa.ideal hfF
  subst := HasSubstitution.app hA hB ha hready.domain pf.ideal pa.ideal hfF
    (hready.action hA) pf.subst pa.subst
  ready := True.intro

theorem RawJudgment.appDF (hA : Γ.as.terms ⊢ A : .sort u) (hB : A :: Γ.as.terms ⊢ B : .sort v)
    (haa' : Γ.as.terms ⊢ a ≡ a' : A)
    (hResult : Γ.as.terms ⊢ B.inst a ≡ B.inst a' : .sort v)
    (pB : RawJudgment (Ctx.extension Γ hA) B B (.sort v))
    (pf : RawJudgment Γ f f' (.forallE A B)) (pa : RawJudgment Γ a a' A)
    (pResult : RawJudgment Γ (B.inst a) (B.inst a') (.sort v)) :
    RawJudgment Γ (.app f a) (.app f' a') (B.inst a) where
  regular := ⟨v, hResult.hasType.1, pResult.fixed⟩
  type := pResult.left
  left := RawTermProperties.app hA hB haa'.hasType.1 pf.type.ready pf.left pa.left pf.fixed
  right := RawTermProperties.app hA hB haa'.hasType.2 pf.type.ready
    pf.right pa.right pf.fixed_right
  equal := HasEquality.app pf.type.ready hA hB haa'
    pf.left.ideal pa.left.ideal pf.fixed pf.equal pa.equal
  fixed := HasFixedness.app pf.type.ready hA hB haa'.hasType.1
    pf.left.ideal pa.left.ideal pf.fixed pa.fixed pa.left.ren pB.left.subst

end DomainSemantics.CoherentShape
