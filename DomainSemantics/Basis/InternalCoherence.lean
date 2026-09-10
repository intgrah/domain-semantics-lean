/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Presheaf

@[expose] public section

namespace DomainSemantics

open CategoryTheory

variable {Γ Γ₁ Γ₂ : Ctx}

def Shape.Compatible {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) : Shape Γ → Shape Γ → Prop
  | .bot, _ => True
  | _, .bot => True
  | .sort r, .sort r' => r = r'
  | .forallE label a _ names ins outs, .forallE label' a' _ names' ins' outs' =>
    Ty.pairPresheaf.map σ.op label = Ty.pairPresheaf.map σ.op label' ∧ Compatible σ a a' ∧
      ∀ i j {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ _),
        Tm.presheaf.map (σ₁ ≫ σ).op (names i) = Tm.presheaf.map (σ₁ ≫ σ).op (names' j) →
        Compatible (σ₁ ≫ σ) (ins i) (ins' j) → Compatible (σ₁ ≫ σ) (outs i) (outs' j)
  | .lam _ names ins outs, .lam _ names' ins' outs' =>
    ∀ i j {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ _),
      Tm.presheaf.map (σ₁ ≫ σ).op (names i) = Tm.presheaf.map (σ₁ ≫ σ).op (names' j) →
      Compatible (σ₁ ≫ σ) (ins i) (ins' j) → Compatible (σ₁ ≫ σ) (outs i) (outs' j)
  | .lam _ _ _ outs, _ => ∀ i, Basis.IsBottom (outs i)
  | _, .lam _ _ _ outs' => ∀ j, Basis.IsBottom (outs' j)
  | .nat, .nat => True
  | .zero, .zero => True
  | .succ name a, .succ name' a' =>
    Tm.presheaf.map σ.op name = Tm.presheaf.map σ.op name' ∧ Compatible σ a a'
  | .id A a b, .id A' a' b' => Compatible σ A A' ∧ Compatible σ a a' ∧ Compatible σ b b'
  | _, _ => False

def Graph.Compatible (σ : Γ₁ ⟶ Γ) (f g : Graph Γ) : Prop :=
  ∀ i j {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁),
    Tm.presheaf.map (σ₁ ≫ σ).op (f.names i) = Tm.presheaf.map (σ₁ ≫ σ).op (g.names j) →
    Shape.Compatible (σ₁ ≫ σ) (f.ins i) (g.ins j) → Shape.Compatible (σ₁ ≫ σ) (f.outs i) (g.outs j)

theorem Graph.Compatible.comp {σ : Γ₁ ⟶ Γ} {f g : Graph Γ}
    (σ₁ : Γ₂ ⟶ Γ₁) (hfg : Graph.Compatible σ f g) : Graph.Compatible (σ₁ ≫ σ) f g := by
  intro i j Γ₂' σ₁' hl hin
  rw [← Category.assoc] at hl hin ⊢
  exact hfg i j (σ₁' ≫ σ₁) hl hin

namespace Shape

theorem Compatible.abs_iff {σ : Γ₁ ⟶ Γ} {f g : Graph Γ} :
    Compatible σ (abs f) (abs g) ↔ Graph.Compatible σ f g :=
  Iff.rfl

theorem Compatible.of_isBottom_left {a b : Shape Γ} (σ : Γ₁ ⟶ Γ)
    (h : Basis.IsBottom a) : Compatible σ a b := by
  induction h generalizing b Γ₁ with
  | bot => cases b <;> trivial
  | lam h ih =>
    cases b with
    | bot => trivial
    | lam _ _ _ _ => exact fun i j Γ₂ σ₁ _ _ => ih i _
    | _ => exact h

theorem Compatible.comm (a b : Shape Γ) {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) :
    Compatible σ a b ↔ Compatible σ b a := by
  induction a generalizing b Γ₁ with
  | sort r =>
    cases b with
    | sort r' => exact Eq.comm
    | _ => exact Iff.rfl
  | forallE _ _ _ _ _ _ ih ihi iho =>
    cases b with
    | forallE _ _ _ _ _ _ =>
      exact ⟨fun ⟨hlabel, hdomain, hgraph⟩ => ⟨hlabel.symm, (ih _ σ).mp hdomain, fun j i _ σ₁ hl hin =>
          (iho i _ _).mp (hgraph i j σ₁ hl.symm ((ihi i _ _).mpr hin))⟩,
        fun ⟨hlabel, hdomain, hgraph⟩ => ⟨hlabel.symm, (ih _ σ).mpr hdomain, fun i j _ σ₁ hl hin =>
          (iho i _ _).mpr (hgraph j i σ₁ hl.symm ((ihi i _ _).mp hin))⟩⟩
    | _ => exact Iff.rfl
  | lam _ _ _ _ ihi iho =>
    cases b with
    | lam _ _ _ _ =>
      exact ⟨fun h j i _ σ₁ hl hin => (iho i _ _).mp (h i j σ₁ hl.symm ((ihi i _ _).mpr hin)),
        fun h i j _ σ₁ hl hin => (iho i _ _).mpr (h j i σ₁ hl.symm ((ihi i _ _).mp hin))⟩
    | _ => exact Iff.rfl
  | succ _ _ ih =>
    cases b with
    | succ _ _ =>
      exact ⟨fun ⟨hlabel, h⟩ => ⟨hlabel.symm, (ih _ σ).mp h⟩,
        fun ⟨hlabel, h⟩ => ⟨hlabel.symm, (ih _ σ).mpr h⟩⟩
    | _ => exact Iff.rfl
  | id _ _ _ ihA iha ihb =>
    cases b with
    | id _ _ _ =>
      exact ⟨fun ⟨hA, ha, hb⟩ => ⟨(ihA _ σ).mp hA, (iha _ σ).mp ha, (ihb _ σ).mp hb⟩,
        fun ⟨hA, ha, hb⟩ => ⟨(ihA _ σ).mpr hA, (iha _ σ).mpr ha, (ihb _ σ).mpr hb⟩⟩
    | _ => exact Iff.rfl
  | _ => cases b <;> exact Iff.rfl

theorem Compatible.symm {σ : Γ₁ ⟶ Γ} {a b : Shape Γ} (h : Compatible σ a b) :
    Compatible σ b a :=
  (comm a b σ).mp h

theorem Compatible.comp {a b : Shape Γ} {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {Γ₂ : Ctx}
    (σ₁ : Γ₂ ⟶ Γ₁) : Compatible σ a b → Compatible (σ₁ ≫ σ) a b := by
  induction a generalizing b Γ₁ with
  | forallE _ _ _ _ _ _ ih _ _ =>
    cases b with
    | forallE _ _ _ _ _ _ =>
      exact fun ⟨hlabel, hdomain, hgraph⟩ =>
        ⟨by simp [hlabel], ih σ₁ hdomain,
          Graph.Compatible.comp (f := ⟨_, _, _, _⟩) (g := ⟨_, _, _, _⟩) σ₁ hgraph⟩
    | _ => exact fun h => h
  | lam _ _ _ _ _ _ =>
    cases b with
    | lam _ _ _ _ => exact Graph.Compatible.comp (f := ⟨_, _, _, _⟩) (g := ⟨_, _, _, _⟩) σ₁
    | _ => exact fun h => h
  | succ _ _ ih =>
    cases b with
    | succ _ _ =>
      exact fun ⟨hlabel, h⟩ =>
        ⟨by simp [hlabel], ih σ₁ h⟩
    | _ => exact fun h => h
  | id _ _ _ ihA iha ihb =>
    cases b with
    | id _ _ _ => exact fun ⟨hA, ha, hb⟩ => ⟨ihA σ₁ hA, iha σ₁ ha, ihb σ₁ hb⟩
    | _ => exact fun h => h
  | _ => cases b <;> exact fun h => h

theorem Compatible.reindexHom_iff (σ : Γ₁ ⟶ Γ) :
    ∀ (a b : Shape Γ) {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁),
      Compatible σ₁ (a.reindexHom σ) (b.reindexHom σ) ↔ Compatible (σ₁ ≫ σ) a b := by
  intro a b Γ₂ σ₁
  induction a generalizing b Γ₂ <;> cases b <;>
    simp! [reindexHom, map, *]

theorem Compatible.reindexHom (σ : Γ₁ ⟶ Γ) {a b : Shape Γ} (h : Compatible (𝟙 Γ) a b) :
    Compatible (𝟙 Γ₁) (a.reindexHom σ) (b.reindexHom σ) := by
  rw [reindexHom_iff, Category.id_comp]
  simpa using h.comp σ

mutual

theorem Compatible.anti_left {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {a a' b : Shape Γ} (h : a ≤ a')
    (hab : Compatible σ a' b) : Compatible σ a b :=
  match h with
  | .collapse h => Compatible.of_isBottom_left σ h
  | .sort _ | .nat | .zero => hab
  | .forallE ha hf => by
    cases b with
    | forallE _ _ _ _ _ _ =>
      refine ⟨hab.1, Compatible.anti_left ha hab.2.1, fun i j Γ₂ σ₁ hn hin => ?_⟩
      exact Entry.anti (hf i)
        (fun j' hn' => hab.2.2 j' j σ₁ <| congr(Tm.presheaf.map (σ₁ ≫ σ).op $hn').trans hn) hin
    | _ => exact hab
  | .lam hf => by
    cases b with
    | lam _ _ _ _ =>
      intro i j Γ₂ σ₁ hn hin
      exact Entry.anti (hf i)
        (fun j' hn' => hab j' j σ₁ <| congr(Tm.presheaf.map (σ₁ ≫ σ).op $hn').trans hn) hin
    | bot => trivial
    | _ =>
      intro i
      exact match hf i with
        | .bottom hbot => hbot
        | .mem j' _ _ hout => Basis.le_bot_iff.mp (hout.trans (hab j').le)
  | .succ h => by
    cases b with
    | succ _ _ => exact ⟨hab.1, (Compatible.anti_left h hab.2 :)⟩
    | _ => exact hab
  | .id hA ha hb => by
    cases b with
    | id _ _ _ =>
      exact ⟨(Compatible.anti_left hA hab.1 :), (Compatible.anti_left ha hab.2.1 :),
        (Compatible.anti_left hb hab.2.2 :)⟩
    | _ => exact hab

theorem Entry.anti {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {g : Graph Γ} {name : Σ A : Ty Γ, Tm Γ A}
    {x y x' y' : Shape Γ} (h : Basis.Entry g name x y)
    (hg : ∀ j, g.names j = name → Compatible σ (g.ins j) x' → Compatible σ (g.outs j) y')
    (hin : Compatible σ x x') : Compatible σ y y' :=
  match h with
  | .bottom hy => Compatible.of_isBottom_left σ hy
  | .mem j hn hin' hout => Compatible.anti_left hout (hg j hn (Compatible.anti_left hin' hin))

end

theorem Compatible.anti {σ : Γ₁ ⟶ Γ} {a a' b b' : Shape Γ} (haa' : a ≤ a')
    (hbb' : b ≤ b') (h : Compatible σ a' b') : Compatible σ a b :=
  (anti_left hbb' (anti_left haa' h).symm).symm

end Shape

namespace Graph

theorem Compatible.symm {σ : Γ₁ ⟶ Γ} {f g : Graph Γ} (hfg : Compatible σ f g) :
    Compatible σ g f :=
  fun j i _ σ₁ hl hin => (hfg i j σ₁ hl.symm hin.symm).symm

theorem Compatible.reindexHom_iff (σ : Γ₁ ⟶ Γ) (f g : Graph Γ) (σ₁ : Γ₂ ⟶ Γ₁) :
    Compatible σ₁ (f.reindexHom σ) (g.reindexHom σ) ↔ Compatible (σ₁ ≫ σ) f g := by
  dsimp only [Compatible, reindexHom, map]
  simp [Shape.Compatible.reindexHom_iff]

theorem Compatible.append_left {σ : Γ₁ ⟶ Γ} {f g h : Graph Γ} (hf : Compatible σ f h)
    (hg : Compatible σ g h) : Compatible σ (f.append g) h :=
  fun i j Γ₂ σ₁ => Fin.addCases
    (fun i => by simpa using hf i j σ₁)
    (fun i => by simpa using hg i j σ₁) i

theorem Compatible.append_right {σ : Γ₁ ⟶ Γ} {f g h : Graph Γ} (hf : Compatible σ h f)
    (hg : Compatible σ h g) : Compatible σ h (f.append g) :=
  (hf.symm.append_left hg.symm).symm

theorem Compatible.of_append_left {σ : Γ₁ ⟶ Γ} {f g h : Graph Γ}
    (hfg : Compatible σ (f.append g) h) : Compatible σ f h := by
  intro i j Γ₂
  simpa using hfg (Fin.castAdd g.size i) j

theorem Compatible.of_append_right {σ : Γ₁ ⟶ Γ} {f g h : Graph Γ}
    (hfg : Compatible σ (f.append g) h) : Compatible σ g h := by
  intro i j Γ₂
  simpa using hfg (Fin.natAdd f.size i) j

theorem Compatible.anti_left {σ : Γ₁ ⟶ Γ} {f f' g : Graph Γ} (hff' : f ≤ f')
    (hfg : Compatible σ f' g) : Compatible σ f g := by
  intro i j Γ₂ σ₁ hlabel hin
  rcases hff' i with hbot | ⟨i', hname, hin', hout⟩
  · exact Shape.Compatible.of_isBottom_left _ hbot
  · refine Shape.Compatible.anti_left hout (hfg i' j σ₁ ?_ (Shape.Compatible.anti_left hin' hin))
    rw [hname]
    exact hlabel

theorem Compatible.anti {σ : Γ₁ ⟶ Γ} {f f' g g' : Graph Γ} (hff' : f ≤ f')
    (hgg' : g ≤ g') (h : Compatible σ f' g') : Compatible σ f g :=
  (anti_left hgg' (anti_left hff' h).symm).symm

abbrev InternallyCompatible (f g : Graph Γ) : Prop := Compatible (𝟙 Γ) f g

theorem InternallyCompatible.compatible {f g : Graph Γ} (hfg : InternallyCompatible f g)
    (σ : Γ₁ ⟶ Γ) : Compatible σ f g := by
  simpa using Compatible.comp σ hfg

abbrev InternallyDirected (f : Graph Γ) : Prop := InternallyCompatible f f

theorem InternallyCompatible.symm {f g : Graph Γ} (hfg : InternallyCompatible f g) :
    InternallyCompatible g f :=
  Compatible.symm hfg

theorem InternallyCompatible.reindex {f g : Graph Γ} (hfg : InternallyCompatible f g)
    (σ : Γ₁ ⟶ Γ) : InternallyCompatible (f.reindexHom σ) (g.reindexHom σ) := by
  rw [InternallyCompatible, Compatible.reindexHom_iff, Category.id_comp]
  simpa using hfg.comp σ

protected theorem InternallyDirected.nil : InternallyDirected (nil : Graph Γ) :=
  fun i => i.elim0

theorem InternallyDirected.append {f g : Graph Γ} (hf : InternallyDirected f)
    (hg : InternallyDirected g) (hfg : InternallyCompatible f g) :
    InternallyDirected (f.append g) :=
  (hf.append_right hfg).append_left (hfg.symm.append_right hg)

theorem InternallyDirected.reindex {f : Graph Γ} (hf : InternallyDirected f)
    (σ : Γ₁ ⟶ Γ) : InternallyDirected (f.reindexHom σ) :=
  InternallyCompatible.reindex hf σ

theorem InternallyDirected.of_append_left {f g : Graph Γ}
    (h : InternallyDirected (f.append g)) : InternallyDirected f :=
  Compatible.of_append_left (Compatible.symm (Compatible.of_append_left h))

theorem InternallyDirected.of_append_right {f g : Graph Γ}
    (h : InternallyDirected (f.append g)) : InternallyDirected g :=
  Compatible.of_append_right (Compatible.symm (Compatible.of_append_right h))

end Graph

end DomainSemantics
