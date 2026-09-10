/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.InternalCoherence
public import Mathlib.CategoryTheory.Subfunctor.Basic
import DomainSemantics.Meta.Judgement

@[expose] public section

namespace DomainSemantics

open CategoryTheory Opposite

variable {Γ Γ₁ Γ₂ : Ctx}

judgement Shape.IsCoherent (Γ : Ctx) : Shape Γ → Prop where

  ──────────────────── bot
  IsCoherent Γ .bot

  ──────────────────── sort {r : Bool}
  IsCoherent Γ (.sort r)

  IsCoherent Γ a
  Graph.InternallyDirected ⟨k, names, ins, outs⟩
  ∀ i, IsCoherent Γ (ins i)
  ∀ i, IsCoherent Γ (outs i)
  ──────────────────── forallE {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a : Shape Γ} {k : Nat}
    {names : Fin k → Σ A : Ty Γ, Tm Γ A} {ins outs : Fin k → Shape Γ}
  IsCoherent Γ (.forallE label a k names ins outs)

  Graph.InternallyDirected ⟨k, names, ins, outs⟩
  ∀ i, IsCoherent Γ (ins i)
  ∀ i, IsCoherent Γ (outs i)
  ──────────────────── lam {k : Nat} {names : Fin k → Σ A : Ty Γ, Tm Γ A} {ins outs : Fin k → Shape Γ}
  IsCoherent Γ (.lam k names ins outs)

  ──────────────────── nat
  IsCoherent Γ .nat

  ──────────────────── zero
  IsCoherent Γ .zero

  IsCoherent Γ a
  ──────────────────── succ {name : Σ A : Ty Γ, Tm Γ A} {a : Shape Γ}
  IsCoherent Γ (.succ name a)

  IsCoherent Γ A
  IsCoherent Γ a
  IsCoherent Γ b
  ──────────────────── id {A a b : Shape Γ}
  IsCoherent Γ (.id A a b)

structure Graph.IsCoherent (Γ : Ctx) (f : Graph Γ) : Prop where
  directed : f.InternallyDirected
  ins : ∀ i, Shape.IsCoherent Γ (f.ins i)
  outs : ∀ i, Shape.IsCoherent Γ (f.outs i)

namespace Shape.IsCoherent

theorem pi {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a : Shape Γ} {f : Graph Γ}
    (ha : IsCoherent Γ a) (hf : Graph.IsCoherent Γ f) : IsCoherent Γ (pi label a f) :=
  .forallE ha hf.directed hf.ins hf.outs

theorem abs {f : Graph Γ} (hf : Graph.IsCoherent Γ f) : IsCoherent Γ (abs f) :=
  .lam hf.directed hf.ins hf.outs

theorem forallE_inv {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a : Shape Γ} {k : Nat}
    {names : Fin k → Σ A : Ty Γ, Tm Γ A} {ins outs : Fin k → Shape Γ}
    (h : IsCoherent Γ (.forallE label a k names ins outs)) :
    IsCoherent Γ a ∧ Graph.IsCoherent Γ ⟨k, names, ins, outs⟩ := by
  cases h with
  | forallE ha hd hi ho => exact ⟨ha, ⟨hd, hi, ho⟩⟩

theorem reindex (σ : Γ₁ ⟶ Γ) {a : Shape Γ} (h : IsCoherent Γ a) :
    IsCoherent Γ₁ (a.reindexHom σ) := by
  induction h with
  | forallE _ hd _ _ ih ihi iho => exact .forallE ih (hd.reindex σ) ihi iho
  | lam hd _ _ ihi iho => exact .lam (hd.reindex σ) ihi iho
  | _ => constructor <;> solve_by_elim

theorem compatible_self {a : Shape Γ} (σ : Γ₁ ⟶ Γ) : IsCoherent Γ a → Compatible σ a a
  | .bot => ⟨⟩
  | .sort => rfl
  | .forallE h hd _ _ => ⟨rfl, compatible_self σ h, hd.compatible σ⟩
  | .lam hd _ _ => hd.compatible σ
  | .nat => ⟨⟩
  | .zero => ⟨⟩
  | .succ h => ⟨rfl, compatible_self σ h⟩
  | .id h₁ h₂ h₃ => ⟨compatible_self σ h₁, compatible_self σ h₂, compatible_self σ h₃⟩

end Shape.IsCoherent

namespace Graph.IsCoherent

theorem reindex (σ : Γ₁ ⟶ Γ) {f : Graph Γ} (hf : IsCoherent Γ f) :
    IsCoherent Γ₁ (f.reindexHom σ) :=
  ⟨hf.directed.reindex σ, fun i => (hf.ins i).reindex σ, fun i => (hf.outs i).reindex σ⟩

protected theorem nil : IsCoherent Γ (nil : Graph Γ) :=
  ⟨InternallyDirected.nil, fun i => i.elim0, fun i => i.elim0⟩

theorem single {label : Σ A : Ty Γ, Tm Γ A} {a b : Shape Γ} (ha : Shape.IsCoherent Γ a)
    (hb : Shape.IsCoherent Γ b) : IsCoherent Γ (single label a b) :=
  ⟨fun _ _ _ σ₁ _ _ => hb.compatible_self (σ₁ ≫ 𝟙 Γ), fun _ => ha, fun _ => hb⟩

theorem append {f g : Graph Γ} (hf : IsCoherent Γ f) (hg : IsCoherent Γ g)
    (hfg : InternallyCompatible f g) : IsCoherent Γ (f.append g) where
  directed := hf.directed.append hg.directed hfg
  ins := Fin.addCases (by simpa using hf.ins) (by simpa using hg.ins)
  outs := Fin.addCases (by simpa using hf.outs) (by simpa using hg.outs)

end Graph.IsCoherent

def Shape.coherent : Subfunctor Shape.presheaf where
  obj Γ₁ := {a | IsCoherent Γ₁.unop a}
  map σ₁ _ ha := ha.reindex σ₁.unop

abbrev CoherentShape (Γ₁ : Ctx) := {a : Shape Γ₁ // a ∈ Shape.coherent.obj (op Γ₁)}

def CoherentGraph (Γ : Ctx) := {f : Graph Γ // Graph.IsCoherent Γ f}

namespace CoherentShape

noncomputable abbrev presheaf := Shape.coherent.toFunctor

noncomputable def reindex {Γ₁ Γ₂ : Ctx} (σ₁ : Γ₁ ⟶ Γ₂) : CoherentShape Γ₂ → CoherentShape Γ₁ :=
  presheaf.map σ₁.op

@[simp] theorem reindex_val {Γ₁ Γ₂ : Ctx} (σ₁ : Γ₁ ⟶ Γ₂) (a : CoherentShape Γ₂) :
    (reindex σ₁ a).1 = a.1.reindexHom σ₁ := rfl

@[simp] theorem reindex_id {Γ₁ : Ctx} (a : CoherentShape Γ₁) : reindex (𝟙 Γ₁) a = a :=
  presheaf.map_id_apply (op Γ₁) a

@[simp] theorem reindex_reindex {Γ₁ Γ₂ Γ₃ : Ctx} (σ : Γ₁ ⟶ Γ₂) (σ₁ : Γ₃ ⟶ Γ₁)
    (a : CoherentShape Γ₂) : reindex σ₁ (reindex σ a) = reindex (σ₁ ≫ σ) a :=
  (presheaf.map_comp_apply σ.op σ₁.op a).symm

instance : Preorder (CoherentShape Γ) := Subtype.preorder _

instance : OrderBot (CoherentShape Γ) where
  bot := ⟨⊥, .bot⟩
  bot_le a := Basis.LE.bot a.1

theorem le_def {a b : CoherentShape Γ} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

theorem le_bot_iff {a : CoherentShape Γ} : a ≤ ⊥ ↔ Basis.IsBottom a.1 := Basis.le_bot_iff

theorem LE.reindex (σ : Γ₁ ⟶ Γ) {a b : CoherentShape Γ} (h : a ≤ b) : reindex σ a ≤ reindex σ b :=
  h.map _ _

def Compatible (a b : CoherentShape Γ) : Prop := Shape.Compatible (𝟙 Γ) a.1 b.1

namespace Compatible

theorem symm {a b : CoherentShape Γ} (hab : Compatible a b) : Compatible b a :=
  Shape.Compatible.symm hab

theorem reindex (σ : Γ₁ ⟶ Γ) {a b : CoherentShape Γ} (hab : Compatible a b) :
    Compatible (CoherentShape.reindex σ a) (CoherentShape.reindex σ b) :=
  Shape.Compatible.reindexHom σ hab

theorem of_common_upper {a b c : CoherentShape Γ} (hac : a ≤ c) (hbc : b ≤ c) : Compatible a b :=
  Shape.Compatible.anti hac hbc (c.2.compatible_self _)

theorem of_exists_upper {a b : CoherentShape Γ} (h : ∃ c, a ≤ c ∧ b ≤ c) : Compatible a b :=
  h.elim fun _ ⟨hac, hbc⟩ => of_common_upper hac hbc

end Compatible

theorem compatible_reindex_iff (σ₁ : Γ₁ ⟶ Γ) (a b : CoherentShape Γ) :
    Compatible (reindex σ₁ a) (reindex σ₁ b) ↔ Shape.Compatible σ₁ a.1 b.1 := by
  simp [Compatible, reindex_val, Shape.Compatible.reindexHom_iff]

def piAtom (label : Σ A : Ty Γ, Ty (Γ.extend A)) : CoherentShape Γ :=
  ⟨.pi label .bot .nil, .pi .bot .nil⟩

def identityMap (a b c : CoherentShape Γ) : CoherentShape Γ := ⟨.id a.1 b.1 c.1, .id a.2 b.2 c.2⟩

end CoherentShape

namespace CoherentGraph

noncomputable def reindex (σ : Γ₁ ⟶ Γ) (f : CoherentGraph Γ) : CoherentGraph Γ₁ := ⟨f.1.reindexHom σ, f.2.reindex σ⟩

@[simp] theorem reindex_val (σ : Γ₁ ⟶ Γ) (f : CoherentGraph Γ) : (f.reindex σ).1 = f.1.reindexHom σ := rfl

@[simp] theorem reindex_id (f : CoherentGraph Γ) : f.reindex (𝟙 Γ) = f :=
  Subtype.ext (Graph.reindexHom_id f.1)

@[simp] theorem reindex_reindex (σ : Γ₁ ⟶ Γ) (σ₁ : Γ₂ ⟶ Γ₁) (f : CoherentGraph Γ) :
    (f.reindex σ).reindex σ₁ = f.reindex (σ₁ ≫ σ) :=
  Subtype.ext (Graph.reindexHom_comp σ σ₁ f.1).symm

def nil (Γ : Ctx) : CoherentGraph Γ := ⟨.nil, .nil⟩

def single (label : Σ A : Ty Γ, Tm Γ A) (a b : CoherentShape Γ) : CoherentGraph Γ :=
  ⟨.single label a.1 b.1, .single a.2 b.2⟩

def append (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1) : CoherentGraph Γ :=
  ⟨f.1.append g.1, f.2.append g.2 hfg⟩

@[simp] theorem append_val (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1) :
    (f.append g hfg).1 = f.1.append g.1 := rfl

theorem reindex_append (σ : Γ₁ ⟶ Γ) (f g : CoherentGraph Γ)
    (hfg : Graph.InternallyCompatible f.1 g.1) :
    (f.append g hfg).reindex σ = (f.reindex σ).append (g.reindex σ) (hfg.reindex σ) :=
  Subtype.ext (Graph.map_append _ _ f.1 g.1)

def input (f : CoherentGraph Γ) (i : Fin f.1.size) : CoherentShape Γ := ⟨f.1.ins i, f.2.ins i⟩

def output (f : CoherentGraph Γ) (i : Fin f.1.size) : CoherentShape Γ := ⟨f.1.outs i, f.2.outs i⟩

@[simp] theorem input_append_left (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1)
    (i : Fin f.1.size) : (f.append g hfg).input (Fin.castAdd g.1.size i) = f.input i :=
  Subtype.ext (Graph.append_ins_left f.1 g.1 i)

@[simp] theorem input_append_right (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1)
    (i : Fin g.1.size) : (f.append g hfg).input (Fin.natAdd f.1.size i) = g.input i :=
  Subtype.ext (Graph.append_ins_right f.1 g.1 i)

@[simp] theorem output_append_left (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1)
    (i : Fin f.1.size) : (f.append g hfg).output (Fin.castAdd g.1.size i) = f.output i :=
  Subtype.ext (Graph.append_outs_left f.1 g.1 i)

@[simp] theorem output_append_right (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1)
    (i : Fin g.1.size) : (f.append g hfg).output (Fin.natAdd f.1.size i) = g.output i :=
  Subtype.ext (Graph.append_outs_right f.1 g.1 i)

def lamGenerator (f : CoherentGraph Γ) : CoherentShape Γ := ⟨.abs f.1, .abs f.2⟩

theorem lamGenerator_le_iff {f g : CoherentGraph Γ} :
    lamGenerator f ≤ lamGenerator g ↔ f.1 ≤ g.1 :=
  Basis.LE.abs_iff

theorem lamGenerator_le_bot_iff {f : CoherentGraph Γ} : lamGenerator f ≤ ⊥ ↔ f.1.IsBottom :=
  CoherentShape.le_bot_iff.trans Basis.IsBottom.abs_iff

theorem lamGenerator_le_append_left (f g : CoherentGraph Γ)
    (hfg : Graph.InternallyCompatible f.1 g.1) : lamGenerator f ≤ lamGenerator (f.append g hfg) :=
  Basis.LE.abs (Graph.LE.append_left f.1 g.1)

theorem lamGenerator_le_append_right (f g : CoherentGraph Γ)
    (hfg : Graph.InternallyCompatible f.1 g.1) : lamGenerator g ≤ lamGenerator (f.append g hfg) :=
  Basis.LE.abs (Graph.LE.append_right f.1 g.1)

end CoherentGraph

namespace CoherentShape

def piGenerator (label : Σ A : Ty Γ, Ty (Γ.extend A)) (a : CoherentShape Γ) (f : CoherentGraph Γ) :
    CoherentShape Γ :=
  ⟨.pi label a.1 f.1, .pi a.2 f.2⟩

theorem piGenerator_le_append_left (label : Σ A : Ty Γ, Ty (Γ.extend A)) {a c : CoherentShape Γ}
    (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1) (hac : a ≤ c) :
    piGenerator label a f ≤ piGenerator label c (f.append g hfg) :=
  Basis.LE.pi hac (Graph.LE.append_left f.1 g.1)

theorem piGenerator_le_append_right (label : Σ A : Ty Γ, Ty (Γ.extend A)) {b c : CoherentShape Γ}
    (f g : CoherentGraph Γ) (hfg : Graph.InternallyCompatible f.1 g.1) (hbc : b ≤ c) :
    piGenerator label b g ≤ piGenerator label c (f.append g hfg) :=
  Basis.LE.pi hbc (Graph.LE.append_right f.1 g.1)

theorem label_eq_of_piAtom_le_piGenerator {label label' : Σ A : Ty Γ, Ty (Γ.extend A)}
    {a : CoherentShape Γ} {f : CoherentGraph Γ} (h : piAtom label' ≤ piGenerator label a f) :
    label' = label :=
  (Basis.LE.forallE_inv h).1

end CoherentShape

end DomainSemantics
