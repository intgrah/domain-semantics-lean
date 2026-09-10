/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Shape
import DomainSemantics.Meta.Judgement

@[expose] public section

namespace DomainSemantics

variable {Γ Γ₁ : Ctx}

namespace Basis

judgement IsBottom : Shape Γ → Prop where

  ──────────────────── bot
  IsBottom .bot

  ∀ i, IsBottom (outs i)
  ──────────────────── lam {k : Nat} {names : Fin k → Σ A : Ty Γ, Tm Γ A} {ins outs : Fin k → Shape Γ}
  IsBottom (.lam k names ins outs)

mutual

judgement LE : Shape Γ → Shape Γ → Prop where

  IsBottom a
  ──────────────────── collapse {a b : Shape Γ}
  LE a b

  ──────────────────── sort (r : Bool)
  LE (.sort r) (.sort r)

  LE a a'
  ∀ i, Entry ⟨k', names', ins', outs'⟩ (names i) (ins i) (outs i)
  ──────────────────── forallE {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a a' : Shape Γ} {k : Nat} {names : Fin k → Σ A : Ty Γ, Tm Γ A}
    {ins outs : Fin k → Shape Γ} {k' : Nat} {names' : Fin k' → Σ A : Ty Γ, Tm Γ A}
    {ins' outs' : Fin k' → Shape Γ}
  LE (.forallE label a k names ins outs) (.forallE label a' k' names' ins' outs')

  ∀ i, Entry ⟨k', names', ins', outs'⟩ (names i) (ins i) (outs i)
  ──────────────────── lam {k : Nat} {names : Fin k → Σ A : Ty Γ, Tm Γ A} {ins outs : Fin k → Shape Γ} {k' : Nat}
    {names' : Fin k' → Σ A : Ty Γ, Tm Γ A} {ins' outs' : Fin k' → Shape Γ}
  LE (.lam k names ins outs) (.lam k' names' ins' outs')

  ──────────────────── nat
  LE .nat .nat

  ──────────────────── zero
  LE .zero .zero

  LE a a'
  ──────────────────── succ {name : Σ A : Ty Γ, Tm Γ A} {a a' : Shape Γ}
  LE (.succ name a) (.succ name a')

  LE A A'
  LE a a'
  LE b b'
  ──────────────────── id {A a b A' a' b' : Shape Γ}
  LE (.id A a b) (.id A' a' b')

judgement Entry : Graph Γ → (Σ A : Ty Γ, Tm Γ A) → Shape Γ → Shape Γ → Prop where

  IsBottom y
  ──────────────────── bottom {g : Graph Γ} {name : Σ A : Ty Γ, Tm Γ A} {x y : Shape Γ}
  Entry g name x y

  g.names j = name
  LE (g.ins j) x
  LE y (g.outs j)
  ──────────────────── mem {g : Graph Γ} {name : Σ A : Ty Γ, Tm Γ A} {x y : Shape Γ} (j : Fin g.size)
  Entry g name x y

end

instance : _root_.LE (Shape Γ) := ⟨Basis.LE⟩

theorem LE.bot (b : Shape Γ) : (.bot : Shape Γ) ≤ b := .collapse .bot

theorem IsBottom.le {a b : Shape Γ} (h : IsBottom a) : a ≤ b := .collapse h

theorem le_bot_iff {a : Shape Γ} : a ≤ .bot ↔ IsBottom a :=
  ⟨fun | .collapse h => h, .collapse⟩

variable (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) in
theorem IsBottom.map {a : Shape Γ} : IsBottom a → IsBottom (a.map arg pi)
  | .bot => .bot
  | .lam h => .lam fun i => map (h i)

theorem IsBottom.of_map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) {a : Shape Γ} :
    IsBottom (a.map arg pi) → IsBottom a := by
  intro h
  induction a with
  | bot => exact .bot
  | lam _ _ _ _ _ iho =>
    cases h with
    | lam h => exact .lam fun i => iho i (h i)
  | _ => nomatch h

@[simp] theorem IsBottom.map_iff (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A))
    {a : Shape Γ} : IsBottom (a.map arg pi) ↔ IsBottom a :=
  ⟨of_map arg pi, map arg pi⟩

end Basis

namespace Graph

def LE (f g : Graph Γ) : Prop := ∀ i, Basis.Entry g (f.names i) (f.ins i) (f.outs i)

instance : _root_.LE (Graph Γ) := ⟨Graph.LE⟩

abbrev IsBottom (g : Graph Γ) : Prop := ∀ i, Basis.IsBottom (g.outs i)

theorem LE.of_isBottom {f g : Graph Γ} (hf : f.IsBottom) : f ≤ g := fun i => .bottom (hf i)

end Graph

namespace Basis

theorem LE.pi {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a a' : Shape Γ} {f g : Graph Γ} (ha : a ≤ a') (hf : f ≤ g) :
    Shape.pi label a f ≤ Shape.pi label a' g := .forallE ha hf

theorem LE.abs {f g : Graph Γ} (hf : f ≤ g) : Shape.abs f ≤ Shape.abs g := .lam hf

theorem LE.forallE_inv {label label' : Σ A : Ty Γ, Ty (Γ.extend A)} {a a' : Shape Γ} {k k' : Nat}
    {names : Fin k → Σ A : Ty Γ, Tm Γ A} {ins outs : Fin k → Shape Γ} {names' : Fin k' → Σ A : Ty Γ, Tm Γ A}
    {ins' outs' : Fin k' → Shape Γ}
    (h : Shape.forallE label a k names ins outs ≤
      Shape.forallE label' a' k' names' ins' outs') :
    label = label' ∧ a ≤ a' ∧ (⟨k, names, ins, outs⟩ : Graph Γ) ≤ ⟨k', names', ins', outs'⟩ := by
  cases h with
  | collapse h => nomatch h
  | forallE ha hf => exact ⟨rfl, ha, hf⟩

theorem LE.lam_inv {k k' : Nat} {names : Fin k → Σ A : Ty Γ, Tm Γ A} {ins outs : Fin k → Shape Γ}
    {names' : Fin k' → Σ A : Ty Γ, Tm Γ A} {ins' outs' : Fin k' → Shape Γ}
    (h : Shape.lam k names ins outs ≤ Shape.lam k' names' ins' outs') :
    (⟨k, names, ins, outs⟩ : Graph Γ) ≤ ⟨k', names', ins', outs'⟩ := by
  cases h with
  | collapse h => cases h with | lam h => exact Graph.LE.of_isBottom h
  | lam hf => exact hf

theorem LE.abs_iff {f g : Graph Γ} : Shape.abs f ≤ Shape.abs g ↔ f ≤ g := ⟨lam_inv, abs⟩

theorem LE.sort_inv {r r' : Bool} (h : (Shape.sort r : Shape Γ) ≤ .sort r') : r = r' := by
  cases h with
  | collapse h => nomatch h
  | sort => rfl

theorem LE.succ_inv {name name' : Σ A : Ty Γ, Tm Γ A} {a a' : Shape Γ}
    (h : Shape.succ name a ≤ .succ name' a') : name = name' ∧ a ≤ a' := by
  cases h with
  | collapse h => nomatch h
  | succ h => exact ⟨rfl, h⟩

theorem IsBottom.abs_iff {g : Graph Γ} : IsBottom (Shape.abs g) ↔ g.IsBottom :=
  ⟨fun | .lam h => h, .lam⟩

theorem IsBottom.abs {g : Graph Γ} (h : g.IsBottom) : IsBottom (Shape.abs g) := .lam h

theorem LE.refl : ∀ a : Shape Γ, a ≤ a
  | .bot => bot _
  | .sort r => sort r
  | .forallE _ a _ _ ins outs =>
    forallE (refl a) fun i => .mem i rfl (refl (ins i)) (refl (outs i))
  | .lam _ _ ins outs => lam fun i => .mem i rfl (refl (ins i)) (refl (outs i))
  | .nat => nat
  | .zero => zero
  | .succ _ a => succ (refl a)
  | .id A a b => id (refl A) (refl a) (refl b)

theorem LE.trans {a b c : Shape Γ} : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  induction b generalizing a c with
  | forallE _ _ _ _ _ _ ih ihi iho =>
    cases hab with
    | collapse h => exact collapse h
    | forallE ha hf =>
      cases hbc with
      | collapse h => nomatch h
      | forallE hb hg =>
        refine forallE (ih ha hb) fun i => ?_
        cases hf i with
        | bottom hy => exact .bottom hy
        | mem j hn hin hout =>
          cases hg j with
          | bottom hy => exact .bottom (le_bot_iff.mp (iho j hout hy.le))
          | mem l hn' hin' hout' =>
            exact .mem l (hn'.trans hn) (ihi j hin' hin) (iho j hout hout')
  | lam _ _ _ _ ihi iho =>
    cases hab with
    | collapse h => exact collapse h
    | lam hf =>
      cases hbc with
      | collapse h =>
        cases h with
        | lam hg =>
          refine collapse (.lam fun i => ?_)
          cases hf i with
          | bottom hy => exact hy
          | mem j _ _ hout => exact le_bot_iff.mp (iho j hout (hg j).le)
      | lam hg =>
        refine lam fun i => ?_
        cases hf i with
        | bottom hy => exact .bottom hy
        | mem j hn hin hout =>
          cases hg j with
          | bottom hy => exact .bottom (le_bot_iff.mp (iho j hout hy.le))
          | mem l hn' hin' hout' =>
            exact .mem l (hn'.trans hn) (ihi j hin' hin) (iho j hout hout')
  | succ _ _ ih =>
    cases hab with
    | collapse h => exact collapse h
    | succ hab =>
      cases hbc with
      | collapse h => nomatch h
      | succ hbc => exact succ (ih hab hbc)
  | id _ _ _ ihA iha ihb =>
    cases hab with
    | collapse h => exact collapse h
    | id hA ha hb =>
      cases hbc with
      | collapse h => nomatch h
      | id hA' ha' hb' => exact id (ihA hA hA') (iha ha ha') (ihb hb hb')
  | _ =>
    cases hab with
    | collapse h => exact collapse h
    | _ => exact hbc

theorem Entry.trans {f g : Graph Γ} (hfg : f ≤ g)
    {name : Σ A : Ty Γ, Tm Γ A} {x y : Shape Γ} : Entry f name x y → Entry g name x y
  | .bottom hy => .bottom hy
  | .mem j hn hin hout => match hfg j with
    | .bottom hy => .bottom (le_bot_iff.mp (hout.trans hy.le))
    | .mem l hn' hin' hout' => .mem l (hn'.trans hn) (hin'.trans hin) (hout.trans hout')

mutual

theorem LE.map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A))
    {a b : Shape Γ} : a ≤ b → a.map arg pi ≤ b.map arg pi
  | .collapse h => .collapse (h.map arg pi)
  | .sort r => .sort r
  | .forallE ha hf => .forallE (ha.map arg pi) fun i => (hf i).map arg pi
  | .lam hf => .lam fun i => (hf i).map arg pi
  | .nat => .nat
  | .zero => .zero
  | .succ h => .succ (h.map arg pi)
  | .id hA ha hb => .id (hA.map arg pi) (ha.map arg pi) (hb.map arg pi)

theorem Entry.map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A))
    {g : Graph Γ} {name : Σ A : Ty Γ, Tm Γ A} {x y : Shape Γ} :
    Entry g name x y →
    Entry (g.map arg pi) (arg name) (x.map arg pi) (y.map arg pi)
  | .bottom hy => .bottom (hy.map arg pi)
  | .mem j hn hin hout => .mem j (congrArg arg hn) (hin.map arg pi) (hout.map arg pi)

end

end Basis

instance : Preorder (Shape Γ) where
  le := (· ≤ ·)
  le_refl := Basis.LE.refl
  le_trans _ _ _ := Basis.LE.trans

instance : OrderBot (Shape Γ) where
  bot := .bot
  bot_le := Basis.LE.bot

theorem Shape.le_def {a b : Shape Γ} : a ≤ b ↔ Basis.LE a b := Iff.rfl

theorem Shape.le_bot_iff {a : Shape Γ} : a ≤ ⊥ ↔ Basis.IsBottom a := Basis.le_bot_iff

namespace Graph.LE

theorem refl (f : Graph Γ) : f ≤ f := fun i => .mem i rfl (Basis.LE.refl _) (Basis.LE.refl _)

theorem trans {f g h : Graph Γ} (hfg : f ≤ g) (hgh : g ≤ h) : f ≤ h :=
  fun i => (hfg i).trans hgh

theorem map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A))
    {f g : Graph Γ} (hfg : f ≤ g) : f.map arg pi ≤ g.map arg pi :=
  fun i => (hfg i).map arg pi

theorem append_left (f g : Graph Γ) : f ≤ f.append g := fun i =>
  .mem (Fin.castAdd g.size i) (append_names_left f g i)
    (by rw [append_ins_left]; exact Basis.LE.refl _) (by rw [append_outs_left]; exact Basis.LE.refl _)

theorem append_right (f g : Graph Γ) : g ≤ f.append g := fun i =>
  .mem (Fin.natAdd f.size i) (append_names_right f g i)
    (by rw [append_ins_right]; exact Basis.LE.refl _) (by rw [append_outs_right]; exact Basis.LE.refl _)

theorem append {f g h : Graph Γ} (hf : f ≤ h) (hg : g ≤ h) : f.append g ≤ h := fun i =>
  Fin.addCases (fun i => by simpa using hf i) (fun i => by simpa using hg i) i

end Graph.LE

theorem Graph.IsBottom.append {f g : Graph Γ} (hf : f.IsBottom)
    (hg : g.IsBottom) : (f.append g).IsBottom := fun i =>
  Fin.addCases (fun i => by simpa using hf i) (fun i => by simpa using hg i) i

end DomainSemantics
