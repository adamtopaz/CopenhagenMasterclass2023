import ExtrDisc.Basic
import Sieves.dagur
import Mathlib.CategoryTheory.Sites.Sheaf
import ExtrDisc.Coherent

universe u

open CategoryTheory ExtrDisc Opposite CategoryTheory.Limits

variable (C : Type _) [Category C] [Precoherent C]

def dagurCoverage [HasFiniteCoproducts C] : Coverage C where
  covering B := 
    { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) } ∪
    { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X) 
      (fun (_ : Unit) ↦ f) ∧ Epi f }
  pullback := by sorry


lemma one : (dagurCoverage ExtrDisc).toDCoverage = (coherentCoverage ExtrDisc).toDCoverage := 
  sorry

lemma two (F : DCoverage C) : F.toCoverage.toDCoverage = F := sorry

lemma three (F : Coverage C) : F.toGrothendieck = F.toDCoverage.toCoverage.toGrothendieck := sorry

def e {X : ExtrDisc} (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) (S : Presieve X) : 
    F.obj (op X) ⟶ (∀ (Y : ExtrDisc) (s : Y ⟶ X) (_ : S s), F.obj (op Y)) := 
  fun x _ s _ ↦ F.map s.op x 

noncomputable
def p₁ {X : ExtrDisc} (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) (S : Presieve X)
    (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → HasPullback s s') : 
    (∀ (Y : ExtrDisc) (s : Y ⟶ X) (_ : S s), F.obj (op Y)) ⟶ 
    (∀ (Y : ExtrDisc) (s : Y ⟶ X) (hs : S s) (Z : ExtrDisc) (s' : Z ⟶ X) (hs' : S s'), 
    F.obj (op (@Limits.pullback _ _ _ _ _ s s' (hS s s' hs hs')))) := 
  fun x Y s hs _ s' hs' ↦ 
  F.map (@pullback.fst _ _ _ _ _ s s' (hS s s' hs hs')).op (x Y s hs)

noncomputable
def p₂ {X : ExtrDisc} (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) (S : Presieve X)
    (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → HasPullback s s') : 
    (∀ (Y : ExtrDisc) (s : Y ⟶ X) (_ : S s), F.obj (op Y)) ⟶ 
    (∀ (Y : ExtrDisc) (s : Y ⟶ X) (hs : S s) (Z : ExtrDisc) (s' : Z ⟶ X) (hs' : S s'), 
    F.obj (op (@Limits.pullback _ _ _ _ _ s s' (hS s s' hs hs')))) := 
  fun x _ s hs Z s' hs' ↦ 
  F.map (@pullback.snd _ _ _ _ _ s s' (hS s s' hs hs')).op (x Z s' hs')

variable {X : ExtrDisc} (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) (S : Presieve X)
    (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → HasPullback s s')

def IsEqualizerDiagram_vi_to_sheaf {X : ExtrDisc} (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) 
    (S : Presieve X) (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → HasPullback s s') : Prop := 
  ∀ y, (p₁ F S hS) y = (p₂ F S hS) y → ∃! x, (e F S) x = y 
  
lemma dagur115_vi_to_sheaf {X : ExtrDisc} (F : ExtrDiscᵒᵖ ⥤ Type _) (S : Presieve X)
    (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → HasPullback s s') : 
    IsEqualizerDiagram_vi_to_sheaf F S hS ↔ S.IsSheafFor F := sorry

lemma final (A : Type _) [Category A] [HasFiniteProducts C] (F : ExtrDiscᵒᵖ ⥤ A)
  (hf : PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry
