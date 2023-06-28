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

def IsEqualizerDiagram_vi_to_sheaf {X : ExtrDisc} (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) 
    (S : Presieve X) (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → HasPullback s s') : Prop := 
  ∀ y, (p₁ F S hS) y = (p₂ F S hS) y → ∃! x, (e F S) x = y 
  
lemma dagur115_vi_to_sheaf {X : ExtrDisc} (F : ExtrDiscᵒᵖ ⥤ Type _) (S : Presieve X)
    (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → HasPullback s s') : 
    IsEqualizerDiagram_vi_to_sheaf F S hS ↔ S.IsSheafFor F := by
  constructor
  <;> intro h
  · -- rw [CategoryTheory.Presieve.isSheafFor_iff_generate]
    dsimp [Presieve.IsSheafFor]
    intro T hT 
    dsimp [Presieve.FamilyOfElements.IsAmalgamation]
    dsimp [IsEqualizerDiagram_vi_to_sheaf] at h
    dsimp [Presieve.FamilyOfElements] at T 
    specialize h T
    dsimp [p₁, p₂, e] at h 
    suffices : ∃! x, (fun _ s _ ↦ F.map s.op x) = T 
    · obtain ⟨x, h⟩ := this 
      apply ExistsUnique.intro x _ _
      · dsimp at h 
        rw [← h.1] 
        intro Y f hf
        rfl
      · intro y 
        have h' := h.2 y 
        intro _
        apply h' 
        dsimp at h 
        rw [← h.1]
        ext
        sorry
    apply h 
    ext Y f hf Z g hg
    dsimp [Presieve.FamilyOfElements.Compatible] at hT
    letI := hS f g hf hg  
    apply hT pullback.fst pullback.snd hf hg  
    simp

  · sorry

lemma final (A : Type _) [Category A] [HasFiniteProducts C] (F : ExtrDiscᵒᵖ ⥤ A)
  (hf : PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry
