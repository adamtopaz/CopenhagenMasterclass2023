import ExtrDisc.Basic
import Sieves.dagur
import Sieves.isSheafForPullbackSieve
import Mathlib.CategoryTheory.Sites.Sheaf
import ExtrDisc.Coherent


universe u v

open CategoryTheory ExtrDisc Opposite CategoryTheory.Limits

variable (C : Type _) [Category C] 

class HasPullbackOfRightMono : Prop where
  HasPullback_of_mono : ∀ (X Y Z : C) (f : X ⟶ Z) {i : Y ⟶ Z} (_ : CategoryTheory.Mono i),
    HasPullback f i

variable [Precoherent C] [HasFiniteCoproducts C]

def DagurSieveIso (B : C) := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }

def DagurSieveSingle (B : C) := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
      (fun (_ : Unit) ↦ f) ∧ Epi f }


def dagurCoverage [HasPullbackOfRightMono C] : Coverage C where
  -- covering B := 
    -- { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    -- S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) } ∪
    -- { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X) 
    --   (fun (_ : Unit) ↦ f) ∧ Epi f }
  covering B :=   (DagurSieveIso C B) ∪ (DagurSieveSingle C B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · set S' := @Presieve.ofArrows C _ Y Unit _ (fun (_ : Unit) ↦ (𝟙 Y)) with hS'
      use S'
      rw [Set.mem_union]
      constructor
      · apply Or.intro_right
        simp only [Set.mem_setOf_eq]
        exact ⟨Y, 𝟙 _, hS', instEpiIdToCategoryStruct _⟩
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rw [Presieve.ofArrows_pUnit] at hg
        induction hg
        simp only [Category.id_comp]
        use sigmaObj Z
        let e := Sigma.desc π
        use f ≫ (CategoryTheory.inv e)
        use e
        constructor
        · rw [hS]
          -- convert @Presieve.ofArrows.mk C _ X _ Z π
          sorry
        · simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    sorry


lemma one : (dagurCoverage ExtrDisc).toDCoverage = (coherentCoverage ExtrDisc).toDCoverage := by
  ext X S  
  dsimp [dagurCoverage, coherentCoverage, Coverage.toDCoverage] 
  constructor
  <;> intro h 
  <;> obtain ⟨T,⟨h,hT⟩⟩ := h 
  · use T 
    refine' ⟨_, by assumption⟩  
    simp only [Set.mem_union, Set.mem_setOf_eq] at h 
    apply Or.elim h 
    <;> intro h
    · obtain ⟨α, x, Xmap, π, h⟩ := h
      use α
      use x
      use Xmap 
      use π 
      refine' ⟨h.1,_⟩  
      have he := (effectiveEpiFamily_tfae Xmap π).out 0 1
      rw [he]
      letI := h.2
      exact inferInstance
    · obtain ⟨Y, f, h⟩ := h
      use Unit
      use inferInstance 
      use (fun _ ↦ Y) 
      use (fun _ ↦ f)
      refine' ⟨h.1,_⟩  
      have he := (effectiveEpiFamily_tfae (fun (_ : Unit) ↦ Y) (fun _ ↦ f)).out 0 1
      rw [he] 
      rw [ExtrDisc.epi_iff_surjective _] at h ⊢ 
      intro x 
      obtain ⟨y,hy⟩ := h.2 x  
      use Sigma.ι (fun (_ : Unit) ↦ Y) Unit.unit y 
      rw [← hy]
      suffices : (f : Y → X) = Sigma.ι (fun (_ : Unit) ↦ Y) Unit.unit ≫ Sigma.desc (fun _ ↦ f)
      · rw [this]
        rfl
      simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]        
  · sorry

lemma one' : (dagurCoverage ExtrDisc).toGrothendieck = 
    (coherentCoverage ExtrDisc).toGrothendieck := by
  ext X S  
  constructor
  <;> intro h 
  · dsimp [Coverage.toGrothendieck] at *
    induction h with 
    | of Y T hT => 
      · apply Coverage.saturate.of 
        dsimp [coherentCoverage]
        dsimp [dagurCoverage] at hT 
        apply Or.elim hT
        <;> intro h
        · obtain ⟨α, x, Xmap, π, h⟩ := h
          use α
          use x
          use Xmap 
          use π 
          refine' ⟨h.1,_⟩  
          have he := (effectiveEpiFamily_tfae Xmap π).out 0 1
          rw [he]
          letI := h.2
          exact inferInstance
        · obtain ⟨Z, f, h⟩ := h
          use Unit
          use inferInstance 
          use (fun _ ↦ Z) 
          use (fun _ ↦ f)
          refine' ⟨h.1,_⟩  
          have he := (effectiveEpiFamily_tfae (fun (_ : Unit) ↦ Z) (fun _ ↦ f)).out 0 1
          rw [he] 
          rw [ExtrDisc.epi_iff_surjective _] at h ⊢ 
          intro x 
          obtain ⟨y,hy⟩ := h.2 x  
          use Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit y 
          rw [← hy]
          suffices : (f : Z → Y) = Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit ≫ Sigma.desc (fun _ ↦ f)
          · rw [this]
            rfl
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]        
    | top Y => 
      · apply Coverage.saturate.top 
    | transitive Y T => 
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption  
  · induction h with 
    | of Y T hT => 
      · sorry    
    | top Y => 
      · apply Coverage.saturate.top
    | transitive Y T => 
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption   

lemma isPullbackSieve_DagurCoverage (X : C) (S : Presieve X)
  (hS : S ∈ (dagurCoverage C).covering X) : isPullbackPresieve S := sorry

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
    exact pullback.condition
  · sorry


lemma is_Dagur_Presieve_iff (X : C) (S : Presieve X)
  (hS : S ∈ (dagurCoverage C).covering X) : ( ∃ (α : Type) (_ : Fintype α) (Z : α → C)
    (π : (a : α) → (Z a ⟶ X)),
    S = Presieve.ofArrows Z π ∧ IsIso (Sigma.desc π))
   ∨ (∃ (Z : C) (f : Z ⟶ X), S = Presieve.ofArrows (fun (_ : Unit) ↦ Z) 
      (fun (_ : Unit) ↦ f) ∧ Epi f) := by
    rcases hS with (H | H)
    · apply Or.intro_left
      exact H
    · apply Or.intro_right
      exact H 


lemma isSheafFor_of_Dagur (X : ExtrDisc) (S : Presieve X)
  (hS : S ∈ (dagurCoverage ExtrDisc.{u}).covering X)
  (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) (hF : PreservesFiniteProducts F) : S.IsSheafFor F := by
  rcases (is_Dagur_Presieve_iff ExtrDisc X S hS) with H | H
  · have : isPullbackPresieve S := (isPullbackSieve_DagurCoverage ExtrDisc X S hS)
    replace this := (Equalizer.Presieve.sheaf_condition' F this).mpr
    apply this
    sorry
  · sorry


lemma final (A : Type u) [Category A] [HasLimits A] (s : A ⥤ Type (u+1)) [PreservesLimits s]
    [ReflectsIsomorphisms s] (F : ExtrDiscᵒᵖ ⥤ A) (hF : PreservesFiniteProducts F) : 
    Presheaf.IsSheaf (coherentTopology ExtrDisc) F := by
  rw [CategoryTheory.Presheaf.IsSheaf]--, Presheaf.isLimit_iff_isSheafFor]
