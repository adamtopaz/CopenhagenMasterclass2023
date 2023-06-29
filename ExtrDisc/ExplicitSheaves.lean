import ExtrDisc.Basic
import Sieves.dagur
import Sieves.isSheafForPullbackSieve
import Mathlib.CategoryTheory.Sites.Sheaf
import ExtrDisc.Coherent


universe u v

open CategoryTheory ExtrDisc Opposite CategoryTheory.Limits

variable (C : Type _) [Category C] 

class HasPullbackOfRightMono : Prop where
  HasPullback_of_mono : ∀ (X Y Z : C) (f : X ⟶ Z) {i : Y ⟶ Z} (_ : Mono i), HasPullback f i

instance : HasPullbackOfRightMono (ExtrDisc) := sorry

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

lemma one (X : ExtrDisc) (S : Sieve X) : 
    S ∈ (dagurCoverage ExtrDisc).toDCoverage.covering X →  
    S ∈ (coherentCoverage ExtrDisc).toDCoverage.covering X := by
  dsimp [dagurCoverage, coherentCoverage, Coverage.toDCoverage] 
  intro h 
  obtain ⟨T,⟨h,hT⟩⟩ := h 
  use T 
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

lemma one' : (dagurCoverage ExtrDisc).toGrothendieck = 
    (coherentTopology ExtrDisc) := by
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
    | top => 
      · apply Coverage.saturate.top 
    | transitive Y T => 
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption  
  · induction h with 
    | of Y T hT => 
      · dsimp [coherentCoverage] at hT 
        obtain ⟨I, hI, Xmap, f, ⟨h, hT⟩⟩ := hT     
        have he := (effectiveEpiFamily_tfae Xmap f).out 0 1
        rw [he] at hT 
        let φ := fun (i : I) ↦ Sigma.ι Xmap i
        let F := Sigma.desc f
        let Z := Sieve.generate T
        have hφ : ∀ i, φ i ≫ F = f i 
        · intro i
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app] 
        have hFZ : ∀ i, Z.pullback F (φ i)
        · intro i
          simp only [Sieve.pullback_apply, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, 
            Sieve.generate_apply]
          refine' ⟨_,(𝟙 _),f i,⟨_,by simp only [Category.id_comp]⟩⟩    
          rw [h]
          exact Presieve.ofArrows.mk i
        let Xs := (∐ fun (i : I) => Xmap i)
        have fZ_mem : (Z.pullback F) ∈ 
            GrothendieckTopology.sieves (Coverage.toGrothendieck ExtrDisc 
            (dagurCoverage ExtrDisc)) Xs
        · sorry
        have hh : ∀ W (ψ : W ⟶ Xs), Coverage.saturate (dagurCoverage ExtrDisc)
            W ((Z.pullback F).pullback ψ)
        · sorry
        let Zf : Sieve Y := Sieve.generate 
          (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F)) 
        apply Coverage.saturate.transitive Y Zf  
        · apply Coverage.saturate.of 
          dsimp [dagurCoverage]
          simp only [Set.mem_union, Set.mem_setOf_eq]
          right
          use Xs 
          use F 
          refine' ⟨rfl, inferInstance⟩  
        · intro R g hZfg 
          have : ∃ τ, g = τ ≫ F := sorry
          obtain ⟨τ, this⟩ := this
          apply Coverage.saturate.transitive R (Zf.pullback g)
          · rw [this, Sieve.pullback_comp Zf]
            sorry
          · sorry
    | top => 
      · apply Coverage.saturate.top
    | transitive Y T => 
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption   

lemma isPullbackSieve_DagurCoverage (X : C) (S : Presieve X) [HasPullbackOfRightMono C]
  (hS : S ∈ (dagurCoverage C).covering X) : isPullbackPresieve S := sorry

lemma two (F : DCoverage C) : F.toCoverage.toDCoverage = F := sorry

lemma three (F : Coverage C) : F.toGrothendieck = F.toDCoverage.toCoverage.toGrothendieck := sorry


lemma is_Dagur_Presieve_iff (X : C) (S : Presieve X) [HasPullbackOfRightMono C]
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

lemma final (A : Type (u+2)) [Category.{u+1} A] [HasFiniteProducts C] (F : ExtrDisc.{u}ᵒᵖ ⥤ A)
    (hF : PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := by
  rw [← one']
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 (@fun X S hS => isSheafFor_of_Dagur X S hS _ ⟨fun J inst => _⟩)
  haveI : PreservesLimitsOfShape (Discrete J) (coyoneda.obj (op E)) := PreservesFiniteLimits.preservesFiniteLimits _
  haveI : PreservesLimitsOfShape (Discrete J) F := hF.1 J
  apply compPreservesLimitsOfShape
  
  

  
