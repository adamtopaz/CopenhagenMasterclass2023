import ExtrDisc.Basic
import Sieves.dagur
import Mathlib.CategoryTheory.Sites.Sheaf
import ExtrDisc.Coherent

universe u v

open CategoryTheory ExtrDisc Opposite CategoryTheory.Limits Functor Presieve

instance : HasPullbackOfRightMono (ExtrDisc.{u}) := sorry

lemma one (X : ExtrDisc.{u}) (S : Sieve X) : 
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
        let Xs := (∐ fun (i : I) => Xmap i)
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
          dsimp at hZfg 
          rw [Presieve.ofArrows_pUnit] at hZfg
          obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg 
          dsimp [Presieve.singleton] at hW 
          induction hW
          rw [← hW', Sieve.pullback_comp Z]
          suffices : Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
            (dagurCoverage ExtrDisc).toGrothendieck R 
          · exact this 
          apply GrothendieckTopology.pullback_stable' 
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (dagurCoverage ExtrDisc) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of 
            dsimp [dagurCoverage] 
            left
            refine' ⟨I, hI, Xmap, φ, ⟨rfl, _⟩⟩ 
            suffices : Sigma.desc φ = 𝟙 _ 
            · rw [this]
              exact inferInstance 
            ext 
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
          intro Q q hq 
          simp only [Sieve.pullback_apply, Sieve.generate_apply] 
          simp only [Sieve.generate_apply] at hq    
          obtain ⟨E, e, r, hq⟩ := hq
          refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩  
          · rw [h]
            induction hq.1
            dsimp 
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
            exact Presieve.ofArrows.mk _
          · rw [← hq.2]
            rfl
    | top => 
      · apply Coverage.saturate.top
    | transitive Y T => 
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption   

lemma isSheafForDagurSieveSingle {X : ExtrDisc} {S : Presieve X} (hS : S ∈ DagurSieveSingle X)
    (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) : IsSheafFor F S := by
  obtain ⟨Y, f, rfl, hf⟩ := hS
  have proj : Projective (toCompHaus.obj X) := inferInstanceAs (Projective X.compHaus)
  have : Epi (toCompHaus.map f) := sorry --This because `f` is surjective
  set g := toCompHaus.preimage <| Projective.factorThru (𝟙 _) (toCompHaus.map f) with hg
  have hfg : g ≫ f = 𝟙 _ := by
    refine' toCompHaus.map_injective _
    rw [map_comp, hg, image_preimage, Projective.factorThru_comp]
    rfl
  intro y hy
  refine' ⟨F.map g.op <| y f <| ofArrows.mk (), fun Z h hZ => _, fun z hz => _⟩
  · cases' hZ with u
    have := hy (f₁ := f) (f₂ := f) (𝟙 Y) (f ≫ g) (ofArrows.mk ()) (ofArrows.mk ()) ?_
    · rw [op_id, F.map_id, types_id_apply] at this
      rw [← types_comp_apply (F.map g.op) (F.map f.op), ← F.map_comp, ← op_comp]
      exact this.symm
    · rw [Category.id_comp, Category.assoc, hfg, Category.comp_id]
  · have := congr_arg (F.map g.op) <| hz f (ofArrows.mk ())
    rwa [← types_comp_apply (F.map f.op) (F.map g.op), ← F.map_comp, ← op_comp, hfg, op_id,
      F.map_id, types_id_apply] at this

lemma isSheafFor_of_Dagur {X : ExtrDisc} {S : Presieve X}
  (hS : S ∈ (dagurCoverage ExtrDisc.{u}).covering X)
  {F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)} (hF : PreservesFiniteProducts F) : S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForDagurSieveIso hSIso hF
  · exact isSheafForDagurSieveSingle hSSingle F

lemma final (A : Type (u+2)) [Category.{u+1} A] {F : ExtrDisc.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := by
  rw [← one']
  exact fun E => (Presieve.isSheaf_coverage _ _).2 <| fun S hS => isSheafFor_of_Dagur hS
    ⟨fun J inst => have := hF.1; compPreservesLimitsOfShape _ _⟩
  
  

  
