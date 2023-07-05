import Sieves.dagur
import Mathlib.Topology.Category.CompHaus.EffectiveEpi
import Mathlib.CategoryTheory.Sites.Sheaf

open CategoryTheory CompHaus Opposite CategoryTheory.Limits Functor Presieve
 
namespace CompHaus

lemma extensivity : Extensivity CompHaus := sorry

lemma epi_pullback_of_epi : EpiPullbackOfEpi CompHaus := sorry

lemma one' : (dagurCoverage' CompHaus epi_pullback_of_epi 
    extensivity).toGrothendieck = 
    (coherentTopology CompHaus) := by
  ext X S  
  constructor
  <;> intro h 
  · dsimp [Coverage.toGrothendieck] at *
    induction h with 
    | of Y T hT => 
      · apply Coverage.saturate.of 
        dsimp [coherentCoverage]
        dsimp [dagurCoverage'] at hT 
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
          rw [CompHaus.epi_iff_surjective _] at h ⊢ 
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
          dsimp [dagurCoverage']
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
            (dagurCoverage' _ _ _).toGrothendieck R 
          · exact this 
          apply GrothendieckTopology.pullback_stable' 
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (dagurCoverage' _ _ _) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of 
            dsimp [dagurCoverage'] 
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

lemma isSheafFor_of_Dagur {X : CompHaus} {S : Presieve X}
    (hS : S ∈ (dagurCoverage' CompHaus epi_pullback_of_epi extensivity).covering X)
    {F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)} (hFpfp : PreservesFiniteProducts F) 
    (hFecs : ∀ {S : Presieve X} (_ : S ∈ DagurSieveSingle X), IsSheafFor F S) : 
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForDagurSieveIso hSIso hFpfp
  · exact hFecs hSSingle 

end CompHaus