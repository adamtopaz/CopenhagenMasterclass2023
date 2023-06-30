import Condensed.SheafCondition
import Mathlib.Condensed.Abelian
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.GroupCat.Adjunctions
import Mathlib.Topology.Category.CompHaus.Projective
import ExtrDisc.Epi
import TopCat.toCondensed
import Condensed.Equivalence

universe u

namespace Condensed

-- Free stuff

open CategoryTheory Limits Opposite

noncomputable
instance : PreservesLimits (forget AddCommGroupCat.{u+1}) :=
    AddCommGroupCat.forgetPreservesLimits.{u+1, u+1}

def forgetAb : CondensedAb.{u} ⥤ Condensed.{u} (Type (u+1)) := 
  sheafCompose _ (forget _)

noncomputable
def freeAb : Condensed.{u} (Type (u+1)) ⥤ CondensedAb.{u} := 
  Sheaf.composeAndSheafify _ <| AddCommGroupCat.free

noncomputable
def adjunction : freeAb ⊣ forgetAb := 
  CategoryTheory.Sheaf.adjunction _ AddCommGroupCat.adj

notation "ℤ[" S "]" => freeAb.obj S
notation "ℤ[" S "]" => freeAb.obj (CompHaus.toCondensed.obj S)
notation "ℤ[" S "]" => freeAb.obj 
  (CompHaus.toCondensed.obj (ExtrDisc.toCompHaus.obj S))

noncomputable
example (S : Condensed.{u} (Type (u+1))) : CondensedAb.{u} := 
  ℤ[S]

noncomputable
example (S : CompHaus) : CondensedAb.{u} := 
  ℤ[S]

noncomputable
example (S : ExtrDisc) : CondensedAb.{u} := 
  ℤ[S]

theorem epi_iff_forall_epi 
    (E X : CondensedAb.{u}) (f : E ⟶ X) :
    Epi f ↔ ∀ (S : ExtrDisc.{u}), Epi (f.val.app (op S.compHaus)) := by
  let e : CondensedAb.{u} ≌ 
    Sheaf (coherentTopology ExtrDisc.{u}) AddCommGroupCat.{u+1} := 
      ExtrDiscCompHaus.equivalence _ |>.symm
  let f' := e.functor.map f
  suffices Epi f' ↔ ∀ (S : ExtrDisc.{u}), Epi (f.val.app (op S.compHaus)) 
    by sorry
  let f'' := sheafToPresheaf _ _ |>.map f'
  suffices Epi f' ↔ Epi f'' by sorry
  sorry -- this depends on the characterization of sheaves 
  -- on ExtrDisc.

theorem projective_of_projective 
    (S : CompHaus.{u}) [Projective S] :
    Projective ℤ[S] := by
  constructor
  intro E X f e he
  rw [epi_iff_forall_epi] at he
  have : ExtremallyDisconnected S := sorry -- Gleason (the easy direction)
  let T : ExtrDisc := ⟨S⟩ 
  specialize he T
  let E' := forgetAb.obj E
  let X' := forgetAb.obj X
  let T' := CompHaus.toCondensed.obj S
  let gg : (T' ⟶ E') → (T' ⟶ X') := 
    fun q => q ≫ forgetAb.map e
  have hg : Function.Surjective gg := sorry 
    -- from he
  let f' : T' ⟶ X' := adjunction.homEquiv _ _ f
  --cases' hg f' with g' hg'
  obtain ⟨g',hg'⟩ := hg f'
  let g : ℤ[S] ⟶ E := 
    (adjunction.homEquiv _ _).symm g'
  refine ⟨g, ?_⟩
  sorry

def projIndex (A : CondensedAb.{u}) := 
  Σ (E : ExtrDisc.{u}), 
    CompHaus.toCondensed.obj E.compHaus ⟶ forgetAb.obj A

#check projIndex

instance : HasColimits CondensedAb.{u} := sorry

noncomputable
def projPres (A : CondensedAb.{u}) : 
    CondensedAb.{u} := 
  ∐ fun (E : projIndex A) => ℤ[E.1]

noncomputable
def projPresπ (A : CondensedAb.{u}) : 
    projPres A ⟶ A := 
  Sigma.desc fun ⟨_,f⟩ => 
    adjunction.homEquiv _ _|>.symm f

-- GOAL
instance : EnoughProjectives CondensedAb.{u} where
  presentation A := Nonempty.intro <| 
    { p := projPres A
      projective := sorry
      f := projPresπ A
      epi := sorry }

end Condensed


















/-
#exit

namespace Condensed

open CategoryTheory Limits Opposite

def forgetAb : CondensedAb.{u} ⥤ Condensed.{u} (Type (u+1)) :=
  letI : PreservesLimits (forget AddCommGroupCat.{u+1}) :=
    AddCommGroupCat.forgetPreservesLimits.{u+1, u+1}
  sheafCompose _ (forget _)

noncomputable
def freeAb : Condensed.{u} (Type (u+1)) ⥤ CondensedAb.{u} := 
  letI : PreservesLimits (forget AddCommGroupCat.{u+1}) :=
    AddCommGroupCat.forgetPreservesLimits.{u+1, u+1}
  Sheaf.composeAndSheafify _ (AddCommGroupCat.free)

noncomputable
def adjunctionAb : freeAb.{u} ⊣ forgetAb := 
  letI : PreservesLimits (forget AddCommGroupCat.{u+1}) :=
    AddCommGroupCat.forgetPreservesLimits.{u+1, u+1}
  CategoryTheory.Sheaf.adjunction _ AddCommGroupCat.adj

notation "ℤ[" S "]" => freeAb.obj S
notation "ℤ[" S "]" => freeAb.obj (CompHaus.toCondensed.obj S)

def _root_.String.tails (S : String) : Array String := Id.run <| do 
  let mut out := #[]
  for i in [:S.length] do 
    out := out.push <| S.extract ⟨i⟩ ⟨S.length⟩ 
  return out

def _root_.String.containsStr (S T : String) : Bool := Id.run <| do
  for tail in S.tails do
    if T.isPrefixOf tail then return true
  return false

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv 
  for (c,tp) in env.constants.toList do
    if c.isInternal then continue
    if c.toString.containsStr "preservesEpi" then 
      IO.println "---"
      IO.println c
      let e ← ppExprWithInfos { env := env } tp.type
      IO.println <| e.fmt

lemma epi_iff_extrDisc {A B : CondensedAb.{u}} 
    (f : A ⟶ B) :
    Epi f ↔ (∀ S : ExtrDisc.{u}, Epi (f.val.app (op S.compHaus))) := by
  let e := Condensed.ExtrDiscCompHaus.equivalence AddCommGroupCat.{u+1}
  let f' := e.inverse.map f
  suffices Epi f' ↔ ∀ (S : ExtrDisc), Epi (f'.val.app (op S)) by sorry
  suffices Epi f' ↔ Epi ((sheafToPresheaf _ _).map f') by sorry
  constructor
  · intro 
    have : (sheafToPresheaf (coherentTopology ExtrDisc) AddCommGroupCat).PreservesEpimorphisms := by
      constructor
      intros
      suffices PreservesColimits (sheafToPresheaf (coherentTopology ExtrDisc) AddCommGroupCat) by
        apply 
          preserves_epi_of_preservesColimit (sheafToPresheaf (coherentTopology ExtrDisc) AddCommGroupCat)
      sorry
    apply Functor.map_epi
  · intro he
    apply (sheafToPresheaf (coherentTopology ExtrDisc) AddCommGroupCat).epi_of_epi_map
    assumption

lemma projective_of_free_of_projective 
    (S : CompHaus.{u}) [Projective S] : Projective (ℤ[S]) := by
  constructor
  intro E X f e he
  rw [epi_iff_extrDisc] at he
  have : ExtremallyDisconnected S := sorry -- Gleason
  let T : ExtrDisc := ⟨S⟩ 
  let g : CompHaus.toCondensed.obj S ⟶ forgetAb.obj X := 
    adjunctionAb.homEquiv _ _ f
  specialize he T
  let thing : (CompHaus.toCondensed.obj T.compHaus ⟶ forgetAb.obj E) → 
    (CompHaus.toCondensed.obj T.compHaus ⟶ forgetAb.obj X) := 
    fun q => q ≫ forgetAb.map e -- essentially e.val.app (op T.compHaus)
  have hthing : Function.Surjective thing := sorry -- from he
  obtain ⟨g', hg'⟩ := hthing g
  let f' : ℤ[S] ⟶ E :=   
    (adjunctionAb.homEquiv _ _).symm g'
  refine ⟨f', ?_⟩ 
  sorry

instance : HasColimits CondensedAb.{u} := sorry

def projectiveIndex (B : CondensedAb.{u}) := 
  Σ (S : ExtrDisc.{u}), CompHaus.toCondensed.obj S.compHaus ⟶ forgetAb.obj B

noncomputable
def projectivePresentation (B : CondensedAb.{u}) : 
    ProjectivePresentation B where
  p := ∐ fun (⟨S,i⟩ : projectiveIndex B) => ℤ[S.compHaus]
  projective := sorry
  f := sorry
  epi := sorry

instance : EnoughProjectives CondensedAb.{u} := EnoughProjectives.mk <| 
  fun _ => ⟨projectivePresentation _⟩ 

end Condensed
-/