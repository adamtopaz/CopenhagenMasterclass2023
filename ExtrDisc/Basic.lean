/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ExtrDisc.Gleason
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected sets.

## Overview

This file defines the type `ExtrDisc` of all extremally (note: not "extremely"!)
disconnected spaces, and gives it the structure of a large category.

The Lean implementation: a term of type `ExtrDisc` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

This file defines the type of all extremally disconnected spaces, gives it the
structure of a large category, and proves some basic observations about this
category and various functors from it.

## Main definitions

* `ExtrDisc` : the category of extremally disconnected spaces.
* `ExtrDisc.toCompHaus` : the forgetful functor `ExtrDisc ⥤ CompHaus` from extremally disconnected
  spaces to compact Hausdorff spaces
* `ExtrDisc.toProfinite` : the functor from extremally disconnected spaces to profinite spaces.

## TODO

The following proofs need to be filled in:

* If `X` is extremally disconnected then it is totally disconnected.
* The forgetful functor `toCompHaus : ExtrDisc ⥤ CompHaus` is full and faithful.
* The functor `toProfinite : ExtrDisc ⥤ Profinite` is full and faithful.
* The category of extremally disconnected spaces has arbitrary coproducts.

-/
universe u

open CategoryTheory

/-- `ExtrDisc` is the category of extremally disconnected spaces. -/
structure ExtrDisc where
  compHaus : CompHaus.{u}
  [extrDisc : ExtremallyDisconnected compHaus]

-- the fields of the structure don't need docstrings
attribute [nolint docBlame] ExtrDisc.compHaus ExtrDisc.extrDisc

namespace CompHaus

-- Proj implies ExtrDisc
@[simps!]
def toExtrDisc (X : CompHaus.{u}) [Projective X] :
    ExtrDisc where
  compHaus := X
  extrDisc := by
    apply CompactT2.Projective.extremallyDisconnected
    intro A B _ _ _ _ _ _ f g hf hg hsurj
    have : CompactSpace (TopCat.of A) := by assumption
    have : T2Space (TopCat.of A) := by assumption
    have : CompactSpace (TopCat.of B) := by assumption
    have : T2Space (TopCat.of B) := by assumption
    let A' : CompHaus := ⟨TopCat.of A⟩ 
    let B' : CompHaus := ⟨TopCat.of B⟩ 
    let f' : X ⟶ B' := ⟨f, hf⟩
    let g' : A' ⟶ B' := ⟨g,hg⟩  
    have : Epi g' := by
      rw [CompHaus.epi_iff_surjective]
      assumption
    obtain ⟨h,hh⟩ := Projective.factors f' g'
    refine ⟨h,h.2,?_⟩ 
    ext t
    apply_fun (fun e => e t) at hh
    exact hh
   

end CompHaus

namespace ExtrDisc

/-- Extremally disconnected spaces form a large category. -/
instance : LargeCategory ExtrDisc.{u} :=
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

/-- The (forgetful) functor from extremally disconnected spaces to compact Hausdorff spaces. -/
@[simps!]
def toCompHaus : ExtrDisc.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

/-- Construct a term of `ExtrDistr` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : ExtrDisc :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

/-- The forgetful functor `ExtrDisc ⥤ CompHaus` is full. -/
instance : Full toCompHaus where
  preimage := fun f => f
  witness := fun f => by simp


/-- The forgetful functor `ExtrDisc ⥤ CompHaus` is faithful. -/
instance : Faithful toCompHaus where
  map_injective := by
    intro X Y a b h
    simp only [inducedFunctor_obj, inducedFunctor_map] at h
    exact h

/-- Extremally disconnected spaces are a concrete category. -/
instance : ConcreteCategory ExtrDisc where
  forget := toCompHaus ⋙ forget _

instance : CoeSort ExtrDisc.{u} (Type u) := ConcreteCategory.hasCoeToSort _
instance {X Y : ExtrDisc.{u}} : FunLike (X ⟶ Y) X (fun _ => Y) := ConcreteCategory.funLike

/-- Extremally disconnected spaces are topological spaces. -/
instance instTopologicalSpace (X : ExtrDisc.{u}) : TopologicalSpace X :=
  show TopologicalSpace X.compHaus from inferInstance

/-- Extremally disconnected spaces are compact. -/
instance (X : ExtrDisc.{u}) : CompactSpace X :=
  show CompactSpace X.compHaus from inferInstance

/-- Extremally disconnected spaces are Hausdorff. -/
instance (X : ExtrDisc.{u}) : T2Space X :=
  show T2Space X.compHaus from inferInstance

instance (X : ExtrDisc.{u}) : ExtremallyDisconnected X :=
  X.2

/-- Extremally disconnected spaces are totally disconnected. -/
instance (X : ExtrDisc.{u}) : TotallySeparatedSpace X :=
{ isTotallySeparated_univ := by
    intro x _ y _ hxy
    obtain ⟨U, V, hUV⟩ := T2Space.t2 x y hxy
    use closure U
    use (closure U)ᶜ
    refine ⟨ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩
    simp only [Set.mem_compl_iff]
    rw [mem_closure_iff]
    push_neg
    use V
    refine' ⟨hUV.2.1,hUV.2.2.2.1,_⟩
    rw [Set.nonempty_iff_ne_empty]
    simp only [not_not]
    rw [← Set.disjoint_iff_inter_eq_empty, disjoint_comm]
    exact hUV.2.2.2.2 }

instance (X : ExtrDisc.{u}) : TotallyDisconnectedSpace X := inferInstance

/-- The functor from extremally disconnected spaces to profinite spaces. -/
@[simps]
def toProfinite : ExtrDisc.{u} ⥤ Profinite.{u} where
  obj X := {
    toCompHaus := X.compHaus,
    IsTotallyDisconnected := show TotallyDisconnectedSpace X from inferInstance }
  map f := f

/-- The functor from extremally disconnected spaces to profinite spaces is full. -/
instance : Full toProfinite := sorry
instance : Faithful toProfinite := sorry

example : toProfinite ⋙ profiniteToCompHaus = toCompHaus :=
  rfl

-- TODO: Gleason's theorem.
instance (X : ExtrDisc) : Projective X.compHaus where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.compHaus.toTop := X.extrDisc
    have hf : f.1.Surjective
    · rwa [CompHaus.epi_iff_surjective] at *
    use ⟨_, (gleason_diagram_commutes φ.continuous f.continuous hf).left⟩
    ext
    exact congr_fun (gleason_diagram_commutes φ.continuous f.continuous hf).right _

end ExtrDisc

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is an extremally disconnected space
  equipped with an epimorphism down to `X`. It is a "constructive" witness to the
  fact that `CompHaus` has enough projectives.  -/
noncomputable
def presentation (X : CompHaus) : ExtrDisc where
  compHaus := (projectivePresentation X).p
  extrDisc := by
    refine' CompactT2.Projective.extremallyDisconnected
      (@fun Y Z _ _ _ _ _ _ f g hfcont hgcont hgsurj => _)
    let g₁ : (CompHaus.of Y) ⟶ (CompHaus.of Z) := ⟨g, hgcont⟩
    let f₁ : (projectivePresentation X).p ⟶ (CompHaus.of Z) := ⟨f, hfcont⟩
    have hg₁ : Epi g₁ := (epi_iff_surjective _).2 hgsurj
    refine' ⟨Projective.factorThru f₁ g₁, (Projective.factorThru f₁ g₁).2, funext (fun _ => _)⟩
    change (Projective.factorThru f₁ g₁ ≫ g₁) _ = f _
    rw [Projective.factorThru_comp]
    rfl

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentationπ (X : CompHaus) : X.presentation.compHaus ⟶ X :=
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance epiPresentπ (X : CompHaus) : Epi X.presentationπ :=
  (projectivePresentation X).epi

/--

               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y

If `Z` is extremally disconnected, X, Y are compact Hausdorff, if `f : X ⟶ Y` is an epi and `e : Z ⟶ Y` is
arbitrary, then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It exists because
`Z` is a projective object in `CompHaus`.
-/
noncomputable
def lift {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] : Z.compHaus ⟶ X :=
  Projective.factorThru e f

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

end CompHaus

/-!
This section contains helper lemmas about the sigma-type `Σ i, π i`,
they probably belong into a different place.
-/
section Sigma

@[simp]
theorem mem_sigma_iff {π : ι → Type _} [∀ i, TopologicalSpace (π i)]
  {i : ι} {x : π i} {s : Set (Σ i, π i)}
    : x ∈ Sigma.mk i ⁻¹' s ↔ ⟨i, x⟩ ∈ s :=
  Iff.rfl

lemma sigma_mk_preimage_image' (h : i ≠ j) : Sigma.mk j ⁻¹' (Sigma.mk i '' U) = ∅ := by
  change Sigma.mk j ⁻¹' {⟨i, u⟩ | u ∈ U} = ∅
  -- change { x | (Sigma.mk j) x ∈ {⟨i, u⟩ | u ∈ U}} = ∅
  simp [h]

lemma sigma_mk_preimage_image_eq_self : Sigma.mk i ⁻¹' (Sigma.mk i '' U) = U := by
  change Sigma.mk i ⁻¹' {⟨i, u⟩ | u ∈ U} = U
  simp

-- Note: It might be possible to use Gleason for this instead
/-- The sigma-type of extremally disconneted spaces is extremally disconnected -/
instance instExtremallyDisconnected
    {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [h₀ : ∀ i, ExtremallyDisconnected (π i)] :
    ExtremallyDisconnected (Σi, π i) := by
  constructor
  intro s hs
  rw [isOpen_sigma_iff] at hs ⊢
  intro i
  rcases h₀ i with ⟨h₀⟩
  have h₁ : IsOpen (closure (Sigma.mk i ⁻¹' s))
  · apply h₀
    exact hs i
  suffices h₂ : Sigma.mk i ⁻¹' closure s = closure (Sigma.mk i ⁻¹' s)
  · rwa [h₂]
  apply IsOpenMap.preimage_closure_eq_closure_preimage
  intro U _
  · rw [isOpen_sigma_iff]
    intro j
    by_cases ij : i = j
    · rw [← ij]
      rw [sigma_mk_preimage_image_eq_self]
      assumption
    · rw [sigma_mk_preimage_image' ij]
      apply isOpen_empty
  · continuity

end Sigma

namespace ExtrDisc

/-!
This section defines the finite Coproduct of a finite family
of profinite spaces `X : α → ExtrDisc.{u}`

Notes: The content is mainly copied from
`Mathlib/Topology/Category/CompHaus/ExplicitLimits.lean`
-/
section FiniteCoproducts

open Limits

-- Assume we have `X a → B` which are jointly surjective.
variable {α : Type} [Fintype α] {B : ExtrDisc.{u}}
  (X : α → ExtrDisc.{u}) (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)


/--
The coproduct of a finite family of objects in `ExtrDisc`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : ExtrDisc := ExtrDisc.of <| Σ (a : α), X a

/-- The inclusion of one of the factors into the explicit finite coproduct. -/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a ; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : ExtrDisc.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
@[simps]
def finiteCoproduct.cocone : Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/-- The explicit finite coproduct cocone is a colimit cocone. -/
@[simps]
def finiteCoproduct.isColimit : IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

-- TODO: Do we even need this?
-- /-- The category of extremally disconnected spaces has arbitrary coproducts. -/
-- instance : Limits.HasCoproducts ExtrDisc.{u} := sorry

/-- The category of extremally disconnected spaces has finite coproducts.

Note: If one had arbitrary coproducts, this could be
`:= Limits.hasFiniteCoproducts_of_hasCoproducts.{u} ExtrDisc.{u}`.
However, since we constructed explicit finite coproducts above, and we don't need
arbitrary coproducts in `ExtrDisc.effectiveEpiFamily_tfae`, we use these finite
coproducts instead.
-/
instance hasFiniteCoproducts : HasFiniteCoproducts ExtrDisc.{u} where
  out n := {
    has_colimit := fun F => {
      exists_colimit := ⟨{
        cocone := {
          pt := finiteCoproduct (F.obj ⟨·⟩)
          ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι (F.obj ⟨·⟩) a }
        isColimit := {
          desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
          fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
          uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
            specialize hm ⟨a⟩
            ext t
            apply_fun (fun q => q t) at hm
            exact hm }}⟩}}

end FiniteCoproducts

end ExtrDisc

namespace CompHaus

lemma Gleason (X : CompHaus.{u}) : 
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    show ExtremallyDisconnected X.toExtrDisc
    infer_instance
  · intro h
    let X' : ExtrDisc := ⟨X⟩ 
    show Projective X'.compHaus
    apply ExtrDisc.instProjectiveCompHausCategoryCompHaus

end CompHaus
