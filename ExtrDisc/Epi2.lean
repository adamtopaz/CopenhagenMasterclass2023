import ExtrDisc.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.ExplicitLimits
--import Mathlib.Topology.Category.CompHaus.EffectiveEpi


import Profinite.Epi

open CategoryTheory Limits

namespace ExtrDisc

universe u

-- For mathlib?
/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : ExtrDisc :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

-- -- For mathlib?
instance {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [∀ i, ExtremallyDisconnected (π i)] :
    ExtremallyDisconnected (Σi, π i) := by
  sorry
--   refine ⟨fun s hs₁ hs₂ ⟨a, hs₃⟩  => ?_⟩
--   simp at hs₃

--   obtain rfl | h := s.eq_empty_or_nonempty
--   · sorry -- exact Set.subsingleton_empty
--   · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
--     exact ht.isPreconnected.subsingleton.image _



/-!
TODO

This section is copied from
`Mathlib/Topology/Category/CompHaus/ExplicitLimits.lean`
-/
section FiniteCoproducts

variable {α : Type} [Fintype α] (X : α → ExtrDisc.{u})

/--
The coproduct of a finite family of objects in `ExtrDisc`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : ExtrDisc := ExtrDisc.of <| Σ (a : α), X a

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
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

/--
The coproduct cocone associated to the explicit finite coproduct.
-/
@[simps]
def finiteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/--
The explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

end FiniteCoproducts


-- Pullback will not work!

-- variable {X Y B : ExtrDisc.{u}} (f : X ⟶ B) (g : Y ⟶ B)
--
-- /--
-- The pullback of two morphisms `f, g` in `ExtrDisc`, constructed explicitly as the set of
-- pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-- -/
-- def pullback : ExtrDisc.{u} :=
--   let set := { xy : X × Y | f xy.fst = g xy.snd }
--   have : CompactSpace set := by
--     rw [← isCompact_iff_compactSpace]
--     apply IsClosed.isCompact
--     exact isClosed_eq (f.continuous.comp continuous_fst) (g.continuous.comp continuous_snd)
--   ExtrDisc.of set
--
-- /--
-- The projection from the pullback to the first component.
-- -/
-- def pullback.fst : pullback f g ⟶ X where
--   toFun := fun ⟨⟨x,_⟩,_⟩ => x
--   continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val
--
-- /--
-- The projection from the pullback to the second component.
-- -/
-- def pullback.snd : pullback f g ⟶ Y where
--   toFun := fun ⟨⟨_,y⟩,_⟩ => y
--   continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

namespace EffectiveEpiFamily

variable {α : Type} [Fintype α] {B : ExtrDisc.{u}}
  {X : α → ExtrDisc.{u}} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

/--
Implementation: This is a setoid on the explicit finite coproduct of `X` whose quotient
will be isomorphic to `B` provided that `X a → B` is an effective epi family.
-/
def relation : Setoid (finiteCoproduct X) where
  r a b := ∃ (Z : ExtrDisc.{u}) (z : Z)
    (fst : Z ⟶ X a.fst) (snd : Z ⟶ X b.fst),
    fst ≫ π _ = snd ≫ π _ ∧ fst z = a.snd ∧ snd z = b.snd
  iseqv := by
    constructor
    · rintro ⟨a,x⟩
      refine ⟨X a, x, 𝟙 _, 𝟙 _, by simp, rfl, rfl⟩
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,w,h1,h2⟩
      exact ⟨Z,z,snd,fst,w.symm,h2,h1⟩
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨z,c⟩ ⟨Z, z,fstZ,sndZ,hZ,hZ1,hZ2⟩
      rintro ⟨W,w,fstW,sndW,hW,hW1,hW2⟩
      refine ⟨pullback sndZ fstW, ⟨⟨z,w⟩, by dsimp; rw [hZ2, hW1]⟩,
       pullback.fst _ _ ≫ fstZ, pullback.snd _ _ ≫ sndW, ?_, hZ1, hW2⟩
      dsimp at *
      simp only [Category.assoc, hZ, ← hW]
      apply ContinuousMap.ext
      rintro ⟨⟨u,v⟩,h⟩
      change π b (sndZ u) = π b (fstW v)
      rw [h]

/--
Implementation: the map from the quotient of `relation π` to `B`, which will eventually
become the function underlying an isomorphism, provided that `X a → B` is an effective epi family.
-/
def ιFun : Quotient (relation π) → B :=
  Quotient.lift (fun ⟨a,x⟩ => π a x) <| by
    rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,h,hx,hy⟩
    dsimp at *
    rw [← hx, ← hy]
    apply_fun (fun t => t z) at h
    exact h

lemma ιFun_continuous : Continuous (ιFun π) := by
  apply Continuous.quotient_lift
  apply continuous_sigma
  intro a
  exact (π a).continuous

lemma ιFun_injective : (ιFun π).Injective := by
  rintro ⟨⟨a,x⟩⟩ ⟨⟨b,y⟩⟩ (h : π _ _ = π _ _)
  apply Quotient.sound'
  refine ⟨pullback (π a) (π b), ⟨⟨x,y⟩,h⟩, pullback.fst _ _, pullback.snd _ _, ?_, rfl, rfl⟩
  ext ⟨_, h⟩ ; exact h

lemma ιFun_surjective : (ιFun π).Surjective := by
  intro b
  obtain ⟨a,x,h⟩ := surj b
  refine ⟨Quotient.mk _ ⟨a,x⟩, h⟩

lemma ιFun_bijective : (ιFun π).Bijective := ⟨ιFun_injective π, ιFun_surjective π surj⟩

/--
Implementation: The quotient of `relation π`, considered as an object of `CompHaus`.
-/
def QB₁ : CompHaus.{u} :=
  haveI : T2Space (Quotient <| relation π) :=
    ⟨fun _ _ h => separated_by_continuous (ιFun_continuous π) <| (ιFun_injective π).ne h ⟩
  CompHaus.of (Quotient <| relation π)

/-- The function `ι_fun`, considered as a morphism. -/
def ι₁Hom : (QB₁ π) ⟶ B.toCompHaus := ⟨ιFun π, ιFun_continuous π⟩

/--
Implementation: The promised isomorphism between `QB` and `B`.
-/
noncomputable
def ι₁Iso : (QB₁ π) ≅ B.toCompHaus :=
  have : IsIso (ι₁Hom π) := by
    apply CompHaus.isIso_of_bijective
    refine ⟨ιFun_injective _, ?_⟩
    intro b
    obtain ⟨a,x,h⟩ := surj b
    refine ⟨Quotient.mk _ ⟨a,x⟩, h⟩
  asIso (ι₁Hom π)

lemma isOpen_iso {X Y : TopCat} {U : Set X} (f : X ≅ Y) (h : IsOpen U) : IsOpen (f.hom '' U) := by
  let ff := TopCat.homeoOfIso f
  rw [← Homeomorph.isOpen_image ff] at h
  assumption

lemma _root_.TotallyDisconnectedSpace_ofIsIso
    {X Y : TopCat} [k : TotallyDisconnectedSpace X] (f : X ≅ Y) :
    TotallyDisconnectedSpace Y := by

  have surj' : Function.Surjective f.hom
  · apply (TopCat.homeoOfIso f).surjective

  have inj' : Function.Injective f.hom
  · apply (TopCat.homeoOfIso f).injective

  constructor
  unfold _root_.IsTotallyDisconnected
  intro t _ ht₂

  apply Set.subsingleton_of_preimage surj'

  replace k := k.isTotallyDisconnected_univ
  unfold _root_.IsTotallyDisconnected at k

  apply k

  tauto

  apply IsPreconnected.preimage_of_open_map
  assumption
  assumption
  · unfold IsOpenMap
    intro U hU
    apply isOpen_iso _ hU
  tauto

lemma CompHaus.TotallyDisconnectedSpace_ofIsIso
    {X Y : CompHaus} [k : TotallyDisconnectedSpace X] (f : X ≅ Y) :
    TotallyDisconnectedSpace Y := by
  have f : X.toTop ≅ Y.toTop
  · exact compHausToTop.mapIso f
  apply _root_.TotallyDisconnectedSpace_ofIsIso f

lemma ExtrDisc.TotallyDisconnectedSpace_ofIsIso
    {X Y : CompHaus} [k : TotallyDisconnectedSpace X] (f : X ≅ Y) :
    TotallyDisconnectedSpace Y := by
  have f : X.toTop ≅ Y.toTop
  · exact compHausToTop.mapIso f
  apply _root_.TotallyDisconnectedSpace_ofIsIso f

lemma QB₁_totallyDisconnectedSpace : TotallyDisconnectedSpace (QB₁ π) :=
  CompHaus.TotallyDisconnectedSpace_ofIsIso (ι₁Iso π surj).symm

/--
Implementation: The quotient of `relation π`, considered as an object of `ExtrDisc`.
-/
def QB₂ : ExtrDisc.{u} where
  toCompHaus := QB₁ π
  IsTotallyDisconnected := QB₁_totallyDisconnectedSpace π surj

/-- The function `ι_fun`, considered as a morphism. -/
def ι₂Hom : (QB₂ π surj) ⟶ B := ⟨ιFun π, ιFun_continuous π⟩

/--
Implementation: The promised isomorphism between `QB` and `B`.
-/
noncomputable
def ι₂Iso : (QB₂ π surj) ≅ B :=
  have : IsIso (ι₂Hom π surj) := by
    apply ExtrDisc.isIso_of_bijective
    refine ⟨ιFun_injective _, ?_⟩
    intro b
    obtain ⟨a,x,h⟩ := surj b
    refine ⟨Quotient.mk _ ⟨a,x⟩, h⟩
  asIso (ι₂Hom π surj)

/--
Implementation: The family of morphisms `X a ⟶ QB` which will be shown to be effective epi.
-/
def π' : (a : α) → (X a ⟶ QB₂ π surj) := fun a =>
  { toFun := fun x => Quotient.mk _ ⟨a, x⟩
    continuous_toFun := by
      apply Continuous.comp
      apply continuous_quot_mk
      apply continuous_sigmaMk (σ := fun a => X a) }

/--
Implementation: The family of morphisms `X a ⟶ QB` is an effective epi.
-/
def structAux : EffectiveEpiFamilyStruct X (π' π surj) where
  desc := fun {W} e h => {
    toFun := Quotient.lift (fun ⟨a,x⟩ => e a x) <| by
      rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,hh,hx,hy⟩
      dsimp at *
      rw [← hx, ← hy]
      specialize h _ _ fst snd ?_
      · ext z
        apply ιFun_injective
        apply_fun (fun q => q z) at hh
        exact hh
      apply_fun (fun q => q z) at h
      exact h
    continuous_toFun := by
      apply Continuous.quotient_lift
      apply continuous_sigma
      intro a
      exact (e a).continuous }
  fac := by intro Z e h a ; ext ; rfl
  uniq := by
    intro Z e h m hm
    ext ⟨⟨a,x⟩⟩
    specialize hm a
    apply_fun (fun q => q x) at hm
    exact hm

@[reassoc]
lemma π'_comp_ι_hom (a : α) : π' π surj a ≫ (ι₂Iso π surj).hom = π a := by ext ; rfl

@[reassoc]
lemma π_comp_ι_inv (a : α) : π a ≫ (ι₂Iso π surj).inv = π' π surj a :=  by
  rw [Iso.comp_inv_eq]
  exact π'_comp_ι_hom _ surj _

/--
Implementation: The family `X` is an effective epi, provided that `π` are jointly surjective.
The theorem `ExtrDisc.effectiveEpiFamily_tfae` should be used instead.
-/
noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => (ι₂Iso π surj).inv ≫ (structAux π surj).desc e (fun {Z} a₁ a₂ g₁ g₂ hh => by
      apply h
      rw [← cancel_mono (ι₂Iso _ surj).inv]
      simpa only [Category.assoc, π_comp_ι_inv])
  fac := by
    intro W e h a
    simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast, π_comp_ι_inv_assoc, (structAux π surj).fac]
  uniq := by
    intro W e h m hm
    dsimp
    rw [Iso.eq_inv_comp]
    apply (structAux π surj).uniq
    intro a
    simpa using hm a

end EffectiveEpiFamily

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : ExtrDisc.{u}}
    (X : α → ExtrDisc.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨ExtrDisc.EffectiveEpiFamily.struct π surj⟩⟩

open List in
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : ExtrDisc.{u}}
    (X : α → ExtrDisc.{u})
    (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 1 → 2
  · intro
    infer_instance
    -- #check CategoryTheory.epiCoproductDescOfEffectiveEpiFamily
  tfae_have 2 → 3
  · intro e
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t,rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id] ; rfl
    rw [this]
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this] ; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext ; rfl
  tfae_have 3 → 1
  · apply effectiveEpiFamily_of_jointly_surjective
  tfae_finish

end ExtrDisc
